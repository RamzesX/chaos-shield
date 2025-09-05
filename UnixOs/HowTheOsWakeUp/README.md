# x86 Bootloader: Interactive Matrix-Themed Demo

A 512-byte x86 bootloader that displays an interactive ASCII art demo with Matrix-themed elements, replacing traditional OS loading with a creative interactive experience.

## Table of Contents

1. [Overview](#overview)
2. [Technical Architecture](#technical-architecture)
3. [x86 Real Mode Programming](#x86-real-mode-programming)
4. [BIOS Services and Interrupts](#bios-services-and-interrupts)
5. [Memory Layout](#memory-layout)
6. [Implementation Details](#implementation-details)
7. [Build and Run Instructions](#build-and-run-instructions)
8. [Code Walkthrough](#code-walkthrough)
9. [Screenshots](#screenshots)
10. [Learning Resources](#learning-resources)

## Overview

This project demonstrates low-level x86 assembly programming by creating a bootloader that, instead of loading an operating system, presents an interactive demo featuring:

- ASCII art rendering of a carrot logo
- Matrix-inspired "red pill/blue pill" choice interface
- Keyboard navigation between options
- Creative use of the 512-byte boot sector limitation
- Direct VGA text mode manipulation

### Why This Project Matters

Understanding bootloaders provides insight into:
- How computers start from power-on
- x86 processor modes and evolution
- BIOS/UEFI firmware interfaces
- Low-level system programming
- The boot process chain: CPU → BIOS → Bootloader → OS

## Technical Architecture

### The Boot Process

```
┌─────────────────────────────────────────────────────────┐
│                     Power On                            │
└────────────────────┬────────────────────────────────────┘
                     ↓
┌─────────────────────────────────────────────────────────┐
│              CPU Reset Vector (0xFFFFFFF0)              │
│         Jumps to BIOS/UEFI firmware code                │
└────────────────────┬────────────────────────────────────┘
                     ↓
┌─────────────────────────────────────────────────────────┐
│                    BIOS POST                            │
│    Power-On Self Test, hardware initialization          │
└────────────────────┬────────────────────────────────────┘
                     ↓
┌─────────────────────────────────────────────────────────┐
│              Boot Device Selection                       │
│    BIOS searches for boot signature 0xAA55              │
└────────────────────┬────────────────────────────────────┘
                     ↓
┌─────────────────────────────────────────────────────────┐
│           Load Boot Sector to 0x7C00                    │
│    First 512 bytes loaded to memory address 0x7C00      │
└────────────────────┬────────────────────────────────────┘
                     ↓
┌─────────────────────────────────────────────────────────┐
│              Execute Bootloader Code                     │
│         CPU jumps to 0x7C00 and begins execution        │
└─────────────────────────────────────────────────────────┘
```

### Boot Sector Structure

The Master Boot Record (MBR) format:

```
Offset    Size    Description
────────────────────────────────────
0x000     446     Bootloader code
0x1BE     64      Partition table (4 entries × 16 bytes)
0x1FE     2       Boot signature (0xAA55)
────────────────────────────────────
Total:    512 bytes
```

In our demo, we use all 510 bytes for code and data, with the final 2 bytes for the boot signature.

## x86 Real Mode Programming

### Processor Modes

The x86 processor starts in **Real Mode**, a 16-bit mode with:
- 1 MB addressable memory (20-bit addressing)
- Segmented memory model
- Direct hardware access
- No memory protection
- BIOS interrupt services available

### Segmented Memory Model

Physical Address = (Segment × 16) + Offset

```
Segment:Offset notation
CS:IP  → Code Segment : Instruction Pointer
DS:SI  → Data Segment : Source Index
ES:DI  → Extra Segment : Destination Index
SS:SP  → Stack Segment : Stack Pointer
```

### Register Set in Real Mode

```
General Purpose (16-bit):
AX (AH/AL) - Accumulator
BX (BH/BL) - Base
CX (CH/CL) - Counter
DX (DH/DL) - Data

Segment Registers:
CS - Code Segment
DS - Data Segment
ES - Extra Segment
SS - Stack Segment

Index/Pointer:
SI - Source Index
DI - Destination Index
SP - Stack Pointer
BP - Base Pointer
IP - Instruction Pointer

Flags:
FLAGS - Status and control flags
```

## BIOS Services and Interrupts

### Interrupt Vector Table (IVT)

Located at 0x0000:0x0000, contains 256 4-byte entries:

```
Interrupt  Vector Address  Service
─────────────────────────────────────
INT 0x10   0x0040         Video Services
INT 0x13   0x004C         Disk Services
INT 0x16   0x0058         Keyboard Services
INT 0x19   0x0064         Bootstrap Loader
```

### Key BIOS Interrupts Used

#### INT 0x10 - Video Services

```assembly
; Set video mode
mov ah, 0x00    ; Function: Set video mode
mov al, 0x03    ; Mode: 80x25 16-color text
int 0x10

; Hide cursor
mov ah, 0x01    ; Function: Set cursor shape
mov ch, 0x26    ; Start scan line (out of range = hidden)
int 0x10

; Set cursor position
mov ah, 0x02    ; Function: Set cursor position
mov bh, 0x00    ; Page number
mov dh, row     ; Row (0-24)
mov dl, column  ; Column (0-79)
int 0x10
```

#### INT 0x16 - Keyboard Services

```assembly
; Check for keystroke
mov ah, 0x01    ; Function: Check keyboard buffer
int 0x16
jz no_key       ; ZF=1 if no key available

; Get keystroke
mov ah, 0x00    ; Function: Get keystroke
int 0x16        ; Returns: AH=scan code, AL=ASCII
```

### VGA Text Mode Memory

Text mode video memory starts at 0xB800:0x0000

Each character cell = 2 bytes:
```
Byte 0: ASCII character code
Byte 1: Attribute byte
        Bits 7-4: Background color
        Bit 3: Background intensity
        Bits 2-0: Foreground color
```

Color codes:
```
0x0 - Black      0x8 - Dark Gray
0x1 - Blue       0x9 - Light Blue
0x2 - Green      0xA - Light Green
0x3 - Cyan       0xB - Light Cyan
0x4 - Red        0xC - Light Red
0x5 - Magenta    0xD - Light Magenta
0x6 - Brown      0xE - Yellow
0x7 - Light Gray 0xF - White
```

## Memory Layout

### Boot Time Memory Map

```
Address Range          Usage
──────────────────────────────────────────
0x00000 - 0x003FF     Interrupt Vector Table
0x00400 - 0x004FF     BIOS Data Area
0x00500 - 0x07BFF     Free (30 KB)
0x07C00 - 0x07DFF     Boot Sector (512 bytes) ← Our code loads here
0x07E00 - 0x9FFFF     Free (~480 KB)
0xA0000 - 0xBFFFF     Video RAM
0xC0000 - 0xFFFFF     BIOS ROM
```

### Our Program's Memory Usage

```
0x7C00 - Start of bootloader code
0x9C00 - Stack pointer initialization
0xB800:0000 - Video memory base (physical 0xB8000)
```

## Implementation Details

### Program Structure

1. **Initialization Phase**
   - Clear registers
   - Set up segments (DS=0, ES=0xB800, SS=0)
   - Initialize stack (SP=0x9C00)
   - Set video mode (80x25 text)
   - Hide cursor

2. **Rendering Phase**
   - Draw blue border
   - Render ASCII art (carrot)
   - Display text messages
   - Show red/blue pill options

3. **Interactive Loop**
   - Poll keyboard
   - Update selection indicator
   - Redraw affected areas

### ASCII Art Design

The program creates visual elements using:
- Box drawing characters
- Colored backgrounds
- Strategic positioning

```
┌──────────────────────────┐
│     CARROT OS            │
│        🥕                │
│                          │
│   For White Rabbit!      │
│                          │
│  > Red Pill              │
│    Blue Pill             │
└──────────────────────────┘
```

### Optimization Techniques

Due to the 512-byte limitation:
- Use of string instructions (STOSW, MOVSB)
- Register reuse
- Compact loop structures
- Direct video memory manipulation
- Minimal stack usage

## Build and Run Instructions

### Prerequisites

**Linux/Unix:**
```bash
# Install NASM assembler
sudo apt-get install nasm

# Install QEMU emulator
sudo apt-get install qemu-system-x86

# Optional: Install hex editor for inspection
sudo apt-get install hexedit
```

**Windows:**
```powershell
# Using Chocolatey
choco install nasm
choco install qemu

# Or download directly:
# NASM: https://www.nasm.us/
# QEMU: https://www.qemu.org/
```

**macOS:**
```bash
# Using Homebrew
brew install nasm
brew install qemu
```

### Building the Bootloader

```bash
# Clone the repository
git clone <repository-url>
cd Bootloader

# Build using makefile
make

# Or build manually:
nasm -f bin boot.asm -o boot.bin
```

### Running the Bootloader

```bash
# Run with QEMU
make run

# Or manually:
qemu-system-i386 -drive format=raw,file=boot.bin

# Alternative: Create floppy image
dd if=/dev/zero of=floppy.img bs=512 count=2880
dd if=boot.bin of=floppy.img bs=512 count=1 conv=notrunc
qemu-system-i386 -fda floppy.img
```

### Testing on Real Hardware (Advanced)

**⚠️ Warning: This will overwrite the boot sector!**

```bash
# Write to USB drive (replace sdX with your device)
sudo dd if=boot.bin of=/dev/sdX bs=512 count=1

# Boot from USB on a real machine
```

## Code Walkthrough

### Initialization Section

```assembly
[ORG 0x7c00]      ; Tell assembler code starts at 0x7C00

; Define keyboard scan codes
LEFT  EQU 75
RIGHT EQU 77
UP    EQU 72
DOWN  EQU 80

; Initialize segments
xor ax, ax        ; AX = 0
mov ds, ax        ; Data Segment = 0
mov ss, ax        ; Stack Segment = 0
mov sp, 0x9c00    ; Stack Pointer (grows downward)

; Set up video segment
mov ah, 0xb8      ; Video memory segment
mov es, ax        ; ES = 0xB800

; Set video mode
mov al, 0x03      ; 80x25 text mode
int 0x10          ; BIOS video service

; Hide cursor
mov ah, 1
mov ch, 0x26      ; Cursor start line (out of range)
int 0x10
```

### Border Drawing

```assembly
; Fill screen with blue background
mov cx, 0x07d0    ; 80×25 = 2000 chars
mov ax, 0xCC00    ; Attribute: blue bg, black fg, no char
xor di, di        ; Start at video memory offset 0
rep stosw         ; Repeat store word

; Create black inner area
mov di, 158       ; Start position (skip first row)
cbw               ; Clear AX
fillin:
scasw            ; Skip 2 positions
scasw
mov cl, 78       ; 78 columns (leaving borders)
rep stosw        ; Fill with black
cmp di, 0x0efe   ; Check if done
jne fillin       ; Loop if not
```

### ASCII Art Rendering

```assembly
; Draw carrot shape
mov di, 0xB65     ; Starting position
mov al, 0x66      ; Character to display
stosb             ; Store byte to video memory

; Complex loop for drawing carrot parts
loop:
   sub di, dx     ; Move position
   stosb          ; Draw character
   sub di, 0xA1   ; Next position calculation
   stosb
   add bx, 0x1    ; Counter
   cmp bx, 0x5    ; Loop 5 times
   jne loop
```

### Text Display

```assembly
; Display "Norbert Marchewka" signature
mov di, 0xf04              ; Position
mov al, 0xc1               ; White on blue
mov si, winmessage         ; Message pointer
mov cl, winmessage_e - winmessage ; Length
winloop: 
   movsb                   ; Move string byte
   stosb                   ; Store with attribute
   loop winloop

winmessage:
   db 0x4e, 0x4d           ; "NM"
   db 0x15, 0x00
winmessage_e:
```

### Interactive Menu System

```assembly
mainloop:
   mov ah, 1              ; Check for keystroke
   int 0x16
   pop ax
   jz persisted           ; No key? Continue with last direction

   ; Clear keyboard buffer
   xor ah, ah
   int 0x16

persisted:
   push ax
   ; Check for arrow keys
   cmp ah, LEFT
   je left
   cmp ah, RIGHT
   je right
   jne mainloop

left:
   ; Move selection indicator to red pill
   mov di, 0xA6E          ; Blue pill position
   mov ax, 0x003E         ; Clear indicator
   stosw
   mov di, 0xA4E          ; Red pill position  
   mov ax, 0x073E         ; Draw indicator '>'
   stosw
   jmp mainloop

right:
   ; Move selection indicator to blue pill
   mov di, 0xA4E          ; Red pill position
   mov ax, 0x003E         ; Clear indicator
   stosw
   mov di, 0xA6E          ; Blue pill position
   mov ax, 0x073E         ; Draw indicator '>'
   stosw
   jmp mainloop
```

### Boot Signature

```assembly
times 510-($-$$) db 0     ; Pad to 510 bytes
dw 0xAA55                 ; Boot signature
```

## Advanced Topics

### Extending Beyond 512 Bytes

For larger programs, implement a two-stage bootloader:

```assembly
; Stage 1 (boot sector)
; Load stage 2 from disk
mov ah, 0x02      ; BIOS read sectors
mov al, 10        ; Number of sectors
mov ch, 0         ; Cylinder
mov cl, 2         ; Starting sector
mov dh, 0         ; Head
mov bx, 0x7E00    ; Load address
int 0x13          ; Disk I/O
jmp 0x7E00        ; Jump to stage 2
```

### Switching to Protected Mode

To access more memory and 32-bit features:

```assembly
; Load GDT
lgdt [gdt_descriptor]

; Enable A20 line
in al, 0x92
or al, 2
out 0x92, al

; Switch to protected mode
mov eax, cr0
or eax, 1
mov cr0, eax

; Far jump to 32-bit code
jmp CODE_SEG:protected_mode_start
```

### UEFI vs Legacy BIOS

Modern systems use UEFI:

| Feature | Legacy BIOS | UEFI |
|---------|------------|------|
| Boot Size | 512 bytes | No limit (file system aware) |
| Mode | 16-bit real | 32/64-bit protected |
| Interface | Interrupts | Function calls |
| Storage | MBR | GPT |
| Security | None | Secure Boot |

### Creating a Simple OS

Next steps to build a minimal OS:

1. **Memory Management**
   - Physical memory detection
   - Page allocation
   - Virtual memory setup

2. **Interrupt Handling**
   - IDT setup
   - Exception handlers
   - Hardware interrupts

3. **Device Drivers**
   - Keyboard driver
   - Display driver
   - Disk driver

4. **File System**
   - Simple FS implementation
   - File operations

5. **Process Management**
   - Task switching
   - Scheduling
   - System calls

## Debugging Techniques

### QEMU Monitor

```bash
# Start QEMU with monitor
qemu-system-i386 -monitor stdio -drive format=raw,file=boot.bin

# Monitor commands:
(qemu) info registers     # Show CPU registers
(qemu) x/20hx 0x7c00     # Examine memory
(qemu) stop              # Pause execution
(qemu) cont              # Continue execution
```

### GDB Debugging

```bash
# Start QEMU with GDB server
qemu-system-i386 -s -S -drive format=raw,file=boot.bin

# In another terminal
gdb
(gdb) target remote localhost:1234
(gdb) set architecture i8086
(gdb) break *0x7c00
(gdb) continue
(gdb) x/10i $pc          # Disassemble
(gdb) info registers     # Show registers
```

### Bochs Debugger

```bash
# Bochs configuration file (bochsrc.txt)
megs: 32
romimage: file=$BXSHARE/BIOS-bochs-latest
vgaromimage: file=$BXSHARE/VGABIOS-lgpl-latest
boot: floppy
floppya: 1_44=boot.bin, status=inserted
log: bochs.log
mouse: enabled=0
display_library: sdl2

# Run with debugger
bochs -f bochsrc.txt
```

## Common Issues and Solutions

### Problem: Bootloader doesn't execute
**Solution:** Verify boot signature (0xAA55) at bytes 510-511

### Problem: Display corruption
**Solution:** Ensure ES points to 0xB800 for video memory

### Problem: Keyboard input not working
**Solution:** Clear keyboard buffer after reading

### Problem: Code exceeds 512 bytes
**Solution:** Optimize or implement two-stage bootloader

## Performance Considerations

### Optimization Strategies

1. **Use String Instructions**
   ```assembly
   rep stosw    ; Faster than loops for memory filling
   rep movsb    ; Efficient for copying
   ```

2. **Register Usage**
   - Keep frequently used values in registers
   - Use 8-bit operations when possible

3. **Memory Access**
   - Minimize memory reads/writes
   - Use word operations over byte when possible

4. **Code Size**
   - Reuse code through subroutines
   - Use compact instructions (CBW, CWD)
   - Eliminate redundant instructions

## Security Considerations

### Boot Sector Viruses

Historical context: Boot sector viruses were common because:
- Direct hardware access
- Executed before OS security
- Difficult to detect

Protection methods:
- UEFI Secure Boot
- Boot sector verification
- Write-protection

### Modern Security

UEFI provides:
- Cryptographic verification
- Measured boot
- TPM integration
- Secure variable storage

## Learning Resources

### Books

1. **"Programming Boot Sector Games"** by Oscar Toledo G.
   - Creating games in 512 bytes
   - Advanced optimization techniques

2. **"The Art of Assembly Language"** by Randall Hyde
   - Comprehensive x86 assembly
   - Real mode programming

3. **"Operating Systems: Design and Implementation"** by Tanenbaum
   - OS concepts
   - MINIX source code

4. **"PC Assembly Language"** by Paul A. Carter
   - Free online book
   - Practical examples

### Online Resources

1. **OSDev Wiki**
   - https://wiki.osdev.org
   - Comprehensive OS development resource

2. **Ralph Brown's Interrupt List**
   - http://www.ctyme.com/rbrown.htm
   - Complete BIOS interrupt reference

3. **James Molloy's Kernel Tutorial**
   - OS development from scratch
   - Step-by-step guide

4. **x86 Assembly Wikibook**
   - https://en.wikibooks.org/wiki/X86_Assembly
   - Free comprehensive guide

### Video Tutorials

1. **"Writing a Simple Operating System from Scratch"**
   - Nick Blundell's tutorial
   - PDF and examples

2. **"OS Development Series"**
   - BrokenThorn Entertainment
   - Comprehensive video series

### Practice Projects

1. **Bootloader Challenges**
   - Display system information
   - Simple text editor
   - Memory test utility
   - Disk sector reader

2. **Game Development**
   - Snake game
   - Tetris clone
   - Maze generator
   - Simple animations

3. **System Utilities**
   - Password protection
   - Boot menu
   - Hardware detection
   - Simple shell

## Conclusion

This bootloader project demonstrates fundamental concepts of low-level system programming. By working within the constraints of 512 bytes, we learn:

- x86 architecture and real mode programming
- BIOS services and hardware interaction
- Memory management and segmentation
- Optimization techniques
- Creative problem-solving within constraints

The transition from power-on to executing custom code reveals the elegant simplicity of the boot process, while the interactive demo shows that even severe constraints can't limit creativity.

Whether you're interested in operating system development, embedded systems, or just understanding how computers really work, bootloader programming provides invaluable insights into the foundation of modern computing.

### Next Steps

1. Extend to a two-stage bootloader
2. Add more interactive features
3. Implement protected mode switching
4. Create a simple kernel
5. Explore UEFI development

Remember: Every operating system, from DOS to Linux to Windows, started with these same 512 bytes. What will you create with yours?

---

## Screenshots

![Boot Screen](screeny/Screenshot%20from%202019-10-11%2011-38-20.png)
*Initial boot screen with carrot ASCII art and menu options*

![Interactive Menu](screeny/Screenshot%20from%202019-10-11%2011-38-22.png)
*Interactive menu showing red pill/blue pill selection*

---

*"Follow the White Rabbit..."* 🐰

**Repository:** Bootloader Project  
**Author:** Norbert Marchewka  
**License:** Educational Use  
**Created:** 2019  
**Updated:** 2024
