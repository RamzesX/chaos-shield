# Quick Reference: x86 Bootloader Development

## Essential BIOS Interrupts

### INT 0x10 - Video Services

```assembly
; AH=0x00: Set video mode
mov ah, 0x00
mov al, 0x03    ; 80x25 color text
int 0x10

; AH=0x01: Set cursor shape
mov ah, 0x01
mov ch, 0x20    ; Cursor off
int 0x10

; AH=0x02: Set cursor position
mov ah, 0x02
mov bh, 0       ; Page
mov dh, row     ; Row (0-24)
mov dl, col     ; Column (0-79)
int 0x10

; AH=0x0E: Teletype output
mov ah, 0x0E
mov al, 'A'     ; Character
mov bh, 0       ; Page
mov bl, 0x07    ; Attribute
int 0x10
```

### INT 0x13 - Disk Services

```assembly
; AH=0x02: Read sectors
mov ah, 0x02
mov al, 1       ; Sectors to read
mov ch, 0       ; Cylinder
mov cl, 2       ; Sector (1-based)
mov dh, 0       ; Head
mov dl, 0x80    ; Drive (0x80=HDD)
mov bx, 0x8000  ; Buffer address
int 0x13
jc error        ; CF=1 on error
```

### INT 0x16 - Keyboard Services

```assembly
; AH=0x00: Get keystroke
mov ah, 0x00
int 0x16
; Returns: AH=scan code, AL=ASCII

; AH=0x01: Check keystroke
mov ah, 0x01
int 0x16
jz no_key       ; ZF=1 if no key
```

## Video Memory Layout

```
Text Mode (0xB8000):
┌──────────────────────────┐
│ Char │ Attr │ Char │ Attr│
└──────────────────────────┘
  Even   Odd    Even   Odd

Attribute Byte:
┌─────────────────────────┐
│ Blink │ Background │ Foreground │
│  7    │    6-4     │    3-0     │
└─────────────────────────┘
```

## Common x86 Instructions

### Data Movement
```assembly
mov dst, src    ; Move data
push src        ; Push to stack
pop dst         ; Pop from stack
xchg op1, op2   ; Exchange values
lea reg, mem    ; Load effective address
```

### String Operations
```assembly
movsb          ; Move byte [DS:SI] to [ES:DI]
movsw          ; Move word
stosb          ; Store AL at [ES:DI]
stosw          ; Store AX at [ES:DI]
lodsb          ; Load [DS:SI] to AL
lodsw          ; Load [DS:SI] to AX
rep            ; Repeat CX times
```

### Arithmetic
```assembly
add dst, src   ; Addition
sub dst, src   ; Subtraction
inc dst        ; Increment
dec dst        ; Decrement
mul src        ; Unsigned multiply
div src        ; Unsigned divide
```

### Logic
```assembly
and dst, src   ; Bitwise AND
or dst, src    ; Bitwise OR
xor dst, src   ; Bitwise XOR
not dst        ; Bitwise NOT
shl dst, count ; Shift left
shr dst, count ; Shift right
```

### Control Flow
```assembly
jmp label      ; Unconditional jump
je/jz label    ; Jump if equal/zero
jne/jnz label  ; Jump if not equal
jl label       ; Jump if less
jg label       ; Jump if greater
call proc      ; Call procedure
ret            ; Return from procedure
loop label     ; Dec CX and jump if non-zero
```

## Segment:Offset Addressing

```
Physical = Segment * 16 + Offset

Example:
0xB800:0x0000 = 0xB8000 (video memory)
0x0000:0x7C00 = 0x07C00 (boot sector)
```

## Boot Sector Template

```assembly
[BITS 16]
[ORG 0x7C00]

start:
    ; Initialize segments
    xor ax, ax
    mov ds, ax
    mov es, ax
    mov ss, ax
    mov sp, 0x7C00
    
    ; Your code here
    
    ; Infinite loop
hang:
    jmp hang

; Boot signature
times 510-($-$$) db 0
dw 0xAA55
```

## Color Codes

```
0x0 Black       0x8 Dark Gray
0x1 Blue        0x9 Light Blue
0x2 Green       0xA Light Green
0x3 Cyan        0xB Light Cyan
0x4 Red         0xC Light Red
0x5 Magenta     0xD Light Magenta
0x6 Brown       0xE Yellow
0x7 Light Gray  0xF White
```

## ASCII Box Drawing

```
┌─┬─┐  ╔═╦═╗  ┏━┳━┓
│ │ │  ║ ║ ║  ┃ ┃ ┃
├─┼─┤  ╠═╬═╣  ┣━╋━┫
│ │ │  ║ ║ ║  ┃ ┃ ┃
└─┴─┘  ╚═╩═╝  ┗━┻━┛

Codes:
─ 0xC4  │ 0xB3  ┌ 0xDA  ┐ 0xBF
└ 0xC0  ┘ 0xD9  ├ 0xC3  ┤ 0xB4
┬ 0xC2  ┴ 0xC1  ┼ 0xC5
```

## Memory Map

```
0x00000-0x003FF  IVT (1KB)
0x00400-0x004FF  BIOS Data (256B)
0x00500-0x07BFF  Free (~30KB)
0x07C00-0x07DFF  Boot Sector (512B)
0x07E00-0x9FFFF  Free (~608KB)
0xA0000-0xBFFFF  Video RAM (128KB)
0xC0000-0xFFFFF  BIOS ROM (256KB)
```

## Debug Commands

```bash
# QEMU Monitor
(qemu) info registers
(qemu) x/16xb 0x7c00
(qemu) stop/cont

# GDB
(gdb) set architecture i8086
(gdb) target remote :1234
(gdb) break *0x7c00
(gdb) x/10i $pc
(gdb) info registers
```

## Common Pitfalls

1. **Forgetting boot signature**: Always end with `dw 0xAA55`
2. **Wrong segment setup**: Initialize all segments explicitly
3. **Stack overflow**: Set SP to safe location
4. **Off-by-one errors**: Video memory is word-aligned
5. **Register clobbering**: Save registers before BIOS calls

## Optimization Tips

1. Use `xor reg, reg` instead of `mov reg, 0` (2 vs 3 bytes)
2. Use `stosw` for filling memory
3. Use `loop` instead of `dec cx; jnz`
4. Combine operations: `mov ax, 0x0720` sets char and attribute
5. Use string instructions with `rep` prefix

## Testing Checklist

- [ ] Boot signature present
- [ ] Segments initialized
- [ ] Stack configured
- [ ] Runs in QEMU
- [ ] Runs in Bochs
- [ ] Runs in VirtualBox
- [ ] Size ≤ 510 bytes
- [ ] No register corruption
- [ ] Keyboard handling works
- [ ] Display renders correctly
