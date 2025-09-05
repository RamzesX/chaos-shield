; ============================================================================
; x86 Bootloader - Interactive Matrix-Themed Demo
; Author: Norbert Marchewka
; Description: A 512-byte bootloader that creates an interactive ASCII art
;              demo featuring a carrot logo and Matrix red/blue pill choice
; ============================================================================

[BITS 16]                      ; 16-bit Real Mode
[ORG 0x7c00]                   ; BIOS loads boot sector here

; ============================================================================
; Constants and Definitions
; ============================================================================

; Keyboard scan codes
LEFT  EQU 75                   ; Left arrow key
RIGHT EQU 77                   ; Right arrow key
UP    EQU 72                   ; Up arrow key (unused)
DOWN  EQU 80                   ; Down arrow key (unused)

; Video memory constants
VIDEO_SEG     EQU 0xB800       ; Text mode video memory segment
SCREEN_WIDTH  EQU 80           ; 80 columns
SCREEN_HEIGHT EQU 25           ; 25 rows
CHAR_BYTES    EQU 2            ; 2 bytes per character (char + attribute)

; Color attributes (Background:Foreground)
ATTR_BLUE_BG  EQU 0xCC         ; Blue background
ATTR_WHITE_BLUE EQU 0xC1       ; White on blue
ATTR_RED      EQU 0x04         ; Red text
ATTR_BLUE     EQU 0x01         ; Blue text
ATTR_CYAN     EQU 0x0C         ; Light red/cyan
ATTR_WHITE    EQU 0x0F         ; Bright white
ATTR_GRAY     EQU 0x07         ; Light gray

; ============================================================================
; Entry Point - Bootloader Initialization
; ============================================================================

boot_start:
    ; Clear registers and set up segments
    xor ax, ax                 ; AX = 0
    mov ds, ax                 ; Data Segment = 0
    mov ss, ax                 ; Stack Segment = 0
    mov sp, 0x9c00             ; Stack pointer (grows downward)

    ; Set up video memory segment
    mov ax, VIDEO_SEG
    mov es, ax                 ; ES = 0xB800 for video memory access

    ; Set video mode to 80x25 16-color text mode
    mov ax, 0x0003             ; AH=00h (set video mode), AL=03h (80x25 text)
    int 0x10                   ; BIOS video interrupt

    ; Hide the text cursor
    mov ah, 0x01               ; Set cursor shape
    mov ch, 0x26               ; Start scan line (out of range = invisible)
    mov cl, 0x07               ; End scan line
    int 0x10                   ; BIOS video interrupt

; ============================================================================
; Draw Border and Background
; ============================================================================

draw_border:
    ; Fill entire screen with blue background
    xor di, di                 ; DI = 0 (start of video memory)
    mov cx, 0x07d0             ; 2000 words (80*25 characters)
    mov ax, ATTR_BLUE_BG << 8 ; Blue background, no character
    rep stosw                  ; Fill video memory

    ; Create black inner area (leaving blue border)
    mov di, 158                ; Start at row 1, column 1 (skip border)

.fill_inner:
    add di, 4                  ; Skip left border (2 chars)
    mov cl, 78                 ; Fill 78 columns
    xor ax, ax                 ; Black background, no character
    rep stosw                  ; Fill row
    cmp di, 0x0efe             ; Check if we've reached the last row
    jb .fill_inner             ; Continue if not done

; ============================================================================
; Draw ASCII Art - Carrot Logo
; ============================================================================

draw_carrot:
    ; Initialize score/position (can be used for game mechanics)
    mov bp, 0x0200

    ; Draw main carrot shape
    mov di, 0x0B65             ; Starting position for carrot
    mov al, 0x66               ; Block character for carrot body
    mov ah, 0x06               ; Brown/orange color

    ; Draw carrot top (leaves)
    mov bx, 5                  ; Loop counter
.draw_leaves:
    sub di, 0xA3               ; Move up and adjust position
    stosb                      ; Draw character
    inc ah                     ; Change color slightly
    sub di, 0xA1               ; Adjust position
    stosb
    dec bx
    jnz .draw_leaves

    ; Draw carrot body
    mov di, 0x0B65             ; Reset position
    mov dx, 0x9E               ; Position offset
    mov cx, 10                 ; Number of segments

.draw_body:
    sub di, dx                ; Calculate position
    stosb                      ; Draw segment
    add dx, 2                  ; Adjust offset
    loop .draw_body

; ============================================================================
; Draw Text Labels
; ============================================================================

draw_text:
    ; Draw "NM" signature (Norbert Marchewka)
    mov di, 0x0f04             ; Bottom area
    mov si, sig_nm
    call draw_string

    ; Draw "Carrot" text
    mov di, 0x0566             ; Position for "Carrot"
    mov si, txt_carrot
    mov ah, ATTR_CYAN
    call draw_string

    ; Draw "For" text
    mov di, 0x060A
    mov ax, 0x0C46             ; 'F'
    stosw
    mov ax, 0x0C6F             ; 'o'
    stosw
    mov ax, 0x0C72             ; 'r'
    stosw

    ; Draw "White Rabbit!" text
    mov di, 0x06A2
    mov si, txt_white
    mov ah, ATTR_WHITE
    call draw_string

    mov di, 0x06AE
    mov si, txt_rabbit
    mov ah, ATTR_CYAN
    call draw_string

    ; Draw "Rabbit OS" at bottom
    mov di, 0x0f8a
    mov si, txt_rabbit_os
    mov ah, ATTR_WHITE_BLUE
    call draw_string

; ============================================================================
; Draw Menu Options
; ============================================================================

draw_menu:
    ; Draw "Red Pill" option
    mov di, 0x0A52
    mov si, txt_red_pill
    mov ah, ATTR_RED
    call draw_string

    ; Draw "Blue Pill" option
    mov di, 0x0A72
    mov si, txt_blue_pill
    mov ah, ATTR_BLUE
    call draw_string

    ; Draw initial selection indicator ('>') at Red Pill
    mov di, 0x0A4E
    mov ax, 0x073E             ; '>' with gray attribute
    stosw

; ============================================================================
; Main Interactive Loop
; ============================================================================

    push ax                    ; Save initial state

main_loop:
    ; Check for keyboard input
    mov ah, 0x01               ; Check keyboard status
    int 0x16                   ; BIOS keyboard interrupt
    pop ax                     ; Restore last key state
    jz .no_key                 ; If no key pressed, continue

    ; Get the key from buffer
    xor ah, ah                 ; Get keystroke
    int 0x16                   ; AH = scan code, AL = ASCII

.no_key:
    push ax                    ; Save current key state

    ; Check for left arrow
    cmp ah, LEFT
    je .select_left

    ; Check for right arrow
    cmp ah, RIGHT
    je .select_right

    jmp main_loop              ; Continue loop

.select_left:
    ; Move indicator to Red Pill (left option)
    mov di, 0x0A6E             ; Blue pill indicator position
    mov ax, 0x0020             ; Clear (space)
    stosw

    mov di, 0x0A4E             ; Red pill indicator position
    mov ax, 0x073E             ; Draw '>'
    stosw
    jmp main_loop

.select_right:
    ; Move indicator to Blue Pill (right option)
    mov di, 0x0A4E             ; Red pill indicator position
    mov ax, 0x0020             ; Clear (space)
    stosw

    mov di, 0x0A6E             ; Blue pill indicator position
    mov ax, 0x073E             ; Draw '>'
    stosw
    jmp main_loop

; ============================================================================
; Utility Functions
; ============================================================================

; Draw a null-terminated string
; Input: SI = string pointer, DI = video position, AH = attribute
draw_string:
    push cx
.loop:
    lodsb                      ; Load character from [SI]
    or al, al                  ; Check for null terminator
    jz .done
    stosw                      ; Store character and attribute
    jmp .loop
.done:
    pop cx
    ret

; ============================================================================
; Data Section
; ============================================================================

sig_nm:
    db "NM", 0x15, 0

txt_carrot:
    db "Carrot", 0

txt_white:
    db "White", 0

txt_rabbit:
    db "Rabbit!", 0

txt_rabbit_os:
    db "Rabbit", 0

txt_red_pill:
    db "Red", 0x00, "Pill", 0

txt_blue_pill:
    db "Blue", 0x00, "Pill", 0

; ============================================================================
; Boot Sector Padding and Signature
; ============================================================================

    ; Pad remainder of boot sector with zeros
    times 510-($-$$) db 0

    ; Boot sector signature (required by BIOS)
    dw 0xAA55

; ============================================================================
; Optional: Padding for floppy disk image
; ============================================================================

    ; Uncomment to create a full 1.44MB floppy image
    ; times (1440 * 1024) - ($ - $$) db 0
