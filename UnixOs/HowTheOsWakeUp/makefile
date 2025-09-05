# Makefile for x86 Bootloader Project
# Author: Norbert Marchewka

# Binary output path
BINDIR = bin
BOOTBIN = $(BINDIR)/boot.bin
DISKIMG = disk.img

# Tools
ASM = nasm
ASMFLAGS = -f bin
QEMU = qemu-system-i386
QEMUFLAGS = -drive format=raw,file=$(DISKIMG)

# Terminal colors for output
RED = \033[0;31m
GREEN = \033[0;32m
YELLOW = \033[1;33m
NC = \033[0m # No Color

.PHONY: all run debug clean help install-deps

# Default target
all: $(DISKIMG)
	@echo "$(GREEN)✓ Build complete!$(NC)"
	@echo "Run 'make run' to start the bootloader"

# Create output directory
$(BINDIR):
	@echo "$(YELLOW)Creating output directory...$(NC)"
	@mkdir -p $(BINDIR)

# Assemble bootloader
$(BOOTBIN): boot.asm | $(BINDIR)
	@echo "$(YELLOW)Assembling bootloader...$(NC)"
	@$(ASM) $(ASMFLAGS) $< -o $@
	@echo "$(GREEN)✓ Assembly complete$(NC)"
	@echo "Size: $$(stat -c%s $@) bytes (max 512)"
	@if [ $$(stat -c%s $@) -gt 512 ]; then \
		echo "$(RED)✗ Error: Bootloader exceeds 512 bytes!$(NC)"; \
		exit 1; \
	fi

# Create disk image
$(DISKIMG): $(BOOTBIN)
	@echo "$(YELLOW)Creating disk image...$(NC)"
	@cp $(BOOTBIN) $(DISKIMG)
	@# Optionally pad to standard floppy size
	@# dd if=/dev/zero of=$(DISKIMG) bs=512 count=2880 2>/dev/null
	@# dd if=$(BOOTBIN) of=$(DISKIMG) bs=512 count=1 conv=notrunc 2>/dev/null
	@echo "$(GREEN)✓ Disk image ready$(NC)"

# Run with QEMU
run: $(DISKIMG)
	@echo "$(YELLOW)Starting QEMU...$(NC)"
	@echo "Controls: Arrow keys to navigate, Ctrl+C to exit"
	@$(QEMU) $(QEMUFLAGS)

# Run with debugging
debug: $(DISKIMG)
	@echo "$(YELLOW)Starting QEMU in debug mode...$(NC)"
	@echo "Connect GDB with: target remote localhost:1234"
	@$(QEMU) -s -S $(QEMUFLAGS)

# Run with monitor
monitor: $(DISKIMG)
	@echo "$(YELLOW)Starting QEMU with monitor...$(NC)"
	@$(QEMU) -monitor stdio $(QEMUFLAGS)

# Disassemble the binary
disasm: $(BOOTBIN)
	@echo "$(YELLOW)Disassembling bootloader...$(NC)"
	@ndisasm -b 16 -o 0x7c00 $(BOOTBIN) | less

# Hexdump the binary
hexdump: $(BOOTBIN)
	@hexdump -C $(BOOTBIN) | less

# Check boot signature
check: $(BOOTBIN)
	@echo "$(YELLOW)Checking boot signature...$(NC)"
	@if hexdump -s 510 -n 2 -e '1/2 "%04x"' $(BOOTBIN) | grep -q "aa55"; then \
		echo "$(GREEN)✓ Valid boot signature found (0xAA55)$(NC)"; \
	else \
		echo "$(RED)✗ Invalid boot signature!$(NC)"; \
		exit 1; \
	fi

# Clean build artifacts
clean:
	@echo "$(YELLOW)Cleaning build artifacts...$(NC)"
	@rm -rf $(BINDIR) $(DISKIMG) *.log 2>/dev/null || true
	@echo "$(GREEN)✓ Clean complete$(NC)"

# Install dependencies
install-deps:
	@echo "$(YELLOW)Installing dependencies...$(NC)"
	@if command -v apt-get >/dev/null 2>&1; then \
		sudo apt-get update && sudo apt-get install -y nasm qemu-system-x86 hexedit; \
	elif command -v yum >/dev/null 2>&1; then \
		sudo yum install -y nasm qemu-system-x86; \
	elif command -v brew >/dev/null 2>&1; then \
		brew install nasm qemu; \
	else \
		echo "$(RED)Please install nasm and qemu manually$(NC)"; \
		exit 1; \
	fi
	@echo "$(GREEN)✓ Dependencies installed$(NC)"

# Create bootable USB (dangerous!)
usb: $(DISKIMG)
	@echo "$(RED)WARNING: This will overwrite the boot sector of the selected device!$(NC)"
	@echo "Available devices:"
	@lsblk -d -o NAME,SIZE,TYPE,MOUNTPOINT | grep -E "disk|usb"
	@echo ""
	@read -p "Enter device (e.g., sdb): " device; \
	if [ -z "$$device" ]; then \
		echo "$(RED)No device specified$(NC)"; \
		exit 1; \
	fi; \
	echo "$(YELLOW)Writing to /dev/$$device...$(NC)"; \
	sudo dd if=$(DISKIMG) of=/dev/$$device bs=512 count=1
	@echo "$(GREEN)✓ Bootable USB created$(NC)"

# Help target
help:
	@echo "$(GREEN)x86 Bootloader Makefile$(NC)"
	@echo ""
	@echo "$(YELLOW)Targets:$(NC)"
	@echo "  all          - Build the bootloader (default)"
	@echo "  run          - Run bootloader in QEMU"
	@echo "  debug        - Run with GDB server"
	@echo "  monitor      - Run with QEMU monitor"
	@echo "  disasm       - Disassemble the binary"
	@echo "  hexdump      - Show hex dump"
	@echo "  check        - Verify boot signature"
	@echo "  clean        - Remove build artifacts"
	@echo "  install-deps - Install required tools"
	@echo "  usb          - Create bootable USB (careful!)"
	@echo "  help         - Show this help"
	@echo ""
	@echo "$(YELLOW)Examples:$(NC)"
	@echo "  make         - Build bootloader"
	@echo "  make run     - Build and run"
	@echo "  make clean   - Clean project"
	@echo ""
	@echo "$(YELLOW)Requirements:$(NC)"
	@echo "  - NASM assembler"
	@echo "  - QEMU emulator"
	@echo "  - 512 bytes max size"

# Statistics about the code
stats: $(BOOTBIN)
	@echo "$(YELLOW)Bootloader Statistics:$(NC)"
	@echo "Size: $$(stat -c%s $(BOOTBIN)) / 512 bytes ($$(echo "scale=1; $$(stat -c%s $(BOOTBIN)) * 100 / 512" | bc)% used)"
	@echo "Lines of code: $$(wc -l < boot.asm)"
	@echo "Instructions: $$(grep -c -E '^\s*(mov|add|sub|cmp|jmp|je|jne|loop|int|push|pop|xor|rep|stosw|stosb|movsb)' boot.asm)"
	@echo "BIOS calls: $$(grep -c 'int 0x' boot.asm)"
	@echo "Labels: $$(grep -c ':' boot.asm)"
