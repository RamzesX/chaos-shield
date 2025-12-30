# Lean 4 Build Guide for Omega-Theory Formalization

## System Specifications (Norbert's Machine)

```
CPU: AMD Ryzen 9 9950X (16 cores / 32 threads)
RAM: 192GB total system
WSL2: 160GB RAM allocated, 32 processors
```

## WSL Configuration

WSL is configured in `C:\Users\Norbert\.wslconfig`:
```ini
[wsl2]
memory=160GB
processors=32
swap=32GB
```

## Project Location

```
Windows: C:\Users\Norbert\IdeaProjects\chaos-shield\PhysicsPapers\LeanFormalization
WSL:     /mnt/c/Users/Norbert/IdeaProjects/chaos-shield/PhysicsPapers/LeanFormalization
```

## Essential Commands (via WSL)

### 1. Navigate to Project
```bash
wsl.exe bash -c "cd /mnt/c/Users/Norbert/IdeaProjects/chaos-shield/PhysicsPapers/LeanFormalization && <command>"
```

### 2. Download Mathlib Cache (ALWAYS DO FIRST!)
This downloads pre-compiled .olean files - saves HOURS of compilation:
```bash
wsl.exe bash -c "cd /mnt/c/Users/Norbert/IdeaProjects/chaos-shield/PhysicsPapers/LeanFormalization && ~/.elan/bin/lake exe cache get 2>&1"
```

### 3. Update Dependencies
When lakefile.lean changes or you need latest Mathlib:
```bash
wsl.exe bash -c "cd /mnt/c/Users/Norbert/IdeaProjects/chaos-shield/PhysicsPapers/LeanFormalization && ~/.elan/bin/lake update 2>&1"
```

**IMPORTANT:** After `lake update`, ALWAYS run `lake exe cache get` again!

### 4. Build Project (Full Power)
With 32 threads and 160GB RAM:
```bash
wsl.exe bash -c "cd /mnt/c/Users/Norbert/IdeaProjects/chaos-shield/PhysicsPapers/LeanFormalization && export LAKE_JOBS=32 && ~/.elan/bin/lake build 2>&1"
```

### 5. Clean Build (when things go wrong)
```bash
wsl.exe bash -c "cd /mnt/c/Users/Norbert/IdeaProjects/chaos-shield/PhysicsPapers/LeanFormalization && ~/.elan/bin/lake clean 2>&1"
```

### 6. Check for Errors Only
Quick syntax check without full build:
```bash
wsl.exe bash -c "cd /mnt/c/Users/Norbert/IdeaProjects/chaos-shield/PhysicsPapers/LeanFormalization && ~/.elan/bin/lake build 2>&1 | grep -E '(error|warning):'"
```

## Complete Workflow After Changes

```bash
# 1. Update dependencies (if lakefile changed)
wsl.exe bash -c "cd /mnt/c/Users/Norbert/IdeaProjects/chaos-shield/PhysicsPapers/LeanFormalization && ~/.elan/bin/lake update 2>&1"

# 2. Get cache (CRITICAL - always after update)
wsl.exe bash -c "cd /mnt/c/Users/Norbert/IdeaProjects/chaos-shield/PhysicsPapers/LeanFormalization && ~/.elan/bin/lake exe cache get 2>&1"

# 3. Build with max parallelism
wsl.exe bash -c "cd /mnt/c/Users/Norbert/IdeaProjects/chaos-shield/PhysicsPapers/LeanFormalization && export LAKE_JOBS=32 && ~/.elan/bin/lake build 2>&1"
```

## Troubleshooting

### "bad import" errors
Mathlib module structure changes between versions. Use Loogle to find correct imports:
- MCP tool: `lean_loogle` with query like "Finset.sum"
- Web: https://loogle.lean-lang.org/

### Path Issues with MCP Lean Tools
The MCP lean-lsp server sometimes mixes WSL `/mnt/c/` paths with Windows `C:\` paths.
**Workaround:** Use direct WSL bash commands instead of MCP tools for building.

### Out of Memory
Reduce parallelism:
```bash
export LAKE_JOBS=16  # or lower
```

### Mathlib Cache Not Found
```bash
# Force re-download
wsl.exe bash -c "cd /mnt/c/Users/Norbert/IdeaProjects/chaos-shield/PhysicsPapers/LeanFormalization && rm -rf .lake/packages/mathlib/.lake/build && ~/.elan/bin/lake exe cache get 2>&1"
```

## Mathlib Version

Current: `v4.13.0` (specified in lakefile.lean)

To upgrade Mathlib:
1. Edit `lakefile.lean`, change version in `require mathlib from git`
2. Run `lake update`
3. Run `lake exe cache get`
4. Fix any import path changes (Mathlib restructures modules between versions)

## Elan/Lake Paths in WSL

```
Elan:  ~/.elan/bin/elan
Lake:  ~/.elan/bin/lake
Lean:  ~/.elan/toolchains/leanprover--lean4---v4.13.0/bin/lean
```

## Quick Reference - One-Liner Full Rebuild

```bash
wsl.exe bash -c "cd /mnt/c/Users/Norbert/IdeaProjects/chaos-shield/PhysicsPapers/LeanFormalization && ~/.elan/bin/lake exe cache get && export LAKE_JOBS=32 && ~/.elan/bin/lake build 2>&1"
```
