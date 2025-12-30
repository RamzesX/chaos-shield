# Building Omega-Theory Lean Formalization

## Prerequisites

- WSL2 with Ubuntu
- Elan (Lean version manager) installed in WSL
- Mathlib cache tool

## Quick Start

```bash
# From Windows CMD/PowerShell - full rebuild with 32 threads
wsl.exe bash -c "cd /mnt/c/Users/Norbert/IdeaProjects/chaos-shield/PhysicsPapers/LeanFormalization && ~/.elan/bin/lake exe cache get && export LAKE_JOBS=32 && ~/.elan/bin/lake build 2>&1"
```

## Step by Step

### 1. Get Mathlib Cache (saves hours!)
```bash
lake exe cache get
```

### 2. Build
```bash
export LAKE_JOBS=32  # Use all cores
lake build
```

### 3. After Updating Dependencies
```bash
lake update
lake exe cache get  # ALWAYS after update!
lake build
```

## Project Structure

```
DiscreteSpacetime/
  Basic/          - Constants, Lattice, Operators
  Axioms/         - Physical postulates
  Geometry/       - Metric, Connection, Curvature, Torsion
  Dynamics/       - Healing flow, Defects, Stability
  Conservation/   - Noether, FourthLaw, SpinInformation
  Torsion/        - SpinTorsion, BigBounce (Poplawski)
  Emergence/      - ContinuumLimit, EinsteinEmergence
  Irrationality/  - Computational bounds from truncated irrationals
  Variational/    - GraphAction, DiscreteNoether, InformationGeodesics
```

## Mathlib Version

v4.13.0 - see lakefile.lean

## Troubleshooting

See `.claude/lean-build-guide.md` for detailed troubleshooting.
