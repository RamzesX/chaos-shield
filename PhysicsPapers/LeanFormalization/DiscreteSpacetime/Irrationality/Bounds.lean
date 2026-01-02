/-
  Irrationality.Bounds
  ====================

  Main error bounds module - re-exports all bound submodules.

  This module re-exports:
  - Bounds.Common: Shared definitions (IrrationalTarget, etc.)
  - Bounds.TightBound: Tighter Euler error bound (HARD)
  - Bounds.ConvergenceComparison: Rate comparisons (MODERATE)
  - Bounds.PrecisionHierarchy: Combined precision theorem (HARD)

  Plus re-exports from BoundsLemmas and Sqrt2Precision:
  - Basic error bounds (pi, e, sqrt2)
  - Precision achievement theorems
  - Convergence to zero theorems

  Usage:
    import DiscreteSpacetime.Irrationality.Bounds
    -- This gives access to all bound-related definitions and theorems
-/

-- Re-export all submodules
import DiscreteSpacetime.Irrationality.Bounds.Common
import DiscreteSpacetime.Irrationality.Bounds.TightBound
import DiscreteSpacetime.Irrationality.Bounds.ConvergenceComparison
import DiscreteSpacetime.Irrationality.Bounds.PrecisionHierarchy
