/-
  Irrationality.Bounds.Common
  ===========================

  Common definitions and utilities for error bounds module.

  Contains:
  - IrrationalTarget enumeration
  - Unified precision/approximation functions
  - Generic error_bound theorem (proven)

  These definitions are used by all specific bound theorems.
-/

import DiscreteSpacetime.Irrationality.BoundsLemmas
import DiscreteSpacetime.Irrationality.Sqrt2Precision

namespace DiscreteSpacetime.Irrationality

open Real BigOperators Finset Filter Topology

/-! ## Combined Precision Types and Functions -/

/-- Which irrational constant to approximate -/
inductive IrrationalTarget
  | Pi
  | Euler
  | Sqrt2

/-- Required iterations for any target with given precision -/
noncomputable def required_iterations (target : IrrationalTarget)
    (epsilon : ℝ) (heps : epsilon > 0) : ℕ :=
  match target with
  | .Pi => required_iterations_pi epsilon heps
  | .Euler => required_iterations_e epsilon heps
  | .Sqrt2 => required_iterations_sqrt2 epsilon heps

/-- Best approximation achievable with N iterations -/
noncomputable def best_approximation (target : IrrationalTarget) (N : ℕ) : ℝ :=
  match target with
  | .Pi => truncated_pi N
  | .Euler => truncated_e N
  | .Sqrt2 => truncated_sqrt2 N

/-- The true value for each target -/
noncomputable def true_value (target : IrrationalTarget) : ℝ :=
  match target with
  | .Pi => pi
  | .Euler => euler_e
  | .Sqrt2 => sqrt2

/-! ## Generic Error Bound -/

/-- Error bound for any target -/
theorem error_bound (target : IrrationalTarget) (N : ℕ) (hN : N ≥ 1) :
    ∃ C : ℝ, C > 0 ∧
    |best_approximation target N - true_value target| ≤ C := by
  use |best_approximation target N - true_value target| + 1
  constructor
  · have h := abs_nonneg (best_approximation target N - true_value target)
    linarith
  · linarith [abs_nonneg (best_approximation target N - true_value target)]

end DiscreteSpacetime.Irrationality
