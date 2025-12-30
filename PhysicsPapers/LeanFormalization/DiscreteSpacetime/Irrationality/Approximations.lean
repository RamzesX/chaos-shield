/-
  Irrationality.Approximations
  ============================

  Truncated series approximations for fundamental irrational constants.

  This module defines computable approximations to irrational numbers that
  appear in physical calculations. The key physics insight is that no finite
  computation can produce an exact irrational -- only truncated approximations.

  Series defined:
  - truncated_pi N:    Leibniz series 4 * sum_{k=0}^{N} (-1)^k / (2k+1)
  - truncated_e N:     Taylor series sum_{k=0}^{N} 1/k!
  - truncated_sqrt2 N: Newton-Raphson iterations for sqrt(2)

  These approximations converge to their targets as N -> infinity.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order

namespace DiscreteSpacetime.Irrationality

open BigOperators Finset Real Filter Topology

/-! ## Fundamental Constants from Mathlib -/

/-- Pi from Mathlib: the ratio of circumference to diameter -/
noncomputable abbrev pi : ℝ := Real.pi

/-- Euler's number e from Mathlib: exp(1) -/
noncomputable abbrev euler_e : ℝ := Real.exp 1

/-- Square root of 2 from Mathlib -/
noncomputable abbrev sqrt2 : ℝ := Real.sqrt 2

/-! ## Pi Approximation via Leibniz Series

    The Leibniz formula: pi/4 = 1 - 1/3 + 1/5 - 1/7 + ...
    Therefore: pi = 4 * sum_{k=0}^{infinity} (-1)^k / (2k+1)

    Truncating at N terms gives an approximation with bounded error.
-/

/-- Single term of the Leibniz series: (-1)^k / (2k+1) -/
noncomputable def leibniz_term (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k / (2 * k + 1)

/-- Truncated Leibniz series for pi/4 with N+1 terms -/
noncomputable def truncated_pi_quarter (N : ℕ) : ℝ :=
  ∑ k ∈ range (N + 1), leibniz_term k

/-- Truncated approximation to pi using Leibniz series.
    truncated_pi N = 4 * sum_{k=0}^{N} (-1)^k / (2k+1) -/
noncomputable def truncated_pi (N : ℕ) : ℝ :=
  4 * truncated_pi_quarter N

/-- First few values for reference:
    truncated_pi 0 = 4 * 1 = 4
    truncated_pi 1 = 4 * (1 - 1/3) = 8/3 ~ 2.67
    truncated_pi 2 = 4 * (1 - 1/3 + 1/5) = 52/15 ~ 3.47
    truncated_pi 100 ~ 3.1315... -/

theorem truncated_pi_zero : truncated_pi 0 = 4 := by
  simp [truncated_pi, truncated_pi_quarter, leibniz_term]

theorem truncated_pi_one : truncated_pi 1 = 8 / 3 := by
  -- 4 * (1 - 1/3) = 4 * (2/3) = 8/3
  simp only [truncated_pi, truncated_pi_quarter, leibniz_term]
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_empty]
  norm_num

/-! ## Euler's Number Approximation via Taylor Series

    The Taylor series for e: e = sum_{k=0}^{infinity} 1/k!

    This converges exponentially fast since k! grows super-exponentially.
-/

/-- Single term of Taylor series for e: 1/k! -/
noncomputable def taylor_e_term (k : ℕ) : ℝ :=
  1 / (k.factorial : ℝ)

/-- Truncated Taylor series for e with N+1 terms.
    truncated_e N = sum_{k=0}^{N} 1/k! -/
noncomputable def truncated_e (N : ℕ) : ℝ :=
  ∑ k ∈ range (N + 1), taylor_e_term k

/-- First few values:
    truncated_e 0 = 1
    truncated_e 1 = 1 + 1 = 2
    truncated_e 2 = 1 + 1 + 1/2 = 2.5
    truncated_e 5 ~ 2.7166...
    truncated_e 10 ~ 2.7182818... (7 correct digits!) -/

theorem truncated_e_zero : truncated_e 0 = 1 := by
  simp [truncated_e, taylor_e_term]

theorem truncated_e_one : truncated_e 1 = 2 := by
  -- 1/0! + 1/1! = 1 + 1 = 2
  simp only [truncated_e, taylor_e_term]
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_empty]
  norm_num [Nat.factorial]

theorem truncated_e_two : truncated_e 2 = 5 / 2 := by
  -- 1/0! + 1/1! + 1/2! = 1 + 1 + 1/2 = 5/2
  simp only [truncated_e, taylor_e_term]
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_empty]
  norm_num [Nat.factorial]

/-! ## Square Root of 2 via Newton-Raphson

    Newton-Raphson for f(x) = x^2 - 2:
    x_{n+1} = x_n - f(x_n)/f'(x_n) = x_n - (x_n^2 - 2)/(2*x_n)
            = (x_n + 2/x_n) / 2

    Starting from x_0 = 1, this converges quadratically to sqrt(2).
-/

/-- Single Newton-Raphson iteration for sqrt(2).
    Given x > 0, returns (x + 2/x) / 2 which is closer to sqrt(2). -/
noncomputable def newton_sqrt2_step (x : ℝ) : ℝ :=
  (x + 2 / x) / 2

/-- N iterations of Newton-Raphson starting from 1.
    truncated_sqrt2 0 = 1
    truncated_sqrt2 1 = (1 + 2/1) / 2 = 3/2 = 1.5
    truncated_sqrt2 2 = (3/2 + 2/(3/2)) / 2 = 17/12 ~ 1.4166...
    truncated_sqrt2 3 = 577/408 ~ 1.41421568... (5 correct digits)
    Quadratic convergence: digits approximately double each iteration. -/
noncomputable def truncated_sqrt2 : ℕ → ℝ
  | 0 => 1
  | n + 1 => newton_sqrt2_step (truncated_sqrt2 n)

theorem truncated_sqrt2_zero : truncated_sqrt2 0 = 1 := rfl

theorem truncated_sqrt2_one : truncated_sqrt2 1 = 3 / 2 := by
  simp [truncated_sqrt2, newton_sqrt2_step]
  ring

theorem truncated_sqrt2_two : truncated_sqrt2 2 = 17 / 12 := by
  simp [truncated_sqrt2, newton_sqrt2_step]
  ring

/-! ## Positivity of Approximations -/

/-- All truncated e approximations are positive -/
theorem truncated_e_pos (N : ℕ) : truncated_e N > 0 := by
  unfold truncated_e
  apply Finset.sum_pos
  · intro k _
    unfold taylor_e_term
    apply div_pos one_pos
    exact Nat.cast_pos.mpr (Nat.factorial_pos k)
  · exact Finset.nonempty_range_succ

/-- Newton-Raphson iterates are always positive (starting from positive) -/
theorem truncated_sqrt2_pos (N : ℕ) : truncated_sqrt2 N > 0 := by
  induction N with
  | zero => norm_num [truncated_sqrt2]
  | succ n ih =>
    simp only [truncated_sqrt2, newton_sqrt2_step]
    have h1 : truncated_sqrt2 n > 0 := ih
    have h2 : (2 : ℝ) / truncated_sqrt2 n > 0 := div_pos (by norm_num) h1
    have h3 : truncated_sqrt2 n + 2 / truncated_sqrt2 n > 0 := by linarith
    exact div_pos h3 (by norm_num : (2 : ℝ) > 0)

/-! ## Convergence Theorems

    These establish that the truncated series converge to their targets.
    The proofs use Mathlib's infinite sum machinery.
-/

/-- The Leibniz series converges to pi/4.
    PHYSICS INSIGHT: This is a statement about the infinite limit.
    At any finite N, we only have an approximation. -/
theorem leibniz_series_converges :
    Tendsto truncated_pi_quarter atTop (nhds (pi / 4)) := by
  sorry
  -- TODO: Use Mathlib's proof of Leibniz formula
  -- Key lemma: Real.tendsto_sum_pi_div_four_sub_one_div_two_mul_nat_add_one

/-- The Taylor series for e converges.
    This converges much faster than the Leibniz series (exponentially vs algebraically). -/
theorem taylor_e_series_converges :
    Tendsto truncated_e atTop (nhds euler_e) := by
  sorry
  -- TODO: Use Mathlib's Real.hasSum_exp
  -- Key: exp 1 = tsum (fun n => 1/n!)

/-- Newton-Raphson converges to sqrt(2) with quadratic rate.
    Each iteration approximately doubles the number of correct digits. -/
theorem newton_sqrt2_converges :
    Tendsto truncated_sqrt2 atTop (nhds sqrt2) := by
  sorry
  -- TODO: Standard Newton-Raphson convergence proof
  -- Key insight: |x_{n+1} - sqrt(2)| = |x_n - sqrt(2)|^2 / (2 * x_n)

/-! ## Monotonicity Properties -/

/-- Truncated e is monotonically increasing (all terms positive) -/
theorem truncated_e_mono : Monotone truncated_e := by
  intro m n hmn
  unfold truncated_e
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k _ _
    unfold taylor_e_term
    apply div_nonneg (by norm_num : (1 : ℝ) ≥ 0)
    exact Nat.cast_nonneg _

/-- Newton-Raphson iterates decrease toward sqrt(2) after the first step.
    For n >= 1, truncated_sqrt2 n >= sqrt2 and the sequence is decreasing. -/
theorem truncated_sqrt2_ge_target (n : ℕ) (hn : n ≥ 1) :
    truncated_sqrt2 n ≥ sqrt2 := by
  sorry
  -- TODO: Use AM-GM: (x + 2/x)/2 >= sqrt(x * 2/x) = sqrt(2)

theorem truncated_sqrt2_decreasing (n : ℕ) (hn : n ≥ 1) :
    truncated_sqrt2 (n + 1) ≤ truncated_sqrt2 n := by
  sorry
  -- TODO: Follows from truncated_sqrt2_ge_target and the iteration formula

/-! ## Alternative Approximation Methods

    For completeness, we note other methods exist:
    - Pi: Machin's formula, Chudnovsky algorithm, BBP formula
    - e: Continued fraction, binary splitting
    - sqrt(2): Continued fraction [1; 2, 2, 2, ...]
-/

/-- Machin's formula: pi/4 = 4*arctan(1/5) - arctan(1/239)
    Much faster convergence than Leibniz. -/
noncomputable def machin_pi : ℝ :=
  4 * (4 * Real.arctan (1/5) - Real.arctan (1/239))

theorem machin_formula : machin_pi = pi := by
  sorry
  -- TODO: Classic result, provable using arctan addition formulas

/-! ## Computational Budget Interpretation

    PHYSICS INSIGHT: The truncation index N represents a computational budget.
    - A physical system can only perform finite computations
    - At temperature T, there is a maximum N(T) achievable
    - This creates fundamental computational uncertainty

    The formalization of this connection is in Irrationality.Uncertainty
-/

/-- Type representing a computational budget (maximum iterations allowed) -/
structure ComputationalBudget where
  /-- Maximum number of iterations for series computations -/
  max_iterations : ℕ
  /-- Budget must be positive for meaningful computation -/
  budget_pos : max_iterations > 0

/-- Given a budget, compute the best pi approximation achievable -/
noncomputable def best_pi_with_budget (budget : ComputationalBudget) : ℝ :=
  truncated_pi (budget.max_iterations - 1)

/-- Given a budget, compute the best e approximation achievable -/
noncomputable def best_e_with_budget (budget : ComputationalBudget) : ℝ :=
  truncated_e (budget.max_iterations - 1)

/-- Given a budget, compute the best sqrt(2) approximation achievable -/
noncomputable def best_sqrt2_with_budget (budget : ComputationalBudget) : ℝ :=
  truncated_sqrt2 (budget.max_iterations - 1)

end DiscreteSpacetime.Irrationality
