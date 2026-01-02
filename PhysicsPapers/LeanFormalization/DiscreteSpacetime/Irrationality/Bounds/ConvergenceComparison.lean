/-
  Irrationality.Bounds.ConvergenceComparison
  ==========================================

  Comparison of convergence rates between different irrational approximations.

  Key theorems:
  1. pi_slower_than_e: Pi requires more iterations than e for same precision
  2. sqrt2_faster_than_e: sqrt(2) requires fewer iterations than e

  Mathematical intuition:
  - Pi (Leibniz): algebraic decay O(1/N)
  - e (Taylor): factorial decay O(1/N!)
  - sqrt2 (Newton): super-exponential decay O(1/2^(2^N))

  Difficulty: MODERATE
  - Requires comparing algebraic vs factorial vs super-exponential growth
  - May need explicit iteration count comparisons at specific epsilon values
-/

import DiscreteSpacetime.Irrationality.Bounds.Common

namespace DiscreteSpacetime.Irrationality

open Real BigOperators Finset Filter Topology

/-! ## Helper Lemmas for Iteration Comparison -/

/-- Factorial values for first few naturals -/
lemma factorial_five : (5 : ℕ).factorial = 120 := by native_decide

lemma factorial_six : (6 : ℕ).factorial = 720 := by native_decide

/-- For epsilon < 1/100, e requires at least 6 iterations because 5! = 120 < 300 < 3/epsilon -/
lemma required_iterations_e_ge_six (epsilon : ℝ) (heps : epsilon > 0) (hsmall : epsilon < 1/100) :
    required_iterations_e epsilon heps ≥ 6 := by
  -- Key: 3/epsilon > 300 > 5! = 120, so we need at least 6 iterations
  unfold required_iterations_e
  -- Show that for all n < 6, n! < 3/epsilon (i.e., n doesn't satisfy the predicate)
  have h3eps : 3 / epsilon > 300 := by
    have h1 : 1/epsilon > 100 := by
      have heps100 : epsilon < 1/100 := hsmall
      have h100pos : (0:ℝ) < 1/100 := by norm_num
      have := div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 1) heps heps100
      simp only [div_one] at this
      calc 1/epsilon > 1/(1/100) := this
        _ = 100 := by norm_num
    calc 3 / epsilon = 3 * (1/epsilon) := by ring
      _ > 3 * 100 := by nlinarith
      _ = 300 := by ring
  -- Use le_find_iff: 6 ≤ Nat.find h ↔ ∀ m < 6, ¬ p m
  rw [ge_iff_le, Nat.le_find_iff]
  intro m hm
  -- Need to show m! < 3/epsilon for m < 6
  simp only [not_le]
  -- All factorials for m < 6 are at most 5! = 120 < 300
  have hm_fact_le : (m.factorial : ℝ) ≤ 120 := by
    have h5fact : (5 : ℕ).factorial = 120 := by native_decide
    have hm_le_5 : m ≤ 5 := Nat.lt_succ_iff.mp hm
    have hfact_mono : m.factorial ≤ (5 : ℕ).factorial := Nat.factorial_le hm_le_5
    calc (m.factorial : ℝ) ≤ ((5 : ℕ).factorial : ℝ) := by exact_mod_cast hfact_mono
      _ = 120 := by rw [h5fact]; norm_num
  linarith

/-! ## Comparison of Convergence Rates -/

/-- Pi requires many more iterations than e for the same precision.

    Intuition: Pi uses Leibniz series with O(1/N) decay,
    while e uses Taylor series with O(1/N!) decay.
    For any epsilon, the number of iterations for pi grows like 1/epsilon,
    while for e it grows like log(1/epsilon).
-/
theorem pi_slower_than_e (epsilon : ℝ) (heps : epsilon > 0) (heps_small : epsilon < 1) :
    required_iterations_pi epsilon heps > required_iterations_e epsilon heps := by
  sorry
  -- MODERATE: Compare algebraic vs factorial decay
  --
  -- Key insight:
  -- - required_iterations_pi ~ (4/epsilon - 3)/2 ~ 2/epsilon
  -- - required_iterations_e ~ log_factorial(3/epsilon) which is much smaller
  --
  -- Approach:
  -- 1. For epsilon < 1, show 2/epsilon > some function of log(3/epsilon)
  -- 2. Use that N! grows faster than any polynomial
  -- 3. May need to establish concrete bounds for specific epsilon ranges

/-- sqrt(2) requires far fewer iterations than e.

    Intuition: Newton-Raphson has quadratic convergence (doubles precision each step),
    giving super-exponential decay O(1/2^(2^N)).
    Taylor series for e has factorial decay O(1/N!).
    Super-exponential beats factorial.
-/
theorem sqrt2_faster_than_e (epsilon : ℝ) (heps : epsilon > 0) (heps_small : epsilon < 1/100) :
    required_iterations_sqrt2 epsilon heps < required_iterations_e epsilon heps := by
  sorry
  -- MODERATE: Compare super-exponential vs factorial
  --
  -- Key insight:
  -- - required_iterations_sqrt2 ~ 1 + log_2(log_2(1/epsilon))
  -- - required_iterations_e ~ inverse_factorial(3/epsilon)
  --
  -- Approach:
  -- 1. Double logarithm grows much slower than inverse factorial
  -- 2. For epsilon < 1/100, we need:
  --    log_2(log_2(100)) ~ log_2(6.6) ~ 2.7 iterations for sqrt2
  --    But for e: 3*100 = 300, need N! ≥ 300, so N ≥ 6
  -- 3. Formalize this comparison

end DiscreteSpacetime.Irrationality
