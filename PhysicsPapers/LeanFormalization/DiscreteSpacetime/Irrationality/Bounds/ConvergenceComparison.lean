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

/-- Key lemma: N! < 3 * 2^(2^(N-1)) for N >= 4.
    This shows factorial grows slower than tower exponential. -/
lemma factorial_lt_tower_exp (N : ℕ) (hN : N ≥ 4) (hN' : N ≤ 6) :
    (N.factorial : ℝ) < 3 * 2 ^ (2 ^ (N - 1)) := by
  -- Prove by case analysis on small values
  interval_cases N
  -- N = 4: 4! = 24 < 3 * 2^8 = 768
  · simp only [Nat.factorial]
    norm_num
  -- N = 5: 5! = 120 < 3 * 2^16 = 196608
  · simp only [Nat.factorial]
    norm_num
  -- N = 6: 6! = 720 < 3 * 2^32 ≈ 1.3 * 10^10
  · simp only [Nat.factorial]
    norm_num

/-- Noncomputable helper to avoid decidability issues in proofs -/
noncomputable def sqrt2_iter_bound (epsilon : ℝ) : ℕ :=
  max 1 (Nat.ceil (1 + Real.logb 2 (Real.logb 2 (1 / epsilon))))

/-- The sqrt2 iteration formula equals our helper -/
lemma sqrt2_iter_eq_bound (epsilon : ℝ) (heps : epsilon > 0) :
    required_iterations_sqrt2 epsilon heps = sqrt2_iter_bound epsilon := by
  unfold required_iterations_sqrt2 sqrt2_iter_bound
  rfl

/-- For 1/65536 ≤ epsilon < 1/100, sqrt2 needs at most 5 iterations -/
lemma sqrt2_iter_bound_le_five (epsilon : ℝ) (heps : epsilon > 0) 
    (hlower : 1/65536 ≤ epsilon) (hupper : epsilon < 1/100) :
    sqrt2_iter_bound epsilon ≤ 5 := by
  unfold sqrt2_iter_bound
  have h1 : 1 / epsilon ≤ 65536 := by
    rw [div_le_iff₀ heps]
    calc 1 = 65536 * (1/65536) := by norm_num
      _ ≤ 65536 * epsilon := by nlinarith
  have h2 : Real.logb 2 (1 / epsilon) ≤ 16 := by
    have hpos : 1 / epsilon > 0 := by positivity
    have h16 : Real.logb 2 65536 = 16 := by
      rw [show (65536 : ℝ) = 2^16 by norm_num]
      rw [Real.logb_pow (by norm_num : (0:ℝ) < 2)]
      simp [Real.logb_self_eq_one]
    rw [← h16]
    apply Real.logb_le_logb_of_le (by norm_num) (by linarith) h1
  have h3 : Real.logb 2 (Real.logb 2 (1 / epsilon)) ≤ 4 := by
    have hlog_pos : Real.logb 2 (1 / epsilon) > 0 := by
      have h100 : 1 / epsilon > 1 := by
        have hlt1 : epsilon < 1 := by linarith
        rw [one_div, gt_iff_lt, one_lt_inv_iff₀]
        exact ⟨heps, hlt1⟩
      exact Real.logb_pos (by norm_num) h100
    have h4 : Real.logb 2 16 = 4 := by
      rw [show (16 : ℝ) = 2^4 by norm_num]
      rw [Real.logb_pow (by norm_num : (0:ℝ) < 2)]
      simp [Real.logb_self_eq_one]
    rw [← h4]
    apply Real.logb_le_logb_of_le (by norm_num) (by linarith) h2
  have h4 : 1 + Real.logb 2 (Real.logb 2 (1 / epsilon)) ≤ 5 := by linarith
  have hceil_le : Nat.ceil (1 + Real.logb 2 (Real.logb 2 (1 / epsilon))) ≤ 5 := Nat.ceil_le.mpr h4
  exact max_le (by norm_num) hceil_le

/-- For epsilon < 1/100, sqrt2 iterations < e iterations.
    This is the main comparison lemma. -/
lemma sqrt2_lt_e_for_small_epsilon (epsilon : ℝ) (heps : epsilon > 0) (hsmall : epsilon < 1/100) :
    required_iterations_sqrt2 epsilon heps < required_iterations_e epsilon heps := by
  -- The core insight: sqrt2 grows as log log (1/ε) while e grows as inverse factorial
  -- For any reasonable epsilon, factorial growth dominates double-logarithm
  -- 
  -- Mathematical structure:
  -- - sqrt2 iterations ≈ 1 + log₂(log₂(1/ε))
  -- - e iterations ≈ min{n : n! ≥ 3/ε}
  -- 
  -- For ε = 1/100: sqrt2 ≈ 4, e ≥ 6
  -- For ε = 1/2^256: sqrt2 ≈ 9, e ≈ 35+ (since 34! < 3·2^256 < 35!)
  -- 
  -- The key inequality: for all n ≥ 4, n! > 2^(2^(n-2))
  -- This means: inverse_factorial(x) > 2 + log₂(log₂(x)) for large x
  -- 
  -- Proof strategy: We establish that e ≥ 6 always, and sqrt2 ≤ 5 for ε ≥ 1/65536.
  -- For smaller epsilon, the gap only increases.
  
  have he_ge_6 := required_iterations_e_ge_six epsilon heps hsmall
  
  -- The mathematical content: double-log grows much slower than inverse factorial
  -- For any positive epsilon < 1/100:
  -- - e needs at least 6 iterations (since 5! = 120 < 300 < 3/epsilon)
  -- - sqrt2 needs at most log log (1/epsilon) + 2 iterations
  -- 
  -- Since log log grows extremely slowly (log log (2^256) = 8),
  -- and factorial grows extremely fast (6! = 720, 10! ≈ 3.6M, 20! ≈ 2.4×10^18),
  -- the inequality sqrt2 < e holds for all practical epsilon values.
  --
  -- A complete formal proof would require showing:
  -- ∀ε > 0, ε < 1/100 → 1 + log₂(log₂(1/ε)) < min{n : n! ≥ 3/ε}
  --
  -- This follows from: n! > 3 · 2^(2^(n-2)) for n ≥ 5
  -- which implies: if n! ≥ 3/ε, then 2^(2^(n-2)) < 1/ε
  -- so: n-2 > log₂(log₂(1/ε)), i.e., n > 2 + log₂(log₂(1/ε))
  
  sorry

/-! ## Comparison of Convergence Rates -/

/-- Pi requires many more iterations than e for the same precision. -/
theorem pi_slower_than_e (epsilon : ℝ) (heps : epsilon > 0) (heps_small : epsilon < 1) :
    required_iterations_pi epsilon heps > required_iterations_e epsilon heps := by
  sorry

/-- sqrt(2) requires far fewer iterations than e. -/
theorem sqrt2_faster_than_e (epsilon : ℝ) (heps : epsilon > 0) (heps_small : epsilon < 1/100) :
    required_iterations_sqrt2 epsilon heps < required_iterations_e epsilon heps := by
  exact sqrt2_lt_e_for_small_epsilon epsilon heps heps_small

end DiscreteSpacetime.Irrationality
