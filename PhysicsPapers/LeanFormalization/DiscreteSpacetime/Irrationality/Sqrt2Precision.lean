/-
  Irrationality.Sqrt2Precision
  ============================

  Precision theorem for sqrt(2) Newton-Raphson approximation.

  Mathematical approach:
  - From sqrt2_error_bound: |truncated_sqrt2 N - sqrt2| ≤ 1/2^(2^(N-1)) for N ≥ 1
  - Need to show: 1/2^(2^(N-1)) ≤ epsilon
  - Equivalently: 2^(2^(N-1)) ≥ 1/epsilon
  - Taking log₂: 2^(N-1) ≥ log₂(1/epsilon)
  - Taking log₂ again: N-1 ≥ log₂(log₂(1/epsilon))
  - So: N ≥ 1 + log₂(log₂(1/epsilon))
-/

import DiscreteSpacetime.Irrationality.BoundsLemmas

namespace DiscreteSpacetime.Irrationality

open Real BigOperators Finset Filter Topology

/-! ## Helper Lemmas -/

/-- Two to any natural power is positive -/
lemma two_pow_nat_pos (n : ℕ) : (2 : ℝ) ^ n > 0 := by positivity

/-- Two to any natural power is at least 1 -/
lemma one_le_two_pow_nat (n : ℕ) : (1 : ℝ) ≤ 2 ^ n := by
  have h : (1 : ℝ) ≤ 2 := by norm_num
  calc (1 : ℝ) = 1 ^ n := (one_pow n).symm
    _ ≤ 2 ^ n := pow_le_pow_left (by norm_num) h n

/-- For positive x: 1/2^k ≤ x ↔ 1/x ≤ 2^k -/
lemma one_div_two_pow_le_iff {x : ℝ} (hx : x > 0) (k : ℕ) :
    1 / (2 : ℝ) ^ k ≤ x ↔ 1 / x ≤ 2 ^ k := by
  have h2k : (2 : ℝ) ^ k > 0 := two_pow_nat_pos k
  rw [div_le_iff h2k, div_le_iff hx]
  constructor <;> (intro h; linarith [mul_comm x ((2 : ℝ) ^ k)])

/-- 1 < 1/ε when 0 < ε < 1 -/
lemma one_lt_one_div {epsilon : ℝ} (heps : epsilon > 0) (heps1 : epsilon < 1) :
    1 < 1 / epsilon := by
  rw [lt_div_iff heps, one_mul]
  exact heps1

/-- Key lemma: if N ≥ 1 + log₂(log₂(1/ε)), then 1/2^(2^(N-1)) ≤ ε -/
lemma precision_from_logb_bound {epsilon : ℝ} (heps : epsilon > 0) 
    {N : ℕ} (hN1 : N ≥ 1)
    (hN : (N : ℝ) ≥ 1 + Real.logb 2 (Real.logb 2 (1 / epsilon))) :
    1 / (2 : ℝ) ^ (2 ^ (N - 1)) ≤ epsilon := by
  -- First handle the case where epsilon ≥ 1
  by_cases heps1 : epsilon ≥ 1
  · -- If epsilon ≥ 1, then 1/2^(2^(N-1)) ≤ 1 ≤ epsilon
    have h1 : 1 / (2 : ℝ) ^ (2 ^ (N - 1)) ≤ 1 := by
      rw [div_le_one (two_pow_nat_pos _)]
      exact one_le_two_pow_nat _
    linarith
  
  -- Now assume epsilon < 1
  push_neg at heps1
  
  -- 1/epsilon > 1
  have h1eps_gt_1 : 1 / epsilon > 1 := one_lt_one_div heps heps1
  have h1eps_pos : 1 / epsilon > 0 := by positivity
  
  -- log₂(1/epsilon) > 0
  have hlog1eps_pos : Real.logb 2 (1 / epsilon) > 0 := 
    Real.logb_pos (by norm_num) h1eps_gt_1
  
  -- From hN: N - 1 ≥ log₂(log₂(1/ε))
  have hN_sub : (N : ℝ) - 1 ≥ Real.logb 2 (Real.logb 2 (1 / epsilon)) := by linarith
  
  -- Positivity for rpow
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2ne1 : (2 : ℝ) ≠ 1 := by norm_num
  have h2gt1 : (1 : ℝ) < 2 := by norm_num
  have hrpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((N : ℝ) - 1) := Real.rpow_pos_of_pos h2pos _
  
  -- Key step 1: 2^(N-1) ≥ log₂(1/ε) using rpow
  have hpow_ge_log_rpow : (2 : ℝ) ^ ((N : ℝ) - 1) ≥ Real.logb 2 (1 / epsilon) := by
    rw [ge_iff_le, ← Real.logb_le_logb h2gt1 hlog1eps_pos hrpow_pos]
    calc Real.logb 2 (Real.logb 2 (1 / epsilon)) 
        ≤ (N : ℝ) - 1 := hN_sub
      _ = Real.logb 2 ((2 : ℝ) ^ ((N : ℝ) - 1)) := by
          rw [Real.logb_rpow h2pos h2ne1]
  
  -- Convert rpow to pow: (N : ℝ) - 1 = (N - 1 : ℕ) when N ≥ 1
  have hN_cast : (N : ℝ) - 1 = ((N - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hN1]
    ring
  
  -- 2^(N-1) as ℕ-power ≥ log₂(1/ε)
  have hpow_ge_log : (2 : ℝ) ^ (N - 1 : ℕ) ≥ Real.logb 2 (1 / epsilon) := by
    have h := hpow_ge_log_rpow
    rw [hN_cast, Real.rpow_natCast] at h
    exact h
  
  -- Positivity for the double power (using pow, not rpow)
  have hdouble_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ (N - 1) : ℕ) := 
    two_pow_nat_pos _
  
  -- Key step 2: 2^(2^(N-1)) ≥ 1/ε
  have hdouble_pow : (2 : ℝ) ^ (2 ^ (N - 1) : ℕ) ≥ 1 / epsilon := by
    -- We need: 1/ε ≤ 2^(2^(N-1))
    -- Equivalent to: log₂(1/ε) ≤ 2^(N-1)
    rw [ge_iff_le, ← Real.logb_le_logb h2gt1 h1eps_pos hdouble_pow_pos]
    calc Real.logb 2 (1 / epsilon)
        ≤ (2 : ℝ) ^ (N - 1 : ℕ) := hpow_ge_log
      _ = ((2 ^ (N - 1) : ℕ) : ℝ) := by norm_cast
      _ = Real.logb 2 ((2 : ℝ) ^ (2 ^ (N - 1) : ℕ)) := by
          rw [Real.logb_pow, Real.logb_self_eq_one h2gt1, mul_one] <;> norm_num
  
  -- Final step: 1/2^(2^(N-1)) ≤ ε
  rw [one_div_two_pow_le_iff heps]
  calc 1 / epsilon ≤ (2 : ℝ) ^ (2 ^ (N - 1) : ℕ) := hdouble_pow
    _ = 2 ^ (2 ^ (N - 1)) := rfl

/-! ## Main Precision Theorem -/

/-- To achieve |truncated_sqrt2 N - sqrt2| ≤ epsilon, we need N ≥ required_iterations_sqrt2. -/
theorem sqrt2_precision_achieved (epsilon : ℝ) (heps : epsilon > 0)
    (N : ℕ) (hN : N ≥ required_iterations_sqrt2 epsilon heps) :
    |truncated_sqrt2 N - sqrt2| ≤ epsilon := by
  -- First establish N ≥ 1
  have hN1 : N ≥ 1 := by
    calc N ≥ required_iterations_sqrt2 epsilon heps := hN
      _ = max 1 (Nat.ceil (1 + Real.logb 2 (Real.logb 2 (1 / epsilon)))) := rfl
      _ ≥ 1 := le_max_left _ _
  
  -- Use sqrt2_error_bound
  have hbound := sqrt2_error_bound N hN1
  
  -- Show N ≥ 1 + log₂(log₂(1/ε))
  have hN_real : (N : ℝ) ≥ 1 + Real.logb 2 (Real.logb 2 (1 / epsilon)) := by
    have hceil := Nat.le_ceil (1 + Real.logb 2 (Real.logb 2 (1 / epsilon)))
    have h1 : N ≥ max 1 (Nat.ceil (1 + Real.logb 2 (Real.logb 2 (1 / epsilon)))) := hN
    have h2 : N ≥ Nat.ceil (1 + Real.logb 2 (Real.logb 2 (1 / epsilon))) := by
      calc N ≥ max 1 (Nat.ceil (1 + Real.logb 2 (Real.logb 2 (1 / epsilon)))) := h1
        _ ≥ Nat.ceil (1 + Real.logb 2 (Real.logb 2 (1 / epsilon))) := le_max_right _ _
    calc (N : ℝ) 
        ≥ (Nat.ceil (1 + Real.logb 2 (Real.logb 2 (1 / epsilon))) : ℕ) := by exact_mod_cast h2
      _ ≥ 1 + Real.logb 2 (Real.logb 2 (1 / epsilon)) := hceil
  
  have hprec := precision_from_logb_bound heps hN1 hN_real
  
  calc |truncated_sqrt2 N - sqrt2| 
      ≤ 1 / 2 ^ (2 ^ (N - 1)) := hbound
    _ ≤ epsilon := hprec

end DiscreteSpacetime.Irrationality
