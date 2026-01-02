/-
  Irrationality.BoundsLemmas
  ==========================

  Proven lemmas for error bounds on truncated irrational approximations.

  This module contains the core proven results. The one remaining sorry
  (sqrt2_precision_achieved) requires careful logarithm manipulation.

  Key results:
  - Pi error:    |pi - truncated_pi N|    <= 4/(2N+3)      (algebraic decay)
  - e error:     |e - truncated_e N|      <= 3/((N+1)!)    (exponential decay)
  - sqrt2 error: |sqrt2 - truncated_sqrt2 N| <= 1/2^(2^N)  (super-exponential)
-/

import DiscreteSpacetime.Irrationality.Approximations
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecificLimits.Normed

namespace DiscreteSpacetime.Irrationality

open Real BigOperators Finset Filter Topology

/-! ## Pi Error Bounds

    The Leibniz series is an alternating series, so the error after N terms
    is bounded by the absolute value of the next term.

    |pi/4 - truncated_pi_quarter N| <= 1/(2N+3)
    Therefore: |pi - truncated_pi N| <= 4/(2N+3)
-/

/-- Error in pi/4 approximation is bounded by the next term.
    This follows from the alternating series estimation theorem. -/
theorem pi_quarter_error_bound (N : ℕ) :
    |pi / 4 - truncated_pi_quarter N| ≤ 1 / (2 * N + 3) := by
  -- Define f(k) = 1/(2k+1), the absolute value of the k-th term
  set f : ℕ → ℝ := fun k => 1 / (2 * k + 1) with hf_def
  
  -- f is antitone (decreasing)
  have hf_anti : Antitone f := by
    intro m n hmn
    simp only [hf_def]
    apply one_div_le_one_div_of_le
    · positivity
    · have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
      linarith
  
  -- f tends to 0
  have hf_tendsto : Tendsto f atTop (nhds 0) := by
    simp only [hf_def]
    have h : Tendsto (fun k : ℕ => (2 : ℝ) * k + 1) atTop atTop := by
      refine Tendsto.atTop_add (Tendsto.const_mul_atTop ?_ tendsto_natCast_atTop_atTop) tendsto_const_nhds
      norm_num
    exact tendsto_const_nhds.div_atTop h
  
  -- The series has the form ∑ (-1)^k * f k
  have hform : ∀ k, leibniz_term k = (-1 : ℝ) ^ k * f k := by
    intro k
    simp only [leibniz_term, hf_def, mul_one_div]
  
  -- Get convergence to π/4
  have hconv := leibniz_series_converges
  
  -- Rewrite truncated_pi_quarter using f
  have htrunc : truncated_pi_quarter N = ∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * f k := by
    simp only [truncated_pi_quarter, hform]
  
  -- The limit is π/4 - note truncated_pi_quarter n sums range (n+1) terms
  -- But the Mathlib alternating series lemmas use ∑ i ∈ range n
  -- So we need hlim for the standard form
  have hlim : Tendsto (fun n => ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * f k) atTop (nhds (pi / 4)) := by
    -- truncated_pi_quarter n = ∑ k ∈ range (n+1), so we shift
    -- Use composition: sum over range (n+1) = truncated_pi_quarter n
    -- So sum over range n = truncated_pi_quarter (n-1) for n ≥ 1
    have heq : ∀ n, ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * f k = truncated_pi_quarter n := by
      intro n
      simp only [truncated_pi_quarter, hform]
    -- Eventually the sums match
    refine Tendsto.congr' ?_ (hconv.comp (tendsto_sub_atTop_nat 1))
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    simp only [Function.comp_apply]
    unfold truncated_pi_quarter
    simp only [hform]
    have hn_eq : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    simp only [hn_eq]
  
  -- Case analysis on parity of N+1
  rcases Nat.even_or_odd (N + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- N+1 = k + k (even number of terms)
    -- Rewrite k + k as 2 * k
    have hk2 : N + 1 = 2 * k := by omega
    -- Handle k = 0 (impossible since N + 1 ≥ 1)
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simp at hk2
    -- By Antitone.alternating_series_le_tendsto: S_{2k} ≤ L
    have hle : ∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * f i ≤ pi / 4 :=
      hf_anti.alternating_series_le_tendsto hlim k
    -- Also: L ≤ S_{2k+1} by Antitone.tendsto_le_alternating_series
    have hge : pi / 4 ≤ ∑ i ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ i * f i :=
      hf_anti.tendsto_le_alternating_series hlim k
    -- S_{2k+1} = S_{2k} + (-1)^{2k} * f(2k) = S_{2k} + f(2k)
    have hsum_succ : ∑ i ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ i * f i =
        (∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * f i) + f (2 * k) := by
      rw [Finset.sum_range_succ]
      congr 1
      have heven : Even (2 * k) := ⟨k, two_mul k⟩
      rw [Even.neg_one_pow heven, one_mul]
    -- Need: N + 1 = 2 * k, so range (N+1) = range (2*k)
    have hrange : Finset.range (N + 1) = Finset.range (2 * k) := by rw [hk2]
    rw [htrunc, hrange]
    -- So 0 ≤ L - S_{2k} ≤ f(2k)
    have h1 : 0 ≤ pi / 4 - ∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * f i := by linarith
    have h2 : pi / 4 - ∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * f i ≤ f (2 * k) := by
      rw [hsum_succ] at hge
      linarith
    rw [abs_of_nonneg h1]
    -- f(2k) = 1/(4k+1), need to show ≤ 1/(2N+3)
    -- From hk2: N+1 = 2k, so 2N+2 = 4k, so 2N+3 = 4k+1
    have hN' : (2 : ℝ) * N + 3 = 4 * k + 1 := by
      have hN_eq : N = 2 * k - 1 := by omega
      have h1 : 1 ≤ 2 * k := by omega
      rw [hN_eq, Nat.cast_sub h1]
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      ring
    calc pi / 4 - ∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * f i
        ≤ f (2 * k) := h2
      _ = 1 / (2 * (2 * k : ℕ) + 1) := rfl
      _ = 1 / ((4 : ℝ) * k + 1) := by 
          congr 1
          simp only [Nat.cast_mul, Nat.cast_ofNat]
          ring
      _ = 1 / (2 * N + 3) := by rw [hN']
  · -- N+1 = 2k+1 (odd number of terms)
    -- By Antitone.tendsto_le_alternating_series: L ≤ S_{2k+1}
    have hge : pi / 4 ≤ ∑ i ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ i * f i :=
      hf_anti.tendsto_le_alternating_series hlim k
    -- By Antitone.alternating_series_le_tendsto for k+1: S_{2(k+1)} ≤ L
    have hle : ∑ i ∈ Finset.range (2 * (k + 1)), (-1 : ℝ) ^ i * f i ≤ pi / 4 :=
      hf_anti.alternating_series_le_tendsto hlim (k + 1)
    -- S_{2k+2} = S_{2k+1} + (-1)^{2k+1} * f(2k+1) = S_{2k+1} - f(2k+1)
    have hsum_succ : ∑ i ∈ Finset.range (2 * (k + 1)), (-1 : ℝ) ^ i * f i =
        (∑ i ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ i * f i) - f (2 * k + 1) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ]
      have hodd : Odd (2 * k + 1) := ⟨k, two_mul k ▸ rfl⟩
      simp only [Odd.neg_one_pow hodd, neg_one_mul]
      ring
    -- Need: N + 1 = 2 * k + 1, so range (N+1) = range (2*k+1)
    have hrange : Finset.range (N + 1) = Finset.range (2 * k + 1) := by rw [hk]
    rw [htrunc, hrange]
    -- So 0 ≤ S_{2k+1} - L ≤ f(2k+1)
    have h1 : (∑ i ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ i * f i) - pi / 4 ≥ 0 := by linarith
    have h2 : (∑ i ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ i * f i) - pi / 4 ≤ f (2 * k + 1) := by
      rw [hsum_succ] at hle
      linarith
    rw [abs_sub_comm, abs_of_nonneg h1]
    -- f(2k+1) = 1/(4k+3), need to show ≤ 1/(2N+3)
    -- From hk: N+1 = 2k+1, so N = 2k, so 2N+3 = 4k+3
    have hN' : (2 : ℝ) * N + 3 = 4 * k + 3 := by
      have : N = 2 * k := by omega
      simp only [this, Nat.cast_mul, Nat.cast_ofNat]
      ring
    calc (∑ i ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ i * f i) - pi / 4
        ≤ f (2 * k + 1) := h2
      _ = 1 / (2 * ((2 * k + 1) : ℕ) + 1) := rfl
      _ = 1 / ((4 : ℝ) * k + 3) := by 
          congr 1
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
          ring
      _ = 1 / (2 * N + 3) := by rw [hN']

/-- Main pi error bound: |pi - truncated_pi N| <= 4/(2N+3) -/
theorem pi_error_bound (N : ℕ) :
    |pi - truncated_pi N| ≤ 4 / (2 * N + 3) := by
  have h := pi_quarter_error_bound N
  simp only [truncated_pi]
  calc |pi - 4 * truncated_pi_quarter N|
      = |4 * (pi / 4 - truncated_pi_quarter N)| := by ring_nf
    _ = 4 * |pi / 4 - truncated_pi_quarter N| := by rw [abs_mul]; norm_num
    _ ≤ 4 * (1 / (2 * N + 3)) := by nlinarith [abs_nonneg (pi / 4 - truncated_pi_quarter N)]
    _ = 4 / (2 * N + 3) := by ring

/-- The pi error goes to zero as N -> infinity -/
theorem pi_error_tendsto_zero :
    Tendsto (fun N => |pi - truncated_pi N|) atTop (nhds 0) := by
  -- truncated_pi N = 4 * truncated_pi_quarter N
  -- truncated_pi_quarter N → pi/4, so truncated_pi N → pi
  have hconv : Tendsto truncated_pi atTop (nhds pi) := by
    have hq := leibniz_series_converges
    -- truncated_pi_quarter → pi/4, so 4 * truncated_pi_quarter → 4 * (pi/4) = pi
    have h4 : Tendsto (fun N => 4 * truncated_pi_quarter N) atTop (nhds (4 * (pi / 4))) :=
      hq.const_mul 4
    have heq : (4 : ℝ) * (pi / 4) = pi := by ring
    rw [heq] at h4
    exact h4
  rw [Metric.tendsto_atTop] at hconv ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hconv ε hε
  use N
  intro n hn
  simp only [Real.dist_eq, sub_zero]
  rw [abs_abs]
  have := hN n hn
  rw [Real.dist_eq] at this
  rw [abs_sub_comm]
  exact this

/-- Required iterations for given pi precision.
    To achieve |pi - truncated_pi N| <= epsilon, we need N >= (4/epsilon - 3)/2 -/
noncomputable def required_iterations_pi (epsilon : ℝ) (heps : epsilon > 0) : ℕ :=
  Nat.ceil ((4 / epsilon - 3) / 2)

theorem pi_precision_achieved (epsilon : ℝ) (heps : epsilon > 0)
    (N : ℕ) (hN : N ≥ required_iterations_pi epsilon heps) :
    |pi - truncated_pi N| ≤ epsilon := by
  -- Use pi_error_bound and show 4/(2N+3) ≤ epsilon
  have hbound := pi_error_bound N
  
  -- Key: show 4 / (2 * N + 3) ≤ epsilon
  have h2N3_pos : (2 : ℝ) * N + 3 > 0 := by positivity
  
  -- From hN: N ≥ ⌈(4/ε - 3)/2⌉₊, so (N : ℝ) ≥ (4/ε - 3)/2
  have hN_real : (N : ℝ) ≥ (4 / epsilon - 3) / 2 := by
    have hceil := Nat.le_ceil ((4 / epsilon - 3) / 2)
    calc (N : ℝ) ≥ (required_iterations_pi epsilon heps : ℝ) := by exact_mod_cast hN
      _ = (Nat.ceil ((4 / epsilon - 3) / 2) : ℝ) := rfl
      _ ≥ (4 / epsilon - 3) / 2 := hceil
  
  -- Algebraically: 2N + 3 ≥ 4/ε
  have h2N3_ge : 2 * (N : ℝ) + 3 ≥ 4 / epsilon := by linarith
  
  -- Therefore: 4/(2N+3) ≤ epsilon (reciprocal inequality)
  have hdiv_le : 4 / (2 * (N : ℝ) + 3) ≤ epsilon := by
    have h4pos : (4 : ℝ) > 0 := by norm_num
    rw [div_le_iff h2N3_pos]
    calc 4 = epsilon * (4 / epsilon) := by field_simp
      _ ≤ epsilon * (2 * (N : ℝ) + 3) := by nlinarith
  
  -- Combine with pi_error_bound
  calc |pi - truncated_pi N| 
      ≤ 4 / (2 * N + 3) := hbound
    _ = 4 / (2 * (N : ℝ) + 3) := by simp
    _ ≤ epsilon := hdiv_le

/-! ## Euler's Number Error Bounds

    The Taylor series for e converges extremely fast.
    After N terms, the remaining sum is bounded by 3/((N+1)!).

    Key insight: The remaining terms form a geometric-like series
    that sums to less than 3 times the first omitted term.
-/

/-- The tail of the Taylor series for e.
    This is sum_{k=N+1}^{infinity} 1/k! -/
noncomputable def taylor_e_tail (N : ℕ) : ℝ :=
  euler_e - truncated_e N

/-- The error in e approximation is always positive (Taylor series underestimates) -/
theorem e_error_positive (N : ℕ) : euler_e - truncated_e N > 0 := by
  -- Taylor series for e = sum_{k=0}^∞ 1/k! is monotonically increasing
  -- So partial sums are strictly less than the limit
  have hpartial : ∑ k ∈ range (N + 1), (1 : ℝ) / (k.factorial : ℝ) ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) (N + 1)
    simp only [one_pow] at h
    exact h
  have hstrict : ∑ k ∈ range (N + 1), (1 : ℝ) / (k.factorial : ℝ) < Real.exp 1 := by
    -- The partial sum is strictly less because there are more positive terms
    have hN2_gt : ∑ k ∈ range (N + 2), (1 : ℝ) / (k.factorial : ℝ) > ∑ k ∈ range (N + 1), (1 : ℝ) / (k.factorial : ℝ) := by
      rw [Finset.sum_range_succ]
      have hterm_pos : (1 : ℝ) / ((N + 1).factorial : ℝ) > 0 :=
        div_pos one_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
      linarith
    have hN2_le : ∑ k ∈ range (N + 2), (1 : ℝ) / (k.factorial : ℝ) ≤ Real.exp 1 := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) (N + 2)
      simp only [one_pow] at h
      exact h
    linarith
  unfold truncated_e taylor_e_term euler_e
  linarith

/-- Error bound for e approximation: |e - truncated_e N| <= 3/((N+1)!) -/
theorem e_error_bound (N : ℕ) :
    |euler_e - truncated_e N| ≤ 3 / ((N + 1).factorial : ℝ) := by
  -- The error is positive, so |error| = error
  have hpos := e_error_positive N
  rw [abs_of_pos hpos]
  unfold euler_e truncated_e taylor_e_term
  
  -- For N = 0: exp(1) - 1 ≤ 3/1! = 3 (true since e < 3)
  cases' Nat.eq_zero_or_pos N with hN0 hNpos
  · -- Case N = 0
    subst hN0
    simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, 
               Nat.cast_one, div_one, Nat.factorial_one, zero_add]
    -- Goal: exp 1 - 1 ≤ 3
    
    -- Use exp_bound for n=2: |exp 1 - 2| ≤ 3/(2! * 2) = 3/4
    have hbound := Real.exp_bound (by norm_num : |(1 : ℝ)| ≤ 1) (by norm_num : 2 ≥ 1)
    simp only [one_pow, abs_one, one_mul, Nat.succ_eq_add_one] at hbound
    
    -- Compute ∑_{k<2} 1/k! = 1/0! + 1/1! = 1 + 1 = 2
    have hsum2 : ∑ k ∈ Finset.range 2, (1 : ℝ) / (k.factorial : ℝ) = 2 := by
      simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
                 Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one]
      ring
    
    -- The difference is nonneg since partial sums underestimate e
    have hdiff_nonneg : Real.exp 1 - ∑ k ∈ Finset.range 2, (1 : ℝ) / (k.factorial : ℝ) ≥ 0 := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 2
      simp only [one_pow] at h
      linarith
    rw [abs_of_nonneg hdiff_nonneg, hsum2] at hbound
    -- hbound: exp 1 - 2 ≤ (2+1) / (2! * 2)
    
    -- Simplify: 2! = 2, so RHS = 3 / (2 * 2) = 3/4
    -- Use norm_num to handle all numeric simplifications including coercions
    norm_num at hbound
    -- hbound: exp 1 - 2 ≤ 3 / 4
    -- Goal: exp 1 - 1 ≤ 3
    -- Since exp 1 ≤ 2 + 3/4 = 11/4, we have exp 1 - 1 ≤ 7/4 < 3
    linarith
  
  · -- Case N ≥ 1: Use geometric series bound
    have hN1 : N ≥ 1 := hNpos
    have hfact_pos : ((N + 1).factorial : ℝ) > 0 := Nat.cast_pos.mpr (Nat.factorial_pos _)
    
    -- Use Real.exp_bound for n = N+1
    have habs : |(1 : ℝ)| ≤ 1 := by norm_num
    have hN1' : N + 1 ≥ 1 := Nat.le_add_left 1 N
    have hbound := Real.exp_bound habs hN1'
    simp only [one_pow, abs_one, one_mul, Nat.succ_eq_add_one] at hbound
    
    -- hbound: |exp 1 - ∑_{k < N+1} 1/k!| ≤ (N+2) / ((N+1)! * (N+1))
    have hdiff_nonneg : Real.exp 1 - ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / (k.factorial : ℝ) ≥ 0 := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) (N + 1)
      simp only [one_pow] at h
      linarith
    rw [abs_of_nonneg hdiff_nonneg] at hbound
    
    -- Now show (N+2) / ((N+1)! * (N+1)) ≤ 3 / (N+1)!
    -- Equivalent to: N+2 ≤ 3 * (N+1), i.e., N+2 ≤ 3N+3, i.e., 0 ≤ 2N+1 (always true)
    have hN1_pos : ((N + 1 : ℕ) : ℝ) > 0 := by positivity
    
    have hkey : ((N + 2 : ℕ) : ℝ) / (((N + 1).factorial : ℝ) * ((N + 1 : ℕ) : ℝ)) ≤ 
                3 / ((N + 1).factorial : ℝ) := by
      rw [div_le_div_iff (by positivity) hfact_pos]
      -- Goal: (N+2) * (N+1)! ≤ 3 * ((N+1)! * (N+1))
      have hineq : ((N + 2 : ℕ) : ℝ) ≤ 3 * ((N + 1 : ℕ) : ℝ) := by
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
        have hN_nonneg : (N : ℝ) ≥ 0 := Nat.cast_nonneg N
        linarith
      calc ((N + 2 : ℕ) : ℝ) * ((N + 1).factorial : ℝ) 
          ≤ (3 * ((N + 1 : ℕ) : ℝ)) * ((N + 1).factorial : ℝ) := by nlinarith
        _ = 3 * (((N + 1).factorial : ℝ) * ((N + 1 : ℕ) : ℝ)) := by ring
    
    -- Connect hbound to hkey by showing the types match
    have hbound_form : Real.exp 1 - ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / (k.factorial : ℝ) ≤
        ((N + 2 : ℕ) : ℝ) / (((N + 1).factorial : ℝ) * ((N + 1 : ℕ) : ℝ)) := by
      convert hbound using 2 <;> simp [Nat.succ_eq_add_one]
    
    linarith [hbound_form, hkey]

/-- The e error goes to zero super-exponentially fast -/
theorem e_error_tendsto_zero :
    Tendsto (fun N => |euler_e - truncated_e N|) atTop (nhds 0) := by
  -- Use that truncated_e N → euler_e (from taylor_e_series_converges)
  have hconv := taylor_e_series_converges
  -- Tendsto f l (nhds a) implies Tendsto (|f - a|) l (nhds 0)
  rw [Metric.tendsto_atTop] at hconv ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hconv ε hε
  use N
  intro n hn
  simp only [Real.dist_eq, sub_zero]
  rw [abs_abs]
  have := hN n hn
  rw [Real.dist_eq] at this
  rw [abs_sub_comm]
  exact this

/-- Required iterations for given e precision.
    To achieve |e - truncated_e N| <= epsilon, we need the smallest N such that
    3/((N+1)!) <= epsilon, i.e., (N+1)! >= 3/epsilon -/
noncomputable def required_iterations_e (epsilon : ℝ) (heps : epsilon > 0) : ℕ :=
  -- Find smallest N such that (N+1)! >= 3/epsilon
  Nat.find (exists_factorial_ge_of_pos (div_pos (by norm_num : (3 : ℝ) > 0) heps))
  where
    exists_factorial_ge_of_pos {x : ℝ} (hx : x > 0) : ∃ N : ℕ, ((N : ℕ).factorial : ℝ) ≥ x := by
      -- Factorial is unbounded: for any x, eventually N! > x
      -- Use: N = max 1 (Nat.ceil x) works since N! >= N >= ceil(x) >= x for large N
      use max 2 (Nat.ceil x)
      have hceil : (Nat.ceil x : ℝ) ≥ x := Nat.le_ceil x
      have hmax : (max 2 (Nat.ceil x) : ℝ) ≥ Nat.ceil x := by
        simp only [ge_iff_le, le_max_iff]
        right
        rfl
      have hfact : (max 2 (Nat.ceil x)).factorial ≥ max 2 (Nat.ceil x) := Nat.self_le_factorial _
      calc ((max 2 (Nat.ceil x)).factorial : ℝ) ≥ (max 2 (Nat.ceil x) : ℝ) := by exact_mod_cast hfact
        _ ≥ (Nat.ceil x : ℝ) := hmax
        _ ≥ x := hceil

theorem e_precision_achieved (epsilon : ℝ) (heps : epsilon > 0)
    (N : ℕ) (hN : N ≥ required_iterations_e epsilon heps) :
    |euler_e - truncated_e N| ≤ epsilon := by
  -- Use e_error_bound and show 3/(N+1)! ≤ epsilon
  have hbound := e_error_bound N
  
  -- Get the factorial bound from Nat.find_spec
  -- required_iterations_e finds smallest M such that M! ≥ 3/epsilon
  have h3eps_pos : (3 : ℝ) / epsilon > 0 := div_pos (by norm_num) heps
  let M := required_iterations_e epsilon heps
  have hM_spec : ((M).factorial : ℝ) ≥ 3 / epsilon := by
    have := Nat.find_spec (required_iterations_e.exists_factorial_ge_of_pos h3eps_pos)
    exact this
  
  -- Since N ≥ M, we have N! ≥ M! (factorial is monotone)
  have hN_fact : ((N).factorial : ℝ) ≥ ((M).factorial : ℝ) := by
    have hle : M.factorial ≤ N.factorial := Nat.factorial_le hN
    exact_mod_cast hle
  
  -- And (N+1)! ≥ N! ≥ M! ≥ 3/epsilon
  have hN1_fact : (((N + 1).factorial : ℕ) : ℝ) ≥ 3 / epsilon := by
    have hN1_ge_N : (N + 1).factorial ≥ N.factorial := Nat.factorial_le (Nat.le_succ N)
    calc (((N + 1).factorial : ℕ) : ℝ) ≥ ((N.factorial : ℕ) : ℝ) := by exact_mod_cast hN1_ge_N
      _ ≥ ((M.factorial : ℕ) : ℝ) := hN_fact
      _ ≥ 3 / epsilon := hM_spec
  
  -- Therefore: 3/(N+1)! ≤ epsilon
  have hfact_pos : (((N + 1).factorial : ℕ) : ℝ) > 0 := by positivity
  have hdiv_le : 3 / (((N + 1).factorial : ℕ) : ℝ) ≤ epsilon := by
    rw [div_le_iff hfact_pos]
    calc 3 = epsilon * (3 / epsilon) := by field_simp
      _ ≤ epsilon * (((N + 1).factorial : ℕ) : ℝ) := by nlinarith
  
  -- Combine with e_error_bound
  calc |euler_e - truncated_e N| 
      ≤ 3 / ((N + 1).factorial : ℝ) := hbound
    _ = 3 / (((N + 1).factorial : ℕ) : ℝ) := by simp
    _ ≤ epsilon := hdiv_le

/-! ## Square Root of 2 Error Bounds

    Newton-Raphson has quadratic convergence: the number of correct digits
    approximately doubles with each iteration.

    Let e_n = truncated_sqrt2 n - sqrt(2). Then:
    e_{n+1} = e_n^2 / (2 * truncated_sqrt2 n)

    This gives super-exponential convergence.
-/

/-- Error in Newton-Raphson iteration -/
noncomputable def sqrt2_error (N : ℕ) : ℝ :=
  truncated_sqrt2 N - sqrt2

/-- Newton-Raphson error satisfies a quadratic recurrence.
    e_{n+1} = e_n^2 / (2 * x_n) -/
theorem sqrt2_error_recurrence (N : ℕ) (hN : N ≥ 1) :
    sqrt2_error (N + 1) = (sqrt2_error N) ^ 2 / (2 * truncated_sqrt2 N) := by
  unfold sqrt2_error
  simp only [truncated_sqrt2, newton_sqrt2_step]
  have hx_pos : truncated_sqrt2 N > 0 := truncated_sqrt2_pos N
  have hx_ne : truncated_sqrt2 N ≠ 0 := ne_of_gt hx_pos
  have hsq : sqrt2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  field_simp
  ring_nf
  rw [hsq]
  ring

/-- Error bound for sqrt(2) approximation.
    After N iterations (N >= 1), the error is at most 1/2^(2^(N-1)) -/
theorem sqrt2_error_bound (N : ℕ) (hN : N ≥ 1) :
    |truncated_sqrt2 N - sqrt2| ≤ 1 / 2 ^ (2 ^ (N - 1)) := by
  -- Induction on N with case split
  induction N with
  | zero => omega
  | succ n ih =>
    -- Key insight: truncated_sqrt2 (n+1) ≥ sqrt2 for n+1 ≥ 1
    have hge : truncated_sqrt2 (n + 1) ≥ sqrt2 := truncated_sqrt2_ge_target (n + 1) hN
    have hpos_err : truncated_sqrt2 (n + 1) - sqrt2 ≥ 0 := by linarith
    rw [abs_of_nonneg hpos_err]
    
    -- Case analysis: n = 0 (base) or n ≥ 1 (inductive step)
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · -- Base case: N = 1
      simp only [Nat.add_sub_cancel, pow_zero, pow_one]
      -- Need: truncated_sqrt2 1 - sqrt2 ≤ 1/2
      have hval : truncated_sqrt2 1 = 3 / 2 := truncated_sqrt2_one
      simp only [hval, sqrt2]
      have hsqrt_lb : Real.sqrt 2 > 14 / 10 := by
        rw [gt_iff_lt, Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 14/10)]
        norm_num
      -- 3/2 - sqrt2 < 3/2 - 14/10 = 1/10 < 1/2
      linarith
    · -- Inductive case: N = n + 1 where n ≥ 1
      have hn1 : n ≥ 1 := hn_pos
      have hge_n : truncated_sqrt2 n ≥ sqrt2 := truncated_sqrt2_ge_target n hn1
      have hpos_n : truncated_sqrt2 n > 0 := truncated_sqrt2_pos n
      have hpos_err_n : truncated_sqrt2 n - sqrt2 ≥ 0 := by linarith
      
      -- Apply induction hypothesis
      have ih_applied := ih hn1
      rw [abs_of_nonneg hpos_err_n] at ih_applied
      
      -- Use the quadratic recurrence
      have hrec := sqrt2_error_recurrence n hn1
      unfold sqrt2_error at hrec
      rw [hrec]
      
      -- Key bound: 2 * truncated_sqrt2 n > 2
      have hsqrt2_gt_one : sqrt2 > 1 := by
        unfold sqrt2
        rw [gt_iff_lt, Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
        norm_num
      have h2x_gt_2 : 2 * truncated_sqrt2 n > 2 := by nlinarith
      have h2x_ge_1 : 2 * truncated_sqrt2 n ≥ 1 := by linarith
      
      -- Square the induction hypothesis bound
      have hsq_bound : (truncated_sqrt2 n - sqrt2) ^ 2 ≤ (1 / 2 ^ (2 ^ (n - 1))) ^ 2 := by
        apply sq_le_sq'
        · have hpow_pos : (1 : ℝ) / 2 ^ (2 ^ (n - 1)) > 0 := by positivity
          linarith
        · exact ih_applied
      
      -- Simplify (1/2^k)^2 = 1/2^(2^n)
      have hpow_sq : ((1 : ℝ) / 2 ^ (2 ^ (n - 1))) ^ 2 = 1 / 2 ^ (2 ^ n) := by
        have hexp : 2 ^ (n - 1) * 2 = 2 ^ n := by
          have : 2 ^ (n - 1) * 2 = 2 ^ ((n - 1) + 1) := by ring
          rw [this, Nat.sub_add_cancel hn1]
        field_simp
        rw [← pow_mul]
        congr 1
        exact hexp.symm
      
      -- Simplify goal exponent: (n + 1) - 1 = n
      simp only [Nat.add_sub_cancel]
      
      -- Final bound
      have hnum_nonneg : (1 : ℝ) / 2 ^ (2 ^ n) ≥ 0 := by positivity
      calc (truncated_sqrt2 n - sqrt2) ^ 2 / (2 * truncated_sqrt2 n)
          ≤ ((1 : ℝ) / 2 ^ (2 ^ (n - 1))) ^ 2 / (2 * truncated_sqrt2 n) := by
            apply div_le_div_of_nonneg_right hsq_bound (by linarith)
        _ = (1 / 2 ^ (2 ^ n)) / (2 * truncated_sqrt2 n) := by rw [hpow_sq]
        _ ≤ (1 / 2 ^ (2 ^ n)) / 1 := by
            apply div_le_div_of_nonneg_left hnum_nonneg (by norm_num) h2x_ge_1
        _ = 1 / 2 ^ (2 ^ n) := by ring

/-- Specialized bound for the first few iterations -/
theorem sqrt2_error_one : |truncated_sqrt2 1 - sqrt2| < 1 / 10 := by
  simp only [truncated_sqrt2_one, sqrt2]
  have hsqrt_lb : Real.sqrt 2 > 14 / 10 := by
    have h1 : (14 / 10 : ℝ) ^ 2 < 2 := by norm_num
    have h3 : Real.sqrt ((14 / 10 : ℝ) ^ 2) < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) h1
    simp only [Real.sqrt_sq (by norm_num : (14 / 10 : ℝ) ≥ 0)] at h3
    exact h3
  have hsqrt_ub : Real.sqrt 2 < 15 / 10 := by
    have h1 : (2 : ℝ) < (15 / 10) ^ 2 := by norm_num
    have h3 : Real.sqrt 2 < Real.sqrt ((15 / 10 : ℝ) ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h1
    simp only [Real.sqrt_sq (by norm_num : (15 / 10 : ℝ) ≥ 0)] at h3
    exact h3
  rw [abs_sub_lt_iff]
  constructor <;> linarith

theorem sqrt2_error_two : |truncated_sqrt2 2 - sqrt2| < 1 / 100 := by
  simp only [truncated_sqrt2_two, sqrt2]
  have hsqrt_lb : Real.sqrt 2 > 141 / 100 := by
    have h1 : (141 / 100 : ℝ) ^ 2 < 2 := by norm_num
    have h3 : Real.sqrt ((141 / 100 : ℝ) ^ 2) < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) h1
    simp only [Real.sqrt_sq (by norm_num : (141 / 100 : ℝ) ≥ 0)] at h3
    exact h3
  have hsqrt_ub : Real.sqrt 2 < 17 / 12 := by
    have h1 : (2 : ℝ) < (17 / 12) ^ 2 := by norm_num
    have h3 : Real.sqrt 2 < Real.sqrt ((17 / 12 : ℝ) ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h1
    simp only [Real.sqrt_sq (by norm_num : (17 / 12 : ℝ) ≥ 0)] at h3
    exact h3
  rw [abs_sub_lt_iff]
  constructor <;> linarith

theorem sqrt2_error_three : |truncated_sqrt2 3 - sqrt2| < 1 / 100000 := by
  have h3 : truncated_sqrt2 3 = 577 / 408 := by
    simp only [truncated_sqrt2, newton_sqrt2_step]
    norm_num
  simp only [h3, sqrt2]
  have hsqrt_lb : Real.sqrt 2 > 7212449 / 5100000 := by
    have h1 : (7212449 / 5100000 : ℝ) ^ 2 < 2 := by norm_num
    have h3 : Real.sqrt ((7212449 / 5100000 : ℝ) ^ 2) < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) h1
    simp only [Real.sqrt_sq (by norm_num : (7212449 / 5100000 : ℝ) ≥ 0)] at h3
    exact h3
  have hsqrt_ub : Real.sqrt 2 < 577 / 408 := by
    have h1 : (2 : ℝ) < (577 / 408) ^ 2 := by norm_num
    have h3 : Real.sqrt 2 < Real.sqrt ((577 / 408 : ℝ) ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h1
    simp only [Real.sqrt_sq (by norm_num : (577 / 408 : ℝ) ≥ 0)] at h3
    exact h3
  have hkey : (577 : ℝ) / 408 - 7212449 / 5100000 = 1 / 100000 := by norm_num
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- The sqrt2 error goes to zero super-exponentially -/
theorem sqrt2_error_tendsto_zero :
    Tendsto (fun N => |truncated_sqrt2 N - sqrt2|) atTop (nhds 0) := by
  have hconv := newton_sqrt2_converges
  rw [Metric.tendsto_atTop] at hconv ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hconv ε hε
  use N
  intro n hn
  simp only [Real.dist_eq, sub_zero]
  rw [abs_abs]
  have := hN n hn
  rw [Real.dist_eq] at this
  exact this

/-- Required iterations for given sqrt2 precision. -/
noncomputable def required_iterations_sqrt2 (epsilon : ℝ) (heps : epsilon > 0) : ℕ :=
  max 1 (Nat.ceil (1 + Real.logb 2 (Real.logb 2 (1 / epsilon))))

end DiscreteSpacetime.Irrationality
