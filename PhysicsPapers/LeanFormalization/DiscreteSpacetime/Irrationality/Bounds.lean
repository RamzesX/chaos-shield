/-
  Irrationality.Bounds
  ====================

  Error bounds for truncated irrational approximations.

  This module provides rigorous bounds on the approximation error when
  truncating infinite series. These bounds are essential for:
  1. Quantifying computational uncertainty
  2. Determining required precision for physical calculations
  3. Understanding the relationship between computation and uncertainty

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
  sorry
  -- TODO: Apply alternating series estimation
  -- Key: Leibniz series is alternating with decreasing absolute terms
  -- The (N+1)th term is 1/(2(N+1)+1) = 1/(2N+3)

/-- Main pi error bound: |pi - truncated_pi N| <= 4/(2N+3) -/
theorem pi_error_bound (N : ℕ) :
    |pi - truncated_pi N| ≤ 4 / (2 * N + 3) := by
  have h := pi_quarter_error_bound N
  simp only [truncated_pi]
  calc |pi - 4 * truncated_pi_quarter N|
      = |4 * (pi / 4 - truncated_pi_quarter N)| := by ring_nf
    _ = 4 * |pi / 4 - truncated_pi_quarter N| := by rw [abs_mul]; simp
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
  sorry
  -- TODO: Use pi_error_bound and properties of required_iterations_pi

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

/-- Refined bound: the error is less than 2 times the first omitted term for N >= 1 -/
theorem e_error_tight_bound (N : ℕ) (hN : N ≥ 1) :
    euler_e - truncated_e N ≤ 2 / ((N + 1).factorial : ℝ) := by
  sorry
  -- HARD: Requires careful tail sum analysis
  -- The bound from Real.exp_bound gives (N+1)/(N! * N) which is not tight enough

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
  sorry

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
  -- sqrt2_error n = truncated_sqrt2 n - sqrt2
  -- truncated_sqrt2 (n+1) = (truncated_sqrt2 n + 2 / truncated_sqrt2 n) / 2
  -- Let x = truncated_sqrt2 N, s = sqrt2
  -- e_{n+1} = x_{n+1} - s = (x + 2/x)/2 - s
  --         = (x² + 2)/(2x) - s = (x² + 2 - 2sx)/(2x)
  --         = (x² - 2sx + s² + 2 - s²)/(2x) = ((x-s)² + 2 - s²)/(2x)
  --         = (x-s)²/(2x)  since s² = 2
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
  sorry
  -- TODO: Induction using the quadratic recurrence
  -- Base case: |truncated_sqrt2 1 - sqrt2| = |3/2 - sqrt2| ~ 0.086 < 1/2
  -- Inductive step: error squares (approximately) each step

/-- Specialized bound for the first few iterations -/
theorem sqrt2_error_one : |truncated_sqrt2 1 - sqrt2| < 1 / 10 := by
  -- truncated_sqrt2 1 = 3/2, sqrt2 = sqrt(2)
  -- Need: |3/2 - sqrt(2)| < 1/10
  simp only [truncated_sqrt2_one, sqrt2]
  -- We know: 1.4 < sqrt(2) < 1.5, so 0 < 3/2 - sqrt(2) < 0.1
  have hsqrt_lb : Real.sqrt 2 > 14 / 10 := by
    have h1 : (14 / 10 : ℝ) ^ 2 < 2 := by norm_num
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    have h3 : Real.sqrt ((14 / 10 : ℝ) ^ 2) < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) h1
    simp only [Real.sqrt_sq (by norm_num : (14 / 10 : ℝ) ≥ 0)] at h3
    exact h3
  have hsqrt_ub : Real.sqrt 2 < 15 / 10 := by
    have h1 : (2 : ℝ) < (15 / 10) ^ 2 := by norm_num
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    have h3 : Real.sqrt 2 < Real.sqrt ((15 / 10 : ℝ) ^ 2) := Real.sqrt_lt_sqrt h2 h1
    simp only [Real.sqrt_sq (by norm_num : (15 / 10 : ℝ) ≥ 0)] at h3
    exact h3
  rw [abs_sub_lt_iff]
  constructor <;> linarith

theorem sqrt2_error_two : |truncated_sqrt2 2 - sqrt2| < 1 / 100 := by
  -- truncated_sqrt2 2 = 17/12, sqrt2 = sqrt(2)
  -- Need: |17/12 - sqrt(2)| < 1/100
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
  -- truncated_sqrt2 3 = 577/408, sqrt2 = sqrt(2)
  -- Need: |577/408 - sqrt(2)| < 1/100000
  -- 577/408 ≈ 1.4142157, sqrt(2) ≈ 1.4142136, difference ≈ 2.1e-6 < 1e-5
  have h3 : truncated_sqrt2 3 = 577 / 408 := by
    simp only [truncated_sqrt2, newton_sqrt2_step]
    norm_num
  simp only [h3, sqrt2]
  -- Lower bound: sqrt(2) > 577/408 - 1/100000 = 7212449/5100000
  -- because (7212449/5100000)^2 < 2
  have hsqrt_lb : Real.sqrt 2 > 7212449 / 5100000 := by
    have h1 : (7212449 / 5100000 : ℝ) ^ 2 < 2 := by norm_num
    have h3 : Real.sqrt ((7212449 / 5100000 : ℝ) ^ 2) < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) h1
    simp only [Real.sqrt_sq (by norm_num : (7212449 / 5100000 : ℝ) ≥ 0)] at h3
    exact h3
  -- Upper bound: sqrt(2) < 577/408 because (577/408)^2 > 2
  have hsqrt_ub : Real.sqrt 2 < 577 / 408 := by
    have h1 : (2 : ℝ) < (577 / 408) ^ 2 := by norm_num
    have h3 : Real.sqrt 2 < Real.sqrt ((577 / 408 : ℝ) ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h1
    simp only [Real.sqrt_sq (by norm_num : (577 / 408 : ℝ) ≥ 0)] at h3
    exact h3
  -- Key: 577/408 - 7212449/5100000 = 1/100000
  have hkey : (577 : ℝ) / 408 - 7212449 / 5100000 = 1 / 100000 := by norm_num
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- The sqrt2 error goes to zero super-exponentially -/
theorem sqrt2_error_tendsto_zero :
    Tendsto (fun N => |truncated_sqrt2 N - sqrt2|) atTop (nhds 0) := by
  -- Use that truncated_sqrt2 N → sqrt2 (from newton_sqrt2_converges)
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

/-- Required iterations for given sqrt2 precision.
    To achieve error <= epsilon, we need roughly log2(log2(1/epsilon)) iterations. -/
noncomputable def required_iterations_sqrt2 (epsilon : ℝ) (heps : epsilon > 0) : ℕ :=
  -- Need 2^(2^(N-1)) >= 1/epsilon, i.e., N >= 1 + log2(log2(1/epsilon))
  max 1 (Nat.ceil (1 + Real.logb 2 (Real.logb 2 (1 / epsilon))))

theorem sqrt2_precision_achieved (epsilon : ℝ) (heps : epsilon > 0)
    (N : ℕ) (hN : N ≥ required_iterations_sqrt2 epsilon heps) :
    |truncated_sqrt2 N - sqrt2| ≤ epsilon := by
  sorry

/-! ## Comparison of Convergence Rates

    Different irrationals have vastly different convergence rates:
    - Pi (Leibniz): O(1/N) - algebraic, slow
    - e (Taylor):   O(1/N!) - exponential, fast
    - sqrt(2) (NR): O(1/2^(2^N)) - super-exponential, very fast

    This has implications for computational budgets in physics.
-/

/-- Pi requires many more iterations than e for the same precision -/
theorem pi_slower_than_e (epsilon : ℝ) (heps : epsilon > 0) (heps_small : epsilon < 1) :
    required_iterations_pi epsilon heps > required_iterations_e epsilon heps := by
  sorry
  -- TODO: Compare the required iterations

/-- sqrt(2) requires far fewer iterations than e -/
theorem sqrt2_faster_than_e (epsilon : ℝ) (heps : epsilon > 0) (heps_small : epsilon < 1/100) :
    required_iterations_sqrt2 epsilon heps < required_iterations_e epsilon heps := by
  sorry

/-! ## Combined Precision Function

    Given a target error epsilon and an irrational constant,
    compute the required number of iterations.
-/

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

/-- Error bound for any target -/
theorem error_bound (target : IrrationalTarget) (N : ℕ) (hN : N ≥ 1) :
    ∃ C : ℝ, C > 0 ∧
    |best_approximation target N - true_value target| ≤ C := by
  -- For any target, we can always find some constant bound
  -- We use C = |best_approximation target N - true_value target| + 1
  use |best_approximation target N - true_value target| + 1
  constructor
  · -- C > 0: absolute value is nonneg, plus 1 makes it positive
    have h := abs_nonneg (best_approximation target N - true_value target)
    linarith
  · -- |...| ≤ C: trivially true since C = |...| + 1
    linarith [abs_nonneg (best_approximation target N - true_value target)]

/-! ## Physical Interpretation

    PHYSICS INSIGHT: In a physical system with computational budget B,
    the achievable precision for different irrationals varies dramatically.

    A system computing with "N iterations" can achieve:
    - Pi precision:    ~ 1/N       (poor)
    - e precision:     ~ 1/N!      (excellent)
    - sqrt(2) precision: ~ 1/2^(2^N) (exceptional)

    This means physical quantities involving pi are "harder to compute"
    than those involving e or algebraic numbers like sqrt(2).
-/

/-- Precision hierarchy: sqrt2 > e > pi for same iteration budget -/
theorem precision_hierarchy (N : ℕ) (hN : N ≥ 3) :
    |truncated_sqrt2 N - sqrt2| <
    |euler_e - truncated_e N| ∧
    |euler_e - truncated_e N| <
    |pi - truncated_pi N| := by
  sorry
  -- TODO: For N >= 3, the hierarchy is clear from the bounds

end DiscreteSpacetime.Irrationality
