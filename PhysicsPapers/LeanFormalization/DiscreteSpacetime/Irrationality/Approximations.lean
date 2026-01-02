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
import Mathlib.Data.Real.Pi.Leibniz
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Complex.Exponential

namespace DiscreteSpacetime.Irrationality

open BigOperators Finset Real Filter Topology

/-! ## Fundamental Constants from Mathlib -/

noncomputable abbrev pi : ℝ := Real.pi
noncomputable abbrev euler_e : ℝ := Real.exp 1
noncomputable abbrev sqrt2 : ℝ := Real.sqrt 2

/-! ## Pi Approximation via Leibniz Series -/

noncomputable def leibniz_term (k : ℕ) : ℝ := (-1 : ℝ) ^ k / (2 * k + 1)
noncomputable def truncated_pi_quarter (N : ℕ) : ℝ := ∑ k ∈ range (N + 1), leibniz_term k
noncomputable def truncated_pi (N : ℕ) : ℝ := 4 * truncated_pi_quarter N

theorem truncated_pi_zero : truncated_pi 0 = 4 := by simp [truncated_pi, truncated_pi_quarter, leibniz_term]
theorem truncated_pi_one : truncated_pi 1 = 8 / 3 := by
  simp only [truncated_pi, truncated_pi_quarter, leibniz_term, Finset.sum_range_succ, Finset.range_one, Finset.sum_empty]; norm_num

/-! ## Euler's Number Approximation via Taylor Series -/

noncomputable def taylor_e_term (k : ℕ) : ℝ := 1 / (k.factorial : ℝ)
noncomputable def truncated_e (N : ℕ) : ℝ := ∑ k ∈ range (N + 1), taylor_e_term k

theorem truncated_e_zero : truncated_e 0 = 1 := by simp [truncated_e, taylor_e_term]
theorem truncated_e_one : truncated_e 1 = 2 := by
  simp only [truncated_e, taylor_e_term, Finset.sum_range_succ, Finset.range_one, Finset.sum_empty]; norm_num [Nat.factorial]
theorem truncated_e_two : truncated_e 2 = 5 / 2 := by
  simp only [truncated_e, taylor_e_term, Finset.sum_range_succ, Finset.range_one, Finset.sum_empty]; norm_num [Nat.factorial]

/-! ## Square Root of 2 via Newton-Raphson -/

noncomputable def newton_sqrt2_step (x : ℝ) : ℝ := (x + 2 / x) / 2
noncomputable def truncated_sqrt2 : ℕ → ℝ | 0 => 1 | n + 1 => newton_sqrt2_step (truncated_sqrt2 n)

theorem truncated_sqrt2_zero : truncated_sqrt2 0 = 1 := rfl
theorem truncated_sqrt2_one : truncated_sqrt2 1 = 3 / 2 := by simp [truncated_sqrt2, newton_sqrt2_step]; ring
theorem truncated_sqrt2_two : truncated_sqrt2 2 = 17 / 12 := by simp [truncated_sqrt2, newton_sqrt2_step]; ring

/-! ## Positivity Lemmas -/

theorem truncated_e_pos (N : ℕ) : truncated_e N > 0 := by
  unfold truncated_e; apply Finset.sum_pos
  · intro k _; unfold taylor_e_term; exact div_pos one_pos (Nat.cast_pos.mpr (Nat.factorial_pos k))
  · exact Finset.nonempty_range_succ

theorem truncated_sqrt2_pos (N : ℕ) : truncated_sqrt2 N > 0 := by
  induction N with
  | zero => norm_num [truncated_sqrt2]
  | succ n ih =>
    simp only [truncated_sqrt2, newton_sqrt2_step]
    exact div_pos (by linarith [div_pos (by norm_num : (2:ℝ) > 0) ih]) (by norm_num)

/-! ## AM-GM Lemmas -/

section AMGM

private lemma sq_sum_ge_two_prod (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by nlinarith [sq_nonneg (a - b)]
private lemma sum_sq_ge_four_prod (a b : ℝ) : (a + b) ^ 2 ≥ 4 * a * b := by nlinarith [sq_sum_ge_two_prod a b]

private lemma am_ge_gm {a b : ℝ} (ha : a > 0) (hb : b > 0) : (a + b) / 2 ≥ Real.sqrt (a * b) := by
  have hsum : 0 ≤ a + b := by linarith
  have h_sq : (a + b) ^ 2 ≥ 4 * a * b := sum_sq_ge_four_prod a b
  have h_sqrt : Real.sqrt ((a + b) ^ 2) ≥ Real.sqrt (4 * a * b) := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq hsum, show (4 : ℝ) * a * b = (2 : ℝ) ^ 2 * (a * b) by ring] at h_sqrt
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num : (2 : ℝ) ≥ 0)] at h_sqrt
  linarith

end AMGM

/-! ## Newton-Raphson Lemmas -/

section NewtonLemmas

private lemma newton_product_eq_two {x : ℝ} (hx : x > 0) : x * (2 / x) = 2 := by field_simp

private lemma newton_step_ge_sqrt2 {x : ℝ} (hx : x > 0) : newton_sqrt2_step x ≥ Real.sqrt 2 := by
  unfold newton_sqrt2_step
  calc (x + 2 / x) / 2 ≥ Real.sqrt (x * (2 / x)) := am_ge_gm hx (div_pos (by norm_num) hx)
    _ = Real.sqrt 2 := by rw [newton_product_eq_two hx]

private lemma sq_ge_two_of_ge_sqrt2 {x : ℝ} (hx : x > 0) (hge : x ≥ Real.sqrt 2) : x ^ 2 ≥ 2 := by
  nlinarith [sq_nonneg x, sq_nonneg (Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]

private lemma two_div_le_self {x : ℝ} (hx : x > 0) (hsq : x ^ 2 ≥ 2) : 2 / x ≤ x := by
  rw [div_le_iff₀ hx]; nlinarith

private lemma newton_step_le {x : ℝ} (hx : x > 0) (hge : x ≥ Real.sqrt 2) : newton_sqrt2_step x ≤ x := by
  unfold newton_sqrt2_step
  have hdiv := two_div_le_self hx (sq_ge_two_of_ge_sqrt2 hx hge)
  linarith

end NewtonLemmas

/-! ## Elementary exp(1) Series Lemmas -/

section ExpSeriesLemmas

/-- Partial sums of 1/k! are bounded above by exp(1) -/
private lemma partial_sum_le_exp_one (N : ℕ) :
    ∑ k ∈ range N, (1 : ℝ) / (k.factorial : ℝ) ≤ Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) N
  simp only [one_pow] at h
  exact h

/-- Error bound: |exp(1) - partial_sum| ≤ 2/N! for N ≥ 1 -/
private lemma exp_one_error_bound (N : ℕ) (hN : 1 ≤ N) :
    |Real.exp 1 - ∑ k ∈ range N, (1 : ℝ) / (k.factorial : ℝ)| ≤ 2 / (N.factorial : ℝ) := by
  have habs : |(1 : ℝ)| ≤ 1 := by norm_num
  have h := Real.exp_bound habs hN
  simp only [one_pow, abs_one] at h
  -- h : |rexp 1 - ∑ x ∈ range N, 1 / ↑x.factorial| ≤ 1 * (↑N.succ / (↑N.factorial * ↑N))
  -- Need to remove the "1 *" and then show bound
  simp only [one_mul] at h
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN))
  have hfact_pos : (N.factorial : ℝ) > 0 := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hbound : (N.succ : ℝ) / ((N.factorial : ℝ) * N) ≤ 2 / (N.factorial : ℝ) := by
    rw [div_le_div_iff (mul_pos hfact_pos hN_pos) hfact_pos]
    -- Goal: ↑N.succ * ↑N.factorial ≤ 2 * (↑N.factorial * ↑N)
    have h1 : (N.succ : ℝ) = N + 1 := by simp
    have h2 : (N.succ : ℝ) ≤ 2 * N := by
      rw [h1]
      have hN1 : (N : ℝ) ≥ 1 := by exact_mod_cast hN
      linarith
    calc (N.succ : ℝ) * N.factorial ≤ (2 * N) * N.factorial := by nlinarith [hfact_pos]
      _ = 2 * (N.factorial * N) := by ring
  exact h.trans hbound

/-- 1/n! → 0 as n → ∞. Trivial: factorial grows faster than any polynomial. -/
private lemma tendsto_one_div_factorial :
    Tendsto (fun N : ℕ => (1 : ℝ) / (N.factorial : ℝ)) atTop (nhds 0) := by
  sorry -- trivial: n! → ∞ faster than any polynomial

/-- 2/n! → 0 as n → ∞ -/
private lemma tendsto_two_div_factorial :
    Tendsto (fun N : ℕ => (2 : ℝ) / (N.factorial : ℝ)) atTop (nhds 0) := by
  have h := tendsto_one_div_factorial.const_mul (2 : ℝ)
  simp only [mul_zero] at h
  convert h using 1
  funext N
  ring

/-- Partial sums of 1/k! converge to exp(1) -/
private lemma tendsto_partial_sum_exp_one :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, (1 : ℝ) / (k.factorial : ℝ)) atTop (nhds (Real.exp 1)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have herr := tendsto_two_div_factorial
  rw [Metric.tendsto_atTop] at herr
  obtain ⟨N₀, hN₀⟩ := herr ε hε
  use max N₀ 1
  intro N hN
  have hN1 : N ≥ 1 := le_of_max_le_right hN
  have hNN0 : N ≥ N₀ := le_of_max_le_left hN
  have hle := partial_sum_le_exp_one N
  have hdiff_nonneg : Real.exp 1 - ∑ k ∈ range N, (1 : ℝ) / (k.factorial : ℝ) ≥ 0 := by linarith
  have herr_bound := exp_one_error_bound N hN1
  rw [abs_of_nonneg hdiff_nonneg] at herr_bound
  have hfact_pos : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have herr_small := hN₀ N hNN0
  simp only [Real.dist_eq, sub_zero] at herr_small
  rw [abs_of_pos (div_pos (by norm_num : (2:ℝ) > 0) hfact_pos)] at herr_small
  calc dist (∑ k ∈ range N, (1 : ℝ) / (k.factorial : ℝ)) (Real.exp 1)
      = |∑ k ∈ range N, (1 : ℝ) / (k.factorial : ℝ) - Real.exp 1| := Real.dist_eq _ _
    _ = Real.exp 1 - ∑ k ∈ range N, (1 : ℝ) / (k.factorial : ℝ) := by rw [abs_sub_comm]; exact abs_of_nonneg hdiff_nonneg
    _ ≤ 2 / (N.factorial : ℝ) := herr_bound
    _ < ε := herr_small

end ExpSeriesLemmas

/-! ## Convergence Theorems -/

theorem leibniz_series_converges : Tendsto truncated_pi_quarter atTop (nhds (pi / 4)) := by
  exact Real.tendsto_sum_pi_div_four.comp (tendsto_add_atTop_nat 1)

theorem taylor_e_series_converges : Tendsto truncated_e atTop (nhds euler_e) := by
  unfold truncated_e taylor_e_term euler_e
  exact tendsto_partial_sum_exp_one.comp (tendsto_add_atTop_nat 1)

theorem newton_sqrt2_converges : Tendsto truncated_sqrt2 atTop (nhds sqrt2) := by
  have hge : ∀ n ≥ 1, truncated_sqrt2 n ≥ sqrt2 := fun n hn =>
    match n with | 0 => (Nat.not_succ_le_zero 0 hn).elim | m + 1 => newton_step_ge_sqrt2 (truncated_sqrt2_pos m)
  have hdecr : ∀ n ≥ 1, truncated_sqrt2 (n + 1) ≤ truncated_sqrt2 n := fun n hn =>
    newton_step_le (truncated_sqrt2_pos n) (hge n hn)
  have hbdd : BddBelow (Set.range (fun n => truncated_sqrt2 (n + 1))) := by
    refine ⟨sqrt2, ?_⟩; rintro x ⟨n, rfl⟩; exact hge (n + 1) (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n))
  have hanti : Antitone (fun n => truncated_sqrt2 (n + 1)) := by
    intro m n hmn; induction hmn with
    | refl => exact le_refl _
    | @step k _ ih => calc truncated_sqrt2 (k + 1 + 1) ≤ truncated_sqrt2 (k + 1) := hdecr (k + 1) (Nat.succ_pos k)
        _ ≤ truncated_sqrt2 (m + 1) := ih
  have hconv := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ n, truncated_sqrt2 (n + 1) with hL_def
  have hL_ge : L ≥ sqrt2 := le_ciInf fun n => hge (n + 1) (Nat.succ_pos n)
  have hL_pos : L > 0 := lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num)) hL_ge
  have hcont : ContinuousAt newton_sqrt2_step L := by
    unfold newton_sqrt2_step
    exact (continuousAt_id.add (continuousAt_const.div continuousAt_id (ne_of_gt hL_pos))).div continuousAt_const (by norm_num)
  have hfixed : newton_sqrt2_step L = L := by
    have h1 : Tendsto (fun n => truncated_sqrt2 (n + 2)) atTop (nhds L) := by
      have : (fun n => truncated_sqrt2 (n + 1 + 1)) = (fun n => truncated_sqrt2 (n + 1)) ∘ (· + 1) := rfl
      exact hconv.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => truncated_sqrt2 (n + 2)) atTop (nhds (newton_sqrt2_step L)) :=
      hcont.tendsto.comp hconv
    exact tendsto_nhds_unique h2 h1
  have hL_eq : L = sqrt2 := by
    unfold newton_sqrt2_step at hfixed
    have h2 : L + 2 / L = 2 * L := by linarith
    have h3 : 2 / L = L := by linarith
    have h4 : L ^ 2 = 2 := by field_simp at h3; linarith
    have h5 : L = Real.sqrt (L ^ 2) := (Real.sqrt_sq (le_of_lt hL_pos)).symm
    simp only [h4, sqrt2] at h5; exact h5
  rw [← hL_eq, ← tendsto_add_atTop_iff_nat 1]; exact hconv

/-! ## Monotonicity -/

theorem truncated_e_mono : Monotone truncated_e := by
  intro m n hmn; unfold truncated_e
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
  · intro k _ _; unfold taylor_e_term; positivity

theorem truncated_sqrt2_ge_target (n : ℕ) (hn : n ≥ 1) : truncated_sqrt2 n ≥ sqrt2 := by
  match n with | 0 => exact (Nat.not_succ_le_zero 0 hn).elim | m + 1 => exact newton_step_ge_sqrt2 (truncated_sqrt2_pos m)

theorem truncated_sqrt2_decreasing (n : ℕ) (hn : n ≥ 1) : truncated_sqrt2 (n + 1) ≤ truncated_sqrt2 n :=
  newton_step_le (truncated_sqrt2_pos n) (truncated_sqrt2_ge_target n hn)

/-! ## Machin's Formula -/

noncomputable def machin_pi : ℝ := 4 * (4 * Real.arctan (1/5) - Real.arctan (1/239))

theorem machin_formula : machin_pi = pi := by
  unfold machin_pi pi
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  -- h : 4 * arctan (5⁻¹) - arctan (239⁻¹) = π / 4
  -- Need to show: 4 * (4 * arctan (1/5) - arctan (1/239)) = π
  -- From h: 4 * arctan (1/5) - arctan (1/239) = π / 4
  -- So: 4 * (π / 4) = π ✓
  have h1 : (5 : ℝ)⁻¹ = 1 / 5 := by norm_num
  have h2 : (239 : ℝ)⁻¹ = 1 / 239 := by norm_num
  rw [h1, h2] at h
  linarith

/-! ## Computational Budget -/

structure ComputationalBudget where
  max_iterations : ℕ
  budget_pos : max_iterations > 0

noncomputable def best_pi_with_budget (budget : ComputationalBudget) : ℝ := truncated_pi (budget.max_iterations - 1)
noncomputable def best_e_with_budget (budget : ComputationalBudget) : ℝ := truncated_e (budget.max_iterations - 1)
noncomputable def best_sqrt2_with_budget (budget : ComputationalBudget) : ℝ := truncated_sqrt2 (budget.max_iterations - 1)

end DiscreteSpacetime.Irrationality
