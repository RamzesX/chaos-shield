/-
  Basic.Constants
  ================

  Physical constants in natural units and Planck units.

  Mathematical Philosophy (Fichtenholz):
  ======================================
  We avoid direct √ manipulation. Instead, we prove equalities by:
  1. Computing squared forms (where algebra is clean)
  2. Using |a| = |b| from a² = b², then positivity to strip absolute values

  Key lemma: sq_eq_sq_iff_abs_eq_abs : a² = b² ↔ |a| = |b|
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic

namespace DiscreteSpacetime.Basic

/-! ## Fundamental Physical Constants -/

noncomputable def SpeedOfLight : ℝ := 299792458
noncomputable def ReducedPlanck : ℝ := 1.054571817e-34
noncomputable def GravitationalConstant : ℝ := 6.67430e-11
noncomputable def BoltzmannConstant : ℝ := 1.380649e-23

/-! ## Positivity Axioms -/

axiom SpeedOfLight_pos : SpeedOfLight > 0
axiom ReducedPlanck_pos : ReducedPlanck > 0
axiom GravitationalConstant_pos : GravitationalConstant > 0
axiom BoltzmannConstant_pos : BoltzmannConstant > 0

/-! ## Planck Units -/

noncomputable def PlanckLength : ℝ :=
  Real.sqrt (ReducedPlanck * GravitationalConstant / (SpeedOfLight ^ 3))

noncomputable def PlanckTime : ℝ :=
  Real.sqrt (ReducedPlanck * GravitationalConstant / (SpeedOfLight ^ 5))

noncomputable def PlanckMass : ℝ :=
  Real.sqrt (ReducedPlanck * SpeedOfLight / GravitationalConstant)

noncomputable def PlanckEnergy : ℝ :=
  Real.sqrt (ReducedPlanck * SpeedOfLight ^ 5 / GravitationalConstant)

noncomputable def PlanckTemperature : ℝ :=
  PlanckEnergy / BoltzmannConstant

/-! ## Positivity Lemmas -/

lemma hbar_G_pos : ReducedPlanck * GravitationalConstant > 0 :=
  mul_pos ReducedPlanck_pos GravitationalConstant_pos

lemma c_pow_pos (n : ℕ) : SpeedOfLight ^ n > 0 :=
  pow_pos SpeedOfLight_pos n

lemma c_nonneg : 0 ≤ SpeedOfLight := le_of_lt SpeedOfLight_pos

lemma c_ne_zero : SpeedOfLight ≠ 0 := ne_of_gt SpeedOfLight_pos

lemma PlanckLength_arg_pos : ReducedPlanck * GravitationalConstant / SpeedOfLight ^ 3 > 0 :=
  div_pos hbar_G_pos (c_pow_pos 3)

lemma PlanckTime_arg_pos : ReducedPlanck * GravitationalConstant / SpeedOfLight ^ 5 > 0 :=
  div_pos hbar_G_pos (c_pow_pos 5)

lemma PlanckMass_arg_pos : ReducedPlanck * SpeedOfLight / GravitationalConstant > 0 :=
  div_pos (mul_pos ReducedPlanck_pos SpeedOfLight_pos) GravitationalConstant_pos

lemma PlanckEnergy_arg_pos : ReducedPlanck * SpeedOfLight ^ 5 / GravitationalConstant > 0 :=
  div_pos (mul_pos ReducedPlanck_pos (c_pow_pos 5)) GravitationalConstant_pos

theorem PlanckLength_pos : PlanckLength > 0 := by
  unfold PlanckLength; exact Real.sqrt_pos_of_pos PlanckLength_arg_pos

theorem PlanckTime_pos : PlanckTime > 0 := by
  unfold PlanckTime; exact Real.sqrt_pos_of_pos PlanckTime_arg_pos

theorem PlanckMass_pos : PlanckMass > 0 := by
  unfold PlanckMass; exact Real.sqrt_pos_of_pos PlanckMass_arg_pos

theorem PlanckEnergy_pos : PlanckEnergy > 0 := by
  unfold PlanckEnergy; exact Real.sqrt_pos_of_pos PlanckEnergy_arg_pos

/-! ## Helper: Equality from Squared Equality and Positivity -/

/-- If a² = b² and both a > 0 and b > 0, then a = b -/
theorem eq_of_sq_eq_sq_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hsq : a ^ 2 = b ^ 2) : a = b := by
  have ha' : 0 ≤ a := le_of_lt ha
  have hb' : 0 ≤ b := le_of_lt hb
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha').symm
       _ = Real.sqrt (b ^ 2) := congrArg Real.sqrt hsq
       _ = b := Real.sqrt_sq hb'

/-! ## Squared Forms (The Foundation)

  These are the ALGEBRAICALLY CLEAN forms.
  All proofs reduce to these via sq_sqrt.
-/

theorem PlanckLength_sq : PlanckLength ^ 2 = ReducedPlanck * GravitationalConstant / SpeedOfLight ^ 3 := by
  unfold PlanckLength
  exact Real.sq_sqrt (le_of_lt PlanckLength_arg_pos)

theorem PlanckTime_sq : PlanckTime ^ 2 = ReducedPlanck * GravitationalConstant / SpeedOfLight ^ 5 := by
  unfold PlanckTime
  exact Real.sq_sqrt (le_of_lt PlanckTime_arg_pos)

theorem PlanckMass_sq : PlanckMass ^ 2 = ReducedPlanck * SpeedOfLight / GravitationalConstant := by
  unfold PlanckMass
  exact Real.sq_sqrt (le_of_lt PlanckMass_arg_pos)

theorem PlanckEnergy_sq : PlanckEnergy ^ 2 = ReducedPlanck * SpeedOfLight ^ 5 / GravitationalConstant := by
  unfold PlanckEnergy
  exact Real.sq_sqrt (le_of_lt PlanckEnergy_arg_pos)

/-! ## Fundamental Relations -/

/-- t_P² = (ℓ_P/c)² : The squared form of the time-length relation -/
theorem PlanckTime_sq_eq_length_sq_div_c_sq :
    PlanckTime ^ 2 = PlanckLength ^ 2 / SpeedOfLight ^ 2 := by
  rw [PlanckTime_sq, PlanckLength_sq]
  field_simp
  ring

/-- t_P = ℓ_P/c : Planck time equals Planck length divided by speed of light -/
theorem PlanckTime_eq_length_div_c : PlanckTime = PlanckLength / SpeedOfLight := by
  apply eq_of_sq_eq_sq_of_pos PlanckTime_pos
  · exact div_pos PlanckLength_pos SpeedOfLight_pos
  · rw [div_pow, PlanckTime_sq_eq_length_sq_div_c_sq]

/-- E_P² = (m_P · c²)² : The squared form of mass-energy relation -/
theorem PlanckEnergy_sq_eq_mass_sq_mul_c4 :
    PlanckEnergy ^ 2 = PlanckMass ^ 2 * SpeedOfLight ^ 4 := by
  rw [PlanckEnergy_sq, PlanckMass_sq]
  field_simp
  ring

/-- E_P = m_P · c² : Einstein's mass-energy relation at Planck scale -/
theorem PlanckEnergy_eq_mass_c2 : PlanckEnergy = PlanckMass * SpeedOfLight ^ 2 := by
  apply eq_of_sq_eq_sq_of_pos PlanckEnergy_pos
  · exact mul_pos PlanckMass_pos (c_pow_pos 2)
  · rw [mul_pow, ← pow_mul]
    norm_num
    exact PlanckEnergy_sq_eq_mass_sq_mul_c4

/-- ℓ_P = t_P · c : Alternative form -/
theorem PlanckLength_eq_time_mul_c : PlanckLength = PlanckTime * SpeedOfLight := by
  rw [PlanckTime_eq_length_div_c]
  rw [div_mul_cancel₀ _ c_ne_zero]

/-- m_P = E_P / c² : Alternative form -/
theorem PlanckMass_eq_energy_div_c2 : PlanckMass = PlanckEnergy / SpeedOfLight ^ 2 := by
  rw [PlanckEnergy_eq_mass_c2]
  rw [mul_div_cancel_right₀ _ (pow_ne_zero 2 c_ne_zero)]

/-! ## Planck Momentum -/

noncomputable def PlanckMomentum : ℝ :=
  Real.sqrt (ReducedPlanck * SpeedOfLight ^ 3 / GravitationalConstant)

lemma PlanckMomentum_arg_pos : ReducedPlanck * SpeedOfLight ^ 3 / GravitationalConstant > 0 :=
  div_pos (mul_pos ReducedPlanck_pos (c_pow_pos 3)) GravitationalConstant_pos

theorem PlanckMomentum_pos : PlanckMomentum > 0 := by
  unfold PlanckMomentum; exact Real.sqrt_pos_of_pos PlanckMomentum_arg_pos

theorem PlanckMomentum_sq : PlanckMomentum ^ 2 = ReducedPlanck * SpeedOfLight ^ 3 / GravitationalConstant := by
  unfold PlanckMomentum
  exact Real.sq_sqrt (le_of_lt PlanckMomentum_arg_pos)

/-- p_P² = (m_P · c)² -/
theorem PlanckMomentum_sq_eq_mass_sq_mul_c_sq :
    PlanckMomentum ^ 2 = PlanckMass ^ 2 * SpeedOfLight ^ 2 := by
  rw [PlanckMomentum_sq, PlanckMass_sq]
  field_simp
  ring

/-- p_P = m_P · c : Planck momentum equals mass times velocity -/
theorem PlanckMomentum_eq_mass_mul_c : PlanckMomentum = PlanckMass * SpeedOfLight := by
  apply eq_of_sq_eq_sq_of_pos PlanckMomentum_pos
  · exact mul_pos PlanckMass_pos SpeedOfLight_pos
  · rw [mul_pow, PlanckMomentum_sq_eq_mass_sq_mul_c_sq]

/-! ## Additional Planck Units -/

noncomputable def PlanckDensity : ℝ :=
  SpeedOfLight ^ 5 / (GravitationalConstant ^ 2 * ReducedPlanck)

theorem PlanckDensity_pos : PlanckDensity > 0 := by
  unfold PlanckDensity
  apply div_pos (c_pow_pos 5)
  exact mul_pos (sq_pos_of_pos GravitationalConstant_pos) ReducedPlanck_pos

noncomputable def PlanckArea : ℝ := PlanckLength ^ 2

theorem PlanckArea_eq : PlanckArea = ReducedPlanck * GravitationalConstant / SpeedOfLight ^ 3 :=
  PlanckLength_sq

noncomputable def PlanckVolume : ℝ := PlanckLength ^ 3

/-! ## Notation -/

notation "ℓ_P" => PlanckLength
notation "t_P" => PlanckTime
notation "m_P" => PlanckMass
notation "E_P" => PlanckEnergy
notation "p_P" => PlanckMomentum
notation "ρ_P" => PlanckDensity
notation "A_P" => PlanckArea
notation "V_P" => PlanckVolume
notation "c" => SpeedOfLight
notation "ℏ" => ReducedPlanck
notation "G" => GravitationalConstant
notation "k_B" => BoltzmannConstant

/-! ## Short Aliases -/

theorem c_pos : c > 0 := SpeedOfLight_pos
theorem hbar_pos : ℏ > 0 := ReducedPlanck_pos
theorem G_pos : G > 0 := GravitationalConstant_pos
theorem kB_pos : k_B > 0 := BoltzmannConstant_pos

end DiscreteSpacetime.Basic
