/-
  Basic.Operators
  ================

  Discrete differential operators on the Planck lattice.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Field.Basic
import DiscreteSpacetime.Basic.Constants
import DiscreteSpacetime.Basic.Lattice

namespace DiscreteSpacetime.Basic

/-! ## Planck Length Utility Lemmas -/

lemma ℓ_P_ne_zero : ℓ_P ≠ 0 := ne_of_gt PlanckLength_pos
lemma two_ℓ_P_ne_zero : 2 * ℓ_P ≠ 0 := mul_ne_zero (by norm_num) ℓ_P_ne_zero
lemma ℓ_P_sq_ne_zero : ℓ_P ^ 2 ≠ 0 := pow_ne_zero 2 ℓ_P_ne_zero
lemma ℓ_P_sq_pos : ℓ_P ^ 2 > 0 := sq_pos_of_pos PlanckLength_pos

/-! ## Scalar Field Lemmas -/

@[simp] lemma scalarField_add_apply (f g : LatticeScalarField) (p : LatticePoint) :
    (f + g) p = f p + g p := rfl

@[simp] lemma scalarField_smul_apply (k : ℝ) (f : LatticeScalarField) (p : LatticePoint) :
    (k • f) p = k * f p := rfl

@[simp] lemma scalarField_mul_apply (f g : LatticeScalarField) (p : LatticePoint) :
    (f * g) p = f p * g p := rfl

/-! ## Forward Difference Operator -/

noncomputable def forwardDiff (f : LatticeScalarField) (μ : SpacetimeIndex)
    (p : LatticePoint) : ℝ :=
  (f (p.shiftPos μ) - f p) / ℓ_P

theorem forwardDiff_add (f g : LatticeScalarField) (μ : SpacetimeIndex) (p : LatticePoint) :
    forwardDiff (f + g) μ p = forwardDiff f μ p + forwardDiff g μ p := by
  unfold forwardDiff
  simp only [scalarField_add_apply]
  have h : ℓ_P ≠ 0 := ℓ_P_ne_zero
  field_simp
  ring

theorem forwardDiff_smul (k : ℝ) (f : LatticeScalarField) (μ : SpacetimeIndex) (p : LatticePoint) :
    forwardDiff (k • f) μ p = k * forwardDiff f μ p := by
  unfold forwardDiff
  simp only [scalarField_smul_apply]
  have h : ℓ_P ≠ 0 := ℓ_P_ne_zero
  field_simp
  ring

theorem forwardDiff_const (k : ℝ) (μ : SpacetimeIndex) (p : LatticePoint) :
    forwardDiff (fun _ => k) μ p = 0 := by
  unfold forwardDiff
  simp only [sub_self, zero_div]

/-! ## Backward Difference Operator -/

noncomputable def backwardDiff (f : LatticeScalarField) (μ : SpacetimeIndex)
    (p : LatticePoint) : ℝ :=
  (f p - f (p.shiftNeg μ)) / ℓ_P

theorem backwardDiff_add (f g : LatticeScalarField) (μ : SpacetimeIndex) (p : LatticePoint) :
    backwardDiff (f + g) μ p = backwardDiff f μ p + backwardDiff g μ p := by
  unfold backwardDiff
  simp only [scalarField_add_apply]
  have h : ℓ_P ≠ 0 := ℓ_P_ne_zero
  field_simp
  ring

theorem backwardDiff_smul (k : ℝ) (f : LatticeScalarField) (μ : SpacetimeIndex) (p : LatticePoint) :
    backwardDiff (k • f) μ p = k * backwardDiff f μ p := by
  unfold backwardDiff
  simp only [scalarField_smul_apply]
  have h : ℓ_P ≠ 0 := ℓ_P_ne_zero
  field_simp
  ring

theorem backwardDiff_const (k : ℝ) (μ : SpacetimeIndex) (p : LatticePoint) :
    backwardDiff (fun _ => k) μ p = 0 := by
  unfold backwardDiff
  simp only [sub_self, zero_div]

/-! ## Symmetric (Central) Difference Operator -/

noncomputable def symmetricDiff (f : LatticeScalarField) (μ : SpacetimeIndex)
    (p : LatticePoint) : ℝ :=
  (f (p.shiftPos μ) - f (p.shiftNeg μ)) / (2 * ℓ_P)

theorem symmetricDiff_add (f g : LatticeScalarField) (μ : SpacetimeIndex) (p : LatticePoint) :
    symmetricDiff (f + g) μ p = symmetricDiff f μ p + symmetricDiff g μ p := by
  unfold symmetricDiff
  simp only [scalarField_add_apply]
  have h : 2 * ℓ_P ≠ 0 := two_ℓ_P_ne_zero
  field_simp
  ring

theorem symmetricDiff_smul (k : ℝ) (f : LatticeScalarField) (μ : SpacetimeIndex) (p : LatticePoint) :
    symmetricDiff (k • f) μ p = k * symmetricDiff f μ p := by
  unfold symmetricDiff
  simp only [scalarField_smul_apply]
  have h : 2 * ℓ_P ≠ 0 := two_ℓ_P_ne_zero
  field_simp
  ring

theorem symmetricDiff_const (k : ℝ) (μ : SpacetimeIndex) (p : LatticePoint) :
    symmetricDiff (fun _ => k) μ p = 0 := by
  unfold symmetricDiff
  simp only [sub_self, zero_div]

theorem symmetricDiff_eq_average (f : LatticeScalarField) (μ : SpacetimeIndex) (p : LatticePoint) :
    symmetricDiff f μ p = (forwardDiff f μ p + backwardDiff f μ p) / 2 := by
  unfold symmetricDiff forwardDiff backwardDiff
  have h : ℓ_P ≠ 0 := ℓ_P_ne_zero
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  -- (f⁺ - f)/ℓ + (f - f⁻)/ℓ = (f⁺ - f⁻)/ℓ
  have step1 : (f (p.shiftPos μ) - f p) / ℓ_P + (f p - f (p.shiftNeg μ)) / ℓ_P =
               (f (p.shiftPos μ) - f (p.shiftNeg μ)) / ℓ_P := by
    rw [← add_div]
    congr 1
    ring
  -- (a/ℓ) / 2 = a / (2ℓ)
  have step2 : (f (p.shiftPos μ) - f (p.shiftNeg μ)) / ℓ_P / 2 =
               (f (p.shiftPos μ) - f (p.shiftNeg μ)) / (2 * ℓ_P) := by
    rw [div_div]
    congr 1
    ring
  rw [step1, step2]

/-! ## Second Derivative -/

noncomputable def secondDeriv (f : LatticeScalarField) (μ : SpacetimeIndex)
    (p : LatticePoint) : ℝ :=
  (f (p.shiftPos μ) - 2 * f p + f (p.shiftNeg μ)) / (ℓ_P ^ 2)

theorem secondDeriv_eq_forward_backward_composition
    (f : LatticeScalarField) (μ : SpacetimeIndex) (p : LatticePoint) :
    secondDeriv f μ p = forwardDiff (fun q => backwardDiff f μ q) μ p := by
  unfold secondDeriv forwardDiff backwardDiff
  simp only [LatticePoint.shiftNeg_shiftPos, LatticePoint.shiftPos_shiftNeg]
  have h : ℓ_P ≠ 0 := ℓ_P_ne_zero
  field_simp
  ring

theorem secondDeriv_eq_backward_forward_composition
    (f : LatticeScalarField) (μ : SpacetimeIndex) (p : LatticePoint) :
    secondDeriv f μ p = backwardDiff (fun q => forwardDiff f μ q) μ p := by
  unfold secondDeriv forwardDiff backwardDiff
  simp only [LatticePoint.shiftNeg_shiftPos, LatticePoint.shiftPos_shiftNeg]
  have h : ℓ_P ≠ 0 := ℓ_P_ne_zero
  field_simp
  ring

theorem secondDeriv_add (f g : LatticeScalarField) (μ : SpacetimeIndex) (p : LatticePoint) :
    secondDeriv (f + g) μ p = secondDeriv f μ p + secondDeriv g μ p := by
  unfold secondDeriv
  simp only [scalarField_add_apply]
  have h : ℓ_P ^ 2 ≠ 0 := ℓ_P_sq_ne_zero
  field_simp
  ring

theorem secondDeriv_smul (k : ℝ) (f : LatticeScalarField) (μ : SpacetimeIndex) (p : LatticePoint) :
    secondDeriv (k • f) μ p = k * secondDeriv f μ p := by
  unfold secondDeriv
  simp only [scalarField_smul_apply]
  have h : ℓ_P ^ 2 ≠ 0 := ℓ_P_sq_ne_zero
  field_simp
  ring

theorem secondDeriv_const (k : ℝ) (μ : SpacetimeIndex) (p : LatticePoint) :
    secondDeriv (fun _ => k) μ p = 0 := by
  unfold secondDeriv
  have h : k - 2 * k + k = 0 := by ring
  rw [h, zero_div]

theorem secondDeriv_linear (a b : ℝ) (μ : SpacetimeIndex) (p : LatticePoint) :
    secondDeriv (fun q => a * (q.index.coord μ : ℝ) + b) μ p = 0 := by
  unfold secondDeriv LatticePoint.shiftPos LatticePoint.shiftNeg
  -- First rewrite using the coord lemmas
  have hp : (p.index.shiftPos μ).coord μ = p.index.coord μ + 1 := LatticeIndex.shiftPos_coord_self p.index μ
  have hm : (p.index.shiftNeg μ).coord μ = p.index.coord μ - 1 := LatticeIndex.shiftNeg_coord_self p.index μ
  simp only [hp, hm, Int.cast_add, Int.cast_one, Int.cast_sub]
  have calc_zero : a * (↑(p.index.coord μ) + 1) + b - 2 * (a * ↑(p.index.coord μ) + b) +
                   (a * (↑(p.index.coord μ) - 1) + b) = 0 := by ring
  rw [calc_zero, zero_div]

/-! ## Discrete Laplacian -/

noncomputable def discreteLaplacian (f : LatticeScalarField) (p : LatticePoint) : ℝ :=
  Finset.univ.sum fun μ => secondDeriv f μ p

theorem discreteLaplacian_add (f g : LatticeScalarField) (p : LatticePoint) :
    discreteLaplacian (f + g) p = discreteLaplacian f p + discreteLaplacian g p := by
  simp only [discreteLaplacian, secondDeriv_add, ← Finset.sum_add_distrib]

theorem discreteLaplacian_smul (k : ℝ) (f : LatticeScalarField) (p : LatticePoint) :
    discreteLaplacian (k • f) p = k * discreteLaplacian f p := by
  simp only [discreteLaplacian, secondDeriv_smul, ← Finset.mul_sum]

theorem discreteLaplacian_const (k : ℝ) (p : LatticePoint) :
    discreteLaplacian (fun _ => k) p = 0 := by
  simp only [discreteLaplacian, secondDeriv_const, Finset.sum_const_zero]

/-! ## Spatial Laplacian -/

noncomputable def spatialLaplacian (f : LatticeScalarField) (p : LatticePoint) : ℝ :=
  (Finset.univ : Finset (Fin 3)).sum fun i => secondDeriv f (spaceIndex i) p

theorem spatialLaplacian_add (f g : LatticeScalarField) (p : LatticePoint) :
    spatialLaplacian (f + g) p = spatialLaplacian f p + spatialLaplacian g p := by
  simp only [spatialLaplacian, secondDeriv_add, ← Finset.sum_add_distrib]

theorem spatialLaplacian_smul (k : ℝ) (f : LatticeScalarField) (p : LatticePoint) :
    spatialLaplacian (k • f) p = k * spatialLaplacian f p := by
  simp only [spatialLaplacian, secondDeriv_smul, ← Finset.mul_sum]

theorem spatialLaplacian_const (k : ℝ) (p : LatticePoint) :
    spatialLaplacian (fun _ => k) p = 0 := by
  simp only [spatialLaplacian, secondDeriv_const, Finset.sum_const_zero]

/-! ## Discrete d'Alembertian -/

noncomputable def discreteDAlembert (f : LatticeScalarField) (p : LatticePoint) : ℝ :=
  -secondDeriv f timeIndex p + spatialLaplacian f p

theorem discreteDAlembert_add (f g : LatticeScalarField) (p : LatticePoint) :
    discreteDAlembert (f + g) p = discreteDAlembert f p + discreteDAlembert g p := by
  simp only [discreteDAlembert, secondDeriv_add, spatialLaplacian_add]
  ring

theorem discreteDAlembert_smul (k : ℝ) (f : LatticeScalarField) (p : LatticePoint) :
    discreteDAlembert (k • f) p = k * discreteDAlembert f p := by
  simp only [discreteDAlembert, secondDeriv_smul, spatialLaplacian_smul]
  ring

theorem discreteDAlembert_const (k : ℝ) (p : LatticePoint) :
    discreteDAlembert (fun _ => k) p = 0 := by
  simp only [discreteDAlembert, secondDeriv_const, spatialLaplacian_const, neg_zero, zero_add]

/-! ## Discrete Gradient and Divergence -/

noncomputable def discreteGradient (f : LatticeScalarField) : LatticeVectorField :=
  fun p μ => symmetricDiff f μ p

theorem discreteGradient_add (f g : LatticeScalarField) (p : LatticePoint) (μ : SpacetimeIndex) :
    discreteGradient (f + g) p μ = discreteGradient f p μ + discreteGradient g p μ :=
  symmetricDiff_add f g μ p

theorem discreteGradient_const (k : ℝ) (p : LatticePoint) (μ : SpacetimeIndex) :
    discreteGradient (fun _ => k) p μ = 0 :=
  symmetricDiff_const k μ p

noncomputable def discreteDivergence (v : LatticeVectorField) : LatticeScalarField :=
  fun p => Finset.univ.sum fun μ => backwardDiff (fun q => v q μ) μ p

/-! ## Operator Commutativity

Note: Forward differences commute with forward differences, and backward with backward.
Mixed forward-backward differences do NOT commute in general (they use different stencils). -/

theorem forwardDiff_comm (f : LatticeScalarField) (μ ν : SpacetimeIndex) (p : LatticePoint) :
    forwardDiff (fun q => forwardDiff f ν q) μ p =
    forwardDiff (fun q => forwardDiff f μ q) ν p := by
  unfold forwardDiff
  have hcomm : (p.shiftPos μ).shiftPos ν = (p.shiftPos ν).shiftPos μ :=
    LatticePoint.shiftPos_comm p μ ν
  have h : ℓ_P ≠ 0 := ℓ_P_ne_zero
  field_simp
  rw [hcomm]
  ring

theorem backwardDiff_comm (f : LatticeScalarField) (μ ν : SpacetimeIndex) (p : LatticePoint) :
    backwardDiff (fun q => backwardDiff f ν q) μ p =
    backwardDiff (fun q => backwardDiff f μ q) ν p := by
  unfold backwardDiff
  have hcomm : (p.shiftNeg μ).shiftNeg ν = (p.shiftNeg ν).shiftNeg μ :=
    LatticePoint.shiftNeg_comm p μ ν
  have h : ℓ_P ≠ 0 := ℓ_P_ne_zero
  field_simp
  rw [hcomm]
  ring

/-! ## Discrete Product Rule -/

theorem forwardDiff_mul (f g : LatticeScalarField) (μ : SpacetimeIndex) (p : LatticePoint) :
    forwardDiff (f * g) μ p =
    f p * forwardDiff g μ p + forwardDiff f μ p * g (p.shiftPos μ) := by
  unfold forwardDiff
  simp only [scalarField_mul_apply]
  have h : ℓ_P ≠ 0 := ℓ_P_ne_zero
  field_simp
  ring

theorem backwardDiff_mul (f g : LatticeScalarField) (μ : SpacetimeIndex) (p : LatticePoint) :
    backwardDiff (f * g) μ p =
    f p * backwardDiff g μ p + backwardDiff f μ p * g (p.shiftNeg μ) := by
  unfold backwardDiff
  simp only [scalarField_mul_apply]
  have h : ℓ_P ≠ 0 := ℓ_P_ne_zero
  field_simp
  ring

/-! ## Higher-Order Operators -/

noncomputable def fourthDeriv (f : LatticeScalarField) (μ : SpacetimeIndex)
    (p : LatticePoint) : ℝ :=
  secondDeriv (fun q => secondDeriv f μ q) μ p

theorem fourthDeriv_const (k : ℝ) (μ : SpacetimeIndex) (p : LatticePoint) :
    fourthDeriv (fun _ => k) μ p = 0 := by
  simp only [fourthDeriv, secondDeriv_const]

noncomputable def biLaplacian (f : LatticeScalarField) (p : LatticePoint) : ℝ :=
  discreteLaplacian (fun q => discreteLaplacian f q) p

theorem biLaplacian_const (k : ℝ) (p : LatticePoint) :
    biLaplacian (fun _ => k) p = 0 := by
  simp only [biLaplacian, discreteLaplacian_const]

/-! ## Inner Product -/

noncomputable def latticeInnerProduct (f g : LatticeScalarField)
    (points : Finset LatticePoint) : ℝ :=
  points.sum fun p => f p * g p * (ℓ_P ^ spacetimeDim)

theorem latticeInnerProduct_comm (f g : LatticeScalarField) (points : Finset LatticePoint) :
    latticeInnerProduct f g points = latticeInnerProduct g f points := by
  simp only [latticeInnerProduct]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-! ## Maximum Principle -/

theorem discrete_maximum_principle
    (f : LatticeScalarField) (p : LatticePoint)
    (hmax : ∀ q ∈ nearestNeighbors p, f q ≤ f p) :
    discreteLaplacian f p ≤ 0 := by
  unfold discreteLaplacian secondDeriv
  apply Finset.sum_nonpos
  intro μ _
  have hpos : f (p.shiftPos μ) ≤ f p := by
    apply hmax
    rw [mem_nearestNeighbors_iff]
    exact ⟨μ, Or.inl rfl⟩
  have hneg : f (p.shiftNeg μ) ≤ f p := by
    apply hmax
    rw [mem_nearestNeighbors_iff]
    exact ⟨μ, Or.inr rfl⟩
  have hsum : f (p.shiftPos μ) + f (p.shiftNeg μ) - 2 * f p ≤ 0 := by linarith
  have heq : f (p.shiftPos μ) - 2 * f p + f (p.shiftNeg μ) =
             f (p.shiftPos μ) + f (p.shiftNeg μ) - 2 * f p := by ring
  rw [heq]
  exact div_nonpos_of_nonpos_of_nonneg hsum (le_of_lt ℓ_P_sq_pos)

end DiscreteSpacetime.Basic
