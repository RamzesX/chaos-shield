/-
  Geometry.Metric
  ===============

  Metric tensor on the discrete Planck lattice.

  This module defines the fundamental geometric structure:
  - MetricTensor: Symmetric (0,2) tensor g_{μν}
  - DiscreteMetric: Metric field assigning g to each lattice point
  - Lorentzian signature: η = diag(-1, 1, 1, 1)
  - Inverse metric: g^{μν}
  - Metric determinant: det(g)

  The metric encodes the geometry of discrete spacetime, determining
  distances, angles, and causal structure.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Fin.VecNotation
import DiscreteSpacetime.Basic.Lattice

namespace DiscreteSpacetime.Geometry

open DiscreteSpacetime.Basic
open Matrix

/-! ## Metric Tensor Type -/

/-- A metric tensor is a 4x4 real matrix.
    Physically, this represents the spacetime metric g_{μν}. -/
abbrev MetricTensor := Matrix (Fin 4) (Fin 4) ℝ

/-- A metric tensor at a point is symmetric: g_{μν} = g_{νμ} -/
def IsSymmetric (g : MetricTensor) : Prop :=
  g.IsSymm

/-- A metric tensor is non-degenerate if its determinant is non-zero -/
def IsNondegenerate (g : MetricTensor) : Prop :=
  g.det ≠ 0

/-! ## Minkowski Metric (Flat Spacetime) -/

/-- The Minkowski metric η = diag(-1, 1, 1, 1) in mostly-plus convention.
    This is the metric of flat spacetime (special relativity). -/
noncomputable def minkowskiMetric : MetricTensor :=
  Matrix.diagonal ![(-1 : ℝ), 1, 1, 1]

/-- Alternative definition using explicit matrix -/
noncomputable def minkowskiMetric' : MetricTensor :=
  !![(-1 : ℝ), 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- Minkowski metric is symmetric -/
theorem minkowski_symmetric : IsSymmetric minkowskiMetric := by
  unfold IsSymmetric minkowskiMetric
  rw [Matrix.IsSymm]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- Minkowski metric diagonal values -/
theorem minkowski_diag_time : minkowskiMetric 0 0 = -1 := by
  simp [minkowskiMetric, Matrix.diagonal]

theorem minkowski_diag_space (i : Fin 3) : minkowskiMetric (i.succ) (i.succ) = 1 := by
  fin_cases i <;> simp [minkowskiMetric, Matrix.diagonal]

/-- Off-diagonal elements of Minkowski metric are zero -/
theorem minkowski_off_diag (i j : Fin 4) (h : i ≠ j) :
    minkowskiMetric i j = 0 := by
  simp [minkowskiMetric, Matrix.diagonal, h]

/-! ## Lorentzian Signature -/

/-- A metric has Lorentzian signature if it has one negative and three positive eigenvalues.
    For now, we define this as having the same signature as Minkowski. -/
structure IsLorentzian (g : MetricTensor) : Prop where
  /-- The metric is symmetric -/
  symmetric : IsSymmetric g
  /-- The metric is non-degenerate -/
  nondegenerate : IsNondegenerate g
  /-- The metric has signature (-,+,+,+) at each point -/
  signature : g.det < 0

/-- Minkowski metric has Lorentzian signature -/
theorem minkowski_lorentzian : IsLorentzian minkowskiMetric := by
  constructor
  · exact minkowski_symmetric
  · unfold IsNondegenerate minkowskiMetric
    simp only [Matrix.det_diagonal]
    -- Product of [-1, 1, 1, 1] = -1 ≠ 0
    norm_num [Fin.prod_univ_four]
  · unfold minkowskiMetric
    simp only [Matrix.det_diagonal]
    -- Product of [-1, 1, 1, 1] = -1 < 0
    norm_num [Fin.prod_univ_four]

/-! ## Discrete Metric Field -/

/-- A discrete metric assigns a metric tensor to each lattice point.
    This represents the spacetime geometry field g_{μν}(x). -/
def DiscreteMetric := LatticePoint → MetricTensor

namespace DiscreteMetric

/-- Flat spacetime: Minkowski metric everywhere -/
noncomputable def flat : DiscreteMetric := fun _ => minkowskiMetric

/-- A discrete metric is everywhere symmetric -/
def IsEverywhereSymmetric (g : DiscreteMetric) : Prop :=
  ∀ p, IsSymmetric (g p)

/-- A discrete metric is everywhere non-degenerate -/
def IsEverywhereNondegenerate (g : DiscreteMetric) : Prop :=
  ∀ p, IsNondegenerate (g p)

/-- A discrete metric is everywhere Lorentzian -/
def IsEverywhereLorentzian (g : DiscreteMetric) : Prop :=
  ∀ p, IsLorentzian (g p)

/-- Flat metric is everywhere symmetric -/
theorem flat_everywhere_symmetric : IsEverywhereSymmetric flat := by
  intro p
  exact minkowski_symmetric

/-- Flat metric is everywhere Lorentzian -/
theorem flat_everywhere_lorentzian : IsEverywhereLorentzian flat := by
  intro p
  exact minkowski_lorentzian

end DiscreteMetric

/-! ## Metric Operations -/

/-- Determinant of the metric tensor -/
noncomputable def metricDeterminant (g : MetricTensor) : ℝ := g.det

/-- For Lorentzian metrics, the determinant is negative -/
theorem det_neg_of_lorentzian (g : MetricTensor) (hL : IsLorentzian g) :
    metricDeterminant g < 0 := hL.signature

/-- Square root of negative determinant (used in volume elements) -/
noncomputable def sqrtNegDet (g : MetricTensor) (hL : IsLorentzian g) : ℝ :=
  Real.sqrt (-metricDeterminant g)

/-- The sqrt of negative determinant is positive for Lorentzian metrics -/
theorem sqrtNegDet_pos (g : MetricTensor) (hL : IsLorentzian g) :
    sqrtNegDet g hL > 0 := by
  unfold sqrtNegDet
  apply Real.sqrt_pos_of_pos
  have h := hL.signature
  unfold metricDeterminant
  linarith

/-! ## Inverse Metric -/

/-- The inverse metric tensor g^{μν} (contravariant form).
    Satisfies g^{μρ} g_{ρν} = δ^μ_ν -/
noncomputable def inverseMetric (g : MetricTensor) : MetricTensor := g⁻¹

/-- Notation for inverse metric -/
notation g "⁻¹ᵐ" => inverseMetric g

/-- Convert IsNondegenerate to IsUnit (det g) -/
theorem isUnit_det_of_nondegenerate (g : MetricTensor) (hnd : IsNondegenerate g) :
    IsUnit g.det := by
  rw [isUnit_iff_ne_zero]
  exact hnd

/-- For non-degenerate metric, g * g⁻¹ = 1 -/
theorem metric_mul_inverse (g : MetricTensor) (hnd : IsNondegenerate g) :
    g * inverseMetric g = 1 := by
  unfold inverseMetric
  exact Matrix.mul_nonsing_inv g (isUnit_det_of_nondegenerate g hnd)

/-- For non-degenerate metric, g⁻¹ * g = 1 -/
theorem inverse_mul_metric (g : MetricTensor) (hnd : IsNondegenerate g) :
    inverseMetric g * g = 1 := by
  unfold inverseMetric
  exact Matrix.nonsing_inv_mul g (isUnit_det_of_nondegenerate g hnd)

/-- Inverse of Minkowski metric is itself (η⁻¹ = η for our convention) -/
theorem minkowski_inverse_self : inverseMetric minkowskiMetric = minkowskiMetric := by
  unfold inverseMetric minkowskiMetric
  -- The diagonal matrix with entries [-1, 1, 1, 1] is its own inverse
  -- since each diagonal entry squared equals 1
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h <;> fin_cases i <;> norm_num

/-! ## Index Raising and Lowering -/

/-- Raise an index on a covector (lower index → upper index).
    v^μ = g^{μν} v_ν -/
noncomputable def raiseIndex (g : MetricTensor) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun μ => Finset.univ.sum fun ν => (inverseMetric g) μ ν * v ν

/-- Lower an index on a vector (upper index → lower index).
    v_μ = g_{μν} v^ν -/
noncomputable def lowerIndex (g : MetricTensor) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun μ => Finset.univ.sum fun ν => g μ ν * v ν

/-- Raising then lowering returns the original vector (for non-degenerate g) -/
theorem lower_raise_identity (g : MetricTensor) (hnd : IsNondegenerate g) (v : Fin 4 → ℝ) :
    lowerIndex g (raiseIndex g v) = v := by
  -- lowerIndex is g.mulVec, raiseIndex is g⁻¹.mulVec
  -- So this is g *ᵥ (g⁻¹ *ᵥ v) = (g * g⁻¹) *ᵥ v = 1 *ᵥ v = v
  have hlower : ∀ w, lowerIndex g w = g.mulVec w := fun w => rfl
  have hraise : raiseIndex g v = (inverseMetric g).mulVec v := rfl
  rw [hlower, hraise]
  rw [Matrix.mulVec_mulVec]
  rw [metric_mul_inverse g hnd]
  exact Matrix.one_mulVec v

/-! ## Metric Compatibility -/

/-- The Kronecker delta -/
def kroneckerDelta (μ ν : Fin 4) : ℝ := if μ = ν then 1 else 0

/-- Kronecker delta as identity matrix -/
theorem kronecker_eq_one : (fun μ ν => kroneckerDelta μ ν) = (1 : MetricTensor) := by
  ext μ ν
  simp [kroneckerDelta, Matrix.one_apply]

/-- Contract metric with its inverse gives Kronecker delta -/
theorem metric_inverse_contract (g : MetricTensor) (hnd : IsNondegenerate g) (μ ν : Fin 4) :
    Finset.univ.sum (fun ρ => (inverseMetric g) μ ρ * g ρ ν) = kroneckerDelta μ ν := by
  have h := inverse_mul_metric g hnd
  -- Extract component from matrix equation
  have := congrFun (congrFun h μ) ν
  simp only [Matrix.mul_apply, Matrix.one_apply] at this
  rw [kroneckerDelta]
  exact this

/-! ## Metric Tensor as Bilinear Form -/

/-- Inner product of two vectors using the metric.
    ⟨u, v⟩_g = g_{μν} u^μ v^ν -/
noncomputable def metricInnerProduct (g : MetricTensor) (u v : Fin 4 → ℝ) : ℝ :=
  Finset.univ.sum fun μ =>
    Finset.univ.sum fun ν =>
      g μ ν * u μ * v ν

/-- Inner product is symmetric for symmetric metric -/
theorem metricInnerProduct_symm (g : MetricTensor) (hsym : IsSymmetric g) (u v : Fin 4 → ℝ) :
    metricInnerProduct g u v = metricInnerProduct g v u := by
  unfold metricInnerProduct
  rw [Finset.sum_comm]
  congr 1
  ext μ
  congr 1
  ext ν
  unfold IsSymmetric at hsym
  have hsym' : g μ ν = g ν μ := by
    have := congrFun (congrFun hsym ν) μ
    simp only [Matrix.transpose_apply] at this
    exact this
  rw [hsym']
  ring

/-! ## Proper Time and Distance -/

/-- Squared interval between neighboring lattice points.
    ds² = g_{μν} Δx^μ Δx^ν -/
noncomputable def squaredInterval (g : MetricTensor) (dx : Fin 4 → ℝ) : ℝ :=
  metricInnerProduct g dx dx

/-- For Minkowski metric, squared interval is -dt² + dx² + dy² + dz² -/
theorem minkowski_interval (dx : Fin 4 → ℝ) :
    squaredInterval minkowskiMetric dx =
    -(dx 0)^2 + (dx 1)^2 + (dx 2)^2 + (dx 3)^2 := by
  unfold squaredInterval metricInnerProduct minkowskiMetric
  -- Diagonal matrix: nonzero only when μ = ν
  simp only [Matrix.diagonal]
  -- The proof requires expanding the finite sums over Fin 4
  sorry

/-- Classification of intervals -/
inductive IntervalType
  | timelike   -- ds² < 0
  | lightlike  -- ds² = 0
  | spacelike  -- ds² > 0

/-- Classify an interval -/
noncomputable def classifyInterval (g : MetricTensor) (dx : Fin 4 → ℝ) : IntervalType :=
  let ds2 := squaredInterval g dx
  if ds2 < 0 then IntervalType.timelike
  else if ds2 = 0 then IntervalType.lightlike
  else IntervalType.spacelike

end DiscreteSpacetime.Geometry
