/-
  Geometry.Connection
  ====================

  Christoffel symbols and covariant derivatives on the discrete Planck lattice.

  This module defines the Levi-Civita connection:
  - Christoffel symbols: Gamma^rho_{mu nu}
  - Definition via discrete metric derivatives
  - THEOREM: Christoffel symmetry in lower indices
  - Covariant derivative of vectors and tensors

  The Christoffel symbols encode how vectors change under parallel transport.
  They are derived from the metric, making the connection metric-compatible.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset
import DiscreteSpacetime.Basic.Lattice
import DiscreteSpacetime.Basic.Operators
import DiscreteSpacetime.Geometry.Metric

namespace DiscreteSpacetime.Geometry

open DiscreteSpacetime.Basic
open Matrix

/-! ## Discrete Metric Derivatives -/

/-- Partial derivative of metric component g_{αβ} along direction μ.
    Uses symmetric difference for O(l_P²) accuracy:
    ∂_μ g_{αβ} ≈ [g_{αβ}(p + e_μ) - g_{αβ}(p - e_μ)] / (2 l_P) -/
noncomputable def metricDerivative (g : DiscreteMetric) (μ α β : Fin 4)
    (p : LatticePoint) : ℝ :=
  symmetricDiff (fun q => (g q) α β) μ p

/-- Notation for metric derivative -/
notation "∂[" μ "]" g:max "[" α "," β "]" => metricDerivative g μ α β

/-! ## Christoffel Symbols -/

/-- Christoffel symbol of the second kind: Gamma^rho_{mu nu}.
    Defined as:
    Gamma^rho_{mu nu} = (1/2) g^{rho sigma} (∂_mu g_{nu sigma} + ∂_nu g_{mu sigma} - ∂_sigma g_{mu nu})

    This is the unique torsion-free, metric-compatible connection. -/
noncomputable def christoffelSymbol (g : DiscreteMetric) (ρ μ ν : Fin 4)
    (p : LatticePoint) : ℝ :=
  (1/2 : ℝ) * Finset.univ.sum fun σ =>
    (inverseMetric (g p)) ρ σ *
    (metricDerivative g μ ν σ p + metricDerivative g ν μ σ p - metricDerivative g σ μ ν p)

/-- Notation for Christoffel symbol -/
notation "Γ[" ρ "," μ "," ν "]" => christoffelSymbol · ρ μ ν

/-- Alternative form emphasizing the three derivative terms -/
noncomputable def christoffelSymbol' (g : DiscreteMetric) (ρ μ ν : Fin 4)
    (p : LatticePoint) : ℝ :=
  (1/2 : ℝ) * Finset.univ.sum fun σ =>
    (inverseMetric (g p)) ρ σ *
    (∂[μ] g [ν, σ] p + ∂[ν] g [μ, σ] p - ∂[σ] g [μ, ν] p)

/-- The two definitions are equal -/
theorem christoffel_eq_christoffel' (g : DiscreteMetric) (ρ μ ν : Fin 4) (p : LatticePoint) :
    christoffelSymbol g ρ μ ν p = christoffelSymbol' g ρ μ ν p := by
  rfl

/-! ## Christoffel Symmetry Theorem -/

/-- KEY THEOREM: Christoffel symbols are symmetric in the lower indices.
    Gamma^rho_{mu nu} = Gamma^rho_{nu mu}

    PROOF: This follows from the symmetry of partial derivatives of the metric
    (which is symmetric), combined with the symmetric structure of the
    Christoffel formula itself.

    The Christoffel formula has three terms:
    - ∂_μ g_{νσ} : becomes ∂_ν g_{μσ} under μ ↔ ν
    - ∂_ν g_{μσ} : becomes ∂_μ g_{νσ} under μ ↔ ν
    - ∂_σ g_{μν} : unchanged since g_{μν} = g_{νμ}

    The first two terms swap, and the third is invariant, so the total is symmetric. -/
theorem christoffel_symmetry (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (ρ μ ν : Fin 4) (p : LatticePoint) :
    christoffelSymbol g ρ μ ν p = christoffelSymbol g ρ ν μ p := by
  unfold christoffelSymbol
  -- The key insight: the sum of the first two terms is symmetric in μ, ν
  -- and the third term is symmetric because g is symmetric
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  -- We need to show:
  -- ∂_μ g_{νσ} + ∂_ν g_{μσ} - ∂_σ g_{μν} = ∂_ν g_{μσ} + ∂_μ g_{νσ} - ∂_σ g_{νμ}
  -- The first two terms clearly swap
  -- For the third term, we need g_{μν} = g_{νμ}
  have h_metric_sym : (g p) μ ν = (g p) ν μ := by
    have := hSym p
    unfold IsSymmetric at this
    have := congrFun (congrFun this ν) μ
    simp only [Matrix.transpose_apply] at this
    exact this
  -- Now we need that ∂_σ g_{μν} = ∂_σ g_{νμ}
  have h_deriv_sym : metricDerivative g σ μ ν p = metricDerivative g σ ν μ p := by
    unfold metricDerivative symmetricDiff
    -- Extract symmetry at both shifted points
    have hpos := hSym (p.shiftPos σ)
    have hneg := hSym (p.shiftNeg σ)
    unfold IsSymmetric at hpos hneg
    -- Get element-wise equalities: g(p+) μ ν = g(p+) ν μ
    have hpos_elem : (g (p.shiftPos σ)) μ ν = (g (p.shiftPos σ)) ν μ := by
      have := congrFun (congrFun hpos ν) μ
      simp only [Matrix.transpose_apply] at this
      exact this
    have hneg_elem : (g (p.shiftNeg σ)) μ ν = (g (p.shiftNeg σ)) ν μ := by
      have := congrFun (congrFun hneg ν) μ
      simp only [Matrix.transpose_apply] at this
      exact this
    -- Rewrite both sides (simp beta-reduces the lambda application)
    simp only [hpos_elem, hneg_elem]
  -- Now combine: first two terms swap, third is invariant
  rw [h_deriv_sym]
  ring

/-- Corollary: swapping lower indices does not change the Christoffel symbol -/
theorem christoffel_lower_swap (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (ρ μ ν : Fin 4) (p : LatticePoint) :
    christoffelSymbol g ρ μ ν p = christoffelSymbol g ρ ν μ p :=
  christoffel_symmetry g hSym ρ μ ν p

/-! ## Christoffel Symbols for Flat Spacetime -/

/-- For flat spacetime (constant Minkowski metric), all Christoffel symbols vanish.
    This is because all derivatives of the metric are zero. -/
theorem christoffel_flat_vanishes (ρ μ ν : Fin 4) (p : LatticePoint) :
    christoffelSymbol DiscreteMetric.flat ρ μ ν p = 0 := by
  unfold christoffelSymbol
  -- For constant metric, all symmetric differences are zero
  have h_deriv_zero : ∀ α β γ, metricDerivative DiscreteMetric.flat α β γ p = 0 := by
    intros α β γ
    unfold metricDerivative symmetricDiff DiscreteMetric.flat
    -- minkowskiMetric is constant, so f(p+e) - f(p-e) = 0
    simp only [sub_self, zero_div]
  simp only [h_deriv_zero, add_zero, sub_zero, mul_zero, Finset.sum_const_zero]

/-! ## Covariant Derivative -/

/-- Covariant derivative of a vector field V^μ along direction ν.
    ∇_ν V^μ = ∂_ν V^μ + Gamma^μ_{νρ} V^ρ -/
noncomputable def covariantDerivVector (g : DiscreteMetric) (V : LatticeVectorField)
    (μ ν : Fin 4) (p : LatticePoint) : ℝ :=
  symmetricDiff (fun q => V q μ) ν p +
  Finset.univ.sum fun ρ => christoffelSymbol g μ ν ρ p * V p ρ

/-- Covariant derivative of a covector (1-form) W_μ along direction ν.
    ∇_ν W_μ = ∂_ν W_μ - Gamma^ρ_{νμ} W_ρ -/
noncomputable def covariantDerivCovector (g : DiscreteMetric) (W : LatticeVectorField)
    (μ ν : Fin 4) (p : LatticePoint) : ℝ :=
  symmetricDiff (fun q => W q μ) ν p -
  Finset.univ.sum fun ρ => christoffelSymbol g ρ ν μ p * W p ρ

/-- Covariant derivative of a (2,0) tensor field T^{μν} along direction ρ.
    ∇_ρ T^{μν} = ∂_ρ T^{μν} + Gamma^μ_{ρσ} T^{σν} + Gamma^ν_{ρσ} T^{μσ} -/
noncomputable def covariantDerivTensor20 (g : DiscreteMetric) (T : LatticeTensorField)
    (μ ν ρ : Fin 4) (p : LatticePoint) : ℝ :=
  symmetricDiff (fun q => T q μ ν) ρ p +
  Finset.univ.sum fun σ => christoffelSymbol g μ ρ σ p * T p σ ν +
  Finset.univ.sum fun σ => christoffelSymbol g ν ρ σ p * T p μ σ

/-- Covariant derivative of a (0,2) tensor field T_{μν} along direction ρ.
    ∇_ρ T_{μν} = ∂_ρ T_{μν} - Gamma^σ_{ρμ} T_{σν} - Gamma^σ_{ρν} T_{μσ} -/
noncomputable def covariantDerivTensor02 (g : DiscreteMetric) (T : LatticeTensorField)
    (μ ν ρ : Fin 4) (p : LatticePoint) : ℝ :=
  let sum1 := Finset.univ.sum (fun σ => christoffelSymbol g σ ρ μ p * T p σ ν)
  let sum2 := Finset.univ.sum (fun σ => christoffelSymbol g σ ρ ν p * T p μ σ)
  symmetricDiff (fun q => T q μ ν) ρ p - sum1 - sum2

/-! ## Metric Compatibility -/

/-! ### Christoffel Lower Index -/

/-- Contraction of Christoffel symbol with metric -/
noncomputable def christoffelLower (g : DiscreteMetric) (ρ μ ν : Fin 4) (p : LatticePoint) : ℝ :=
  Finset.univ.sum fun σ => (g p) ρ σ * christoffelSymbol g σ μ ν p

/-- The lowered Christoffel symbol has a simpler form:
    Gamma_{ρμν} = (1/2)(∂_μ g_{νρ} + ∂_ν g_{μρ} - ∂_ρ g_{μν}) -/
theorem christoffel_lower_formula (g : DiscreteMetric) (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (ρ μ ν : Fin 4) (p : LatticePoint) :
    christoffelLower g ρ μ ν p =
    (1/2 : ℝ) * (metricDerivative g μ ν ρ p + metricDerivative g ν μ ρ p - metricDerivative g ρ μ ν p) := by
  unfold christoffelLower christoffelSymbol
  -- Goal: Σ_σ g_{ρσ} * ((1/2) * Σ_τ g^{στ} * D_τ) = (1/2) * D_ρ

  -- Step 1: Key lemma - metric contraction gives Kronecker delta
  have h_contract : ∀ τ : Fin 4,
      Finset.univ.sum (fun σ => (g p) ρ σ * (inverseMetric (g p)) σ τ) =
      if ρ = τ then 1 else 0 := by
    intro τ
    have hnd_p := hNd p
    have h := metric_mul_inverse (g p) hnd_p
    have := congrFun (congrFun h ρ) τ
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    exact this

  -- Step 2: Distribute g_{ρσ} into the inner sum and exchange sum order
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

  -- Step 3: Define the derivative term for clarity
  set D := fun τ : Fin 4 =>
    metricDerivative g μ ν τ p + metricDerivative g ν μ τ p - metricDerivative g τ μ ν p with hD

  -- Step 4: Transform the double sum step by step
  have h_inner : ∀ τ : Fin 4,
      Finset.univ.sum (fun σ => (g p) ρ σ * (1 / 2 * ((inverseMetric (g p)) σ τ * D τ))) =
      if ρ = τ then 1 / 2 * D τ else 0 := by
    intro τ
    calc Finset.univ.sum (fun σ => (g p) ρ σ * (1 / 2 * ((inverseMetric (g p)) σ τ * D τ)))
        = Finset.univ.sum (fun σ => (1 / 2 * D τ) * ((g p) ρ σ * (inverseMetric (g p)) σ τ)) := by
          apply Finset.sum_congr rfl; intro σ _; ring
      _ = (1 / 2 * D τ) * Finset.univ.sum (fun σ => (g p) ρ σ * (inverseMetric (g p)) σ τ) := by
          rw [← Finset.mul_sum]
      _ = (1 / 2 * D τ) * (if ρ = τ then 1 else 0) := by rw [h_contract]
      _ = if ρ = τ then 1 / 2 * D τ else 0 := by split_ifs <;> ring

  -- Step 5: Apply h_inner to rewrite the outer sum
  calc Finset.univ.sum (fun τ => Finset.univ.sum (fun σ =>
          (g p) ρ σ * (1 / 2 * ((inverseMetric (g p)) σ τ * D τ))))
      = Finset.univ.sum (fun τ => if ρ = τ then 1 / 2 * D τ else 0) := by
        apply Finset.sum_congr rfl; intro τ _; exact h_inner τ
    _ = if ρ ∈ Finset.univ then 1 / 2 * D ρ else 0 := Finset.sum_ite_eq Finset.univ ρ _
    _ = 1 / 2 * D ρ := by simp only [Finset.mem_univ, if_true]
    _ = 1 / 2 * (metricDerivative g μ ν ρ p + metricDerivative g ν μ ρ p - metricDerivative g ρ μ ν p) := by rfl

/-! ### Helper Lemmas -/

/-- Helper: The sum Σ_σ Γ^σ_{ρμ} g_{σν} equals christoffelLower g ν ρ μ.
    This follows from metric symmetry: g_{σν} = g_{νσ}. -/
theorem christoffel_metric_contraction (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (ν ρ μ : Fin 4) (p : LatticePoint) :
    Finset.univ.sum (fun σ => christoffelSymbol g σ ρ μ p * (g p) σ ν) =
    christoffelLower g ν ρ μ p := by
  unfold christoffelLower
  apply Finset.sum_congr rfl
  intro σ _
  -- Need: Γ^σ_{ρμ} * g_{σν} = g_{νσ} * Γ^σ_{ρμ}
  -- By commutativity of multiplication and metric symmetry
  have h_sym : (g p) σ ν = (g p) ν σ := by
    have := hSym p
    unfold IsSymmetric at this
    have := congrFun (congrFun this ν) σ
    simp only [Matrix.transpose_apply] at this
    exact this
  rw [h_sym]
  ring

/-- Helper: Symmetry of metric derivative in the last two indices.
    ∂_ρ g_{μν} = ∂_ρ g_{νμ} when metric is symmetric. -/
theorem metricDerivative_symm (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (ρ μ ν : Fin 4) (p : LatticePoint) :
    metricDerivative g ρ μ ν p = metricDerivative g ρ ν μ p := by
  unfold metricDerivative symmetricDiff
  have hpos := hSym (p.shiftPos ρ)
  have hneg := hSym (p.shiftNeg ρ)
  unfold IsSymmetric at hpos hneg
  have hpos_elem : (g (p.shiftPos ρ)) μ ν = (g (p.shiftPos ρ)) ν μ := by
    have := congrFun (congrFun hpos ν) μ
    simp only [Matrix.transpose_apply] at this
    exact this
  have hneg_elem : (g (p.shiftNeg ρ)) μ ν = (g (p.shiftNeg ρ)) ν μ := by
    have := congrFun (congrFun hneg ν) μ
    simp only [Matrix.transpose_apply] at this
    exact this
  simp only [hpos_elem, hneg_elem]

/-- The Levi-Civita connection is metric compatible: ∇_ρ g_{μν} = 0.
    This is a fundamental property that follows from the definition of
    Christoffel symbols in terms of metric derivatives.

    PROOF: The two Christoffel terms contracted with the metric give
    christoffelLower, which by christoffel_lower_formula expand to
    derivative terms that exactly cancel the partial derivative. -/
theorem metric_compatibility (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (μ ν ρ : Fin 4) (p : LatticePoint) :
    covariantDerivTensor02 g (fun q α β => (g q) α β) μ ν ρ p = 0 := by
  unfold covariantDerivTensor02
  -- Goal: ∂_ρ g_{μν} - Σ_σ Γ^σ_{ρμ} g_{σν} - Σ_σ Γ^σ_{ρν} g_{μσ} = 0

  -- Step 1: Rewrite Christoffel sums as christoffelLower
  have h1 : Finset.univ.sum (fun σ => christoffelSymbol g σ ρ μ p * (g p) σ ν) =
            christoffelLower g ν ρ μ p := christoffel_metric_contraction g hSym ν ρ μ p

  -- For second sum: Σ_σ Γ^σ_{ρν} g_{μσ} = Σ_σ Γ^σ_{ρν} g_{σμ} (by symmetry) = christoffelLower g μ ρ ν
  have h2_pre : ∀ σ, (g p) μ σ = (g p) σ μ := by
    intro σ
    have := hSym p
    unfold IsSymmetric at this
    have := congrFun (congrFun this μ) σ
    simp only [Matrix.transpose_apply] at this
    exact this.symm
  have h2 : Finset.univ.sum (fun σ => christoffelSymbol g σ ρ ν p * (g p) μ σ) =
            christoffelLower g μ ρ ν p := by
    calc Finset.univ.sum (fun σ => christoffelSymbol g σ ρ ν p * (g p) μ σ)
        = Finset.univ.sum (fun σ => christoffelSymbol g σ ρ ν p * (g p) σ μ) := by
          apply Finset.sum_congr rfl; intro σ _; rw [h2_pre]
      _ = christoffelLower g μ ρ ν p := christoffel_metric_contraction g hSym μ ρ ν p

  rw [h1, h2]

  -- Step 2: Apply christoffel_lower_formula
  rw [christoffel_lower_formula g hNd ν ρ μ p]
  rw [christoffel_lower_formula g hNd μ ρ ν p]

  -- Step 3: Use metric derivative symmetry
  -- ∂_ρ g_{νμ} = ∂_ρ g_{μν}
  have hd1 : metricDerivative g ρ ν μ p = metricDerivative g ρ μ ν p :=
    metricDerivative_symm g hSym ρ ν μ p

  -- Step 4: The goal simplifies to:
  -- symmetricDiff g_{μν} ρ p - (1/2)(...) - (1/2)(...) = 0
  -- Note: symmetricDiff (fun q => g q μ ν) = metricDerivative g ρ μ ν p

  -- Unfold metricDerivative in christoffel_lower_formula results
  unfold metricDerivative

  -- Step 5: Algebraic simplification using symmetry
  -- LHS: ∂_ρ g_{μν} - (1/2)(∂_ρ g_{μν} + ∂_μ g_{ρν} - ∂_ν g_{ρμ})
  --                 - (1/2)(∂_ρ g_{νμ} + ∂_ν g_{ρμ} - ∂_μ g_{ρν})
  -- Using ∂_ρ g_{νμ} = ∂_ρ g_{μν} (from hd1, now unfolded):
  -- = ∂_ρ g_{μν} - (1/2)(2*∂_ρ g_{μν})
  -- = 0

  -- hd1 is now about symmetricDiff after unfold
  have hd1' : symmetricDiff (fun q => (g q) ν μ) ρ p = symmetricDiff (fun q => (g q) μ ν) ρ p := by
    unfold symmetricDiff
    have hpos := hSym (p.shiftPos ρ)
    have hneg := hSym (p.shiftNeg ρ)
    unfold IsSymmetric at hpos hneg
    have hpos_elem : (g (p.shiftPos ρ)) ν μ = (g (p.shiftPos ρ)) μ ν := by
      have := congrFun (congrFun hpos μ) ν
      simp only [Matrix.transpose_apply] at this
      exact this
    have hneg_elem : (g (p.shiftNeg ρ)) ν μ = (g (p.shiftNeg ρ)) μ ν := by
      have := congrFun (congrFun hneg μ) ν
      simp only [Matrix.transpose_apply] at this
      exact this
    simp only [hpos_elem, hneg_elem]

  rw [hd1']
  ring

/-! ## Parallel Transport -/

/-- A vector field V is parallel transported along direction μ if ∇_μ V = 0 -/
def IsParallelTransported (g : DiscreteMetric) (V : LatticeVectorField) (μ : Fin 4)
    (p : LatticePoint) : Prop :=
  ∀ ν, covariantDerivVector g V ν μ p = 0

/-- A curve is a geodesic if its tangent vector is parallel transported along itself.
    For discrete lattice, we consider geodesic as piecewise linear path. -/
structure DiscreteGeodesic (g : DiscreteMetric) where
  /-- Path as sequence of lattice points -/
  path : ℕ → LatticePoint
  /-- Tangent vectors at each point (discrete approximation) -/
  tangent : ℕ → Fin 4 → ℝ
  /-- Geodesic equation: tangent is parallel transported -/
  geodesic_eq : ∀ n μ ν, covariantDerivVector g (fun _ => tangent n) μ ν (path n) = 0

/-! ## Christoffel Trace -/

/-- Trace of Christoffel symbol: Gamma^μ_{μν} -/
noncomputable def christoffelTrace (g : DiscreteMetric) (ν : Fin 4) (p : LatticePoint) : ℝ :=
  Finset.univ.sum fun μ => christoffelSymbol g μ μ ν p

/-- The trace is related to the derivative of ln(sqrt(-g)).
    Gamma^μ_{μν} = ∂_ν ln(sqrt(-g)) -/
theorem christoffel_trace_formula (g : DiscreteMetric) (hL : DiscreteMetric.IsEverywhereLorentzian g)
    (ν : Fin 4) (p : LatticePoint) :
    christoffelTrace g ν p =
    symmetricDiff (fun q => Real.log (Real.sqrt (-(g q).det))) ν p := by
  -- This follows from the identity ∂_ν g = g · g^{μρ} ∂_ν g_{μρ}
  sorry -- Requires determinant derivative formula

end DiscreteSpacetime.Geometry
