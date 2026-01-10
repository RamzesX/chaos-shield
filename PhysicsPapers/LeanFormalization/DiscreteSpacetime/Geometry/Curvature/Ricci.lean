/-
  Geometry.Curvature.Ricci
  ========================

  Ricci tensor and its properties.

  Definitions:
  - ricciTensor: R_{μν} = R^ρ_{μρν} (trace of Riemann)
  - ricciTensor': Alternative definition via metric contraction

  PROVEN:
  - ricci'_symmetric: R_{μν} = R_{νμ} (for ricciTensor', from pair swap)
  - ricciTensor_eq_ricciTensor': Bridge between two definitions
  - ricci_symmetric: R_{μν} = R_{νμ} (main theorem)
-/

import DiscreteSpacetime.Geometry.Curvature.Common
import DiscreteSpacetime.Geometry.Curvature.Symmetries

namespace DiscreteSpacetime.Geometry.Curvature

open DiscreteSpacetime.Basic
open DiscreteSpacetime.Geometry
open Matrix
open BigOperators
open Finset

/-! ## Ricci Tensor Definitions -/

/-- Ricci tensor R_{μν} = R^ρ_{μρν} (contraction on first and third indices).
    This is the trace of the Riemann tensor. -/
noncomputable def ricciTensor (g : DiscreteMetric) (μ ν : Fin 4)
    (p : LatticePoint) : ℝ :=
  ∑ ρ : Fin 4, riemannTensor g ρ μ ρ ν p

/-- Alternative: Contract using the metric.
    R_{μν} = g^{ρσ} R_{ρμσν} -/
noncomputable def ricciTensor' (g : DiscreteMetric) (μ ν : Fin 4)
    (p : LatticePoint) : ℝ :=
  ∑ ρ : Fin 4, ∑ σ : Fin 4, (inverseMetric (g p)) ρ σ * riemannLower g ρ μ σ ν p

/-! ## Ricci Tensor Symmetry via ricciTensor' -/

/-- Inverse metric is symmetric: g^{ρσ} = g^{σρ} -/
lemma inverseMetric_symm (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (p : LatticePoint) (ρ σ : Fin 4) :
    (inverseMetric (g p)) ρ σ = (inverseMetric (g p)) σ ρ := by
  -- The inverse of a symmetric matrix is symmetric
  unfold inverseMetric
  have h_sym_p := hSym p
  have h_inv_symm : ((g p)⁻¹)ᵀ = (g p)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]
    unfold IsSymmetric at h_sym_p
    rw [h_sym_p]
  have := congrFun (congrFun h_inv_symm σ) ρ
  simp only [Matrix.transpose_apply] at this
  exact this

/-- Ricci tensor (alternative definition) is symmetric: R_{μν} = R_{νμ}

    PROOF:
    R_{μν} = g^{ρσ} R_{ρμσν}
           = g^{ρσ} R_{σνρμ}    (pair swap: R_{ρσμν} = R_{μνρσ}, here ρ,μ,σ,ν → σ,ν,ρ,μ)
           = g^{σρ} R_{ρνσμ}    (relabel dummy indices ρ↔σ)
           = g^{ρσ} R_{ρνσμ}    (inverse metric symmetry)
           = R_{νμ} -/
theorem ricci'_symmetric (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (μ ν : Fin 4) (p : LatticePoint) :
    ricciTensor' g μ ν p = ricciTensor' g ν μ p := by
  unfold ricciTensor'
  -- Step 1: Apply pair swap to R_{ρμσν}
  -- R_{ρμσν} = R_{σνρμ} (pair swap with indices ρ,μ,σ,ν)
  have h_swap : ∀ ρ σ, riemannLower g ρ μ σ ν p = riemannLower g σ ν ρ μ p := by
    intros ρ σ
    exact riemann_lower_pair_swap g hSym hNd ρ μ σ ν p
  -- Step 2: Rewrite using pair swap
  conv_lhs =>
    congr
    · skip
    · ext ρ
      congr
      · skip
      · ext σ
        rw [h_swap ρ σ]
  -- Now LHS = Σ_{ρσ} g^{ρσ} R_{σνρμ}
  -- Step 3: Exchange summation indices ρ ↔ σ
  rw [Finset.sum_comm]
  -- Now LHS = Σ_{σρ} g^{ρσ} R_{σνρμ} = Σ_{σρ} g^{ρσ} R_{σνρμ}
  -- Relabel: call σ→ρ', ρ→σ' to get Σ_{ρ'σ'} g^{σ'ρ'} R_{ρ'νσ'μ}
  -- Step 4: Use inverse metric symmetry g^{ρσ} = g^{σρ}
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro ρ _
  -- Need: g^{ρσ} * R_{σνρμ} = g^{σρ} * R_{σνρμ}
  -- Use g^{ρσ} = g^{σρ}
  rw [inverseMetric_symm g hSym hNd p ρ σ]

/-! ## Bridge Lemma: ricciTensor = ricciTensor' -/

/-- Key identity: metric contraction gives Kronecker delta.
    Σ_λ g_{ρλ} g^{λσ} = δ_{ρσ} -/
lemma metric_contraction_delta (g : DiscreteMetric) (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (p : LatticePoint) (ρ σ : Fin 4) :
    ∑ lam : Fin 4, (g p) ρ lam * (inverseMetric (g p)) lam σ = if ρ = σ then 1 else 0 := by
  have h := metric_mul_inverse (g p) (hNd p)
  have := congrFun (congrFun h ρ) σ
  simp only [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

/-- Raising then lowering an index gives back the original.
    R^ρ_{σμν} = Σ_λ g^{ρλ} R_{λσμν}

    This is the definition of raising the first index. -/
lemma riemann_raise_lower (g : DiscreteMetric) (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (ρ σ μ ν : Fin 4) (p : LatticePoint) :
    riemannTensor g ρ σ μ ν p = ∑ lam : Fin 4, (inverseMetric (g p)) ρ lam * riemannLower g lam σ μ ν p := by
  -- R_{λσμν} = Σ_τ g_{λτ} R^τ_{σμν}
  -- So: Σ_λ g^{ρλ} R_{λσμν} = Σ_λ g^{ρλ} Σ_τ g_{λτ} R^τ_{σμν}
  --                        = Σ_τ (Σ_λ g^{ρλ} g_{λτ}) R^τ_{σμν}
  --                        = Σ_τ δ^ρ_τ R^τ_{σμν}
  --                        = R^ρ_{σμν}
  unfold riemannLower
  -- Use matrix multiplication identity
  have h_delta : ∀ tau : Fin 4, ∑ lam : Fin 4, (inverseMetric (g p)) ρ lam * (g p) lam tau =
                               if ρ = tau then 1 else 0 := by
    intro tau
    have h := inverse_mul_metric (g p) (hNd p)
    have := congrFun (congrFun h ρ) tau
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  -- Compute RHS step by step
  symm
  calc ∑ lam : Fin 4, (inverseMetric (g p)) ρ lam * ∑ tau : Fin 4, (g p) lam tau * riemannTensor g tau σ μ ν p
      = ∑ lam : Fin 4, ∑ tau : Fin 4, (inverseMetric (g p)) ρ lam * ((g p) lam tau * riemannTensor g tau σ μ ν p) := by
        apply Finset.sum_congr rfl; intro lam _; rw [Finset.mul_sum]
    _ = ∑ tau : Fin 4, ∑ lam : Fin 4, (inverseMetric (g p)) ρ lam * ((g p) lam tau * riemannTensor g tau σ μ ν p) := by
        rw [Finset.sum_comm]
    _ = ∑ tau : Fin 4, ∑ lam : Fin 4, ((inverseMetric (g p)) ρ lam * (g p) lam tau) * riemannTensor g tau σ μ ν p := by
        apply Finset.sum_congr rfl; intro tau _; apply Finset.sum_congr rfl; intro lam _; ring
    _ = ∑ tau : Fin 4, (∑ lam : Fin 4, (inverseMetric (g p)) ρ lam * (g p) lam tau) * riemannTensor g tau σ μ ν p := by
        apply Finset.sum_congr rfl; intro tau _; rw [← Finset.sum_mul]
    _ = ∑ tau : Fin 4, (if ρ = tau then 1 else 0) * riemannTensor g tau σ μ ν p := by
        apply Finset.sum_congr rfl; intro tau _; rw [h_delta tau]
    _ = ∑ tau : Fin 4, if ρ = tau then riemannTensor g tau σ μ ν p else 0 := by
        apply Finset.sum_congr rfl; intro tau _; split_ifs <;> ring
    _ = riemannTensor g ρ σ μ ν p := by
        rw [Finset.sum_ite_eq]; simp only [Finset.mem_univ, if_true]

/-- Bridge lemma: The two definitions of Ricci tensor are equal.
    R_{μν} = R^ρ_{μρν} = g^{ρσ} R_{ρμσν} -/
theorem ricciTensor_eq_ricciTensor' (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (μ ν : Fin 4) (p : LatticePoint) :
    ricciTensor g μ ν p = ricciTensor' g μ ν p := by
  unfold ricciTensor ricciTensor'
  -- LHS = Σ_ρ R^ρ_{μρν}
  -- RHS = Σ_{ρσ} g^{ρσ} R_{ρμσν}
  -- Use riemann_raise_lower: R^ρ_{μρν} = Σ_λ g^{ρλ} R_{λμρν}
  conv_lhs =>
    congr
    · skip
    · ext ρ
      rw [riemann_raise_lower g hNd ρ μ ρ ν p]
  -- Now LHS = Σ_ρ Σ_λ g^{ρλ} R_{λμρν}
  -- We need to match this with RHS = Σ_{ρσ} g^{ρσ} R_{ρμσν}
  -- Relabel in LHS: ρ→σ, λ→ρ to get Σ_σ Σ_ρ g^{σρ} R_{ρμσν}
  rw [Finset.sum_comm]
  -- Now LHS = Σ_λ Σ_ρ g^{ρλ} R_{λμρν}
  apply Finset.sum_congr rfl
  intro lam _
  apply Finset.sum_congr rfl
  intro ρ _
  -- Need: g^{ρλ} R_{λμρν} = g^{λρ} R_{λμρν}
  -- Use inverse metric symmetry
  rw [inverseMetric_symm g hSym hNd p ρ lam]

/-! ## Main Theorem: Ricci Tensor Symmetry -/

/-- Ricci tensor is symmetric: R_{μν} = R_{νμ}

    PROOF: Combine the bridge lemma with ricci'_symmetric. -/
theorem ricci_symmetric (g : DiscreteMetric) (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (μ ν : Fin 4) (p : LatticePoint) :
    ricciTensor g μ ν p = ricciTensor g ν μ p := by
  calc ricciTensor g μ ν p
      = ricciTensor' g μ ν p := ricciTensor_eq_ricciTensor' g hSym hNd μ ν p
    _ = ricciTensor' g ν μ p := ricci'_symmetric g hSym hNd μ ν p
    _ = ricciTensor g ν μ p := (ricciTensor_eq_ricciTensor' g hSym hNd ν μ p).symm

end DiscreteSpacetime.Geometry.Curvature
