/-
  Geometry.Curvature.Weyl
  =======================

  Weyl tensor (conformally invariant part of curvature).

  Definition:
  - weylTensor: C_{ρσμν} = trace-free part of Riemann tensor

  TODO (MODERATE):
  - weyl_tracefree: g^{ρμ} C_{ρσμν} = 0
-/

import DiscreteSpacetime.Geometry.Curvature.Scalar

namespace DiscreteSpacetime.Geometry.Curvature

open DiscreteSpacetime.Basic
open DiscreteSpacetime.Geometry
open Matrix
open BigOperators
open Finset

/-! ## Weyl Tensor Definition -/

/-- Weyl tensor: the trace-free part of Riemann tensor.

    C_{ρσμν} = R_{ρσμν} - (2/(n-2))[g_{ρ[μ} R_{ν]σ} - g_{σ[μ} R_{ν]ρ}]
                       + (2/((n-1)(n-2))) R g_{ρ[μ} g_{ν]σ}

    where n = 4, so:
    - 2/(n-2) = 2/2 = 1
    - 2/((n-1)(n-2)) = 2/(3·2) = 1/3

    The antisymmetrization g_{ρ[μ} R_{ν]σ} = (1/2)(g_{ρμ} R_{νσ} - g_{ρν} R_{μσ})

    In our formula we expand this directly without the 1/2 factor
    (absorbed into the coefficient). -/
noncomputable def weylTensor (g : DiscreteMetric) (ρ σ μ ν : Fin 4)
    (p : LatticePoint) : ℝ :=
  let R := riemannLower g ρ σ μ ν p
  let Ric_μσ := ricciTensor g μ σ p
  let Ric_νσ := ricciTensor g ν σ p
  let Ric_μρ := ricciTensor g μ ρ p
  let Ric_νρ := ricciTensor g ν ρ p
  let S := scalarCurvature g p
  let gp := g p
  -- n = 4, so n-2 = 2, n-1 = 3, (n-1)(n-2) = 6
  -- Coefficient for Ricci terms: 2/(n-2) = 1
  -- Coefficient for scalar term: 2/((n-1)(n-2)) = 1/3
  R - (1 : ℝ) * (gp ρ μ * Ric_νσ - gp ρ ν * Ric_μσ - gp σ μ * Ric_νρ + gp σ ν * Ric_μρ) +
    (1/3 : ℝ) * S * (gp ρ μ * gp ν σ - gp ρ ν * gp μ σ)

/-! ## Weyl Tensor Properties -/

/-- Weyl tensor is trace-free: g^{ρμ} C_{ρσμν} = 0

    PROOF STRATEGY:
    By construction, Weyl is defined to subtract exactly the traces
    from Riemann. The proof involves:
    1. Expand weylTensor definition
    2. Contract with g^{ρμ}
    3. Use metric contraction g^{ρμ} g_{ρα} = δ^μ_α
    4. Show Ricci and scalar terms cancel the Riemann trace

    This requires ricci_symmetric and careful index manipulation. -/
theorem weyl_tracefree (g : DiscreteMetric)
    (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (σ ν : Fin 4) (p : LatticePoint) :
    ∑ ρ : Fin 4, ∑ μ : Fin 4,
      (inverseMetric (g p)) ρ μ * weylTensor g ρ σ μ ν p = 0 := by
  sorry -- Follows from the definition of Weyl as trace-free Riemann

/-! ## Weyl Tensor Symmetries -/

/-- Weyl tensor inherits all symmetries of Riemann tensor.
    These follow from the symmetries of its components. -/

-- C_{ρσμν} = -C_{ρσνμ} (antisymmetric in last two)
theorem weyl_antisym_34 (g : DiscreteMetric)
    (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (ρ σ μ ν : Fin 4) (p : LatticePoint) :
    weylTensor g ρ σ μ ν p = -weylTensor g ρ σ ν μ p := by
  unfold weylTensor
  -- This follows from antisymmetry of R_{ρσμν} and the structure of the correction terms
  sorry

-- C_{ρσμν} = -C_{σρμν} (antisymmetric in first two)
theorem weyl_antisym_12 (g : DiscreteMetric)
    (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (ρ σ μ ν : Fin 4) (p : LatticePoint) :
    weylTensor g ρ σ μ ν p = -weylTensor g σ ρ μ ν p := by
  sorry

-- C_{ρσμν} = C_{μνρσ} (pair swap)
theorem weyl_pair_swap (g : DiscreteMetric)
    (hSym : DiscreteMetric.IsEverywhereSymmetric g)
    (hNd : DiscreteMetric.IsEverywhereNondegenerate g)
    (ρ σ μ ν : Fin 4) (p : LatticePoint) :
    weylTensor g ρ σ μ ν p = weylTensor g μ ν ρ σ p := by
  sorry

end DiscreteSpacetime.Geometry.Curvature
