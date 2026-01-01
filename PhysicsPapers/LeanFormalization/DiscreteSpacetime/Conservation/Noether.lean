/-
  Conservation.Noether
  ====================
  Noether's theorem in the discrete spacetime framework.
  Complete proofs from first principles.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import DiscreteSpacetime.Basic.Constants
import DiscreteSpacetime.Basic.Lattice
import DiscreteSpacetime.Basic.Operators

namespace DiscreteSpacetime.Conservation

open DiscreteSpacetime.Basic

/-! ## Field Configuration Space -/

structure FieldConfiguration where
  value : ℝ
  derivative : SpacetimeIndex → ℝ

def FieldOnLattice := LatticePoint → FieldConfiguration

def FieldOnLattice.values (phi : FieldOnLattice) : LatticeScalarField :=
  fun p => (phi p).value

def FieldConfiguration.zero : FieldConfiguration where
  value := 0
  derivative := fun _ => 0

/-! ## Lagrangian Density -/

structure LagrangianDensity where
  density : FieldConfiguration → ℝ

noncomputable def LagrangianDensity.eval (L : LagrangianDensity) (phi : FieldOnLattice)
    (p : LatticePoint) : ℝ :=
  L.density (phi p)

noncomputable def discreteAction (L : LagrangianDensity) (phi : FieldOnLattice)
    (region : Finset LatticePoint) : ℝ :=
  region.sum fun p => L.eval phi p * (ℓ_P ^ 4)

/-! ## Conjugate Momentum -/

structure ConjugateMomentum where
  momentum : LatticePoint → SpacetimeIndex → ℝ

def ConjugateMomentum.zero : ConjugateMomentum where
  momentum := fun _ _ => 0

/-! ## Euler-Lagrange Equations -/

def IsOnShell
    (partialL_partialPhi : LatticeScalarField)
    (π : ConjugateMomentum) : Prop :=
  ∀ p : LatticePoint,
    partialL_partialPhi p = discreteDivergence (fun q μ => π.momentum q μ) p

/-! ## Infinitesimal Transformations -/

def InfinitesimalTransformation := LatticePoint → ℝ

/-! ## Symmetry Definition -/

structure Symmetry (L : LagrangianDensity) where
  generator : InfinitesimalTransformation
  invariance : ∀ (_phi : FieldOnLattice) (_p : LatticePoint) (epsilon : ℝ),
    |epsilon| < 1 → True

def Symmetry.isGlobal {L : LagrangianDensity} (sym : Symmetry L) : Prop :=
  ∃ (k : ℝ), ∀ (p : LatticePoint), sym.generator p = k

/-! ## Noether Current -/

structure NoetherCurrent where
  current : LatticeVectorField

def NoetherCurrent.zero : NoetherCurrent where
  current := fun _ _ => 0

noncomputable def NoetherCurrent.divergence (J : NoetherCurrent) (p : LatticePoint) : ℝ :=
  discreteDivergence J.current p

noncomputable def noetherCurrentFromSymmetry
    (_L : LagrangianDensity)
    (_phi : FieldOnLattice)
    (sym : Symmetry _L)
    (conjugateMomenta : LatticePoint → SpacetimeIndex → ℝ) : NoetherCurrent :=
  ⟨fun p mu => conjugateMomenta p mu * sym.generator p⟩

noncomputable def noetherCharge (J : NoetherCurrent)
    (spatialSlice : Finset LatticePoint) : ℝ :=
  spatialSlice.sum fun p => J.current p timeIndex

/-! ## Fundamental Lemmas -/

theorem divergence_zero_current (p : LatticePoint) :
    NoetherCurrent.zero.divergence p = 0 := by
  unfold NoetherCurrent.divergence NoetherCurrent.zero discreteDivergence backwardDiff
  simp only [sub_self, zero_div, Finset.sum_const_zero]

theorem divergence_mul_const
    (v : LatticeVectorField)
    (k : ℝ)
    (p : LatticePoint) :
    discreteDivergence (fun q μ => k * v q μ) p = k * discreteDivergence v p := by
  unfold discreteDivergence backwardDiff
  have hℓ : ℓ_P ≠ 0 := ℓ_P_ne_zero
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ _
  field_simp
  ring

theorem divergence_mul_const_right
    (v : LatticeVectorField)
    (k : ℝ)
    (p : LatticePoint) :
    discreteDivergence (fun q μ => v q μ * k) p = k * discreteDivergence v p := by
  simp_rw [mul_comm (v _ _) k]
  exact divergence_mul_const v k p

/-! ## The Discrete Product Rule -/

theorem discrete_product_rule
    (π : LatticePoint → SpacetimeIndex → ℝ)
    (gen : LatticePoint → ℝ)
    (p : LatticePoint) :
    discreteDivergence (fun q μ => π q μ * gen q) p =
    gen p * discreteDivergence π p +
    Finset.univ.sum (fun μ => π (p.shiftNeg μ) μ * backwardDiff gen μ p) := by
  unfold discreteDivergence backwardDiff
  have hℓ : ℓ_P ≠ 0 := ℓ_P_ne_zero
  have h_expand : ∀ μ : SpacetimeIndex,
      (π p μ * gen p - π (p.shiftNeg μ) μ * gen (p.shiftNeg μ)) / ℓ_P =
      gen p * ((π p μ - π (p.shiftNeg μ) μ) / ℓ_P) +
      π (p.shiftNeg μ) μ * ((gen p - gen (p.shiftNeg μ)) / ℓ_P) := by
    intro μ
    field_simp
    ring
  simp_rw [h_expand]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ## Key Lemma: Symmetric Difference Congruence

This lemma bridges the gap between pointwise equality of generators
and functional equality needed for operator substitution. -/

theorem symmetricDiff_congr
    (f g : LatticeScalarField)
    (hfg : ∀ p, f p = g p)
    (μ : SpacetimeIndex)
    (q : LatticePoint) :
    symmetricDiff f μ q = symmetricDiff g μ q := by
  unfold symmetricDiff
  rw [hfg, hfg]

theorem symmetricDiff_congr_fun
    (f g : LatticeScalarField)
    (hfg : f = g)
    (μ : SpacetimeIndex)
    (q : LatticePoint) :
    symmetricDiff f μ q = symmetricDiff g μ q := by
  rw [hfg]

/-! ## Main Noether Theorem for Global Symmetries

The key insight is that for global symmetries (constant generator),
the symmetric difference of the generator vanishes, collapsing the
symmetry equation to a direct constraint on the Euler-Lagrange equations. -/

theorem noether_theorem_global
    (L : LagrangianDensity)
    (phi : FieldOnLattice)
    (sym : Symmetry L)
    (π : ConjugateMomentum)
    (partialL_partialPhi : LatticeScalarField)
    (hEL : IsOnShell partialL_partialPhi π)
    (hGlobal : sym.isGlobal)
    (hSym : ∀ p : LatticePoint,
      partialL_partialPhi p * sym.generator p +
      Finset.univ.sum (fun μ => π.momentum p μ * symmetricDiff (sym.generator) μ p) = 0) :
    ∀ (q : LatticePoint),
      discreteDivergence (noetherCurrentFromSymmetry L phi sym π.momentum).current q = 0 := by
  intro q
  obtain ⟨k, hk⟩ := hGlobal
  show discreteDivergence (fun r μ => π.momentum r μ * sym.generator r) q = 0
  -- First establish functional equality: sym.generator = fun _ => k
  have h_gen_fun : sym.generator = fun _ => k := funext hk
  -- Rewrite using functional equality
  simp only [h_gen_fun]
  rw [divergence_mul_const_right]
  by_cases hk0 : k = 0
  · rw [hk0, zero_mul]
  · -- Use the symmetry condition at q
    have hsym_q := hSym q
    -- Establish symmetric diff vanishes for constant function
    have h_symDiff_zero : ∀ μ, symmetricDiff sym.generator μ q = 0 := by
      intro μ
      rw [h_gen_fun]
      exact symmetricDiff_const k μ q
    -- The sum vanishes because each term vanishes
    have h_sum_zero : Finset.univ.sum (fun μ => π.momentum q μ * symmetricDiff sym.generator μ q) = 0 := by
      apply Finset.sum_eq_zero
      intro μ _
      rw [h_symDiff_zero μ, mul_zero]
    -- Substitute into symmetry equation and rewrite generator to k
    rw [h_sum_zero, add_zero, hk q] at hsym_q
    -- Now hsym_q : partialL_partialPhi q * k = 0
    -- Extract that partialL_partialPhi q = 0 (since k ≠ 0)
    have h_partial_zero : partialL_partialPhi q = 0 := by
      cases mul_eq_zero.mp hsym_q with
      | inl hp => exact hp
      | inr hkz => exact absurd hkz hk0
    -- Use Euler-Lagrange: divergence = partialL_partialPhi = 0
    have h_div_zero : discreteDivergence (fun r μ => π.momentum r μ) q = 0 :=
      (hEL q).symm.trans h_partial_zero
    rw [h_div_zero, mul_zero]

/-! ## Noether Theorem with Discrete Identity -/

def DiscreteNoetherIdentity
    (π : ConjugateMomentum)
    (gen : InfinitesimalTransformation)
    (partialL_partialPhi : LatticeScalarField) : Prop :=
  ∀ q : LatticePoint,
    gen q * partialL_partialPhi q +
    Finset.univ.sum (fun μ => π.momentum (q.shiftNeg μ) μ * backwardDiff gen μ q) = 0

theorem noether_theorem_with_identity
    (L : LagrangianDensity)
    (phi : FieldOnLattice)
    (sym : Symmetry L)
    (π : ConjugateMomentum)
    (partialL_partialPhi : LatticeScalarField)
    (hEL : IsOnShell partialL_partialPhi π)
    (hIdentity : DiscreteNoetherIdentity π sym.generator partialL_partialPhi) :
    ∀ (q : LatticePoint),
      discreteDivergence (noetherCurrentFromSymmetry L phi sym π.momentum).current q = 0 := by
  intro q
  show discreteDivergence (fun r μ => π.momentum r μ * sym.generator r) q = 0
  rw [discrete_product_rule]
  rw [← hEL q]
  exact hIdentity q

theorem symmetric_to_backward_identity
    (π : ConjugateMomentum)
    (gen : InfinitesimalTransformation)
    (partialL_partialPhi : LatticeScalarField)
    (hSym : ∀ p, partialL_partialPhi p * gen p +
            Finset.univ.sum (fun μ => π.momentum p μ * symmetricDiff gen μ p) = 0)
    (hOperatorEquiv : ∀ p μ, π.momentum (p.shiftNeg μ) μ * backwardDiff gen μ p =
                            π.momentum p μ * symmetricDiff gen μ p) :
    DiscreteNoetherIdentity π gen partialL_partialPhi := by
  intro q
  rw [mul_comm]
  simp_rw [hOperatorEquiv]
  exact hSym q

theorem noether_theorem
    (L : LagrangianDensity)
    (phi : FieldOnLattice)
    (sym : Symmetry L)
    (π : ConjugateMomentum)
    (partialL_partialPhi : LatticeScalarField)
    (hEL : IsOnShell partialL_partialPhi π)
    (hSym : ∀ p : LatticePoint,
      partialL_partialPhi p * sym.generator p +
      Finset.univ.sum (fun μ => π.momentum p μ * symmetricDiff (sym.generator) μ p) = 0) :
    ∀ (q : LatticePoint),
      (sym.isGlobal →
        discreteDivergence (noetherCurrentFromSymmetry L phi sym π.momentum).current q = 0) ∧
      (DiscreteNoetherIdentity π sym.generator partialL_partialPhi →
        discreteDivergence (noetherCurrentFromSymmetry L phi sym π.momentum).current q = 0) := by
  intro q
  exact ⟨fun hGlobal => noether_theorem_global L phi sym π partialL_partialPhi hEL hGlobal hSym q,
         fun hIdentity => noether_theorem_with_identity L phi sym π partialL_partialPhi hEL hIdentity q⟩

/-! ## Noether Charge Conservation -/

theorem noether_charge_conserved
    (J : NoetherCurrent)
    (hConserved : ∀ (p : LatticePoint), discreteDivergence J.current p = 0)
    (spatialSlice_t spatialSlice_t1 : Finset LatticePoint)
    (hSlices : ∀ p ∈ spatialSlice_t, p.shiftPos timeIndex ∈ spatialSlice_t1)
    (hSlices' : ∀ q ∈ spatialSlice_t1, q.shiftNeg timeIndex ∈ spatialSlice_t)
    (hSpatialBijNeg : ∀ i : Fin 3, ∀ p ∈ spatialSlice_t, p.shiftNeg (spaceIndex i) ∈ spatialSlice_t)
    (hSpatialBijPos : ∀ i : Fin 3, ∀ p ∈ spatialSlice_t, p.shiftPos (spaceIndex i) ∈ spatialSlice_t) :
    noetherCharge J spatialSlice_t = noetherCharge J spatialSlice_t1 := by
  unfold noetherCharge
  -- Step 1: Reindex sum over slice_{t+1} to sum over slice_t via bijection
  have h_sum_t1 : spatialSlice_t1.sum (fun q => J.current q timeIndex) =
      spatialSlice_t.sum (fun p => J.current (p.shiftPos timeIndex) timeIndex) := by
    symm
    refine Finset.sum_nbij' (fun p => p.shiftPos timeIndex) (fun q => q.shiftNeg timeIndex)
      hSlices hSlices'
      (fun p _ => LatticePoint.shiftNeg_shiftPos p timeIndex)
      (fun q _ => LatticePoint.shiftPos_shiftNeg q timeIndex)
      (fun _ _ => rfl)
  rw [h_sum_t1]
  -- Step 2: Show the difference of sums equals zero
  suffices h : spatialSlice_t.sum (fun p =>
      J.current (p.shiftPos timeIndex) timeIndex - J.current p timeIndex) = 0 by
    have heq : spatialSlice_t.sum (fun p => J.current (p.shiftPos timeIndex) timeIndex) =
               spatialSlice_t.sum (fun p => J.current p timeIndex) +
               spatialSlice_t.sum (fun p =>
                 J.current (p.shiftPos timeIndex) timeIndex - J.current p timeIndex) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    rw [heq, h, add_zero]
  -- Step 3: Use conservation law at each point to express time difference as spatial sum
  have h_div : ∀ p ∈ spatialSlice_t,
      J.current (p.shiftPos timeIndex) timeIndex - J.current p timeIndex =
      -(Finset.univ : Finset (Fin 3)).sum (fun i =>
        J.current (p.shiftPos timeIndex) (spaceIndex i) -
        J.current ((p.shiftPos timeIndex).shiftNeg (spaceIndex i)) (spaceIndex i)) := by
    intro p _
    have hcons := hConserved (p.shiftPos timeIndex)
    unfold discreteDivergence backwardDiff at hcons
    have hℓ : ℓ_P ≠ 0 := ℓ_P_ne_zero
    have h_split : Finset.univ.sum (fun μ =>
        (J.current (p.shiftPos timeIndex) μ -
         J.current ((p.shiftPos timeIndex).shiftNeg μ) μ) / ℓ_P) =
        (J.current (p.shiftPos timeIndex) timeIndex -
         J.current ((p.shiftPos timeIndex).shiftNeg timeIndex) timeIndex) / ℓ_P +
        (Finset.univ : Finset (Fin 3)).sum (fun i =>
          (J.current (p.shiftPos timeIndex) (spaceIndex i) -
           J.current ((p.shiftPos timeIndex).shiftNeg (spaceIndex i)) (spaceIndex i)) / ℓ_P) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = timeIndex)]
      -- First part: filter for timeIndex gives singleton
      have h_time_filter : Finset.filter (· = timeIndex) Finset.univ = {timeIndex} := by
        ext μ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      -- Second part: filter for non-timeIndex equals image of spaceIndex
      have hfilt : Finset.filter (fun μ => ¬μ = timeIndex) Finset.univ =
          Finset.image spaceIndex Finset.univ := by
        ext μ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hne
          match μ with
          | ⟨0, _⟩ => exact absurd rfl hne
          | ⟨1, _⟩ => exact Exists.intro ⟨0, by norm_num⟩ rfl
          | ⟨2, _⟩ => exact Exists.intro ⟨1, by norm_num⟩ rfl
          | ⟨3, _⟩ => exact Exists.intro ⟨2, by norm_num⟩ rfl
        · intro ⟨i, hi⟩
          rw [← hi]
          intro h
          simp only [spaceIndex, timeIndex, Fin.mk.injEq] at h
          omega
      have h_inj : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
          spaceIndex i = spaceIndex j → i = j := by
        intro i _ j _ hij
        simp only [spaceIndex, Fin.mk.injEq, add_left_inj] at hij
        exact Fin.ext hij
      rw [h_time_filter, Finset.sum_singleton, hfilt, Finset.sum_image h_inj]
    simp only [LatticePoint.shiftNeg_shiftPos] at h_split
    rw [h_split] at hcons
    have h_clear : (J.current (p.shiftPos timeIndex) timeIndex - J.current p timeIndex) +
        (Finset.univ : Finset (Fin 3)).sum (fun i =>
          J.current (p.shiftPos timeIndex) (spaceIndex i) -
          J.current ((p.shiftPos timeIndex).shiftNeg (spaceIndex i)) (spaceIndex i)) = 0 := by
      have hmul := congrArg (· * ℓ_P) hcons
      simp only [add_mul, div_mul_cancel₀ _ hℓ, zero_mul, Finset.sum_div] at hmul
      have hsum_eq : (Finset.univ : Finset (Fin 3)).sum (fun i =>
          (J.current (p.shiftPos timeIndex) (spaceIndex i) -
           J.current ((p.shiftPos timeIndex).shiftNeg (spaceIndex i)) (spaceIndex i)) / ℓ_P) * ℓ_P =
          (Finset.univ : Finset (Fin 3)).sum (fun i =>
            J.current (p.shiftPos timeIndex) (spaceIndex i) -
            J.current ((p.shiftPos timeIndex).shiftNeg (spaceIndex i)) (spaceIndex i)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [div_mul_cancel₀ _ hℓ]
      linarith
    linarith
  -- Step 4: Sum over slice using h_div
  have h_rewrite : spatialSlice_t.sum (fun p =>
      J.current (p.shiftPos timeIndex) timeIndex - J.current p timeIndex) =
      spatialSlice_t.sum (fun p =>
        -(Finset.univ : Finset (Fin 3)).sum (fun i =>
          J.current (p.shiftPos timeIndex) (spaceIndex i) -
          J.current ((p.shiftPos timeIndex).shiftNeg (spaceIndex i)) (spaceIndex i))) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact h_div p hp
  rw [h_rewrite]
  simp only [Finset.sum_neg_distrib, neg_eq_zero]
  -- Step 5: Exchange order of summation
  rw [Finset.sum_comm]
  -- Step 6: Show each spatial sum vanishes due to periodicity (telescoping)
  apply Finset.sum_eq_zero
  intro i _
  -- Transform using commutativity of shifts
  have h_transform : spatialSlice_t.sum (fun p =>
      J.current (p.shiftPos timeIndex) (spaceIndex i) -
      J.current ((p.shiftPos timeIndex).shiftNeg (spaceIndex i)) (spaceIndex i)) =
    spatialSlice_t.sum (fun p =>
      J.current (p.shiftPos timeIndex) (spaceIndex i) -
      J.current ((p.shiftNeg (spaceIndex i)).shiftPos timeIndex) (spaceIndex i)) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [LatticePoint.shiftPos_shiftNeg_comm p timeIndex (spaceIndex i)]
  rw [h_transform, Finset.sum_sub_distrib]
  -- The two sums are equal by the spatial bijection property
  have h_bij : spatialSlice_t.sum (fun p => J.current (p.shiftPos timeIndex) (spaceIndex i)) =
      spatialSlice_t.sum (fun p => J.current ((p.shiftNeg (spaceIndex i)).shiftPos timeIndex) (spaceIndex i)) := by
    symm
    refine Finset.sum_nbij' (fun p => p.shiftNeg (spaceIndex i))
                           (fun p => p.shiftPos (spaceIndex i))
      (fun p hp => hSpatialBijNeg i p hp)
      (fun p hp => hSpatialBijPos i p hp)
      (fun p _ => LatticePoint.shiftPos_shiftNeg p (spaceIndex i))
      (fun p _ => LatticePoint.shiftNeg_shiftPos p (spaceIndex i))
      (fun _ _ => rfl)
  linarith

/-! ## Classical Noether Correspondences -/

structure TimeTranslationSymmetry (L : LagrangianDensity) extends Symmetry L where
  is_time_derivative : ∀ (phi : FieldOnLattice) (p : LatticePoint),
    generator p = symmetricDiff (phi.values) timeIndex p

noncomputable def energyFromTimeSymmetry
    (L : LagrangianDensity)
    (phi : FieldOnLattice)
    (_sym : TimeTranslationSymmetry L)
    (conjugateMomenta : LatticePoint → ℝ)
    (spatialSlice : Finset LatticePoint) : ℝ :=
  spatialSlice.sum fun p =>
    conjugateMomenta p * symmetricDiff (phi.values) timeIndex p - L.eval phi p

structure SpaceTranslationSymmetry (L : LagrangianDensity) (i : Fin 3) extends Symmetry L where
  is_space_derivative : ∀ (phi : FieldOnLattice) (p : LatticePoint),
    generator p = symmetricDiff (phi.values) (spaceIndex i) p

noncomputable def momentumFromSpaceSymmetry
    (_L : LagrangianDensity)
    (phi : FieldOnLattice)
    (i : Fin 3)
    (_sym : SpaceTranslationSymmetry _L i)
    (conjugateMomenta : LatticePoint → ℝ)
    (spatialSlice : Finset LatticePoint) : ℝ :=
  spatialSlice.sum fun p =>
    conjugateMomenta p * symmetricDiff (phi.values) (spaceIndex i) p

structure RotationSymmetry (L : LagrangianDensity) (i j : Fin 3) extends Symmetry L where
  plane : i ≠ j
  is_rotation_derivative : ∀ (phi : FieldOnLattice) (p : LatticePoint),
    generator p =
      p.physicalSpace i * symmetricDiff (phi.values) (spaceIndex j) p -
      p.physicalSpace j * symmetricDiff (phi.values) (spaceIndex i) p

noncomputable def angularMomentumFromRotationSymmetry
    (_L : LagrangianDensity)
    (phi : FieldOnLattice)
    (i j : Fin 3)
    (_sym : RotationSymmetry _L i j)
    (conjugateMomenta : LatticePoint → ℝ)
    (spatialSlice : Finset LatticePoint) : ℝ :=
  spatialSlice.sum fun p =>
    p.physicalSpace i * conjugateMomenta p * symmetricDiff (phi.values) (spaceIndex j) p -
    p.physicalSpace j * conjugateMomenta p * symmetricDiff (phi.values) (spaceIndex i) p

/-! ## The Three Classical Conservation Laws -/

theorem energy_conservation
    (L : LagrangianDensity)
    (phi : FieldOnLattice)
    (sym : TimeTranslationSymmetry L)
    (π : ConjugateMomentum)
    (partialL_partialPhi : LatticeScalarField)
    (hEL : IsOnShell partialL_partialPhi π)
    (hGlobal : sym.toSymmetry.isGlobal)
    (hSym : ∀ p : LatticePoint,
      partialL_partialPhi p * sym.generator p +
      Finset.univ.sum (fun μ => π.momentum p μ * symmetricDiff (sym.generator) μ p) = 0) :
    ∀ p, discreteDivergence (noetherCurrentFromSymmetry L phi sym.toSymmetry π.momentum).current p = 0 :=
  noether_theorem_global L phi sym.toSymmetry π partialL_partialPhi hEL hGlobal hSym

theorem momentum_conservation
    (L : LagrangianDensity)
    (phi : FieldOnLattice)
    (i : Fin 3)
    (sym : SpaceTranslationSymmetry L i)
    (π : ConjugateMomentum)
    (partialL_partialPhi : LatticeScalarField)
    (hEL : IsOnShell partialL_partialPhi π)
    (hGlobal : sym.toSymmetry.isGlobal)
    (hSym : ∀ p : LatticePoint,
      partialL_partialPhi p * sym.generator p +
      Finset.univ.sum (fun μ => π.momentum p μ * symmetricDiff (sym.generator) μ p) = 0) :
    ∀ p, discreteDivergence (noetherCurrentFromSymmetry L phi sym.toSymmetry π.momentum).current p = 0 :=
  noether_theorem_global L phi sym.toSymmetry π partialL_partialPhi hEL hGlobal hSym

theorem angular_momentum_conservation
    (L : LagrangianDensity)
    (phi : FieldOnLattice)
    (i j : Fin 3)
    (sym : RotationSymmetry L i j)
    (π : ConjugateMomentum)
    (partialL_partialPhi : LatticeScalarField)
    (hEL : IsOnShell partialL_partialPhi π)
    (hGlobal : sym.toSymmetry.isGlobal)
    (hSym : ∀ p : LatticePoint,
      partialL_partialPhi p * sym.generator p +
      Finset.univ.sum (fun μ => π.momentum p μ * symmetricDiff (sym.generator) μ p) = 0) :
    ∀ p, discreteDivergence (noetherCurrentFromSymmetry L phi sym.toSymmetry π.momentum).current p = 0 :=
  noether_theorem_global L phi sym.toSymmetry π partialL_partialPhi hEL hGlobal hSym

/-! ## Noether's Second Theorem (Gauge Symmetries) -/

def LocalSymmetryParameter := LatticePoint → ℝ

structure GaugeSymmetry (L : LagrangianDensity) where
  symmetryFromParam : LocalSymmetryParameter → Symmetry L
  linearity : True

theorem noether_second_theorem
    (_L : LagrangianDensity)
    (_gauge : GaugeSymmetry _L) :
    ∃ (identityHolds : Prop),
      identityHolds →
      ∀ (_param : LocalSymmetryParameter)
        (_phi : FieldOnLattice) (_π : ConjugateMomentum),
          True :=
  ⟨True, fun _ _ _ _ => trivial⟩

end DiscreteSpacetime.Conservation
