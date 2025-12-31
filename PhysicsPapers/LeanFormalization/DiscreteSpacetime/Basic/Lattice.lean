/-
  Basic.Lattice
  ==============

  The Planck lattice Λ = ℓ_P · ℤ⁴.

  This module defines the discrete spacetime structure:
  - LatticeIndex: Integer coordinates in ℤ⁴
  - LatticePoint: Physical coordinates scaled by Planck length
  - Neighborhood relations and lattice topology
  - Finite regions and summation over lattice

  The key insight is that physical spacetime at the Planck scale
  is discrete, not continuous.

  Mathematical Foundation:
  ========================
  The lattice ℤ⁴ is a free abelian group of rank 4, and forms
  a hypercubic lattice with coordination number 2d = 8.
  Each point has exactly 8 nearest neighbors: ±1 in each of 4 directions.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Notation
import DiscreteSpacetime.Basic.Constants

namespace DiscreteSpacetime.Basic

/-! ## Spacetime Dimension -/

/-- Spacetime is 4-dimensional (1 time + 3 space) -/
def spacetimeDim : ℕ := 4

/-- Spacetime dimension is positive -/
theorem spacetimeDim_pos : 0 < spacetimeDim := by norm_num [spacetimeDim]

/-- Spacetime dimension is nonzero -/
theorem spacetimeDim_ne_zero : spacetimeDim ≠ 0 := by norm_num [spacetimeDim]

/-- Type alias for spacetime indices (0 = time, 1,2,3 = space) -/
abbrev SpacetimeIndex := Fin spacetimeDim

/-- Time index -/
def timeIndex : SpacetimeIndex := ⟨0, by norm_num [spacetimeDim]⟩

/-- Space indices -/
def spaceIndex (i : Fin 3) : SpacetimeIndex := ⟨i.val + 1, by
  have hi := i.isLt
  simp only [spacetimeDim]
  omega⟩

/-! ## Lattice Index (Integer Coordinates) -/

/-- A lattice index is a point in ℤ⁴.
    These are the "discrete coordinates" of a spacetime point.
    Mathematically, this is an element of the free abelian group ℤ⁴. -/
structure LatticeIndex where
  coords : Fin spacetimeDim → ℤ
  deriving DecidableEq

/-- Extensionality for LatticeIndex -/
@[ext]
theorem LatticeIndex.ext {p q : LatticeIndex} (h : p.coords = q.coords) : p = q := by
  cases p; cases q; simp_all

namespace LatticeIndex

/-- The origin of the lattice -/
def origin : LatticeIndex := ⟨fun _ => 0⟩

/-- Get coordinate along a specific axis -/
def coord (p : LatticeIndex) (μ : SpacetimeIndex) : ℤ := p.coords μ

/-- Time coordinate -/
def t (p : LatticeIndex) : ℤ := p.coord timeIndex

/-- Spatial coordinates -/
def x (p : LatticeIndex) : Fin 3 → ℤ := fun i => p.coord (spaceIndex i)

/-! ### Additive Group Structure on ℤ⁴ -/

/-- Add two lattice indices (coordinate-wise) -/
instance : Add LatticeIndex where
  add p q := ⟨fun μ => p.coords μ + q.coords μ⟩

/-- Subtract lattice indices (coordinate-wise) -/
instance : Sub LatticeIndex where
  sub p q := ⟨fun μ => p.coords μ - q.coords μ⟩

/-- Negate a lattice index (coordinate-wise) -/
instance : Neg LatticeIndex where
  neg p := ⟨fun μ => -p.coords μ⟩

/-- Zero lattice index -/
instance : Zero LatticeIndex where
  zero := origin

/-- Addition is coordinate-wise -/
@[simp]
theorem add_coords (p q : LatticeIndex) (μ : SpacetimeIndex) :
    (p + q).coords μ = p.coords μ + q.coords μ := rfl

/-- Subtraction is coordinate-wise -/
@[simp]
theorem sub_coords (p q : LatticeIndex) (μ : SpacetimeIndex) :
    (p - q).coords μ = p.coords μ - q.coords μ := rfl

/-- Negation is coordinate-wise -/
@[simp]
theorem neg_coords (p : LatticeIndex) (μ : SpacetimeIndex) :
    (-p).coords μ = -(p.coords μ) := rfl

/-- Zero coords are all zero -/
@[simp]
theorem zero_coords (μ : SpacetimeIndex) : (0 : LatticeIndex).coords μ = 0 := rfl

/-- Origin equals zero -/
theorem origin_eq_zero : origin = (0 : LatticeIndex) := rfl

/-- LatticeIndex forms an additive commutative group -/
instance : AddCommGroup LatticeIndex where
  add_assoc p q r := by ext μ; simp [add_assoc]
  zero_add p := by ext μ; simp
  add_zero p := by ext μ; simp
  neg_add_cancel p := by ext μ; simp
  add_comm p q := by ext μ; simp [add_comm]
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ### Unit Vectors and Shifts -/

/-- Unit vector along axis μ: e_μ has 1 at position μ and 0 elsewhere -/
def unitVector (μ : SpacetimeIndex) : LatticeIndex :=
  ⟨fun ν => if μ = ν then 1 else 0⟩

/-- Unit vector has 1 at its own index -/
@[simp]
theorem unitVector_self (μ : SpacetimeIndex) : (unitVector μ).coords μ = 1 := by
  simp [unitVector]

/-- Unit vector has 0 at other indices -/
theorem unitVector_other {μ ν : SpacetimeIndex} (h : μ ≠ ν) :
    (unitVector μ).coords ν = 0 := by
  simp [unitVector, h]

/-- Unit vectors are distinct -/
theorem unitVector_injective : Function.Injective unitVector := by
  intro μ ν h
  by_contra hne
  have h1 : (unitVector μ).coords μ = 1 := unitVector_self μ
  have h2 : (unitVector ν).coords μ = 0 := unitVector_other (Ne.symm hne)
  rw [h] at h1
  rw [h1] at h2
  exact one_ne_zero h2

/-- Shift by +1 along axis μ: p + e_μ -/
def shiftPos (p : LatticeIndex) (μ : SpacetimeIndex) : LatticeIndex :=
  p + unitVector μ

/-- Shift by -1 along axis μ: p - e_μ -/
def shiftNeg (p : LatticeIndex) (μ : SpacetimeIndex) : LatticeIndex :=
  p - unitVector μ

/-- shiftPos changes coordinate μ by +1 -/
@[simp]
theorem shiftPos_coord_self (p : LatticeIndex) (μ : SpacetimeIndex) :
    (p.shiftPos μ).coords μ = p.coords μ + 1 := by
  simp [shiftPos]

/-- shiftPos leaves other coordinates unchanged -/
theorem shiftPos_coord_other (p : LatticeIndex) {μ ν : SpacetimeIndex} (h : μ ≠ ν) :
    (p.shiftPos μ).coords ν = p.coords ν := by
  simp [shiftPos, unitVector_other h]

/-- shiftNeg changes coordinate μ by -1 -/
@[simp]
theorem shiftNeg_coord_self (p : LatticeIndex) (μ : SpacetimeIndex) :
    (p.shiftNeg μ).coords μ = p.coords μ - 1 := by
  simp [shiftNeg, unitVector]

/-- shiftNeg leaves other coordinates unchanged -/
theorem shiftNeg_coord_other (p : LatticeIndex) {μ ν : SpacetimeIndex} (h : μ ≠ ν) :
    (p.shiftNeg μ).coords ν = p.coords ν := by
  simp [shiftNeg, unitVector_other h]

/-- Positive shift is injective in the point -/
theorem shiftPos_injective (μ : SpacetimeIndex) :
    Function.Injective (fun p : LatticeIndex => p.shiftPos μ) := by
  intro p q h
  have heq : p + unitVector μ = q + unitVector μ := h
  ext ν
  have := congrArg (fun x => x.coords ν) heq
  simp at this
  exact this

/-- Negative shift is injective in the point -/
theorem shiftNeg_injective (μ : SpacetimeIndex) :
    Function.Injective (fun p : LatticeIndex => p.shiftNeg μ) := by
  intro p q h
  have heq : p - unitVector μ = q - unitVector μ := h
  ext ν
  have := congrArg (fun x => x.coords ν) heq
  simp at this
  exact this

/-- shiftPos along different axes gives different results -/
theorem shiftPos_ne_shiftPos_of_ne (p : LatticeIndex) {μ ν : SpacetimeIndex} (h : μ ≠ ν) :
    p.shiftPos μ ≠ p.shiftPos ν := by
  intro heq
  have h1 : (p.shiftPos μ).coords μ = p.coords μ + 1 := shiftPos_coord_self p μ
  have h2 : (p.shiftPos ν).coords μ = p.coords μ := by
    simp only [shiftPos, add_coords]
    simp [unitVector, Ne.symm h]
  rw [heq] at h1
  rw [h1] at h2
  omega

/-- shiftNeg along different axes gives different results -/
theorem shiftNeg_ne_shiftNeg_of_ne (p : LatticeIndex) {μ ν : SpacetimeIndex} (h : μ ≠ ν) :
    p.shiftNeg μ ≠ p.shiftNeg ν := by
  intro heq
  have h1 : (p.shiftNeg μ).coords μ = p.coords μ - 1 := shiftNeg_coord_self p μ
  have h2 : (p.shiftNeg ν).coords μ = p.coords μ := by
    simp only [shiftNeg, sub_coords]
    simp [unitVector, Ne.symm h]
  rw [heq] at h1
  rw [h1] at h2
  omega

/-- Positive and negative shifts along the same axis are different -/
theorem shiftPos_ne_shiftNeg (p : LatticeIndex) (μ : SpacetimeIndex) :
    p.shiftPos μ ≠ p.shiftNeg μ := by
  intro heq
  have h1 : (p.shiftPos μ).coords μ = p.coords μ + 1 := shiftPos_coord_self p μ
  have h2 : (p.shiftNeg μ).coords μ = p.coords μ - 1 := shiftNeg_coord_self p μ
  rw [heq] at h1
  rw [h1] at h2
  omega

/-- Positive shift along μ differs from negative shift along ν -/
theorem shiftPos_ne_shiftNeg_any (p : LatticeIndex) (μ ν : SpacetimeIndex) :
    p.shiftPos μ ≠ p.shiftNeg ν := by
  intro heq
  by_cases h : μ = ν
  · subst h
    exact shiftPos_ne_shiftNeg p μ heq
  · have h1 : (p.shiftPos μ).coords μ = p.coords μ + 1 := shiftPos_coord_self p μ
    have h2 : (p.shiftNeg ν).coords μ = p.coords μ := by
      simp only [shiftNeg, sub_coords]
      simp [unitVector, Ne.symm h]
    rw [heq] at h1
    rw [h1] at h2
    omega

/-- Inverse operations: shift back after shift forward -/
@[simp]
theorem shiftNeg_shiftPos (p : LatticeIndex) (μ : SpacetimeIndex) :
    (p.shiftPos μ).shiftNeg μ = p := by
  ext ν
  by_cases h : μ = ν
  · subst h; simp [shiftPos, shiftNeg]
  · simp [shiftPos, shiftNeg, unitVector_other h]

/-- Inverse operations: shift forward after shift back -/
@[simp]
theorem shiftPos_shiftNeg (p : LatticeIndex) (μ : SpacetimeIndex) :
    (p.shiftNeg μ).shiftPos μ = p := by
  ext ν
  by_cases h : μ = ν
  · subst h; simp [shiftPos, shiftNeg]
  · simp [shiftPos, shiftNeg, unitVector_other h]

/-- Shifts along different axes commute -/
theorem shiftPos_shiftPos_comm (p : LatticeIndex) (μ ν : SpacetimeIndex) :
    (p.shiftPos μ).shiftPos ν = (p.shiftPos ν).shiftPos μ := by
  ext ρ
  simp only [shiftPos, add_coords]
  ring

/-- Negative shifts along different axes commute -/
theorem shiftNeg_shiftNeg_comm (p : LatticeIndex) (μ ν : SpacetimeIndex) :
    (p.shiftNeg μ).shiftNeg ν = (p.shiftNeg ν).shiftNeg μ := by
  ext ρ
  simp only [shiftNeg, sub_coords]
  ring

/-- Mixed shifts commute -/
theorem shiftPos_shiftNeg_comm (p : LatticeIndex) (μ ν : SpacetimeIndex) :
    (p.shiftPos μ).shiftNeg ν = (p.shiftNeg ν).shiftPos μ := by
  ext ρ
  simp only [shiftPos, shiftNeg, add_coords, sub_coords]
  ring

/-! ### Manhattan Distance (L¹ norm) -/

/-- Manhattan distance (L¹ norm on the lattice) -/
def manhattanDist (p q : LatticeIndex) : ℕ :=
  (Finset.univ.sum fun μ => (p.coord μ - q.coord μ).natAbs)

/-- Manhattan distance is symmetric -/
theorem manhattanDist_comm (p q : LatticeIndex) :
    manhattanDist p q = manhattanDist q p := by
  unfold manhattanDist
  congr 1
  ext μ
  have : p.coord μ - q.coord μ = -(q.coord μ - p.coord μ) := by ring
  rw [this, Int.natAbs_neg]

/-- Manhattan distance to self is zero -/
@[simp]
theorem manhattanDist_self (p : LatticeIndex) : manhattanDist p p = 0 := by
  unfold manhattanDist coord
  simp

/-- Manhattan distance is zero iff points are equal -/
theorem manhattanDist_eq_zero_iff (p q : LatticeIndex) :
    manhattanDist p q = 0 ↔ p = q := by
  constructor
  · intro h
    unfold manhattanDist at h
    have hsum := Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _) |>.mp h
    ext μ
    have := hsum μ (Finset.mem_univ μ)
    simp only [Int.natAbs_eq_zero, sub_eq_zero] at this
    exact this
  · intro h
    subst h
    simp

/-- Two points are nearest neighbors if their Manhattan distance is 1 -/
def isNearestNeighbor (p q : LatticeIndex) : Prop :=
  manhattanDist p q = 1

/-- Nearest neighbor relation is symmetric -/
theorem isNearestNeighbor_comm (p q : LatticeIndex) :
    isNearestNeighbor p q ↔ isNearestNeighbor q p := by
  unfold isNearestNeighbor
  rw [manhattanDist_comm]

/-- shiftPos creates a nearest neighbor -/
theorem shiftPos_isNearestNeighbor (p : LatticeIndex) (μ : SpacetimeIndex) :
    isNearestNeighbor p (p.shiftPos μ) := by
  unfold isNearestNeighbor manhattanDist coord shiftPos
  simp only [add_coords]
  have step : ∀ ν, (p.coords ν - (p.coords ν + (unitVector μ).coords ν)).natAbs =
         if μ = ν then 1 else 0 := by
    intro ν
    by_cases h : μ = ν
    · subst h
      simp [unitVector]
    · simp [unitVector, h]
  simp_rw [step]
  rw [Finset.sum_ite_eq]
  simp

/-- shiftNeg creates a nearest neighbor -/
theorem shiftNeg_isNearestNeighbor (p : LatticeIndex) (μ : SpacetimeIndex) :
    isNearestNeighbor p (p.shiftNeg μ) := by
  unfold isNearestNeighbor manhattanDist coord shiftNeg
  simp only [sub_coords]
  have step : ∀ ν, (p.coords ν - (p.coords ν - (unitVector μ).coords ν)).natAbs =
         if μ = ν then 1 else 0 := by
    intro ν
    by_cases h : μ = ν
    · subst h
      simp [unitVector, Int.natAbs_neg]
    · simp [unitVector, h]
  simp_rw [step]
  rw [Finset.sum_ite_eq]
  simp

end LatticeIndex

/-! ## Lattice Point (Physical Coordinates) -/

/-- A lattice point in physical coordinates.
    These are points in the actual Planck lattice Λ = ℓ_P · ℤ⁴. -/
structure LatticePoint where
  /-- The underlying integer coordinates -/
  index : LatticeIndex
  deriving DecidableEq

/-- Extensionality for LatticePoint -/
@[ext]
theorem LatticePoint.ext {p q : LatticePoint} (h : p.index = q.index) : p = q := by
  cases p; cases q; simp_all

namespace LatticePoint

/-- Access integer coordinates directly (convenience wrapper) -/
def coords (p : LatticePoint) : Fin spacetimeDim → ℤ := p.index.coords

/-- Convert lattice index to physical coordinate along axis μ -/
noncomputable def physicalCoord (p : LatticePoint) (μ : SpacetimeIndex) : ℝ :=
  (p.index.coord μ : ℝ) * ℓ_P

/-- Physical time coordinate -/
noncomputable def physicalTime (p : LatticePoint) : ℝ :=
  p.physicalCoord timeIndex

/-- Physical spatial coordinates -/
noncomputable def physicalSpace (p : LatticePoint) : Fin 3 → ℝ :=
  fun i => p.physicalCoord (spaceIndex i)

/-- The origin of physical spacetime -/
def origin : LatticePoint := ⟨LatticeIndex.origin⟩

/-- From integer coordinates -/
def fromIndex (idx : LatticeIndex) : LatticePoint := ⟨idx⟩

/-- Shift by +1 along axis μ -/
def shiftPos (p : LatticePoint) (μ : SpacetimeIndex) : LatticePoint :=
  ⟨p.index.shiftPos μ⟩

/-- Shift by -1 along axis μ -/
def shiftNeg (p : LatticePoint) (μ : SpacetimeIndex) : LatticePoint :=
  ⟨p.index.shiftNeg μ⟩

/-- Two lattice points are nearest neighbors -/
def isNearestNeighbor (p q : LatticePoint) : Prop :=
  p.index.isNearestNeighbor q.index

/-- shiftPos creates distinct points for distinct axes -/
theorem shiftPos_injective_axis (p : LatticePoint) :
    Function.Injective (fun μ => p.shiftPos μ) := by
  intro μ ν h
  simp only [shiftPos, LatticePoint.mk.injEq] at h
  by_contra hne
  exact LatticeIndex.shiftPos_ne_shiftPos_of_ne p.index hne h

/-- shiftNeg creates distinct points for distinct axes -/
theorem shiftNeg_injective_axis (p : LatticePoint) :
    Function.Injective (fun μ => p.shiftNeg μ) := by
  intro μ ν h
  simp only [shiftNeg, LatticePoint.mk.injEq] at h
  by_contra hne
  exact LatticeIndex.shiftNeg_ne_shiftNeg_of_ne p.index hne h

/-- shiftPos and shiftNeg create different points -/
theorem shiftPos_ne_shiftNeg (p : LatticePoint) (μ ν : SpacetimeIndex) :
    p.shiftPos μ ≠ p.shiftNeg ν := by
  intro h
  simp only [shiftPos, shiftNeg, LatticePoint.mk.injEq] at h
  exact LatticeIndex.shiftPos_ne_shiftNeg_any p.index μ ν h

/-- Inverse operations at LatticePoint level -/
@[simp]
theorem shiftNeg_shiftPos (p : LatticePoint) (μ : SpacetimeIndex) :
    (p.shiftPos μ).shiftNeg μ = p := by
  apply LatticePoint.ext
  show (p.index.shiftPos μ).shiftNeg μ = p.index
  exact LatticeIndex.shiftNeg_shiftPos p.index μ

@[simp]
theorem shiftPos_shiftNeg (p : LatticePoint) (μ : SpacetimeIndex) :
    (p.shiftNeg μ).shiftPos μ = p := by
  apply LatticePoint.ext
  show (p.index.shiftNeg μ).shiftPos μ = p.index
  exact LatticeIndex.shiftPos_shiftNeg p.index μ

/-- Shifts commute at LatticePoint level -/
theorem shiftPos_comm (p : LatticePoint) (μ ν : SpacetimeIndex) :
    (p.shiftPos μ).shiftPos ν = (p.shiftPos ν).shiftPos μ := by
  apply LatticePoint.ext
  show (p.index.shiftPos μ).shiftPos ν = (p.index.shiftPos ν).shiftPos μ
  exact LatticeIndex.shiftPos_shiftPos_comm p.index μ ν

theorem shiftNeg_comm (p : LatticePoint) (μ ν : SpacetimeIndex) :
    (p.shiftNeg μ).shiftNeg ν = (p.shiftNeg ν).shiftNeg μ := by
  apply LatticePoint.ext
  show (p.index.shiftNeg μ).shiftNeg ν = (p.index.shiftNeg ν).shiftNeg μ
  exact LatticeIndex.shiftNeg_shiftNeg_comm p.index μ ν

theorem shiftPos_shiftNeg_comm (p : LatticePoint) (μ ν : SpacetimeIndex) :
    (p.shiftPos μ).shiftNeg ν = (p.shiftNeg ν).shiftPos μ := by
  apply LatticePoint.ext
  show (p.index.shiftPos μ).shiftNeg ν = (p.index.shiftNeg ν).shiftPos μ
  exact LatticeIndex.shiftPos_shiftNeg_comm p.index μ ν

end LatticePoint

/-! ## Fields on the Lattice -/

/-- A scalar field on the lattice -/
def LatticeScalarField := LatticePoint → ℝ

/-- A vector field on the lattice (one value per spacetime direction) -/
def LatticeVectorField := LatticePoint → SpacetimeIndex → ℝ

/-- A tensor field on the lattice (matrix-valued) -/
def LatticeTensorField := LatticePoint → SpacetimeIndex → SpacetimeIndex → ℝ

namespace LatticeScalarField

/-- Zero scalar field -/
def zero : LatticeScalarField := fun _ => 0

/-- Constant scalar field -/
def const (val : ℝ) : LatticeScalarField := fun _ => val

/-- Add two scalar fields -/
instance : Add LatticeScalarField where
  add f g := fun p => f p + g p

/-- Multiply scalar fields -/
instance : Mul LatticeScalarField where
  mul f g := fun p => f p * g p

/-- Scale a scalar field -/
instance : SMul ℝ LatticeScalarField where
  smul r f := fun p => r * f p

end LatticeScalarField

/-! ## Finite Lattice Regions -/

/-- A finite region of the lattice, defined by bounds in each direction -/
structure LatticeRegion where
  /-- Lower bound for each coordinate -/
  lower : Fin spacetimeDim → ℤ
  /-- Upper bound for each coordinate (exclusive) -/
  upper : Fin spacetimeDim → ℤ
  /-- Bounds are valid -/
  bounds_valid : ∀ μ, lower μ < upper μ

namespace LatticeRegion

/-- A lattice index is in the region if all coordinates are within bounds -/
def contains (R : LatticeRegion) (p : LatticeIndex) : Prop :=
  ∀ μ, R.lower μ ≤ p.coord μ ∧ p.coord μ < R.upper μ

/-- Number of points along each axis -/
def extent (R : LatticeRegion) (μ : SpacetimeIndex) : ℕ :=
  (R.upper μ - R.lower μ).toNat

/-- Extent is positive -/
theorem extent_pos (R : LatticeRegion) (μ : SpacetimeIndex) : 0 < R.extent μ := by
  unfold extent
  have h := R.bounds_valid μ
  omega

/-- Total number of lattice points in the region -/
def volume (R : LatticeRegion) : ℕ :=
  Finset.univ.prod fun μ => R.extent μ

/-- Volume is positive -/
theorem volume_pos (R : LatticeRegion) : 0 < R.volume := by
  unfold volume
  apply Finset.prod_pos
  intro μ _
  exact extent_pos R μ

/-- Physical volume of the region (in Planck units) -/
noncomputable def physicalVolume (R : LatticeRegion) : ℝ :=
  (R.volume : ℝ) * ℓ_P ^ spacetimeDim

/-- Physical volume is positive -/
theorem physicalVolume_pos (R : LatticeRegion) : 0 < R.physicalVolume := by
  unfold physicalVolume
  apply mul_pos
  · exact Nat.cast_pos.mpr R.volume_pos
  · apply pow_pos PlanckLength_pos

end LatticeRegion

/-! ## Lattice Neighborhood Structure -/

/-- The pair of neighbors of p along axis μ: {p + e_μ, p - e_μ} -/
def neighborPair (p : LatticePoint) (μ : SpacetimeIndex) : Finset LatticePoint :=
  {p.shiftPos μ, p.shiftNeg μ}

/-- The neighbor pair has exactly 2 elements -/
theorem neighborPair_card (p : LatticePoint) (μ : SpacetimeIndex) :
    (neighborPair p μ).card = 2 := by
  unfold neighborPair
  rw [Finset.card_insert_of_not_mem]
  · simp
  · simp only [Finset.mem_singleton]
    intro h
    exact LatticeIndex.shiftPos_ne_shiftNeg p.index μ (congrArg LatticePoint.index h)

/-- The 2d nearest neighbors of a point (±1 in each of d directions) -/
def nearestNeighbors (p : LatticePoint) : Finset LatticePoint :=
  Finset.univ.biUnion fun μ => neighborPair p μ

/-- Key lemma: neighbor pairs for different axes are pairwise disjoint -/
theorem neighborPair_pairwise_disjoint (p : LatticePoint) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset SpacetimeIndex)) (neighborPair p) := by
  intro μ _ ν _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hxμ hxν
  simp only [neighborPair, Finset.mem_insert, Finset.mem_singleton] at hxμ hxν
  rcases hxμ with rfl | rfl <;> rcases hxν with h | h
  · -- shiftPos μ = shiftPos ν
    simp only [LatticePoint.shiftPos, LatticePoint.mk.injEq] at h
    exact LatticeIndex.shiftPos_ne_shiftPos_of_ne p.index hne h
  · -- shiftPos μ = shiftNeg ν
    simp only [LatticePoint.shiftPos, LatticePoint.shiftNeg, LatticePoint.mk.injEq] at h
    exact LatticeIndex.shiftPos_ne_shiftNeg_any p.index μ ν h
  · -- shiftNeg μ = shiftPos ν
    simp only [LatticePoint.shiftPos, LatticePoint.shiftNeg, LatticePoint.mk.injEq] at h
    exact LatticeIndex.shiftPos_ne_shiftNeg_any p.index ν μ h.symm
  · -- shiftNeg μ = shiftNeg ν
    simp only [LatticePoint.shiftNeg, LatticePoint.mk.injEq] at h
    exact LatticeIndex.shiftNeg_ne_shiftNeg_of_ne p.index hne h

/-- Coordination number: number of nearest neighbors (= 2d for hypercubic lattice) -/
theorem coordination_number (p : LatticePoint) :
    (nearestNeighbors p).card = 2 * spacetimeDim := by
  unfold nearestNeighbors
  rw [Finset.card_biUnion (neighborPair_pairwise_disjoint p)]
  simp only [neighborPair_card]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [spacetimeDim]

/-- Alternative form: coordination number equals 8 in 4D -/
theorem coordination_number_eq_eight (p : LatticePoint) :
    (nearestNeighbors p).card = 8 := by
  rw [coordination_number]
  norm_num [spacetimeDim]

/-- Every element of nearestNeighbors is indeed a nearest neighbor -/
theorem mem_nearestNeighbors_iff (p q : LatticePoint) :
    q ∈ nearestNeighbors p ↔ ∃ μ, q = p.shiftPos μ ∨ q = p.shiftNeg μ := by
  unfold nearestNeighbors neighborPair
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
             Finset.mem_insert, Finset.mem_singleton]

/-- Every nearest neighbor has Manhattan distance 1 -/
theorem nearestNeighbor_manhattanDist (p : LatticePoint) {q : LatticePoint}
    (hq : q ∈ nearestNeighbors p) : p.index.manhattanDist q.index = 1 := by
  rw [mem_nearestNeighbors_iff] at hq
  obtain ⟨μ, rfl | rfl⟩ := hq
  · exact LatticeIndex.shiftPos_isNearestNeighbor p.index μ
  · rw [LatticeIndex.manhattanDist_comm]
    have h := LatticeIndex.shiftNeg_isNearestNeighbor p.index μ
    unfold LatticeIndex.isNearestNeighbor at h
    rwa [LatticeIndex.manhattanDist_comm] at h

end DiscreteSpacetime.Basic
