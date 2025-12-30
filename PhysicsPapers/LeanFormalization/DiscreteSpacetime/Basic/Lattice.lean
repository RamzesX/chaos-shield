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
-/

import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Int.Basic (removed - Int is in core)
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.MetricSpace.Basic
import DiscreteSpacetime.Basic.Constants

namespace DiscreteSpacetime.Basic

/-! ## Spacetime Dimension -/

/-- Spacetime is 4-dimensional (1 time + 3 space) -/
def spacetimeDim : ℕ := 4

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
    These are the "discrete coordinates" of a spacetime point. -/
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

/-- Add two lattice indices -/
instance : Add LatticeIndex where
  add p q := ⟨fun μ => p.coords μ + q.coords μ⟩

/-- Subtract lattice indices -/
instance : Sub LatticeIndex where
  sub p q := ⟨fun μ => p.coords μ - q.coords μ⟩

/-- Negate a lattice index -/
instance : Neg LatticeIndex where
  neg p := ⟨fun μ => -p.coords μ⟩

/-- Zero lattice index -/
instance : Zero LatticeIndex where
  zero := origin

/-- Unit vector along axis μ -/
def unitVector (μ : SpacetimeIndex) : LatticeIndex :=
  ⟨fun ν => if μ = ν then 1 else 0⟩

/-- Shift by +1 along axis μ -/
def shiftPos (p : LatticeIndex) (μ : SpacetimeIndex) : LatticeIndex :=
  p + unitVector μ

/-- Shift by -1 along axis μ -/
def shiftNeg (p : LatticeIndex) (μ : SpacetimeIndex) : LatticeIndex :=
  p - unitVector μ

/-- Manhattan distance (L¹ norm on the lattice) -/
def manhattanDist (p q : LatticeIndex) : ℕ :=
  (Finset.univ.sum fun μ => (p.coord μ - q.coord μ).natAbs)

/-- Two points are nearest neighbors if their Manhattan distance is 1 -/
def isNearestNeighbor (p q : LatticeIndex) : Prop :=
  manhattanDist p q = 1

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

/-- Total number of lattice points in the region -/
def volume (R : LatticeRegion) : ℕ :=
  Finset.univ.prod fun μ => R.extent μ

/-- Physical volume of the region (in Planck units) -/
noncomputable def physicalVolume (R : LatticeRegion) : ℝ :=
  (R.volume : ℝ) * ℓ_P ^ spacetimeDim

end LatticeRegion

/-! ## Lattice Neighborhood Structure -/

/-- The 2d nearest neighbors of a point (±1 in each of d directions) -/
def nearestNeighbors (p : LatticePoint) : Finset LatticePoint :=
  Finset.univ.biUnion fun μ =>
    {p.shiftPos μ, p.shiftNeg μ}

/-- Coordination number: number of nearest neighbors (= 2d for hypercubic lattice) -/
theorem coordination_number (p : LatticePoint) :
    (nearestNeighbors p).card = 2 * spacetimeDim := by
  sorry -- TODO: Prove this for hypercubic lattice

end DiscreteSpacetime.Basic
