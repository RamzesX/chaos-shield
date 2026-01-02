/-
  Omega-Theory: Discrete Spacetime Framework
  ==========================================

  A Lean 4 formalization of the discrete spacetime physics framework,
  building machine-verified proofs from axioms to emergence theorems.

  Architecture:
  - Basic: Physical constants, lattice structure, discrete operators
  - Axioms: Physical postulates (discrete spacetime, action quantization, information conservation)
  - Geometry: Discrete differential geometry (metric, connection, curvature, torsion)
  - Irrationality: Computational deadlines from truncated irrationals
  - Dynamics: Healing flow and stability theory
  - Conservation: Noether theorems, Fourth Law, and spin-information coupling
  - Torsion: Einstein-Cartan theory and Poplawski's Big Bounce
  - Emergence: Continuum limit and Einstein equation derivation
  - Variational: Erdős-Lagrangian correspondence, information geodesics

  New in v2.0 (Poplawski Integration):
  - Einstein-Cartan torsion formalization
  - Spin-torsion coupling (Cartan's equations)
  - Torsion-enhanced healing flow
  - Big Bounce theorem (singularity avoidance)
  - Spin-information correspondence
  - Redundant singularity protection

  New in v2.1 (Erdős-Lagrangian Unification):
  - Graph Lagrangian and action principles
  - Discrete Noether's theorem (symmetry → conservation)
  - Fourth Law derivation from gauge symmetry
  - Information geodesics (action-minimizing paths)
  - Erdős-Action equivalence theorem

  References:
  - Appendix P: Einstein-Cartan Torsion Integration
  - Poplawski, N. J. (2010-2021). Einstein-Cartan cosmology series.
  - ErdosLagrangianUnification.md: Graph-action correspondence

  Copyright (c) 2024. All rights reserved.
-/

-- Basic modules (foundations)
import DiscreteSpacetime.Basic.Constants
import DiscreteSpacetime.Basic.Lattice
import DiscreteSpacetime.Basic.Operators

-- Axioms (physical postulates)
import DiscreteSpacetime.Axioms.Spacetime
import DiscreteSpacetime.Axioms.Action
import DiscreteSpacetime.Axioms.Information
import DiscreteSpacetime.Axioms.Computation

-- Geometry (discrete differential geometry)
import DiscreteSpacetime.Geometry.Metric
import DiscreteSpacetime.Geometry.Connection
import DiscreteSpacetime.Geometry.Curvature
import DiscreteSpacetime.Geometry.Einstein
import DiscreteSpacetime.Geometry.Torsion  -- NEW: Einstein-Cartan torsion

-- Irrationality (computational bounds)
import DiscreteSpacetime.Irrationality.Approximations
import DiscreteSpacetime.Irrationality.BoundsLemmas
import DiscreteSpacetime.Irrationality.Sqrt2Precision
import DiscreteSpacetime.Irrationality.Bounds
import DiscreteSpacetime.Irrationality.Uncertainty

-- Dynamics (healing flow)
import DiscreteSpacetime.Dynamics.Defects
import DiscreteSpacetime.Dynamics.Healing  -- UPDATED: Now includes torsion enhancement
import DiscreteSpacetime.Dynamics.Stability

-- Conservation (Noether theorems)
import DiscreteSpacetime.Conservation.Noether
import DiscreteSpacetime.Conservation.FourthLaw
import DiscreteSpacetime.Conservation.Correspondence
import DiscreteSpacetime.Conservation.SpinInformation  -- NEW: Spin-information coupling

-- Torsion (Einstein-Cartan integration - Poplawski)
import DiscreteSpacetime.Torsion.SpinTorsion  -- NEW: Spin-torsion coupling
import DiscreteSpacetime.Torsion.BigBounce    -- NEW: Singularity avoidance

-- Emergence (continuum limit)
import DiscreteSpacetime.Emergence.ContinuumLimit
import DiscreteSpacetime.Emergence.EinsteinEmergence
import DiscreteSpacetime.Emergence.Predictions

-- Variational (Erdős-Lagrangian correspondence)
import DiscreteSpacetime.Variational.GraphAction        -- NEW: Graph Lagrangian/action
import DiscreteSpacetime.Variational.DiscreteNoether    -- NEW: Discrete Noether's theorem
import DiscreteSpacetime.Variational.InformationGeodesics  -- NEW: Information geodesics
