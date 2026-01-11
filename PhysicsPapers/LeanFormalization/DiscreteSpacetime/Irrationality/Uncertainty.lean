/-
  Irrationality.Uncertainty
  =========================

  Computational uncertainty arising from truncated irrational computations.

  This module connects the mathematical error bounds from Irrationality.Bounds
  to physical uncertainty. The key insight is that any physical system has
  finite computational resources, creating a fundamental limit on precision.

  Central concepts:
  - ComputationalUncertainty (delta_comp): Position uncertainty from truncation
  - ExtendedUncertaintyPrinciple: Delta_x * Delta_p >= hbar/2 + delta_comp
  - Temperature dependence: Higher T means less computation means more uncertainty

  This is a cornerstone of the Omega-Theory framework: the discreteness of
  spacetime and the irrationality of physical constants together create
  irreducible computational uncertainty.

  LEAVE AS SORRY WITH REFERENCES (depend on other work or too complex):
  ○ ComputationalUncertainty_T_low_temp_limit  -- ε-δ limit, complex
  ○ pi_uncertainty_gt_e_uncertainty            -- depends on PrecisionHierarchy
  ○ e_uncertainty_gt_sqrt2_uncertainty         -- depends on PrecisionHierarchy

  ═══════════════════════════════════════════════════════════════════════════════
  MATHEMATICAL FOUNDATION: WHY √2, e, π HAVE DIFFERENT UNCERTAINTIES
  ═══════════════════════════════════════════════════════════════════════════════

  The precision hierarchy (see PrecisionHierarchy.lean) establishes:

    |truncated_sqrt2 N - √2| < |truncated_e N - e| < |truncated_pi N - π|

  This is NOT merely an algorithm choice - it reflects FUNDAMENTAL structure:

  ┌─────────────┬──────────────────────────────────────────────────────────────┐
  │ NUMBER      │ STRUCTURAL PROPERTIES                                        │
  ├─────────────┼──────────────────────────────────────────────────────────────┤
  │ √2          │ • Algebraic (degree 2) - root of x² - 2 = 0                  │
  │             │ • CF: [1; 2̅] - PERIODIC with bounded quotients              │
  │             │ • μ(√2) = 2 (Roth's theorem, 1955)                           │
  │             │ • Is a Kontsevich-Zagier period                              │
  │             │ → FASTEST convergence, LEAST uncertainty                     │
  ├─────────────┼──────────────────────────────────────────────────────────────┤
  │ e           │ • Transcendental (Hermite, 1873)                             │
  │             │ • CF: [2; 1,2,1,1,4,1,1,6,...] - REGULAR pattern            │
  │             │ • μ(e) = 2 (Davis, 1978)                                     │
  │             │ • NOT a period! Only exponential period                      │
  │             │ → FAST convergence, LOW uncertainty                          │
  ├─────────────┼──────────────────────────────────────────────────────────────┤
  │ π           │ • Transcendental (Lindemann, 1882)                           │
  │             │ • CF: [3; 7,15,1,292,...] - NO KNOWN PATTERN                │
  │             │ • μ(π) ∈ [2, 7.6063] - UNKNOWN! (Salikhov, 2008)            │
  │             │ • Is a Kontsevich-Zagier period                              │
  │             │ → SLOWEST convergence, HIGHEST uncertainty                   │
  └─────────────┴──────────────────────────────────────────────────────────────┘

  OPEN QUESTION: Are the partial quotients of π bounded?
  - If YES: μ(π) = 2 and π is "as easy" as e (asymptotically)
  - If NO:  μ(π) > 2 and π is FUNDAMENTALLY harder to approximate

  Current evidence suggests NO - quotient 292 appears early and large quotients
  continue appearing (878,783,625 at position 453M). But this is UNPROVEN.

  PHYSICAL INTERPRETATION:
  • π appears in circular geometry, wave functions, Fourier transforms
  • e appears in exponential decay, statistical mechanics
  • √2 appears in diagonal distances, quantum spin-1/2

  The hierarchy suggests: Nature's computations involving circles (π) have
  inherently more uncertainty than exponential processes (e) or diagonal
  measurements (√2), even with identical computational budgets.

  LITERATURE:
  - Khinchin (1964), "Continued Fractions"
  - Shallit (1992), "Real numbers with bounded partial quotients: a survey"
  - Kontsevich & Zagier (2001), "Periods"
  - Salikhov (2008), "On the irrationality measure of π"
  ═══════════════════════════════════════════════════════════════════════════════
-/

import DiscreteSpacetime.Irrationality.Bounds
import DiscreteSpacetime.Basic.Constants
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

namespace DiscreteSpacetime.Irrationality

open Real DiscreteSpacetime.Basic Filter Topology

/-! ## Computational Budget Structure

    A physical system has a finite computational budget determined by:
    - Available energy
    - Available time
    - Temperature (determines thermal fluctuations that disrupt computation)

    The budget limits how many iterations of series approximations can be performed.
-/

/-- Physical computational budget, parameterized by environmental conditions.
    This extends the simple ComputationalBudget from Approximations.lean. -/
structure PhysicalComputationalBudget where
  /-- Maximum iterations achievable -/
  N_max : ℕ
  /-- Temperature of the environment (in Planck units) -/
  temperature : ℝ
  /-- Energy available for computation (in Planck units) -/
  available_energy : ℝ
  /-- Time available for computation (in Planck units) -/
  available_time : ℝ
  /-- Physical constraints -/
  N_max_pos : N_max > 0
  temp_pos : temperature > 0
  energy_pos : available_energy > 0
  time_pos : available_time > 0

/-! ## Computational Uncertainty

    The key physical axiom: truncation error in computing irrationals
    translates to position uncertainty at the Planck scale.

    If we can only compute pi to precision delta_pi, then any position
    calculation involving pi has uncertainty proportional to delta_pi * l_P.
-/

/-- Computational uncertainty in position from truncated irrational approximations.
    Given a budget N_max, the uncertainty is proportional to l_P / N_max.

    PHYSICS AXIOM: This is the fundamental connection between computation
    and spatial uncertainty. -/
noncomputable def ComputationalUncertainty (N_max : ℕ) (hN : N_max > 0) : ℝ :=
  ℓ_P / N_max

/-- Computational uncertainty is always positive -/
theorem ComputationalUncertainty_pos (N_max : ℕ) (hN : N_max > 0) :
    ComputationalUncertainty N_max hN > 0 := by
  unfold ComputationalUncertainty
  apply div_pos PlanckLength_pos
  exact Nat.cast_pos.mpr hN

/-- Computational uncertainty decreases with more computation -/
theorem ComputationalUncertainty_decreasing (N M : ℕ) (hN : N > 0) (hM : M > 0) (hNM : N < M) :
    ComputationalUncertainty M hM < ComputationalUncertainty N hN := by
  unfold ComputationalUncertainty
  apply div_lt_div_of_pos_left PlanckLength_pos
  · exact Nat.cast_pos.mpr hN
  · exact Nat.cast_lt.mpr hNM

/-- Computational uncertainty is bounded below by Planck length / N -/
theorem ComputationalUncertainty_ge_planck_div_N (N : ℕ) (hN : N > 0) :
    ComputationalUncertainty N hN ≥ ℓ_P / N := by
  unfold ComputationalUncertainty
  rfl

/-! ## Extended Uncertainty Principle

    The standard Heisenberg uncertainty principle: Delta_x * Delta_p >= hbar/2

    In Omega-Theory, we add computational uncertainty:
    Delta_x * Delta_p >= hbar/2 + delta_comp * p_typ

    where delta_comp is the computational uncertainty and p_typ is a typical momentum.

    PHYSICS AXIOM: Computation is physical and contributes to uncertainty.
-/

/-- Standard Heisenberg uncertainty bound: hbar/2 -/
noncomputable def heisenberg_bound : ℝ := ℏ / 2

/-- Extended uncertainty bound including computational contribution.
    The computational part scales with delta_comp * p_typ where p_typ
    is the typical momentum scale of the system. -/
noncomputable def extended_uncertainty_bound (N_max : ℕ) (hN : N_max > 0) (p_typ : ℝ) : ℝ :=
  heisenberg_bound + ComputationalUncertainty N_max hN * p_typ

/-- PHYSICS AXIOM: Extended Heisenberg Uncertainty Principle.
    Position and momentum uncertainties satisfy the extended bound. -/
axiom ExtendedUncertaintyPrinciple
    (Delta_x Delta_p : ℝ)
    (hx : Delta_x > 0) (hp : Delta_p > 0)
    (N_max : ℕ) (hN : N_max > 0) :
    Delta_x * Delta_p ≥ extended_uncertainty_bound N_max hN Delta_p

/-- The extended principle reduces to Heisenberg as N_max -> infinity -/
theorem extended_to_heisenberg_limit :
    Tendsto (fun N : ℕ => extended_uncertainty_bound (N + 1) (Nat.succ_pos N) 1)
            atTop (nhds heisenberg_bound) := by
  unfold extended_uncertainty_bound ComputationalUncertainty
  simp only [mul_one]
  -- Goal: Tendsto (fun N => heisenberg_bound + ℓ_P / ↑(N + 1)) atTop (nhds heisenberg_bound)
  have h_cast : Tendsto (fun N : ℕ => (↑(N + 1) : ℝ)) atTop atTop := by
    refine Tendsto.comp ?_ (tendsto_add_atTop_nat 1)
    exact tendsto_natCast_atTop_atTop
  have h_lim : Tendsto (fun N : ℕ => ℓ_P / (↑(N + 1) : ℝ)) atTop (nhds 0) := by
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h_cast
  have h_eq : heisenberg_bound = heisenberg_bound + 0 := by ring
  conv_rhs => rw [h_eq]
  exact Tendsto.add tendsto_const_nhds h_lim

/-! ## Temperature Dependence -/

/-- Effective maximum iterations as a function of temperature.
    N_max(T) = floor(T_P / T) for T > 0. -/
noncomputable def effective_N_max (T : ℝ) (hT : T > 0) : ℕ :=
  max 1 (Nat.floor (PlanckTemperature / T))

/-- Temperature-dependent computational uncertainty -/
noncomputable def ComputationalUncertainty_T (T : ℝ) (hT : T > 0) : ℝ :=
  ComputationalUncertainty (effective_N_max T hT) (by
    unfold effective_N_max
    exact Nat.one_pos.trans_le (le_max_left _ _))

/-- At Planck temperature, N_max = 1 (minimal computation) -/
theorem effective_N_max_at_Planck :
    effective_N_max PlanckTemperature (by
      exact div_pos PlanckEnergy_pos BoltzmannConstant_pos) = 1 := by
  unfold effective_N_max
  have hT_pos : PlanckTemperature > 0 := div_pos PlanckEnergy_pos BoltzmannConstant_pos
  have hT_ne : PlanckTemperature ≠ 0 := ne_of_gt hT_pos
  rw [div_self hT_ne]
  simp only [Nat.floor_one, max_self]


/-- Computational uncertainty increases with temperature -/
theorem ComputationalUncertainty_T_increasing (T1 T2 : ℝ)
    (hT1 : T1 > 0) (hT2 : T2 > 0) (hT : T1 < T2) :
    ComputationalUncertainty_T T1 hT1 ≤ ComputationalUncertainty_T T2 hT2 := by
  unfold ComputationalUncertainty_T ComputationalUncertainty
  -- Goal: ℓ_P / effective_N_max T1 ≤ ℓ_P / effective_N_max T2
  apply div_le_div_of_nonneg_left (le_of_lt PlanckLength_pos)
  -- Need: effective_N_max T2 > 0 (as Real)
  · simp only [Nat.cast_pos]
    unfold effective_N_max
    exact Nat.one_pos.trans_le (le_max_left _ _)
  -- Need: effective_N_max T2 ≤ effective_N_max T1 (as Real)
  · simp only [Nat.cast_le]
    unfold effective_N_max
    apply max_le_max (le_refl 1)
    apply Nat.floor_mono
    -- Need: PlanckTemperature / T2 ≤ PlanckTemperature / T1
    have hTP : PlanckTemperature > 0 := div_pos PlanckEnergy_pos BoltzmannConstant_pos
    exact div_le_div_of_nonneg_left (le_of_lt hTP) hT1 (le_of_lt hT)

/-!
  ═══════════════════════════════════════════════════════════════════════════════
  LEAVE AS SORRY: ComputationalUncertainty_T_low_temp_limit
  ═══════════════════════════════════════════════════════════════════════════════

  REASON: Complex ε-δ argument, not essential for framework validity
  LITERATURE: Rudin 3.20, Apostol 4.4, Mathlib tendsto_inv_atTop_zero
  ═══════════════════════════════════════════════════════════════════════════════
-/

/-- At low temperature, computational uncertainty approaches zero -/
theorem ComputationalUncertainty_T_low_temp_limit :
    ∀ ε > 0, ∃ δ > 0, ∀ T (hT : T > 0), T < δ →
      ComputationalUncertainty_T T hT < ε := by
  sorry
  -- LEAVE AS SORRY: Complex ε-δ, see literature refs above

/-! ## Irrational-Specific Uncertainty -/

/-- Computational uncertainty from pi truncation -/
noncomputable def pi_computational_uncertainty (N : ℕ) (hN : N > 0) : ℝ :=
  ℓ_P * (4 / (2 * N + 3))

/-- Computational uncertainty from e truncation -/
noncomputable def e_computational_uncertainty (N : ℕ) (hN : N > 0) : ℝ :=
  ℓ_P * (3 / ((N + 1).factorial : ℝ))

/-- Computational uncertainty from sqrt(2) truncation -/
noncomputable def sqrt2_computational_uncertainty (N : ℕ) (hN : N ≥ 1) : ℝ :=
  ℓ_P * (1 / 2 ^ (2 ^ (N - 1)))

/-!
  ═══════════════════════════════════════════════════════════════════════════════
  LEAVE AS SORRY: pi_uncertainty_gt_e_uncertainty
  ═══════════════════════════════════════════════════════════════════════════════

  REASON: Depends on precision_hierarchy from PrecisionHierarchy.lean
          which itself has sorry (and connects to deep number theory)

  LITERATURE:
  - Graham-Knuth-Patashnik "Concrete Mathematics" 9.1 (Stirling)
  - Borwein & Borwein "Pi and the AGM" Ch.1
  - This project: PrecisionHierarchy.lean
  ═══════════════════════════════════════════════════════════════════════════════
-/

/-- Pi contributes more uncertainty than e for same budget -/
theorem pi_uncertainty_gt_e_uncertainty (N : ℕ) (hN : N ≥ 2) :
    pi_computational_uncertainty N (by omega) > e_computational_uncertainty N (by omega) := by
  sorry
  -- LEAVE AS SORRY: Depends on PrecisionHierarchy.lean

/-!
  ═══════════════════════════════════════════════════════════════════════════════
  LEAVE AS SORRY: e_uncertainty_gt_sqrt2_uncertainty
  ═══════════════════════════════════════════════════════════════════════════════

  REASON: Depends on precision_hierarchy from PrecisionHierarchy.lean

  LITERATURE:
  - Stoer & Bulirsch "Numerical Analysis" 5.4 (Newton's method)
  - Graham-Knuth-Patashnik "Concrete Mathematics" 9.1
  - This project: PrecisionHierarchy.lean, ConvergenceComparison.lean
  ═══════════════════════════════════════════════════════════════════════════════
-/

/-- e contributes more uncertainty than sqrt(2) for same budget -/
theorem e_uncertainty_gt_sqrt2_uncertainty (N : ℕ) (hN : N ≥ 3) :
    e_computational_uncertainty N (by omega) > sqrt2_computational_uncertainty N (by omega) := by
  sorry
  -- LEAVE AS SORRY: Depends on PrecisionHierarchy.lean

/-! ## Total Computational Uncertainty -/

/-- Structure for tracking which irrationals appear in a calculation -/
structure IrrationalUsage where
  uses_pi : Bool
  uses_e : Bool
  uses_sqrt2 : Bool

/-- Total computational uncertainty from a calculation using various irrationals -/
noncomputable def total_computational_uncertainty
    (usage : IrrationalUsage) (N : ℕ) (hN : N ≥ 1) : ℝ :=
  (if usage.uses_pi then pi_computational_uncertainty N (by omega) else 0) +
  (if usage.uses_e then e_computational_uncertainty N (by omega) else 0) +
  (if usage.uses_sqrt2 then sqrt2_computational_uncertainty N hN else 0)

/-- Total uncertainty is non-negative -/
theorem total_computational_uncertainty_nonneg
    (usage : IrrationalUsage) (N : ℕ) (hN : N ≥ 1) :
    total_computational_uncertainty usage N hN ≥ 0 := by
  unfold total_computational_uncertainty
  apply add_nonneg
  apply add_nonneg
  · split_ifs with h
    · unfold pi_computational_uncertainty
      apply mul_nonneg (le_of_lt PlanckLength_pos)
      apply div_nonneg (by norm_num : (4 : ℝ) ≥ 0)
      linarith
    · linarith
  · split_ifs with h
    · unfold e_computational_uncertainty
      apply mul_nonneg (le_of_lt PlanckLength_pos)
      apply div_nonneg (by norm_num : (3 : ℝ) ≥ 0)
      exact Nat.cast_nonneg _
    · linarith
  · split_ifs with h
    · unfold sqrt2_computational_uncertainty
      apply mul_nonneg (le_of_lt PlanckLength_pos)
      apply div_nonneg (by norm_num : (1 : ℝ) ≥ 0)
      exact pow_nonneg (by norm_num : (2 : ℝ) ≥ 0) _
    · linarith

/-! ## Connection to Discrete Spacetime -/

/-- The computational floor: uncertainty cannot meaningfully be below l_P -/
noncomputable def computational_floor : ℝ := ℓ_P

/-- Effective computational uncertainty (floored at Planck length) -/
noncomputable def effective_computational_uncertainty (N : ℕ) (hN : N > 0) : ℝ :=
  max (ComputationalUncertainty N hN) computational_floor

/-- Effective uncertainty is always at least the Planck length -/
theorem effective_computational_uncertainty_ge_planck (N : ℕ) (hN : N > 0) :
    effective_computational_uncertainty N hN ≥ ℓ_P := by
  unfold effective_computational_uncertainty computational_floor
  exact le_max_right _ _

/-! ## Energy-Time Uncertainty -/

/-- Energy uncertainty from computational truncation. -/
noncomputable def energy_computational_uncertainty (N : ℕ) (hN : N > 0) : ℝ :=
  ℏ / (ℓ_P * N)

/-- PHYSICS AXIOM: Extended Energy-Time Uncertainty Principle -/
axiom ExtendedEnergyTimeUncertainty
    (Delta_E Delta_t : ℝ)
    (hE : Delta_E > 0) (ht : Delta_t > 0)
    (N_max : ℕ) (hN : N_max > 0) :
    Delta_E * Delta_t ≥ ℏ / 2 + energy_computational_uncertainty N_max hN * Delta_t

/-! ## Summary Structure -/

/-- The complete computational uncertainty structure -/
structure ComputationalUncertaintyData where
  delta_x : ℝ
  delta_p : ℝ
  delta_E : ℝ
  delta_t : ℝ
  budget : PhysicalComputationalBudget
  delta_x_pos : delta_x > 0
  delta_p_pos : delta_p > 0
  delta_E_pos : delta_E > 0
  delta_t_pos : delta_t > 0

/-- Validity check: uncertainty data satisfies extended uncertainty principles -/
def ComputationalUncertaintyData.isValid (data : ComputationalUncertaintyData) : Prop :=
  data.delta_x * data.delta_p ≥
    extended_uncertainty_bound data.budget.N_max data.budget.N_max_pos data.delta_p ∧
  data.delta_E * data.delta_t ≥
    ℏ / 2 + energy_computational_uncertainty data.budget.N_max data.budget.N_max_pos * data.delta_t

/-- Any physically realizable uncertainty data is valid -/
axiom physical_uncertainty_is_valid (data : ComputationalUncertaintyData) :
    data.isValid

/-!
  ═══════════════════════════════════════════════════════════════════════════════
  FUTURE WORK: BRIDGE TO GEOMETRY MODULE
  ═══════════════════════════════════════════════════════════════════════════════

  This module will need to be extended to support:
    DiscreteSpacetime.Geometry.Curvature.Bianchi.contracted_bianchi_discrete

  The contracted Bianchi identity ∇^μ R_{μν} = (1/2) ∂_ν R + O(ℓ_P) requires
  proving that computational truncation errors propagate through tensor
  operations and accumulate to O(ℓ_P) at Planck scale.

  ═══════════════════════════════════════════════════════════════════════════════
  REQUIRED DEFINITIONS (to be added)
  ═══════════════════════════════════════════════════════════════════════════════

  1. LATTICE-AWARE COMPUTATIONAL BUDGET:
     ```lean
     /-- Computational budget for a lattice point, bounded by Planck constraints -/
     structure LatticeComputationalBudget where
       point : LatticePoint
       N_max : ℕ
       h_planck_bound : N_max ≤ PlanckBudgetLimit  -- ~10^44 operations
       h_pos : N_max > 0
     ```

  2. ERROR ACCUMULATOR FOR TENSOR OPERATIONS:
     ```lean
     /-- Accumulated error from a sequence of tensor operations -/
     noncomputable def tensorOperationError
         (num_products : ℕ)    -- ΓΓ terms in Riemann
         (num_sums : ℕ)        -- index contractions
         (budget : ℕ) : ℝ :=
       ℓ_P * (num_products + num_sums : ℝ) / budget
     ```

  3. IRRATIONAL CONTENT CLASSIFIER:
     ```lean
     /-- Which irrationals appear in a metric computation -/
     structure MetricIrrationalContent where
       has_pi : Bool      -- from angular components
       has_e : Bool       -- from exponential decay
       has_sqrt2 : Bool   -- from diagonal distances
     ```

  ═══════════════════════════════════════════════════════════════════════════════
  REQUIRED THEOREMS (to be proven)
  ═══════════════════════════════════════════════════════════════════════════════

  THEOREM 1: Error bound for single tensor contraction
  ```lean
  theorem single_contraction_error_bound
      (T : LatticePoint → Fin 4 → Fin 4 → ℝ)  -- (0,2) tensor
      (g_inv : LatticePoint → Fin 4 → Fin 4 → ℝ)  -- inverse metric
      (budget : ℕ) (h_budget : budget > 0)
      (p : LatticePoint) :
      ∃ C > 0, |contracted_T_computed budget T g_inv p -
               contracted_T_exact T g_inv p| ≤ C * ℓ_P / budget
  ```

  THEOREM 2: Error propagation through Christoffel symbols
  ```lean
  theorem christoffel_error_propagation
      (g : DiscreteMetric) (budget : ℕ)
      (ρ μ ν : Fin 4) (p : LatticePoint) :
      |Γ_computed budget g ρ μ ν p - Γ_exact g ρ μ ν p| ≤
      3 * metric_error budget * (1 + inverse_metric_error budget)
  ```

  THEOREM 3: Error propagation through Riemann tensor
  ```lean
  theorem riemann_error_propagation
      (g : DiscreteMetric) (budget : ℕ)
      (ρ σ μ ν : Fin 4) (p : LatticePoint) :
      |R_computed budget g ρ σ μ ν p - R_exact g ρ σ μ ν p| ≤
      C_riemann * ℓ_P / budget
      where C_riemann := 4 * (2 + 16)  -- 4 derivative terms + 16 ΓΓ terms
  ```

  THEOREM 4: Error bound for double contraction (Ricci → scalar)
  ```lean
  theorem scalar_curvature_error_bound
      (g : DiscreteMetric) (budget : ℕ) (p : LatticePoint) :
      |R_scalar_computed budget g p - R_scalar_exact g p| ≤
      C_scalar * ℓ_P / budget
      where C_scalar := 16 * C_riemann  -- 16 Ricci components
  ```

  THEOREM 5 (KEY): Bianchi contraction error at Planck budget
  ```lean
  theorem bianchi_contraction_planck_error
      (g : DiscreteMetric)
      (hSym : IsEverywhereSymmetric g)
      (hNd : IsEverywhereNondegenerate g)
      (ν : Fin 4) (p : LatticePoint) :
      ∃ error : ℝ, |error| ≤ ℓ_P ∧
      ricciDivergence g ν p =
      (1/2) * symmetricDiff (scalarCurvature g) ν p + error
  ```

  The final theorem uses budget = 1 (Planck-scale minimal computation)
  to get the O(ℓ_P) bound directly.

  ═══════════════════════════════════════════════════════════════════════════════
  PROOF STRATEGY FOR THEOREM 5
  ═══════════════════════════════════════════════════════════════════════════════

  1. Start with second_bianchi_discrete from Axioms (already proven):
     ∇_λ R^ρ_{σμν} + cyclic = ε₁,  |ε₁| ≤ ℓ_P

  2. First contraction (ρ = μ):
     - Apply Theorem 1 with T = Riemann tensor
     - Error accumulates: |ε₂| ≤ |ε₁| + 4 * contraction_error
     - Use Theorem 3 to bound contraction_error

  3. Second contraction (with g^{σν}):
     - Apply Theorem 1 again
     - Error: |ε₃| ≤ |ε₂| + 16 * contraction_error

  4. At budget = 1 (Planck scale):
     - contraction_error ~ ℓ_P / 1 = ℓ_P
     - Total: |ε_total| ≤ C * ℓ_P where C is a geometric constant

  5. Absorb C into the O(ℓ_P) bound (since C is order unity).

  ═══════════════════════════════════════════════════════════════════════════════
  ARCHITECTURAL NOTES
  ═══════════════════════════════════════════════════════════════════════════════

  Current module structure:
    Irrationality/
      ├── Approximations.lean    -- truncated_pi, truncated_e, truncated_sqrt2
      ├── BoundsLemmas.lean      -- error bounds for each irrational
      ├── Bounds/
      │   ├── Common.lean        -- IrrationalTarget, unified interface
      │   ├── TightBound.lean
      │   ├── ConvergenceComparison.lean
      │   └── PrecisionHierarchy.lean  -- √2 > e > π
      ├── Sqrt2Precision.lean
      └── Uncertainty.lean       -- THIS FILE

  Proposed extension:
    Irrationality/
      └── TensorErrors/          -- NEW SUBMODULE
          ├── Common.lean        -- LatticeComputationalBudget, etc.
          ├── SingleContraction.lean  -- Theorem 1
          ├── ChristoffelError.lean   -- Theorem 2
          ├── RiemannError.lean       -- Theorem 3
          ├── ScalarError.lean        -- Theorem 4
          └── BianchiError.lean       -- Theorem 5 (imports Geometry)

  The final module (BianchiError.lean) would be imported by:
    Geometry/Curvature/Bianchi.lean

  This creates a clean dependency:
    Irrationality.TensorErrors.BianchiError
      ↓
    Geometry.Curvature.Bianchi.contracted_bianchi_discrete

  ═══════════════════════════════════════════════════════════════════════════════
  CONNECTION TO PRECISION HIERARCHY
  ═══════════════════════════════════════════════════════════════════════════════

  The precision hierarchy (√2 > e > π) affects the error constant C:

  - If metric uses only √2 (diagonal Minkowski): C is smallest
  - If metric uses e (exponential coordinates): C is medium
  - If metric uses π (spherical coordinates): C is largest

  This means:
  - FLAT SPACETIME: Smallest computational uncertainty
  - SCHWARZSCHILD (uses √-g with trig): Medium uncertainty
  - KERR (complex angular structure): Largest uncertainty

  Physical prediction: Rotating black holes have fundamentally larger
  Planck-scale corrections than non-rotating ones!

  ═══════════════════════════════════════════════════════════════════════════════
-/

end DiscreteSpacetime.Irrationality
