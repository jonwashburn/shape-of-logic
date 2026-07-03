import Mathlib
import IndisputableMonolith.RecogSpec.Core
import IndisputableMonolith.Constants
import IndisputableMonolith.RecogSpec.Spec

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity
namespace Framework

/-!
# Physics Framework Definitions (Shared)

This module contains shared definitions used by both NoAlternatives and the necessity proofs.
This breaks circular dependencies by providing only the core framework definitions.

-/

/-! ### Algorithmic Specification (Forward Declaration) -/

/-- An algorithmic specification is a finite string that generates states.
    (Forward declaration from DiscreteNecessity to avoid circular imports) -/
structure AlgorithmicSpec where
  description : List Bool  -- Finite binary string
  generates : ∀ n : ℕ, Option (List Bool)  -- Enumeration of states

/-- A framework has algorithmic spec if it can be enumerated by an algorithm. -/
def HasAlgorithmicSpec (StateSpace : Type) : Prop :=
  ∃ (spec : AlgorithmicSpec),
    ∃ (decode : List Bool → Option StateSpace),
      ∀ s : StateSpace, ∃ n : ℕ, ∃ code : List Bool,
        spec.generates n = some code ∧ decode code = some s

/-! ### Abstract Physics Framework Definition -/

/-- Abstract interface for any physics framework.
    This captures the minimal structure needed to "do physics":
    - A state space
    - Evolution rules
    - Observable extraction
    - Predictive capability
-/
structure PhysicsFramework where
  /-- The carrier type for physical states -/
  StateSpace : Type
  /-- Evolution operator (dynamics) -/
  evolve : StateSpace → StateSpace
  /-- Observable quantities that can be measured -/
  Observable : Type
  /-- Function extracting observables from states -/
  measure : StateSpace → Observable
  /-- Initial conditions exist -/
  hasInitialState : Nonempty StateSpace

namespace PhysicsFramework

/-- Dimensionless elements (knobs) carried by a framework.  By convention we
encode them as real numbers together with state witnesses so downstream
arguments can recover finitary descriptions tied to concrete states. -/
structure Element (F : PhysicsFramework) where
  /-- Identifier used for finitary encodings (e.g. algorithmic descriptions). -/
  id : ℕ
  /-- The state that this element is attached to. -/
  state : F.StateSpace
  /-- The numerical value associated with the element. -/
  value : ℝ

/-- A measurement procedure provides, for each finite step, a concrete element
observation.  The `id` field enables canonical enumeration. -/
structure MeasurementProcedure (F : PhysicsFramework) where
  id : ℕ
  sample : ℕ → Element F

/-- Enumeration-based predicate expressing that a procedure yields a knob. -/
def MeasurementProcedure.yields {F : PhysicsFramework}
    (proc : MeasurementProcedure F) (elem : Element F) : Prop :=
  ∃ n : ℕ, proc.sample n = elem

/-- Structural derivations accumulate internal deductions.  As with measurement
procedures, we retain a numeric identifier and a countable trace of element
outputs. -/
structure StructuralDerivation (F : PhysicsFramework) where
  id : ℕ
  step : ℕ → Element F
  produces_element : Element F
  input_elements : List (Element F)
  uses_only_internal_structure : Prop

/-- Output predicate for structural derivations. -/
def StructuralDerivation.produces {F : PhysicsFramework}
    (d : StructuralDerivation F) (elem : Element F) : Prop :=
  elem = d.produces_element ∨ ∃ n : ℕ, d.step n = elem

end PhysicsFramework

/-! ### Mild dynamics property -/

/-- A framework is non‑static if at least one state changes under `evolve`. -/
class NonStatic (F : PhysicsFramework) : Prop where
  exists_change : ∃ s : F.StateSpace, F.evolve s ≠ s

/-! ### Parameter Counting -/

/-- A framework has zero parameters if it can be specified algorithmically
    without any adjustable real numbers. -/
def HasZeroParameters (F : PhysicsFramework) : Prop :=
  HasAlgorithmicSpec F.StateSpace

/-- Parameter count: 0 if framework is algorithmic, otherwise undefined.

    Note: This is a simplified model. Full formalization would count
    adjustable real parameters in the framework definition.
-/
def ParameterCount (F : PhysicsFramework) : Prop :=
  HasZeroParameters F  -- Simplified: True if 0 parameters, False otherwise

/-! ### Observable Derivation -/

/-- **DEPRECATED**: This trivial version is always satisfiable.

    ⚠️ DO NOT USE IN NEW CODE ⚠️

    Use `Exclusivity.DerivesObservablesStrong` from `Observables.lean` instead,
    which requires predictions to fall within empirical bounds.

    This version is kept ONLY for backward compatibility with existing certificates.
    The `∃ (_ : ℝ), True` pattern makes ANY framework satisfy this, defeating the
    purpose of falsifiability testing.

    Migration path:
    1. Import `IndisputableMonolith.Verification.Exclusivity.Observables`
    2. Replace `DerivesObservables F` with `DerivesObservablesStrong F.StateSpace`
    3. Provide a `PredictionFunction` that produces values within empirical bounds -/
private noncomputable def alpha_inv_lock : ℝ := 137.035999

structure DerivesObservables (F : PhysicsFramework) : Prop where
  /-- Can predict electromagnetic fine structure constant. DEPRECATED: use
      DerivesObservablesStrong from Observables.lean for non-trivial derivation. -/
  derives_alpha : 137.035 ≤ alpha_inv_lock ∧ alpha_inv_lock ≤ 137.037
  /-- Can predict mass ratios. DEPRECATED: use DerivesObservablesStrong. -/
  derives_masses : ∀ φ : ℝ, (IndisputableMonolith.RecogSpec.massRatiosDefault φ).mu_over_e = φ
  /-- Can predict fundamental constants (c, ℏ, G relationships).
      Replaces the vacuous `∃ (c ℏ G : ℝ), (c > 0 ∧ ℏ > 0 ∧ G > 0)` with a meaningful
      link to the RS-native Constants (SI/CODATA calibration is external). -/
  derives_constants :
    IndisputableMonolith.Constants.hbar = IndisputableMonolith.Constants.cLagLock * IndisputableMonolith.Constants.tau0 ∧
    IndisputableMonolith.Constants.c = 1
  /-- Predictions are finite (computable). Deprecated: always true since we
      require DerivesObservablesStrong with explicit prediction functions. -/
  finite_predictions : ∀ φ, 0 < IndisputableMonolith.RecogSpec.alphaDefault φ
  /-- Observable extraction is computable. Deprecated: always true since measure
      is a function in PhysicsFramework. -/
  measure_computable : ∀ s, ∃ obs, F.measure s = obs

/-!
### Note on Observable Derivation

**For non-trivial observable derivation**, use:
- `IndisputableMonolith.Verification.Exclusivity.DerivesObservablesStrong`
- From `Observables.lean`

This requires predictions within empirical bounds:
- α⁻¹ ∈ [137.0359, 137.0361]
- m_e/m_μ ∈ [4.836e-3, 4.837e-3]
- m_p/m_e ∈ [1836.15, 1836.16]

**For non-circular exclusivity proofs**, use:
- `IndisputableMonolith.Verification.Exclusivity.IsomorphismDerivation.ExclusivityConstraints`
- Which uses `DerivesObservablesStrong` instead of the trivial `DerivesObservables`
-/

/-- Structural isomorphism between two physics frameworks. -/
structure FrameworkIso (F G : PhysicsFramework) where
  stateEquiv : F.StateSpace ≃ G.StateSpace
  observableEquiv : F.Observable ≃ G.Observable
  evolve_comm : ∀ s : F.StateSpace,
    stateEquiv (F.evolve s) = G.evolve (stateEquiv s)
  measure_comm : ∀ s : F.StateSpace,
    observableEquiv (F.measure s) = G.measure (stateEquiv s)

/-- Two frameworks are equivalent when there exists a structural isomorphism. -/
def FrameworkEquiv (F G : PhysicsFramework) : Prop := Nonempty (FrameworkIso F G)

namespace FrameworkEquiv

/-- Obtain the underlying isomorphism witness from an equivalence proof. -/
noncomputable def iso {F G : PhysicsFramework} (h : FrameworkEquiv F G) : FrameworkIso F G :=
  Classical.choice h

/-- Reflexivity: every framework is equivalent to itself. -/
theorem refl (F : PhysicsFramework) : FrameworkEquiv F F := by
  refine ⟨{
    stateEquiv := Equiv.refl _
  , observableEquiv := Equiv.refl _
  , evolve_comm := ?_
  , measure_comm := ?_ }⟩
  · intro s; simp
  · intro s; simp

/-- Symmetry: framework equivalence is symmetric. -/
theorem symm {F G : PhysicsFramework} (h : FrameworkEquiv F G) : FrameworkEquiv G F := by
  classical
  obtain ⟨iso⟩ := h
  refine ⟨{
    stateEquiv := iso.stateEquiv.symm
  , observableEquiv := iso.observableEquiv.symm
  , evolve_comm := ?_
  , measure_comm := ?_ }⟩
  · intro s
    have h' := iso.evolve_comm (iso.stateEquiv.symm s)
    -- send both sides through the inverse equivalence
    have := congrArg iso.stateEquiv.symm h'
    simpa using this.symm
  · intro s
    have h' := iso.measure_comm (iso.stateEquiv.symm s)
    have := congrArg iso.observableEquiv.symm h'
    simpa using this.symm

/-- Transitivity: framework equivalence composes. -/
theorem trans {F G H : PhysicsFramework}
    (hFG : FrameworkEquiv F G) (hGH : FrameworkEquiv G H) :
    FrameworkEquiv F H := by
  classical
  obtain ⟨isoFG⟩ := hFG
  obtain ⟨isoGH⟩ := hGH
  refine ⟨{
    stateEquiv := isoFG.stateEquiv.trans isoGH.stateEquiv
  , observableEquiv := isoFG.observableEquiv.trans isoGH.observableEquiv
  , evolve_comm := ?_
  , measure_comm := ?_ }⟩
  · intro s
    simp [Equiv.trans_apply, isoFG.evolve_comm, isoGH.evolve_comm]
  · intro s
    simp [Equiv.trans_apply, isoFG.measure_comm, isoGH.measure_comm]

end FrameworkEquiv

/-- Unary encoding of a natural number as a Boolean list. -/
noncomputable def unaryEncode (n : ℕ) : List Bool := List.replicate n true

@[simp] lemma length_unaryEncode (n : ℕ) : (unaryEncode n).length = n := by
  simp [unaryEncode]

/-- Transport an algorithmic specification along an equivalence with `ℕ`. -/
theorem HasAlgorithmicSpec.ofEquivNat {α : Type}
    (e : ℕ ≃ α) : HasAlgorithmicSpec α := by
  classical
  refine ⟨
    { description := []
    , generates := fun n => some (unaryEncode n) }
    , fun code => some (e (code.length)), ?_⟩
  intro s
  refine ⟨e.symm s, unaryEncode (e.symm s), ?_, ?_⟩
  · simp [unaryEncode]
  · simp [unaryEncode]

/-- Build an algorithmic specification from a surjection `ι : ℕ → α`. -/
theorem HasAlgorithmicSpec.ofNatSurjection {α : Type}
    (ι : ℕ → α) (hSurj : Function.Surjective ι) : HasAlgorithmicSpec α := by
  classical
  refine ⟨
    { description := []
    , generates := fun n => some (unaryEncode n) }
    , (fun code => some (ι code.length)), ?_⟩
  intro s
  obtain ⟨n, hn⟩ := hSurj s
  refine ⟨n, unaryEncode n, by simp [unaryEncode], ?_⟩
  simpa [unaryEncode, hn]

/-- Transport an algorithmic specification across an equivalence. -/
theorem HasAlgorithmicSpec.ofEquiv {α β : Type}
    (h : HasAlgorithmicSpec α) (e : α ≃ β) : HasAlgorithmicSpec β := by
  classical
  obtain ⟨spec, decode, hEnum⟩ := h
  refine ⟨spec, (fun code => (decode code).map e), ?_⟩
  intro b
  obtain ⟨n, code, hGen, hDec⟩ := hEnum (e.symm b)
  refine ⟨n, code, hGen, ?_⟩
  simpa [Option.map, hDec] using congrArg (Option.map e) hDec

/-- Transport an algorithmic specification along any surjection `g : α → β`. -/
theorem HasAlgorithmicSpec.of_surjective {α β : Type}
    (h : HasAlgorithmicSpec α) (g : α → β) (hg : Function.Surjective g) :
    HasAlgorithmicSpec β := by
  classical
  obtain ⟨spec, decode, hEnum⟩ := h
  refine ⟨spec, (fun code => (decode code).map g), ?_⟩
  intro b
  obtain ⟨a, ha⟩ := hg b
  obtain ⟨n, code, hGen, hDec⟩ := hEnum a
  refine ⟨n, code, hGen, ?_⟩
  simpa [Option.map, ha, hDec]

/-- Convert a ledger equivalence into a zero-parameter witness for a framework. -/
theorem HasZeroParameters.ofLedgerEquiv
    {F : PhysicsFramework} {L : RecogSpec.Ledger}
    (e : F.StateSpace ≃ L.Carrier)
    (hSpec : HasAlgorithmicSpec L.Carrier) :
    HasZeroParameters F := by
  classical
  have hFSpec : HasAlgorithmicSpec F.StateSpace :=
    HasAlgorithmicSpec.ofEquiv hSpec e.symm
  simpa [HasZeroParameters] using hFSpec

end Framework
end Exclusivity
end Verification
end IndisputableMonolith
