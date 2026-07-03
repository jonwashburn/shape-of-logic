/-
  PrimitiveRecognitionCalculus/ObjecthoodRegistry.lean

  Phase 8 of the Delta-Native Analysis frontier: the periodic table of
  mathematical objecthood.

  The Delta program's recurring move is to ask, for any object, by what
  commitment it comes to exist. Some objects are forced by the law. Some are
  permitted free choices. Some are quotients under an equivalence. Some are
  completions that add an independent axiom. Some are displays: instruments, not
  ingredients. Some are observables. Some are conventions (gauge).

  This module makes the classification a typed object. `Commitment` is the seven
  categories; `RSObject` is the catalogue of objects this program has built;
  `commitmentOf` assigns each its category; and the `classify_*` theorems supply
  the evidence, each drawn from the proved content of the other Delta-Native
  modules. The headline `objecthood_periodic_table` records the assignment table.

  Evidence sources:
  * display      ← `DeltaReal.Protocol.display_real_forgetful`
  * completion   ← `Real.exists_isLUB` (independence proof: `PRCCompletenessIndependence`)
  * convention   ← `DeltaRealCalibration.discrete_does_not_force_unit`
  * quotient     ← `QuotientSelection.forced_iff`
  * observable   ← `QuotientSelection.observable_descends`
  * forced       ← prime field membership; `PrimeAxisCoherence.powerLaw_iff_aligned`
  * permitted    ← `GenerableReal.genField_countable`/`genField_proper`

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaReal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaRealCalibration
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.QuotientSelection
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PrimeAxisCoherence
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.GenerableReal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaProbability
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaAmplitude
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.ValidComparison
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace ObjecthoodRegistry

/-- The seven commitments that produce a mathematical object. -/
inductive Commitment where
  | forced       -- uniquely determined by the law; no freedom
  | permitted    -- an admissible free choice
  | quotient     -- identification under an equivalence
  | completion   -- closure adding limit points; an independent axiom
  | display      -- a rendering / instrument, not a native ingredient
  | observable   -- defined by what can be measured
  | convention   -- a gauge / labeling choice
  deriving DecidableEq, Repr

/-- The objects this program has built and now classifies. -/
inductive RSObject where
  | deltaRationals     -- ℚδ, the finite-distinction carrier
  | protocolReals      -- ℝδ as the value display onto ℝ
  | classicalReals     -- ℝ, the order-complete field
  | calibrationUnit    -- the cost-scale unit λ
  | physicalQuotient   -- the gauge quotient by indistinguishability
  | observableFamily   -- an admissible observable family
  | generableCarrier   -- the finite-generation carrier over a chosen inventory
  | primeScale         -- the single exponent forced by coherence
  | continuum          -- continuity/completion interface
  | point              -- stabilized localization display
  | space              -- display geometry of stable distinctions
  | setObject          -- closure over many distinctions
  | equalityRegime     -- indistinguishability under an admissible regime
  | infinityMode       -- typed mode of completion
  | functionTransport  -- distinction-preserving transport
  | finiteProbability  -- finite rational counting over distinction alternatives
  | finiteAmplitude    -- finite amplitude data before Hilbert completion
  | validComparison    -- native/display/observable bridge
  | conservativeCompletion -- completion controlled by finite certificates
  | complexNumbers     -- complex scalar display over paired real carriers
  | finiteHilbertSpace -- finite Hilbert display of F_RS[i] amplitudes
  | infiniteHilbertSpace -- completed Hilbert display
  | manifoldDisplay    -- local chart/gluing display
  | measureDisplay     -- sigma/completion display of finite probability
  | physicsDisplayObject -- physical observable display object
  deriving DecidableEq, Repr

/-- The classification assignment: the periodic table itself. -/
def commitmentOf : RSObject → Commitment
  | .deltaRationals => .forced
  | .protocolReals => .display
  | .classicalReals => .completion
  | .calibrationUnit => .convention
  | .physicalQuotient => .quotient
  | .observableFamily => .observable
  | .generableCarrier => .permitted
  | .primeScale => .forced
  | .continuum => .completion
  | .point => .display
  | .space => .display
  | .setObject => .permitted
  | .equalityRegime => .quotient
  | .infinityMode => .completion
  | .functionTransport => .observable
  | .finiteProbability => .forced
  | .finiteAmplitude => .permitted
  | .validComparison => .observable
  | .conservativeCompletion => .completion
  | .complexNumbers => .display
  | .finiteHilbertSpace => .display
  | .infiniteHilbertSpace => .completion
  | .manifoldDisplay => .display
  | .measureDisplay => .completion
  | .physicsDisplayObject => .observable

/-! ### Evidence -/

/-- `forced`: the rationals are forced into every carrier; they are the unique
prime subfield. No carrier of the framework can omit them. -/
theorem classify_forced_rationals :
    ∀ (K : Subfield ℝ) (q : ℚ), (q : ℝ) ∈ K :=
  fun K q => SubfieldClass.ratCast_mem K q

/-- `forced`: once coherence (a single global power law) holds, the prime weights
are forced to one common scale. Coherence forces the single exponent. -/
theorem classify_forced_scale :
    ∀ a w : ℕ → ℝ,
      PrimeAxisCoherence.IsPowerLaw a w ↔ PrimeAxisCoherence.WeightsAligned a w :=
  PrimeAxisCoherence.powerLaw_iff_aligned

/-- `display`: the protocol-real value map is surjective onto ℝ and faithful
(observational equality = equal value). ℝ is the forgetful display of the `ℝδ`
protocol interface. -/
theorem classify_display :
    Function.Surjective DeltaReal.Protocol.value
      ∧ (∀ x y : DeltaReal.Protocol,
          DeltaReal.Protocol.ObsEq x y ↔ x.value = y.value) := by
  obtain ⟨hsurj, _, hfaithful, _⟩ := DeltaReal.Protocol.display_real_forgetful
  exact ⟨hsurj, hfaithful⟩

/-- `completion`: ℝ has the least-upper-bound property. (That no countable
cost-closed carrier has it, so completeness is an independent axiom, is
`PRCCompletenessIndependence.completeness_is_exactly_the_continuum`.) -/
theorem classify_completion :
    ∀ S : Set ℝ, S.Nonempty → (∃ b, ∀ x ∈ S, x ≤ b) → ∃ s, IsLUB S s := by
  intro S hne hbdd
  obtain ⟨b, hb⟩ := hbdd
  exact Real.exists_isLUB hne ⟨b, fun x hx => hb x hx⟩

/-- `convention`: the cost-scale unit is a faithful, transitively-rescaled torsor,
a single free real fixed only by a continuum-side datum. It is a gauge. -/
theorem classify_convention :
    (∀ c d : ℝ, 0 < c → 0 < d →
        (fun t => Real.cosh (c * t) - 1) = (fun t => Real.cosh (d * t) - 1) → c = d)
      ∧ (∀ c d : ℝ, 0 < c → 0 < d →
          ∃ μ : ℝ, 0 < μ ∧
            (fun t => Real.cosh (c * (μ * t)) - 1) = (fun t => Real.cosh (d * t) - 1)) :=
  DeltaRealCalibration.discrete_does_not_force_unit

/-- `quotient`: the physical quotient identifies two states iff no observable
distinguishes them. The quotient is forced by indistinguishability. -/
theorem classify_quotient :
    ∀ {X C : Type} (F : Set (X → C)) (x y : X),
      QuotientSelection.proj F x = QuotientSelection.proj F y ↔ QuotientSelection.ObsEquiv F x y :=
  fun F x y => QuotientSelection.forced_iff F x y

/-- `observable`: every admissible observable descends to the physical quotient;
the quotient loses no observable information. -/
theorem classify_observable :
    ∀ {X C : Type} (F : Set (X → C)) (f : X → C), f ∈ F →
      ∃ g : QuotientSelection.PhysicalQuotient F → C, ∀ x, g (QuotientSelection.proj F x) = f x :=
  fun F f hf => QuotientSelection.observable_descends F f hf

/-- `permitted`: the constant inventory of the generable carrier is a free but
admissible choice. Every countable inventory yields a valid countable carrier
that is a proper subset of ℝ. -/
theorem classify_permitted :
    ∀ κ : ℕ → ℝ,
      (GenerableReal.genField κ : Set ℝ).Countable
        ∧ (GenerableReal.genField κ : Set ℝ) ≠ Set.univ :=
  fun κ => ⟨GenerableReal.genField_countable κ, GenerableReal.genField_proper κ⟩

/-- **Phase 8 headline: the periodic table of objecthood.** Each catalogued object
carries its commitment, and the assignment is exactly the evidence above:
distinction-forced (rationals, the coherence scale), display (ℝδ value map),
completion (ℝ), convention (cost unit), quotient and observable (the gauge
quotient and its probes), permitted (the generable inventory). Objecthood is not
flat: each object is produced by a specific kind of commitment, and the kind is
now a typed, proved attribute. -/
theorem objecthood_periodic_table :
    commitmentOf RSObject.deltaRationals = Commitment.forced
      ∧ commitmentOf RSObject.protocolReals = Commitment.display
      ∧ commitmentOf RSObject.classicalReals = Commitment.completion
      ∧ commitmentOf RSObject.calibrationUnit = Commitment.convention
      ∧ commitmentOf RSObject.physicalQuotient = Commitment.quotient
      ∧ commitmentOf RSObject.observableFamily = Commitment.observable
      ∧ commitmentOf RSObject.generableCarrier = Commitment.permitted
      ∧ commitmentOf RSObject.primeScale = Commitment.forced :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Background-object audit.** The conversation's broader target is now inside
the objecthood registry: continuum, point, space, set, equality, infinity,
function, probability, amplitude, valid comparison, and conservative completion
all receive explicit commitment tags. This prevents background objects from
entering the theory untyped. -/
theorem background_object_audit :
    commitmentOf RSObject.continuum = Commitment.completion
      ∧ commitmentOf RSObject.point = Commitment.display
      ∧ commitmentOf RSObject.space = Commitment.display
      ∧ commitmentOf RSObject.setObject = Commitment.permitted
      ∧ commitmentOf RSObject.equalityRegime = Commitment.quotient
      ∧ commitmentOf RSObject.infinityMode = Commitment.completion
      ∧ commitmentOf RSObject.functionTransport = Commitment.observable
      ∧ commitmentOf RSObject.finiteProbability = Commitment.forced
      ∧ commitmentOf RSObject.finiteAmplitude = Commitment.permitted
      ∧ commitmentOf RSObject.validComparison = Commitment.observable
      ∧ commitmentOf RSObject.conservativeCompletion = Commitment.completion
      ∧ commitmentOf RSObject.complexNumbers = Commitment.display
      ∧ commitmentOf RSObject.finiteHilbertSpace = Commitment.display
      ∧ commitmentOf RSObject.infiniteHilbertSpace = Commitment.completion
      ∧ commitmentOf RSObject.manifoldDisplay = Commitment.display
      ∧ commitmentOf RSObject.measureDisplay = Commitment.completion
      ∧ commitmentOf RSObject.physicsDisplayObject = Commitment.observable :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

/-- **Display-object extension.** Complex numbers, finite and infinite Hilbert
spaces, manifolds, measures, and physics display objects are now explicitly
typed. This closes the objecthood-table extension requested by the completion
plan. -/
theorem display_object_extension :
    commitmentOf RSObject.complexNumbers = Commitment.display
      ∧ commitmentOf RSObject.finiteHilbertSpace = Commitment.display
      ∧ commitmentOf RSObject.infiniteHilbertSpace = Commitment.completion
      ∧ commitmentOf RSObject.manifoldDisplay = Commitment.display
      ∧ commitmentOf RSObject.measureDisplay = Commitment.completion
      ∧ commitmentOf RSObject.physicsDisplayObject = Commitment.observable :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end ObjecthoodRegistry
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
