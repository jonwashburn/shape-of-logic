import IndisputableMonolith.Foundation.CostFromDistinction
import IndisputableMonolith.Foundation.HierarchyForcing
import IndisputableMonolith.Foundation.HierarchyRealizationObstruction
import IndisputableMonolith.Foundation.PostingExtensivity
import IndisputableMonolith.Foundation.PublicSpine.SelectedClosureNecessity
import IndisputableMonolith.Foundation.PublicSpine.FreeJointRecognition
import IndisputableMonolith.Foundation.UnifiedForcingChain

/-!
# SeedComposeBridge — φ-spine gap 1 (seed compose → L₂ = L₀ + L₁)

Target (from `ClosureDischargeProbe`): prove that the level-2 orbit event is
the join of independent seed events whose sizes are the level observables
`L0`, `L1`, so recognition-work additivity under join yields `L2 = L0 + L1`.

## What is THEOREM here

1. Under the named Recognition package `SeedRecognitionWorkPostingModel`
   (UFC), the seed size law is forced:
   `levels 2 = levels 0 + levels 1`
   (`seed_recognition_work_forces_additive_levels`).
2. The only non-theorem field of that package needed for the size law, beyond
   recognition-work additivity (already a `CostFunction` axiom), is the
   **seed-compose identification** `levelEvent 2 = compose(levelEvent 0,
   levelEvent 1)` together with the level↔cost reading (`level_size_eq`).
3. Bare `ClosedObservableFramework` does **not** force additive scale posting
   (Bool-orbit obstruction, re-exported).
4. RCL / posting d'Alembert alone does **not** force the seed size law
   (packaging surfaces that assume `seed_post_additive` are recorded as such).

## WALL

No theorem in the monolith derives `seed_event_composes` for a general
hierarchy / COF orbit from earlier Recognition structure without taking that
identification (or the size law itself) as a field. The missing lemma is
stated precisely as `SeedEventComposeIdentificationOpen`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace SeedComposeBridge

open CostFromDistinction
open HierarchyForcing
open HierarchyRealizationObstruction
open PostingExtensivity
open SelectedClosureNecessity
open FreeJointRecognition
open ClosedFramework
open UnifiedForcingChain
open UnifiedForcingChain.SupportEvent

/-! ## Positive bridge: recognition-work package ⇒ additive levels -/

/-- **Seed-compose size law (THEOREM under Recognition seed posting).**

If hierarchy levels are recognition-work costs of representing events, the
level-2 event is the posting/join of the level-0 and level-1 seeds, and those
seeds are independent, then `L₂ = L₀ + L₁`.

This is the UFC theorem `canonical_seed_size_law_of_seed_recognition_work`,
re-exported at the PublicSpine gap surface. -/
theorem seed_recognition_work_forces_additive_levels
    (M : NontrivialMultilevelComposition)
    {Event : Type} [ConfigSpace Event]
    {κ : CostFunction Event}
    {levelEvent : ℕ → Event}
    {compose : Event → Event → Event}
    (model : SeedRecognitionWorkPostingModel M Event κ levelEvent compose) :
    M.levels canonical_seed_post_index = M.levels 0 + M.levels 1 :=
  (canonical_seed_size_law_of_seed_recognition_work M model).seed_size_law

/-- Same bridge via the additive seed-posting model (size additivity may be
assumed abstractly; recognition-work specializes it). -/
theorem additive_seed_posting_forces_additive_levels
    (M : NontrivialMultilevelComposition)
    {Event : Type}
    {levelEvent : ℕ → Event}
    {size : Event → ℝ}
    {compose : Event → Event → Event}
    (model : AdditiveSeedPostingModel M Event levelEvent size compose) :
    M.levels canonical_seed_post_index = M.levels 0 + M.levels 1 :=
  (canonical_seed_size_law_of_additive_posting_model M model).seed_size_law

/-- Unpack: the size-law proof uses exactly three content pieces —
level reading, seed compose, and recognition-work additivity on the seed pair. -/
theorem seed_compose_bridge_mechanics
    (M : NontrivialMultilevelComposition)
    {Event : Type} [ConfigSpace Event]
    (κ : CostFunction Event)
    (levelEvent : ℕ → Event)
    (compose : Event → Event → Event)
    (level_size_eq : ∀ k, M.levels k = κ.C (levelEvent k))
    (seed_event_composes :
      levelEvent canonical_seed_post_index =
        compose (levelEvent 0) (levelEvent 1))
    (seed_compose_eq_join :
      compose (levelEvent 0) (levelEvent 1) =
        ConfigSpace.join (levelEvent 0) (levelEvent 1))
    (seed_independent :
      ConfigSpace.Independent (levelEvent 0) (levelEvent 1)) :
    M.levels canonical_seed_post_index = M.levels 0 + M.levels 1 :=
  seed_recognition_work_forces_additive_levels M {
    level_size_eq := level_size_eq
    seed_event_composes := seed_event_composes
    seed_compose_eq_join := seed_compose_eq_join
    seed_independent := seed_independent
  }

/-- On the free event carrier, Recognition compatibility forces the seed
composition operation to be configuration-space join. This closes operation
selection; it does not identify a hierarchy's level-2 event with the seed
composition. -/
theorem seedRecognitionWorkPostingModel_of_recognitionCompatible
    {Atom : Type} [DecidableEq Atom]
    (M : NontrivialMultilevelComposition)
    (levelEvent : ℕ → FreeEvent Atom)
    (compose : FreeEvent Atom → FreeEvent Atom → FreeEvent Atom)
    (hcompat : RecognitionCompatible compose)
    (level_size_eq : ∀ k, M.levels k = freeCost.C (levelEvent k))
    (seed_event_composes :
      levelEvent canonical_seed_post_index =
        compose (levelEvent 0) (levelEvent 1))
    (seed_independent :
      ConfigSpace.Independent (levelEvent 0) (levelEvent 1)) :
    SeedRecognitionWorkPostingModel
      M (FreeEvent Atom) freeCost levelEvent compose where
  level_size_eq := level_size_eq
  seed_event_composes := seed_event_composes
  seed_compose_eq_join :=
    recognitionCompatible_eq_join
      compose hcompat (levelEvent 0) (levelEvent 1)
  seed_independent := seed_independent

/-- Phase-2 split: operation selection is theorem-backed on free supports,
while the orbit-level seed-event identification remains the open seam. -/
structure SeedComposeOpSelectionClosed : Prop where
  compatible_eq_join :
    ∀ {Atom : Type} [DecidableEq Atom]
      (op : FreeEvent Atom → FreeEvent Atom → FreeEvent Atom),
      RecognitionCompatible op →
        ∀ a b, op a b = ConfigSpace.join a b
  xor_fail : ¬ RecognitionCompatible (Atom := Two) (interp .xor)
  meet_fail : ¬ RecognitionCompatible (Atom := Two) (interp .meet)
  weak_law_insufficient :
    (∀ a b : FreeEvent Two,
        ConfigSpace.Independent a b →
          freeCost.C (interp .xor a b) = freeCost.C a + freeCost.C b) ∧
      ¬ RecognitionCompatible (Atom := Two) (interp .xor)

theorem seedComposeOpSelectionClosed_holds : SeedComposeOpSelectionClosed where
  compatible_eq_join := fun op h a b =>
    recognitionCompatible_eq_join op h a b
  xor_fail := xor_not_recognitionCompatible
  meet_fail := meet_not_recognitionCompatible
  weak_law_insufficient := xor_accepted_by_weak_law_fails_full

/-- Canonical support-event interpretation: seed compose holds by the
level-tagged support model, and the size law follows once levels read
support costs. -/
theorem canonical_support_seed_compose_holds :
    canonicalSeedLevelEvent canonical_seed_post_index =
      supportCompose (canonicalSeedLevelEvent 0) (canonicalSeedLevelEvent 1) :=
  canonicalSeedLevelEvent_seed_composes

theorem canonical_support_seed_forces_additive_levels
    (M : NontrivialMultilevelComposition)
    (level_size_eq :
      ∀ k, M.levels k = SupportEvent.supportCost.C (canonicalSeedLevelEvent k)) :
    M.levels canonical_seed_post_index = M.levels 0 + M.levels 1 :=
  seed_recognition_work_forces_additive_levels M
    (canonical_seed_recognition_work_model_of_support_events M level_size_eq)

/-! ## Negatives: what does NOT force the seed size law -/

/-- Bare closed-observable frameworks need not carry additive scale posting
(Bool orbit). Re-exported so this module owns the obstruction at the gap. -/
theorem bare_cof_does_not_force_additive_posting :
    ∃ (F : ClosedObservableFramework) (base : F.S),
      ¬ CarriesAdditiveScalePosting F base :=
  HierarchyRealizationObstruction.closedFramework_does_not_force_additive_posting

/-- `RCLSeedPostingSemantics` packages `seed_post_additive` as a field; the
"forces size law" theorem is therefore packaging, not a derivation of compose. -/
theorem rcl_seed_semantics_packages_additive
    (M : NontrivialMultilevelComposition)
    (sem : RCLSeedPostingSemantics M) :
    M.levels canonical_seed_post_index = M.levels 0 + M.levels 1 :=
  sem.seed_post_additive

/-- Posting d'Alembert is a real identity and does not by itself constrain
hierarchy level sizes. Recorded to block the misread that RCL alone yields
`L2 = L0 + L1`. -/
theorem posting_dalembert_identity (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    PostingPotential (x * y) + PostingPotential (x / y) =
      2 * PostingPotential x * PostingPotential y :=
  posting_dalembert x y hx hy

/-- Concrete witness: posting potentials of powers of 2 fail the naive
"level-2 potential = level-0 + level-1" reading that would mimic seed closure.
(`Π(4) = 17/8`, `Π(1)+Π(2) = 1 + 5/4 = 9/4`.) -/
theorem posting_potential_powers_miss_seed_additive :
    PostingPotential ((2 : ℝ) ^ 2) ≠
      PostingPotential ((2 : ℝ) ^ 0) + PostingPotential ((2 : ℝ) ^ 1) := by
  unfold PostingPotential Cost.Jcost
  norm_num

/-! ## Typed WALL: missing seed-compose identification -/

/-- **Missing lemma (precise).**

There is no theorem deriving, from Recognition structure that does not already
assume seed compose or the size law, that a hierarchy's level-2 representing
event equals the join of independent level-0 and level-1 seed events.

Content already available:
* `ConfigSpace.join` is binary and recognition-work cost is additive on
  independent joins (`recognition_work_posting_size_additive`);
* the canonical support-event *interpretation* sets level 2 to that join
  (`canonicalSeedLevelEvent_seed_composes`);
* under `SeedRecognitionWorkPostingModel`, the size law follows.

What remains OPEN: a Recognition-native forcing that an arbitrary scale
hierarchy / COF orbit *must* be read through such a seed-compose event
interpretation (rather than disclosing `seed_event_composes` or
`CarriesAdditiveScalePosting`). -/
structure SeedEventComposeIdentificationOpen : Prop where
  /-- Documentation marker: the identification lemma is not claimed. -/
  stated : True := trivial

/-- Wall binder for gap 1. -/
structure SeedComposeBridgeWall : Prop where
  /-- Free-support Recognition compatibility closes operation selection. -/
  op_selection_closed : SeedComposeOpSelectionClosed
  /-- Under seed recognition-work posting, additive levels are THEOREM. -/
  under_seed_model :
    ∀ (M : NontrivialMultilevelComposition)
      {Event : Type} [ConfigSpace Event]
      {κ : CostFunction Event}
      {levelEvent : ℕ → Event}
      {compose : Event → Event → Event},
      SeedRecognitionWorkPostingModel M Event κ levelEvent compose →
      M.levels canonical_seed_post_index = M.levels 0 + M.levels 1
  /-- Bare COF obstruction retained. -/
  cof_obstruction :
    ∃ (F : ClosedFramework.ClosedObservableFramework) (base : F.S),
      ¬ CarriesAdditiveScalePosting F base
  /-- Posting-potential powers witness that d'Alembert ≠ seed size law. -/
  dalembert_not_size_law :
    PostingPotential ((2 : ℝ) ^ 2) ≠
      PostingPotential ((2 : ℝ) ^ 0) + PostingPotential ((2 : ℝ) ^ 1)
  /-- Named OPEN: derive seed-event compose identification. -/
  compose_id_open : SeedEventComposeIdentificationOpen

theorem seedComposeBridgeWall_holds : SeedComposeBridgeWall where
  op_selection_closed := seedComposeOpSelectionClosed_holds
  under_seed_model := fun M _ _ _ _ _ model =>
    seed_recognition_work_forces_additive_levels M model
  cof_obstruction := bare_cof_does_not_force_additive_posting
  dalembert_not_size_law := posting_potential_powers_miss_seed_additive
  compose_id_open := {}

/-- Status tag for the parent session: gap 1 is a typed WALL on the
compose-identification step; the recognition-work half is closed. -/
def seedComposeStatus : String := "WALL"

end SeedComposeBridge
end PublicSpine
end Foundation
end IndisputableMonolith
