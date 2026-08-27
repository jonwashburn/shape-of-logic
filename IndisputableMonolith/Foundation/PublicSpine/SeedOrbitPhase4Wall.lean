import IndisputableMonolith.Foundation.PublicSpine.SeedComposeBridge

/-!
# SeedOrbitPhase4Wall: exact cost data does not identify the seed orbit

Recognition compatibility closes the binary operation on free finite events:
the operation is join. It still does not assign a hierarchy's level-2 event.

The paired readings below share one hierarchy, one Recognition-compatible
operation, independent seeds, exact level-to-cost readings at every index, and
the same cost at every index. Both also satisfy the additive level-2 cost image.
One assigns the seed join at level 2; the other assigns a distinct event of the
same cost. This is the Phase-4 typed wall.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace SeedOrbitPhase4Wall

open CostFromDistinction
open HierarchyForcing
open UnifiedForcingChain
open FreeJointRecognition

/-- Current honest lower package: exact cost reading, operation selection, and
seed independence. It contains no level-2 event identity. -/
structure SeedOrbitLowerData
    (M : NontrivialMultilevelComposition)
    {A : Type} [DecidableEq A]
    (op : FreeEvent A → FreeEvent A → FreeEvent A)
    (levelEvent : ℕ → FreeEvent A) : Prop where
  level_size_eq : ∀ k, M.levels k = freeCost.C (levelEvent k)
  recognition_compatible : RecognitionCompatible op
  seed_independent :
    ConfigSpace.Independent (levelEvent 0) (levelEvent 1)

/-- Negative-only stress premise. This cost image is not proposed as a
positive bridge premise. -/
def SeedCostImage
    {A : Type} [DecidableEq A]
    (levelEvent : ℕ → FreeEvent A) : Prop :=
  freeCost.C (levelEvent canonical_seed_post_index) =
    freeCost.C (levelEvent 0) + freeCost.C (levelEvent 1)

/-- Exact support condition needed to identify the second event on the free
carrier: both seeds survive and no atom is invented. -/
structure SeedOrbitSupportExact
    {A : Type} [DecidableEq A]
    (levelEvent : ℕ → FreeEvent A) : Prop where
  seed0_extensive :
    (levelEvent 0).support ⊆
      (levelEvent canonical_seed_post_index).support
  seed1_extensive :
    (levelEvent 1).support ⊆
      (levelEvent canonical_seed_post_index).support
  no_invention :
    (levelEvent canonical_seed_post_index).support ⊆
      (levelEvent 0).support ∪ (levelEvent 1).support

/-- The additive cost image identifies the cost of the selected composition,
not the event itself. -/
theorem costImage_eq_compose
    {A : Type} [DecidableEq A]
    {M : NontrivialMultilevelComposition}
    {op : FreeEvent A → FreeEvent A → FreeEvent A}
    {levelEvent : ℕ → FreeEvent A}
    (lower : SeedOrbitLowerData M op levelEvent)
    (hcost : SeedCostImage levelEvent) :
    freeCost.C (levelEvent canonical_seed_post_index) =
      freeCost.C (op (levelEvent 0) (levelEvent 1)) := by
  calc
    freeCost.C (levelEvent canonical_seed_post_index) =
        freeCost.C (levelEvent 0) + freeCost.C (levelEvent 1) := hcost
    _ = freeCost.C (op (levelEvent 0) (levelEvent 1)) :=
      (lower.recognition_compatible.1 _ _ lower.seed_independent).symm

abbrev Atom := Fin 3

def seed0 : FreeEvent Atom := ⟨{0}⟩
def seed1 : FreeEvent Atom := ⟨{1}⟩
def compose : FreeEvent Atom → FreeEvent Atom → FreeEvent Atom := interp .join
def joinEvent : FreeEvent Atom := compose seed0 seed1
def nonjoinEvent : FreeEvent Atom := ⟨{0, 2}⟩

/-- A positive hierarchy whose level-2 cost is 2 and every other level cost is
1. Both event readings below realize exactly these levels. -/
def levels (k : ℕ) : ℝ :=
  if k = canonical_seed_post_index then 2 else 1

def hierarchy : NontrivialMultilevelComposition where
  levels := levels
  levels_pos := by
    intro k
    simp only [levels]
    split <;> norm_num
  at_least_three := by
    norm_num [levels, canonical_seed_post_index]

/-- Intended reading: level 2 is the seed join. -/
def joinReading (k : ℕ) : FreeEvent Atom :=
  if k = canonical_seed_post_index then joinEvent
  else if k = 1 then seed1 else seed0

/-- Decoy reading: level 2 has the same cost but replaces atom 1 by atom 2. -/
def nonjoinReading (k : ℕ) : FreeEvent Atom :=
  if k = canonical_seed_post_index then nonjoinEvent
  else if k = 1 then seed1 else seed0

theorem compose_recognitionCompatible : RecognitionCompatible compose :=
  join_recognitionCompatible

theorem readings_agree_off_level_two
    (k : ℕ) (hk : k ≠ canonical_seed_post_index) :
    joinReading k = nonjoinReading k := by
  simp [joinReading, nonjoinReading, hk]

theorem readings_share_lower_seed_data :
    joinReading 0 = nonjoinReading 0 ∧
      joinReading 1 = nonjoinReading 1 := by
  norm_num [joinReading, nonjoinReading, canonical_seed_post_index]

theorem seed_independent :
    ConfigSpace.Independent seed0 seed1 := by
  change Disjoint seed0.support seed1.support
  decide

theorem nonjoinEvent_support_card : nonjoinEvent.support.card = 2 := by
  decide

theorem joinEvent_support_card : joinEvent.support.card = 2 := by
  decide

theorem nonjoinEvent_cost_eq_joinEvent_cost :
    freeCost.C nonjoinEvent = freeCost.C joinEvent := by
  norm_num [freeCost, nonjoinEvent_support_card, joinEvent_support_card]

theorem nonjoinEvent_ne_joinEvent : nonjoinEvent ≠ joinEvent := by
  intro h
  have hmem : (2 : Atom) ∈ nonjoinEvent.support := by
    simp [nonjoinEvent]
  rw [h] at hmem
  simp [joinEvent, compose, interp, seed0, seed1, ConfigSpace.join] at hmem

theorem joinReading_level_size_eq :
    ∀ k, hierarchy.levels k = freeCost.C (joinReading k) := by
  intro k
  by_cases h2 : k = canonical_seed_post_index
  · subst k
    norm_num [hierarchy, levels, joinReading, freeCost,
      joinEvent_support_card, canonical_seed_post_index]
  · by_cases h1 : k = 1
    · subst k
      norm_num [hierarchy, levels, joinReading, seed1, freeCost,
        canonical_seed_post_index]
    · simp [hierarchy, levels, joinReading, h2, h1, seed0, freeCost]

theorem nonjoinReading_level_size_eq :
    ∀ k, hierarchy.levels k = freeCost.C (nonjoinReading k) := by
  intro k
  by_cases h2 : k = canonical_seed_post_index
  · subst k
    norm_num [hierarchy, levels, nonjoinReading, freeCost,
      nonjoinEvent_support_card, canonical_seed_post_index]
  · by_cases h1 : k = 1
    · subst k
      norm_num [hierarchy, levels, nonjoinReading, seed1, freeCost,
        canonical_seed_post_index]
    · simp [hierarchy, levels, nonjoinReading, h2, h1, seed0, freeCost]

theorem readings_have_same_cost_at_every_index (k : ℕ) :
    freeCost.C (joinReading k) = freeCost.C (nonjoinReading k) := by
  calc
    freeCost.C (joinReading k) = hierarchy.levels k :=
      (joinReading_level_size_eq k).symm
    _ = freeCost.C (nonjoinReading k) :=
      nonjoinReading_level_size_eq k

theorem joinReading_seed_independent :
    ConfigSpace.Independent (joinReading 0) (joinReading 1) := by
  norm_num [joinReading, canonical_seed_post_index]
  exact seed_independent

theorem nonjoinReading_seed_independent :
    ConfigSpace.Independent (nonjoinReading 0) (nonjoinReading 1) := by
  norm_num [nonjoinReading, canonical_seed_post_index]
  exact seed_independent

theorem joinReading_additive_cost_image : SeedCostImage joinReading := by
  norm_num [SeedCostImage, joinReading, freeCost, joinEvent_support_card,
    seed0, seed1, canonical_seed_post_index]

theorem nonjoinReading_additive_cost_image : SeedCostImage nonjoinReading := by
  norm_num [SeedCostImage, nonjoinReading, freeCost,
    nonjoinEvent_support_card, seed0, seed1, canonical_seed_post_index]

theorem joinReading_lowerData :
    SeedOrbitLowerData hierarchy compose joinReading where
  level_size_eq := joinReading_level_size_eq
  recognition_compatible := compose_recognitionCompatible
  seed_independent := joinReading_seed_independent

theorem nonjoinReading_lowerData :
    SeedOrbitLowerData hierarchy compose nonjoinReading where
  level_size_eq := nonjoinReading_level_size_eq
  recognition_compatible := compose_recognitionCompatible
  seed_independent := nonjoinReading_seed_independent

theorem joinReading_seed_event_composes :
    joinReading canonical_seed_post_index =
      compose (joinReading 0) (joinReading 1) := by
  norm_num [joinReading, joinEvent, canonical_seed_post_index]

theorem nonjoinReading_not_seed_event_composes :
    nonjoinReading canonical_seed_post_index ≠
      compose (nonjoinReading 0) (nonjoinReading 1) := by
  norm_num [nonjoinReading, canonical_seed_post_index]
  exact nonjoinEvent_ne_joinEvent

theorem readings_disagree_at_level_two :
    joinReading canonical_seed_post_index ≠
      nonjoinReading canonical_seed_post_index := by
  norm_num [joinReading, nonjoinReading, canonical_seed_post_index]
  exact nonjoinEvent_ne_joinEvent.symm

/-- Phase-4 impossibility: exact level-cost reading, Recognition-compatible
compose, independent seeds, and even the exact additive level-2 cost image do
not force the level-2 event identity. -/
theorem exact_cost_reading_does_not_identify_seed_orbit :
    ¬ (∀ {A : Type} [DecidableEq A]
        (M : NontrivialMultilevelComposition)
        (op : FreeEvent A → FreeEvent A → FreeEvent A)
        (levelEvent : ℕ → FreeEvent A),
        SeedOrbitLowerData M op levelEvent →
        SeedCostImage levelEvent →
          levelEvent canonical_seed_post_index =
            op (levelEvent 0) (levelEvent 1)) := by
  intro h
  exact nonjoinReading_not_seed_event_composes
    (h hierarchy compose nonjoinReading nonjoinReading_lowerData
      nonjoinReading_additive_cost_image)

theorem freeEvent_eq_of_support_eq
    {A : Type} {a b : FreeEvent A}
    (h : a.support = b.support) : a = b := by
  cases a with
  | mk sa =>
    cases b with
    | mk sb =>
      exact congrArg FreeEvent.mk h

/-- On the free carrier, seed compose is equivalent to exact support
extensivity plus no-invention. This theorem identifies the required output of
any future generative orbit law; assuming `SeedOrbitSupportExact` would package
the target. -/
theorem seed_event_composes_iff_support_exact
    {A : Type} [DecidableEq A]
    (op : FreeEvent A → FreeEvent A → FreeEvent A)
    (levelEvent : ℕ → FreeEvent A)
    (hcompat : RecognitionCompatible op) :
    levelEvent canonical_seed_post_index =
        op (levelEvent 0) (levelEvent 1) ↔
      SeedOrbitSupportExact levelEvent := by
  constructor
  · intro heq
    have hsupport :
        (levelEvent canonical_seed_post_index).support =
          (levelEvent 0).support ∪ (levelEvent 1).support := by
      calc
        (levelEvent canonical_seed_post_index).support =
            (op (levelEvent 0) (levelEvent 1)).support :=
          congrArg FreeEvent.support heq
        _ = (levelEvent 0).support ∪ (levelEvent 1).support :=
          recognitionCompatible_support_eq_union op hcompat _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [hsupport]
      exact Finset.subset_union_left
    · rw [hsupport]
      exact Finset.subset_union_right
    · rw [hsupport]
  · intro hexact
    apply freeEvent_eq_of_support_eq
    have hlevel :
        (levelEvent canonical_seed_post_index).support =
          (levelEvent 0).support ∪ (levelEvent 1).support :=
      Finset.Subset.antisymm hexact.no_invention
        (Finset.union_subset
          hexact.seed0_extensive hexact.seed1_extensive)
    exact hlevel.trans
      (recognitionCompatible_support_eq_union op hcompat _ _).symm

/-- A future premise reopens this route only if it accepts the intended reading
and forces the exact support output from lower data. -/
def ReopensSeedOrbit
    (P : (ℕ → FreeEvent Atom) → Prop) : Prop :=
  P joinReading ∧
    ∀ levelEvent,
      SeedOrbitLowerData hierarchy compose levelEvent →
      P levelEvent →
      SeedOrbitSupportExact levelEvent

/-- Every premise meeting the reopen condition rejects the equal-cost
nonjoining reading. -/
theorem reopen_condition_rejects_same_cost_nonjoin
    {P : (ℕ → FreeEvent Atom) → Prop}
    (hP : ReopensSeedOrbit P) :
    ¬ P nonjoinReading := by
  intro hbad
  have hexact := hP.2 nonjoinReading nonjoinReading_lowerData hbad
  exact nonjoinReading_not_seed_event_composes
    ((seed_event_composes_iff_support_exact
      compose nonjoinReading compose_recognitionCompatible).2 hexact)

/-- Packaging audit: the canonical support interpretation composes by
definition. This is a model witness, not general orbit identification. -/
theorem canonical_support_seed_compose_is_definitional :
    canonicalSeedLevelEvent canonical_seed_post_index =
      supportCompose (canonicalSeedLevelEvent 0) (canonicalSeedLevelEvent 1) := by
  rfl

end SeedOrbitPhase4Wall
end PublicSpine
end Foundation
end IndisputableMonolith
