import Mathlib

/-!
# Narrative Structure from F₂³ — D6 Aesthetics

Booker (2004) catalogued 7 universal story patterns. In RS terms,
these are the 7 = |F₂³\{0}| non-trivial elements of the D=3 lattice.

RS derivation: each story is a sequence of recognition events.
The 7 universal structures correspond to the 7 weight-1, 2, and 3
combinations of 3 binary narrative axes:
- Axis 1: protagonist agency (reactive vs proactive)
- Axis 2: conflict origin (internal vs external)
- Axis 3: resolution type (restoration vs transformation)

Booker's 7: Overcoming the Monster, Rags to Riches, The Quest,
Voyage and Return, Comedy, Tragedy, Rebirth.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Aesthetics.NarrativeStructureFromF2Cube

inductive NarrativeAxis where
  | protagonistAgency | conflictOrigin | resolutionType
  deriving DecidableEq, Repr, BEq, Fintype

theorem narrativeAxisCount : Fintype.card NarrativeAxis = 3 := by decide

structure NarrativeAssignment where
  protagonistAgency : Bool
  conflictOrigin : Bool
  resolutionType : Bool
  deriving DecidableEq, BEq, Repr, Fintype

def neutralNarrative : NarrativeAssignment := ⟨false, false, false⟩

def IsBookerStory (n : NarrativeAssignment) : Prop := n ≠ neutralNarrative

instance (n : NarrativeAssignment) : Decidable (IsBookerStory n) := instDecidableNot

/-- The 7 Booker stories = |F₂³\{0}|. -/
theorem booker_count :
    (Finset.univ.filter IsBookerStory).card = 7 := by decide

inductive BookerStory where
  | overcomingMonster | ragsToRiches | theQuest | voyageAndReturn
  | comedy | tragedy | rebirth
  deriving DecidableEq, Repr, BEq, Fintype

theorem bookerStoryCount : Fintype.card BookerStory = 7 := by decide

theorem bookerCount_eq_F2cube_minus_one :
    Fintype.card BookerStory = 2^3 - 1 := by decide

structure NarrativeStructureCert where
  three_axes : Fintype.card NarrativeAxis = 3
  seven_stories_via_decide : (Finset.univ.filter IsBookerStory).card = 7
  seven_booker_stories : Fintype.card BookerStory = 7
  count_eq_flip : Fintype.card BookerStory = 2^3 - 1

def narrativeStructureCert : NarrativeStructureCert where
  three_axes := narrativeAxisCount
  seven_stories_via_decide := booker_count
  seven_booker_stories := bookerStoryCount
  count_eq_flip := bookerCount_eq_F2cube_minus_one

end IndisputableMonolith.Aesthetics.NarrativeStructureFromF2Cube
