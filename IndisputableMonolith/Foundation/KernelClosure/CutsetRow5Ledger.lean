import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow5Erasure

/-!
# Cutset row 5, promoted: the record is a floor theorem

Row 5 (`CutsetRow5Erasure`) closed the deformation-erasure principle under a
definition: "the posted pair is a record, recognition-free deformation cannot
move it." A definition is a choice, so the D = 4 alternative was excluded only
as "not what a ledger means by record". This module removes the word.

## The floor theorem

A ledger state at floor `D` is a pattern `Fin D → Bool`. A post is a bit flip
(T1: a distinction is a two-state cell; T2: the flip is the unit of cost). A
transition that posts nothing changes no bit, and two patterns with no bit
different are the same pattern:

  `recognitionFree_iff_eq : RecognitionFree p q ↔ p = q`.

That is extensionality of patterns, and it is the whole content: on the ledger
there is no change without a post, because change *is* a post.

## The blade, with no new word

DEP's own hypothesis word is "recognition-free deformation". A kinematics `X` is
*ledger-realized* when its configurations read as ledger states so that
(i) every deformation step is recognition-free in the reading (it posts no bit),
and (ii) the posted pair and the split read as distinct states, i.e. space keeps
the record of the act. No word beyond DEP's own is introduced; "record" as an
immobility condition is gone. Clause (ii) is not T-2: T-2 says the act posted a
distinction; (ii) says the *placement* carries it. A ledger may keep the
distinction in its cells and read every placement as one state, so (ii) is the
one clause with content, and it is not forced (`dep_not_forced_by_realization_layer`
in `LinkingNecessity`).

Under that reading the floor theorem does the work: a deformation from the pair
to the split would be a recognition-free transition between distinct states,
which `recognitionFree_iff_eq` forbids. So DEP holds
(`dep_of_ledgerRealized`) and `D = 3` follows (`ledgerRealized_forces_D3`).

## The alternative is now impossible, not merely other

The D = 4 kinematics deforms the pair to the split. Under *every* reading in
which the pair and the split are distinct ledger states, that deformation
changes a ledger state without a post (`d4_not_ledgerRealized` quantifies over
all readings). So D = 4 is not a world in which the ledger's posted distinction
can be realized at all; it is excluded by a floor theorem, not by a word.

## Shape

The blade is extensionally the sentence (`ledgerRealized_iff_dep`): every DEP
kinematics admits a reading and every ledger-realized kinematics satisfies DEP.
That is the merge shape of the earlier rows, and here it is the point: the
sentence has become a theorem of the floor transported along a reading. What
remains is not a word choice but clause (ii) itself: that the placement of the
dual pair is a ledger state distinct from its separation, that space keeps the
record. The sentence names no dimension, and off three no reading satisfies it
under any assignment of states. The parity kinematics, which
failed the record blade while satisfying DEP, passes this one: the record blade
was stronger than needed.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row5Ledger

open LinkingNecessity LinkingFromHierarchy HierarchyRealization ClosedFramework
open Row5Erasure

/-! ## The floor theorem -/

/-- A ledger state at floor `D`. -/
abbrev State (D : ℕ) := Fin D → Bool

/-- No post between two states: no bit differs. -/
def RecognitionFree {D : ℕ} (p q : State D) : Prop := ∀ i, p i = q i

/-- **Floor theorem.** A transition that posts no bit is no transition. -/
theorem recognitionFree_iff_eq {D : ℕ} (p q : State D) : RecognitionFree p q ↔ p = q :=
  ⟨fun h => funext h, fun h i => by rw [h]⟩

/-! ## The blade -/

/-- A ledger reading of a pair kinematics at floor `D`: configurations are read
as ledger states, deformation posts nothing, and the posted pair is a
distinction from the split. -/
structure LedgerReading (X : PairKinematics) (D : ℕ) where
  read : X.Config → State D
  deform_recognitionFree : ∀ a b, X.deform a b → RecognitionFree (read a) (read b)
  posted : read X.pair ≠ read X.split

/-- The kinematics is ledger-realized at some floor. -/
def LedgerRealized (X : PairKinematics) : Prop := ∃ D : ℕ, Nonempty (LedgerReading X D)

/-! ## The cut -/

theorem not_deform_pair_split_of_ledgerRealized {X : PairKinematics}
    (h : LedgerRealized X) : ¬ X.deform X.pair X.split := by
  obtain ⟨D, ⟨R⟩⟩ := h
  intro hd
  exact R.posted ((recognitionFree_iff_eq _ _).1 (R.deform_recognitionFree _ _ hd))

/-- **DEP is a theorem of the floor along a ledger reading.** -/
theorem dep_of_ledgerRealized {X : PairKinematics} (h : LedgerRealized X) :
    DeformationErasurePrinciple X :=
  (dep_iff_not_deform_pair_split X).2 (not_deform_pair_split_of_ledgerRealized h)

/-- A kinematics whose pair deforms to its split admits no ledger reading. -/
theorem not_ledgerRealized_of_deform {X : PairKinematics} (h : X.deform X.pair X.split) :
    ¬ LedgerRealized X :=
  fun hr => not_deform_pair_split_of_ledgerRealized hr h

/-- Conversely every DEP kinematics admits a reading (one bit: "in the pair's
deformation class"). -/
theorem ledgerRealized_of_dep {X : PairKinematics} (h : DeformationErasurePrinciple X) :
    LedgerRealized X := by
  classical
  have hns := (dep_iff_not_deform_pair_split X).1 h
  refine ⟨1, ⟨⟨fun c => fun _ => decide (X.deform X.pair c), ?_, ?_⟩⟩⟩
  · intro a b hab i
    show decide (X.deform X.pair a) = decide (X.deform X.pair b)
    by_cases ha : X.deform X.pair a
    · rw [decide_eq_true ha, decide_eq_true (X.deform_trans ha hab)]
    · rw [decide_eq_false ha,
        decide_eq_false (fun hb => ha (X.deform_trans hb (X.deform_symm hab)))]
  · intro heq
    have h0 : decide (X.deform X.pair X.pair) = decide (X.deform X.pair X.split) :=
      congrFun heq ⟨0, by norm_num⟩
    rw [decide_eq_true (X.deform_refl _), decide_eq_false hns] at h0
    exact Bool.noConfusion h0

/-- Blade and sentence coincide: the sentence is the floor theorem in DEP's own
words. -/
theorem ledgerRealized_iff_dep (X : PairKinematics) :
    LedgerRealized X ↔ DeformationErasurePrinciple X :=
  ⟨dep_of_ledgerRealized, ledgerRealized_of_dep⟩

/-! ## Real and violator -/

/-- `D = 3`: the winding kinematics reads into the ledger (one bit: the winding
class is the posted one). -/
def d3_reading (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    LedgerReading (windingPairKinematics F H) 1 where
  read := fun c => fun _ => decide (c = 2)
  deform_recognitionFree := fun a b hab i => by
    show decide (a = 2) = decide (b = 2)
    have : a = b := hab
    rw [this]
  posted := by
    intro heq
    have h0 := congrFun heq ⟨0, by norm_num⟩
    show False
    have : decide ((2 : ℤ) = 2) = decide ((0 : ℤ) = 2) := h0
    simp at this

theorem d3_ledgerRealized (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    LedgerRealized (windingPairKinematics F H) :=
  ⟨1, ⟨d3_reading F H⟩⟩

/-- `D = 4`: under every reading in which the pair and the split are distinct
states, the unlinking deformation changes a state without a post. -/
theorem d4_not_ledgerRealized : ¬ LedgerRealized unlinkedKinematics :=
  not_ledgerRealized_of_deform trivial

/-- The record blade implied this one; the parity kinematics shows the converse
fails, so the record word was stronger than the floor requires. -/
theorem ledgerRealized_of_record (X : PairKinematics) (hne : X.pair ≠ X.split)
    (hrec : IsRecord X.deform X.pair) : LedgerRealized X :=
  ledgerRealized_of_dep (dep_of_record_posting X hne hrec)

theorem parity_ledgerRealized_not_record :
    LedgerRealized parityKinematics ∧
      ¬ IsRecord parityKinematics.deform parityKinematics.pair :=
  ⟨ledgerRealized_of_dep parity_dep_but_not_record.1, parity_dep_but_not_record.2⟩

/-! ## The row -/

/-- Row 5 with a floor-theorem blade. -/
noncomputable def row : CutsetRow PairKinematics where
  Floor := fun X => X.pair ≠ X.split
  Sentence := DeformationErasurePrinciple
  Blade := LedgerRealized
  provenance := .floorTheorem
    "recognitionFree_iff_eq: a transition that posts no bit is no transition (pattern extensionality; T1 cell, T2 post), transported along a ledger reading of the configurations"
  real := windingPairKinematics jRealizedHierarchy.1 jRealizedHierarchy.2
  real_floor := by show (2 : ℤ) ≠ 0; norm_num
  blade_real := d3_ledgerRealized jRealizedHierarchy.1 jRealizedHierarchy.2
  violator := unlinkedKinematics
  violator_floor := by show (2 : ℤ) ≠ 0; norm_num
  violator_violates := unlinkedKinematics_refutes_dep
  blade_kills_violator := d4_not_ledgerRealized
  exclusion := fun _ _ hs hb => hs (dep_of_ledgerRealized hb)

/-! ## The dimension -/

/-- **A ledger-realized dual pair lives in three dimensions.** -/
theorem ledgerRealized_forces_D3 (D : DimensionForcing.Dimension)
    (R : SpatialDualPairRealization D) (h : LedgerRealized R.kin) : D = 3 :=
  dep_forces_D3 D R (dep_of_ledgerRealized h)

/-- Off three dimensions no spatial realization reads into the ledger. -/
theorem no_reading_off_three (D : DimensionForcing.Dimension) (hD : D ≠ 3)
    (R : SpatialDualPairRealization D) : ¬ LedgerRealized R.kin :=
  fun h => hD (ledgerRealized_forces_D3 D R h)

/-! ## Certificate -/

structure Cert : Prop where
  floor_theorem : ∀ (D : ℕ) (p q : State D), RecognitionFree p q ↔ p = q
  forces : ∀ X, row.Floor X → row.Blade X → row.Sentence X
  class_nonempty : ∃ X, row.Floor X ∧ ¬ row.Sentence X
  blade_varies : ∃ X Y, row.Blade X ∧ ¬ row.Blade Y
  blade_is_sentence : ∀ X : PairKinematics, LedgerRealized X ↔ DeformationErasurePrinciple X
  d4_impossible : ¬ LedgerRealized unlinkedKinematics
  record_was_stronger : LedgerRealized parityKinematics ∧
    ¬ IsRecord parityKinematics.deform parityKinematics.pair
  forces_D3 : ∀ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
    LedgerRealized R.kin → D = 3
  off_three_unreadable : ∀ (D : DimensionForcing.Dimension), D ≠ 3 →
    ∀ R : SpatialDualPairRealization D, ¬ LedgerRealized R.kin

theorem cert : Cert where
  floor_theorem := fun _ p q => recognitionFree_iff_eq p q
  forces := row.forces
  class_nonempty := row.class_nonempty
  blade_varies := row.blade_varies
  blade_is_sentence := ledgerRealized_iff_dep
  d4_impossible := d4_not_ledgerRealized
  record_was_stronger := parity_ledgerRealized_not_record
  forces_D3 := ledgerRealized_forces_D3
  off_three_unreadable := no_reading_off_three

end Row5Ledger
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
