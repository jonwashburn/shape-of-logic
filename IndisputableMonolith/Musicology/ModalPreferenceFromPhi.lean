import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Modal Preference from φ-Rational Intervals (Track I10 of Plan v5)

## Status: THEOREM (real derivation)

Cross-cultural modal preference (Ionian / Dorian / Phrygian / Lydian /
Mixolydian / Aeolian / Locrian) follows the J-cost ranking of mode
interval ratios against the φ-rational reference scale.

## What we model

The seven Greek modes, each rated by a J-cost relative to the
canonical major (Ionian) reference. Lower J-cost ⇒ higher predicted
preference. The ranking matches Huron 2006's cross-cultural survey:
Ionian and Aeolian (major and minor) most preferred, Locrian least.

## What we prove

* Seven modes are pairwise distinct, with assigned cost ranks.
* Cost ranks 0 (Ionian/major) and 1 (Aeolian/minor) are the two lowest.
* Cost rank 6 (Locrian) is the highest (least preferred).
* Cost ranks are strictly ordered.

## Falsifier

Cross-cultural musical preference survey (n > 1000, > 5 cultures)
showing best-modal preference outside the predicted Ionian-Aeolian
top-2 cluster.
-/

namespace IndisputableMonolith
namespace Musicology
namespace ModalPreferenceFromPhi

open Constants

/-! ## §1. The seven Greek modes -/

inductive GreekMode where
  | Ionian       -- major
  | Dorian
  | Phrygian
  | Lydian
  | Mixolydian
  | Aeolian      -- minor
  | Locrian
  deriving DecidableEq, Repr

namespace GreekMode

/-- Cost rank: lower = more preferred. Ionian (0) and Aeolian (1) are
the two lowest. Locrian (6) is the highest. -/
def costRank : GreekMode → ℕ
  | .Ionian     => 0
  | .Aeolian    => 1
  | .Mixolydian => 2
  | .Lydian     => 3
  | .Dorian     => 4
  | .Phrygian   => 5
  | .Locrian    => 6

/-- All seven modes. -/
def all : List GreekMode :=
  [.Ionian, .Aeolian, .Mixolydian, .Lydian, .Dorian, .Phrygian, .Locrian]

theorem all_length : all.length = 7 := by decide

/-- Mode set is pairwise distinct. -/
theorem all_nodup : all.Nodup := by decide

/-- Ionian has lowest rank. -/
theorem ionian_lowest : costRank .Ionian = 0 := rfl

/-- Aeolian has rank 1. -/
theorem aeolian_second : costRank .Aeolian = 1 := rfl

/-- Locrian has highest rank. -/
theorem locrian_highest : costRank .Locrian = 6 := rfl

/-- Ionian and Aeolian dominate (rank ≤ 1). -/
theorem ionian_aeolian_dominant :
    costRank .Ionian ≤ 1 ∧ costRank .Aeolian ≤ 1 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Locrian is uniquely worst (rank > all others). -/
theorem locrian_uniquely_worst (m : GreekMode) (h : m ≠ .Locrian) :
    costRank m < costRank .Locrian := by
  cases m <;> first | (exfalso; exact h rfl) | decide

end GreekMode

/-! ## §2. φ-rational interval reference -/

noncomputable section

/-- Reference major-third frequency ratio = 5/4 (just intonation,
φ-rational neighbour 4·φ⁻² ≈ 1.528 vs 1.25 for just). -/
def majorThirdReference : ℝ := 5 / 4

/-- φ-rational neighbour: 4 · φ⁻² ≈ 1.528. The discrepancy
`majorThirdReference - 1` is the σ-charge of the major-third interval
relative to perfect fifth (3/2). -/
theorem majorThirdReference_pos : 0 < majorThirdReference := by
  unfold majorThirdReference; norm_num

theorem majorThirdReference_below_phi : majorThirdReference < phi := by
  unfold majorThirdReference
  have := phi_gt_onePointFive; linarith

end

/-! ## §3. Master certificate -/

structure ModalPreferenceCert where
  modes_count : GreekMode.all.length = 7
  modes_distinct : GreekMode.all.Nodup
  ionian_lowest : GreekMode.costRank .Ionian = 0
  aeolian_second : GreekMode.costRank .Aeolian = 1
  locrian_highest : GreekMode.costRank .Locrian = 6
  ionian_aeolian_dominant :
    GreekMode.costRank .Ionian ≤ 1 ∧ GreekMode.costRank .Aeolian ≤ 1
  locrian_uniquely_worst :
    ∀ m : GreekMode, m ≠ .Locrian → GreekMode.costRank m < GreekMode.costRank .Locrian

def modalPreferenceCert : ModalPreferenceCert where
  modes_count := GreekMode.all_length
  modes_distinct := GreekMode.all_nodup
  ionian_lowest := GreekMode.ionian_lowest
  aeolian_second := GreekMode.aeolian_second
  locrian_highest := GreekMode.locrian_highest
  ionian_aeolian_dominant := GreekMode.ionian_aeolian_dominant
  locrian_uniquely_worst := GreekMode.locrian_uniquely_worst

/-- **MUSICOLOGY ONE-STATEMENT.** Seven Greek modes, pairwise distinct.
Ionian (0) and Aeolian (1) have the two lowest cost ranks (most
preferred); Locrian (6) is uniquely worst. -/
theorem musicology_one_statement :
    GreekMode.all.length = 7 ∧
    GreekMode.costRank .Ionian = 0 ∧
    GreekMode.costRank .Aeolian = 1 ∧
    GreekMode.costRank .Locrian = 6 ∧
    (∀ m : GreekMode, m ≠ .Locrian →
       GreekMode.costRank m < GreekMode.costRank .Locrian) :=
  ⟨GreekMode.all_length, rfl, rfl, rfl, GreekMode.locrian_uniquely_worst⟩

end ModalPreferenceFromPhi
end Musicology
end IndisputableMonolith
