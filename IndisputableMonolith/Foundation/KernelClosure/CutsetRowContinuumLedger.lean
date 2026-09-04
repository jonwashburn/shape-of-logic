import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetRowContinuum
import IndisputableMonolith.Foundation.FloorToT5Obstruction

/-!
# The continuum row, promoted: the alternative is not a distinct ledger object

`CutsetRowContinuum` closed the step from the rationals to the reals under a
definition: the cost of a ratio the floor does not post is what its floors read.
The wild cost was excluded by that word. This module asks what the alternative
*is* to the ledger, and finds that it is not an alternative.

## The floor has no continuum

The forced floor stops at the rationals: it has no log-positive-ratio
coordinates (`FloorToT5Obstruction.bool_floor_no_T5_continuum_coordinates`).
Every quantity the ledger posts is a count, and every ratio it compares is a
ratio of counts. A function `F : ℝ → ℝ` is therefore not a ledger object; the
ledger object is its restriction to the positive rationals. Two costs that agree
at every positive rational are the same ledger object
(`LedgerIndistinguishable`).

## Every alternative is impossible or is not an alternative

Let `F` be any candidate cost on the reals. Either

* `F` differs from `J` at some positive rational: then `F` is not a structural
  native cost, because every structural native cost is `J` at every positive
  rational with no continuity (`rationalNative_of_native`). This alternative
  breaks the count-side ledger and is impossible; or
* `F` agrees with `J` at every positive rational: then `F` and `J` are the same
  ledger object. Whatever `F` does at irrational arguments is not a ledger
  fact. The wild cost is of this kind (`wild_indistinguishable_from_jcost`).

So there is no third case (`alternative_dichotomy`): nothing the ledger can
post distinguishes an alternative from `J`.

## What floor readability then is

Among the presentations of the one ledger object on the reals, floor
readability selects exactly one (`unique_readable_extension`), and `J` is it
(`jcost_floorReadable`). It is a definition of the presentation, not a
constraint on the ledger, and the constraint it would have added is empty: no
count reading can see it. The definition remains (the harness row of
`CutsetRowContinuum` stands); what changes is the status of the alternative,
from "excluded by a word" to "not a distinct object of the theory".

Grade: on count ratios DERIVED (`deltaOnly`); on the reals the presentation is
MODEL and its alternatives are ledger-indistinguishable (THEOREM).

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace RowContinuumLedger

open Cost Cost.FunctionalEquation
open PrimitiveRecognitionCalculus PrimitiveRecognitionCalculus.PRCJCost
open RowContinuum

/-- Two costs are the same ledger object when they agree at every positive
count ratio. -/
def LedgerIndistinguishable (F G : ℝ → ℝ) : Prop :=
  ∀ t : ℚ, 0 < t → F (t : ℝ) = G (t : ℝ)

theorem ledgerIndistinguishable_refl (F : ℝ → ℝ) : LedgerIndistinguishable F F :=
  fun _ _ => rfl

theorem ledgerIndistinguishable_symm {F G : ℝ → ℝ} (h : LedgerIndistinguishable F G) :
    LedgerIndistinguishable G F :=
  fun t ht => (h t ht).symm

theorem ledgerIndistinguishable_trans {F G K : ℝ → ℝ} (h₁ : LedgerIndistinguishable F G)
    (h₂ : LedgerIndistinguishable G K) : LedgerIndistinguishable F K :=
  fun t ht => (h₁ t ht).trans (h₂ t ht)

/-- Rational-native is "the same ledger object as `J`". -/
theorem indistinguishable_of_rationalNative {F : ℝ → ℝ} (h : RationalNative F) :
    LedgerIndistinguishable F Jcost := h

/-- The wild cost is the same ledger object as `J`. -/
theorem wild_indistinguishable_from_jcost : LedgerIndistinguishable wildCost Jcost :=
  wildCost_rationalNative

/-- **Every alternative is impossible or is not an alternative.** -/
theorem alternative_dichotomy (F : ℝ → ℝ) :
    LedgerIndistinguishable F Jcost ∨ ∃ t : ℚ, 0 < t ∧ F (t : ℝ) ≠ Jcost (t : ℝ) := by
  classical
  by_cases h : ∀ t : ℚ, 0 < t → F (t : ℝ) = Jcost (t : ℝ)
  · exact Or.inl h
  · right
    push_neg at h
    exact h

/-- A cost that differs from `J` at a count ratio is not a structural native
cost: the first branch of the dichotomy is impossible for a ledger. -/
theorem not_native_of_differs {F : ℝ → ℝ} {t : ℚ} (ht : 0 < t)
    (hne : F (t : ℝ) ≠ Jcost (t : ℝ)) :
    ¬ ∃ G : RatioOrbit → RatioOrbit, PRCStructuralNativeCostHypotheses G ∧
      ∀ q : RatioOrbit, 0 < q.toRat → F ((q.toRat : ℚ) : ℝ) = (((G q).toRat : ℚ) : ℝ) := by
  rintro ⟨G, hG, hr⟩
  exact hne (rationalNative_of_native hG hr t ht)

/-- Among presentations of the one ledger object, floor readability selects
exactly one. -/
theorem unique_readable_extension {F G : ℝ → ℝ}
    (hFG : LedgerIndistinguishable F G)
    (hGJ : LedgerIndistinguishable G Jcost)
    (hF : FloorReadable F) (hG : FloorReadable G) :
    ∀ x : ℝ, 0 < x → F x = G x := by
  intro x hx
  have hFJ : RationalNative F := ledgerIndistinguishable_trans hFG hGJ
  rw [eq_jcost_of_floorReadable hFJ hF x hx, eq_jcost_of_floorReadable hGJ hG x hx]

/-- The floor has no continuum coordinates: a function on the reals is not a
floor object. Restated from `FloorToT5Obstruction`. -/
theorem floor_has_no_continuum :
    ¬ Nonempty (PositiveRatioBridgeStrict.LogPositiveRatioCoordinates
      (K := Bool) ⟨false, true, Bool.noConfusion⟩) :=
  FloorToT5Obstruction.bool_floor_no_T5_continuum_coordinates

/-! ## Certificate -/

structure Cert : Prop where
  /-- The floor stops at the rationals. -/
  no_continuum : ¬ Nonempty (PositiveRatioBridgeStrict.LogPositiveRatioCoordinates
    (K := Bool) ⟨false, true, Bool.noConfusion⟩)
  /-- Every candidate cost is the same ledger object as `J` or differs at a count. -/
  dichotomy : ∀ F : ℝ → ℝ,
    LedgerIndistinguishable F Jcost ∨ ∃ t : ℚ, 0 < t ∧ F (t : ℝ) ≠ Jcost (t : ℝ)
  /-- The second branch is not a ledger. -/
  differing_is_not_native : ∀ (F : ℝ → ℝ) (t : ℚ), 0 < t → F (t : ℝ) ≠ Jcost (t : ℝ) →
    ¬ ∃ G : RatioOrbit → RatioOrbit, PRCStructuralNativeCostHypotheses G ∧
      ∀ q : RatioOrbit, 0 < q.toRat → F ((q.toRat : ℚ) : ℝ) = (((G q).toRat : ℚ) : ℝ)
  /-- The wild cost is in the first branch: not a distinct ledger object. -/
  wild_is_jcost_to_the_ledger : LedgerIndistinguishable wildCost Jcost
  /-- Floor readability picks one presentation. -/
  unique_presentation : ∀ F G : ℝ → ℝ, LedgerIndistinguishable F G →
    LedgerIndistinguishable G Jcost → FloorReadable F → FloorReadable G →
    ∀ x : ℝ, 0 < x → F x = G x
  /-- And `J` is it. -/
  presentation_exists : FloorReadable Jcost

theorem cert : Cert where
  no_continuum := floor_has_no_continuum
  dichotomy := alternative_dichotomy
  differing_is_not_native := fun _ _ ht hne => not_native_of_differs ht hne
  wild_is_jcost_to_the_ledger := wild_indistinguishable_from_jcost
  unique_presentation := fun _ _ hFG hGJ hF hG => unique_readable_extension hFG hGJ hF hG
  presentation_exists := jcost_floorReadable

end RowContinuumLedger
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
