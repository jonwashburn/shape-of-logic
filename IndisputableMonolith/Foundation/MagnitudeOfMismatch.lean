import Mathlib
import IndisputableMonolith.Foundation.PrimitiveDistinction

/-!
# Magnitude of Mismatch: Symmetry from Single-Valued Predication

The Logic_FE rigidity theorem encodes the Aristotelian condition (L2)
Non-Contradiction as symmetry of the comparison operator,
`C x y = C y x`. The companion paper
`RS_Magnitude_of_Mismatch_Uniqueness.tex` argues that this encoding is not
an interpretive choice but a structural necessity: any comparison that
returns a single value when applied to an unordered pair `{x, y}` must be
symmetric. The asymmetric "directed revision" reading does not produce a
single binary function; it produces two distinct directional functions.

This module formalises that argument. The relevant primitive is the
observation that a function `K → K → Cost` is the same data as a
function `Sym2 K → Cost` exactly when it is symmetric. We prove both
directions:

* `singleValued_implies_symmetric`: if `C` factors through `Sym2 K`, it
  is symmetric.
* `symmetric_implies_factorsThrough`: any symmetric `C` factors through
  `Sym2 K`.

The combined `singleValued_iff_symmetric` is the Lean form of
Theorem 4 of the companion paper. Together with the `PrimitiveDistinction`
result that (L1), (L2), (L3a) are definitional, this leaves the
magnitude-of-mismatch encoding without any interpretive freedom: it is
the unique reading consistent with single-valued predication on a
distinguished pair.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MagnitudeOfMismatch

open Classical

/-! ## Single-Valuedness on the Unordered Pair -/

/-- A comparison operator `C : K → K → Cost` is **single-valued on the
unordered pair** if it factors through the type of unordered pairs `Sym2 K`.

Operationally: there is a single function `f` such that the cost
`C x y` is `f s(x, y)` and the order in which the arguments are
presented does not affect the value. -/
def SingleValuedOnUnorderedPair {K Cost : Type*} (C : K → K → Cost) : Prop :=
  ∃ f : Sym2 K → Cost, ∀ x y, C x y = f s(x, y)

/-! ## Symmetry Forced by Single-Valuedness -/

/-- **Single-valued predication forces symmetry.**

If a comparison operator factors through the unordered pair, then the
order of its arguments does not matter. The asymmetric reading (where
`C x y` and `C y x` are different values) is not a single function on
pairs; it is two distinct directional functions. -/
theorem singleValued_implies_symmetric
    {K Cost : Type*} (C : K → K → Cost)
    (h : SingleValuedOnUnorderedPair C) :
    ∀ x y : K, C x y = C y x := by
  intro x y
  rcases h with ⟨f, hf⟩
  have hxy := hf x y
  have hyx := hf y x
  have hsym : (s(x, y) : Sym2 K) = s(y, x) := Sym2.eq_swap
  rw [hxy, hyx, hsym]

/-- **Conversely: symmetric comparisons factor through unordered pairs.**

Any symmetric function on `K × K` is the lift of a single function on
`Sym2 K`. So symmetry and single-valuedness on the unordered pair are
equivalent. -/
theorem symmetric_implies_factorsThrough
    {K Cost : Type*} (C : K → K → Cost)
    (hsymm : ∀ x y : K, C x y = C y x) :
    SingleValuedOnUnorderedPair C := by
  refine ⟨Sym2.lift ⟨fun a b => C a b, fun a b => hsymm a b⟩, ?_⟩
  intro x y
  simp [Sym2.lift_mk]

/-- **Equivalence: single-valuedness on the unordered pair is symmetry.** -/
theorem singleValued_iff_symmetric
    {K Cost : Type*} (C : K → K → Cost) :
    SingleValuedOnUnorderedPair C ↔ ∀ x y : K, C x y = C y x :=
  ⟨singleValued_implies_symmetric C,
   fun h => symmetric_implies_factorsThrough C h⟩

/-! ## Asymmetry Splits the Operator -/

/-- The negation: if `C` is asymmetric on at least one pair, it cannot
factor through the unordered pair. Single-valuedness fails the moment the
two orderings give different values.

This is the Lean form of Theorem 3 of the companion paper: asymmetry
splits a single binary function into two directional functions. -/
theorem asymmetric_not_singleValued
    {K Cost : Type*} (C : K → K → Cost)
    (h : ∃ x y : K, C x y ≠ C y x) :
    ¬ SingleValuedOnUnorderedPair C := by
  rintro hSV
  rcases h with ⟨x, y, hxy⟩
  exact hxy (singleValued_implies_symmetric C hSV x y)

/-! ## Connection to PrimitiveDistinction

The `PrimitiveDistinction.equalityCost` is the canonical equality-induced
cost. By the equivalence above, it is single-valued on the unordered pair
iff it is symmetric — and `non_contradiction_from_equality` already proves
symmetry of the equality-induced cost. So the equality-induced cost is in
the canonical magnitude-of-mismatch shape automatically, with no further
choice. -/

open IndisputableMonolith.Foundation.PrimitiveDistinction

/-- The equality-induced cost is single-valued on the unordered pair. -/
theorem equalityCost_singleValued (K : Type*) (weight : ℝ) :
    SingleValuedOnUnorderedPair (equalityCost K weight) :=
  symmetric_implies_factorsThrough (equalityCost K weight)
    (non_contradiction_from_equality K weight)

/-! ## Headline: Magnitude-of-Mismatch is Forced

Combining the two directions, the magnitude-of-mismatch encoding of (L2)
(symmetry) is the unique encoding consistent with treating a comparison
as a single-valued predicate on a distinguished pair.

Asymmetric ("directed revision") readings are not single binary functions;
they are two-valued, hence multi-valued by the standard meaning of
single-valuedness. The Aristotelian Non-Contradiction reading on operator
structure forces symmetry.
-/

/-- **Magnitude-of-Mismatch theorem (combined).**

On any carrier and cost type, a comparison operator is single-valued on
the unordered pair if and only if it satisfies (L2) Non-Contradiction
in operator form (`C x y = C y x`). The two are equivalent statements;
neither is more primitive than the other. The asymmetric reading of
Non-Contradiction does not produce a single comparison operator. -/
theorem magnitude_of_mismatch_forced
    {K Cost : Type*} (C : K → K → Cost) :
    SingleValuedOnUnorderedPair C ↔ ∀ x y : K, C x y = C y x :=
  singleValued_iff_symmetric C

end MagnitudeOfMismatch
end Foundation
end IndisputableMonolith
