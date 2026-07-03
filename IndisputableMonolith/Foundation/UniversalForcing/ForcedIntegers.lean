/-
  UniversalForcing/ForcedIntegers.lean

  The middle forced layer: from counting to the integers, by differences.

  The δ paper claims distinction forces three discrete layers: the natural
  numbers, the integers, and the rational field. The Lean spine forced the first
  (`ForcedSemiring`: the forced arithmetic is canonically `ℕ`) and the third
  (`ForcedRatios`: the ratios of forced numbers are exactly `ℚ_{>0}`). This module
  fills the middle: the *differences* of forced numbers are exactly `ℤ`.

  The construction is the additive mirror of `ForcedRatios`. There, two counts are
  compared multiplicatively (the ratio `a/b`), the comparison symmetry is the
  reciprocal involution `x ↦ x⁻¹`, and its fixed locus is the unit ratio `a = b`,
  which is the recognition cost's zero. Here two counts are compared additively
  (the difference `a − b`), the comparison symmetry is negation `z ↦ −z` (the
  debit/credit swap of the ledger), and its fixed locus is again the diagonal
  `a = b`, the additive null. Counting forces `ℕ`; the ledger's two-sided
  (credit/debit) nature forces its difference group `ℤ`.

  Results, parallel to `ForcedRatios`:

  * `integers_surject`: every integer is a difference of two forced numbers, so
    the forced difference layer is all of `ℤ`, with the embedding `toInt`
    preserving `0, 1, +, ×` and injective.
  * `forced_difference_zero_iff`: a difference of forced numbers vanishes exactly
    on the diagonal `a = b` (the additive null locus).
  * `forced_difference_fixed_iff`: the negation involution fixes a forced
    difference exactly on the diagonal — the additive analogue of the reciprocal
    involution fixing the unit ratio.
-/

import IndisputableMonolith.Foundation.UniversalForcing.ForcedSemiring

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace ForcedIntegers

open ArithmeticFromLogic
open ArithmeticFromLogic.LogicNat

/-! ## The canonical embedding of the forced arithmetic into `ℤ`. -/

/-- Embed a forced number into the integers by its iteration count. -/
def toInt (n : LogicNat) : ℤ := (LogicNat.toNat n : ℤ)

@[simp] theorem toInt_zero : toInt LogicNat.zero = 0 := by simp [toInt]

@[simp] theorem toInt_one : toInt 1 = 1 := by
  show ((LogicNat.toNat 1 : ℕ) : ℤ) = 1
  rw [show LogicNat.toNat 1 = 1 from rfl]
  norm_num

theorem toInt_add (a b : LogicNat) : toInt (a + b) = toInt a + toInt b := by
  simp only [toInt]
  rw [LogicNat.toNat_add]
  push_cast
  ring

theorem toInt_mul (a b : LogicNat) : toInt (a * b) = toInt a * toInt b := by
  simp only [toInt]
  rw [LogicNat.toNat_mul]
  push_cast
  ring

theorem toInt_injective : Function.Injective toInt := by
  intro a b h
  have hnat : LogicNat.toNat a = LogicNat.toNat b := by
    have : (LogicNat.toNat a : ℤ) = (LogicNat.toNat b : ℤ) := h
    exact_mod_cast this
  exact LogicNat.equivNat.injective hnat

theorem toInt_nonneg (n : LogicNat) : 0 ≤ toInt n := by
  simp only [toInt]
  exact Int.natCast_nonneg _

/-! ## The forced differences are exactly the integers. -/

/-- **Every integer is a difference of two forced numbers.** The forced
difference layer is all of `ℤ`, so distinction forces the full additive group of
integers, not a proper sub-collection. -/
theorem integers_surject (z : ℤ) :
    ∃ a b : LogicNat, z = toInt a - toInt b := by
  refine ⟨LogicNat.fromNat z.toNat, LogicNat.fromNat (-z).toNat, ?_⟩
  simp only [toInt, LogicNat.toNat_fromNat]
  omega

/-! ## The negation involution acts on the forced differences. -/

/-- A difference of forced numbers vanishes exactly on the diagonal: the additive
null locus is `a = b`, mirroring the multiplicative unit locus of `ForcedRatios`. -/
theorem forced_difference_zero_iff (a b : LogicNat) :
    toInt a - toInt b = 0 ↔ a = b := by
  constructor
  · intro h
    have : toInt a = toInt b := by omega
    exact toInt_injective this
  · intro h; subst h; ring

/-- Negation swaps the two counts of a forced difference: `−(a − b) = b − a`. This
is the additive analogue of the reciprocal swap `(a/b)⁻¹ = b/a` on forced ratios. -/
theorem forced_difference_neg_swap (a b : LogicNat) :
    -(toInt a - toInt b) = toInt b - toInt a := by ring

/-- **The additive analogue of the reciprocal fixed-point law.** The negation
involution fixes a forced difference exactly on the diagonal `a = b` — just as the
reciprocal involution fixes a forced ratio exactly on the unit `a = b`. The two
forced layers, integers and ratios, carry the same comparison geometry: an
involution that swaps two counts, fixed precisely where the counts agree. -/
theorem forced_difference_fixed_iff (a b : LogicNat) :
    (toInt a - toInt b = -(toInt a - toInt b)) ↔ a = b := by
  rw [forced_difference_neg_swap]
  constructor
  · intro h
    have hz : toInt a - toInt b = 0 := by omega
    exact (forced_difference_zero_iff a b).mp hz
  · intro h; subst h; ring

/-! ## Certificate: distinction forces the additive group of integers. -/

/-- **Certificate.** The forced arithmetic embeds in `ℤ` preserving `0, 1, +, ×`;
its differences are exactly `ℤ`; and the negation involution fixes a difference
precisely on the diagonal. The integer layer the δ paper names is forced,
canonical, and carries the additive mirror of the ratio layer's comparison
geometry. -/
structure ForcedIntegersCert where
  embed : LogicNat → ℤ
  embed_zero : embed LogicNat.zero = 0
  embed_one : embed 1 = 1
  embed_add : ∀ a b, embed (a + b) = embed a + embed b
  embed_mul : ∀ a b, embed (a * b) = embed a * embed b
  embed_injective : Function.Injective embed
  differences_surject : ∀ z : ℤ, ∃ a b : LogicNat, z = embed a - embed b
  negation_diagonal : ∀ a b : LogicNat,
      (toInt a - toInt b = -(toInt a - toInt b)) ↔ a = b

/-- The forced-integers certificate holds. -/
def forcedIntegersCert_holds : ForcedIntegersCert where
  embed := toInt
  embed_zero := toInt_zero
  embed_one := toInt_one
  embed_add := toInt_add
  embed_mul := toInt_mul
  embed_injective := toInt_injective
  differences_surject := integers_surject
  negation_diagonal := forced_difference_fixed_iff

end ForcedIntegers
end UniversalForcing
end Foundation
end IndisputableMonolith
