import Mathlib
import IndisputableMonolith.Foundation.RealsFromLogic

/-!
  ComplexFromLogic.lean

  Complex numbers over the recovered real line.

  We do not redevelop complex analysis in this file.  We construct the carrier
  `LogicComplex` as pairs of recovered reals and prove the carrier-level
  equivalence with Mathlib's `ℂ`.  Later analytic modules can state explicitly
  when holomorphy/contour integration are being performed in Mathlib `ℂ` via
  this equivalence.
-/

namespace IndisputableMonolith
namespace Foundation
namespace ComplexFromLogic

open RealsFromLogic
open RealsFromLogic.LogicReal
open RationalsFromLogic

noncomputable section

/-- Complex numbers built over recovered reals. -/
structure LogicComplex where
  re : LogicReal
  im : LogicReal

namespace LogicComplex

/-- Transport a recovered complex number to Mathlib's complex line. -/
def toComplex (z : LogicComplex) : ℂ :=
  ⟨toReal z.re, toReal z.im⟩

/-- Transport a Mathlib complex number to the recovered complex line. -/
def fromComplex (z : ℂ) : LogicComplex where
  re := fromReal z.re
  im := fromReal z.im

@[simp] theorem toComplex_re (z : LogicComplex) :
    (toComplex z).re = toReal z.re := rfl

@[simp] theorem toComplex_im (z : LogicComplex) :
    (toComplex z).im = toReal z.im := rfl

@[simp] theorem toComplex_fromComplex (z : ℂ) :
    toComplex (fromComplex z) = z := by
  apply Complex.ext <;> simp [toComplex, fromComplex, toReal_fromReal]

@[simp] theorem fromComplex_toComplex (z : LogicComplex) :
    fromComplex (toComplex z) = z := by
  cases z with
  | mk re im =>
    simp [toComplex, fromComplex, fromReal_toReal]

/-- Carrier equivalence between recovered complex numbers and Mathlib `ℂ`. -/
def equivComplex : LogicComplex ≃ ℂ where
  toFun := toComplex
  invFun := fromComplex
  left_inv := fromComplex_toComplex
  right_inv := toComplex_fromComplex

/-- Equality transfer for recovered complex numbers. -/
theorem eq_iff_toComplex_eq {z w : LogicComplex} :
    z = w ↔ toComplex z = toComplex w := by
  constructor
  · exact congrArg toComplex
  · intro h
    have := congrArg fromComplex h
    rw [fromComplex_toComplex, fromComplex_toComplex] at this
    exact this

/-! ## Algebra and coordinate transport -/

instance : Zero LogicComplex := ⟨fromComplex 0⟩
instance : One LogicComplex := ⟨fromComplex 1⟩
instance : Add LogicComplex := ⟨fun z w => fromComplex (toComplex z + toComplex w)⟩
instance : Neg LogicComplex := ⟨fun z => fromComplex (-toComplex z)⟩
instance : Sub LogicComplex := ⟨fun z w => fromComplex (toComplex z - toComplex w)⟩
instance : Mul LogicComplex := ⟨fun z w => fromComplex (toComplex z * toComplex w)⟩
instance : Inv LogicComplex := ⟨fun z => fromComplex (toComplex z)⁻¹⟩
instance : Div LogicComplex := ⟨fun z w => fromComplex (toComplex z / toComplex w)⟩

@[simp] theorem toComplex_zero : toComplex (0 : LogicComplex) = 0 := by
  exact toComplex_fromComplex 0

@[simp] theorem toComplex_one : toComplex (1 : LogicComplex) = 1 := by
  exact toComplex_fromComplex 1

@[simp] theorem toComplex_add (z w : LogicComplex) :
    toComplex (z + w) = toComplex z + toComplex w := by
  simp [HAdd.hAdd, Add.add]

@[simp] theorem toComplex_neg (z : LogicComplex) :
    toComplex (-z) = -toComplex z := by
  simp [Neg.neg]

@[simp] theorem toComplex_sub (z w : LogicComplex) :
    toComplex (z - w) = toComplex z - toComplex w := by
  simp [HSub.hSub, Sub.sub]

@[simp] theorem toComplex_mul (z w : LogicComplex) :
    toComplex (z * w) = toComplex z * toComplex w := by
  simp [HMul.hMul, Mul.mul]

@[simp] theorem toComplex_inv (z : LogicComplex) :
    toComplex z⁻¹ = (toComplex z)⁻¹ := by
  simp [Inv.inv]

@[simp] theorem toComplex_div (z w : LogicComplex) :
    toComplex (z / w) = toComplex z / toComplex w := by
  simp [HDiv.hDiv, Div.div]

/-- Embed recovered reals into recovered complex numbers. -/
def ofLogicReal (x : LogicReal) : LogicComplex where
  re := x
  im := 0

@[simp] theorem toComplex_ofLogicReal (x : LogicReal) :
    toComplex (ofLogicReal x) = (toReal x : ℂ) := by
  apply Complex.ext <;> simp [ofLogicReal, toComplex]

/-- Embed recovered rationals into recovered complex numbers through recovered
reals. -/
def ofLogicRat (q : RationalsFromLogic.LogicRat) : LogicComplex :=
  ofLogicReal (RealsFromLogic.LogicReal.ofLogicRat q)

@[simp] theorem toComplex_ofLogicRat (q : RationalsFromLogic.LogicRat) :
    toComplex (ofLogicRat q) = ((RationalsFromLogic.LogicRat.toRat q : ℚ) : ℂ) := by
  rw [ofLogicRat, toComplex_ofLogicReal, toReal_ofLogicRat]
  norm_num

/-- The recovered complex carrier is exactly Mathlib `ℂ`, by transport. -/
theorem logicComplex_recovered_from_mathlib :
    (∀ z : LogicComplex, fromComplex (toComplex z) = z) ∧
    (∀ z : ℂ, toComplex (fromComplex z) = z) :=
  ⟨fromComplex_toComplex, toComplex_fromComplex⟩

end LogicComplex

end

end ComplexFromLogic
end Foundation
end IndisputableMonolith
