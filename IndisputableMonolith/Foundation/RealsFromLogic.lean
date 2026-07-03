import Mathlib.Topology.UniformSpace.CompareReals
import IndisputableMonolith.Foundation.RationalsFromLogic

/-!
  RealsFromLogic.lean

  Recovery of the real numbers from the Law-of-Logic rational layer.

  The construction uses Mathlib's Bourbaki completion of `ℚ` as the
  completion engine, while the input rationals are the recovered rationals
  `LogicRat` from `Foundation.RationalsFromLogic`.  In other words:

    Law of Logic
      ⊢ LogicNat
      ⊢ LogicInt
      ⊢ LogicRat ≃ ℚ
      ⊢ Completion ℚ ≃ ℝ

  The type `LogicReal` is a wrapper around `CompareReals.Bourbakiℝ`,
  Mathlib's uniform-space completion of the rational uniform space.  The
  map `toReal` is the canonical comparison equivalence with Mathlib's
  Cauchy real numbers.

  This file intentionally exposes a transport-first API.  Algebra and
  order on `LogicReal` are defined by pulling back the corresponding
  structures along `toReal`, so every downstream theorem can reduce to
  the existing real theorem and then be read back as a recovered-real
  theorem.
-/

namespace IndisputableMonolith
namespace Foundation
namespace RealsFromLogic

open Filter UniformSpace
open RationalsFromLogic RationalsFromLogic.LogicRat

noncomputable section

/-! ## 1. Logic-rational Cauchy sequences -/

/-- A recovered-rational Cauchy sequence. The Cauchy predicate is measured
after transport to Mathlib's `ℚ`, using the standard uniform structure on
`ℚ`. This is the exact point where the recovered rational layer enters the
Cauchy completion. -/
structure CauchySeqLogicRat where
  seq : ℕ → LogicRat
  cauchy_toRat : CauchySeq (fun n => toRat (seq n))

/-- The underlying Mathlib-rational sequence of a recovered-rational Cauchy
sequence. -/
def CauchySeqLogicRat.toRatSeq (s : CauchySeqLogicRat) : ℕ → ℚ :=
  fun n => toRat (s.seq n)

theorem CauchySeqLogicRat.toRatSeq_cauchy (s : CauchySeqLogicRat) :
    CauchySeq s.toRatSeq :=
  s.cauchy_toRat

/-! ## 2. The recovered real type -/

/-- `LogicReal` is the Cauchy completion of the recovered rationals, realized
through the canonical completion of `ℚ` and the equivalence `LogicRat ≃ ℚ`.

The wrapper prevents global instance pollution on `Completion ℚ` while still
letting us reuse Mathlib's completed real line. -/
structure LogicReal where
  val : CompareReals.Bourbakiℝ

namespace LogicReal

/-- Transport a recovered real to Mathlib's real line. -/
noncomputable def toReal (x : LogicReal) : ℝ :=
  CompareReals.compareEquiv x.val

/-- Transport a Mathlib real into the recovered real line. -/
noncomputable def fromReal (x : ℝ) : LogicReal :=
  ⟨CompareReals.compareEquiv.symm x⟩

theorem toReal_fromReal (x : ℝ) : toReal (fromReal x) = x := by
  simp [toReal, fromReal]

theorem fromReal_toReal (x : LogicReal) : fromReal (toReal x) = x := by
  cases x
  simp [toReal, fromReal]

/-- Carrier equivalence between recovered reals and Mathlib reals. -/
noncomputable def equivReal : LogicReal ≃ ℝ where
  toFun := toReal
  invFun := fromReal
  left_inv := fromReal_toReal
  right_inv := toReal_fromReal

/-- Equality transfer: recovered real equality is exactly equality after
transport to Mathlib's real line. -/
theorem eq_iff_toReal_eq {x y : LogicReal} : x = y ↔ toReal x = toReal y := by
  constructor
  · exact congrArg toReal
  · intro h
    have := congrArg fromReal h
    rw [fromReal_toReal, fromReal_toReal] at this
    exact this

/-! ## 3. Embedding of recovered rationals -/

/-- Coerce a Mathlib rational into the Bourbaki completion. -/
noncomputable def ofRatCore (q : ℚ) : LogicReal :=
  ⟨Completion.coe' (show CompareReals.Q from q)⟩

/-- Embed a recovered rational into `LogicReal`. -/
noncomputable def ofLogicRat (q : LogicRat) : LogicReal :=
  ofRatCore (toRat q)

theorem toReal_ofRatCore (q : ℚ) : toReal (ofRatCore q) = (q : ℝ) := by
  -- `CompareReals.compareEquiv` is the unique completion comparison map;
  -- on dense rational points it agrees with the usual rational coercion.
  simpa [toReal, ofRatCore, CompareReals.compareEquiv] using
    (CompareReals.bourbakiPkg.compare_coe rationalCauSeqPkg
      (show CompareReals.Q from q))

theorem toReal_ofLogicRat (q : LogicRat) : toReal (ofLogicRat q) = (toRat q : ℝ) := by
  rw [ofLogicRat, toReal_ofRatCore]

/-! ## 4. Algebra and order by transport through `toReal` -/

instance : Zero LogicReal := ⟨fromReal 0⟩
instance : One LogicReal := ⟨fromReal 1⟩
instance : Add LogicReal := ⟨fun x y => fromReal (toReal x + toReal y)⟩
instance : Neg LogicReal := ⟨fun x => fromReal (-toReal x)⟩
instance : Sub LogicReal := ⟨fun x y => fromReal (toReal x - toReal y)⟩
instance : Mul LogicReal := ⟨fun x y => fromReal (toReal x * toReal y)⟩
instance : Inv LogicReal := ⟨fun x => fromReal (toReal x)⁻¹⟩
instance : Div LogicReal := ⟨fun x y => fromReal (toReal x / toReal y)⟩
instance : LE LogicReal := ⟨fun x y => toReal x ≤ toReal y⟩
instance : LT LogicReal := ⟨fun x y => toReal x < toReal y⟩

@[simp] theorem toReal_zero : toReal (0 : LogicReal) = 0 := toReal_fromReal 0
@[simp] theorem toReal_one : toReal (1 : LogicReal) = 1 := toReal_fromReal 1
@[simp] theorem toReal_add (x y : LogicReal) : toReal (x + y) = toReal x + toReal y :=
  toReal_fromReal _
@[simp] theorem toReal_neg (x : LogicReal) : toReal (-x) = -toReal x :=
  toReal_fromReal _
@[simp] theorem toReal_sub (x y : LogicReal) : toReal (x - y) = toReal x - toReal y :=
  toReal_fromReal _
@[simp] theorem toReal_mul (x y : LogicReal) : toReal (x * y) = toReal x * toReal y :=
  toReal_fromReal _
@[simp] theorem toReal_inv (x : LogicReal) : toReal x⁻¹ = (toReal x)⁻¹ :=
  toReal_fromReal _
@[simp] theorem toReal_div (x y : LogicReal) : toReal (x / y) = toReal x / toReal y :=
  toReal_fromReal _

theorem le_iff_toReal_le {x y : LogicReal} : x ≤ y ↔ toReal x ≤ toReal y := Iff.rfl
theorem lt_iff_toReal_lt {x y : LogicReal} : x < y ↔ toReal x < toReal y := Iff.rfl

theorem add_assoc' (x y z : LogicReal) : (x + y) + z = x + (y + z) := by
  rw [eq_iff_toReal_eq]
  simp
  ring

theorem add_comm' (x y : LogicReal) : x + y = y + x := by
  rw [eq_iff_toReal_eq]
  simp
  ring

theorem zero_add' (x : LogicReal) : (0 : LogicReal) + x = x := by
  rw [eq_iff_toReal_eq]
  simp

theorem add_zero' (x : LogicReal) : x + (0 : LogicReal) = x := by
  rw [eq_iff_toReal_eq]
  simp

theorem add_left_neg' (x : LogicReal) : -x + x = 0 := by
  rw [eq_iff_toReal_eq]
  simp

theorem mul_assoc' (x y z : LogicReal) : (x * y) * z = x * (y * z) := by
  rw [eq_iff_toReal_eq]
  simp
  ring

theorem mul_comm' (x y : LogicReal) : x * y = y * x := by
  rw [eq_iff_toReal_eq]
  simp
  ring

theorem one_mul' (x : LogicReal) : (1 : LogicReal) * x = x := by
  rw [eq_iff_toReal_eq]
  simp

theorem mul_one' (x : LogicReal) : x * (1 : LogicReal) = x := by
  rw [eq_iff_toReal_eq]
  simp

theorem mul_add' (x y z : LogicReal) : x * (y + z) = x * y + x * z := by
  rw [eq_iff_toReal_eq]
  simp
  ring

theorem add_mul' (x y z : LogicReal) : (x + y) * z = x * z + y * z := by
  rw [eq_iff_toReal_eq]
  simp
  ring

/-! ## 5. Completeness certificate -/

/-- The underlying Bourbaki completion is complete. This is the formal
completion theorem for the recovered real layer. -/
theorem bourbaki_complete : CompleteSpace CompareReals.Bourbakiℝ := by
  change CompleteSpace (Completion CompareReals.Q)
  infer_instance

/-- Every recovered real is represented by a Mathlib real and vice versa. -/
theorem logicReal_recovered_from_completion :
    (∀ x : LogicReal, fromReal (toReal x) = x) ∧
    (∀ x : ℝ, toReal (fromReal x) = x) :=
  ⟨fromReal_toReal, toReal_fromReal⟩

end LogicReal

end

end RealsFromLogic
end Foundation
end IndisputableMonolith
