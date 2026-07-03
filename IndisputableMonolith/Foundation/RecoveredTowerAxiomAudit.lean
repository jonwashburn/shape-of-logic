import IndisputableMonolith.Foundation.ArithmeticFromLogic
import IndisputableMonolith.Foundation.IntegersFromLogic
import IndisputableMonolith.Foundation.RationalsFromLogic
import IndisputableMonolith.Foundation.RealsFromLogic
import IndisputableMonolith.Foundation.ComplexFromLogic

/-!
  RecoveredTowerAxiomAudit.lean

  Audit surface for the Law-of-Logic recovered number tower:

    LogicNat → LogicInt → LogicRat → LogicReal → LogicComplex.

  The point of this file is not to rebuild arithmetic. It pins the named
  recovery/equality/transport theorems in one import target so `#print axioms`
  can be run consistently as the tower is strengthened.
-/

namespace IndisputableMonolith
namespace Foundation
namespace RecoveredTowerAxiomAudit

/-! ## Natural numbers -/

example : ArithmeticFromLogic.LogicNat ≃ Nat :=
  ArithmeticFromLogic.LogicNat.equivNat
-- #print axioms ArithmeticFromLogic.LogicNat.equivNat
--   no axioms

example (a b : ArithmeticFromLogic.LogicNat) :
    ArithmeticFromLogic.LogicNat.toNat (a + b)
      = ArithmeticFromLogic.LogicNat.toNat a + ArithmeticFromLogic.LogicNat.toNat b :=
  ArithmeticFromLogic.LogicNat.toNat_add a b
-- #print axioms ArithmeticFromLogic.LogicNat.toNat_add
--   no axioms

example (a b : ArithmeticFromLogic.LogicNat) :
    ArithmeticFromLogic.LogicNat.toNat (a * b)
      = ArithmeticFromLogic.LogicNat.toNat a * ArithmeticFromLogic.LogicNat.toNat b :=
  ArithmeticFromLogic.LogicNat.toNat_mul a b
-- #print axioms ArithmeticFromLogic.LogicNat.toNat_mul
--   no axioms

/-! ## Integers -/

example : IntegersFromLogic.LogicInt ≃ Int :=
  IntegersFromLogic.LogicInt.equivInt
-- #print axioms IntegersFromLogic.LogicInt.equivInt
--   propext, Quot.sound

example (a b : IntegersFromLogic.LogicInt) :
    IntegersFromLogic.LogicInt.toInt (a + b)
      = IntegersFromLogic.LogicInt.toInt a + IntegersFromLogic.LogicInt.toInt b :=
  IntegersFromLogic.LogicInt.toInt_add a b
-- #print axioms IntegersFromLogic.LogicInt.toInt_add
--   propext, Quot.sound

example (a b : IntegersFromLogic.LogicInt) :
    IntegersFromLogic.LogicInt.toInt (a * b)
      = IntegersFromLogic.LogicInt.toInt a * IntegersFromLogic.LogicInt.toInt b :=
  IntegersFromLogic.LogicInt.toInt_mul a b
-- #print axioms IntegersFromLogic.LogicInt.toInt_mul
--   propext, Quot.sound

/-! ## Rationals -/

noncomputable example : RationalsFromLogic.LogicRat ≃ ℚ :=
  RationalsFromLogic.LogicRat.equivRat
-- #print axioms RationalsFromLogic.LogicRat.equivRat
--   propext, Classical.choice, Quot.sound

example (a b : RationalsFromLogic.LogicRat) :
    RationalsFromLogic.LogicRat.toRat (a + b)
      = RationalsFromLogic.LogicRat.toRat a + RationalsFromLogic.LogicRat.toRat b :=
  RationalsFromLogic.LogicRat.toRat_add a b
-- #print axioms RationalsFromLogic.LogicRat.toRat_add
--   propext, Classical.choice, Quot.sound

example (a b : RationalsFromLogic.LogicRat) :
    RationalsFromLogic.LogicRat.toRat (a * b)
      = RationalsFromLogic.LogicRat.toRat a * RationalsFromLogic.LogicRat.toRat b :=
  RationalsFromLogic.LogicRat.toRat_mul a b
-- #print axioms RationalsFromLogic.LogicRat.toRat_mul
--   propext, Classical.choice, Quot.sound

/-! ## Reals -/

noncomputable example : RealsFromLogic.LogicReal ≃ ℝ :=
  RealsFromLogic.LogicReal.equivReal
-- #print axioms RealsFromLogic.LogicReal.equivReal
--   propext, Classical.choice, Quot.sound

example (x y : RealsFromLogic.LogicReal) :
    RealsFromLogic.LogicReal.toReal (x + y)
      = RealsFromLogic.LogicReal.toReal x + RealsFromLogic.LogicReal.toReal y :=
  RealsFromLogic.LogicReal.toReal_add x y
-- #print axioms RealsFromLogic.LogicReal.toReal_add
--   propext, Classical.choice, Quot.sound

example (x y : RealsFromLogic.LogicReal) :
    RealsFromLogic.LogicReal.toReal (x * y)
      = RealsFromLogic.LogicReal.toReal x * RealsFromLogic.LogicReal.toReal y :=
  RealsFromLogic.LogicReal.toReal_mul x y
-- #print axioms RealsFromLogic.LogicReal.toReal_mul
--   propext, Classical.choice, Quot.sound

/-! ## Complex numbers -/

noncomputable example : ComplexFromLogic.LogicComplex ≃ ℂ :=
  ComplexFromLogic.LogicComplex.equivComplex
-- #print axioms ComplexFromLogic.LogicComplex.equivComplex
--   propext, Classical.choice, Quot.sound

example (z w : ComplexFromLogic.LogicComplex) :
    ComplexFromLogic.LogicComplex.toComplex (z + w)
      = ComplexFromLogic.LogicComplex.toComplex z + ComplexFromLogic.LogicComplex.toComplex w :=
  ComplexFromLogic.LogicComplex.toComplex_add z w
-- #print axioms ComplexFromLogic.LogicComplex.toComplex_add
--   propext, Classical.choice, Quot.sound

example (z w : ComplexFromLogic.LogicComplex) :
    ComplexFromLogic.LogicComplex.toComplex (z * w)
      = ComplexFromLogic.LogicComplex.toComplex z * ComplexFromLogic.LogicComplex.toComplex w :=
  ComplexFromLogic.LogicComplex.toComplex_mul z w
-- #print axioms ComplexFromLogic.LogicComplex.toComplex_mul
--   propext, Classical.choice, Quot.sound

end RecoveredTowerAxiomAudit
end Foundation
end IndisputableMonolith
