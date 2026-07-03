import IndisputableMonolith.Foundation.UniversalForcing
import IndisputableMonolith.Foundation.DiscreteLogicRealization
import IndisputableMonolith.Foundation.CategoricalLogicRealization
import IndisputableMonolith.Foundation.ModularLogicRealization
import IndisputableMonolith.Foundation.OrderedLogicRealization
import IndisputableMonolith.Foundation.PhysicsLogicRealization

/-!
  UniversalForcingAudit.lean

  Reproducible audit surface for the Universal Forcing program.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcingAudit

open UniversalForcing
open DiscreteLogicRealization
open CategoricalLogicRealization
open ModularLogicRealization
open OrderedLogicRealization
open PhysicsLogicRealization

/-! ## Abstract theorem surface -/

noncomputable example (R S : LogicRealization.{0, 0}) :
    (arithmeticOf R).peano.carrier ≃ (arithmeticOf S).peano.carrier :=
  ArithmeticOf.equivOfInitial (arithmeticOf R) (arithmeticOf S)
-- #print axioms UniversalForcing.arithmetic_invariant
--   propext, Quot.sound

example (R : LogicRealization) :
    ArithmeticOf.PeanoSurface (arithmeticOf R) :=
  peano_surface R
-- #print axioms UniversalForcing.peano_surface
--   propext, Quot.sound

/-! ## Continuous positive-ratio realization -/

noncomputable example
    (C : LogicAsFunctionalEquation.ComparisonOperator)
    (h : LogicAsFunctionalEquation.SatisfiesLawsOfLogic C)
    (S : LogicRealization.{0, 0}) :
    (arithmeticOf (LogicRealization.ofPositiveRatioComparison C h)).peano.carrier
      ≃ (arithmeticOf S).peano.carrier :=
  ArithmeticOf.equivOfInitial
    (arithmeticOf (LogicRealization.ofPositiveRatioComparison C h)) (arithmeticOf S)
-- #print axioms UniversalForcing.continuous_positive_ratio_arithmetic_invariant
--   propext, Quot.sound

/-! ## Discrete and categorical realizations -/

example : boolRealization.hasIdentityStep :=
  bool_hasIdentityStep
-- #print axioms DiscreteLogicRealization.bool_hasIdentityStep
--   propext

noncomputable example (R : LogicRealization.{0, 0}) :
    (arithmeticOf boolRealization).peano.carrier ≃ (arithmeticOf R).peano.carrier :=
  ArithmeticOf.equivOfInitial (arithmeticOf boolRealization) (arithmeticOf R)
-- #print axioms DiscreteLogicRealization.bool_arithmetic_invariant
--   propext, Quot.sound

noncomputable example (R : LogicRealization.{0, 0}) :
    (arithmeticOf canonicalCategoricalRealization).peano.carrier
      ≃ (arithmeticOf R).peano.carrier :=
  ArithmeticOf.equivOfInitial (arithmeticOf canonicalCategoricalRealization) (arithmeticOf R)
-- #print axioms CategoricalLogicRealization.categorical_arithmetic_invariant
--   propext, Quot.sound

/-! ## Modular, ordered, and physics realizations -/

noncomputable example (k : ℕ) (R : LogicRealization.{0, 0}) :
    (arithmeticOf (modularRealization k)).peano.carrier ≃ (arithmeticOf R).peano.carrier :=
  ArithmeticOf.equivOfInitial (arithmeticOf (modularRealization k)) (arithmeticOf R)
-- #print axioms ModularLogicRealization.modular_arithmetic_invariant
--   propext, Quot.sound

example (k : ℕ) (n : ArithmeticFromLogic.LogicNat) :
    modularInterpret k
        (ArithmeticFromLogic.LogicNat.fromNat
          (ArithmeticFromLogic.LogicNat.toNat n + modulus k))
      = modularInterpret k n :=
  modular_interpret_periodic k n
-- #print axioms ModularLogicRealization.modular_interpret_periodic
--   propext, Quot.sound

example :
    LogicRealization.FaithfulArithmeticInterpretation natOrderedRealization :=
  ordered_faithful
-- #print axioms OrderedLogicRealization.ordered_faithful
--   propext, Quot.sound

noncomputable example (R : LogicRealization.{0, 0}) :
    (arithmeticOf natOrderedRealization).peano.carrier ≃ (arithmeticOf R).peano.carrier :=
  ArithmeticOf.equivOfInitial (arithmeticOf natOrderedRealization) (arithmeticOf R)
-- #print axioms OrderedLogicRealization.ordered_arithmetic_invariant
--   propext, Quot.sound

example :
    LogicRealization.FaithfulArithmeticInterpretation physicsRealization :=
  physics_faithful
-- #print axioms PhysicsLogicRealization.physics_faithful
--   propext, Quot.sound

noncomputable example (R : LogicRealization.{0, 0}) :
    (arithmeticOf physicsRealization).peano.carrier ≃ (arithmeticOf R).peano.carrier :=
  ArithmeticOf.equivOfInitial (arithmeticOf physicsRealization) (arithmeticOf R)
-- #print axioms PhysicsLogicRealization.physics_arithmetic_invariant
--   propext, Quot.sound

end UniversalForcingAudit
end Foundation
end IndisputableMonolith
