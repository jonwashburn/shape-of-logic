import IndisputableMonolith.Foundation.ArithmeticOf

/-!
  UniversalForcing.lean

  First formal statement of the Universal Forcing theorem:

  any two Law-of-Logic realizations have canonically equivalent forced
  arithmetic objects, because those objects are initial Peano algebras.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing

/-- The forced arithmetic object of a realization. -/
def arithmeticOf (R : LogicRealization) : ArithmeticOf R :=
  ArithmeticOf.extracted R

/-- **Universal Forcing, first theorem form.**

For any two Law-of-Logic realizations, the arithmetic objects extracted from
them are canonically equivalent. In this first formal spine the equivalence is
the unique equivalence between initial Peano algebras. Later realization
modules enrich the interpretation map from each carrier into this invariant
arithmetic object. This definition now uses the realization's own internal
orbit, not the reference `LogicNat` object. -/
noncomputable def arithmetic_invariant
    (R S : LogicRealization) :
    (arithmeticOf R).peano.carrier ≃ (arithmeticOf S).peano.carrier :=
  ArithmeticOf.equivOfInitial (arithmeticOf R) (arithmeticOf S)

/-- The forced arithmetic of every realization is canonically equivalent to
the reference `LogicNat` Peano object. This is the simplest form of the
Universal Forcing theorem. -/
noncomputable def arith_universal_initial (R : LogicRealization) :
    (arithmeticOf R).peano.carrier ≃ ArithmeticFromLogic.LogicNat :=
  R.orbitEquivLogicNat

/-- **Universal Forcing Meta-Theorem, abstract spine.**

Any two Law-of-Logic realizations have canonically equivalent forced
arithmetic objects. -/
noncomputable def universal_forcing (R S : LogicRealization) :
    (arithmeticOf R).peano.carrier ≃ (arithmeticOf S).peano.carrier :=
  ArithmeticOf.equivOfInitial (arithmeticOf R) (arithmeticOf S)

/-- The continuous positive-ratio realization has the same forced arithmetic
as every other realization. -/
noncomputable def continuous_positive_ratio_arithmetic_invariant
    (C : LogicAsFunctionalEquation.ComparisonOperator)
    (h : LogicAsFunctionalEquation.SatisfiesLawsOfLogic C)
    (S : LogicRealization.{0, 0}) :
    (arithmeticOf (LogicRealization.ofPositiveRatioComparison C h)).peano.carrier
      ≃ (arithmeticOf S).peano.carrier :=
  ArithmeticOf.equivOfInitial
    (arithmeticOf (LogicRealization.ofPositiveRatioComparison C h)) (arithmeticOf S)

/-- The Peano surface is available for the forced arithmetic of every
realization. -/
theorem peano_surface (R : LogicRealization) :
    ArithmeticOf.PeanoSurface (arithmeticOf R) :=
  ArithmeticOf.extracted_peanoSurface R

/-! ## Paper-Upgrade Certificate

This package is the Lean-facing headline for the arithmetic paper's stronger
version: the positive-ratio construction is not a special arithmetic choice.
Every Law-of-Logic realization extracts an initial Peano object, every such
object is equivalent to the reference `LogicNat`, and any two extracted
arithmetic objects are canonically equivalent.
-/

/-- **Universal Forcing certificate.**

The arithmetic extracted from any admissible Law-of-Logic realization is
initial, has the Peano surface, is equivalent to `LogicNat`, and is invariant
up to canonical equivalence across realizations. -/
structure UniversalForcingCert where
  invariant :
    ∀ R S : LogicRealization.{0, 0},
      (arithmeticOf R).peano.carrier ≃ (arithmeticOf S).peano.carrier
  to_reference :
    ∀ R : LogicRealization.{0, 0},
      (arithmeticOf R).peano.carrier ≃ ArithmeticFromLogic.LogicNat
  peano :
    ∀ R : LogicRealization.{0, 0},
      ArithmeticOf.PeanoSurface (arithmeticOf R)
  continuous_positive_ratio_invariant :
    ∀ (C : LogicAsFunctionalEquation.ComparisonOperator)
      (h : LogicAsFunctionalEquation.SatisfiesLawsOfLogic C)
      (S : LogicRealization.{0, 0}),
      (arithmeticOf (LogicRealization.ofPositiveRatioComparison C h)).peano.carrier
        ≃ (arithmeticOf S).peano.carrier

/-- The Universal Forcing certificate is inhabited by the existing initiality
theorems. -/
noncomputable def universalForcingCert : UniversalForcingCert where
  invariant := fun R S => by
    change R.Orbit ≃ S.Orbit
    exact R.orbitEquivLogicNat.trans S.orbitEquivLogicNat.symm
  to_reference := fun R => by
    change R.Orbit ≃ ArithmeticFromLogic.LogicNat
    exact R.orbitEquivLogicNat
  peano := fun R => peano_surface R
  continuous_positive_ratio_invariant := fun C h S =>
    by
      change ArithmeticFromLogic.LogicNat ≃ S.Orbit
      exact S.orbitEquivLogicNat.symm

/-- Any two Law-of-Logic realizations force the same arithmetic surface. -/
theorem forced_arithmetic_surfaces_equivalent (R S : LogicRealization.{0, 0}) :
    Nonempty ((arithmeticOf R).peano.carrier ≃ (arithmeticOf S).peano.carrier) :=
  ⟨by
    change R.Orbit ≃ S.Orbit
    exact R.orbitEquivLogicNat.trans S.orbitEquivLogicNat.symm⟩

end UniversalForcing
end Foundation
end IndisputableMonolith
