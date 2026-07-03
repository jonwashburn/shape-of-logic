import Mathlib
import IndisputableMonolith.Measurement.BornRule

/-!
# Born Rule Derivation Certificate (two-outcome, axiom-free)

This certificate packages the derived two-outcome Born rule statement from
`IndisputableMonolith/Measurement/BornRule.lean` **without** any hidden typeclass axioms.

It states: given a two-branch rotation and amplitudes whose squared norms match the
geometric `cos²/sin²` amplitudes, the normalized recognition-cost probabilities match
those squared norms.
-/

namespace IndisputableMonolith
namespace Verification
namespace BornRuleDerivation

open IndisputableMonolith.Measurement

structure BornRuleDerivationCert where
  deriving Repr

@[simp] def BornRuleDerivationCert.verified (_c : BornRuleDerivationCert) : Prop :=
  ∀ (α₁ α₂ : ℂ) (rot : TwoBranchRotation),
    (‖α₁‖ ^ 2 + ‖α₂‖ ^ 2 = 1) →
    (‖α₁‖ ^ 2 = complementAmplitudeSquared rot) →
    (‖α₂‖ ^ 2 = initialAmplitudeSquared rot) →
      ∃ m : TwoOutcomeMeasurement,
        prob₁ m = ‖α₁‖ ^ 2 ∧
        prob₂ m = ‖α₂‖ ^ 2

@[simp] theorem BornRuleDerivationCert.verified_any (c : BornRuleDerivationCert) :
    BornRuleDerivationCert.verified c := by
  intro α₁ α₂ rot hα hrot₁ hrot₂
  exact born_rule_from_C (α₁:=α₁) (α₂:=α₂) hα rot hrot₁ hrot₂

end BornRuleDerivation
end Verification
end IndisputableMonolith
