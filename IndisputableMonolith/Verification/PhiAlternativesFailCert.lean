import Mathlib
import IndisputableMonolith.PhiSupport.Alternatives
import IndisputableMonolith.RecogSpec.PhiSelectionCore

/-!
# Phi Alternatives Fail Certificate

This module certifies that common mathematical constants (e, π, √2, √3, √5) **fail**
the PhiSelection criterion, demonstrating that φ is uniquely determined by the
mathematical structure and not an arbitrary choice among "nice" constants.

This addresses the "numerology objection" by proving exclusion: even though φ
has a simple closed form (1 + √5)/2, the selection criterion x² = x + 1 is not
satisfied by other common mathematical constants.

Combined with φ uniqueness (PhiPinnedCert), this shows:
1. φ is the ONLY positive solution to x² = x + 1 (uniqueness)
2. Common alternatives all fail (exclusion)
3. Therefore φ is mathematically forced, not chosen by fitting
-/

namespace IndisputableMonolith
namespace Verification
namespace PhiAlternativesFail

open IndisputableMonolith.PhiSupport.Alternatives

/-- Certificate structure for alternative constants failing selection. -/
structure PhiAlternativesFailCert where
  deriving Repr

/-- Verification predicate: all tested common constants fail PhiSelection. -/
@[simp] def PhiAlternativesFailCert.verified (_c : PhiAlternativesFailCert) : Prop :=
  -- Euler's number e fails
  ¬RecogSpec.PhiSelection (Real.exp 1) ∧
  -- π fails
  ¬RecogSpec.PhiSelection Real.pi ∧
  -- √2 fails
  ¬RecogSpec.PhiSelection (Real.sqrt 2) ∧
  -- √3 fails
  ¬RecogSpec.PhiSelection (Real.sqrt 3) ∧
  -- √5 fails (notably, despite φ = (1 + √5)/2)
  ¬RecogSpec.PhiSelection (Real.sqrt 5)

/-- The certificate verifies by referencing the proven theorems. -/
@[simp] theorem PhiAlternativesFailCert.verified_any (c : PhiAlternativesFailCert) :
    PhiAlternativesFailCert.verified c :=
  common_constants_fail_selection

end PhiAlternativesFail
end Verification
end IndisputableMonolith
