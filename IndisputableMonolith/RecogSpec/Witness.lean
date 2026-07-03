import Mathlib
-- import IndisputableMonolith.Measurement
import IndisputableMonolith.Patterns
import IndisputableMonolith.RecogSpec.Spec
import IndisputableMonolith.RecogSpec.MatchesLegacy
-- import IndisputableMonolith.Quantum

namespace IndisputableMonolith
namespace RecogSpec
namespace Witness

-- Note: Witness.Core is currently empty, no export needed

/-- Minimal universal dimless witness. -/
noncomputable abbrev UD_minimal (φ : ℝ) : UniversalDimless φ := UD_explicit φ

/-- Minimal matching witness. -/
lemma matches_minimal (φ : ℝ) (L : Ledger) (B : Bridge L) :
    Matches φ L B (UD_minimal φ) := by
  exact matchesEval_to_Matches φ L B (UD_minimal φ) (matchesEval_explicit φ L B)

end Witness
end RecogSpec
end IndisputableMonolith
