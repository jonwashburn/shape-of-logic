import IndisputableMonolith.RecogSpec.Spec

namespace IndisputableMonolith
namespace RecogSpec

/-!
# Matches (legacy conversions)

`RecogSpec.Matches` is an existential predicate (`∃ pack, ...`) and is therefore a smuggling hotspot.
The certified surface should prefer the computed predicate `MatchesEval` (or `MatchesEvalWith`).

This module provides **legacy compatibility** conversions from `MatchesEval` to `Matches` for
older code paths. It is intentionally kept out of the certified import-closure.
-/

lemma matchesEval_to_Matches (φ : ℝ) (L : Ledger) (B : Bridge L) (U : UniversalDimless φ) :
    MatchesEval φ L B U → Matches φ L B U := by
  intro h
  unfold Matches
  refine ⟨dimlessPack_explicit φ L B, ?_⟩
  exact h

lemma matches_explicit (φ : ℝ) (L : Ledger) (B : Bridge L) :
    Matches φ L B (UD_explicit φ) := by
  exact matchesEval_to_Matches (φ:=φ) (L:=L) (B:=B) (U:=UD_explicit φ)
    (matchesEval_explicit (φ:=φ) (L:=L) (B:=B))

end RecogSpec
end IndisputableMonolith
