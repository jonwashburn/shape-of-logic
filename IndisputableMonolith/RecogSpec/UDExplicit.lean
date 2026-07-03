import IndisputableMonolith.RecogSpec.Spec

namespace IndisputableMonolith
namespace RecogSpec

/-- Minimal explicit universal dimless witness (reuses existing UD_explicit). -/
noncomputable abbrev UD_minimal (φ : ℝ) : UniversalDimless φ := UD_explicit φ

/-- Existence part: trivial bridge and explicit UD witness. -/
noncomputable def exists_bridge_and_UD (φ : ℝ) (L : Ledger) :
  ∃ B : Bridge L, ∃ U : UniversalDimless φ, MatchesEval φ L B U := by
  refine ⟨⟨()⟩, ⟨UD_explicit φ, ?h⟩⟩
  -- `MatchesEval` is inhabited by `matchesEval_explicit`
  exact matchesEval_explicit φ L ⟨()⟩

/-- Units equivalence by value equality -/
def unitsEqv_byValue (L : Ledger) : UnitsEqv L :=
{ Rel := fun B₁ B₂ => B₁ = B₂
, refl := by intro B; rfl
, symm := by
    intro B₁ B₂ h
    exact h.symm
, trans := by
    intro B₁ B₂ B₃ h12 h23
    exact h12.trans h23 }

end RecogSpec
end IndisputableMonolith
