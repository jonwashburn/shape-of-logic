import Mathlib
import IndisputableMonolith.Verification.BridgeCore

/-!
# UnitsRescaled Laws Certificate

This audit certificate records basic **closure properties** of the anchor-rescaling
relation `Verification.UnitsRescaled`:

- reflexivity (every units pack is rescaled to itself),
- symmetry (rescalings can be inverted),
- transitivity (rescalings compose).

Because `UnitsRescaled` is a `Type` (a structure), the certificate records these
laws at the `Prop` level via `Nonempty`.
-/

namespace IndisputableMonolith
namespace Verification
namespace UnitsRescaledLaws

open IndisputableMonolith.Constants

structure UnitsRescaledLawsCert where
  deriving Repr

@[simp] def UnitsRescaledLawsCert.verified (_c : UnitsRescaledLawsCert) : Prop :=
  -- refl
  (∀ U : RSUnits, Nonempty (UnitsRescaled U U))
  ∧
  -- symm
  (∀ {U U' : RSUnits}, Nonempty (UnitsRescaled U U') → Nonempty (UnitsRescaled U' U))
  ∧
  -- trans
  (∀ {U U' U'' : RSUnits},
      Nonempty (UnitsRescaled U U') →
      Nonempty (UnitsRescaled U' U'') →
        Nonempty (UnitsRescaled U U''))

@[simp] theorem UnitsRescaledLawsCert.verified_any (c : UnitsRescaledLawsCert) :
    UnitsRescaledLawsCert.verified c := by
  refine And.intro ?refl (And.intro ?symm ?trans)
  · intro U
    exact ⟨UnitsRescaled.refl U⟩
  · intro U U' h
    rcases h with ⟨hUU'⟩
    exact ⟨UnitsRescaled.symm hUU'⟩
  · intro U U' U'' h₁ h₂
    rcases h₁ with ⟨hUU'⟩
    rcases h₂ with ⟨hU'U''⟩
    exact ⟨UnitsRescaled.trans hUU' hU'U''⟩

end UnitsRescaledLaws
end Verification
end IndisputableMonolith

