import Mathlib
import IndisputableMonolith.RecogSpec.Spec

/-!
# Units-from-Anchors Rescaling Certificate

This audit certificate records that rescaling anchors by a positive factor `s`
corresponds to a `Verification.UnitsRescaled` relation between the resulting
`RSUnits` packs (with `c` fixed).

This makes the “units are only defined up to scale” invariance explicit in the
certified surface.
-/

namespace IndisputableMonolith
namespace Verification
namespace UnitsFromAnchorsRescale

open IndisputableMonolith.RecogSpec

/-- Rescale anchors by a factor `s` (scaling both a1 and a2).

The consistency field is preserved because `a1 = 0 → a2 = 0` implies
`s*a1 = 0 → s*a2 = 0`. -/
def rescaleAnchors (s : ℝ) (A : RecogSpec.Anchors) : RecogSpec.Anchors :=
{ a1 := s * A.a1
  a2 := s * A.a2
  consistent := by
    intro h
    by_cases hs : s = 0
    · simp [hs]
    · have ha1 : A.a1 = 0 := by
        -- from s*a1=0 and s≠0
        have : s = 0 ∨ A.a1 = 0 := mul_eq_zero.mp h
        cases this with
        | inl hs0 => exact (hs hs0).elim
        | inr ha1 => exact ha1
      have ha2 : A.a2 = 0 := A.consistent ha1
      simp [ha2] }

private lemma speedFromAnchors_rescale (A : RecogSpec.Anchors) (s : ℝ) (hs : 0 < s) :
    RecogSpec.speedFromAnchors (rescaleAnchors s A) = RecogSpec.speedFromAnchors A := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  by_cases hA : A.a1 = 0
  · -- degenerate anchors: both speeds are 0
    have hA' : (rescaleAnchors s A).a1 = 0 := by simp [rescaleAnchors, hA]
    simp [RecogSpec.speedFromAnchors, hA, hA', rescaleAnchors]
  · have hA' : (rescaleAnchors s A).a1 ≠ 0 := by
      -- s*a1 ≠ 0
      simp [rescaleAnchors, hs0, hA]
    -- compute both speeds on the nondegenerate branch and cancel `s`
    have hsA : RecogSpec.speedFromAnchors (rescaleAnchors s A) =
        (rescaleAnchors s A).a2 / (rescaleAnchors s A).a1 :=
      RecogSpec.speedFromAnchors_of_ne_zero (A := rescaleAnchors s A) hA'
    have hA0 : RecogSpec.speedFromAnchors A = A.a2 / A.a1 :=
      RecogSpec.speedFromAnchors_of_ne_zero (A := A) hA
    -- simplify the ratio
    have hcancel : (s * A.a2) / (s * A.a1) = A.a2 / A.a1 := by
      field_simp [hs0, hA]
    -- finish
    calc
      RecogSpec.speedFromAnchors (rescaleAnchors s A)
          = (rescaleAnchors s A).a2 / (rescaleAnchors s A).a1 := hsA
      _ = (s * A.a2) / (s * A.a1) := by simp [rescaleAnchors]
      _ = A.a2 / A.a1 := hcancel
      _ = RecogSpec.speedFromAnchors A := hA0.symm

private def unitsFromAnchors_unitsRescaled (A : RecogSpec.Anchors) (s : ℝ) (hs : 0 < s) :
    Verification.UnitsRescaled (RecogSpec.unitsFromAnchors A) (RecogSpec.unitsFromAnchors (rescaleAnchors s A)) := by
  refine
    { s := s
      hs := hs
      tau0 := by simp [RecogSpec.unitsFromAnchors, rescaleAnchors]
      ell0 := by simp [RecogSpec.unitsFromAnchors, rescaleAnchors]
      cfix := by
        -- c = speedFromAnchors is invariant under rescaling
        simp [RecogSpec.unitsFromAnchors, speedFromAnchors_rescale (A := A) (s := s) hs] }

structure UnitsFromAnchorsRescaleCert where
  deriving Repr

@[simp] def UnitsFromAnchorsRescaleCert.verified (_c : UnitsFromAnchorsRescaleCert) : Prop :=
  ∀ (A : RecogSpec.Anchors) (s : ℝ), 0 < s →
    Nonempty
      (Verification.UnitsRescaled
        (RecogSpec.unitsFromAnchors A)
        (RecogSpec.unitsFromAnchors (rescaleAnchors s A)))

@[simp] theorem UnitsFromAnchorsRescaleCert.verified_any (c : UnitsFromAnchorsRescaleCert) :
    UnitsFromAnchorsRescaleCert.verified c := by
  intro A s hs
  exact ⟨unitsFromAnchors_unitsRescaled (A := A) (s := s) hs⟩

end UnitsFromAnchorsRescale
end Verification
end IndisputableMonolith
