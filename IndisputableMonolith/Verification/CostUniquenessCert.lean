import Mathlib
import IndisputableMonolith.CostUniqueness

/-!
# Cost Uniqueness (Classical) Certificate

This audit certificate packages the "full" cost uniqueness theorem for `Jcost` under an
explicit hypothesis bundle (`IndisputableMonolith.CostUniqueness.UniqueCostAxioms`).

Unlike `Verification/T5UniqueCert.lean` (which uses the compact `JensenSketch` interface),
this cert records a more classical route: symmetry + normalization + strict convexity +
calibration + continuity + the cosh-add functional identity.

All assumptions are passed explicitly (no hidden typeclass axioms), and the proof is
entirely `sorry`-free.
-/

namespace IndisputableMonolith
namespace Verification
namespace CostUniqueness

open IndisputableMonolith.Cost

structure CostUniquenessCert where
  deriving Repr

/-- Verification predicate: any function satisfying `UniqueCostAxioms` agrees with `Jcost`
on all positive reals. -/
@[simp] def CostUniquenessCert.verified (_c : CostUniquenessCert) : Prop :=
  ∀ (F : ℝ → ℝ),
    _root_.IndisputableMonolith.CostUniqueness.UniqueCostAxioms F →
      ∀ {x : ℝ}, 0 < x → F x = Jcost x

@[simp] theorem CostUniquenessCert.verified_any (c : CostUniquenessCert) :
    CostUniquenessCert.verified c := by
  intro F hF x hx
  exact _root_.IndisputableMonolith.CostUniqueness.unique_cost_on_pos F hF hx

end CostUniqueness
end Verification
end IndisputableMonolith
