import Mathlib
import IndisputableMonolith.Cost

/-!
# T5 Packaging Certificate (transport lemma, NOT the uniqueness theorem)

**Honesty note (2026 audit correction).** This certificate is a *packaging
tautology*, and its docstring previously oversold it as "the crown jewel."
The `JensenSketch` hypotheses include BOTH `F(exp t) ≤ J(exp t)` and
`J(exp t) ≤ F(exp t)`, i.e. they already assert `F = J` on the exponential
axis. The conclusion `F = J on (0,∞)` is then just transport along
`exp/log` surjectivity. Hypothesis ≈ conclusion; no uniqueness content
lives here.

The ACTUAL T5 uniqueness theorem — the one with real mathematical
content — is `law_of_logic_forces_jcost` in `Cost/FunctionalEquation.lean`:
reciprocal symmetry + unit normalization + the composition law (C6) +
calibration + continuity force `F = J`, via the proved Aczél/d'Alembert
classification (`Cost/AczelProof.lean`). Cite THAT theorem for T5
uniqueness claims; cite this certificate only as the trivial axis-to-ray
transport step.
-/

namespace IndisputableMonolith
namespace Verification
namespace T5Unique

open IndisputableMonolith.Cost

structure T5UniqueCert where
  deriving Repr

/-- Verification predicate: exp-axis-to-positive-ray transport.

Any function F satisfying `JensenSketch` (whose bounds already pin
`F = J` on the exponential axis) equals `Jcost` on the positive reals.
This is a packaging/transport lemma; the substantive T5 uniqueness
theorem is `law_of_logic_forces_jcost` (see module header). -/
@[simp] def T5UniqueCert.verified (_c : T5UniqueCert) : Prop :=
  ∀ (F : ℝ → ℝ) [JensenSketch F] {x : ℝ}, 0 < x → F x = Jcost x

@[simp] theorem T5UniqueCert.verified_any (c : T5UniqueCert) :
    T5UniqueCert.verified c := by
  intro F _ x hx
  exact T5_cost_uniqueness_on_pos hx

end T5Unique
end Verification
end IndisputableMonolith

