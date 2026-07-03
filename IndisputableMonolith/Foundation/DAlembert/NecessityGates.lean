import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.DAlembert.Counterexamples

/-!
# Necessity Gates for RCL Inevitability

The counterexample in `Foundation/DAlembert/Counterexamples.lean` shows that

> (symmetry + normalization + C² + calibration + existence of *some* combiner P)

does **not** force the d'Alembert/RCL structure.

Therefore, any honest ``full inevitability'' statement must include at least one
additional nondegeneracy gate that rules out the additive/quadratic-log branch.

This module implements the **minimal** such gate:

## Gate: Interaction / Non-additivity

If costs were purely additive under composition, then in log-coordinates the cost is quadratic:

`F(x) = (log x)^2 / 2`

and the combiner is `P(u,v)=2u+2v`. This branch does not produce the RCL.

The interaction gate asserts that there exists at least one pair of comparisons
whose combined cost is **not** purely additive in the two individual costs.

This is the weakest possible ``anti-quadratic'' gate and is satisfied by `Jcost`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DAlembert
namespace NecessityGates

open Real
open IndisputableMonolith.Cost
open IndisputableMonolith.Foundation.DAlembert.Counterexamples

/-! ## Gate definition -/

/-- **Interaction / non-additivity gate** for a cost `F`.

`HasInteraction F` means there exist `x,y>0` such that the product/quotient combined cost
is not purely additive in the two individual costs. -/
def HasInteraction (F : ℝ → ℝ) : Prop :=
  ∃ x y : ℝ, 0 < x ∧ 0 < y ∧
    F (x * y) + F (x / y) ≠ 2 * F x + 2 * F y

/-! ## The quadratic-log branch fails the gate -/

lemma Fquad_additive (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Fquad (x * y) + Fquad (x / y) = 2 * Fquad x + 2 * Fquad y := by
  -- This is exactly `Fquad_consistency` with `Padd u v = 2u+2v`.
  simpa [Padd] using (Fquad_consistency x y hx hy)

theorem Fquad_noInteraction : ¬ HasInteraction Fquad := by
  intro h
  rcases h with ⟨x, y, hx, hy, hneq⟩
  exact hneq (Fquad_additive x y hx hy)

/-! ## Jcost satisfies the gate -/

theorem Jcost_hasInteraction : HasInteraction Jcost := by
  -- Concrete witness: x = y = 2.
  refine ⟨2, 2, by norm_num, by norm_num, ?_⟩
  -- Evaluate numerically: J(4) + J(1) ≠ 2J(2) + 2J(2).
  -- J(1)=0, J(2)=1/4, J(4)=9/8.
  norm_num [Jcost]

end NecessityGates
end DAlembert
end Foundation
end IndisputableMonolith
