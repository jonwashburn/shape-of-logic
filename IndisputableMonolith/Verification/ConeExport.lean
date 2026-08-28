import Mathlib
import IndisputableMonolith.Causality.Basic
import IndisputableMonolith.LightCone.StepBounds
import IndisputableMonolith.Constants

/-!
# Cone bound over the causal reach structure

`LightCone.StepBounds` proves the cone bound over its own minimal local
kinematics. This module exports the same bound over the library-wide
`Causality.Kinematics` / `Causality.ReachN`, with the per-step clauses
stated directly as hypotheses: each act advances `time` by exactly
`U.tau0` and moves `rad` by at most `U.ell0`, and any `n`-step reach
then obeys `rad y - rad x ≤ U.c * (time y - time x)` with no `n` in the
statement.
-/

namespace IndisputableMonolith
namespace Verification

section ConeExport

variable {α : Type}

/-- View a causal kinematics as the local kinematics of `LightCone.StepBounds`. -/
def toLocal (K : Causality.Kinematics α) : LightCone.Local.Kinematics α :=
  ⟨K.step⟩

/-- Causal reach transports to the local reach used by `LightCone.StepBounds`. -/
lemma reachN_toLocal {K : Causality.Kinematics α} :
    ∀ {n x y}, Causality.ReachN K n x y → LightCone.Local.ReachN (toLocal K) n x y := by
  intro n x y h
  induction h with
  | zero => exact LightCone.Local.ReachN.zero
  | succ _ step ih => exact LightCone.Local.ReachN.succ ih step

/-- Verification-level cone bound: if each act advances the clock by exactly
    `U.tau0` and displaces the marker by at most `U.ell0`, then any `n`-step
    reach obeys `rad y - rad x ≤ U.c * (time y - time x)`, with no `n` in the
    statement. -/
theorem cone_bound_export
    (K : Causality.Kinematics α) (U : Constants.RSUnits) (time rad : α → ℝ)
    (step_time : ∀ {y z}, K.step y z → time z = time y + U.tau0)
    (step_rad : ∀ {y z}, K.step y z → rad z ≤ rad y + U.ell0)
    {n x y} (h : Causality.ReachN K n x y) :
    rad y - rad x ≤ U.c * (time y - time x) := by
  have H : LightCone.StepBounds (toLocal K) U time rad :=
    { step_time := fun hs => step_time hs
      step_rad := fun hs => step_rad hs }
  exact LightCone.StepBounds.cone_bound H (reachN_toLocal h)

end ConeExport

end Verification
end IndisputableMonolith
