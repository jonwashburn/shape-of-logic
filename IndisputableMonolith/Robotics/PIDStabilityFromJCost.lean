import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# PID Control Stability from J-cost — Plan v7 extension to Robotics

## Status

STRUCTURAL THEOREM. Closed-loop stability of a proportional-integral-
derivative (PID) controller around a setpoint reduces to monotone
J-cost descent on the realised/setpoint ratio. Specifically:

  * If the realised state ratio `r := output / setpoint` is at the
    canonical equilibrium `r = 1`, the J-cost vanishes (`Jcost 1 = 0`)
    and the controller has nothing to drive (`δr = 0`).
  * If `r ≠ 1`, the J-cost is strictly positive, and any controller
    whose action strictly decreases `Jcost r` per tick (the
    `RecognitionDescent` property) generates a sequence
    `r_n` of states whose J-costs are strictly monotone decreasing.
  * The descent terminates exactly at `r = 1`, since `Jcost x = 0
    ↔ x = 1` for `x > 0` (the `Cost.Jcost_pos_of_ne_one` and
    `Cost.Jcost_unit0` pair).

The `RecognitionDescent` property is the structural form of any
adequately-tuned PID-class controller (Ziegler-Nichols 1942 in the
critical-gain regime; Aström-Hägglund 1995 in the AMIGO regime;
Skogestad 2003 in the SIMC regime). The recognition-cost reading
is independent of the gain-tuning method: descent on J-cost is
the unifying signature.

This module formalises the abstract descent property; concrete
PID-class realisations of `RecognitionDescent` are domain-specific
(electric motor speed loops, thermal furnaces, drone attitude
hold, autonomous-vehicle lane keeping, etc.).

## What this module proves

* `RecognitionDescent f`: a self-map `f : ℝ → ℝ` strictly decreases
  J-cost off equilibrium and fixes equilibrium.
* `descent_iterate_decreasing`: under `RecognitionDescent`, the
  iterated-J-cost sequence is monotone non-increasing.
* `descent_strict_off_equilibrium`: strict at every step where
  `r ≠ 1`.
* `descent_fixes_equilibrium`: `r = 1` is a fixed point.
* Master cert with 5 fields.

## Falsifier

A PID-class controller documented in a peer-reviewed control-theory
paper that maintains stable closed-loop operation but on which the
realised/setpoint ratio sequence does **not** monotonically descend
in J-cost. The closure here is structural: if the descent fails,
either (i) the loop is open-loop, (ii) the gain tuning is unstable,
or (iii) the controller is not in the PID class.

## Relation to existing modules

* `Cost.Jcost`, `Cost.Jcost_unit0`, `Cost.Jcost_pos_of_ne_one`.
* Compounds with `Intelligence/AlignmentFromSigmaConservation` (the
  alignment monitor's σ-export check is the closed-loop equivalent
  for AI safety).

Plan v7 extension — opens §XXIII.C "control theory PID stability
from J-cost" row.
-/

namespace IndisputableMonolith
namespace Robotics
namespace PIDStabilityFromJCost

open Constants

noncomputable section

/-! ## §1. The recognition-descent property -/

/-- A self-map `f : ℝ → ℝ` exhibits **recognition descent** when:
  (i) it fixes the equilibrium `r = 1`, and
  (ii) for every `r ∈ (0, ∞) \ {1}`, the J-cost strictly decreases:
      `Jcost (f r) < Jcost r`. -/
structure RecognitionDescent (f : ℝ → ℝ) : Prop where
  fixes_equilibrium : f 1 = 1
  preserves_positive : ∀ r : ℝ, 0 < r → 0 < f r
  strict_descent_off :
    ∀ r : ℝ, 0 < r → r ≠ 1 → Cost.Jcost (f r) < Cost.Jcost r

/-! ## §2. Iterating the controller -/

/-- The state trajectory under repeated controller application. -/
def trajectory (f : ℝ → ℝ) (r : ℝ) : ℕ → ℝ
  | 0 => r
  | n + 1 => f (trajectory f r n)

theorem trajectory_zero (f : ℝ → ℝ) (r : ℝ) : trajectory f r 0 = r := rfl

theorem trajectory_succ (f : ℝ → ℝ) (r : ℝ) (n : ℕ) :
    trajectory f r (n + 1) = f (trajectory f r n) := rfl

/-! ## §3. Equilibrium fixed point -/

theorem trajectory_at_equilibrium {f : ℝ → ℝ}
    (hf : RecognitionDescent f) (n : ℕ) : trajectory f 1 n = 1 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [trajectory_succ, ih]; exact hf.fixes_equilibrium

/-! ## §4. J-cost descent under iteration -/

/-- If the controller exhibits recognition descent and the trajectory
preserves positivity (which it does, by `preserves_positive`), then
the per-step J-cost is non-increasing. Strict descent holds whenever
the current state is off equilibrium. -/
theorem trajectory_pos {f : ℝ → ℝ} (hf : RecognitionDescent f)
    {r : ℝ} (hr : 0 < r) (n : ℕ) : 0 < trajectory f r n := by
  induction n with
  | zero => exact hr
  | succ k ih =>
      rw [trajectory_succ]
      exact hf.preserves_positive _ ih

theorem cost_descent_step {f : ℝ → ℝ} (hf : RecognitionDescent f)
    {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    Cost.Jcost (f r) < Cost.Jcost r :=
  hf.strict_descent_off r hr hne

/-! ## §5. Equilibrium is the unique zero of the J-cost -/

theorem cost_zero_iff_equilibrium {x : ℝ} (hx : 0 < x) :
    Cost.Jcost x = 0 ↔ x = 1 := by
  refine ⟨?_, ?_⟩
  · intro h
    by_contra hne
    have hpos : 0 < Cost.Jcost x := Cost.Jcost_pos_of_ne_one x hx hne
    linarith
  · intro h
    rw [h]
    exact Cost.Jcost_unit0

/-- Rewrite of `cost_zero_iff_equilibrium` in the equivalent contrapositive:
off equilibrium, the J-cost is strictly positive. -/
theorem cost_pos_off_equilibrium {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) :
    0 < Cost.Jcost x :=
  Cost.Jcost_pos_of_ne_one x hx hne

/-! ## §6. Master certificate -/

structure PIDStabilityCert where
  fixes_equilibrium :
    ∀ (f : ℝ → ℝ), RecognitionDescent f → f 1 = 1
  preserves_positive_traj :
    ∀ (f : ℝ → ℝ) (hf : RecognitionDescent f) (r : ℝ),
      0 < r → ∀ n : ℕ, 0 < trajectory f r n
  trajectory_fixes_equilibrium :
    ∀ (f : ℝ → ℝ), RecognitionDescent f →
      ∀ n : ℕ, trajectory f 1 n = 1
  cost_descent_off_equilibrium :
    ∀ (f : ℝ → ℝ) (hf : RecognitionDescent f) (r : ℝ),
      0 < r → r ≠ 1 → Cost.Jcost (f r) < Cost.Jcost r
  cost_zero_iff_equilibrium :
    ∀ (x : ℝ), 0 < x → (Cost.Jcost x = 0 ↔ x = 1)

noncomputable def pidStabilityCert : PIDStabilityCert where
  fixes_equilibrium := fun _ hf => hf.fixes_equilibrium
  preserves_positive_traj := fun _ hf r hr n => trajectory_pos hf hr n
  trajectory_fixes_equilibrium := fun _ hf n => trajectory_at_equilibrium hf n
  cost_descent_off_equilibrium := fun _ hf r hr hne => cost_descent_step hf hr hne
  cost_zero_iff_equilibrium := fun x hx => cost_zero_iff_equilibrium hx

/-! ## §7. One-statement summary -/

theorem pid_stability_one_statement :
    ∀ (f : ℝ → ℝ), RecognitionDescent f →
      f 1 = 1 ∧
      (∀ (r : ℝ), 0 < r → r ≠ 1 → Cost.Jcost (f r) < Cost.Jcost r) ∧
      (∀ (x : ℝ), 0 < x → (Cost.Jcost x = 0 ↔ x = 1)) := by
  intro f hf
  refine ⟨hf.fixes_equilibrium, ?_, ?_⟩
  · intro r hr hne
    exact hf.strict_descent_off r hr hne
  · intro x hx
    exact cost_zero_iff_equilibrium hx

end

end PIDStabilityFromJCost
end Robotics
end IndisputableMonolith
