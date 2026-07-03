import Mathlib
import IndisputableMonolith.Patterns

/-!
# Eight-Tick Discrete-Time Dynamics

This module formalizes the temporal side of the Navier--Stokes lattice program.
The main point is simple but important: once time is treated as discrete, an
8-step window becomes the natural stability unit, and certificates over one
window propagate to all later windows by iteration.
-/

namespace IndisputableMonolith
namespace NavierStokes
namespace EightTickDynamics

open Patterns

noncomputable section

/-- An abstract one-step discrete dynamics with a defect functional. -/
structure OneStepDynamics (α : Type) where
  step : α → α
  defect : α → ℝ
  defect_nonincreasing : ∀ s, defect (step s) ≤ defect s

/-- The 8-step evolution operator. -/
def step8 {α : Type} (dyn : OneStepDynamics α) : α → α :=
  dyn.step^[8]

/-- Iterating a one-step defect-nonincreasing map preserves defect monotonicity. -/
theorem iterate_defect_nonincreasing {α : Type} (dyn : OneStepDynamics α) :
    ∀ n s, dyn.defect ((dyn.step^[n]) s) ≤ dyn.defect s := by
  intro n
  induction n with
  | zero =>
      intro s
      simp
  | succ n ihn =>
      intro s
      rw [Function.iterate_succ_apply']
      exact le_trans (dyn.defect_nonincreasing ((dyn.step^[n]) s)) (ihn s)

/-- A single 8-tick window is defect-nonincreasing. -/
theorem step8_defect_nonincreasing {α : Type} (dyn : OneStepDynamics α) :
    ∀ s, dyn.defect (step8 dyn s) ≤ dyn.defect s := by
  intro s
  simpa [step8] using iterate_defect_nonincreasing dyn 8 s

/-- The 8-step dynamics itself is a one-step defect-nonincreasing system. -/
def windowDynamics {α : Type} (dyn : OneStepDynamics α) : OneStepDynamics α where
  step := step8 dyn
  defect := dyn.defect
  defect_nonincreasing := step8_defect_nonincreasing dyn

/-- Repeated 8-tick windows remain defect-nonincreasing. -/
theorem window_certificate_extends {α : Type} (dyn : OneStepDynamics α) :
    ∀ n s, dyn.defect (((step8 dyn)^[n]) s) ≤ dyn.defect s := by
  simpa [windowDynamics] using iterate_defect_nonincreasing (windowDynamics dyn)

/-- The pattern-level 8-tick cycle exists in D=3. -/
theorem eight_tick_cycle_exists : ∃ w : CompleteCover 3, w.period = 8 :=
  period_exactly_8

/-- Any full cover of 3-bit patterns needs at least 8 ticks. -/
theorem eight_tick_minimal {T : Nat}
    (pass : Fin T → Pattern 3) (covers : Function.Surjective pass) :
    8 ≤ T :=
  eight_tick_min pass covers

/-- A finite-window certificate for the 8-step operator. -/
structure EightTickCertificate (α : Type) where
  dyn : OneStepDynamics α
  initial : α
  one_window_bound :
    dyn.defect (step8 dyn initial) ≤ dyn.defect initial

/-- The one-window certificate propagates to every later 8-tick window. -/
theorem eight_tick_certificate_propagates {α : Type} (cert : EightTickCertificate α) :
    ∀ n, cert.dyn.defect (((step8 cert.dyn)^[n]) cert.initial) ≤
      cert.dyn.defect cert.initial :=
by
  intro n
  exact window_certificate_extends cert.dyn n cert.initial

end

end EightTickDynamics
end NavierStokes
end IndisputableMonolith
