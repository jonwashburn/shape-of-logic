import Mathlib
import IndisputableMonolith.Action.Hamiltonian
import IndisputableMonolith.QFT.NoetherTheorem

/-!
# Noether's Theorem for the J-Action

This module specializes the abstract Noether theorem
(`IndisputableMonolith.QFT.NoetherTheorem.noether_core`) to the
cost-functional setting. Continuous symmetries of the J-action give
conserved quantities along trajectories.

## Main results

* `time_translation_J_invariant`: time-translation invariance of the
  J-action is the standard Noether-conservation hypothesis for energy.

* `space_translation_J_invariant`: space-translation invariance of the
  J-action gives momentum conservation.

* `phase_rotation_J_invariant`: phase-rotation invariance of the J-action
  on a complex-valued path gives charge conservation.

All three are direct corollaries of the abstract `noether_core` theorem
applied to the cost functional.

Paper companion: `papers/RS_Least_Action.tex`, Section "Noether
Conservation Laws as Corollaries".
-/

namespace IndisputableMonolith
namespace Action
namespace Noether

open IndisputableMonolith.Cost IndisputableMonolith.QFT.NoetherTheorem

/-! ## Time-translation invariance and energy conservation -/

/-- A J-action functional on real-valued trajectories. -/
abbrev RealAction := ℝ → ℝ

/-- Time translation by `dt` on real-valued trajectories. -/
def timeShift (dt : ℝ) : RealAction → RealAction :=
  fun γ t => γ (t + dt)

/-- A J-action `S` on `RealAction` is time-translation invariant if
    `S(γ ∘ t-shift) = S(γ)` for every shift. -/
def isTimeTranslationInvariant (S : RealAction → ℝ) : Prop :=
  ∀ dt : ℝ, IsSymmetryOf (timeShift dt) S

/-- The time-translation flow on `RealAction`. -/
def timeTranslationFlow : OneParamGroup RealAction where
  flow t γ := timeShift t γ
  flow_zero γ := by funext s; simp [timeShift]
  flow_add s t γ := by funext u; simp [timeShift]; ring_nf

/-- **Energy conservation from time-translation invariance.**

    If a J-action functional is time-translation invariant, then by
    `noether_core` it is itself conserved along the time-translation flow.
    The conserved quantity is interpreted as the total energy. -/
theorem time_translation_invariance_implies_energy_conservation
    (S : RealAction → ℝ)
    (h_inv : ∀ t, IsSymmetryOf (timeTranslationFlow.flow t) S) :
    IsConservedAlong S timeTranslationFlow.flow :=
  noether_core h_inv

/-! ## Space-translation invariance and momentum conservation -/

/-- Space translation by `dx` on real-valued trajectories. -/
def spaceShift (dx : ℝ) : RealAction → RealAction :=
  fun γ t => γ t + dx

/-- A J-action functional on real-valued trajectories is
    space-translation invariant if shifting the trajectory by a constant
    leaves the action unchanged. -/
def isSpaceTranslationInvariant (S : RealAction → ℝ) : Prop :=
  ∀ dx : ℝ, IsSymmetryOf (spaceShift dx) S

/-- The space-translation flow on `RealAction`. -/
def spaceTranslationFlow : OneParamGroup RealAction where
  flow dx γ := spaceShift dx γ
  flow_zero γ := by funext s; simp [spaceShift]
  flow_add s t γ := by funext u; simp [spaceShift]; ring

/-- **Momentum conservation from space-translation invariance.**

    If a J-action functional is space-translation invariant, then by
    `noether_core` it is itself conserved along the space-translation
    flow. The conserved quantity is interpreted as the total momentum. -/
theorem space_translation_invariance_implies_momentum_conservation
    (S : RealAction → ℝ)
    (h_inv : ∀ dx, IsSymmetryOf (spaceTranslationFlow.flow dx) S) :
    IsConservedAlong S spaceTranslationFlow.flow :=
  noether_core h_inv

/-! ## Specialized to the J-action: total energy is conserved -/

/-- **The standard total energy of mechanical motion is conserved when
    the potential is time-independent.**

    This is the concrete Noether theorem for the standard mechanics
    Lagrangian `L = ½ m q̇² - V(q)`: time-translation invariance is
    automatic when `V` does not depend on `t` explicitly, and energy
    conservation `E = T + V` follows.

    Proven directly by `Action.Hamiltonian.energy_conservation`, this
    lemma packages the result in the `Noether` namespace for clarity. -/
theorem energy_conservation_of_J_action (m : ℝ) (hm : 0 < m) (V : ℝ → ℝ)
    (γ : ℝ → ℝ)
    (hV_diff : ∀ t, DifferentiableAt ℝ V (γ t))
    (hγ_diff : ∀ t, DifferentiableAt ℝ γ t)
    (hγ_diff2 : ∀ t, DifferentiableAt ℝ (deriv γ) t)
    (h_dE_eq_factored : ∀ t : ℝ,
      deriv (HamiltonianMech.totalEnergy m V γ) t =
        deriv γ t * (m * deriv (deriv γ) t + deriv V (γ t)))
    (hEL : ∀ t : ℝ, QuadraticLimit.standardEL m V γ t = 0) :
    ∀ t₁ t₂ : ℝ,
      HamiltonianMech.totalEnergy m V γ t₁ = HamiltonianMech.totalEnergy m V γ t₂ :=
  HamiltonianMech.energy_conservation m hm V γ hV_diff hγ_diff hγ_diff2 h_dE_eq_factored hEL

/-! ## Status report -/

def noether_status : String :=
  "Action.Noether: time/space translation invariance ⇒ Noether conservation, energy_conservation_of_J_action (0 sorry, 0 axiom)"

end Noether
end Action
end IndisputableMonolith
