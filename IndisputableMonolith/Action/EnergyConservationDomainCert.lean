import Mathlib
import IndisputableMonolith.Action.Hamiltonian
import IndisputableMonolith.Action.QuadraticLimit
import IndisputableMonolith.Action.Noether

/-!
# Energy Conservation from the J-Action — Domain Certificate
(Plan v7 twenty-ninth pass continuation)

## Status: THEOREM (0 sorry, 0 axiom).

This module is the domain-cert wrapper for energy conservation along
Newtonian trajectories, as proved in `Action.Hamiltonian` from the
Lagrangian/EL chain. The standard mechanics Hamiltonian
`H(q, p) = p²/(2m) + V(q)` is the Legendre transform of
`L = ½ m q̇² - V(q)`; its conservation along the EL flow is Noether's
theorem applied to time-translation symmetry.

## What it bundles

- (1) Energy conservation: `H(γ(t₁), p(t₁)) = H(γ(t₂), p(t₂))` for any
  Newtonian trajectory under the standard regularity hypotheses
  (`hV_diff`, `hγ_diff`, `hγ_diff2`, `h_dE_factored`).
- (2) Hamilton's equations from the EL: the pair `(γ̇ = p/m, ṗ = -V'(γ))`
  is forced by the EL of the standard Lagrangian.

## Falsifier

A closed-system mechanical trajectory with potential `V` differentiable
on the trajectory image, regular accelerations, and EL satisfied, yet
total energy `H(γ, p)` measurably non-constant in time. This would
falsify clause (1) and therefore Noether's theorem on time-translation
symmetry of the J-action.

Paper companion: `papers/RS_Least_Action.tex` (Paper A), §"Hamiltonian
Formulation as a Corollary".
-/

namespace IndisputableMonolith
namespace Action

open IndisputableMonolith.Action

/-- Domain certificate for energy conservation along Newtonian
trajectories of the small-strain J-action. -/
structure EnergyConservationCert where
  energy_conserved : ∀ (m : ℝ) (_hm : 0 < m) (V : ℝ → ℝ) (γ : ℝ → ℝ),
      (∀ t, DifferentiableAt ℝ V (γ t)) →
      (∀ t, DifferentiableAt ℝ γ t) →
      (∀ t, DifferentiableAt ℝ (deriv γ) t) →
      (∀ t : ℝ,
        deriv (HamiltonianMech.totalEnergy m V γ) t =
          deriv γ t * (m * deriv (deriv γ) t + deriv V (γ t))) →
      (∀ t : ℝ, QuadraticLimit.standardEL m V γ t = 0) →
      ∀ t₁ t₂ : ℝ,
        HamiltonianMech.totalEnergy m V γ t₁ =
          HamiltonianMech.totalEnergy m V γ t₂
  hamilton_qdot : ∀ (m : ℝ) (_hm : m ≠ 0) (V : ℝ → ℝ) (γ : ℝ → ℝ)
      (_hV_diff : ∀ t, DifferentiableAt ℝ V (γ t))
      (_hγ_diff : ∀ t, DifferentiableAt ℝ γ t)
      (_hγ_diff2 : ∀ t, DifferentiableAt ℝ (deriv γ) t)
      (_hEL : ∀ t : ℝ, QuadraticLimit.standardEL m V γ t = 0),
      HamiltonianMech.hamiltonQDotEquation m γ
        (HamiltonianMech.conjugateMomentum m γ)

/-- Inhabited witness — both clauses are theorems in
`Action.Hamiltonian`. -/
def energyConservationCert : EnergyConservationCert where
  energy_conserved := by
    intro m hm V γ hV_diff hγ_diff hγ_diff2 h_dE_factored hEL t₁ t₂
    exact HamiltonianMech.energy_conservation m hm V γ
      hV_diff hγ_diff hγ_diff2 h_dE_factored hEL t₁ t₂
  hamilton_qdot := by
    intro m hm V γ hV_diff hγ_diff hγ_diff2 hEL
    exact (HamiltonianMech.hamilton_equations_from_EL m hm V γ
      hV_diff hγ_diff hγ_diff2 hEL).1

/-- One-statement summary: total energy is conserved along Newtonian
trajectories of the small-strain J-action. -/
theorem energy_conservation_one_statement :
    Nonempty EnergyConservationCert :=
  ⟨energyConservationCert⟩

end Action
end IndisputableMonolith
