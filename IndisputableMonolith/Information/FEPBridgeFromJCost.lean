import Mathlib
import IndisputableMonolith.Cost

/-!
# FEP Bridge from J-Cost

This module is the first Lean anchor for comparing Recognition Science with
Friston-style free-energy-principle (FEP) mechanics.

The result is deliberately local.  FEP uses KL / variational free energy,
while RS uses the reciprocal cost

`J(x) = (x + x⁻¹) / 2 - 1`.

In log-ratio coordinates `x = exp u`, RS gives `J(exp u) = cosh u - 1`.
Therefore the local quadratic contact with the Fisher/KL geometry is exact
at the level of value, first derivative, and second derivative at equilibrium.

This does not yet derive Markov blankets or Bayesian filtering from RCL.  It
marks the theorem-grade part of the bridge and names the remaining structure.
-/

namespace IndisputableMonolith
namespace Information
namespace FEPBridgeFromJCost

open Cost

noncomputable section

/-! ## Local KL / Fisher Contact -/

/-- The local quadratic proxy for KL divergence in one log-ratio coordinate. -/
noncomputable def klQuadratic (u : ℝ) : ℝ := u ^ 2 / 2

/-- In log coordinates, reciprocal J-cost is exactly `cosh u - 1`. -/
theorem jcost_log_exact (u : ℝ) :
    Jlog u = Real.cosh u - 1 :=
  Jlog_as_cosh u

/-- The KL quadratic has zero value at equilibrium. -/
@[simp] theorem klQuadratic_zero : klQuadratic 0 = 0 := by
  simp [klQuadratic]

/-- The KL quadratic has zero first derivative at equilibrium. -/
theorem hasDerivAt_klQuadratic (u : ℝ) :
    HasDerivAt klQuadratic u u := by
  unfold klQuadratic
  have hsq : HasDerivAt (fun v : ℝ => v ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u)
  have h := hsq.div_const 2
  convert h using 1
  ring

@[simp] theorem deriv_klQuadratic_zero : deriv klQuadratic 0 = 0 := by
  simpa using (hasDerivAt_klQuadratic 0).deriv

/-- The second derivative of the KL quadratic at equilibrium is `1`. -/
theorem hasDerivAt_deriv_klQuadratic_zero :
    HasDerivAt (deriv klQuadratic) 1 0 := by
  have h_eq : deriv klQuadratic = fun u : ℝ => u := by
    funext u
    exact (hasDerivAt_klQuadratic u).deriv
  rw [h_eq]
  simpa using (hasDerivAt_id 0)

/-- The second derivative of log-coordinate J-cost at equilibrium is `1`. -/
theorem hasDerivAt_deriv_Jlog_zero :
    HasDerivAt (deriv Jlog) 1 0 := by
  have h_eq : deriv Jlog = Real.sinh := by
    funext u
    exact (hasDerivAt_Jlog u).deriv
  rw [h_eq]
  simpa using (Real.hasDerivAt_sinh 0)

/-- RS reciprocal cost and the KL quadratic have the same Fisher curvature
at equilibrium.  This is the exact local crossover with FEP-style free energy.
-/
theorem jcost_kl_same_second_order_at_equilibrium :
    Jlog 0 = klQuadratic 0 ∧
    deriv Jlog 0 = deriv klQuadratic 0 ∧
    deriv (deriv Jlog) 0 = deriv (deriv klQuadratic) 0 := by
  constructor
  · simp [Jlog_zero]
  constructor
  · simp
  · have hJ := hasDerivAt_deriv_Jlog_zero.deriv
    have hK := hasDerivAt_deriv_klQuadratic_zero.deriv
    rw [hJ, hK]

/-! ## Markov-Blanket Scaffold -/

/-- The four FEP state classes in the particular partition. -/
inductive FEPStateClass where
  | external
  | sensory
  | active
  | internal
  deriving DecidableEq, Repr, BEq, Fintype

/-- A sparse coupling relation between FEP state classes. -/
abbrev Coupling := FEPStateClass → FEPStateClass → Prop

/-- The FEP Markov-blanket sparsity condition: no direct internal-external
coupling in either direction.  Coupling must pass through sensory/active
boundary states. -/
def HasMarkovBlanketSparsity (C : Coupling) : Prop :=
  ¬ C FEPStateClass.internal FEPStateClass.external ∧
  ¬ C FEPStateClass.external FEPStateClass.internal

/-- Recognition-ledger boundary condition with the same sparse-coupling shape.
This is the RS-side object that future work must derive from RCL/ledger forcing,
instead of assuming as a partition. -/
def HasLedgerBoundarySparsity (C : Coupling) : Prop :=
  ¬ C FEPStateClass.internal FEPStateClass.external ∧
  ¬ C FEPStateClass.external FEPStateClass.internal

/-- The current bridge between FEP blankets and RS ledger boundaries is a
shape theorem: the two sparsity predicates are definitionally the same.

The hard follow-on is deriving `HasLedgerBoundarySparsity` from RCL/J-cost
dynamics for a concrete recognition field.
-/
theorem markov_blanket_sparsity_iff_ledger_boundary_sparsity (C : Coupling) :
    HasMarkovBlanketSparsity C ↔ HasLedgerBoundarySparsity C := by
  rfl

/-- A compact certificate for the theorem-grade part of the FEP bridge. -/
structure FEPBridgeLocalCert where
  exact_log_cost : ∀ u : ℝ, Jlog u = Real.cosh u - 1
  fisher_contact :
    Jlog 0 = klQuadratic 0 ∧
    deriv Jlog 0 = deriv klQuadratic 0 ∧
    deriv (deriv Jlog) 0 = deriv (deriv klQuadratic) 0
  blanket_boundary_shape :
    ∀ C : Coupling, HasMarkovBlanketSparsity C ↔ HasLedgerBoundarySparsity C

/-- The local FEP/RS bridge certificate. -/
noncomputable def fepBridgeLocalCert : FEPBridgeLocalCert where
  exact_log_cost := jcost_log_exact
  fisher_contact := jcost_kl_same_second_order_at_equilibrium
  blanket_boundary_shape := markov_blanket_sparsity_iff_ledger_boundary_sparsity

theorem fep_bridge_local_cert_holds : Nonempty FEPBridgeLocalCert :=
  ⟨fepBridgeLocalCert⟩

end
end FEPBridgeFromJCost
end Information
end IndisputableMonolith
