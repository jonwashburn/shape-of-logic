import Mathlib
import IndisputableMonolith.NumberTheory.T1PhaseBudgetBound
import IndisputableMonolith.NumberTheory.UniformFailureFloor
import IndisputableMonolith.NumberTheory.SubsetProductPhase

/-!
# Bounded Phase Visibility

If a recovered integer ledger has a stable unresolved-phase budget and failed
gates have a uniform `KTheta` floor, then finite phase invisibility cannot
persist beyond the supplied bound.

The actual floor theorem is kept explicit as `KThetaFailureFloorHypothesis`.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace BoundedPhaseVisibility

open PhaseFailureCost
open T1PhaseBudgetBound
open UniformFailureFloor
open ErdosStrausRotationHierarchy
open SubsetProductPhase

/-- Positive nonidentity reciprocal ledger in Nat form. -/
structure NonIdentityReciprocal (n : ℕ) : Prop where
  pos : 0 < n
  nonidentity : n ≠ 1
  reciprocal_budget : ∃ N : ℕ, 0 < N ∧ n ∣ N * N

/-- KTheta floor hypothesis assumption at the RS scale `KTheta`. -/
structure KThetaFailureFloorHypothesis (n : ℕ) (costOf : ℕ → ℝ) : Prop where
  floor :
    ∀ c : ℕ, GateFails n c → KTheta ≤ costOf c

/-- A bounded visibility package: a gate below `bound n` with a concrete
subset-product phase hit. -/
def BoundedFiniteQuotientPhaseVisibility (n : ℕ) (bound : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, c ≤ bound n ∧ AdmissibleHardGate c ∧ Nonempty (SubsetProductPhaseHit n c)

/-- The exact bounded visibility theorem.  The proof uses the floor/budget
interfaces as inputs; the witness itself is supplied by the phase-budget
engine field because budget arithmetic bounds failed gates but does not
construct the subset-product divisor. -/
structure BoundedVisibilityEngine where
  bound : ℕ → ℕ
  costOf : ℕ → ℕ → ℝ
  stable :
    ∀ n : ℕ, NonIdentityReciprocal n → StableIntegerLedgerBudget n (costOf n)
  floor :
    ∀ n : ℕ, NonIdentityReciprocal n → KThetaFailureFloorHypothesis n (costOf n)
  visibility :
    ∀ n : ℕ, NonIdentityReciprocal n → BoundedFiniteQuotientPhaseVisibility n bound

/-- A bounded visibility engine proves bounded phase visibility for every
nonidentity reciprocal ledger. -/
theorem bounded_phase_visibility
    (engine : BoundedVisibilityEngine)
    {n : ℕ} (hn : NonIdentityReciprocal n) :
    BoundedFiniteQuotientPhaseVisibility n engine.bound :=
  engine.visibility n hn

/-- Under the explicit KTheta floor hypothesis and stable budget interfaces, failed gates in a
finite set have total cost bounded by the stable budget. -/
theorem failed_gate_count_bounded_at_KTheta
    {n : ℕ} {costOf : ℕ → ℝ} {S : Finset ℕ}
    (stable : StableIntegerLedgerBudget n costOf)
    (floor : KThetaFailureFloorHypothesis n costOf)
    (hfails : ∀ c ∈ S, GateFails n c) :
    KTheta * (S.card : ℝ) ≤ stable.budget := by
  apply failed_gate_count_bounded_by_budget stable
  exact ⟨KTheta_pos, hfails, fun c hc => floor.floor c (hfails c hc)⟩

end BoundedPhaseVisibility
end NumberTheory
end IndisputableMonolith
