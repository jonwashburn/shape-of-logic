import Mathlib
import IndisputableMonolith.NumberTheory.VisibilityFromFloorBudget
import IndisputableMonolith.NumberTheory.PhaseBudgetEngineFromRS

/-!
# Minimal Visibility Engine

Repackages the bounded visibility engine without the visibility field.
That field is now a theorem (`hits_balanced_phase_of_floor_and_budget`), so
only the explicit RS-physical inputs (stable budget, uniform `KTheta` floor)
are required.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace MinimalVisibilityEngine

open BoundedPhaseVisibility
open VisibilityFromFloorBudget
open PhaseBudgetEngineFromRS
open ErdosStrausRotationHierarchy
open SubsetProductPhase
open ErdosStrausBoxPhase
open T1PhaseBudgetBound
open scoped Classical

/-- A minimal visibility engine carries only KTheta floor hypothesis and stable budget.  No
visibility field. -/
structure MinimalEngine where
  costOf : ℕ → ℕ → ℝ
  stable :
    ∀ n : ℕ, NonIdentityReciprocal n → StableIntegerLedgerBudget n (costOf n)
  floor :
    ∀ n : ℕ, NonIdentityReciprocal n → KThetaFailureFloorHypothesis n (costOf n)

/-- A minimal engine yields a successful admissible gate for every
nonidentity reciprocal ledger. -/
theorem hits_admissible_gate (engine : MinimalEngine)
    {n : ℕ} (hn : NonIdentityReciprocal n) :
    ∃ c : ℕ, AdmissibleHardGate c ∧ HitsBalancedPhase n c :=
  hits_balanced_phase_of_floor_and_budget hn (engine.stable n hn) (engine.floor n hn)

/-- A successful admissible gate gives a `SubsetProductPhaseHit` witness. -/
theorem subset_product_hit_of_minimal (engine : MinimalEngine)
    {n : ℕ} (hn : NonIdentityReciprocal n) :
    ∃ c : ℕ, AdmissibleHardGate c ∧ Nonempty (SubsetProductPhaseHit n c) := by
  classical
  rcases hits_admissible_gate engine hn with ⟨c, hc, hhit⟩
  exact ⟨c, hc, subsetProductPhaseHit_of_hitsBalancedPhase hhit⟩

/-- A minimal visibility engine (KTheta floor hypothesis + stable budget) supplies the
`PhaseBudgetEngine` directly.  The bound field receives the gate witness
itself, so the membership check is satisfied by reflexivity. -/
noncomputable def phaseBudgetEngine (engine : MinimalEngine) :
    PhaseBudgetToErdosStraus.PhaseBudgetEngine where
  bound := fun n =>
    if h : ResidualTrap n then
      Classical.choose (subset_product_hit_of_minimal engine
        (nonIdentityReciprocal_of_residualTrap h))
    else 0
  supplies_hit := by
    intro n hntrap
    have hn : NonIdentityReciprocal n :=
      nonIdentityReciprocal_of_residualTrap hntrap
    have hex := subset_product_hit_of_minimal engine hn
    refine ⟨Classical.choose hex, ?_, ?_, ?_⟩
    · simp [hntrap]
    · exact (Classical.choose_spec hex).1
    · exact (Classical.choose_spec hex).2

/-- Final closure: a minimal visibility engine solves the residual class. -/
theorem erdos_straus_residual_from_minimal_engine
    (engine : MinimalEngine)
    {n : ℕ} (hn : ResidualTrap n) :
    ErdosStrausRCL.HasRationalErdosStrausRepr (n : ℚ) :=
  PhaseBudgetToErdosStraus.erdos_straus_residual_from_phaseBudget
    (phaseBudgetEngine engine) hn

end MinimalVisibilityEngine
end NumberTheory
end IndisputableMonolith
