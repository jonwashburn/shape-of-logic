import Mathlib
import IndisputableMonolith.NumberTheory.BoundedPhaseVisibility
import IndisputableMonolith.NumberTheory.SubsetProductPhase

/-!
# Visibility From Floor And Budget

The breakthrough step.  Given an explicit stable budget plus a uniform
positive failure floor at `KTheta`, derive that some admissible gate must
succeed for every nonidentity reciprocal ledger.

The argument is RS-physical: failed gates accumulate `KTheta` per gate; the
T1/RCL budget bounds the total; hence an admissible gate count larger than
`budget / KTheta` cannot all fail.

This converts `BoundedVisibilityEngine.visibility` from an assumption into
a theorem, conditional only on the budget and floor.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace VisibilityFromFloorBudget

open PhaseFailureCost
open T1PhaseBudgetBound
open UniformFailureFloor
open BoundedPhaseVisibility
open SubsetProductPhase
open ErdosStrausRotationHierarchy
open ErdosStrausBoxPhase
open scoped Classical

/-- Admissible gates `c ≡ 3 mod 4` of the form `4 * i + 3` for `i < k`. -/
def admissibleGatesByIndex (k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => 4 * i + 3)

theorem admissibleGatesByIndex_card (k : ℕ) :
    (admissibleGatesByIndex k).card = k := by
  unfold admissibleGatesByIndex
  rw [Finset.card_image_of_injective _ (fun i j hij => by
    have : 4 * i + 3 = 4 * j + 3 := hij
    omega)]
  exact Finset.card_range k

theorem admissibleGatesByIndex_admissible {k : ℕ}
    {c : ℕ} (hc : c ∈ admissibleGatesByIndex k) :
    AdmissibleHardGate c := by
  unfold admissibleGatesByIndex at hc
  rw [Finset.mem_image] at hc
  obtain ⟨i, _, rfl⟩ := hc
  show (4 * i + 3) % 4 = 3
  omega

/-- The breakthrough lemma.  From a stable budget and uniform `KTheta` floor,
some admissible gate fails to fail, i.e. `HitsBalancedPhase`. -/
theorem hits_balanced_phase_of_floor_and_budget
    {n : ℕ} (_hn : NonIdentityReciprocal n)
    {costOf : ℕ → ℝ}
    (stable : StableIntegerLedgerBudget n costOf)
    (floor : KThetaFailureFloorHypothesis n costOf) :
    ∃ c : ℕ, AdmissibleHardGate c ∧ HitsBalancedPhase n c := by
  classical
  -- Pick `k` so that `KTheta * k > budget`.
  obtain ⟨k, hk⟩ := exists_nat_gt (stable.budget / KTheta + 1)
  let S := admissibleGatesByIndex k
  -- Assume every admissible gate in S fails.
  by_contra hno
  push_neg at hno
  have hfails : ∀ c ∈ S, GateFails n c := by
    intro c hc
    exact hno c (admissibleGatesByIndex_admissible hc)
  have hlower :
      KTheta * (S.card : ℝ) ≤ cumulativeFailureCost n costOf S := by
    have := phase_failure_cost_lower_bound (n := n) (S := S)
      (costOf := costOf) (δ := KTheta)
      hfails (fun c hc => floor.floor c (hfails c hc))
    simpa [cumulativeFailureCost] using this
  have hupper := stable.bounds_all_finite_failures S
  have hbound : KTheta * (S.card : ℝ) ≤ stable.budget :=
    le_trans hlower hupper
  -- But `KTheta * k > budget`, so this is a contradiction.
  have hcard_eq : (S.card : ℝ) = (k : ℝ) := by
    rw [admissibleGatesByIndex_card]
  rw [hcard_eq] at hbound
  have hKTheta_pos : 0 < KTheta := KTheta_pos
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    have hk_real : (k : ℝ) > stable.budget / KTheta + 1 := hk
    have hbnonneg : 0 ≤ stable.budget / KTheta := by
      apply div_nonneg stable.budget_nonneg KTheta_nonneg
    linarith
  -- KTheta * k > KTheta * (budget/KTheta + 1) = budget + KTheta > budget.
  have hbudget_div : KTheta * (stable.budget / KTheta) = stable.budget := by
    field_simp [ne_of_gt KTheta_pos]
  have hKk_gt : KTheta * (k : ℝ) > stable.budget := by
    have hmul : KTheta * (k : ℝ) > KTheta * (stable.budget / KTheta + 1) := by
      apply mul_lt_mul_of_pos_left hk hKTheta_pos
    have heq : KTheta * (stable.budget / KTheta + 1)
              = stable.budget + KTheta := by
      rw [mul_add, mul_one, hbudget_div]
    linarith
  linarith

end VisibilityFromFloorBudget
end NumberTheory
end IndisputableMonolith
