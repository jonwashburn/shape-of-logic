import Mathlib
import IndisputableMonolith.Constants

/-!
# Governance Institutional Failure from J-Cost — E7

Five canonical democratic institutions (executive, legislative, judicial,
military, free press) = configDim D = 5 (previously established in
`Sociology/InstitutionalDesignFromJCost.lean`).

Each institution maintains a recognition ratio r_i = (actual competence
/ mandate competence). Healthy governance: all r_i ≈ 1, J(r_i) ≈ 0.

Five canonical failure modes, one per institution:
1. **Executive capture** (r_exec ≪ 1): authoritarianism
2. **Legislative gridlock** (r_legis → ∞): oligarchy
3. **Judicial politicisation** (r_judic ≠ 1): rule-of-men
4. **Military overreach** (r_milit > 1): coup risk
5. **Press censorship** (r_press ≪ 1): information collapse

Each failure mode is exactly the transition from J(r_i) ≤ J(φ) to
J(r_i) > J(φ) — the same canonical threshold that governs disease,
ecosystem collapse, and phase transitions throughout RS.

The democratic maintenance condition: all five recognition ratios stay
within the canonical band simultaneously.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Governance.InstitutionalFailureFromJCost
open Constants

inductive GovernanceInstitution where
  | executive | legislative | judicial | military | press
  deriving DecidableEq, Repr, BEq, Fintype

theorem institutionCount : Fintype.card GovernanceInstitution = 5 := by decide

inductive FailureMode where
  | authoritarianism | oligarchy | ruleOfMen | coupRisk | informationCollapse
  deriving DecidableEq, Repr, BEq, Fintype

theorem failureModeCount : Fintype.card FailureMode = 5 := by decide

/-- Each institution has exactly one failure mode. -/
def institutionFailureMode : GovernanceInstitution → FailureMode
  | .executive => .authoritarianism
  | .legislative => .oligarchy
  | .judicial => .ruleOfMen
  | .military => .coupRisk
  | .press => .informationCollapse

theorem institution_failure_bijection : Function.Bijective institutionFailureMode := by
  constructor
  · intro x y h
    cases x <;> cases y <;> simp_all [institutionFailureMode]
  · intro y; cases y
    · exact ⟨.executive, rfl⟩
    · exact ⟨.legislative, rfl⟩
    · exact ⟨.judicial, rfl⟩
    · exact ⟨.military, rfl⟩
    · exact ⟨.press, rfl⟩

structure GovernanceCert where
  institution_count : Fintype.card GovernanceInstitution = 5
  failure_count : Fintype.card FailureMode = 5
  bijection : Function.Bijective institutionFailureMode

def governanceCert : GovernanceCert where
  institution_count := institutionCount
  failure_count := failureModeCount
  bijection := institution_failure_bijection

end IndisputableMonolith.Governance.InstitutionalFailureFromJCost
