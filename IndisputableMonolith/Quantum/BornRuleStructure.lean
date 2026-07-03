import Mathlib
import IndisputableMonolith.Quantum.BornRule

namespace IndisputableMonolith
namespace Quantum
namespace BornRuleStructure

open BornRule

/-- Structural Born-rule content: probability weights are nonnegative. -/
def born_rule_from_ledger : Prop := ∀ ψ : ℂ, 0 ≤ Complex.normSq ψ

theorem born_rule_structure : born_rule_from_ledger := by
  intro ψ
  exact born_rule_consistent ψ

/-- Phase cancellation in probabilities: global phase does not alter `|ψ|²`. -/
theorem born_rule_phase_cancels (r θ : ℝ) :
    Complex.normSq ((r : ℂ) * Complex.exp (θ * Complex.I)) = r ^ 2 :=
  born_rule_phase_independent r θ

/-- Born-rule structure gives nonnegativity at any specific amplitude. -/
theorem born_rule_nonnegative_at (h : born_rule_from_ledger) (ψ : ℂ) :
    0 ≤ Complex.normSq ψ :=
  h ψ

/-- Born-rule structure implies nonnegative probability weight at each amplitude. -/
theorem born_rule_implies_nonnegative (h : born_rule_from_ledger) (ψ : ℂ) :
    0 ≤ Complex.normSq ψ :=
  born_rule_nonnegative_at h ψ

end BornRuleStructure
end Quantum
end IndisputableMonolith
