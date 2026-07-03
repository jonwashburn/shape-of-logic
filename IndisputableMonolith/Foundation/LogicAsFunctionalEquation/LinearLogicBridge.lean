import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.CountOnceComparison

/-!
# Resource-sensitive syntax for counted-once comparison

This module formalises the normal-form version of counted-once resource
syntax.  Each constituent comparison may appear at most once, so the only
scalar monomials are `1`, `u`, `v`, and `u*v`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

/-- Normal-form counted-once resource expressions.  The constructor `both`
represents the joint interaction `u*v`; there are no constructors for `u^2`,
`v^2`, square roots, branch choices, or infinite series. -/
inductive CountedOnceResourceExpr where
  | const : ℝ → CountedOnceResourceExpr
  | atomU : CountedOnceResourceExpr
  | atomV : CountedOnceResourceExpr
  | both : CountedOnceResourceExpr
  | add : CountedOnceResourceExpr → CountedOnceResourceExpr → CountedOnceResourceExpr
  | scale : ℝ → CountedOnceResourceExpr → CountedOnceResourceExpr

namespace CountedOnceResourceExpr

/-- Evaluation of a counted-once resource expression. -/
def eval : CountedOnceResourceExpr → ℝ → ℝ → ℝ
  | const a, _, _ => a
  | atomU, u, _ => u
  | atomV, _, v => v
  | both, u, v => u * v
  | add e f, u, v => eval e u v + eval f u v
  | scale k e, u, v => k * eval e u v

/-- A semantic bi-affine representation. -/
def HasBiAffineForm (e : CountedOnceResourceExpr) : Prop :=
  ∃ a b c d : ℝ, ∀ u v, eval e u v = a + b*u + c*v + d*u*v

/-- Every counted-once resource expression is bi-affine. -/
theorem counted_once_expr_biaffine :
    ∀ e : CountedOnceResourceExpr, HasBiAffineForm e := by
  intro e
  induction e with
  | const a =>
      refine ⟨a, 0, 0, 0, ?_⟩
      intro u v
      simp [eval]
  | atomU =>
      refine ⟨0, 1, 0, 0, ?_⟩
      intro u v
      simp [eval]
  | atomV =>
      refine ⟨0, 0, 1, 0, ?_⟩
      intro u v
      simp [eval]
  | both =>
      refine ⟨0, 0, 0, 1, ?_⟩
      intro u v
      simp [eval]
  | add e f ihe ihf =>
      rcases ihe with ⟨a₁,b₁,c₁,d₁,h₁⟩
      rcases ihf with ⟨a₂,b₂,c₂,d₂,h₂⟩
      refine ⟨a₁+a₂, b₁+b₂, c₁+c₂, d₁+d₂, ?_⟩
      intro u v
      simp [eval, h₁ u v, h₂ u v]
      ring
  | scale k e ihe =>
      rcases ihe with ⟨a,b,c,d,h⟩
      refine ⟨k*a, k*b, k*c, k*d, ?_⟩
      intro u v
      simp [eval, h u v]
      ring

/-- A counted-once resource expression induces a counted-once combiner. -/
theorem expr_induces_counted_once_combiner
    (e : CountedOnceResourceExpr) :
    CountedOnceCombiner (fun u v => eval e u v) := by
  exact counted_once_expr_biaffine e

/-- Searchable alias: resource-linearity gives bi-affinity. -/
theorem resource_linearity_gives_biaffinity
    (e : CountedOnceResourceExpr) :
    HasBiAffineForm e :=
  counted_once_expr_biaffine e

end CountedOnceResourceExpr

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith
