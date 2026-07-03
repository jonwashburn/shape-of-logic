import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.DirectProof

/-!
# Quartic-log counterexample

This module formalises the algebraic heart of the counterexample from the
Logic Functional Equation paper:

`C(x,y) = (log (x/y))^4`

has a continuous symmetric combiner on the nonnegative range,

`Φ(a,b) = 2a + 2b + 12 sqrt(a b)`,

but no constant `c` can make the square-root term equal to `c a b` for all
positive `a,b`.  Thus arbitrary continuous compositionality does not force
the RCL family; finite pairwise polynomial closure is essential.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

open Real

/-- The quartic-log comparison used as the counterexample. -/
noncomputable def quarticLogComparison : ComparisonOperator :=
  fun x y => (Real.log (x / y)) ^ (4 : Nat)

/-- The continuous non-polynomial combiner associated to the quartic-log
comparison on the nonnegative range. -/
noncomputable def quarticCombiner (a b : ℝ) : ℝ :=
  2 * a + 2 * b + 12 * Real.sqrt (a * b)

theorem quarticCombiner_symmetric :
    ∀ a b : ℝ, quarticCombiner a b = quarticCombiner b a := by
  intro a b
  unfold quarticCombiner
  rw [mul_comm a b]
  ring

theorem quarticCombiner_nonneg_on_nonneg :
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ quarticCombiner a b := by
  intro a b ha hb
  unfold quarticCombiner
  have h2a : 0 ≤ 2 * a := by positivity
  have h2b : 0 ≤ 2 * b := by positivity
  have hsqrt : 0 ≤ 12 * Real.sqrt (a * b) := by positivity
  linarith

/-- The square-root term in the quartic combiner cannot be represented by a
single bilinear coefficient `c*a*b` on all positive inputs. -/
theorem quartic_sqrt_term_not_bilinear :
    ¬ ∃ c : ℝ, ∀ a b : ℝ, 0 < a → 0 < b →
      12 * Real.sqrt (a * b) = c * a * b := by
  intro h
  rcases h with ⟨c, hc⟩
  have h11 := hc 1 1 (by norm_num) (by norm_num)
  have hc_eq : c = 12 := by
    norm_num [Real.sqrt_one] at h11
    linarith
  have h44 := hc 4 4 (by norm_num) (by norm_num)
  have hsqrt16 : Real.sqrt (4 * 4) = 4 := by
    norm_num
  rw [hsqrt16, hc_eq] at h44
  norm_num at h44

/-- Therefore the quartic combiner is not in the RCL bilinear family. -/
theorem quarticCombiner_not_rcl_family :
    ¬ ∃ c : ℝ, ∀ a b : ℝ, 0 < a → 0 < b →
      quarticCombiner a b = 2 * a + 2 * b + c * a * b := by
  intro h
  rcases h with ⟨c, hc⟩
  apply quartic_sqrt_term_not_bilinear
  refine ⟨c, ?_⟩
  intro a b ha hb
  have hab := hc a b ha hb
  unfold quarticCombiner at hab
  linarith

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith
