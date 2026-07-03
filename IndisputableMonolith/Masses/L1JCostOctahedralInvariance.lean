import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Masses.L1bHyperoctahedralGroup
import IndisputableMonolith.Masses.L1UniformityFromOctahedral

namespace IndisputableMonolith
namespace Masses
namespace L1JCostOctahedralInvariance

open scoped BigOperators
open IndisputableMonolith.Cost
open IndisputableMonolith.Masses.L1bHyperoctahedralGroup
open IndisputableMonolith.Masses.L1bHyperoctahedralGroup.SignedPerm
open IndisputableMonolith.Masses.L1UniformityFromOctahedral
open IndisputableMonolith.Constants.AlphaDerivation (solid_angle_Q3)

/-!
# L1 J-cost octahedral invariance (MODEL → THEOREM lift, door L1-Test2)

This module discharges the residual MODEL floor of L1_Test2 by constructing
a non-vacuous J-cost functional on configurations `Fin 3 → ℝ` that is
genuinely invariant under the hyperoctahedral group `B3 = O_h`, and then
deriving the vertex uniformity as a corollary.

The key insight is that while the vertex action is transitive (forcing any
invariant vertex density to be constant), the configuration action is NOT
transitive, so a non-constant invariant functional on configurations is
non-vacuous. The vertex uniformity is then DERIVED from the J-cost symmetry
via the equivariant embedding of vertices into configurations.
-/

/-- The core J-cost functional on configurations: sum of per-coordinate J-costs
of the exponentiated coordinates. This is the non-vacuous object whose invariance
is a genuine symmetry of the recognition cost J. -/
noncomputable def Jcfg (v : Fin 3 → ℝ) : ℝ := ∑ i, Cost.Jcost (Real.exp (v i))

/-- Per-term sign-flip invariance: `Jcost(exp(-t)) = Jcost(exp t)`.
This follows from the closed form `Jcost(exp t) = (exp t + exp(-t))/2 - 1`
together with `exp(-(-t)) = exp t`. -/
lemma Jcost_exp_neg (t : ℝ) : Cost.Jcost (Real.exp (-t)) = Cost.Jcost (Real.exp t) := by
  rw [Cost.Jcost_exp, Cost.Jcost_exp, neg_neg]
  ring

/-- **Core invariance.** The J-cost functional is invariant under the
hyperoctahedral group action on configurations. The proof uses:
  (1) per-term sign-flip invariance `Jcost_exp_neg`, and
  (2) reindexing the sum by the permutation via `Equiv.sum_comp`. -/
theorem Jcfg_invariant : ∀ (g : SignedPerm) (v : Fin 3 → ℝ), Jcfg (g • v) = Jcfg v := by
  intro g v
  unfold Jcfg
  have h_term : ∀ i : Fin 3,
      Cost.Jcost (Real.exp ((g • v) i)) = Cost.Jcost (Real.exp (v (g.perm i))) := by
    intro i
    have hval : (g • v) i = if g.sign i then -(v (g.perm i)) else v (g.perm i) := rfl
    rw [hval]
    by_cases hs : g.sign i = true
    · rw [if_pos hs, Jcost_exp_neg]
    · rw [if_neg hs]
  rw [Finset.sum_congr rfl (fun i _ => h_term i)]
  exact Equiv.sum_comp g.perm (fun i => Cost.Jcost (Real.exp (v i)))

/-- **Non-vacuity.** The J-cost functional is non-constant: the zero
configuration has cost 0, while the all-ones configuration has positive cost. -/
theorem Jcfg_nonconstant : Jcfg (fun _ => (0:ℝ)) ≠ Jcfg (fun _ => (1:ℝ)) := by
  have hL : Jcfg (fun _ => (0:ℝ)) = 0 := by
    unfold Jcfg
    simp [Real.exp_zero, Cost.Jcost_unit0]
  have hR : Jcfg (fun _ => (1:ℝ)) = 3 * Cost.Jcost (Real.exp 1) := by
    unfold Jcfg
    simp only [Fin.sum_univ_three]
    ring
  have hexp_gt : (1:ℝ) < Real.exp 1 := by
    have h := Real.add_one_le_exp (1:ℝ)
    linarith
  have hpos : 0 < Cost.Jcost (Real.exp 1) := by
    apply Cost.Jcost_pos_of_ne_one
    · exact Real.exp_pos 1
    · exact ne_of_gt hexp_gt
  rw [hL, hR]
  exact ne_of_lt (by linarith [hpos] : (0:ℝ) < 3 * Cost.Jcost (Real.exp 1))

/-- The equivariant embedding of cube vertices into configurations:
`true ↦ -1`, `false ↦ 1`. -/
def embed (b : CubeVertex) : Fin 3 → ℝ := fun i => if b i then -1 else 1

/-- **Equivariance.** The embedding intertwines the vertex action and the
configuration action. -/
theorem embed_equivariant : ∀ (g : SignedPerm) (b : CubeVertex),
    embed (g • b) = g • (embed b) := by
  intro g b
  funext i
  have hL : embed (g • b) i
      = (if xor (g.sign i) (b (g.perm i)) then (-1:ℝ) else 1) := rfl
  have hR : (g • embed b) i
      = (if g.sign i then -(if b (g.perm i) then (-1:ℝ) else 1)
         else (if b (g.perm i) then (-1:ℝ) else 1)) := rfl
  rw [hL, hR]
  by_cases hs : g.sign i = true <;> by_cases hb : b (g.perm i) = true <;>
    simp [hs, hb]

/-- The vertex density induced by the J-cost functional. -/
noncomputable def d (b : CubeVertex) : ℝ := Jcfg (embed b)

/-- **Vertex invariance (discharges the floor).** The induced vertex density is
`O_h`-invariant, derived from the J-cost symmetry via equivariance. -/
theorem d_invariant : ∀ (g : SignedPerm) (b : CubeVertex), d (g • b) = d b := by
  intro g b
  unfold d
  rw [embed_equivariant, Jcfg_invariant]

/-- **Capstone.** Given the measure hypotheses of `uniform_reduction_from_invariance`,
the flux integral equals `solid_angle_Q3 * (d b0)`. -/
theorem uniform_reduction_from_jcost
    {m : CubeVertex → ℝ} {b0 : CubeVertex}
    (htot : ∑ v, m v = solid_angle_Q3) :
    ∑ v, m v * d v = solid_angle_Q3 * (d b0) := by
  exact uniform_reduction_from_invariance d_invariant b0 rfl htot

end L1JCostOctahedralInvariance
end Masses
end IndisputableMonolith
