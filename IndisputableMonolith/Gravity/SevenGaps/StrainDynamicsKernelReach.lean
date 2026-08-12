import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Cost.SymplecticAction
import IndisputableMonolith.Gravity.SevenGaps.DescentPrincipleUniversality

/-!
# How far the recognition kernel reaches: it fixes the cost, not the motion

## The question

The C2 bridge's stationarity premise is reduced to its weakest sufficient
form: the substrate's strain dynamics is continuous and strictly lowers
recognition cost at every state other than the least-cost state
(`DescentPrincipleUniversality`). This module asks whether that residue is
forced by the recognition kernel, and answers: no, and for a reason that is
structural rather than accidental.

## What the kernel says about cost

The kernel's cost content is exactly the premise package of
`law_of_logic_forces_jcost`: a cost is reciprocal, normalized, satisfies the
recognition composition law, is calibrated to unit log curvature, and is
continuous on the positive ratios. Those five premises force the cost to be
`J`, and `J` satisfies all five (`jcost_kernelCostContent`).

Every one of them is a statement about the cost assigned to a single ratio.
None quantifies over a map on the ratio ledger, over a sequence of postings,
or over anything that changes. The kernel fixes what a configuration costs.
It does not say how a configuration moves.

## The reach wall

That gap is not a formality, and the counterexample is not contrived: it is
the ledger's own reciprocal involution `x ↦ 1/x`, which in the strain
coordinate is `t ↦ -t`. Its invariance is precisely the reciprocity premise
that makes the cost `J` in the first place. It is continuous, it preserves
bare recognition cost exactly (`reciprocalInvolution_preserves_cost`), and
from any nonzero strain its orbit oscillates forever without ever reaching
the carrier (`reciprocalInvolution_never_reaches`). So the single most
canonical motion on the ratio ledger satisfies everything the kernel says
and refutes the residue
(`kernel_cost_content_does_not_entail_cost_spending`).

## The named postulate

What the C2 bridge adopts is therefore stated here as an explicit object,
the honest analog of an action principle:

`CostSpendingSubstrate a` = a continuous map on the strain space that
strictly lowers the sourced cost at every state other than the least-cost
state.

It is proved **consistent** (`costSpendingSubstrate_nonempty`: the banked
gradient step inhabits it, so the postulate is not empty and does not prove
everything), **sufficient** (`CostSpendingSubstrate.reaches_carrier`: every
orbit of every inhabitant reaches the sourced least-cost carrier), and
**not determining** (`residue_has_two_models`, `no_unique_dynamics_from_residue`:
it has at least two distinct models, so any principle naming a single flow,
steepest descent in a fixed metric included, is strictly stronger than what
the bridge needs).

## What is proved (all THEOREM; 0 sorry, 0 admit, no new axiom, no
`native_decide`)

* `jcost_kernelCostContent`: `J` satisfies the kernel's five cost premises.
* `reciprocalInvolution_preserves_cost`, `reciprocalInvolution_never_reaches`,
  `kernel_cost_content_does_not_entail_cost_spending`: the reach wall.
* `no_kernel_derivation_of_residue`: the wall in its exact logical form, that
  the implication from the kernel's cost premises to the residue is false.
* `costSpendingSubstrate_nonempty`, `CostSpendingSubstrate.reaches_carrier`,
  `residue_has_two_models`, `no_unique_dynamics_from_residue`: the postulate,
  consistent, sufficient, and not determining.

## Scope, stated exactly

The wall says the kernel's **cost** premises fix no motion on the strain
space. It does not say the kernel is silent about motion everywhere: the
tick update is a kernel object, and it is already known to be
reversal-conjugate and 8-periodic on its core, hence unable to descend
(`RecognitionUpdateDescentWall`). The two results agree and are
complementary: the kernel's cost layer says nothing about motion, and the
kernel's one motion layer provably cannot supply descent. A derivation of
the residue would need a recognition premise about how ledger ratios change
between postings, and no such premise is in the kernel's cost content.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace StrainDescent

open Real Set Filter
open scoped Topology

noncomputable section

/-! ## §1. The kernel's cost content -/

/-- The recognition kernel's content about cost: exactly the premise package
that `law_of_logic_forces_jcost` consumes to force the cost to be `J`. Every
field is a property of the cost of a single ratio. -/
structure KernelCostContent (F : ℝ → ℝ) : Prop where
  reciprocal : Cost.FunctionalEquation.IsReciprocalCost F
  normalized : Cost.FunctionalEquation.IsNormalized F
  composition : Cost.FunctionalEquation.SatisfiesCompositionLaw F
  calibrated : Cost.FunctionalEquation.IsCalibrated F
  continuous : ContinuousOn F (Set.Ioi 0)

/-- **THEOREM.** The recognition cost satisfies the kernel's cost content. -/
theorem jcost_kernelCostContent : KernelCostContent Cost.Jcost where
  reciprocal := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    unfold Cost.Jcost
    field_simp
    ring
  normalized := by
    unfold Cost.FunctionalEquation.IsNormalized Cost.Jcost
    norm_num
  composition := Cost.SymplecticAction.jcost_satisfiesCompositionLaw_via_symplectic
  calibrated := by
    have hG : Cost.FunctionalEquation.G Cost.Jcost = fun t => Real.cosh t - 1 :=
      funext Cost.FunctionalEquation.Jcost_G_eq_cosh_sub_one
    have h1 : deriv (fun t : ℝ => Real.cosh t - 1) = Real.sinh := by
      funext t
      exact ((Real.hasDerivAt_cosh t).sub_const 1).deriv
    have h2 : deriv Real.sinh = Real.cosh := by
      funext t
      exact (Real.hasDerivAt_sinh t).deriv
    unfold Cost.FunctionalEquation.IsCalibrated
    rw [hG, h1, h2, Real.cosh_zero]
  continuous := by
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.div _ continuousOn_const (by norm_num)
    apply ContinuousOn.add continuousOn_id
    apply ContinuousOn.inv₀ continuousOn_id
    intro x hx
    exact ne_of_gt hx

/-! ## §2. The reach wall: the ledger's own involution refutes the residue -/

/-- The ledger's reciprocal involution `x ↦ 1/x`, in the strain coordinate
`t = log x`. Its invariance is the reciprocity premise of the kernel's cost
content. -/
def reciprocalInvolution : ℝ → ℝ := fun t => -t

theorem reciprocalInvolution_continuous : Continuous reciprocalInvolution :=
  continuous_neg

/-- **THEOREM.** The reciprocal involution preserves bare recognition cost
exactly. It spends nothing, anywhere. -/
theorem reciprocalInvolution_preserves_cost (t : ℝ) :
    sourceCost1 0 (reciprocalInvolution t) = sourceCost1 0 t := by
  unfold sourceCost1 reciprocalInvolution
  rw [Real.cosh_neg]
  ring

theorem reciprocalInvolution_iterate_even (t₀ : ℝ) (k : ℕ) :
    reciprocalInvolution^[2 * k] t₀ = t₀ := by
  induction k with
  | zero => simp
  | succ m ih =>
    have h : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [h, Function.iterate_add_apply]
    have h2 : reciprocalInvolution^[2] t₀ = t₀ := by
      simp [reciprocalInvolution, Function.iterate_succ_apply]
    rw [h2, ih]

/-- **THEOREM.** From any nonzero strain the involution's orbit never reaches
the carrier: it oscillates forever. -/
theorem reciprocalInvolution_never_reaches (t₀ : ℝ) (h : t₀ ≠ 0) :
    ¬ Tendsto (fun k => reciprocalInvolution^[k] t₀) atTop (𝓝 (Real.arsinh 0)) := by
  intro hcon
  rw [Real.arsinh_zero] at hcon
  have hidx : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_mono (fun k => by omega : ∀ k : ℕ, k ≤ 2 * k) tendsto_id
  have hsub := hcon.comp hidx
  rw [Function.comp_def] at hsub
  simp only [reciprocalInvolution_iterate_even t₀] at hsub
  have := tendsto_nhds_unique hsub (tendsto_const_nhds (x := t₀) (f := atTop))
  exact h this.symm

/-- **THEOREM (the reach wall).** The kernel's cost content holds, while a
continuous map on the strain space fails the residue: the ledger's own
reciprocal involution, whose invariance is the reciprocity premise itself,
preserves recognition cost everywhere and never reaches the carrier. So the
residue is not entailed by what the kernel says about cost. -/
theorem kernel_cost_content_does_not_entail_cost_spending :
    KernelCostContent Cost.Jcost ∧
    ∃ S : ℝ → ℝ, Continuous S ∧
      (∀ t, sourceCost1 0 (S t) = sourceCost1 0 t) ∧
      ¬ (∀ t, t ≠ Real.arsinh 0 → sourceCost1 0 (S t) < sourceCost1 0 t) := by
  refine ⟨jcost_kernelCostContent, reciprocalInvolution,
    reciprocalInvolution_continuous, reciprocalInvolution_preserves_cost, ?_⟩
  intro hcon
  have h1 : (1:ℝ) ≠ Real.arsinh 0 := by
    rw [Real.arsinh_zero]
    norm_num
  have := hcon 1 h1
  rw [reciprocalInvolution_preserves_cost 1] at this
  exact lt_irrefl _ this

/-- **THEOREM (the wall in its exact logical form).** There is no derivation
of the residue from the kernel's cost content: the implication "the kernel's
cost premises hold, therefore every continuous map on the strain space spends
cost off the least-cost state" is false. This is the precise statement the
reach question asked for, and the reciprocal involution refutes it. -/
theorem no_kernel_derivation_of_residue :
    ¬ (KernelCostContent Cost.Jcost →
        ∀ S : ℝ → ℝ, Continuous S →
          ∀ t, t ≠ Real.arsinh 0 → sourceCost1 0 (S t) < sourceCost1 0 t) := by
  intro hderiv
  have h1 : (1:ℝ) ≠ Real.arsinh 0 := by
    rw [Real.arsinh_zero]
    norm_num
  have h := hderiv jcost_kernelCostContent reciprocalInvolution
    reciprocalInvolution_continuous 1 h1
  rw [reciprocalInvolution_preserves_cost 1] at h
  exact lt_irrefl _ h

/-! ## §3. The named postulate -/

/-- **The C2 bridge's remaining adoption, named.** A cost-spending substrate
is a continuous map on a hinge channel's strain space that strictly lowers
the sourced recognition cost at every state other than the least-cost state.

This is the whole of what the bridge assumes about motion. It names no
metric, no step law, no rate, and no gradient. -/
structure CostSpendingSubstrate (a : ℝ) where
  step : ℝ → ℝ
  step_continuous : Continuous step
  spends_cost : ∀ t, t ≠ Real.arsinh a → sourceCost1 a (step t) < sourceCost1 a t

/-- **THEOREM (sufficiency).** Every cost-spending substrate reaches the
sourced least-cost carrier, from every initial strain. -/
theorem CostSpendingSubstrate.reaches_carrier {a : ℝ} (P : CostSpendingSubstrate a)
    (s₀ : ℝ) :
    Tendsto (fun k => P.step^[k] s₀) atTop (𝓝 (Real.arsinh a)) :=
  cost_decreasing_dynamics_converges' a P.step P.step_continuous P.spends_cost s₀

/-- **THEOREM (consistency).** The postulate is inhabited: the banked gradient
step is a cost-spending substrate. So adopting it is not adopting a
contradiction. -/
theorem costSpendingSubstrate_nonempty (a : ℝ) : Nonempty (CostSpendingSubstrate a) := by
  refine ⟨⟨strainStep1 a, strainStep1_continuous a, ?_⟩⟩
  intro t ht
  apply descent_one_dim_lt a t
  intro hres
  apply ht
  exact (step_fixed_iff_arsinh a t).mp (by
    unfold strainStep1
    rw [hres]
    ring)

/-- The map that collapses every strain straight to the least-cost state. -/
def collapseStep (a : ℝ) : ℝ → ℝ := fun _ => Real.arsinh a

/-- The map that halves the distance to the least-cost state. -/
def halfwayStep (a : ℝ) : ℝ → ℝ := fun t => (t + Real.arsinh a) / 2

def collapse_substrate (a : ℝ) : CostSpendingSubstrate a where
  step := collapseStep a
  step_continuous := continuous_const
  spends_cost := by
    intro t ht
    exact sourceCost1_lt_of_ne a t ht

def halfway_substrate (a : ℝ) : CostSpendingSubstrate a where
  step := halfwayStep a
  step_continuous := by
    unfold halfwayStep
    fun_prop
  spends_cost := by
    intro t ht
    unfold halfwayStep
    rcases lt_or_gt_of_ne ht with hlt | hgt
    · -- t < arsinh a: the midpoint lies strictly between t and the minimum
      have hmid1 : t < (t + Real.arsinh a) / 2 := by linarith
      have hmid2 : (t + Real.arsinh a) / 2 ≤ Real.arsinh a := by linarith
      exact sourceCost1_strictAntiOn a (mem_Iic.mpr hlt.le) (mem_Iic.mpr hmid2) hmid1
    · have hmid1 : (t + Real.arsinh a) / 2 < t := by linarith
      have hmid2 : Real.arsinh a ≤ (t + Real.arsinh a) / 2 := by linarith
      exact sourceCost1_strictMonoOn a (mem_Ici.mpr hmid2) (mem_Ici.mpr hgt.le) hmid1

/-- **THEOREM (the postulate does not name a dynamics).** The residue has at
least two distinct models. -/
theorem residue_has_two_models (a : ℝ) :
    ∃ P Q : CostSpendingSubstrate a, P.step ≠ Q.step := by
  refine ⟨collapse_substrate a, halfway_substrate a, ?_⟩
  intro hcon
  have h := congrFun hcon (Real.arsinh a + 2)
  simp only [collapse_substrate, halfway_substrate, collapseStep, halfwayStep] at h
  linarith

/-- **THEOREM.** No single flow is determined by the residue, so every
principle that names one (steepest descent in a fixed metric included) is
strictly stronger than what the C2 bridge needs. -/
theorem no_unique_dynamics_from_residue (a : ℝ) :
    ¬ ∃ S₀ : ℝ → ℝ, ∀ P : CostSpendingSubstrate a, P.step = S₀ := by
  rintro ⟨S₀, hS₀⟩
  obtain ⟨P, Q, hne⟩ := residue_has_two_models a
  exact hne ((hS₀ P).trans (hS₀ Q).symm)

end

end StrainDescent
end SevenGaps
end Gravity
end IndisputableMonolith
