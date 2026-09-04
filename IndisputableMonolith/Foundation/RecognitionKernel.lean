import Mathlib
import IndisputableMonolith.Foundation.NothingToDistinction
import IndisputableMonolith.Foundation.MeasureForcing
import IndisputableMonolith.Foundation.DimensionForcing
import IndisputableMonolith.Foundation.HierarchyRealization
import IndisputableMonolith.Foundation.HierarchyRealizationObstruction
import IndisputableMonolith.Foundation.ClosedObservableFramework
import IndisputableMonolith.Foundation.PublicSpine
import IndisputableMonolith.Foundation.PublicSpineLinkingClosure
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Cost.AczelProof
import IndisputableMonolith.Cost.ContDiffReduction
import IndisputableMonolith.CostUniqueness
import IndisputableMonolith.Constants
import IndisputableMonolith.PhiSupport.Lemmas
import IndisputableMonolith.Foundation.KernelIndependenceCore
import IndisputableMonolith.Foundation.KernelContinuityShrink

/-!
# Recognition Kernel (Phase 1)

The atomic free-hypothesis kernel of the T-2→T9 forcing spine, and the first
Lean object spanning the bare-distinction floor through the forced measure. The
floor is `Empty ≠ Unit` plus a non-singleton universe of discourse, stated
inside an ambient type theory that supplies everything except the inequality
(`Foundation.NothingToDistinction`); it is not a derivation from absolute
nothing.

## Why the carriers are variables

The kernel is stated over **unknown** carriers: an unknown cost `F`, an unknown
dimension `D`, an unknown weight `w`, and an unknown realized hierarchy `H` over
an unknown framework `Fr`. This is the whole content of the phase. Instantiating
the fields at the canonical objects (`Cost.Jcost`, `3`, `latticeWeight`) turns
every field into an already-proved theorem, and `kernel_forces_spine` would then
discharge its conclusions without consulting the kernel at all: a vacuous
sufficiency claim. Over variables the statement says the intended thing, namely
that anything satisfying the kernel **is** the canonical object.

`recognitionKernel_canonical` is the anti-vacuity witness (the kernel is
satisfiable), not the content.

## Membership

Present (six): composition law, calibration, linking detection, weight
positivity, weight factorization, self-similar step, plus the realized hierarchy
carried in the parameters. Every one of the six has a countermodel
(`KernelIndependence.members_all_independent`), so none of them is surplus.

Absent by proof, not by omission: **normalization** (forced by the composition law
plus calibration, `KernelIndependence.composition_calibration_forces_normalized`,
2026-07-24 shrink), **continuity** (forced by the same two,
`KernelContinuity.composition_calibration_forces_continuity`, 2026-07-25 shrink),
reciprocity (forced by normalization plus the composition law), smoothness (the
Aczel instance is proved from continuity, which is now derived), the T1–T4
corollaries, the T7 arithmetic, and the legacy T8 encoding predicate.

The two shrinks together collapse the whole cost sector to two premises:
`composition_calibration_forces_jcost` says the composition law and calibration
alone force `F = Jcost` on the positives.

## Honest tags

`step_self_similar` is HYPOTHESIS-tagged at its source, so the measure end of
the spine is FORCED-CONDITIONAL on it. The T5→T6 seam is a named residual: the
realized hierarchy enters as a premise because a closed observable framework
alone does not force its fields (`hierarchy_premise_is_load_bearing`).
-/

namespace IndisputableMonolith
namespace Foundation

open Cost.FunctionalEquation
open ClosedFramework
open HierarchyRealization
open MeasureForcing

noncomputable section

/-! ## Normalization is redundant (Phase 3 shrink, landed)

A kernel member earns its place only if it cannot be derived from the others.
Normalization falls twice over, and only the second route is free.

The first route, kept below for the record, derives `F 1 = 0` from the
composition law plus pointwise **nonnegativity**. That is a wash: nonnegativity
is not a kernel member and is not itself forced, so the premise count is
unchanged. This was the Phase 1 verdict.

The second route is free: the composition law plus **calibration**, which is
already a member, force `F 1 = 0`
(`KernelIndependence.composition_calibration_forces_normalized`). The unit
diagonal leaves only `F 1 = 0` or `F ≡ -1` on the positives, and a constant has
vanishing log-curvature, so calibration kills the second branch. Normalization is
therefore deleted from the structure and derived inside `kernel_forces_spine`.

The composition law *alone* does not suffice, which is what makes calibration
load-bearing here rather than decorative: see
`composition_law_alone_does_not_force_normalized`. -/

/-- **Shrink attempt.** Composition law plus pointwise nonnegativity on `(0,∞)`
force `F 1 = 0`. Same algebra as `CalibrationBoundary.RCL.identity_of_nonnegative`,
transported to the `SatisfiesCompositionLaw` surface. -/
theorem composition_law_nonneg_forces_normalized
    (F : ℝ → ℝ)
    (hComp : SatisfiesCompositionLaw F)
    (hNonneg : ∀ x : ℝ, 0 < x → 0 ≤ F x) :
    IsNormalized F := by
  have h := hComp (1 : ℝ) 1 (by norm_num) (by norm_num)
  have h' : F 1 + F 1 = 2 * F 1 * F 1 + 2 * F 1 + 2 * F 1 := by
    simpa using h
  have hquad : F 1 * (F 1 + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hquad with hzero | hneg
  · exact hzero
  · have hnn : 0 ≤ F 1 := hNonneg 1 (by norm_num)
    linarith

/-- **The composition law alone is not enough.** The constant `-1` satisfies the
composition law and is not normalized, so the shrink genuinely consumes
calibration; and the nonnegativity route genuinely consumes nonnegativity. Both
halves matter: the first says the free shrink needs a second member, the second
says which member it must not be. -/
theorem composition_law_alone_does_not_force_normalized :
    (∀ F : ℝ → ℝ,
      SatisfiesCompositionLaw F →
      (∀ x : ℝ, 0 < x → 0 ≤ F x) →
      IsNormalized F) ∧
    ¬ (∀ F : ℝ → ℝ, SatisfiesCompositionLaw F → IsNormalized F) := by
  refine ⟨composition_law_nonneg_forces_normalized, ?_⟩
  intro h
  have hComp : SatisfiesCompositionLaw (fun _ : ℝ => (-1 : ℝ)) := by
    intro x y _hx _hy
    norm_num
  have hNorm := h (fun _ => (-1 : ℝ)) hComp
  change (-1 : ℝ) = 0 at hNorm
  exact absurd hNorm (by linarith)

/-! ## Continuity is redundant too (Phase 3 shrink, landed 2026-07-25)

The same pair does it again. `KernelContinuity.composition_calibration_forces_continuity`
derives `ContinuousOn F (Set.Ioi 0)` from the composition law plus calibration, so
continuity left the structure as well.

The reason it works is worth stating, because the paper argument says the opposite.
A d'Alembert functional equation without regularity has wild Hamel-basis solutions,
which is why the published cost theorem assumes continuity. Those solutions are
nowhere differentiable, and Lean's `deriv` returns `0` off the differentiability set,
so none of them can satisfy `IsCalibrated`, which asserts
`deriv (deriv (G F)) 0 = 1`. Lean's calibration is strictly stronger than its paper
reading: it carries local regularity, and that is enough. The chain then runs through
monotonicity on a right window, the free lower bound `H ≥ -1` that every d'Alembert
solution satisfies, and two instances of the functional equation to pin the limit
value at `1`.

The consequence for the cost sector is the theorem below: **two** premises force the
recognition cost, where the published statement uses four. -/

/-- **The cost sector needs two premises.** The composition law and calibration alone
force the unknown cost to be the recognition cost on the positives. Normalization,
reciprocity, and continuity are all derived en route, and smoothness comes from the
Aczel instance over derived continuity. -/
theorem composition_calibration_forces_jcost
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (hCalib : IsCalibrated F) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  have hNorm : IsNormalized F :=
    KernelIndependence.composition_calibration_forces_normalized F hComp hCalib
  have hCont : ContinuousOn F (Set.Ioi 0) :=
    KernelContinuity.composition_calibration_forces_continuity F hComp hCalib
  exact law_of_logic_forces_jcost F
    (composition_law_forces_reciprocity F hNorm hComp)
    hNorm hComp hCalib hCont

/-! ## The kernel -/

/-- **Recognition Kernel.** The atomic free hypotheses of the T-2→T9 spine,
stated over unknown carriers.

The realized hierarchy sits in the parameters rather than in a field because it
is data, not a proposition; requiring it is exactly the T5→T6 residual. -/
structure RecognitionKernel
    (F : ℝ → ℝ) (D : ℕ) (w : ℕ → ℝ)
    (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr) : Prop where
  /-- Free hyp: `Cost.FunctionalEquation.SatisfiesCompositionLaw`.
  Independence: `KernelIndependence.logSqCost`, the `c = 0` member of the
  bilinear family, satisfies every other cost-sector member and fails this one.
  The combiner's linear coefficient is forced
  (`KernelIndependence.linear_coefficient_forced`); its product coefficient is a
  unit convention and not derivable
  (`KernelIndependence.product_coefficient_is_a_choice`), so this member carries
  one calibration-shaped choice, named rather than hidden. -/
  composition_law : SatisfiesCompositionLaw F
  /-- Free hyp: `Cost.FunctionalEquation.IsCalibrated`.
  Independence: `KernelIndependence.zeroCost`. The most load-bearing member in the
  kernel: it also carries normalization (2026-07-24 shrink) and continuity
  (2026-07-25 shrink), because in Lean it asserts a genuine second derivative and
  therefore silently carries local regularity. -/
  calibration : IsCalibrated F
  /-- Free hyp: `PublicSpine.DetectsNontrivialLinking` at the unknown `D`.
  Independence: `D = 0`. -/
  linking_detection : PublicSpine.DetectsNontrivialLinking D
  /-- Free hyp: `RecognitionWeightRule.w_pos`. -/
  weight_pos : ∀ n : ℕ, 0 < w n
  /-- Free hyp: `RecognitionWeightRule.factorizes`. -/
  weight_factorizes : ∀ m n : ℕ, w (m + n) = w m * w n
  /-- Free hyp: `RecognitionWeightRule.step_self_similar`. HYPOTHESIS-tagged at
  source, so the measure end of the spine is conditional on it. -/
  step_self_similar : w 1 = 1 / (1 + w 1)

/-! ## The spine -/

/-- **Kernel spine.** The conclusions the kernel must deliver, from absolute
nothing through the forced measure. The T9 end is the forced measure, not the
consciousness rung that `ExtendedForcingChain` calls T9. -/
structure KernelSpine
    (F : ℝ → ℝ) (D : ℕ) (w : ℕ → ℝ)
    (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr) : Prop where
  /-- T-2: the initial object is not the terminal object. Needs no kernel input.
  It does need the ambient type theory, which is not premise-free; see the header
  of `Foundation.NothingToDistinction` for what that theory supplies. -/
  t_minus2_distinction : NothingToDistinction.Nothing ≠ NothingToDistinction.Something
  /-- T5: the unknown cost is the recognition cost. -/
  cost_is_jcost : ∀ x : ℝ, 0 < x → F x = Cost.Jcost x
  /-- T6: the unknown hierarchy's scale is the golden ratio. -/
  scale_is_phi : (HierarchyRealization.realized_to_ladder Fr H).ratio = PhiForcing.φ
  /-- T8: the unknown dimension is three, via the non-encoding public spine. -/
  dimension_is_three : D = 3
  /-- T7: the tick count follows from the dimension. -/
  eight_tick : DimensionForcing.EightTickFromDimension D = 8
  /-- T9: the unknown weight is the forced measure. -/
  weight_is_forced : ∀ n : ℕ, w n = MeasureForcing.latticeWeight n

/-- **Phase 1 span.** A recognition kernel forces the spine from absolute
nothing through the forced measure. Every conclusion except the premise-free
T-2 end consumes a kernel field or a kernel parameter. -/
theorem kernel_forces_spine
    {F : ℝ → ℝ} {D : ℕ} {w : ℕ → ℝ}
    {Fr : ClosedObservableFramework} {H : RealizedHierarchy Fr}
    (K : RecognitionKernel F D w Fr H) :
    KernelSpine F D w Fr H where
  t_minus2_distinction := NothingToDistinction.nothing_ne_something
  cost_is_jcost :=
    composition_calibration_forces_jcost F K.composition_law K.calibration
  scale_is_phi := HierarchyRealization.realized_hierarchy_forces_phi Fr H
  dimension_is_three := PublicSpineLinkingClosure.forces_D3 D K.linking_detection
  eight_tick := by
    rw [PublicSpineLinkingClosure.forces_D3 D K.linking_detection]
    rfl
  weight_is_forced := fun n =>
    MeasureForcing.RecognitionWeightRule.weight_forced
      { w := w
      , w_pos := K.weight_pos
      , factorizes := K.weight_factorizes
      , step_self_similar := K.step_self_similar } n

/-! ## Anti-vacuity

The kernel is satisfiable. This is the check that the fields are not jointly
contradictory; it is not the content of the phase. -/

/-- The canonical objects satisfy the kernel, for any realized hierarchy. -/
theorem recognitionKernel_canonical
    (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr) :
    RecognitionKernel Cost.Jcost 3 MeasureForcing.latticeWeight Fr H where
  composition_law := CostUniqueness.Jcost_satisfies_composition_law
  calibration := CostUniqueness.Jcost_is_calibrated
  linking_detection := PublicSpine.detectsNontrivialLinking_three
  weight_pos := MeasureForcing.latticeWeight_pos
  weight_factorizes := fun m n =>
    pow_add (1 / Constants.phi) m n
  step_self_similar := by
    have hfp : Constants.phi = 1 + 1 / Constants.phi := PhiSupport.phi_fixed_point
    simp only [MeasureForcing.latticeWeight, pow_one]
    rw [← hfp]

/-! ## The named T5→T6 residual

The realized hierarchy is a kernel parameter rather than a derived object
because a closed observable framework does not force its fields. Naming the
residual is the honest alternative to widening what counts as derived. -/

/-- The hierarchy premise is load-bearing: some closed observable framework
fails both the self-similar-ratio and the additive-posting fields. -/
theorem hierarchy_premise_is_load_bearing :
    ∃ (F0 : ClosedObservableFramework) (base : F0.S),
      (¬ (∀ k,
        F0.r (F0.T^[k + 2] base) / F0.r (F0.T^[k + 1] base) =
          F0.r (F0.T^[k + 1] base) / F0.r (F0.T^[k] base))) ∧
      (¬ (F0.r (F0.T^[2] base) = F0.r (F0.T^[1] base) + F0.r base)) :=
  HierarchyRealizationObstruction.closedFramework_does_not_force_realizedHierarchy_fields

end
end Foundation
end IndisputableMonolith
