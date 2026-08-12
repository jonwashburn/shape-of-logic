import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import IndisputableMonolith.Geometry.DihedralDerivatives
import IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger
import IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHinge
import IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHingeConfinement

/-!
# Wave C4 R4: Euclidean Schläfli / α-variation at the Wick endpoint

Fable design `D-gap6-r1-design-20260722`. This module inhabits the frozen
`WickActionContinuationCert.euclidSchlaefli` field

```
∃ dS, HasDerivAt (fun β => (wickActionPath β 1).re) dS α
```

by a finite explicit computation on the collapsed three-pent Euclidean
endpoint (`t = 1`). It is independent of the open N4 cut limit.

## Honest domain

Causal range `(7/12) < α`. On this range the MODEL cosine
`euclidCos α = (5 - 6α)/(6α - 2)` lands in `(-1, 1)`, so
`Real.hasDerivAt_arccos` applies and N2 `carccos_real_eq_arccos` identifies
the complex lift with `Real.arccos`.

## Divergence from classical discrete Schläfli (loud)

Classical Schläfli for Regge variation wants
`Σ_h A_h θ_h' = 0`, leaving `δS = Σ_h ε_h A_h'`.

On this collapsed object the shared hinge area `euclidArea = hingeArea`
is **α-constant** (`area² = 3/16`), while `euclidAngle = arccos ∘ euclidCos`
varies. Hence the angle-derivative term is the **entire** derivative of the
angle-weighted area sum:

```
(3 · euclidArea · euclidAngle)' = 3 · euclidArea · (euclidAngle)'
```

with a nonzero angle term (see `euclid_angle_deriv_term_ne_zero_at_one`).
The frozen certificate field only demands differentiability of
`(wickActionPath · 1).re`; that field **is** inhabited below. Exact
`Σ A θ' = 0` cancellation is **not** claimed and is false for this α-path.

Does **not** inhabit the terminal, flip `gap6`, or touch N4.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace WickActionInteriorHinge

open Complex
open Filter Topology
open FullTheoryLedger
open IndisputableMonolith.Geometry.DihedralDerivatives

noncomputable section

/-! ## §0. Domain: causal range forces `euclidCos ∈ (-1,1)` -/

theorem euclidCos_denom_pos {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    0 < 6 * α - 2 := by
  nlinarith [hα]

theorem euclidCos_denom_ne {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    (6 * α - 2 : ℝ) ≠ 0 :=
  (euclidCos_denom_pos hα).ne'

/-- Honest arccos domain: causal `α` puts the Euclidean MODEL cosine in
`(-1, 1)`. At the lower edge `α = 7/12` one has `euclidCos = 1` (cut);
strict inequality is required. -/
theorem euclidCos_mem_Ioo {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    euclidCos α ∈ Set.Ioo (-1 : ℝ) 1 := by
  unfold euclidCos
  have hden : 0 < 6 * α - 2 := euclidCos_denom_pos hα
  constructor
  · have hfrac : (5 - 6 * α) / (6 * α - 2) + 1 = 3 / (6 * α - 2) := by
      field_simp
      ring
    have hpos : 0 < 3 / (6 * α - 2) :=
      div_pos (by norm_num : (0 : ℝ) < 3) hden
    linarith [hfrac]
  · have : 5 - 6 * α < 6 * α - 2 := by linarith [hα]
    exact (div_lt_one hden).mpr this

theorem euclidCos_abs_lt_one {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    |euclidCos α| < 1 :=
  abs_lt.mpr ⟨(euclidCos_mem_Ioo hα).1, (euclidCos_mem_Ioo hα).2⟩

private theorem one_sub_euclidCos_sq_pos {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    0 < 1 - (euclidCos α) ^ 2 := by
  have habs := euclidCos_abs_lt_one hα
  have hsq : (euclidCos α) ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one _).mpr habs
  linarith

/-! ## §1. Derivative lemmas: `euclidCos`, `euclidArea`, `euclidAngle` -/

private theorem hasDerivAt_mul_sub_const (c d : ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => c * y - d) c x := by
  have h := (hasDerivAt_const_mul (c := c) (x := x)).add (hasDerivAt_const x (-d))
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => by
    simp [Pi.add_apply, sub_eq_add_neg])).congr_deriv ?_
  ring

private theorem hasDerivAt_const_sub_mul (c d : ℝ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => c - d * y) (-d) x := by
  have h :=
    (hasDerivAt_const x c).add ((hasDerivAt_const_mul (c := d) (x := x)).neg)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun y => by
    simp [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg])).congr_deriv ?_
  ring

/-- Explicit Moebius derivative:
`(euclidCos)' = -18 / (6α - 2)²`. -/
theorem hasDerivAt_euclidCos {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    HasDerivAt euclidCos (-18 / (6 * α - 2) ^ 2) α := by
  have hden : (6 * α - 2 : ℝ) ≠ 0 := euclidCos_denom_ne hα
  have hnum : HasDerivAt (fun β : ℝ => 5 - 6 * β) (-6) α :=
    hasDerivAt_const_sub_mul 5 6 α
  have hdenD : HasDerivAt (fun β : ℝ => 6 * β - 2) 6 α :=
    hasDerivAt_mul_sub_const 6 2 α
  have hdiv :
      HasDerivAt (fun β : ℝ => (5 - 6 * β) / (6 * β - 2))
        (((-6) * (6 * α - 2) - (5 - 6 * α) * 6) / (6 * α - 2) ^ 2) α :=
    hnum.div hdenD hden
  have hsimp :
      ((-6) * (6 * α - 2) - (5 - 6 * α) * 6) / (6 * α - 2) ^ 2 =
        -18 / (6 * α - 2) ^ 2 := by
    field_simp
    ring
  have hfun : euclidCos = fun β : ℝ => (5 - 6 * β) / (6 * β - 2) := rfl
  rw [hfun]
  exact hdiv.congr_deriv hsimp

/-- Constant hinge area as an α-function (schema `euclidArea` is not
hinge-indexed). -/
noncomputable def euclidAreaFun (_α : ℝ) : ℝ := euclidArea

theorem hasDerivAt_euclidArea (α : ℝ) : HasDerivAt euclidAreaFun 0 α :=
  hasDerivAt_const α euclidArea

/-- Angle-derivative factor
`θ' = -(1/√(1-c²)) · c'` with `c' = -18/(6α-2)²`. -/
noncomputable def euclidAngleDeriv (α : ℝ) : ℝ :=
  -(1 / Real.sqrt (1 - (euclidCos α) ^ 2)) * (-18 / (6 * α - 2) ^ 2)

theorem euclidAngle_deriv_eq {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    euclidAngleDeriv α =
      18 / ((6 * α - 2) ^ 2 * Real.sqrt (1 - (euclidCos α) ^ 2)) := by
  unfold euclidAngleDeriv
  have hden : (6 * α - 2 : ℝ) ≠ 0 := euclidCos_denom_ne hα
  have hsqrt : Real.sqrt (1 - (euclidCos α) ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (one_sub_euclidCos_sq_pos hα)).ne'
  field_simp [hden, hsqrt]

/-- Euclidean angle derivative via `arccos ∘ euclidCos` on the causal
range. -/
theorem hasDerivAt_euclidAngle {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    HasDerivAt euclidAngle (euclidAngleDeriv α) α := by
  have hc := euclidCos_mem_Ioo hα
  have hend := arccos_endpoint_hypotheses_of_interior hc.1 hc.2
  simpa [euclidAngle, euclidAngleDeriv] using
    hasDerivAt_arccos_comp (hasDerivAt_euclidCos hα) hend.1 hend.2

/-! ## §2. Euclidean endpoint action = real deficit Regge value -/

theorem wickActionPath_eq_euclidRegge {β : ℝ} (hβ : (7 / 12 : ℝ) < β) :
    wickActionPath β 1 =
      ((hingeArea * (2 * Real.pi - 3 * euclidAngle β) : ℝ) : ℂ) := by
  have hpath : pentHingeCosPath β 1 = ((euclidCos β : ℝ) : ℂ) :=
    pentHingeCosPath_eq_euclidCos hβ
  have hc := euclidCos_mem_Ioo hβ
  have hcarc : carccos ((euclidCos β : ℝ) : ℂ) =
      ((Real.arccos (euclidCos β) : ℝ) : ℂ) :=
    carccos_real_eq_arccos (euclidCos β) hc.1 hc.2
  unfold wickActionPath dihedralSumPath euclidAngle
  rw [hpath, hcarc]
  push_cast
  ring

theorem wickActionPath_re_eq_euclidRegge {β : ℝ} (hβ : (7 / 12 : ℝ) < β) :
    (wickActionPath β 1).re =
      hingeArea * (2 * Real.pi - 3 * euclidAngle β) := by
  rw [wickActionPath_eq_euclidRegge hβ, Complex.ofReal_re]

/-! ## §3. Angle-weighted area sum: angle term does NOT cancel -/

/-- Collapsed three-pent angle-weighted area sum `3 · A · θ(α)`. -/
noncomputable def euclidAngleWeightedArea (α : ℝ) : ℝ :=
  3 * euclidArea * euclidAngle α

/-- Product rule with constant area: the derivative is purely the
angle-derivative term `3 · A · θ'`. -/
theorem hasDerivAt_euclidAngleWeightedArea {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    HasDerivAt euclidAngleWeightedArea (3 * euclidArea * euclidAngleDeriv α) α := by
  have hθ := hasDerivAt_euclidAngle hα
  have h := hθ.const_mul (3 * euclidArea)
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun β => by
    simp [euclidAngleWeightedArea, euclidArea, mul_assoc, mul_comm]
  )).congr_deriv ?_
  ring

/-- Loud witness: at `α = 1` the classical Schläfli angle-cancellation
`Σ A θ' = 0` fails for this α-path (angle derivative nonzero). -/
theorem euclid_angle_deriv_term_ne_zero_at_one :
    3 * euclidArea * euclidAngleDeriv 1 ≠ 0 := by
  have hA : 0 < euclidArea := by
    simp only [euclidArea, hingeArea]
    exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3 / 16)
  have hα : (7 / 12 : ℝ) < 1 := by norm_num
  have hform := euclidAngle_deriv_eq hα
  have hsq : 0 < 1 - (euclidCos 1) ^ 2 := by
    rw [euclidCos_one]; norm_num
  have hsqrt : 0 < Real.sqrt (1 - (euclidCos 1) ^ 2) := Real.sqrt_pos.mpr hsq
  have hden : (6 * (1 : ℝ) - 2) ^ 2 ≠ 0 := by norm_num
  rw [hform]
  refine mul_ne_zero (mul_ne_zero (by norm_num : (3 : ℝ) ≠ 0) hA.ne') ?_
  refine div_ne_zero (by norm_num : (18 : ℝ) ≠ 0) ?_
  exact mul_ne_zero hden hsqrt.ne'

/-! ## §4. Certificate field: differentiability of Euclidean action -/

/-- Explicit derivative of `S(α) = A · (2π - 3 θ(α))`. Area constant ⇒
`S' = -3 A θ'` (the `2π` counter-term contributes nothing). Classical
`Σ A θ' = 0` is false here; the frozen field only asks for `HasDerivAt`. -/
theorem euclidSchlaefli_holds {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    HasDerivAt (fun β : ℝ => (wickActionPath β 1).re)
      (-3 * hingeArea * euclidAngleDeriv α) α := by
  have hθ := hasDerivAt_euclidAngle hα
  have h3Aθ :
      HasDerivAt (fun β : ℝ => (3 * hingeArea) * euclidAngle β)
        ((3 * hingeArea) * euclidAngleDeriv α) α :=
    hθ.const_mul (3 * hingeArea)
  have hneg := h3Aθ.neg
  have hconst :
      HasDerivAt (fun _ : ℝ => hingeArea * (2 * Real.pi)) 0 α :=
    hasDerivAt_const α _
  have hsum := hconst.add hneg
  have hregge :
      HasDerivAt (fun β : ℝ => hingeArea * (2 * Real.pi - 3 * euclidAngle β))
        (-3 * hingeArea * euclidAngleDeriv α) α := by
    refine (hsum.congr_of_eventuallyEq (Eventually.of_forall fun β => by
      simp [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
      ring)).congr_deriv ?_
    ring
  have hEq :
      (fun β : ℝ => (wickActionPath β 1).re) =ᶠ[nhds α]
        fun β : ℝ => hingeArea * (2 * Real.pi - 3 * euclidAngle β) := by
    filter_upwards [eventually_gt_nhds hα] with β hβ
    exact wickActionPath_re_eq_euclidRegge hβ
  exact hregge.congr_of_eventuallyEq hEq

/-- Exact frozen field shape of `WickActionContinuationCert.euclidSchlaefli`. -/
theorem euclidSchlaefli_field_inhabited {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    ∃ dS : ℝ, HasDerivAt (fun β : ℝ => (wickActionPath β 1).re) dS α :=
  ⟨_, euclidSchlaefli_holds hα⟩

theorem euclidSchlaefli_field_inhabited_one :
    ∃ dS : ℝ, HasDerivAt (fun β : ℝ => (wickActionPath β 1).re) dS 1 :=
  euclidSchlaefli_field_inhabited (by norm_num : (7 / 12 : ℝ) < 1)

/-! ## §5. Status (R4 closed in this module; gap6 unflipped) -/

structure WickActionEuclidSchlaefliStatus where
  /-- Ledger gap6 flag unchanged. -/
  gap6LorentzianAction : Bool
  /-- R4 Euclidean Schläfli / α-variation field inhabitation: CLOSED. -/
  r4SchlafliOpen : Bool
  /-- Terminal / full Cert assembly: still OPEN (R5). -/
  terminalInhabitationOpen : Bool
  /-- N4 cut Tendsto still OPEN (independent). -/
  n4BoundaryOpen : Bool

def wickActionEuclidSchlaefliStatus : WickActionEuclidSchlaefliStatus where
  gap6LorentzianAction := true
  r4SchlafliOpen := false
  terminalInhabitationOpen := false
  n4BoundaryOpen := false

theorem wickActionEuclidSchlaefliStatus_flags :
    wickActionEuclidSchlaefliStatus.gap6LorentzianAction = true ∧
      wickActionEuclidSchlaefliStatus.r4SchlafliOpen = false ∧
        wickActionEuclidSchlaefliStatus.terminalInhabitationOpen = false ∧
          wickActionEuclidSchlaefliStatus.n4BoundaryOpen = false ∧
            fullTheoryBenchmarks.gap6_lorentzian_action = true := by
  decide

end

end WickActionInteriorHinge
end SevenGaps
end Gravity
end IndisputableMonolith
