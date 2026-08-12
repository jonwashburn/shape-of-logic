import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import IndisputableMonolith.Gravity.SevenGaps.CausalSimplex4D
import IndisputableMonolith.Gravity.SevenGaps.ThreePentCausalConsistency
import IndisputableMonolith.Gravity.SevenGaps.WickActionComplexFirst
import IndisputableMonolith.Gravity.SevenGaps.WickActionCutLimit
import IndisputableMonolith.Gravity.SevenGaps.WickActionEuclidSchlaefli
import IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHinge
import IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHingeConfinement
import IndisputableMonolith.Gravity.SevenGaps.WickFourOneAllHinges
import IndisputableMonolith.Gravity.SevenGaps.WickThreeTwoHinges

/-!
# Wave C4 R5: certificate assembly at α = 1 (partial receipt)

Binding adjudication: `D-gap6-r5-assembly-adjudication-20260723`.

## Obligation 0 (attack first)

Compare the pointwise value `carccos (pentHingeCosPath 1 0)` with the N4
one-sided cut limit `π + I · arcosh(11/8)`.

**Outcome B (landed):** they disagree. The principal log branch at the real
cut cosine `-(11/8)` yields
`carccos(-(11/8)) = π - I · arcosh(11/8)`, while N4's lower-half approach
lands on `π + I · arcosh(11/8)`. Hence the frozen `contAction` field
`ContinuousOn (wickActionPath 1) (Icc 0 1)` is unsatisfiable (value/limit
mismatch at the cut). We prove the named no-go and assemble the repaired
certificate `WickActionContinuationCertV2 1`.

## Honesty walls

* `euclidSchlaefli` certifies differentiability of the Euclidean-endpoint
  action on the collapsed one-hinge geometry, **not** classical multi-hinge
  Schläfli cancellation `Σ A θ' = 0` (which fails here; see
  `WickActionEuclidSchlaefli.euclid_angle_deriv_term_ne_zero_at_one`).
* Historical R5 partial receipt assembled CertV2 at α = 1 only. That
  partial-open posture is **superseded** (2026-07-23): family assembly
  landed in `WickActionCertFamilyAssembly.lean`; V2 terminal
  `wick_action_continuation_4d_v2_holds`; ledger flip receipted in
  `WickActionV2CloseStatus.lean` (`gap6_lorentzian_action_bound_to_v2`).
  Status block below records `gap6LorentzianAction := true` /
  `familyV2Open := false`. Frozen V1 `wick_action_continuation_4d` remains
  retired (`not_wick_action_continuation_4d` / contAction unsatisfiable).
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace WickActionInteriorHinge

open Complex
open Filter Topology
open CausalSimplex4D
open ThreePentCausalConsistency
open WickActionComplexFirst
open WickFourOneAllHinges (csqrt_ofReal_neg csqrt_ofReal_nonneg)
open WickThreeTwoHinges

noncomputable section

/-! ## §0. Decisive cut computation (Outcome B) -/

private lemma sqrt57_div_eight :
    Real.sqrt (57 / 64) = Real.sqrt 57 / 8 := by
  have h64 : Real.sqrt (64 : ℝ) = 8 := by
    have : (64 : ℝ) = 8 ^ 2 := by norm_num
    rw [this, Real.sqrt_sq (by norm_num)]
  calc
    Real.sqrt (57 / 64) = Real.sqrt 57 / Real.sqrt 64 :=
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 57) 64
    _ = Real.sqrt 57 / 8 := by rw [h64]

private lemma arcosh_eleven_over_eight :
    Real.arcosh (11 / 8) = Real.log ((11 + Real.sqrt 57) / 8) := by
  rw [Real.arcosh]
  have hsq : (11 / 8 : ℝ) ^ 2 - 1 = 57 / 64 := by norm_num
  have hsqrt : Real.sqrt ((11 / 8 : ℝ) ^ 2 - 1) = Real.sqrt 57 / 8 := by
    rw [hsq, sqrt57_div_eight]
  have hsum :
      (11 / 8 : ℝ) + Real.sqrt ((11 / 8) ^ 2 - 1) =
        (11 + Real.sqrt 57) / 8 := by
    rw [hsqrt]; ring
  rw [hsum]

/-- Pointwise principal value of `carccos` at the Lorentzian cut cosine. -/
theorem carccos_at_lorentz_cut_one :
    carccos (pentHingeCosPath 1 0) =
      (↑(Real.pi) : ℂ) - I * ↑(Real.arcosh (11 / 8)) := by
  rw [pentHingeCosPath_one_zero, lorentzCos_one]
  set x : ℝ := -(11 / 8)
  have hone_sub :
      (1 : ℂ) - (↑x : ℂ) ^ 2 = ↑(-(57 / 64 : ℝ)) := by
    simp only [x, ofReal_neg, ofReal_div, ofReal_ofNat]
    norm_num
  have hcs :
      csqrt ((1 : ℂ) - (↑x : ℂ) ^ 2) =
        ↑(Real.sqrt (57 / 64)) * I := by
    have hneg : (-(57 / 64 : ℝ)) < 0 := by norm_num
    have h := csqrt_ofReal_neg hneg
    simpa [hone_sub, ofReal_neg] using h
  have hI :
      I * (↑(Real.sqrt 57 / 8 : ℝ) * I) = -↑(Real.sqrt 57 / 8 : ℝ) := by
    set r : ℂ := ↑(Real.sqrt 57 / 8 : ℝ)
    calc
      I * (r * I) = (I * I) * r := by ring
      _ = (-1 : ℂ) * r := by rw [I_mul_I]
      _ = -r := by ring
  have harg :
      (↑x : ℂ) + I * csqrt ((1 : ℂ) - (↑x : ℂ) ^ 2) =
        ↑(-(11 + Real.sqrt 57) / 8 : ℝ) := by
    rw [hcs, sqrt57_div_eight, hI]
    have hx : (↑x : ℂ) = ↑(-(11 / 8 : ℝ)) := by simp [x]
    rw [hx]
    have :
        (↑(-(11 / 8 : ℝ)) : ℂ) + (-↑(Real.sqrt 57 / 8 : ℝ)) =
          ↑(-(11 + Real.sqrt 57) / 8 : ℝ) := by
      simp [ofReal_neg, ofReal_div, ofReal_ofNat, ofReal_add]
      ring
    -- after hI rewrite the goal is ofReal + (-ofReal)
    simpa [sub_eq_add_neg] using this
  have harg_neg : (-(11 + Real.sqrt 57) / 8 : ℝ) < 0 := by
    have hsqrt : 0 ≤ Real.sqrt 57 := Real.sqrt_nonneg _
    linarith [hsqrt]
  have hlog :
      log (↑x + I * csqrt ((1 : ℂ) - (↑x : ℂ) ^ 2)) =
        ↑(Real.log ((11 + Real.sqrt 57) / 8)) + (Real.pi : ℂ) * I := by
    rw [harg]
    have hnorm :
        ‖(↑(-(11 + Real.sqrt 57) / 8 : ℝ) : ℂ)‖ =
          (11 + Real.sqrt 57) / 8 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg harg_neg]
      ring
    apply Complex.ext
    · rw [log_re, hnorm]
      simp [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    · rw [log_im, arg_ofReal_of_neg harg_neg]
      simp [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  have hnegI_pi : (-I) * ((Real.pi : ℂ) * I) = (Real.pi : ℂ) := by
    have hII : (-I) * I = (1 : ℂ) := by
      simp [neg_mul, I_mul_I]
    calc
      (-I) * ((Real.pi : ℂ) * I) = ((-I) * I) * (Real.pi : ℂ) := by ring
      _ = (1 : ℂ) * (Real.pi : ℂ) := by rw [hII]
      _ = (Real.pi : ℂ) := by ring
  have hcarc :
      carccos (↑x : ℂ) =
        (↑(Real.pi) : ℂ) - I * ↑(Real.log ((11 + Real.sqrt 57) / 8)) := by
    simp only [carccos, hlog]
    have h1 :
        (-I) * (↑(Real.log ((11 + Real.sqrt 57) / 8)) + (Real.pi : ℂ) * I) =
          (-I) * ↑(Real.log ((11 + Real.sqrt 57) / 8)) +
            (-I) * ((Real.pi : ℂ) * I) := by
      rw [mul_add]
    rw [h1, hnegI_pi]
    ring
  rw [hcarc, arcosh_eleven_over_eight]

/-- N4 disclosed cut limit for `carccos` at α = 1. -/
theorem carccos_cut_limit_value_one :
    (↑(lorentzAngleRe 1) : ℂ) + I * ↑(lorentzRapidity 1) =
      (↑(Real.pi) : ℂ) + I * ↑(Real.arcosh (11 / 8)) := by
  unfold lorentzAngleRe lorentzRapidity
  rw [lorentzCos_one, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 8)]

/-- Decisive mismatch: pointwise principal value ≠ one-sided cut limit. -/
theorem carccos_value_ne_cut_limit_one :
    carccos (pentHingeCosPath 1 0) ≠
      (↑(lorentzAngleRe 1) : ℂ) + I * ↑(lorentzRapidity 1) := by
  rw [carccos_at_lorentz_cut_one, carccos_cut_limit_value_one]
  set R : ℝ := Real.arcosh (11 / 8)
  have hR : 0 < R := by
    dsimp [R]
    exact Real.arcosh_pos (by norm_num : (1 : ℝ) < 11 / 8)
  intro h
  -- π - I R = π + I R ⇒ -I R = I R ⇒ 2 I R = 0 ⇒ R = 0
  have h' :
      (↑(Real.pi) : ℂ) - I * ↑R = (↑(Real.pi) : ℂ) + I * ↑R := h
  have hsub :
      ((↑(Real.pi) : ℂ) - I * ↑R) - ((↑(Real.pi) : ℂ) + I * ↑R) = 0 := by
    rw [h']; ring
  have h2 : (-(2 : ℂ) * I) * ↑R = 0 := by
    convert hsub using 1
    ring
  have hI2 : (-(2 : ℂ) * I) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)) I_ne_zero
  have hR0 : (↑R : ℂ) = 0 :=
    (mul_eq_zero.mp h2).resolve_left hI2
  exact hR.ne' (ofReal_eq_zero.mp hR0)

/-! ## §1. No-go: frozen `contAction` unsatisfiable at α = 1 -/

private lemma wickActionPath_zero_ne_lorentz_limit :
    wickActionPath 1 0 ≠
      (((hingeArea * (2 * Real.pi - 3 * lorentzAngleRe 1) : ℝ) : ℂ) -
        I * ((hingeArea * (3 * lorentzRapidity 1) : ℝ) : ℂ)) := by
  intro heq
  -- Expand both sides through dihedralSumPath / carccos
  have hL :
      (((hingeArea * (2 * Real.pi - 3 * lorentzAngleRe 1) : ℝ) : ℂ) -
          I * ((hingeArea * (3 * lorentzRapidity 1) : ℝ) : ℂ)) =
        (hingeArea : ℂ) *
          ((2 * Real.pi : ℂ) -
            3 *
              ((↑(lorentzAngleRe 1) : ℂ) + I * ↑(lorentzRapidity 1))) := by
    unfold lorentzAngleRe
    simp [ofReal_mul, ofReal_add, ofReal_sub, mul_add, sub_eq_add_neg]
    ring
  have hV :
      wickActionPath 1 0 =
        (hingeArea : ℂ) *
          ((2 * Real.pi : ℂ) - 3 * carccos (pentHingeCosPath 1 0)) := by
    unfold wickActionPath dihedralSumPath; rfl
  rw [hV, hL] at heq
  have hA : (hingeArea : ℂ) ≠ 0 := by
    have : (0 : ℝ) < hingeArea :=
      Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3 / 16)
    exact ofReal_ne_zero.mpr this.ne'
  have hmul := mul_left_cancel₀ hA heq
  -- 2π - 3 v = 2π - 3 L ⇒ v = L
  have hv :
      carccos (pentHingeCosPath 1 0) =
        (↑(lorentzAngleRe 1) : ℂ) + I * ↑(lorentzRapidity 1) := by
    have h3 : (3 : ℂ) ≠ 0 := by norm_num
    -- hmul : 2π - 3 v = 2π - 3 L  ⇒  3 v = 3 L
    exact mul_left_cancel₀ h3 (sub_right_inj.mp hmul)
  exact carccos_value_ne_cut_limit_one hv

/-- ContinuousOn on `Icc 0 1` forces the right-limit at 0 to equal `f 0`. -/
private lemma tendsto_Ioi_of_continuousOn_Icc
    {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f 0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hcw :=
    hf.continuousWithinAt (Set.left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
  rw [Metric.continuousWithinAt_iff] at hcw
  obtain ⟨δ, hδ, hδf⟩ := hcw ε hε
  refine ⟨min δ 1, lt_min hδ (by norm_num : (0 : ℝ) < 1), ?_⟩
  intro x hx hxδ
  have hxδ' : dist x (0 : ℝ) < δ := (lt_min_iff.mp hxδ).1
  have hxlt : x < 1 := by
    have : dist x (0 : ℝ) < 1 := (lt_min_iff.mp hxδ).2
    -- x > 0 ⇒ dist = x
    have hxpos : 0 < x := hx
    have : |x| < 1 := by simpa [Real.dist_eq] using this
    rw [abs_of_pos hxpos] at this
    exact this
  exact hδf ⟨le_of_lt hx, le_of_lt hxlt⟩ hxδ'

/-- Named no-go: frozen `contAction` field is unsatisfiable at α = 1. -/
theorem contAction_not_satisfiable_at_one :
    ¬ ContinuousOn (wickActionPath 1) (Set.Icc 0 1) := by
  intro hcont
  have hval :=
    tendsto_Ioi_of_continuousOn_Icc (f := wickActionPath 1) hcont
  have hlim := lorentzAnchor_one_holds
  have huniq := tendsto_nhds_unique hval hlim
  exact wickActionPath_zero_ne_lorentz_limit huniq

/-! ## §2. Repaired certificate schema (V2) -/

/-- Repaired action-level Wick continuation certificate: replaces the
unsatisfiable closed-interval `contAction` by interior continuity on
`Ioc 0 1` plus an explicit one-sided cut `Tendsto` (standard branch-cut
resolution). All other fields match `WickActionContinuationCert` verbatim.

Honesty (`euclidSchlaefli`): this field certifies differentiability of the
Euclidean endpoint action on the collapsed one-hinge geometry, **not**
classical multi-hinge Schläfli cancellation `Σ A θ' = 0` (provably fails
on one hinge; see `euclid_angle_deriv_term_ne_zero_at_one`). -/
structure WickActionContinuationCertV2 (α : ℝ) : Prop where
  causalRange : (7 / 12 : ℝ) < α
  chartsAgree :
    inducedSqEdges pentAVert 1 α =
        CausalSimplex4D.lorentzianSqEdges CausalPentType.threeTwo 1 α ∧
      inducedSqEdges pentBVert 1 α =
        CausalSimplex4D.lorentzianSqEdges CausalPentType.threeTwo 1 α ∧
      inducedSqEdges pentCVert 1 α =
        CausalSimplex4D.lorentzianSqEdges CausalPentType.threeTwo 1 α
  branchRegularSum :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      OffArccosCut (pentHingeCosPath α t) ∧
        (1 - pentHingeCosPath α t ^ 2) ∈ slitPlane ∧
          (pentHingeCosPath α t + I * csqrt (1 - pentHingeCosPath α t ^ 2)) ∈
            slitPlane
  /-- Continuous on the open-at-cut interval (honest replacement for
  closed-interval continuity through the branch cut). -/
  contActionInterior : ContinuousOn (wickActionPath α) (Set.Ioc 0 1)
  /-- One-sided cut limit pinned separately (disclosed Lorentzian boundary). -/
  cutLimit :
    Filter.Tendsto (wickActionPath α) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (((hingeArea * (2 * Real.pi - 3 * lorentzAngleRe α) : ℝ) : ℂ) -
          I * ((hingeArea * (3 * lorentzRapidity α) : ℝ) : ℂ)))
  euclidCosReal :
    pentHingeCosPath α 1 = ((euclidCos α : ℝ) : ℂ) ∧
      (α = 1 → euclidCos α = -(1 / 4))
  euclidAnchor :
    wickActionPath α 1 =
      ((hingeArea * (2 * Real.pi - 3 * Real.arccos (euclidCos α)) : ℝ) : ℂ)
  lorentzAnchor :
    Filter.Tendsto (wickActionPath α) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (((hingeArea * (2 * Real.pi - 3 * lorentzAngleRe α) : ℝ) : ℂ) -
          I * ((hingeArea * (3 * lorentzRapidity α) : ℝ) : ℂ)))
  rapidityPinned : lorentzRapidity α ≠ 0
  /-- Differentiability of Euclidean-endpoint action (NOT classical Schläfli
  cancellation; see module docstring). -/
  euclidSchlaefli :
    ∃ dS : ℝ, HasDerivAt (fun β : ℝ => (wickActionPath β 1).re) dS α

/-- Ledger family Prop for the repaired certificate. LEFT OPEN / uninhabited. -/
def wick_action_continuation_v2_family : Prop :=
  ∀ α : ℝ, (7 / 12 : ℝ) < α → WickActionContinuationCertV2 α

/-- Named α = 1 package Prop (inhabited below). Does **not** close the
ledger terminal `wick_action_continuation_4d`, which still demands the
frozen V1 family. -/
def wick_action_continuation_v2_at_one : Prop :=
  WickActionContinuationCertV2 1

/-! ## §3. Interior continuity on `Ioc 0 1` -/

theorem offArccosCut_pentHingeCosPath_Ioc_one {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    OffArccosCut (pentHingeCosPath 1 t) := by
  rcases ht with ⟨ht0, ht1⟩
  rcases lt_or_eq_of_le ht1 with ht1' | rfl
  · exact Or.inl (im_pentHingeCosPath_neg_one ⟨ht0, ht1'⟩).ne
  · -- t = 1: Euclidean cosine -(1/4) ∈ (-1,1)
    refine Or.inr ?_
    rw [pentHingeCosPath_one_one, euclidCos_one]
    constructor <;> norm_num

theorem continuousOn_pentHingeCosPath_Ioc_one :
    ContinuousOn (pentHingeCosPath 1) (Set.Ioc 0 1) := by
  have h := (boundary_threeTwo_spacelike).1
  have heq : pentHingeCosPath 1 = threeTwoCosPath 3 4 :=
    pentHingeCosPath_one_eq_threeTwo
  simpa [heq] using h.mono Set.Ioc_subset_Icc_self

theorem continuousOn_carccos_comp_pent_Ioc_one :
    ContinuousOn (fun t => carccos (pentHingeCosPath 1 t)) (Set.Ioc 0 1) := by
  have hpath := continuousOn_pentHingeCosPath_Ioc_one
  have hmaps :
      Set.MapsTo (pentHingeCosPath 1) (Set.Ioc 0 1) {w | OffArccosCut w} :=
    fun _ ht => offArccosCut_pentHingeCosPath_Ioc_one ht
  exact continuousOn_carccos.comp hpath hmaps

theorem continuousOn_wickActionPath_Ioc_one :
    ContinuousOn (wickActionPath 1) (Set.Ioc 0 1) := by
  have hθ := continuousOn_carccos_comp_pent_Ioc_one
  have h3 : ContinuousOn (fun t => (3 : ℂ) * carccos (pentHingeCosPath 1 t))
      (Set.Ioc 0 1) :=
    continuousOn_const.mul hθ
  have hsub :
      ContinuousOn
        (fun t =>
          (2 * Real.pi : ℂ) - 3 * carccos (pentHingeCosPath 1 t))
        (Set.Ioc 0 1) :=
    continuousOn_const.sub h3
  have hA :
      ContinuousOn
        (fun t =>
          (hingeArea : ℂ) *
            ((2 * Real.pi : ℂ) - 3 * carccos (pentHingeCosPath 1 t)))
        (Set.Ioc 0 1) :=
    continuousOn_const.mul hsub
  refine hA.congr ?_
  intro t _
  unfold wickActionPath dihedralSumPath
  rfl

/-! ## §4. Assemble `WickActionContinuationCertV2 1` -/

theorem chartsAgree_one :
    inducedSqEdges pentAVert 1 1 =
        CausalSimplex4D.lorentzianSqEdges CausalPentType.threeTwo 1 1 ∧
      inducedSqEdges pentBVert 1 1 =
        CausalSimplex4D.lorentzianSqEdges CausalPentType.threeTwo 1 1 ∧
      inducedSqEdges pentCVert 1 1 =
        CausalSimplex4D.lorentzianSqEdges CausalPentType.threeTwo 1 1 :=
  ⟨induced_pentA_eq 1 1, induced_pentB_eq 1 1, induced_pentC_eq 1 1⟩

theorem euclidAnchor_one :
    wickActionPath 1 1 =
      ((hingeArea * (2 * Real.pi - 3 * Real.arccos (euclidCos 1)) : ℝ) : ℂ) := by
  simpa [euclidAngle] using
    wickActionPath_eq_euclidRegge (by norm_num : (7 / 12 : ℝ) < 1)

/-- Banked partial receipt: repaired V2 certificate at the physical coupling
α = 1. Does not inhabit `wick_action_continuation_4d`. -/
theorem wickActionContinuationCertV2_one :
    WickActionContinuationCertV2 1 where
  causalRange := by norm_num
  chartsAgree := chartsAgree_one
  branchRegularSum := branchRegularSum_one
  contActionInterior := continuousOn_wickActionPath_Ioc_one
  cutLimit := lorentzAnchor_one_holds
  euclidCosReal := by
    refine ⟨pentHingeCosPath_one_one, ?_⟩
    intro h; exact euclidCos_one
  euclidAnchor := euclidAnchor_one
  lorentzAnchor := lorentzAnchor_one_holds
  rapidityPinned := rapidityPinned_one
  -- Honesty: differentiability only; NOT classical Schläfli cancellation.
  euclidSchlaefli := euclidSchlaefli_field_inhabited_one

theorem wick_action_continuation_v2_at_one_holds :
    wick_action_continuation_v2_at_one :=
  wickActionContinuationCertV2_one

/-! ## §5. Codified decoys -/

/-- Decoy: a Euclidean-only (real) certificate is falsified by the genuine
non-real Lorentzian endpoint. -/
theorem decoy_euclidean_only_falsified :
    (((hingeArea * (2 * Real.pi - 3 * lorentzAngleRe 1) : ℝ) : ℂ) -
        I * ((hingeArea * (3 * lorentzRapidity 1) : ℝ) : ℂ)).im ≠ 0 :=
  lorentz_endpoint_not_real

/-- Decoy: an interior-point (`nhds`) limit cannot discharge `cutLimit`
(exact filter is `nhdsWithin 0 (Ioi 0)`). -/
theorem decoy_interior_nhds_not_cutLimit_filter :
    nhds (0 : ℝ) ≠ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
  intro h
  -- `Ioi 0` is a member of the cut filter, but not of plain `nhds 0`
  -- (every nhds-neighborhood of 0 contains 0 itself, which is outside `Ioi`).
  have hIoi : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    self_mem_nhdsWithin
  have hIoi' : Set.Ioi (0 : ℝ) ∈ nhds (0 : ℝ) := by simpa [h] using hIoi
  exact absurd (mem_of_mem_nhds hIoi') (lt_irrefl (0 : ℝ))

/-! ## §6. Status (partial receipt; gap6 unflipped) -/

structure WickActionCertAssemblyStatus where
  gap6LorentzianAction : Bool
  contActionV1Unsatisfiable : Bool
  certV2AtOneClosed : Bool
  familyV2Open : Bool
  terminalV1Open : Bool

def wickActionCertAssemblyStatus : WickActionCertAssemblyStatus where
  gap6LorentzianAction := true
  contActionV1Unsatisfiable := true
  certV2AtOneClosed := true
  familyV2Open := false
  terminalV1Open := false

theorem wickActionCertAssemblyStatus_flags :
    wickActionCertAssemblyStatus.gap6LorentzianAction = true ∧
      wickActionCertAssemblyStatus.contActionV1Unsatisfiable = true ∧
        wickActionCertAssemblyStatus.certV2AtOneClosed = true ∧
          wickActionCertAssemblyStatus.familyV2Open = false ∧
            wickActionCertAssemblyStatus.terminalV1Open = false ∧
              (¬ ContinuousOn (wickActionPath 1) (Set.Icc 0 1)) ∧
                wick_action_continuation_v2_at_one :=
  ⟨rfl, rfl, rfl, rfl, rfl, contAction_not_satisfiable_at_one,
    wick_action_continuation_v2_at_one_holds⟩

end

end WickActionInteriorHinge
end SevenGaps
end Gravity
end IndisputableMonolith
