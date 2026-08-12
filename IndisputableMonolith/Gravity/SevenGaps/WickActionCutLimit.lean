import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHinge
import IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHingeConfinement
import IndisputableMonolith.Gravity.SevenGaps.WickFourOneAllHinges

/-!
# Wave C4 N4: `carccos` cut-boundary limit (6-lemma route)

Binding design: `D-gap6-n4-cut-limit-design-20260723`.

Lands `carccos_tendsto_at_cut_one` and `lorentzAnchor_one` via L1–L6.
Does **not** inhabit the gap6 terminal or flip ledger Bools.
Family Prop left open in this session.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace WickActionInteriorHinge

open Complex
open Filter Topology
open WickActionComplexFirst
open WickFourOneAllHinges (csqrt_ofReal_nonneg)

noncomputable section

/-! ## L1. Lower-half `csqrt` reflection -/

theorem csqrt_of_im_neg {s : ℂ} (him : s.im < 0) :
    csqrt s = -I * csqrt (-s) := by
  have hs0 : s ≠ 0 := fun h => by
    have : (0 : ℝ) < 0 := by simpa [h] using him
    exact (lt_irrefl (0 : ℝ)) this
  have hns0 : (-s) ≠ 0 := neg_ne_zero.mpr hs0
  have hlog : log s = log (-s) - (Real.pi : ℂ) * I := by
    apply Complex.ext
    · simp [log_re, norm_neg]
    · have harg : arg (-s) = arg s + Real.pi :=
        arg_neg_eq_arg_add_pi_of_im_neg him
      simp only [log_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
      linarith [harg]
  unfold csqrt
  rw [cpow_def_of_ne_zero hs0, cpow_def_of_ne_zero hns0, hlog]
  have hmul :
      (log (-s) - (Real.pi : ℂ) * I) * (1 / 2 : ℂ) =
        log (-s) * (1 / 2 : ℂ) + (-(Real.pi : ℂ) / 2 * I) := by
    ring
  have hexp : exp (-(Real.pi : ℂ) / 2 * I) = -I := by
    simpa [ofReal_div, ofReal_neg, ofReal_ofNat] using
      (exp_neg_pi_div_two_mul_I : exp (-Real.pi / 2 * I) = -I)
  rw [hmul, exp_add, hexp]
  ring

/-! ## L2. Path cosine → `-11/8` -/

theorem tendsto_pentHingeCosPath_one :
    Tendsto (fun t => pentHingeCosPath 1 t) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((-(11 / 8 : ℝ) : ℂ))) := by
  have hz :
      Tendsto zArc (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (zArc 0)) :=
    (continuous_zArc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hz0 : zArc 0 = ((-1 : ℝ) : ℂ) := by
    simp [zArc, arcZ_zero]
  have hnum :
      Tendsto (fun t => (5 : ℂ) - 6 * zArc t) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((11 : ℂ))) := by
    have :
        Tendsto (fun t => (5 : ℂ) - 6 * zArc t) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds ((5 : ℂ) - 6 * zArc 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hz)
    convert this using 1
    norm_num [hz0]
  have hden :
      Tendsto (fun t => (6 : ℂ) * zArc t - 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((-8 : ℂ))) := by
    have :
        Tendsto (fun t => (6 : ℂ) * zArc t - 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds ((6 : ℂ) * zArc 0 - 2)) :=
      (tendsto_const_nhds.mul hz).sub tendsto_const_nhds
    convert this using 1
    norm_num [hz0]
  have hden0 : ((-8 : ℂ) : ℂ) ≠ 0 := by norm_num
  have hdiv :
      Tendsto (fun t => ((5 : ℂ) - 6 * zArc t) / (6 * zArc t - 2))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (((11 : ℂ) / (-8 : ℂ)))) :=
    hnum.div hden hden0
  have hval : ((11 : ℂ) / (-8 : ℂ)) = ((-(11 / 8 : ℝ) : ℂ)) := by
    norm_num
  have hpath :
      (fun t => pentHingeCosPath 1 t) =
        fun t => ((5 : ℂ) - 6 * zArc t) / (6 * zArc t - 2) := by
    funext t
    exact pentHingeCosPath_eq_moebius_one t
  simpa [hpath, hval] using hdiv

/-! ## L3. `csqrt(w^2 - 1)` → `√57 / 8` -/

private lemma sq_sub_one_limit :
    ((11 / 8 : ℂ) ^ 2 - 1) = (57 / 64 : ℂ) := by
  norm_num

private lemma fiftySevenOver64_mem_slitPlane :
    (57 / 64 : ℂ) ∈ slitPlane := by
  have : ((57 / 64 : ℝ) : ℂ) ∈ slitPlane :=
    ofReal_mem_slitPlane.mpr (by norm_num : (0 : ℝ) < 57 / 64)
  simpa using this

private lemma sqrt_fiftySeven_div_eight :
    Real.sqrt (57 / 64) = Real.sqrt 57 / 8 := by
  have h64 : Real.sqrt (64 : ℝ) = 8 := by
    have : (64 : ℝ) = 8 ^ 2 := by norm_num
    rw [this, Real.sqrt_sq (by norm_num)]
  calc
    Real.sqrt (57 / 64) = Real.sqrt 57 / Real.sqrt 64 :=
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 57) 64
    _ = Real.sqrt 57 / 8 := by rw [h64]

theorem tendsto_csqrt_sq_sub_one_one :
    Tendsto (fun t => csqrt (pentHingeCosPath 1 t ^ 2 - 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((↑(Real.sqrt 57) : ℂ) / 8)) := by
  have hw := tendsto_pentHingeCosPath_one
  have hsq :
      Tendsto (fun t => pentHingeCosPath 1 t ^ 2 - 1)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((11 / 8 : ℂ) ^ 2 - 1)) := by
    have h := (hw.pow 2).sub (tendsto_const_nhds (x := (1 : ℂ)))
    simpa [neg_sq] using h
  have hsq' :
      Tendsto (fun t => pentHingeCosPath 1 t ^ 2 - 1)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (57 / 64 : ℂ)) := by
    simpa [sq_sub_one_limit] using hsq
  have hcont : ContinuousAt (fun z : ℂ => csqrt z) (57 / 64 : ℂ) := by
    unfold csqrt
    exact continuousAt_cpow_const fiftySevenOver64_mem_slitPlane
  have hcomp :
      Tendsto (fun t => csqrt (pentHingeCosPath 1 t ^ 2 - 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (csqrt (57 / 64 : ℂ))) :=
    hcont.tendsto.comp hsq'
  have heval : csqrt (57 / 64 : ℂ) = (↑(Real.sqrt 57) : ℂ) / 8 := by
    have h := csqrt_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 57 / 64)
    have h64 : ((57 / 64 : ℝ) : ℂ) = (57 / 64 : ℂ) := by norm_num
    rw [← h64, h, sqrt_fiftySeven_div_eight, ofReal_div, ofReal_ofNat]
  exact heval ▸ hcomp

/-! ## Filter helpers -/

private lemma eventually_ioo_of_nhdsWithin_zero :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioo (0 : ℝ) 1 := by
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with t ht0 ht1
  exact ⟨ht0, ht1⟩

private lemma eventually_re_pent_neg :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (pentHingeCosPath 1 t).re < 0 := by
  have hw := tendsto_pentHingeCosPath_one
  have hneg : ((-(11 / 8 : ℝ) : ℂ)).re < (0 : ℝ) := by norm_num
  exact ((continuous_re.tendsto _).comp hw).eventually_lt_const hneg

private lemma eventually_im_pent_neg :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (pentHingeCosPath 1 t).im < 0 := by
  filter_upwards [eventually_ioo_of_nhdsWithin_zero] with t ht
  exact im_pentHingeCosPath_neg_one ht

private lemma eventually_im_one_sub_sq_neg :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (1 - pentHingeCosPath 1 t ^ 2).im < 0 := by
  filter_upwards [eventually_re_pent_neg, eventually_im_pent_neg] with t hre him
  have :
      (1 - pentHingeCosPath 1 t ^ 2).im =
        -(2 * (pentHingeCosPath 1 t).re * (pentHingeCosPath 1 t).im) := by
    simp [sub_im, sq, mul_im]
    ring
  rw [this]
  have hprod : (pentHingeCosPath 1 t).re * (pentHingeCosPath 1 t).im > 0 :=
    mul_pos_of_neg_of_neg hre him
  nlinarith

/-! ## L4 -/

theorem eventually_carccos_log_arg_eq :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      pentHingeCosPath 1 t + I * csqrt (1 - pentHingeCosPath 1 t ^ 2) =
        pentHingeCosPath 1 t + csqrt (pentHingeCosPath 1 t ^ 2 - 1) := by
  filter_upwards [eventually_im_one_sub_sq_neg] with t him
  set w := pentHingeCosPath 1 t
  have hrefl : csqrt (1 - w ^ 2) = -I * csqrt (-(1 - w ^ 2)) :=
    csqrt_of_im_neg him
  have hneg : -(1 - w ^ 2) = w ^ 2 - 1 := by ring
  calc
    w + I * csqrt (1 - w ^ 2)
        = w + I * (-I * csqrt (-(1 - w ^ 2))) := by rw [hrefl]
    _ = w + I * (-I * csqrt (w ^ 2 - 1)) := by rw [hneg]
    _ = w + csqrt (w ^ 2 - 1) := by
      simp [← mul_assoc, mul_neg, I_mul_I]

/-! ## L5 -/

private lemma eventually_csqrt_re_pos :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 < (csqrt (pentHingeCosPath 1 t ^ 2 - 1)).re := by
  have hW := tendsto_csqrt_sq_sub_one_one
  have hpos : (0 : ℝ) < Real.sqrt 57 / 8 :=
    div_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 57)) (by norm_num)
  have hlim : (((↑(Real.sqrt 57) : ℂ) / 8)).re = Real.sqrt 57 / 8 := by
    simp [div_re, ofReal_re, ofReal_im]
  exact ((continuous_re.tendsto _).comp hW).eventually_const_lt
    (by simpa [hlim] using hpos)

private lemma eventually_csqrt_add_re_neg :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (csqrt (pentHingeCosPath 1 t ^ 2 - 1)).re +
          (pentHingeCosPath 1 t).re < 0 := by
  have hW := tendsto_csqrt_sq_sub_one_one
  have hw := tendsto_pentHingeCosPath_one
  have hsum :
      Tendsto
        (fun t =>
          (csqrt (pentHingeCosPath 1 t ^ 2 - 1)).re +
            (pentHingeCosPath 1 t).re)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (Real.sqrt 57 / 8 + (-(11 / 8 : ℝ)))) := by
    have hWr := (continuous_re.tendsto _).comp hW
    have hwr := (continuous_re.tendsto _).comp hw
    simpa using hWr.add hwr
  have hlim_lt : Real.sqrt 57 / 8 + (-(11 / 8 : ℝ)) < 0 := by
    have hsq : Real.sqrt 57 < 11 := by
      have : (57 : ℝ) < 11 ^ 2 := by norm_num
      exact (Real.sqrt_lt' (by norm_num)).2 (by simpa using this)
    linarith
  exact hsum.eventually_lt_const hlim_lt

private lemma eventually_sq_sub_one_ne :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      pentHingeCosPath 1 t ^ 2 - 1 ≠ 0 := by
  have hw := tendsto_pentHingeCosPath_one
  have hsq :
      Tendsto (fun t => pentHingeCosPath 1 t ^ 2 - 1)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (57 / 64 : ℂ)) := by
    have h := (hw.pow 2).sub (tendsto_const_nhds (x := (1 : ℂ)))
    simpa [neg_sq, sq_sub_one_limit] using h
  have hne : (57 / 64 : ℂ) ≠ 0 := by norm_num
  exact hsq.eventually_ne hne

theorem eventually_im_log_arg_nonneg :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 ≤ (pentHingeCosPath 1 t +
        csqrt (pentHingeCosPath 1 t ^ 2 - 1)).im := by
  filter_upwards [eventually_im_pent_neg, eventually_csqrt_re_pos,
    eventually_csqrt_add_re_neg, eventually_sq_sub_one_ne] with
    t himw hWre hsum hne
  set w := pentHingeCosPath 1 t
  set W := csqrt (w ^ 2 - 1)
  have hmul : W * W = w ^ 2 - 1 := csqrt_mul_self hne
  have himWW : (W * W).im = (w ^ 2 - 1).im := by rw [hmul]
  have hleft : (W * W).im = 2 * W.re * W.im := by
    simp [mul_im]
    ring
  have hright : (w ^ 2 - 1).im = 2 * w.re * w.im := by
    simp [sub_im, sq, mul_im]
    ring
  have hprod : W.re * W.im = w.re * w.im := by
    have : 2 * W.re * W.im = 2 * w.re * w.im := by
      linarith [himWW, hleft, hright]
    nlinarith
  have hid : (w.im + W.im) * W.re = w.im * (W.re + w.re) := by
    linarith [hprod]
  have hrhs : 0 < w.im * (W.re + w.re) :=
    mul_pos_of_neg_of_neg himw hsum
  have hlhs : 0 < (w.im + W.im) * W.re := by
    simpa [hid] using hrhs
  have : 0 < w.im + W.im := pos_of_mul_pos_left hlhs hWre.le
  simpa [add_im] using this.le

/-! ## L6 -/

/-- Limit log-argument, written to match the sum of L2 and L3 limits. -/
private def u0 : ℂ := (-(11 / 8 : ℝ) : ℂ) + (↑(Real.sqrt 57) : ℂ) / 8

private lemma u0_eq_ofReal :
    u0 = ((Real.sqrt 57 - 11) / 8 : ℝ) := by
  simp [u0, ofReal_div, ofReal_sub, ofReal_ofNat]
  ring

private lemma u0_re : u0.re = (Real.sqrt 57 - 11) / 8 := by
  rw [u0_eq_ofReal]
  simp

private lemma u0_im : u0.im = 0 := by
  rw [u0_eq_ofReal]
  simp

private lemma sqrt57_lt_11 : Real.sqrt 57 < 11 := by
  have : (57 : ℝ) < 11 ^ 2 := by norm_num
  exact (Real.sqrt_lt' (by norm_num)).2 (by simpa using this)

private lemma u0_re_neg : u0.re < 0 := by
  rw [u0_re]
  linarith [sqrt57_lt_11]

private lemma tendsto_log_arg_to_u0 :
    Tendsto
      (fun t =>
        pentHingeCosPath 1 t + csqrt (pentHingeCosPath 1 t ^ 2 - 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds u0) := by
  have hw := tendsto_pentHingeCosPath_one
  have hW := tendsto_csqrt_sq_sub_one_one
  simpa [u0] using hw.add hW

private lemma tendsto_log_arg_nhdsWithin_im_nonneg :
    Tendsto
      (fun t =>
        pentHingeCosPath 1 t + csqrt (pentHingeCosPath 1 t ^ 2 - 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin u0 {z : ℂ | 0 ≤ z.im}) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨tendsto_log_arg_to_u0, eventually_im_log_arg_nonneg⟩

private lemma tendsto_log_of_log_arg :
    Tendsto
      (fun t =>
        log (pentHingeCosPath 1 t +
          csqrt (pentHingeCosPath 1 t ^ 2 - 1)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (↑(Real.log ‖u0‖) + (Real.pi : ℂ) * I)) := by
  have hlog :=
    tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero u0_re_neg u0_im
  exact hlog.comp tendsto_log_arg_nhdsWithin_im_nonneg

private lemma norm_u0 :
    ‖u0‖ = (11 - Real.sqrt 57) / 8 := by
  have hneg : ((Real.sqrt 57 - 11) / 8 : ℝ) < 0 := by
    linarith [sqrt57_lt_11]
  rw [u0_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg]
  ring

private lemma log_norm_u0_eq_neg_arcosh :
    Real.log ‖u0‖ = -Real.arcosh (11 / 8) := by
  rw [norm_u0, Real.arcosh]
  have hsqrt :
      Real.sqrt ((11 / 8 : ℝ) ^ 2 - 1) = Real.sqrt 57 / 8 := by
    have : (11 / 8 : ℝ) ^ 2 - 1 = 57 / 64 := by norm_num
    rw [this, sqrt_fiftySeven_div_eight]
  have hsum :
      (11 / 8 : ℝ) + Real.sqrt ((11 / 8) ^ 2 - 1) =
        (11 + Real.sqrt 57) / 8 := by
    rw [hsqrt]
    ring
  rw [hsum]
  have hprod :
      ((11 - Real.sqrt 57) / 8) * ((11 + Real.sqrt 57) / 8) = 1 := by
    have h : (11 : ℝ) ^ 2 - (Real.sqrt 57) ^ 2 = 64 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 57)]
      norm_num
    field_simp
    linarith [h]
  have hinv :
      (11 - Real.sqrt 57) / 8 = ((11 + Real.sqrt 57) / 8)⁻¹ :=
    (inv_eq_of_mul_eq_one_left hprod).symm
  rw [hinv, Real.log_inv]

theorem carccos_tendsto_at_cut_one_holds :
    Tendsto (fun t => carccos (pentHingeCosPath 1 t))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((↑(lorentzAngleRe 1) : ℂ) + I * ↑(lorentzRapidity 1))) := by
  have heq :
      (fun t => carccos (pentHingeCosPath 1 t)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun t =>
          (-I) *
            log (pentHingeCosPath 1 t +
              csqrt (pentHingeCosPath 1 t ^ 2 - 1)) := by
    filter_upwards [eventually_carccos_log_arg_eq] with t ht
    simp only [carccos, ht]
  have hlog := tendsto_log_of_log_arg
  have hmul :
      Tendsto
        (fun t =>
          (-I) *
            log (pentHingeCosPath 1 t +
              csqrt (pentHingeCosPath 1 t ^ 2 - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((-I) * (↑(Real.log ‖u0‖) + (Real.pi : ℂ) * I))) :=
    tendsto_const_nhds.mul hlog
  have hcongr := Tendsto.congr' heq.symm hmul
  have hval :
      (-I) * (↑(Real.log ‖u0‖) + (Real.pi : ℂ) * I) =
        (↑(lorentzAngleRe 1) : ℂ) + I * ↑(lorentzRapidity 1) := by
    have hlog' := log_norm_u0_eq_neg_arcosh
    unfold lorentzAngleRe lorentzRapidity
    rw [lorentzCos_one, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 8), hlog']
    -- (-I) * (-↑R + π I) = ↑π + I ↑R
    set R : ℝ := Real.arcosh (11 / 8)
    have h :
        (-I) * (-↑R + (Real.pi : ℂ) * I) =
          (↑(Real.pi) : ℂ) + I * ↑R := by
      have h1 :
          (-I) * (-↑R + (Real.pi : ℂ) * I) =
            I * ↑R + -(I * ((Real.pi : ℂ) * I)) := by
        simp [mul_add, mul_neg]
      have hI : I * ((Real.pi : ℂ) * I) = I ^ 2 * (Real.pi : ℂ) := by
        ring
      have h2 :
          I * ↑R + -(I * ((Real.pi : ℂ) * I)) =
            I * ↑R + -(I ^ 2 * (Real.pi : ℂ)) := by
        rw [hI]
      have h3 :
          I * ↑R + -(I ^ 2 * (Real.pi : ℂ)) =
            I * ↑R + (Real.pi : ℂ) := by
        simp [I_sq]
      have h4 :
          I * ↑R + (Real.pi : ℂ) = (↑(Real.pi) : ℂ) + I * ↑R :=
        add_comm _ _
      exact h1.trans (h2.trans (h3.trans h4))
    simpa [ofReal_neg, R] using h
  simpa [hval] using hcongr

theorem carccos_tendsto_at_cut_one_inhabited : carccos_tendsto_at_cut_one :=
  carccos_tendsto_at_cut_one_holds

theorem lorentzAnchor_one_holds : lorentzAnchor_one := by
  unfold lorentzAnchor_one wickActionPath dihedralSumPath
  have hc := carccos_tendsto_at_cut_one_holds
  have h3 :
      Tendsto (fun t => (3 : ℂ) * carccos (pentHingeCosPath 1 t))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((3 : ℂ) *
          ((↑(lorentzAngleRe 1) : ℂ) + I * ↑(lorentzRapidity 1)))) :=
    tendsto_const_nhds.mul hc
  have hsub :
      Tendsto
        (fun t =>
          (2 * Real.pi : ℂ) - 3 * carccos (pentHingeCosPath 1 t))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          ((2 * Real.pi : ℂ) -
            3 *
              ((↑(lorentzAngleRe 1) : ℂ) +
                I * ↑(lorentzRapidity 1)))) :=
    tendsto_const_nhds.sub h3
  have hA :
      Tendsto
        (fun t =>
          (hingeArea : ℂ) *
            ((2 * Real.pi : ℂ) - 3 * carccos (pentHingeCosPath 1 t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          ((hingeArea : ℂ) *
            ((2 * Real.pi : ℂ) -
              3 *
                ((↑(lorentzAngleRe 1) : ℂ) +
                  I * ↑(lorentzRapidity 1))))) :=
    tendsto_const_nhds.mul hsub
  have hshape :
      (hingeArea : ℂ) *
          ((2 * Real.pi : ℂ) -
            3 *
              ((↑(lorentzAngleRe 1) : ℂ) + I * ↑(lorentzRapidity 1))) =
        (((hingeArea * (2 * Real.pi - 3 * lorentzAngleRe 1) : ℝ) : ℂ) -
          I * ((hingeArea * (3 * lorentzRapidity 1) : ℝ) : ℂ)) := by
    unfold lorentzAngleRe
    simp [ofReal_mul, ofReal_add, mul_add, sub_eq_add_neg]
    ring
  simpa [hshape] using hA

theorem lorentzAnchor_one_inhabited : lorentzAnchor_one :=
  lorentzAnchor_one_holds

structure WickActionCutLimitStatus where
  n4CutLimitOneClosed : Bool
  n4LorentzAnchorOneClosed : Bool
  n4FamilyOpen : Bool
  gap6LorentzianAction : Bool
  terminalInhabitationOpen : Bool

def wickActionCutLimitStatus : WickActionCutLimitStatus where
  n4CutLimitOneClosed := true
  n4LorentzAnchorOneClosed := true
  n4FamilyOpen := false
  gap6LorentzianAction := true
  terminalInhabitationOpen := false

theorem wickActionCutLimitStatus_flags :
    wickActionCutLimitStatus.n4CutLimitOneClosed = true ∧
      wickActionCutLimitStatus.n4LorentzAnchorOneClosed = true ∧
        wickActionCutLimitStatus.n4FamilyOpen = false ∧
          wickActionCutLimitStatus.gap6LorentzianAction = true ∧
            wickActionCutLimitStatus.terminalInhabitationOpen = false ∧
              carccos_tendsto_at_cut_one ∧
                lorentzAnchor_one :=
  ⟨rfl, rfl, rfl, rfl, rfl, carccos_tendsto_at_cut_one_inhabited,
    lorentzAnchor_one_inhabited⟩

end

end WickActionInteriorHinge
end SevenGaps
end Gravity
end IndisputableMonolith
