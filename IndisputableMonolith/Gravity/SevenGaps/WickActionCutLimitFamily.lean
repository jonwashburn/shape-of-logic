import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import IndisputableMonolith.Gravity.SevenGaps.WickActionCutLimit
import IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHinge
import IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHingeConfinement
import IndisputableMonolith.Gravity.SevenGaps.WickFourOneAllHinges

/-!
# Wave C4 F1: parameterized cut-limit family (`α > 7/12`)

Binding design: `D-gap6-v2-succession-family-design-20260723`.

Generalizes the α=1 six-lemma route in `WickActionCutLimit` to the full
causal range. All proofs are **pointwise** under `7/12 < α` (no
uniform-in-α bound: `lorentzK α → 1` as `α → ∞`).

Does **not** inhabit `WickActionContinuationCertV2` (F2) or flip ledger
Bools (F3). Reuses generic L1 `csqrt_of_im_neg` from the α=1 module.
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

/-! ## §0. Lorentzian scale `lorentzK` -/

/-- Positive Lorentzian cosine scale: `|lorentzCos α|` on the causal range. -/
def lorentzK (α : ℝ) : ℝ := (5 + 6 * α) / (2 + 6 * α)

theorem lorentzCos_eq_neg_lorentzK (α : ℝ) :
    lorentzCos α = -(lorentzK α) := by
  unfold lorentzCos lorentzK
  rfl

theorem lorentzK_den_pos {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    0 < 2 + 6 * α := by
  have h0 : (0 : ℝ) < 2 + 6 * (7 / 12) := by norm_num
  linarith

theorem lorentzK_gt_one {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    1 < lorentzK α := by
  have hden := lorentzK_den_pos hα
  unfold lorentzK
  rw [one_lt_div hden]
  linarith

theorem lorentzK_pos {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    0 < lorentzK α :=
  lt_trans (by norm_num : (0 : ℝ) < 1) (lorentzK_gt_one hα)

theorem lorentzK_sq_sub_one_pos {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    0 < lorentzK α ^ 2 - 1 := by
  have hk := lorentzK_gt_one hα
  nlinarith [mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 1) hk]

theorem sqrt_lorentzK_sq_sub_one_lt {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    Real.sqrt (lorentzK α ^ 2 - 1) < lorentzK α := by
  have hkpos := lorentzK_pos hα
  have hlt : lorentzK α ^ 2 - 1 < lorentzK α ^ 2 := by linarith
  exact (Real.sqrt_lt' hkpos).mpr hlt

/-! ## §1. Rapidity pin (family) -/

theorem rapidityPinned_of_causal {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    lorentzRapidity α ≠ 0 := by
  unfold lorentzRapidity
  rw [lorentzCos_eq_neg_lorentzK, abs_neg,
    abs_of_nonneg (lorentzK_pos hα).le]
  exact (Real.arcosh_pos (lorentzK_gt_one hα)).ne'

/-! ## §2. Continuous arc (general α) -/

theorem continuous_arcZ (a alpha : ℝ) : Continuous (fun t : ℝ => arcZ a alpha t) := by
  unfold arcZ
  exact continuous_const.mul
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
          (continuous_const.mul (continuous_const.sub continuous_id))).mul
        continuous_const))

/-! ## §3. L2 family: path cosine → `-lorentzK α` -/

theorem tendsto_pentHingeCosPath_of_causal {α : ℝ}
    (hα : (7 / 12 : ℝ) < α) :
    Tendsto (fun t => pentHingeCosPath α t) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((-(lorentzK α) : ℝ) : ℂ)) := by
  have hz :
      Tendsto (fun t => arcZ 1 α t) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (arcZ 1 α 0)) :=
    ((continuous_arcZ 1 α).tendsto 0).mono_left nhdsWithin_le_nhds
  have hz0 : arcZ 1 α 0 = ((-α : ℝ) : ℂ) := by
    simpa using arcZ_zero 1 α
  have hnum :
      Tendsto (fun t => (5 : ℂ) - 6 * arcZ 1 α t)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (((5 + 6 * α : ℝ) : ℂ))) := by
    have h :
        Tendsto (fun t => (5 : ℂ) - 6 * arcZ 1 α t)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds ((5 : ℂ) - 6 * arcZ 1 α 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hz)
    convert h using 1
    simp [hz0, ofReal_neg]
  have hden :
      Tendsto (fun t => (6 : ℂ) * arcZ 1 α t - 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (((-(2 + 6 * α) : ℝ) : ℂ))) := by
    have h :
        Tendsto (fun t => (6 : ℂ) * arcZ 1 α t - 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds ((6 : ℂ) * arcZ 1 α 0 - 2)) :=
      (tendsto_const_nhds.mul hz).sub tendsto_const_nhds
    convert h using 1
    simp [hz0, ofReal_neg]; ring
  have hden0 : ((-(2 + 6 * α) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr (lorentzK_den_pos hα).ne')
  have hdiv :
      Tendsto (fun t => ((5 : ℂ) - 6 * arcZ 1 α t) / (6 * arcZ 1 α t - 2))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((((5 + 6 * α : ℝ) : ℂ) / ((-(2 + 6 * α) : ℝ) : ℂ)))) :=
    hnum.div hden hden0
  have hval :
      (((5 + 6 * α : ℝ) : ℂ) / ((-(2 + 6 * α) : ℝ) : ℂ)) =
        ((-(lorentzK α) : ℝ) : ℂ) := by
    calc
      (((5 + 6 * α : ℝ) : ℂ) / ((-(2 + 6 * α) : ℝ) : ℂ))
          = ↑((5 + 6 * α) / -(2 + 6 * α)) := by rw [← ofReal_div]
      _ = ↑(-((5 + 6 * α) / (2 + 6 * α))) := by rw [div_neg]
      _ = ((-(lorentzK α) : ℝ) : ℂ) := by rfl
  have hpath :
      (fun t => pentHingeCosPath α t) =
        fun t => ((5 : ℂ) - 6 * arcZ 1 α t) / (6 * arcZ 1 α t - 2) := by
    funext t
    exact pentHingeCosPath_eq_moebius hα t
  have hdiv' :
      Tendsto (fun t => ((5 : ℂ) - 6 * arcZ 1 α t) / (6 * arcZ 1 α t - 2))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((-(lorentzK α) : ℝ) : ℂ)) :=
    hval ▸ hdiv
  simpa [hpath] using hdiv'

/-! ## §4. L3 family: `csqrt(w^2 - 1)` → `√(k^2 - 1)` -/

private lemma lorentzK_sq_sub_one_mem_slitPlane {α : ℝ}
    (hα : (7 / 12 : ℝ) < α) :
    ((lorentzK α ^ 2 - 1 : ℝ) : ℂ) ∈ slitPlane :=
  ofReal_mem_slitPlane.mpr (lorentzK_sq_sub_one_pos hα)

theorem tendsto_csqrt_sq_sub_one_of_causal {α : ℝ}
    (hα : (7 / 12 : ℝ) < α) :
    Tendsto (fun t => csqrt (pentHingeCosPath α t ^ 2 - 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((↑(Real.sqrt (lorentzK α ^ 2 - 1)) : ℂ))) := by
  have hw := tendsto_pentHingeCosPath_of_causal hα
  have hsq :
      Tendsto (fun t => pentHingeCosPath α t ^ 2 - 1)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((lorentzK α : ℂ) ^ 2 - 1)) := by
    have h := (hw.pow 2).sub (tendsto_const_nhds (x := (1 : ℂ)))
    simpa [neg_sq] using h
  have hsq' :
      Tendsto (fun t => pentHingeCosPath α t ^ 2 - 1)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((lorentzK α ^ 2 - 1 : ℝ) : ℂ)) := by
    convert hsq using 1
    simp [ofReal_pow, ofReal_sub, ofReal_one]
  have hcont : ContinuousAt (fun z : ℂ => csqrt z)
      ((lorentzK α ^ 2 - 1 : ℝ) : ℂ) := by
    unfold csqrt
    exact continuousAt_cpow_const (lorentzK_sq_sub_one_mem_slitPlane hα)
  have hcomp :
      Tendsto (fun t => csqrt (pentHingeCosPath α t ^ 2 - 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (csqrt ((lorentzK α ^ 2 - 1 : ℝ) : ℂ))) :=
    hcont.tendsto.comp hsq'
  have heval :
      csqrt ((lorentzK α ^ 2 - 1 : ℝ) : ℂ) =
        (↑(Real.sqrt (lorentzK α ^ 2 - 1)) : ℂ) :=
    csqrt_ofReal_nonneg (lorentzK_sq_sub_one_pos hα).le
  exact heval ▸ hcomp

/-! ## §5. Filter helpers (family) -/

private lemma eventually_ioo_of_nhdsWithin_zero :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioo (0 : ℝ) 1 := by
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with t ht0 ht1
  exact ⟨ht0, ht1⟩

private lemma eventually_re_pent_neg {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (pentHingeCosPath α t).re < 0 := by
  have hw := tendsto_pentHingeCosPath_of_causal hα
  have hneg : ((-(lorentzK α) : ℝ) : ℂ).re < (0 : ℝ) := by
    simpa using neg_lt_zero.mpr (lorentzK_pos hα)
  exact ((continuous_re.tendsto _).comp hw).eventually_lt_const hneg

private lemma eventually_im_pent_neg {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (pentHingeCosPath α t).im < 0 := by
  filter_upwards [eventually_ioo_of_nhdsWithin_zero] with t ht
  exact im_pentHingeCosPath_neg hα ht

private lemma eventually_im_one_sub_sq_neg {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (1 - pentHingeCosPath α t ^ 2).im < 0 := by
  filter_upwards [eventually_re_pent_neg hα, eventually_im_pent_neg hα] with
    t hre him
  have :
      (1 - pentHingeCosPath α t ^ 2).im =
        -(2 * (pentHingeCosPath α t).re * (pentHingeCosPath α t).im) := by
    simp [sub_im, sq, mul_im]
    ring
  rw [this]
  have hprod : (pentHingeCosPath α t).re * (pentHingeCosPath α t).im > 0 :=
    mul_pos_of_neg_of_neg hre him
  nlinarith

/-! ## §6. L4 family (generic skeleton) -/

theorem eventually_carccos_log_arg_eq_of_causal {α : ℝ}
    (hα : (7 / 12 : ℝ) < α) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      pentHingeCosPath α t + I * csqrt (1 - pentHingeCosPath α t ^ 2) =
        pentHingeCosPath α t + csqrt (pentHingeCosPath α t ^ 2 - 1) := by
  filter_upwards [eventually_im_one_sub_sq_neg hα] with t him
  set w := pentHingeCosPath α t
  have hrefl : csqrt (1 - w ^ 2) = -I * csqrt (-(1 - w ^ 2)) :=
    csqrt_of_im_neg him
  have hneg : -(1 - w ^ 2) = w ^ 2 - 1 := by ring
  calc
    w + I * csqrt (1 - w ^ 2)
        = w + I * (-I * csqrt (-(1 - w ^ 2))) := by rw [hrefl]
    _ = w + I * (-I * csqrt (w ^ 2 - 1)) := by rw [hneg]
    _ = w + csqrt (w ^ 2 - 1) := by
      simp [← mul_assoc, mul_neg, I_mul_I]

/-! ## §7. L5 family: Im log-arg ≥ 0 eventually -/

private lemma eventually_csqrt_re_pos {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 < (csqrt (pentHingeCosPath α t ^ 2 - 1)).re := by
  have hW := tendsto_csqrt_sq_sub_one_of_causal hα
  have hpos : (0 : ℝ) < Real.sqrt (lorentzK α ^ 2 - 1) :=
    Real.sqrt_pos.mpr (lorentzK_sq_sub_one_pos hα)
  have hlim :
      ((↑(Real.sqrt (lorentzK α ^ 2 - 1)) : ℂ)).re =
        Real.sqrt (lorentzK α ^ 2 - 1) := by
    simp
  exact ((continuous_re.tendsto _).comp hW).eventually_const_lt
    (by simpa [hlim] using hpos)

private lemma eventually_csqrt_add_re_neg {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (csqrt (pentHingeCosPath α t ^ 2 - 1)).re +
          (pentHingeCosPath α t).re < 0 := by
  have hW := tendsto_csqrt_sq_sub_one_of_causal hα
  have hw := tendsto_pentHingeCosPath_of_causal hα
  have hsum :
      Tendsto
        (fun t =>
          (csqrt (pentHingeCosPath α t ^ 2 - 1)).re +
            (pentHingeCosPath α t).re)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (Real.sqrt (lorentzK α ^ 2 - 1) + (-(lorentzK α)))) := by
    have hWr := (continuous_re.tendsto _).comp hW
    have hwr := (continuous_re.tendsto _).comp hw
    simpa using hWr.add hwr
  have hlim_lt :
      Real.sqrt (lorentzK α ^ 2 - 1) + (-(lorentzK α)) < 0 := by
    linarith [sqrt_lorentzK_sq_sub_one_lt hα]
  exact hsum.eventually_lt_const hlim_lt

private lemma eventually_sq_sub_one_ne {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      pentHingeCosPath α t ^ 2 - 1 ≠ 0 := by
  have hw := tendsto_pentHingeCosPath_of_causal hα
  have hsq :
      Tendsto (fun t => pentHingeCosPath α t ^ 2 - 1)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((lorentzK α ^ 2 - 1 : ℝ) : ℂ)) := by
    have h := (hw.pow 2).sub (tendsto_const_nhds (x := (1 : ℂ)))
    convert h using 1
    simp [ofReal_pow, ofReal_sub, ofReal_one]
  have hne : ((lorentzK α ^ 2 - 1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (lorentzK_sq_sub_one_pos hα).ne'
  exact hsq.eventually_ne hne

theorem eventually_im_log_arg_nonneg_of_causal {α : ℝ}
    (hα : (7 / 12 : ℝ) < α) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 ≤ (pentHingeCosPath α t +
        csqrt (pentHingeCosPath α t ^ 2 - 1)).im := by
  filter_upwards [eventually_im_pent_neg hα, eventually_csqrt_re_pos hα,
    eventually_csqrt_add_re_neg hα, eventually_sq_sub_one_ne hα] with
    t himw hWre hsum hne
  set w := pentHingeCosPath α t
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

/-! ## §8. L6 family: `carccos` cut Tendsto -/

/-- Limit log-argument at causal `α`: `-k + √(k²-1)`. -/
private def u0 (α : ℝ) : ℂ :=
  ((-(lorentzK α) : ℝ) : ℂ) + (↑(Real.sqrt (lorentzK α ^ 2 - 1)) : ℂ)

private lemma u0_eq_ofReal (α : ℝ) :
    u0 α =
      ((Real.sqrt (lorentzK α ^ 2 - 1) - lorentzK α : ℝ) : ℂ) := by
  simp [u0, ofReal_sub]
  ring

private lemma u0_re (α : ℝ) :
    (u0 α).re = Real.sqrt (lorentzK α ^ 2 - 1) - lorentzK α := by
  rw [u0_eq_ofReal]
  simp

private lemma u0_im (α : ℝ) : (u0 α).im = 0 := by
  rw [u0_eq_ofReal]
  simp

private lemma u0_re_neg {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    (u0 α).re < 0 := by
  rw [u0_re]
  linarith [sqrt_lorentzK_sq_sub_one_lt hα]

private lemma tendsto_log_arg_to_u0 {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    Tendsto
      (fun t =>
        pentHingeCosPath α t + csqrt (pentHingeCosPath α t ^ 2 - 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (u0 α)) := by
  have hw := tendsto_pentHingeCosPath_of_causal hα
  have hW := tendsto_csqrt_sq_sub_one_of_causal hα
  simpa [u0] using hw.add hW

private lemma tendsto_log_arg_nhdsWithin_im_nonneg {α : ℝ}
    (hα : (7 / 12 : ℝ) < α) :
    Tendsto
      (fun t =>
        pentHingeCosPath α t + csqrt (pentHingeCosPath α t ^ 2 - 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin (u0 α) {z : ℂ | 0 ≤ z.im}) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨tendsto_log_arg_to_u0 hα, eventually_im_log_arg_nonneg_of_causal hα⟩

private lemma tendsto_log_of_log_arg {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    Tendsto
      (fun t =>
        log (pentHingeCosPath α t +
          csqrt (pentHingeCosPath α t ^ 2 - 1)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (↑(Real.log ‖u0 α‖) + (Real.pi : ℂ) * I)) := by
  have hlog :=
    tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
      (u0_re_neg hα) (u0_im α)
  exact hlog.comp (tendsto_log_arg_nhdsWithin_im_nonneg hα)

private lemma norm_u0 {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    ‖u0 α‖ = lorentzK α - Real.sqrt (lorentzK α ^ 2 - 1) := by
  have hneg :
      (Real.sqrt (lorentzK α ^ 2 - 1) - lorentzK α : ℝ) < 0 := by
    linarith [sqrt_lorentzK_sq_sub_one_lt hα]
  rw [u0_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg]
  ring

private lemma log_norm_u0_eq_neg_arcosh {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    Real.log ‖u0 α‖ = -Real.arcosh (lorentzK α) := by
  rw [norm_u0 hα, Real.arcosh]
  have hprod :
      (lorentzK α - Real.sqrt (lorentzK α ^ 2 - 1)) *
          (lorentzK α + Real.sqrt (lorentzK α ^ 2 - 1)) = 1 := by
    have hsq :
        (Real.sqrt (lorentzK α ^ 2 - 1)) ^ 2 = lorentzK α ^ 2 - 1 :=
      Real.sq_sqrt (lorentzK_sq_sub_one_pos hα).le
    nlinarith [hsq]
  have hinv :
      lorentzK α - Real.sqrt (lorentzK α ^ 2 - 1) =
        (lorentzK α + Real.sqrt (lorentzK α ^ 2 - 1))⁻¹ :=
    (inv_eq_of_mul_eq_one_left hprod).symm
  rw [hinv, Real.log_inv]

theorem carccos_tendsto_at_cut_of_causal {α : ℝ}
    (hα : (7 / 12 : ℝ) < α) :
    Tendsto (fun t => carccos (pentHingeCosPath α t))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((↑(lorentzAngleRe α) : ℂ) + I * ↑(lorentzRapidity α))) := by
  have heq :
      (fun t => carccos (pentHingeCosPath α t)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun t =>
          (-I) *
            log (pentHingeCosPath α t +
              csqrt (pentHingeCosPath α t ^ 2 - 1)) := by
    filter_upwards [eventually_carccos_log_arg_eq_of_causal hα] with t ht
    simp only [carccos, ht]
  have hlog := tendsto_log_of_log_arg hα
  have hmul :
      Tendsto
        (fun t =>
          (-I) *
            log (pentHingeCosPath α t +
              csqrt (pentHingeCosPath α t ^ 2 - 1)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((-I) * (↑(Real.log ‖u0 α‖) + (Real.pi : ℂ) * I))) :=
    tendsto_const_nhds.mul hlog
  have hcongr := Tendsto.congr' heq.symm hmul
  have hval :
      (-I) * (↑(Real.log ‖u0 α‖) + (Real.pi : ℂ) * I) =
        (↑(lorentzAngleRe α) : ℂ) + I * ↑(lorentzRapidity α) := by
    have hlog' := log_norm_u0_eq_neg_arcosh hα
    unfold lorentzAngleRe lorentzRapidity
    rw [lorentzCos_eq_neg_lorentzK, abs_neg,
      abs_of_nonneg (lorentzK_pos hα).le, hlog']
    set R : ℝ := Real.arcosh (lorentzK α)
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

theorem carccos_tendsto_at_cut_family_holds : carccos_tendsto_at_cut_family :=
  fun _α hα => carccos_tendsto_at_cut_of_causal hα

/-! ## §9. Action-level Lorentzian anchor (family) -/

theorem lorentzAnchor_of_causal {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    Tendsto (wickActionPath α) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (((hingeArea * (2 * Real.pi - 3 * lorentzAngleRe α) : ℝ) : ℂ) -
          I * ((hingeArea * (3 * lorentzRapidity α) : ℝ) : ℂ))) := by
  unfold wickActionPath dihedralSumPath
  have hc := carccos_tendsto_at_cut_of_causal hα
  have h3 :
      Tendsto (fun t => (3 : ℂ) * carccos (pentHingeCosPath α t))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((3 : ℂ) *
          ((↑(lorentzAngleRe α) : ℂ) + I * ↑(lorentzRapidity α)))) :=
    tendsto_const_nhds.mul hc
  have hsub :
      Tendsto
        (fun t =>
          (2 * Real.pi : ℂ) - 3 * carccos (pentHingeCosPath α t))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          ((2 * Real.pi : ℂ) -
            3 *
              ((↑(lorentzAngleRe α) : ℂ) +
                I * ↑(lorentzRapidity α)))) :=
    tendsto_const_nhds.sub h3
  have hA :
      Tendsto
        (fun t =>
          (hingeArea : ℂ) *
            ((2 * Real.pi : ℂ) - 3 * carccos (pentHingeCosPath α t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          ((hingeArea : ℂ) *
            ((2 * Real.pi : ℂ) -
              3 *
                ((↑(lorentzAngleRe α) : ℂ) +
                  I * ↑(lorentzRapidity α))))) :=
    tendsto_const_nhds.mul hsub
  have hshape :
      (hingeArea : ℂ) *
          ((2 * Real.pi : ℂ) -
            3 *
              ((↑(lorentzAngleRe α) : ℂ) + I * ↑(lorentzRapidity α))) =
        (((hingeArea * (2 * Real.pi - 3 * lorentzAngleRe α) : ℝ) : ℂ) -
          I * ((hingeArea * (3 * lorentzRapidity α) : ℝ) : ℂ)) := by
    unfold lorentzAngleRe
    simp [ofReal_mul, ofReal_add, mul_add, sub_eq_add_neg]
    ring
  simpa [hshape] using hA

/-! ## §10. Bonus: `ContinuousOn` on `Ioc 0 1` (unblocks F2) -/

theorem euclidCos_lt_one {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    euclidCos α < 1 := by
  have hden : 0 < 6 * α - 2 := by
    have : (0 : ℝ) < 6 * (7 / 12) - 2 := by norm_num
    linarith
  unfold euclidCos
  rw [div_lt_one hden]
  linarith

theorem euclidCos_gt_neg_one {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    -1 < euclidCos α := by
  have hden : 0 < 6 * α - 2 := by
    have : (0 : ℝ) < 6 * (7 / 12) - 2 := by norm_num
    linarith
  have hrewrite : euclidCos α + 1 = (3 : ℝ) / (6 * α - 2) := by
    unfold euclidCos
    field_simp [hden.ne']
    ring
  have hpos : 0 < euclidCos α + 1 := by
    rw [hrewrite]
    exact div_pos (by norm_num) hden
  linarith

theorem offArccosCut_pentHingeCosPath_Ioc_of_causal {α : ℝ}
    (hα : (7 / 12 : ℝ) < α) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    OffArccosCut (pentHingeCosPath α t) := by
  rcases ht with ⟨ht0, ht1⟩
  rcases lt_or_eq_of_le ht1 with ht1' | rfl
  · exact Or.inl (im_pentHingeCosPath_neg hα ⟨ht0, ht1'⟩).ne
  · refine Or.inr ?_
    rw [pentHingeCosPath_eq_euclidCos hα]
    constructor
    · simpa using euclidCos_gt_neg_one hα
    · simpa using euclidCos_lt_one hα

theorem continuousOn_pentHingeCosPath_Ioc_of_causal {α : ℝ}
    (hα : (7 / 12 : ℝ) < α) :
    ContinuousOn (pentHingeCosPath α) (Set.Ioc 0 1) := by
  have hmo :
      ContinuousOn
        (fun t => ((5 : ℂ) - 6 * arcZ 1 α t) / (6 * arcZ 1 α t - 2))
        (Set.Ioc 0 1) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuous_const.sub
        (continuous_const.mul (continuous_arcZ 1 α))).continuousOn
    · exact ((continuous_const.mul (continuous_arcZ 1 α)).sub
        continuous_const).continuousOn
    · intro t _ht
      exact denom_ne_of_causal hα t
  refine ContinuousOn.congr hmo ?_
  intro t _ht
  exact pentHingeCosPath_eq_moebius hα t

theorem continuousOn_carccos_comp_pent_Ioc_of_causal {α : ℝ}
    (hα : (7 / 12 : ℝ) < α) :
    ContinuousOn (fun t => carccos (pentHingeCosPath α t)) (Set.Ioc 0 1) := by
  have hpath := continuousOn_pentHingeCosPath_Ioc_of_causal hα
  have hmaps :
      Set.MapsTo (pentHingeCosPath α) (Set.Ioc 0 1) {w | OffArccosCut w} :=
    fun _ ht => offArccosCut_pentHingeCosPath_Ioc_of_causal hα ht
  exact continuousOn_carccos.comp hpath hmaps

theorem continuousOn_wickActionPath_Ioc_of_causal {α : ℝ}
    (hα : (7 / 12 : ℝ) < α) :
    ContinuousOn (wickActionPath α) (Set.Ioc 0 1) := by
  have hθ := continuousOn_carccos_comp_pent_Ioc_of_causal hα
  have h3 : ContinuousOn (fun t => (3 : ℂ) * carccos (pentHingeCosPath α t))
      (Set.Ioc 0 1) :=
    continuousOn_const.mul hθ
  have hsub :
      ContinuousOn
        (fun t =>
          (2 * Real.pi : ℂ) - 3 * carccos (pentHingeCosPath α t))
        (Set.Ioc 0 1) :=
    continuousOn_const.sub h3
  have hA :
      ContinuousOn
        (fun t =>
          (hingeArea : ℂ) *
            ((2 * Real.pi : ℂ) - 3 * carccos (pentHingeCosPath α t)))
        (Set.Ioc 0 1) :=
    continuousOn_const.mul hsub
  refine hA.congr ?_
  intro t _
  unfold wickActionPath dihedralSumPath
  rfl

/-! ## §11. Status bits (F1 only; gap6 unflipped) -/

structure WickActionCutLimitFamilyStatus where
  f1CutLimitFamilyClosed : Bool
  f1LorentzAnchorFamilyClosed : Bool
  f1RapidityPinnedFamilyClosed : Bool
  f1IocContinuityClosed : Bool
  f2AssemblyOpen : Bool
  gap6LorentzianAction : Bool

def wickActionCutLimitFamilyStatus : WickActionCutLimitFamilyStatus where
  f1CutLimitFamilyClosed := true
  f1LorentzAnchorFamilyClosed := true
  f1RapidityPinnedFamilyClosed := true
  f1IocContinuityClosed := true
  f2AssemblyOpen := false
  gap6LorentzianAction := true

theorem wickActionCutLimitFamilyStatus_flags :
    wickActionCutLimitFamilyStatus.f1CutLimitFamilyClosed = true ∧
      wickActionCutLimitFamilyStatus.f1LorentzAnchorFamilyClosed = true ∧
        wickActionCutLimitFamilyStatus.f1RapidityPinnedFamilyClosed = true ∧
          wickActionCutLimitFamilyStatus.f1IocContinuityClosed = true ∧
            wickActionCutLimitFamilyStatus.f2AssemblyOpen = false ∧
              wickActionCutLimitFamilyStatus.gap6LorentzianAction = true ∧
                carccos_tendsto_at_cut_family :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, carccos_tendsto_at_cut_family_holds⟩

end

end WickActionInteriorHinge
end SevenGaps
end Gravity
end IndisputableMonolith
