import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHinge
import IndisputableMonolith.Gravity.SevenGaps.WickThreeTwoHinges

/-!
# Wave C4 N3+N4: Moebius confinement + Lorentzian cut-boundary value

Fable design `D-gap6-r1-design-20260722`, session 2.

* **N3** (α-family, causal range): Moebius collapse, MODEL path equality,
  `Im < 0` confinement, `branchRegularSum` field shape. CLOSED.
* **N4**: cut-boundary Tendsto resisted after honest effort (Mathlib
  one-sided log/csqrt filter API). Design-authorized fallback: named Props
  `carccos_tendsto_at_cut_one` / `lorentzAnchor_one` / family Prop left open;
  decoy `lorentz_endpoint_not_real` and `rapidityPinned_one` CLOSED.
  Re-scopes R5 toward the sharper-blocker packaging path if the limit stays open.

Does **not** inhabit the terminal, flip gap6, or touch Schläfli.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace WickActionInteriorHinge

open Complex
open Filter Topology
open CausalSimplex4D
open WickActionComplexFirst
open WickThreeTwoHinges

noncomputable section

/-! ## §N3a. Arc lemmas -/

theorem continuationEdgesC_threeTwo (α t : ℝ) :
    continuationEdgesC CausalPentType.threeTwo 1 α t =
      hingeEdges32C (arcZ 1 α t) := by
  funext e
  unfold continuationEdgesC hingeEdges32C
  by_cases h : isTimelike CausalPentType.threeTwo e = true
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    norm_num

theorem normSq_arcZ_one (α t : ℝ) :
    Complex.normSq (arcZ 1 α t) = α ^ 2 := by
  unfold arcZ
  simp only [pow_two, mul_one]
  have hexp :
      Complex.normSq (Complex.exp (((Real.pi * (1 - t) : ℝ) : ℂ) * I)) = 1 := by
    have hre := Complex.exp_ofReal_mul_I_re (Real.pi * (1 - t))
    have him := Complex.exp_ofReal_mul_I_im (Real.pi * (1 - t))
    rw [Complex.normSq_apply, hre, him, ← pow_two, ← pow_two]
    exact Real.cos_sq_add_sin_sq (Real.pi * (1 - t))
  rw [Complex.normSq_mul, hexp, mul_one, Complex.normSq_ofReal]

theorem denom_ne_of_causal {α : ℝ} (hα : (7 / 12 : ℝ) < α) (t : ℝ) :
    6 * arcZ 1 α t - 2 ≠ 0 := by
  intro h
  have hpos : 0 < α := lt_trans (by norm_num : (0 : ℝ) < 7 / 12) hα
  have h6 : (6 : ℂ) * arcZ 1 α t = 2 := by linear_combination h
  have hns :
      Complex.normSq ((6 : ℂ) * arcZ 1 α t) = Complex.normSq (2 : ℂ) := by
    rw [h6]
  rw [Complex.normSq_mul, normSq_arcZ_one, Complex.normSq_ofNat,
    Complex.normSq_ofNat] at hns
  have hα2 : α ^ 2 = (1 / 9 : ℝ) := by
    have : (36 : ℝ) * α ^ 2 = 4 := by convert hns using 1 <;> ring
    nlinarith
  have hgt : (1 / 9 : ℝ) < α ^ 2 := by
    have h13 : (1 / 3 : ℝ) < α :=
      lt_trans (by norm_num : (1 / 3 : ℝ) < 7 / 12) hα
    nlinarith [mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 3) h13]
  exact absurd hα2 (ne_of_gt hgt)

theorem arcZ_im_eq (α t : ℝ) :
    (arcZ 1 α t).im = α * Real.sin (Real.pi * (1 - t)) := by
  unfold arcZ
  simp only [pow_two, mul_one]
  rw [mul_im, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_re]
  ring

theorem arcZ_im_pos_of_causal {α t : ℝ} (hα : (7 / 12 : ℝ) < α)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) : 0 < (arcZ 1 α t).im := by
  have hpos : 0 < α := lt_trans (by norm_num : (0 : ℝ) < 7 / 12) hα
  rw [arcZ_im_eq]
  refine mul_pos hpos ?_
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos Real.pi_pos (by linarith [ht.2])
  · calc Real.pi * (1 - t) < Real.pi * 1 :=
        mul_lt_mul_of_pos_left (by linarith [ht.1]) Real.pi_pos
    _ = Real.pi := mul_one _

/-! ## §N3b. Moebius + MODEL path equality -/

theorem pentHingeCosPath_eq_moebius {α : ℝ} (hα : (7 / 12 : ℝ) < α)
    (t : ℝ) :
    pentHingeCosPath α t =
      (5 - 6 * arcZ 1 α t) / (6 * arcZ 1 α t - 2) := by
  unfold pentHingeCosPath dihedralCosSplitC dihedralDenomSplitC
  rw [continuationEdgesC_threeTwo]
  have hv3 : cmVertexIndexC 3 = 4 := rfl
  have hv4 : cmVertexIndexC 4 = 5 := rfl
  rw [hv3, hv4, cof32_d4, cof32_d5, cof32_45,
    csqrt_mul_self (denom_ne_of_causal hα t)]

theorem pentHingeCosPath_eq_moebius_one (t : ℝ) :
    pentHingeCosPath 1 t = (5 - 6 * zArc t) / (6 * zArc t - 2) := by
  simpa [zArc] using
    pentHingeCosPath_eq_moebius (by norm_num : (7 / 12 : ℝ) < 1) t

theorem pentHingeCosPath_one_eq_threeTwo :
    pentHingeCosPath 1 = threeTwoCosPath 3 4 := rfl

theorem euclidCos_one : euclidCos 1 = -(1 / 4) := by
  unfold euclidCos; norm_num

theorem lorentzCos_one : lorentzCos 1 = -(11 / 8) := by
  unfold lorentzCos; norm_num

theorem pentHingeCosPath_eq_euclidCos {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    pentHingeCosPath α 1 = ((euclidCos α : ℝ) : ℂ) := by
  rw [pentHingeCosPath_eq_moebius hα, arcZ_one, euclidCos]
  simp [ofReal_div, ofReal_sub, ofReal_mul, ofReal_ofNat]

theorem pentHingeCosPath_eq_lorentzCos {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    pentHingeCosPath α 0 = ((lorentzCos α : ℝ) : ℂ) := by
  rw [pentHingeCosPath_eq_moebius hα, arcZ_zero]
  have hreal :
      ((5 - 6 * (-α)) / (6 * (-α) - 2) : ℝ) = lorentzCos α := by
    unfold lorentzCos
    have h1 : (5 - 6 * (-α) : ℝ) = 5 + 6 * α := by ring
    have h2 : (6 * (-α) - 2 : ℝ) = -(2 + 6 * α) := by ring
    rw [h1, h2, div_neg]
  simp only [pow_two, mul_one]
  -- `(5 - 6 * ↑(-α)) / ... = ↑((5 - 6 * (-α)) / ...)` by ofReal homomorphism
  have hcast :
      (5 - 6 * ((-α : ℝ) : ℂ)) / (6 * ((-α : ℝ) : ℂ) - 2) =
        ((((5 - 6 * (-α)) / (6 * (-α) - 2)) : ℝ) : ℂ) := by
    norm_cast
  rw [hcast, hreal]

theorem pentHingeCosPath_one_zero :
    pentHingeCosPath 1 0 = ((lorentzCos 1 : ℝ) : ℂ) :=
  pentHingeCosPath_eq_lorentzCos (by norm_num)

theorem pentHingeCosPath_one_one :
    pentHingeCosPath 1 1 = ((euclidCos 1 : ℝ) : ℂ) :=
  pentHingeCosPath_eq_euclidCos (by norm_num)

/-! ## §N3c. Half-plane confinement -/

theorem im_pentHingeCosPath_eq {α : ℝ} (hα : (7 / 12 : ℝ) < α) (t : ℝ) :
    (pentHingeCosPath α t).im =
      (-18 * (arcZ 1 α t).im) / Complex.normSq (6 * arcZ 1 α t - 2) := by
  rw [pentHingeCosPath_eq_moebius hα]
  have hnum :
      (5 - 6 * arcZ 1 α t).im * (6 * arcZ 1 α t - 2).re -
        (5 - 6 * arcZ 1 α t).re * (6 * arcZ 1 α t - 2).im =
        -18 * (arcZ 1 α t).im := by
    simp only [sub_im, sub_re, mul_im, mul_re, re_ofNat, im_ofNat]
    ring
  rw [div_im, div_sub_div_same, hnum]

theorem im_pentHingeCosPath_neg {α : ℝ} (hα : (7 / 12 : ℝ) < α)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (pentHingeCosPath α t).im < 0 := by
  rw [im_pentHingeCosPath_eq hα]
  have hy : 0 < (arcZ 1 α t).im := arcZ_im_pos_of_causal hα ht
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by norm_num) hy)
    (Complex.normSq_pos.mpr (denom_ne_of_causal hα t))

theorem im_pentHingeCosPath_neg_one {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (pentHingeCosPath 1 t).im < 0 :=
  im_pentHingeCosPath_neg (by norm_num) ht

/-! ## §N3d. branchRegularSum field shape -/

theorem branchRegularSum_of_causal {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      OffArccosCut (pentHingeCosPath α t) ∧
        (1 - pentHingeCosPath α t ^ 2) ∈ slitPlane ∧
          (pentHingeCosPath α t + I * csqrt (1 - pentHingeCosPath α t ^ 2)) ∈
            slitPlane := by
  intro t ht
  have hoff : OffArccosCut (pentHingeCosPath α t) :=
    Or.inl (im_pentHingeCosPath_neg hα ht).ne
  exact ⟨hoff, offArccosCut_slitPlane _ hoff⟩

theorem branchRegularSum_one :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      OffArccosCut (pentHingeCosPath 1 t) ∧
        (1 - pentHingeCosPath 1 t ^ 2) ∈ slitPlane ∧
          (pentHingeCosPath 1 t + I * csqrt (1 - pentHingeCosPath 1 t ^ 2)) ∈
            slitPlane :=
  branchRegularSum_of_causal (by norm_num)

/-! ## §N4. Cut-boundary fallback (named Props) + closed decoy/rapidity -/

/-- N4 missing limit at `α = 1` (design fallback: precisely-stated Prop). -/
def carccos_tendsto_at_cut_one : Prop :=
  Tendsto (fun t => carccos (pentHingeCosPath 1 t))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds ((↑(lorentzAngleRe 1) : ℂ) + I * ↑(lorentzRapidity 1)))

/-- Family cut-boundary Prop (open; scope reduction). -/
def carccos_tendsto_at_cut_family : Prop :=
  ∀ α : ℝ, (7 / 12 : ℝ) < α →
    Tendsto (fun t => carccos (pentHingeCosPath α t))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((↑(lorentzAngleRe α) : ℂ) + I * ↑(lorentzRapidity α)))

/-- `lorentzAnchor` field shape at `α = 1` (open; depends on cut Tendsto). -/
def lorentzAnchor_one : Prop :=
  Tendsto (wickActionPath 1) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (nhds
      (((hingeArea * (2 * Real.pi - 3 * lorentzAngleRe 1) : ℝ) : ℂ) -
        I * ((hingeArea * (3 * lorentzRapidity 1) : ℝ) : ℂ)))

theorem rapidityPinned_one : lorentzRapidity 1 ≠ 0 := by
  unfold lorentzRapidity
  rw [lorentzCos_one, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 8)]
  exact (Real.arcosh_pos (by norm_num : (1 : ℝ) < 11 / 8)).ne'

theorem lorentz_endpoint_im_eq :
    (((hingeArea * (2 * Real.pi - 3 * lorentzAngleRe 1) : ℝ) : ℂ) -
        I * ((hingeArea * (3 * lorentzRapidity 1) : ℝ) : ℂ)).im =
      -(3 * hingeArea * lorentzRapidity 1) := by
  simp [sub_im, mul_im, I_re, I_im]
  ring

/-- Decoy falsifier: Lorentzian endpoint action imaginary part nonzero. -/
theorem lorentz_endpoint_not_real :
    (((hingeArea * (2 * Real.pi - 3 * lorentzAngleRe 1) : ℝ) : ℂ) -
        I * ((hingeArea * (3 * lorentzRapidity 1) : ℝ) : ℂ)).im ≠ 0 := by
  rw [lorentz_endpoint_im_eq]
  have hA : 0 < hingeArea :=
    Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3 / 16)
  have hR : 0 < lorentzRapidity 1 := by
    unfold lorentzRapidity
    rw [lorentzCos_one, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 8)]
    exact Real.arcosh_pos (by norm_num : (1 : ℝ) < 11 / 8)
  have hpos : 0 < 3 * hingeArea * lorentzRapidity 1 :=
    mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3) hA) hR
  exact neg_ne_zero.mpr hpos.ne'


end

end WickActionInteriorHinge
end SevenGaps
end Gravity
end IndisputableMonolith
