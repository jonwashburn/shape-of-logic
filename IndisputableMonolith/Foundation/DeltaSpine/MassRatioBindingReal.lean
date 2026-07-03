import Mathlib
import IndisputableMonolith.Foundation.DeltaSpine.MassRatioBinding
import IndisputableMonolith.Foundation.DeltaSpine.GoldenIntReal
import IndisputableMonolith.RSBridge.Anchor

/-!
# Mass Ratio Binding: σ1 Real Display (muon/electron ↔ rung 11)

**Forcing tier: σ1 (CHOICE).** This module is the *display layer* for
`MassRatioBinding.lean` (the σ0 kernel-decided facts). Everything here is a
real-number reading of certificates the kernel already verified by `decide`
on ℤ[φ]; the only new mathematical content is:

* the interpretation map `toReal : ℤ[φ] → ℝ` (noncomputable, σ1), and
* the RS model linkage via `RSBridge.anchor_ratio`.

## What is proved

Let `R` be any real number in the CODATA-2022 ±10σ window for the
muon/electron mass ratio (`muEWindow R`, i.e. `R ∈ [206.7682367, 206.7683287]`).
Then, writing `φ` for the golden ratio and `L := log_φ R`:

1. `muE_window_between_rungs`: `φ^11 < R < φ^12` — the measured ratio sits
   strictly between two adjacent φ-rungs.
2. `muE_logb_window`: `11 < L < 12`.
3. `muE_logb_halfstep`: `21/2 < L < 23/2` — `R²` lies between `φ^21` and
   `φ^23`, so `L` is within a half-step of 11.
4. `muE_nearest_rung_unique`: rung 11 is the **unique nearest integer rung**:
   for every integer `n ≠ 11`, `|L - 11| < |L - n|`.
5. `muE_epsilon_bracket`: the deviation `ε := L - 11` satisfies
   `5/63 < ε < 7/88` (i.e. `0.0794 < ε < 0.0795…`), a kernel-certified
   two-sided bracket ~0.2% wide.
6. `epsilon_upper_lt_inv_four_pi`: `7/88 < 1/(4π)`, hence
   `muE_deviation_refutes_inv4pi`: `ε < 1/(4π)` — the measured deviation is
   strictly below the `1/(4π)` curvature-scale candidate, refuting
   `ε = 1/(4π)` (≈ 0.0796) as an exact identification.
7. `muE_anchor_prediction`: the RS anchor model itself predicts
   `m_μ/m_e = φ^11` at the anchor scale: electron and muon share
   `Z = 1332`, so `anchor_ratio` collapses to the pure rung gap
   `rung μ − rung e = 13 − 2 = 11`.
8. `muE_rung_gap_certified`: the capstone bundle — the model's φ^11
   prediction and the measured window's bracket `(φ^11, φ^12)`, nearest-rung
   uniqueness, and the ε bracket, all in one statement.

## Honest status

* The six inequalities on `R` are THEOREMs conditional only on the MEASURED
  hypothesis `muEWindow R` (CODATA 2022, ±10σ). The kernel arithmetic behind
  them is σ0 (`MassRatioBinding.lean`).
* `muE_anchor_prediction` is a THEOREM about the RS **model** `massAtAnchor`
  (rung assignments are definitional inputs; see `RSBridge/Anchor.lean`).
* The *identification* of the measured ratio with the model's anchor ratio
  (i.e. that physical masses at the anchor scale realize `massAtAnchor`) is
  the standing RS phenomenology claim, NOT proved here. What IS proved: the
  model says φ^11 exactly, the measurement says φ^11 · φ^ε with
  ε ∈ (5/63, 7/88), and ε < 1/(4π). The residual ε is the open QED-dressing
  seam, stated honestly as a bracket.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DeltaSpine

open GoldenInt

/-- The CODATA-2022 ±10σ window for the muon/electron mass ratio, as a
    predicate on a real number `R`. Numerically `[206.7682367, 206.7683287]`
    (central value 206.7682827, σ = 4.6e-6). MEASURED hypothesis. -/
def muEWindow (R : ℝ) : Prop :=
  (muE_lo : ℝ) / (muE_scale : ℝ) ≤ R ∧ R ≤ (muE_hi : ℝ) / (muE_scale : ℝ)

private lemma muE_scale_pos : (0 : ℤ) < muE_scale := by norm_num [muE_scale]

private lemma muE_lo_div_pos : (0 : ℝ) < (muE_lo : ℝ) / (muE_scale : ℝ) := by
  norm_num [muE_lo, muE_scale]

/-- Any ratio in the window is positive. -/
theorem muEWindow_pos {R : ℝ} (hR : muEWindow R) : 0 < R :=
  lt_of_lt_of_le muE_lo_div_pos hR.1

/-! ## Level 1: the window sits strictly between rungs 11 and 12 -/

/-- σ1 reading of the σ0 window certificates: `φ^11 < R < φ^12`. -/
theorem muE_window_between_rungs {R : ℝ} (hR : muEWindow R) :
    PhiForcing.φ ^ (11 : ℕ) < R ∧ R < PhiForcing.φ ^ (12 : ℕ) := by
  obtain ⟨hlo, hhi⟩ := hR
  have h1 := ratGt_toReal muE_scale_pos muE_window_lower
  have h2 := ratLt_toReal muE_scale_pos muE_window_upper
  rw [toReal_phiPow] at h1 h2
  exact ⟨lt_of_lt_of_le h1 hlo, lt_of_le_of_lt hhi h2⟩

/-! ## Level 2: half-step bracket via `R²` -/

/-- σ1 reading of the σ0 square certificates: `φ^21 < R² < φ^23`. -/
theorem muE_sq_between {R : ℝ} (hR : muEWindow R) :
    PhiForcing.φ ^ (21 : ℕ) < R ^ 2 ∧ R ^ 2 < PhiForcing.φ ^ (23 : ℕ) := by
  obtain ⟨hlo, hhi⟩ := hR
  have hRpos := muEWindow_pos ⟨hlo, hhi⟩
  constructor
  · have h1 := ratGt_toReal (pow_pos muE_scale_pos 2) muE_nearest_rung_lower
    rw [toReal_phiPow] at h1
    push_cast at h1
    have hsq : ((muE_lo : ℝ) / (muE_scale : ℝ)) ^ 2 ≤ R ^ 2 :=
      pow_le_pow_left₀ (le_of_lt muE_lo_div_pos) hlo 2
    rw [div_pow] at hsq
    exact lt_of_lt_of_le h1 hsq
  · have h2 := ratLt_toReal (pow_pos muE_scale_pos 2) muE_nearest_rung_upper
    rw [toReal_phiPow] at h2
    push_cast at h2
    have hsq : R ^ 2 ≤ ((muE_hi : ℝ) / (muE_scale : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hRpos) hhi 2
    rw [div_pow] at hsq
    exact lt_of_le_of_lt hsq h2

/-! ## Level 3: tight deviation bracket via `R^63` and `R^88` -/

/-- σ1 reading of the σ0 deviation certificates: `φ^698 < R^63`. -/
theorem muE_pow63_gt {R : ℝ} (hR : muEWindow R) :
    PhiForcing.φ ^ (698 : ℕ) < R ^ 63 := by
  obtain ⟨hlo, _⟩ := hR
  have h1 := ratGt_toReal (pow_pos muE_scale_pos 63) muE_deviation_lower
  rw [toReal_phiPow] at h1
  push_cast at h1
  have hp : ((muE_lo : ℝ) / (muE_scale : ℝ)) ^ 63 ≤ R ^ 63 :=
    pow_le_pow_left₀ (le_of_lt muE_lo_div_pos) hlo 63
  rw [div_pow] at hp
  exact lt_of_lt_of_le h1 hp

/-- σ1 reading of the σ0 deviation certificates: `R^88 < φ^975`. -/
theorem muE_pow88_lt {R : ℝ} (hR : muEWindow R) :
    R ^ 88 < PhiForcing.φ ^ (975 : ℕ) := by
  have hRpos := muEWindow_pos hR
  obtain ⟨_, hhi⟩ := hR
  have h2 := ratLt_toReal (pow_pos muE_scale_pos 88) muE_deviation_upper
  rw [toReal_phiPow] at h2
  push_cast at h2
  have hp : R ^ 88 ≤ ((muE_hi : ℝ) / (muE_scale : ℝ)) ^ 88 :=
    pow_le_pow_left₀ (le_of_lt hRpos) hhi 88
  rw [div_pow] at hp
  exact lt_of_le_of_lt hp h2

/-! ## Logarithmic display: `L = log_φ R` -/

private lemma logb_lift_lower {R : ℝ} {a k : ℕ}
    (h : PhiForcing.φ ^ a < R ^ k) :
    (a : ℝ) < (k : ℝ) * Real.logb PhiForcing.φ R := by
  have hb : (1 : ℝ) < PhiForcing.φ := PhiForcing.phi_gt_one
  have hx : (0 : ℝ) < PhiForcing.φ ^ a := pow_pos PhiForcing.phi_pos a
  have hlt := Real.logb_lt_logb hb hx h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hb, mul_one] at hlt
  exact hlt

private lemma logb_lift_upper {R : ℝ} (hR : 0 < R) {a k : ℕ}
    (h : R ^ k < PhiForcing.φ ^ a) :
    (k : ℝ) * Real.logb PhiForcing.φ R < (a : ℝ) := by
  have hb : (1 : ℝ) < PhiForcing.φ := PhiForcing.phi_gt_one
  have hx : (0 : ℝ) < R ^ k := pow_pos hR k
  have hlt := Real.logb_lt_logb hb hx h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hb, mul_one] at hlt
  exact hlt

/-- `11 < log_φ R < 12`: the measured ratio's φ-logarithm sits strictly
    between the adjacent integer rungs. -/
theorem muE_logb_window {R : ℝ} (hR : muEWindow R) :
    (11 : ℝ) < Real.logb PhiForcing.φ R ∧ Real.logb PhiForcing.φ R < 12 := by
  have hRpos := muEWindow_pos hR
  obtain ⟨h1, h2⟩ := muE_window_between_rungs hR
  have hl : (11 : ℝ) < 1 * Real.logb PhiForcing.φ R := by
    exact_mod_cast logb_lift_lower (k := 1) (by simpa using h1)
  have hu : (1 : ℝ) * Real.logb PhiForcing.φ R < 12 := by
    exact_mod_cast logb_lift_upper hRpos (k := 1) (by simpa using h2)
  constructor <;> linarith

/-- `21/2 < log_φ R < 23/2`: the φ-logarithm is within a half-step of 11,
    so 11 is a nearest integer rung. -/
theorem muE_logb_halfstep {R : ℝ} (hR : muEWindow R) :
    (21 : ℝ) / 2 < Real.logb PhiForcing.φ R ∧
    Real.logb PhiForcing.φ R < (23 : ℝ) / 2 := by
  have hRpos := muEWindow_pos hR
  obtain ⟨h1, h2⟩ := muE_sq_between hR
  have hl : (21 : ℝ) < 2 * Real.logb PhiForcing.φ R := by
    exact_mod_cast logb_lift_lower (k := 2) h1
  have hu : (2 : ℝ) * Real.logb PhiForcing.φ R < 23 := by
    exact_mod_cast logb_lift_upper hRpos (k := 2) h2
  constructor <;> linarith

/-- Rung 11 is the **unique nearest integer rung** to `log_φ R`:
    every other integer is strictly farther away. -/
theorem muE_nearest_rung_unique {R : ℝ} (hR : muEWindow R) :
    ∀ n : ℤ, n ≠ 11 →
      |Real.logb PhiForcing.φ R - 11| < |Real.logb PhiForcing.φ R - (n : ℝ)| := by
  intro n hn
  set L := Real.logb PhiForcing.φ R with hLdef
  obtain ⟨h1, h2⟩ := muE_logb_halfstep hR
  have habs : |L - 11| < 1 / 2 := by
    rw [abs_lt]; constructor <;> linarith
  have hn1 : (1 : ℝ) ≤ |(n : ℝ) - 11| := by
    have h : (1 : ℤ) ≤ |n - 11| := Int.one_le_abs (sub_ne_zero.mpr hn)
    exact_mod_cast h
  have htri : |(n : ℝ) - 11| ≤ |(n : ℝ) - L| + |L - 11| := abs_sub_le _ L _
  have hcomm : |L - (n : ℝ)| = |(n : ℝ) - L| := abs_sub_comm L _
  rw [hcomm]
  linarith

/-- The kernel-certified two-sided deviation bracket:
    `5/63 < log_φ R − 11 < 7/88` (≈ `0.07937 < ε < 0.07955`). -/
theorem muE_epsilon_bracket {R : ℝ} (hR : muEWindow R) :
    (5 : ℝ) / 63 < Real.logb PhiForcing.φ R - 11 ∧
    Real.logb PhiForcing.φ R - 11 < (7 : ℝ) / 88 := by
  have hRpos := muEWindow_pos hR
  have hl : (698 : ℝ) < 63 * Real.logb PhiForcing.φ R := by
    exact_mod_cast logb_lift_lower (k := 63) (muE_pow63_gt hR)
  have hu : (88 : ℝ) * Real.logb PhiForcing.φ R < 975 := by
    exact_mod_cast logb_lift_upper hRpos (k := 88) (muE_pow88_lt hR)
  constructor
  · linarith
  · linarith

/-! ## Refuting ε = 1/(4π) -/

/-- `7/88 < 1/(4π)`: the certified upper bound on the deviation is strictly
    below the `1/(4π)` candidate (uses `π < 3.1416`, Mathlib `pi_lt_d4`). -/
theorem epsilon_upper_lt_inv_four_pi : (7 : ℝ) / 88 < 1 / (4 * Real.pi) := by
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

/-- The measured deviation is strictly below `1/(4π)`: the exact
    identification `ε = 1/(4π)` is refuted by the CODATA window. -/
theorem muE_deviation_refutes_inv4pi {R : ℝ} (hR : muEWindow R) :
    Real.logb PhiForcing.φ R - 11 < 1 / (4 * Real.pi) :=
  lt_trans (muE_epsilon_bracket hR).2 epsilon_upper_lt_inv_four_pi

/-! ## RS model linkage: the anchor model predicts exactly φ^11 -/

/-- Electron and muon carry the same charge-index `Z = 1332`. -/
theorem muE_equal_Z : RSBridge.ZOf RSBridge.Fermion.mu = RSBridge.ZOf RSBridge.Fermion.e := rfl

/-- The RS anchor model's prediction: `m_μ/m_e = φ^11` exactly at the anchor
    scale. Same-Z species cancel the gap term, leaving the pure rung gap
    `rung μ − rung e = 13 − 2 = 11`. -/
theorem muE_anchor_prediction :
    RSBridge.massAtAnchor RSBridge.Fermion.mu / RSBridge.massAtAnchor RSBridge.Fermion.e
      = PhiForcing.φ ^ (11 : ℕ) := by
  rw [RSBridge.anchor_ratio _ _ muE_equal_Z]
  have hrung : ((RSBridge.rung RSBridge.Fermion.mu : ℝ) - (RSBridge.rung RSBridge.Fermion.e : ℝ))
      = ((11 : ℕ) : ℝ) := by
    norm_num [RSBridge.rung]
  rw [hrung, Real.exp_nat_mul,
      show Constants.phi = PhiForcing.φ from rfl,
      Real.exp_log PhiForcing.phi_pos]

/-! ## Capstone -/

/-- **Capstone (σ1 display).** For any `R` in the CODATA ±10σ window for
    `m_μ/m_e`:

    * the RS anchor model predicts the ratio is exactly `φ^11`;
    * the measured window sits strictly inside `(φ^11, φ^12)`;
    * 11 is the unique nearest integer rung to `log_φ R`;
    * the deviation `ε = log_φ R − 11` is bracketed in `(5/63, 7/88)`;
    * `ε < 1/(4π)` (the curvature-candidate identification is refuted).

    Kernel content is σ0 (`MassRatioBinding.lean`); this statement is its
    σ1 real-number reading plus the model linkage. -/
theorem muE_rung_gap_certified {R : ℝ} (hR : muEWindow R) :
    (RSBridge.massAtAnchor RSBridge.Fermion.mu / RSBridge.massAtAnchor RSBridge.Fermion.e
        = PhiForcing.φ ^ (11 : ℕ))
    ∧ (PhiForcing.φ ^ (11 : ℕ) < R ∧ R < PhiForcing.φ ^ (12 : ℕ))
    ∧ (∀ n : ℤ, n ≠ 11 →
        |Real.logb PhiForcing.φ R - 11| < |Real.logb PhiForcing.φ R - (n : ℝ)|)
    ∧ ((5 : ℝ) / 63 < Real.logb PhiForcing.φ R - 11 ∧
        Real.logb PhiForcing.φ R - 11 < (7 : ℝ) / 88)
    ∧ Real.logb PhiForcing.φ R - 11 < 1 / (4 * Real.pi) :=
  ⟨muE_anchor_prediction,
   muE_window_between_rungs hR,
   muE_nearest_rung_unique hR,
   muE_epsilon_bracket hR,
   muE_deviation_refutes_inv4pi hR⟩

end DeltaSpine
end Foundation
end IndisputableMonolith
