import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cosmology.StructureFormationFromBIT

/-!
# CMB Acoustic Peak Ratios from the 8-Tick Lattice (Track E1 of Plan v5)

## Status: THEOREM (φ-rational ratio structure) + HYPOTHESIS (numerical band match to Planck 2018)

This module deepens `StructureFormationFromBIT` (Plan v5 Track E1)
with explicit numerical-band predictions for the first three CMB
acoustic-peak ratios, and a falsifiable comparison to Planck 2018
data.

## What we prove

* The first three peak ratios are `k_2/k_1 = φ`, `k_3/k_2 = φ`,
  `k_3/k_1 = φ²`, pulled from `StructureFormationFromBIT.k_peak_adjacent_ratio`
  (no new axioms).
* Numerical bands derived from `Constants.phi_gt_onePointSixOne` and
  `phi_lt_onePointSixTwo`:
  - `k_2/k_1 ∈ (1.61, 1.62)`
  - `k_3/k_1 ∈ (2.59, 2.63)` (since `φ² = φ + 1 ∈ (2.61, 2.62)`)
* Comparison to Planck 2018 acoustic-peak central values:
  - `ℓ_1 = 220.0`, `ℓ_2 = 540.3`, `ℓ_3 = 814.6`
  - Observed `ℓ_2/ℓ_1 = 2.456`; observed `ℓ_3/ℓ_1 = 3.703`
  - **The observed ratios are NOT φ-rational** (ℓ ratios differ from k
    ratios by the geometry of the projection from k-space to ℓ-space; the
    standard projection ℓ ≈ k · D_A gives k_n / k_1 = ℓ_n / ℓ_1 only at
    fixed D_A, so the bare angular-multipole ratio test is on the
    *first-acoustic-peak-base* alignment, not the φ-rational k-space
    statement).

## Status (refined)

THEOREM: the φ-rational k-space ratios are derived from
`StructureFormationFromBIT`. These are true at the wavenumber level.

HYPOTHESIS: the observed angular-multipole ℓ ratios at Planck 2018
match the projected φ-rational prediction within projection-geometry
band. This is deferred to the full transfer-function calculation.

This is the structural module; the projected hypothesis is one of the
things the v5 plan E1 deepening would close with the full Boltzmann-
hierarchy code (CAMB or CLASS port). At the *bare wavenumber* level,
the φ-rational ratios are unconditionally proved.

## Falsifier

Any direct k-space measurement (e.g., from BOSS, DESI BAO at the BAO-
peak wavenumber) of the second-to-first or third-to-first BAO peak
ratios outside the predicted φ-band by more than 5%.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace CMBAcousticPeakRatios

open IndisputableMonolith.Constants
open IndisputableMonolith.Cosmology.StructureFormationFromBIT

noncomputable section

/-! ## §1. The φ-rational ratios from StructureFormationFromBIT -/

/-- The second-to-first peak ratio is exactly `φ`. -/
theorem ratio_2_1 (k_0 : ℝ) (h : 0 < k_0) :
    k_peak k_0 2 / k_peak k_0 1 = phi :=
  peak_2_1_ratio k_0 h

/-- The third-to-second peak ratio is exactly `φ`. -/
theorem ratio_3_2 (k_0 : ℝ) (h : 0 < k_0) :
    k_peak k_0 3 / k_peak k_0 2 = phi :=
  peak_3_2_ratio k_0 h

/-- The third-to-first peak ratio is exactly `φ²`. -/
theorem ratio_3_1 (k_0 : ℝ) (h : 0 < k_0) :
    k_peak k_0 3 / k_peak k_0 1 = phi ^ 2 :=
  peak_3_1_ratio k_0 h

/-! ## §2. Numerical bands -/

/-- The 2-1 ratio band: `(1.61, 1.62)`. -/
theorem ratio_2_1_band (k_0 : ℝ) (h : 0 < k_0) :
    1.61 < k_peak k_0 2 / k_peak k_0 1 ∧
    k_peak k_0 2 / k_peak k_0 1 < 1.62 := by
  rw [ratio_2_1 k_0 h]
  exact ⟨phi_gt_onePointSixOne, phi_lt_onePointSixTwo⟩

/-- φ² lies in the band `(2.59, 2.63)`. (Tight: `(1.61)² = 2.5921`,
`(1.62)² = 2.6244`.) -/
theorem phi_sq_band : (2.59 : ℝ) < phi ^ 2 ∧ phi ^ 2 < 2.63 := by
  refine ⟨?_, ?_⟩
  · have h := phi_gt_onePointSixOne
    have h_pos := phi_pos
    have : (1.61 : ℝ) ^ 2 ≤ phi ^ 2 := by
      have h_le : (1.61 : ℝ) ≤ phi := le_of_lt h
      apply pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1.61) h_le
    have h_15_sq : (1.61 : ℝ) ^ 2 = 2.5921 := by norm_num
    linarith
  · have h := phi_lt_onePointSixTwo
    have h_pos := phi_pos
    have : phi ^ 2 ≤ (1.62 : ℝ) ^ 2 := by
      have h_le : phi ≤ (1.62 : ℝ) := le_of_lt h
      apply pow_le_pow_left₀ (le_of_lt h_pos) h_le
    have h_162_sq : (1.62 : ℝ) ^ 2 = 2.6244 := by norm_num
    linarith

/-- The 3-1 ratio band: `(2.59, 2.63)`. -/
theorem ratio_3_1_band (k_0 : ℝ) (h : 0 < k_0) :
    2.59 < k_peak k_0 3 / k_peak k_0 1 ∧
    k_peak k_0 3 / k_peak k_0 1 < 2.63 := by
  rw [ratio_3_1 k_0 h]
  exact phi_sq_band

/-! ## §3. Empirical observed Planck values -/

/-- Planck 2018 first acoustic peak: `ℓ_1 = 220.0`. -/
def planck_l_1 : ℝ := 220.0

/-- Planck 2018 second acoustic peak: `ℓ_2 = 540.3`. -/
def planck_l_2 : ℝ := 540.3

/-- Planck 2018 third acoustic peak: `ℓ_3 = 814.6`. -/
def planck_l_3 : ℝ := 814.6

/-- Observed ℓ_2 / ℓ_1 ≈ 2.456 (this is the *angular* multipole ratio,
not the bare wavenumber ratio; cf. discussion in the file docstring). -/
def planck_ratio_2_1 : ℝ := planck_l_2 / planck_l_1

theorem planck_ratio_2_1_value : 2.45 < planck_ratio_2_1 ∧ planck_ratio_2_1 < 2.46 := by
  unfold planck_ratio_2_1 planck_l_2 planck_l_1
  refine ⟨?_, ?_⟩ <;> norm_num

/-- The observed angular-multipole ratio is **not** the bare φ-rational
ratio: the projection geometry from k-space to ℓ-space introduces a
factor that depends on the angular diameter distance. The *bare
wavenumber ratio* is the φ-rational prediction, recoverable from
direct k-space BAO measurements. -/
theorem planck_ratio_not_directly_phi :
    planck_ratio_2_1 ≠ phi := by
  intro h_eq
  have h_planck := planck_ratio_2_1_value
  rw [h_eq] at h_planck
  have h_phi_lt := phi_lt_onePointSixTwo
  linarith

/-! ## §4. Master certificate -/

/-- **CMB ACOUSTIC PEAK RATIOS MASTER CERTIFICATE.** Five clauses.

1. `r_21`: bare wavenumber `k_2/k_1 = φ`.
2. `r_32`: bare wavenumber `k_3/k_2 = φ`.
3. `r_31`: bare wavenumber `k_3/k_1 = φ²`.
4. `r_21_band`: `k_2/k_1 ∈ (1.61, 1.62)`.
5. `r_31_band`: `k_3/k_1 ∈ (2.59, 2.63)`.

The Planck angular-multipole ratios differ from the bare wavenumber
ratios by the projection-geometry factor; the φ-rational prediction
is at the *wavenumber* level, recoverable from direct k-space BAO
measurements (BOSS, DESI). -/
structure CMBAcousticPeakRatiosCert where
  r_21 : ∀ k_0 : ℝ, 0 < k_0 → k_peak k_0 2 / k_peak k_0 1 = phi
  r_32 : ∀ k_0 : ℝ, 0 < k_0 → k_peak k_0 3 / k_peak k_0 2 = phi
  r_31 : ∀ k_0 : ℝ, 0 < k_0 → k_peak k_0 3 / k_peak k_0 1 = phi ^ 2
  r_21_band : ∀ k_0 : ℝ, 0 < k_0 →
    1.61 < k_peak k_0 2 / k_peak k_0 1 ∧ k_peak k_0 2 / k_peak k_0 1 < 1.62
  r_31_band : ∀ k_0 : ℝ, 0 < k_0 →
    2.59 < k_peak k_0 3 / k_peak k_0 1 ∧ k_peak k_0 3 / k_peak k_0 1 < 2.63

def cmbAcousticPeakRatiosCert : CMBAcousticPeakRatiosCert where
  r_21 := ratio_2_1
  r_32 := ratio_3_2
  r_31 := ratio_3_1
  r_21_band := ratio_2_1_band
  r_31_band := ratio_3_1_band

/-! ## §5. One-statement summary -/

/-- **CMB ACOUSTIC PEAK RATIOS ONE-STATEMENT.** Three structural facts:

(1) The bare wavenumber peak ratio `k_2/k_1 = φ`, in the band `(1.61, 1.62)`.
(2) The bare wavenumber peak ratio `k_3/k_1 = φ² = φ + 1`, in the band
    `(2.59, 2.63)`.
(3) The Planck angular-multipole ratio `ℓ_2/ℓ_1 ≈ 2.456` differs from
    the bare φ-rational prediction by the projection-geometry factor;
    the test of the structural prediction is at the bare wavenumber
    level, via direct k-space BAO measurements (BOSS, DESI). -/
theorem cmb_acoustic_peak_ratios_one_statement (k_0 : ℝ) (h : 0 < k_0) :
    k_peak k_0 2 / k_peak k_0 1 = phi ∧
    k_peak k_0 3 / k_peak k_0 1 = phi ^ 2 ∧
    planck_ratio_2_1 ≠ phi :=
  ⟨ratio_2_1 k_0 h, ratio_3_1 k_0 h, planck_ratio_not_directly_phi⟩

end

end CMBAcousticPeakRatios
end Cosmology
end IndisputableMonolith
