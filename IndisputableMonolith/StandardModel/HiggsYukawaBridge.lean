import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.Anchor
import IndisputableMonolith.Masses.MassLaw

/-!
# Higgs–Yukawa Bridge

This module exposes the standard-model Yukawa coupling for a fermion as a
ratio of an RS-derived mass to the electroweak scale `v`, in the canonical
form

    y_f = √2 · m_f / v.

The mass `m_f` is supplied by `Masses.MassLaw.predict_mass`.  The result is
that *no Yukawa is fit independently*: every Yukawa is a function of the
fermion's rung on the φ-ladder and of the electroweak scale `v`, with the
SM extraction convention `y_f = √2 m_f / v` translated into the same
ladder structure.

The φ-rung scaling property is preserved: increasing the fermion's rung by
one multiplies its Yukawa coupling by `φ`.  Generation jumps are therefore
`φ^(Δr)` where `Δr` is the integer rung difference, *not* `φ^1` between
adjacent SM generations.

## Status

* `THEOREM`: Yukawa positivity, φ-rung scaling, ratio of Yukawas equals
  ratio of masses.
* `CONDITIONAL`: identification of the SM Yukawa value `y_f^{SM}` with the
  RS Yukawa requires the same `v` as in the SM extraction (this is the
  same normalisation hypothesis as `HiggsEFTBridge.NormalizationHypothesis`,
  but expressed for fermions).
* `OPEN`: deriving the rung map for each SM species from cube combinatorics
  is a separate project, tracked under the `OPEN_RUNG_MAP` tag.
-/

namespace IndisputableMonolith
namespace StandardModel
namespace HiggsYukawaBridge

open Real
open Constants
open Masses
open Masses.MassLaw

noncomputable section

/-! ## §1. Yukawa Coupling -/

/-- Standard-Model Yukawa extraction convention:

    `y_f = √2 · m_f / v`

    where `m_f = predict_mass sector rung Z` is the φ-ladder mass. -/
def yukawa_SM (sector : Anchor.Sector) (rung Z : ℤ) (v : ℝ) : ℝ :=
  Real.sqrt 2 * predict_mass sector rung Z / v

/-- Yukawa couplings are positive for `v > 0`. -/
theorem yukawa_SM_pos
    (sector : Anchor.Sector) (rung Z : ℤ) (v : ℝ) (hv : 0 < v) :
    0 < yukawa_SM sector rung Z v := by
  unfold yukawa_SM
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hm : 0 < predict_mass sector rung Z := predict_mass_pos sector rung Z
  have hnum : 0 < Real.sqrt 2 * predict_mass sector rung Z := mul_pos hsqrt2 hm
  exact div_pos hnum hv

/-- φ-rung scaling: increasing rung by 1 multiplies the Yukawa by `φ`. -/
theorem yukawa_SM_phi_scaling
    (sector : Anchor.Sector) (rung Z : ℤ) (v : ℝ) (hv : 0 < v) :
    yukawa_SM sector (rung + 1) Z v = phi * yukawa_SM sector rung Z v := by
  unfold yukawa_SM
  have hscale : predict_mass sector (rung + 1) Z = phi * predict_mass sector rung Z :=
    mass_rung_scaling sector rung Z
  have hv_ne : v ≠ 0 := ne_of_gt hv
  rw [hscale]
  field_simp

/-- The Yukawa ratio between adjacent rungs is exactly `φ`. -/
theorem yukawa_SM_ratio_adjacent
    (sector : Anchor.Sector) (rung Z : ℤ) (v : ℝ) (hv : 0 < v) :
    yukawa_SM sector (rung + 1) Z v / yukawa_SM sector rung Z v = phi := by
  have h := yukawa_SM_phi_scaling sector rung Z v hv
  have hpos : 0 < yukawa_SM sector rung Z v := yukawa_SM_pos sector rung Z v hv
  have hne : yukawa_SM sector rung Z v ≠ 0 := ne_of_gt hpos
  rw [h]
  field_simp

/-- The ratio of two Yukawas (same sector, same charge) equals the ratio
    of their masses; the `v`-dependence cancels. -/
theorem yukawa_SM_ratio_independent_of_v
    (sector : Anchor.Sector) (rung1 rung2 Z : ℤ) (v : ℝ) (hv : 0 < v) :
    yukawa_SM sector rung1 Z v / yukawa_SM sector rung2 Z v
      = predict_mass sector rung1 Z / predict_mass sector rung2 Z := by
  unfold yukawa_SM
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  have hv_ne : v ≠ 0 := ne_of_gt hv
  have hm2_pos : 0 < predict_mass sector rung2 Z := predict_mass_pos sector rung2 Z
  have hm2_ne : predict_mass sector rung2 Z ≠ 0 := ne_of_gt hm2_pos
  field_simp

/-! ## §2. Cross-Sector Generation Gap -/

/-- The Yukawa scaling under an integer rung difference `Δr ≥ 0`:

    y_f(rung + n) = φ^n · y_f(rung). -/
theorem yukawa_SM_phi_pow_scaling
    (sector : Anchor.Sector) (rung Z : ℤ) (n : ℕ) (v : ℝ) (hv : 0 < v) :
    yukawa_SM sector (rung + (n : ℤ)) Z v
      = phi ^ n * yukawa_SM sector rung Z v := by
  induction n with
  | zero =>
      simp [yukawa_SM]
  | succ k ih =>
      have h_one_step :
          yukawa_SM sector (rung + ((k : ℤ) + 1)) Z v
            = phi * yukawa_SM sector (rung + (k : ℤ)) Z v := by
        have := yukawa_SM_phi_scaling sector (rung + (k : ℤ)) Z v hv
        simpa [add_assoc] using this
      have hcast : (rung + (((k + 1 : ℕ) : ℤ))) = (rung + ((k : ℤ) + 1)) := by
        push_cast
        ring
      rw [hcast, h_one_step, ih]
      ring

/-! ## §3. SM-Normalisation Hypothesis -/

/-- The SM-normalisation hypothesis for fermion species: `v` is the same
    electroweak scale as the one used in the SM Yukawa extraction.

    This is the fermion-sector counterpart of
    `HiggsEFTBridge.NormalizationHypothesis`.  It states that the Yukawa
    coupling extracted from `m_f` and `v` via `y_f = √2 m_f / v` is the
    same as the Yukawa appearing in the SM Lagrangian. -/
def YukawaNormalizationHypothesis
    (sector : Anchor.Sector) (rung Z : ℤ) (v y_SM : ℝ) : Prop :=
  yukawa_SM sector rung Z v = y_SM

/-- Under the normalisation hypothesis, the SM-extracted Yukawa is positive. -/
theorem yukawa_SM_pos_of_hypothesis
    (sector : Anchor.Sector) (rung Z : ℤ) (v y_SM : ℝ) (hv : 0 < v)
    (hY : YukawaNormalizationHypothesis sector rung Z v y_SM) :
    0 < y_SM := by
  unfold YukawaNormalizationHypothesis at hY
  have h := yukawa_SM_pos sector rung Z v hv
  rw [← hY]; exact h

/-! ## §4. Master Bridge Certificate -/

/-- Master certificate for the Higgs–Yukawa bridge. -/
structure HiggsYukawaBridgeCert where
  /-- THEOREM: every Yukawa is positive for `v > 0`. -/
  yukawa_pos      : ∀ s r Z v, 0 < v → 0 < yukawa_SM s r Z v
  /-- THEOREM: adjacent-rung scaling by `φ`. -/
  yukawa_phi_step : ∀ s r Z v, 0 < v →
    yukawa_SM s (r + 1) Z v = phi * yukawa_SM s r Z v
  /-- THEOREM: integer-rung scaling by `φ^n`. -/
  yukawa_phi_pow  : ∀ s r Z (n : ℕ) v, 0 < v →
    yukawa_SM s (r + (n : ℤ)) Z v = phi ^ n * yukawa_SM s r Z v
  /-- THEOREM: ratio of Yukawas equals ratio of masses. -/
  yukawa_ratio_v_independent :
    ∀ s r1 r2 Z v, 0 < v →
      yukawa_SM s r1 Z v / yukawa_SM s r2 Z v
        = predict_mass s r1 Z / predict_mass s r2 Z

def higgsYukawaBridgeCert : HiggsYukawaBridgeCert where
  yukawa_pos      := yukawa_SM_pos
  yukawa_phi_step := yukawa_SM_phi_scaling
  yukawa_phi_pow  := yukawa_SM_phi_pow_scaling
  yukawa_ratio_v_independent := yukawa_SM_ratio_independent_of_v

theorem higgsYukawaBridgeCert_inhabited : Nonempty HiggsYukawaBridgeCert :=
  ⟨higgsYukawaBridgeCert⟩

end

end HiggsYukawaBridge
end StandardModel
end IndisputableMonolith
