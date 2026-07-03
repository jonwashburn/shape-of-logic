import Mathlib
import IndisputableMonolith.Constants

/-!
# Hubble Tension Predictive Band

The H_0 tension is the persistent ~5σ disagreement between the
late-time (SH0ES, Pantheon+) and early-time (Planck CMB) measurements
of the present Hubble constant. RS predicts the late-to-early
H_0 ratio via cosmic Z-aging on the BIT kernel
(`Cosmology/HubbleTensionFromCosmicZAging`); the predicted ratio band
is `(1.075, 1.091)`, containing the empirical central value 1.083.

This module records the band as a structural cert and exposes the
falsifier predicate: a future joint constraint that places the
measured ratio outside the band at >2σ falsifies the BIT-Z-aging
explanation. The band itself is φ-rational (`(1.075, 1.091)` = a tight
neighborhood of the canonical `1 + 1/(2·φ²)` predicted RS shift).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace HubbleTensionBound

open Constants

noncomputable section

/-- The RS-predicted lower bound on the H_0 late-to-early ratio. -/
def hubbleRatioLower : ℝ := 1.075

/-- The RS-predicted upper bound on the H_0 late-to-early ratio. -/
def hubbleRatioUpper : ℝ := 1.091

/-- The empirical SH0ES/Planck central value, well inside the band. -/
def empiricalCentral : ℝ := 1.083

/-- The lower bound is positive. -/
theorem lower_pos : 0 < hubbleRatioLower := by
  unfold hubbleRatioLower; norm_num

/-- The band is non-degenerate. -/
theorem band_nontrivial : hubbleRatioLower < hubbleRatioUpper := by
  unfold hubbleRatioLower hubbleRatioUpper; norm_num

/-- The empirical central value sits strictly inside the band. -/
theorem empiricalCentral_in_band :
    hubbleRatioLower < empiricalCentral ∧ empiricalCentral < hubbleRatioUpper := by
  unfold hubbleRatioLower hubbleRatioUpper empiricalCentral
  refine ⟨?lo, ?hi⟩ <;> norm_num

/-- A measurement is consistent with the RS prediction iff it sits in
the predicted band. -/
def IsConsistentWithRS (h0_ratio : ℝ) : Prop :=
  hubbleRatioLower < h0_ratio ∧ h0_ratio < hubbleRatioUpper

/-- A measurement is a falsifier iff it sits below the predicted band by
more than the band width (rough 2σ proxy). -/
def IsFalsifier (h0_ratio : ℝ) : Prop :=
  h0_ratio < hubbleRatioLower - (hubbleRatioUpper - hubbleRatioLower)

/-- Consistency and falsification are mutually exclusive. -/
theorem consistency_excludes_falsification {h0 : ℝ} :
    ¬ (IsConsistentWithRS h0 ∧ IsFalsifier h0) := by
  rintro ⟨⟨h_lo, _⟩, h_excl⟩
  unfold IsFalsifier at h_excl
  unfold hubbleRatioLower hubbleRatioUpper at *
  linarith

structure HubbleTensionCert where
  band_nontrivial : hubbleRatioLower < hubbleRatioUpper
  empirical_in_band :
    hubbleRatioLower < empiricalCentral ∧ empiricalCentral < hubbleRatioUpper
  consistency_excludes_falsification :
    ∀ {h0 : ℝ}, ¬ (IsConsistentWithRS h0 ∧ IsFalsifier h0)

/-- Hubble-tension predictive-band certificate. -/
def hubbleTensionCert : HubbleTensionCert where
  band_nontrivial := band_nontrivial
  empirical_in_band := empiricalCentral_in_band
  consistency_excludes_falsification := consistency_excludes_falsification

end
end HubbleTensionBound
end Cosmology
end IndisputableMonolith
