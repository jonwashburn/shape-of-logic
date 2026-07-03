import Mathlib
import IndisputableMonolith.Measurement.RSNative.Core
import IndisputableMonolith.Measurement.RSNative.Calibration.SI
import IndisputableMonolith.Constants.RSNativeUnits

/-!
# Single-Anchor SI Calibration (RS-native Measurement Framework)

This module provides a **concrete single-anchor calibration protocol** for reporting
RS-native measurements in SI without introducing any *fit parameters*.

## Idea

- RS-native theory runs in tick/voxel/coh/act with \(c=1\) and no SI numerals.
- If one wants SI reporting, one must provide a calibration seam.
- We choose a **single scalar anchor**: `seconds_per_tick` (τ₀ in seconds).

Then we *derive* the full `ExternalCalibration`:

- meters_per_voxel is fixed by the SI definition of \(c\): 299792458 m/s
- joules_per_coh is fixed by the SI definition of Planck's constant \(h\) (exact),
  hence \(\hbar = h/(2\pi)\), together with the RS identity `1 act = 1 coh * 1 tick`

So, **only one empirical scalar** is supplied; everything else is derived or definitional.
-/

namespace IndisputableMonolith
namespace Measurement
namespace RSNative
namespace Calibration
namespace SingleAnchor

open IndisputableMonolith.Constants.RSNativeUnits
open IndisputableMonolith.Measurement.RSNative

noncomputable section

/-! ## SI definitional constants (not fit parameters) -/

/-- SI-definitional speed of light in meters per second (exact). -/
def c_SI : ℝ := 299792458

lemma c_SI_pos : 0 < c_SI := by
  norm_num [c_SI]

/-- SI-definitional Planck constant \(h\) (exact, 2019 SI): 6.62607015×10⁻³⁴ J·s.

We write this exactly as a rational: 662607015 / 10^42. -/
noncomputable def h_SI : ℝ :=
  (662607015 : ℝ) / ((10 : ℝ) ^ (42 : ℕ))

lemma h_SI_pos : 0 < h_SI := by
  unfold h_SI
  have hnum : (0 : ℝ) < (662607015 : ℝ) := by norm_num
  have hden : (0 : ℝ) < (10 : ℝ) ^ (42 : ℕ) := by
    exact pow_pos (by norm_num : (0 : ℝ) < 10) 42
  exact div_pos hnum hden

/-- Reduced Planck constant \(\hbar = h/(2\pi)\) (exact given SI definition of \(h\)). -/
noncomputable def hbar_SI : ℝ :=
  h_SI / (2 * Real.pi)

lemma hbar_SI_pos : 0 < hbar_SI := by
  unfold hbar_SI
  have hden : (0 : ℝ) < 2 * Real.pi := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    exact mul_pos h2 Real.pi_pos
  exact div_pos h_SI_pos hden

/-! ## Calibration protocol (measurement framework) -/

/-- Single-anchor SI calibration protocol: provide τ₀ in seconds.

This is an *explicit* seam. It does not tune any dimensionless RS predictions;
it only fixes the SI reporting scale. -/
def tau0_seconds_protocol : Protocol :=
  { name := "calibration.single_anchor.tau0_seconds"
    summary :=
      "Single-anchor SI calibration. Supply τ0 (seconds per tick) as the only empirical scalar. " ++
      "Derive meters_per_voxel via SI-defined c=299792458 and derive joules_per_coh via SI-defined h (hbar=h/(2π)) " ++
      "together with RS identity 1 act = 1 coh * 1 tick. No mass-data fitting; this is a reporting seam only."
    status := .hypothesis
    assumptions :=
      [ "A1: τ0 (one RS tick) corresponds to a stable physical duration that can be measured in SI seconds using a declared lab protocol."
      , "A2: SI definitional constants (c and h) are treated as exact conventions; they introduce no fit freedom."
      ]
    falsifiers :=
      [ "F1: Two independent anchors for τ0 (e.g. time-first vs length-first) disagree beyond stated uncertainties."
      , "F2: Under the derived calibration, the SI speed consistency check fails beyond uncertainty."
      ]
  }

theorem tau0_seconds_protocol_hygienic : Protocol.hygienic tau0_seconds_protocol := by
  simp [Protocol.hygienic, tau0_seconds_protocol]

/-! ## Derive the full `ExternalCalibration` from one scalar -/

/-- Build a full `ExternalCalibration` from one scalar: τ₀ in seconds. -/
noncomputable def externalCalibration_of_tau0_seconds (tau0_s : ℝ) (htau : 0 < tau0_s) :
    ExternalCalibration :=
  { seconds_per_tick := tau0_s
    meters_per_voxel := (c_SI : ℝ) * tau0_s
    joules_per_coh := hbar_SI / tau0_s
    seconds_pos := htau
    meters_pos := mul_pos c_SI_pos htau
    joules_pos := div_pos hbar_SI_pos htau
    speed_consistent := by
      have htau_ne : tau0_s ≠ 0 := ne_of_gt htau
      -- (c_SI * tau0_s) / tau0_s = 299792458
      simp [c_SI, htau_ne]
  }

/-! ## Certificate: one-scalar calibration seam (explicit) -/

/-- A calibration certificate bundling:
1) the single-anchor protocol
2) one measured scalar τ₀ in seconds
3) the derived full `ExternalCalibration` used for SI reporting

Everything beyond τ₀ is derived (or SI-definitional). -/
structure CalibrationCert where
  /-- The single empirical scalar: τ₀ in seconds (seconds per tick). -/
  tau0_seconds : Measurement ℝ
  /-- Protocol is the canonical single-anchor protocol. -/
  protocol_ok : tau0_seconds.protocol = tau0_seconds_protocol
  /-- Positivity: τ₀ must be positive. -/
  tau0_pos : 0 < tau0_seconds.value

/-- The derived `ExternalCalibration` associated to a certificate. -/
noncomputable def calibration (cert : CalibrationCert) : ExternalCalibration :=
  externalCalibration_of_tau0_seconds cert.tau0_seconds.value cert.tau0_pos

theorem calibration_protocol_hygienic (cert : CalibrationCert) :
    Protocol.hygienic cert.tau0_seconds.protocol := by
  simpa [cert.protocol_ok] using tau0_seconds_protocol_hygienic

/-! ## Consistency checks (derived, not additional parameters) -/

/-- Under the derived calibration, 1 voxel/tick reports exactly c_SI in m/s. -/
theorem c_reports_exact (cert : CalibrationCert) :
    IndisputableMonolith.Constants.RSNativeUnits.to_m_per_s (calibration cert)
        IndisputableMonolith.Constants.RSNativeUnits.c = c_SI := by
  -- This follows from the `speed_consistent` field plus `c_in_si`.
  -- Note: RSNativeUnits.c = 1 (voxel/tick).
  have := IndisputableMonolith.Constants.RSNativeUnits.c_in_si (calibration cert)
  simpa [c_SI] using this

/-- Under the derived calibration, 1 act reports \(\hbar\) in SI \(J·s\). -/
theorem one_act_reports_hbar (cert : CalibrationCert) :
    IndisputableMonolith.Measurement.RSNative.Calibration.SI.to_joule_seconds
        (calibration cert) (⟨(1 : ℝ)⟩ : Act) = hbar_SI := by
  -- Expand definitions and cancel τ0_s.
  have htau_ne : cert.tau0_seconds.value ≠ 0 := ne_of_gt cert.tau0_pos
  -- to_joule_seconds uses: (A:ℝ) * (joules_per_coh * seconds_per_tick)
  simp [IndisputableMonolith.Measurement.RSNative.Calibration.SI.to_joule_seconds,
    calibration, externalCalibration_of_tau0_seconds, htau_ne, hbar_SI]

/-! ## Convenience constructor (for use in examples/tests) -/

/-- Build a certificate from a chosen τ₀ (seconds per tick).

This is a helper for downstream modules; real usage should supply a `Protocol`d
measurement record coming from a declared empirical procedure. -/
def mkCert (tau0_s : ℝ) (htau : 0 < tau0_s) : CalibrationCert :=
  { tau0_seconds :=
      { value := tau0_s
        protocol := tau0_seconds_protocol
        notes := ["Units: SI seconds per RS tick (single-anchor calibration seam)."] }
    protocol_ok := rfl
    tau0_pos := htau
  }

end

end SingleAnchor
end Calibration
end RSNative
end Measurement
end IndisputableMonolith
