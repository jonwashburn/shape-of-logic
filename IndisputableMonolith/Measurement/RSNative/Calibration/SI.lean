import Mathlib
import IndisputableMonolith.Measurement.RSNative.Core
import IndisputableMonolith.Constants.RSNativeUnits

/-!
# RS-Native → SI Calibration Adapter

This module is the explicit seam where RS-native quantities can be *reported* in SI.

Key rule:
- RS-native theory and RS-native measurement catalogs must not depend on CODATA numerals.
- SI conversion happens only through an explicit `ExternalCalibration` record supplied externally.
-/

namespace IndisputableMonolith
namespace Measurement
namespace RSNative
namespace Calibration
namespace SI

open IndisputableMonolith.Constants.RSNativeUnits

/-! ## Scalar conversions -/

@[simp] noncomputable def to_seconds (cal : ExternalCalibration) (t : Tick) : ℝ :=
  (t : ℝ) * cal.seconds_per_tick

@[simp] noncomputable def to_meters (cal : ExternalCalibration) (L : Voxel) : ℝ :=
  (L : ℝ) * cal.meters_per_voxel

@[simp] noncomputable def to_joules (cal : ExternalCalibration) (E : Coh) : ℝ :=
  (E : ℝ) * cal.joules_per_coh

/-- Convert action quanta (act) to SI \(J·s\).

In RS-native units, `1 act` corresponds to `1 coh * 1 tick`.
So the SI conversion is `joules_per_coh * seconds_per_tick`.
-/
@[simp] noncomputable def to_joule_seconds (cal : ExternalCalibration) (A : Act) : ℝ :=
  (A : ℝ) * (cal.joules_per_coh * cal.seconds_per_tick)

/-! ## Measurement-level conversion helpers -/

private def scaleUncertainty (c : ℝ) (hc : 0 ≤ c) (u : Uncertainty) : Uncertainty :=
  match u with
  | .sigma σ hσ =>
      .sigma (σ * c) (mul_nonneg hσ hc)
  | .interval lo hi hlohi =>
      .interval (lo * c) (hi * c) (mul_le_mul_of_nonneg_right hlohi hc)
  | .discrete support =>
      .discrete (support.map (fun vw => (vw.1 * c, vw.2)))

noncomputable def measure_to_seconds (cal : ExternalCalibration) (m : Measurement Tick) : Measurement ℝ :=
  Measurement.map (to_seconds cal)
    (Measurement.mapUncertainty
      (fun u => scaleUncertainty cal.seconds_per_tick (le_of_lt cal.seconds_pos) u) m)

noncomputable def measure_to_meters (cal : ExternalCalibration) (m : Measurement Voxel) : Measurement ℝ :=
  Measurement.map (to_meters cal)
    (Measurement.mapUncertainty
      (fun u => scaleUncertainty cal.meters_per_voxel (le_of_lt cal.meters_pos) u) m)

noncomputable def measure_to_joules (cal : ExternalCalibration) (m : Measurement Coh) : Measurement ℝ :=
  Measurement.map (to_joules cal)
    (Measurement.mapUncertainty
      (fun u => scaleUncertainty cal.joules_per_coh (le_of_lt cal.joules_pos) u) m)

noncomputable def measure_to_joule_seconds (cal : ExternalCalibration) (m : Measurement Act) : Measurement ℝ :=
  Measurement.map (to_joule_seconds cal)
    (Measurement.mapUncertainty
      (fun u =>
        scaleUncertainty (cal.joules_per_coh * cal.seconds_per_tick)
          (mul_nonneg (le_of_lt cal.joules_pos) (le_of_lt cal.seconds_pos)) u) m)

end SI
end Calibration
end RSNative
end Measurement
end IndisputableMonolith
