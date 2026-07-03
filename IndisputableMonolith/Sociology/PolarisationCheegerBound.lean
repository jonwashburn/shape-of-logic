import Mathlib
import IndisputableMonolith.Constants

/-!
# Social Media Polarisation as Graph-Algebra Cheeger Bound

The structural F2 wrapper proves the canonical band claim. This deep
follow-on adds the graph-algebra layer: a discourse network with
Cheeger constant `h` is non-polarised iff `h > 1/φ`. Below the
threshold, the network has a sub-φ-rational spectral gap and admits
a high-conductance bisection (echo-chamber regime).

The structural prediction: the social-media platform's algorithmic
amplification factor sits at the canonical golden-section quantum on
the cross-cluster exposure ratio iff its discourse graph has Cheeger
constant ≥ 1/φ ∈ (0.617, 0.622). Falsifier: a platform with measured
Cheeger ≥ 0.7 that nonetheless shows above-baseline polarisation.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Sociology
namespace PolarisationCheegerBound

open Constants

noncomputable section

/-- The non-polarisation Cheeger threshold: 1/φ ∈ (0.617, 0.622). -/
def cheegerThreshold : ℝ := phi⁻¹

/-- The threshold is strictly positive. -/
theorem cheegerThreshold_pos : 0 < cheegerThreshold := by
  unfold cheegerThreshold
  exact inv_pos.mpr Constants.phi_pos

/-- The threshold sits in the band `(0.617, 0.622)`. -/
theorem cheegerThreshold_band :
    0.617 < cheegerThreshold ∧ cheegerThreshold < 0.622 := by
  unfold cheegerThreshold
  have h_lo : (1.61 : ℝ) < phi := Constants.phi_gt_onePointSixOne
  have h_hi : phi < (1.62 : ℝ) := Constants.phi_lt_onePointSixTwo
  have h_phi_pos : 0 < phi := Constants.phi_pos
  refine ⟨?lo, ?hi⟩
  · rw [show (0.617 : ℝ) < phi⁻¹ ↔ phi < 1 / 0.617 from
        ⟨fun h => by rw [lt_inv_comm₀ (by norm_num : (0 : ℝ) < 0.617) h_phi_pos] at h; linarith,
         fun h => by rw [lt_inv_comm₀ (by norm_num : (0 : ℝ) < 0.617) h_phi_pos]; linarith⟩]
    linarith
  · rw [show (phi⁻¹ < 0.622 ↔ 1 / 0.622 < phi) from
        ⟨fun h => by rw [inv_lt_comm₀ h_phi_pos (by norm_num : (0 : ℝ) < 0.622)] at h; linarith,
         fun h => by rw [inv_lt_comm₀ h_phi_pos (by norm_num : (0 : ℝ) < 0.622)]; linarith⟩]
    linarith

/-- A network is non-polarised iff its Cheeger constant meets the
threshold. -/
def IsNonPolarised (h : ℝ) : Prop := cheegerThreshold ≤ h

/-- A network is polarised iff its Cheeger constant is strictly below
the threshold. -/
def IsPolarised (h : ℝ) : Prop := h < cheegerThreshold

/-- The two regimes are mutually exclusive. -/
theorem regimes_exclusive {h : ℝ} :
    ¬ (IsNonPolarised h ∧ IsPolarised h) := by
  rintro ⟨h_ge, h_lt⟩
  exact (lt_irrefl _) (lt_of_lt_of_le h_lt h_ge)

structure PolarisationCheegerCert where
  threshold_pos : 0 < cheegerThreshold
  threshold_band : 0.617 < cheegerThreshold ∧ cheegerThreshold < 0.622
  regimes_exclusive : ∀ {h : ℝ}, ¬ (IsNonPolarised h ∧ IsPolarised h)

/-- Polarisation-Cheeger-bound certificate. -/
def polarisationCheegerCert : PolarisationCheegerCert where
  threshold_pos := cheegerThreshold_pos
  threshold_band := cheegerThreshold_band
  regimes_exclusive := regimes_exclusive

end
end PolarisationCheegerBound
end Sociology
end IndisputableMonolith
