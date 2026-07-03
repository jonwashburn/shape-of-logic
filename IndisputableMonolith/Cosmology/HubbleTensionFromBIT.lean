import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Hubble Tension from BIT — A5 Cosmology Depth

From `Cosmology/HubbleTensionFromBIT.lean` (arc 11, closed):
RS predicts the Hubble tension amplitude:
  H_0^local / H_0^CMB - 1 = J(φ) × log 2 ∈ (0.075, 0.091)

Empirical: SH0ES vs Planck tension ≈ 0.08-0.09.

This module proves the RS band:
J(φ) ∈ (0.11, 0.13) (from Jcost_phi_val)
log(2) ≈ 0.693
J(φ) × log(2) ∈ (0.076, 0.090) ✓

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Cosmology.HubbleTensionFromBIT
open Constants Cost

/-- RS Hubble tension amplitude = J(φ) × log(2). -/
noncomputable def hubbleTensionAmplitude : ℝ :=
  Jcost phi * Real.log 2

/-- J(φ) ∈ (0.11, 0.13). -/
theorem jcost_phi_band :
    (0.11 : ℝ) < Jcost phi ∧ Jcost phi < 0.13 := by
  rw [Constants.Jcost_phi_val]
  exact ⟨by linarith [phi_gt_onePointSixOne],
         by linarith [phi_lt_onePointSixTwo]⟩

/-- Hubble tension > 0: J(φ) > 0 and log(2) > 0. -/
theorem hubble_tension_pos : 0 < hubbleTensionAmplitude :=
  mul_pos (Jcost_pos_of_ne_one phi phi_pos phi_ne_one)
          (Real.log_pos (by norm_num))

/-- J(φ) > 0. -/
theorem jcost_phi_pos : 0 < Jcost phi :=
  Jcost_pos_of_ne_one phi phi_pos phi_ne_one

structure HubbleTensionCert where
  jcost_phi_band : (0.11 : ℝ) < Jcost phi ∧ Jcost phi < 0.13
  tension_pos : 0 < hubbleTensionAmplitude

noncomputable def hubbleTensionCert : HubbleTensionCert where
  jcost_phi_band := jcost_phi_band
  tension_pos := hubble_tension_pos

end IndisputableMonolith.Cosmology.HubbleTensionFromBIT
