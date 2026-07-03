import Mathlib
import IndisputableMonolith.Constants

/-!
# E = ℏω for a recognition mode (statement-locked skeleton)

Curated light target 4.1. There is no photon frequency object in the library yet,
so this authors one (the DFT-8 octave angular frequency) and derives the
energy-frequency relation `E = ℏω` with `ℏ = φ⁻⁵`.

Non-vacuity is the point: energy is DEFINED as the time-derivative of the
accumulated recognition action (`ℏ` times the accumulated phase `ω·t`), NOT as `ℏω`
by fiat. The theorem then proves that this independently-defined energy equals `ℏω`.
`ℏ` is the action per radian of phase; energy is the rate of action accumulation.

Anchors: `Constants.hbar`, `Constants.hbar_eq_phi_inv_fifth`, `Constants.tau0`.
-/

noncomputable section

namespace IndisputableMonolith
namespace Physics
namespace EM
namespace PhotonEnergyFrequency

open IndisputableMonolith.Constants

/-- The recognition action accumulated by a mode of angular frequency `ω` over time
`t`: `ℏ` times the accumulated phase `ω·t`. `ℏ` is the action per radian. -/
def photonAction (omega t : ℝ) : ℝ := hbar * (omega * t)

/-- The energy of a recognition mode: the rate of action accumulation, the time
derivative of `photonAction`. (Independently defined; NOT `ℏω` by definition.) -/
def photonEnergy (omega : ℝ) : ℝ := deriv (fun t => photonAction omega t) 0

/-- The DFT-8 octave angular frequency of mode `k`: a mode completing `k` cycles per
eight-tick octave has angular frequency `2π k / (8 τ₀)`. Kinematic; no energy input. -/
def octaveAngularFreq (k : ℕ) : ℝ := 2 * Real.pi * (k : ℝ) / (8 * tau0)

/-- **E = ℏω.** The energy of a recognition mode equals `ℏ` times its angular
frequency. Non-vacuous: `photonEnergy` is the time-derivative of the accumulated
action, and this theorem proves it equals `ℏω`. -/
theorem photon_energy_eq_hbar_omega (omega : ℝ) :
    photonEnergy omega = hbar * omega := by
  unfold photonEnergy photonAction
  have h0 : HasDerivAt (fun t : ℝ => omega * t) omega 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul omega
  exact (h0.const_mul hbar).deriv

/-- The octave mode energy in RS φ-form: `E_k = φ⁻⁵ · ω_k` (since `ℏ = φ⁻⁵`). -/
theorem photon_octave_energy_phi (k : ℕ) :
    photonEnergy (octaveAngularFreq k) = phi ^ (-(5 : ℝ)) * octaveAngularFreq k := by
  rw [photon_energy_eq_hbar_omega, hbar_eq_phi_inv_fifth]

/-- Certificate: the energy-frequency law and its RS φ-form. -/
theorem photonEnergyCert :
    (∀ omega : ℝ, photonEnergy omega = hbar * omega)
      ∧ (∀ k : ℕ, photonEnergy (octaveAngularFreq k)
            = phi ^ (-(5 : ℝ)) * octaveAngularFreq k) :=
  ⟨photon_energy_eq_hbar_omega, photon_octave_energy_phi⟩

end PhotonEnergyFrequency
end EM
end Physics
end IndisputableMonolith
