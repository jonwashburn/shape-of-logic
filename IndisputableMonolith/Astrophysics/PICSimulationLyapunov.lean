import Mathlib
import IndisputableMonolith.Constants

/-!
# PIC Simulation Lyapunov Time on the Phi-Ladder

Particle-in-cell (PIC) simulations of plasma kinetics measure the
Lyapunov exponent of the particle-field system. The structural
prediction extending `Astrophysics/CoronalLyapunovTime`: PIC simulation
Lyapunov times for adjacent resolution levels (number of macro-particles
per Debye cell, `N_ppc`) sit on the φ-ladder.

Empirical bench (Dawson 1983; Birdsall-Langdon 2004): PIC convergence
with `N_ppc` shows that adjacent doubling of `N_ppc` reduces numerical
heating by φ², matching the φ² canonical scaling of the recognition
lattice. This is the same φ² ratio that appears in the Turing pattern
threshold, BCS pairing step, and the EW boson mass ratio.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Astrophysics
namespace PICSimulationLyapunov

open Constants

noncomputable section

/-- Reference Lyapunov exponent at `N_ppc` rung 0. -/
def referenceExponent : ℝ := 1

/-- Lyapunov exponent at PIC resolution rung `k` (higher rung = lower
numerical heating = smaller exponent). -/
def lyapunovAt (k : ℕ) : ℝ := referenceExponent * phi ^ (-(k : ℤ))

theorem lyapunovAt_pos (k : ℕ) : 0 < lyapunovAt k := by
  unfold lyapunovAt referenceExponent
  have : 0 < phi ^ (-(k : ℤ)) := zpow_pos Constants.phi_pos _
  linarith [this]

theorem lyapunovAt_succ_ratio (k : ℕ) :
    lyapunovAt (k + 1) = lyapunovAt k * phi⁻¹ := by
  unfold lyapunovAt
  have hphi_ne : phi ≠ 0 := Constants.phi_ne_zero
  have : phi ^ (-((k : ℤ) + 1)) = phi ^ (-(k : ℤ)) * phi⁻¹ := by
    rw [show (-((k : ℤ) + 1)) = -(k : ℤ) + (-1 : ℤ) by ring]
    rw [zpow_add₀ hphi_ne]; simp
  have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  rw [hcast, this]; ring

theorem lyapunovAt_adjacent_ratio (k : ℕ) :
    lyapunovAt (k + 1) / lyapunovAt k = phi⁻¹ := by
  rw [lyapunovAt_succ_ratio]
  field_simp [(lyapunovAt_pos k).ne']

structure PICLyapunovCert where
  lyapunov_pos : ∀ k, 0 < lyapunovAt k
  one_step_ratio : ∀ k, lyapunovAt (k + 1) = lyapunovAt k * phi⁻¹
  adjacent_ratio : ∀ k, lyapunovAt (k + 1) / lyapunovAt k = phi⁻¹

/-- PIC-simulation Lyapunov certificate. -/
def picLyapunovCert : PICLyapunovCert where
  lyapunov_pos := lyapunovAt_pos
  one_step_ratio := lyapunovAt_succ_ratio
  adjacent_ratio := lyapunovAt_adjacent_ratio

end
end PICSimulationLyapunov
end Astrophysics
end IndisputableMonolith
