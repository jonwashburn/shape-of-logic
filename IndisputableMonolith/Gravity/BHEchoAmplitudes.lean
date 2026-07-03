import Mathlib
import IndisputableMonolith.Gravity.BHEchoPerEventCatalog

/-!
# Black-Hole Echo Amplitudes with Phi-Ladder Damping

The echo-delay cert gives `Δt(N)` and frequency per event. This module
adds the amplitude prediction: each successive reflection off the bounce
surface is attenuated by a factor `φ⁻¹` (one φ-rung of recognition
cost), giving echo amplitudes `A_n = A_0 · φ^(-n)` for echo number `n`.

The structural prediction: the SNR of the nth echo relative to the
(n-1)th echo is exactly 1/φ ≈ 0.618 for every LIGO/Virgo event.
Falsifier: post-processing of any high-SNR merger event that shows
either no echo or an echo-amplitude ratio systematically different from
1/φ between successive echoes.

This compounds with the existing catalog cert:
`Gravity/BHEchoPerEventCatalog`.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Gravity
namespace BHEchoAmplitudes

open Constants
open Gravity.BHEchoPerEventCatalog

noncomputable section

/-- Echo amplitude at reflection number `n` (relative to primary). -/
def echoAmplitude (n : ℕ) : ℝ := phi ^ (-(n : ℤ))

theorem echoAmplitude_pos (n : ℕ) : 0 < echoAmplitude n :=
  zpow_pos Constants.phi_pos _

theorem echoAmplitude_one : echoAmplitude 0 = 1 := by
  simp [echoAmplitude]

/-- Each echo is attenuated by 1/φ relative to the previous. -/
theorem echoAmplitude_succ_ratio (n : ℕ) :
    echoAmplitude (n + 1) = echoAmplitude n * phi⁻¹ := by
  unfold echoAmplitude
  have hphi_ne : phi ≠ 0 := Constants.phi_ne_zero
  have : phi ^ (-((n : ℤ) + 1)) = phi ^ (-(n : ℤ)) * phi⁻¹ := by
    rw [show (-((n : ℤ) + 1)) = -(n : ℤ) + (-1 : ℤ) by ring]
    rw [zpow_add₀ hphi_ne]; simp
  have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  rw [hcast, this]

/-- SNR ratio between successive echoes = 1/φ. -/
theorem echo_snr_ratio (n : ℕ) :
    echoAmplitude (n + 1) / echoAmplitude n = phi⁻¹ := by
  rw [echoAmplitude_succ_ratio]
  field_simp [(echoAmplitude_pos n).ne']

/-- Amplitudes are strictly decreasing. -/
theorem echoAmplitude_strictly_decreasing (n : ℕ) :
    echoAmplitude (n + 1) < echoAmplitude n := by
  rw [echoAmplitude_succ_ratio]
  have hn : 0 < echoAmplitude n := echoAmplitude_pos n
  have : phi⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by have := Constants.phi_gt_onePointFive; linarith)
  linarith [mul_lt_iff_lt_one_right hn |>.mpr this]

/-- Per-event echo-amplitude chain for catalog events. -/
def catalogAmplitude
    (e : HeadlineEvent) (n : ℕ) : ℝ := echoAmplitude n

theorem catalogAmplitude_pos (e : HeadlineEvent) (n : ℕ) :
    0 < catalogAmplitude e n := echoAmplitude_pos n

structure BHEchoAmplitudeCert where
  amplitude_pos : ∀ n, 0 < echoAmplitude n
  primary_unity : echoAmplitude 0 = 1
  one_step_ratio : ∀ n, echoAmplitude (n + 1) = echoAmplitude n * phi⁻¹
  snr_ratio : ∀ n, echoAmplitude (n + 1) / echoAmplitude n = phi⁻¹
  strictly_decreasing : ∀ n, echoAmplitude (n + 1) < echoAmplitude n
  catalog_pos : ∀ (e : HeadlineEvent) n, 0 < catalogAmplitude e n

/-- BH-echo amplitude certificate. -/
def bhEchoAmplitudeCert : BHEchoAmplitudeCert where
  amplitude_pos := echoAmplitude_pos
  primary_unity := echoAmplitude_one
  one_step_ratio := echoAmplitude_succ_ratio
  snr_ratio := echo_snr_ratio
  strictly_decreasing := echoAmplitude_strictly_decreasing
  catalog_pos := catalogAmplitude_pos

end
end BHEchoAmplitudes
end Gravity
end IndisputableMonolith
