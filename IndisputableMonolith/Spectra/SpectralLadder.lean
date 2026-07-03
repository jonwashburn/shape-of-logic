import Mathlib
import IndisputableMonolith.Constants

/-!
# Spectral Ladder (scaffold)

Cross-domain spectral rails: f_n = f0 · φ^{2n}, where f0 = E_coh / h.
This module exposes basic helpers for rails and an eight-gate coherence test.
-/

namespace IndisputableMonolith
namespace Spectra
namespace SpectralLadder

open scoped BigOperators Real

noncomputable section

/-- Base frequency f0 (e.g., E_coh/h) is supplied by the caller.
    A default fit-free choice from RS gates is \(1/(2\pi\cdot\tau_0)\). -/
def f0_default : ℝ := 1 / (2 * Real.pi * IndisputableMonolith.Constants.tau0)

def railFactor (n : ℤ) : ℝ :=
  Real.rpow IndisputableMonolith.Constants.phi ((2 : ℝ) * (n : ℝ))

def frequencyOnRail (f0 : ℝ) (n : ℤ) : ℝ :=
  f0 * railFactor n

/-- Sliding sum over 8 samples (coherence/neutrality diagnostic). -/
def sum8 (x : ℕ → ℝ) (t0 : ℕ) : ℝ :=
  (Finset.range 8).sum (fun k => x (t0 + k))

def eightGateCoherent (x : ℕ → ℝ) (t0 : ℕ) : Prop :=
  sum8 x t0 = 0

end

end SpectralLadder
end Spectra
end IndisputableMonolith
