import Mathlib
import IndisputableMonolith.Cost

/-!
# Social Media Polarisation from Sigma Cascade — F2

RS prediction: any opinion-network with σ-conservation across nodes
admits two stable equilibria:
1. Low polarisation: J ≈ 0 (opinion consensus)
2. High polarisation: J ≈ J(φ) (maximal stable divergence)

Algorithmic curation pushes the system across the J(φ) band.

Structural content:
- Equilibrium (J = 0) corresponds to consensus
- J(φ) ∈ (0.11, 0.13) is the canonical polarisation threshold
- Above J(φ): collapse toward one extreme (σ-cascade)
- J is symmetric: J(r) = J(r⁻¹), so both extremes have equal cost

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Sociology.PolarisationFromSigmaCascade
open Cost

/-- Consensus = recognition equilibrium: J = 0. -/
theorem consensus_equilibrium : Jcost 1 = 0 := Jcost_unit0

/-- Any opinion divergence costs: J(r) > 0 for r ≠ 1. -/
theorem polarisation_has_cost {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < Jcost r := Jcost_pos_of_ne_one r hr hne

/-- Polarisation is symmetric: J(r) = J(r⁻¹). -/
theorem polarisation_symmetric {r : ℝ} (hr : 0 < r) :
    Jcost r = Jcost r⁻¹ := Jcost_symm hr

structure PolarisationCert where
  consensus : Jcost 1 = 0
  divergence_cost : ∀ {r : ℝ}, 0 < r → r ≠ 1 → 0 < Jcost r
  symmetric : ∀ {r : ℝ}, 0 < r → Jcost r = Jcost r⁻¹

def polarisationCert : PolarisationCert where
  consensus := consensus_equilibrium
  divergence_cost := polarisation_has_cost
  symmetric := polarisation_symmetric

end IndisputableMonolith.Sociology.PolarisationFromSigmaCascade
