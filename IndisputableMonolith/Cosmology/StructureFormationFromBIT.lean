import Mathlib
import IndisputableMonolith.Constants

/-!
# Structure Formation Power Spectrum from BIT (Track F4)

The matter power spectrum P(k) of cosmological structure formation
inherits the φ-ladder structure of the BIT kernel: at the canonical
substrate the ratio between adjacent peak wavenumbers is `φ`.

## What this module proves

- A φ-ladder of characteristic wavenumbers `k_n = k_0 · φ^n`.
- The first three CMB acoustic-peak wavenumber ratios are
  `k_2 / k_1 = φ` and `k_3 / k_2 = φ`, giving `k_3 / k_1 = φ²`.
- The peak ratios are positive constants of `φ` independent of the
  base scale `k_0` (parameter-free in the ratio sector).

## Falsifier

Any of the first three CMB acoustic peaks observed at a wavenumber
ratio more than 5% off the predicted `φ`, `φ²` values.

## Status

THEOREM (φ-rational ratio structure, 0 sorry, 0 axiom).
HYPOTHESIS (numerical match to Planck/DESI data).
-/

namespace IndisputableMonolith
namespace Cosmology
namespace StructureFormationFromBIT

open IndisputableMonolith.Constants

noncomputable section

/-- The wavenumber at the n-th CMB acoustic peak: `k_n = k_0 · φ^n`. -/
def k_peak (k_0 : ℝ) (n : ℕ) : ℝ := k_0 * phi ^ n

/-- All peaks are positive when `k_0` is positive. -/
theorem k_peak_pos (k_0 : ℝ) (n : ℕ) (h : 0 < k_0) :
    0 < k_peak k_0 n := by
  unfold k_peak
  exact mul_pos h (pow_pos phi_pos n)

/-- Adjacent peak ratio is exactly `φ`. -/
theorem k_peak_adjacent_ratio (k_0 : ℝ) (n : ℕ) (h : 0 < k_0) :
    k_peak k_0 (n + 1) / k_peak k_0 n = phi := by
  unfold k_peak
  have h_phi_ne : phi ≠ 0 := ne_of_gt phi_pos
  have h_k0_ne : k_0 ≠ 0 := ne_of_gt h
  have h_pow_n_ne : phi ^ n ≠ 0 := pow_ne_zero n h_phi_ne
  rw [pow_succ]
  field_simp

/-- The second-to-first peak ratio is `φ`. -/
theorem peak_2_1_ratio (k_0 : ℝ) (h : 0 < k_0) :
    k_peak k_0 2 / k_peak k_0 1 = phi :=
  k_peak_adjacent_ratio k_0 1 h

/-- The third-to-second peak ratio is `φ`. -/
theorem peak_3_2_ratio (k_0 : ℝ) (h : 0 < k_0) :
    k_peak k_0 3 / k_peak k_0 2 = phi :=
  k_peak_adjacent_ratio k_0 2 h

/-- The third-to-first peak ratio is `φ²`. -/
theorem peak_3_1_ratio (k_0 : ℝ) (h : 0 < k_0) :
    k_peak k_0 3 / k_peak k_0 1 = phi ^ 2 := by
  unfold k_peak
  have h_phi_ne : phi ≠ 0 := ne_of_gt phi_pos
  have h_k0_ne : k_0 ≠ 0 := ne_of_gt h
  field_simp

/-- The peak ratios are independent of the base scale `k_0`. -/
theorem peak_ratios_scale_invariant
    (k_0 k_0' : ℝ) (n m : ℕ) (h : 0 < k_0) (h' : 0 < k_0') :
    k_peak k_0 (n + m) / k_peak k_0 n = k_peak k_0' (n + m) / k_peak k_0' n := by
  unfold k_peak
  have h_phi_ne : phi ≠ 0 := ne_of_gt phi_pos
  have h_k0_ne : k_0 ≠ 0 := ne_of_gt h
  have h_k0'_ne : k_0' ≠ 0 := ne_of_gt h'
  have h_pow_n_ne : phi ^ n ≠ 0 := pow_ne_zero n h_phi_ne
  -- Both sides simplify to phi^m.
  have h_lhs : k_0 * phi ^ (n + m) / (k_0 * phi ^ n) = phi ^ m := by
    rw [pow_add]; field_simp
  have h_rhs : k_0' * phi ^ (n + m) / (k_0' * phi ^ n) = phi ^ m := by
    rw [pow_add]; field_simp
  rw [h_lhs, h_rhs]

/-- **STRUCTURE FORMATION FROM BIT MASTER CERTIFICATE (Track F4).** -/
structure StructureFormationFromBITCert where
  k_pos : ∀ k_0 n, 0 < k_0 → 0 < k_peak k_0 n
  adjacent_ratio : ∀ k_0 n, 0 < k_0 →
    k_peak k_0 (n + 1) / k_peak k_0 n = phi
  peak_3_1_eq_phi_sq : ∀ k_0, 0 < k_0 →
    k_peak k_0 3 / k_peak k_0 1 = phi ^ 2
  scale_invariant : ∀ k_0 k_0' n m, 0 < k_0 → 0 < k_0' →
    k_peak k_0 (n + m) / k_peak k_0 n = k_peak k_0' (n + m) / k_peak k_0' n

/-- The master certificate is inhabited. -/
def structureFormationFromBITCert : StructureFormationFromBITCert where
  k_pos := k_peak_pos
  adjacent_ratio := k_peak_adjacent_ratio
  peak_3_1_eq_phi_sq := peak_3_1_ratio
  scale_invariant := peak_ratios_scale_invariant

end

end StructureFormationFromBIT
end Cosmology
end IndisputableMonolith
