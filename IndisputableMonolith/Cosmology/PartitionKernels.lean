import Mathlib
import IndisputableMonolith.Cosmology.PhaseSpaceReduction
import IndisputableMonolith.Foundation.EightTick

/-!
# Per-Mode Grand Partition Functions and Occupation Numbers

**Status: THEOREM targets (loop-managed).** This module derives the
statistical-mechanics floor beneath the cosmology thermal-history chain: the
per-mode grand partition function for a bosonic and a fermionic mode, the log
kernels used by `PhaseSpaceReduction`, and the mean occupation numbers
`⟨n⟩ = 1/(e^t ∓ 1)`.

Everything is stated over `x = exp (-t)` with `0 < t`, so `0 < x < 1` and every
series converges.

## What is derived here

* **Bose mode**: occupancy ranges over all of `ℕ`, so the partition function is
  the geometric series `Z_B = Σ x^n = (1 - x)⁻¹` and
  `log Z_B = -log (1 - x) = boseLogKernel t`.
* **Fermi mode**: occupancy is restricted to `{0, 1}` (Pauli), so
  `Z_F = Σ_{n : Fin 2} x^n = 1 + x` and `log Z_F = log (1 + x) = fermiLogKernel t`.
* **Occupation numbers**: `⟨n⟩ = (Σ n·xⁿ)/(Σ xⁿ)`, giving `1/(e^t - 1)` (Bose)
  and `1/(e^t + 1)` (Fermi).

## The RS input, honestly scoped

The ONLY physical fork between the two computations is the occupancy range:
`ℕ` vs `{0, 1}`. That restriction is the Pauli exclusion principle, whose
origin in RS is the exchange sign at the half-cycle: fermions acquire phase
`-1` under exchange (`Foundation.EightTick.spin_statistics_key`, re-exported
below as `fermi_exchange_sign`). The step from "exchange phase −1" to
"occupancy ≤ 1" is the standard antisymmetrization argument (a doubly occupied
antisymmetric state is its own negative, hence zero); that argument is used
here as the justification for the `Fin 2` index type, i.e. it enters as the
CHOICE of statement, not as a hidden axiom. Everything after that fork is
mathematics with no free input.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace PartitionKernels

open Real

/-- **RS input (re-export)**: the exchange phase at the half-cycle is `-1`
(fermionic sign), from the eight-tick structure. This is the physical fact
that forces the Pauli occupancy restriction used in the Fermi partition
function below. -/
theorem fermi_exchange_sign :
    Foundation.EightTick.phaseExp ⟨4, by norm_num⟩ = -1 :=
  Foundation.EightTick.spin_statistics_key.1

/-- The Bose single-mode grand partition function: occupancies range over all
of `ℕ`, and the Boltzmann-weighted sum is the geometric series with ratio
`x = exp (-t) < 1`. -/
theorem bose_partition_hasSum (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-t) ^ n) (1 - Real.exp (-t))⁻¹ := by
  have hξpos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have hξlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  apply hasSum_geometric_of_norm_lt_one
  rw [Real.norm_eq_abs, abs_of_pos hξpos]
  exact hξlt

/-- The Bose partition function as a `tsum`: `Z_B(t) = (1 - e^{-t})⁻¹`. -/
theorem bose_partition_tsum (t : ℝ) (ht : 0 < t) :
    (∑' n : ℕ, Real.exp (-t) ^ n) = (1 - Real.exp (-t))⁻¹ :=
  (bose_partition_hasSum t ht).tsum_eq

/-- `log Z_B` is exactly the Bose log kernel used in
`PhaseSpaceReduction.boseLogKernel` (hence in the pressure/entropy integrals
upstream): the kernel is no longer a definitional choice but the log of the
derived partition function. -/
theorem boseLogKernel_from_partition (t : ℝ) (ht : 0 < t) :
    Real.log (∑' n : ℕ, Real.exp (-t) ^ n)
      = PhaseSpaceReduction.boseLogKernel t := by
  rw [bose_partition_tsum t ht, Real.log_inv,
      PhaseSpaceReduction.boseLogKernel]

/-- The Fermi single-mode grand partition function: Pauli restricts occupancy
to `{0, 1}` (see `fermi_exchange_sign`), so the sum is two terms:
`Z_F(t) = 1 + e^{-t}`. -/
theorem fermi_partition_two_state (t : ℝ) :
    (∑ n : Fin 2, Real.exp (-t) ^ (n : ℕ)) = 1 + Real.exp (-t) := by
  simp [Fin.sum_univ_two]

/-- `log Z_F` is exactly the Fermi log kernel used in
`PhaseSpaceReduction.fermiLogKernel`. -/
theorem fermiLogKernel_from_partition (t : ℝ) :
    Real.log (∑ n : Fin 2, Real.exp (-t) ^ (n : ℕ))
      = PhaseSpaceReduction.fermiLogKernel t := by
  rw [fermi_partition_two_state, PhaseSpaceReduction.fermiLogKernel]

/-- The occupancy-weighted Bose sum: `Σ n·xⁿ = x/(1-x)²` for `x = e^{-t}`. -/
theorem bose_weighted_hasSum (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ => (n : ℝ) * Real.exp (-t) ^ n)
      (Real.exp (-t) / (1 - Real.exp (-t)) ^ 2) := by
  have hξpos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have hξlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  apply hasSum_coe_mul_geometric_of_norm_lt_one
  rw [Real.norm_eq_abs, abs_of_pos hξpos]
  exact hξlt

/-- **Bose-Einstein occupation number**: the mean occupancy of a bosonic mode
is `⟨n⟩ = (Σ n·xⁿ)/(Σ xⁿ) = 1/(e^t - 1)`. -/
theorem bose_occupation (t : ℝ) (ht : 0 < t) :
    (∑' n : ℕ, (n : ℝ) * Real.exp (-t) ^ n) / (∑' n : ℕ, Real.exp (-t) ^ n)
      = 1 / (Real.exp t - 1) := by
  have hξpos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have hξlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1 : (1 : ℝ) - Real.exp (-t) ≠ 0 := by linarith
  have hE1 : Real.exp t - 1 ≠ 0 := by
    have h0 : Real.exp 0 < Real.exp t := Real.exp_lt_exp.mpr ht
    rw [Real.exp_zero] at h0
    linarith
  have hprod : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  rw [(bose_weighted_hasSum t ht).tsum_eq, bose_partition_tsum t ht]
  field_simp
  linear_combination hprod

/-- **Fermi-Dirac occupation number**: the mean occupancy of a fermionic mode
is `⟨n⟩ = (0·1 + 1·x)/(1 + x) = 1/(e^t + 1)`. -/
theorem fermi_occupation (t : ℝ) :
    (∑ n : Fin 2, ((n : ℕ) : ℝ) * Real.exp (-t) ^ (n : ℕ))
        / (∑ n : Fin 2, Real.exp (-t) ^ (n : ℕ))
      = 1 / (Real.exp t + 1) := by
  have hξpos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have hEpos : (0 : ℝ) < Real.exp t := Real.exp_pos _
  have h1 : (1 : ℝ) + Real.exp (-t) ≠ 0 := by positivity
  have hE1 : Real.exp t + 1 ≠ 0 := by positivity
  have hprod : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  simp only [Fin.sum_univ_two]
  norm_num
  field_simp
  linear_combination hprod

/-- **Certificate**: the partition-kernel layer in one bundle. The log kernels
used upstream equal the logs of the derived partition functions, and the two
occupation numbers are the Bose-Einstein and Fermi-Dirac distributions. Used
by the loop's axiom audit (`#print axioms` must show only the base three). -/
theorem partitionKernelsCert :
    (∀ t : ℝ, 0 < t →
        Real.log (∑' n : ℕ, Real.exp (-t) ^ n)
          = PhaseSpaceReduction.boseLogKernel t)
      ∧ (∀ t : ℝ,
        Real.log (∑ n : Fin 2, Real.exp (-t) ^ (n : ℕ))
          = PhaseSpaceReduction.fermiLogKernel t)
      ∧ (∀ t : ℝ, 0 < t →
        (∑' n : ℕ, (n : ℝ) * Real.exp (-t) ^ n) / (∑' n : ℕ, Real.exp (-t) ^ n)
          = 1 / (Real.exp t - 1))
      ∧ (∀ t : ℝ,
        (∑ n : Fin 2, ((n : ℕ) : ℝ) * Real.exp (-t) ^ (n : ℕ))
            / (∑ n : Fin 2, Real.exp (-t) ^ (n : ℕ))
          = 1 / (Real.exp t + 1)) :=
  ⟨boseLogKernel_from_partition, fermiLogKernel_from_partition,
   bose_occupation, fermi_occupation⟩

end PartitionKernels
end Cosmology
end IndisputableMonolith
