import Mathlib
import IndisputableMonolith.Cosmology.PartitionKernels
import IndisputableMonolith.Cosmology.FermionWeightIntegral

/-!
# Energy Kernels from Occupation Numbers

**Status: THEOREM targets (loop-managed).** Connects the occupation numbers
derived in `PartitionKernels` (from the per-mode grand partition function) to
the energy integrands `t³/(e^t ∓ 1)` whose integrals are already proved in
`FermionWeightIntegral` (`π⁴/15` and `7π⁴/120`, hence the `7/8` ratio).

With this module the chain reads, end to end:

  partition function `Z` (PartitionKernels)
    → occupation number `⟨n⟩ = 1/(e^t ∓ 1)` (PartitionKernels)
    → energy integrand `t³·⟨n⟩` (this module)
    → integral values and the `7/8` ratio (FermionWeightIntegral /
      ThermalWeightSevenEighths).

So `7/8` is derived from the partition function, not merely from a
conveniently chosen integrand.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace OccupationEnergy

open Real Set MeasureTheory

/-- The Bose energy integrand equals (dimensionless energy per mode `t³`) ×
(the occupation number derived from the partition function). -/
theorem bose_energy_kernel_eq (t : ℝ) (ht : 0 < t) :
    t ^ 3 / (Real.exp t - 1)
      = t ^ 3 * ((∑' n : ℕ, (n : ℝ) * Real.exp (-t) ^ n)
          / (∑' n : ℕ, Real.exp (-t) ^ n)) := by
  rw [PartitionKernels.bose_occupation t ht]
  ring

/-- The Fermi energy integrand equals `t³` × (the Pauli-restricted occupation
number derived from the two-state partition function). -/
theorem fermi_energy_kernel_eq (t : ℝ) (_ht : 0 < t) :
    t ^ 3 / (Real.exp t + 1)
      = t ^ 3 * ((∑ n : Fin 2, ((n : ℕ) : ℝ) * Real.exp (-t) ^ (n : ℕ))
          / (∑ n : Fin 2, Real.exp (-t) ^ (n : ℕ))) := by
  rw [PartitionKernels.fermi_occupation t]
  ring

/-- **The 7/8 ratio, stated at the partition-function level**: the ratio of
the thermal energy integrals, with each integrand written as
`t³ × ⟨n⟩` (occupation numbers from the derived partition functions), is
exactly `7/8`. -/
theorem energy_ratio_seven_eighths :
    (∫ t in Ioi (0 : ℝ),
        t ^ 3 * ((∑ n : Fin 2, ((n : ℕ) : ℝ) * Real.exp (-t) ^ (n : ℕ))
          / (∑ n : Fin 2, Real.exp (-t) ^ (n : ℕ))))
      / (∫ t in Ioi (0 : ℝ),
        t ^ 3 * ((∑' n : ℕ, (n : ℝ) * Real.exp (-t) ^ n)
          / (∑' n : ℕ, Real.exp (-t) ^ n)))
      = 7 / 8 := by
  have hf : (∫ t in Ioi (0 : ℝ),
      t ^ 3 * ((∑ n : Fin 2, ((n : ℕ) : ℝ) * Real.exp (-t) ^ (n : ℕ))
        / (∑ n : Fin 2, Real.exp (-t) ^ (n : ℕ))))
      = ∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t + 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    exact (fermi_energy_kernel_eq t ht).symm
  have hb : (∫ t in Ioi (0 : ℝ),
      t ^ 3 * ((∑' n : ℕ, (n : ℝ) * Real.exp (-t) ^ n)
        / (∑' n : ℕ, Real.exp (-t) ^ n)))
      = ∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    exact (bose_energy_kernel_eq t ht).symm
  rw [hf, hb]
  exact FermionWeightIntegral.fermi_div_bose_integral

/-- **Certificate** for the axiom audit. -/
theorem occupationEnergyCert :
    (∀ t : ℝ, 0 < t →
        t ^ 3 / (Real.exp t - 1)
          = t ^ 3 * ((∑' n : ℕ, (n : ℝ) * Real.exp (-t) ^ n)
              / (∑' n : ℕ, Real.exp (-t) ^ n)))
      ∧ ((∫ t in Ioi (0 : ℝ),
            t ^ 3 * ((∑ n : Fin 2, ((n : ℕ) : ℝ) * Real.exp (-t) ^ (n : ℕ))
              / (∑ n : Fin 2, Real.exp (-t) ^ (n : ℕ))))
          / (∫ t in Ioi (0 : ℝ),
            t ^ 3 * ((∑' n : ℕ, (n : ℝ) * Real.exp (-t) ^ n)
              / (∑' n : ℕ, Real.exp (-t) ^ n)))
          = 7 / 8) :=
  ⟨bose_energy_kernel_eq, energy_ratio_seven_eighths⟩

end OccupationEnergy
end Cosmology
end IndisputableMonolith
