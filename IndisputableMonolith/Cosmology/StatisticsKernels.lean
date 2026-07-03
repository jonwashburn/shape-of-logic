import Mathlib
import IndisputableMonolith.Cosmology.PhaseSpaceReduction

/-!
# Statistics Kernels: `∓ln(1∓e^{−t})` and `t/(eᵗ∓1)` from the partition function

## What this module derives

`PhaseSpaceReduction` (and `GrandPotential` before it) took the Bose/Fermi
pressure kernels `−ln(1−e^{−t})`, `ln(1+e^{−t})` and energy kernels
`t/(eᵗ∓1)` as *definitions* (MODEL).  This module derives all four from
the grand partition function of a single mode at `μ = 0`:

  `Z_mode = Σ_n  e^{−n·E/T}`   over the allowed occupancies `n`,

with `t = E/T` dimensionless.  The only inputs are:

* the Gibbs weight `e^{−n·t}` of the `n`-quanta microstate, and
* the occupancy sets: `n ∈ ℕ` for bosons (unrestricted),
  `n ∈ {0, 1}` for fermions (Pauli exclusion).

From these:

1. **Partition functions** (`bosePartition_eq`, `fermiPartition_eq`):
   the geometric series gives `Z_B = (1−e^{−t})⁻¹`; the two-state sum
   gives `Z_F = 1 + e^{−t}`.
2. **Pressure kernels are `ln Z`** (`boseLogKernel_eq_log_partition`,
   `fermiLogKernel_eq_log_partition`): the previously-defined log kernels
   are literally `ln Z_mode`.
3. **Occupation numbers** (`boseOccupation_eq`, `fermiOccupation_eq`):
   the ensemble mean `⟨n⟩ = (Σ n·wₙ)/Z` evaluates to the Bose–Einstein
   `1/(eᵗ−1)` and Fermi–Dirac `1/(eᵗ+1)` distributions.
4. **Energy kernels are `t·⟨n⟩`** (`boseEnergyKernel_eq_occupation`,
   `fermiEnergyKernel_eq_occupation`).
5. **Thermodynamic consistency** (`boseLogKernel_hasDerivAt`,
   `mode_energy_bose`, …): `⟨n⟩ = −d(ln Z)/dt`, and in physical
   variables `⟨E⟩ = −∂_β ln Z` per mode — the pressure and energy
   kernels are not independent inputs but derivative-related, exactly
   as the grand-canonical formalism demands.
6. **Capstones** (`plasmaPressure_from_partitionFunction`,
   `plasmaEnergy_from_occupation`): the plasma pressure/energy of the
   η_B chain now start from `Σ e^{−nE/T}` in momentum space.

## Provenance ledger (honest tags)

* THEOREM (this module): the four kernel functional forms; the BE/FD
  distributions; `⟨n⟩ = −d ln Z/dt`; `⟨E⟩ = −∂_β ln Z`; the Pauli bound
  `⟨n⟩_F < 1`; the identification with the `GrandPotential` integrands.
* MODEL (remaining upstream inputs): the Gibbs weight `e^{−βE}` itself
  (the canonical-ensemble measure), and the occupancy sets — bosonic
  `ℕ` vs fermionic `{0,1}`.  The RS-side exclusion principle is
  formalized as a J-cost statement in
  `Foundation.PauliExclusionFromJCost` / `Foundation.SpinStatistics`;
  the bridge from that certificate to the occupancy set `{0,1}` used
  here remains OPEN.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace StatisticsKernels

open Real MeasureTheory Set
open PhaseSpaceReduction (boseLogKernel fermiLogKernel boseEnergyKernel
  fermiEnergyKernel phaseSpaceDensity)

/-! ## §1. Single-mode Gibbs weights and partition functions -/

/-- Gibbs weight of the `n`-quanta microstate of a mode at dimensionless
energy `t = E/T` (equivalently `β·E`), chemical potential zero:
`w_n = e^{−n·t}`. -/
noncomputable def boltzmannWeight (t : ℝ) (n : ℕ) : ℝ := Real.exp (-(n * t))

/-- Bosonic single-mode grand partition function: unrestricted occupancy,
`Z_B(t) = Σ_{n∈ℕ} e^{−n·t}`. -/
noncomputable def bosePartition (t : ℝ) : ℝ := ∑' n : ℕ, boltzmannWeight t n

/-- Fermionic single-mode grand partition function: Pauli-restricted
occupancy `n ∈ {0,1}`, `Z_F(t) = Σ_{n<2} e^{−n·t}`. -/
noncomputable def fermiPartition (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 2, boltzmannWeight t n

/-- Mean occupation of a bosonic mode: `⟨n⟩ = (Σ n·w_n)/Z_B`. -/
noncomputable def boseOccupation (t : ℝ) : ℝ :=
  (∑' n : ℕ, (n : ℝ) * boltzmannWeight t n) / bosePartition t

/-- Mean occupation of a fermionic mode: `⟨n⟩ = (Σ_{n<2} n·w_n)/Z_F`. -/
noncomputable def fermiOccupation (t : ℝ) : ℝ :=
  (∑ n ∈ Finset.range 2, (n : ℝ) * boltzmannWeight t n) / fermiPartition t

/-- The Gibbs weight is the `n`-th power of the one-quantum weight. -/
lemma boltzmannWeight_pow (t : ℝ) (n : ℕ) :
    boltzmannWeight t n = Real.exp (-t) ^ n := by
  unfold boltzmannWeight
  rw [← Real.exp_nat_mul]
  ring_nf

lemma exp_neg_lt_one {t : ℝ} (ht : 0 < t) : Real.exp (-t) < 1 :=
  Real.exp_lt_one_iff.mpr (by linarith)

lemma one_lt_exp {t : ℝ} (ht : 0 < t) : 1 < Real.exp t := by
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr ht

/-! ## §2. Closed forms of the partition functions -/

/-- **Bose partition function** (geometric series): for `t > 0`,
`Z_B(t) = (1 − e^{−t})⁻¹`. -/
theorem bosePartition_eq {t : ℝ} (ht : 0 < t) :
    bosePartition t = (1 - Real.exp (-t))⁻¹ := by
  unfold bosePartition
  simp only [boltzmannWeight_pow]
  exact tsum_geometric_of_lt_one (le_of_lt (Real.exp_pos _))
    (exp_neg_lt_one ht)

/-- **Fermi partition function** (two occupancy states):
`Z_F(t) = 1 + e^{−t}`, for every `t`. -/
theorem fermiPartition_eq (t : ℝ) :
    fermiPartition t = 1 + Real.exp (-t) := by
  unfold fermiPartition boltzmannWeight
  simp [Finset.sum_range_succ]

lemma bosePartition_pos {t : ℝ} (ht : 0 < t) : 0 < bosePartition t := by
  rw [bosePartition_eq ht]
  have := exp_neg_lt_one ht
  exact inv_pos.mpr (by linarith)

lemma fermiPartition_pos (t : ℝ) : 0 < fermiPartition t := by
  rw [fermiPartition_eq]
  positivity

/-! ## §3. The pressure kernels are `ln Z_mode` -/

/-- **THEOREM: the Bose pressure kernel is the log partition function.**
`−ln(1−e^{−t}) = ln Z_B(t)`.  The kernel that was a definition in
`PhaseSpaceReduction` is the grand-canonical `ln Z` of one mode. -/
theorem boseLogKernel_eq_log_partition {t : ℝ} (ht : 0 < t) :
    boseLogKernel t = Real.log (bosePartition t) := by
  rw [bosePartition_eq ht, Real.log_inv]
  rfl

/-- **THEOREM: the Fermi pressure kernel is the log partition function.**
`ln(1+e^{−t}) = ln Z_F(t)`. -/
theorem fermiLogKernel_eq_log_partition (t : ℝ) :
    fermiLogKernel t = Real.log (fermiPartition t) := by
  rw [fermiPartition_eq]
  rfl

/-! ## §4. The occupation numbers: Bose–Einstein and Fermi–Dirac -/

/-- **THEOREM (Bose–Einstein distribution).**  The ensemble-mean
occupation of a bosonic mode is `⟨n⟩_B = 1/(eᵗ−1)`: the weighted
geometric series `Σ n·xⁿ = x/(1−x)²` divided by `Z_B = (1−x)⁻¹`. -/
theorem boseOccupation_eq {t : ℝ} (ht : 0 < t) :
    boseOccupation t = 1 / (Real.exp t - 1) := by
  unfold boseOccupation
  rw [bosePartition_eq ht]
  simp only [boltzmannWeight_pow]
  have hx0 : (0 : ℝ) ≤ Real.exp (-t) := le_of_lt (Real.exp_pos _)
  have hx1 : Real.exp (-t) < 1 := exp_neg_lt_one ht
  rw [tsum_coe_mul_geometric_of_norm_lt_one
    (by rw [Real.norm_of_nonneg hx0]; exact hx1)]
  have hy : 1 < Real.exp t := one_lt_exp ht
  have hy0 : Real.exp t ≠ 0 := ne_of_gt (Real.exp_pos t)
  have hy1 : Real.exp t - 1 ≠ 0 := by linarith
  have h1x : 1 - Real.exp (-t) ≠ 0 := by linarith
  rw [Real.exp_neg]
  rw [Real.exp_neg] at h1x
  field_simp

/-- **THEOREM (Fermi–Dirac distribution).**  The ensemble-mean occupation
of a fermionic mode is `⟨n⟩_F = 1/(eᵗ+1)`, for every `t` (the two-state
sum needs no convergence condition). -/
theorem fermiOccupation_eq (t : ℝ) :
    fermiOccupation t = 1 / (Real.exp t + 1) := by
  unfold fermiOccupation boltzmannWeight
  rw [fermiPartition_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, neg_zero,
    Real.exp_zero, zero_add, add_zero]
  have hy0 : Real.exp t ≠ 0 := ne_of_gt (Real.exp_pos t)
  have hpos : (0 : ℝ) < 1 + Real.exp (-t) := by positivity
  rw [Real.exp_neg]
  rw [Real.exp_neg] at hpos
  field_simp

/-- **Pauli bound.**  A fermionic mode is never more than singly
occupied on average: `⟨n⟩_F < 1`.  This is the statistical shadow of the
occupancy restriction `n ∈ {0,1}`. -/
theorem fermiOccupation_lt_one (t : ℝ) : fermiOccupation t < 1 := by
  rw [fermiOccupation_eq]
  have h := Real.exp_pos t
  rw [div_lt_one (by linarith)]
  linarith

/-- A bosonic mode at positive energy has positive mean occupation. -/
theorem boseOccupation_pos {t : ℝ} (ht : 0 < t) : 0 < boseOccupation t := by
  rw [boseOccupation_eq ht]
  have := one_lt_exp ht
  exact div_pos one_pos (by linarith)

/-! ## §5. The energy kernels are `t·⟨n⟩` -/

/-- **THEOREM: the Bose energy kernel is `t·⟨n⟩_B`.**  The integrand of
the plasma energy is (dimensionless energy) × (mean occupation). -/
theorem boseEnergyKernel_eq_occupation {t : ℝ} (ht : 0 < t) :
    boseEnergyKernel t = t * boseOccupation t := by
  rw [boseOccupation_eq ht]
  unfold PhaseSpaceReduction.boseEnergyKernel
  ring

/-- **THEOREM: the Fermi energy kernel is `t·⟨n⟩_F`.** -/
theorem fermiEnergyKernel_eq_occupation (t : ℝ) :
    fermiEnergyKernel t = t * fermiOccupation t := by
  rw [fermiOccupation_eq]
  unfold PhaseSpaceReduction.fermiEnergyKernel
  ring

/-! ## §6. Thermodynamic consistency: `⟨n⟩ = −d(ln Z)/dt` -/

/-- **THEOREM (grand-canonical consistency, Bose).**  The mean occupation
is minus the derivative of the log partition function with respect to the
dimensionless energy: `d/dt[−ln(1−e^{−t})] = −⟨n⟩_B(t)`.  The pressure
and energy kernels are therefore *one* input, not two. -/
theorem boseLogKernel_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt boseLogKernel (-(boseOccupation t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s))
      (Real.exp (-t) * (-1)) t := (Real.hasDerivAt_exp (-t)).comp t h1
  have h3 : HasDerivAt (fun s : ℝ => 1 - Real.exp (-s))
      (0 - Real.exp (-t) * (-1)) t := (hasDerivAt_const t 1).sub h2
  have hlt : Real.exp (-t) < 1 := exp_neg_lt_one ht
  have hne : 1 - Real.exp (-t) ≠ 0 := by linarith
  have h4 := (h3.log hne).neg
  have heq : -((0 - Real.exp (-t) * (-1)) / (1 - Real.exp (-t)))
      = -(boseOccupation t) := by
    rw [boseOccupation_eq ht]
    have hy0 : Real.exp t ≠ 0 := ne_of_gt (Real.exp_pos t)
    have hy1 : Real.exp t - 1 ≠ 0 := by
      have := one_lt_exp ht; linarith
    rw [Real.exp_neg]
    rw [Real.exp_neg] at hne
    field_simp
    ring
  rw [← heq]
  exact h4

/-- **THEOREM (grand-canonical consistency, Fermi).**
`d/dt[ln(1+e^{−t})] = −⟨n⟩_F(t)`, for every `t`. -/
theorem fermiLogKernel_hasDerivAt (t : ℝ) :
    HasDerivAt fermiLogKernel (-(fermiOccupation t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s))
      (Real.exp (-t) * (-1)) t := (Real.hasDerivAt_exp (-t)).comp t h1
  have h3 : HasDerivAt (fun s : ℝ => 1 + Real.exp (-s))
      (0 + Real.exp (-t) * (-1)) t := (hasDerivAt_const t 1).add h2
  have hpos : (0 : ℝ) < 1 + Real.exp (-t) := by positivity
  have h4 := h3.log (ne_of_gt hpos)
  have heq : (0 + Real.exp (-t) * (-1)) / (1 + Real.exp (-t))
      = -(fermiOccupation t) := by
    rw [fermiOccupation_eq]
    have hy0 : Real.exp t ≠ 0 := ne_of_gt (Real.exp_pos t)
    rw [Real.exp_neg]
    rw [Real.exp_neg] at hpos
    field_simp
    ring
  rw [← heq]
  exact h4

/-- The energy kernel is `−t` times the derivative of the pressure
kernel: `t/(eᵗ−1) = −t·(d/dt) ln Z_B`.  Pressure kernel in, energy kernel
out — no independent input. -/
theorem boseEnergyKernel_from_logKernel {t : ℝ} (ht : 0 < t) :
    boseEnergyKernel t = -t * deriv boseLogKernel t := by
  rw [(boseLogKernel_hasDerivAt ht).deriv, boseEnergyKernel_eq_occupation ht]
  ring

/-- Fermi version: `t/(eᵗ+1) = −t·(d/dt) ln Z_F`. -/
theorem fermiEnergyKernel_from_logKernel (t : ℝ) :
    fermiEnergyKernel t = -t * deriv fermiLogKernel t := by
  rw [(fermiLogKernel_hasDerivAt t).deriv, fermiEnergyKernel_eq_occupation]
  ring

/-! ## §7. Physical variables: `⟨E⟩ = −∂_β ln Z` per mode -/

/-- **THEOREM (textbook form, Bose).**  For a mode of energy `E > 0`, the
mean energy is minus the β-derivative of the log partition function:
`−∂_β ln Z_B(βE) = E·⟨n⟩_B(βE)`. -/
theorem mode_energy_bose (E : ℝ) (hE : 0 < E) {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun b => Real.log (bosePartition (b * E)))
      (-(E * boseOccupation (β * E))) β := by
  have h1 : HasDerivAt (fun b : ℝ => b * E) E β := by
    simpa using (hasDerivAt_id β).mul_const E
  have hβE : 0 < β * E := mul_pos hβ hE
  have h2 := (boseLogKernel_hasDerivAt hβE).comp β h1
  have h3 : HasDerivAt (fun b => boseLogKernel (b * E))
      (-(E * boseOccupation (β * E))) β := by
    convert h2 using 1
    ring
  apply h3.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hβ] with b hb
  exact (boseLogKernel_eq_log_partition (mul_pos hb hE)).symm

/-- **THEOREM (textbook form, Fermi).**  `−∂_β ln Z_F(βE) = E·⟨n⟩_F(βE)`. -/
theorem mode_energy_fermi (E : ℝ) {β : ℝ} :
    HasDerivAt (fun b => Real.log (fermiPartition (b * E)))
      (-(E * fermiOccupation (β * E))) β := by
  have h1 : HasDerivAt (fun b : ℝ => b * E) E β := by
    simpa using (hasDerivAt_id β).mul_const E
  have h2 := (fermiLogKernel_hasDerivAt (β * E)).comp β h1
  have h3 : HasDerivAt (fun b => fermiLogKernel (b * E))
      (-(E * fermiOccupation (β * E))) β := by
    convert h2 using 1
    ring
  apply h3.congr_of_eventuallyEq
  filter_upwards [Filter.univ_mem] with b _
  exact (fermiLogKernel_eq_log_partition (b * E)).symm

/-! ## §8. Capstones: the plasma potential starts at `Σ e^{−nE/T}` -/

/-- The bose kernels agree a.e. in momentum space (they differ at most at
`k = 0`, a null set), so the phase-space integrals coincide. -/
lemma phaseSpaceDensity_congr_pos (g T : ℝ) (hT : 0 < T) (K₁ K₂ : ℝ → ℝ)
    (h : ∀ t : ℝ, 0 < t → K₁ t = K₂ t) :
    phaseSpaceDensity 3 g T K₁ = phaseSpaceDensity 3 g T K₂ := by
  unfold PhaseSpaceReduction.phaseSpaceDensity
  congr 1
  apply integral_congr_ae
  have h0 : (volume : Measure (EuclideanSpace ℝ (Fin 3))) {0} = 0 :=
    measure_singleton 0
  filter_upwards [compl_mem_ae_iff.mpr h0] with k hk
  have hknorm : (0 : ℝ) < ‖k‖ := norm_pos_iff.mpr (by simpa using hk)
  rw [h (‖k‖ / T) (div_pos hknorm hT)]

/-- **CAPSTONE (pressure).**  The plasma pressure of the η_B chain equals
the phase-space integral of `T·ln Z_mode(E/T)` — the grand-canonical
pressure `P = (T/V)·ln Z` — with `Z_B = Σ_{n∈ℕ} e^{−nE/T}` and
`Z_F = Σ_{n∈{0,1}} e^{−nE/T}`.  The log kernels are gone as inputs; only
the Gibbs weight and the occupancy sets remain. -/
theorem plasmaPressure_from_partitionFunction (gB gF : ℝ) {T : ℝ}
    (hT : 0 < T) :
    phaseSpaceDensity 3 gB T (fun t => Real.log (bosePartition t))
      + phaseSpaceDensity 3 gF T (fun t => Real.log (fermiPartition t))
      = GrandPotential.plasmaPressure gB gF T := by
  have hB := phaseSpaceDensity_congr_pos gB T hT
    (fun t => Real.log (bosePartition t)) boseLogKernel
    (fun t ht => (boseLogKernel_eq_log_partition ht).symm)
  have hF := phaseSpaceDensity_congr_pos gF T hT
    (fun t => Real.log (fermiPartition t)) fermiLogKernel
    (fun t _ => (fermiLogKernel_eq_log_partition t).symm)
  rw [hB, hF]
  exact PhaseSpaceReduction.plasmaPressure_from_phaseSpace gB gF hT

/-- **CAPSTONE (energy).**  The plasma energy equals the phase-space
integral of `E·⟨n⟩(E/T)`: mean occupation times mode energy, with `⟨n⟩`
derived from the same partition functions. -/
theorem plasmaEnergy_from_occupation (gB gF : ℝ) {T : ℝ} (hT : 0 < T) :
    phaseSpaceDensity 3 gB T (fun t => t * boseOccupation t)
      + phaseSpaceDensity 3 gF T (fun t => t * fermiOccupation t)
      = GrandPotential.plasmaEnergy gB gF T := by
  have hB := phaseSpaceDensity_congr_pos gB T hT
    (fun t => t * boseOccupation t) boseEnergyKernel
    (fun t ht => (boseEnergyKernel_eq_occupation ht).symm)
  have hF := phaseSpaceDensity_congr_pos gF T hT
    (fun t => t * fermiOccupation t) fermiEnergyKernel
    (fun t _ => (fermiEnergyKernel_eq_occupation t).symm)
  rw [hB, hF]
  exact PhaseSpaceReduction.plasmaEnergy_from_phaseSpace gB gF hT

/-! ## §9. The number-density integrand is `t²·⟨n⟩` -/

/-- The photon/boson number integrand of `NumberDensityIntegral`
(`t²/(eᵗ−1)`, whose integral is `2ζ(3)`) is `t²·⟨n⟩_B(t)`: number density
counts occupation over modes. -/
theorem number_integrand_bose {t : ℝ} (ht : 0 < t) :
    t ^ 2 * boseOccupation t = t ^ 2 / (Real.exp t - 1) := by
  rw [boseOccupation_eq ht]; ring

/-- Fermion number integrand (`t²/(eᵗ+1)`, integral `(3/2)ζ(3)`) is
`t²·⟨n⟩_F(t)`. -/
theorem number_integrand_fermi (t : ℝ) :
    t ^ 2 * fermiOccupation t = t ^ 2 / (Real.exp t + 1) := by
  rw [fermiOccupation_eq]; ring

end StatisticsKernels
end Cosmology
end IndisputableMonolith
