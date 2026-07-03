import Mathlib
import IndisputableMonolith.Cosmology.GrandPotential

/-!
# Phase-Space Reduction: the `g/(2π²)·T⁴` prefactor from D = 3

## What this module derives

`GrandPotential.plasmaPressure` and `plasmaEnergy` were *defined* in the
1-dimensional reduced form

  `P = (g/2π²) · T⁴ · ∫ t² K(t) dt`,

i.e. the angular factor `4π/(2π)³ = 1/(2π²)` and the `T⁴` scaling were
assumed as part of the definition (MODEL).  This module derives both from
the underlying 3-dimensional momentum-space integral

  `P = (g/(2π)³) · ∫ d³k  T·K(‖k‖/T)`

using only:

* the radial (co-area) reduction of a Haar integral of a norm-dependent
  function (`MeasureTheory.integral_fun_norm_addHaar`),
* the volume of the unit ball in ℝ³ (`4π/3`), and
* the substitution `k = T·t` (`integral_comp_mul_left_Ioi`).

Both reduction theorems are **unconditional** (no integrability
hypotheses): the Mathlib change-of-variables lemmas hold in junk-value
semantics on both sides simultaneously.

## The dimension connection (Stefan–Boltzmann exponent = D + 1)

`phaseSpaceDensity_T_scaling` proves, for ANY spatial dimension `d ≠ 0`,

  `P_d(T) = T^(d+1) · P_d(1)`.

So the Stefan–Boltzmann exponent 4 is not an independent input: it is
`D + 1` with `D = 3`, and D = 3 is a THEOREM upstream
(`Foundation.UnifiedForcingChain.t8_holds`, the T8 dimension forcing).
`stefan_boltzmann_from_D3` instantiates this at `d = 3`.

## Provenance ledger (honest tags)

* THEOREM (this module): the `1/(2π²)` prefactor = (unit-ball volume
  `4π/3`) × (dimension 3) / (mode density `(2π)³`); the `T⁴` scaling =
  `T^(D+1)` at `D = 3`; the identification of the reduced integrals with
  `plasmaPressure`/`plasmaEnergy`.
* THEOREM (upstream): `D = 3` (T8); the integral values `π⁴/45`, `7π⁴/360`,
  `π⁴/15`, `7π⁴/120` (`RadiationEntropyRelation`, `FermionWeightIntegral`);
  the potential structure `s = dP/dT` (`GrandPotential`).
* MODEL (remaining upstream inputs): the phase-space mode density
  `d³k/(2π)³` per unit volume (Fourier mode counting in a box, ℏ = 1);
  the massless dispersion `E = ‖k‖` (c = 1).
* THEOREM (downstream, `StatisticsKernels`): the Bose/Fermi log kernels
  `∓ln(1∓e^{−E/T})` and energy kernels `t/(eᵗ∓1)` are DERIVED from the
  single-mode grand partition function `Σ e^{−n·E/T}` (geometric series
  for `n ∈ ℕ`, two-state sum for `n ∈ {0,1}`), together with the BE/FD
  distributions and `⟨n⟩ = −d(ln Z)/dt` consistency.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace PhaseSpaceReduction

open Real MeasureTheory Set Metric

/-! ## §1. The phase-space integral and its named kernels -/

/-- Grand-canonical phase-space integral of one massless sector in `d`
spatial dimensions: degeneracy `g`, temperature `T`, dimensionless kernel
`K` evaluated at `E/T` with `E = ‖k‖`, and mode density `1/(2π)^d`.

* Pressure: `K(t) = −ln(1−e^{−t})` (Bose) or `ln(1+e^{−t})` (Fermi),
  from `±T·ln Z` per mode.
* Energy density: `K(t) = t/(eᵗ∓1)`, i.e. `E·n(E/T)` per mode rescaled
  by `T`. -/
noncomputable def phaseSpaceDensity (d : ℕ) (g T : ℝ) (K : ℝ → ℝ) : ℝ :=
  g / (2 * π) ^ d * ∫ k : EuclideanSpace ℝ (Fin d), T * K (‖k‖ / T)

/-- Bose pressure kernel `−ln(1−e^{−t})`. -/
noncomputable def boseLogKernel (t : ℝ) : ℝ := -Real.log (1 - Real.exp (-t))

/-- Fermi pressure kernel `ln(1+e^{−t})`. -/
noncomputable def fermiLogKernel (t : ℝ) : ℝ := Real.log (1 + Real.exp (-t))

/-- Bose energy kernel `t/(eᵗ−1)` (occupation number times `E/T`). -/
noncomputable def boseEnergyKernel (t : ℝ) : ℝ := t / (Real.exp t - 1)

/-- Fermi energy kernel `t/(eᵗ+1)`. -/
noncomputable def fermiEnergyKernel (t : ℝ) : ℝ := t / (Real.exp t + 1)

/-! ## §2. The two reduction lemmas -/

/-- **Radial reduction in D = 3.**  A Haar integral over momentum space of
a function of `‖k‖` collapses to `4π ∫ y² f(y) dy`: the co-area
factorization (sphere × radius), with the angular factor `4π` arriving as
`3 × vol(B³) = 3 × (4π/3)`.  Unconditional. -/
theorem integral_norm_fin_three (f : ℝ → ℝ) :
    (∫ k : EuclideanSpace ℝ (Fin 3), f ‖k‖)
      = 4 * π * ∫ y in Ioi (0 : ℝ), y ^ 2 * f y := by
  have h := MeasureTheory.integral_fun_norm_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) f
  simp only [finrank_euclideanSpace, Fintype.card_fin] at h
  have hball : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (ball 0 1)
      = π * 4 / 3 := by
    rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
    rw [ENNReal.ofReal_one, one_pow, one_mul,
      ENNReal.toReal_ofReal (by positivity)]
  rw [h, hball]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- **Temperature substitution** `y = T·t`: pulls `T^(n+1)` out of a radial
integral with weight `yⁿ` and kernel argument `y/T`.  Unconditional. -/
theorem radial_scale_pow (n : ℕ) (K : ℝ → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ y in Ioi (0 : ℝ), y ^ n * K (y / T))
      = T ^ (n + 1) * ∫ t in Ioi (0 : ℝ), t ^ n * K t := by
  have hT0 : T ≠ 0 := ne_of_gt hT
  have hb : (0 : ℝ) < T⁻¹ := inv_pos.mpr hT
  have hsub := integral_comp_mul_left_Ioi (fun x => x ^ n * K x) 0 hb
  simp only [mul_zero, inv_inv, smul_eq_mul] at hsub
  -- hsub : ∫ x in Ioi 0, (T⁻¹*x)^n * K (T⁻¹*x) = T * ∫ x in Ioi 0, x^n * K x
  have hfun : (fun y : ℝ => y ^ n * K (y / T))
      = fun y : ℝ => T ^ n * ((T⁻¹ * y) ^ n * K (T⁻¹ * y)) := by
    funext y
    rw [inv_mul_eq_div]
    have hpow : T ^ n * (y / T) ^ n = y ^ n := by
      rw [div_pow]
      field_simp
    calc y ^ n * K (y / T)
        = (T ^ n * (y / T) ^ n) * K (y / T) := by rw [hpow]
      _ = T ^ n * ((y / T) ^ n * K (y / T)) := by ring
  rw [hfun, integral_const_mul, hsub]
  ring

/-! ## §3. The main theorem: the 1D form with its `g/(2π²)·T⁴` prefactor -/

/-- **THEOREM (phase-space reduction, D = 3).**  The 3-dimensional
grand-canonical integral reduces to the 1-dimensional form with prefactor
`g/(2π²) · T⁴`:

  `(g/(2π)³) ∫ d³k T·K(‖k‖/T)  =  (g/2π²) · T⁴ · ∫ t² K(t) dt`.

The `1/(2π²)` is `4π/(2π)³` (angular / mode density); the `T⁴` is
`T·T³ = T^(D+1)` from the kernel rescaling and the substitution `k = T·t`.
Nothing about the kernel is used: this holds for pressure, energy, entropy
and number-density kernels alike. -/
theorem phaseSpaceDensity_reduction (g : ℝ) {T : ℝ} (hT : 0 < T)
    (K : ℝ → ℝ) :
    phaseSpaceDensity 3 g T K
      = g / (2 * π ^ 2) * T ^ 4 * ∫ t in Ioi (0 : ℝ), t ^ 2 * K t := by
  unfold phaseSpaceDensity
  have hrad := integral_norm_fin_three (fun y => T * K (y / T))
  simp only [] at hrad
  rw [hrad]
  have hswap : (fun y : ℝ => y ^ 2 * (T * K (y / T)))
      = fun y : ℝ => T * (y ^ 2 * K (y / T)) := by
    funext y; ring
  rw [hswap, integral_const_mul, radial_scale_pow 2 K hT]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ## §4. The plasma pressure and energy are the reduced integrals -/

/-- **THEOREM (pressure from phase space).**  The 3D grand-canonical
pressure integral with the Bose/Fermi log kernels *is* the
`GrandPotential.plasmaPressure` that was previously definitional: its
`g/(2π²)·T⁴` prefactor is now derived. -/
theorem plasmaPressure_from_phaseSpace (gB gF : ℝ) {T : ℝ} (hT : 0 < T) :
    phaseSpaceDensity 3 gB T boseLogKernel
      + phaseSpaceDensity 3 gF T fermiLogKernel
      = GrandPotential.plasmaPressure gB gF T := by
  rw [phaseSpaceDensity_reduction gB hT, phaseSpaceDensity_reduction gF hT]
  unfold GrandPotential.plasmaPressure boseLogKernel fermiLogKernel
  rfl

/-- **THEOREM (energy from phase space).**  Same for the energy density:
the 3D integral of `E·n(E/T)` with `E = ‖k‖` is
`GrandPotential.plasmaEnergy`. -/
theorem plasmaEnergy_from_phaseSpace (gB gF : ℝ) {T : ℝ} (hT : 0 < T) :
    phaseSpaceDensity 3 gB T boseEnergyKernel
      + phaseSpaceDensity 3 gF T fermiEnergyKernel
      = GrandPotential.plasmaEnergy gB gF T := by
  rw [phaseSpaceDensity_reduction gB hT, phaseSpaceDensity_reduction gF hT]
  unfold GrandPotential.plasmaEnergy boseEnergyKernel fermiEnergyKernel
  have hB : (fun t : ℝ => t ^ 2 * (t / (Real.exp t - 1)))
      = fun t : ℝ => t ^ 3 / (Real.exp t - 1) := by
    funext t; ring
  have hF : (fun t : ℝ => t ^ 2 * (t / (Real.exp t + 1)))
      = fun t : ℝ => t ^ 3 / (Real.exp t + 1) := by
    funext t; ring
  rw [hB, hF]

/-- **Closed form from the 3D integral.**  Chaining the reduction with the
Mellin-transform integral values: the phase-space pressure is
`(π²/90)(g_B + (7/8)g_F)·T⁴` — Stefan–Boltzmann with the fermionic `7/8`,
now derived end-to-end from the momentum-space integral. -/
theorem phaseSpacePressure_closed_form (gB gF : ℝ) {T : ℝ} (hT : 0 < T) :
    phaseSpaceDensity 3 gB T boseLogKernel
      + phaseSpaceDensity 3 gF T fermiLogKernel
      = π ^ 2 / 90 * (gB + 7 / 8 * gF) * T ^ 4 := by
  rw [plasmaPressure_from_phaseSpace gB gF hT,
    GrandPotential.plasmaPressure_eq]

/-- Energy closed form: `(π²/30)(g_B + (7/8)g_F)·T⁴`. -/
theorem phaseSpaceEnergy_closed_form (gB gF : ℝ) {T : ℝ} (hT : 0 < T) :
    phaseSpaceDensity 3 gB T boseEnergyKernel
      + phaseSpaceDensity 3 gF T fermiEnergyKernel
      = π ^ 2 / 30 * (gB + 7 / 8 * gF) * T ^ 4 := by
  rw [plasmaEnergy_from_phaseSpace gB gF hT,
    GrandPotential.plasmaEnergy_eq]

/-! ## §5. The Stefan–Boltzmann exponent is D + 1 -/

/-- **THEOREM (T-scaling in general dimension).**  In `d ≠ 0` spatial
dimensions the phase-space density scales as `T^(d+1)`:

  `P_d(T) = T^(d+1) · P_d(1)`.

The proof never evaluates the unit-ball volume — the scaling is pure
dimensional analysis of the measure `d^d k` against the substitution
`k = T·t`.  The exponent is structural: one power of `T` per momentum
dimension plus one from the kernel prefactor. -/
theorem phaseSpaceDensity_T_scaling (d : ℕ) (hd : d ≠ 0) (g : ℝ) {T : ℝ}
    (hT : 0 < T) (K : ℝ → ℝ) :
    phaseSpaceDensity d g T K = T ^ (d + 1) * phaseSpaceDensity d g 1 K := by
  haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
  unfold phaseSpaceDensity
  have h1 := MeasureTheory.integral_fun_norm_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (fun y => T * K (y / T))
  have h2 := MeasureTheory.integral_fun_norm_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (fun y => (1 : ℝ) * K (y / 1))
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    nsmul_eq_mul, div_one, one_mul] at h1 h2
  simp only [div_one, one_mul]
  rw [h1, h2]
  have hswap : (fun y : ℝ => y ^ (d - 1) * (T * K (y / T)))
      = fun y : ℝ => T * (y ^ (d - 1) * K (y / T)) := by
    funext y; ring
  rw [hswap, integral_const_mul, radial_scale_pow (d - 1) K hT,
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)]
  ring

/-- **Stefan–Boltzmann from D = 3.**  At the forced spatial dimension
`D = 3` (THEOREM upstream: `Foundation.UnifiedForcingChain.t8_holds`), the
scaling exponent is `3 + 1 = 4`.  The `T⁴` of radiation thermodynamics is
the dimension theorem wearing thermodynamic clothes. -/
theorem stefan_boltzmann_from_D3 (g : ℝ) {T : ℝ} (hT : 0 < T)
    (K : ℝ → ℝ) :
    phaseSpaceDensity 3 g T K = T ^ 4 * phaseSpaceDensity 3 g 1 K :=
  phaseSpaceDensity_T_scaling 3 (by norm_num) g hT K

/-! ## §6. The potential structure now starts in momentum space -/

/-- **Capstone: `s = dP/dT` for the phase-space pressure.**  The derivative
of the 3D momentum-space pressure integral is the `radiationEntropy` built
from the independent entropy integrals: the full chain

  3D phase space → 1D reduction → potential `P(T)` → `s = P′` →
  Euler `ρ = Ts − P` → `g*s`, dilution `4/11`, `p = ρ/3`

is now anchored at the grand-canonical momentum integral, with only the
mode density `1/(2π)³`, the dispersion `E = ‖k‖`, and the statistics
kernels remaining as upstream inputs. -/
theorem phaseSpacePressure_potential (gB gF : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun T => phaseSpaceDensity 3 gB T boseLogKernel
        + phaseSpaceDensity 3 gF T fermiLogKernel)
      (NeutrinoDilution.radiationEntropy gB gF x) x := by
  have hbase := GrandPotential.plasmaPressure_potential gB gF x
  apply hbase.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with T hT
  exact plasmaPressure_from_phaseSpace gB gF hT

end PhaseSpaceReduction
end Cosmology
end IndisputableMonolith
