import Mathlib
import IndisputableMonolith.Cosmology.EntropyPerPhoton
import IndisputableMonolith.Cosmology.FermionWeightIntegral

/-!
# Number-Density Integrals: `∫ t²/(eᵗ−1) = 2ζ(3)` and the 3/4 Fermion Weight

**Status: THEOREM (integral layer, s = 3).**

`Cosmology.FermionWeightIntegral` closed the *energy-density* integrals (the
Mellin transforms at `s = 4`). This module closes the *number-density* layer
(`s = 3`), which is the last analytic ingredient of the
`entropyPerPhoton_eq_ratio` formula:

  photon number density  `n_γ = (g_γ/(2π²)) T³ ∫ t²/(eᵗ−1) dt = (2ζ(3)/π²) T³`.

The results:

  Bose:  `∫_{0}^{∞} t²/(eᵗ−1) dt = Γ(3)·ζ(3) = 2·ζ(3)`
  Fermi: `∫_{0}^{∞} t²/(eᵗ+1) dt = Γ(3)·η(3) = (3/2)·ζ(3)`,

so the number-density fermion weight is `η(3)/ζ(3) = 1 − 2⁻² = 3/4` (the
companion of the 7/8 *entropy* weight; it is what dilutes fermionic *number*
densities, e.g. `n_ν/n_γ` per species before dilution).

## Derivation

Same two-step Mellin argument as the `s = 4` module, at `s = 3`:

1. **Series layer.** Split `ζ(3) = ∑ 1/n³` into even and odd parts:
   `∑ 1/(2k)³ = ζ(3)/8`, hence odd part `= (7/8)ζ(3)`, hence
   `η(3) = odd − even = (3/4)·ζ(3)`. (Here `ζ(3)` is
   `EntropyPerPhoton.zeta3`, the Apéry constant as a `tsum`; no closed form
   exists and none is needed.)
2. **Integral layer.** `hasSum_mellin` turns the geometric expansions of the
   kernels (`FermionWeightIntegral.bose_series` / `fermi_series`) into
   Dirichlet series at `s = 3` with `Γ(3) = 2`, and uniqueness of
   unconditional sums evaluates both Mellin integrals.

## Capstone

`entropyPerPhoton_from_integrals` rewrites the whole
`entropyPerPhoton = π⁴·g*s/(45·ζ(3))` ratio as a ratio of the two derived
thermodynamic integrals: numerator `(4/3)·(∫t³/(eᵗ−1))/(2π²)·g*s` (entropy
density coefficient via `s = (4/3)ρ/T`), denominator
`g_γ·(∫t²/(eᵗ−1))/(2π²)` (photon number density coefficient). After this
module the only MODEL content left in the entropy-per-photon chain is the
particle census (`g_γ = 2`, `g_e = 4`, `g_ν = 6`) and the statistical-
mechanics identifications (phase-space measure, `s = (4/3)ρ/T`); every
analytic constant is THEOREM. All theorems here are axiom-clean.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace NumberDensityIntegral

open Real MeasureTheory Set
open EntropyPerPhoton (zeta3 zeta3_summable zeta3_pos)
open FermionWeightIntegral (boseKernel fermiKernel bose_series fermi_series)

/-! ## §1. ζ(3) as an unshifted `HasSum` (the `n = 0` term vanishes) -/

/-- `∑_{n≥0} 1/(n+1)³ = ζ(3)`: the defining sum of `EntropyPerPhoton.zeta3`. -/
lemma hasSum_zeta3_shift :
    HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 3) zeta3 := by
  unfold EntropyPerPhoton.zeta3
  exact zeta3_summable.hasSum

/-- `∑_{n≥0} 1/n³ = ζ(3)` over all of ℕ (the `n = 0` term is `1/0 = 0`). -/
lemma hasSum_zeta3_unshifted :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) zeta3 := by
  have hshift : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3) zeta3 :=
    hasSum_zeta3_shift.congr_fun fun n => by push_cast; ring
  have h := (hasSum_nat_add_iff
    (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) 1).mp hshift
  simpa using h

/-! ## §2. Series layer: η(3) = (3/4)·ζ(3) by the even/odd split -/

/-- Pointwise identity `1/(2k)³ = (1/k³)/8`, including `k = 0` where both
sides are `0` (division by zero). -/
lemma even_term_eq :
    (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 3)
      = fun k : ℕ => ((1 : ℝ) / (k : ℝ) ^ 3) / 8 := by
  funext k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; norm_num
  · have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    push_cast
    field_simp
    ring

/-- The even-index part of `ζ(3)`: `∑_k 1/(2k)³ = ζ(3)/8`. -/
lemma hasSum_even :
    HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 3) (zeta3 / 8) := by
  rw [even_term_eq]
  exact hasSum_zeta3_unshifted.div_const 8

lemma summable_odd :
    Summable (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 3) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) :=
    hasSum_zeta3_unshifted.summable
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    simp only at hab
    omega
  have h2 := h.comp_injective hinj
  exact h2.congr fun k => by simp only [Function.comp_apply]

/-- The odd-index part of `ζ(3)`: `∑_k 1/(2k+1)³ = ζ(3)·(7/8)`, by
subtraction and uniqueness of unconditional sums. -/
lemma hasSum_odd :
    HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 3)
      (zeta3 * (7 / 8)) := by
  obtain ⟨B, hB⟩ := summable_odd
  have hfull : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) (zeta3 / 8 + B) :=
    HasSum.even_add_odd hasSum_even hB
  have hval : zeta3 / 8 + B = zeta3 := hfull.unique hasSum_zeta3_unshifted
  have hBval : B = zeta3 * (7 / 8) := by linarith
  exact hBval ▸ hB

/-- Even-index terms of the alternating series are negatives of the
even-`ζ` terms. -/
lemma eta_term_even (k : ℕ) :
    ((-1 : ℝ)) ^ (2 * k + 1) / ((2 * k : ℕ) : ℝ) ^ 3
      = -((1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 3) := by
  rw [(odd_two_mul_add_one k).neg_one_pow]
  push_cast
  ring

/-- Odd-index terms of the alternating series are the odd-`ζ` terms. -/
lemma eta_term_odd (k : ℕ) :
    ((-1 : ℝ)) ^ (2 * k + 1 + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ 3
      = (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 3 := by
  have heven : Even (2 * k + 1 + 1) := ⟨k + 1, by ring⟩
  rw [heven.neg_one_pow]

/-- **THEOREM (η(3) as a `HasSum`).** The alternating series
`∑ (−1)^(n+1)/n³` converges unconditionally to `(3/4)·ζ(3)`,
i.e. `η(3) = (3/4)·ζ(3)`. -/
theorem hasSum_eta_three :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 3)
      (3 / 4 * zeta3) := by
  have he : HasSum
      (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / ((2 * k : ℕ) : ℝ) ^ 3)
      (-(zeta3 / 8)) := by
    have hfun : (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / ((2 * k : ℕ) : ℝ) ^ 3)
        = fun k : ℕ => -((1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 3) := by
      funext k; exact eta_term_even k
    rw [hfun]
    exact hasSum_even.neg
  have ho : HasSum
      (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1 + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ 3)
      (zeta3 * (7 / 8)) := by
    have hfun : (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1 + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ 3)
        = fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 3 := by
      funext k; exact eta_term_odd k
    rw [hfun]
    exact hasSum_odd
  have h := HasSum.even_add_odd
    (f := fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 3) he ho
  convert h using 1
  ring

/-- `∑_{n≥0} (−1)ⁿ/(n+1)³ = η(3) = (3/4)·ζ(3)` (index-shifted). -/
lemma hasSum_eta3_shift :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 3)
      (3 / 4 * zeta3) := by
  have hbase : HasSum (fun m : ℕ => (-1 : ℝ) ^ (m + 1) / (m : ℝ) ^ 3)
      (3 / 4 * zeta3
        + ∑ i ∈ Finset.range 1, (-1 : ℝ) ^ (i + 1) / (i : ℝ) ^ 3) := by
    simpa using hasSum_eta_three
  have h := (hasSum_nat_add_iff
    (f := fun m : ℕ => (-1 : ℝ) ^ (m + 1) / (m : ℝ) ^ 3) 1).mpr hbase
  exact h.congr_fun fun n => by push_cast [pow_succ]; ring

/-- Summability of the shifted `p`-series with real (rpow) exponent 3, as
required by `hasSum_mellin`. -/
lemma summable_shift_rpow3 :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (3 : ℝ)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (3 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have h2 := (summable_nat_add_iff
    (f := fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ (3 : ℝ)) 1).mpr h
  exact h2.congr fun n => by push_cast; ring_nf

/-! ## §3. Mellin transforms at s = 3 -/

/-- Mellin/Dirichlet identity for the Bose kernel at `s = 3`. -/
lemma hasSum_mellin_bose3 :
    HasSum (fun n : ℕ =>
        Complex.Gamma 3 * (1 : ℂ) / (((n : ℝ) + 1 : ℝ) : ℂ) ^ (3 : ℂ))
      (mellin boseKernel 3) := by
  refine hasSum_mellin (a := fun _ : ℕ => (1 : ℂ)) (p := fun n : ℕ => (n : ℝ) + 1)
    (F := boseKernel) (s := 3)
    (fun i => Or.inr (by positivity)) (by norm_num) (fun t ht => ?_) ?_
  · have ht' : (0 : ℝ) < t := ht
    have hC : HasSum (fun n : ℕ => ((Real.exp (-t) ^ (n + 1) : ℝ) : ℂ))
        (boseKernel t) := Complex.hasSum_ofReal.mpr (bose_series ht')
    refine hC.congr_fun fun n => ?_
    have hexp : Real.exp (-((n : ℝ) + 1) * t) = Real.exp (-t) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [one_mul, hexp]
  · simpa using summable_shift_rpow3

/-- Mellin/Dirichlet identity for the Fermi kernel at `s = 3`. -/
lemma hasSum_mellin_fermi3 :
    HasSum (fun n : ℕ =>
        Complex.Gamma 3 * (-1 : ℂ) ^ n / (((n : ℝ) + 1 : ℝ) : ℂ) ^ (3 : ℂ))
      (mellin fermiKernel 3) := by
  refine hasSum_mellin (a := fun n : ℕ => (-1 : ℂ) ^ n)
    (p := fun n : ℕ => (n : ℝ) + 1) (F := fermiKernel) (s := 3)
    (fun i => Or.inr (by positivity)) (by norm_num) (fun t ht => ?_) ?_
  · have ht' : (0 : ℝ) < t := ht
    have hC : HasSum
        (fun n : ℕ => (((-1 : ℝ) ^ n * Real.exp (-t) ^ (n + 1) : ℝ) : ℂ))
        (fermiKernel t) := Complex.hasSum_ofReal.mpr (fermi_series ht')
    refine hC.congr_fun fun n => ?_
    have hexp : Real.exp (-((n : ℝ) + 1) * t) = Real.exp (-t) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  · simpa using summable_shift_rpow3

/-! ## §4. Closed-form values -/

/-- `Γ(3) = 2! = 2`. -/
lemma gamma_three : Complex.Gamma 3 = 2 := by
  have h := Complex.Gamma_ofNat_eq_factorial 2
  norm_num [Nat.factorial] at h
  convert h using 2
  norm_num

/-- `(n+1)^(3:ℂ)` (cpow of a positive real) is the real cube, cast. -/
lemma cpow_shift3 (n : ℕ) :
    ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (3 : ℂ) = ((((n : ℝ) + 1) ^ 3 : ℝ) : ℂ) := by
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  push_cast
  ring

/-- `mellin (1/(eᵗ−1)) 3 = 2·ζ(3)` (i.e. `Γ(3)·ζ(3)`). -/
lemma mellin_bose3_value : mellin boseKernel 3 = ((2 * zeta3 : ℝ) : ℂ) := by
  refine hasSum_mellin_bose3.unique ?_
  have hre : HasSum (fun n : ℕ => (2 : ℝ) * ((1 : ℝ) / ((n : ℝ) + 1) ^ 3))
      (2 * zeta3) := hasSum_zeta3_shift.mul_left 2
  have hC := Complex.hasSum_ofReal.mpr hre
  refine hC.congr_fun fun n => ?_
  rw [gamma_three, cpow_shift3 n]
  push_cast
  ring

/-- `mellin (1/(eᵗ+1)) 3 = (3/2)·ζ(3)` (i.e. `Γ(3)·η(3)`). -/
lemma mellin_fermi3_value : mellin fermiKernel 3 = ((3 / 2 * zeta3 : ℝ) : ℂ) := by
  refine hasSum_mellin_fermi3.unique ?_
  have hre : HasSum (fun n : ℕ => (2 : ℝ) * ((-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 3))
      (3 / 2 * zeta3) := by
    have h := hasSum_eta3_shift.mul_left 2
    convert h using 1
    ring
  have hC := Complex.hasSum_ofReal.mpr hre
  refine hC.congr_fun fun n => ?_
  rw [gamma_three, cpow_shift3 n]
  push_cast
  ring

/-! ## §5. The Mellin transforms are the number-density integrals -/

/-- `mellin boseKernel 3` is the (complexified) Bose number integral. -/
lemma mellin_bose3_eq_integral :
    mellin boseKernel 3
      = (((∫ t in Ioi (0 : ℝ), t ^ 2 / (Real.exp t - 1) : ℝ)) : ℂ) := by
  have h1 : mellin boseKernel 3
      = ∫ t in Ioi (0 : ℝ), ((t ^ 2 / (Real.exp t - 1) : ℝ) : ℂ) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [smul_eq_mul, show (3 : ℂ) - 1 = ((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
    unfold FermionWeightIntegral.boseKernel
    push_cast
    ring
  rw [h1, integral_complex_ofReal]

/-- `mellin fermiKernel 3` is the (complexified) Fermi number integral. -/
lemma mellin_fermi3_eq_integral :
    mellin fermiKernel 3
      = (((∫ t in Ioi (0 : ℝ), t ^ 2 / (Real.exp t + 1) : ℝ)) : ℂ) := by
  have h1 : mellin fermiKernel 3
      = ∫ t in Ioi (0 : ℝ), ((t ^ 2 / (Real.exp t + 1) : ℝ) : ℂ) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [smul_eq_mul, show (3 : ℂ) - 1 = ((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
    unfold FermionWeightIntegral.fermiKernel
    push_cast
    ring
  rw [h1, integral_complex_ofReal]

/-! ## §6. The number-density integrals in closed form -/

/-- **THEOREM (Bose number integral).** `∫_{0}^{∞} t²/(eᵗ−1) dt = 2·ζ(3)`.
This is the analytic content of the photon number density
`n_γ = (2ζ(3)/π²)·T³`. -/
theorem bose_number_integral_value :
    (∫ t in Ioi (0 : ℝ), t ^ 2 / (Real.exp t - 1)) = 2 * zeta3 := by
  have h := mellin_bose3_value
  rw [mellin_bose3_eq_integral] at h
  exact Complex.ofReal_inj.mp h

/-- **THEOREM (Fermi number integral).** `∫_{0}^{∞} t²/(eᵗ+1) dt = (3/2)·ζ(3)`. -/
theorem fermi_number_integral_value :
    (∫ t in Ioi (0 : ℝ), t ^ 2 / (Real.exp t + 1)) = 3 / 2 * zeta3 := by
  have h := mellin_fermi3_value
  rw [mellin_fermi3_eq_integral] at h
  exact Complex.ofReal_inj.mp h

/-- **THEOREM (3/4 number-density fermion weight).** The Fermi–Dirac number
integral is exactly 3/4 of the Bose–Einstein one: `η(3)/ζ(3) = 1 − 2⁻² = 3/4`
(the companion of the 7/8 entropy weight). -/
theorem fermi_div_bose_number_integral :
    (∫ t in Ioi (0 : ℝ), t ^ 2 / (Real.exp t + 1))
      / (∫ t in Ioi (0 : ℝ), t ^ 2 / (Real.exp t - 1)) = 3 / 4 := by
  rw [bose_number_integral_value, fermi_number_integral_value]
  have hz : zeta3 ≠ 0 := zeta3_pos.ne'
  field_simp
  ring

/-! ## §7. Capstone: the density coefficients of `entropyPerPhoton` -/

/-- **THEOREM (photon number-density coefficient provenance).** The `2ζ(3)/π²`
coefficient of `n_γ = (2ζ(3)/π²)·T³` is `g_γ·(∫t²/(eᵗ−1))/(2π²)` with
`g_γ = 2`: the Bose number integral over the phase-space normalization. -/
theorem number_density_coeff_provenance :
    ((EntropyPerPhoton.gPhoton : ℚ) : ℝ)
        * (∫ t in Ioi (0 : ℝ), t ^ 2 / (Real.exp t - 1)) / (2 * π ^ 2)
      = 2 * zeta3 / π ^ 2 := by
  rw [bose_number_integral_value]
  unfold EntropyPerPhoton.gPhoton
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

/-- **THEOREM (entropy-density coefficient provenance).** The `2π²/45`
coefficient of `s = (2π²/45)·g*s·T³` is `(4/3)·(∫t³/(eᵗ−1))/(2π²)`: the
radiation relation `s = (4/3)ρ/T` applied to the Bose energy integral over
the phase-space normalization. -/
theorem entropy_density_coeff_provenance :
    4 / 3 * ((∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t - 1)) / (2 * π ^ 2))
      = 2 * π ^ 2 / 45 := by
  rw [FermionWeightIntegral.bose_integral_value]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **THEOREM (entropy per photon from the thermodynamic integrals).**
`entropyPerPhoton` is exactly the ratio built from the two derived integrals:
numerator = entropy-density coefficient `(4/3)·(∫t³/(eᵗ−1))/(2π²)` times
`g*s`; denominator = photon number-density coefficient
`g_γ·(∫t²/(eᵗ−1))/(2π²)`. Every analytic constant in the entropy-per-photon
chain is now THEOREM; the remaining MODEL content is the particle census and
the statistical-mechanics identifications. -/
theorem entropyPerPhoton_from_integrals :
    EntropyPerPhoton.entropyPerPhoton
      = (4 / 3 * ((∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t - 1)) / (2 * π ^ 2))
            * ((EntropyPerPhoton.gStarS : ℚ) : ℝ))
        / (((EntropyPerPhoton.gPhoton : ℚ) : ℝ)
            * (∫ t in Ioi (0 : ℝ), t ^ 2 / (Real.exp t - 1)) / (2 * π ^ 2)) := by
  rw [FermionWeightIntegral.bose_integral_value, bose_number_integral_value,
    EntropyPerPhoton.gStarS_eq]
  unfold EntropyPerPhoton.entropyPerPhoton EntropyPerPhoton.gPhoton
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hz : zeta3 ≠ 0 := zeta3_pos.ne'
  push_cast
  field_simp
  ring

end NumberDensityIntegral
end Cosmology
end IndisputableMonolith
