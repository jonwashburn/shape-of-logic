import Mathlib
import IndisputableMonolith.Cosmology.EntropyPerPhoton
import IndisputableMonolith.Cosmology.FermionWeight

/-!
# The 7/8 Fermion Weight at the Integral (Thermodynamic) Layer

**Status: THEOREM (integral layer).**

`Cosmology.FermionWeight` derived the series identity `η(4) = (7/8)·ζ(4)`.
This module closes the remaining mathematical gap between that series identity
and the *thermodynamic* statement actually used in the entropy bookkeeping:
the Fermi–Dirac energy integral is 7/8 of the Bose–Einstein one,

  `∫_{0}^{∞} t³/(eᵗ+1) dt = (7/8) · ∫_{0}^{∞} t³/(eᵗ−1) dt`,

with both sides evaluated in closed form:

  Bose:  `∫ t³/(eᵗ−1) = Γ(4)·ζ(4) = 6·π⁴/90 = π⁴/15`
  Fermi: `∫ t³/(eᵗ+1) = Γ(4)·η(4) = 6·(7/8)·π⁴/90 = 7π⁴/120`.

## Derivation

Both integrals are Mellin transforms at `s = 4` of geometric series in `e^{−t}`:

  `1/(eᵗ−1) = ∑_{n≥0} e^{−(n+1)t}`,  `1/(eᵗ+1) = ∑_{n≥0} (−1)ⁿ e^{−(n+1)t}`  (t > 0),

and Mathlib's `hasSum_mellin` ("Mellin transform of a power series in exp(−t)
is a Dirichlet series") gives

  `mellin F s = ∑_n Γ(s)·aₙ/(n+1)^s`

for `F t = ∑ aₙ e^{−(n+1)t}`. At `s = 4` with `Γ(4) = 3! = 6`, the Dirichlet
sides are the shifted `ζ(4)` and `η(4)` sums evaluated in
`Cosmology.FermionWeight`. The Mellin integrand `t³·F(t)` is exactly the
thermodynamic integrand, so uniqueness of unconditional sums closes both
integrals, and the 7/8 ratio follows.

With this module the *entire mathematical content* of
`EntropyPerPhoton.fermionWeight = 7/8` is THEOREM: the only MODEL content left
in the entropy-per-photon chain is the physics bookkeeping (which species are
relativistic, i.e. the `g*` census), not the 7/8 statistics factor itself.
All theorems here are axiom-clean (Lean's base three only).
-/

namespace IndisputableMonolith
namespace Cosmology
namespace FermionWeightIntegral

open Real MeasureTheory Set

/-- The Bose–Einstein kernel `1/(eᵗ−1)`, complex-valued for the Mellin machinery. -/
noncomputable def boseKernel (t : ℝ) : ℂ := ((1 / (Real.exp t - 1) : ℝ) : ℂ)

/-- The Fermi–Dirac kernel `1/(eᵗ+1)`, complex-valued for the Mellin machinery. -/
noncomputable def fermiKernel (t : ℝ) : ℂ := ((1 / (Real.exp t + 1) : ℝ) : ℂ)

/-! ## §1. Geometric-series expansions of the kernels (t > 0) -/

/-- `1/(eᵗ−1) = ∑_{n≥0} (e^{−t})^{n+1}` for `t > 0`. -/
lemma bose_series {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-t) ^ (n + 1)) (1 / (Real.exp t - 1)) := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hr1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-t))
  have hval : Real.exp (-t) * (1 - Real.exp (-t))⁻¹ = 1 / (Real.exp t - 1) := by
    have h1 : (1 : ℝ) < Real.exp t := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr ht
    have hne : Real.exp t - 1 ≠ 0 := by linarith
    have hne2 : (1 : ℝ) - Real.exp (-t) ≠ 0 := by linarith
    have hepos : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
    rw [Real.exp_neg]
    rw [Real.exp_neg] at hne2
    field_simp
  exact (hval ▸ h).congr_fun fun n => by rw [pow_succ]; ring

/-- `1/(eᵗ+1) = ∑_{n≥0} (−1)ⁿ (e^{−t})^{n+1}` for `t > 0`. -/
lemma fermi_series {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * Real.exp (-t) ^ (n + 1))
      (1 / (Real.exp t + 1)) := by
  have hr0 : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have hr1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hnorm : ‖-Real.exp (-t)‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have h := (hasSum_geometric_of_norm_lt_one hnorm).mul_left (Real.exp (-t))
  have hval : Real.exp (-t) * (1 - -Real.exp (-t))⁻¹ = 1 / (Real.exp t + 1) := by
    have hepos : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
    have hne : Real.exp t + 1 ≠ 0 := by positivity
    have hne2 : (1 : ℝ) - -Real.exp (-t) ≠ 0 := by
      rw [sub_neg_eq_add]
      positivity
    rw [sub_neg_eq_add, Real.exp_neg]
    rw [sub_neg_eq_add, Real.exp_neg] at hne2
    field_simp
  exact (hval ▸ h).congr_fun fun n => by rw [neg_pow, pow_succ]; ring

/-! ## §2. Shifted Dirichlet sums (from `Cosmology.FermionWeight`) -/

/-- `∑_{n≥0} 1/(n+1)⁴ = ζ(4) = π⁴/90` (index-shifted `hasSum_zeta_four`). -/
lemma hasSum_zeta_shift :
    HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 4) (π ^ 4 / 90) := by
  have hbase : HasSum (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 4)
      (π ^ 4 / 90 + ∑ i ∈ Finset.range 1, (1 : ℝ) / (i : ℝ) ^ 4) := by
    simpa using hasSum_zeta_four
  have h := (hasSum_nat_add_iff
    (f := fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 4) 1).mpr hbase
  exact h.congr_fun fun n => by push_cast; ring

/-- `∑_{n≥0} (−1)ⁿ/(n+1)⁴ = η(4) = (7/8)·(π⁴/90)` (index-shifted
`FermionWeight.hasSum_eta_four`). -/
lemma hasSum_eta_shift :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 4)
      (7 / 8 * (π ^ 4 / 90)) := by
  have hbase : HasSum (fun m : ℕ => (-1 : ℝ) ^ (m + 1) / (m : ℝ) ^ 4)
      (7 / 8 * (π ^ 4 / 90)
        + ∑ i ∈ Finset.range 1, (-1 : ℝ) ^ (i + 1) / (i : ℝ) ^ 4) := by
    simpa using FermionWeight.hasSum_eta_four
  have h := (hasSum_nat_add_iff
    (f := fun m : ℕ => (-1 : ℝ) ^ (m + 1) / (m : ℝ) ^ 4) 1).mpr hbase
  exact h.congr_fun fun n => by push_cast [pow_succ]; ring

/-- Summability of the shifted `p`-series with real (rpow) exponent, as
required by `hasSum_mellin`. -/
lemma summable_shift_rpow :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (4 : ℝ)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (4 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have h2 := (summable_nat_add_iff
    (f := fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ (4 : ℝ)) 1).mpr h
  exact h2.congr fun n => by push_cast; ring_nf

/-! ## §3. Mellin transforms at s = 4 -/

/-- Mellin/Dirichlet identity for the Bose kernel at `s = 4`. -/
lemma hasSum_mellin_bose :
    HasSum (fun n : ℕ =>
        Complex.Gamma 4 * (1 : ℂ) / (((n : ℝ) + 1 : ℝ) : ℂ) ^ (4 : ℂ))
      (mellin boseKernel 4) := by
  refine hasSum_mellin (a := fun _ : ℕ => (1 : ℂ)) (p := fun n : ℕ => (n : ℝ) + 1)
    (F := boseKernel) (s := 4)
    (fun i => Or.inr (by positivity)) (by norm_num) (fun t ht => ?_) ?_
  · -- geometric series, cast to ℂ
    have ht' : (0 : ℝ) < t := ht
    have hC : HasSum (fun n : ℕ => ((Real.exp (-t) ^ (n + 1) : ℝ) : ℂ))
        (boseKernel t) := Complex.hasSum_ofReal.mpr (bose_series ht')
    refine hC.congr_fun fun n => ?_
    have hexp : Real.exp (-((n : ℝ) + 1) * t) = Real.exp (-t) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [one_mul, hexp]
  · simpa using summable_shift_rpow

/-- Mellin/Dirichlet identity for the Fermi kernel at `s = 4`. -/
lemma hasSum_mellin_fermi :
    HasSum (fun n : ℕ =>
        Complex.Gamma 4 * (-1 : ℂ) ^ n / (((n : ℝ) + 1 : ℝ) : ℂ) ^ (4 : ℂ))
      (mellin fermiKernel 4) := by
  refine hasSum_mellin (a := fun n : ℕ => (-1 : ℂ) ^ n)
    (p := fun n : ℕ => (n : ℝ) + 1) (F := fermiKernel) (s := 4)
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
  · simpa using summable_shift_rpow

/-! ## §4. Closed-form values -/

/-- `Γ(4) = 3! = 6`. -/
lemma gamma_four : Complex.Gamma 4 = 6 := by
  have h := Complex.Gamma_ofNat_eq_factorial 3
  norm_num [Nat.factorial] at h
  convert h using 2
  norm_num

/-- `(n+1)^(4:ℂ)` (cpow of a positive real) is the real fourth power, cast. -/
lemma cpow_shift (n : ℕ) :
    ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ (4 : ℂ) = ((((n : ℝ) + 1) ^ 4 : ℝ) : ℂ) := by
  rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  push_cast
  ring

/-- `mellin (1/(eᵗ−1)) 4 = π⁴/15` (i.e. `Γ(4)·ζ(4)`). -/
lemma mellin_bose_value : mellin boseKernel 4 = ((π ^ 4 / 15 : ℝ) : ℂ) := by
  refine hasSum_mellin_bose.unique ?_
  have hre : HasSum (fun n : ℕ => (6 : ℝ) * ((1 : ℝ) / ((n : ℝ) + 1) ^ 4))
      (π ^ 4 / 15) := by
    have h := hasSum_zeta_shift.mul_left 6
    convert h using 1
    ring
  have hC := Complex.hasSum_ofReal.mpr hre
  refine hC.congr_fun fun n => ?_
  rw [gamma_four, cpow_shift n]
  push_cast
  ring

/-- `mellin (1/(eᵗ+1)) 4 = 7π⁴/120` (i.e. `Γ(4)·η(4)`). -/
lemma mellin_fermi_value : mellin fermiKernel 4 = ((7 * π ^ 4 / 120 : ℝ) : ℂ) := by
  refine hasSum_mellin_fermi.unique ?_
  have hre : HasSum (fun n : ℕ => (6 : ℝ) * ((-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 4))
      (7 * π ^ 4 / 120) := by
    have h := hasSum_eta_shift.mul_left 6
    convert h using 1
    ring
  have hC := Complex.hasSum_ofReal.mpr hre
  refine hC.congr_fun fun n => ?_
  rw [gamma_four, cpow_shift n]
  push_cast
  ring

/-! ## §5. The Mellin transforms are the thermodynamic integrals -/

/-- `mellin boseKernel 4` is the (complexified) Bose–Einstein integral. -/
lemma mellin_bose_eq_integral :
    mellin boseKernel 4
      = (((∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t - 1) : ℝ)) : ℂ) := by
  have h1 : mellin boseKernel 4
      = ∫ t in Ioi (0 : ℝ), ((t ^ 3 / (Real.exp t - 1) : ℝ) : ℂ) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [smul_eq_mul, show (4 : ℂ) - 1 = ((3 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
    unfold boseKernel
    push_cast
    ring
  rw [h1, integral_complex_ofReal]

/-- `mellin fermiKernel 4` is the (complexified) Fermi–Dirac integral. -/
lemma mellin_fermi_eq_integral :
    mellin fermiKernel 4
      = (((∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t + 1) : ℝ)) : ℂ) := by
  have h1 : mellin fermiKernel 4
      = ∫ t in Ioi (0 : ℝ), ((t ^ 3 / (Real.exp t + 1) : ℝ) : ℂ) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [smul_eq_mul, show (4 : ℂ) - 1 = ((3 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
    unfold fermiKernel
    push_cast
    ring
  rw [h1, integral_complex_ofReal]

/-! ## §6. The thermodynamic integrals in closed form -/

/-- **THEOREM (Bose–Einstein integral).** `∫_{0}^{∞} t³/(eᵗ−1) dt = π⁴/15`. -/
theorem bose_integral_value :
    (∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t - 1)) = π ^ 4 / 15 := by
  have h := mellin_bose_value
  rw [mellin_bose_eq_integral] at h
  exact Complex.ofReal_inj.mp h

/-- **THEOREM (Fermi–Dirac integral).** `∫_{0}^{∞} t³/(eᵗ+1) dt = 7π⁴/120`. -/
theorem fermi_integral_value :
    (∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t + 1)) = 7 * π ^ 4 / 120 := by
  have h := mellin_fermi_value
  rw [mellin_fermi_eq_integral] at h
  exact Complex.ofReal_inj.mp h

/-! ## §7. Capstone: the 7/8 weight is the integral ratio -/

/-- **THEOREM (7/8 at the thermodynamic layer).** The Fermi–Dirac energy
integral is exactly 7/8 of the Bose–Einstein one. -/
theorem fermi_div_bose_integral :
    (∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t + 1))
      / (∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t - 1)) = 7 / 8 := by
  rw [bose_integral_value, fermi_integral_value]
  rw [div_eq_iff (by positivity)]
  ring

/-- **THEOREM (fermion weight provenance, integral layer).** The `7/8` MODEL
constant of `EntropyPerPhoton.fermionWeight` is the ratio of the actual
thermodynamic integrals: `∫ t³/(eᵗ+1) = fermionWeight · ∫ t³/(eᵗ−1)`.
Together with `FermionWeight.fermionWeight_eq_eta_zeta_ratio` (series layer)
this makes the full mathematical content of the 7/8 factor THEOREM; the
remaining MODEL content of the entropy chain is the relativistic-species
census (`g*`), not the statistics factor. -/
theorem fermi_integral_eq_weight_mul_bose :
    (∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t + 1))
      = ((EntropyPerPhoton.fermionWeight : ℚ) : ℝ)
          * ∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t - 1) := by
  rw [bose_integral_value, fermi_integral_value]
  unfold EntropyPerPhoton.fermionWeight
  push_cast
  ring

end FermionWeightIntegral
end Cosmology
end IndisputableMonolith
