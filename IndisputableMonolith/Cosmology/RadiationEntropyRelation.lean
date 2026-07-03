import Mathlib
import IndisputableMonolith.Cosmology.FermionWeightIntegral
import IndisputableMonolith.Cosmology.NumberDensityIntegral

/-!
# The Radiation Entropy Relation s = (4/3)·ρ/T from the Entropy Functional

**Status: THEOREM (this module, 0 sorry).**

This module closes the next MODEL element in the η_B chain: the
statistical-mechanics identification `s = (4/3)·ρ/T` for a massless quantum
gas.  Up to now the entropy chain (`EntropyPerPhoton`, `NumberDensityIntegral`)
*used* the 4/3 factor as an assumed thermodynamic input.  Here it is **derived**
from the microscopic entropy functional of quantum statistics.

## What is proved

For the dimensionless radiation integrals (x = E/T):

* **Bose–Einstein** (f = 1/(eˣ−1), entropy integrand
  σ_B(x) = x²[(1+f)ln(1+f) − f ln f]):
  `∫₀^∞ σ_B = 4π⁴/45 = (4/3)·∫₀^∞ x³/(eˣ−1)`  (`bose_entropy_eq_four_thirds_energy`)

* **Fermi–Dirac** (f = 1/(eˣ+1), entropy integrand
  σ_F(x) = x²[−f ln f − (1−f)ln(1−f)]):
  `∫₀^∞ σ_F = 7π⁴/90 = (4/3)·∫₀^∞ x³/(eˣ+1)`  (`fermi_entropy_eq_four_thirds_energy`)

* **The 7/8 entropy weight**: `∫σ_F / ∫σ_B = 7/8`
  (`fermi_div_bose_entropy`) — the fermionic statistics factor now holds at
  the *entropy-functional* layer, not only at the energy layer.

* **The entropy coefficient**: `∫σ_B / (2π²) = 2π²/45`
  (`entropy_coeff_from_functional`) — the `2π²/45` prefactor of
  `s_γ = (2π²/45)·g·T³` emerges from the functional, with the 4/3 never
  assumed.

## Method

The pointwise identity (proved in `bose_entropy_pointwise` /
`fermi_entropy_pointwise`) splits each entropy integrand into the energy
kernel plus a logarithmic kernel:

* Bose:  σ_B(x) = x³/(eˣ−1) + x²·(−ln(1−e^{−x}))
* Fermi: σ_F(x) = x³/(eˣ+1) + x²·ln(1+e^{−x})

The logarithmic kernels expand by `Real.hasSum_pow_div_log_of_abs_lt_one`
(the Mercator series in e^{−x}), and their Mellin transforms at s = 3
evaluate via `hasSum_mellin` to Γ(3)·ζ(4) = π⁴/45 (Bose) and
Γ(3)·η(4) = 7π⁴/360 (Fermi).  Combined with the energy integrals π⁴/15 and
7π⁴/120 (`FermionWeightIntegral`), the totals are 4π⁴/45 and 7π⁴/90, which
are exactly 4/3 of the energy integrals.  Integrability of each piece is
extracted by contraposition from the nonvanishing of its computed value.

## What remains MODEL upstream

The phase-space normalization g/(2π²) (degeneracy count and ℏ=c=k_B=1
units) and the identification of the *physical* entropy density with the
ideal-gas entropy functional are definitional bridges; all functional and
numerical content of `s = (4/3)ρ/T` and of the 7/8 weight is THEOREM.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace RadiationEntropyRelation

open Real MeasureTheory Set

/-! ## §1. The logarithmic kernels and their Mercator expansions -/

/-- The Bose logarithmic kernel `−ln(1−e^{−t})`, complex-valued for the
Mellin machinery. -/
noncomputable def boseLogKernel (t : ℝ) : ℂ :=
  ((-Real.log (1 - Real.exp (-t)) : ℝ) : ℂ)

/-- The Fermi logarithmic kernel `ln(1+e^{−t})`, complex-valued for the
Mellin machinery. -/
noncomputable def fermiLogKernel (t : ℝ) : ℂ :=
  ((Real.log (1 + Real.exp (-t)) : ℝ) : ℂ)

/-- Mercator expansion `−ln(1−e^{−t}) = ∑_{n≥0} (e^{−t})^{n+1}/(n+1)` for `t > 0`. -/
lemma boseLog_series {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-t) ^ (n + 1) / ((n : ℝ) + 1))
      (-Real.log (1 - Real.exp (-t))) := by
  have habs : |Real.exp (-t)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  exact (Real.hasSum_pow_div_log_of_abs_lt_one habs).congr_fun
    fun n => by ring

/-- Mercator expansion `ln(1+e^{−t}) = ∑_{n≥0} (−1)ⁿ (e^{−t})^{n+1}/(n+1)`
for `t > 0`. -/
lemma fermiLog_series {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * Real.exp (-t) ^ (n + 1) / ((n : ℝ) + 1))
      (Real.log (1 + Real.exp (-t))) := by
  have habs : |(-Real.exp (-t))| < 1 := by
    rw [abs_neg, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one habs).neg
  have hval : -(-Real.log (1 - -Real.exp (-t))) = Real.log (1 + Real.exp (-t)) := by
    rw [neg_neg, sub_neg_eq_add]
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  rw [neg_pow, pow_succ]
  ring

/-! ## §2. Summability of the weighted coefficient norms -/

/-- Summability of `‖1/(n+1)‖ / (n+1)³`, as required by `hasSum_mellin`
for the Bose logarithmic kernel. -/
lemma summable_norm_boseLog :
    Summable (fun n : ℕ =>
      ‖((1 / ((n : ℝ) + 1) : ℝ) : ℂ)‖ / ((n : ℝ) + 1) ^ ((3 : ℂ)).re) := by
  refine FermionWeightIntegral.summable_shift_rpow.congr fun n => ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : ‖((1 / ((n : ℝ) + 1) : ℝ) : ℂ)‖ = 1 / ((n : ℝ) + 1) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  rw [h1, show ((3 : ℂ)).re = (3 : ℝ) by norm_num,
    show (4 : ℝ) = (3 : ℝ) + 1 by norm_num, Real.rpow_add hpos, Real.rpow_one,
    div_div, mul_comm (((n : ℝ) + 1) ^ (3 : ℝ)) ((n : ℝ) + 1)]

/-- Summability of `‖(−1)ⁿ/(n+1)‖ / (n+1)³`, as required by `hasSum_mellin`
for the Fermi logarithmic kernel. -/
lemma summable_norm_fermiLog :
    Summable (fun n : ℕ =>
      ‖(((-1 : ℝ) ^ n / ((n : ℝ) + 1) : ℝ) : ℂ)‖ / ((n : ℝ) + 1) ^ ((3 : ℂ)).re) := by
  refine FermionWeightIntegral.summable_shift_rpow.congr fun n => ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : ‖(((-1 : ℝ) ^ n / ((n : ℝ) + 1) : ℝ) : ℂ)‖ = 1 / ((n : ℝ) + 1) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one,
      one_pow, abs_of_pos hpos]
  rw [h1, show ((3 : ℂ)).re = (3 : ℝ) by norm_num,
    show (4 : ℝ) = (3 : ℝ) + 1 by norm_num, Real.rpow_add hpos, Real.rpow_one,
    div_div, mul_comm (((n : ℝ) + 1) ^ (3 : ℝ)) ((n : ℝ) + 1)]

/-! ## §3. Mellin transforms of the logarithmic kernels at s = 3 -/

/-- Mellin/Dirichlet identity for the Bose logarithmic kernel at `s = 3`. -/
lemma hasSum_mellin_boseLog :
    HasSum (fun n : ℕ =>
        Complex.Gamma 3 * ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
          / (((n : ℝ) + 1 : ℝ) : ℂ) ^ (3 : ℂ))
      (mellin boseLogKernel 3) := by
  refine hasSum_mellin (a := fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))
    (p := fun n : ℕ => (n : ℝ) + 1) (F := boseLogKernel) (s := 3)
    (fun i => Or.inr (by positivity)) (by norm_num) (fun t ht => ?_) ?_
  · have ht' : (0 : ℝ) < t := ht
    have hC : HasSum
        (fun n : ℕ => ((Real.exp (-t) ^ (n + 1) / ((n : ℝ) + 1) : ℝ) : ℂ))
        (boseLogKernel t) := Complex.hasSum_ofReal.mpr (boseLog_series ht')
    refine hC.congr_fun fun n => ?_
    have hexp : Real.exp (-((n : ℝ) + 1) * t) = Real.exp (-t) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  · exact summable_norm_boseLog

/-- Mellin/Dirichlet identity for the Fermi logarithmic kernel at `s = 3`. -/
lemma hasSum_mellin_fermiLog :
    HasSum (fun n : ℕ =>
        Complex.Gamma 3 * (((-1 : ℝ) ^ n / ((n : ℝ) + 1) : ℝ) : ℂ)
          / (((n : ℝ) + 1 : ℝ) : ℂ) ^ (3 : ℂ))
      (mellin fermiLogKernel 3) := by
  refine hasSum_mellin (a := fun n : ℕ => (((-1 : ℝ) ^ n / ((n : ℝ) + 1) : ℝ) : ℂ))
    (p := fun n : ℕ => (n : ℝ) + 1) (F := fermiLogKernel) (s := 3)
    (fun i => Or.inr (by positivity)) (by norm_num) (fun t ht => ?_) ?_
  · have ht' : (0 : ℝ) < t := ht
    have hC : HasSum
        (fun n : ℕ =>
          (((-1 : ℝ) ^ n * Real.exp (-t) ^ (n + 1) / ((n : ℝ) + 1) : ℝ) : ℂ))
        (fermiLogKernel t) := Complex.hasSum_ofReal.mpr (fermiLog_series ht')
    refine hC.congr_fun fun n => ?_
    have hexp : Real.exp (-((n : ℝ) + 1) * t) = Real.exp (-t) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  · exact summable_norm_fermiLog

/-! ## §4. Closed-form values of the logarithmic Mellin transforms -/

/-- `mellin (−ln(1−e^{−t})) 3 = Γ(3)·ζ(4) = π⁴/45`. -/
lemma mellin_boseLog_value : mellin boseLogKernel 3 = ((π ^ 4 / 45 : ℝ) : ℂ) := by
  refine hasSum_mellin_boseLog.unique ?_
  have hre : HasSum (fun n : ℕ => (2 : ℝ) * ((1 : ℝ) / ((n : ℝ) + 1) ^ 4))
      (π ^ 4 / 45) := by
    have h := FermionWeightIntegral.hasSum_zeta_shift.mul_left 2
    convert h using 1
    ring
  have hC := Complex.hasSum_ofReal.mpr hre
  refine hC.congr_fun fun n => ?_
  rw [NumberDensityIntegral.gamma_three, NumberDensityIntegral.cpow_shift3 n]
  have hne : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

/-- `mellin (ln(1+e^{−t})) 3 = Γ(3)·η(4) = 7π⁴/360`. -/
lemma mellin_fermiLog_value :
    mellin fermiLogKernel 3 = ((7 * π ^ 4 / 360 : ℝ) : ℂ) := by
  refine hasSum_mellin_fermiLog.unique ?_
  have hre : HasSum (fun n : ℕ => (2 : ℝ) * ((-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 4))
      (7 * π ^ 4 / 360) := by
    have h := FermionWeightIntegral.hasSum_eta_shift.mul_left 2
    convert h using 1
    ring
  have hC := Complex.hasSum_ofReal.mpr hre
  refine hC.congr_fun fun n => ?_
  rw [NumberDensityIntegral.gamma_three, NumberDensityIntegral.cpow_shift3 n]
  have hne : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

/-! ## §5. The Mellin transforms are the logarithmic integrals -/

/-- `mellin boseLogKernel 3` is the (complexified) Bose logarithmic integral. -/
lemma mellin_boseLog_eq_integral :
    mellin boseLogKernel 3
      = (((∫ t in Ioi (0 : ℝ), t ^ 2 * (-Real.log (1 - Real.exp (-t))) : ℝ)) : ℂ) := by
  have h1 : mellin boseLogKernel 3
      = ∫ t in Ioi (0 : ℝ), ((t ^ 2 * (-Real.log (1 - Real.exp (-t))) : ℝ) : ℂ) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [smul_eq_mul, show (3 : ℂ) - 1 = ((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
    unfold boseLogKernel
    push_cast
    ring
  rw [h1, integral_complex_ofReal]

/-- `mellin fermiLogKernel 3` is the (complexified) Fermi logarithmic integral. -/
lemma mellin_fermiLog_eq_integral :
    mellin fermiLogKernel 3
      = (((∫ t in Ioi (0 : ℝ), t ^ 2 * Real.log (1 + Real.exp (-t)) : ℝ)) : ℂ) := by
  have h1 : mellin fermiLogKernel 3
      = ∫ t in Ioi (0 : ℝ), ((t ^ 2 * Real.log (1 + Real.exp (-t)) : ℝ) : ℂ) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [smul_eq_mul, show (3 : ℂ) - 1 = ((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
    unfold fermiLogKernel
    push_cast
    ring
  rw [h1, integral_complex_ofReal]

/-! ## §6. The logarithmic integrals in closed form -/

/-- **THEOREM.** `∫₀^∞ t²·(−ln(1−e^{−t})) dt = π⁴/45`. -/
theorem boseLog_integral_value :
    (∫ t in Ioi (0 : ℝ), t ^ 2 * (-Real.log (1 - Real.exp (-t)))) = π ^ 4 / 45 := by
  have h := mellin_boseLog_value
  rw [mellin_boseLog_eq_integral] at h
  exact Complex.ofReal_inj.mp h

/-- **THEOREM.** `∫₀^∞ t²·ln(1+e^{−t}) dt = 7π⁴/360`. -/
theorem fermiLog_integral_value :
    (∫ t in Ioi (0 : ℝ), t ^ 2 * Real.log (1 + Real.exp (-t))) = 7 * π ^ 4 / 360 := by
  have h := mellin_fermiLog_value
  rw [mellin_fermiLog_eq_integral] at h
  exact Complex.ofReal_inj.mp h

/-! ## §7. The entropy integrands and their pointwise decomposition -/

/-- The Bose–Einstein entropy integrand
`σ_B(t) = t²[(1+f)ln(1+f) − f ln f]` with `f = 1/(eᵗ−1)`. -/
noncomputable def boseEntropyIntegrand (t : ℝ) : ℝ :=
  t ^ 2 * ((1 + 1 / (Real.exp t - 1)) * Real.log (1 + 1 / (Real.exp t - 1))
    - (1 / (Real.exp t - 1)) * Real.log (1 / (Real.exp t - 1)))

/-- The Fermi–Dirac entropy integrand
`σ_F(t) = t²[−f ln f − (1−f)ln(1−f)]` with `f = 1/(eᵗ+1)`. -/
noncomputable def fermiEntropyIntegrand (t : ℝ) : ℝ :=
  t ^ 2 * (-(1 / (Real.exp t + 1)) * Real.log (1 / (Real.exp t + 1))
    - (1 - 1 / (Real.exp t + 1)) * Real.log (1 - 1 / (Real.exp t + 1)))

/-- **Pointwise decomposition (Bose).** For `t > 0`,
`σ_B(t) = t³/(eᵗ−1) + t²·(−ln(1−e^{−t}))`: the entropy integrand is the
energy kernel plus the logarithmic kernel. -/
lemma bose_entropy_pointwise {t : ℝ} (ht : 0 < t) :
    boseEntropyIntegrand t
      = t ^ 3 / (Real.exp t - 1) + t ^ 2 * (-Real.log (1 - Real.exp (-t))) := by
  have hE1 : (1 : ℝ) < Real.exp t := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr ht
  have hEpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hne : Real.exp t - 1 ≠ 0 := by linarith
  have hlog1f : Real.log (1 + 1 / (Real.exp t - 1))
      = t - Real.log (Real.exp t - 1) := by
    have hval : (1 : ℝ) + 1 / (Real.exp t - 1) = Real.exp t / (Real.exp t - 1) := by
      field_simp
      ring
    rw [hval, Real.log_div hEpos.ne' hne, Real.log_exp]
  have hlogf : Real.log (1 / (Real.exp t - 1)) = -Real.log (Real.exp t - 1) := by
    rw [one_div, Real.log_inv]
  have hlogm : Real.log (1 - Real.exp (-t)) = Real.log (Real.exp t - 1) - t := by
    have hval : (1 : ℝ) - Real.exp (-t) = (Real.exp t - 1) / Real.exp t := by
      rw [Real.exp_neg]
      field_simp
    rw [hval, Real.log_div hne hEpos.ne', Real.log_exp]
  unfold boseEntropyIntegrand
  rw [hlog1f, hlogf, hlogm]
  ring

/-- **Pointwise decomposition (Fermi).** For `t > 0`,
`σ_F(t) = t³/(eᵗ+1) + t²·ln(1+e^{−t})`: the entropy integrand is the
energy kernel plus the logarithmic kernel. -/
lemma fermi_entropy_pointwise {t : ℝ} (_ht : 0 < t) :
    fermiEntropyIntegrand t
      = t ^ 3 / (Real.exp t + 1) + t ^ 2 * Real.log (1 + Real.exp (-t)) := by
  have hEpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hne : Real.exp t + 1 ≠ 0 := by positivity
  have hlogf : Real.log (1 / (Real.exp t + 1)) = -Real.log (Real.exp t + 1) := by
    rw [one_div, Real.log_inv]
  have hlog1f : Real.log (1 - 1 / (Real.exp t + 1))
      = t - Real.log (Real.exp t + 1) := by
    have hval : (1 : ℝ) - 1 / (Real.exp t + 1) = Real.exp t / (Real.exp t + 1) := by
      field_simp
      ring
    rw [hval, Real.log_div hEpos.ne' hne, Real.log_exp]
  have hlogp : Real.log (1 + Real.exp (-t)) = Real.log (Real.exp t + 1) - t := by
    have hval : (1 : ℝ) + Real.exp (-t) = (Real.exp t + 1) / Real.exp t := by
      rw [Real.exp_neg]
      field_simp
    rw [hval, Real.log_div hne hEpos.ne', Real.log_exp]
  unfold fermiEntropyIntegrand
  rw [hlogf, hlog1f, hlogp]
  ring

/-! ## §8. Integrability of the pieces (by contraposition from the values) -/

/-- The Bose energy kernel is integrable on `(0,∞)` (its integral is `π⁴/15 ≠ 0`). -/
lemma integrableOn_bose_energy :
    IntegrableOn (fun t : ℝ => t ^ 3 / (Real.exp t - 1)) (Ioi (0 : ℝ)) := by
  by_contra hcon
  have h0 : (∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t - 1)) = 0 :=
    integral_undef hcon
  rw [FermionWeightIntegral.bose_integral_value] at h0
  have hpos : (0 : ℝ) < π ^ 4 / 15 := by positivity
  linarith

/-- The Bose logarithmic kernel is integrable on `(0,∞)`
(its integral is `π⁴/45 ≠ 0`). -/
lemma integrableOn_boseLog :
    IntegrableOn (fun t : ℝ => t ^ 2 * (-Real.log (1 - Real.exp (-t))))
      (Ioi (0 : ℝ)) := by
  by_contra hcon
  have h0 : (∫ t in Ioi (0 : ℝ), t ^ 2 * (-Real.log (1 - Real.exp (-t)))) = 0 :=
    integral_undef hcon
  rw [boseLog_integral_value] at h0
  have hpos : (0 : ℝ) < π ^ 4 / 45 := by positivity
  linarith

/-- The Fermi energy kernel is integrable on `(0,∞)`
(its integral is `7π⁴/120 ≠ 0`). -/
lemma integrableOn_fermi_energy :
    IntegrableOn (fun t : ℝ => t ^ 3 / (Real.exp t + 1)) (Ioi (0 : ℝ)) := by
  by_contra hcon
  have h0 : (∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t + 1)) = 0 :=
    integral_undef hcon
  rw [FermionWeightIntegral.fermi_integral_value] at h0
  have hpos : (0 : ℝ) < 7 * π ^ 4 / 120 := by positivity
  linarith

/-- The Fermi logarithmic kernel is integrable on `(0,∞)`
(its integral is `7π⁴/360 ≠ 0`). -/
lemma integrableOn_fermiLog :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.log (1 + Real.exp (-t)))
      (Ioi (0 : ℝ)) := by
  by_contra hcon
  have h0 : (∫ t in Ioi (0 : ℝ), t ^ 2 * Real.log (1 + Real.exp (-t))) = 0 :=
    integral_undef hcon
  rw [fermiLog_integral_value] at h0
  have hpos : (0 : ℝ) < 7 * π ^ 4 / 360 := by positivity
  linarith

/-! ## §9. The entropy integrals in closed form -/

/-- **THEOREM (Bose entropy integral).**
`∫₀^∞ t²[(1+f)ln(1+f) − f ln f] dt = 4π⁴/45` with `f = 1/(eᵗ−1)`. -/
theorem bose_entropy_integral_value :
    (∫ t in Ioi (0 : ℝ), boseEntropyIntegrand t) = 4 * π ^ 4 / 45 := by
  have hsplit : (∫ t in Ioi (0 : ℝ), boseEntropyIntegrand t)
      = ∫ t in Ioi (0 : ℝ),
          (t ^ 3 / (Real.exp t - 1) + t ^ 2 * (-Real.log (1 - Real.exp (-t)))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    exact bose_entropy_pointwise ht
  rw [hsplit, integral_add integrableOn_bose_energy integrableOn_boseLog,
    FermionWeightIntegral.bose_integral_value, boseLog_integral_value]
  ring

/-- **THEOREM (Fermi entropy integral).**
`∫₀^∞ t²[−f ln f − (1−f)ln(1−f)] dt = 7π⁴/90` with `f = 1/(eᵗ+1)`. -/
theorem fermi_entropy_integral_value :
    (∫ t in Ioi (0 : ℝ), fermiEntropyIntegrand t) = 7 * π ^ 4 / 90 := by
  have hsplit : (∫ t in Ioi (0 : ℝ), fermiEntropyIntegrand t)
      = ∫ t in Ioi (0 : ℝ),
          (t ^ 3 / (Real.exp t + 1) + t ^ 2 * Real.log (1 + Real.exp (-t))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    exact fermi_entropy_pointwise ht
  rw [hsplit, integral_add integrableOn_fermi_energy integrableOn_fermiLog,
    FermionWeightIntegral.fermi_integral_value, fermiLog_integral_value]
  ring

/-! ## §10. Capstones: s = (4/3)ρ/T, the 7/8 entropy weight, and 2π²/45 -/

/-- **THEOREM (s = (4/3)ρ/T, Bose).** The Bose entropy integral is exactly
`4/3` of the Bose energy integral.  This is the dimensionless content of the
thermodynamic relation `s = (4/3)·ρ/T` for a massless boson gas, derived from
the microscopic entropy functional (never assumed). -/
theorem bose_entropy_eq_four_thirds_energy :
    (∫ t in Ioi (0 : ℝ), boseEntropyIntegrand t)
      = 4 / 3 * ∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t - 1) := by
  rw [bose_entropy_integral_value, FermionWeightIntegral.bose_integral_value]
  ring

/-- **THEOREM (s = (4/3)ρ/T, Fermi).** The Fermi entropy integral is exactly
`4/3` of the Fermi energy integral: the same 4/3 law holds for a massless
fermion gas. -/
theorem fermi_entropy_eq_four_thirds_energy :
    (∫ t in Ioi (0 : ℝ), fermiEntropyIntegrand t)
      = 4 / 3 * ∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t + 1) := by
  rw [fermi_entropy_integral_value, FermionWeightIntegral.fermi_integral_value]
  ring

/-- **THEOREM (7/8 at the entropy layer).** The Fermi entropy integral is
exactly `7/8` of the Bose one: the fermionic statistics weight of
`EntropyPerPhoton.fermionWeight` holds directly for entropy, not only for
energy. -/
theorem fermi_div_bose_entropy :
    (∫ t in Ioi (0 : ℝ), fermiEntropyIntegrand t)
      / (∫ t in Ioi (0 : ℝ), boseEntropyIntegrand t) = 7 / 8 := by
  rw [bose_entropy_integral_value, fermi_entropy_integral_value]
  rw [div_eq_iff (by positivity)]
  ring

/-- **THEOREM (entropy weight provenance, entropy layer).**
`∫σ_F = fermionWeight · ∫σ_B` with the `7/8` MODEL constant of
`EntropyPerPhoton.fermionWeight`. -/
theorem fermi_entropy_eq_weight_mul_bose :
    (∫ t in Ioi (0 : ℝ), fermiEntropyIntegrand t)
      = ((EntropyPerPhoton.fermionWeight : ℚ) : ℝ)
          * ∫ t in Ioi (0 : ℝ), boseEntropyIntegrand t := by
  rw [bose_entropy_integral_value, fermi_entropy_integral_value]
  unfold EntropyPerPhoton.fermionWeight
  push_cast
  ring

/-- **THEOREM (the 2π²/45 entropy coefficient from the functional).**
`s_γ = (g/2π²)·T³·∫σ_B = (2π²/45)·g·T³`: dividing the derived entropy
integral by the phase-space normalization `2π²` yields exactly the `2π²/45`
prefactor of the photon entropy density, with the `4/3` factor never
assumed. -/
theorem entropy_coeff_from_functional :
    (∫ t in Ioi (0 : ℝ), boseEntropyIntegrand t) / (2 * π ^ 2) = 2 * π ^ 2 / 45 := by
  rw [bose_entropy_integral_value]
  rw [div_eq_iff (by positivity)]
  ring

end RadiationEntropyRelation
end Cosmology
end IndisputableMonolith
