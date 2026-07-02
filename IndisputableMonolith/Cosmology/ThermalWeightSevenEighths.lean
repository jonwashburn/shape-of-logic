import Mathlib
import IndisputableMonolith.Cosmology.GStarDerivation

/-!
# The 7/8 thermal weight is a THEOREM, not a convention

STATUS: THEOREM (axiom-clean; Mathlib base axioms only).

The fermionic weight `7/8` appearing in `g_⋆ = g_b + (7/8) g_f` is the ratio
of the Fermi-Dirac to the Bose-Einstein energy-density integrals:

  ∫₀^∞ t³/(eᵗ+1) dt  /  ∫₀^∞ t³/(eᵗ−1) dt  =  η(4)/ζ(4)  =  7/8.

Both integrals are Mellin transforms at `s = 4`:

  mellin (1/(eᵗ−1)) 4 = Γ(4)·ζ(4) = 6 · π⁴/90,
  mellin (1/(eᵗ+1)) 4 = Γ(4)·η(4) = 6 · (7/8) · π⁴/90,

where the Dirichlet eta value `η(4) = (7/8)·ζ(4)` follows from the even/odd
split of the alternating series.  This module proves the whole chain:

* `hasSum_eta_four`      : `Σ (−1)^(n+1)/n⁴ = (7/8)(π⁴/90)`  (analytic core)
* `mellin_boseKernel_eq` : `∫₀^∞ t³/(eᵗ−1) dt = 6·π⁴/90`
* `mellin_fermiKernel_eq`: `∫₀^∞ t³/(eᵗ+1) dt = (7/8)·6·π⁴/90`
* `fermi_bose_ratio`     : the ratio is exactly `7/8`
* `fermion_boltzmann_forced` : `GStarDerivation.fermion_boltzmann` equals
  that ratio, so the `def := 7/8` is a computed consequence of quantum
  statistics, not a hand-entered convention.

WHAT REMAINS PHYSICS INPUT: *which* species gets the `+1` (Fermi-Dirac)
denominator versus the `−1` (Bose-Einstein) one.  That sign is the exchange
statistics sign, which RS forces via the 8-tick phase
(`Foundation.EightTick.spin_statistics_key`: half-integer spin ↔ phase `−1`
at tick 4).  Given the sign, the 7/8 is pure mathematics, proved here.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace ThermalWeightSevenEighths

open Real Set MeasureTheory

/-! ## Part 1: series values

`ζ(4) = π⁴/90` split into even/odd index parts, and the alternating
(Dirichlet eta) value `η(4) = (7/8)·ζ(4)`.  Lean's `1/0 = 0` convention
makes the `n = 0` terms vanish, so all sums run over all of `ℕ`. -/

/-- Even-index part of `ζ(4)`: `Σ_k 1/(2k)⁴ = (1/16)(π⁴/90)`. -/
lemma hasSum_even_inv_pow_four :
    HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 4)
      (1 / 16 * (π ^ 4 / 90)) := by
  have h := hasSum_zeta_four.mul_left (1 / 16 : ℝ)
  have hfe : (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 4)
      = fun k : ℕ => (1 / 16 : ℝ) * ((1 : ℝ) / (k : ℝ) ^ 4) := by
    funext k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num
    · have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
      push_cast
      field_simp
      ring
  rw [hfe]
  exact h

/-- The odd-index part of `ζ(4)` is summable (comparison via injection). -/
lemma summable_odd_inv_pow_four :
    Summable (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 4) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    simp only at hab
    omega
  simpa [Function.comp_def] using hasSum_zeta_four.summable.comp_injective hinj

/-- Odd-index part of `ζ(4)`: `Σ_k 1/(2k+1)⁴ = (15/16)(π⁴/90)`. -/
lemma hasSum_odd_inv_pow_four :
    HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 4)
      (15 / 16 * (π ^ 4 / 90)) := by
  obtain ⟨x, hx⟩ := summable_odd_inv_pow_four
  have hsplit : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4)
      (1 / 16 * (π ^ 4 / 90) + x) :=
    HasSum.even_add_odd (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4)
      hasSum_even_inv_pow_four hx
  have hval : 1 / 16 * (π ^ 4 / 90) + x = π ^ 4 / 90 :=
    hsplit.unique hasSum_zeta_four
  have hx' : x = 15 / 16 * (π ^ 4 / 90) := by linarith
  rwa [hx'] at hx

/-- **Dirichlet eta at 4**: `Σ_n (−1)^(n+1)/n⁴ = (7/8)(π⁴/90) = (7/8)·ζ(4)`.
This is the analytic content of the fermionic 7/8 weight. -/
theorem hasSum_eta_four :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4)
      (7 / 8 * (π ^ 4 / 90)) := by
  have heven : HasSum
      (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / ((2 * k : ℕ) : ℝ) ^ 4)
      (-(1 / 16 * (π ^ 4 / 90))) := by
    have h := hasSum_even_inv_pow_four.neg
    have hfe : (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / ((2 * k : ℕ) : ℝ) ^ 4)
        = fun k : ℕ => -((1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 4) := by
      funext k
      have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
      rw [hodd.neg_one_pow]
      ring
    rw [hfe]
    exact h
  have hodd : HasSum
      (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1 + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ 4)
      (15 / 16 * (π ^ 4 / 90)) := by
    have hfe : (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1 + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ 4)
        = fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 4 := by
      funext k
      have heven' : Even (2 * k + 1 + 1) := ⟨k + 1, by ring⟩
      rw [heven'.neg_one_pow]
    rw [hfe]
    exact hasSum_odd_inv_pow_four
  have hsum := HasSum.even_add_odd
    (f := fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4) heven hodd
  have hval : -(1 / 16 * (π ^ 4 / 90)) + 15 / 16 * (π ^ 4 / 90)
      = 7 / 8 * (π ^ 4 / 90) := by ring
  rwa [hval] at hsum

/-! ## Part 2: index-shifted series (for the Dirichlet-series form) -/

/-- `Σ_{n≥0} 1/(n+1)⁴ = π⁴/90` (the `n=0` term of `ζ(4)` vanishes). -/
lemma hasSum_shift_zeta_four :
    HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4) (π ^ 4 / 90) := by
  rw [hasSum_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) 1]
  simpa using hasSum_zeta_four

/-- `Σ_{n≥0} (−1)^n/(n+1)⁴ = (7/8)(π⁴/90)` (shifted eta series). -/
lemma hasSum_shift_eta_four :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ) ^ 4)
      (7 / 8 * (π ^ 4 / 90)) := by
  have h : HasSum
      (fun n : ℕ => (-1 : ℝ) ^ (n + 1 + 1) / ((n + 1 : ℕ) : ℝ) ^ 4)
      (7 / 8 * (π ^ 4 / 90)) := by
    rw [hasSum_nat_add_iff (f := fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4) 1]
    simpa using hasSum_eta_four
  have hfe : (fun n : ℕ => (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ) ^ 4)
      = fun n : ℕ => (-1 : ℝ) ^ (n + 1 + 1) / ((n + 1 : ℕ) : ℝ) ^ 4 := by
    funext n
    have hp : (-1 : ℝ) ^ (n + 1 + 1) = (-1 : ℝ) ^ n := by
      simp [pow_succ]
    rw [hp]
  rw [hfe]
  exact h

/-! ## Part 3: the thermal kernels and their geometric expansions -/

/-- Bose-Einstein thermal kernel `1/(eᵗ − 1)` (ℂ-valued, for `mellin`). -/
noncomputable def boseKernel (t : ℝ) : ℂ := 1 / (Real.exp t - 1)

/-- Fermi-Dirac thermal kernel `1/(eᵗ + 1)`. -/
noncomputable def fermiKernel (t : ℝ) : ℂ := 1 / (Real.exp t + 1)

/-- Shared term identity: `e^{−t}·(e^{−t})ⁿ = e^{−(n+1)t}`. -/
private lemma exp_term (t : ℝ) (n : ℕ) :
    Real.exp (-t) * Real.exp (-t) ^ n = Real.exp (-((n + 1 : ℕ) : ℝ) * t) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Geometric expansion of the Bose kernel:
`Σ_n e^{−(n+1)t} = 1/(eᵗ − 1)` for `t > 0`. -/
lemma hasSum_boseKernel_expansion {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => (1 : ℂ) * Real.exp (-((n + 1 : ℕ) : ℝ) * t))
      (boseKernel t) := by
  have hE : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hξpos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have hξlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : HasSum (fun n : ℕ => Real.exp (-t) ^ n) (1 - Real.exp (-t))⁻¹ := by
    apply hasSum_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_pos hξpos]
    exact hξlt
  have hmul := hgeom.mul_left (Real.exp (-t))
  have hval : Real.exp (-t) * (1 - Real.exp (-t))⁻¹ = (Real.exp t - 1)⁻¹ := by
    rw [Real.exp_neg, ← mul_inv]
    congr 1
    rw [mul_sub, mul_one, mul_inv_cancel₀ hE]
  rw [hval] at hmul
  have hreal : HasSum (fun n : ℕ => Real.exp (-((n + 1 : ℕ) : ℝ) * t))
      ((Real.exp t - 1)⁻¹) := by
    have hfe : (fun n : ℕ => Real.exp (-((n + 1 : ℕ) : ℝ) * t))
        = fun n : ℕ => Real.exp (-t) * Real.exp (-t) ^ n := by
      funext n
      rw [exp_term t n]
    rw [hfe]
    exact hmul
  have hlift := Complex.hasSum_ofReal.mpr hreal
  have hker : boseKernel t = (((Real.exp t - 1)⁻¹ : ℝ) : ℂ) := by
    rw [boseKernel, one_div]
    push_cast
    ring
  rw [hker]
  simpa using hlift

/-- Geometric expansion of the Fermi kernel:
`Σ_n (−1)ⁿ e^{−(n+1)t} = 1/(eᵗ + 1)` for `t > 0`. -/
lemma hasSum_fermiKernel_expansion {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n * Real.exp (-((n + 1 : ℕ) : ℝ) * t))
      (fermiKernel t) := by
  have hE : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hξpos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have hξlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : HasSum (fun n : ℕ => (-Real.exp (-t)) ^ n)
      (1 - -Real.exp (-t))⁻¹ := by
    apply hasSum_geometric_of_norm_lt_one
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos hξpos]
    exact hξlt
  have hmul := hgeom.mul_left (Real.exp (-t))
  have hval : Real.exp (-t) * (1 - -Real.exp (-t))⁻¹ = (Real.exp t + 1)⁻¹ := by
    rw [sub_neg_eq_add, Real.exp_neg, ← mul_inv]
    congr 1
    rw [mul_add, mul_one, mul_inv_cancel₀ hE]
  rw [hval] at hmul
  have hreal : HasSum
      (fun n : ℕ => (-1 : ℝ) ^ n * Real.exp (-((n + 1 : ℕ) : ℝ) * t))
      ((Real.exp t + 1)⁻¹) := by
    have hfe : (fun n : ℕ => (-1 : ℝ) ^ n * Real.exp (-((n + 1 : ℕ) : ℝ) * t))
        = fun n : ℕ => Real.exp (-t) * (-Real.exp (-t)) ^ n := by
      funext n
      rw [neg_pow, ← exp_term t n]
      ring
    rw [hfe]
    exact hmul
  have hlift := Complex.hasSum_ofReal.mpr hreal
  have hker : fermiKernel t = (((Real.exp t + 1)⁻¹ : ℝ) : ℂ) := by
    rw [fermiKernel, one_div]
    push_cast
    ring
  rw [hker]
  have hfe2 : (fun n : ℕ => (-1 : ℂ) ^ n * (Real.exp (-((n + 1 : ℕ) : ℝ) * t) : ℝ))
      = fun n : ℕ =>
        (((-1 : ℝ) ^ n * Real.exp (-((n + 1 : ℕ) : ℝ) * t) : ℝ) : ℂ) := by
    funext n
    push_cast
    ring
  rw [hfe2]
  exact hlift

/-! ## Part 4: Mellin transforms at `s = 4` and the 7/8 ratio -/

/-- `Γ(4) = 3! = 6` in ℂ. -/
lemma complex_Gamma_four : Complex.Gamma 4 = 6 := by
  have h : (4 : ℂ) = ((3 : ℕ) : ℂ) + 1 := by norm_num
  rw [h, Complex.Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]

/-- The Bose-Einstein energy integral:
`∫₀^∞ t³/(eᵗ−1) dt = mellin boseKernel 4 = Γ(4)·ζ(4) = 6·π⁴/90`. -/
theorem mellin_boseKernel_eq :
    mellin boseKernel 4 = ((6 * (π ^ 4 / 90) : ℝ) : ℂ) := by
  have hp : ∀ n : ℕ, (fun _ : ℕ => (1 : ℂ)) n = 0 ∨ 0 < ((n + 1 : ℕ) : ℝ) :=
    fun n => Or.inr (by positivity)
  have hs : 0 < (4 : ℂ).re := by norm_num
  have hF : ∀ t ∈ Ioi (0 : ℝ),
      HasSum (fun n : ℕ => (1 : ℂ) * Real.exp (-((n + 1 : ℕ) : ℝ) * t))
        (boseKernel t) :=
    fun t ht => hasSum_boseKernel_expansion ht
  have h_sum : Summable
      (fun n : ℕ => ‖(1 : ℂ)‖ / ((n + 1 : ℕ) : ℝ) ^ (4 : ℂ).re) := by
    have h4 : ((4 : ℂ).re) = ((4 : ℕ) : ℝ) := by norm_num
    simp only [norm_one, h4, Real.rpow_natCast]
    exact hasSum_shift_zeta_four.summable
  have hmellin := hasSum_mellin (a := fun _ : ℕ => (1 : ℂ))
    (p := fun n : ℕ => ((n + 1 : ℕ) : ℝ)) (F := boseKernel) (s := 4)
    hp hs hF h_sum
  have hvalue : HasSum
      (fun n : ℕ =>
        Complex.Gamma 4 * (1 : ℂ) / (((n + 1 : ℕ) : ℝ) : ℂ) ^ (4 : ℂ))
      ((6 * (π ^ 4 / 90) : ℝ) : ℂ) := by
    have hreal := hasSum_shift_zeta_four.mul_left (6 : ℝ)
    have hlift := Complex.hasSum_ofReal.mpr hreal
    have hfe : (fun n : ℕ =>
          Complex.Gamma 4 * (1 : ℂ) / (((n + 1 : ℕ) : ℝ) : ℂ) ^ (4 : ℂ))
        = fun n : ℕ =>
          (((6 : ℝ) * ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 4) : ℝ) : ℂ) := by
      funext n
      have h4 : (4 : ℂ) = ((4 : ℕ) : ℂ) := by norm_num
      rw [complex_Gamma_four, h4, Complex.cpow_natCast]
      push_cast
      ring
    rw [hfe]
    exact hlift
  exact hmellin.unique hvalue

/-- The Fermi-Dirac energy integral:
`∫₀^∞ t³/(eᵗ+1) dt = mellin fermiKernel 4 = Γ(4)·η(4) = (7/8)·6·π⁴/90`. -/
theorem mellin_fermiKernel_eq :
    mellin fermiKernel 4 = ((7 / 8 * (6 * (π ^ 4 / 90)) : ℝ) : ℂ) := by
  have hp : ∀ n : ℕ, (fun k : ℕ => (-1 : ℂ) ^ k) n = 0 ∨ 0 < ((n + 1 : ℕ) : ℝ) :=
    fun n => Or.inr (by positivity)
  have hs : 0 < (4 : ℂ).re := by norm_num
  have hF : ∀ t ∈ Ioi (0 : ℝ),
      HasSum (fun n : ℕ => (-1 : ℂ) ^ n * Real.exp (-((n + 1 : ℕ) : ℝ) * t))
        (fermiKernel t) :=
    fun t ht => hasSum_fermiKernel_expansion ht
  have h_sum : Summable
      (fun n : ℕ => ‖(-1 : ℂ) ^ n‖ / ((n + 1 : ℕ) : ℝ) ^ (4 : ℂ).re) := by
    have h4 : ((4 : ℂ).re) = ((4 : ℕ) : ℝ) := by norm_num
    simp only [norm_pow, norm_neg, norm_one, one_pow, h4, Real.rpow_natCast]
    exact hasSum_shift_zeta_four.summable
  have hmellin := hasSum_mellin (a := fun k : ℕ => (-1 : ℂ) ^ k)
    (p := fun n : ℕ => ((n + 1 : ℕ) : ℝ)) (F := fermiKernel) (s := 4)
    hp hs hF h_sum
  have hvalue : HasSum
      (fun n : ℕ =>
        Complex.Gamma 4 * (-1 : ℂ) ^ n / (((n + 1 : ℕ) : ℝ) : ℂ) ^ (4 : ℂ))
      ((7 / 8 * (6 * (π ^ 4 / 90)) : ℝ) : ℂ) := by
    have hreal := hasSum_shift_eta_four.mul_left (6 : ℝ)
    have hlift := Complex.hasSum_ofReal.mpr hreal
    have hfe : (fun n : ℕ =>
          Complex.Gamma 4 * (-1 : ℂ) ^ n / (((n + 1 : ℕ) : ℝ) : ℂ) ^ (4 : ℂ))
        = fun n : ℕ =>
          (((6 : ℝ) * ((-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ) ^ 4) : ℝ) : ℂ) := by
      funext n
      have h4 : (4 : ℂ) = ((4 : ℕ) : ℂ) := by norm_num
      rw [complex_Gamma_four, h4, Complex.cpow_natCast]
      push_cast
      ring
    have hv : (6 : ℝ) * (7 / 8 * (π ^ 4 / 90)) = 7 / 8 * (6 * (π ^ 4 / 90)) := by
      ring
    rw [hfe]
    rw [hv] at hlift
    exact hlift
  exact hmellin.unique hvalue

/-- **The 7/8 ratio theorem**: the Fermi-Dirac to Bose-Einstein energy-density
ratio is exactly `7/8`.  This is the thermal weight in `g_⋆ = g_b + (7/8) g_f`,
now a computed consequence of quantum statistics. -/
theorem fermi_bose_ratio :
    mellin fermiKernel 4 / mellin boseKernel 4 = 7 / 8 := by
  have hne : ((6 * (π ^ 4 / 90) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  rw [mellin_fermiKernel_eq, mellin_boseKernel_eq, Complex.ofReal_mul,
    mul_div_assoc, div_self hne, mul_one]
  norm_num

/-- **Bridge to `GStarDerivation`**: the `fermion_boltzmann` value used in the
`g_⋆` accounting equals the proved Fermi/Bose Mellin ratio.  The `def := 7/8`
is therefore no longer a convention: it is forced by the quantum statistics
of the two thermal kernels.  (Which kernel each species gets is the exchange
sign, forced by RS via `Foundation.EightTick.spin_statistics_key`.) -/
theorem fermion_boltzmann_forced :
    ((GStarDerivation.fermion_boltzmann : ℚ) : ℂ)
      = mellin fermiKernel 4 / mellin boseKernel 4 := by
  rw [fermi_bose_ratio]
  norm_num [GStarDerivation.fermion_boltzmann]

end ThermalWeightSevenEighths
end Cosmology
end IndisputableMonolith
