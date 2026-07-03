import Mathlib

/-!
# Entropy per Photon 7.04 from ζ(3), π⁴, and g*s = 43/11

**Status: THEOREM (analysis + arithmetic) over MODEL inputs (Standard Model
particle content and Fermi–Dirac statistics).**

This module derives the entropy-per-photon ratio used by the baryogenesis
dynamical lane,

  `s / n_γ = π⁴ g*s / (45 ζ(3))  ∈ (7.0393, 7.0396)`,

replacing the bare constant `7.04` in `EpsilonCPFromGap.dynPrefactor` with a
derivation. The three ingredients:

## 1. ζ(3) window (THEOREM)

`zeta3 := ∑ 1/(n+1)³` is bounded by splitting at 40 terms:
the partial sum `S40` is evaluated exactly by `norm_num`
(`1.2017520 < S40 < 1.2017522`), and the tail `∑_{n≥41} 1/n³` is trapped by
two telescoping series,

  `1/(2(n+41)(n+42)) − 1/(2(n+42)(n+43)) = 1/((n+41)(n+42)(n+43)) ≤ 1/(n+41)³`
  `1/(2(n+40)(n+41)) − 1/(2(n+41)(n+42)) = 1/((n+40)(n+41)(n+42)) ≥ 1/(n+41)³`

giving `1/3444 ≤ tail ≤ 1/3280` and hence

  `1.202042 < ζ(3) < 1.202065`   (true value 1.2020569…).

## 2. π⁴ window (THEOREM)

From Mathlib's `Real.pi_gt_d6` / `Real.pi_lt_d6`:
`97.40900 < π⁴ < 97.40914` (true value 97.409091…).

## 3. g*s = 43/11 (THEOREM (arithmetic) from MODEL particle content)

Present-day entropy degrees of freedom. MODEL inputs: the photon has 2
polarizations; e± carry 4 fermionic dof; 3 neutrino generations carry 6
fermionic dof. The `7/8` fermion weight is now THEOREM, not a MODEL input:
`Cosmology.FermionWeight` proves the series identity `η(4) = (7/8)·ζ(4)`
and `Cosmology.FermionWeightIntegral` proves the thermodynamic integrals
themselves (`∫x³/(eˣ+1) = 7π⁴/120 = (7/8)·∫x³/(eˣ−1)`, both axiom-clean).
Entropy conservation through e± annihilation heats photons but not the
decoupled neutrinos:

  `(T_ν/T_γ)³ = g_after/g_before = 2 / (2 + (7/8)·4) = 4/11`,

so `g*s = 2 + (7/8)·6·(4/11) = 43/11`.

The conservation step itself is now THEOREM, not arithmetic-by-definition:
`Cosmology.NeutrinoDilution` (which imports this module) derives
`(T_ν/T_γ)³ = 4/11` from comoving entropy conservation plus free neutrino
streaming, with the plasma entropy density built from the entropy-functional
integrals of `Cosmology.RadiationEntropyRelation` (`∫σ_B = 4π⁴/45`,
`∫σ_F = 7π⁴/90`, both derived), and re-derives `g*s = 43/11` as the
present-day total (`gStarS_from_conservation`). What stays MODEL is only
the particle content and the two named conservation hypotheses.

## Result

  `entropyPerPhoton = π⁴ (43/11) / (45 ζ(3)) ∈ (7.0393, 7.0396)`.

The bare `7.04` used in the staging modules is this value rounded to three
significant figures. The bridge module `DynPrefactorDerived` propagates the
window into the dynamical prefactor `P = (28/79) · s/n_γ` and re-proves the
rung-selection theorems with the fully derived prefactor.

Reference: Kolb & Turner, *The Early Universe*, §3.3–3.4.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace EntropyPerPhoton

open Filter Topology

/-! ## §1. g*s = 43/11 from particle content and entropy conservation -/

/-- Photon internal dof: 2 polarizations (MODEL input). -/
def gPhoton : ℚ := 2

/-- Electron–positron internal dof: 2 spin states × (e⁻ + e⁺) (MODEL input). -/
def gElectron : ℚ := 4

/-- Neutrino internal dof: 3 generations × (ν + ν̄) × 1 helicity (MODEL input). -/
def gNeutrino : ℚ := 6

/-- Fermionic entropy weight `7/8`: the ratio of the Fermi–Dirac to
Bose–Einstein thermodynamic integrals, `∫x³/(eˣ+1) / ∫x³/(eˣ−1) = η(4)/ζ(4)
= 1 − 2⁻³ = 7/8`.

**THEOREM-backed** (upgraded from MODEL 2026-07-01): the series layer is
`FermionWeight.fermionWeight_eq_eta_zeta_ratio` (`η(4) = (7/8)·ζ(4)`), and
the integral layer is `FermionWeightIntegral.fermi_integral_eq_weight_mul_bose`
(`∫ t³/(eᵗ+1) = (7/8)·∫ t³/(eᵗ−1)`, with both integrals in closed form:
`π⁴/15` and `7π⁴/120`). Both are axiom-clean. The modules import this
definition (not vice versa), so the value stays a plain rational here. -/
def fermionWeight : ℚ := 7 / 8

/-- Entropy dof of the photon–electron plasma before e± annihilation:
`2 + (7/8)·4 = 11/2`. -/
def gBefore : ℚ := gPhoton + fermionWeight * gElectron

/-- Entropy dof of the photon sector after e± annihilation: photons only. -/
def gAfter : ℚ := gPhoton

/-- **THEOREM-backed (neutrino dilution).** Entropy conservation in the
photon–electron sector across e± annihilation (`g·(aT)³` fixed while
decoupled neutrinos redshift freely) forces
`(T_ν/T_γ)³ = g_after/g_before = 4/11`.

The physical derivation is `NeutrinoDilution.dilution_from_entropy_conservation`
(which imports this module, not vice versa): entropy conservation plus free
neutrino streaming force `(T_ν/T_γ)³ = 4/11`, with the plasma entropy built
from the derived entropy-functional integrals (`RadiationEntropyRelation`),
so the `11/2 → 2` dof drop is itself derived, never assumed. Here the value
stays a plain rational. -/
def dilutionCubed : ℚ := gAfter / gBefore

theorem dilutionCubed_eq : dilutionCubed = 4 / 11 := by
  unfold dilutionCubed gAfter gBefore gPhoton fermionWeight gElectron
  norm_num

/-- Present-day entropy degrees of freedom: photons at `T_γ` plus 3 neutrino
species diluted by `(T_ν/T_γ)³ = 4/11`. -/
def gStarS : ℚ := gPhoton + fermionWeight * gNeutrino * dilutionCubed

/-- **THEOREM.** `g*s = 43/11 ≈ 3.909`. -/
theorem gStarS_eq : gStarS = 43 / 11 := by
  unfold gStarS gPhoton fermionWeight gNeutrino
  rw [dilutionCubed_eq]
  norm_num

/-! ## §2. ζ(3) window

`zeta3 = S40 + tail`. The tail `∑_{n≥0} 1/(n+41)³` is trapped between two
telescoping sums; `S40` is evaluated by exact rational arithmetic. -/

/-- Apéry's constant as the series `∑_{n≥0} 1/(n+1)³`. -/
noncomputable def zeta3 : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3

lemma zeta3_summable : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) := by
  have h := (Real.summable_one_div_nat_pow (p := 3)).mpr (by norm_num)
  have h1 := ((summable_nat_add_iff 1).mpr h)
  refine h1.congr fun n => ?_
  push_cast
  ring_nf

lemma tail_summable : Summable (fun n : ℕ => 1 / ((n : ℝ) + 41) ^ 3) := by
  have h := (Real.summable_one_div_nat_pow (p := 3)).mpr (by norm_num)
  have h41 := ((summable_nat_add_iff 41).mpr h)
  refine h41.congr fun n => ?_
  push_cast
  ring_nf

/-- Split ζ(3) at 40 terms. -/
lemma zeta3_split :
    zeta3 = (∑ i ∈ Finset.range 40, 1 / ((i : ℝ) + 1) ^ 3)
      + ∑' n : ℕ, 1 / ((n : ℝ) + 41) ^ 3 := by
  have h := zeta3_summable.sum_add_tsum_nat_add 40
  unfold zeta3
  rw [← h]
  congr 1
  refine tsum_congr fun n => ?_
  push_cast
  ring_nf

/-! ### Lower telescope: `gLo n = 1/(2(n+41)(n+42))`, differences ≤ tail terms -/

/-- Lower telescoping comparator for the ζ(3) tail. -/
noncomputable def gLo (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 41) * ((n : ℝ) + 42))

lemma gLo_nonneg (n : ℕ) : 0 ≤ gLo n := by unfold gLo; positivity

lemma gLo_tendsto : Tendsto gLo atTop (𝓝 0) := by
  apply squeeze_zero gLo_nonneg (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  unfold gLo
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma gLo_step (n : ℕ) :
    gLo n - gLo (n + 1) = 1 / (((n : ℝ) + 41) * ((n : ℝ) + 42) * ((n : ℝ) + 43)) := by
  unfold gLo
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  push_cast
  field_simp
  ring

lemma gLo_antitone (n : ℕ) : 0 ≤ gLo n - gLo (n + 1) := by
  rw [gLo_step]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  positivity

lemma hasSum_gLo : HasSum (fun n : ℕ => gLo n - gLo (n + 1)) (gLo 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg gLo_antitone]
  have hps : ∀ n : ℕ, ∑ i ∈ Finset.range n, (gLo i - gLo (i + 1)) = gLo 0 - gLo n :=
    fun n => Finset.sum_range_sub' gLo n
  simp only [hps]
  simpa using tendsto_const_nhds.sub gLo_tendsto

lemma term_lo (n : ℕ) : gLo n - gLo (n + 1) ≤ 1 / ((n : ℝ) + 41) ^ 3 := by
  rw [gLo_step]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- The ζ(3) tail is at least `gLo 0 = 1/3444`. -/
lemma tail_ge : (1 : ℝ) / 3444 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 41) ^ 3 := by
  have h0 : gLo 0 = 1 / 3444 := by unfold gLo; norm_num
  exact h0 ▸ hasSum_le term_lo hasSum_gLo tail_summable.hasSum

/-! ### Upper telescope: `gHi n = 1/(2(n+40)(n+41))`, differences ≥ tail terms -/

/-- Upper telescoping comparator for the ζ(3) tail. -/
noncomputable def gHi (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 40) * ((n : ℝ) + 41))

lemma gHi_tendsto : Tendsto gHi atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by unfold gHi; positivity) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  unfold gHi
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma gHi_step (n : ℕ) :
    gHi n - gHi (n + 1) = 1 / (((n : ℝ) + 40) * ((n : ℝ) + 41) * ((n : ℝ) + 42)) := by
  unfold gHi
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  push_cast
  field_simp
  ring

lemma gHi_antitone (n : ℕ) : 0 ≤ gHi n - gHi (n + 1) := by
  rw [gHi_step]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  positivity

lemma hasSum_gHi : HasSum (fun n : ℕ => gHi n - gHi (n + 1)) (gHi 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg gHi_antitone]
  have hps : ∀ n : ℕ, ∑ i ∈ Finset.range n, (gHi i - gHi (i + 1)) = gHi 0 - gHi n :=
    fun n => Finset.sum_range_sub' gHi n
  simp only [hps]
  simpa using tendsto_const_nhds.sub gHi_tendsto

lemma term_hi (n : ℕ) : 1 / ((n : ℝ) + 41) ^ 3 ≤ gHi n - gHi (n + 1) := by
  rw [gHi_step]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- The ζ(3) tail is at most `gHi 0 = 1/3280`. -/
lemma tail_le : (∑' n : ℕ, 1 / ((n : ℝ) + 41) ^ 3) ≤ 1 / 3280 := by
  have h0 : gHi 0 = 1 / 3280 := by unfold gHi; norm_num
  exact h0 ▸ hasSum_le term_hi tail_summable.hasSum hasSum_gHi

/-! ### Partial sum S40 by exact rational arithmetic -/

lemma S40_gt :
    (1.2017520 : ℝ) < ∑ i ∈ Finset.range 40, 1 / ((i : ℝ) + 1) ^ 3 := by
  norm_num [Finset.sum_range_succ]

lemma S40_lt :
    (∑ i ∈ Finset.range 40, 1 / ((i : ℝ) + 1) ^ 3) < 1.2017522 := by
  norm_num [Finset.sum_range_succ]

/-! ### The ζ(3) window -/

/-- **THEOREM.** `ζ(3) > 1.202042`. -/
theorem zeta3_gt : (1.202042 : ℝ) < zeta3 := by
  rw [zeta3_split]
  have h1 := S40_gt
  have h2 := tail_ge
  linarith

/-- **THEOREM.** `ζ(3) < 1.202065`. -/
theorem zeta3_lt : zeta3 < (1.202065 : ℝ) := by
  rw [zeta3_split]
  have h1 := S40_lt
  have h2 := tail_le
  linarith

theorem zeta3_pos : 0 < zeta3 := lt_trans (by norm_num) zeta3_gt

/-! ## §3. π⁴ window from Mathlib's six-digit π bounds -/

/-- **THEOREM.** `π⁴ > 97.40900`. -/
theorem pi4_gt : (97.40900 : ℝ) < Real.pi ^ 4 := by
  have h := Real.pi_gt_d6
  calc (97.40900 : ℝ) < (3.141592 : ℝ) ^ 4 := by norm_num
    _ < Real.pi ^ 4 := by
        apply pow_lt_pow_left₀ h (by norm_num)
        norm_num

/-- **THEOREM.** `π⁴ < 97.40914`. -/
theorem pi4_lt : Real.pi ^ 4 < (97.40914 : ℝ) := by
  have h := Real.pi_lt_d6
  calc Real.pi ^ 4 < (3.141593 : ℝ) ^ 4 := by
        apply pow_lt_pow_left₀ h (le_of_lt Real.pi_pos)
        norm_num
    _ < (97.40914 : ℝ) := by norm_num

/-! ## §4. The entropy-per-photon ratio -/

/-- Entropy per photon today: `s/n_γ = π⁴ g*s / (45 ζ(3))` with
`g*s = 43/11`. -/
noncomputable def entropyPerPhoton : ℝ := Real.pi ^ 4 * (43 / 11) / (45 * zeta3)

/-- The ratio in terms of the derived `gStarS` (the `43/11` in the definition
is not bare: it is `gStarS`). -/
theorem entropyPerPhoton_eq_formula :
    entropyPerPhoton = Real.pi ^ 4 * (gStarS : ℝ) / (45 * zeta3) := by
  rw [gStarS_eq]
  norm_num [entropyPerPhoton]

/-- **THEOREM (formula provenance).** `entropyPerPhoton` is exactly the ratio
of the entropy density `s = (2π²/45)·g*s·T³` to the photon number density
`n_γ = (2ζ(3)/π²)·T³` at any temperature `T > 0`. -/
theorem entropyPerPhoton_eq_ratio (T : ℝ) (hT : T ≠ 0) :
    (2 * Real.pi ^ 2 / 45 * (gStarS : ℝ) * T ^ 3)
      / (2 * zeta3 / Real.pi ^ 2 * T ^ 3) = entropyPerPhoton := by
  rw [entropyPerPhoton_eq_formula]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hz : zeta3 ≠ 0 := ne_of_gt zeta3_pos
  field_simp

/-- **THEOREM.** `s/n_γ > 7.0393`. -/
theorem entropyPerPhoton_gt : (7.0393 : ℝ) < entropyPerPhoton := by
  have hz := zeta3_lt
  have hp := pi4_gt
  have hzpos := zeta3_pos
  unfold entropyPerPhoton
  rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 45 * zeta3)]
  nlinarith

/-- **THEOREM.** `s/n_γ < 7.0396`. -/
theorem entropyPerPhoton_lt : entropyPerPhoton < (7.0396 : ℝ) := by
  have hz := zeta3_gt
  have hp := pi4_lt
  have hzpos := zeta3_pos
  unfold entropyPerPhoton
  rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 45 * zeta3)]
  nlinarith

theorem entropyPerPhoton_pos : 0 < entropyPerPhoton :=
  lt_trans (by norm_num) entropyPerPhoton_gt

/-- **THEOREM (the staged constant is the derived value to 3 s.f.).**
`|s/n_γ − 7.04| < 0.0007`: the bare `7.04` in the staging modules is the
derived ratio rounded to three significant figures. -/
theorem entropyPerPhoton_near_704 : |entropyPerPhoton - 7.04| < 0.0007 := by
  rw [abs_sub_lt_iff]
  constructor
  · linarith [entropyPerPhoton_lt]
  · linarith [entropyPerPhoton_gt]

end EntropyPerPhoton
end Cosmology
end IndisputableMonolith
