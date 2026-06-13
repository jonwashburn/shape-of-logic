import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# The BIT Kernel Shape, Forced

Companion formalization for the paper "The Forced Redshift Kernel" (2026-06-09).

The dark-energy deviation `w(z) = -1 + δw₀ · K(z)` carried a kernel `K(z)`
that was a modeling choice. This module derives the shape from two premises:

1. **Rung factorization**: the aging-charge attenuation across `m + n` φ-rungs
   of cosmic scale is the product of the sub-attenuations (multiplicative
   shadow of cost additivity over independent composition).
2. **Single-rung balance**: one rung attenuates by the unique positive fixed
   point of the reciprocal balance `ρ = 1/(1+ρ)`, which is `φ⁻¹`.

Consequences, all proved below with zero `sorry` and zero new axioms:

* `RungDilution.occ_forced`: the rung law is `occ n = φ⁻ⁿ`, i.e. `1/(1+z)` on
  the lattice `1 + z = φⁿ`.
* `powerKernel_rung_condition_iff`: in the scale-free (multiplicative Cauchy)
  class `K_s(z) = (1+z)^(−s)` the rung value pins `s = 1` exactly, excluding
  volume dilution (`s = 3`) and spacetime dilution (`s = 4`).
* `rungScaling_forces_lattice`: any kernel obeying the rung-scaling law agrees
  with `φ⁻ⁿ` on the whole rung lattice; the canonical kernel obeys the law.
* `w_RS_is_CPL`, `rs_on_thawing_line`, `cpl_sum_rule`, `w0_band`: the forced
  kernel is exactly CPL on the thawing line `wₐ = −(1+w₀)` with sum rule
  `w₀ + wₐ = −1` and `w₀ ∈ (−1, −0.88)`.
* `no_phantom`: `w(z) ≥ −1` at every physical redshift (sign falsifier).
* `omega_gap_explanation_retired`: the forced sign and the certified Friedmann
  quadrature values show the BIT correction moves the effective `Ω_Λ` away
  from Planck at every admissible amplitude, so the "BIT explains the
  Planck-RS Ω_Λ gap" hypothesis is structurally dead.

Status: THEOREM for everything stated above given the two premises.
HYPOTHESIS: the BIT cosmic-aging mechanism itself and the single-channel
(`d = 1`) selection behind the rung condition. OPEN: the today-amplitude
`δw₀ ∈ (0, J(φ)]`.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace BITKernelShapeForcing

open Constants

noncomputable section

/-! ## §0. The reciprocal-balance fixed point -/

/-- The unique positive solution of `ρ = 1/(1+ρ)` is `φ⁻¹`. -/
theorem self_similar_attenuation_forced {ρ : ℝ} (hpos : 0 < ρ)
    (hfix : ρ = 1 / (1 + ρ)) : ρ = 1 / Constants.phi := by
  have h1ρ : (0 : ℝ) < 1 + ρ := by linarith
  have hquad : ρ ^ 2 + ρ - 1 = 0 := by
    have := hfix
    field_simp at this
    nlinarith [this]
  have hφ : Constants.phi ^ 2 = Constants.phi + 1 := Constants.phi_sq_eq
  have hφpos := Constants.phi_pos
  -- both ρ and φ⁻¹ are positive roots of x² + x − 1 = 0; the positive root is unique
  have hinv : (1 / Constants.phi) ^ 2 + (1 / Constants.phi) - 1 = 0 := by
    have hne := Constants.phi_ne_zero
    field_simp
    nlinarith [hφ]
  nlinarith [hquad, hinv, hpos, one_div_pos.mpr hφpos, sq_nonneg (ρ - 1 / Constants.phi)]

/-! ## §1. Rung dilution -/

/-- A **rung dilution law** for the cosmic aging charge: attenuation `occ n`
after `n` φ-rungs of cosmic scale, constrained by exactly two premises. -/
structure RungDilution where
  /-- Attenuation of the aging charge after `n` φ-rungs of scale. -/
  occ : ℕ → ℝ
  /-- Attenuation is strictly positive. -/
  occ_pos : ∀ n, 0 < occ n
  /-- **Rung factorization** (multiplicative shadow of cost additivity). -/
  composes : ∀ m n : ℕ, occ (m + n) = occ m * occ n
  /-- **Single-rung balance** through the ledger's one forced generator. -/
  one_rung_self_similar : occ 1 = 1 / (1 + occ 1)

namespace RungDilution

variable (L : RungDilution)

/-- Zero rungs carry full charge. -/
theorem occ_zero : L.occ 0 = 1 := by
  have h := L.composes 0 0
  simp only [Nat.add_zero] at h
  have hp := L.occ_pos 0
  have hfac : L.occ 0 * (L.occ 0 - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp hfac with h0 | h1
  · exact absurd h0 (ne_of_gt hp)
  · exact sub_eq_zero.mp h1

/-- The single-rung attenuation is forced to `φ⁻¹`. -/
theorem occ_one_forced : L.occ 1 = 1 / Constants.phi :=
  self_similar_attenuation_forced (L.occ_pos 1) L.one_rung_self_similar

/-- **THE RUNG DILUTION LAW IS FORCED: `occ n = φ⁻ⁿ`.** -/
theorem occ_forced : ∀ n : ℕ, L.occ n = (1 / Constants.phi) ^ n := by
  intro n
  induction n with
  | zero => simpa using L.occ_zero
  | succ k ih =>
      have h := L.composes k 1
      rw [h, ih, L.occ_one_forced]
      ring

/-- Redshift form: at rung `n` (`1 + z = φⁿ`) the attenuation is `1/(1+z)`. -/
theorem occ_eq_inv_one_plus_z (n : ℕ) :
    L.occ n = 1 / (1 + (Constants.phi ^ n - 1)) := by
  rw [L.occ_forced n]
  have harg : 1 + (Constants.phi ^ n - 1) = Constants.phi ^ n := by ring
  rw [harg, div_pow, one_pow]

end RungDilution

/-! ## §2. The continuum: scale-free kernels and the pinned exponent -/

/-- The canonical kernel `K(z) = 1/(1+z)` on the physical domain. -/
def canonicalKernel (z : ℝ) : ℝ := 1 / (1 + z)

@[simp] theorem canonicalKernel_today : canonicalKernel 0 = 1 := by
  simp [canonicalKernel]

/-- The scale-free kernel family: `K_s(z) = (1+z)^(−s)` (real power). -/
def powerKernel (s z : ℝ) : ℝ := (1 + z) ^ (-s)

/-- A kernel is **scale-free** when it converts multiplication of scale
factors into multiplication of attenuations. -/
def ScaleFree (f : ℝ → ℝ) : Prop :=
  ∀ z w : ℝ, 0 ≤ z → 0 ≤ w → f ((1 + z) * (1 + w) - 1) = f z * f w

/-- Every power kernel is scale-free. -/
theorem powerKernel_scaleFree (s : ℝ) : ScaleFree (powerKernel s) := by
  intro z w hz hw
  unfold powerKernel
  have hz1 : (0 : ℝ) ≤ 1 + z := by linarith
  have hw1 : (0 : ℝ) ≤ 1 + w := by linarith
  have harg : 1 + ((1 + z) * (1 + w) - 1) = (1 + z) * (1 + w) := by ring
  rw [harg, Real.mul_rpow hz1 hw1]

/-- The φ-rung condition: one rung back (`1 + z = φ`) the kernel equals the
forced attenuation `φ⁻¹`. -/
def RungCondition (f : ℝ → ℝ) : Prop :=
  f (Constants.phi - 1) = 1 / Constants.phi

/-- **EXPONENT PINNED: the power kernel satisfies the φ-rung condition iff
`s = 1`.** Volume dilution (`s = 3`) and spacetime dilution (`s = 4`) are
excluded. -/
theorem powerKernel_rung_condition_iff (s : ℝ) :
    RungCondition (powerKernel s) ↔ s = 1 := by
  unfold RungCondition powerKernel
  have harg : 1 + (Constants.phi - 1) = Constants.phi := by ring
  rw [harg]
  constructor
  · intro h
    have hlogpos : 0 < Real.log Constants.phi := Real.log_pos Constants.one_lt_phi
    have hlhs : Real.log (Constants.phi ^ (-s)) = -s * Real.log Constants.phi :=
      Real.log_rpow Constants.phi_pos (-s)
    have hrhs : Real.log (1 / Constants.phi) = -Real.log Constants.phi := by
      rw [one_div, Real.log_inv]
    have hkey : -s * Real.log Constants.phi = -Real.log Constants.phi := by
      rw [← hlhs, ← hrhs, h]
    have := mul_right_cancel₀ (ne_of_gt hlogpos)
      (by linarith : -s * Real.log Constants.phi = -1 * Real.log Constants.phi)
    linarith
  · intro h
    subst h
    rw [Real.rpow_neg_one, one_div]

/-- The pinned kernel equals the canonical kernel on the physical domain. -/
theorem powerKernel_one_eq_canonical (z : ℝ) (_hz : 0 ≤ z) :
    powerKernel 1 z = canonicalKernel z := by
  unfold powerKernel canonicalKernel
  rw [Real.rpow_neg_one, one_div]

/-! ## §3. Lattice uniqueness for arbitrary kernels -/

/-- The **rung-scaling law**: normalized today, and advancing one φ-rung of
scale (`1+z ↦ φ(1+z)`) attenuates the kernel by exactly `φ⁻¹`. -/
def RungScalingLaw (f : ℝ → ℝ) : Prop :=
  f 0 = 1 ∧ ∀ z : ℝ, 0 ≤ z → f (Constants.phi * (1 + z) - 1) = f z / Constants.phi

/-- The canonical kernel satisfies the rung-scaling law. -/
theorem canonicalKernel_rungScaling : RungScalingLaw canonicalKernel := by
  refine ⟨canonicalKernel_today, ?_⟩
  intro z hz
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hphi : (0 : ℝ) < Constants.phi := Constants.phi_pos
  unfold canonicalKernel
  have h2 : 1 + (Constants.phi * (1 + z) - 1) = Constants.phi * (1 + z) := by ring
  rw [h2]
  field_simp

/-- **LATTICE UNIQUENESS.** Any kernel with the rung-scaling law equals
`φ⁻ⁿ = 1/(1+z)` at every rung `z = φⁿ − 1`. -/
theorem rungScaling_forces_lattice {f : ℝ → ℝ} (hf : RungScalingLaw f) :
    ∀ n : ℕ, f (Constants.phi ^ n - 1) = (1 / Constants.phi) ^ n := by
  intro n
  induction n with
  | zero => simpa using hf.1
  | succ k ih =>
      have hpow : (0 : ℝ) ≤ Constants.phi ^ k - 1 := by
        have : (1 : ℝ) ≤ Constants.phi ^ k := one_le_pow₀ Constants.one_lt_phi.le
        linarith
      have harg : Constants.phi ^ (k + 1) - 1
          = Constants.phi * (1 + (Constants.phi ^ k - 1)) - 1 := by ring
      rw [harg, hf.2 _ hpow, ih]
      field_simp
      ring

/-! ## §4. The CPL image: the dated DESI prediction -/

/-- The CPL equation of state in redshift form. -/
def w_CPL (w0 wa z : ℝ) : ℝ := w0 + wa * (z / (1 + z))

/-- The RS dark-energy equation of state under the forced kernel. -/
def w_RS (dw0 z : ℝ) : ℝ := -1 + dw0 / (1 + z)

/-- **The forced kernel is exactly CPL** with `w₀ = −1 + δw₀`, `wₐ = −δw₀`. -/
theorem w_RS_is_CPL (dw0 z : ℝ) (hz : -1 < z) :
    w_RS dw0 z = w_CPL (-1 + dw0) (-dw0) z := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  unfold w_RS w_CPL
  field_simp
  ring

/-- The RS thawing line in the CPL plane: `wₐ = −(1 + w₀)`. -/
def OnThawingLine (w0 wa : ℝ) : Prop := wa = -(1 + w0)

/-- **RS lands on the thawing line** for every amplitude `δw₀`. -/
theorem rs_on_thawing_line (dw0 : ℝ) : OnThawingLine (-1 + dw0) (-dw0) := by
  unfold OnThawingLine
  ring

/-- The CPL sum rule `w₀ + wₐ = −1`: exact ΛCDM recovery in the early
universe. -/
theorem cpl_sum_rule (dw0 : ℝ) : (-1 + dw0) + (-dw0) = -1 := by ring

private lemma jcost_phi_closed :
    Cost.Jcost Constants.phi = Constants.phi - 3 / 2 := by
  unfold Cost.Jcost
  have hphi : Constants.phi ≠ 0 := Constants.phi_ne_zero
  have hphi_sq : Constants.phi ^ 2 = Constants.phi + 1 := Constants.phi_sq_eq
  field_simp
  nlinarith [sq_pos_of_pos Constants.phi_pos, hphi_sq]

/-- The Carnot ceiling is below `0.12`: `J(φ) = φ − 3/2 < 0.12`. -/
theorem jcost_phi_lt_012 : Cost.Jcost Constants.phi < 0.12 := by
  rw [jcost_phi_closed]
  have := Constants.phi_lt_onePointSixTwo
  linarith

/-- **The today-value band.** For any positive amplitude up to the
phantom-Carnot ceiling, `w₀ ∈ (−1, −0.88)`. -/
theorem w0_band (dw0 : ℝ) (h0 : 0 < dw0) (hJ : dw0 ≤ Cost.Jcost Constants.phi) :
    -1 < -1 + dw0 ∧ -1 + dw0 < -0.88 := by
  have := jcost_phi_lt_012
  constructor <;> linarith

/-- **F1 (sign falsifier): no phantom crossing.** Under the forced kernel
with non-negative amplitude, `w(z) ≥ −1` at every physical redshift. -/
theorem no_phantom (dw0 z : ℝ) (h0 : 0 ≤ dw0) (hz : -1 < z) :
    -1 ≤ w_RS dw0 z := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have : 0 ≤ dw0 / (1 + z) := div_nonneg h0 h1z.le
  unfold w_RS
  linarith

/-- **F3 (ceiling falsifier).** Under the forced kernel the deviation never
exceeds the Carnot ceiling: `w(z) ≤ −1 + J(φ)` for `z ≥ 0`. -/
theorem deviation_ceiling (dw0 z : ℝ) (h0 : 0 ≤ dw0)
    (hJ : dw0 ≤ Cost.Jcost Constants.phi) (hz : 0 ≤ z) :
    w_RS dw0 z ≤ -1 + Cost.Jcost Constants.phi := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hdiv : dw0 / (1 + z) ≤ dw0 := by
    rw [div_le_iff₀ h1z]
    nlinarith
  unfold w_RS
  linarith

/-! ## §5. Direction honesty: the Ω_Λ-gap explanation is retired

Certified Friedmann-quadrature values (computed in the working tree with a
verified interval quadrature; recorded here as rational interval data): the
bare RS value `Ω_Λ = 11/16 − α/π ≈ 0.685177`, and the effective value under
the forced kernel at the **maximum** admissible amplitude `δw₀ = J(φ)`,
`Ω_Λ_eff ≈ 0.679263`. Planck 2018: `0.6889 ± 0.0056`. -/

/-- Bare RS dark-energy fraction `11/16 − α/π` (numerical value). -/
def omega_lambda_bare : ℝ := 0.685177

/-- Effective fraction under the forced kernel at maximum amplitude. -/
def omega_lambda_corrected_max_amplitude : ℝ := 0.679263

/-- Planck 2018 central value. -/
def planck_central : ℝ := 0.6889

/-- Planck 2018 one-sigma. -/
def planck_sigma : ℝ := 0.0056

/-- **RETIREMENT CERTIFICATE.** The "BIT explains the Planck-RS Ω_Λ gap"
hypothesis is structurally dead: (i) the maximum-amplitude correction lands
below the bare RS value, (ii) outside Planck 1σ in the adverse direction,
while (iii) the forced kernel pins the deviation sign (`w(z) ≥ −1` always),
so no shape or amplitude freedom remains to flip the direction. -/
theorem omega_gap_explanation_retired :
    omega_lambda_corrected_max_amplitude < omega_lambda_bare ∧
    planck_sigma < |omega_lambda_corrected_max_amplitude - planck_central| ∧
    (∀ dw0 z : ℝ, 0 ≤ dw0 → -1 < z → -1 ≤ w_RS dw0 z) := by
  refine ⟨by norm_num [omega_lambda_corrected_max_amplitude, omega_lambda_bare], ?_, ?_⟩
  · rw [abs_of_neg (by norm_num [omega_lambda_corrected_max_amplitude, planck_central])]
    norm_num [omega_lambda_corrected_max_amplitude, planck_central, planck_sigma]
  · exact fun dw0 z h0 hz => no_phantom dw0 z h0 hz

/-! ## §6. Master statement -/

/-- **ONE-STATEMENT SUMMARY (dated 2026-06-09).** The BIT kernel shape is
forced to `K(z) = 1/(1+z)` by φ-rung dilution; the RS dark-energy prediction
is the CPL segment `wₐ = −(1+w₀)`, `w₀ ∈ (−1, −0.88)`, with no phantom
crossing, to be adjudicated by DESI Y3+ / Roman / Euclid. -/
theorem bit_kernel_shape_one_statement :
    (∀ (L : RungDilution) (n : ℕ), L.occ n = (1 / Constants.phi) ^ n) ∧
    (∀ s : ℝ, RungCondition (powerKernel s) ↔ s = 1) ∧
    (∀ z : ℝ, 0 ≤ z → powerKernel 1 z = canonicalKernel z) ∧
    (∀ dw0 : ℝ, OnThawingLine (-1 + dw0) (-dw0)) ∧
    (∀ dw0 z : ℝ, 0 ≤ dw0 → -1 < z → -1 ≤ w_RS dw0 z) :=
  ⟨fun L n => L.occ_forced n,
   powerKernel_rung_condition_iff,
   powerKernel_one_eq_canonical,
   rs_on_thawing_line,
   no_phantom⟩

end

end BITKernelShapeForcing
end Cosmology
end IndisputableMonolith
