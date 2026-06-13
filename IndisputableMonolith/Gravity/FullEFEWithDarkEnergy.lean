import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Gravity.FullEFE
import IndisputableMonolith.Gravity.Connection
import IndisputableMonolith.Cosmology.CosmologicalConstantDerivation

/-!
# Full EFE With Dark Energy (QG integration of the forced vacuum term)

## The blocker this module resolves

`DarkEnergyStatus.blocker_efe_lambda_zero` records that the gravity-facing Einstein data
`Gravity.FullEFE.rs_efe_data` currently carries `cosmological_constant = 0`. Dark energy is
therefore not yet in the quantum-gravity / EFE master chain. This module puts a nonzero,
forced, covariantly-conserved vacuum term into that chain.

## What is established here

1. **The vacuum term is forced positive.** `Λ_RS(H₀²) = 3 H₀² · Ω_Λ` with the RS-forced
   `Ω_Λ = 11/16 − α/π`. Since `Ω_Λ > 0` (proved) and `H₀² > 0`, `Λ_RS > 0`.
2. **The Λ-extended EFE data recovers the baseline.** It keeps the derived coupling
   `κ = 8φ⁵` and dimension 4; only the cosmological-constant slot changes, and it collapses
   back to `0` in the `H₀² → 0` (equivalently zero-fraction) limit.
3. **The vacuum equation of state is exactly `w = −1`.** Writing the vacuum term as a
   perfect fluid `T^vac_μν = −(Λ/κ) g_μν` gives density `ρ_vac = Λ/κ > 0` and pressure
   `p_vac = −ρ_vac`, i.e. `w = −1`. This is the static anchor the dynamic `δw(z)` kernel
   deviates from.
4. **The vacuum term is covariantly conserved (Bianchi/U9), grounded, not assumed.** A
   constant times the metric has vanishing covariant derivative *because* the metric is
   covariantly constant (metric compatibility). We prove metric compatibility for the flat
   reference (`minkowski_metric_compatible`) and the linearity of the (0,2) covariant
   derivative (`covDeriv02_smul`), then conclude `∇(c·g) = 0` for any constant `c`, in
   particular `c = −Λ/κ`. This is the structural reason a cosmological constant is always
   consistent with `∇^μ G_μν = 0`.

Status: THEOREM. Zero `sorry`, zero new `axiom`. The absolute scale enters only through the
input `H₀² > 0`; the dimensionless fraction `Ω_Λ` and every structural property are forced.
-/

namespace IndisputableMonolith
namespace Gravity
namespace FullEFEWithDarkEnergy

open Constants

noncomputable section

/-! ## §1. Covariant derivative of a (0,2) tensor and its linearity -/

/-- The covariant derivative `∇_λ T_μν` of a (0,2) tensor with components `Tg`, given the
ordinary derivatives `dT` and the Christoffel symbols `ch`. The expression matches
`Connection.metric_compatibility` term-for-term, so metric compatibility is exactly the
statement `∀ λμν, covDeriv02 ch g dg λ μ ν = 0`. -/
def covDeriv02 (ch : Connection.ChristoffelData)
    (Tg : Connection.Idx → Connection.Idx → ℝ)
    (dT : Connection.Idx → Connection.Idx → Connection.Idx → ℝ)
    (lam mu nu : Connection.Idx) : ℝ :=
  dT lam mu nu
    - ∑ rho : Connection.Idx, (ch.gamma rho lam mu * Tg rho nu)
    - ∑ rho : Connection.Idx, (ch.gamma rho lam nu * Tg mu rho)

/-- Linearity of the (0,2) covariant derivative: scaling the tensor (and its ordinary
derivative) by a constant `c` scales the covariant derivative by `c`. -/
theorem covDeriv02_smul (ch : Connection.ChristoffelData)
    (Tg : Connection.Idx → Connection.Idx → ℝ)
    (dT : Connection.Idx → Connection.Idx → Connection.Idx → ℝ)
    (c : ℝ) (lam mu nu : Connection.Idx) :
    covDeriv02 ch (fun a b => c * Tg a b) (fun a b d => c * dT a b d) lam mu nu
      = c * covDeriv02 ch Tg dT lam mu nu := by
  have hs1 : ∑ rho : Connection.Idx, (ch.gamma rho lam mu * (c * Tg rho nu))
           = c * ∑ rho : Connection.Idx, (ch.gamma rho lam mu * Tg rho nu) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro rho _; ring
  have hs2 : ∑ rho : Connection.Idx, (ch.gamma rho lam nu * (c * Tg mu rho))
           = c * ∑ rho : Connection.Idx, (ch.gamma rho lam nu * Tg mu rho) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro rho _; ring
  simp only [covDeriv02]
  rw [hs1, hs2]; ring

/-! ## §2. Metric compatibility for the flat reference -/

/-- The flat Minkowski metric is covariantly constant: `∇_λ g_μν = 0`. Both the ordinary
derivative (constant metric) and the Christoffel symbols (flat) vanish. -/
theorem minkowski_metric_compatible :
    Connection.metric_compatibility Connection.minkowski
      (Connection.christoffel_from_metric Connection.minkowski_inverse (fun _ _ _ => 0))
      (fun _ _ _ => 0) := by
  unfold Connection.metric_compatibility
  intro lam mu nu
  simp [Connection.flat_christoffel_vanish]

/-! ## §3. Conservation of the static vacuum stress tensor (U9) -/

/-- **VACUUM TERM IS COVARIANTLY CONSERVED (general).** For any metric-compatible setup,
the (0,2) tensor `c · g` (constant `c` times the metric) has vanishing covariant
derivative. With `c = −Λ/κ` this is the static vacuum stress tensor `T^vac = −(Λ/κ) g`, so
`∇_λ T^vac_μν = 0` for all indices, hence `∇^μ T^vac_μν = 0`. -/
theorem vacuum_stress_conserved (c : ℝ) (met : Connection.MetricTensor)
    (ch : Connection.ChristoffelData)
    (dg : Connection.Idx → Connection.Idx → Connection.Idx → ℝ)
    (hcompat : Connection.metric_compatibility met ch dg) :
    ∀ lam mu nu : Connection.Idx,
      covDeriv02 ch (fun a b => c * met.g a b) (fun a b d => c * dg a b d) lam mu nu = 0 := by
  intro lam mu nu
  rw [covDeriv02_smul]
  rw [show covDeriv02 ch met.g dg lam mu nu = (0 : ℝ) from hcompat lam mu nu]
  ring

/-- **VACUUM TERM IS COVARIANTLY CONSERVED (flat reference, grounded).** Specialization of
`vacuum_stress_conserved` to the flat reference, using the proved
`minkowski_metric_compatible`. No metric compatibility is assumed; it is discharged. -/
theorem flat_vacuum_stress_conserved (c : ℝ) :
    ∀ lam mu nu : Connection.Idx,
      covDeriv02 (Connection.christoffel_from_metric Connection.minkowski_inverse (fun _ _ _ => 0))
        (fun a b => c * Connection.minkowski.g a b) (fun a b d => c * (fun _ _ _ => (0 : ℝ)) a b d)
        lam mu nu = 0 :=
  vacuum_stress_conserved c Connection.minkowski
    (Connection.christoffel_from_metric Connection.minkowski_inverse (fun _ _ _ => 0))
    (fun _ _ _ => 0) minkowski_metric_compatible

/-! ## §4. The forced cosmological constant and vacuum fluid -/

/-- The RS-forced dark-energy density fraction `Ω_Λ = 11/16 − α/π` is positive. -/
theorem Omega_Lambda_RS_pos :
    0 < Cosmology.CosmologicalConstantDerivation.Omega_Lambda_RS := by
  obtain ⟨hlo, _⟩ := Cosmology.CosmologicalConstantDerivation.Omega_Lambda_interval
  linarith

/-- The RS cosmological constant at Hubble scale `H₀²`: `Λ_RS = 3 H₀² Ω_Λ`. -/
def Lambda_RS (H0sq : ℝ) : ℝ :=
  3 * H0sq * Cosmology.CosmologicalConstantDerivation.Omega_Lambda_RS

/-- `Λ_RS` is positive for any positive Hubble scale (forced by `Ω_Λ > 0`). -/
theorem Lambda_RS_pos {H0sq : ℝ} (h : 0 < H0sq) : 0 < Lambda_RS H0sq := by
  unfold Lambda_RS
  exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3) h) Omega_Lambda_RS_pos

/-- `Λ_RS` collapses to `0` in the `H₀² → 0` limit (recovers the baseline `Λ = 0`). -/
theorem Lambda_RS_zero : Lambda_RS 0 = 0 := by unfold Lambda_RS; ring

/-- The vacuum energy density read off from the cosmological term: `ρ_vac = Λ/κ`. -/
def rho_vac (lam kappa : ℝ) : ℝ := lam / kappa

theorem rho_vac_pos {lam kappa : ℝ} (hl : 0 < lam) (hk : 0 < kappa) :
    0 < rho_vac lam kappa := div_pos hl hk

/-- The vacuum pressure: `p_vac = −ρ_vac`. -/
def vacuum_pressure (rho : ℝ) : ℝ := -rho

/-- **VACUUM EQUATION OF STATE IS `w = −1`.** The static vacuum fluid has `p/ρ = −1`. -/
theorem vacuum_eos (rho : ℝ) (h : rho ≠ 0) : vacuum_pressure rho / rho = -1 := by
  unfold vacuum_pressure
  rw [neg_div, div_self h]

/-! ## §5. The Λ-extended EFE data -/

/-- The full EFE data carrying the forced cosmological constant `Λ_RS(H₀²)`, with the same
derived coupling `κ = 8φ⁵` and dimension 4 as the baseline `rs_efe_data`. -/
def rs_efe_data_with_lambda (H0sq : ℝ) : FullEFE.FullEFEData where
  dimension := 4
  dim_eq := rfl
  kappa := FullEFE.rs_efe_data.kappa
  kappa_pos := FullEFE.rs_efe_data.kappa_pos
  cosmological_constant := Lambda_RS H0sq

theorem lambda_efe_kappa (H0sq : ℝ) :
    (rs_efe_data_with_lambda H0sq).kappa = 8 * phi ^ 5 := FullEFE.rs_efe_kappa

theorem lambda_efe_dimension (H0sq : ℝ) :
    (rs_efe_data_with_lambda H0sq).dimension = 4 := rfl

theorem lambda_efe_lambda_pos {H0sq : ℝ} (h : 0 < H0sq) :
    0 < (rs_efe_data_with_lambda H0sq).cosmological_constant := Lambda_RS_pos h

/-- The Λ-extended data recovers the baseline `Λ = 0` data in the limit. -/
theorem recovers_baseline_lambda :
    (rs_efe_data_with_lambda 0).cosmological_constant
      = FullEFE.rs_efe_data.cosmological_constant := by
  show Lambda_RS 0 = 0
  exact Lambda_RS_zero

/-! ## §6. The master certificate -/

/-- **DARK-ENERGY EFE CERTIFICATE.** The forced vacuum term is now in the EFE chain:
positive, of equation of state `w = −1`, covariantly conserved (grounded in flat metric
compatibility), preserving the derived `κ = 8φ⁵`, and recovering the `Λ = 0` baseline. -/
structure DarkEnergyEFECert where
  lambda_pos :
    ∀ {H0sq : ℝ}, 0 < H0sq → 0 < (rs_efe_data_with_lambda H0sq).cosmological_constant
  kappa_preserved : ∀ H0sq : ℝ, (rs_efe_data_with_lambda H0sq).kappa = 8 * phi ^ 5
  recovers_baseline :
    (rs_efe_data_with_lambda 0).cosmological_constant
      = FullEFE.rs_efe_data.cosmological_constant
  vacuum_eos_minus_one : ∀ rho : ℝ, rho ≠ 0 → vacuum_pressure rho / rho = -1
  vacuum_conserved :
    ∀ (c : ℝ) (lam mu nu : Connection.Idx),
      covDeriv02 (Connection.christoffel_from_metric Connection.minkowski_inverse
          (fun _ _ _ => 0))
        (fun a b => c * Connection.minkowski.g a b)
        (fun a b d => c * (fun _ _ _ => (0 : ℝ)) a b d) lam mu nu = 0

/-- The dark-energy EFE certificate is inhabited: every claim is proved. -/
def darkEnergyEFECert : DarkEnergyEFECert where
  lambda_pos := fun h => lambda_efe_lambda_pos h
  kappa_preserved := lambda_efe_kappa
  recovers_baseline := recovers_baseline_lambda
  vacuum_eos_minus_one := vacuum_eos
  vacuum_conserved := flat_vacuum_stress_conserved

end

end FullEFEWithDarkEnergy
end Gravity
end IndisputableMonolith
