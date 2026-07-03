import Mathlib
import IndisputableMonolith.Cosmology.RadiationEntropyRelation
import IndisputableMonolith.Cosmology.EntropyPerPhoton

/-!
# Neutrino Dilution (Tν/Tγ)³ = 4/11 and g*s = 43/11 from Entropy Conservation

**Status: THEOREM (this module, 0 sorry) over two named MODEL hypotheses —
both now DISCHARGED downstream in `EntropyConservationFRW` (comoving entropy
conservation and the `1/a` redshift law are derived there from the FRW
continuity equation, itself derived from the two Friedmann equations, plus
the equilibrium identities; see `dilution_from_frw`).**

This module closes the next MODEL element in the η_B chain.  Up to now the
neutrino dilution factor `(T_ν/T_γ)³ = 4/11` and the effective entropy dof
`g*s = 43/11` lived in `EntropyPerPhoton` as bare rational arithmetic
(`dilutionCubed_eq`, `gStarS_eq`): the *ratio* `gAfter/gBefore` was defined,
not derived.  Here both are **derived from entropy conservation through
e± annihilation**, with the plasma entropy density built from the
integrals proven in `RadiationEntropyRelation` (the entropy functional
`σ(x) = x²[±(1±f)ln(1±f) − f ln f]`, whose closed forms `4π⁴/45` and
`7π⁴/90` were derived from the Mercator/Mellin machinery — the `4/3` and
`7/8` factors never assumed).

## The physical derivation

* `radiationEntropy gB gF T` is the entropy density of a relativistic plasma
  with `gB` bosonic and `gF` fermionic internal dof at temperature `T`:
  each species contributes `(g/2π²)·T³·∫σ`, with `∫σ_B = 4π⁴/45` and
  `∫σ_F = 7π⁴/90` **derived**.  The single structural theorem
  `radiationEntropy_eq` collapses this to `(2π²/45)·(gB + (7/8)·gF)·T³`,
  where the `7/8` is the *entropy-layer* fermion weight.

* **MODEL hypothesis 1 (adiabatic expansion):** comoving entropy of the
  electromagnetically coupled sector is conserved through e± annihilation,
  `s(before)·a₁³ = s(after)·a₂³`.

* **MODEL hypothesis 2 (free streaming):** neutrinos decouple before
  annihilation sharing the plasma temperature, and their temperature then
  redshifts as `1/a`, i.e. `a·T_ν` is constant: `a₂·T_ν = a₁·T₁`.

* **THEOREM (`dilution_from_entropy_conservation`):** these two hypotheses
  force `(T_ν/T_γ)³ = 4/11`.  The `11/2 → 2` drop in coupled dof is not an
  input: it is `radiationEntropy 2 4 T` vs `radiationEntropy 2 0 T` with
  the 7/8 entropy weight emerging from the derived integrals.

* **THEOREM (`gStarS_from_conservation`):** the present-day total entropy
  (photons at `T_γ` + 6 fermionic neutrino dof at `T_ν`) is then exactly
  `(2π²/45)·(43/11)·T_γ³` — the effective dof `g*s = 43/11` of
  `EntropyPerPhoton.gStarS` is derived, not assumed.

## What remains MODEL upstream

The particle content (2 photon polarizations, 4 e± dof, 6 neutrino dof),
instantaneous decoupling, and the two hypotheses above.  All statistical
mechanics (the 7/8 entropy weight, the 4/3 law, the 2π²/45 coefficient, and
the 4/11 and 43/11 ratios *given* the hypotheses) is THEOREM.

Reference: Kolb & Turner, *The Early Universe*, §3.3–3.4.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace NeutrinoDilution

open Real MeasureTheory Set

/-! ## §1. The plasma entropy density from the derived entropy functional -/

/-- Entropy density of a relativistic plasma with `gB` bosonic and `gF`
fermionic internal degrees of freedom at temperature `T`, built directly
from the entropy-functional integrals of `RadiationEntropyRelation`:
each species contributes `(g/2π²)·T³·∫σ`. -/
noncomputable def radiationEntropy (gB gF T : ℝ) : ℝ :=
  gB / (2 * π ^ 2) * T ^ 3
      * (∫ t in Ioi (0 : ℝ), RadiationEntropyRelation.boseEntropyIntegrand t)
    + gF / (2 * π ^ 2) * T ^ 3
      * (∫ t in Ioi (0 : ℝ), RadiationEntropyRelation.fermiEntropyIntegrand t)

/-- **THEOREM (structural form).** The plasma entropy density collapses to
`(2π²/45)·(gB + (7/8)·gF)·T³`, with the `2π²/45` coefficient and the `7/8`
entropy weight both coming from the derived integrals `∫σ_B = 4π⁴/45`,
`∫σ_F = 7π⁴/90` — neither is assumed. -/
theorem radiationEntropy_eq (gB gF T : ℝ) :
    radiationEntropy gB gF T = 2 * π ^ 2 / 45 * (gB + 7 / 8 * gF) * T ^ 3 := by
  unfold radiationEntropy
  rw [RadiationEntropyRelation.bose_entropy_integral_value,
    RadiationEntropyRelation.fermi_entropy_integral_value]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The photon–electron plasma before e± annihilation (2 bosonic + 4
fermionic dof) carries exactly `gBefore = 11/2` effective entropy dof: the
`11/2` of `EntropyPerPhoton.gBefore` is the functional-layer value. -/
theorem plasma_before_eq_gBefore (T : ℝ) :
    radiationEntropy ((EntropyPerPhoton.gPhoton : ℚ) : ℝ)
        ((EntropyPerPhoton.gElectron : ℚ) : ℝ) T
      = 2 * π ^ 2 / 45 * ((EntropyPerPhoton.gBefore : ℚ) : ℝ) * T ^ 3 := by
  rw [radiationEntropy_eq]
  unfold EntropyPerPhoton.gBefore EntropyPerPhoton.gPhoton
    EntropyPerPhoton.gElectron EntropyPerPhoton.fermionWeight
  push_cast
  ring

/-! ## §2. The dilution theorem -/

/-- **THEOREM (neutrino dilution from entropy conservation).**
If comoving entropy of the coupled photon–e± sector is conserved through
annihilation (`radiationEntropy 2 4 T₁ · a₁³ = radiationEntropy 2 0 T_γ · a₂³`)
and decoupled neutrinos redshift freely from the shared pre-annihilation
temperature (`a₂·T_ν = a₁·T₁`), then

  `(T_ν/T_γ)³ = 4/11`.

The dof drop `11/2 → 2` is not an input: it is produced by the derived
entropy-functional integrals inside `radiationEntropy_eq`. -/
theorem dilution_from_entropy_conservation
    {a₁ a₂ T₁ Tγ Tν : ℝ} (ha₂ : a₂ ≠ 0) (hTγ : Tγ ≠ 0)
    (hcons : radiationEntropy 2 4 T₁ * a₁ ^ 3 = radiationEntropy 2 0 Tγ * a₂ ^ 3)
    (hfree : a₂ * Tν = a₁ * T₁) :
    (Tν / Tγ) ^ 3 = 4 / 11 := by
  rw [radiationEntropy_eq, radiationEntropy_eq] at hcons
  have hC : (2 * π ^ 2 / 45 : ℝ) ≠ 0 := by positivity
  have hkey : (11 / 2 : ℝ) * (a₁ * T₁) ^ 3 = 2 * (a₂ * Tγ) ^ 3 := by
    have h : (2 * π ^ 2 / 45 : ℝ) * ((11 / 2) * (a₁ * T₁) ^ 3)
        = (2 * π ^ 2 / 45) * (2 * (a₂ * Tγ) ^ 3) := by
      linear_combination hcons
    exact mul_left_cancel₀ hC h
  rw [← hfree] at hkey
  have ha₂3 : (a₂ : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 ha₂
  have hTT : (11 / 2 : ℝ) * Tν ^ 3 = 2 * Tγ ^ 3 := by
    have h : a₂ ^ 3 * ((11 / 2 : ℝ) * Tν ^ 3) = a₂ ^ 3 * (2 * Tγ ^ 3) := by
      linear_combination hkey
    exact mul_left_cancel₀ ha₂3 h
  rw [div_pow, div_eq_iff (pow_ne_zero 3 hTγ)]
  linarith

/-- **THEOREM (provenance).** The physically derived dilution equals the
arithmetic `EntropyPerPhoton.dilutionCubed = gAfter/gBefore`: the rational
definition upstream is the value forced by entropy conservation. -/
theorem dilution_eq_dilutionCubed
    {a₁ a₂ T₁ Tγ Tν : ℝ} (ha₂ : a₂ ≠ 0) (hTγ : Tγ ≠ 0)
    (hcons : radiationEntropy 2 4 T₁ * a₁ ^ 3 = radiationEntropy 2 0 Tγ * a₂ ^ 3)
    (hfree : a₂ * Tν = a₁ * T₁) :
    (Tν / Tγ) ^ 3 = ((EntropyPerPhoton.dilutionCubed : ℚ) : ℝ) := by
  have h4 : ((EntropyPerPhoton.dilutionCubed : ℚ) : ℝ) = 4 / 11 := by
    rw [EntropyPerPhoton.dilutionCubed_eq]
    norm_num
  rw [h4]
  exact dilution_from_entropy_conservation ha₂ hTγ hcons hfree

/-! ## §3. g*s = 43/11 from the diluted neutrino sector -/

/-- **THEOREM (present-day entropy).** Photons at `T_γ` plus 6 fermionic
neutrino dof at `T_ν` with `(T_ν/T_γ)³ = 4/11` carry total entropy
`(2π²/45)·(43/11)·T_γ³`. -/
theorem total_entropy_today
    {Tγ Tν : ℝ} (hTγ : Tγ ≠ 0) (hdil : (Tν / Tγ) ^ 3 = 4 / 11) :
    radiationEntropy 2 0 Tγ + radiationEntropy 0 6 Tν
      = 2 * π ^ 2 / 45 * (43 / 11) * Tγ ^ 3 := by
  rw [radiationEntropy_eq, radiationEntropy_eq]
  have hTν3 : Tν ^ 3 = 4 / 11 * Tγ ^ 3 := by
    rw [div_pow, div_eq_iff (pow_ne_zero 3 hTγ)] at hdil
    linarith
  rw [hTν3]
  ring

/-- **THEOREM (provenance).** The present-day total equals
`(2π²/45)·gStarS·T_γ³` with `EntropyPerPhoton.gStarS`: the `43/11` upstream
is the value forced by the diluted neutrino sector. -/
theorem total_entropy_eq_gStarS
    {Tγ Tν : ℝ} (hTγ : Tγ ≠ 0) (hdil : (Tν / Tγ) ^ 3 = 4 / 11) :
    radiationEntropy 2 0 Tγ + radiationEntropy 0 6 Tν
      = 2 * π ^ 2 / 45 * ((EntropyPerPhoton.gStarS : ℚ) : ℝ) * Tγ ^ 3 := by
  have h : ((EntropyPerPhoton.gStarS : ℚ) : ℝ) = 43 / 11 := by
    rw [EntropyPerPhoton.gStarS_eq]
    norm_num
  rw [h]
  exact total_entropy_today hTγ hdil

/-- **CAPSTONE.** Entropy conservation through e± annihilation plus free
neutrino streaming force the present-day entropy density to be
`(2π²/45)·(43/11)·T_γ³`: the effective dof `g*s = 43/11` entering
`entropyPerPhoton = π⁴·g*s/(45·ζ(3))` (and hence the η_B dynamical
prefactor) is **derived** from the entropy functional, not assumed. -/
theorem gStarS_from_conservation
    {a₁ a₂ T₁ Tγ Tν : ℝ} (ha₂ : a₂ ≠ 0) (hTγ : Tγ ≠ 0)
    (hcons : radiationEntropy 2 4 T₁ * a₁ ^ 3 = radiationEntropy 2 0 Tγ * a₂ ^ 3)
    (hfree : a₂ * Tν = a₁ * T₁) :
    radiationEntropy 2 0 Tγ + radiationEntropy 0 6 Tν
      = 2 * π ^ 2 / 45 * ((EntropyPerPhoton.gStarS : ℚ) : ℝ) * Tγ ^ 3 :=
  total_entropy_eq_gStarS hTγ
    (dilution_from_entropy_conservation ha₂ hTγ hcons hfree)

end NeutrinoDilution
end Cosmology
end IndisputableMonolith
