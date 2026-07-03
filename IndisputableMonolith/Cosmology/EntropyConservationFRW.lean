import Mathlib
import IndisputableMonolith.Cosmology.NeutrinoDilution

/-!
# Entropy Conservation from the FRW Continuity Equation

**Status: THEOREM (this module, 0 sorry).**

This module discharges the two MODEL hypotheses that `NeutrinoDilution` was
stated over.  There, `(T_ν/T_γ)³ = 4/11` and `g*s = 43/11` were derived from

* **adiabatic expansion** — comoving entropy `s·a³` of the coupled sector is
  conserved through e± annihilation, and
* **free streaming** — the decoupled neutrino temperature redshifts as `1/a`
  (`a·T_ν` constant),

both *assumed*.  Here both are **derived**:

## The derivation chain

* **§0 (`continuity_from_friedmann`).** The FRW continuity equation
  `a·ρ′ = −3a′(ρ+p)` is itself not an axiom: it is forced by the two
  Friedmann equations `a′² = (8πG/3)ρa²` and `a″a = −(4πG/3)(ρ+3p)a²`
  (differentiate the first, substitute the second, cancel `(8πG/3)a²`).
  This is the Bianchi-identity compatibility of the Einstein equations,
  done with `HasDerivAt` and no division.

* **§1 (`comoving_entropy_conserved`).** For any fluid in local equilibrium —
  Euler relation `T·s = ρ + p` (zero chemical potential) and Gibbs–Duhem
  `p′ = s·T′` — the continuity equation forces `d/dt (s·a³) = 0`:
  differentiating Euler and applying Gibbs–Duhem gives `T·s′ = ρ′`;
  continuity then gives `T·(a·s′ + 3a′·s) = 0`, and `T ≠ 0` cancels.
  Comoving entropy conservation is a *theorem*, not a postulate.

* **§2 (`radiation_aT_conserved`).** For a decoupled radiation gas
  (`ρ = αT⁴`, `p = ρ/3`) the continuity equation alone forces
  `d/dt (a·T) = 0`: the free-streaming redshift law is a *theorem*.
  The equilibrium identities are automatic for radiation
  (`radiation_euler`, `radiation_gibbs_duhem`), so no extra physics enters.

* **§3 (global constancy).** Pointwise vanishing derivatives upgrade to
  `s(t₁)a(t₁)³ = s(t₂)a(t₂)³` and `a(t₁)T(t₁) = a(t₂)T(t₂)` via the mean
  value theorem (`is_const_of_deriv_eq_zero`).

* **§4 (capstones).** Feeding these into
  `NeutrinoDilution.dilution_from_entropy_conservation`:
  `(T_ν/T_γ)³ = 4/11` and the present-day entropy `(2π²/45)·(43/11)·T_γ³`
  now follow from the continuity equations plus equilibrium thermodynamics —
  the former MODEL hypotheses are gone from the chain.

## What remains MODEL upstream

The Friedmann equations (the GR input), local equilibrium of the coupled
sector (Euler + Gibbs–Duhem as named identities), sector decoupling (the
neutrino gas satisfies its own continuity equation — no energy exchange),
the boundary identifications (plasma dof before/after annihilation, shared
temperature at decoupling), and instantaneous decoupling.  All the
*dynamics* — that expansion is adiabatic and that free radiation redshifts
as `1/a` — is now derived.

Reference: Kolb & Turner, *The Early Universe*, §3.3–3.4; Weinberg,
*Cosmology*, §1.1 (Bianchi identity and the continuity equation).
-/

namespace IndisputableMonolith
namespace Cosmology
namespace EntropyConservationFRW

open Real

/-! ## §0. The continuity equation from the Friedmann equations -/

/-- **THEOREM (continuity from Friedmann).** The FRW continuity equation
`a·ρ′ = −3a′(ρ+p)` follows from the two Friedmann equations

* I:  `a′² = (8πG/3)·ρ·a²`  (holding along the evolution), and
* II: `a″·a = −(4πG/3)·(ρ+3p)·a²`  (at the given time),

by differentiating I and eliminating `a″` with II.  No division is used;
`G ≠ 0` and `a(t) ≠ 0` cancel the common factor `(8πG/3)·a²`. -/
theorem continuity_from_friedmann
    {a ρ p : ℝ → ℝ} {a' : ℝ → ℝ} {a'' ρ' G t : ℝ}
    (hG : G ≠ 0) (hat : a t ≠ 0)
    (had : ∀ u, HasDerivAt a (a' u) u)
    (ha'd : HasDerivAt a' a'' t)
    (hρd : HasDerivAt ρ ρ' t)
    (hF1 : ∀ u, a' u ^ 2 = 8 * π * G / 3 * (ρ u * a u ^ 2))
    (hF2 : a'' * a t = -(4 * π * G / 3) * ((ρ t + 3 * p t) * a t ^ 2)) :
    a t * ρ' = -3 * a' t * (ρ t + p t) := by
  -- Differentiate the first Friedmann equation.
  have hL : HasDerivAt (fun u => a' u ^ 2) (2 * a' t * a'') t := by
    simpa using ha'd.fun_pow 2
  have hpow : HasDerivAt (fun u => a u ^ 2) (2 * a t * a' t) t := by
    simpa using (had t).fun_pow 2
  have hprod : HasDerivAt (fun u => ρ u * a u ^ 2)
      (ρ' * a t ^ 2 + ρ t * (2 * a t * a' t)) t := hρd.mul hpow
  have hR : HasDerivAt (fun u => 8 * π * G / 3 * (ρ u * a u ^ 2))
      (8 * π * G / 3 * (ρ' * a t ^ 2 + ρ t * (2 * a t * a' t))) t :=
    hprod.const_mul (8 * π * G / 3)
  have hfun : (fun u => a' u ^ 2)
      = fun u => 8 * π * G / 3 * (ρ u * a u ^ 2) := funext hF1
  rw [hfun] at hL
  have heq : 2 * a' t * a''
      = 8 * π * G / 3 * (ρ' * a t ^ 2 + ρ t * (2 * a t * a' t)) :=
    hL.unique hR
  -- Eliminate a″ with the second Friedmann equation; cancel (8πG/3)·a².
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hC : (8 * π * G / 3 : ℝ) ≠ 0 := by
    apply div_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)
    exact mul_ne_zero (mul_ne_zero (by norm_num) hπ) hG
  have hkey : 8 * π * G / 3 * a t ^ 2
      * (a t * ρ' + 3 * a' t * (ρ t + p t)) = 0 := by
    linear_combination 2 * a' t * hF2 - a t * heq
  have hcancel :=
    (mul_eq_zero.mp hkey).resolve_left (mul_ne_zero hC (pow_ne_zero 2 hat))
  linarith

/-! ## §1. Comoving entropy conservation for an equilibrium fluid -/

/-- **THEOREM (adiabatic expansion derived).** For a fluid in local
equilibrium — Euler relation `T·s = ρ + p` along the evolution and
Gibbs–Duhem `p′ = s·T′` at the given time — the FRW continuity equation
`a·ρ′ = −3a′(ρ+p)` forces `d/dt (s·a³) = 0`.

Differentiating the Euler relation gives `T′s + Ts′ = ρ′ + p′`; Gibbs–Duhem
removes the `T′` terms, leaving `T·s′ = ρ′`; continuity plus Euler then give
`T·(a·s′ + 3a′·s) = 0`, and `T ≠ 0` cancels. -/
theorem comoving_entropy_conserved
    {ρ p s T a : ℝ → ℝ} {ρ' p' s' a' T' t : ℝ}
    (hTt : T t ≠ 0)
    (hρ : HasDerivAt ρ ρ' t) (hp : HasDerivAt p p' t)
    (hs : HasDerivAt s s' t) (ha : HasDerivAt a a' t)
    (hT : HasDerivAt T T' t)
    (hEuler : ∀ u, T u * s u = ρ u + p u)
    (hGD : p' = s t * T')
    (hcont : a t * ρ' = -3 * a' * (ρ t + p t)) :
    HasDerivAt (fun u => s u * a u ^ 3) 0 t := by
  -- Differentiate the Euler relation.
  have hTs : HasDerivAt (fun u => T u * s u) (T' * s t + T t * s') t :=
    hT.mul hs
  have hρp : HasDerivAt (fun u => ρ u + p u) (ρ' + p') t := hρ.add hp
  have hfun : (fun u => T u * s u) = fun u => ρ u + p u := funext hEuler
  rw [hfun] at hTs
  have hdiff : T' * s t + T t * s' = ρ' + p' := hTs.unique hρp
  -- Gibbs–Duhem kills the T′ terms: T·s′ = ρ′.
  have hTs' : T t * s' = ρ' := by linear_combination hdiff + hGD
  -- Continuity + Euler force a·s′ + 3a′·s = 0.
  have hkey : a t * s' + 3 * a' * s t = 0 := by
    have h1 : T t * (a t * s' + 3 * a' * s t) = 0 := by
      linear_combination a t * hTs' + 3 * a' * hEuler t + hcont
    exact (mul_eq_zero.mp h1).resolve_left hTt
  -- Assemble the product derivative of s·a³.
  have hpow : HasDerivAt (fun u => a u ^ 3) (3 * a t ^ 2 * a') t := by
    simpa using ha.fun_pow 3
  have hprod : HasDerivAt (fun u => s u * a u ^ 3)
      (s' * a t ^ 3 + s t * (3 * a t ^ 2 * a')) t := hs.mul hpow
  have hzero : s' * a t ^ 3 + s t * (3 * a t ^ 2 * a') = 0 := by
    linear_combination a t ^ 2 * hkey
  rw [hzero] at hprod
  exact hprod

/-! ## §2. Free streaming: a·T conserved for a decoupled radiation gas -/

/-- **THEOREM (free streaming derived).** For a decoupled radiation gas with
`ρ = αT⁴` and `p = ρ/3`, the FRW continuity equation alone forces
`d/dt (a·T) = 0`: the redshift law `T ∝ 1/a` is not an assumption.
Continuity reads `4αT³·(a·T′ + a′·T) = 0` and `α ≠ 0`, `T ≠ 0` cancel. -/
theorem radiation_aT_conserved
    {T a : ℝ → ℝ} {T' a' ρ' t α : ℝ}
    (hα : α ≠ 0) (hTt : T t ≠ 0)
    (hT : HasDerivAt T T' t) (ha : HasDerivAt a a' t)
    (hρ : HasDerivAt (fun u => α * T u ^ 4) ρ' t)
    (hcont : a t * ρ' = -3 * a' * (α * T t ^ 4 + α * T t ^ 4 / 3)) :
    HasDerivAt (fun u => a u * T u) 0 t := by
  -- The density derivative is 4αT³T′ by uniqueness.
  have hpow : HasDerivAt (fun u => T u ^ 4) (4 * T t ^ 3 * T') t := by
    simpa using hT.fun_pow 4
  have h4 : HasDerivAt (fun u => α * T u ^ 4) (α * (4 * T t ^ 3 * T')) t :=
    hpow.const_mul α
  have hρval : ρ' = α * (4 * T t ^ 3 * T') := hρ.unique h4
  -- Continuity collapses to 4αT³·(a′T + aT′) = 0.
  have hkey : a' * T t + a t * T' = 0 := by
    have h1 : 4 * α * T t ^ 3 * (a' * T t + a t * T') = 0 := by
      rw [hρval] at hcont
      linear_combination hcont
    have hne : (4 * α * T t ^ 3 : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hα) (pow_ne_zero 3 hTt)
    exact (mul_eq_zero.mp h1).resolve_left hne
  have hprod : HasDerivAt (fun u => a u * T u) (a' * T t + a t * T') t :=
    ha.mul hT
  rw [hkey] at hprod
  exact hprod

/-- For radiation (`ρ = αT⁴`, `p = ρ/3`, `s = (4/3)αT³`) the Euler relation
`T·s = ρ + p` is an algebraic identity — no extra equilibrium input. -/
theorem radiation_euler (α T : ℝ) :
    T * (4 / 3 * α * T ^ 3) = α * T ^ 4 + α * T ^ 4 / 3 := by ring

/-- For radiation the Gibbs–Duhem relation `p′ = s·T′` is automatic:
`d/dt (αT⁴/3) = (4/3)αT³·T′`. -/
theorem radiation_gibbs_duhem {T : ℝ → ℝ} {T' t α : ℝ}
    (hT : HasDerivAt T T' t) :
    HasDerivAt (fun u => α * T u ^ 4 / 3) (4 / 3 * α * T t ^ 3 * T') t := by
  have hpow : HasDerivAt (fun u => T u ^ 4) (4 * T t ^ 3 * T') t := by
    simpa using hT.fun_pow 4
  have h := (hpow.const_mul α).div_const 3
  have hval : α * (4 * T t ^ 3 * T') / 3 = 4 / 3 * α * T t ^ 3 * T' := by
    ring
  rw [hval] at h
  exact h

/-- Composition check: Friedmann I + II plus the equilibrium identities give
comoving entropy conservation directly (continuity is not assumed). -/
theorem entropy_conserved_from_friedmann
    {ρ p s T a : ℝ → ℝ} {a' : ℝ → ℝ} {ρ' p' s' T' a'' G t : ℝ}
    (hG : G ≠ 0) (hat : a t ≠ 0) (hTt : T t ≠ 0)
    (had : ∀ u, HasDerivAt a (a' u) u)
    (ha'd : HasDerivAt a' a'' t)
    (hρd : HasDerivAt ρ ρ' t) (hpd : HasDerivAt p p' t)
    (hsd : HasDerivAt s s' t) (hTd : HasDerivAt T T' t)
    (hF1 : ∀ u, a' u ^ 2 = 8 * π * G / 3 * (ρ u * a u ^ 2))
    (hF2 : a'' * a t = -(4 * π * G / 3) * ((ρ t + 3 * p t) * a t ^ 2))
    (hEuler : ∀ u, T u * s u = ρ u + p u)
    (hGD : p' = s t * T') :
    HasDerivAt (fun u => s u * a u ^ 3) 0 t :=
  comoving_entropy_conserved hTt hρd hpd hsd (had t) hTd hEuler hGD
    (continuity_from_friedmann hG hat had ha'd hρd hF1 hF2)

/-! ## §3. Global constancy from pointwise conservation -/

/-- **Global adiabaticity.** If the equilibrium fluid satisfies the
continuity equation at every time, comoving entropy is the same at any two
times: `s(t₁)·a(t₁)³ = s(t₂)·a(t₂)³`. -/
theorem comoving_entropy_constant
    {ρ p s T a : ℝ → ℝ} {ρ' p' s' a' T' : ℝ → ℝ}
    (hTt : ∀ t, T t ≠ 0)
    (hρ : ∀ t, HasDerivAt ρ (ρ' t) t) (hp : ∀ t, HasDerivAt p (p' t) t)
    (hs : ∀ t, HasDerivAt s (s' t) t) (ha : ∀ t, HasDerivAt a (a' t) t)
    (hT : ∀ t, HasDerivAt T (T' t) t)
    (hEuler : ∀ u, T u * s u = ρ u + p u)
    (hGD : ∀ t, p' t = s t * T' t)
    (hcont : ∀ t, a t * ρ' t = -3 * a' t * (ρ t + p t))
    (t₁ t₂ : ℝ) :
    s t₁ * a t₁ ^ 3 = s t₂ * a t₂ ^ 3 := by
  have h0 : ∀ t, HasDerivAt (fun u => s u * a u ^ 3) 0 t := fun t =>
    comoving_entropy_conserved (hTt t) (hρ t) (hp t) (hs t) (ha t) (hT t)
      hEuler (hGD t) (hcont t)
  exact is_const_of_deriv_eq_zero (fun t => (h0 t).differentiableAt)
    (fun t => (h0 t).deriv) t₁ t₂

/-- **Global free streaming.** If the decoupled radiation gas satisfies its
continuity equation at every time, `a·T` is the same at any two times. -/
theorem radiation_aT_constant
    {T a : ℝ → ℝ} {T' a' ρ' : ℝ → ℝ} {α : ℝ}
    (hα : α ≠ 0) (hTt : ∀ t, T t ≠ 0)
    (hT : ∀ t, HasDerivAt T (T' t) t) (ha : ∀ t, HasDerivAt a (a' t) t)
    (hρ : ∀ t, HasDerivAt (fun u => α * T u ^ 4) (ρ' t) t)
    (hcont : ∀ t, a t * ρ' t
        = -3 * a' t * (α * T t ^ 4 + α * T t ^ 4 / 3))
    (t₁ t₂ : ℝ) :
    a t₁ * T t₁ = a t₂ * T t₂ := by
  have h0 : ∀ t, HasDerivAt (fun u => a u * T u) 0 t := fun t =>
    radiation_aT_conserved hα (hTt t) (hT t) (ha t) (hρ t) (hcont t)
  exact is_const_of_deriv_eq_zero (fun t => (h0 t).differentiableAt)
    (fun t => (h0 t).deriv) t₁ t₂

/-! ## §4. Capstones: the dilution and g*s from the continuity equations -/

/-- **CAPSTONE (dilution from FRW dynamics).** Replace the two MODEL
hypotheses of `NeutrinoDilution.dilution_from_entropy_conservation` by
physics: the coupled sector is an equilibrium fluid (Euler + Gibbs–Duhem)
satisfying the FRW continuity equation, and the decoupled neutrino gas is
free radiation (`ρ_ν = α_ν T_ν⁴`) satisfying its own continuity equation.
Then comoving entropy conservation and the `1/a` redshift law are *derived*
(§§1–3), and with the boundary data (plasma dof `2+4 → 2` across e±
annihilation, shared temperature at decoupling) they force

  `(T_ν/T_γ)³ = 4/11`. -/
theorem dilution_from_frw
    {ρ p s T a Tν : ℝ → ℝ} {ρ' p' s' a' T' Tν' ρν' : ℝ → ℝ}
    {t₁ t₂ : ℝ} {T₁ Tγ αν : ℝ}
    (hTt : ∀ t, T t ≠ 0) (hαν : αν ≠ 0) (hTνt : ∀ t, Tν t ≠ 0)
    (ha₂ : a t₂ ≠ 0) (hTγ : Tγ ≠ 0)
    (hρ : ∀ t, HasDerivAt ρ (ρ' t) t) (hp : ∀ t, HasDerivAt p (p' t) t)
    (hs : ∀ t, HasDerivAt s (s' t) t) (ha : ∀ t, HasDerivAt a (a' t) t)
    (hT : ∀ t, HasDerivAt T (T' t) t)
    (hTν : ∀ t, HasDerivAt Tν (Tν' t) t)
    (hρν : ∀ t, HasDerivAt (fun u => αν * Tν u ^ 4) (ρν' t) t)
    (hEuler : ∀ u, T u * s u = ρ u + p u)
    (hGD : ∀ t, p' t = s t * T' t)
    (hcont : ∀ t, a t * ρ' t = -3 * a' t * (ρ t + p t))
    (hcontν : ∀ t, a t * ρν' t
        = -3 * a' t * (αν * Tν t ^ 4 + αν * Tν t ^ 4 / 3))
    (hbefore : s t₁ = NeutrinoDilution.radiationEntropy 2 4 T₁)
    (hafter : s t₂ = NeutrinoDilution.radiationEntropy 2 0 Tγ)
    (hshare : Tν t₁ = T₁) :
    (Tν t₂ / Tγ) ^ 3 = 4 / 11 := by
  -- Adiabaticity of the coupled sector (derived, §§1, 3).
  have hcons : NeutrinoDilution.radiationEntropy 2 4 T₁ * a t₁ ^ 3
      = NeutrinoDilution.radiationEntropy 2 0 Tγ * a t₂ ^ 3 := by
    have h := comoving_entropy_constant hTt hρ hp hs ha hT hEuler hGD hcont t₁ t₂
    rw [hbefore, hafter] at h
    exact h
  -- Free streaming of the neutrino sector (derived, §§2, 3).
  have hfree : a t₂ * Tν t₂ = a t₁ * T₁ := by
    have h := radiation_aT_constant hαν hTνt hTν ha hρν hcontν t₂ t₁
    rw [hshare] at h
    exact h
  exact NeutrinoDilution.dilution_from_entropy_conservation ha₂ hTγ hcons hfree

/-- **CAPSTONE (g*s from FRW dynamics).** With the same physics inputs, the
present-day entropy density (photons at `T_γ` + 6 fermionic neutrino dof at
the diluted `T_ν`) equals `(2π²/45)·gStarS·T_γ³` with
`EntropyPerPhoton.gStarS = 43/11`: the effective entropy dof entering the
η_B dynamical prefactor is forced by the continuity equations. -/
theorem gStarS_from_frw
    {ρ p s T a Tν : ℝ → ℝ} {ρ' p' s' a' T' Tν' ρν' : ℝ → ℝ}
    {t₁ t₂ : ℝ} {T₁ Tγ αν : ℝ}
    (hTt : ∀ t, T t ≠ 0) (hαν : αν ≠ 0) (hTνt : ∀ t, Tν t ≠ 0)
    (ha₂ : a t₂ ≠ 0) (hTγ : Tγ ≠ 0)
    (hρ : ∀ t, HasDerivAt ρ (ρ' t) t) (hp : ∀ t, HasDerivAt p (p' t) t)
    (hs : ∀ t, HasDerivAt s (s' t) t) (ha : ∀ t, HasDerivAt a (a' t) t)
    (hT : ∀ t, HasDerivAt T (T' t) t)
    (hTν : ∀ t, HasDerivAt Tν (Tν' t) t)
    (hρν : ∀ t, HasDerivAt (fun u => αν * Tν u ^ 4) (ρν' t) t)
    (hEuler : ∀ u, T u * s u = ρ u + p u)
    (hGD : ∀ t, p' t = s t * T' t)
    (hcont : ∀ t, a t * ρ' t = -3 * a' t * (ρ t + p t))
    (hcontν : ∀ t, a t * ρν' t
        = -3 * a' t * (αν * Tν t ^ 4 + αν * Tν t ^ 4 / 3))
    (hbefore : s t₁ = NeutrinoDilution.radiationEntropy 2 4 T₁)
    (hafter : s t₂ = NeutrinoDilution.radiationEntropy 2 0 Tγ)
    (hshare : Tν t₁ = T₁) :
    NeutrinoDilution.radiationEntropy 2 0 Tγ
        + NeutrinoDilution.radiationEntropy 0 6 (Tν t₂)
      = 2 * π ^ 2 / 45 * ((EntropyPerPhoton.gStarS : ℚ) : ℝ) * Tγ ^ 3 :=
  NeutrinoDilution.total_entropy_eq_gStarS hTγ
    (dilution_from_frw hTt hαν hTνt ha₂ hTγ hρ hp hs ha hT hTν hρν
      hEuler hGD hcont hcontν hbefore hafter hshare)

end EntropyConservationFRW
end Cosmology
end IndisputableMonolith
