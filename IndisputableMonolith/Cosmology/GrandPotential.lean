import Mathlib
import IndisputableMonolith.Cosmology.RadiationEntropyRelation
import IndisputableMonolith.Cosmology.FermionWeightIntegral
import IndisputableMonolith.Cosmology.EntropyConservationFRW

/-!
# Euler and Gibbs–Duhem from the Grand Potential

**Status: THEOREM (this module, 0 sorry).**

`EntropyConservationFRW` derived comoving entropy conservation from the FRW
continuity equation *given* two named equilibrium identities:

* Euler relation `T·s = ρ + p`, and
* Gibbs–Duhem relation `p′ = s·T′`.

This module discharges both.  In the grand-canonical ensemble at zero chemical
potential a fluid is characterised by a single thermodynamic potential — the
pressure `P(T)` (equivalently the grand potential density `Ω = −P`).  Entropy
density is *defined* as `s = dP/dT` and energy density by the Legendre
transform `ρ = T·s − P`.  With that structure:

* **Euler** `T·s = ρ + P` is an algebraic identity of the Legendre transform
  (`potential_euler`),
* **Gibbs–Duhem** `d/dt P(T(t)) = s·T′` is the chain rule
  (`potential_gibbs_duhem`), and
* the fundamental relation **`dρ = T·ds`** follows (`energy_deriv`):
  `ρ′(T) = s + T·s′ − s = T·s′`.

So the two hypotheses of `comoving_entropy_conserved` collapse into ONE
structural statement — "the coupled sector's pressure is a differentiable
potential with `s = dP/dT`" — which is the *definition* of local equilibrium,
not an extra dynamical assumption (`potential_entropy_conserved`).

## The concrete plasma realizes the structure

§2 instantiates the potential with statistical mechanics.  The pressure of a
massless Bose/Fermi gas is the log-kernel integral of the grand partition
function:

  `P = (g_B/2π²)·T⁴·∫ t²(−ln(1−e^{−t})) dt + (g_F/2π²)·T⁴·∫ t² ln(1+e^{−t}) dt`

The two integrals were **derived** in `RadiationEntropyRelation` via Mellin
transforms (`π⁴/45` and `7π⁴/360`), giving

  `P = (π²/90)·(g_B + (7/8)·g_F)·T⁴`   (`plasmaPressure_eq`).

Its temperature derivative is *exactly* the `radiationEntropy` of
`NeutrinoDilution` (`plasmaPressure_potential`) — the same object previously
obtained from the independent entropy integrals `∫σ_B = 4π⁴/45`,
`∫σ_F = 7π⁴/90`.  And the Legendre transform `T·s − P` reproduces the
independently derived energy integrals `π⁴/15`, `7π⁴/120`
(`plasma_energyOf`), forcing the radiation equation of state `p = ρ/3`
(`plasma_eos`) — the EOS is a *theorem* of the ensemble, not an input.

## Capstone

`dilution_from_potential`: the neutrino dilution `(T_ν/T_γ)³ = 4/11` now
follows from: FRW continuity for each sector + "the coupled sector has a
pressure potential" + boundary data.  Euler and Gibbs–Duhem are gone from the
hypothesis list; `gStarS_from_potential` propagates this to `g*s = 43/11`,
the effective dof in the η_B dynamical prefactor.

## What remains MODEL upstream

The grand-canonical form of the plasma pressure at the boundaries (statistical
mechanics input, though its integrals are derived), the Friedmann equations
behind the continuity equation (discharged separately in
`EntropyConservationFRW.continuity_from_friedmann`), sector decoupling, and
the boundary identifications (dof `2+4 → 2` across e± annihilation, shared
temperature at decoupling).

Reference: Landau & Lifshitz, *Statistical Physics* §24–§27 (grand potential,
`Ω = −PV`, `S = −∂Ω/∂T`); Kolb & Turner §3.3–3.4.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace GrandPotential

open Real MeasureTheory Set

/-! ## §1. The abstract potential fluid -/

/-- Energy density of a potential fluid: the Legendre transform of the
pressure potential, `ρ(T) = T·s(T) − P(T)`, with `s = dP/dT`.  This is
`ρ = T·(∂P/∂T) − P`, i.e. `U = TS − PV + μN` per unit volume at `μ = 0`. -/
noncomputable def energyOf (P s : ℝ → ℝ) : ℝ → ℝ := fun x => x * s x - P x

/-- **Euler relation (derived).** `T·s = ρ + P` is an algebraic identity of
the Legendre-transform structure — not an independent equilibrium postulate. -/
theorem potential_euler (P s : ℝ → ℝ) (x : ℝ) :
    x * s x = energyOf P s x + P x := by
  simp only [energyOf]
  ring

/-- **Gibbs–Duhem relation (derived).** Along any temperature trajectory
`T(t)`, the pressure obeys `p′ = s(T)·T′`: this is the chain rule applied to
`s = dP/dT`, not an independent postulate. -/
theorem potential_gibbs_duhem
    {P s T : ℝ → ℝ} {T' t : ℝ}
    (hP : HasDerivAt P (s (T t)) (T t))
    (hT : HasDerivAt T T' t) :
    HasDerivAt (fun u => P (T u)) (s (T t) * T') t := by
  simpa [Function.comp] using hP.comp t hT

/-- Entropy along a trajectory: `d/dt s(T(t)) = s′(T)·T′` (chain rule). -/
theorem potential_entropy_deriv
    {s T : ℝ → ℝ} {sT T' t : ℝ}
    (hs : HasDerivAt s sT (T t))
    (hT : HasDerivAt T T' t) :
    HasDerivAt (fun u => s (T u)) (sT * T') t := by
  simpa [Function.comp] using hs.comp t hT

/-- **Fundamental relation `dρ = T·ds` (derived).** The energy density of a
potential fluid has temperature derivative `ρ′(T) = T·s′(T)`:
differentiating `ρ = T·s − P` gives `s + T·s′ − s`. -/
theorem energy_deriv
    {P s : ℝ → ℝ} {sT x : ℝ}
    (hP : HasDerivAt P (s x) x)
    (hs : HasDerivAt s sT x) :
    HasDerivAt (energyOf P s) (x * sT) x := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hxs : HasDerivAt (fun y => y * s y) (1 * s x + x * sT) x := hid.mul hs
  have h : HasDerivAt (fun y => y * s y - P y)
      (1 * s x + x * sT - s x) x := hxs.sub hP
  have hval : 1 * s x + x * sT - s x = x * sT := by ring
  rw [hval] at h
  exact h

/-- Energy along a trajectory: `d/dt ρ(T(t)) = T·s′(T)·T′`. -/
theorem potential_energy_deriv
    {P s T : ℝ → ℝ} {sT T' t : ℝ}
    (hP : HasDerivAt P (s (T t)) (T t))
    (hs : HasDerivAt s sT (T t))
    (hT : HasDerivAt T T' t) :
    HasDerivAt (fun u => energyOf P s (T u)) (T t * sT * T') t := by
  have hx : HasDerivAt (energyOf P s) (T t * sT) (T t) := energy_deriv hP hs
  simpa [Function.comp, mul_assoc] using hx.comp t hT

/-- **THEOREM (entropy conservation from the potential alone).** For a fluid
whose pressure is a differentiable potential with `s = dP/dT` — the definition
of local equilibrium at zero chemical potential — the FRW continuity equation
forces `d/dt (s·a³) = 0`.  The Euler and Gibbs–Duhem hypotheses of
`EntropyConservationFRW.comoving_entropy_conserved` are *derived* here
(`potential_euler`, `potential_gibbs_duhem`), not assumed. -/
theorem potential_entropy_conserved
    {P s : ℝ → ℝ} {T a : ℝ → ℝ} {sT T' a' t : ℝ}
    (hTt : T t ≠ 0)
    (hP : HasDerivAt P (s (T t)) (T t))
    (hs : HasDerivAt s sT (T t))
    (hT : HasDerivAt T T' t) (ha : HasDerivAt a a' t)
    (hcont : a t * (T t * sT * T')
        = -3 * a' * (energyOf P s (T t) + P (T t))) :
    HasDerivAt (fun u => s (T u) * a u ^ 3) 0 t :=
  EntropyConservationFRW.comoving_entropy_conserved hTt
    (potential_energy_deriv hP hs hT)
    (potential_gibbs_duhem hP hT)
    (potential_entropy_deriv hs hT)
    ha hT
    (fun u => potential_euler P s (T u))
    rfl
    hcont

/-- **Global adiabaticity from the potential.** If the potential structure and
the continuity equation hold at every time, comoving entropy is globally
constant: `s(T(t₁))·a(t₁)³ = s(T(t₂))·a(t₂)³`. -/
theorem potential_entropy_constant
    {P s : ℝ → ℝ} {T a : ℝ → ℝ} {sT T' a' : ℝ → ℝ}
    (hTt : ∀ t, T t ≠ 0)
    (hP : ∀ t, HasDerivAt P (s (T t)) (T t))
    (hs : ∀ t, HasDerivAt s (sT t) (T t))
    (hT : ∀ t, HasDerivAt T (T' t) t) (ha : ∀ t, HasDerivAt a (a' t) t)
    (hcont : ∀ t, a t * (T t * sT t * T' t)
        = -3 * a' t * (energyOf P s (T t) + P (T t)))
    (t₁ t₂ : ℝ) :
    s (T t₁) * a t₁ ^ 3 = s (T t₂) * a t₂ ^ 3 := by
  have h0 : ∀ t, HasDerivAt (fun u => s (T u) * a u ^ 3) 0 t := fun t =>
    potential_entropy_conserved (hTt t) (hP t) (hs t) (hT t) (ha t) (hcont t)
  exact is_const_of_deriv_eq_zero (fun t => (h0 t).differentiableAt)
    (fun t => (h0 t).deriv) t₁ t₂

/-! ## §2. The relativistic plasma realizes the potential structure -/

/-- Pressure of a massless Bose/Fermi plasma from the grand partition
function: `P = (g/2π²)·T⁴·∫ t²(−ln(1∓e^{−t})) dt` per sector.  The log
kernels are the grand-canonical `ln Z` integrands after the angular
integration and the substitution `t = E/T`. -/
noncomputable def plasmaPressure (gB gF T : ℝ) : ℝ :=
  gB / (2 * π ^ 2) * T ^ 4
      * (∫ t in Ioi (0 : ℝ), t ^ 2 * (-Real.log (1 - Real.exp (-t))))
    + gF / (2 * π ^ 2) * T ^ 4
      * (∫ t in Ioi (0 : ℝ), t ^ 2 * Real.log (1 + Real.exp (-t)))

/-- Energy density of the same plasma from the occupation-number integrals
`∫ t³/(eᵗ∓1) dt` (derived in `FermionWeightIntegral`). -/
noncomputable def plasmaEnergy (gB gF T : ℝ) : ℝ :=
  gB / (2 * π ^ 2) * T ^ 4
      * (∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t - 1))
    + gF / (2 * π ^ 2) * T ^ 4
      * (∫ t in Ioi (0 : ℝ), t ^ 3 / (Real.exp t + 1))

/-- **THEOREM (plasma pressure closed form).** The log-kernel integrals
(`π⁴/45`, `7π⁴/360`, both derived via Mellin transforms) collapse the
pressure to `P = (π²/90)·(g_B + (7/8)·g_F)·T⁴`.  The `7/8` is the same
fermionic weight that appears in entropy and energy — here it comes out of
the pressure channel independently. -/
theorem plasmaPressure_eq (gB gF T : ℝ) :
    plasmaPressure gB gF T = π ^ 2 / 90 * (gB + 7 / 8 * gF) * T ^ 4 := by
  unfold plasmaPressure
  rw [RadiationEntropyRelation.boseLog_integral_value,
    RadiationEntropyRelation.fermiLog_integral_value]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **THEOREM (plasma energy closed form).** The energy integrals (`π⁴/15`,
`7π⁴/120`) give `ρ = (π²/30)·(g_B + (7/8)·g_F)·T⁴`. -/
theorem plasmaEnergy_eq (gB gF T : ℝ) :
    plasmaEnergy gB gF T = π ^ 2 / 30 * (gB + 7 / 8 * gF) * T ^ 4 := by
  unfold plasmaEnergy
  rw [FermionWeightIntegral.bose_integral_value,
    FermionWeightIntegral.fermi_integral_value]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **THEOREM (the plasma is a potential fluid).** The temperature derivative
of the statistical-mechanical pressure is *exactly* the `radiationEntropy` of
`NeutrinoDilution` — the object previously built from the independent entropy
integrals `∫σ_B`, `∫σ_F`.  So `s = dP/dT` holds between two independently
derived statistical-mechanical quantities: the potential structure of the
plasma is a theorem, not a definition. -/
theorem plasmaPressure_potential (gB gF x : ℝ) :
    HasDerivAt (fun T => plasmaPressure gB gF T)
      (NeutrinoDilution.radiationEntropy gB gF x) x := by
  rw [NeutrinoDilution.radiationEntropy_eq]
  have hfun : (fun T => plasmaPressure gB gF T)
      = fun T => π ^ 2 / 90 * (gB + 7 / 8 * gF) * T ^ 4 :=
    funext fun T => plasmaPressure_eq gB gF T
  rw [hfun]
  have hpow : HasDerivAt (fun T : ℝ => T ^ 4) (4 * x ^ 3) x := by
    simpa using hasDerivAt_pow 4 x
  have h := hpow.const_mul (π ^ 2 / 90 * (gB + 7 / 8 * gF))
  have hval : π ^ 2 / 90 * (gB + 7 / 8 * gF) * (4 * x ^ 3)
      = 2 * π ^ 2 / 45 * (gB + 7 / 8 * gF) * x ^ 3 := by ring
  rw [hval] at h
  exact h

/-- **THEOREM (Legendre consistency).** The abstract Legendre energy
`T·s − P` built from the pressure potential and the entropy equals the
independently derived energy integral: `∫ t³/(eᵗ∓1)` agrees with
`4·∫ t²·logkernel − ∫ t²·logkernel`.  Two separate ensemble computations
meet — this is the internal consistency of the grand-canonical structure. -/
theorem plasma_energyOf (gB gF : ℝ) :
    energyOf (plasmaPressure gB gF) (NeutrinoDilution.radiationEntropy gB gF)
      = plasmaEnergy gB gF := by
  funext T
  simp only [energyOf]
  rw [NeutrinoDilution.radiationEntropy_eq, plasmaEnergy_eq, plasmaPressure_eq]
  ring

/-- **THEOREM (radiation equation of state derived).** `p = ρ/3` is forced by
the grand-canonical integrals — it is not an input anywhere in the chain. -/
theorem plasma_eos (gB gF T : ℝ) :
    plasmaPressure gB gF T = plasmaEnergy gB gF T / 3 := by
  rw [plasmaEnergy_eq, plasmaPressure_eq]
  ring

/-! ## §3. Capstones: dilution and g*s with Euler/Gibbs–Duhem discharged -/

/-- **CAPSTONE (dilution from the potential).** `(T_ν/T_γ)³ = 4/11` from:
the coupled sector has a pressure potential with `s = dP/dT` (local
equilibrium, the *only* thermodynamic input), both sectors satisfy their FRW
continuity equations, and the boundary data (plasma dof `2+4 → 2` across e±
annihilation, shared temperature at decoupling).  Compared with
`EntropyConservationFRW.dilution_from_frw`, the Euler and Gibbs–Duhem
hypotheses are gone — they are theorems of the potential structure. -/
theorem dilution_from_potential
    {P s : ℝ → ℝ} {T a Tν : ℝ → ℝ} {sT T' a' Tν' ρν' : ℝ → ℝ}
    {t₁ t₂ : ℝ} {T₁ Tγ αν : ℝ}
    (hTt : ∀ t, T t ≠ 0) (hαν : αν ≠ 0) (hTνt : ∀ t, Tν t ≠ 0)
    (ha₂ : a t₂ ≠ 0) (hTγ : Tγ ≠ 0)
    (hP : ∀ t, HasDerivAt P (s (T t)) (T t))
    (hs : ∀ t, HasDerivAt s (sT t) (T t))
    (hT : ∀ t, HasDerivAt T (T' t) t) (ha : ∀ t, HasDerivAt a (a' t) t)
    (hTν : ∀ t, HasDerivAt Tν (Tν' t) t)
    (hρν : ∀ t, HasDerivAt (fun u => αν * Tν u ^ 4) (ρν' t) t)
    (hcont : ∀ t, a t * (T t * sT t * T' t)
        = -3 * a' t * (energyOf P s (T t) + P (T t)))
    (hcontν : ∀ t, a t * ρν' t
        = -3 * a' t * (αν * Tν t ^ 4 + αν * Tν t ^ 4 / 3))
    (hbefore : s (T t₁) = NeutrinoDilution.radiationEntropy 2 4 T₁)
    (hafter : s (T t₂) = NeutrinoDilution.radiationEntropy 2 0 Tγ)
    (hshare : Tν t₁ = T₁) :
    (Tν t₂ / Tγ) ^ 3 = 4 / 11 := by
  -- Adiabaticity of the coupled sector: derived from the potential structure.
  have hcons : NeutrinoDilution.radiationEntropy 2 4 T₁ * a t₁ ^ 3
      = NeutrinoDilution.radiationEntropy 2 0 Tγ * a t₂ ^ 3 := by
    have h := potential_entropy_constant hTt hP hs hT ha hcont t₁ t₂
    rw [hbefore, hafter] at h
    exact h
  -- Free streaming of the neutrino sector (derived in EntropyConservationFRW).
  have hfree : a t₂ * Tν t₂ = a t₁ * T₁ := by
    have h := EntropyConservationFRW.radiation_aT_constant hαν hTνt hTν ha
      hρν hcontν t₂ t₁
    rw [hshare] at h
    exact h
  exact NeutrinoDilution.dilution_from_entropy_conservation ha₂ hTγ hcons hfree

/-- **CAPSTONE (g*s from the potential).** The present-day entropy density
equals `(2π²/45)·(43/11)·T_γ³` with the same reduced hypothesis list: the
effective entropy dof in the η_B dynamical prefactor now rests on FRW
continuity + the existence of a pressure potential + boundary data. -/
theorem gStarS_from_potential
    {P s : ℝ → ℝ} {T a Tν : ℝ → ℝ} {sT T' a' Tν' ρν' : ℝ → ℝ}
    {t₁ t₂ : ℝ} {T₁ Tγ αν : ℝ}
    (hTt : ∀ t, T t ≠ 0) (hαν : αν ≠ 0) (hTνt : ∀ t, Tν t ≠ 0)
    (ha₂ : a t₂ ≠ 0) (hTγ : Tγ ≠ 0)
    (hP : ∀ t, HasDerivAt P (s (T t)) (T t))
    (hs : ∀ t, HasDerivAt s (sT t) (T t))
    (hT : ∀ t, HasDerivAt T (T' t) t) (ha : ∀ t, HasDerivAt a (a' t) t)
    (hTν : ∀ t, HasDerivAt Tν (Tν' t) t)
    (hρν : ∀ t, HasDerivAt (fun u => αν * Tν u ^ 4) (ρν' t) t)
    (hcont : ∀ t, a t * (T t * sT t * T' t)
        = -3 * a' t * (energyOf P s (T t) + P (T t)))
    (hcontν : ∀ t, a t * ρν' t
        = -3 * a' t * (αν * Tν t ^ 4 + αν * Tν t ^ 4 / 3))
    (hbefore : s (T t₁) = NeutrinoDilution.radiationEntropy 2 4 T₁)
    (hafter : s (T t₂) = NeutrinoDilution.radiationEntropy 2 0 Tγ)
    (hshare : Tν t₁ = T₁) :
    NeutrinoDilution.radiationEntropy 2 0 Tγ
        + NeutrinoDilution.radiationEntropy 0 6 (Tν t₂)
      = 2 * π ^ 2 / 45 * ((EntropyPerPhoton.gStarS : ℚ) : ℝ) * Tγ ^ 3 :=
  NeutrinoDilution.total_entropy_eq_gStarS hTγ
    (dilution_from_potential hTt hαν hTνt ha₂ hTγ hP hs hT ha hTν hρν
      hcont hcontν hbefore hafter hshare)

end GrandPotential
end Cosmology
end IndisputableMonolith
