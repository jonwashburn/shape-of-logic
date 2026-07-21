import Mathlib
import IndisputableMonolith.Holography.KeystoneFactorThree

/-!
# Deficit-Free Period: 2π/κ forced by holonomy closure (LEG-B core chain)

**Status: THEOREM for the mathematical chain; the physics bridge carries two named
MODEL premises.** This module is the canonical formalization of the LEG-B derive
captain's accepted derivation steps (`rs-bekenstein-legb-loop` on Steve, physics-critic
gated; journal entries `derive_20260702_065112`, `derive_20260702_082715`,
`derive_20260702_090702`, all ACCEPT, zero rejections), promoting the banked scratch
leaves (`state/bekenstein_legb_closed/legb_exp_period_lattice.lean`,
`legb_clausius_to_bekenstein.lean`, `legb_eight_tick_circle_period.lean`) into one
auditable canonical chain.

## The chain (what is proved here)

1. **Holonomy carrier (THEOREM, definitional + lattice).** The per-cycle phase-return
   map of a clocked recognition cycle at rate `κ` is `h(T) = exp(iκT)`. The return is
   exact (`h(T) = 1`) iff `κT ∈ 2πℤ` (`holonomy_eq_one_iff_lattice`,
   `holonomy_eq_one_iff`). This is the U(1) target the 8-tick clock embeds into
   (`legb_eight_tick_circle_period`; `EightTickSubperiodExclusion` for the discrete
   exclusion of subperiods).

2. **Deficit-cost functional (THEOREM).** The recognition cost of an imperfect return
   with phase deficit `δ` is `C(δ) = 1 − cos δ = ½‖1 − exp(iδ)‖²`
   (`deficitCost_eq_half_normSq`): the squared chord distance between the returned
   phase and perfect closure, i.e. the J-cost quadratic form on the U(1) carrier. It
   is nonnegative (`deficitCost_nonneg`), vanishes EXACTLY on `2πℤ`
   (`deficitCost_eq_zero_iff`), is strictly positive off the lattice
   (`deficitCost_pos_of_not_period`), and has a strict quadratic minimum at closure:
   critical point at 0 with second derivative `cos 0 = 1 > 0`
   (`deficitCost_hasDerivAt`, `deficitCost_critical_at_zero`,
   `deficitCost_second_deriv_pos_at_zero`).

3. **Minimal positive deficit-free period (THEOREM).** For `κ > 0` the set of
   positive deficit-free return times `{T > 0 | C(κT) = 0}` has LEAST element
   `β = 2π/κ` (`euclideanPeriod_isLeast`). This is the target the derive captain holds
   as `legb_minimal_positive_period`, landed here canonically. 2π is not chosen: it is
   the smallest positive zero of the deficit cost, which is itself the unique J-form
   on the forced U(1) carrier.

4. **Physics bridge (CONDITIONAL on two named MODEL premises).** With
   `HorizonRate κ R` (the static-horizon phase rate is `κ = 1/R`, the
   Schwarzschild/Rindler surface-gravity convention in the ledger normalization) and
   `ClausiusForm S E β` (the static-horizon entropy is the thermal `S = βE` at the
   Euclidean period), the deficit-free period forces
   `S = 2πER` (`bekenstein_saturation_from_deficit_free_period`), the exact
   SATURATING value of the Casini/Bekenstein form consumed by
   `KeystoneFactorThree` (`totalEntropyBound_saturating_case`).

## What this does NOT close (honest boundary)

This module derives the MAGNITUDE of the Euclidean period (2π/κ, forced) and the
SATURATING value `S = 2πER` for the thermal/Clausius state. It does NOT discharge
LEG-B proper (`KeystoneFactorThree.TotalEntropyBekensteinBound` as a bound for ALL
states, which is Casini's relative-entropy positivity statement) and it does not
derive the two MODEL premises:

- `ClausiusForm` imports the first law / KMS-thermality of the horizon state. The
  captain's open target `legb_kms_window_unique` (uniqueness of the KMS analytic
  window) is the derivation route.
- `HorizonRate` imports the surface-gravity normalization `κ = 1/R`. The Live Bet 2
  audit (R = 2GE kernel-derivability) tracks its status; see the master plan.

The weakest link sets the tag: consumers of the bridge theorems are CONDITIONAL.
The lattice/minimality chain (items 1-3) is unconditional and axiom-clean.

Provenance: `plans/RS_Bekenstein_Quarter_Master_Plan_20260702.html` (LEG-B);
`glm/bekenstein_legb/DERIVATION_LOG.md`. The seam-modular verdict
(`SeamModularHamiltonian`) killed the classical GF(2) route to 2π, so this
holonomy/KMS lane is the only live route, as steered on 2026-07-02.
-/

namespace IndisputableMonolith
namespace Holography
namespace DeficitFreePeriod

open Complex

/-- The per-cycle holonomy carrier: the phase-return map `h(T) = exp(iκT)` of a
clocked recognition cycle running at rate `κ` for time `T`. Accepted derive step
`derive_20260702_065112`: the 8-tick clock embeds in U(1) and its per-cycle return is
this exponential (see `legb_eight_tick_circle_period` for the discrete embedding). -/
noncomputable def holonomy (kappa T : ℝ) : ℂ :=
  Complex.exp (kappa * T * Complex.I)

/-- The deficit-cost functional: the recognition cost of a phase deficit `δ`,
`C(δ) = 1 − cos δ`. Accepted derive step `derive_20260702_082715`. Equivalently the
squared chord distance `½‖1 − exp(iδ)‖²` (see `deficitCost_eq_half_normSq`), the
J-cost quadratic form on the U(1) carrier. -/
noncomputable def deficitCost (δ : ℝ) : ℝ :=
  1 - Real.cos δ

/-- The Euclidean period forced by deficit-free closure: `β = 2π/κ`. -/
noncomputable def euclideanPeriod (kappa : ℝ) : ℝ :=
  2 * Real.pi / kappa

/-- Named MODEL premise (Clausius form): the static-horizon entropy is the thermal
entropy `S = βE` at Euclidean period `β`. This is the first-law/KMS-thermality input;
its derivation route is the captain's open `legb_kms_window_unique` target. -/
def ClausiusForm (S E beta : ℝ) : Prop :=
  S = beta * E

/-- Named MODEL premise (horizon rate): the static-horizon phase rate is `κ = 1/R`
(surface-gravity convention in the ledger normalization; Live Bet 2 tracks its
kernel-derivability). -/
def HorizonRate (kappa R : ℝ) : Prop :=
  kappa = 1 / R

/-! ## The deficit-cost functional is the chord-distance J-form on U(1) -/

/-- `C(δ) = ½‖1 − exp(iδ)‖²`: the deficit cost is exactly half the squared chord
distance between the returned phase and perfect closure. -/
theorem deficitCost_eq_half_normSq (δ : ℝ) :
    deficitCost δ = (1 / 2) * Complex.normSq (1 - Complex.exp (δ * Complex.I)) := by
  have hre : (1 - Complex.exp ((δ : ℂ) * Complex.I)).re = 1 - Real.cos δ := by
    simp [Complex.sub_re, Complex.exp_ofReal_mul_I_re]
  have him : (1 - Complex.exp ((δ : ℂ) * Complex.I)).im = -Real.sin δ := by
    simp [Complex.sub_im, Complex.exp_ofReal_mul_I_im]
  rw [Complex.normSq_apply, hre, him]
  have hpyth := Real.sin_sq_add_cos_sq δ
  unfold deficitCost
  nlinarith [hpyth]

/-- The deficit cost is nonnegative. -/
theorem deficitCost_nonneg (δ : ℝ) : 0 ≤ deficitCost δ := by
  unfold deficitCost
  linarith [Real.cos_le_one δ]

/-- The zero set of the deficit cost is EXACTLY the lattice `2πℤ`: perfect closure
happens at integer numbers of full turns and nowhere else. -/
theorem deficitCost_eq_zero_iff (δ : ℝ) :
    deficitCost δ = 0 ↔ ∃ n : ℤ, δ = (n : ℝ) * (2 * Real.pi) := by
  unfold deficitCost
  constructor
  · intro h
    have hcos : Real.cos δ = 1 := by linarith
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff δ).mp hcos
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, rfl⟩
    have := Real.cos_int_mul_two_pi n
    linarith

/-- Strict positivity off the closure lattice: any phase deficit not a whole number
of turns costs strictly positive recognition (accepted derive step
`derive_20260702_090702`). -/
theorem deficitCost_pos_of_not_period (δ : ℝ)
    (h : ¬∃ n : ℤ, δ = (n : ℝ) * (2 * Real.pi)) :
    0 < deficitCost δ := by
  rcases lt_or_eq_of_le (deficitCost_nonneg δ) with hpos | heq
  · exact hpos
  · exact absurd ((deficitCost_eq_zero_iff δ).mp heq.symm) h

/-! ## Local convexity at closure: strict quadratic minimum -/

/-- The deficit cost is differentiable with derivative `sin δ`. -/
theorem deficitCost_hasDerivAt (δ : ℝ) :
    HasDerivAt deficitCost (Real.sin δ) δ := by
  have h := (Real.hasDerivAt_cos δ).const_sub (1 : ℝ)
  simpa [deficitCost] using h

/-- Closure is a critical point: the derivative of the deficit cost vanishes at
`δ = 0`. -/
theorem deficitCost_critical_at_zero : HasDerivAt deficitCost 0 0 := by
  simpa using deficitCost_hasDerivAt 0

/-- The second derivative at closure is `cos 0 = 1 > 0`: the derivative `sin` has
slope 1 at `δ = 0`, so closure is a strict quadratic minimum of the deficit cost
(accepted derive step `derive_20260702_090702`: local convexity `C''(0) = 1`). -/
theorem deficitCost_second_deriv_pos_at_zero :
    HasDerivAt Real.sin 1 0 := by
  simpa using Real.hasDerivAt_sin 0

/-! ## Holonomy closure ↔ deficit-free ↔ the 2πℤ lattice -/

/-- The holonomy returns exactly (`h(T) = 1`) iff `κT` lies on the `2πℤ` lattice. -/
theorem holonomy_eq_one_iff_lattice (kappa T : ℝ) :
    holonomy kappa T = 1 ↔ ∃ n : ℤ, kappa * T = (n : ℝ) * (2 * Real.pi) := by
  unfold holonomy
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : ((kappa * T : ℝ) : ℂ) * Complex.I =
        (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast
      linear_combination hn
    have h3 := mul_right_cancel₀ Complex.I_ne_zero h2
    exact_mod_cast h3
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hC : ((kappa : ℂ) * (T : ℂ)) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
      exact_mod_cast hn
    calc (kappa : ℂ) * (T : ℂ) * Complex.I
        = ((n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by rw [hC]
      _ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring

/-- Deficit-free return and exact holonomy closure are the SAME condition: the
deficit cost of the accumulated phase vanishes iff the holonomy returns to 1. -/
theorem holonomy_deficit_free_iff (kappa T : ℝ) :
    deficitCost (kappa * T) = 0 ↔ holonomy kappa T = 1 := by
  rw [deficitCost_eq_zero_iff, holonomy_eq_one_iff_lattice]

/-- Exact return times are the lattice `T ∈ (2π/κ)ℤ` (the canonical form of the
banked `legb_exp_period_lattice`, both directions). -/
theorem holonomy_eq_one_iff (kappa T : ℝ) (hk : kappa ≠ 0) :
    holonomy kappa T = 1 ↔ ∃ n : ℤ, T = (n : ℝ) * (2 * Real.pi / kappa) := by
  rw [holonomy_eq_one_iff_lattice]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h1 : T * kappa = (n : ℝ) * (2 * Real.pi) := by linarith [hn]
    have h2 : T = (n : ℝ) * (2 * Real.pi) / kappa := eq_div_of_mul_eq hk h1
    rw [h2, mul_div_assoc]
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    field_simp

/-! ## The minimal positive deficit-free period is 2π/κ -/

/-- **The headline (LEG-B `legb_minimal_positive_period`, landed canonically).**
For `κ > 0`, the set of positive deficit-free return times has least element
`β = 2π/κ`. 2π is forced: it is the smallest positive zero of the deficit-cost
functional, which is itself the J-form on the forced U(1) carrier. -/
theorem euclideanPeriod_isLeast (kappa : ℝ) (hk : 0 < kappa) :
    IsLeast {T : ℝ | 0 < T ∧ deficitCost (kappa * T) = 0} (euclideanPeriod kappa) := by
  constructor
  · refine ⟨div_pos (by positivity) hk, ?_⟩
    rw [deficitCost_eq_zero_iff]
    refine ⟨1, ?_⟩
    unfold euclideanPeriod
    push_cast
    field_simp
  · rintro T ⟨hT, hzero⟩
    rw [deficitCost_eq_zero_iff] at hzero
    obtain ⟨n, hn⟩ := hzero
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have hprod : (0 : ℝ) < (n : ℝ) * (2 * Real.pi) := hn ▸ mul_pos hk hT
      nlinarith
    have hnZ : (1 : ℤ) ≤ n := by exact_mod_cast Int.cast_pos.mp hnR
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnZ
    have hT_eq : T = (n : ℝ) * (2 * Real.pi) / kappa :=
      eq_div_of_mul_eq (ne_of_gt hk) (by linarith [hn])
    unfold euclideanPeriod
    rw [hT_eq]
    have hnum : 2 * Real.pi ≤ (n : ℝ) * (2 * Real.pi) := by
      nlinarith [Real.pi_pos]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hk.le)

/-! ## The physics bridge: deficit-free period → S = 2πER (saturating case) -/

/-- **CONDITIONAL bridge.** Given the two named MODEL premises (`HorizonRate`:
`κ = 1/R`; `ClausiusForm`: `S = βE` at the deficit-free Euclidean period
`β = 2π/κ`), the entropy of the static horizon is exactly `S = 2πER`: the
SATURATING value of the Bekenstein/Casini form. Canonical form of the banked
`legb_clausius_to_bekenstein`. -/
theorem bekenstein_saturation_from_deficit_free_period
    (S E R kappa : ℝ) (hR : 0 < R)
    (hRate : HorizonRate kappa R)
    (hClausius : ClausiusForm S E (euclideanPeriod kappa)) :
    S = 2 * Real.pi * E * R := by
  unfold HorizonRate at hRate
  unfold ClausiusForm euclideanPeriod at hClausius
  subst hRate
  rw [hClausius]
  have hR' : R ≠ 0 := ne_of_gt hR
  field_simp

/-- The saturating thermal state satisfies the `KeystoneFactorThree` bound form with
equality. NOTE the honest scope: this shows the CLAUSIUS STATE saturates the bound
form; it is NOT the general bound for arbitrary states (LEG-B proper, still OPEN with
the derive captain). -/
theorem totalEntropyBound_saturating_case
    (S E R kappa : ℝ) (hR : 0 < R)
    (hRate : HorizonRate kappa R)
    (hClausius : ClausiusForm S E (euclideanPeriod kappa)) :
    KeystoneFactorThree.TotalEntropyBekensteinBound S E R := by
  have h := bekenstein_saturation_from_deficit_free_period S E R kappa hR hRate hClausius
  unfold KeystoneFactorThree.TotalEntropyBekensteinBound
  linarith

/-! ## Certificate -/

/-- Bundled certificate for the deficit-free-period chain: the deficit cost is
nonnegative with zero set exactly `2πℤ`, deficit-free return IS holonomy closure,
the minimal positive deficit-free period is `2π/κ`, and (given the two named MODEL
premises) the static-horizon entropy saturates at `S = 2πER`. The first four fields
are unconditional THEOREMs; the last is the CONDITIONAL physics bridge. -/
structure DeficitFreePeriodCert : Prop where
  cost_nonneg : ∀ δ : ℝ, 0 ≤ deficitCost δ
  cost_zero_iff : ∀ δ : ℝ, deficitCost δ = 0 ↔ ∃ n : ℤ, δ = (n : ℝ) * (2 * Real.pi)
  holonomy_iff : ∀ kappa T : ℝ, deficitCost (kappa * T) = 0 ↔ holonomy kappa T = 1
  minimal_period : ∀ kappa : ℝ, 0 < kappa →
    IsLeast {T : ℝ | 0 < T ∧ deficitCost (kappa * T) = 0} (euclideanPeriod kappa)
  saturation : ∀ S E R kappa : ℝ, 0 < R → HorizonRate kappa R →
    ClausiusForm S E (euclideanPeriod kappa) → S = 2 * Real.pi * E * R

/-- The certificate holds. -/
theorem deficitFreePeriodCert : DeficitFreePeriodCert where
  cost_nonneg := deficitCost_nonneg
  cost_zero_iff := deficitCost_eq_zero_iff
  holonomy_iff := holonomy_deficit_free_iff
  minimal_period := euclideanPeriod_isLeast
  saturation := bekenstein_saturation_from_deficit_free_period

end DeficitFreePeriod
end Holography
end IndisputableMonolith
