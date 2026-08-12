import IndisputableMonolith.Gravity.SevenGaps.HKTKineticNormalizedRigidity
import IndisputableMonolith.Cost.Convexity
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Cost.SymplecticAction

/-!
# Pillar 1 work item 1: halving the disclosed constraint premise

`HKTKineticNormalizedRigidity.KineticNormalizedCanonicalMom` carries a disclosed
premise,

    S.hp a b p = (2 * cKin) * p     with `cKin ≠ 0` constant,

and four kill theorems in that module show the rigidity conclusion is false
without it, so the premise carries the whole load. This module reduces that load
and reports, in Lean, exactly how far the reduction goes and where it stops.

## What is established

**§2. Only half the premise was ever an assumption.** The premise says two
things: the momentum response is linear in the momentum, and its coefficient
does not look at the neighbouring field values. Assume only the second, together
with vanishing at zero momentum,

    S.hp a b p = φ p,   φ 0 = 0,

and the point-split functional equation carried by every `CanonicalMom` target
forces `φ` to be exactly linear, with an explicit nonzero coefficient
(`kinetic_normalization_of_universal_response`). No recognition input is used.
Under the ambient `CanonicalMom` axioms the two classes are therefore
*equivalent*, which is what `UniversalKineticCanonicalMom.toKineticNormalized`
and its converse say. The result is not a larger model class; it is that the
load-bearing surface of the disclosed premise is field-independence alone.

**§3. Field-independence is equivalent to channel separation.** Writing the
density as a momentum-channel cost plus a link term, `h a b p = K p + U a b`
with `K` stationary at zero momentum, is equivalent to §2's hypothesis
(`universal_of_channelSeparated`, `channelSeparated_of_universal`). That is a
restatement, not a weakening, and it is recorded as one. Its only value is
provenance: `Foundation.JHessianGolden.additivePosting` already formalizes
recognition cost as posted additively coordinate by coordinate,
`Φ(x) = Σᵢ J(xᵢ)`, with Hessian `diag(J''(xᵢ))`. Channel separation is that
additivity applied to a two-channel split. Whether the momentum and the spatial
link are distinct ledger channels is **not proved here**; see the open items
below.

**§4. The exact cost is excluded from the linear chart.** Identify the momentum
with the log-imbalance linearly, `t = κ p`; then `Jlog t = cosh t - 1` gives
momentum response `w κ sinh (κ p)`, derived rather than assumed
(`costKinetic_hp_eq_sinh`), which §2 forces linear, and `sinh` is not linear
(`no_exact_cost_kinetic_canonicalMom`). Read the scope literally: this excludes
that chart, not the cost. §8 exhibits a chart in which the exact cost is
quadratic and does inhabit the algebra.

**§5. The balance jet fits, with a fitted coefficient.** The second-order jet
about balance is `JlogQuad t = (J''(1) / 2) * t ^ 2`
(`JlogQuad_matches_Jlog_to_second_order`). A target with that momentum sector
satisfies the disclosed premise with `cKin = w * κ ^ 2 * J''(1) / 2`
(`quadCost_hp_eq_linear`) and inherits full ADM rigidity
(`quadCost_ADM_rigidity`). Both `w` and `κ` are free, so that number is a fit.

**§6. The load-bearing test.** The variable-kinetic inhabitant of the kill tower
is a field-dependent cost weight and is excluded from the universal class
(`vacuumKinetic_not_universalKinetic`), while the ADM anchor still inhabits it,
so §2 has not emptied the class.

**§7 does not work, and says so.** Its route was to impose the calibration
condition `J''(1) = 1` on a per-site jet family. Three defects kill it: the
family is defined in this module, so the per-site condition is settled by an
unfold and is the between-site equality renamed; the free chart absorbs the
value, so only constancy does work and the recognition number does none; and the
family fails the Recognition Composition Law outright (`jetCost_not_rcl`). The
section is kept with that diagnosis because the general lesson transfers: a
pointwise recognition condition carries weight only in proportion to the depth of
the uniqueness theorem behind it, and none at all if the ambient free parameters
can absorb its value.

**§8. The composition law carries the premise.** Two results. First the chart:
`J (exp t) = 2 sinh (t / 2) ^ 2`, so identifying the momentum with the
half-imbalance *sine*, `t = 2 arsinh (λ p)`, makes the exact recognition cost
`2 λ ^ 2 p ^ 2` with no truncation (`Jlog_two_arsinh`). The exact cost inhabits
the undeformed algebra, and §5's truncation was an artifact of §4's chart. Then
the derivation: let each site carry its own cost weight `W a b`, so
field-independence is absent from the hypothesis, and require each site's weight
to satisfy the Recognition Composition Law. Since `w * J` satisfies that law only
for `w` in `{0, 1}` (`compositionLaw_forces_unit_weight`), because a rescaled
recognition cost is not a recognition cost, every weight is forced to `1`, hence
`S.hp a b p = 4 λ ^ 2 p` and `cKin = 2 λ ^ 2 > 0`
(`rclKinetic_hp_eq_linear`, `rclKinetic_ADM_rigidity`). The ADM anchor inhabits
the class at `λ = 1/2` with its own coefficient `1/2` (`hamDynRCLKinetic`), and
deleting the clause readmits the kill inhabitant *exactly*, not by analogy: at
`λ = 1/2` with weights `2 / (1 + a ^ 2)` the profile is
`vacuumKineticLocalProfile` (`vacuumKineticLocalProfile_eq_exactCost`), which
`not_HKTRigidityModVacuumStatementN2` refutes. The exclusion is also proved
directly from the clause (`no_rcl_presentation_of_vacuumKinetic`).

## What is and is not established

Established: the substrate supplies two facts about the constraint sector that
the algebra does not. The momentum-channel cost weight cannot vary from site to
site, and it cannot be negative, so the kinetic coefficient is field-independent
and positive. Both come from one theorem about the composition law, applied to
the repo's own `Cost.Jcost`, and deleting that theorem's hypothesis makes the
rigidity conclusion false rather than weaker.

Not established: the magnitude. `cKin = 2 λ ^ 2` with `λ` free, and `λ` is fixed
in the anchor only by matching ADM's coefficient, so it is fitted. Nor is the
channel identification discharged: the chart is assumed to be one global
constant, and a site-dependent chart `λ a b` reproduces the kill inhabitant at
unit weight. That is the honest boundary. Recognition now does logical work in
the constraint sector, and it does not yet predict a number there.

## The open objects, named

1. A ledger-axiom predicate on point-split targets that forces the chart to be
   global, which is what would discharge the channel identification. The test it
   must pass is sharper than before: it has to separate two countermodels, the
   variable-weight kill inhabitant *and* the unit-weight site-dependent chart
   `λ a b`. A predicate that only excludes the first is another guard that does
   not discriminate.
2. Any independent fixing of `λ`, that is, a quantization of the momentum-channel
   half-imbalance sine against a recognition constant rather than against ADM's
   `cKin`. This is the only thing that would turn `cKin = 2 λ ^ 2` from a
   positivity statement into a number.

Provenance of the corrections: a cross-family hostile read (Grok 4.5, 2026-07-25)
forced the §1 to §6 language, and a four-family panel (Opus 5, Grok 4.5,
GPT-5.6 Sol, Kimi K3, 2026-07-25) killed §7 and supplied both the composition-law
route and the chart identity that §8 is built on.

No `sorry`, no `admit`, no new axiom, no `native_decide`. No FullTheoryLedger
flag changes.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace HKTKineticFromRecognitionCost

open HypersurfaceDeformation DynamicStructureBracket DynamicStructureFunctionBlocker
open HKTPointSplitTarget HKTPointSplitStrong HKTLocalFunctionalEquation
open HKTCanonicalMomTarget HKTCanonicalMomRigidity
open HKTKineticNormalizedRigidity
open FullTheoryLedger

noncomputable section

/-! ## §1. The weakened premise -/

/-- A `CanonicalMom` target whose momentum response is *ultralocal-universal*:
it depends on the momentum alone, not on the neighbouring field values, and it
vanishes at zero momentum.

As a hypothesis this is weaker than `KineticNormalizedCanonicalMom`, which also
demands linearity. As a class it is not larger: §2 proves the two coincide under
the ambient `CanonicalMom` axioms. -/
structure UniversalKineticCanonicalMom where
  target : HKTPointSplitTargetDynCanonicalMom
  universal_response :
    ∃ (h : LocalHamProfile) (S : LocalHamSmooth h) (φ : ℝ → ℝ),
      ContDiff ℝ 2 (profileMap h) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          target.hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j)) ∧
          (∀ a b p : ℝ, S.hp a b p = φ p) ∧ φ 0 = 0

/-! ## §2. The functional equation forces linearity -/

/-- The structure function of a `CanonicalMom` target takes a nonzero value
somewhere: a structure function vanishing identically would be phase-space
constant, which `structure_nonconstant` forbids. -/
theorem exists_structure_value_ne_zero
    (T : HKTPointSplitTargetDynCanonicalMom) (g : ℝ → ℝ)
    (hG : ∀ (x : PhaseSpace 2) (j : ZMod 2), T.structureFunction x j = g (x.1 j)) :
    ∃ a : ℝ, g a ≠ 0 := by
  by_contra hall
  push_neg at hall
  refine T.structure_nonconstant ?_
  intro x y j
  rw [hG x j, hG y j, hall (x.1 j), hall (y.1 j)]

/-- **Half the premise, derived.** A field-independent momentum response
vanishing at zero momentum is automatically linear on any `CanonicalMom`
point-split target, with the coefficient read off the momentum coupling, the
structure function, and the gradient response at one point.

Nothing about recognition enters. What enters is that the point-split functional
equation is separately linear in each momentum slot, so a response that cannot
hide field dependence cannot hide nonlinearity either. The choice of the point
`(a₀, a₀ + 1)` is free: the denominator cannot vanish, since a vanishing one
would make the equation read `0 = cMom * g a₀ * r`, false at `r = 1`. -/
theorem kinetic_normalization_of_universal_response
    (T : HKTPointSplitTargetDynCanonicalMom)
    (h : LocalHamProfile) (S : LocalHamSmooth h) (g : ℝ → ℝ) (cMom : ℝ) (φ : ℝ → ℝ)
    (hHam : ∀ (x : PhaseSpace 2) (j : ZMod 2),
      T.hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j))
    (hG : ∀ (x : PhaseSpace 2) (j : ZMod 2), T.structureFunction x j = g (x.1 j))
    (hcMom : cMom ≠ 0)
    (hMom : ∀ (x : PhaseSpace 2) (j : ZMod 2),
      T.momDensity x j = cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j))
    (hUniv : ∀ a b p : ℝ, S.hp a b p = φ p) (hφ0 : φ 0 = 0) :
    ∃ cKin : ℝ, cKin ≠ 0 ∧ ∀ a b p : ℝ, S.hp a b p = (2 * cKin) * p := by
  obtain ⟨a₀, hga₀⟩ := exists_structure_value_ne_zero T g hG
  have hFE := alternating_FE_of_profile T h S g cMom hHam hG hMom
  -- Evaluate the functional equation at `(a, b, p, r) = (a₀, a₀ + 1, 0, r)`.
  have key : ∀ r : ℝ, S.hb a₀ (a₀ + 1) 0 * φ r = cMom * g a₀ * r := by
    intro r
    have hr := hFE a₀ (a₀ + 1) 0 r
    rw [hUniv (a₀ + 1) a₀ r, hUniv a₀ (a₀ + 1) 0, hφ0] at hr
    have hsub : a₀ + 1 - a₀ = (1 : ℝ) := by ring
    rw [hsub] at hr
    linarith [hr]
  have hprod : cMom * g a₀ ≠ 0 := mul_ne_zero hcMom hga₀
  have hbne : S.hb a₀ (a₀ + 1) 0 ≠ 0 := by
    intro h0
    have h1 := key 1
    rw [h0, zero_mul, mul_one] at h1
    exact hprod h1.symm
  refine ⟨cMom * g a₀ / (2 * S.hb a₀ (a₀ + 1) 0), ?_, ?_⟩
  · exact div_ne_zero hprod (mul_ne_zero two_ne_zero hbne)
  · intro a b p
    rw [hUniv a b p]
    refine mul_left_cancel₀ hbne ?_
    rw [key p]
    field_simp

/-- The derived coefficient does not depend on which point was used to read it
off: any two constants presenting the same response agree. -/
theorem kinetic_coefficient_unique {h : LocalHamProfile} (S : LocalHamSmooth h)
    (c₁ c₂ : ℝ)
    (h₁ : ∀ a b p : ℝ, S.hp a b p = (2 * c₁) * p)
    (h₂ : ∀ a b p : ℝ, S.hp a b p = (2 * c₂) * p) : c₁ = c₂ := by
  have hEq := (h₁ 0 0 1).symm.trans (h₂ 0 0 1)
  linarith [hEq]

/-- Every universal-response target is kinetic-normalized. -/
def UniversalKineticCanonicalMom.toKineticNormalized
    (T : UniversalKineticCanonicalMom) : KineticNormalizedCanonicalMom where
  target := T.target
  kinetic_normalized := by
    obtain ⟨h, S, φ, hcd, hHam, hUniv, hφ0⟩ := T.universal_response
    obtain ⟨g, hG⟩ := T.target.structure_profile
    obtain ⟨cMom, hcMom, hMom⟩ := T.target.canonical_mom
    obtain ⟨cKin, hcKin, hHp⟩ :=
      kinetic_normalization_of_universal_response T.target h S g cMom φ hHam hG
        hcMom hMom hUniv hφ0
    exact ⟨h, S, cKin, hcd, hcKin, hHam, hHp⟩

/-- And conversely, so the two classes are the same class and §2 is an
equivalence rather than an enlargement. -/
def KineticNormalizedCanonicalMom.toUniversalKinetic
    (T : KineticNormalizedCanonicalMom) : UniversalKineticCanonicalMom where
  target := T.target
  universal_response := by
    obtain ⟨h, S, cKin, hcd, _hcKin, hHam, hHp⟩ := T.kinetic_normalized
    exact ⟨h, S, fun p => (2 * cKin) * p, hcd, hHam, hHp, by ring⟩

/-- **Rigidity without the assumed normalization.** The ADM shape and the
canonical momentum form hold for every target whose momentum response is merely
field-independent and stationary at zero momentum. -/
theorem HKTRigidityUniversalKineticN2_holds (T : UniversalKineticCanonicalMom) :
    ∃ cKin cGrad cMom : ℝ, ∃ V : ℝ → ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.target.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (T.target.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              V (x.1 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.target.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) :=
  HKTRigidityKineticNormalizedN2_holds T.toKineticNormalized

/-! ## §3. Channel separation, and where its provenance stops -/

/-- The density splits into a momentum-channel cost and a link term, with the
momentum channel stationary at zero momentum.

`Foundation.JHessianGolden.additivePosting` formalizes recognition cost as
posted additively coordinate by coordinate, `Φ(x) = Σᵢ J(xᵢ)`, with Hessian
`diag(J''(xᵢ))`; this is that additivity for a two-channel split, and the
stationarity clause is `J'(1) = 0` transported to the momentum chart. The two
theorems below show this is logically the same hypothesis as §2's, so the
recognition layer supplies provenance and not strength. -/
def ChannelSeparated (h : LocalHamProfile) : Prop :=
  ∃ (K : ℝ → ℝ) (U : ℝ → ℝ → ℝ),
    (∀ a b p : ℝ, h a b p = K p + U a b) ∧ HasDerivAt K 0 0

theorem universal_of_channelSeparated
    (h : LocalHamProfile) (S : LocalHamSmooth h)
    (hcd : ContDiff ℝ 2 (profileMap h)) (hCS : ChannelSeparated h) :
    ∃ φ : ℝ → ℝ, (∀ a b p : ℝ, S.hp a b p = φ p) ∧ φ 0 = 0 := by
  obtain ⟨K, U, hEq, hK0⟩ := hCS
  have hKderiv : ∀ a b p : ℝ, HasDerivAt K (S.hp a b p) p := by
    intro a b p
    have hS := hasDerivAt_hp_of_normalized h S hcd a b p
    have hfun : (fun t => h a b t) = fun t => K t + U a b :=
      funext fun t => hEq a b t
    rw [hfun] at hS
    simpa using hS.add_const (-(U a b))
  refine ⟨fun p => S.hp 0 0 p, ?_, ?_⟩
  · intro a b p
    exact (hKderiv a b p).unique (hKderiv 0 0 p)
  · exact (hKderiv 0 0 0).unique hK0

theorem channelSeparated_of_universal
    (h : LocalHamProfile) (S : LocalHamSmooth h)
    (hcd : ContDiff ℝ 2 (profileMap h)) (φ : ℝ → ℝ)
    (hUniv : ∀ a b p : ℝ, S.hp a b p = φ p) (hφ0 : φ 0 = 0) :
    ChannelSeparated h := by
  refine ⟨fun p => h 0 0 p - h 0 0 0, fun a b => h a b 0, ?_, ?_⟩
  · intro a b p
    have hF : ∀ t : ℝ, HasDerivAt (fun u => h a b u - h 0 0 u) 0 t := by
      intro t
      have h1 := hasDerivAt_hp_of_normalized h S hcd a b t
      have h2 := hasDerivAt_hp_of_normalized h S hcd 0 0 t
      have hsub := h1.sub h2
      rw [hUniv a b t, hUniv 0 0 t, sub_self] at hsub
      exact hsub
    have hdiff : Differentiable ℝ (fun u => h a b u - h 0 0 u) :=
      fun t => (hF t).differentiableAt
    have hconst :=
      is_const_of_deriv_eq_zero hdiff (fun t => (hF t).deriv) p 0
    simp only at hconst
    linarith [hconst]
  · have h1 := hasDerivAt_hp_of_normalized h S hcd 0 0 0
    rw [hUniv 0 0 0, hφ0] at h1
    exact h1.sub_const (h 0 0 0)

/-! ## §4. The exact recognition cost is excluded -/

/-- A local Hamiltonian density carrying its momentum dependence as the
recognition cost of a ledger imbalance, read in the log-imbalance chart: the
momentum `p` sits at ledger ratio `exp (κ * p)`, whose cost is `Jlog (κ * p)`,
with cost weight `w`. Both `w` and `κ` are free constants. -/
def costKineticProfile (w κ : ℝ) (U : ℝ → ℝ → ℝ) : LocalHamProfile :=
  fun a b p => w * Cost.Jlog (κ * p) + U a b

/-- A `CanonicalMom` target whose momentum sector is the exact recognition cost. -/
structure CostKineticCanonicalMom where
  target : HKTPointSplitTargetDynCanonicalMom
  cost_kinetic :
    ∃ (h : LocalHamProfile) (S : LocalHamSmooth h) (w κ : ℝ) (U : ℝ → ℝ → ℝ),
      ContDiff ℝ 2 (profileMap h) ∧ w ≠ 0 ∧ κ ≠ 0 ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          target.hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j)) ∧
          (∀ a b p : ℝ, h a b p = w * Cost.Jlog (κ * p) + U a b)

/-- The momentum response of a recognition-cost density is `w κ sinh (κ p)`,
derived from `Jlog = cosh - 1` rather than assumed. -/
theorem costKinetic_hp_eq_sinh
    (h : LocalHamProfile) (S : LocalHamSmooth h) (w κ : ℝ) (U : ℝ → ℝ → ℝ)
    (hcd : ContDiff ℝ 2 (profileMap h))
    (hProf : ∀ a b p : ℝ, h a b p = w * Cost.Jlog (κ * p) + U a b)
    (a b p : ℝ) :
    S.hp a b p = w * (Real.sinh (κ * p) * κ) := by
  have hS := hasDerivAt_hp_of_normalized h S hcd a b p
  have hfun : (fun t => h a b t) = fun t => w * Cost.Jlog (κ * t) + U a b :=
    funext fun t => hProf a b t
  rw [hfun] at hS
  have hinner : HasDerivAt (fun t : ℝ => κ * t) κ p := by
    simpa using (hasDerivAt_id p).const_mul κ
  have hJ : HasDerivAt (fun t : ℝ => Cost.Jlog (κ * t)) (Real.sinh (κ * p) * κ) p :=
    (Cost.hasDerivAt_Jlog (κ * p)).comp p hinner
  have hexp : HasDerivAt (fun t : ℝ => w * Cost.Jlog (κ * t) + U a b)
      (w * (Real.sinh (κ * p) * κ)) p := (hJ.const_mul w).add_const (U a b)
  exact hS.unique hexp

/-- The cost form satisfies §2's two hypotheses: field-independence because the
cost reads the imbalance alone, vanishing at zero momentum because the cost is
stationary at the balanced ratio. -/
theorem costKinetic_universal
    (h : LocalHamProfile) (S : LocalHamSmooth h) (w κ : ℝ) (U : ℝ → ℝ → ℝ)
    (hcd : ContDiff ℝ 2 (profileMap h))
    (hProf : ∀ a b p : ℝ, h a b p = w * Cost.Jlog (κ * p) + U a b) :
    (∀ a b p : ℝ, S.hp a b p = w * (Real.sinh (κ * p) * κ)) ∧
      w * (Real.sinh (κ * 0) * κ) = 0 := by
  refine ⟨costKinetic_hp_eq_sinh h S w κ U hcd hProf, ?_⟩
  rw [mul_zero, Real.sinh_zero, zero_mul, mul_zero]

private theorem one_lt_cosh_one : (1 : ℝ) < Real.cosh 1 := by
  rw [Real.cosh_eq]
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  linarith

private theorem sinh_one_pos : (0 : ℝ) < Real.sinh 1 := by
  rw [Real.sinh_eq]
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp (-1) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
  rw [Real.exp_zero] at h2
  linarith

/-- `sinh` is not linear: no constant rescaling of the identity matches it. -/
theorem sinh_not_linear (c : ℝ) : ¬ ∀ t : ℝ, Real.sinh t = c * t := by
  intro hlin
  have h1 : Real.sinh 1 = c := by
    have := hlin 1
    linarith [this]
  have h2 : Real.sinh 2 = c * 2 := hlin 2
  have htwo : Real.sinh (2 * (1 : ℝ)) = 2 * Real.sinh 1 * Real.cosh 1 :=
    Real.sinh_two_mul 1
  rw [show (2 * (1 : ℝ)) = 2 by norm_num] at htwo
  rw [h2, h1] at htwo
  have hcpos : (0 : ℝ) < c := by rw [← h1]; exact sinh_one_pos
  nlinarith [one_lt_cosh_one, hcpos, htwo]

/-- **The exclusion, in the linear chart only.** No nondegenerate `CanonicalMom`
point-split target carries the exact recognition cost in its momentum sector
*when the momentum is identified with the log-imbalance linearly*, `t = κ p`.

§2 forces the momentum response linear; §4 makes it `w κ sinh (κ p)`; `sinh` is
not linear. Read the scope literally: `CostKineticCanonicalMom` hardcodes the
linear chart, so this excludes that chart and not the cost. §8 exhibits a chart in
which the same exact cost is quadratic and does inhabit the algebra, so this is a
no-go about a coordinate identification rather than about recognition. It is also
not a statement that the higher terms are a physical correction: in this chart
they leave the algebra rather than deform it. -/
theorem no_exact_cost_kinetic_canonicalMom : IsEmpty CostKineticCanonicalMom := by
  constructor
  intro T
  obtain ⟨h, S, w, κ, U, hcd, hw, hκ, hHam, hProf⟩ := T.cost_kinetic
  obtain ⟨g, hG⟩ := T.target.structure_profile
  obtain ⟨cMom, hcMom, hMom⟩ := T.target.canonical_mom
  obtain ⟨hHp, hφ0⟩ := costKinetic_universal h S w κ U hcd hProf
  obtain ⟨cKin, _hcKin, hLin⟩ :=
    kinetic_normalization_of_universal_response T.target h S g cMom
      (fun p => w * (Real.sinh (κ * p) * κ)) hHam hG hcMom hMom hHp hφ0
  have hall : ∀ p : ℝ, w * (Real.sinh (κ * p) * κ) = (2 * cKin) * p := by
    intro p
    rw [← hHp 0 0 p]
    exact hLin 0 0 p
  refine sinh_not_linear (2 * cKin / (w * κ * κ)) ?_
  intro t
  have ht := hall (t / κ)
  rw [mul_div_cancel₀ t hκ] at ht
  field_simp at ht ⊢
  nlinarith [ht]

/-! ## §5. The surviving object: the balance jet -/

/-- The recognition cost's curvature at the balanced ratio, `deriv (deriv Jcost) 1`,
proved equal to `1` in `Cost/Convexity.lean`. -/
def recogCurvature : ℝ := deriv (deriv Cost.Jcost) 1

theorem recogCurvature_eq_one : recogCurvature = 1 := Cost.deriv2_Jcost_one

/-- The second-order jet of the recognition cost about balance, written so that
its coefficient is literally the recognition primitive. -/
def JlogQuad (t : ℝ) : ℝ := (recogCurvature / 2) * t ^ 2

theorem JlogQuad_eq_half_sq (t : ℝ) : JlogQuad t = t ^ 2 / 2 := by
  rw [JlogQuad, recogCurvature_eq_one]; ring

theorem deriv_Jlog_eq_sinh : deriv Cost.Jlog = Real.sinh :=
  funext fun t => (Cost.hasDerivAt_Jlog t).deriv

/-- The curvature of the recognition cost at balance, computed in the
log-imbalance chart, is `J''(1)`. -/
theorem deriv2_Jlog_zero_eq_recogCurvature :
    deriv (deriv Cost.Jlog) 0 = recogCurvature := by
  rw [deriv_Jlog_eq_sinh, Real.deriv_sinh, Real.cosh_zero, recogCurvature_eq_one]

theorem hasDerivAt_JlogQuad (t : ℝ) :
    HasDerivAt JlogQuad (recogCurvature * t) t := by
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_id t).pow 2
  have hmul := hsq.const_mul (recogCurvature / 2)
  have hrw : recogCurvature / 2 * (2 * t) = recogCurvature * t := by ring
  rw [hrw] at hmul
  exact hmul

private theorem deriv_JlogQuad_eq : deriv JlogQuad = fun t => recogCurvature * t :=
  funext fun t => (hasDerivAt_JlogQuad t).deriv

/-- `JlogQuad` is the second-order jet: value, slope, and curvature at balance
all agree with the exact recognition cost. -/
theorem JlogQuad_matches_Jlog_to_second_order :
    JlogQuad 0 = Cost.Jlog 0 ∧
      deriv JlogQuad 0 = deriv Cost.Jlog 0 ∧
        deriv (deriv JlogQuad) 0 = deriv (deriv Cost.Jlog) 0 := by
  have hval : JlogQuad 0 = Cost.Jlog 0 := by
    rw [JlogQuad_eq_half_sq, Cost.Jlog_as_cosh, Real.cosh_zero]; norm_num
  have hslope : deriv JlogQuad 0 = deriv Cost.Jlog 0 := by
    rw [deriv_JlogQuad_eq, deriv_Jlog_eq_sinh]
    show recogCurvature * (0 : ℝ) = Real.sinh 0
    rw [mul_zero, Real.sinh_zero]
  have hcurv : deriv (deriv JlogQuad) 0 = deriv (deriv Cost.Jlog) 0 := by
    rw [deriv_JlogQuad_eq, deriv2_Jlog_zero_eq_recogCurvature]
    have hlin : HasDerivAt (fun t : ℝ => recogCurvature * t) recogCurvature 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul recogCurvature
    exact hlin.deriv
  exact ⟨hval, hslope, hcurv⟩

/-- A local Hamiltonian density whose momentum sector is the recognition cost
truncated at its balance jet. -/
def quadCostKineticProfile (w κ : ℝ) (U : ℝ → ℝ → ℝ) : LocalHamProfile :=
  fun a b p => w * JlogQuad (κ * p) + U a b

/-- A `CanonicalMom` target whose momentum sector is the balance jet. -/
structure QuadCostKineticCanonicalMom where
  target : HKTPointSplitTargetDynCanonicalMom
  quad_cost_kinetic :
    ∃ (h : LocalHamProfile) (S : LocalHamSmooth h) (w κ : ℝ) (U : ℝ → ℝ → ℝ),
      ContDiff ℝ 2 (profileMap h) ∧ w ≠ 0 ∧ κ ≠ 0 ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          target.hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j)) ∧
          (∀ a b p : ℝ, h a b p = w * JlogQuad (κ * p) + U a b)

/-- The disclosed premise holds for a balance-jet density with

    cKin = w * κ ^ 2 * J''(1) / 2.

Field-independent because `J''` is evaluated at the balanced ratio, where it is
the universal number `1`; `J''` itself is `x ^ (-3)` and is not constant, so
field-independence is a property of balance and not an identity. `w` and `κ`
are free, so this expression fixes no number: it is a consistency statement, not
a prediction. -/
theorem quadCost_hp_eq_linear
    (h : LocalHamProfile) (S : LocalHamSmooth h) (w κ : ℝ) (U : ℝ → ℝ → ℝ)
    (hcd : ContDiff ℝ 2 (profileMap h))
    (hProf : ∀ a b p : ℝ, h a b p = w * JlogQuad (κ * p) + U a b)
    (a b p : ℝ) :
    S.hp a b p = (2 * (w * κ ^ 2 * recogCurvature / 2)) * p := by
  have hS := hasDerivAt_hp_of_normalized h S hcd a b p
  have hfun : (fun t => h a b t) = fun t => w * JlogQuad (κ * t) + U a b :=
    funext fun t => hProf a b t
  rw [hfun] at hS
  have hinner : HasDerivAt (fun t : ℝ => κ * t) κ p := by
    simpa using (hasDerivAt_id p).const_mul κ
  have hJ : HasDerivAt (fun t : ℝ => JlogQuad (κ * t))
      (recogCurvature * (κ * p) * κ) p :=
    (hasDerivAt_JlogQuad (κ * p)).comp p hinner
  have hexp : HasDerivAt (fun t : ℝ => w * JlogQuad (κ * t) + U a b)
      (w * (recogCurvature * (κ * p) * κ)) p := (hJ.const_mul w).add_const (U a b)
  rw [hS.unique hexp]
  ring

theorem quadCost_cKin_ne_zero {w κ : ℝ} (hw : w ≠ 0) (hκ : κ ≠ 0) :
    w * κ ^ 2 * recogCurvature / 2 ≠ 0 := by
  have hnum : w * κ ^ 2 * recogCurvature ≠ 0 := by
    rw [recogCurvature_eq_one, mul_one]
    exact mul_ne_zero hw (pow_ne_zero 2 hκ)
  exact div_ne_zero hnum (by norm_num : (2 : ℝ) ≠ 0)

/-- A balance-jet target inhabits the kinetic-normalized class with the derived
coefficient, so it consumes the derived form rather than an assumed field. -/
def QuadCostKineticCanonicalMom.toKineticNormalized
    (T : QuadCostKineticCanonicalMom) : KineticNormalizedCanonicalMom where
  target := T.target
  kinetic_normalized := by
    obtain ⟨h, S, w, κ, U, hcd, hw, hκ, hHam, hProf⟩ := T.quad_cost_kinetic
    exact ⟨h, S, w * κ ^ 2 * recogCurvature / 2, hcd,
      quadCost_cKin_ne_zero hw hκ, hHam,
      quadCost_hp_eq_linear h S w κ U hcd hProf⟩

/-- Every balance-jet target is ADM in shape with canonical momentum form, and
no normalization is assumed in the hypothesis. -/
theorem quadCost_ADM_rigidity (T : QuadCostKineticCanonicalMom) :
    ∃ cKin cGrad cMom : ℝ, ∃ V : ℝ → ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.target.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (T.target.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              V (x.1 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.target.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) :=
  HKTRigidityKineticNormalizedN2_holds T.toKineticNormalized

/-! ## §6. The load-bearing test -/

/-- **Removing field-independence breaks the proof.** The variable-kinetic
inhabitant of the kill tower carries the field-dependent weight `1 / (1 + a ^ 2)`
on its momentum term, which is exactly a cost weight that looks at the field. It
is excluded from the universal class, and the kill theorems in
`HKTKineticNormalizedRigidity` show the rigidity statement is false once such an
inhabitant is admitted. So field-independence does not merely strengthen the
conclusion; dropping it falsifies it. -/
theorem vacuumKinetic_not_universalKinetic :
    ¬ ∃ T : UniversalKineticCanonicalMom,
      T.target = vacuumKineticCanonicalMomTarget := by
  rintro ⟨T, hEq⟩
  exact vacuumKinetic_not_kineticNormalized ⟨T.toKineticNormalized, hEq⟩

/-- The ADM anchor still inhabits the weakened class, so §2 has not emptied it. -/
def hamDynUniversalKinetic : UniversalKineticCanonicalMom :=
  KineticNormalizedCanonicalMom.toUniversalKinetic hamDynKineticNormalized

theorem hamDyn_satisfies_universalKinetic :
    ∃ cKin cGrad cMom : ℝ, ∃ V : ℝ → ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynUniversalKinetic.target.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (hamDynUniversalKinetic.target.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              V (x.1 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynUniversalKinetic.target.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) :=
  HKTRigidityUniversalKineticN2_holds hamDynUniversalKinetic

/-! ## §7. Field-independence derived from a recognition primitive

**This route does not work, and the section is kept because knowing why is worth
more than the theorems are.** It is superseded by §8. The construction: let every
pair of neighbouring field values carry its own momentum-sector cost jet in one
global chart, with its own log-curvature `c a b`, so that field-independence is
absent from the shape; then impose
`Cost.FunctionalEquation.IsCalibrated (jetCost (c a b))` at each site, which
forces every `c a b` to `1`, hence the disclosed premise with `cKin = κ ^ 2 / 2`.
Everything below that sentence is proved, the class is nonempty, and the kill
inhabitant is excluded. It still fails, for three reasons, all of them found by a
cross-family panel (Opus 5, Grok 4.5, GPT-5.6 Sol, Kimi K3, 2026-07-25) and none
of them repaired here.

First, `jetCost` is a family this module defines, and
`IsCalibrated (jetCost c) ↔ c = 1` is settled by unfolding that definition. A
per-site condition whose unique solution is read off a definition is the
between-site equality renamed, so the defence that calibration looks at one site
while field-independence relates two sites is empty here. It has content only when
the uniqueness of the solution is a theorem, which is what §8 arranges.

Second, the value is absorbed. `cKin = κ ^ 2 / 2` with `κ` free, so the class of
targets with all curvatures equal to `1` in chart `κ` is the class with all
curvatures equal to any positive constant `c₀` in chart `κ / sqrt c₀`. The
recognition *number* `J''(1) = 1` therefore does no work; only the constancy does.

Third, `jetCost c` is not a recognition cost. It fails the Recognition
Composition Law for every nonzero `c` (`jetCost_not_rcl`, proved in §8). So this
section imposes a normalization on an object the substrate rejects.

What survives is the negative result, worth stating because it is general: a
recognition condition imposed pointwise carries logical weight only in proportion
to the depth of the uniqueness theorem behind it, and a condition whose value the
ambient free parameters can absorb carries none at all.
-/

/-- The multiplicative cost function whose balance jet has log-curvature `c`:
in the log-imbalance chart `x = exp t` it is `t ↦ (c / 2) * t ^ 2`. -/
def jetCost (c : ℝ) : ℝ → ℝ := fun x => (c / 2) * (Real.log x) ^ 2

theorem G_jetCost (c : ℝ) :
    Cost.FunctionalEquation.G (jetCost c) = fun t => (c / 2) * t ^ 2 := by
  funext t
  simp [Cost.FunctionalEquation.G, jetCost, Real.log_exp]

private theorem deriv_half_sq (c : ℝ) :
    deriv (fun t : ℝ => (c / 2) * t ^ 2) = fun t => c * t := by
  funext t
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_id t).pow 2
  have hmul := hsq.const_mul (c / 2)
  rw [show c / 2 * (2 * t) = c * t by ring] at hmul
  exact hmul.deriv

private theorem deriv_linear_zero (c : ℝ) : deriv (fun t : ℝ => c * t) 0 = c := by
  simpa using ((hasDerivAt_id (0 : ℝ)).const_mul c).deriv

/-- **Calibration reads off the jet coefficient.** A balance jet is calibrated
exactly when its log-curvature is `J''(1) = 1`.

Do not read `jetCost c` as a recognition cost. It satisfies no composition law
for any nonzero `c` (`jetCost_not_rcl`), and calling it one here would
contradict that theorem. It is a one-parameter deformation of the recognition
cost's jet, which is a different object. -/
theorem isCalibrated_jetCost_iff (c : ℝ) :
    Cost.FunctionalEquation.IsCalibrated (jetCost c) ↔ c = 1 := by
  unfold Cost.FunctionalEquation.IsCalibrated
  rw [G_jetCost, deriv_half_sq, deriv_linear_zero]

/-- `jetCost` is not an ad hoc family invented for this section. In the log chart
it is `t ↦ (c / 2) * t ^ 2`, and at the recognition curvature `c = J''(1)` that
is exactly `JlogQuad`, the balance jet of the actual recognition cost from §5. So
`jetCost` is the one-parameter deformation of the recognition cost's own jet, and
`isCalibrated_jetCost_iff` says the calibration axiom selects the undeformed
member. -/
theorem G_jetCost_recogCurvature :
    Cost.FunctionalEquation.G (jetCost recogCurvature) = JlogQuad := by
  rw [G_jetCost]
  funext t
  rw [JlogQuad]

/-- A local Hamiltonian density whose momentum sector is, at each pair of
neighbouring field values, the balance jet of that pair's own cost function,
read in one global chart `κ`. The log-curvature `c a b` is free to look at the
field: this shape does not assume field-independence. -/
def perSiteJetProfile (c : ℝ → ℝ → ℝ) (κ : ℝ) (U : ℝ → ℝ → ℝ) : LocalHamProfile :=
  fun a b p => (c a b / 2) * (κ * p) ^ 2 + U a b

/-- The calibration clause is a statement about the density, not about the
auxiliary family. Read the density in the log-imbalance chart `t = κ p`; the
clause holds at a site exactly when the density's curvature there, at balance, is
the recognition curvature `J''(1)`. Nothing is hidden in `jetCost`. -/
theorem isCalibrated_iff_density_curvature
    (c : ℝ → ℝ → ℝ) (κ : ℝ) (U : ℝ → ℝ → ℝ) (hκ : κ ≠ 0) (a b : ℝ) :
    Cost.FunctionalEquation.IsCalibrated (jetCost (c a b)) ↔
      deriv (deriv (fun t : ℝ => perSiteJetProfile c κ U a b (t / κ))) 0
        = recogCurvature := by
  have hchart : (fun t : ℝ => perSiteJetProfile c κ U a b (t / κ))
      = fun t : ℝ => (c a b / 2) * t ^ 2 + U a b := by
    funext t
    simp only [perSiteJetProfile]
    rw [mul_div_cancel₀ t hκ]
  have hshift : deriv (fun t : ℝ => (c a b / 2) * t ^ 2 + U a b)
      = deriv (fun t : ℝ => (c a b / 2) * t ^ 2) := by
    funext t
    exact deriv_add_const (f := fun u : ℝ => (c a b / 2) * u ^ 2) (x := t) (c := U a b)
  rw [isCalibrated_jetCost_iff, hchart, hshift, deriv_half_sq, deriv_linear_zero,
    recogCurvature_eq_one]

/-- A `CanonicalMom` target whose momentum sector is a per-site cost jet in a
global chart, with every site's jet *calibrated*. The jets are not recognition
costs; see `jetCost_not_rcl` and the section header. -/
structure CalibratedJetCanonicalMom where
  target : HKTPointSplitTargetDynCanonicalMom
  calibrated_jet :
    ∃ (h : LocalHamProfile) (S : LocalHamSmooth h) (c : ℝ → ℝ → ℝ) (κ : ℝ)
      (U : ℝ → ℝ → ℝ),
      ContDiff ℝ 2 (profileMap h) ∧ κ ≠ 0 ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          target.hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j)) ∧
          (∀ a b p : ℝ, h a b p = perSiteJetProfile c κ U a b p) ∧
          (∀ a b : ℝ, Cost.FunctionalEquation.IsCalibrated (jetCost (c a b)))

/-- **Field-independence, derived.** Calibration forces every site's
log-curvature to `1`, so the momentum response is `κ ^ 2 * p` at every pair of
field values, which is the disclosed premise with `cKin = κ ^ 2 / 2`. -/
theorem calibratedJet_hp_eq_linear
    (h : LocalHamProfile) (S : LocalHamSmooth h) (c : ℝ → ℝ → ℝ) (κ : ℝ)
    (U : ℝ → ℝ → ℝ)
    (hcd : ContDiff ℝ 2 (profileMap h))
    (hProf : ∀ a b p : ℝ, h a b p = perSiteJetProfile c κ U a b p)
    (hCal : ∀ a b : ℝ, Cost.FunctionalEquation.IsCalibrated (jetCost (c a b)))
    (a b p : ℝ) :
    S.hp a b p = (2 * (κ ^ 2 / 2)) * p := by
  have hc : c a b = 1 := (isCalibrated_jetCost_iff (c a b)).mp (hCal a b)
  have hS := hasDerivAt_hp_of_normalized h S hcd a b p
  have hfun : (fun t => h a b t) = fun t => (1 / 2 : ℝ) * (κ * t) ^ 2 + U a b := by
    funext t
    rw [hProf a b t]
    simp only [perSiteJetProfile, hc]
  rw [hfun] at hS
  have hinner : HasDerivAt (fun t : ℝ => κ * t) κ p := by
    simpa using (hasDerivAt_id p).const_mul κ
  have hsq : HasDerivAt (fun t : ℝ => (κ * t) ^ 2) (2 * (κ * p) * κ) p := by
    simpa using hinner.pow 2
  have hhalf := hsq.const_mul (1 / 2 : ℝ)
  rw [show (1 / 2 : ℝ) * (2 * (κ * p) * κ) = κ ^ 2 * p by ring] at hhalf
  rw [hS.unique (hhalf.add_const (U a b))]
  ring

theorem calibratedJet_cKin_ne_zero {κ : ℝ} (hκ : κ ≠ 0) : κ ^ 2 / 2 ≠ 0 :=
  div_ne_zero (pow_ne_zero 2 hκ) (by norm_num)

/-- A calibrated-jet target inhabits the kinetic-normalized class, with the
coefficient derived from the calibration axiom rather than assumed. -/
def CalibratedJetCanonicalMom.toKineticNormalized
    (T : CalibratedJetCanonicalMom) : KineticNormalizedCanonicalMom where
  target := T.target
  kinetic_normalized := by
    obtain ⟨h, S, c, κ, U, hcd, hκ, hHam, hProf, hCal⟩ := T.calibrated_jet
    exact ⟨h, S, κ ^ 2 / 2, hcd, calibratedJet_cKin_ne_zero hκ, hHam,
      calibratedJet_hp_eq_linear h S c κ U hcd hProf hCal⟩

/-- Every calibrated-jet target is ADM in shape, with the canonical momentum
relation. No field-independence appears anywhere in the hypothesis. -/
theorem calibratedJet_ADM_rigidity (T : CalibratedJetCanonicalMom) :
    ∃ cKin cGrad cMom : ℝ, ∃ V : ℝ → ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.target.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (T.target.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              V (x.1 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.target.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) :=
  HKTRigidityKineticNormalizedN2_holds T.toKineticNormalized

/-- **The class is nonempty, so the rigidity above is not vacuous.** The ADM
anchor's momentum sector is literally the calibrated recognition jet in the
chart `κ = 1`: `hamDynLocalProfile a b p = (1/2) * p ^ 2 + U a b`, which is
`perSiteJetProfile` with every log-curvature equal to the recognition primitive.
Nothing is fitted here; the anchor was written before this section existed. -/
def hamDynCalibratedJet : CalibratedJetCanonicalMom where
  target := hamDynPointSplitTargetCanonicalMom
  calibrated_jet := by
    refine ⟨hamDynLocalProfile, hamDynLocalSmooth, (fun _ _ => 1), 1,
      (fun a b => (1 / 2 : ℝ) * ((1 + a * a) * ((b - a) * (b - a)))),
      hamDynLocalProfile_contDiff2, one_ne_zero,
      hamDynDensity_eq_localProfile, ?_, ?_⟩
    · intro a b p
      simp only [hamDynLocalProfile, perSiteJetProfile]
      ring
    · intro _ _
      exact (isCalibrated_jetCost_iff 1).mpr rfl

instance : Nonempty CalibratedJetCanonicalMom := ⟨hamDynCalibratedJet⟩

theorem hamDyn_satisfies_calibratedJet :
    ∃ cKin cGrad cMom : ℝ, ∃ V : ℝ → ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynCalibratedJet.target.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (hamDynCalibratedJet.target.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              V (x.1 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynCalibratedJet.target.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) :=
  calibratedJet_ADM_rigidity hamDynCalibratedJet

/-! ### The removal test

The two theorems below are the discrimination. The first says the kill
inhabitant has exactly the per-site jet shape, so the shape assumption is not
secretly excluding it; the second says its jet at `a = 0` is uncalibrated, so
the recognition clause is what excludes it. -/

/-- The variable-kinetic kill inhabitant *is* a per-site jet profile: chart
`κ = 1`, log-curvatures `c a b = 2 / (1 + a ^ 2)`. So the shape assumed in this
section admits it. -/
theorem vacuumKineticLocalProfile_eq_perSiteJet :
    vacuumKineticLocalProfile
      = perSiteJetProfile (fun a _ => 2 * vacuumKineticA a) 1 vacuumKineticW := by
  funext a b p
  simp only [vacuumKineticLocalProfile, perSiteJetProfile]
  ring

/-- Its jet at `a = 0` has log-curvature `2`, not `1`, so it is not calibrated.
This is the clause that excludes it, and §7's header explains why excluding it
this way is worth less than it looks. -/
theorem vacuumKinetic_jet_not_calibrated :
    ¬ Cost.FunctionalEquation.IsCalibrated (jetCost (2 * vacuumKineticA 0)) := by
  rw [isCalibrated_jetCost_iff]
  simp only [vacuumKineticA]
  norm_num

/-- **The kill inhabitant is excluded by the recognition clause.** Together with
`not_HKTRigidityModVacuumStatementN2`, which says the rigidity conclusion is
false once this inhabitant is admitted, and with
`vacuumKineticLocalProfile_eq_perSiteJet`, which says the shape assumption alone
does admit it: deleting the calibration clause does not weaken the theorem, it
falsifies it. -/
theorem vacuumKinetic_not_calibratedJet :
    ¬ ∃ T : CalibratedJetCanonicalMom,
      T.target = vacuumKineticCanonicalMomTarget := by
  rintro ⟨T, hEq⟩
  exact vacuumKinetic_not_kineticNormalized ⟨T.toKineticNormalized, hEq⟩

/-! ### The same primitive at the exact level

The jet argument above uses calibration. At the exact level the composition law
does the corresponding job on its own: it admits no free cost weight at all, so
a weight that looks at the field is not a recognition cost at any site where it
differs from one. This is why §4's exclusion cannot be dodged by rescaling. -/

/-- **The recognition composition law admits no free weight.** If `w * J`
satisfies the RCL then `w` is `0` or `1`. A single instance, `x = y = 2`,
already forces it. -/
theorem compositionLaw_forces_unit_weight (w : ℝ)
    (hComp : Cost.FunctionalEquation.SatisfiesCompositionLaw
      (fun x => w * Cost.Jcost x)) :
    w = 0 ∨ w = 1 := by
  have h := hComp 2 2 (by norm_num) (by norm_num)
  have e4 : Cost.Jcost (2 * 2) = 9 / 8 := by norm_num [Cost.Jcost]
  have e1 : Cost.Jcost (2 / 2) = 0 := by norm_num [Cost.Jcost]
  have e2 : Cost.Jcost 2 = 1 / 4 := by norm_num [Cost.Jcost]
  simp only [e4, e1, e2] at h
  have hquad : w * (w - 1) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp hquad with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/-- A field-dependent cost weight is not a family of recognition costs unless it
is constantly one. -/
theorem rcl_forces_field_independent_weight (W : ℝ → ℝ → ℝ)
    (hComp : ∀ a b : ℝ, Cost.FunctionalEquation.SatisfiesCompositionLaw
      (fun x => W a b * Cost.Jcost x))
    (hne : ∀ a b : ℝ, W a b ≠ 0) (a b : ℝ) : W a b = 1 :=
  (compositionLaw_forces_unit_weight (W a b) (hComp a b)).resolve_left (hne a b)

/-! ## §8. The exact recognition cost, in the chart where it is quadratic

§4 excluded the exact cost. That exclusion is real but narrower than its old
name: it excludes the *linear* chart `t = κ p`, in which the response is `sinh`
and cannot be linear. The chart is not forced, and there is one in which the
exact cost is quadratic on the nose. The recognition cost has the half-imbalance
form `J (exp t) = 2 * sinh (t / 2) ^ 2`, so identify the momentum with the
half-imbalance *sine* rather than with the imbalance itself,
`sinh (t / 2) = λ p`, equivalently `t = 2 * arsinh (λ p)`. Then

    J (exp (2 * arsinh (λ p))) = 2 * λ ^ 2 * p ^ 2

exactly, with no truncation and no jet (`Jlog_two_arsinh`). The exact recognition
cost inhabits the undeformed `CanonicalMom` algebra, §5's concession that only the
balance jet survives was an artifact of the linear chart, and open item 2 of this
module, the deformed algebra, is not needed for this purpose.

That removes the truncation but not the field dependence, since the cost weight
`W a b` is still free. Here the load is carried by the Recognition Composition
Law, and carried as a theorem rather than as a definition: `w * J` satisfies the
law only for `w` in `{0, 1}` (`compositionLaw_forces_unit_weight`), because a
rescaled recognition cost is not a recognition cost. Imposing the law site by
site therefore forces unit weight at every site, which is field-independence, and
it forces the sign, so `cKin = 2 * λ ^ 2 > 0`.

Why this is not §7 again. §7's clause was calibration of a family this module
itself defined; its unique solution is read off by unfolding a definition, its
value is absorbed by the free chart, and `jetCost_not_rcl` proves the family was
not a recognition cost at all. §8's clause is a nonlinear functional equation on
the repo's own `Cost.Jcost`, its unique solution is a theorem, and the
countermodel is exact rather than illustrative: delete the clause, take chart
`λ = 1/2` and weights `W a = 2 / (1 + a ^ 2)`, and the profile *is* the kill
inhabitant (`vacuumKineticLocalProfile_eq_exactCost`), which
`not_HKTRigidityModVacuumStatementN2` refutes. The exclusion is also proved
directly from the clause rather than routed through the older one
(`no_rcl_presentation_of_vacuumKinetic`).

What remains assumed is the whole of what remains: the chart is one global
constant `λ`. A site-dependent `λ a b` reproduces the kill inhabitant at unit
weight, so the momentum-channel identification is not discharged, and `λ` is
unfixed, so `cKin = 2 λ ^ 2` is a positivity statement and not a number.
Recognition supplies two facts the algebra does not: the cost weight cannot vary
from site to site, and it cannot be negative. It does not supply the magnitude.
-/

/-- **The recognition cost is exactly quadratic in the half-imbalance sine.**
`J (exp t) = 2 * sinh (t / 2) ^ 2`, so at `t = 2 * arsinh u` the cost is `2 u ^ 2`
with no truncation. This is the identity that repairs §4's chart. -/
theorem Jlog_two_arsinh (u : ℝ) : Cost.Jlog (2 * Real.arsinh u) = 2 * u ^ 2 := by
  have hbase := Real.cosh_sq_sub_sinh_sq (Real.arsinh u)
  rw [Real.sinh_arsinh] at hbase
  rw [Cost.Jlog_as_cosh, Real.cosh_two_mul, Real.sinh_arsinh]
  linarith

/-- A density posting the *exact* recognition cost of the momentum channel, read
in the half-imbalance-sine chart, with a per-site cost weight `W a b` that is
free to look at the field. -/
def exactCostKineticProfile (W : ℝ → ℝ → ℝ) (lam : ℝ) (U : ℝ → ℝ → ℝ) :
    LocalHamProfile :=
  fun a b p => W a b * Cost.Jlog (2 * Real.arsinh (lam * p)) + U a b

theorem exactCostKineticProfile_quadratic
    (W : ℝ → ℝ → ℝ) (lam : ℝ) (U : ℝ → ℝ → ℝ) (a b p : ℝ) :
    exactCostKineticProfile W lam U a b p
      = W a b * (2 * (lam * p) ^ 2) + U a b := by
  rw [exactCostKineticProfile, Jlog_two_arsinh]

/-- A `CanonicalMom` target posting the exact recognition cost of the momentum
channel, with every site's cost weight required to satisfy the Recognition
Composition Law. Field-independence is absent from the hypothesis. -/
structure RCLKineticCanonicalMom where
  target : HKTPointSplitTargetDynCanonicalMom
  rcl_kinetic :
    ∃ (h : LocalHamProfile) (S : LocalHamSmooth h) (W : ℝ → ℝ → ℝ) (lam : ℝ)
      (U : ℝ → ℝ → ℝ),
      ContDiff ℝ 2 (profileMap h) ∧ lam ≠ 0 ∧ (∀ a b : ℝ, W a b ≠ 0) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          target.hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j)) ∧
          (∀ a b p : ℝ, h a b p = exactCostKineticProfile W lam U a b p) ∧
          (∀ a b : ℝ, Cost.FunctionalEquation.SatisfiesCompositionLaw
            (fun x => W a b * Cost.Jcost x))

/-- **Field-independence, derived from the composition law.** The law forces unit
weight at every site, so the momentum response is `4 λ ^ 2 p` everywhere, which is
the disclosed premise with `cKin = 2 λ ^ 2`. -/
theorem rclKinetic_hp_eq_linear
    (h : LocalHamProfile) (S : LocalHamSmooth h) (W : ℝ → ℝ → ℝ) (lam : ℝ)
    (U : ℝ → ℝ → ℝ)
    (hcd : ContDiff ℝ 2 (profileMap h))
    (hW : ∀ a b : ℝ, W a b ≠ 0)
    (hProf : ∀ a b p : ℝ, h a b p = exactCostKineticProfile W lam U a b p)
    (hRCL : ∀ a b : ℝ, Cost.FunctionalEquation.SatisfiesCompositionLaw
      (fun x => W a b * Cost.Jcost x))
    (a b p : ℝ) :
    S.hp a b p = (2 * (2 * lam ^ 2)) * p := by
  have hw : W a b = 1 := rcl_forces_field_independent_weight W hRCL hW a b
  have hS := hasDerivAt_hp_of_normalized h S hcd a b p
  have hfun : (fun t => h a b t) = fun t => 2 * (lam * t) ^ 2 + U a b := by
    funext t
    rw [hProf a b t, exactCostKineticProfile_quadratic, hw, one_mul]
  rw [hfun] at hS
  have hinner : HasDerivAt (fun t : ℝ => lam * t) lam p := by
    simpa using (hasDerivAt_id p).const_mul lam
  have hsq : HasDerivAt (fun t : ℝ => (lam * t) ^ 2) (2 * (lam * p) * lam) p := by
    simpa using hinner.pow 2
  have htwo := hsq.const_mul (2 : ℝ)
  rw [show (2 : ℝ) * (2 * (lam * p) * lam) = (2 * (2 * lam ^ 2)) * p by ring] at htwo
  exact hS.unique (htwo.add_const (U a b))

/-- **Recognition fixes the sign.** The composition law admits no negative
weight, and the chart contributes a square, so the kinetic coefficient is
strictly positive. -/
theorem rclKinetic_cKin_pos {lam : ℝ} (hlam : lam ≠ 0) : 0 < 2 * lam ^ 2 := by
  have h1 : 0 < lam ^ 2 := by
    rcases hlam.lt_or_gt with h | h <;> nlinarith
  linarith

theorem rclKinetic_cKin_ne_zero {lam : ℝ} (hlam : lam ≠ 0) : 2 * lam ^ 2 ≠ 0 :=
  ne_of_gt (rclKinetic_cKin_pos hlam)

def RCLKineticCanonicalMom.toKineticNormalized
    (T : RCLKineticCanonicalMom) : KineticNormalizedCanonicalMom where
  target := T.target
  kinetic_normalized := by
    obtain ⟨h, S, W, lam, U, hcd, hlam, hW, hHam, hProf, hRCL⟩ := T.rcl_kinetic
    exact ⟨h, S, 2 * lam ^ 2, hcd, rclKinetic_cKin_ne_zero hlam, hHam,
      rclKinetic_hp_eq_linear h S W lam U hcd hW hProf hRCL⟩

/-- Full ADM rigidity for targets posting the exact recognition cost. -/
theorem rclKinetic_ADM_rigidity (T : RCLKineticCanonicalMom) :
    ∃ cKin cGrad cMom : ℝ, ∃ V : ℝ → ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.target.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (T.target.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              V (x.1 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.target.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) :=
  HKTRigidityKineticNormalizedN2_holds T.toKineticNormalized

/-- The kinetic coefficient of any target in the class is strictly positive, so
recognition rules out the wrong-sign kinetic term as well as the field-dependent
one. -/
theorem rclKinetic_positive_kinetic_coefficient (T : RCLKineticCanonicalMom) :
    ∃ cKin : ℝ, 0 < cKin ∧
      ∃ (h : LocalHamProfile) (S : LocalHamSmooth h),
        ∀ a b p : ℝ, S.hp a b p = (2 * cKin) * p := by
  obtain ⟨h, S, W, lam, U, hcd, hlam, hW, hHam, hProf, hRCL⟩ := T.rcl_kinetic
  exact ⟨2 * lam ^ 2, rclKinetic_cKin_pos hlam, h, S,
    rclKinetic_hp_eq_linear h S W lam U hcd hW hProf hRCL⟩

/-- **The class is nonempty.** The ADM anchor posts the exact recognition cost at
unit weight in the chart `λ = 1/2`, and its composition-law clause is the repo's
own theorem that `J` satisfies the law.

`λ = 1/2` **is** a fit, and an earlier version of this docstring claimed the
opposite. The chart constant is free, `cKin = 2 λ²`, and the value `1/2` was
chosen because it is what reproduces the anchor's coefficient. What is not
fitted is the weight, which the composition law forces to one, and the sign,
which `rclKinetic_cKin_pos` forces positive. The magnitude is open; see the
module header. -/
def hamDynRCLKinetic : RCLKineticCanonicalMom where
  target := hamDynPointSplitTargetCanonicalMom
  rcl_kinetic := by
    refine ⟨hamDynLocalProfile, hamDynLocalSmooth, (fun _ _ => 1), (1 / 2 : ℝ),
      (fun a b => (1 / 2 : ℝ) * ((1 + a * a) * ((b - a) * (b - a)))),
      hamDynLocalProfile_contDiff2, by norm_num, (fun _ _ => one_ne_zero),
      hamDynDensity_eq_localProfile, ?_, ?_⟩
    · intro a b p
      rw [exactCostKineticProfile_quadratic]
      simp only [hamDynLocalProfile]
      ring
    · intro _ _
      simpa only [one_mul] using
        Cost.SymplecticAction.jcost_satisfiesCompositionLaw_via_symplectic

instance : Nonempty RCLKineticCanonicalMom := ⟨hamDynRCLKinetic⟩

theorem hamDyn_satisfies_rclKinetic :
    ∃ cKin cGrad cMom : ℝ, ∃ V : ℝ → ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynRCLKinetic.target.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (hamDynRCLKinetic.target.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              V (x.1 j)) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynRCLKinetic.target.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) :=
  rclKinetic_ADM_rigidity hamDynRCLKinetic

/-! ### The removal test, exact this time -/

/-- **Deleting the composition-law clause readmits the kill inhabitant exactly.**
At chart `λ = 1/2` with weights `W a b = 2 / (1 + a ^ 2)`, the exact-cost profile
*is* `vacuumKineticLocalProfile`. Nothing is approximated and nothing is
illustrative: the shape without the clause contains the very target that
`not_HKTRigidityModVacuumStatementN2` uses to refute rigidity. -/
theorem vacuumKineticLocalProfile_eq_exactCost :
    vacuumKineticLocalProfile
      = exactCostKineticProfile (fun a _ => 2 * vacuumKineticA a) (1 / 2)
          vacuumKineticW := by
  funext a b p
  rw [exactCostKineticProfile_quadratic]
  simp only [vacuumKineticLocalProfile]
  ring

/-- Those weights are not recognition costs: at `a = 0` the weight is `2`, and
the composition law admits only `0` and `1`. -/
theorem vacuumKinetic_weight_not_rcl :
    ¬ Cost.FunctionalEquation.SatisfiesCompositionLaw
      (fun x => (2 * vacuumKineticA 0) * Cost.Jcost x) := by
  intro hComp
  rcases compositionLaw_forces_unit_weight _ hComp with h | h <;>
    · rw [show vacuumKineticA 0 = 1 by simp [vacuumKineticA]] at h
      norm_num at h

/-- **Direct exclusion, consuming the clause.** No composition-law-certified
presentation of the kill inhabitant's profile exists, in any chart. This does not
route through the older kinetic-normalization exclusion: the law forces unit
weight, and then two field values disagree about the coefficient. -/
theorem no_rcl_presentation_of_vacuumKinetic
    (W : ℝ → ℝ → ℝ) (lam : ℝ) (U : ℝ → ℝ → ℝ)
    (hW : ∀ a b : ℝ, W a b ≠ 0)
    (hRCL : ∀ a b : ℝ, Cost.FunctionalEquation.SatisfiesCompositionLaw
      (fun x => W a b * Cost.Jcost x)) :
    vacuumKineticLocalProfile ≠ exactCostKineticProfile W lam U := by
  intro hEq
  have hval : ∀ a b p : ℝ,
      vacuumKineticA a * (p * p) + vacuumKineticW a b
        = 2 * (lam * p) ^ 2 + U a b := by
    intro a b p
    have h := congrFun (congrFun (congrFun hEq a) b) p
    rw [exactCostKineticProfile_quadratic,
      rcl_forces_field_independent_weight W hRCL hW a b, one_mul] at h
    exact h
  have hU : ∀ a b : ℝ, vacuumKineticW a b = U a b := by
    intro a b
    have h := hval a b 0
    nlinarith [h]
  have hA : ∀ a : ℝ, vacuumKineticA a = 2 * lam ^ 2 := by
    intro a
    have h := hval a 0 1
    have hu := hU a 0
    nlinarith [h, hu]
  have h0 := hA 0
  have h1 := hA 1
  rw [show vacuumKineticA 0 = 1 by simp [vacuumKineticA]] at h0
  rw [show vacuumKineticA 1 = 1 / 2 by norm_num [vacuumKineticA]] at h1
  linarith

/-- **§7's family was not a recognition cost.** For every nonzero curvature the
jet family violates the composition law, the residual being
`-(c ^ 2 / 2) * (log x) ^ 2 * (log y) ^ 2`; at `x = y = e` the two sides are
`2 * c` and `c ^ 2 / 2 + 2 * c`. Calibration alone does not make an object a
recognition cost, which is the second reason §7 does not carry the load and §8
imposes the law itself. -/
theorem jetCost_not_rcl (c : ℝ) (hc : c ≠ 0) :
    ¬ Cost.FunctionalEquation.SatisfiesCompositionLaw (jetCost c) := by
  intro hComp
  have h := hComp (Real.exp 1) (Real.exp 1) (Real.exp_pos 1) (Real.exp_pos 1)
  have hmul : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
    rw [← Real.exp_add]; norm_num
  have hdiv : Real.exp 1 / Real.exp 1 = 1 := div_self (Real.exp_ne_zero 1)
  rw [hmul, hdiv] at h
  simp only [jetCost, Real.log_exp, Real.log_one] at h
  have hc2 : c * c = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp hc2 with h' | h' <;> exact hc h'

/-! ## §9. Axiom audit -/

#print axioms exists_structure_value_ne_zero
#print axioms kinetic_normalization_of_universal_response
#print axioms kinetic_coefficient_unique
#print axioms HKTRigidityUniversalKineticN2_holds
#print axioms universal_of_channelSeparated
#print axioms channelSeparated_of_universal
#print axioms costKinetic_hp_eq_sinh
#print axioms costKinetic_universal
#print axioms sinh_not_linear
#print axioms no_exact_cost_kinetic_canonicalMom
#print axioms recogCurvature_eq_one
#print axioms deriv2_Jlog_zero_eq_recogCurvature
#print axioms JlogQuad_matches_Jlog_to_second_order
#print axioms quadCost_hp_eq_linear
#print axioms quadCost_ADM_rigidity
#print axioms vacuumKinetic_not_universalKinetic
#print axioms hamDyn_satisfies_universalKinetic
#print axioms isCalibrated_jetCost_iff
#print axioms G_jetCost_recogCurvature
#print axioms isCalibrated_iff_density_curvature
#print axioms calibratedJet_hp_eq_linear
#print axioms calibratedJet_ADM_rigidity
#print axioms hamDyn_satisfies_calibratedJet
#print axioms vacuumKineticLocalProfile_eq_perSiteJet
#print axioms vacuumKinetic_jet_not_calibrated
#print axioms vacuumKinetic_not_calibratedJet
#print axioms compositionLaw_forces_unit_weight
#print axioms rcl_forces_field_independent_weight
#print axioms Jlog_two_arsinh
#print axioms exactCostKineticProfile_quadratic
#print axioms rclKinetic_hp_eq_linear
#print axioms rclKinetic_cKin_pos
#print axioms rclKinetic_ADM_rigidity
#print axioms rclKinetic_positive_kinetic_coefficient
#print axioms hamDyn_satisfies_rclKinetic
#print axioms vacuumKineticLocalProfile_eq_exactCost
#print axioms vacuumKinetic_weight_not_rcl
#print axioms no_rcl_presentation_of_vacuumKinetic
#print axioms jetCost_not_rcl

end

end HKTKineticFromRecognitionCost
end SevenGaps
end Gravity
end IndisputableMonolith
