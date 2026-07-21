import Mathlib
import IndisputableMonolith.Gravity.QuantumChannel.BMVPositive
import IndisputableMonolith.Gravity.QuantumChannel.NoClassicalMediator
import IndisputableMonolith.Gravity.QuantumChannel.SubstrateLocalAccess

/-!
# BMV Falsifier Band: the certified entanglement witness and the falsifier floor

## Panel framing (binding)

BMV entanglement is predicted by ANY quantum mediator, so this package is
permanently EXCLUDED from the pillar-3 discriminator slot. It cannot
distinguish RS from GR+QFT or from any other quantum-mediator model that
produces the same four branch phases (see
`same_branch_phases_same_BMV_witness` below, which records exactly why).

Instead, this package is the FALSIFIER FLOOR. What a clean null
formally refutes is stated exactly here, with no inflation:

* THEOREM (this file): under the package {Newtonian weak-field phase
  model (`BMVPositive.weakFieldPhase`, a MODEL input) + the named
  geometry (MODEL inputs of Section 1)}, the joint state is non-product
  (nonzero amplitude-matrix determinant), with the invariant certified
  in `[1/2, 7/10]`, bounded away from `0 mod 2 pi`. A measured product
  state at this geometry therefore contradicts THAT PACKAGE:
  `clean_null_refutes_rs` (model-point form) and
  `bmv_band_entanglement` (band-robust form).
* MODEL/OPEN (not formalized here or upstream): the premise that the
  RS gravitational channel produces the Newtonian weak-field phases at
  this geometry with this magnitude. The Track 2.C/2.D forcing theorems
  cited in `rs_amplitude_channel_unique` force the CHANNEL to be
  amplitude-linear under their named structural premises; they say
  nothing formal about the MAGNITUDE of the branch phases. The two
  halves of this module do not touch formally. Only with that
  unformalized premise added does "clean null refutes the package"
  extend to "clean null refutes the framework". The framework-level
  falsification reading is therefore MODEL/OPEN, not THEOREM.

## Honest tier

* THEOREM: all the algebra and the certified numeric bands in this file
  (kernel-checked, `norm_num` on exact rational literals; zero sorry,
  zero new axioms, no `native_decide`). The entanglement statement
  proved is exactly `det != 0`, the non-product criterion for the pure
  two-qubit branch state; no entanglement-entropy statement is used or
  claimed anywhere in this module.
* MODEL: the Newtonian weak-field phase formula, the choice of
  experimental geometry (masses, coherence time, branch separations),
  and the CODATA values of G and hbar, which are measured inputs, not
  RS derivations.
* MODEL/OPEN: the bridge premise that the RS channel reproduces the
  Newtonian weak-field phase magnitudes at this geometry (see above).
* The amplitude-channel forcing statement carries the exact structural
  premises of the existing Track 2.C/2.D modules; see the docstring of
  `rs_amplitude_channel_unique` for the honest premise list. Nothing is
  axiomatized here.

## Contents

1. `rs_bmv_witness_band`: at one named representative geometry
   (Bose-et-al-2017-style mass and time scales in a parallel
   two-interferometer configuration; see Section 1), the entangling
   invariant
   `dPhi = (G m1 m2 T / hbar)(1/r_LL + 1/r_RR - 1/r_LR - 1/r_RL)`
   equals the exact rational `26696 / 47475` (about `0.5623` rad), lies
   in the certified band `[1/2, 7/10]` with `0 < 1/2` and
   `7/10 < 2 pi`, and therefore the joint two-mass state at this
   geometry is non-product (nonzero amplitude-matrix determinant), via
   `BMVPositive.entangled_of_branchPhase_in_open_period`.
2. `rs_amplitude_channel_unique`: the strongest honest composition of
   the existing AmplitudeLinearForced* results tying the RS
   gravitational channel to the amplitude-linear one.
3. `bmv_band_entanglement`: the band-robust falsifier. ANY four branch
   phases whose entangling invariant lands in `[1/2, 7/10]` give a
   non-product state; `clean_null_refutes_rs` is its model-point
   instantiation at the exact rational geometry values.
4. `same_branch_phases_same_BMV_witness`: the non-discrimination
   disclosure. Any mediator model producing the same four branch phases
   yields the same amplitude matrix, determinant, and witness.
5. `BMVFalsifierStatus`: documentation status record, including the
   permanent pillar-3 exclusion flag.
-/

namespace IndisputableMonolith
namespace Gravity
namespace QuantumChannel
namespace BMVFalsifierBand

noncomputable section

/-! ## Section 1. Named experimental geometry and physical constants

All values are exact rational literals in SI units so that `norm_num`
can certify every band without floating point or `native_decide`.
-/

/-- CODATA Newtonian constant of gravitation,
`G = 6.674e-11 m^3 kg^-1 s^-2`, as the exact rational `6674 / 10^14`.
Provenance: CODATA recommended value, rounded to four significant
figures. MEASURED input, not an RS derivation. -/
def G_SI : ℝ := 6674 / 10 ^ 14

/-- Reduced Planck constant `hbar = 1.055e-34 J s`, as the exact
rational `1055 / 10^37`. Provenance: CODATA (exact SI hbar is
1.054571817e-34 J s), rounded to four significant figures. MEASURED
input, not an RS derivation. -/
def hbar_SI : ℝ := 1055 / 10 ^ 37

/-- MODEL: representative parallel two-interferometer geometry, mass 1.
`m1 = 1e-14 kg`, a Bose-et-al-2017-style microdiamond mass scale. -/
def m1_SI : ℝ := 1 / 10 ^ 14

/-- MODEL: representative parallel two-interferometer geometry, mass 2.
`m2 = 1e-14 kg`, equal test masses. -/
def m2_SI : ℝ := 1 / 10 ^ 14

/-- MODEL: representative parallel two-interferometer geometry,
interaction (coherence) time `T = 2.5 s`. -/
def T_SI : ℝ := 5 / 2

/-- MODEL: representative parallel two-interferometer geometry,
branch-pair distance `r_LL = 250e-6 m` (the inter-interferometer
distance; the LL and RR pairs sit directly across from each other).

Configuration note: `r_LL = r_RR = 250 um` with `r_LR = r_RL = 450 um`
violates the collinear-adjacent identity `r_LL + r_RR = r_LR + r_RL`,
so this is NOT the adjacent linear Bose et al. 2017 configuration. It
is realizable as the parallel two-interferometer BMV variant:
inter-interferometer distance `d = 250 um`, in-interferometer branch
separation `sqrt(450^2 - 250^2) um`, approximately `374 um`, so that
the cross pairs sit at `sqrt(d^2 + dx^2) = 450 um`. -/
def r_LL_SI : ℝ := 250 / 10 ^ 6

/-- MODEL: representative parallel two-interferometer geometry,
branch-pair distance `r_RR = 250e-6 m` (directly-across pair; see the
configuration note on `r_LL_SI`). -/
def r_RR_SI : ℝ := 250 / 10 ^ 6

/-- MODEL: representative parallel two-interferometer geometry,
branch-pair distance `r_LR = 450e-6 m` (diagonal cross pair; see the
configuration note on `r_LL_SI`). -/
def r_LR_SI : ℝ := 450 / 10 ^ 6

/-- MODEL: representative parallel two-interferometer geometry,
branch-pair distance `r_RL = 450e-6 m` (diagonal cross pair; see the
configuration note on `r_LL_SI`). -/
def r_RL_SI : ℝ := 450 / 10 ^ 6

/-! ## Section 2. The four weak-field branch phases and the invariant -/

/-- The weak-field branch phase `phi_LL` at the named geometry. -/
def phase_LL : ℝ :=
  BMVPositive.weakFieldPhase G_SI hbar_SI m1_SI m2_SI T_SI r_LL_SI

/-- The weak-field branch phase `phi_LR` at the named geometry. -/
def phase_LR : ℝ :=
  BMVPositive.weakFieldPhase G_SI hbar_SI m1_SI m2_SI T_SI r_LR_SI

/-- The weak-field branch phase `phi_RL` at the named geometry. -/
def phase_RL : ℝ :=
  BMVPositive.weakFieldPhase G_SI hbar_SI m1_SI m2_SI T_SI r_RL_SI

/-- The weak-field branch phase `phi_RR` at the named geometry. -/
def phase_RR : ℝ :=
  BMVPositive.weakFieldPhase G_SI hbar_SI m1_SI m2_SI T_SI r_RR_SI

/-- The entangling invariant
`dPhi = (G m1 m2 T / hbar)(1/r_LL + 1/r_RR - 1/r_LR - 1/r_RL)`
evaluated at the named geometry, via the weak-field formula of
`BMVPositive`. -/
def deltaPhi : ℝ :=
  BMVPositive.weakFieldBranchInvariant G_SI hbar_SI m1_SI m2_SI T_SI
    r_LL_SI r_LR_SI r_RL_SI r_RR_SI

/-- The `BMVPositive.branchPhaseInvariant` of the four named phases is
definitionally the weak-field invariant `deltaPhi`. -/
theorem branchPhaseInvariant_eq_deltaPhi :
    BMVPositive.branchPhaseInvariant phase_LL phase_LR phase_RL phase_RR
      = deltaPhi := rfl

/-! ## Section 3. The certified value and band (THEOREM) -/

/-- **Exact value.** At the named geometry the entangling invariant is
the exact rational `26696 / 47475`, approximately `0.562317` rad.
Kernel-checked rational arithmetic: the prefactor is
`G m1 m2 T / hbar = 16685 / 105500000 m = 1.5815e-4 m` (dimensions of
length: `[m^3 kg^-1 s^-2][kg][kg][s] / [kg m^2 s^-1] = m`) and the
geometric bracket is `2/(250e-6) - 2/(450e-6) = 32000/9 m^-1`. -/
theorem deltaPhi_eq_rat : deltaPhi = 26696 / 47475 := by
  unfold deltaPhi BMVPositive.weakFieldBranchInvariant
    BMVPositive.weakFieldPhase G_SI hbar_SI m1_SI m2_SI T_SI
    r_LL_SI r_LR_SI r_RL_SI r_RR_SI
  norm_num

/-- Certified lower band edge: `1/2 <= deltaPhi`. -/
theorem deltaPhi_ge_half : (1 / 2 : ℝ) ≤ deltaPhi := by
  rw [deltaPhi_eq_rat]; norm_num

/-- Certified upper band edge: `deltaPhi <= 7/10`. -/
theorem deltaPhi_le_seven_tenths : deltaPhi ≤ (7 / 10 : ℝ) := by
  rw [deltaPhi_eq_rat]; norm_num

/-- Strict positivity of the invariant. -/
theorem deltaPhi_pos : (0 : ℝ) < deltaPhi := by
  rw [deltaPhi_eq_rat]; norm_num

/-- The upper band edge is strictly below one period:
`7/10 < 2 pi` (using `3 < pi`). -/
theorem seven_tenths_lt_two_pi : (7 / 10 : ℝ) < 2 * Real.pi := by
  have h := Real.pi_gt_three
  linarith

/-- The invariant is strictly inside the open period `(0, 2 pi)`. -/
theorem deltaPhi_lt_two_pi : deltaPhi < 2 * Real.pi :=
  lt_of_le_of_lt deltaPhi_le_seven_tenths seven_tenths_lt_two_pi

/-- **Not congruent to zero mod 2 pi.** For every integer `n`, the
invariant differs from `n * (2 pi)`: the band `[1/2, 7/10]` excludes
`n <= 0` (those multiples are nonpositive) and `n >= 1` (those are at
least `2 pi > 6`). This is the formal content of "bounded away from 0
mod 2 pi". -/
theorem deltaPhi_not_congruent_zero (n : ℤ) :
    deltaPhi ≠ (n : ℝ) * (2 * Real.pi) := by
  intro h
  have hπ := Real.pi_gt_three
  have hlo := deltaPhi_ge_half
  have hhi := deltaPhi_le_seven_tenths
  rcases le_or_gt n 0 with hn | hn
  · have hn' : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    have hmul : (n : ℝ) * (2 * Real.pi) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hn' (by positivity)
    rw [h] at hlo
    linarith
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hmul : 2 * Real.pi ≤ (n : ℝ) * (2 * Real.pi) :=
      le_mul_of_one_le_left (by positivity) hn1
    rw [h] at hhi
    linarith

/-! ## Section 4. Target 1: the certified witness band (THEOREM) -/

/-- **RS BMV witness band.** At the named representative geometry
(MODEL inputs of Section 1), the entangling invariant lies in the
certified band `0 < 1/2 <= deltaPhi <= 7/10 < 2 pi`, and consequently
the joint two-mass state is entangled: the branch amplitude matrix has
nonzero determinant (non-product state), by
`BMVPositive.entangled_of_branchPhase_in_open_period`.

The band is THEOREM-grade (exact rational arithmetic, kernel checked);
the geometry itself is a MODEL choice. The witness magnitude is
`deltaPhi = 26696 / 47475`, approximately `0.562` rad. -/
theorem rs_bmv_witness_band :
    ((0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) ≤ deltaPhi ∧
      deltaPhi ≤ (7 / 10 : ℝ) ∧ (7 / 10 : ℝ) < 2 * Real.pi) ∧
    Matrix.det
      (BMVPositive.branchAmplitudeMatrix
        phase_LL phase_LR phase_RL phase_RR) ≠ 0 := by
  refine ⟨⟨by norm_num, deltaPhi_ge_half, deltaPhi_le_seven_tenths,
    seven_tenths_lt_two_pi⟩, ?_⟩
  apply BMVPositive.entangled_of_branchPhase_in_open_period
  · rw [branchPhaseInvariant_eq_deltaPhi]
    exact deltaPhi_pos
  · rw [branchPhaseInvariant_eq_deltaPhi]
    exact deltaPhi_lt_two_pi

/-- Convenience extraction: the joint state at the named geometry is
entangled (nonzero determinant of the branch amplitude matrix). -/
theorem rs_bmv_geometry_entangled :
    Matrix.det
      (BMVPositive.branchAmplitudeMatrix
        phase_LL phase_LR phase_RL phase_RR) ≠ 0 :=
  rs_bmv_witness_band.2

/-! ## Section 5. Target 2: the amplitude channel is the RS channel -/

/-- **RS amplitude channel unique (honest composition).** The strongest
statement available from the existing Track 2.C/2.D modules that the RS
gravitational channel is the amplitude-linear one. Exact premises:

1. Clauses 1 and 2 are conditional on a
   `NoClassicalMediator.T0T8ConsistentSubstrate`, which is by
   definition an `AmplitudeLinearForced.RecognitionCoupledFactorization`:
   the joint substrate is the binary tensor product
   `Signal8 (x)[C] Signal8`, the joint operator is `C`-linear and
   factorizes on pure tensors (the named factor-product STRUCTURAL
   hypothesis of Track 2.C), and the matter side equals the substrate
   recognition update `cyclic_shift` (the T0-T8 forcing-chain input).
   Under those premises the channel response is forced amplitude-linear
   (clause 1) and any density-only (CPTP-classical) response collapses
   to the zero response (clause 2). Source:
   `NoClassicalMediator.channel_forced_amplitude_linear_under_T0T8` and
   `NoClassicalMediator.no_classical_mediator_under_T0T8`.
2. Clause 3 replaces global pure-tensor factorization by the substrate
   measurement-access premise (`ArisesFromSubstrateAccess`: the channel
   response is a nonzero matter-section readout of a `C`-linear joint
   operator). Honesty disclosure: `SubstrateSemanticsUnconditional`
   proves `IsAmplitudeLinear R_C <-> EXISTS R_J,
   ArisesFromSubstrateAccess R_J R_C`, so this premise is provably
   equivalent to the conclusion; clause 3 is one direction of that iff
   and adds NO forcing content beyond the factor-product clauses 1-2.
   It is recorded because it is the semantic reading of
   amplitude-linearity used by the source modules, not as extra
   evidence. Source:
   `AmplitudeLinearForced.isAmplitudeLinear_channel_of_arisesFromSubstrateAccess`.

This is a STRUCTURAL THEOREM, conditional exactly on the listed named
structural premises. Nothing new is axiomatized here; the unconditional
lift (arbitrary joint operators, no access principle) remains open in
the source modules and is not claimed. -/
theorem rs_amplitude_channel_unique :
    (∀ F : NoClassicalMediator.T0T8ConsistentSubstrate,
        AmplitudeLinearForced.IsAmplitudeLinear F.R_C) ∧
    (∀ F : NoClassicalMediator.T0T8ConsistentSubstrate,
        AmplitudeLinearForced.IsDensityOnly F.R_C →
          ∀ φ : AmplitudeLinearForced.Signal8, F.R_C φ = 0) ∧
    (∀ (R_J : AmplitudeLinearForced.JointSubstrate →ₗ[ℂ]
              AmplitudeLinearForced.JointSubstrate)
       (R_C : AmplitudeLinearForced.Signal8 →
              AmplitudeLinearForced.Signal8),
        AmplitudeLinearForced.ArisesFromSubstrateAccess R_J R_C →
          AmplitudeLinearForced.IsAmplitudeLinear R_C) :=
  ⟨NoClassicalMediator.channel_forced_amplitude_linear_under_T0T8,
   fun F hDen φ =>
     NoClassicalMediator.no_classical_mediator_under_T0T8 F hDen φ,
   fun _ _ hAccess =>
     AmplitudeLinearForced.isAmplitudeLinear_channel_of_arisesFromSubstrateAccess
       hAccess⟩

/-! ## Section 6. Target 3: the falsifier floor (THEOREM) -/

/-- **Band-robust falsifier (THEOREM).** ANY four branch phases whose
entangling invariant `phi_LL + phi_RR - phi_LR - phi_RL` lands in the
certified band `[1/2, 7/10]` produce a non-product joint state: the
branch amplitude matrix has nonzero determinant. This is the
experimentally meaningful form: the observed phases need not equal the
model-point rationals exactly; any measurement or model uncertainty
that keeps the invariant inside the band preserves the contradiction
with a measured product state. Follows from the open-period witness
`BMVPositive.entangled_of_branchPhase_in_open_period` since
`0 < 1/2` and `7/10 < 2 pi`. -/
theorem bmv_band_entanglement
    (φ_LL φ_LR φ_RL φ_RR : ℝ)
    (hlo : (1 / 2 : ℝ) ≤
      BMVPositive.branchPhaseInvariant φ_LL φ_LR φ_RL φ_RR)
    (hhi : BMVPositive.branchPhaseInvariant φ_LL φ_LR φ_RL φ_RR ≤
      (7 / 10 : ℝ)) :
    Matrix.det
      (BMVPositive.branchAmplitudeMatrix φ_LL φ_LR φ_RL φ_RR) ≠ 0 := by
  apply BMVPositive.entangled_of_branchPhase_in_open_period
  · linarith
  · have h := seven_tenths_lt_two_pi
    linarith

/-- **Model-point instantiation of the falsifier.** This is the
band falsifier `bmv_band_entanglement` evaluated at the exact rational
model point: IF the observed branch phases equal the Newtonian
weak-field values at the named geometry EXACTLY (the four equality
hypotheses), THEN a measured product state (zero determinant, zero
entanglement witness) is a contradiction.

Honest scope: because the hypotheses are exact equalities to the
rational model values, this instantiation has no direct experimental
content by itself (its proof is substitution into
`rs_bmv_geometry_entangled`); the experimentally meaningful statement
is the band-robust `bmv_band_entanglement` above. What a clean null
under controlled decoherence at this geometry and coherence time
formally refutes is the package {Newtonian weak-field phase model +
this geometry}. Extending that to "refutes the framework" requires the
unformalized MODEL/OPEN premise that the RS channel produces the
Newtonian weak-field phase magnitudes at this geometry; see the module
header. The invariant at the model point sits in `[1/2, 7/10]`,
bounded away from `0 mod 2 pi` (`deltaPhi_not_congruent_zero`), so the
determinant is provably nonzero (`rs_bmv_geometry_entangled`); within
the stated package there is no free parameter with which to soften the
null. -/
theorem clean_null_refutes_rs
    (φ_LL φ_LR φ_RL φ_RR : ℝ)
    (hLL : φ_LL = phase_LL) (hLR : φ_LR = phase_LR)
    (hRL : φ_RL = phase_RL) (hRR : φ_RR = phase_RR)
    (hNull :
      Matrix.det
        (BMVPositive.branchAmplitudeMatrix φ_LL φ_LR φ_RL φ_RR) = 0) :
    False := by
  subst hLL; subst hLR; subst hRL; subst hRR
  exact rs_bmv_geometry_entangled hNull

/-! ## Section 7. Target 4: the non-discrimination disclosure -/

/-- **Same branch phases, same BMV witness.** Any mediator model that
produces the same four branch phases yields the same amplitude matrix,
the same determinant, and the same entangling invariant. The witness is
a function of the phases alone. This trivial congruence is stated
explicitly so the ledger records WHY the BMV package cannot
discriminate RS from GR+QFT (or any other quantum mediator producing
the weak-field phases): it is why this package is permanently excluded
from the pillar-3 discriminator slot and serves only as the falsifier
floor. -/
theorem same_branch_phases_same_BMV_witness
    {φ_LL φ_LR φ_RL φ_RR ψ_LL ψ_LR ψ_RL ψ_RR : ℝ}
    (hLL : φ_LL = ψ_LL) (hLR : φ_LR = ψ_LR)
    (hRL : φ_RL = ψ_RL) (hRR : φ_RR = ψ_RR) :
    BMVPositive.branchAmplitudeMatrix φ_LL φ_LR φ_RL φ_RR
      = BMVPositive.branchAmplitudeMatrix ψ_LL ψ_LR ψ_RL ψ_RR ∧
    Matrix.det (BMVPositive.branchAmplitudeMatrix φ_LL φ_LR φ_RL φ_RR)
      = Matrix.det
          (BMVPositive.branchAmplitudeMatrix ψ_LL ψ_LR ψ_RL ψ_RR) ∧
    BMVPositive.branchPhaseInvariant φ_LL φ_LR φ_RL φ_RR
      = BMVPositive.branchPhaseInvariant ψ_LL ψ_LR ψ_RL ψ_RR := by
  subst hLL; subst hLR; subst hRL; subst hRR
  exact ⟨rfl, rfl, rfl⟩

/-! ## Section 8. Target 5: status record -/

/-- Status record for the BMV falsifier-band package. Honest reading:
the flags below are set by definition in `bmvFalsifierStatus`; the
`rfl` projection theorems only confirm the definition, they carry no
mathematical content. This structure is a documentation record; the
mathematics lives in the theorems above (`rs_bmv_witness_band`,
`bmv_band_entanglement`, `clean_null_refutes_rs`,
`rs_amplitude_channel_unique`, `same_branch_phases_same_BMV_witness`).
The `excluded_from_pillar3` flag records the permanent panel decision:
BMV entanglement cannot discriminate between quantum-mediator models
(`same_branch_phases_same_BMV_witness`), so it is a falsifier floor,
never a pillar-3 discriminator. -/
structure BMVFalsifierStatus where
  /-- `rs_bmv_witness_band`: certified band and entanglement witness. -/
  witness_band_certified : Bool
  /-- `rs_amplitude_channel_unique`: forcing theorems cited with exact
  premises. -/
  amplitude_channel_theorem_cited : Bool
  /-- `bmv_band_entanglement` and `clean_null_refutes_rs`: the
  falsifier is a named theorem (band-robust and model-point forms). -/
  falsifier_named : Bool
  /-- Permanent exclusion from the pillar-3 discriminator slot. -/
  excluded_from_pillar3 : Bool

/-- The canonical status inhabitant: every flag is set `true` by
definition (documentation record, not a proof obligation). -/
def bmvFalsifierStatus : BMVFalsifierStatus where
  witness_band_certified := true
  amplitude_channel_theorem_cited := true
  falsifier_named := true
  excluded_from_pillar3 := true

theorem bmvFalsifierStatus_witness_band_certified :
    bmvFalsifierStatus.witness_band_certified = true := rfl

theorem bmvFalsifierStatus_amplitude_channel_theorem_cited :
    bmvFalsifierStatus.amplitude_channel_theorem_cited = true := rfl

theorem bmvFalsifierStatus_falsifier_named :
    bmvFalsifierStatus.falsifier_named = true := rfl

theorem bmvFalsifierStatus_excluded_from_pillar3 :
    bmvFalsifierStatus.excluded_from_pillar3 = true := rfl

/-- All four status flags at once. Each `rfl` confirms the definition
of `bmvFalsifierStatus` only; see the structure docstring. -/
theorem bmvFalsifierStatus_all :
    bmvFalsifierStatus.witness_band_certified = true ∧
    bmvFalsifierStatus.amplitude_channel_theorem_cited = true ∧
    bmvFalsifierStatus.falsifier_named = true ∧
    bmvFalsifierStatus.excluded_from_pillar3 = true :=
  ⟨rfl, rfl, rfl, rfl⟩

end

end BMVFalsifierBand
end QuantumChannel
end Gravity
end IndisputableMonolith
