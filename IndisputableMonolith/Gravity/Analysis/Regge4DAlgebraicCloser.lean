import IndisputableMonolith.Gravity.Analysis.Regge4DContinuumPreflight
import IndisputableMonolith.Gravity.Analysis.ReggeBlochM2Symbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeFlat4DHessianAssembly
import IndisputableMonolith.Gravity.Analysis.EdgeTTDecomposition4D
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DOrbitClassification

/-!
# Regge 4D algebraic closer: banked witnesses, full-moment skeleton, OPEN isotropy

QG full-theory campaign, 4D counterpart of `ReggeTTAlgebraicCloser`.
Consumes the frozen continuum preflight target and the geometry-derived
orbit / (1,1)-symbol stack.  Banks every immediately available algebraic
identity; names the full TT isotropy / gauge / plus-cross agreement
targets as OPEN Props with status flags `false`.

## What this module proves (THEOREM)

* Decoy: one-orbit `(1,1)` `m2Symbol` equals `-3`, not the frozen EH
  coefficient `einsteinHilbertTTCoefficient4D = -1/4` (via preflight).
* Plus / cross Frobenius-normalized TT witnesses inhabit
  `IsTTPolarization4D` (via preflight).
* Gauge: `(1,1)`-orbit `m2Symbol decoyGauge = 0` (via M2 module).
* Full zero-momentum moment object: sum over `HingeOrbitType` of
  `orbitZeroMomQuadratic`, identified with
  `trueWeightZeroMomQuadratic`, vanishing on axis TT plus and decoy
  gauge (via assembly theorems).

## OPEN (named Prop + status `false`; no sorry-as-proof)

* `Regge4DFullTTIsotropyTarget`: for every nonzero real direction and
  every Frobenius-normalized TT polarization, the all-orbit m² moment
  divided by `|k|²` equals `einsteinHilbertTTCoefficient4D = -1/4`.
* `Regge4DPureGaugeVanishesTarget`: pure-gauge all-orbit m² moment
  vanishes for every nonzero direction.
* `Regge4DPlusCrossAgreeTarget`: plus and cross normalized symbols agree.

## Disclosures (binding)

* Continuum symbol Prop is now the concrete transported sequence
  `finiteTransportedSymbol` (see `Regge4DTransportedAlgebraicCloser`);
  factorized `ReggeBlochAllOrbitSymbol4D` is not that object.
* Zero-momentum full-moment identities below remain banked witnesses;
  finite-momentum EH Tendsto lives in the transported closer as OPEN.
* This does **not** prove `S_RS_converges_EH_4d`.
* This does **not** flip `gap_action_recovery`.
* No `sorry`, no `admit`, no new axioms, no `native_decide`, no `: True`
  shells as headlines.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace Regge4DAlgebraicCloser

open BigOperators
open Regge4DContinuumPreflight
open ReggeBlochM2Symbol4D
open ReggeFlat4DHessianAssembly
open ReggeHinge4DOrbitClassification
open ReggeEdgeStencil4D
open EdgeTTDecomposition4D (axisWave axisTTPlus IsTT)

/-- Prefer the preflight matrix alias; both are definitionally `Matrix (Fin 4) (Fin 4) ℝ`. -/
abbrev Mat4 := Regge4DContinuumPreflight.Mat4

noncomputable section

/-! ## §1. Banked decoy and normalized TT witnesses -/

/-- Decoy: the single-orbit `(1,1)` m² coefficient is not the continuum EH
target. -/
theorem decoy_one_orbit_m2_ne_eh_coefficient :
    ReggeBlochM2Symbol4D.m2Symbol axisTTPlus = -3 ∧
      einsteinHilbertTTCoefficient4D = -(1 / 4 : ℝ) ∧
        (-3 : ℝ) ≠ -(1 / 4 : ℝ) :=
  decoy_one_orbit_m2_is_not_continuum_target

/-- Axis plus polarization, Frobenius-normalized, is TT. -/
theorem plus_normalized_isTTPolarization :
    IsTTPolarization4D axisWave axisTTPlusNormalized :=
  axisTTPlusNormalized_isTTPolarization

/-- Axis cross polarization, Frobenius-normalized, is TT. -/
theorem cross_normalized_isTTPolarization :
    IsTTPolarization4D axisWave axisTTCrossNormalized :=
  axisTTCrossNormalized_isTTPolarization

/-- Nonvacuity of the TT hypothesis class used by continuum targets. -/
theorem tt_witnesses_nonvacuous :
    IsTTPolarization4D axisWave axisTTPlusNormalized ∧
      IsTTPolarization4D axisWave axisTTCrossNormalized :=
  continuum_target_hypothesis_nonvacuous

/-! ## §2. Banked (1,1)-orbit gauge vanishing on the symbolDir ray -/

/-- Gauge: the closed-form `(1,1)` m² symbol vanishes on `decoyGauge`. -/
theorem gauge_m2Symbol_vanishes_on_decoy :
    ReggeBlochM2Symbol4D.m2Symbol decoyGauge = 0 :=
  m2Symbol_decoyGauge

/-- TT nonvacuity of the same one-orbit coefficient. -/
theorem one_orbit_m2Symbol_axis_ne_zero :
    ReggeBlochM2Symbol4D.m2Symbol axisTTPlus ≠ 0 :=
  m2Symbol_axisTTPlus_ne_zero

/-- Frozen EH coefficient value (definitional). -/
theorem eh_tt_coefficient_eq :
    einsteinHilbertTTCoefficient4D = -(1 / 4 : ℝ) :=
  einsteinHilbertTTCoefficient4D_eq

/-! ## §3. Full-moment object as orbit sum (AllOrbit module absent) -/

/-- Per-orbit contribution to the full zero-momentum moment. -/
def fullMomentOrbitContribution (ty : HingeOrbitType) (H : Mat4) : ℝ :=
  orbitZeroMomQuadratic ty H

/-- Full zero-momentum moment: sum of orbit contributions over every
`HingeOrbitType`.  When `ReggeBlochAllOrbitSymbol4D` lands, its finite-
momentum m² polynomial is the intended continuum-facing upgrade of this
object; the zero-momentum reduction must continue to match. -/
def fullMomentZeroMomentum (H : Mat4) : ℝ :=
  ∑ ty : HingeOrbitType, fullMomentOrbitContribution ty H

theorem fullMomentZeroMomentum_eq_trueWeight (H : Mat4) :
    fullMomentZeroMomentum H = trueWeightZeroMomQuadratic H := by
  unfold fullMomentZeroMomentum fullMomentOrbitContribution
    trueWeightZeroMomQuadratic
  rfl

theorem fullMomentOrbitContribution_eq_bilinear (ty : HingeOrbitType)
    (H : Mat4) :
    fullMomentOrbitContribution ty H = orbitZeroMomBilinear ty H H :=
  orbitZeroMomQuadratic_eq_bilinear ty H

theorem fullMomentZeroMomentum_eq_bilinear (H : Mat4) :
    fullMomentZeroMomentum H = trueWeightZeroMomBilinear H H := by
  rw [fullMomentZeroMomentum_eq_trueWeight,
    trueWeightZeroMomQuadratic_eq_bilinear]

/-- Zero-momentum full moment vanishes on axis TT plus. -/
theorem fullMomentZeroMomentum_axisTTPlus :
    fullMomentZeroMomentum axisTTPlus = 0 := by
  rw [fullMomentZeroMomentum_eq_trueWeight,
    trueWeightZeroMomQuadratic_axisTTPlus]

/-- Zero-momentum full moment vanishes on decoy gauge. -/
theorem fullMomentZeroMomentum_decoyGauge :
    fullMomentZeroMomentum decoyGauge = 0 := by
  rw [fullMomentZeroMomentum_eq_trueWeight,
    trueWeightZeroMomQuadratic_decoyGauge]

/-- Zero-momentum full moment vanishes on decoy trace / homothety. -/
theorem fullMomentZeroMomentum_decoyTrace :
    fullMomentZeroMomentum decoyTrace = 0 := by
  rw [fullMomentZeroMomentum_eq_trueWeight,
    trueWeightZeroMomQuadratic_decoyTrace]

/-- Per-orbit deficit annihilation implies per-orbit contribution zero. -/
theorem fullMomentOrbitContribution_of_deficit_zero
    (ty : HingeOrbitType) (H : Mat4)
    (h : classDot (orbitDeficitKernel ty) H = 0) :
    fullMomentOrbitContribution ty H = 0 := by
  unfold fullMomentOrbitContribution orbitZeroMomQuadratic
  rw [h, mul_zero]

theorem fullMomentOrbitContribution_axisTTPlus (ty : HingeOrbitType) :
    fullMomentOrbitContribution ty axisTTPlus = 0 :=
  fullMomentOrbitContribution_of_deficit_zero ty _
    (orbitDeficit_dot_axisTTPlus ty)

theorem fullMomentOrbitContribution_decoyGauge (ty : HingeOrbitType) :
    fullMomentOrbitContribution ty decoyGauge = 0 :=
  fullMomentOrbitContribution_of_deficit_zero ty _
    (orbitDeficit_dot_decoyGauge ty)

/-! ## §4. OPEN algebraic continuum targets

These are the algebraic-layer packaging of the preflight continuum Props.
They quantify over real directions and Frobenius-normalized TT data.
Status flags below stay `false`; inhabitation is deferred to later
modules that supply the all-orbit finite-momentum m² moment.
-/

/-- Integer mode matching the axis wave `(1,0,0,0)` used by the plus/cross
witnesses. -/
def axisIntMode : IntMode4 :=
  fun i => if i = 0 then (1 : ℤ) else 0

/-- **OPEN**: algebraic packaging of the preflight continuum EH target.
For every nonzero integer mode and Frobenius-normalized TT polarization,
the `|k|²`-normalized **concrete transported** continuum symbol equals
`einsteinHilbertTTCoefficient4D = -1/4`. -/
def Regge4DFullTTIsotropyTarget : Prop :=
  Regge4DContinuumEHTarget

/-- **OPEN**: pure-gauge continuum symbol vanishes for every nonzero mode
and every gauge vector (preflight packaging). -/
def Regge4DPureGaugeVanishesTarget : Prop :=
  Regge4DContinuumGaugeZeroTarget

/-- **OPEN**: plus and cross normalized continuum symbols agree on the
axis mode (concrete transported sequences for each polarization). -/
def Regge4DPlusCrossAgreeTarget : Prop :=
  ∀ Λplus Λcross : ℝ,
    Regge4DContinuumSymbolIs axisIntMode axisTTPlusNormalized Λplus →
      Regge4DContinuumSymbolIs axisIntMode axisTTCrossNormalized Λcross →
        Λplus = Λcross

/-- Packaged algebraic closer target (all three OPEN conjuncts). -/
def Regge4DAlgebraicCloserTarget : Prop :=
  Regge4DFullTTIsotropyTarget ∧
    Regge4DPureGaugeVanishesTarget ∧
      Regge4DPlusCrossAgreeTarget

/-- Convenience: full isotropy implies the frozen coefficient value. -/
theorem fullTTIsotropyTarget_mentions_eh_coefficient :
    einsteinHilbertTTCoefficient4D = -(1 / 4 : ℝ) ∧
      Regge4DFullTTIsotropyTarget = Regge4DContinuumEHTarget :=
  ⟨einsteinHilbertTTCoefficient4D_eq, rfl⟩

/-! ## §5. Status flags (gap_action_recovery stays false) -/

structure Regge4DAlgebraicCloserStatus where
  decoyOneOrbitClosed : Bool
  plusCrossWitnessesClosed : Bool
  gaugeM2SymbolClosed : Bool
  fullMomentZeroMomClosed : Bool
  /-- Full TT isotropy at EH coefficient: still OPEN. -/
  fullTTIsotropyClosed : Bool
  /-- Pure-gauge vanishing for every direction: still OPEN. -/
  pureGaugeVanishesClosed : Bool
  /-- Plus/cross continuum agreement: still OPEN. -/
  plusCrossAgreeClosed : Bool
  /-- Continuum action recovery: not claimed here. -/
  srsConvergesEH4d : Bool
  /-- Ledger flag must stay false. -/
  gapActionRecovery : Bool

def regge4DAlgebraicCloserStatus : Regge4DAlgebraicCloserStatus where
  decoyOneOrbitClosed := true
  plusCrossWitnessesClosed := true
  gaugeM2SymbolClosed := true
  fullMomentZeroMomClosed := true
  fullTTIsotropyClosed := false
  pureGaugeVanishesClosed := false
  plusCrossAgreeClosed := false
  srsConvergesEH4d := false
  gapActionRecovery := false

theorem regge4DAlgebraicCloserStatus_flags :
    regge4DAlgebraicCloserStatus.decoyOneOrbitClosed = true ∧
      regge4DAlgebraicCloserStatus.plusCrossWitnessesClosed = true ∧
        regge4DAlgebraicCloserStatus.gaugeM2SymbolClosed = true ∧
          regge4DAlgebraicCloserStatus.fullMomentZeroMomClosed = true ∧
            regge4DAlgebraicCloserStatus.fullTTIsotropyClosed = false ∧
              regge4DAlgebraicCloserStatus.pureGaugeVanishesClosed = false ∧
                regge4DAlgebraicCloserStatus.plusCrossAgreeClosed = false ∧
                  regge4DAlgebraicCloserStatus.srsConvergesEH4d = false ∧
                    regge4DAlgebraicCloserStatus.gapActionRecovery = false := by
  decide

/-- Honesty: banked one-orbit identities do not inhabit the OPEN isotropy
target, and the ledger flag stays false. -/
theorem banked_does_not_flip_gap_or_isotropy :
    regge4DAlgebraicCloserStatus.fullTTIsotropyClosed = false ∧
      regge4DAlgebraicCloserStatus.gapActionRecovery = false ∧
        ReggeBlochM2Symbol4D.m2Symbol axisTTPlus ≠
          einsteinHilbertTTCoefficient4D := by
  refine ⟨rfl, rfl, ?_⟩
  rw [m2Symbol_axisTTPlus, einsteinHilbertTTCoefficient4D_eq]
  norm_num

end

end Regge4DAlgebraicCloser
end Analysis
end Gravity
end IndisputableMonolith
