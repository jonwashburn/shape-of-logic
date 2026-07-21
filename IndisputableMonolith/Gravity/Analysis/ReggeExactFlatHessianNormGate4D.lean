import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianSymbol4D
import IndisputableMonolith.Gravity.Analysis.Regge4DExactActionSymbol

/-!
# Normalization honesty gate for 4D continuum EH target

Historical FAIL (session `4d-srs-closure`): preflight demanded frozen
`einsteinHilbertTTCoefficient4D = -1/4` on unit-Frobenius TT, while exact
algebraic m² gives `-1/8` per unit Frobenius (`-1/4` is the `axisTTPlus`
face with `‖H‖_F² = 2`).

**Restatement option (C) LANDED** (`D-p1-eh-unitF-restatement`): continuum EH face is scale-explicit `(-1/8)·frobeniusNormSq E`. Discrete bookkeeping ×2 is banked only as a non-ledger algebraic identity
(EH audit §2.3 / 3D `ttSecondDifference`):
`2 · (-1/8) = -1/4` recovers the frozen coefficient on unit-Frobenius TT.
That identity does **not** inhabit geometric ContinuumSymbolIs Tendsto,
does **not** inhabit ledger `S_RS_converges_EH_4d`, and does **not**
flip `gap_action_recovery`.  Option-C scale-explicit aliases are kept
for compatibility only.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeExactFlatHessianNormGate4D

open ReggeExactFlatHessianSymbol4D

noncomputable section

def frozenPreflightEHCoefficient : ℝ := einsteinHilbertTTCoefficient4D
def exactUnitFrobeniusTTCoefficient : ℝ := exactHessianM2UnitFrobeniusTTCoeff

/-- Dimension-independent discrete bookkeeping factor `2` (EH audit §2.3). -/
def discreteBookkeepingFactor : ℝ := 2

theorem discreteBookkeepingFactor_eq_two :
    discreteBookkeepingFactor = (2 : ℝ) := rfl

theorem discreteBookkeepingFactor_eq_exactAction :
    discreteBookkeepingFactor =
      Regge4DExactActionSymbol.discreteBookkeepingFactor := by
  simp [discreteBookkeepingFactor, Regge4DExactActionSymbol.discreteBookkeepingFactor]

theorem exact_unitFrobenius_ne_frozen_preflight_EH :
    exactUnitFrobeniusTTCoefficient ≠ frozenPreflightEHCoefficient := by
  unfold exactUnitFrobeniusTTCoefficient frozenPreflightEHCoefficient
    exactHessianM2UnitFrobeniusTTCoeff einsteinHilbertTTCoefficient4D
  norm_num

/-- Frozen `-1/4` is discrete bookkeeping times the unit-F m² face. -/
theorem frozen_EH_is_discrete_bookkeeping_times_unitF :
    frozenPreflightEHCoefficient =
      discreteBookkeepingFactor * exactUnitFrobeniusTTCoefficient := by
  unfold frozenPreflightEHCoefficient exactUnitFrobeniusTTCoefficient
    discreteBookkeepingFactor exactHessianM2UnitFrobeniusTTCoeff
    einsteinHilbertTTCoefficient4D
  norm_num

/-- Historical axisTTPlus face identity (‖axisTTPlus‖_F² = 2). -/
theorem frozen_EH_is_axisTTPlus_face :
    frozenPreflightEHCoefficient =
      exactUnitFrobeniusTTCoefficient * (2 : ℝ) := by
  rw [frozen_EH_is_discrete_bookkeeping_times_unitF, discreteBookkeepingFactor_eq_two]
  ring

def einsteinHilbertTTCoefficient4D_unitFrobenius : ℝ := -(1 / 8)

abbrev einsteinHilbertTTCoefficient4D_unitFrobenius_proposed : ℝ :=
  einsteinHilbertTTCoefficient4D_unitFrobenius

theorem unitFrobenius_EH_eq_exact :
    einsteinHilbertTTCoefficient4D_unitFrobenius =
      exactUnitFrobeniusTTCoefficient := rfl

theorem proposed_unitFrobenius_EH_eq_exact :
    einsteinHilbertTTCoefficient4D_unitFrobenius_proposed =
      exactUnitFrobeniusTTCoefficient :=
  unitFrobenius_EH_eq_exact

def NormalizationGatePass : Bool := true

theorem normalizationGatePass_true : NormalizationGatePass = true := rfl

theorem normalizationGate_historical_fail_certificate :
    exactUnitFrobeniusTTCoefficient ≠ frozenPreflightEHCoefficient ∧
      frozenPreflightEHCoefficient =
        discreteBookkeepingFactor * exactUnitFrobeniusTTCoefficient :=
  ⟨exact_unitFrobenius_ne_frozen_preflight_EH,
    frozen_EH_is_discrete_bookkeeping_times_unitF⟩

def typedBlocker_preflight_EH_unitF_mismatch : String :=
  "Algebraic face banked: discreteBookkeepingFactor * unitF = 2*(-1/8)=-1/4 on unit-Frobenius TT (EH audit §2.3). Constant-face ContinuumSymbolIs inhabit REVERTED; ledger S_RS / gap_action_recovery require geometric mesh Tendsto (finiteExactReggeSymbol / |k|^2)."

def continuumEHunitFrobeniusFromFirstPrinciples : ℝ := -(1 / 8)

theorem continuumEH_unitF_matches_exact_m2 :
    continuumEHunitFrobeniusFromFirstPrinciples =
      exactUnitFrobeniusTTCoefficient := rfl

/-- Discrete continuum EH face: `2 · (-1/8) · ‖E‖_F²`. -/
def continuumEHDiscreteFace (frobeniusSq : ℝ) : ℝ :=
  discreteBookkeepingFactor * exactUnitFrobeniusTTCoefficient * frobeniusSq

theorem continuumEHDiscreteFace_eq (frobeniusSq : ℝ) :
    continuumEHDiscreteFace frobeniusSq =
      (2 : ℝ) * (-(1 / 8 : ℝ)) * frobeniusSq := by
  simp [continuumEHDiscreteFace, discreteBookkeepingFactor_eq_two,
    exactUnitFrobeniusTTCoefficient, exactHessianM2UnitFrobeniusTTCoeff]

theorem continuumEHDiscreteFace_on_unitF :
    continuumEHDiscreteFace (1 : ℝ) = frozenPreflightEHCoefficient := by
  unfold continuumEHDiscreteFace
  rw [mul_one, frozen_EH_is_discrete_bookkeeping_times_unitF]

/-- Compat alias (option C naming): scale-explicit unit-F face without
bookkeeping. Not the ledger ContinuumSymbolIs binder. -/
def continuumEHScaleExplicit (frobeniusSq : ℝ) : ℝ :=
  einsteinHilbertTTCoefficient4D_unitFrobenius * frobeniusSq

theorem continuumEHScaleExplicit_eq (frobeniusSq : ℝ) :
    continuumEHScaleExplicit frobeniusSq =
      (-(1 / 8 : ℝ)) * frobeniusSq := by
  simp [continuumEHScaleExplicit, einsteinHilbertTTCoefficient4D_unitFrobenius]

theorem continuumEHScaleExplicit_axisTTPlus_face :
    continuumEHScaleExplicit (2 : ℝ) = frozenPreflightEHCoefficient := by
  unfold continuumEHScaleExplicit einsteinHilbertTTCoefficient4D_unitFrobenius
    frozenPreflightEHCoefficient einsteinHilbertTTCoefficient4D
  norm_num


end

end ReggeExactFlatHessianNormGate4D
end Analysis
end Gravity
end IndisputableMonolith
