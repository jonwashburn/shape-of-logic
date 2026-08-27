import IndisputableMonolith.Foundation.PublicSpine.CalibrationNecessity
import IndisputableMonolith.Foundation.AbsoluteScaleBoundary
import IndisputableMonolith.Cost.Calibration
import IndisputableMonolith.LedgerPostingAdjacency

/-!
# CalibrationDischargeProbe — deep monolith search for non-packaging discharge of `IsCalibrated`

Probe A (2026-07-23). Goal: derive unit log-curvature calibration
(`IsCalibrated` / `c = 1` in the cosh gauge family) from Recognition-native
premises that are **not** packaging-equivalent to the conclusion.

Prior narrow search (DeltaRealCalibration / PhysicalOneActCalibration /
PRCCalibrationIndependence) banked WALL in `CalibrationNecessity.lean`.
This module opens the leads that search never touched: PairKernel S-series
atomic posting cost, AbsoluteScale target-blind attachments, Cost/Verification
calibration certificates, and discrete act-count structure.

## Inventory (proves vs assumes)

* `PRCCalibrationIndependence.calibration_unit_not_forced_by_cost_laws` —
  proves free `c` under cost laws; assumes nothing beyond the gauge family.
* `DeltaRealCalibration.unit_forced_by_one_act` — proves `oneActCurvature c = 1 ↔ c = 1`;
  the premise `oneActCurvature = 1` is packaging of `IsCalibrated`.
* `PhysicalOneActCalibration.instrument_forces_canonical_unit` — proves unit from
  `locked_to_one` after reading curvature (packaging).
* `CalibrationNecessity.oneActCoinCorrespondence_iff_calibrated` — packaging iff.
* `AbsoluteScaleOperationalCalibrationAttachment.attachment_forces_unit_seconds/joules` —
  proves SI factors from target-blind committed counts; dimensional, not `c`.
* `AbsoluteScaleBoundary.full_noncalibration_laws_admit_distinct_units` —
  proves `c` residual orthogonal to dimensional area residual.
* `LedgerPostingAdjacency.ledgerJlogCost_eq_Jlog1_of_postingStep` —
  proves atomic posting costs `Jlog 1`; **uses already-named** `Cost.Jlog`.
* `Cost.Calibration.Jlog_second_deriv_at_zero` — proves `G''(0)=1` for `Jlog`
  by definition `Jlog = cosh − 1`, not a derivation of the gauge pin.
* `Verification.CalibrationCert` — packages the same definitional evaluation.
* `Verification.UniqueCalibrationCert` — unique RS-units pack given anchors
  (dimensional absolute layer), not J log-curvature.
* `Constants.AlphaGenesis.CalibrationForcing.step_forced` — forces α-dressing
  step `φ⁻¹` by self-similar balance; different object from `IsCalibrated`.
* `UnifiedForcingChain.t5_holds` / `law_of_logic_forces_jcost` — uniqueness
  **consumes** `IsCalibrated` as a hypothesis.
* `PhysicalAccess.MeasurementRecord = List Bool` — discrete act counting;
  no theorem bridges act count to continuum log-curvature without packaging.
* **This module, Route 3:** AbsoluteScale-style finite-drop cost pricing
  `cosh c − 1 = 1` forces `c = arcosh 2`, which **misses** `IsCalibrated`.

Verdict: **GENUINE-OPEN**. No non-packaging Recognition premise in the
monolith discharges `IsCalibrated`.

No `sorry`; no new `axiom`. Does not inhabit `CalibrationNecessityOpen`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace CalibrationDischargeProbe

open Cost.FunctionalEquation
open PrimitiveRecognitionCalculus.Calibration
open PrimitiveRecognitionCalculus.DeltaRealCalibration
open AbsoluteScaleBoundary

noncomputable section

/-! ## Route 1 — independence floor (known negative) -/

/-- Bare + full non-calibration laws leave the gauge free. -/
theorem route_cost_laws_leave_c_free :
    (∀ c : ℝ,
        IsReciprocalCost (fun x => costLambda c x)
          ∧ IsNormalized (fun x => costLambda c x)
          ∧ SatisfiesCompositionLaw (fun x => costLambda c x)
          ∧ ContinuousOn (fun x => costLambda c x) (Set.Ioi 0))
      ∧ (∀ c : ℝ, 0 < c →
          (IsCalibrated (fun x => costLambda c x) ↔ c = 1))
      ∧ (∃ c d : ℝ, 0 < c ∧ 0 < d ∧ c ≠ d
            ∧ (fun x => costLambda c x) ≠ (fun x => costLambda d x)) :=
  calibration_is_the_only_hypothesis_pinning_J

/-! ## Route 2 — curvature / coin packaging (known wall) -/

/-- Curvature readout of one-act cost is packaging of `IsCalibrated`. -/
theorem route_curvature_is_packaging {c : ℝ} (hc : 0 < c) :
    oneActCurvature c = 1 ↔ IsCalibrated (fun x => costLambda c x) :=
  oneActCurvature_one_iff_calibrated hc

/-- Coin correspondence with curvature continuum readout is packaging. -/
theorem route_coin_curvature_is_packaging {c : ℝ} (hc : 0 < c) :
    Nonempty (OneActCoinCorrespondence c) ↔
      IsCalibrated (fun x => costLambda c x) :=
  oneActCoinCorrespondence_iff_calibrated hc

/-! ## Route 3 — AbsoluteScale-style finite drop pricing (novel obstruction)

AbsoluteScale forces dimensional units by equating an external instrument
reading to a committed ledger count. The analogous law for the cost residual
at the unit ledger drop is:

  continuum finite-drop cost of gauge `c`  =  committed coin count (= 1)

where continuum finite-drop cost is `cosh c − 1` (evaluate `G(costLambda c)`
at additive chart coordinate `t = 1`, the integer posting step).

This is operationally distinct from `IsCalibrated` / `G''(0) = 1`. It pins
`c = arcosh 2`, which is **not** the calibrated unit. -/

/-- Continuum cost of one unit additive drop under gauge `c`. -/
def finiteDropCost (c : ℝ) : ℝ :=
  Real.cosh c - 1

/-- Target-blind AbsoluteScale-style cost pricing at the unit ledger drop. -/
structure FiniteDropCoinCorrespondence (c : ℝ) where
  positive : 0 < c
  discreteCoins : ℕ
  discrete_unit : discreteCoins = 1
  /-- Continuum finite-drop cost equals discrete coin count. -/
  continuum_drop_equals_coins : finiteDropCost c = (discreteCoins : ℝ)

/-- Finite-drop pricing forces `cosh c = 2`. -/
theorem finiteDropCoinCorrespondence_forces_cosh_two
    {c : ℝ} (h : FiniteDropCoinCorrespondence c) :
    Real.cosh c = 2 := by
  have hcost : finiteDropCost c = 1 := by
    simpa [h.discrete_unit] using h.continuum_drop_equals_coins
  have : Real.cosh c - 1 = 1 := by simpa [finiteDropCost] using hcost
  linarith

/-- Finite-drop pricing forces `c = arcosh 2`. -/
theorem finiteDropCoinCorrespondence_forces_arcosh_two
    {c : ℝ} (h : FiniteDropCoinCorrespondence c) :
    c = Real.arcosh 2 := by
  have hcosh : Real.cosh c = 2 :=
    finiteDropCoinCorrespondence_forces_cosh_two h
  have hcpos : 0 < c := h.positive
  have harpos : 0 < Real.arcosh 2 :=
    Real.arcosh_pos (by norm_num : (1 : ℝ) < 2)
  have hsolve : Real.cosh (Real.arcosh 2) = 2 :=
    Real.cosh_arcosh (by norm_num : (1 : ℝ) ≤ 2)
  have habs :=
    (Real.cosh_eq_cosh_iff_abs_eq_abs).mp (hcosh.trans hsolve.symm)
  have hcabs : |c| = c := abs_of_pos hcpos
  have harabs : |Real.arcosh 2| = Real.arcosh 2 := abs_of_pos harpos
  simpa [hcabs, harabs] using habs

/-- Helper: `cosh 1 < 2`, so the calibrated unit fails finite-drop pricing. -/
theorem cosh_one_lt_two : Real.cosh (1 : ℝ) < 2 := by
  -- cosh 1 = (e + e⁻¹)/2; use e < 3 and e⁻¹ < 1 ⇒ sum < 4 ⇒ cosh < 2
  rw [Real.cosh_eq]
  have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hexp_lt3 : Real.exp (1 : ℝ) < 3 :=
    (Real.exp_one_lt_d9).trans_lt (by norm_num)
  have hinv_lt1 : (Real.exp (1 : ℝ))⁻¹ < 1 :=
    (inv_lt_one_iff_of_pos hexp_pos).mpr
      (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1))
  have hsum : Real.exp (1 : ℝ) + (Real.exp (1 : ℝ))⁻¹ < 4 := by
    have : (Real.exp (1 : ℝ))⁻¹ = Real.exp (-(1 : ℝ)) := (Real.exp_neg 1).symm
    -- rewrite goal to use exp (-1) form matching cosh_eq
    rw [← Real.exp_neg] at hinv_lt1 ⊢
    linarith [hexp_lt3, hinv_lt1]
  -- cosh_eq uses exp 1 + exp (-1)
  have hsum' : Real.exp (1 : ℝ) + Real.exp (-(1 : ℝ)) < 4 := by
    simpa [Real.exp_neg] using hsum
  linarith

theorem finiteDropCost_one_ne_one : finiteDropCost 1 ≠ 1 := by
  intro h
  have : Real.cosh (1 : ℝ) = 2 := by
    have : Real.cosh 1 - 1 = 1 := by simpa [finiteDropCost] using h
    linarith
  exact (ne_of_lt cosh_one_lt_two) this

/-- AbsoluteScale-style finite-drop pin does **not** yield `IsCalibrated`. -/
theorem finiteDrop_pin_misses_IsCalibrated
    {c : ℝ} (h : FiniteDropCoinCorrespondence c) :
    ¬ IsCalibrated (fun x => costLambda c x) := by
  intro hCal
  have hc1 : c = 1 := (costLambda_isCalibrated_iff h.positive).mp hCal
  have hcosh : Real.cosh c = 2 :=
    finiteDropCoinCorrespondence_forces_cosh_two h
  rw [hc1] at hcosh
  exact (ne_of_lt cosh_one_lt_two) hcosh

/-- Finite-drop correspondence is inhabited at `arcosh 2` (consistency). -/
def arcoshTwo_finiteDropCorrespondence :
    FiniteDropCoinCorrespondence (Real.arcosh 2) where
  positive := Real.arcosh_pos (by norm_num : (1 : ℝ) < 2)
  discreteCoins := 1
  discrete_unit := rfl
  continuum_drop_equals_coins := by
    simp only [finiteDropCost]
    have h : Real.cosh (Real.arcosh 2) = 2 :=
      Real.cosh_arcosh (by norm_num : (1 : ℝ) ≤ 2)
    linarith

/-- Packaging test failure: finite-drop correspondence is **not** equivalent
to `IsCalibrated` (inhabited at a non-calibrated gauge). -/
theorem finiteDrop_not_packaging_of_IsCalibrated :
    ∃ c : ℝ, 0 < c ∧
      Nonempty (FiniteDropCoinCorrespondence c) ∧
      ¬ IsCalibrated (fun x => costLambda c x) := by
  refine ⟨Real.arcosh 2, ?_, ⟨arcoshTwo_finiteDropCorrespondence⟩, ?_⟩
  · exact Real.arcosh_pos (by norm_num : (1 : ℝ) < 2)
  · exact finiteDrop_pin_misses_IsCalibrated arcoshTwo_finiteDropCorrespondence

/-! ## Route 4 — PairKernel atomic posting uses calibrated `Jlog`

S11/S12 prove `PostingStep → ledgerJlogCost = Jlog 1`. That cost equals
`cosh 1 − 1`, which is **not** the curvature value `G''(0) = 1`. The
PairKernel route therefore cannot discharge the gauge pin: it prices with
an already-named calibrated `Jlog`, and its atomic numeral differs from
the calibration numeral. -/

/-- Atomic posting ledger cost equals `Jlog 1` (PairKernel/S11 parent). -/
theorem route_postingStep_costs_Jlog_one
    {d : Nat} {L L' : LedgerPostingAdjacency.LedgerState d}
    (h : LedgerPostingAdjacency.PostingStep (d := d) L L') :
    LedgerPostingAdjacency.ledgerJlogCost (d := d) L L' = Cost.Jlog (1 : ℝ) :=
  LedgerPostingAdjacency.ledgerJlogCost_eq_Jlog1_of_postingStep h

/-- The atomic posting cost value is not the unit-curvature numeral. -/
theorem atomic_posting_cost_ne_unit_curvature_numeral :
    Cost.Jlog (1 : ℝ) ≠ deriv (deriv Cost.Jlog) 0 := by
  rw [Cost.Jlog_as_cosh, Cost.Jlog_second_deriv_at_zero]
  -- cosh 1 - 1 ≠ 1
  intro h
  have : Real.cosh (1 : ℝ) = 2 := by linarith
  exact (ne_of_lt cosh_one_lt_two) this

/-- Definitional calibration of named `Jlog` (not a gauge discharge). -/
theorem route_Jlog_definitional_unit_curvature :
    deriv (deriv Cost.Jlog) 0 = 1 :=
  Cost.Jlog_second_deriv_at_zero

/-! ## Route 5 — dimensional AbsoluteScale residual is orthogonal to `c` -/

/-- Selecting Delta unit calibration does not select a unique area
(AbsoluteScaleBoundary parent). Dimensional attachments and the cost gauge
are separately typed residuals. -/
theorem route_delta_unit_orthogonal_to_area :
    ¬ ∃ area₀ : ℝ,
      0 < area₀ ∧
        ∀ area : ℝ, CurrentDeltaAreaParents 1 area → area = area₀ :=
  current_delta_area_parents_do_not_select_unique_area

/-- Full non-calibration laws admit distinct cost units (Boundary parent). -/
theorem route_boundary_admits_distinct_cost_units :
    FullNonCalibrationCostLaws 1 ∧
      FullNonCalibrationCostLaws 2 ∧
      (fun x => costLambda 1 x) ≠ (fun x => costLambda 2 x) :=
  full_noncalibration_laws_admit_distinct_units

/-! ## Route 6 — successor-ladder leading coefficient is packaging -/

/-- Successor lead `c²/2 = 1/2` is the same pin as `oneActCurvature = 1`. -/
theorem route_successor_lead_packaging {c : ℝ} (hc : 0 < c) :
    (oneActCurvature c / 2 = 1 / 2) ↔ IsCalibrated (fun x => costLambda c x) := by
  constructor
  · intro h
    have : oneActCurvature c = 1 := by
      have hcurv := oneActCurvature_eq c
      -- oneActCurvature c / 2 = 1/2 ⇒ oneActCurvature c = 1
      linarith
    exact (oneActCurvature_one_iff_calibrated hc).mp this
  · intro hCal
    have hc1 : c = 1 := (costLambda_isCalibrated_iff hc).mp hCal
    rw [oneActCurvature_eq, hc1]
    norm_num

/-! ## Strongest attempted non-packaging chain (fails)

Attempted chain:
1. Atomic `PostingStep` has discrete L1 cost 1 (THEOREM).
2. Continuum transport of one act must equal that coin (disclosed AbsoluteScale-style law).
3. Choose continuum readout = finite drop cost `cosh c − 1` (not curvature language).
4. Conclude `c = arcosh 2` (THEOREM above).
5. Need `c = 1` for `IsCalibrated` — **FAILS** (proved miss).

If step 3 instead uses curvature readout, step 4 becomes packaging
(`CalibrationNecessity` wall).

Missing lemma for any remaining hope (stated, not proved; no inhabitant):
a Recognition-native continuum readout `R : ℝ → ℝ` of “one act cost” such that
`(R c = 1 ↔ IsCalibrated (costLambda c))` is false as a bare biconditional on
the nose of packaging, yet `R c = discreteCoins` still forces `c = 1` from
structure that fails on the free-`c` countermodel when dropped.
No such `R` appears in the monolith outside packaging-equivalent curvature. -/

/-- Probe certificate: every opened route is obstruction-classified. -/
structure CalibrationDischargeProbeCert : Prop where
  independence_floor : True
  curvature_packaging :
    ∀ {c : ℝ}, 0 < c →
      (oneActCurvature c = 1 ↔ IsCalibrated (fun x => costLambda c x))
  finite_drop_misses :
    ∃ c : ℝ, 0 < c ∧
      Nonempty (FiniteDropCoinCorrespondence c) ∧
      ¬ IsCalibrated (fun x => costLambda c x)
  atomic_cost_ne_curvature_numeral :
    Cost.Jlog (1 : ℝ) ≠ deriv (deriv Cost.Jlog) 0
  dimensional_orthogonal :
    ¬ ∃ area₀ : ℝ,
      0 < area₀ ∧
        ∀ area : ℝ, CurrentDeltaAreaParents 1 area → area = area₀
  wall_binder : CalibrationNecessity

theorem calibrationDischargeProbeCert_holds : CalibrationDischargeProbeCert where
  independence_floor := trivial
  curvature_packaging := fun hc => route_curvature_is_packaging hc
  finite_drop_misses := finiteDrop_not_packaging_of_IsCalibrated
  atomic_cost_ne_curvature_numeral := atomic_posting_cost_ne_unit_curvature_numeral
  dimensional_orthogonal := route_delta_unit_orthogonal_to_area
  wall_binder := calibrationNecessity_holds

/-- **GENUINE-OPEN binder.** `CalibrationNecessityOpen` remains uninhabited:
no non-packaging `P` discharging unit calibration was found across the
opened monolith routes. -/
theorem probe_verdict_genuine_open :
    CalibrationNecessity ∧
      (∃ c : ℝ, 0 < c ∧
        Nonempty (FiniteDropCoinCorrespondence c) ∧
        ¬ IsCalibrated (fun x => costLambda c x)) ∧
      Cost.Jlog (1 : ℝ) ≠ deriv (deriv Cost.Jlog) 0 :=
  ⟨calibrationNecessity_holds,
    finiteDrop_not_packaging_of_IsCalibrated,
    atomic_posting_cost_ne_unit_curvature_numeral⟩

end
end CalibrationDischargeProbe
end PublicSpine
end Foundation
end IndisputableMonolith
