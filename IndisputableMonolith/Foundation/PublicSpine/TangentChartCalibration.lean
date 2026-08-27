import IndisputableMonolith.Foundation.PublicSpine.CalibrationNecessity

/-!
# TangentChartCalibration — force continuum ledger readout at the tangent chart?

Probe follow-on (2026-07-23). Parent probe
`CalibrationDischargeProbe` (do not edit) already proved: one-coin-per-act at
the **integer chart** `t = 1` (finite drop `cosh c − 1 = 1`) forces
`c = arcosh 2`, inhabited while `¬ IsCalibrated`. Unit calibration is therefore
the claim that a Recognition-native continuum cost reads the ledger at the
**tangent / instantaneous-rate chart**, not at the first integer act.

This module attempts that chart-forcing derivation, then classifies every
candidate as packaging of `IsCalibrated`, or as a pin to a different constant
(`arcosh 2` or `√2`). Finite-drop facts below restate the parent probe's
sorry-free theorems (same proofs) under a light import cone
(`CalibrationNecessity` only). AbsoluteScale orthogonality remains a parent
theorem (`AbsoluteScaleBoundary.current_delta_area_parents_do_not_select_unique_area`)
and is not re-imported here.

## Inventory

* Integer finite-drop pin → `arcosh 2` (parent probe THEOREM).
* Tangent density readout `G''(0) = 1` → packaging of `IsCalibrated`.
* Second-order lead of `n` micro-acts of size `1/n` is `c²/2`; matching that
  lead to 1 coin forces `c = √2` (misses calibration).
* Matching the Taylor-corrected lead `c²` to 1 is again packaging of
  `oneActCurvature = 1`.
* AbsoluteScale attachments kill SI factors, not `c` (parent boundary; cited).
* Discrete posting L1 = 1 does not select a continuum chart by itself.

Verdict: **WALL**. `CalibrationNecessityOpen` stays uninhabited. A stronger open
`TangentChartNecessityOpen` names the missing non-packaging chart-forcing premise.

No `sorry`; no new `axiom`. Does not edit parent modules.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace TangentChartCalibration

open Cost.FunctionalEquation
open PrimitiveRecognitionCalculus.Calibration
open PrimitiveRecognitionCalculus.DeltaRealCalibration

noncomputable section

/-! ## Parent probe restatement: integer finite-drop chart -/

/-- Continuum cost of one unit additive drop under gauge `c`
(parent: `CalibrationDischargeProbe.finiteDropCost`). -/
def finiteDropCost (c : ℝ) : ℝ :=
  Real.cosh c - 1

/-- Target-blind AbsoluteScale-style cost pricing at the unit ledger drop
(parent: `CalibrationDischargeProbe.FiniteDropCoinCorrespondence`). -/
structure FiniteDropCoinCorrespondence (c : ℝ) where
  positive : 0 < c
  discreteCoins : ℕ
  discrete_unit : discreteCoins = 1
  continuum_drop_equals_coins : finiteDropCost c = (discreteCoins : ℝ)

theorem finiteDropCoinCorrespondence_forces_cosh_two
    {c : ℝ} (h : FiniteDropCoinCorrespondence c) :
    Real.cosh c = 2 := by
  have hcost : finiteDropCost c = 1 := by
    simpa [h.discrete_unit] using h.continuum_drop_equals_coins
  have : Real.cosh c - 1 = 1 := by simpa [finiteDropCost] using hcost
  linarith

theorem finiteDropCoinCorrespondence_forces_arcosh_two
    {c : ℝ} (h : FiniteDropCoinCorrespondence c) :
    c = Real.arcosh 2 := by
  have hcosh : Real.cosh c = 2 :=
    finiteDropCoinCorrespondence_forces_cosh_two h
  have hcnonneg : 0 ≤ c := le_of_lt h.positive
  calc
    c = Real.arcosh (Real.cosh c) := (Real.arcosh_cosh hcnonneg).symm
    _ = Real.arcosh 2 := by rw [hcosh]

theorem cosh_one_lt_two : Real.cosh (1 : ℝ) < 2 := by
  rw [Real.cosh_eq]
  have hexp_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hexp_lt3 : Real.exp (1 : ℝ) < 3 :=
    lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hinv_lt1 : (Real.exp (1 : ℝ))⁻¹ < 1 :=
    (inv_lt_one₀ hexp_pos).mpr
      (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1))
  have hsum' : Real.exp (1 : ℝ) + Real.exp (-(1 : ℝ)) < 4 := by
    have hinv' : Real.exp (-(1 : ℝ)) < 1 := by
      simpa [Real.exp_neg] using hinv_lt1
    linarith [hexp_lt3, hinv']
  linarith

theorem finiteDropCost_one_ne_one : finiteDropCost 1 ≠ 1 := by
  intro h
  have : Real.cosh (1 : ℝ) = 2 := by
    have : Real.cosh 1 - 1 = 1 := by simpa [finiteDropCost] using h
    linarith
  exact (ne_of_lt cosh_one_lt_two) this

theorem finiteDrop_pin_misses_IsCalibrated
    {c : ℝ} (h : FiniteDropCoinCorrespondence c) :
    ¬ IsCalibrated (fun x => costLambda c x) := by
  intro hCal
  have hc1 : c = 1 := (costLambda_isCalibrated_iff h.positive).mp hCal
  have hcosh : Real.cosh c = 2 :=
    finiteDropCoinCorrespondence_forces_cosh_two h
  rw [hc1] at hcosh
  exact (ne_of_lt cosh_one_lt_two) hcosh

def arcoshTwo_finiteDropCorrespondence :
    FiniteDropCoinCorrespondence (Real.arcosh 2) where
  positive := Real.arcosh_pos (by norm_num : (1 : ℝ) < 2)
  discreteCoins := 1
  discrete_unit := rfl
  continuum_drop_equals_coins := by
    simp only [finiteDropCost]
    have h : Real.cosh (Real.arcosh 2) = 2 :=
      Real.cosh_arcosh (by norm_num : (1 : ℝ) ≤ 2)
    rw [h]
    norm_num

theorem finiteDrop_not_packaging_of_IsCalibrated :
    ∃ c : ℝ, 0 < c ∧
      Nonempty (FiniteDropCoinCorrespondence c) ∧
      ¬ IsCalibrated (fun x => costLambda c x) := by
  refine ⟨Real.arcosh 2, ?_, ⟨arcoshTwo_finiteDropCorrespondence⟩, ?_⟩
  · exact Real.arcosh_pos (by norm_num : (1 : ℝ) < 2)
  · exact finiteDrop_pin_misses_IsCalibrated arcoshTwo_finiteDropCorrespondence

/-! ## Charts: integer finite drop vs tangent density -/

abbrev integerChartCost (c : ℝ) : ℝ := finiteDropCost c

abbrev tangentChartCost (c : ℝ) : ℝ := oneActCurvature c

theorem integerChartCost_eq (c : ℝ) : integerChartCost c = Real.cosh c - 1 :=
  rfl

theorem tangentChartCost_eq (c : ℝ) : tangentChartCost c = c ^ 2 :=
  oneActCurvature_eq c

theorem charts_disagree_at_unit :
    integerChartCost 1 ≠ tangentChartCost 1 := by
  simpa [integerChartCost, tangentChartCost, oneActCurvature_eq, finiteDropCost] using
    finiteDropCost_one_ne_one

theorem integer_chart_one_coin_forces_arcosh_two
    {c : ℝ} (h : FiniteDropCoinCorrespondence c) :
    c = Real.arcosh 2 :=
  finiteDropCoinCorrespondence_forces_arcosh_two h

theorem integer_chart_one_coin_misses_IsCalibrated
    {c : ℝ} (h : FiniteDropCoinCorrespondence c) :
    ¬ IsCalibrated (fun x => costLambda c x) :=
  finiteDrop_pin_misses_IsCalibrated h

/-! ## Route T1 — one-coin at the tangent density (packaging) -/

structure TangentCoinCorrespondence (c : ℝ) where
  positive : 0 < c
  discreteCoins : ℕ
  discrete_unit : discreteCoins = 1
  continuum_tangent_equals_coins : tangentChartCost c = (discreteCoins : ℝ)

theorem tangentCoinCorrespondence_forces_unit
    {c : ℝ} (h : TangentCoinCorrespondence c) : c = 1 := by
  have hcurv : tangentChartCost c = 1 := by
    simpa [h.discrete_unit] using h.continuum_tangent_equals_coins
  have : oneActCurvature c = 1 := by simpa [tangentChartCost] using hcurv
  exact (unit_forced_by_one_act h.positive).mp this

theorem tangentCoinCorrespondence_forces_calibrated
    {c : ℝ} (h : TangentCoinCorrespondence c) :
    IsCalibrated (fun x => costLambda c x) := by
  have hc1 : c = 1 := tangentCoinCorrespondence_forces_unit h
  exact (costLambda_isCalibrated_iff h.positive).mpr hc1

theorem tangentCoinCorrespondence_iff_calibrated {c : ℝ} (hc : 0 < c) :
    Nonempty (TangentCoinCorrespondence c) ↔
      IsCalibrated (fun x => costLambda c x) := by
  constructor
  · rintro ⟨h⟩
    exact tangentCoinCorrespondence_forces_calibrated h
  · intro hCal
    have hc1 : c = 1 := (costLambda_isCalibrated_iff hc).mp hCal
    refine ⟨⟨hc, 1, rfl, ?_⟩⟩
    rw [tangentChartCost_eq, hc1]
    norm_num

theorem tangent_density_one_iff_calibrated {c : ℝ} (hc : 0 < c) :
    tangentChartCost c = 1 ↔ IsCalibrated (fun x => costLambda c x) := by
  rw [tangentChartCost_eq, ← oneActCurvature_eq c, oneActCurvature_one_iff_calibrated hc]

/-! ## Route T2 — second-order lead of subdivided micro-acts -/

theorem cosh_sub_one_eq_two_sinh_sq (x : ℝ) :
    Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
  have hx : x = 2 * (x / 2) := by ring
  calc
    Real.cosh x - 1 = Real.cosh (2 * (x / 2)) - 1 := by rw [← hx]
    _ = Real.cosh (x / 2) ^ 2 + Real.sinh (x / 2) ^ 2 - 1 := by
        rw [Real.cosh_two_mul]
    _ = (Real.sinh (x / 2) ^ 2 + 1) + Real.sinh (x / 2) ^ 2 - 1 := by
        rw [Real.cosh_sq]
    _ = 2 * Real.sinh (x / 2) ^ 2 := by ring

/-- Closed-form second-order lead of one discrete act subdivided into equal
micro-acts of additive size `1/n` (the `n → ∞` lead of `n² (cosh(c/n) − 1)`).
Equals half the tangent density. -/
def subdivisionLeadCost (c : ℝ) : ℝ :=
  c ^ 2 / 2

theorem subdivisionLeadCost_eq_half_tangent (c : ℝ) :
    subdivisionLeadCost c = tangentChartCost c / 2 := by
  unfold subdivisionLeadCost tangentChartCost
  rw [oneActCurvature_eq]

theorem micro_act_total_eq_two_sinh_sq {c : ℝ} {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 2 * (Real.cosh (c / (n : ℝ)) - 1) =
      2 * ((n : ℝ) * Real.sinh (c / (2 * (n : ℝ)))) ^ 2 := by
  have hx := cosh_sub_one_eq_two_sinh_sq (c / (n : ℝ))
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hhalf : (c / (n : ℝ)) / 2 = c / (2 * (n : ℝ)) := by
    field_simp [hn0]
  calc
    (n : ℝ) ^ 2 * (Real.cosh (c / (n : ℝ)) - 1)
        = (n : ℝ) ^ 2 * (2 * Real.sinh ((c / (n : ℝ)) / 2) ^ 2) := by rw [hx]
    _ = (n : ℝ) ^ 2 * (2 * Real.sinh (c / (2 * (n : ℝ))) ^ 2) := by rw [hhalf]
    _ = 2 * ((n : ℝ) * Real.sinh (c / (2 * (n : ℝ)))) ^ 2 := by ring

structure NaiveSubdivisionCoinCorrespondence (c : ℝ) where
  positive : 0 < c
  discreteCoins : ℕ
  discrete_unit : discreteCoins = 1
  subdivision_lead_equals_coins : subdivisionLeadCost c = (discreteCoins : ℝ)

theorem naiveSubdivision_forces_sq_two
    {c : ℝ} (h : NaiveSubdivisionCoinCorrespondence c) :
    c ^ 2 = 2 := by
  have hlead : subdivisionLeadCost c = 1 := by
    simpa [h.discrete_unit] using h.subdivision_lead_equals_coins
  have : c ^ 2 / 2 = 1 := by simpa [subdivisionLeadCost] using hlead
  linarith

theorem naiveSubdivision_forces_sqrt_two
    {c : ℝ} (h : NaiveSubdivisionCoinCorrespondence c) :
    c = Real.sqrt 2 := by
  have hsq : c ^ 2 = 2 := naiveSubdivision_forces_sq_two h
  have hpos : 0 < c := h.positive
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq' : c ^ 2 = (Real.sqrt 2) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact hsq
  exact (sq_eq_sq₀ hpos.le hsqrt).mp hsq'

def sqrtTwo_naiveSubdivisionCorrespondence :
    NaiveSubdivisionCoinCorrespondence (Real.sqrt 2) where
  positive := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  discreteCoins := 1
  discrete_unit := rfl
  subdivision_lead_equals_coins := by
    simp only [subdivisionLeadCost]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num

theorem sqrt_two_ne_one : Real.sqrt 2 ≠ (1 : ℝ) := by
  intro h
  have hsq : (Real.sqrt 2) ^ 2 = (1 : ℝ) ^ 2 := by rw [h]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_pow] at hsq
  norm_num at hsq

theorem naiveSubdivision_misses_IsCalibrated
    {c : ℝ} (h : NaiveSubdivisionCoinCorrespondence c) :
    ¬ IsCalibrated (fun x => costLambda c x) := by
  intro hCal
  have hc1 : c = 1 := (costLambda_isCalibrated_iff h.positive).mp hCal
  have hsqrt : c = Real.sqrt 2 := naiveSubdivision_forces_sqrt_two h
  rw [hc1] at hsqrt
  exact sqrt_two_ne_one hsqrt.symm

theorem naiveSubdivision_not_packaging_of_IsCalibrated :
    ∃ c : ℝ, 0 < c ∧
      Nonempty (NaiveSubdivisionCoinCorrespondence c) ∧
      ¬ IsCalibrated (fun x => costLambda c x) := by
  refine ⟨Real.sqrt 2, ?_, ⟨sqrtTwo_naiveSubdivisionCorrespondence⟩, ?_⟩
  · exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  · exact naiveSubdivision_misses_IsCalibrated sqrtTwo_naiveSubdivisionCorrespondence

/-! ## Route T3 — Taylor-corrected subdivision lead (packaging) -/

theorem taylor_corrected_lead_eq_tangent (c : ℝ) :
    2 * subdivisionLeadCost c = tangentChartCost c := by
  unfold subdivisionLeadCost tangentChartCost
  rw [oneActCurvature_eq]
  ring

theorem taylor_corrected_one_iff_calibrated {c : ℝ} (hc : 0 < c) :
    (2 * subdivisionLeadCost c = 1) ↔
      IsCalibrated (fun x => costLambda c x) := by
  rw [taylor_corrected_lead_eq_tangent, tangent_density_one_iff_calibrated hc]

/-! ## Chart trichotomy -/

structure ChartTrichotomy : Prop where
  integer_pins_arcosh_two :
    ∃ c : ℝ, 0 < c ∧
      Nonempty (FiniteDropCoinCorrespondence c) ∧
      c = Real.arcosh 2 ∧
      ¬ IsCalibrated (fun x => costLambda c x)
  naive_subdivision_pins_sqrt_two :
    ∃ c : ℝ, 0 < c ∧
      Nonempty (NaiveSubdivisionCoinCorrespondence c) ∧
      c = Real.sqrt 2 ∧
      ¬ IsCalibrated (fun x => costLambda c x)
  tangent_is_packaging :
    ∀ {c : ℝ}, 0 < c →
      (Nonempty (TangentCoinCorrespondence c) ↔
        IsCalibrated (fun x => costLambda c x))

theorem chartTrichotomy_holds : ChartTrichotomy where
  integer_pins_arcosh_two := by
    refine ⟨Real.arcosh 2, ?_, ⟨arcoshTwo_finiteDropCorrespondence⟩, rfl, ?_⟩
    · exact Real.arcosh_pos (by norm_num : (1 : ℝ) < 2)
    · exact finiteDrop_pin_misses_IsCalibrated arcoshTwo_finiteDropCorrespondence
  naive_subdivision_pins_sqrt_two := by
    refine ⟨Real.sqrt 2, ?_, ⟨sqrtTwo_naiveSubdivisionCorrespondence⟩, rfl, ?_⟩
    · exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    · exact naiveSubdivision_misses_IsCalibrated sqrtTwo_naiveSubdivisionCorrespondence
  tangent_is_packaging := fun hc => tangentCoinCorrespondence_iff_calibrated hc

/-! ## WALL binder + stronger OPEN residual -/

structure TangentChartNecessity : Prop where
  trichotomy : ChartTrichotomy
  tangent_packaging_iff :
    ∀ {c : ℝ}, 0 < c →
      (Nonempty (TangentCoinCorrespondence c) ↔
        IsCalibrated (fun x => costLambda c x))
  taylor_corrected_packaging_iff :
    ∀ {c : ℝ}, 0 < c →
      (2 * subdivisionLeadCost c = 1 ↔
        IsCalibrated (fun x => costLambda c x))
  integer_misses :
    ∃ c : ℝ, 0 < c ∧
      Nonempty (FiniteDropCoinCorrespondence c) ∧
      ¬ IsCalibrated (fun x => costLambda c x)
  subdivision_misses :
    ∃ c : ℝ, 0 < c ∧
      Nonempty (NaiveSubdivisionCoinCorrespondence c) ∧
      ¬ IsCalibrated (fun x => costLambda c x)
  charts_disagree : integerChartCost 1 ≠ tangentChartCost 1
  parent_calibration_wall : CalibrationNecessity
  independence_floor :
    (∀ c : ℝ,
        IsReciprocalCost (fun x => costLambda c x)
          ∧ IsNormalized (fun x => costLambda c x)
          ∧ SatisfiesCompositionLaw (fun x => costLambda c x)
          ∧ ContinuousOn (fun x => costLambda c x) (Set.Ioi 0))
      ∧ (∀ c : ℝ, 0 < c →
          (IsCalibrated (fun x => costLambda c x) ↔ c = 1))
      ∧ (∃ c d : ℝ, 0 < c ∧ 0 < d ∧ c ≠ d
            ∧ (fun x => costLambda c x) ≠ (fun x => costLambda d x))

theorem tangentChartNecessity_holds : TangentChartNecessity where
  trichotomy := chartTrichotomy_holds
  tangent_packaging_iff := fun hc => tangentCoinCorrespondence_iff_calibrated hc
  taylor_corrected_packaging_iff := fun hc => taylor_corrected_one_iff_calibrated hc
  integer_misses := finiteDrop_not_packaging_of_IsCalibrated
  subdivision_misses := naiveSubdivision_not_packaging_of_IsCalibrated
  charts_disagree := charts_disagree_at_unit
  parent_calibration_wall := calibrationNecessity_holds
  independence_floor := calibration_is_the_only_hypothesis_pinning_J

theorem tangent_chart_necessity_is_wall :
    (∀ {c : ℝ}, 0 < c →
      (Nonempty (TangentCoinCorrespondence c) ↔
        IsCalibrated (fun x => costLambda c x))) ∧
      (∃ c : ℝ, 0 < c ∧
        Nonempty (FiniteDropCoinCorrespondence c) ∧
        ¬ IsCalibrated (fun x => costLambda c x)) ∧
      (∃ c : ℝ, 0 < c ∧
        Nonempty (NaiveSubdivisionCoinCorrespondence c) ∧
        ¬ IsCalibrated (fun x => costLambda c x)) ∧
      integerChartCost 1 ≠ tangentChartCost 1 :=
  ⟨fun hc => tangentCoinCorrespondence_iff_calibrated hc,
    finiteDrop_not_packaging_of_IsCalibrated,
    naiveSubdivision_not_packaging_of_IsCalibrated,
    charts_disagree_at_unit⟩

/-- OPEN residual (stronger than `CalibrationNecessityOpen`): a Recognition-native
premise `P` that forces the continuum one-act readout to be the tangent chart
(equivalently, forces `IsCalibrated` via a chart-selection law), fails on the
independence countermodel when dropped, and is **not** packaging-equivalent to
`IsCalibrated` / `tangentChartCost = 1` / `oneActCurvature = 1`.

Intentionally uninhabited: no `tangentChartNecessityOpen_holds` theorem. The
chart trichotomy above is the obstruction certificate. -/
def TangentChartNecessityOpen : Prop :=
  ∃ (P : ℝ → Prop),
    (∀ c : ℝ, 0 < c → P c → IsCalibrated (fun x => costLambda c x)) ∧
      (∃ c : ℝ,
        0 < c ∧ c ≠ 1 ∧ FullNonCalibrationCostLaws c ∧ ¬ P c) ∧
      (∀ c : ℝ, 0 < c →
        ¬ (P c ↔ IsCalibrated (fun x => costLambda c x))) ∧
      (∀ c : ℝ, 0 < c → ¬ (P c ↔ tangentChartCost c = 1)) ∧
      (∀ c : ℝ, 0 < c → ¬ (P c ↔ oneActCurvature c = 1))

structure TangentChartCalibrationCert : Prop where
  wall : TangentChartNecessity
  trichotomy : ChartTrichotomy

theorem tangentChartCalibrationCert_holds : TangentChartCalibrationCert where
  wall := tangentChartNecessity_holds
  trichotomy := chartTrichotomy_holds

theorem probe_verdict_tangent_chart_wall :
    TangentChartNecessity ∧
      ChartTrichotomy ∧
      (∀ {c : ℝ}, 0 < c →
        (Nonempty (TangentCoinCorrespondence c) ↔
          IsCalibrated (fun x => costLambda c x))) :=
  ⟨tangentChartNecessity_holds, chartTrichotomy_holds,
    fun hc => tangentCoinCorrespondence_iff_calibrated hc⟩

end
end TangentChartCalibration
end PublicSpine
end Foundation
end IndisputableMonolith
