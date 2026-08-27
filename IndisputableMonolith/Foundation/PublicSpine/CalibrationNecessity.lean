import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCCalibrationIndependence
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaRealCalibration
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PhysicalOneActCalibration

/-!
# CalibrationNecessity — Lane A hard-half binder (WALL)

Campaign: `plans/PartI_Hard_Half_Closure_Plan_20260723.html`, Lane A.
Binding: `D-part1-hard-half-20260723`, `D-part1-dep-pattern`.

Goal was to derive unit calibration from a disclosed Recognition premise that is
**not** packaging of `IsCalibrated` / `G''(0)=1`. Inventory of existing
“forces unit” content:

* `DeltaRealCalibration.NormalizedOneActInterface` — field
  `curvature_unit : oneActCurvature = 1` (packaging).
* `PhysicalOneActCalibration.OneActInstrument` — `locked_to_one` after reading
  curvature (packaging).
* `PRCCalibrationIndependence` — independence: bare / full non-calibration laws
  leave free `c` (falsifier floor).
* `CalibrationGauge` — uniqueness under `IsCalibrated` + independence (already
  banked).

Attempted content-typed premise `OneActCoinCorrespondence` (discrete coin count
↔ continuum one-act cost) forces the unit **only when** the continuum cost is
read as one-act log-curvature, which is equivalent to `IsCalibrated` on
`costLambda c`. That fails the countermodel / packaging test as a genuine
discharge. Verdict: **WALL**.

What is THEOREM here: the conditional packaging implications, the packaging
equivalence, the free-`c` countermodel, the unique scale residual inside the
gauge family, and the wall binder. What stays OPEN: `CalibrationNecessityOpen`
(non-packaging `P` forcing the unit). No three-axiom miracle claim.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine

open Cost.FunctionalEquation
open PrimitiveRecognitionCalculus.Calibration
open PrimitiveRecognitionCalculus.DeltaRealCalibration
open PrimitiveRecognitionCalculus.PhysicalOneActCalibration

/-! ## Attempted content-typed premise (coin ↔ act) -/

/-- Scaffold without the controversial act-count match: a positive gauge unit
and a discrete ledger coin count equal to one. Satisfied by every positive `c`.
Data-carrying (not `Prop`) so the coin count is inspectable. -/
structure BareCoinActScaffold (c : ℝ) where
  positive : 0 < c
  discreteCoins : ℕ
  discrete_unit : discreteCoins = 1

/-- **Attempted `P_calib`.** One discrete ledger coin for a minimal recognition
posting equals the continuum interface cost of one act at the identity chart.

Fields are operationally about coin count and continuum act cost. The continuum
readout is the one-act log-curvature (the only continuum one-act cost already
tied to the gauge family in-repo). With that readout, the match is
packaging-equivalent to `IsCalibrated` on `costLambda c` — banked below as the
wall, not as discharge. -/
structure OneActCoinCorrespondence (c : ℝ) where
  positive : 0 < c
  discreteCoins : ℕ
  discrete_unit : discreteCoins = 1
  /-- Continuum one-act cost equals discrete coin count (act-count invariance). -/
  continuum_act_equals_coins : oneActCurvature c = (discreteCoins : ℝ)

/-- Dropping the act-count match leaves a bare scaffold. -/
def OneActCoinCorrespondence.toBare {c : ℝ} (h : OneActCoinCorrespondence c) :
    BareCoinActScaffold c where
  positive := h.positive
  discreteCoins := h.discreteCoins
  discrete_unit := h.discrete_unit

/-! ## Conditional forcing (packaging path) -/

theorem oneActCoinCorrespondence_forces_unit
    {c : ℝ} (h : OneActCoinCorrespondence c) : c = 1 := by
  have hcurv : oneActCurvature c = 1 := by
    simpa [h.discrete_unit] using h.continuum_act_equals_coins
  exact (unit_forced_by_one_act h.positive).mp hcurv

theorem oneActCoinCorrespondence_forces_calibrated
    {c : ℝ} (h : OneActCoinCorrespondence c) :
    IsCalibrated (fun x => costLambda c x) := by
  have hc1 : c = 1 := oneActCoinCorrespondence_forces_unit h
  exact (costLambda_isCalibrated_iff h.positive).mpr hc1

/-- Packaging equivalence on the positive gauge family: nonempty coin
correspondence at `c` iff `IsCalibrated` for `costLambda c`. -/
theorem oneActCoinCorrespondence_iff_calibrated {c : ℝ} (hc : 0 < c) :
    Nonempty (OneActCoinCorrespondence c) ↔
      IsCalibrated (fun x => costLambda c x) := by
  constructor
  · rintro ⟨h⟩
    exact oneActCoinCorrespondence_forces_calibrated h
  · intro hCal
    have hc1 : c = 1 := (costLambda_isCalibrated_iff hc).mp hCal
    refine ⟨⟨hc, 1, rfl, ?_⟩⟩
    rw [oneActCurvature_eq, hc1]
    norm_num

theorem oneActCurvature_one_iff_calibrated {c : ℝ} (hc : 0 < c) :
    oneActCurvature c = 1 ↔ IsCalibrated (fun x => costLambda c x) := by
  rw [unit_forced_by_one_act hc, costLambda_isCalibrated_iff hc]

/-- Normalized one-act interface at unit `c` is likewise packaging of curvature = 1. -/
theorem normalizedInterface_at_unit_iff_curvature_one {c : ℝ} (hc : 0 < c) :
    (∃ I : NormalizedOneActInterface, I.unit = c) ↔ oneActCurvature c = 1 := by
  constructor
  · rintro ⟨I, hI⟩
    simpa [← hI] using I.curvature_unit
  · intro hcurv
    exact ⟨⟨c, hc, hcurv⟩, rfl⟩

/-- Physical one-act instrument locked at unit `c` packages the same datum. -/
theorem oneActInstrument_at_unit_iff_curvature_one {c : ℝ} (hc : 0 < c) :
    (∃ I : OneActInstrument, I.unit = c) ↔ oneActCurvature c = 1 := by
  constructor
  · rintro ⟨I, hI⟩
    have hlock : I.readout = 1 := I.locked_to_one
    have : oneActCurvature I.unit = 1 := by
      rw [← I.reads_curvature, hlock]
    simpa [← hI] using this
  · intro hcurv
    refine ⟨⟨c, hc, 1, ?_, rfl⟩, rfl⟩
    exact hcurv.symm

/-! ## Countermodel (controversial conjunct dropped) -/

/-- Full non-calibration cost laws for a gauge member (no `IsCalibrated`). -/
def FullNonCalibrationCostLaws (c : ℝ) : Prop :=
  IsReciprocalCost (fun x => costLambda c x) ∧
    IsNormalized (fun x => costLambda c x) ∧
    SatisfiesCompositionLaw (fun x => costLambda c x) ∧
    ContinuousOn (fun x => costLambda c x) (Set.Ioi 0)

theorem fullNonCalibrationCostLaws (c : ℝ) : FullNonCalibrationCostLaws c :=
  ⟨costLambda_isReciprocalCost c, costLambda_isNormalized c,
    costLambda_satisfiesCompositionLaw c, costLambda_continuousOn c⟩

/-- Without the act-count match, a free scale `c = 2 ≠ 1` still satisfies the
bare scaffold and the full non-calibration cost laws. -/
theorem countermodel_without_act_count_match :
    ∃ c : ℝ,
      Nonempty (BareCoinActScaffold c) ∧
        c ≠ 1 ∧
        FullNonCalibrationCostLaws c ∧
        ¬ IsCalibrated (fun x => costLambda c x) := by
  refine ⟨2, ⟨⟨two_pos, 1, rfl⟩⟩, by norm_num, fullNonCalibrationCostLaws 2, ?_⟩
  intro hCal
  have : (2 : ℝ) = 1 := (costLambda_isCalibrated_iff two_pos).mp hCal
  norm_num at this

/-- The canonical unit does satisfy the coin correspondence (consistency, not
necessity from weaker axioms). -/
def canonical_oneActCoinCorrespondence : OneActCoinCorrespondence 1 where
  positive := one_pos
  discreteCoins := 1
  discrete_unit := rfl
  continuum_act_equals_coins := by
    rw [oneActCurvature_eq]
    norm_num

/-! ## Unique positive scale residual inside the gauge family -/

/-- Unique positive scale parameter for a fixed gauge-family member. -/
theorem unique_positive_scale_in_gauge_family {c : ℝ} (hc : 0 < c) :
    ∃! lam : ℝ, 0 < lam ∧ (fun x => costLambda lam x) = (fun x => costLambda c x) := by
  refine ⟨c, ⟨hc, rfl⟩, ?_⟩
  intro lam ⟨hlam, heq⟩
  exact costLambda_inj hlam hc heq

/-! ## WALL binder + OPEN residual -/

/-- **Lane A WALL binder.** Assembles: packaging-equivalent coin premise ⇒ unit;
countermodel with free `c` when the match is dropped; unique scale residual in
the gauge family; independence floor; explicit packaging equivalences for the
in-repo “forces unit” instruments. Does **not** claim three-axiom discharge. -/
structure CalibrationNecessity : Prop where
  coin_forces_unit :
    ∀ {c : ℝ}, OneActCoinCorrespondence c → c = 1
  coin_forces_calibrated :
    ∀ {c : ℝ}, OneActCoinCorrespondence c →
      IsCalibrated (fun x => costLambda c x)
  coin_packaging_iff :
    ∀ {c : ℝ}, 0 < c →
      (Nonempty (OneActCoinCorrespondence c) ↔
        IsCalibrated (fun x => costLambda c x))
  curvature_packaging_iff :
    ∀ {c : ℝ}, 0 < c →
      (oneActCurvature c = 1 ↔ IsCalibrated (fun x => costLambda c x))
  normalized_interface_packaging :
    ∀ {c : ℝ}, 0 < c →
      ((∃ I : NormalizedOneActInterface, I.unit = c) ↔ oneActCurvature c = 1)
  instrument_packaging :
    ∀ {c : ℝ}, 0 < c →
      ((∃ I : OneActInstrument, I.unit = c) ↔ oneActCurvature c = 1)
  countermodel_free_scale :
    ∃ c : ℝ,
      Nonempty (BareCoinActScaffold c) ∧
        c ≠ 1 ∧
        FullNonCalibrationCostLaws c ∧
        ¬ IsCalibrated (fun x => costLambda c x)
  unique_gauge_scale :
    ∀ {c : ℝ}, 0 < c →
      ∃! lam : ℝ, 0 < lam ∧ (fun x => costLambda lam x) = (fun x => costLambda c x)
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
  /-- Packaging-shaped pins are exactly the in-repo unit pins among cost-law
  models of the gauge family. -/
  packaging_only_pins_unit :
    ∀ {c : ℝ}, 0 < c →
      (IsCalibrated (fun x => costLambda c x) ↔ c = 1) ∧
        (oneActCurvature c = 1 ↔ c = 1) ∧
        (Nonempty (OneActCoinCorrespondence c) ↔ c = 1)

/-- The WALL / COND package holds by assembling existing theorems. -/
theorem calibrationNecessity_holds : CalibrationNecessity where
  coin_forces_unit := fun h => oneActCoinCorrespondence_forces_unit h
  coin_forces_calibrated := fun h => oneActCoinCorrespondence_forces_calibrated h
  coin_packaging_iff := fun hc => oneActCoinCorrespondence_iff_calibrated hc
  curvature_packaging_iff := fun hc => oneActCurvature_one_iff_calibrated hc
  normalized_interface_packaging := fun hc =>
    normalizedInterface_at_unit_iff_curvature_one hc
  instrument_packaging := fun hc => oneActInstrument_at_unit_iff_curvature_one hc
  countermodel_free_scale := countermodel_without_act_count_match
  unique_gauge_scale := fun hc => unique_positive_scale_in_gauge_family hc
  independence_floor := calibration_is_the_only_hypothesis_pinning_J
  packaging_only_pins_unit := fun hc => by
    refine ⟨costLambda_isCalibrated_iff hc, unit_forced_by_one_act hc, ?_⟩
    constructor
    · intro h
      obtain ⟨corr⟩ := h
      exact oneActCoinCorrespondence_forces_unit corr
    · intro hc1
      exact (oneActCoinCorrespondence_iff_calibrated hc).mpr
        ((costLambda_isCalibrated_iff hc).mpr hc1)

/-- OPEN residual: a Recognition-native premise `P` on the gauge parameter that
forces unit calibration, fails on the independence countermodel when its
controversial conjunct is dropped, and is **not** packaging-equivalent to
`IsCalibrated` / `oneActCurvature = 1` / `locked_to_one`.

This declaration names the missing bridge. There is intentionally **no**
`calibrationNecessityOpen_holds` theorem. Packaging inhabitants
(`P := fun c => IsCalibrated (costLambda c)`, or coin correspondence with
curvature readout) are not Recognition discharge of the hard half.
-/
def CalibrationNecessityOpen : Prop :=
  ∃ (P : ℝ → Prop),
    (∀ c : ℝ, 0 < c → P c → IsCalibrated (fun x => costLambda c x)) ∧
      (∃ c : ℝ,
        0 < c ∧ c ≠ 1 ∧ FullNonCalibrationCostLaws c ∧ ¬ P c) ∧
      (∀ c : ℝ, 0 < c →
        ¬ (P c ↔ IsCalibrated (fun x => costLambda c x))) ∧
      (∀ c : ℝ, 0 < c → ¬ (P c ↔ oneActCurvature c = 1))

/-- Explicit wall theorem: the attempted coin premise is packaging, and free
`c` survives without it. -/
theorem calibration_necessity_is_wall :
    (∀ {c : ℝ}, 0 < c →
      (Nonempty (OneActCoinCorrespondence c) ↔
        IsCalibrated (fun x => costLambda c x))) ∧
      (∃ c : ℝ,
        Nonempty (BareCoinActScaffold c) ∧
          c ≠ 1 ∧
          FullNonCalibrationCostLaws c ∧
          ¬ IsCalibrated (fun x => costLambda c x)) ∧
      (∀ {c : ℝ}, 0 < c →
        (oneActCurvature c = 1 ↔ IsCalibrated (fun x => costLambda c x))) :=
  ⟨fun hc => oneActCoinCorrespondence_iff_calibrated hc,
    countermodel_without_act_count_match,
    fun hc => oneActCurvature_one_iff_calibrated hc⟩

end PublicSpine
end Foundation
end IndisputableMonolith
