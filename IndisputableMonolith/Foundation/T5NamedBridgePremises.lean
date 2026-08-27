import Mathlib
import IndisputableMonolith.Foundation.FloorToT5Obstruction
import IndisputableMonolith.Foundation.DistinctionToJCost
import IndisputableMonolith.Foundation.PositiveRatioBridgeStrict
import IndisputableMonolith.Foundation.PrimitiveDistinction
import IndisputableMonolith.CostUniqueness

/-!
# Named T5 bridge premises: FloorSupplyTowardT5 → T5_FromDistinction

Mission receipt for the named-bridge arc after `FloorToT5Obstruction`.

`FloorSupplyTowardT5` is what the Boolean T0–T4 floor genuinely supplies.
`T5_FromDistinction` also carries continuous positive-ratio / J / RCL content.
This module names exactly the analytic premises that fill that gap, proves the
upgrade, discharges those premises as theorems about the positive-ratio
surface (not as floor consequences), and records omission decoys.

Honest status relative to the Boolean floor: every field of
`AnalyticT5BridgePremises` remains unforced from `FloorSupplyTowardT5`
(`FloorToT5Obstruction` already proves continuum coordinates are absent).
They are THEOREM on the ℝ>0 / J carrier once that analytic surface is named.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace T5NamedBridgePremises

open Cost
open Cost.FunctionalEquation
open LogicAsFunctionalEquation
open DistinctionToJCost
open FloorToT5Obstruction
open PositiveRatioBridgeStrict
open PrimitiveDistinction

/-! ## 1. Exact analytic premise inventory -/

/-- Everything `T5_FromDistinction` needs that is not already in
`FloorSupplyTowardT5`. These are positive-ratio / J facts, not Boolean-floor
consequences. -/
structure AnalyticT5BridgePremises : Prop where
  /-- Canonical J positive-ratio comparison satisfies the Law of Logic. -/
  j_comparison_laws : SatisfiesLawsOfLogic jcostComparison
  /-- Law of Logic on that comparison forces an RCL-form combiner. -/
  rcl_from_laws :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      DAlembert.Inevitability.HasMultiplicativeConsistency
        (derivedCost jcostComparison) P ∧
      (∀ u v, P u v = 2 * u + 2 * v + c * u * v)
  /-- J is reciprocal. -/
  J_reciprocal : IsReciprocalCost Cost.Jcost
  /-- J is normalized at 1. -/
  J_normalized : IsNormalized Cost.Jcost
  /-- J satisfies the Recognition Composition Law. -/
  J_composition : SatisfiesCompositionLaw Cost.Jcost
  /-- J is log-calibrated. -/
  J_calibrated : IsCalibrated Cost.Jcost
  /-- J is continuous on positive reals. -/
  J_continuous : ContinuousOn Cost.Jcost (Set.Ioi 0)
  /-- Uniqueness: the T5 hypothesis package forces any such cost to equal J. -/
  uniqueness :
    ∀ (F : ℝ → ℝ),
      AczelSmoothnessPackage →
      IsReciprocalCost F →
      IsNormalized F →
      SatisfiesCompositionLaw F →
      IsCalibrated F →
      ContinuousOn F (Set.Ioi 0) →
      ∀ {x : ℝ}, 0 < x → F x = Cost.Jcost x

/-- The named analytic premises, discharged as global positive-ratio / J
theorems. -/
theorem analyticT5BridgePremises : AnalyticT5BridgePremises where
  j_comparison_laws := jcostComparison_satisfies_laws
  rcl_from_laws :=
    positiveRatio_law_forces_RCL jcostComparison jcostComparison_satisfies_laws
  J_reciprocal := CostUniqueness.Jcost_is_reciprocal
  J_normalized := CostUniqueness.Jcost_is_normalized
  J_composition := CostUniqueness.Jcost_satisfies_composition_law
  J_calibrated := CostUniqueness.Jcost_is_calibrated
  J_continuous := CostUniqueness.Jcost_continuous_pos
  uniqueness := by
    intro F hAczel hRecip hNorm hComp hCalib hCont x hx
    let _ : AczelSmoothnessPackage := hAczel
    exact Cost.FunctionalEquation.law_of_logic_forces_jcost F
      hRecip hNorm hComp hCalib hCont x hx

/-! ## 2. Upgrade: floor supply + named premises ⊢ T5_FromDistinction -/

/-- **Upgrade theorem.** Boolean-floor supply plus the named analytic premises
yield the distinction-threaded T5 surface. -/
theorem t5_from_floor_supply_plus_analytic
    {K : Type} {h : ∃ x y : K, x ≠ y}
    (supply : FloorSupplyTowardT5 h)
    (bridge : AnalyticT5BridgePremises) :
    T5_FromDistinction h where
  t4 := supply.t4
  floor_realization := supply.logic_realization
  j_comparison_laws := bridge.j_comparison_laws
  orbit_invariant :=
    ⟨forcedQuotient_to_positiveRatio_orbit h
      jcostComparison bridge.j_comparison_laws⟩
  rcl_surface := bridge.rcl_from_laws
  J_reciprocal := bridge.J_reciprocal
  J_normalized := bridge.J_normalized
  J_composition := bridge.J_composition
  J_calibrated := bridge.J_calibrated
  J_continuous := bridge.J_continuous
  uniqueness := bridge.uniqueness

/-- Specialization: discharged premises upgrade every distinction floor. -/
theorem t5_from_floor_supply
    {K : Type} {h : ∃ x y : K, x ≠ y}
    (supply : FloorSupplyTowardT5 h) :
    T5_FromDistinction h :=
  t5_from_floor_supply_plus_analytic supply analyticT5BridgePremises

/-- The existing packaging theorem factors as supply + named premises. -/
theorem distinction_forces_T5_factors
    {K : Type} (h : ∃ x y : K, x ≠ y) :
    T5_FromDistinction h :=
  t5_from_floor_supply (floor_supply_toward_T5 h)

/-! ## 3. Relative to the Boolean floor: premises stay unforced -/

/-- **Floor status.** Continuum log-coordinates remain absent from the forced
quotient even after the floor supply is granted. Naming analytic premises does
not put them inside the Boolean floor. -/
theorem analytic_premises_do_not_live_on_floor
    {K : Type} (h : ∃ x y : K, x ≠ y)
    (_supply : FloorSupplyTowardT5 h)
    (_bridge : AnalyticT5BridgePremises) :
    ¬ Nonempty (LogPositiveRatioCoordinates h) :=
  bare_floor_no_log_positive_ratio_coordinates h

/-- Supply alone refuses continuum T5 coordinates (omission of the analytic
carrier). -/
theorem omission_without_analytic_carrier
    {K : Type} (h : ∃ x y : K, x ≠ y)
    (supply : FloorSupplyTowardT5 h) :
    ¬ Nonempty (LogPositiveRatioCoordinates h) :=
  bare_floor_does_not_force_T5_continuum h supply

/-- Omission of composition consistency: floor-native equality / Hamming cost
is not analytic recognition cost. -/
theorem omission_without_composition_consistency :
    ∃ weight : ℝ,
      weight ≠ 0 ∧
        ¬ CompositionConsistency (hammingCostOnReal weight) :=
  equality_cost_not_analytic_recognition_cost

/-- Law-of-Logic on a positive-ratio comparison is the named gate into RCL;
without such a comparison the RCL surface is not available from the floor. -/
theorem rcl_requires_named_positive_ratio_laws
    (C : ComparisonOperator) (hC : SatisfiesLawsOfLogic C) :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      DAlembert.Inevitability.HasMultiplicativeConsistency (derivedCost C) P ∧
      (∀ u v, P u v = 2 * u + 2 * v + c * u * v) :=
  positiveRatio_law_forces_RCL C hC

/-! ## 4. Certificate -/

/-- Machine-checkable named T5 bridge certificate. -/
structure T5NamedBridgeCert : Prop where
  /-- Exact analytic premise list. -/
  premises : AnalyticT5BridgePremises
  /-- Upgrade: supply + premises ⊢ T5_FromDistinction. -/
  upgrade :
    ∀ {K : Type} {h : ∃ x y : K, x ≠ y},
      FloorSupplyTowardT5 h →
        AnalyticT5BridgePremises →
          T5_FromDistinction h
  /-- Discharged premises specialize the upgrade. -/
  upgrade_discharged :
    ∀ {K : Type} {h : ∃ x y : K, x ≠ y},
      FloorSupplyTowardT5 h → T5_FromDistinction h
  /-- Continuum coordinates still absent from the floor after naming premises. -/
  premises_not_on_floor :
    ∀ {K : Type} (h : ∃ x y : K, x ≠ y),
      FloorSupplyTowardT5 h →
        AnalyticT5BridgePremises →
          ¬ Nonempty (LogPositiveRatioCoordinates h)
  /-- Omission decoy A: no analytic continuum carrier on the floor. -/
  decoy_no_continuum_carrier :
    ∀ {K : Type} (h : ∃ x y : K, x ≠ y),
      FloorSupplyTowardT5 h →
        ¬ Nonempty (LogPositiveRatioCoordinates h)
  /-- Omission decoy B: equality cost fails composition consistency. -/
  decoy_equality_cost :
    ∃ weight : ℝ,
      weight ≠ 0 ∧
        ¬ CompositionConsistency (hammingCostOnReal weight)
  /-- RCL from named positive-ratio Law of Logic. -/
  rcl_from_named_laws :
    ∀ (C : ComparisonOperator),
      SatisfiesLawsOfLogic C →
        ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
          DAlembert.Inevitability.HasMultiplicativeConsistency
            (derivedCost C) P ∧
          (∀ u v, P u v = 2 * u + 2 * v + c * u * v)

/-- The named T5 bridge certificate. -/
theorem t5NamedBridgeCert : T5NamedBridgeCert where
  premises := analyticT5BridgePremises
  upgrade := fun supply bridge =>
    t5_from_floor_supply_plus_analytic supply bridge
  upgrade_discharged := fun supply => t5_from_floor_supply supply
  premises_not_on_floor := fun h supply bridge =>
    analytic_premises_do_not_live_on_floor h supply bridge
  decoy_no_continuum_carrier := fun h supply =>
    omission_without_analytic_carrier h supply
  decoy_equality_cost := omission_without_composition_consistency
  rcl_from_named_laws := fun C hC =>
    rcl_requires_named_positive_ratio_laws C hC

end T5NamedBridgePremises
end Foundation
end IndisputableMonolith
