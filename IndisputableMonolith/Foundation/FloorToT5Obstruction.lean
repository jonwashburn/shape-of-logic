import Mathlib
import IndisputableMonolith.Foundation.DistinctionToT4
import IndisputableMonolith.Foundation.DistinctionToJCost
import IndisputableMonolith.Foundation.PositiveRatioBridgeStrict
import IndisputableMonolith.Foundation.PrimitiveDistinction
import IndisputableMonolith.Foundation.ObjectDistinctionFloor
import IndisputableMonolith.Foundation.UniversalInstantiationFromDistinction

/-!
# Floor → T5 obstruction: what the Boolean floor supplies, and what it does not

Mission receipt for the T4 → T5 seam.

`DistinctionToJCost.distinction_forces_T5` places the continuous J / RCL surface
**beside** the distinction-threaded floor (orbit equivalence to a supplied
positive-ratio realization). It does not put continuum log-coordinates *inside*
the two-class quotient.

This module makes that split machine-checkable:

1. **Supply.** The Boolean T0–T4 floor from a distinction supplies a forced
   quotient ≃ `Bool`, a recognition-work cost, and a `LogicRealization` whose
   orbit is `LogicNat`.
2. **Obstruction.** That same floor cannot carry injective log-coordinate
   positive-ratio coordinates (`PositiveRatioBridgeStrict`).
3. **Decoys.** (a) The T4 floor coexists with that obstruction. (b) Equality /
   Hamming cost on positive reals fails composition consistency, so the
   floor-native equality cost is not the analytic recognition cost.

Honest reading: T5 is not carrier-forced from the Boolean floor alone. The
analytic positive-ratio layer remains a named bridge input, matching
`forces_vs_instantiates`.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace FloorToT5Obstruction

open DistinctionToT4
open DistinctionToJCost
open PositiveRatioBridgeStrict
open PrimitiveDistinction

/-! ## 1. What the Boolean T0–T4 floor supplies toward T5 -/

/-- Exact inventory of what a distinction-threaded T0–T4 floor gives the T5
bridge, and nothing more. -/
structure FloorSupplyTowardT5
    {K : Type} (h : ∃ x y : K, x ≠ y) : Prop where
  /-- T4 surface on the forced quotient. -/
  t4 : T4_FromDistinction h
  /-- Forced quotient is Boolean. -/
  quotient_bool : Nonempty (ForcedQuotient h ≃ Bool)
  /-- Recognition-work cost on the forced quotient. -/
  recognition_work :
    Nonempty (CostFromDistinction.CostFunction.RecognitionWorkConstraintCert
      (ForcedQuotient h))
  /-- Law-of-Logic realization on the forced quotient. -/
  logic_realization : Nonempty LogicRealization.{0, 0}
  /-- That realization's orbit is canonically `LogicNat`. -/
  orbit_is_LogicNat :
    Nonempty
      ((forcedQuotientLogicRealization h).Orbit ≃
        ArithmeticFromLogic.LogicNat)

/-- The distinction-threaded T4 floor supplies exactly the inventory above. -/
theorem floor_supply_toward_T5
    {K : Type} (h : ∃ x y : K, x ≠ y) :
    FloorSupplyTowardT5 h where
  t4 := distinction_forces_T4 h
  quotient_bool := ⟨forcedQuotientBoolEquiv h⟩
  recognition_work := forcedQuotient_recognition_work_constraint h
  logic_realization := forcedQuotient_logicRealization_nonempty h
  orbit_is_LogicNat :=
    ⟨(forcedQuotientLogicRealization h).orbitEquivLogicNat⟩

/-! ## 2. Kernel obstruction: bare floor does not contain T5 continuum -/

/-- **Obstruction.** The forced two-class quotient cannot carry injective
log-coordinate positive-ratio coordinates. Continuum T5 geometry is not
internal to the Boolean floor. -/
theorem bare_floor_no_log_positive_ratio_coordinates
    {K : Type} (h : ∃ x y : K, x ≠ y) :
    ¬ Nonempty (LogPositiveRatioCoordinates h) :=
  forced_quotient_no_log_positive_ratio_coordinates h

/-- Concrete Boolean instance of the continuum obstruction. -/
theorem bool_floor_no_T5_continuum_coordinates :
    ¬ Nonempty (LogPositiveRatioCoordinates
      (K := Bool) ⟨false, true, Bool.noConfusion⟩) :=
  bool_floor_no_log_positive_ratio_coordinates

/-! ## 3. Decoys -/

/-- **Decoy A.** The T4 floor coexists with the proved absence of T5 continuum
coordinates on that same floor. Having T4 therefore does not put log-positive
ratio coordinates inside the carrier quotient. -/
theorem t4_floor_coexists_with_no_log_coordinates
    {K : Type} (h : ∃ x y : K, x ≠ y) :
    T4_FromDistinction h ∧
      ¬ Nonempty (LogPositiveRatioCoordinates h) :=
  ⟨distinction_forces_T4 h,
    bare_floor_no_log_positive_ratio_coordinates h⟩

/-- **Decoy B.** Floor-native equality / Hamming cost on positive reals fails
composition consistency, so it is not the analytic recognition cost used by
T5 (`law_of_logic_forces_jcost`). -/
theorem equality_cost_not_analytic_recognition_cost :
    ∃ weight : ℝ,
      weight ≠ 0 ∧
        ¬ CompositionConsistency (hammingCostOnReal weight) :=
  ⟨(1 : ℝ), by norm_num, equality_cost_insufficient_for_recognition 1 (by norm_num)⟩

/-- Supply plus obstruction on one record: what the floor gives, and the
continuum coordinate it refuses. -/
theorem floor_supply_and_continuum_obstruction
    {K : Type} (h : ∃ x y : K, x ≠ y) :
    FloorSupplyTowardT5 h ∧
      ¬ Nonempty (LogPositiveRatioCoordinates h) :=
  ⟨floor_supply_toward_T5 h, bare_floor_no_log_positive_ratio_coordinates h⟩

/-! ## 4. Certificate: honest T4 → T5 seam -/

/-- Machine-checkable T4 → T5 seam certificate. -/
structure FloorToT5SeamCert : Prop where
  /-- Boolean floor supply toward T5. -/
  supply :
    ∀ {K : Type} (h : ∃ x y : K, x ≠ y), FloorSupplyTowardT5 h
  /-- Continuum log-coordinates are absent from the forced quotient. -/
  continuum_obstruction :
    ∀ {K : Type} (h : ∃ x y : K, x ≠ y),
      ¬ Nonempty (LogPositiveRatioCoordinates h)
  /-- Decoy A: T4 coexists with that obstruction. -/
  decoy_t4_without_continuum :
    ∀ {K : Type} (h : ∃ x y : K, x ≠ y),
      T4_FromDistinction h ∧
        ¬ Nonempty (LogPositiveRatioCoordinates h)
  /-- Decoy B: equality cost is not analytic recognition cost. -/
  decoy_equality_cost :
    ∃ weight : ℝ,
      weight ≠ 0 ∧
        ¬ CompositionConsistency (hammingCostOnReal weight)
  /-- Matches the carrier-forces-floor half of `forces_vs_instantiates`
  (T-1–T4 spine from the supplied distinction). -/
  forces_vs_instantiates_aligned :
    ∀ (K : Type) (h : ∃ x y : K, x ≠ y),
      ObjectDistinctionFloor.CarrierForcedFloor K h

/-- The T4 → T5 seam certificate. -/
theorem floorToT5SeamCert : FloorToT5SeamCert where
  supply := fun h => floor_supply_toward_T5 h
  continuum_obstruction := fun h =>
    bare_floor_no_log_positive_ratio_coordinates h
  decoy_t4_without_continuum := fun h =>
    t4_floor_coexists_with_no_log_coordinates h
  decoy_equality_cost := equality_cost_not_analytic_recognition_cost
  forces_vs_instantiates_aligned :=
    fun K h => DistinctionToT4.distinction_forces_T0_to_T4 K h

/-- Headline obstruction: bare Boolean / forced-quotient floor does not force
the T5 continuum positive-ratio coordinate surface. -/
theorem bare_floor_does_not_force_T5_continuum
    {K : Type} (h : ∃ x y : K, x ≠ y)
    (_supply : FloorSupplyTowardT5 h) :
    ¬ Nonempty (LogPositiveRatioCoordinates h) :=
  bare_floor_no_log_positive_ratio_coordinates h

end FloorToT5Obstruction
end Foundation
end IndisputableMonolith
