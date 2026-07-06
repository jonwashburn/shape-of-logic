import Mathlib
import IndisputableMonolith.Foundation.NothingToDistinction
import IndisputableMonolith.Foundation.TMinus1ToT1Bridge
import IndisputableMonolith.Foundation.LogicRealization
import IndisputableMonolith.Foundation.UniversalForcing
import IndisputableMonolith.Foundation.UniversalInstantiationFromDistinction
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation
import IndisputableMonolith.Foundation.DiscretenessForcing
import IndisputableMonolith.Foundation.LedgerForcing
import IndisputableMonolith.Foundation.PhiForcing
import IndisputableMonolith.Foundation.PhiForcingDerived
import IndisputableMonolith.Foundation.HierarchyDynamics
import IndisputableMonolith.Foundation.DimensionForcing
import IndisputableMonolith.Foundation.CircleWindingChain
import IndisputableMonolith.Foundation.RecognitionForcing
import IndisputableMonolith.Recognition
import IndisputableMonolith.Cost
import IndisputableMonolith.CostUniqueness

/-!
# Public T-1 through T8 Forcing Spine

This module exposes the public, theory-only T-1 through T8 forcing spine:

* T-1: absolute distinguishability floor.
* T0: Boolean recognition-work split.
* T1: cost-form Meta-Principle.
* T2: two-state discreteness of the floor.
* T3: additive ledger bookkeeping.
* T4: recognition witness on the discrete floor.
* T5: uniqueness of the canonical reciprocal cost.
* T6: φ forced by realized self-similar hierarchy.
* T7: eight-tick cadence from dimension.
* T8: D = 3 from linking / eight-tick / gap-sync compatibility.

It deliberately stops before the private operator / measurement layers
that live in the `/reality` repository.
-/

namespace IndisputableMonolith
namespace Foundation
namespace TMinus1ToT8Bridge

open Real
open CostFromDistinction

namespace T01

/-- Compatibility alias for the Boolean recognition-work cost used by the
public T-1 through T8 spine. -/
abbrev boolRecognitionCost : CostFromDistinction.CostFunction Bool :=
  TMinus1ToT1Bridge.boolRecognitionCost

end T01

/-! ## T-1, T0, T1 aliases from the public first bridge -/

abbrev TMinus1_AbsoluteFloor := TMinus1ToT1Bridge.TMinus1_AbsoluteFloor.{0, 0}
abbrev T0_Logic_Forced := TMinus1ToT1Bridge.T0_Logic_Forced
abbrev T1_MP_Forced := TMinus1ToT1Bridge.T1_MetaPrinciple_Forced
abbrev TMinus1_To_T0_Bridge := TMinus1ToT1Bridge.TMinus1_To_T0_Bridge
abbrev T0_To_T1_Bridge := TMinus1ToT1Bridge.T0_To_T1_Bridge

def tminus1_holds : TMinus1_AbsoluteFloor := @TMinus1ToT1Bridge.tminus1_holds.{0, 0}
def tminus1_to_t0_bridge : TMinus1_AbsoluteFloor → TMinus1_To_T0_Bridge :=
  TMinus1ToT1Bridge.tminus1_to_t0_bridge
def t0_to_t1_bridge_holds : (h0 : T0_Logic_Forced) → T0_To_T1_Bridge h0 :=
  TMinus1ToT1Bridge.t0_to_t1_bridge_holds

/-! ## Normalized two-point floor audit -/

/-- A normalized two-point recognition floor.  This is the abstract version
of the Boolean floor: one empty/consistent point, one marked inconsistent
point, a unit-normalized recognition-work cost, and an equivalence to `Bool`
showing that `Bool` is only the canonical representative. -/
structure NormalizedTwoPointRecognitionFloor
    (Config : Type) [CostFromDistinction.ConfigSpace Config]
    (mark : Config) (cost : CostFromDistinction.CostFunction Config)
    (toBoolEquiv : Config ≃ Bool) : Prop where
  mark_ne_emp : mark ≠ CostFromDistinction.ConfigSpace.emp
  exhaustive :
    ∀ Γ : Config, Γ = CostFromDistinction.ConfigSpace.emp ∨ Γ = mark
  consistent_iff_emp :
    ∀ Γ : Config,
      CostFromDistinction.ConfigSpace.IsConsistent Γ ↔
        Γ = CostFromDistinction.ConfigSpace.emp
  cost_emp_zero : cost.C CostFromDistinction.ConfigSpace.emp = 0
  cost_mark_one : cost.C mark = 1
  toBool_emp : toBoolEquiv CostFromDistinction.ConfigSpace.emp = false
  toBool_mark : toBoolEquiv mark = true

/-- The concrete Boolean floor is the canonical normalized two-point
recognition floor. -/
theorem bool_normalized_two_point_floor :
    NormalizedTwoPointRecognitionFloor Bool true
      TMinus1ToT1Bridge.boolRecognitionCost (Equiv.refl Bool) where
  mark_ne_emp := by
    intro h
    change true = false at h
    exact Bool.noConfusion h
  exhaustive := by
    intro Γ
    cases Γ
    · exact Or.inl rfl
    · exact Or.inr rfl
  consistent_iff_emp := by
    intro Γ
    rfl
  cost_emp_zero := rfl
  cost_mark_one := rfl
  toBool_emp := rfl
  toBool_mark := rfl

instance NormalizedTwoPointRecognitionFloor.instSubsingleton
    {Config : Type} [CostFromDistinction.ConfigSpace Config]
    {mark : Config} {cost : CostFromDistinction.CostFunction Config}
    {toBoolEquiv : Config ≃ Bool} :
    Subsingleton (NormalizedTwoPointRecognitionFloor Config mark cost toBoolEquiv) where
  allEq _ _ := by rfl

theorem normalized_two_point_floor_unique
    {Config : Type} [CostFromDistinction.ConfigSpace Config]
    {mark : Config} {cost : CostFromDistinction.CostFunction Config}
    {toBoolEquiv : Config ≃ Bool}
    (h1 h2 : NormalizedTwoPointRecognitionFloor Config mark cost toBoolEquiv) :
    h1 = h2 :=
  Subsingleton.elim _ _

/-- On a normalized two-point floor, the cost is forced to be the `0/1`
indicator pulled back along the equivalence to `Bool`.  This is the
theorem-level form of "unit recognition work" rather than a hidden definition
of the Boolean representative. -/
theorem normalized_two_point_cost_eq_indicator
    {Config : Type} [CostFromDistinction.ConfigSpace Config]
    {mark : Config} {cost : CostFromDistinction.CostFunction Config}
    {toBoolEquiv : Config ≃ Bool}
    (h : NormalizedTwoPointRecognitionFloor Config mark cost toBoolEquiv)
    (Γ : Config) :
    cost.C Γ = if toBoolEquiv Γ = false then 0 else 1 := by
  rcases h.exhaustive Γ with hΓ | hΓ
  · rw [hΓ, h.toBool_emp, h.cost_emp_zero]
    simp
  · rw [hΓ, h.toBool_mark, h.cost_mark_one]
    simp

/-- For fixed empty/marked states, the equivalence-to-`Bool` of a normalized
two-point floor is unique. -/
theorem normalized_two_point_equiv_unique
    {Config : Type} [CostFromDistinction.ConfigSpace Config]
    {mark : Config}
    {cost₁ cost₂ : CostFromDistinction.CostFunction Config}
    {toBoolEquiv₁ toBoolEquiv₂ : Config ≃ Bool}
    (h₁ : NormalizedTwoPointRecognitionFloor Config mark cost₁ toBoolEquiv₁)
    (h₂ : NormalizedTwoPointRecognitionFloor Config mark cost₂ toBoolEquiv₂) :
    toBoolEquiv₁ = toBoolEquiv₂ := by
  ext Γ
  rcases h₁.exhaustive Γ with hΓ | hΓ
  · rw [hΓ, h₁.toBool_emp, h₂.toBool_emp]
  · rw [hΓ, h₁.toBool_mark, h₂.toBool_mark]

/-- Any two normalized two-point recognition costs over the same two-point
shape agree pointwise. -/
theorem normalized_two_point_cost_unique_up_to_equiv
    {Config : Type} [CostFromDistinction.ConfigSpace Config]
    {mark : Config}
    {cost₁ cost₂ : CostFromDistinction.CostFunction Config}
    {toBoolEquiv₁ toBoolEquiv₂ : Config ≃ Bool}
    (h₁ : NormalizedTwoPointRecognitionFloor Config mark cost₁ toBoolEquiv₁)
    (h₂ : NormalizedTwoPointRecognitionFloor Config mark cost₂ toBoolEquiv₂) :
    toBoolEquiv₁ = toBoolEquiv₂ ∧ ∀ Γ : Config, cost₁.C Γ = cost₂.C Γ := by
  have heq : toBoolEquiv₁ = toBoolEquiv₂ :=
    normalized_two_point_equiv_unique h₁ h₂
  constructor
  · exact heq
  · intro Γ
    rw [normalized_two_point_cost_eq_indicator h₁ Γ]
    rw [normalized_two_point_cost_eq_indicator h₂ Γ]
    rw [heq]

/-- Any normalized Boolean two-point floor with marked state `true` is the
canonical Boolean floor: the equivalence is `Equiv.refl Bool` and the cost
agrees pointwise with `boolRecognitionCost`. -/
theorem bool_normalized_two_point_floor_unique
    {cost : CostFromDistinction.CostFunction Bool}
    {toBoolEquiv : Bool ≃ Bool}
    (h : NormalizedTwoPointRecognitionFloor Bool true cost toBoolEquiv) :
    toBoolEquiv = Equiv.refl Bool ∧
      ∀ Γ : Bool, cost.C Γ = TMinus1ToT1Bridge.boolRecognitionCost.C Γ := by
  exact normalized_two_point_cost_unique_up_to_equiv
    h bool_normalized_two_point_floor

theorem absolute_bool_floor_unique_normalized_01
    (_floor : AbsoluteFloorClosure.AbsoluteFloorWitness Bool)
    {cost : CostFromDistinction.CostFunction Bool}
    {toBoolEquiv : Bool ≃ Bool}
    (h : NormalizedTwoPointRecognitionFloor Bool true cost toBoolEquiv) :
    toBoolEquiv = Equiv.refl Bool ∧
      ∀ Γ : Bool, cost.C Γ = TMinus1ToT1Bridge.boolRecognitionCost.C Γ :=
  bool_normalized_two_point_floor_unique h

/-! ## T2: discreteness from the floor split -/

structure T2_Discreteness_Forced : Prop where
  state_dichotomy : ∀ Γ : Bool, Γ = false ∨ Γ = true
  states_distinct : (false : Bool) ≠ true
  zero_cost_selects_consistency :
    ∀ Γ : Bool, T01.boolRecognitionCost.C Γ = 0 → Γ = false
  positive_cost_selects_marked :
    ∀ Γ : Bool, 0 < T01.boolRecognitionCost.C Γ → Γ = true

structure T1_To_T2_Bridge (b01 : TMinus1_To_T0_Bridge) (h1 : T1_MP_Forced) :
    Prop where
  floor_used : AbsoluteFloorClosure.AbsoluteFloorWitness Bool
  floor_dichotomy : ∀ Γ : Bool, Γ = false ∨ Γ = true
  floor_states_distinct : (false : Bool) ≠ true
  consistency_is_false :
    ∀ Γ : Bool, CostFromDistinction.ConfigSpace.IsConsistent Γ → Γ = false
  positive_cost_selects_marked :
    ∀ Γ : Bool, 0 < T01.boolRecognitionCost.C Γ → Γ = true
  t2 : T2_Discreteness_Forced

theorem t1_to_t2_bridge_holds
    (b01 : TMinus1_To_T0_Bridge) (h1 : T1_MP_Forced) :
    T1_To_T2_Bridge b01 h1 where
  floor_used := b01.bool_floor
  floor_dichotomy := b01.floor_config.floor_dichotomy
  floor_states_distinct := b01.floor_config.false_true_distinct
  consistency_is_false := fun Γ hΓ =>
    (b01.floor_config.consistency_iff_false Γ).mp hΓ
  positive_cost_selects_marked := by
    intro Γ hpos
    have hinc : ¬CostFromDistinction.ConfigSpace.IsConsistent Γ :=
      (b01.positive_iff_inconsistent Γ).mp hpos
    rcases b01.floor_config.floor_dichotomy Γ with hΓ | hΓ
    · exfalso
      exact hinc ((b01.floor_config.consistency_iff_false Γ).mpr hΓ)
    · exact hΓ
  t2 := {
    state_dichotomy := b01.floor_config.floor_dichotomy
    states_distinct := b01.floor_config.false_true_distinct
    zero_cost_selects_consistency := fun Γ hzero =>
      (b01.floor_config.consistency_iff_false Γ).mp
        (h1.zero_cost_consistent Γ hzero)
    positive_cost_selects_marked := by
      intro Γ hpos
      have hinc : ¬CostFromDistinction.ConfigSpace.IsConsistent Γ :=
        (b01.positive_iff_inconsistent Γ).mp hpos
      rcases b01.floor_config.floor_dichotomy Γ with hΓ | hΓ
      · exfalso
        exact hinc ((b01.floor_config.consistency_iff_false Γ).mpr hΓ)
      · exact hΓ
  }

/-! ## T3: ledger from additive recognition work -/

structure T3_Ledger_Forced : Prop where
  empty_balanced : T01.boolRecognitionCost.C false = 0
  empty_join_left :
    ∀ Γ : Bool, CostFromDistinction.ConfigSpace.join false Γ = Γ
  empty_join_cost_neutral :
    ∀ Γ : Bool,
      T01.boolRecognitionCost.C (CostFromDistinction.ConfigSpace.join false Γ) =
        T01.boolRecognitionCost.C Γ
  independent_join_additive :
    ∀ Γ₁ Γ₂ : Bool,
      CostFromDistinction.ConfigSpace.Independent Γ₁ Γ₂ →
        T01.boolRecognitionCost.C
          (CostFromDistinction.ConfigSpace.join Γ₁ Γ₂) =
        T01.boolRecognitionCost.C Γ₁ + T01.boolRecognitionCost.C Γ₂

structure T0_T2_To_T3_Bridge
    (b01 : TMinus1_To_T0_Bridge) (h0 : T0_Logic_Forced) (h2 : T2_Discreteness_Forced) :
    Prop where
  floor_empty_join :
    ∀ Γ : Bool, CostFromDistinction.ConfigSpace.join false Γ = Γ
  t0_additivity :
    ∀ Γ₁ Γ₂ : Bool,
      CostFromDistinction.ConfigSpace.Independent Γ₁ Γ₂ →
        T01.boolRecognitionCost.C
          (CostFromDistinction.ConfigSpace.join Γ₁ Γ₂) =
        T01.boolRecognitionCost.C Γ₁ + T01.boolRecognitionCost.C Γ₂
  t2_floor_split : ∀ Γ : Bool, Γ = false ∨ Γ = true
  t3 : T3_Ledger_Forced

theorem t0_t2_to_t3_bridge_holds
    (b01 : TMinus1_To_T0_Bridge) (h0 : T0_Logic_Forced) (h2 : T2_Discreteness_Forced) :
    T0_T2_To_T3_Bridge b01 h0 h2 where
  floor_empty_join := b01.floor_config.empty_join_left
  t0_additivity := h0.additive_indep
  t2_floor_split := h2.state_dichotomy
  t3 := {
    empty_balanced := h0.consistency_zero
    empty_join_left := by
      intro Γ
      rcases h2.state_dichotomy Γ with hΓ | hΓ
      · simpa [hΓ] using b01.floor_config.empty_join_left Γ
      · simpa [hΓ] using b01.floor_config.empty_join_left Γ
    empty_join_cost_neutral := by
      intro Γ
      rw [b01.floor_config.empty_join_left Γ]
    independent_join_additive := h0.additive_indep
  }

/-! ## T4: recognition from the discrete balanced floor -/

structure T4_Recognition_Forced : Prop where
  floor_distinction : ∃ a b : Bool, a ≠ b
  floor_recognition : Nonempty (Recognition.Recognize Bool Bool)
  floor_recognition_structure :
    ∃ R : Recognition.RecognitionStructure, R.U = Bool
  zero_cost_recognition :
    T01.boolRecognitionCost.C false = 0 →
      Nonempty (Recognition.Recognize Bool Bool)

structure BalancedFloorRecognition
    (hbalanced : T01.boolRecognitionCost.C false = 0) : Prop where
  source_balance : T01.boolRecognitionCost.C false = 0
  recognition : Nonempty (Recognition.Recognize Bool Bool)

theorem balanced_floor_recognition
    (hbalanced : T01.boolRecognitionCost.C false = 0) :
    BalancedFloorRecognition hbalanced where
  source_balance := hbalanced
  recognition := ⟨⟨false, false⟩⟩

theorem recognition_from_balanced_floor_ledger :
    T01.boolRecognitionCost.C false = 0 →
      Nonempty (Recognition.Recognize Bool Bool) :=
  fun hbalanced => (balanced_floor_recognition hbalanced).recognition

structure T2_T3_To_T4_Bridge (h2 : T2_Discreteness_Forced) (h3 : T3_Ledger_Forced) :
    Prop where
  distinction_from_t2 : ∃ a b : Bool, a ≠ b
  balanced_ledger_from_t3 : T01.boolRecognitionCost.C false = 0
  balanced_floor_recognition_cert :
    BalancedFloorRecognition balanced_ledger_from_t3
  recognition_from_balanced_ledger :
    T01.boolRecognitionCost.C false = 0 →
      Nonempty (Recognition.Recognize Bool Bool)
  t4 : T4_Recognition_Forced

theorem t2_t3_to_t4_bridge_holds
    (h2 : T2_Discreteness_Forced) (h3 : T3_Ledger_Forced) :
    T2_T3_To_T4_Bridge h2 h3 where
  distinction_from_t2 := ⟨false, true, h2.states_distinct⟩
  balanced_ledger_from_t3 := h3.empty_balanced
  balanced_floor_recognition_cert := balanced_floor_recognition h3.empty_balanced
  recognition_from_balanced_ledger := recognition_from_balanced_floor_ledger
  t4 := {
    floor_distinction := ⟨false, true, h2.states_distinct⟩
    floor_recognition := recognition_from_balanced_floor_ledger h3.empty_balanced
    floor_recognition_structure := ⟨{ U := Bool, R := fun a b => a = b }, rfl⟩
    zero_cost_recognition := fun hzero => recognition_from_balanced_floor_ledger hzero
  }

/-! ## T5: unique reciprocal cost from continuous positive-ratio realization -/

namespace T4ToT5

open LogicAsFunctionalEquation

noncomputable def floorRealization : LogicRealization.{0, 0} :=
  UniversalInstantiationFromDistinction.logicRealizationOfDistinction
    Bool false true (by decide)

noncomputable def positiveRatioRealization
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    LogicRealization.{0, 0} :=
  LogicRealization.ofPositiveRatioComparison C h

noncomputable def floor_to_positive_ratio_arithmetic
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    (UniversalForcing.arithmeticOf floorRealization).peano.carrier ≃
      (UniversalForcing.arithmeticOf (positiveRatioRealization C h)).peano.carrier :=
  by
    change floorRealization.Orbit ≃ (positiveRatioRealization C h).Orbit
    exact floorRealization.orbitEquivLogicNat.trans
      (positiveRatioRealization C h).orbitEquivLogicNat.symm

end T4ToT5

structure T4_To_T5_Realization_Bridge (h4 : T4_Recognition_Forced) : Prop where
  t4_floor_recognition : Nonempty (Recognition.Recognize Bool Bool)
  t4_floor_distinction : ∃ a b : Bool, a ≠ b
  floor_realization : Nonempty LogicRealization.{0, 0}
  positive_ratio_realization :
    ∀ (C : LogicAsFunctionalEquation.ComparisonOperator)
      (h : LogicAsFunctionalEquation.SatisfiesLawsOfLogic C),
      Nonempty LogicRealization.{0, 0}
  arithmetic_invariant :
    ∀ (C : LogicAsFunctionalEquation.ComparisonOperator)
      (h : LogicAsFunctionalEquation.SatisfiesLawsOfLogic C),
      Nonempty
        ((UniversalForcing.arithmeticOf T4ToT5.floorRealization).peano.carrier ≃
          (UniversalForcing.arithmeticOf
            (T4ToT5.positiveRatioRealization C h)).peano.carrier)
  rcl_surface :
    ∀ (C : LogicAsFunctionalEquation.ComparisonOperator)
      (h : LogicAsFunctionalEquation.SatisfiesLawsOfLogic C),
      ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
        DAlembert.Inevitability.HasMultiplicativeConsistency
          (LogicAsFunctionalEquation.derivedCost C) P ∧
        (∀ u v, P u v = 2*u + 2*v + c*u*v)

noncomputable def t4_to_t5_bridge_holds (h4 : T4_Recognition_Forced) :
    T4_To_T5_Realization_Bridge h4 where
  t4_floor_recognition := h4.floor_recognition
  t4_floor_distinction := h4.floor_distinction
  floor_realization := ⟨T4ToT5.floorRealization⟩
  positive_ratio_realization := fun C h => ⟨T4ToT5.positiveRatioRealization C h⟩
  arithmetic_invariant := fun C h =>
    ⟨by
      change T4ToT5.floorRealization.Orbit ≃
        (T4ToT5.positiveRatioRealization C h).Orbit
      exact T4ToT5.floorRealization.orbitEquivLogicNat.trans
        (T4ToT5.positiveRatioRealization C h).orbitEquivLogicNat.symm⟩
  rcl_surface := fun C h =>
    LogicAsFunctionalEquation.RCL_is_unique_functional_form_of_logic C h

structure T5_J_Unique : Prop where
  J_reciprocal : Cost.FunctionalEquation.IsReciprocalCost Cost.Jcost
  J_normalized : Cost.FunctionalEquation.IsNormalized Cost.Jcost
  J_composition : Cost.FunctionalEquation.SatisfiesCompositionLaw Cost.Jcost
  J_calibrated : Cost.FunctionalEquation.IsCalibrated Cost.Jcost
  J_continuous : ContinuousOn Cost.Jcost (Set.Ioi 0)
  uniqueness :
    ∀ (F : ℝ → ℝ),
      Cost.FunctionalEquation.AczelSmoothnessPackage →
      Cost.FunctionalEquation.IsReciprocalCost F →
      Cost.FunctionalEquation.IsNormalized F →
      Cost.FunctionalEquation.SatisfiesCompositionLaw F →
      Cost.FunctionalEquation.IsCalibrated F →
      ContinuousOn F (Set.Ioi 0) →
      ∀ {x : ℝ}, 0 < x → F x = Cost.Jcost x

structure T4_To_T5_Cost_Bridge
    {h4 : T4_Recognition_Forced} (bridge : T4_To_T5_Realization_Bridge h4) :
    Prop where
  rcl_surface_available :
    ∀ (C : LogicAsFunctionalEquation.ComparisonOperator)
      (h : LogicAsFunctionalEquation.SatisfiesLawsOfLogic C),
      ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
        DAlembert.Inevitability.HasMultiplicativeConsistency
          (LogicAsFunctionalEquation.derivedCost C) P ∧
        (∀ u v, P u v = 2*u + 2*v + c*u*v)
  rcl_surface_is_bridge_surface :
    rcl_surface_available = bridge.rcl_surface
  t5 : T5_J_Unique

/-- **HONESTY NOTE (2026 audit, T4→T5 arrow).** The T5 record below is
proved entirely from `CostUniqueness` lemmas about `Jcost` and from
`law_of_logic_forces_jcost`; it consumes NOTHING from `bridge` beyond
re-exporting `bridge.rcl_surface` as a field. An earlier revision bound
`bridge.rcl_surface` inside the uniqueness proof as an unused variable
(`_rcl_surface`), which cosmetically suggested the T−1..T4 floor feeds the
T5 proof. It does not: deleting T−1..T4 would break no T5 proof. The
substantive gap — that the floor's own cost provably CANNOT satisfy the
composition law T5 needs (`PrimitiveDistinction.lean`), so the continuous
positive-ratio comparison surface is an imported hypothesis (SI2/C6), not
a consequence of the floor — is recorded in the paper as open problems.
This structure packages the conditional chain; it is not a forcing proof
of T5 from T4.

Repair pointer: `Foundation.RecognitionLedgerFloor` builds the upgraded
carrier (free additive defect ledger `I →₀ ℕ` with kernel-derived
observable equivalence and unconditional additivity) that answers the
audit's kernel/cokernel gaps at the floor level. That module is NOT yet
wired into this chain: no field of this bridge consumes it. Integrating
it — i.e. replacing the imported comparison-surface hypothesis with a
theorem from the ledger floor, if that is possible at all — is an open
task, not a completed step. -/
theorem t4_to_t5_cost_bridge_holds
    {h4 : T4_Recognition_Forced} (bridge : T4_To_T5_Realization_Bridge h4) :
    T4_To_T5_Cost_Bridge bridge where
  rcl_surface_available := bridge.rcl_surface
  rcl_surface_is_bridge_surface := rfl
  t5 := {
    J_reciprocal := CostUniqueness.Jcost_is_reciprocal
    J_normalized := CostUniqueness.Jcost_is_normalized
    J_composition := CostUniqueness.Jcost_satisfies_composition_law
    J_calibrated := CostUniqueness.Jcost_is_calibrated
    J_continuous := CostUniqueness.Jcost_continuous_pos
    uniqueness := fun F hAczel hRecip hNorm hComp hCalib hCont => by
      let _ : Cost.FunctionalEquation.AczelSmoothnessPackage := hAczel
      exact Cost.FunctionalEquation.law_of_logic_forces_jcost F
        hRecip hNorm hComp hCalib hCont
  }

/-! ## T6: φ from realized self-similar hierarchy -/

structure T5_To_T6_SelfSimilarity_Bridge (h5 : T5_J_Unique) : Prop where
  t5_uniqueness_available :
    ∀ (F : ℝ → ℝ),
      Cost.FunctionalEquation.AczelSmoothnessPackage →
      Cost.FunctionalEquation.IsReciprocalCost F →
      Cost.FunctionalEquation.IsNormalized F →
      Cost.FunctionalEquation.SatisfiesCompositionLaw F →
      Cost.FunctionalEquation.IsCalibrated F →
      ContinuousOn F (Set.Ioi 0) →
      ∀ {x : ℝ}, 0 < x → F x = Cost.Jcost x
  internal_hierarchy_forces_phi :
    ∀ (F : ClosedFramework.ClosedObservableFramework)
      (H : HierarchyRealization.RealizedHierarchy F),
      (HierarchyRealization.realized_to_ladder F H).ratio = PhiForcing.φ
  self_similar_forces_golden :
    ∀ S : PhiForcing.SelfSimilar,
      PhiForcing.satisfies_golden_constraint S.ratio
  golden_constraint_unique :
    ∀ r : ℝ, 0 < r → PhiForcing.satisfies_golden_constraint r → r = PhiForcing.φ
  discrete_ledger_ratio_phi :
    ∀ (L : PhiForcing.DiscreteLedger) (r : ℝ),
      PhiForcing.is_self_similar L r → r = PhiForcing.φ

theorem t5_to_t6_bridge_holds (h5 : T5_J_Unique) :
    T5_To_T6_SelfSimilarity_Bridge h5 where
  t5_uniqueness_available := h5.uniqueness
  internal_hierarchy_forces_phi := HierarchyDynamics.bridge_T5_T6_internal
  self_similar_forces_golden := PhiForcing.self_similar_forces_golden_constraint
  golden_constraint_unique := fun r hr hgold =>
    PhiForcing.phi_unique_self_similar hr hgold
  discrete_ledger_ratio_phi := PhiForcing.phi_forced

structure T6_Phi_Forced : Prop where
  phi_equation : PhiForcing.φ^2 = PhiForcing.φ + 1
  phi_positive : PhiForcing.φ > 0
  phi_unique : ∀ r : ℝ, 0 < r → r^2 = r + 1 → r = PhiForcing.φ

theorem t6_phi_unique_from_derived :
    ∀ r : ℝ, 0 < r → r^2 = r + 1 → r = PhiForcing.φ := by
  intro r hr hgolden
  have hr_ne_one : r ≠ 1 := by
    intro hr1
    rw [hr1] at hgolden
    norm_num at hgolden
  have hclosure : 1 + r = r^2 := by linarith [hgolden]
  have hphi : r = Constants.phi :=
    PhiForcingDerived.phi_forcing_complete r hr hr_ne_one hclosure
  simpa [PhiForcing.φ, Constants.phi] using hphi

theorem t6_holds : T6_Phi_Forced := {
  phi_equation := PhiForcing.phi_equation
  phi_positive := PhiForcing.phi_pos
  phi_unique := t6_phi_unique_from_derived
}

structure T5_To_T6_Forced_Bridge (h5 : T5_J_Unique) : Prop where
  self_similarity : T5_To_T6_SelfSimilarity_Bridge h5
  t6 : T6_Phi_Forced

theorem t5_to_t6_forced_bridge_holds (h5 : T5_J_Unique) :
    T5_To_T6_Forced_Bridge h5 where
  self_similarity := t5_to_t6_bridge_holds h5
  t6 := t6_holds

/-! ## T7/T8: eight-tick and dimension -/

structure T7_EightTick_Forced : Prop where
  eight_is_2_cubed : DimensionForcing.eight_tick = 2^3
  from_dimension : DimensionForcing.EightTickFromDimension 3 = DimensionForcing.eight_tick

structure T8_Dimension_Forced : Prop where
  linking_forces_D3 : ∀ D, DimensionForcing.SupportsNontrivialLinking D → D = 3
  eight_tick_forces_D3 :
    ∀ D, DimensionForcing.EightTickFromDimension D = DimensionForcing.eight_tick → D = 3
  unique_dimension : ∃! D, DimensionForcing.RSCompatibleDimension D

theorem t8_holds : T8_Dimension_Forced := {
  linking_forces_D3 := DimensionForcing.linking_requires_D3
  eight_tick_forces_D3 := DimensionForcing.eight_tick_forces_D3
  unique_dimension := DimensionForcing.dimension_forced
}

structure T8_To_T7_EightTick_Bridge (h8 : T8_Dimension_Forced) : Prop where
  compatible_dimension_three :
    ∀ D : DimensionForcing.Dimension,
      DimensionForcing.RSCompatibleDimension D → D = 3
  compatible_dimension_eight_tick :
    ∀ D : DimensionForcing.Dimension,
      DimensionForcing.RSCompatibleDimension D →
        DimensionForcing.EightTickFromDimension D = DimensionForcing.eight_tick
  dimension_three_eight_tick :
    DimensionForcing.EightTickFromDimension 3 = DimensionForcing.eight_tick

theorem t8_to_t7_bridge_holds (h8 : T8_Dimension_Forced) :
    T8_To_T7_EightTick_Bridge h8 where
  compatible_dimension_three := by
    intro D hD
    exact h8.linking_forces_D3 D hD.linking
  compatible_dimension_eight_tick := by
    intro D hD
    exact hD.eight_tick
  dimension_three_eight_tick := rfl

theorem t7_from_t8 (h8 : T8_Dimension_Forced) : T7_EightTick_Forced := {
  eight_is_2_cubed := DimensionForcing.eight_tick_is_2_cubed
  from_dimension := (t8_to_t7_bridge_holds h8).dimension_three_eight_tick
}

/-! ## Complete public T-1 through T8 certificate -/

structure CompleteForcingChainT8 where
  tminus1 : TMinus1_AbsoluteFloor
  tminus1_to_t0 : TMinus1_To_T0_Bridge
  t0 : T0_Logic_Forced
  t0_to_t1 : T0_To_T1_Bridge t0
  t1 : T1_MP_Forced
  t1_to_t2 : T1_To_T2_Bridge tminus1_to_t0 t1
  t2 : T2_Discreteness_Forced
  t0_t2_to_t3 : T0_T2_To_T3_Bridge tminus1_to_t0 t0 t2
  t3 : T3_Ledger_Forced
  t2_t3_to_t4 : T2_T3_To_T4_Bridge t2 t3
  t4 : T4_Recognition_Forced
  t4_to_t5 : T4_To_T5_Realization_Bridge t4
  t4_to_t5_cost : T4_To_T5_Cost_Bridge t4_to_t5
  t5 : T5_J_Unique
  t5_to_t6 : T5_To_T6_Forced_Bridge t5
  t6 : T6_Phi_Forced
  t8 : T8_Dimension_Forced
  t8_to_t7 : T8_To_T7_EightTick_Bridge t8
  t7 : T7_EightTick_Forced

noncomputable def complete_forcing_chain_t8 : CompleteForcingChainT8 :=
  let hm1 := tminus1_holds
  let b01 := tminus1_to_t0_bridge hm1
  let h0 := b01.t0
  let b12 := t0_to_t1_bridge_holds h0
  let h1 := b12.t1
  let b23 := t1_to_t2_bridge_holds b01 h1
  let h2 := b23.t2
  let b03 := t0_t2_to_t3_bridge_holds b01 h0 h2
  let h3 := b03.t3
  let b34 := t2_t3_to_t4_bridge_holds h2 h3
  let h4 := b34.t4
  let b45 := t4_to_t5_bridge_holds h4
  let b45c := t4_to_t5_cost_bridge_holds b45
  let h5 := b45c.t5
  let b56 := t5_to_t6_forced_bridge_holds h5
  let h6 := b56.t6
  let h8 := t8_holds
  let b87 := t8_to_t7_bridge_holds h8
  let h7 := t7_from_t8 h8
  {
    tminus1 := hm1
    tminus1_to_t0 := b01
    t0 := h0
    t0_to_t1 := b12
    t1 := h1
    t1_to_t2 := b23
    t2 := h2
    t0_t2_to_t3 := b03
    t3 := h3
    t2_t3_to_t4 := b34
    t4 := h4
    t4_to_t5 := b45
    t4_to_t5_cost := b45c
    t5 := h5
    t5_to_t6 := b56
    t6 := h6
    t8 := h8
    t8_to_t7 := b87
    t7 := h7
  }

theorem complete_forcing_chain_t8_nonempty : Nonempty CompleteForcingChainT8 :=
  ⟨complete_forcing_chain_t8⟩

/-! ## T-2 through T8 public certificate -/

/-- Public core certificate from the T-2 "absolute nothing" floor through T8.

`NothingToDistinction.nothingToDistinctionCert` discharges the meta-language and
object-distinction floor from the Lean encoding of `Empty`; `CompleteForcingChainT8`
then carries the public T-1 through T8 forcing spine. -/
structure CompleteForcingChainTMinus2ToT8 : Prop where
  tminus2_to_tminus1 : NothingToDistinction.NothingToDistinctionCert
  tminus1_to_t8 : Nonempty CompleteForcingChainT8
  circle_h1_nonzero : MathlibCohomologyBridge.circleH1ZNonzero
  circle_h1_iso_int : MathlibCohomologyBridge.circleH1ZIsoInt
  mathlib_circle_linking_backend :
    Nonempty MathlibCohomologyBridge.MathlibCircleLinkingBackend

/-- The public T-2 through T8 forcing certificate is theorem-backed. -/
theorem complete_forcing_chain_tminus2_to_t8 :
    CompleteForcingChainTMinus2ToT8 where
  tminus2_to_tminus1 := NothingToDistinction.nothingToDistinctionCert
  tminus1_to_t8 := complete_forcing_chain_t8_nonempty
  circle_h1_nonzero := CircleWindingChain.circleH1ZNonzero_unconditional
  circle_h1_iso_int := CircleWindingChain.circleH1ZIsoInt_holds
  mathlib_circle_linking_backend := CircleWindingChain.mathlibCircleLinkingBackend_holds

end TMinus1ToT8Bridge
end Foundation
end IndisputableMonolith
