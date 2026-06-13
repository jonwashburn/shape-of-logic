import IndisputableMonolith.Foundation.AbsoluteFloorClosure
import IndisputableMonolith.Foundation.CostFromDistinction

/-!
# T-1 to T1 Bridge

This public module isolates the first three levels of the forcing chain:

* T-1: the absolute floor of distinguishability.
* T0: the minimal recognition-work cost interface.
* T1: the cost-form Meta-Principle, inconsistent floor states cannot be
  selected at zero cost.

The point is deliberately modest. This file does not import the analytic
`J`-cost surface. It proves the pre-analytic bridge from the absolute floor
to the Boolean recognition-work split.
-/

namespace IndisputableMonolith
namespace Foundation
namespace TMinus1ToT1Bridge

open CostFromDistinction

/-! ## T-1: Absolute floor -/

/-- T-1: the chain starts from the already-closed absolute-floor certificate. -/
structure TMinus1_AbsoluteFloor : Prop where
  closure : AbsoluteFloorClosure.AbsoluteFloorClosureCert

/-- T-1 holds. -/
theorem tminus1_holds : TMinus1_AbsoluteFloor where
  closure := AbsoluteFloorClosure.absoluteFloorClosureCert

/-! ## Boolean recognition-work floor -/

/- The minimal object-level configuration space supplied by the absolute
floor is Boolean: `false` is empty/consistent, `true` is marked
inconsistent. Independent joins are the joins in which two independent
inconsistencies are not double-counted in the same Boolean cell. -/
instance boolConfigSpace : ConfigSpace Bool where
  emp := false
  join := fun a b => a || b
  IsConsistent := fun a => a = false
  Independent := fun a b => a = false ∨ b = false
  emp_consistent := rfl
  independent_symm := by
    intro a b h
    exact h.elim (fun ha => Or.inr ha) (fun hb => Or.inl hb)
  emp_independent := by
    intro a
    exact Or.inl rfl
  join_comm := by
    intro a b
    cases a <;> cases b <;> rfl
  join_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  emp_join := by
    intro a
    cases a <;> rfl
  consistent_of_join_indep := by
    intro a b _hab ha hb
    cases a <;> cases b <;> simp at *
  inconsistent_of_join_indep_left := by
    intro a b _hab ha hjoin
    cases a <;> cases b <;> simp at *

/-- The concrete recognition-work cost on the Boolean floor. -/
def boolRecognitionCost : CostFunction Bool where
  C := fun a => if a = false then 0 else 1
  nonneg := by
    intro a
    cases a <;> norm_num
  dichotomy := by
    intro a
    change (if a = false then 0 else 1) = 0 <-> a = false
    cases a <;> norm_num
  additivity := by
    intro a b hab
    cases a <;> cases b
    · have hjoin : CostFromDistinction.ConfigSpace.join false false = false := rfl
      rw [hjoin]
      norm_num
    · have hjoin : CostFromDistinction.ConfigSpace.join false true = true := rfl
      rw [hjoin]
      norm_num
    · have hjoin : CostFromDistinction.ConfigSpace.join true false = true := rfl
      rw [hjoin]
      norm_num
    · exfalso
      change true = false ∨ true = false at hab
      exact hab.elim (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h)

/-- The Boolean floor carries the recognition-work constraint theorem. -/
theorem bool_recognition_work_constraint :
    Nonempty (CostFunction.RecognitionWorkConstraintCert Bool) :=
  CostFunction.recognition_work_constraint_theorem boolRecognitionCost

/-! ## T0: Logic from recognition work -/

/-- T0: logic is the zero/positive split of recognition work. -/
structure T0_Logic_Forced : Prop where
  recognition_work : Nonempty (CostFunction.RecognitionWorkConstraintCert Bool)
  consistency_zero : boolRecognitionCost.C false = 0
  inconsistency_positive :
    forall a : Bool, Not (ConfigSpace.IsConsistent a) -> 0 < boolRecognitionCost.C a
  zero_cost_consistent :
    forall a : Bool, boolRecognitionCost.C a = 0 -> ConfigSpace.IsConsistent a
  additive_indep :
    forall a b : Bool, ConfigSpace.Independent a b ->
      boolRecognitionCost.C (ConfigSpace.join a b) =
        boolRecognitionCost.C a + boolRecognitionCost.C b

/-- T0 holds on the pre-analytic Boolean recognition-work floor. -/
theorem t0_holds : T0_Logic_Forced where
  recognition_work := bool_recognition_work_constraint
  consistency_zero := rfl
  inconsistency_positive := by
    intro a ha
    exact (CostFunction.cost_pos_iff_inconsistent boolRecognitionCost a).mpr ha
  zero_cost_consistent := by
    intro a hzero
    exact (boolRecognitionCost.dichotomy a).mp hzero
  additive_indep := boolRecognitionCost.additivity

/-! ## Boolean floor interface extracted from T-1 -/

/-- The absolute Boolean floor canonically supports the concrete Boolean
configuration interface used by the public T0 bridge. -/
structure BoolFloorConfigFromWitness
    (floor : AbsoluteFloorClosure.AbsoluteFloorWitness Bool) : Prop where
  floor_nontrivial : ∃ a b : Bool, a ≠ b
  floor_dichotomy : ∀ a : Bool, a = false ∨ a = true
  false_true_distinct : (false : Bool) ≠ true
  emp_is_false : (ConfigSpace.emp : Bool) = false
  join_is_or : ∀ a b : Bool, ConfigSpace.join a b = (a || b)
  consistency_iff_false : ∀ a : Bool, ConfigSpace.IsConsistent a ↔ a = false
  empty_join_left : ∀ a : Bool, ConfigSpace.join false a = a

/-- The Boolean absolute-floor witness supplies the concrete Boolean
configuration interface. -/
theorem bool_floor_config_from_witness
    (floor : AbsoluteFloorClosure.AbsoluteFloorWitness Bool) :
    BoolFloorConfigFromWitness floor where
  floor_nontrivial :=
    AbsoluteFloorClosure.bare_distinguishability_of_absolute_floor floor
  floor_dichotomy := by
    intro a
    cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  false_true_distinct := by
    decide
  emp_is_false := rfl
  join_is_or := by
    intro a b
    rfl
  consistency_iff_false := by
    intro a
    rfl
  empty_join_left := by
    intro a
    cases a <;> rfl

/-- The Boolean recognition-work cost is unit-normalized on the marked
inconsistent state. -/
structure BoolRecognitionCostFromFloor
    (floor : AbsoluteFloorClosure.AbsoluteFloorWitness Bool) : Prop where
  zero_empty : boolRecognitionCost.C false = 0
  unit_marked : boolRecognitionCost.C true = 1
  inconsistent_unit :
    ∀ a : Bool, Not (ConfigSpace.IsConsistent a) -> boolRecognitionCost.C a = 1
  positive_iff_inconsistent :
    ∀ a : Bool, 0 < boolRecognitionCost.C a ↔ Not (ConfigSpace.IsConsistent a)

/-- The Boolean floor supplies the unit-normalized recognition-work cost. -/
theorem bool_recognition_cost_from_floor
    (floor : AbsoluteFloorClosure.AbsoluteFloorWitness Bool) :
    BoolRecognitionCostFromFloor floor where
  zero_empty := rfl
  unit_marked := rfl
  inconsistent_unit := by
    intro a ha
    cases a
    · exfalso
      exact ha rfl
    · rfl
  positive_iff_inconsistent := CostFunction.cost_pos_iff_inconsistent boolRecognitionCost

/-! ## T-1 to T0 bridge -/

/-- T-1 supplies the Boolean absolute floor and therefore the minimal T0
recognition-work interface. -/
structure TMinus1_To_T0_Bridge : Prop where
  bool_floor : AbsoluteFloorClosure.AbsoluteFloorWitness Bool
  floor_config : BoolFloorConfigFromWitness bool_floor
  floor_cost : BoolRecognitionCostFromFloor bool_floor
  recognition_work : Nonempty (CostFunction.RecognitionWorkConstraintCert Bool)
  consistency_zero : boolRecognitionCost.C false = 0
  positive_iff_inconsistent :
    forall a : Bool, 0 < boolRecognitionCost.C a ↔ Not (ConfigSpace.IsConsistent a)
  t0 : T0_Logic_Forced

/-- The absolute floor supplies the minimal T0 cost interface. -/
theorem tminus1_to_t0_bridge
    (floor : TMinus1_AbsoluteFloor) :
    TMinus1_To_T0_Bridge where
  bool_floor := floor.closure.bool_witness
  floor_config := bool_floor_config_from_witness floor.closure.bool_witness
  floor_cost := bool_recognition_cost_from_floor floor.closure.bool_witness
  recognition_work := bool_recognition_work_constraint
  consistency_zero := rfl
  positive_iff_inconsistent := CostFunction.cost_pos_iff_inconsistent boolRecognitionCost
  t0 := t0_holds

/-- The canonical T-1 to T0 bridge. -/
theorem tminus1_to_t0_bridge_holds : TMinus1_To_T0_Bridge where
  bool_floor := AbsoluteFloorClosure.bool_absolute_floor
  floor_config := bool_floor_config_from_witness AbsoluteFloorClosure.bool_absolute_floor
  floor_cost := bool_recognition_cost_from_floor AbsoluteFloorClosure.bool_absolute_floor
  recognition_work := bool_recognition_work_constraint
  consistency_zero := rfl
  positive_iff_inconsistent := CostFunction.cost_pos_iff_inconsistent boolRecognitionCost
  t0 := t0_holds

/-! ## T1: Cost-form Meta-Principle -/

/-- T1: an inconsistent recognition-work state cannot be selected at zero cost. -/
structure T1_MetaPrinciple_Forced : Prop where
  inconsistent_positive :
    forall a : Bool, Not (ConfigSpace.IsConsistent a) -> 0 < boolRecognitionCost.C a
  zero_cost_consistent :
    forall a : Bool, boolRecognitionCost.C a = 0 -> ConfigSpace.IsConsistent a
  marked_inconsistent_positive : 0 < boolRecognitionCost.C true

/-- T1 follows from T0. This proof uses the T0 hypothesis. -/
theorem t1_corollary_of_t0 : T0_Logic_Forced -> T1_MetaPrinciple_Forced :=
  fun h0 => {
    inconsistent_positive := h0.inconsistency_positive
    zero_cost_consistent := h0.zero_cost_consistent
    marked_inconsistent_positive := h0.inconsistency_positive true (by
      intro htrue
      change true = false at htrue
      exact Bool.noConfusion htrue)
  }

/-- T0 supplies the T1 bridge. -/
structure T0_To_T1_Bridge (h0 : T0_Logic_Forced) : Prop where
  t1 : T1_MetaPrinciple_Forced
  t1_eq_corollary : t1 = t1_corollary_of_t0 h0

/-- The T0-to-T1 bridge is theorem-backed. -/
theorem t0_to_t1_bridge_holds (h0 : T0_Logic_Forced) :
    T0_To_T1_Bridge h0 where
  t1 := t1_corollary_of_t0 h0
  t1_eq_corollary := rfl

/-- T1 holds. -/
theorem t1_holds : T1_MetaPrinciple_Forced :=
  (t0_to_t1_bridge_holds t0_holds).t1

/-- Compact public certificate for the first forcing bridge. -/
structure TMinus1ToT1Cert : Prop where
  tminus1 : TMinus1_AbsoluteFloor
  bridge : TMinus1_To_T0_Bridge
  t0 : T0_Logic_Forced
  t0_to_t1 : T0_To_T1_Bridge t0
  t1 : T1_MetaPrinciple_Forced

/-- The public T-1 to T1 certificate is theorem-backed. -/
theorem tminus1_to_t1_cert : TMinus1ToT1Cert :=
  let hm1 := tminus1_holds
  let b01 := tminus1_to_t0_bridge hm1
  let h0 := b01.t0
  let b12 := t0_to_t1_bridge_holds h0
  {
    tminus1 := hm1
    bridge := b01
    t0 := h0
    t0_to_t1 := b12
    t1 := b12.t1
  }

end TMinus1ToT1Bridge
end Foundation
end IndisputableMonolith
