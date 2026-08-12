import IndisputableMonolith.Gravity.SevenGaps.HKTKineticFromRecognitionCost

/-!
# Axiom audit: constraint-sector recognition premise

Every declaration cited in the paper
`papers/QG_Constraint_Sector_Recognition_Premise_20260725.tex` must print
within `[propext, Classical.choice, Quot.sound]`.

The retained-failure declarations of §7 are audited too. They are cited in the
paper as proved defects, so their axiom cleanliness is load-bearing in exactly
the same way as the positive results.
-/

open IndisputableMonolith.Gravity.SevenGaps
open IndisputableMonolith.Gravity.SevenGaps.HKTKineticFromRecognitionCost

/-! ## §2 and §3: half the premise was never an assumption -/

#check kinetic_normalization_of_universal_response
#check kinetic_coefficient_unique
#check HKTRigidityUniversalKineticN2_holds
#check universal_of_channelSeparated
#check channelSeparated_of_universal

#print axioms kinetic_normalization_of_universal_response
#print axioms kinetic_coefficient_unique
#print axioms HKTRigidityUniversalKineticN2_holds
#print axioms universal_of_channelSeparated
#print axioms channelSeparated_of_universal

/-! ## §4: scope of the linear-chart exclusion -/

#check costKinetic_hp_eq_sinh
#check sinh_not_linear
#check no_exact_cost_kinetic_canonicalMom

#print axioms costKinetic_hp_eq_sinh
#print axioms sinh_not_linear
#print axioms no_exact_cost_kinetic_canonicalMom

/-! ## §6: the enlarged class is not empty -/

#check vacuumKinetic_not_universalKinetic
#check hamDyn_satisfies_universalKinetic

#print axioms vacuumKinetic_not_universalKinetic
#print axioms hamDyn_satisfies_universalKinetic

/-! ## §7: the retained failure, with its defects -/

#check isCalibrated_jetCost_iff
#check jetCost_not_rcl

#print axioms isCalibrated_jetCost_iff
#print axioms jetCost_not_rcl

/-! ## §8: the composition law carries the premise -/

#check compositionLaw_forces_unit_weight
#check rcl_forces_field_independent_weight
#check Jlog_two_arsinh
#check exactCostKineticProfile_quadratic
#check rclKinetic_hp_eq_linear
#check rclKinetic_cKin_pos
#check rclKinetic_cKin_ne_zero
#check rclKinetic_ADM_rigidity
#check rclKinetic_positive_kinetic_coefficient
#check hamDyn_satisfies_rclKinetic
#check vacuumKineticLocalProfile_eq_exactCost
#check vacuumKinetic_weight_not_rcl
#check no_rcl_presentation_of_vacuumKinetic

#print axioms compositionLaw_forces_unit_weight
#print axioms rcl_forces_field_independent_weight
#print axioms Jlog_two_arsinh
#print axioms exactCostKineticProfile_quadratic
#print axioms rclKinetic_hp_eq_linear
#print axioms rclKinetic_cKin_pos
#print axioms rclKinetic_cKin_ne_zero
#print axioms rclKinetic_ADM_rigidity
#print axioms rclKinetic_positive_kinetic_coefficient
#print axioms hamDyn_satisfies_rclKinetic
#print axioms vacuumKineticLocalProfile_eq_exactCost
#print axioms vacuumKinetic_weight_not_rcl
#print axioms no_rcl_presentation_of_vacuumKinetic
