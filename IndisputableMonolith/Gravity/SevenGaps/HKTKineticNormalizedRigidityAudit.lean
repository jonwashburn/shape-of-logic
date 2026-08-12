import IndisputableMonolith.Gravity.SevenGaps.HKTKineticNormalizedRigidity

open IndisputableMonolith.Gravity.SevenGaps.HKTKineticNormalizedRigidity
open IndisputableMonolith.Gravity.SevenGaps.HKTVacuumSectorKill
open IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

#check vacuumKineticCanonicalMomTarget
#check not_HKTRigidityModVacuumStatementN2
#check KineticNormalizedCanonicalMom
#check ftc_recovery_of_normalized
#check HKTRigidityKineticNormalizedN2_holds
#check hamDynKineticNormalized
#check hamDyn_satisfies_kineticNormalized
#check vacuumKinetic_not_kineticNormalized
#check hktKineticNormalizedRigidityStatus_flags

#print axioms not_HKTRigidityModVacuumStatementN2
#print axioms ftc_recovery_of_normalized
#print axioms HKTRigidityKineticNormalizedN2_holds
#print axioms hamDyn_satisfies_kineticNormalized
#print axioms vacuumKinetic_not_kineticNormalized
#print axioms kinetic_split_of_intensivity
#print axioms gradient_recovery_of_intensivity

example : fullTheoryBenchmarks.gap5_constraint_recovery = true := rfl
example : hktKineticNormalizedRigidityStatus.modVacuumRigidityKilled = true := rfl
example : hktKineticNormalizedRigidityStatus.kineticNormalizedRigidityClosed = true := rfl
example : hktKineticNormalizedRigidityStatus.ftcRecoveryDerived = true := rfl
example : hktVacuumSectorKillStatus.modVacuumRigidityOpen = false := rfl
