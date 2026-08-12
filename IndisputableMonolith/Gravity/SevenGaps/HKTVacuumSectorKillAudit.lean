import IndisputableMonolith.Gravity.SevenGaps.HKTVacuumSectorKill

open IndisputableMonolith.Gravity.SevenGaps.HKTVacuumSectorKill
open IndisputableMonolith.Gravity.SevenGaps.HKTCanonicalMomTarget
open IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

#check vacuumShiftCanonicalMomTarget
#check not_HKTRigidityStatementPointSplitDynN2Canonical
#check HKTRigidityModVacuumStatementN2
#check vacuumShift_satisfies_modVacuum
#check hamDyn_satisfies_modVacuum
#check Note_modVacuumKilledInC4
#check hktVacuumSectorKillStatus_flags

#print axioms not_HKTRigidityStatementPointSplitDynN2Canonical
#print axioms vacuumShift_satisfies_modVacuum
#print axioms hamDyn_satisfies_modVacuum
#print axioms hktVacuumSectorKillStatus_flags

example : fullTheoryBenchmarks.gap5_constraint_recovery = true := rfl
example : hktVacuumSectorKillStatus.canonicalMomRigidityKilled = true := rfl
example : hktVacuumSectorKillStatus.modVacuumRigidityOpen = false := rfl
example : hktVacuumSectorKillStatus.gap5ConstraintRecovery = false := rfl

-- Mod-vacuum statement remains DEFINED here; C4 kills it in
-- `HKTKineticNormalizedRigidity`.
#check HKTRigidityModVacuumStatementN2
#check HKTRigidityStatementPointSplitDynN2Canonical
