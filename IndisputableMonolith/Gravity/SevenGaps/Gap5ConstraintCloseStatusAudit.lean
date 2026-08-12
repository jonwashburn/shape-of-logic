import IndisputableMonolith.Gravity.SevenGaps.Gap5ConstraintCloseStatus

/-!
# Axiom audit: Wave C5 Gap5ConstraintCloseStatus

Headline theorems must print within
`[propext, Classical.choice, Quot.sound]`.
Zero `sorryAx`.
-/

open IndisputableMonolith.Gravity.SevenGaps.Gap5ConstraintCloseStatus
open IndisputableMonolith.Gravity.SevenGaps.HKTKineticNormalizedRigidity
open IndisputableMonolith.Gravity.SevenGaps.HKTVacuumSectorKill
open IndisputableMonolith.Gravity.SevenGaps.HKTCanonicalMomTarget
open IndisputableMonolith.Gravity.SevenGaps.HKTOneSiteCounterexample
open IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger
open IndisputableMonolith.Gravity.SevenGaps.CampaignLedger
open IndisputableMonolith.Gravity.SevenGaps.Gap5ConstraintResidualDAG

#check hojman_pins_general_relativity_holds
#check gap5_constraint_recovery_both_halves
#check gap5_constraint_recovery_bound_to_terminals
#check gap5_kill_tower_scope_certificate
#check gap5ConstraintCloseStatus_flags
#check ftc_recovery_of_normalized

#print axioms hojman_pins_general_relativity_holds
#print axioms gap5_constraint_recovery_both_halves
#print axioms gap5_constraint_recovery_bound_to_terminals
#print axioms gap5_kill_tower_scope_certificate
#print axioms ftc_recovery_of_normalized
#print axioms not_HKTRigidityStatement_one
#print axioms not_HKTRigidityStatementPointSplitDynN2Strong
#print axioms not_HKTRigidityStatementPointSplitDynN2Canonical
#print axioms not_HKTRigidityModVacuumStatementN2

example : fullTheoryBenchmarks.gap5_constraint_recovery = true := rfl
example : sevenGapsCampaignStatus.gap5_continuum_algebra_hkt_open = false := rfl
example : gap5ResidualDAGStatus.hktRigidityOpen = false := rfl
example : gap5ResidualDAGStatus.packagedTargetOpen = false := rfl
example : gap5ResidualDAGStatus.gap5ConstraintRecovery = true := rfl
