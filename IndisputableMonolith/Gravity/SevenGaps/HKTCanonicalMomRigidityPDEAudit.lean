import IndisputableMonolith.Gravity.SevenGaps.HKTCanonicalMomRigidityPDE

open IndisputableMonolith.Gravity.SevenGaps.HKTCanonicalMomRigidity
open IndisputableMonolith.Gravity.SevenGaps.HKTCanonicalMomTarget
open IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

#check LocalHamSmoothContDiff2Obligation
#check sqrtAffineProfile_contDiff2
#check not_forced_linear_hp_of_contDiff2_FE
#check not_forced_hb_p_independent_of_contDiff2_FE
#check ConstantKineticSlope
#check hb_shape_of_constant_kinetic_slope
#check ADM_quadratic_of_gauges
#check HKTRigidityPointSplitDynN2Canonical_smooth
#check hamDynLocalProfile_contDiff2
#check hamDyn_smooth_scoped_rigidity
#check SolveProfileFEQuadratic_of_smoothScopedData
#check hktCanonicalMomRigidityC2Status_flags

#print axioms sqrtAffineProfile_contDiff2
#print axioms not_forced_linear_hp_of_contDiff2_FE
#print axioms HKTRigidityPointSplitDynN2Canonical_smooth
#print axioms hamDyn_smooth_scoped_rigidity
#print axioms SolveProfileFEQuadratic_of_smoothScopedData
#print axioms hktCanonicalMomRigidityC2Status_flags

example : fullTheoryBenchmarks.gap5_constraint_recovery = true := rfl
example : hktCanonicalMomRigidityC2Status.pdeLemmaClosed = false := rfl
example : hktCanonicalMomRigidityC2Status.smoothScopedRigidityClosed = true := rfl
example : hktCanonicalMomRigidityC2Status.gap5ConstraintRecovery = false := rfl

-- Unconditioned rigidity remains a Prop (not claimed as a universal theorem).
#check HKTRigidityStatementPointSplitDynN2Canonical
#check solve_profile_FE_quadratic
