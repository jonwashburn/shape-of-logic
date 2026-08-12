import IndisputableMonolith.Gravity.SevenGaps.HKTCanonicalMomRigidity

open IndisputableMonolith.Gravity.SevenGaps.HKTCanonicalMomRigidity
open IndisputableMonolith.Gravity.SevenGaps.HKTCanonicalMomTarget
open IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

#check profiled_ham_ham_alternating_FE
#check fe_at_r_zero
#check fe_at_p_zero
#check HpLinearInP
#check HbPIndependent
#check LocalHamSmoothContDiff2Obligation
#check hb_coupling_of_linear_ansatz
#check SolveProfileFEQuadratic
#check solve_profile_FE_quadratic
#check hamDyn_solve_profile_FE_quadratic
#check canonicalMom_rigidity_of_FE_solution
#check HKTRigidityStatementPointSplitDynN2Canonical_of_solve
#check hamDyn_canonicalMom_rigidity_conclusion
#check hktCanonicalMomRigidityC1Status_flags

#print axioms profiled_ham_ham_alternating_FE
#print axioms fe_at_r_zero
#print axioms hb_coupling_of_linear_ansatz
#print axioms canonicalMom_rigidity_of_FE_solution
#print axioms HKTRigidityStatementPointSplitDynN2Canonical_of_solve
#print axioms hamDyn_solve_profile_FE_quadratic
#print axioms hamDyn_canonicalMom_rigidity_conclusion
#print axioms hktCanonicalMomRigidityC1Status_flags

example : fullTheoryBenchmarks.gap5_constraint_recovery = true := rfl
example : hktCanonicalMomRigidityC1Status.feExtractionClosed = true := rfl
example : hktCanonicalMomRigidityC1Status.pdeLemmaClosed = false := rfl
example : hktCanonicalMomRigidityC1Status.gap5ConstraintRecovery = false := rfl

-- Rigidity statement remains a Prop (not claimed as a theorem this session).
#check HKTRigidityStatementPointSplitDynN2Canonical
