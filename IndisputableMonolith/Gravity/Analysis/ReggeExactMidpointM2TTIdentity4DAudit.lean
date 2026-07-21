import IndisputableMonolith.Gravity.Analysis.ReggeExactMidpointM2TTIdentity4D

open IndisputableMonolith.Gravity.Analysis.ReggeExactMidpointM2TTIdentity4D
open IndisputableMonolith.Gravity.Analysis.ReggeExactMidpointM2TTIdentity4D.KernelCert

/-!
Audit for typed blocker `exact_midpoint_m2_tt_identity` (kernel upgrade).

Expected axiom set for the main identity and table certificates:
`[propext, Classical.choice, Quot.sound]` — no `Lean.ofReduceBool` /
`Lean.trustCompiler`.
-/

#print axioms m2Coeff_eq_explicitM2Coeff
#print axioms symFull_explicit_eq_symFull_closed
#print axioms exactMidpointBlochM2_eq_biquad
#print axioms biquad_symFull
#print axioms biquad_closedCoeff_eq_closedForm
#print axioms exactMidpointBlochM2_eq_closedForm_of_symmetric
#print axioms exactMidpointBlochM2_eq_neg_eighth_frobenius_tt

theorem m2_tt_identity_audit_package :
    ExactMidpointM2TTIdentityProved = true :=
  exactMidpointM2TTIdentityProved_true

#print axioms m2_tt_identity_audit_package
