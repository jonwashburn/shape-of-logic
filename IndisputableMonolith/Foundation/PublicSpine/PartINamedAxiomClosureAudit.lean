import IndisputableMonolith.Foundation.PublicSpine.PartINamedAxiomClosure

/-!
# PartINamedAxiomClosureAudit

Kernel-facing dependency receipt for the four Part I physical identifications.

Until 2026-07-25 these were four global `axiom` declarations, and this file
existed to confirm that each closure theorem exposed its own named axiom while
the four model-nonemptiness theorems stayed clean. The axioms are gone: each law
is now an explicit argument, so every declaration below should audit to the base
triple `{propext, Classical.choice, Quot.sound}` and nothing else. The audit
therefore inverts. It used to check that the axioms showed up where expected; it
now checks that no named axiom shows up anywhere, which is the stronger and
simpler property.

Read the printed footprints, not the fact that the file compiles. A
`#print axioms` command succeeds whatever it prints, so this file is a report
and not a gate. `scripts/reality_audit.py` is the counting gate.

Caveat that governs how to read the base triple, per `institute-identity.mdc`:
auditing to `{propext, Classical.choice, Quot.sound}` is a statement about which
postulates are used, never a statement about prior structure. Lean does not
report the universe hierarchy, inductive type formation, constructors and
recursors, function and dependent types, definitional equality, transport, or
decidability instances, and the laws below are structures built out of exactly
those. A clean footprint here means the four physical identifications cost no
postulate, not that they came from nothing.
-/

open IndisputableMonolith.Foundation.PublicSpine.PartINamedAxiomClosure

/-! ## The law types are inhabited, so no axiom was ever needed to obtain one. -/

#print axioms calibrationLaw_nonempty
#print axioms adjacencyLaw_nonempty
#print axioms seedOrbitPhysicalClassLaw_nonempty
#print axioms semanticClockLaw_nonempty

/-! ## Closure theorems: each is now universally quantified over its law. -/

#print axioms calibrationLaw_gauge_eq_one
#print axioms physicalCost_eq_Jcost
#print axioms calibrationLaw_rejects_chart_countermodels
#print axioms physicalScale_eq_phi
#print axioms plasticCountermodel_ne_physical
#print axioms seedOrbitLaw_forces_seed_compose
#print axioms seedOrbitLaw_support_exact
#print axioms seedOrbitLaw_forces_additive_levels
#print axioms seedOrbitLaw_nonvacuous_generated_family
#print axioms seedOrbitLaw_rejects_compiled_nonjoin
#print axioms recognitionCompletePass_period_bound
#print axioms recognitionCompletePass_rejects_six
#print axioms recognitionCompletePass_strictly_narrower_than_surjective

/-! ## The Part I certificate, which is what the public spine re-exports. -/

#print axioms partINamedAxiomClosureCert_holds
