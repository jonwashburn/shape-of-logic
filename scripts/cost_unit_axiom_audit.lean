/-
Kernel audit for the cost-unit slice, run against the public tree.

The two papers claim that the classification of the anchor-free cost ledger and the
leastness of `J` over it carry no project-local axioms, and that the six exponentials
theorem enters as an explicit hypothesis rather than as an axiom. `#print axioms` is
the check: each declaration below must report only `propext`, `Classical.choice` and
`Quot.sound`, the three axioms of the ambient proof assistant. A named hypothesis is
invisible to this command by construction, which is the point of stating it in the type.

Run: `lake env lean scripts/cost_unit_axiom_audit.lean`
-/
import IndisputableMonolith.Cost.GaugeOrbitClassification
import IndisputableMonolith.Cost.UnitFromMinimality
import IndisputableMonolith.Cost.MonotoneMultiplicativePower
import IndisputableMonolith.Cost.FunctionalEquation

#print axioms IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCost.GaugeOrbitIsSignedPowerFamily_of_sixExponentials
#print axioms IndisputableMonolith.Cost.MonotonePower.exists_exponent

-- The nondegeneracy dichotomy. None of these takes the six exponentials hypothesis, so a
-- clean report here is the whole claim: the condition that separates the degenerate solution
-- from every other one is decided inside the kernel from the ledger alone.
#print axioms IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCost.vanishes_at_two_iff_trace_two
#print axioms IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCost.vanishes_at_two_iff_flat
#print axioms IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCost.charges_positively_at_two
#print axioms IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCost.strict_somewhere_iff_charges_at_two
#print axioms IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCost.charges_at_two_iff_not_signGauge
#print axioms IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCost.signGauge_sees_orientation_only

#print axioms IndisputableMonolith.Cost.UnitFromMinimality.jcost_lt_pow
#print axioms IndisputableMonolith.Cost.UnitFromMinimality.anchor_is_minimality_over_powers
#print axioms IndisputableMonolith.Cost.FunctionalEquation.law_of_logic_forces_jcost
#print axioms IndisputableMonolith.Cost.FunctionalEquation.hasLogCurvature_full_filter_forces_zero
