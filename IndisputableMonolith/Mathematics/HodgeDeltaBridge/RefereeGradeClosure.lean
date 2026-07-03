import IndisputableMonolith.Mathematics.HodgeDeltaBridge.ImageEquivalence

/-!
# δ-Hodge Bridge: referee-grade closure surface

This file states the exact remaining theorem needed for a classical
referee-grade Hodge proof via the δ-Hodge bridge.

It proves:

* if every `(X,p)` admits a fixed canonical cycle-class map whose compatible
  rational Hodge classes are all certificate-displayed, then the classical
  `RationalHodgeConjectureStatement` follows;
* for any fixed `(X,p,cl)`, the δ-admissible version already gives algebraic
  cycles with no toy `cycle := cl.targetCohomology.carrier` bridge.

It does **not** assert the remaining universality condition.  That condition is
the real target of the next sessions.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement

universe u

/-- The exact δ-Hodge universality condition needed to obtain the classical
rational Hodge conjecture: every smooth projective `X` and codimension `p` has a
fixed cycle-class map whose compatible rational Hodge classes are all displayed
by finite algebraic distinction certificates. -/
def DeltaHodgeUniversality : Prop :=
  ∀ (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ),
    ∃ cl : CanonicalCycleClassMap.{u} X p, ConservativeHodgeCompletion cl

/-- Fixed-map δ-admissible Hodge theorem: for a fixed map, every admissible
class has an algebraic cycle representative. -/
theorem rational_hodge_for_delta_admissible_classes
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p) :
    ∀ (α : RationalHodgeClass.{u, u} X p),
      AdmissibleRationalHodgeClass cl α →
        ∃ Z : AlgebraicCycle.{u, u} X p, Nonempty (CycleClassEquals cl Z α) :=
  fun α hα => hodge_class_has_algebraic_cycle_of_admissible cl α hα

/-- The classical rational Hodge statement follows from δ-Hodge universality.
This is the correct closure theorem shape: it exposes the one remaining bridge
condition rather than hiding it in a toy cycle interface. -/
theorem rational_hodge_from_delta_hodge_universality
    (hδ : DeltaHodgeUniversality.{u}) :
    RationalHodgeConjectureStatement.{u} := by
  intro X p
  rcases hδ X p with ⟨cl, hC⟩
  refine ⟨cl, ?_⟩
  intro α hcompat
  exact hodge_class_has_algebraic_cycle_of_conservative_completion cl hC α hcompat

/-- Name reserved for the final target.  This proposition is deliberately the
classical Hodge statement, not the weaker δ-admissible version. -/
def hodge_conjecture_unconditional_referee_grade : Prop :=
  RationalHodgeConjectureStatement.{u}

/-- Current bridge headline: the final target is reduced to δ-Hodge
universality, with finite certificates supplying every compatible display class.
The proof of universality is the remaining work. -/
theorem referee_grade_hodge_reduced_to_delta_universality :
    DeltaHodgeUniversality.{u} → hodge_conjecture_unconditional_referee_grade.{u} :=
  rational_hodge_from_delta_hodge_universality

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

