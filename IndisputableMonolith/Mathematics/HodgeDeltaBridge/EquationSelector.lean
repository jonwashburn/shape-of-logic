import IndisputableMonolith.Mathematics.HodgeDeltaBridge.EquationCertificate
import IndisputableMonolith.Mathematics.HodgeDeltaBridge.GeometricSelector

/-!
# δ-Hodge Bridge: equation selector criterion

The previous layer reduced final closure to a global geometric selector.  This
module strengthens that: a global selector whose components are finite
homogeneous equation-cut data is sufficient.

This is now a concrete algebraic-geometry construction target:

construct `GlobalEquationCertificateSelector`.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement

universe u

/-- An equation selector for one fixed canonical cycle-class map.  It assigns
finite homogeneous equation-cut component data to every compatible rational
Hodge class and proves that the resulting certificate displays that class. -/
structure EquationCertificateSelector
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p) where
  select :
    ∀ (α : RationalHodgeClass.{u, u} X p)
      (_hcompat : α.cohomologyClass = cl.targetCohomology),
      EquationFiniteCertificate X p
  displays :
    ∀ (α : RationalHodgeClass.{u, u} X p)
      (hcompat : α.cohomologyClass = cl.targetCohomology),
      CertificateDisplaysClass cl ((select α hcompat).toFiniteCertificate) α

/-- An equation selector yields a geometric selector by forgetting equation-cut
data to projective subvariety data. -/
def geometricSelectorOfEquation
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {cl : CanonicalCycleClassMap.{u} X p}
    (S : EquationCertificateSelector cl) :
    GeometricCertificateSelector cl where
  select := fun α hcompat => (S.select α hcompat).toGeometricCertificate
  displays := S.displays

/-- Fixed-map Hodge theorem from an equation-cut selector. -/
theorem hodge_for_fixed_map_from_equation_selector
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (S : EquationCertificateSelector cl) :
    ∀ (α : RationalHodgeClass.{u, u} X p)
      (_hcompat : α.cohomologyClass = cl.targetCohomology),
      ∃ Z : AlgebraicCycle.{u, u} X p, Nonempty (CycleClassEquals cl Z α) :=
  hodge_for_fixed_map_from_geometric_selector cl (geometricSelectorOfEquation S)

/-- Global equation selector data: every `(X,p)` has a fixed canonical
cycle-class map and an equation-cut selector for it. -/
structure GlobalEquationCertificateSelector where
  cl :
    ∀ (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ),
      CanonicalCycleClassMap.{u} X p
  selector :
    ∀ (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ),
      EquationCertificateSelector (cl X p)

/-- Global equation selectors yield global geometric selectors. -/
def globalGeometricSelectorOfEquation
    (G : GlobalEquationCertificateSelector.{u}) :
    GlobalGeometricCertificateSelector.{u} where
  cl := G.cl
  selector := fun X p => geometricSelectorOfEquation (G.selector X p)

/-- A global equation-cut selector proves the final Hodge target through the
δ-Hodge bridge. -/
theorem hodge_conjecture_from_global_equation_certificate_selector
    (G : GlobalEquationCertificateSelector.{u}) :
    hodge_conjecture_unconditional_referee_grade.{u} :=
  hodge_conjecture_from_global_geometric_certificate_selector
    (globalGeometricSelectorOfEquation G)

/-- Current strongest constructive criterion: construct finite homogeneous
equation-cut certificates for all rational Hodge classes and Hodge follows. -/
theorem global_equation_selector_is_sufficient_for_final_goal :
    Nonempty (GlobalEquationCertificateSelector.{u}) →
      hodge_conjecture_unconditional_referee_grade.{u} := by
  intro h
  rcases h with ⟨G⟩
  exact hodge_conjecture_from_global_equation_certificate_selector G

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

