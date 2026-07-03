import IndisputableMonolith.Mathematics.HodgeDeltaBridge.GeometricCertificate
import IndisputableMonolith.Mathematics.HodgeDeltaBridge.UniversalityCriterion

/-!
# δ-Hodge Bridge: geometric selector criterion

This module sharpens the remaining target again.  A global finite-certificate
selector is enough for final closure; a global geometric-certificate selector is
a stronger, more referee-grade way to produce it.

The remaining problem is now explicit:

construct `GlobalGeometricCertificateSelector` from algebraic geometry.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement

universe u

/-- A geometric selector for one fixed canonical cycle-class map.  It assigns
finite projective algebraic subvariety data to every compatible rational Hodge
class and proves that the resulting finite certificate displays the class. -/
structure GeometricCertificateSelector
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p) where
  select :
    ∀ (α : RationalHodgeClass.{u, u} X p)
      (_hcompat : α.cohomologyClass = cl.targetCohomology),
      GeometricFiniteCertificate X p
  displays :
    ∀ (α : RationalHodgeClass.{u, u} X p)
      (hcompat : α.cohomologyClass = cl.targetCohomology),
      CertificateDisplaysClass cl ((select α hcompat).toFiniteCertificate) α

/-- A geometric selector yields the finite-certificate selector required by the
previous bridge layer. -/
def finiteSelectorOfGeometric
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {cl : CanonicalCycleClassMap.{u} X p}
    (S : GeometricCertificateSelector cl) :
    FiniteCertificateSelector cl where
  select := fun α hcompat => (S.select α hcompat).toFiniteCertificate
  displays := S.displays

/-- Geometric selector form of the fixed-map Hodge theorem. -/
theorem hodge_for_fixed_map_from_geometric_selector
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (S : GeometricCertificateSelector cl) :
    ∀ (α : RationalHodgeClass.{u, u} X p)
      (_hcompat : α.cohomologyClass = cl.targetCohomology),
      ∃ Z : AlgebraicCycle.{u, u} X p, Nonempty (CycleClassEquals cl Z α) :=
  hodge_for_fixed_map_from_selector cl (finiteSelectorOfGeometric S)

/-- Global geometric selector data: every `(X,p)` has a fixed canonical
cycle-class map and a geometric selector for it. -/
structure GlobalGeometricCertificateSelector where
  cl :
    ∀ (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ),
      CanonicalCycleClassMap.{u} X p
  selector :
    ∀ (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ),
      GeometricCertificateSelector (cl X p)

/-- A global geometric selector yields a global finite selector. -/
def globalFiniteSelectorOfGeometric
    (G : GlobalGeometricCertificateSelector.{u}) :
    GlobalFiniteCertificateSelector.{u} where
  cl := G.cl
  selector := fun X p => finiteSelectorOfGeometric (G.selector X p)

/-- A global geometric certificate selector proves the final Hodge target through
the δ-Hodge bridge. -/
theorem hodge_conjecture_from_global_geometric_certificate_selector
    (G : GlobalGeometricCertificateSelector.{u}) :
    hodge_conjecture_unconditional_referee_grade.{u} :=
  hodge_conjecture_from_global_finite_certificate_selector
    (globalFiniteSelectorOfGeometric G)

/-- The strongest current constructive criterion: construct a global geometric
certificate selector and the final Hodge theorem follows. -/
theorem global_geometric_selector_is_sufficient_for_final_goal :
    Nonempty (GlobalGeometricCertificateSelector.{u}) →
      hodge_conjecture_unconditional_referee_grade.{u} := by
  intro h
  rcases h with ⟨G⟩
  exact hodge_conjecture_from_global_geometric_certificate_selector G

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

