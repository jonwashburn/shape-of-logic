import IndisputableMonolith.Mathematics.HodgeDeltaBridge.GeometricCertificate

/-!
# δ-Hodge Bridge: finite equation-cut certificates

This module pushes the certificate layer one step closer to explicit projective
algebraic geometry.  A projective component is now allowed to be specified by a
finite list of homogeneous equations in the chosen projective embedding display.

The equations are still interface-level expressions; this file does not build a
full polynomial algebraic-geometry API.  The important move is that the
certificate is finite equation data, not a bare cohomology vector and not merely
an already-packaged algebraic-cycle token.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement

universe u

/-- A finite homogeneous equation system in the projective embedding display of
`X`.  The expression type is intentionally abstract: the finite support and the
vanishing predicate are the certificate-relevant data at this layer. -/
structure HomogeneousEquationSystem
    (X : SmoothProjectiveComplexVariety.{u}) where
  equation : Type u
  fintype_equation : Fintype equation
  expression : equation → Type u
  vanishesOn : X.carrier → Prop
  certified_vanishing : Prop
  certified_vanishing_holds : certified_vanishing

instance
    {X : SmoothProjectiveComplexVariety.{u}}
    (E : HomogeneousEquationSystem X) : Fintype E.equation :=
  E.fintype_equation

/-- A projective algebraic subvariety component cut out by a finite homogeneous
equation system, with codimension/irreducibility/(p,p) witnesses. -/
structure EquationCutSubvarietyData
    (X : SmoothProjectiveComplexVariety.{u})
    (p : ℕ) where
  equations : HomogeneousEquationSystem X
  carrier : Type u
  carrier_nonempty : Nonempty carrier
  embedding : carrier → X.carrier
  satisfies_equations : ∀ y : carrier, equations.vanishesOn (embedding y)
  codimension : ℕ
  codimension_eq : codimension = p
  irreducible : Prop
  irreducible_holds : irreducible
  type_pp : Prop
  type_pp_holds : type_pp

instance
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (V : EquationCutSubvarietyData X p) : Nonempty V.carrier :=
  V.carrier_nonempty

namespace EquationCutSubvarietyData

/-- Forget finite equation-cut data to projective algebraic subvariety data. -/
def toProjectiveData
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (V : EquationCutSubvarietyData X p) :
    ProjectiveAlgebraicSubvarietyData X p where
  carrier := V.carrier
  carrier_nonempty := V.carrier_nonempty
  embedding := V.embedding
  codimension := V.codimension
  codimension_eq := V.codimension_eq
  irreducible := V.irreducible
  irreducible_holds := V.irreducible_holds
  type_pp := V.type_pp
  type_pp_holds := V.type_pp_holds

end EquationCutSubvarietyData

/-- A finite equation-cut certificate: finitely many components, each specified
by finite homogeneous equations, with rational coefficients. -/
structure EquationFiniteCertificate
    (X : SmoothProjectiveComplexVariety.{u})
    (p : ℕ) where
  component : Type u
  fintype_component : Fintype component
  subvariety : component → EquationCutSubvarietyData X p
  coefficient : component → ℚ

instance
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (E : EquationFiniteCertificate X p) : Fintype E.component :=
  E.fintype_component

namespace EquationFiniteCertificate

/-- Forget finite equation-cut certificate data to finite geometric certificate
data. -/
def toGeometricCertificate
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (E : EquationFiniteCertificate X p) :
    GeometricFiniteCertificate X p where
  component := E.component
  fintype_component := E.fintype_component
  subvariety := fun i => (E.subvariety i).toProjectiveData
  coefficient := E.coefficient

/-- Equation certificates produce finite algebraic distinction certificates by
forgetting equations to projective component data and then to algebraic cycles. -/
def toFiniteCertificate
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (E : EquationFiniteCertificate X p) :
    FiniteAlgebraicDistinctionCertificate X p :=
  E.toGeometricCertificate.toFiniteCertificate

/-- Equation-cut certificate headline: finite homogeneous equation data yields a
finite algebraic distinction certificate. -/
theorem equation_certificate_yields_finite_certificate
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (E : EquationFiniteCertificate X p) :
    Nonempty (FiniteAlgebraicDistinctionCertificate X p) :=
  ⟨E.toFiniteCertificate⟩

/-- Equation-cut certificate also yields a geometric finite certificate. -/
theorem equation_certificate_yields_geometric_certificate
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (E : EquationFiniteCertificate X p) :
    Nonempty (GeometricFiniteCertificate X p) :=
  ⟨E.toGeometricCertificate⟩

end EquationFiniteCertificate

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

