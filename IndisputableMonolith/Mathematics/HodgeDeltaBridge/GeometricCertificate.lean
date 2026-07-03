import IndisputableMonolith.Mathematics.HodgeDeltaBridge.DisplayMap

/-!
# δ-Hodge Bridge: geometric finite certificates

The first certificate layer wrapped an existing `AlgebraicCycle`.  This module
pushes one step closer to geometry: a certificate is finite projective
subvariety component data (with rational coefficients) from which the
`AlgebraicCycle` is constructed.

This still does not prove that every rational Hodge class has such data.  It
does remove one layer of abstraction from the remaining selector target.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement

universe u

/-- Projective algebraic subvariety component data inside a smooth projective
variety `X`, with codimension `p`.  The fields are still interface-level, but
they are geometric fields, not a cohomology carrier masquerading as a cycle. -/
structure ProjectiveAlgebraicSubvarietyData
    (X : SmoothProjectiveComplexVariety.{u})
    (p : ℕ) where
  carrier : Type u
  carrier_nonempty : Nonempty carrier
  embedding : carrier → X.carrier
  codimension : ℕ
  codimension_eq : codimension = p
  irreducible : Prop
  irreducible_holds : irreducible
  type_pp : Prop
  type_pp_holds : type_pp

instance
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (V : ProjectiveAlgebraicSubvarietyData X p) : Nonempty V.carrier :=
  V.carrier_nonempty

/-- A finite geometric Hodge certificate: finitely many projective algebraic
subvariety components with rational coefficients. -/
structure GeometricFiniteCertificate
    (X : SmoothProjectiveComplexVariety.{u})
    (p : ℕ) where
  component : Type u
  fintype_component : Fintype component
  subvariety : component → ProjectiveAlgebraicSubvarietyData X p
  coefficient : component → ℚ

instance
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (G : GeometricFiniteCertificate X p) : Fintype G.component :=
  G.fintype_component

namespace GeometricFiniteCertificate

/-- Turn finite geometric component data into the classical algebraic cycle
interface. -/
def toAlgebraicCycle
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (G : GeometricFiniteCertificate X p) :
    AlgebraicCycle.{u, u} X p :=
  { support := Σ i : G.component, (G.subvariety i).carrier
    irreducibleComponent := G.component
    fintype_components := G.fintype_component
    componentMap := fun i => ⟨i, Classical.choice (G.subvariety i).carrier_nonempty⟩
    coefficient := G.coefficient
    embedding_in_carrier := fun s => (G.subvariety s.1).embedding s.2
    codimension := fun i => (G.subvariety i).codimension
    codimension_eq := fun i => (G.subvariety i).codimension_eq
    component_irreducible := fun i => (G.subvariety i).irreducible
    component_irreducible_holds := fun i => (G.subvariety i).irreducible_holds }

/-- Finite support coding for the algebraic cycle constructed from geometric
component data. -/
def finiteSupport
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (G : GeometricFiniteCertificate X p) :
    FiniteAlgebraicSupport G.toAlgebraicCycle where
  index := G.component
  fintype_index := G.fintype_component
  encode := id
  covers := fun i => ⟨i, rfl⟩

/-- The `(p,p)` display witness supplied by the geometric components. -/
def typePPWitness
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (G : GeometricFiniteCertificate X p) :
    TypePPDisplayWitness G.toAlgebraicCycle where
  displayTag := G.component
  finite_tag := G.fintype_component
  component_type_pp := fun i => (G.subvariety i).type_pp
  component_type_pp_holds := fun i => (G.subvariety i).type_pp_holds

/-- A geometric finite certificate canonically produces a finite algebraic
distinction certificate. -/
def toFiniteCertificate
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (G : GeometricFiniteCertificate X p) :
    FiniteAlgebraicDistinctionCertificate X p where
  cycle := G.toAlgebraicCycle
  finiteSupport := G.finiteSupport
  typePP := G.typePPWitness

/-- The finite certificate extracted from a geometric certificate carries the
same algebraic cycle constructed from the component data. -/
theorem toFiniteCertificate_cycle
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (G : GeometricFiniteCertificate X p) :
    G.toFiniteCertificate.toAlgebraicCycle = G.toAlgebraicCycle :=
  rfl

/-- Geometric certificate headline: finite projective subvariety data yields an
actual finite algebraic distinction certificate. -/
theorem geometric_certificate_yields_finite_certificate
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (G : GeometricFiniteCertificate X p) :
    Nonempty (FiniteAlgebraicDistinctionCertificate X p) :=
  ⟨G.toFiniteCertificate⟩

end GeometricFiniteCertificate

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

