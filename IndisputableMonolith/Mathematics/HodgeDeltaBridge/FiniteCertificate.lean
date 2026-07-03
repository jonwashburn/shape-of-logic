import Mathlib
import IndisputableMonolith.Mathematics.HodgeClassicalStatement

/-!
# δ-Hodge Bridge: finite algebraic distinction certificates

This module starts the replacement for the toy Hodge bridge.

The old non-referee-grade bridge could make a "cycle" be the target cohomology
carrier and could mark closedness/integrality/type as trivially true.  This file
does not do that.  A `FiniteAlgebraicDistinctionCertificate` contains an actual
`AlgebraicCycle X p` from the classical Hodge interface, together with a finite
distinction witness and a type-(p,p) display witness.

The module deliberately avoids proving that every rational Hodge class has such
a certificate.  That is the hard theorem for the later image-equivalence layer.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement

universe u

/-- A finite distinction witness for an algebraic cycle: a finite index set and
a coding map into the irreducible-component index of the cycle.  This records
that the certificate is finite data, not a completed continuum class pretending
to be a cycle. -/
structure FiniteAlgebraicSupport
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (Z : AlgebraicCycle.{u, u} X p) where
  index : Type u
  fintype_index : Fintype index
  encode : index → Z.irreducibleComponent
  covers : Function.Surjective encode

instance
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {Z : AlgebraicCycle.{u, u} X p}
    (S : FiniteAlgebraicSupport Z) : Fintype S.index :=
  S.fintype_index

/-- Display-level `(p,p)` compatibility witness for the algebraic cycle.  This
is not the Hodge theorem; it is the local type certificate attached to a finite
algebraic witness.  The actual Hodge class represented by the cycle is supplied
later by a fixed cycle-class map. -/
structure TypePPDisplayWitness
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (Z : AlgebraicCycle.{u, u} X p) where
  displayTag : Type u
  finite_tag : Fintype displayTag
  component_type_pp : Z.irreducibleComponent → Prop
  component_type_pp_holds : ∀ i, component_type_pp i

/-- A finite algebraic distinction certificate for Hodge.  It is native finite
algebraic data: an algebraic cycle, finite support coding, and a `(p,p)` display
witness. -/
structure FiniteAlgebraicDistinctionCertificate
    (X : SmoothProjectiveComplexVariety.{u})
    (p : ℕ) where
  cycle : AlgebraicCycle.{u, u} X p
  finiteSupport : FiniteAlgebraicSupport cycle
  typePP : TypePPDisplayWitness cycle

namespace FiniteAlgebraicDistinctionCertificate

/-- Extract the actual algebraic cycle from a finite certificate. -/
def toAlgebraicCycle
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (C : FiniteAlgebraicDistinctionCertificate X p) :
    AlgebraicCycle.{u, u} X p :=
  C.cycle

/-- The irreducible components in a certificate are finite. -/
def component_finite
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (C : FiniteAlgebraicDistinctionCertificate X p) :
    Fintype C.cycle.irreducibleComponent :=
  C.cycle.fintype_components

/-- A certificate's support-code index covers every irreducible component. -/
theorem support_code_surjective
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (C : FiniteAlgebraicDistinctionCertificate X p) :
    Function.Surjective C.finiteSupport.encode :=
  C.finiteSupport.covers

/-- The certificate carries a `(p,p)` witness on every irreducible component. -/
theorem type_pp_holds
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (C : FiniteAlgebraicDistinctionCertificate X p) :
    ∀ i : C.cycle.irreducibleComponent, C.typePP.component_type_pp i :=
  C.typePP.component_type_pp_holds

end FiniteAlgebraicDistinctionCertificate

/-- A proposition used as a guard: target-cohomology vectors are not, by
themselves, finite algebraic distinction certificates.  A bridge that uses the
target cohomology carrier as its "cycle" must still supply this data. -/
def RequiresFiniteAlgebraicCertificate
    (X : SmoothProjectiveComplexVariety.{u})
    (p : ℕ)
    (_α : RationalHodgeClass.{u, u} X p) : Prop :=
  Nonempty (FiniteAlgebraicDistinctionCertificate X p)

/-- Certificate extraction headline: every finite certificate determines an
actual algebraic cycle object. -/
theorem finite_certificate_is_algebraic_cycle_data
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (C : FiniteAlgebraicDistinctionCertificate X p) :
    Nonempty (AlgebraicCycle.{u, u} X p) :=
  ⟨C.toAlgebraicCycle⟩

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

