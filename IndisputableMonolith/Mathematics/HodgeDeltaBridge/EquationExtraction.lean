import IndisputableMonolith.Mathematics.HodgeDeltaBridge.FullTargetRealization

/-!
# δ-Hodge Bridge: finite equation extraction surface

This file names the algebraic geometry engine that still has to be built.
Instead of asking directly for an `EquationFiniteCertificate`, it asks for
finite homogeneous ideal codes, component carriers cut out by those ideals, and
cycle-class display equality against the supplied full Hodge target.

No Hodge content is assumed here.  The module proves only that this explicit
extraction data packages into the full-target realization criterion.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement

universe u

/-- Finite projective coordinate code for the selected projective embedding
display of `X`. -/
structure ProjectiveCoordinateCode
    (X : SmoothProjectiveComplexVariety.{u}) where
  coordinate : Type u
  fintype_coordinate : Fintype coordinate

instance
    {X : SmoothProjectiveComplexVariety.{u}}
    (C : ProjectiveCoordinateCode X) : Fintype C.coordinate :=
  C.fintype_coordinate

/-- A finitely supported homogeneous polynomial code over a finite projective
coordinate display. -/
structure HomogeneousPolynomialCode
    {X : SmoothProjectiveComplexVariety.{u}}
    (C : ProjectiveCoordinateCode X) where
  monomial : Type u
  fintype_monomial : Fintype monomial
  coefficient : monomial → ℚ
  exponent : monomial → C.coordinate → ℕ
  totalDegree : ℕ
  homogeneous : ∀ m : monomial, Finset.univ.sum (fun c => exponent m c) = totalDegree

instance
    {X : SmoothProjectiveComplexVariety.{u}}
    {C : ProjectiveCoordinateCode X}
    (P : HomogeneousPolynomialCode C) : Fintype P.monomial :=
  P.fintype_monomial

/-- Finite homogeneous ideal code: finitely many homogeneous polynomial
generators plus the common-zero predicate they define on `X`. -/
structure FiniteHomogeneousIdealCode
    (X : SmoothProjectiveComplexVariety.{u}) where
  coordinateCode : ProjectiveCoordinateCode X
  generator : Type u
  fintype_generator : Fintype generator
  polynomial : generator → HomogeneousPolynomialCode coordinateCode
  vanishesAt : X.carrier → Prop
  saturated : Prop
  saturated_holds : saturated
  radical : Prop
  radical_holds : radical
  common_zero_certified : Prop
  common_zero_certified_holds : common_zero_certified

instance
    {X : SmoothProjectiveComplexVariety.{u}}
    (I : FiniteHomogeneousIdealCode X) : Fintype I.generator :=
  I.fintype_generator

namespace FiniteHomogeneousIdealCode

/-- Forget ideal-code structure to the existing equation-system interface. -/
def toEquationSystem
    {X : SmoothProjectiveComplexVariety.{u}}
    (I : FiniteHomogeneousIdealCode X) :
    HomogeneousEquationSystem X where
  equation := I.generator
  fintype_equation := I.fintype_generator
  expression := fun _ => PUnit
  vanishesOn := I.vanishesAt
  certified_vanishing := I.common_zero_certified
  certified_vanishing_holds := I.common_zero_certified_holds

end FiniteHomogeneousIdealCode

/-- One projective component extracted from finite homogeneous ideal data. -/
structure EquationExtractionComponent
    (X : SmoothProjectiveComplexVariety.{u})
    (p : ℕ) where
  ideal : FiniteHomogeneousIdealCode X
  carrier : Type u
  carrier_nonempty : Nonempty carrier
  embedding : carrier → X.carrier
  satisfies_ideal : ∀ y : carrier, ideal.vanishesAt (embedding y)
  codimension : ℕ
  codimension_eq : codimension = p
  irreducible : Prop
  irreducible_holds : irreducible
  type_pp : Prop
  type_pp_holds : type_pp

namespace EquationExtractionComponent

/-- Convert an extracted component to the equation-cut component interface. -/
def toEquationCutSubvarietyData
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (V : EquationExtractionComponent X p) :
    EquationCutSubvarietyData X p where
  equations := V.ideal.toEquationSystem
  carrier := V.carrier
  carrier_nonempty := V.carrier_nonempty
  embedding := V.embedding
  satisfies_equations := V.satisfies_ideal
  codimension := V.codimension
  codimension_eq := V.codimension_eq
  irreducible := V.irreducible
  irreducible_holds := V.irreducible_holds
  type_pp := V.type_pp
  type_pp_holds := V.type_pp_holds

end EquationExtractionComponent

/-- Finite equation extraction support: finitely many extracted equation-cut
components and rational coefficients. -/
structure FiniteEquationExtractionSupport
    (X : SmoothProjectiveComplexVariety.{u})
    (p : ℕ) where
  component : Type u
  fintype_component : Fintype component
  data : component → EquationExtractionComponent X p
  coefficient : component → ℚ

instance
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (S : FiniteEquationExtractionSupport X p) : Fintype S.component :=
  S.fintype_component

namespace FiniteEquationExtractionSupport

/-- Convert extraction support to the existing finite equation-certificate
interface. -/
def toEquationFiniteCertificate
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (S : FiniteEquationExtractionSupport X p) :
    EquationFiniteCertificate X p where
  component := S.component
  fintype_component := S.fintype_component
  subvariety := fun i => (S.data i).toEquationCutSubvarietyData
  coefficient := S.coefficient

end FiniteEquationExtractionSupport

/-- Full-target finite equation extraction for one Hodge class. -/
structure FullTargetEquationExtraction
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {H : FullRationalHodgeTarget X p}
    (F : FullTargetCycleClassMap H)
    (α : H.hodgeClass) where
  support : FiniteEquationExtractionSupport X p
  displays :
    CertificateDisplaysClass
      F.cl
      support.toEquationFiniteCertificate.toFiniteCertificate
      (H.toRationalHodgeClass α)

namespace FullTargetEquationExtraction

/-- Extracted equation data gives the per-class realization object. -/
def toRealization
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {H : FullRationalHodgeTarget X p}
    {F : FullTargetCycleClassMap H}
    {α : H.hodgeClass}
    (E : FullTargetEquationExtraction F α) :
    FullTargetEquationRealization F α where
  certificate := E.support.toEquationFiniteCertificate
  displays := E.displays

end FullTargetEquationExtraction

/-- Extraction family for a supplied full Hodge target. -/
structure FullTargetEquationExtractionFamily
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (H : FullRationalHodgeTarget X p) where
  map : FullTargetCycleClassMap H
  extract : ∀ α : H.hodgeClass, FullTargetEquationExtraction map α

/-- An extraction family gives a realization family. -/
def realizationFamilyOfExtractionFamily
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {H : FullRationalHodgeTarget X p}
    (E : FullTargetEquationExtractionFamily H) :
    FullTargetEquationRealizationFamily H where
  map := E.map
  realize := fun α => (E.extract α).toRealization

/-- Global finite equation extraction data.  This is now the explicit
projective-algebraic construction target. -/
structure GlobalFullTargetEquationExtractionFamily where
  extraction :
    ∀ (X : SmoothProjectiveComplexVariety.{u})
      (p : ℕ)
      (H : FullRationalHodgeTarget X p),
      FullTargetEquationExtractionFamily H

/-- Global extraction data yields global realization data. -/
def globalRealizationFamilyOfExtractionFamily
    (G : GlobalFullTargetEquationExtractionFamily.{u}) :
    GlobalFullTargetEquationRealizationFamily.{u} where
  realization := fun X p H =>
    realizationFamilyOfExtractionFamily (G.extraction X p H)

/-- Global finite equation extraction proves the strengthened final target. -/
theorem full_target_hodge_from_global_equation_extraction
    (G : GlobalFullTargetEquationExtractionFamily.{u}) :
    hodge_conjecture_unconditional_full_target.{u} :=
  full_target_hodge_from_global_realization_family
    (globalRealizationFamilyOfExtractionFamily G)

/-- Nonempty global finite equation extraction data is sufficient for final
Hodge closure in the strengthened full-target interface. -/
theorem global_full_target_equation_extraction_is_sufficient :
    Nonempty (GlobalFullTargetEquationExtractionFamily.{u}) →
      hodge_conjecture_unconditional_full_target.{u} := by
  intro h
  rcases h with ⟨G⟩
  exact full_target_hodge_from_global_equation_extraction G

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

