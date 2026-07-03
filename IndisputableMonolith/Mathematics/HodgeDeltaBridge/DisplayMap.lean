import IndisputableMonolith.Mathematics.HodgeDeltaBridge.FiniteCertificate

/-!
# δ-Hodge Bridge: display map from finite certificates

This module defines the display map from finite algebraic distinction
certificates to the fixed rational cohomology target of a canonical cycle-class
map.

The quantifier order is the guard:

1. choose `(X,p)`;
2. choose a fixed `CanonicalCycleClassMap X p`;
3. display finite certificates through that map.

No per-class cycle-class map is chosen.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement

universe u

/-- Display value of a finite algebraic certificate under a fixed canonical
cycle-class map. -/
def certificateDisplay
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (C : FiniteAlgebraicDistinctionCertificate X p) :
    cl.targetCohomology.carrier :=
  cl.cycleClass C.toAlgebraicCycle

/-- A rational Hodge class is displayed by a finite certificate when it is
cohomology-compatible with the fixed cycle-class target and the certificate's
display equals its class vector. -/
structure CertificateDisplaysClass
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (C : FiniteAlgebraicDistinctionCertificate X p)
    (α : RationalHodgeClass.{u, u} X p) where
  cohomologyCompatible : α.cohomologyClass = cl.targetCohomology
  display_eq :
    certificateDisplay cl C =
      RationalHodgeClass.castClassVector α cohomologyCompatible

/-- Certificate display immediately yields the existing cycle-class equality
structure for the extracted algebraic cycle. -/
def cycleClassEquals_of_certificate_display
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {cl : CanonicalCycleClassMap.{u} X p}
    {C : FiniteAlgebraicDistinctionCertificate X p}
    {α : RationalHodgeClass.{u, u} X p}
    (h : CertificateDisplaysClass cl C α) :
    CycleClassEquals cl C.toAlgebraicCycle α where
  cohomologyCompatible := h.cohomologyCompatible
  classEquality := h.display_eq

/-- If a class is displayed by a finite certificate, then it has an algebraic
cycle representative under the fixed cycle-class map. -/
theorem certificate_display_has_cycle
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (α : RationalHodgeClass.{u, u} X p)
    (C : FiniteAlgebraicDistinctionCertificate X p)
    (h : CertificateDisplaysClass cl C α) :
    ∃ Z : AlgebraicCycle.{u, u} X p, Nonempty (CycleClassEquals cl Z α) :=
  ⟨C.toAlgebraicCycle, ⟨cycleClassEquals_of_certificate_display h⟩⟩

/-- Zero compatibility for display is inherited from the fixed cycle-class map. -/
theorem certificateDisplay_zero_coeff
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (C : FiniteAlgebraicDistinctionCertificate X p)
    (hzero : ∀ i : C.toAlgebraicCycle.irreducibleComponent,
      C.toAlgebraicCycle.coefficient i = 0) :
    certificateDisplay cl C = cl.targetCohomology.zero :=
  cl.map_zero C.toAlgebraicCycle hzero

/-- Additivity of certificate display for extracted algebraic cycles.  The
certificate layer for sums is built later; the display law already follows from
the fixed canonical map. -/
theorem certificateDisplay_add_cycles
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (C₁ C₂ : FiniteAlgebraicDistinctionCertificate X p) :
    cl.cycleClass (AlgebraicCycle.add C₁.toAlgebraicCycle C₂.toAlgebraicCycle) =
      cl.targetCohomology.add (certificateDisplay cl C₁) (certificateDisplay cl C₂) :=
  cl.map_add C₁.toAlgebraicCycle C₂.toAlgebraicCycle

/-- Scalar compatibility of certificate display for extracted algebraic cycles. -/
theorem certificateDisplay_smul_cycle
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (q : ℚ)
    (C : FiniteAlgebraicDistinctionCertificate X p) :
    cl.cycleClass (AlgebraicCycle.smul q C.toAlgebraicCycle) =
      cl.targetCohomology.smul q (certificateDisplay cl C) :=
  cl.map_smul q C.toAlgebraicCycle

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

