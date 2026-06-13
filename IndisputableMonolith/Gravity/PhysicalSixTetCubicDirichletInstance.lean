import IndisputableMonolith.Geometry.PeriodicFreudenthalTorus
import IndisputableMonolith.Geometry.ReggeActionNonlinearCorrespondence
import IndisputableMonolith.Gravity.FreudenthalLengthChainEndpointCert
import IndisputableMonolith.Gravity.ReggeCubicLatticeLimit

/-!
# Physical Six-Tet Cubic Dirichlet Instance

This module connects the encoded periodic Freudenthal torus scaffold to the
`PhysicalSixTetCubicDirichletModel` target.

It does not assert the physical Dirichlet equality for free.  Instead it
packages the exact theorem obligations needed to instantiate the physical
model on a periodic Freudenthal torus.
-/

namespace IndisputableMonolith
namespace Gravity
namespace PhysicalSixTetCubicDirichletInstance

open Geometry.ReggeTriangulation3D
open Geometry.ReggeHessian3D
open Geometry.Triangulation3DConsistency
open Geometry.ReggeActionConcrete
open Geometry.ReggeActionSmoothness
open Geometry.ReggeActionFirstVariation
open Geometry.ReggeActionSecondVariation
open Geometry.ReggeActionNonlinearHessianProof
open Geometry.ReggeActionNonlinearCorrespondence
open Geometry.ReggeActionCubicTaylorBound
open Geometry.PeriodicFreudenthalTorus
open Geometry.ReggeRigorousFoundation
open Geometry.SchlaefliTetrahedronProof
open Geometry.SchlaefliTetrahedron
open ReggeCubicLatticeLimit

noncomputable section

def CanonicalHessianIsDirichlet
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz) : Prop :=
  ∀ ξ : VertexPotential P.K,
    hessianQuadratic (canonicalReggeHessian P.K P.hK) ξ =
      canonicalDirichletEnergy P.K P.hK ξ

theorem canonicalHessianIsDirichlet_of_encodedPeriodicFreudenthal
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz) :
    CanonicalHessianIsDirichlet P :=
  fun ξ => canonicalReggeHessian_quadratic_eq_dirichlet P.K P.hK ξ

/-- Physical finite-difference Dirichlet operator placeholder, separated from
the abstract canonical graph Dirichlet energy.  A later proof should replace
this with the actual six-tet cubic stencil expression. -/
abbrev PhysicalFiniteDifferenceDirichletAction
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz) :=
  VertexPotential P.K → ℝ

/-- The exact remaining physical identification target: the canonical
Dirichlet energy from incidence weights equals the concrete six-tet
finite-difference Dirichlet action. -/
def PhysicalFiniteDifferenceDirichletTarget
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz)
    (D : PhysicalFiniteDifferenceDirichletAction P) : Prop :=
  ∀ ξ : VertexPotential P.K, canonicalDirichletEnergy P.K P.hK ξ = D ξ

/-- Concrete edge-stencil candidate for the physical six-tet finite-difference
Dirichlet action: sum over the encoded global periodic edges, weighted by the
flat global edge length.  This is distinct from the abstract canonical
vertex-pair Dirichlet energy and is the next physical identification target. -/
def periodicEdgeStencilDirichletAction
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz) :
    PhysicalFiniteDifferenceDirichletAction P :=
  canonicalEdgeStencilDirichletEnergy P.K P.hK

/-- The three axis displacement classes inside the seven positive Freudenthal
edge classes. -/
def periodicAxisDisp (d : Fin 3) : Fin 7 :=
  ⟨d.1, by omega⟩

/-- Corrected rational axis stencil exposed by the Session 202 mixed-target
audit.  The mixed hinge-deficit quadratic cancels the local square-root factors
and matches twice the axis-edge stencil, not the full
`sqrt(periodicDispSqEdge)` seven-class edge stencil. -/
def canonicalPeriodicMixedAxisStencilAction
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    PhysicalFiniteDifferenceDirichletAction
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) :=
  fun ξ =>
    ∑ base : Vertex Nx Ny Nz, ∑ d : Fin 3,
      let edge : PeriodicEdge Nx Ny Nz := { base := base, disp := periodicAxisDisp d }
      2 *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

def PeriodicEdgeStencilDirichletTarget
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz) : Prop :=
  PhysicalFiniteDifferenceDirichletTarget P
    (periodicEdgeStencilDirichletAction P)

theorem periodicEdgeStencilDirichletAction_nonneg
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz)
    (ξ : VertexPotential P.K) :
    0 ≤ periodicEdgeStencilDirichletAction P ξ := by
  exact canonicalEdgeStencilDirichletEnergy_nonneg P.K P.hK ξ

theorem periodicEdgeStencilTarget_of_noSelfLoop
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz)
    (hNoLoop : NoSelfLoopEdges P.K) :
    PeriodicEdgeStencilDirichletTarget P :=
  canonicalDirichletEqualsEdgeStencil_of_sumComm_and_reindex P.K P.hK
    (canonicalEdgeStencilSumComm P.K P.hK)
    (canonicalEdgePairWeightReindex_of_noSelfLoop P.K P.hK hNoLoop)

theorem canonicalPeriodicNoSelfLoopEdges
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    NoSelfLoopEdges (canonicalPeriodicTriangulation Nx Ny Nz) := by
  intro e h
  have hverts :
      (edgeFinEquiv Nx Ny Nz e).endpoints.1 =
        (edgeFinEquiv Nx Ny Nz e).endpoints.2 := by
    unfold canonicalPeriodicTriangulation canonicalEdgeVerts at h
    exact (vertexFinEquiv Nx Ny Nz).symm.injective h
  exact PeriodicEdge.endpoints_ne hx hy hz (edgeFinEquiv Nx Ny Nz e) hverts

theorem canonicalPeriodicEdgeStencilTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    PeriodicEdgeStencilDirichletTarget
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) :=
  periodicEdgeStencilTarget_of_noSelfLoop
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz)
    (canonicalPeriodicNoSelfLoopEdges Nx Ny Nz hx hy hz)

theorem canonicalPeriodicJQuadraticTerm_eq_edgeStencil
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    canonicalJQuadraticTerm
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        ξ =
      (1 / 2) * periodicEdgeStencilDirichletAction
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) ξ := by
  rw [canonicalJQuadraticTerm_eq_dirichlet]
  rw [canonicalPeriodicEdgeStencilTarget Nx Ny Nz hx hy hz ξ]

/-- The concrete local nonlinear Regge/J-cost correspondence on the canonical
periodic Freudenthal torus, with the quadratic term written as the real
edge-stencil Dirichlet operator. -/
def CanonicalPeriodicEdgeStencilLocalCorrespondence
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
    ∀ ξ : VertexPotential P.K, ‖ξ‖ < r →
      ‖reggeAction P.K P.hK ξ -
          reggeAction P.K P.hK (zeroPotential P.K) -
          (1 / 2) * periodicEdgeStencilDirichletAction P ξ‖ ≤
        C * ‖ξ‖ ^ (3 : ℕ)

/-- Concrete periodic Freudenthal form of the strongest true replacement:
the full nonlinear Regge action is its flat value plus one half of the periodic
edge-stencil/J quadratic energy, up to a controlled cubic remainder. -/
def CanonicalPeriodicStrongestTrueReplacement
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz

theorem canonicalPeriodicStrongestTrueReplacement_iff_edgeStencilLocalCorrespondence
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicStrongestTrueReplacement Nx Ny Nz hx hy hz ↔
      CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  Iff.rfl

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_taylor
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hTaylor :
      NonlinearReggeCubicTaylorTheorem
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  have hLocal := nonlinearRegge_localCorrespondence_of_taylorTheorem P.K P.hK hTaylor
  rcases hLocal with ⟨r, C, hr, hC, hineq⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro ξ hξ
  have hJ := canonicalPeriodicJQuadraticTerm_eq_edgeStencil Nx Ny Nz hx hy hz ξ
  simpa [CanonicalPeriodicEdgeStencilLocalCorrespondence, P, hJ]
    using hineq ξ hξ

/-- Periodic Freudenthal local correspondence from the now-closed line-Taylor
cascade.  The remaining caller data are the flat configuration and the standard
remainder first/second variation jets; the cubic Taylor estimate itself is no
longer a separate input. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_flat_and_remainderJets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFlat :
      FlatConfiguration
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
    (hFirst :
      ReggeActionRemainderFirstVariationInput
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalReggeHessian
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK))
    (hSecond :
      ReggeActionRemainderSecondVariationInput
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  exact canonicalPeriodicEdgeStencilLocalCorrespondence_of_taylor Nx Ny Nz hx hy hz
    (nonlinearReggeCubicTaylorTheorem_of_flat_and_remainderJets
      P.K P.hK hFlat hFirst hSecond)

/-- Periodic Freudenthal local correspondence from flatness, the remainder
first variation, and the nonlinear directional Hessian theorem.  The Hessian
theorem supplies the remainder second-variation jet; the closed line-Taylor
cascade then supplies the cubic remainder bound. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_flat_first_and_directionalHessian
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFlat :
      FlatConfiguration
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
    (hFirst :
      ReggeActionRemainderFirstVariationInput
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalReggeHessian
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK))
    (hHessian :
      NonlinearReggeDirectionalHessianTheorem
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  exact canonicalPeriodicEdgeStencilLocalCorrespondence_of_flat_and_remainderJets
    Nx Ny Nz hx hy hz hFlat hFirst
    (reggeActionRemainderSecondVariationInput_of_flat_directionalHessian
      P.K P.hK hFlat hHessian)

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_eventuallyZero_edgeStencil_and_taylor
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFlat :
      FlatConfiguration
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
    (D : DeficitAngleDirectionalDerivativePackage
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        hFlat)
    (hMixed :
      MixedHingeDeficitEdgeStencilTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        D)
    (hTaylor :
      NonlinearReggeCubicTaylorTheorem
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  have hLocal :=
    nonlinearRegge_localCorrespondence_of_eventuallyZero_edgeStencil_and_taylor
      P.K P.hK hFlat D hZero hMixed
      (canonicalPeriodicEdgeStencilTarget Nx Ny Nz hx hy hz) hTaylor
  rcases hLocal with ⟨r, C, hr, hC, hineq⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro ξ hξ
  have hJ := canonicalPeriodicJQuadraticTerm_eq_edgeStencil Nx Ny Nz hx hy hz ξ
  simpa [CanonicalPeriodicEdgeStencilLocalCorrespondence, P, hJ]
    using hineq ξ hξ

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_localHessianTaylorInputs
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFlat :
      FlatConfiguration
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
    (hInputs :
      NonlinearReggeLocalHessianTaylorInputs
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        hFlat) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  have hLocal :=
    nonlinearRegge_localCorrespondence_of_localHessianTaylorInputs
      P.K P.hK hFlat hInputs
  rcases hLocal with ⟨r, C, hr, hC, hineq⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro ξ hξ
  have hJ := canonicalPeriodicJQuadraticTerm_eq_edgeStencil Nx Ny Nz hx hy hz ξ
  simpa [CanonicalPeriodicEdgeStencilLocalCorrespondence, P, hJ]
    using hineq ξ hξ

theorem canonicalPeriodicStrongestTrueReplacement_of_localHessianTaylorInputs
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFlat :
      FlatConfiguration
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
    (hInputs :
      NonlinearReggeLocalHessianTaylorInputs
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        hFlat) :
    CanonicalPeriodicStrongestTrueReplacement Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_localHessianTaylorInputs
    Nx Ny Nz hx hy hz hFlat hInputs

/-- The theorem data needed to identify the encoded periodic Freudenthal torus
with the physical cubic Dirichlet model. -/
structure PeriodicFreudenthalDirichletCertificate
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz) where
  latticeSpacing : ℝ
  spacing_pos : 0 < latticeSpacing
  continuumAction : VertexPotential P.K → ℝ
  errorConstant : ℝ
  errorConstant_nonneg : 0 ≤ errorConstant
  sixTetCubicDecomposition : Prop
  canonicalHessian_is_dirichlet : Prop
  physicalFiniteDifferenceAction : PhysicalFiniteDifferenceDirichletAction P
  physicalFiniteDifference_identification :
    PhysicalFiniteDifferenceDirichletTarget P physicalFiniteDifferenceAction
  finiteDifferenceEstimate :
    ∀ ξ : VertexPotential P.K,
      |reggeActionSecondOrder P.K P.hK (canonicalReggeHessian P.K P.hK) ξ -
        continuumAction ξ| ≤ errorConstant * latticeSpacing ^ (2 : ℕ)

def regularModel_of_periodicFreudenthalCertificate
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {P : EncodedPeriodicFreudenthalTorus Nx Ny Nz}
    (C : PeriodicFreudenthalDirichletCertificate P) :
    RegularCubicLatticeModel P.K P.hK where
  latticeSpacing := C.latticeSpacing
  spacing_pos := C.spacing_pos
  continuumAction := C.continuumAction
  errorConstant := C.errorConstant
  errorConstant_nonneg := C.errorConstant_nonneg
  secondOrder_action_error := C.finiteDifferenceEstimate

def physicalSixTetModel_of_periodicFreudenthalCertificate
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {P : EncodedPeriodicFreudenthalTorus Nx Ny Nz}
    (C : PeriodicFreudenthalDirichletCertificate P) :
    PhysicalSixTetCubicDirichletModel P.K P.hK where
  regularModel := regularModel_of_periodicFreudenthalCertificate C
  sixTetCubicDecomposition := C.sixTetCubicDecomposition
  canonicalHessian_is_dirichlet := C.canonicalHessian_is_dirichlet
  finiteDifferenceEstimate := C.finiteDifferenceEstimate

def cubicLimitInput_of_periodicFreudenthalCertificate
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {P : EncodedPeriodicFreudenthalTorus Nx Ny Nz}
    (C : PeriodicFreudenthalDirichletCertificate P) :
    ReggeCubicLatticeLimitInput P.K P.hK :=
  cubicLatticeLimitInput_of_physicalSixTetModel P.K P.hK
    (physicalSixTetModel_of_periodicFreudenthalCertificate C)

theorem periodicFreudenthalCertificate_cubicLimit
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {P : EncodedPeriodicFreudenthalTorus Nx Ny Nz}
    (C : PeriodicFreudenthalDirichletCertificate P) :
    ReggeSecondOrderCubicLatticeLimit P.K P.hK
      (regularModel_of_periodicFreudenthalCertificate C) :=
  C.finiteDifferenceEstimate

/-- Refinement-family convergence at the physical periodic-Freudenthal
certificate layer.  This connects the six-tet/edge-stencil certificate path to
the abstract cubic-lattice convergence wrapper: once the certified
`C a^2` envelope tends to zero, the second-order Regge action converges
pointwise to the supplied continuum action. -/
theorem periodicFreudenthalCertificate_error_vanishes_along_family
    {α : Type*} {l : Filter α}
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {P : EncodedPeriodicFreudenthalTorus Nx Ny Nz}
    (C : α → PeriodicFreudenthalDirichletCertificate P)
    (hEnvelope :
      Filter.Tendsto
        (fun t : α => (C t).errorConstant * (C t).latticeSpacing ^ (2 : ℕ))
        l (nhds 0))
    (ξ : VertexPotential P.K) :
    Filter.Tendsto
      (fun t : α =>
        |reggeActionSecondOrder P.K P.hK (canonicalReggeHessian P.K P.hK) ξ -
          (C t).continuumAction ξ|)
      l (nhds 0) := by
  exact
    reggeSecondOrderCubicLatticeLimit_error_vanishes_along_models
      P.K P.hK
      (fun t : α => regularModel_of_periodicFreudenthalCertificate (C t))
      (fun t => periodicFreudenthalCertificate_cubicLimit (C t))
      hEnvelope ξ

/-- Usable refinement criterion for Track 1.B: if the certificate error
constants are uniformly bounded and the lattice spacing tends to zero, then the
physical periodic-Freudenthal certificate family converges pointwise. -/
theorem periodicFreudenthalCertificate_error_vanishes_of_bounded_error_and_spacing
    {α : Type*} {l : Filter α}
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {P : EncodedPeriodicFreudenthalTorus Nx Ny Nz}
    (C : α → PeriodicFreudenthalDirichletCertificate P)
    (B : ℝ)
    (hBound : ∀ t : α, (C t).errorConstant ≤ B)
    (hSpacing : Filter.Tendsto (fun t : α => (C t).latticeSpacing) l (nhds 0))
    (ξ : VertexPotential P.K) :
    Filter.Tendsto
      (fun t : α =>
        |reggeActionSecondOrder P.K P.hK (canonicalReggeHessian P.K P.hK) ξ -
          (C t).continuumAction ξ|)
      l (nhds 0) := by
  have hEnvelope :
      Filter.Tendsto
        (fun t : α => (C t).errorConstant * (C t).latticeSpacing ^ (2 : ℕ))
        l (nhds 0) := by
    apply squeeze_zero
    · intro t
      exact mul_nonneg (C t).errorConstant_nonneg (sq_nonneg (C t).latticeSpacing)
    · intro t
      exact mul_le_mul_of_nonneg_right (hBound t) (sq_nonneg (C t).latticeSpacing)
    · have hcont : Continuous (fun a : ℝ => B * a ^ (2 : ℕ)) := by
        continuity
      have ht := hcont.tendsto (0 : ℝ)
      simpa using ht.comp hSpacing
  exact periodicFreudenthalCertificate_error_vanishes_along_family C hEnvelope ξ

/-- A refinement-indexed family of physical periodic-Freudenthal certificates
with exactly the hypotheses needed for pointwise second-order convergence. -/
structure PeriodicFreudenthalRefinementFamily
    {α : Type*} (l : Filter α)
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz) where
  cert : α → PeriodicFreudenthalDirichletCertificate P
  errorBound : ℝ
  error_bound : ∀ t : α, (cert t).errorConstant ≤ errorBound
  spacing_tendsto_zero :
    Filter.Tendsto (fun t : α => (cert t).latticeSpacing) l (nhds 0)

theorem PeriodicFreudenthalRefinementFamily.pointwise_converges
    {α : Type*} {l : Filter α}
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {P : EncodedPeriodicFreudenthalTorus Nx Ny Nz}
    (F : PeriodicFreudenthalRefinementFamily l P)
    (ξ : VertexPotential P.K) :
    Filter.Tendsto
      (fun t : α =>
        |reggeActionSecondOrder P.K P.hK (canonicalReggeHessian P.K P.hK) ξ -
          (F.cert t).continuumAction ξ|)
      l (nhds 0) :=
  periodicFreudenthalCertificate_error_vanishes_of_bounded_error_and_spacing
    F.cert F.errorBound F.error_bound F.spacing_tendsto_zero ξ

/-- Transfer from a spacing-dependent continuum comparison action to a fixed
continuum action.  Once the certificate family proves
`S_Regge(a) - S_cont(a) → 0`, it is enough to prove
`S_cont(a) → S_continuum` to get `S_Regge(a) → S_continuum`. -/
theorem PeriodicFreudenthalRefinementFamily.pointwise_converges_to_fixed_limit
    {α : Type*} {l : Filter α}
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {P : EncodedPeriodicFreudenthalTorus Nx Ny Nz}
    (F : PeriodicFreudenthalRefinementFamily l P)
    (limitAction : VertexPotential P.K → ℝ)
    (ξ : VertexPotential P.K)
    (hContinuum :
      Filter.Tendsto (fun t : α => (F.cert t).continuumAction ξ)
        l (nhds (limitAction ξ))) :
    Filter.Tendsto
      (fun _t : α =>
        reggeActionSecondOrder P.K P.hK (canonicalReggeHessian P.K P.hK) ξ)
      l (nhds (limitAction ξ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hRegge := F.pointwise_converges ξ
  have hContinuumAbs :
      Filter.Tendsto
        (fun t : α => |(F.cert t).continuumAction ξ - limitAction ξ|)
        l (nhds 0) := by
    have hdist := tendsto_iff_dist_tendsto_zero.mp hContinuum
    simpa [Real.dist_eq] using hdist
  have hsum := hRegge.add hContinuumAbs
  apply squeeze_zero
  · intro t
    exact dist_nonneg
  · intro t
    let R := reggeActionSecondOrder P.K P.hK (canonicalReggeHessian P.K P.hK) ξ
    let C := (F.cert t).continuumAction ξ
    let L := limitAction ξ
    calc
      dist R L = |R - L| := by
        simp [Real.dist_eq]
      _ = |(R - C) + (C - L)| := by
        congr 1
        ring
      _ ≤ |R - C| + |C - L| := abs_add_le _ _
  · simpa [Real.dist_eq] using hsum

/-- Exact-comparison sanity certificate for an encoded periodic Freudenthal
torus.  The continuum action is chosen to be the canonical second-order Regge
action itself, so the error bound is zero.  This does not replace the physical
finite-difference Dirichlet identification; it proves the certificate pathway
is inhabited for every encoded periodic torus. -/
def exactPeriodicFreudenthalComparisonCertificate
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz) :
    PeriodicFreudenthalDirichletCertificate P where
  latticeSpacing := 1
  spacing_pos := by norm_num
  continuumAction := reggeActionSecondOrder P.K P.hK (canonicalReggeHessian P.K P.hK)
  errorConstant := 0
  errorConstant_nonneg := le_rfl
  sixTetCubicDecomposition := True
  canonicalHessian_is_dirichlet := CanonicalHessianIsDirichlet P
  physicalFiniteDifferenceAction := canonicalDirichletEnergy P.K P.hK
  physicalFiniteDifference_identification := by
    intro ξ
    rfl
  finiteDifferenceEstimate := by
    intro ξ
    simp

/-- Exact-comparison certificate with an arbitrary positive lattice spacing.
This is the spacing-varying version needed for refinement-indexed families. -/
def exactPeriodicFreudenthalComparisonCertificateAtSpacing
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz)
    (a : ℝ) (ha : 0 < a) :
    PeriodicFreudenthalDirichletCertificate P where
  latticeSpacing := a
  spacing_pos := ha
  continuumAction := reggeActionSecondOrder P.K P.hK (canonicalReggeHessian P.K P.hK)
  errorConstant := 0
  errorConstant_nonneg := le_rfl
  sixTetCubicDecomposition := True
  canonicalHessian_is_dirichlet := CanonicalHessianIsDirichlet P
  physicalFiniteDifferenceAction := canonicalDirichletEnergy P.K P.hK
  physicalFiniteDifference_identification := by
    intro ξ
    rfl
  finiteDifferenceEstimate := by
    intro ξ
    simp

/-- The spacing-varying exact comparison certificates converge along any
refinement schedule whose lattice spacing tends to zero.  This theorem is a
certificate-path sanity check, not the physical continuum normalization. -/
theorem exactPeriodicFreudenthalComparisonCertificateAtSpacing_converges
    {α : Type*} {l : Filter α}
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz)
    (a : α → ℝ) (ha : ∀ t : α, 0 < a t)
    (hSpacing : Filter.Tendsto a l (nhds 0))
    (ξ : VertexPotential P.K) :
    Filter.Tendsto
      (fun t : α =>
        |reggeActionSecondOrder P.K P.hK (canonicalReggeHessian P.K P.hK) ξ -
          (exactPeriodicFreudenthalComparisonCertificateAtSpacing P (a t) (ha t)).continuumAction ξ|)
      l (nhds 0) := by
  exact
    periodicFreudenthalCertificate_error_vanishes_of_bounded_error_and_spacing
      (fun t : α => exactPeriodicFreudenthalComparisonCertificateAtSpacing P (a t) (ha t))
      0
      (by
        intro t
        simp [exactPeriodicFreudenthalComparisonCertificateAtSpacing])
      (by
        simpa [exactPeriodicFreudenthalComparisonCertificateAtSpacing] using hSpacing)
      ξ

/-- Canonical periodic certificate using the actual periodic edge-stencil
Dirichlet action as the finite-difference operator.  The continuum comparison
is still the exact second-order Regge comparison, so this closes the operator
identification without claiming the separate continuum-normalization estimate. -/
def canonicalPeriodicEdgeStencilComparisonCertificate
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    PeriodicFreudenthalDirichletCertificate
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) where
  latticeSpacing := 1
  spacing_pos := by norm_num
  continuumAction :=
    reggeActionSecondOrder
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
      (canonicalReggeHessian
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
  errorConstant := 0
  errorConstant_nonneg := le_rfl
  sixTetCubicDecomposition := True
  canonicalHessian_is_dirichlet :=
    CanonicalHessianIsDirichlet
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz)
  physicalFiniteDifferenceAction :=
    periodicEdgeStencilDirichletAction
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz)
  physicalFiniteDifference_identification :=
    canonicalPeriodicEdgeStencilTarget Nx Ny Nz hx hy hz
  finiteDifferenceEstimate := by
    intro ξ
    simp

/-- Canonical periodic edge-stencil certificate with arbitrary positive lattice
spacing.  This is the spacing-varying canonical periodic family used by the
refinement criterion. -/
def canonicalPeriodicEdgeStencilComparisonCertificateAtSpacing
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : ℝ) (ha : 0 < a) :
    PeriodicFreudenthalDirichletCertificate
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) where
  latticeSpacing := a
  spacing_pos := ha
  continuumAction :=
    reggeActionSecondOrder
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
      (canonicalReggeHessian
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
  errorConstant := 0
  errorConstant_nonneg := le_rfl
  sixTetCubicDecomposition := True
  canonicalHessian_is_dirichlet :=
    CanonicalHessianIsDirichlet
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz)
  physicalFiniteDifferenceAction :=
    periodicEdgeStencilDirichletAction
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz)
  physicalFiniteDifference_identification :=
    canonicalPeriodicEdgeStencilTarget Nx Ny Nz hx hy hz
  finiteDifferenceEstimate := by
    intro ξ
    simp

/-- Canonical periodic edge-stencil certificate with a supplied physical
continuum comparison action and a supplied `C a^2` estimate.  This is the
non-exact certificate constructor needed for the real Track 1.B continuum
normalization step. -/
def canonicalPeriodicEdgeStencilContinuumCertificateAtSpacing
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : ℝ) (ha : 0 < a)
    (continuumAction :
      VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K → ℝ)
    (errorConstant : ℝ) (hErrorNonneg : 0 ≤ errorConstant)
    (hEstimate :
      ∀ ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
        |reggeActionSecondOrder
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (canonicalReggeHessian
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
            ξ - continuumAction ξ| ≤ errorConstant * a ^ (2 : ℕ)) :
    PeriodicFreudenthalDirichletCertificate
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) where
  latticeSpacing := a
  spacing_pos := ha
  continuumAction := continuumAction
  errorConstant := errorConstant
  errorConstant_nonneg := hErrorNonneg
  sixTetCubicDecomposition := True
  canonicalHessian_is_dirichlet :=
    CanonicalHessianIsDirichlet
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz)
  physicalFiniteDifferenceAction :=
    periodicEdgeStencilDirichletAction
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz)
  physicalFiniteDifference_identification :=
    canonicalPeriodicEdgeStencilTarget Nx Ny Nz hx hy hz
  finiteDifferenceEstimate := hEstimate

/-- Spacing-refinement convergence for the canonical periodic edge-stencil
certificate family.  This is the first actual spacing-varying periodic
Freudenthal certificate path into the Track 1.B second-order convergence
wrapper. -/
theorem canonicalPeriodicEdgeStencilComparisonCertificateAtSpacing_converges
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : α → ℝ) (ha : ∀ t : α, 0 < a t)
    (hSpacing : Filter.Tendsto a l (nhds 0))
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun t : α =>
        |reggeActionSecondOrder
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (canonicalReggeHessian
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
            ξ -
          (canonicalPeriodicEdgeStencilComparisonCertificateAtSpacing Nx Ny Nz hx hy hz
            (a t) (ha t)).continuumAction ξ|)
      l (nhds 0) := by
  exact
    periodicFreudenthalCertificate_error_vanishes_of_bounded_error_and_spacing
      (fun t : α =>
        canonicalPeriodicEdgeStencilComparisonCertificateAtSpacing Nx Ny Nz hx hy hz (a t) (ha t))
      0
      (by
        intro t
        simp [canonicalPeriodicEdgeStencilComparisonCertificateAtSpacing])
      (by
        simpa [canonicalPeriodicEdgeStencilComparisonCertificateAtSpacing] using hSpacing)
      ξ

def canonicalPeriodicEdgeStencilRefinementFamily
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : α → ℝ) (ha : ∀ t : α, 0 < a t)
    (hSpacing : Filter.Tendsto a l (nhds 0)) :
    PeriodicFreudenthalRefinementFamily l
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) where
  cert := fun t =>
    canonicalPeriodicEdgeStencilComparisonCertificateAtSpacing Nx Ny Nz hx hy hz
      (a t) (ha t)
  errorBound := 0
  error_bound := by
    intro t
    simp [canonicalPeriodicEdgeStencilComparisonCertificateAtSpacing]
  spacing_tendsto_zero := by
    simpa [canonicalPeriodicEdgeStencilComparisonCertificateAtSpacing] using hSpacing

theorem canonicalPeriodicEdgeStencilRefinementFamily_pointwise_converges
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : α → ℝ) (ha : ∀ t : α, 0 < a t)
    (hSpacing : Filter.Tendsto a l (nhds 0))
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun t : α =>
        |reggeActionSecondOrder
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (canonicalReggeHessian
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
            ξ -
          ((canonicalPeriodicEdgeStencilRefinementFamily Nx Ny Nz hx hy hz a ha hSpacing).cert t).continuumAction ξ|)
      l (nhds 0) :=
  (canonicalPeriodicEdgeStencilRefinementFamily Nx Ny Nz hx hy hz a ha hSpacing).pointwise_converges ξ

/-- Refinement-family constructor for the true physical continuum comparison
path: each spacing gets a canonical periodic edge-stencil certificate with a
supplied continuum action and a supplied `C a^2` estimate.  Uniform boundedness
of the supplied constants is the only analytic hypothesis needed by the
abstract convergence wrapper. -/
def canonicalPeriodicEdgeStencilContinuumRefinementFamily
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : α → ℝ) (ha : ∀ t : α, 0 < a t)
    (hSpacing : Filter.Tendsto a l (nhds 0))
    (continuumAction :
      α →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K → ℝ)
    (errorConstant : α → ℝ)
    (hErrorNonneg : ∀ t : α, 0 ≤ errorConstant t)
    (B : ℝ) (hBound : ∀ t : α, errorConstant t ≤ B)
    (hEstimate :
      ∀ t : α,
        ∀ ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
          |reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              ξ - continuumAction t ξ| ≤ errorConstant t * a t ^ (2 : ℕ)) :
    PeriodicFreudenthalRefinementFamily l
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) where
  cert := fun t =>
    canonicalPeriodicEdgeStencilContinuumCertificateAtSpacing
      Nx Ny Nz hx hy hz (a t) (ha t) (continuumAction t)
      (errorConstant t) (hErrorNonneg t) (hEstimate t)
  errorBound := B
  error_bound := by
    intro t
    simpa [canonicalPeriodicEdgeStencilContinuumCertificateAtSpacing] using hBound t
  spacing_tendsto_zero := by
    simpa [canonicalPeriodicEdgeStencilContinuumCertificateAtSpacing] using hSpacing

theorem canonicalPeriodicEdgeStencilContinuumRefinementFamily_pointwise_converges
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : α → ℝ) (ha : ∀ t : α, 0 < a t)
    (hSpacing : Filter.Tendsto a l (nhds 0))
    (continuumAction :
      α →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K → ℝ)
    (errorConstant : α → ℝ)
    (hErrorNonneg : ∀ t : α, 0 ≤ errorConstant t)
    (B : ℝ) (hBound : ∀ t : α, errorConstant t ≤ B)
    (hEstimate :
      ∀ t : α,
        ∀ ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
          |reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              ξ - continuumAction t ξ| ≤ errorConstant t * a t ^ (2 : ℕ))
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun t : α =>
        |reggeActionSecondOrder
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (canonicalReggeHessian
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
            ξ -
          ((canonicalPeriodicEdgeStencilContinuumRefinementFamily
            Nx Ny Nz hx hy hz a ha hSpacing continuumAction errorConstant
            hErrorNonneg B hBound hEstimate).cert t).continuumAction ξ|)
      l (nhds 0) :=
  (canonicalPeriodicEdgeStencilContinuumRefinementFamily
    Nx Ny Nz hx hy hz a ha hSpacing continuumAction errorConstant
    hErrorNonneg B hBound hEstimate).pointwise_converges ξ

theorem canonicalPeriodicEdgeStencilContinuumRefinementFamily_converges_to_fixed_limit
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : α → ℝ) (ha : ∀ t : α, 0 < a t)
    (hSpacing : Filter.Tendsto a l (nhds 0))
    (continuumAction :
      α →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K → ℝ)
    (errorConstant : α → ℝ)
    (hErrorNonneg : ∀ t : α, 0 ≤ errorConstant t)
    (B : ℝ) (hBound : ∀ t : α, errorConstant t ≤ B)
    (hEstimate :
      ∀ t : α,
        ∀ ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
          |reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              ξ - continuumAction t ξ| ≤ errorConstant t * a t ^ (2 : ℕ))
    (limitAction :
      VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K → ℝ)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (hContinuum :
      Filter.Tendsto (fun t : α => continuumAction t ξ) l (nhds (limitAction ξ))) :
    Filter.Tendsto
      (fun _t : α =>
        reggeActionSecondOrder
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
          (canonicalReggeHessian
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
          ξ)
      l (nhds (limitAction ξ)) := by
  let F :=
    canonicalPeriodicEdgeStencilContinuumRefinementFamily
      Nx Ny Nz hx hy hz a ha hSpacing continuumAction errorConstant
      hErrorNonneg B hBound hEstimate
  exact F.pointwise_converges_to_fixed_limit limitAction ξ (by
    simpa [F, canonicalPeriodicEdgeStencilContinuumRefinementFamily] using hContinuum)

/-- Data package for the remaining fixed-continuum comparison step in Track
1.B.  To instantiate this with Einstein-Hilbert, future work must provide the
fixed continuum action, spacing-dependent comparison actions, `C a^2`
estimates, bounded constants, and convergence of the spacing-dependent actions
to the fixed one. -/
structure CanonicalPeriodicFixedContinuumComparisonData
    {α : Type*} (l : Filter α)
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) where
  spacing : α → ℝ
  spacing_pos : ∀ t : α, 0 < spacing t
  spacing_tendsto_zero : Filter.Tendsto spacing l (nhds 0)
  continuumAction :
    α →
      VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K → ℝ
  errorConstant : α → ℝ
  error_nonneg : ∀ t : α, 0 ≤ errorConstant t
  errorBound : ℝ
  error_bound : ∀ t : α, errorConstant t ≤ errorBound
  estimate :
    ∀ t : α,
      ∀ ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
        |reggeActionSecondOrder
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (canonicalReggeHessian
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
            ξ - continuumAction t ξ| ≤ errorConstant t * spacing t ^ (2 : ℕ)
  limitAction :
    VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K → ℝ
  continuum_tendsto :
    ∀ ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
      Filter.Tendsto (fun t : α => continuumAction t ξ) l (nhds (limitAction ξ))

def CanonicalPeriodicFixedContinuumComparisonData.toRefinementFamily
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedContinuumComparisonData l Nx Ny Nz hx hy hz) :
    PeriodicFreudenthalRefinementFamily l
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) :=
  canonicalPeriodicEdgeStencilContinuumRefinementFamily
    Nx Ny Nz hx hy hz D.spacing D.spacing_pos D.spacing_tendsto_zero
    D.continuumAction D.errorConstant D.error_nonneg D.errorBound
    D.error_bound D.estimate

theorem CanonicalPeriodicFixedContinuumComparisonData.pointwise_regge_tendsto_limit
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedContinuumComparisonData l Nx Ny Nz hx hy hz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun _t : α =>
        reggeActionSecondOrder
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
          (canonicalReggeHessian
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
          ξ)
      l (nhds (D.limitAction ξ)) :=
  canonicalPeriodicEdgeStencilContinuumRefinementFamily_converges_to_fixed_limit
    Nx Ny Nz hx hy hz D.spacing D.spacing_pos D.spacing_tendsto_zero
    D.continuumAction D.errorConstant D.error_nonneg D.errorBound
    D.error_bound D.estimate D.limitAction ξ (D.continuum_tendsto ξ)

/-- Finite-probe aggregate version of the fixed-continuum comparison theorem.
This is the finite-dimensional precursor to the later pointwise-to-integral
lift in Track 1.B. -/
theorem CanonicalPeriodicFixedContinuumComparisonData.finite_probe_regge_tendsto_limit
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedContinuumComparisonData l Nx Ny Nz hx hy hz)
    {n : ℕ}
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun _t : α =>
        ∑ i : Fin n,
          reggeActionSecondOrder
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (canonicalReggeHessian
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
            (probe i))
      l (nhds (∑ i : Fin n, D.limitAction (probe i))) := by
  classical
  simpa using
    (tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (f := fun i (_t : α) =>
        reggeActionSecondOrder
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
          (canonicalReggeHessian
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
          (probe i))
      (a := fun i => D.limitAction (probe i))
      (by
        intro i _hi
        exact
          CanonicalPeriodicFixedContinuumComparisonData.pointwise_regge_tendsto_limit
            Nx Ny Nz hx hy hz D (probe i)))

/-- Weighted finite-probe aggregate convergence.  This is the Riemann-sum
shape needed for later integral approximations: finite probes with fixed
weights converge to the weighted fixed-continuum sum. -/
theorem CanonicalPeriodicFixedContinuumComparisonData.weighted_finite_probe_regge_tendsto_limit
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedContinuumComparisonData l Nx Ny Nz hx hy hz)
    {n : ℕ}
    (weight : Fin n → ℝ)
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun _t : α =>
        ∑ i : Fin n,
          weight i *
            reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (probe i))
      l (nhds (∑ i : Fin n, weight i * D.limitAction (probe i))) := by
  classical
  simpa using
    (tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (f := fun i (_t : α) =>
        weight i *
          reggeActionSecondOrder
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (canonicalReggeHessian
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
            (probe i))
      (a := fun i => weight i * D.limitAction (probe i))
      (by
        intro i _hi
        exact
          (tendsto_const_nhds.mul
            (CanonicalPeriodicFixedContinuumComparisonData.pointwise_regge_tendsto_limit
              Nx Ny Nz hx hy hz D (probe i)))))

/-- Variable-weight finite-probe aggregate convergence.  This is the mesh
quadrature shape: if the finite probe weights vary with the refinement
parameter but converge to fixed limiting weights, then the weighted Regge
aggregate converges to the weighted fixed-continuum aggregate. -/
theorem CanonicalPeriodicFixedContinuumComparisonData.variable_weighted_finite_probe_regge_tendsto_limit
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedContinuumComparisonData l Nx Ny Nz hx hy hz)
    {n : ℕ}
    (weight : α → Fin n → ℝ)
    (limitWeight : Fin n → ℝ)
    (hWeight :
      ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i)))
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun t : α =>
        ∑ i : Fin n,
          weight t i *
            reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (probe i))
      l (nhds (∑ i : Fin n, limitWeight i * D.limitAction (probe i))) := by
  classical
  simpa using
    (tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (f := fun i (t : α) =>
        weight t i *
          reggeActionSecondOrder
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (canonicalReggeHessian
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
            (probe i))
      (a := fun i => limitWeight i * D.limitAction (probe i))
      (by
        intro i _hi
        exact
          (hWeight i).mul
            (CanonicalPeriodicFixedContinuumComparisonData.pointwise_regge_tendsto_limit
              Nx Ny Nz hx hy hz D (probe i))))

/-- Fixed-weight finite-probe residual convergence.  This is the zero-error
form of the weighted aggregate theorem: the discrete weighted Regge sum minus
the fixed-continuum weighted sum vanishes along the refinement filter. -/
theorem CanonicalPeriodicFixedContinuumComparisonData.weighted_finite_probe_regge_residual_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedContinuumComparisonData l Nx Ny Nz hx hy hz)
    {n : ℕ}
    (weight : Fin n → ℝ)
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun _t : α =>
        (∑ i : Fin n,
          weight i *
            reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (probe i)) -
          ∑ i : Fin n, weight i * D.limitAction (probe i))
      l (nhds 0) := by
  classical
  have hConv :=
    CanonicalPeriodicFixedContinuumComparisonData.weighted_finite_probe_regge_tendsto_limit
      Nx Ny Nz hx hy hz D weight probe
  let limitSum : ℝ := ∑ i : Fin n, weight i * D.limitAction (probe i)
  have hConst : Filter.Tendsto (fun _t : α => limitSum) l (nhds limitSum) :=
    tendsto_const_nhds
  simpa [limitSum] using (hConv.sub hConst)

/-- Variable-weight finite-probe residual convergence.  This is the
Riemann-sum residual form needed for the later integral argument: if the
mesh-dependent weights converge, then the difference between the variable
weighted Regge aggregate and the limiting weighted continuum aggregate tends
to zero. -/
theorem CanonicalPeriodicFixedContinuumComparisonData.variable_weighted_finite_probe_regge_residual_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedContinuumComparisonData l Nx Ny Nz hx hy hz)
    {n : ℕ}
    (weight : α → Fin n → ℝ)
    (limitWeight : Fin n → ℝ)
    (hWeight :
      ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i)))
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun t : α =>
        (∑ i : Fin n,
          weight t i *
            reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (probe i)) -
          ∑ i : Fin n, limitWeight i * D.limitAction (probe i))
      l (nhds 0) := by
  classical
  have hConv :=
    CanonicalPeriodicFixedContinuumComparisonData.variable_weighted_finite_probe_regge_tendsto_limit
      Nx Ny Nz hx hy hz D weight limitWeight hWeight probe
  let limitSum : ℝ := ∑ i : Fin n, limitWeight i * D.limitAction (probe i)
  have hConst : Filter.Tendsto (fun _t : α => limitSum) l (nhds limitSum) :=
    tendsto_const_nhds
  simpa [limitSum] using (hConv.sub hConst)

/-- Candidate fixed physical Dirichlet/EH continuum action for the canonical
periodic Freudenthal comparison.  The type is intentionally just the action
functional on vertex potentials; the analytic burden is carried by the
comparison-data structures below. -/
abbrev CanonicalPeriodicFixedPhysicalContinuumAction
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :=
  VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K → ℝ

/-- Fixed-action specialization of the Track 1.B comparison data.  This is the
interface for the physical Dirichlet/EH step when the continuum action is
already fixed and only the spacing-dependent `C a^2` estimates remain to be
proved. -/
structure CanonicalPeriodicFixedPhysicalActionComparisonData
    {α : Type*} (l : Filter α)
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) where
  spacing : α → ℝ
  spacing_pos : ∀ t : α, 0 < spacing t
  spacing_tendsto_zero : Filter.Tendsto spacing l (nhds 0)
  fixedAction : CanonicalPeriodicFixedPhysicalContinuumAction Nx Ny Nz hx hy hz
  errorConstant : α → ℝ
  error_nonneg : ∀ t : α, 0 ≤ errorConstant t
  errorBound : ℝ
  error_bound : ∀ t : α, errorConstant t ≤ errorBound
  estimate :
    ∀ t : α,
      ∀ ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
        |reggeActionSecondOrder
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (canonicalReggeHessian
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
            ξ - fixedAction ξ| ≤ errorConstant t * spacing t ^ (2 : ℕ)

def CanonicalPeriodicFixedPhysicalActionComparisonData.toFixedContinuumComparisonData
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedPhysicalActionComparisonData l Nx Ny Nz hx hy hz) :
    CanonicalPeriodicFixedContinuumComparisonData l Nx Ny Nz hx hy hz where
  spacing := D.spacing
  spacing_pos := D.spacing_pos
  spacing_tendsto_zero := D.spacing_tendsto_zero
  continuumAction := fun _t => D.fixedAction
  errorConstant := D.errorConstant
  error_nonneg := D.error_nonneg
  errorBound := D.errorBound
  error_bound := D.error_bound
  estimate := D.estimate
  limitAction := D.fixedAction
  continuum_tendsto := by
    intro ξ
    exact tendsto_const_nhds

/-- Pointwise convergence to a fixed physical Dirichlet/EH action, once the
fixed-action `C a^2` estimates are supplied. -/
theorem CanonicalPeriodicFixedPhysicalActionComparisonData.pointwise_regge_tendsto_fixed_action
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedPhysicalActionComparisonData l Nx Ny Nz hx hy hz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun _t : α =>
        reggeActionSecondOrder
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
          (canonicalReggeHessian
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
          ξ)
      l (nhds (D.fixedAction ξ)) :=
  CanonicalPeriodicFixedContinuumComparisonData.pointwise_regge_tendsto_limit
    Nx Ny Nz hx hy hz
    (D.toFixedContinuumComparisonData Nx Ny Nz hx hy hz) ξ

/-- Fixed-weight finite-probe residual convergence specialized to a fixed
physical Dirichlet/EH action. -/
theorem CanonicalPeriodicFixedPhysicalActionComparisonData.weighted_finite_probe_residual_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedPhysicalActionComparisonData l Nx Ny Nz hx hy hz)
    {n : ℕ}
    (weight : Fin n → ℝ)
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun _t : α =>
        (∑ i : Fin n,
          weight i *
            reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (probe i)) -
          ∑ i : Fin n, weight i * D.fixedAction (probe i))
      l (nhds 0) :=
  CanonicalPeriodicFixedContinuumComparisonData.weighted_finite_probe_regge_residual_tendsto_zero
    Nx Ny Nz hx hy hz
    (D.toFixedContinuumComparisonData Nx Ny Nz hx hy hz)
    weight probe

/-- Variable-weight finite-probe residual convergence specialized to a fixed
physical Dirichlet/EH action.  This is the direct Riemann-sum hook for the
fixed-action comparison path. -/
theorem CanonicalPeriodicFixedPhysicalActionComparisonData.variable_weighted_finite_probe_residual_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedPhysicalActionComparisonData l Nx Ny Nz hx hy hz)
    {n : ℕ}
    (weight : α → Fin n → ℝ)
    (limitWeight : Fin n → ℝ)
    (hWeight :
      ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i)))
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun t : α =>
        (∑ i : Fin n,
          weight t i *
            reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (probe i)) -
          ∑ i : Fin n, limitWeight i * D.fixedAction (probe i))
      l (nhds 0) :=
  CanonicalPeriodicFixedContinuumComparisonData.variable_weighted_finite_probe_regge_residual_tendsto_zero
    Nx Ny Nz hx hy hz
    (D.toFixedContinuumComparisonData Nx Ny Nz hx hy hz)
    weight limitWeight hWeight probe

/-- The canonical fixed Dirichlet continuum action on the periodic Freudenthal
torus: flat Regge value plus one half of the concrete periodic edge-stencil
Dirichlet energy.  This is still the quadratic/Dirichlet continuum action, not
the full nonlinear Einstein-Hilbert theorem. -/
def canonicalPeriodicFixedDirichletContinuumAction
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicFixedPhysicalContinuumAction Nx Ny Nz hx hy hz :=
  fun ξ =>
    reggeAction
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (zeroPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) +
      (1 / 2) *
        periodicEdgeStencilDirichletAction
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) ξ

/-- The canonical second-order Regge action is exactly the fixed periodic
Dirichlet continuum action.  This closes the fixed Dirichlet action instance
of the comparison wrapper with zero error; it does not close the full
nonlinear EH convergence theorem. -/
theorem canonicalPeriodicFixedDirichletContinuumAction_eq_reggeSecondOrder
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz ξ =
      reggeActionSecondOrder
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalReggeHessian
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
        ξ := by
  unfold canonicalPeriodicFixedDirichletContinuumAction reggeActionSecondOrder
  rw [← canonicalPeriodicEdgeStencilTarget Nx Ny Nz hx hy hz ξ]
  rw [← canonicalReggeHessian_quadratic_eq_dirichlet
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
    ξ]

/-- Zero-error fixed-action comparison data for the canonical periodic
Dirichlet action along any positive spacing schedule tending to zero. -/
def canonicalPeriodicFixedDirichletActionComparisonData
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : α → ℝ) (ha : ∀ t : α, 0 < a t)
    (hSpacing : Filter.Tendsto a l (nhds 0)) :
    CanonicalPeriodicFixedPhysicalActionComparisonData l Nx Ny Nz hx hy hz where
  spacing := a
  spacing_pos := ha
  spacing_tendsto_zero := hSpacing
  fixedAction := canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz
  errorConstant := fun _t => 0
  error_nonneg := by
    intro t
    exact le_rfl
  errorBound := 0
  error_bound := by
    intro t
    exact le_rfl
  estimate := by
    intro t ξ
    rw [canonicalPeriodicFixedDirichletContinuumAction_eq_reggeSecondOrder]
    simp

/-- Pointwise convergence for the canonical fixed Dirichlet action instance.
The convergence is immediate because this fixed action is exactly the
second-order Regge action; the theorem packages that exact instance for the
same interface used by the later EH comparison. -/
theorem canonicalPeriodicFixedDirichletAction_pointwise_tendsto
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : α → ℝ) (ha : ∀ t : α, 0 < a t)
    (hSpacing : Filter.Tendsto a l (nhds 0))
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun _t : α =>
        reggeActionSecondOrder
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
          (canonicalReggeHessian
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
          ξ)
      l (nhds (canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz ξ)) :=
  CanonicalPeriodicFixedPhysicalActionComparisonData.pointwise_regge_tendsto_fixed_action
    Nx Ny Nz hx hy hz
    (canonicalPeriodicFixedDirichletActionComparisonData Nx Ny Nz hx hy hz a ha hSpacing)
    ξ

/-- Fixed-weight finite-probe residual convergence for the exact fixed
Dirichlet action instance. -/
theorem canonicalPeriodicFixedDirichletAction_weighted_finite_probe_residual_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : α → ℝ) (ha : ∀ t : α, 0 < a t)
    (hSpacing : Filter.Tendsto a l (nhds 0))
    {n : ℕ}
    (weight : Fin n → ℝ)
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun _t : α =>
        (∑ i : Fin n,
          weight i *
            reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (probe i)) -
          ∑ i : Fin n,
            weight i *
              canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz (probe i))
      l (nhds 0) :=
  CanonicalPeriodicFixedPhysicalActionComparisonData.weighted_finite_probe_residual_tendsto_zero
    Nx Ny Nz hx hy hz
    (canonicalPeriodicFixedDirichletActionComparisonData Nx Ny Nz hx hy hz a ha hSpacing)
    weight probe

/-- Variable-weight finite-probe residual convergence for the exact fixed
Dirichlet action instance. -/
theorem canonicalPeriodicFixedDirichletAction_variable_weighted_finite_probe_residual_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : α → ℝ) (ha : ∀ t : α, 0 < a t)
    (hSpacing : Filter.Tendsto a l (nhds 0))
    {n : ℕ}
    (weight : α → Fin n → ℝ)
    (limitWeight : Fin n → ℝ)
    (hWeight :
      ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i)))
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    Filter.Tendsto
      (fun t : α =>
        (∑ i : Fin n,
          weight t i *
            reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (probe i)) -
          ∑ i : Fin n,
            limitWeight i *
              canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz (probe i))
      l (nhds 0) :=
  CanonicalPeriodicFixedPhysicalActionComparisonData.variable_weighted_finite_probe_residual_tendsto_zero
    Nx Ny Nz hx hy hz
    (canonicalPeriodicFixedDirichletActionComparisonData Nx Ny Nz hx hy hz a ha hSpacing)
    weight limitWeight hWeight probe

/-- The local nonlinear Regge correspondence, rewritten against the fixed
Dirichlet action from the Track 1.B fixed-action pipeline. -/
theorem canonicalPeriodicNonlinearResidual_bound_to_fixedDirichlet
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
        ‖ξ‖ < r →
          ‖reggeAction
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              ξ -
            canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz ξ‖ ≤
            C * ‖ξ‖ ^ (3 : ℕ) := by
  rcases hLocal with ⟨r, C, hr, hC, hineq⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro ξ hξ
  have hResidual :
      reggeAction
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
          ξ -
        canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz ξ =
        reggeAction
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            ξ -
          reggeAction
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (zeroPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) -
          (1 / 2) *
            periodicEdgeStencilDirichletAction
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) ξ := by
    unfold canonicalPeriodicFixedDirichletContinuumAction
    ring
  rw [hResidual]
  exact hineq ξ hξ

/-- If a family of perturbations stays inside the local chart and its norm
tends to zero, then the full nonlinear Regge action converges to the fixed
Dirichlet quadratic action along that family.  This is a local nonlinear
residual statement, not the full EH continuum theorem. -/
theorem canonicalPeriodicNonlinearResidual_tendsto_zero_to_fixedDirichlet
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ ξ : α →
          VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
        (∀ t : α, ‖ξ t‖ < r) →
          Filter.Tendsto (fun t : α => ‖ξ t‖) l (nhds 0) →
            Filter.Tendsto
              (fun t : α =>
                ‖reggeAction
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (ξ t) -
                  canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz (ξ t)‖)
              l (nhds 0) := by
  rcases canonicalPeriodicNonlinearResidual_bound_to_fixedDirichlet
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hBound⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro ξ hSmall hNorm
  have hEnvelope :
      Filter.Tendsto (fun t : α => C * ‖ξ t‖ ^ (3 : ℕ)) l (nhds 0) := by
    have hcont : Continuous (fun x : ℝ => C * x ^ (3 : ℕ)) := by
      continuity
    have ht := hcont.tendsto (0 : ℝ)
    simpa using ht.comp hNorm
  apply squeeze_zero
  · intro t
    exact norm_nonneg _
  · intro t
    exact hBound (ξ t) (hSmall t)
  · exact hEnvelope

/-- Eventual-local-chart version of the nonlinear residual theorem.  The
perturbation family only has to be inside the local chart eventually along the
filter, which is the form needed for refinement limits. -/
theorem canonicalPeriodicNonlinearResidual_tendsto_zero_eventually_to_fixedDirichlet
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ ξ : α →
          VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
        (∀ᶠ t : α in l, ‖ξ t‖ < r) →
          Filter.Tendsto (fun t : α => ‖ξ t‖) l (nhds 0) →
            Filter.Tendsto
              (fun t : α =>
                ‖reggeAction
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (ξ t) -
                  canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz (ξ t)‖)
              l (nhds 0) := by
  rcases canonicalPeriodicNonlinearResidual_bound_to_fixedDirichlet
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hBound⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro ξ hSmallEventually hNorm
  have hEnvelope :
      Filter.Tendsto (fun t : α => C * ‖ξ t‖ ^ (3 : ℕ)) l (nhds 0) := by
    have hcont : Continuous (fun x : ℝ => C * x ^ (3 : ℕ)) := by
      continuity
    have ht := hcont.tendsto (0 : ℝ)
    simpa using ht.comp hNorm
  have hNonneg :
      ∀ᶠ t : α in l,
        0 ≤
          ‖reggeAction
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (ξ t) -
            canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz (ξ t)‖ :=
    Filter.Eventually.of_forall (fun t => norm_nonneg _)
  have hUpper :
      ∀ᶠ t : α in l,
        ‖reggeAction
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (ξ t) -
          canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz (ξ t)‖ ≤
          C * ‖ξ t‖ ^ (3 : ℕ) :=
    hSmallEventually.mono (fun t ht => hBound (ξ t) ht)
  exact squeeze_zero' hNonneg hUpper hEnvelope

/-- Scalar-amplitude specialization of the eventual-local nonlinear residual
theorem.  If a fixed perturbation direction is scaled by an amplitude tending
to zero, then the full nonlinear Regge residual against the fixed Dirichlet
quadratic action tends to zero. -/
theorem canonicalPeriodicNonlinearResidual_tendsto_zero_scaled_to_fixedDirichlet
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ (amp : α → ℝ)
        (probe :
          VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K),
        Filter.Tendsto amp l (nhds 0) →
          Filter.Tendsto
            (fun t : α =>
              ‖reggeAction
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                  (amp t • probe) -
                canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz
                  (amp t • probe)‖)
            l (nhds 0) := by
  rcases canonicalPeriodicNonlinearResidual_tendsto_zero_eventually_to_fixedDirichlet
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hResidual⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro amp probe hAmp
  let ξ : α →
      VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K :=
    fun t => amp t • probe
  have hNorm : Filter.Tendsto (fun t : α => ‖ξ t‖) l (nhds 0) := by
    have hAmpNorm : Filter.Tendsto (fun t : α => ‖amp t‖) l (nhds (0 : ℝ)) := by
      simpa using hAmp.norm
    have hMul :
        Filter.Tendsto (fun t : α => ‖amp t‖ * ‖probe‖) l
          (nhds ((0 : ℝ) * ‖probe‖)) :=
      hAmpNorm.mul tendsto_const_nhds
    simpa [ξ, norm_smul] using hMul
  have hSmallEventually : ∀ᶠ t : α in l, ‖ξ t‖ < r := by
    have hDist := (Metric.tendsto_nhds.mp hNorm) r hr
    exact hDist.mono (fun t ht => by
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg (ξ t))] using ht)
  simpa [ξ] using hResidual ξ hSmallEventually hNorm

/-- Spacing-amplitude specialization of the local nonlinear residual theorem.
If the scalar amplitude is the lattice spacing schedule itself and the spacing
tends to zero, then the nonlinear residual against the fixed Dirichlet action
tends to zero for every fixed perturbation direction. -/
theorem canonicalPeriodicNonlinearResidual_tendsto_zero_spacing_scaled_to_fixedDirichlet
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ (spacing : α → ℝ)
        (probe :
          VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K),
        Filter.Tendsto spacing l (nhds 0) →
          Filter.Tendsto
            (fun t : α =>
              ‖reggeAction
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                  (spacing t • probe) -
                canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz
                  (spacing t • probe)‖)
            l (nhds 0) := by
  rcases canonicalPeriodicNonlinearResidual_tendsto_zero_scaled_to_fixedDirichlet
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hScaled⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro spacing probe hSpacing
  exact hScaled spacing probe hSpacing

/-- Finite weighted aggregate of spacing-scaled nonlinear residuals.  This
packages the local nonlinear residual control in the finite Riemann-sum shape
needed before adding mesh-dependent weights. -/
theorem canonicalPeriodicNonlinearResidual_weighted_finite_probe_spacing_scaled_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : Fin n → ℝ),
        Filter.Tendsto spacing l (nhds 0) →
          Filter.Tendsto
            (fun t : α =>
              ∑ i : Fin n,
                weight i *
                  (reggeAction
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (spacing t • probe i) -
                  canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz
                    (spacing t • probe i)))
            l (nhds 0) := by
  classical
  rcases canonicalPeriodicNonlinearResidual_tendsto_zero_spacing_scaled_to_fixedDirichlet
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hScaled⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n spacing probe weight hSpacing
  simpa using
    (tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (f := fun i (t : α) =>
        weight i *
          (reggeAction
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (spacing t • probe i) -
          canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz
            (spacing t • probe i)))
      (a := fun _i => 0)
      (by
        intro i _hi
        have hNorm := hScaled spacing (probe i) hSpacing
        have hScalar :
            Filter.Tendsto
              (fun t : α =>
                reggeAction
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                  (spacing t • probe i) -
                canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz
                  (spacing t • probe i))
              l (nhds 0) := by
          apply tendsto_iff_dist_tendsto_zero.mpr
          simpa [Real.dist_eq] using hNorm
        simpa using hScalar.const_mul (weight i)))

/-- Variable-weight finite aggregate of spacing-scaled nonlinear residuals.
This is the mesh-quadrature version of the local nonlinear residual control:
if each finite weight converges to a fixed limiting weight, the weighted
nonlinear residual still tends to zero. -/
theorem canonicalPeriodicNonlinearResidual_variable_weighted_finite_probe_spacing_scaled_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            Filter.Tendsto
              (fun t : α =>
                ∑ i : Fin n,
                  weight t i *
                    (reggeAction
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                      (spacing t • probe i) -
                    canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz
                      (spacing t • probe i)))
              l (nhds 0) := by
  classical
  rcases canonicalPeriodicNonlinearResidual_tendsto_zero_spacing_scaled_to_fixedDirichlet
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hScaled⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n spacing probe weight limitWeight hWeight hSpacing
  simpa using
    (tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (f := fun i (t : α) =>
        weight t i *
          (reggeAction
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (spacing t • probe i) -
          canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz
            (spacing t • probe i)))
      (a := fun _i => 0)
      (by
        intro i _hi
        have hNorm := hScaled spacing (probe i) hSpacing
        have hScalar :
            Filter.Tendsto
              (fun t : α =>
                reggeAction
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                  (spacing t • probe i) -
                canonicalPeriodicFixedDirichletContinuumAction Nx Ny Nz hx hy hz
                  (spacing t • probe i))
              l (nhds 0) := by
          apply tendsto_iff_dist_tendsto_zero.mpr
          simpa [Real.dist_eq] using hNorm
        simpa using (hWeight i).mul hScalar))

/-- Variable-weight finite aggregate of the full nonlinear Regge residual
against the canonical second-order Regge action, for spacing-scaled probes.
This is the same local nonlinear residual as the fixed-Dirichlet theorem, with
the fixed Dirichlet action rewritten by its exact second-order Regge
identification. -/
theorem canonicalPeriodicNonlinearResidual_variable_weighted_finite_probe_spacing_scaled_to_secondOrder_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            Filter.Tendsto
              (fun t : α =>
                ∑ i : Fin n,
                  weight t i *
                    (reggeAction
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                      (spacing t • probe i) -
                    reggeActionSecondOrder
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                      (canonicalReggeHessian
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                      (spacing t • probe i)))
              l (nhds 0) := by
  rcases canonicalPeriodicNonlinearResidual_variable_weighted_finite_probe_spacing_scaled_tendsto_zero
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hDirichlet⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n spacing probe weight limitWeight hWeight hSpacing
  simpa [canonicalPeriodicFixedDirichletContinuumAction_eq_reggeSecondOrder]
    using hDirichlet spacing probe weight limitWeight hWeight hSpacing

/-- Aggregate-difference form of the variable-weight nonlinear residual against
the canonical second-order Regge action.  This is the form needed for the next
finite Riemann-sum composition step: the full nonlinear weighted aggregate and
the second-order weighted aggregate differ by a term tending to zero. -/
theorem canonicalPeriodicNonlinearAggregate_variable_weighted_finite_probe_spacing_scaled_to_secondOrder_residual_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            Filter.Tendsto
              (fun t : α =>
                (∑ i : Fin n,
                  weight t i *
                    reggeAction
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                      (spacing t • probe i)) -
                  ∑ i : Fin n,
                    weight t i *
                      reggeActionSecondOrder
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (canonicalReggeHessian
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                        (spacing t • probe i))
              l (nhds 0) := by
  rcases canonicalPeriodicNonlinearResidual_variable_weighted_finite_probe_spacing_scaled_to_secondOrder_tendsto_zero
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hResidual⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n spacing probe weight limitWeight hWeight hSpacing
  simpa [Finset.sum_sub_distrib, mul_sub] using
    hResidual spacing probe weight limitWeight hWeight hSpacing

/-- Scaled finite nonlinear residual against the canonical second-order Regge
action.  The cubic local remainder makes the residual divided by
`||spacing(t)||^2` tend to zero for spacing-scaled probes.  This is the first
nontrivial scaled interface after the unscaled aggregate-vanishing lemmas. -/
theorem canonicalPeriodicNonlinearResidual_variable_weighted_finite_probe_spacing_scaled_to_secondOrder_div_spacing_norm_sq_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      ((reggeAction
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (spacing t • probe i) -
                        reggeActionSecondOrder
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (canonicalReggeHessian
                            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                          (spacing t • probe i)) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l (nhds 0) := by
  classical
  rcases canonicalPeriodicNonlinearResidual_bound_to_fixedDirichlet
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hBound⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n spacing probe weight limitWeight hWeight hSpacing hSpacing_ne
  simpa using
    (tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (f := fun i (t : α) =>
        weight t i *
          ((reggeAction
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (spacing t • probe i) -
            reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (spacing t • probe i)) /
            ‖spacing t‖ ^ (2 : ℕ)))
      (a := fun _i => 0)
      (by
        intro i _hi
        have hScaledNorm :
            Filter.Tendsto
              (fun t : α => ‖spacing t • probe i‖) l (nhds 0) := by
          have hSpacingNorm :
              Filter.Tendsto (fun t : α => ‖spacing t‖) l (nhds (0 : ℝ)) := by
            simpa using hSpacing.norm
          have hMul :
              Filter.Tendsto (fun t : α => ‖spacing t‖ * ‖probe i‖) l
                (nhds ((0 : ℝ) * ‖probe i‖)) :=
            hSpacingNorm.mul tendsto_const_nhds
          simpa [norm_smul] using hMul
        have hSmallEventually : ∀ᶠ t : α in l, ‖spacing t • probe i‖ < r := by
          have hDist := (Metric.tendsto_nhds.mp hScaledNorm) r hr
          exact hDist.mono (fun t ht => by
            simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg (spacing t • probe i))] using ht)
        have hEnvelope :
            Filter.Tendsto
              (fun t : α => (C * ‖probe i‖ ^ (3 : ℕ)) * ‖spacing t‖)
              l (nhds 0) := by
          have hSpacingNorm :
              Filter.Tendsto (fun t : α => ‖spacing t‖) l (nhds (0 : ℝ)) := by
            simpa using hSpacing.norm
          simpa using (hSpacingNorm.const_mul (C * ‖probe i‖ ^ (3 : ℕ)))
        have hAbsTendsto :
            Filter.Tendsto
              (fun t : α =>
                |(reggeAction
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                      (spacing t • probe i) -
                    reggeActionSecondOrder
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                      (canonicalReggeHessian
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                      (spacing t • probe i)) /
                    ‖spacing t‖ ^ (2 : ℕ)|)
              l (nhds 0) := by
          have hNonneg :
              ∀ᶠ t : α in l,
                0 ≤
                  |(reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) -
                      reggeActionSecondOrder
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (canonicalReggeHessian
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                        (spacing t • probe i)) /
                      ‖spacing t‖ ^ (2 : ℕ)| :=
            Filter.Eventually.of_forall (fun t => abs_nonneg _)
          have hUpper :
              ∀ᶠ t : α in l,
                |(reggeAction
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                      (spacing t • probe i) -
                    reggeActionSecondOrder
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                      (canonicalReggeHessian
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                      (spacing t • probe i)) /
                    ‖spacing t‖ ^ (2 : ℕ)| ≤
                  (C * ‖probe i‖ ^ (3 : ℕ)) * ‖spacing t‖ :=
            (hSmallEventually.and hSpacing_ne).mono (fun t ht => by
              rcases ht with ⟨hsmall, hne⟩
              let residual : ℝ :=
                reggeAction
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (spacing t • probe i) -
                  reggeActionSecondOrder
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (canonicalReggeHessian
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                    (spacing t • probe i)
              have hb :
                  ‖residual‖ ≤ C * ‖spacing t • probe i‖ ^ (3 : ℕ) := by
                simpa [residual, canonicalPeriodicFixedDirichletContinuumAction_eq_reggeSecondOrder]
                  using hBound (spacing t • probe i) hsmall
              have hbAbs :
                  |residual| ≤ C * (‖spacing t‖ * ‖probe i‖) ^ (3 : ℕ) := by
                simpa [Real.norm_eq_abs, norm_smul] using hb
              have hnorm_ne : ‖spacing t‖ ≠ 0 := by
                intro hnorm
                exact hne (norm_eq_zero.mp hnorm)
              have hdenpos : 0 < ‖spacing t‖ ^ (2 : ℕ) :=
                sq_pos_of_ne_zero hnorm_ne
              calc
                |residual / ‖spacing t‖ ^ (2 : ℕ)|
                    = |residual| / ‖spacing t‖ ^ (2 : ℕ) := by
                      rw [abs_div, abs_of_pos hdenpos]
                _ ≤ (C * (‖spacing t‖ * ‖probe i‖) ^ (3 : ℕ)) /
                    ‖spacing t‖ ^ (2 : ℕ) := by
                      exact div_le_div_of_nonneg_right hbAbs hdenpos.le
                _ = (C * ‖probe i‖ ^ (3 : ℕ)) * ‖spacing t‖ := by
                      field_simp [hnorm_ne])
          exact squeeze_zero' hNonneg hUpper hEnvelope
        have hScalar :
            Filter.Tendsto
              (fun t : α =>
                (reggeAction
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (spacing t • probe i) -
                  reggeActionSecondOrder
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (canonicalReggeHessian
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                    (spacing t • probe i)) /
                  ‖spacing t‖ ^ (2 : ℕ))
              l (nhds 0) := by
          apply tendsto_iff_dist_tendsto_zero.mpr
          simpa only [Real.dist_eq, sub_zero] using hAbsTendsto
        simpa using (hWeight i).mul hScalar))

/-- Finite mesh-weighted scaled second-order aggregate convergence from
pointwise scaled second-order limits.  This is the finite Riemann-sum interface
for the quadratic layer: once each probe has a supplied continuum-normalized
limit after division by `||spacing(t)||^2`, convergent mesh weights give the
corresponding weighted finite aggregate limit. -/
theorem canonicalPeriodicSecondOrder_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    {n : ℕ}
    (spacing : α → ℝ)
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (weight : α → Fin n → ℝ)
    (limitWeight : Fin n → ℝ)
    (secondOrderLimit : Fin n → ℝ)
    (hWeight :
      ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i)))
    (hSecondOrder :
      ∀ i : Fin n,
        Filter.Tendsto
          (fun t : α =>
            reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (spacing t • probe i) /
              ‖spacing t‖ ^ (2 : ℕ))
          l (nhds (secondOrderLimit i))) :
    Filter.Tendsto
      (fun t : α =>
        ∑ i : Fin n,
          weight t i *
            (reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (spacing t • probe i) /
              ‖spacing t‖ ^ (2 : ℕ)))
      l (nhds (∑ i : Fin n, limitWeight i * secondOrderLimit i)) := by
  classical
  simpa using
    (tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (f := fun i (t : α) =>
        weight t i *
          (reggeActionSecondOrder
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
            (canonicalReggeHessian
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
            (spacing t • probe i) /
            ‖spacing t‖ ^ (2 : ℕ)))
      (a := fun i => limitWeight i * secondOrderLimit i)
      (by
        intro i _hi
        exact (hWeight i).mul (hSecondOrder i)))

/-- Flat-deficit zero target for the Regge flat background.  This is the exact
geometric input needed to normalize the flat Regge action to zero; the
remaining periodic-Freudenthal task is to prove this target from the canonical
flat geometry. -/
def FlatDeficitZeroTarget (K : Triangulation3D) : Prop :=
  ∀ e : Fin K.nE, deficitAngle K (zeroPotential K) e = 0

/-- Equivalent angle-sum form of flat zero deficit: the incident local
dihedral-angle contributions around each global edge sum to `2π`. -/
def FlatDeficitAngleSumTarget (K : Triangulation3D) : Prop :=
  ∀ e : Fin K.nE,
    (∑ τ : Fin K.nT, localDeficitAngleContribution K (zeroPotential K) e τ) =
      2 * Real.pi

/-- The incident-angle-sum target implies zero deficit by unfolding the Regge
deficit angle. -/
theorem flatDeficitZeroTarget_of_angleSum
    (K : Triangulation3D)
    (hSum : FlatDeficitAngleSumTarget K) :
    FlatDeficitZeroTarget K := by
  intro e
  unfold deficitAngle
  rw [hSum e]
  ring

/-- `FlatConfiguration` already contains the flat-deficit-zero field.  This
bridge lets the scaled finite-limit machinery consume the standard
flat-configuration package directly. -/
theorem FlatDeficitZeroTarget.of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    FlatDeficitZeroTarget K :=
  hFlat.flat_deficit_zero

/-- The `FlatDeficitZeroTarget` is definitionally the same condition as the
global zero-deficit input used by the smoothness/flat-configuration layer. -/
theorem flatDeficitZeroTarget_iff_globalZeroDeficitAtFlat
    (K : Triangulation3D) :
    FlatDeficitZeroTarget K ↔ GlobalZeroDeficitAtFlat K := by
  rfl

/-- Angle-sum form of the global zero-deficit input used by the smoothness
package. -/
theorem globalZeroDeficitAtFlat_of_angleSum
    (K : Triangulation3D)
    (hSum : FlatDeficitAngleSumTarget K) :
    GlobalZeroDeficitAtFlat K :=
  (flatDeficitZeroTarget_iff_globalZeroDeficitAtFlat K).1
    (flatDeficitZeroTarget_of_angleSum K hSum)

/-- Local Freudenthal dihedral angle for one tetrahedral edge slot, evaluated
on the canonical one-cube Freudenthal squared-edge tuple. -/
def freudenthalLocalDihedralAngle (f : Fin 6) : ℝ :=
  Geometry.DihedralDerivatives.dihedralAngle3Sq
    Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges f

/-- Contribution of one periodic cell/tetrahedron pair to the angle sum around
a typed periodic edge. -/
def canonicalPeriodicTypedEdgeAngleContribution
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz) : ℝ :=
  match canonicalEdgeSlot? edge cellTet.1 cellTet.2 with
  | some f => freudenthalLocalDihedralAngle f
  | none => 0

/-- Typed-edge version of the canonical periodic Freudenthal zero-deficit
angle-sum target.  This removes the anonymous finite edge encoder from the
next proof: it remains only to classify the incident cell/tetrahedron slots of
each typed periodic edge and evaluate their Freudenthal angles. -/
def CanonicalPeriodicTypedEdgeAngleSumTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] : Prop :=
  ∀ edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz,
    (∑ τ : Fin (Fintype.card (Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz)),
      canonicalPeriodicTypedEdgeAngleContribution edge (tetFinEquiv Nx Ny Nz τ)) =
      2 * Real.pi

/-- Direct typed-cell/tetrahedron version of the canonical periodic
Freudenthal angle-sum target.  This removes the `Fin` tetrahedron encoder from
the remaining incidence proof: the next step can classify the finite set of
typed pairs `(cell, localTet)` directly. -/
def CanonicalPeriodicDirectTypedEdgeAngleSumTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] : Prop :=
  ∀ edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz,
    (∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
      canonicalPeriodicTypedEdgeAngleContribution edge cellTet) =
      2 * Real.pi

/-- A typed periodic cell/tetrahedron pair is incident to a typed periodic edge
when the computable local edge-slot lookup finds a local slot. -/
def canonicalPeriodicTypedEdgeIncident
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz) : Prop :=
  (canonicalEdgeSlot? edge cellTet.1 cellTet.2).isSome = true

instance canonicalPeriodicTypedEdgeIncident_decidable
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz) :
    Decidable (canonicalPeriodicTypedEdgeIncident edge cellTet) := by
  unfold canonicalPeriodicTypedEdgeIncident
  infer_instance

/-- Witness form of typed edge incidence: a concrete local Freudenthal edge slot
`f` is found by `canonicalEdgeSlot?`.  This is the form needed for the finite
incident-star classification. -/
def canonicalPeriodicTypedEdgeIncidentSlotWitness
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz) : Prop :=
  ∃ f : Fin 6, canonicalEdgeSlot? edge cellTet.1 cellTet.2 = some f

instance canonicalPeriodicTypedEdgeIncidentSlotWitness_decidable
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz) :
    Decidable (canonicalPeriodicTypedEdgeIncidentSlotWitness edge cellTet) := by
  unfold canonicalPeriodicTypedEdgeIncidentSlotWitness
  infer_instance

/-- The boolean `isSome` incident predicate is exactly the existence of a local
Freudenthal edge-slot witness. -/
theorem canonicalPeriodicTypedEdgeIncident_iff_slotWitness
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz) :
    canonicalPeriodicTypedEdgeIncident edge cellTet ↔
      canonicalPeriodicTypedEdgeIncidentSlotWitness edge cellTet := by
  unfold canonicalPeriodicTypedEdgeIncident canonicalPeriodicTypedEdgeIncidentSlotWitness
  exact Option.isSome_iff_exists

/-- A concrete local-slot witness identifies the typed periodic edge as the
translated Freudenthal local edge for that cell and tetrahedron. -/
theorem canonicalPeriodicTypedEdge_eq_localEdgeOf_of_slotWitness
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz}
    {cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz}
    {f : Fin 6}
    (hSlot : canonicalEdgeSlot? edge cellTet.1 cellTet.2 = some f) :
    edge = localEdgeOf cellTet.1 cellTet.2 f :=
  canonicalEdgeSlot_eq_some_implies hSlot

/-- Once the local edge slot is known, the typed edge angle contribution is the
corresponding Freudenthal local dihedral angle. -/
theorem canonicalPeriodicTypedEdgeAngleContribution_eq_of_slot
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz}
    {cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz}
    {f : Fin 6}
    (hSlot : canonicalEdgeSlot? edge cellTet.1 cellTet.2 = some f) :
    canonicalPeriodicTypedEdgeAngleContribution edge cellTet =
      freudenthalLocalDihedralAngle f := by
  simp [canonicalPeriodicTypedEdgeAngleContribution, hSlot]

/-- Geometric witness form of typed edge incidence: the typed periodic edge is
exactly the translated local Freudenthal edge of a typed cell/tetrahedron pair. -/
def canonicalPeriodicTypedEdgeLocalEdgeOfWitness
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz) : Prop :=
  ∃ f : Fin 6, edge = localEdgeOf cellTet.1 cellTet.2 f

instance canonicalPeriodicTypedEdgeLocalEdgeOfWitness_decidable
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz) :
    Decidable (canonicalPeriodicTypedEdgeLocalEdgeOfWitness edge cellTet) := by
  unfold canonicalPeriodicTypedEdgeLocalEdgeOfWitness
  infer_instance

/-- The slot-witness and geometric `localEdgeOf` witness forms of typed
incidence are equivalent. -/
theorem canonicalPeriodicTypedEdgeIncidentSlotWitness_iff_localEdgeOf
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz) :
    canonicalPeriodicTypedEdgeIncidentSlotWitness edge cellTet ↔
      canonicalPeriodicTypedEdgeLocalEdgeOfWitness edge cellTet := by
  constructor
  · intro h
    rcases h with ⟨f, hSlot⟩
    exact ⟨f, canonicalEdgeSlot_eq_some_implies hSlot⟩
  · intro h
    rcases h with ⟨f, hEdge⟩
    refine ⟨f, ?_⟩
    exact canonicalEdgeSlot_eq_some_of_noDup
      (fun f g hg => canonicalPeriodicLocalEdgeNoDup Nx Ny Nz cellTet.1 cellTet.2 f g hg)
      hEdge

/-- A geometric `localEdgeOf` witness identifies the Freudenthal local angle
contributing to the typed periodic edge. -/
theorem canonicalPeriodicTypedEdgeAngleContribution_eq_of_localEdgeOf
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz}
    {cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz}
    {f : Fin 6}
    (hEdge : edge = localEdgeOf cellTet.1 cellTet.2 f) :
    canonicalPeriodicTypedEdgeAngleContribution edge cellTet =
      freudenthalLocalDihedralAngle f := by
  have hSlot : canonicalEdgeSlot? edge cellTet.1 cellTet.2 = some f :=
    canonicalEdgeSlot_eq_some_of_noDup
      (fun f g hg => canonicalPeriodicLocalEdgeNoDup Nx Ny Nz cellTet.1 cellTet.2 f g hg)
      hEdge
  exact canonicalPeriodicTypedEdgeAngleContribution_eq_of_slot hSlot

/-- A geometric `localEdgeOf` witness pins the typed periodic edge to the
positive displacement class of the underlying Freudenthal local edge slot. -/
theorem canonicalPeriodicTypedEdge_disp_eq_of_localEdgeOf
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz}
    {cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz}
    {f : Fin 6}
    (hEdge : edge = localEdgeOf cellTet.1 cellTet.2 f) :
    edge.disp = Geometry.PeriodicFreudenthalTorus.cubeEdgeDisp
      (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f) := by
  rw [hEdge]
  simp [localEdgeOf]

/-- A geometric `localEdgeOf` witness also pins the typed periodic edge's base
vertex to the translated base vertex of the underlying Freudenthal local edge. -/
theorem canonicalPeriodicTypedEdge_base_eq_of_localEdgeOf
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz}
    {cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz}
    {f : Fin 6}
    (hEdge : edge = localEdgeOf cellTet.1 cellTet.2 f) :
    edge.base = Geometry.PeriodicFreudenthalTorus.addVertexBits cellTet.1
      (Geometry.PeriodicFreudenthalTorus.cubeEdgeBase
        (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f)) := by
  rw [hEdge]
  simp [localEdgeOf]

/-- Equality with a translated local Freudenthal edge is exactly the pair of
typed periodic edge equations for base vertex and positive displacement. -/
theorem canonicalPeriodicTypedEdge_eq_localEdgeOf_iff_base_and_disp
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz)
    (f : Fin 6) :
    edge = localEdgeOf cellTet.1 cellTet.2 f ↔
      edge.base = addVertexBits cellTet.1
        (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f)) ∧
      edge.disp = cubeEdgeDisp
        (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f) := by
  constructor
  · intro hEdge
    exact ⟨canonicalPeriodicTypedEdge_base_eq_of_localEdgeOf hEdge,
      canonicalPeriodicTypedEdge_disp_eq_of_localEdgeOf hEdge⟩
  · intro h
    cases edge
    simp [localEdgeOf] at h ⊢
    exact h

/-- Each typed cell/tetrahedron contribution can be written as an explicit sum
over the six local Freudenthal edge slots, guarded by the geometric equality
`edge = localEdgeOf cell tet f`. -/
theorem canonicalPeriodicTypedEdgeAngleContribution_eq_sum_localSlots
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz) :
    canonicalPeriodicTypedEdgeAngleContribution edge cellTet =
      ∑ f : Fin 6,
        if edge = localEdgeOf cellTet.1 cellTet.2 f then
          freudenthalLocalDihedralAngle f else 0 := by
  classical
  cases hslot : canonicalEdgeSlot? edge cellTet.1 cellTet.2 with
  | none =>
      rw [Finset.sum_eq_zero]
      · simp [canonicalPeriodicTypedEdgeAngleContribution, hslot]
      · intro f _
        have hne : edge ≠ localEdgeOf cellTet.1 cellTet.2 f := by
          intro hEdge
          have hsome : canonicalEdgeSlot? edge cellTet.1 cellTet.2 = some f :=
            canonicalEdgeSlot_eq_some_of_noDup
              (fun f g hg =>
                canonicalPeriodicLocalEdgeNoDup Nx Ny Nz cellTet.1 cellTet.2 f g hg)
              hEdge
          rw [hslot] at hsome
          contradiction
        simp [hne]
  | some f =>
      have hEdge : edge = localEdgeOf cellTet.1 cellTet.2 f :=
        canonicalEdgeSlot_eq_some_implies hslot
      have hSlotLocal :
          canonicalEdgeSlot? (localEdgeOf cellTet.1 cellTet.2 f) cellTet.1 cellTet.2 =
            some f :=
        canonicalEdgeSlot_eq_some_of_noDup
          (fun f g hg =>
            canonicalPeriodicLocalEdgeNoDup Nx Ny Nz cellTet.1 cellTet.2 f g hg)
          rfl
      rw [Finset.sum_eq_single f]
      · simp [canonicalPeriodicTypedEdgeAngleContribution, hEdge, hSlotLocal]
      · intro g _ hg
        have hne : edge ≠ localEdgeOf cellTet.1 cellTet.2 g := by
          intro hEdgeG
          have hfg : f = g :=
            canonicalPeriodicLocalEdgeNoDup Nx Ny Nz cellTet.1 cellTet.2 f g
              (by rw [← hEdge, ← hEdgeG])
          exact hg hfg.symm
        simp [hne]
      · intro hf
        exact (hf (Finset.mem_univ f)).elim

/-- In the local-slot expansion, slots whose displacement class differs from
the typed edge's displacement class contribute zero and may be deleted. -/
theorem canonicalPeriodicLocalSlotSum_eq_dispFiltered
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz) :
    (∑ f : Fin 6,
        if edge = localEdgeOf cellTet.1 cellTet.2 f then
          freudenthalLocalDihedralAngle f else 0) =
      ∑ f ∈ (Finset.univ.filter
        (fun f : Fin 6 => edge.disp = cubeEdgeDisp
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))),
        if edge = localEdgeOf cellTet.1 cellTet.2 f then
          freudenthalLocalDihedralAngle f else 0 := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro f _
  by_cases hDisp :
      edge.disp = cubeEdgeDisp
        (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f)
  · simp [hDisp]
  · have hne : edge ≠ localEdgeOf cellTet.1 cellTet.2 f := by
      intro hEdge
      exact hDisp (canonicalPeriodicTypedEdge_disp_eq_of_localEdgeOf hEdge)
    simp [hDisp, hne]

/-- After filtering by displacement class, the remaining full edge equality
guard is equivalent to the base-vertex offset equation. -/
theorem canonicalPeriodicDispFilteredLocalSlotSum_eq_baseFiltered
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz) :
    (∑ f ∈ (Finset.univ.filter
        (fun f : Fin 6 => edge.disp = cubeEdgeDisp
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))),
        if edge = localEdgeOf cellTet.1 cellTet.2 f then
          freudenthalLocalDihedralAngle f else 0) =
      ∑ f ∈ (Finset.univ.filter
        (fun f : Fin 6 => edge.disp = cubeEdgeDisp
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))),
        if edge.base = addVertexBits cellTet.1
          (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f)) then
          freudenthalLocalDihedralAngle f else 0 := by
  classical
  refine Finset.sum_congr rfl ?_
  intro f hf
  have hDisp :
      edge.disp = cubeEdgeDisp
        (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f) :=
    (Finset.mem_filter.mp hf).2
  have hiff : (edge = localEdgeOf cellTet.1 cellTet.2 f) ↔
      edge.base = addVertexBits cellTet.1
        (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f)) := by
    constructor
    · intro hEdge
      exact canonicalPeriodicTypedEdge_base_eq_of_localEdgeOf hEdge
    · intro hBase
      exact (canonicalPeriodicTypedEdge_eq_localEdgeOf_iff_base_and_disp edge cellTet f).2
        ⟨hBase, hDisp⟩
  have hLocalBase :
      (localEdgeOf cellTet.1 cellTet.2 f).base =
        addVertexBits cellTet.1
          (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f)) := by
    simp [localEdgeOf]
  by_cases hBase :
      edge.base = addVertexBits cellTet.1
        (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))
  · have hEq : edge = localEdgeOf cellTet.1 cellTet.2 f := hiff.2 hBase
    simp [hEq, hLocalBase]
  · have hEq : edge ≠ localEdgeOf cellTet.1 cellTet.2 f := by
      intro hEdge
      exact hBase (hiff.1 hEdge)
    simp [hBase, hEq]

/-- Incident-filter version of the direct typed-cell/tetrahedron angle-sum
target.  All nonincident typed pairs have zero contribution, so the remaining
geometric proof can focus only on the finite incident star of each edge. -/
def CanonicalPeriodicIncidentFilteredEdgeAngleSumTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] : Prop :=
  ∀ edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz,
    (∑ cellTet ∈
      (Finset.univ.filter
        (fun cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz =>
          canonicalPeriodicTypedEdgeIncident edge cellTet)),
      canonicalPeriodicTypedEdgeAngleContribution edge cellTet) =
      2 * Real.pi

/-- `localEdgeOf`-filtered version of the incident angle-sum target.  This is
the purely geometric finite-star form: the remaining proof classifies exactly
which translated local Freudenthal edges equal a given typed periodic edge. -/
def CanonicalPeriodicLocalEdgeOfFilteredEdgeAngleSumTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] : Prop :=
  ∀ edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz,
    (∑ cellTet ∈
      (Finset.univ.filter
        (fun cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz =>
          canonicalPeriodicTypedEdgeLocalEdgeOfWitness edge cellTet)),
      canonicalPeriodicTypedEdgeAngleContribution edge cellTet) =
      2 * Real.pi

/-- Triple-sum version of the canonical periodic Freudenthal angle-sum target:
sum directly over typed cells, local tetrahedra, and local edge slots, with
nonmatching triples contributing zero. -/
def CanonicalPeriodicLocalSlotTripleAngleSumTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] : Prop :=
  ∀ edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz,
    (∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
      ∑ f : Fin 6,
        if edge = localEdgeOf cellTet.1 cellTet.2 f then
          freudenthalLocalDihedralAngle f else 0) =
      2 * Real.pi

/-- Displacement-filtered triple-sum target: for each typed periodic edge,
only local Freudenthal slots with the same positive displacement class are
enumerated. -/
def CanonicalPeriodicDispFilteredLocalSlotTripleAngleSumTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] : Prop :=
  ∀ edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz,
    (∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
      ∑ f ∈ (Finset.univ.filter
        (fun f : Fin 6 => edge.disp = cubeEdgeDisp
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))),
        if edge = localEdgeOf cellTet.1 cellTet.2 f then
          freudenthalLocalDihedralAngle f else 0) =
      2 * Real.pi

/-- Base-and-displacement filtered triple-sum target: displacement matching is
handled by the finite local-slot filter, and incidence is reduced to the
periodic base-vertex offset equation. -/
def CanonicalPeriodicBaseDispFilteredLocalSlotTripleAngleSumTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] : Prop :=
  ∀ edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz,
    (∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
      ∑ f ∈ (Finset.univ.filter
        (fun f : Fin 6 => edge.disp = cubeEdgeDisp
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))),
        if edge.base = addVertexBits cellTet.1
          (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f)) then
          freudenthalLocalDihedralAngle f else 0) =
      2 * Real.pi

/-- Local Freudenthal `(tet, edge-slot)` pairs.  This is the finite table left
after the periodic-cell base-offset equation has been isolated. -/
abbrev FreudenthalLocalPair := Fin 6 × Fin 6

/-- Positive displacement class of a local Freudenthal `(tet, edge-slot)` pair. -/
def freudenthalLocalPairDisp (pair : FreudenthalLocalPair) : Fin 7 :=
  cubeEdgeDisp (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2)

/-- The seven displacement-class fiber sizes in the one-cube Freudenthal local
edge-slot table.  Classes `0,1,2,6` have six local representatives; classes
`3,4,5` have four. -/
def freudenthalLocalDispMultiplicity : Fin 7 → ℕ
  | 0 => 6
  | 1 => 6
  | 2 => 6
  | 3 => 4
  | 4 => 4
  | 5 => 4
  | 6 => 6

/-- Explicit local Freudenthal `(tet, edge-slot)` fiber for each positive
displacement class. -/
def freudenthalLocalPairDispFiber : Fin 7 → Finset FreudenthalLocalPair
  | 0 => {((0 : Fin 6), (0 : Fin 6)), ((1 : Fin 6), (0 : Fin 6)),
    ((2 : Fin 6), (3 : Fin 6)), ((3 : Fin 6), (5 : Fin 6)),
    ((4 : Fin 6), (3 : Fin 6)), ((5 : Fin 6), (5 : Fin 6))}
  | 1 => {((0 : Fin 6), (3 : Fin 6)), ((1 : Fin 6), (5 : Fin 6)),
    ((2 : Fin 6), (0 : Fin 6)), ((3 : Fin 6), (0 : Fin 6)),
    ((4 : Fin 6), (5 : Fin 6)), ((5 : Fin 6), (3 : Fin 6))}
  | 2 => {((0 : Fin 6), (5 : Fin 6)), ((1 : Fin 6), (3 : Fin 6)),
    ((2 : Fin 6), (5 : Fin 6)), ((3 : Fin 6), (3 : Fin 6)),
    ((4 : Fin 6), (0 : Fin 6)), ((5 : Fin 6), (0 : Fin 6))}
  | 3 => {((0 : Fin 6), (1 : Fin 6)), ((2 : Fin 6), (1 : Fin 6)),
    ((4 : Fin 6), (4 : Fin 6)), ((5 : Fin 6), (4 : Fin 6))}
  | 4 => {((1 : Fin 6), (1 : Fin 6)), ((2 : Fin 6), (4 : Fin 6)),
    ((3 : Fin 6), (4 : Fin 6)), ((4 : Fin 6), (1 : Fin 6))}
  | 5 => {((0 : Fin 6), (4 : Fin 6)), ((1 : Fin 6), (4 : Fin 6)),
    ((3 : Fin 6), (1 : Fin 6)), ((5 : Fin 6), (1 : Fin 6))}
  | 6 => {((0 : Fin 6), (2 : Fin 6)), ((1 : Fin 6), (2 : Fin 6)),
    ((2 : Fin 6), (2 : Fin 6)), ((3 : Fin 6), (2 : Fin 6)),
    ((4 : Fin 6), (2 : Fin 6)), ((5 : Fin 6), (2 : Fin 6))}

/-- The explicit local displacement fiber table agrees with the computable
`freudenthalLocalPairDisp` filter. -/
theorem freudenthalLocalPairDispFiber_eq_filter (d : Fin 7) :
    freudenthalLocalPairDispFiber d =
      ((Finset.univ : Finset FreudenthalLocalPair).filter
        (fun pair => freudenthalLocalPairDisp pair = d)) := by
  fin_cases d <;> native_decide

/-- Freudenthal local angle attached to a local `(tet, edge-slot)` pair. -/
def freudenthalLocalPairAngle (pair : FreudenthalLocalPair) : ℝ :=
  freudenthalLocalDihedralAngle pair.2

/-- Symbolic local-angle sum template for each positive displacement class.
The first three axis classes receive two copies each of slots `0`, `3`, and
`5`; the face-diagonal classes receive two copies each of slots `1` and `4`;
the body-diagonal class receives six copies of slot `2`. -/
def freudenthalLocalDispAngleSumTemplate : Fin 7 → ℝ
  | 0 => 2 * freudenthalLocalDihedralAngle 0 +
    2 * freudenthalLocalDihedralAngle 3 +
    2 * freudenthalLocalDihedralAngle 5
  | 1 => 2 * freudenthalLocalDihedralAngle 0 +
    2 * freudenthalLocalDihedralAngle 3 +
    2 * freudenthalLocalDihedralAngle 5
  | 2 => 2 * freudenthalLocalDihedralAngle 0 +
    2 * freudenthalLocalDihedralAngle 3 +
    2 * freudenthalLocalDihedralAngle 5
  | 3 => 2 * freudenthalLocalDihedralAngle 1 +
    2 * freudenthalLocalDihedralAngle 4
  | 4 => 2 * freudenthalLocalDihedralAngle 1 +
    2 * freudenthalLocalDihedralAngle 4
  | 5 => 2 * freudenthalLocalDihedralAngle 1 +
    2 * freudenthalLocalDihedralAngle 4
  | 6 => 6 * freudenthalLocalDihedralAngle 2

/-- Exact symbolic local-angle sum over the explicit local-pair displacement
fiber. -/
theorem freudenthalLocalPairDispFiber_angle_sum (d : Fin 7) :
    (∑ pair ∈ freudenthalLocalPairDispFiber d, freudenthalLocalPairAngle pair) =
      freudenthalLocalDispAngleSumTemplate d := by
  fin_cases d <;>
    simp [freudenthalLocalPairDispFiber, freudenthalLocalPairAngle,
      freudenthalLocalDispAngleSumTemplate]
  all_goals ring_nf

/-- Exact symbolic local-angle sum over the computable local-pair displacement
filter. -/
theorem freudenthalLocalPairDisp_filter_angle_sum (d : Fin 7) :
    (∑ pair ∈ ((Finset.univ : Finset FreudenthalLocalPair).filter
      (fun pair => freudenthalLocalPairDisp pair = d)),
      freudenthalLocalPairAngle pair) =
      freudenthalLocalDispAngleSumTemplate d := by
  rw [← freudenthalLocalPairDispFiber_eq_filter d]
  exact freudenthalLocalPairDispFiber_angle_sum d

/-- Closed-form Schläfli coefficient for a local `(tet, slot)` pair and local
edge-slot direction `k`. -/
def freudenthalLocalPairClosedFormSchlaefliCoeff (pair : FreudenthalLocalPair) (k : Fin 6) : ℝ :=
  dihedralClosedDerivLength Geometry.FreudenthalCubeTriangulation.freudenthalTet pair.2 k

/-- Closed-form Schläfli coefficient as the evaluated rationalized summand. -/
theorem freudenthalLocalPairClosedFormSchlaefliCoeff_eq_snorm
    (pair : FreudenthalLocalPair) (k : Fin 6) :
    freudenthalLocalPairClosedFormSchlaefliCoeff pair k =
      schlaefliPolySummandNorm Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges pair.2 k *
        Real.sqrt (Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k) /
          (2 * Real.sqrt (Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges pair.2)) := by
  dsimp [freudenthalLocalPairClosedFormSchlaefliCoeff]
  exact FreudenthalLengthChainEndpointCert.freudenthalDihedralClosedDerivLength_snorm pair.2 k

/-- Closed-form Schläfli coefficient from the finite lookup table. -/
theorem freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table
    (pair : FreudenthalLocalPair) (k : Fin 6) :
    freudenthalLocalPairClosedFormSchlaefliCoeff pair k =
      FreudenthalLengthChainEndpointCert.freudenthalSchlaefliPolySummandNormTable pair.2 k *
        Real.sqrt (Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k) /
          (2 * Real.sqrt (Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges pair.2)) := by
  rw [freudenthalLocalPairClosedFormSchlaefliCoeff_eq_snorm,
    FreudenthalLengthChainEndpointCert.freudenthalSchlaefliPolySummandNorm_eq_table]

/-- Symbolic local length-chain summand for one Freudenthal local pair. -/
def freudenthalLocalPairLengthChainSummand (pair : FreudenthalLocalPair) (edgeLengthDir : Fin 6 → ℝ) : ℝ :=
  ∑ k : Fin 6, freudenthalLocalPairClosedFormSchlaefliCoeff pair k * edgeLengthDir k

theorem freudenthalLocalPairLengthChainSummand_eq_coeffDot
    (pair : FreudenthalLocalPair) (edgeLengthDir : Fin 6 → ℝ) :
    freudenthalLocalPairLengthChainSummand pair edgeLengthDir =
      ∑ k : Fin 6, freudenthalLocalPairClosedFormSchlaefliCoeff pair k * edgeLengthDir k := by
  rfl

/-- Symbolic local length-chain sum template for each positive displacement
class.  The caller supplies one conformal edge-length directional derivative
per local edge slot; specialization to the explicit periodic fiber uses
`freudenthalExplicitFiberDispLengthChainSumTemplate`. -/
def freudenthalLocalDispLengthChainSumTemplate (d : Fin 7) (edgeLengthDir : Fin 6 → ℝ) : ℝ :=
  ∑ pair ∈ freudenthalLocalPairDispFiber d, freudenthalLocalPairLengthChainSummand pair edgeLengthDir

/-- Exact symbolic local length-chain sum over the explicit local-pair
displacement fiber. -/
theorem freudenthalLocalPairDispFiber_lengthChain_sum (d : Fin 7) (edgeLengthDir : Fin 6 → ℝ) :
    (∑ pair ∈ freudenthalLocalPairDispFiber d, freudenthalLocalPairLengthChainSummand pair edgeLengthDir) =
      freudenthalLocalDispLengthChainSumTemplate d edgeLengthDir := by
  rfl

/-- Exact symbolic local length-chain sum over the computable local-pair
displacement filter. -/
theorem freudenthalLocalPairDisp_filter_lengthChain_sum (d : Fin 7) (edgeLengthDir : Fin 6 → ℝ) :
    (∑ pair ∈ ((Finset.univ : Finset FreudenthalLocalPair).filter
        (fun pair => freudenthalLocalPairDisp pair = d)),
      freudenthalLocalPairLengthChainSummand pair edgeLengthDir) =
      freudenthalLocalDispLengthChainSumTemplate d edgeLengthDir := by
  rw [← freudenthalLocalPairDispFiber_eq_filter d]
  exact freudenthalLocalPairDispFiber_lengthChain_sum d edgeLengthDir

/-- The base/displacement-filtered periodic cell/tet/slot sum collapses to the
one-cube local-pair displacement fiber sum.  For each matching local pair,
`sum_ite_eq_of_addVertexBits` supplies the unique periodic cell solving the
base-offset equation. -/
theorem canonicalPeriodicBaseDispFilteredLocalSlotTripleSum_eq_localPairDisp_filter_angle_sum
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    (∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
      ∑ f ∈ (Finset.univ.filter
        (fun f : Fin 6 => edge.disp = cubeEdgeDisp
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))),
        if edge.base = addVertexBits cellTet.1
          (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f)) then
          freudenthalLocalDihedralAngle f else 0) =
      (∑ pair ∈ ((Finset.univ : Finset FreudenthalLocalPair).filter
        (fun pair => freudenthalLocalPairDisp pair = edge.disp)),
        freudenthalLocalPairAngle pair) := by
  classical
  unfold Geometry.PeriodicFreudenthalTorus.PeriodicTet
  rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_comm]
  trans (∑ tet : Fin 6,
      ∑ f ∈ (Finset.univ.filter
        (fun f : Fin 6 => edge.disp = cubeEdgeDisp
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
        freudenthalLocalDihedralAngle f)
  · refine Finset.sum_congr rfl ?_
    intro tet _
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Vertex Nx Ny Nz)))
      (t := (Finset.univ.filter
        (fun f : Fin 6 => edge.disp = cubeEdgeDisp
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))))]
    refine Finset.sum_congr rfl ?_
    intro f _
    exact sum_ite_eq_of_addVertexBits
      (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))
      edge.base (freudenthalLocalDihedralAngle f)
  · unfold FreudenthalLocalPair freudenthalLocalPairDisp freudenthalLocalPairAngle
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_filter]
    rw [Finset.sum_product]
    simp [Finset.sum_filter, eq_comm]

/-- The base/displacement-filtered periodic cell/tet/slot sum is exactly the
symbolic Freudenthal local angle template for the typed edge's displacement
class.  The only remaining zero-deficit work is therefore the three explicit
template identities to `2π`. -/
theorem canonicalPeriodicBaseDispFilteredLocalSlotTripleSum_eq_angleTemplate
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    (∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
      ∑ f ∈ (Finset.univ.filter
        (fun f : Fin 6 => edge.disp = cubeEdgeDisp
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))),
        if edge.base = addVertexBits cellTet.1
          (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f)) then
          freudenthalLocalDihedralAngle f else 0) =
      freudenthalLocalDispAngleSumTemplate edge.disp := by
  rw [canonicalPeriodicBaseDispFilteredLocalSlotTripleSum_eq_localPairDisp_filter_angle_sum edge]
  exact freudenthalLocalPairDisp_filter_angle_sum edge.disp

/-- The final local Freudenthal angle identities needed after the periodic
cell-count collapse.  This is now the whole `2π` content of the
base/displacement-filtered zero-deficit target. -/
def FreudenthalLocalDispAngleTemplateTarget : Prop :=
  ∀ d : Fin 7, freudenthalLocalDispAngleSumTemplate d = 2 * Real.pi

/-- The three distinct local Freudenthal angle identities underlying the seven
positive displacement classes.  Axis classes share the first identity,
face-diagonal classes share the second, and the body-diagonal class is the
third. -/
def FreudenthalLocalThreeAngleIdentityTarget : Prop :=
  (2 * freudenthalLocalDihedralAngle 0 +
      2 * freudenthalLocalDihedralAngle 3 +
      2 * freudenthalLocalDihedralAngle 5 = 2 * Real.pi) ∧
    (2 * freudenthalLocalDihedralAngle 1 +
      2 * freudenthalLocalDihedralAngle 4 = 2 * Real.pi) ∧
    (6 * freudenthalLocalDihedralAngle 2 = 2 * Real.pi)

/-- Arithmetic simplification used by the Freudenthal cofactor-cosine values:
`sqrt 32 = 4 * sqrt 2`, hence `4 / sqrt 32 = sqrt 2 / 2`. -/
private theorem four_div_sqrt_thirty_two_eq_sqrt_two_div_two :
    (4 : ℝ) / Real.sqrt 32 = Real.sqrt 2 / 2 := by
  rw [show (32 : ℝ) = 16 * 2 by norm_num]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  have hsqrt16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)
  rw [hsqrt16]
  have hsqrt2_ne : Real.sqrt (2 : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  field_simp [hsqrt2_ne]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Exact cofactor-cosine values of the canonical Freudenthal tetrahedron's six
local dihedral angles. -/
theorem freudenthalLocalDihedralCos_eq (f : Fin 6) :
    Geometry.DihedralCayleyMenger.dihedralCos3Sq
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges f =
      match f with
      | 0 => Real.sqrt 2 / 2
      | 1 => 0
      | 2 => (1 / 2 : ℝ)
      | 3 => 0
      | 4 => 0
      | 5 => Real.sqrt 2 / 2 := by
  fin_cases f
  all_goals
    rw [Geometry.CofactorDerivatives.dihedralCos3Sq_eq_poly]
    unfold Geometry.CofactorDerivatives.dihedralCos3SqPoly
      Geometry.CofactorDerivatives.dihedralCofactorNumeratorPoly
      Geometry.CofactorDerivatives.dihedralDenom3Poly
    simp [Geometry.DihedralCayleyMenger.oppositeCMVertices]
    unfold Geometry.CofactorPolynomial.cmCofactor3Poly
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges
    norm_num
  · exact four_div_sqrt_thirty_two_eq_sqrt_two_div_two
  · exact four_div_sqrt_thirty_two_eq_sqrt_two_div_two

/-- Exact local dihedral angle values of the canonical Freudenthal tetrahedron:
`π/4`, `π/2`, `π/3`, `π/2`, `π/2`, `π/4`. -/
theorem freudenthalLocalDihedralAngle_eq (f : Fin 6) :
    freudenthalLocalDihedralAngle f =
      match f with
      | 0 => Real.pi / 4
      | 1 => Real.pi / 2
      | 2 => Real.pi / 3
      | 3 => Real.pi / 2
      | 4 => Real.pi / 2
      | 5 => Real.pi / 4 := by
  fin_cases f
  · unfold freudenthalLocalDihedralAngle Geometry.DihedralDerivatives.dihedralAngle3Sq
    rw [freudenthalLocalDihedralCos_eq]
    rw [← Real.cos_pi_div_four]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  · unfold freudenthalLocalDihedralAngle Geometry.DihedralDerivatives.dihedralAngle3Sq
    rw [freudenthalLocalDihedralCos_eq]
    exact Real.arccos_zero
  · unfold freudenthalLocalDihedralAngle Geometry.DihedralDerivatives.dihedralAngle3Sq
    rw [freudenthalLocalDihedralCos_eq]
    rw [← Real.cos_pi_div_three]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  · unfold freudenthalLocalDihedralAngle Geometry.DihedralDerivatives.dihedralAngle3Sq
    rw [freudenthalLocalDihedralCos_eq]
    exact Real.arccos_zero
  · unfold freudenthalLocalDihedralAngle Geometry.DihedralDerivatives.dihedralAngle3Sq
    rw [freudenthalLocalDihedralCos_eq]
    exact Real.arccos_zero
  · unfold freudenthalLocalDihedralAngle Geometry.DihedralDerivatives.dihedralAngle3Sq
    rw [freudenthalLocalDihedralCos_eq]
    rw [← Real.cos_pi_div_four]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])

/-- The three local Freudenthal angle identities close exactly. -/
theorem freudenthalLocalThreeAngleIdentityTarget :
    FreudenthalLocalThreeAngleIdentityTarget := by
  unfold FreudenthalLocalThreeAngleIdentityTarget
  have h0 := freudenthalLocalDihedralAngle_eq 0
  have h1 := freudenthalLocalDihedralAngle_eq 1
  have h2 := freudenthalLocalDihedralAngle_eq 2
  have h3 := freudenthalLocalDihedralAngle_eq 3
  have h4 := freudenthalLocalDihedralAngle_eq 4
  have h5 := freudenthalLocalDihedralAngle_eq 5
  constructor
  · rw [h0, h3, h5]
    ring
  constructor
  · rw [h1, h4]
    ring
  · rw [h2]
    ring

/-- The seven displacement-class angle-template identities reduce to the three
distinct Freudenthal local angle identities. -/
theorem freudenthalLocalDispAngleTemplateTarget_of_threeAngleIdentities
    (h : FreudenthalLocalThreeAngleIdentityTarget) :
    FreudenthalLocalDispAngleTemplateTarget := by
  intro d
  rcases h with ⟨hAxis, hFace, hBody⟩
  fin_cases d <;> simp [freudenthalLocalDispAngleSumTemplate, hAxis, hFace, hBody]

/-- The seven displacement-class angle-template identities for the canonical
Freudenthal tetrahedron. -/
theorem freudenthalLocalDispAngleTemplateTarget :
    FreudenthalLocalDispAngleTemplateTarget :=
  freudenthalLocalDispAngleTemplateTarget_of_threeAngleIdentities
    freudenthalLocalThreeAngleIdentityTarget

/-- Closed-form length-chain slot weight for one local Freudenthal pair:
`∂θ_e/∂L_k · √L_k` at the canonical Freudenthal tetrahedron. -/
noncomputable def freudenthalLocalPairClosedFormSlotWeight
    (pair : FreudenthalLocalPair) (k : Fin 6) : ℝ :=
  dihedralClosedDerivLength Geometry.FreudenthalCubeTriangulation.freudenthalTet pair.2 k *
    Real.sqrt (Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k)

/-- Per-displacement-class endpoint-template form of the explicit-fiber mixed
target: after the encoded closed-form fiber sum is identified with a function
`F d ξ₀ ξ₁` of the two endpoint potentials only, it must satisfy
`√s_d · (ξ₀+ξ₁)/2 · (-F d ξ₀ ξ₁) = √s_d · (ξ₀-ξ₁)²`. -/
def FreudenthalLocalDispLengthChainEndpointTemplateTarget
    (d : Fin 7) (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ ξ₀ ξ₁ : ℝ,
    Real.sqrt (periodicDispSqEdge d) * (ξ₀ + ξ₁) / 2 * (-F ξ₀ ξ₁) =
      Real.sqrt (periodicDispSqEdge d) * (ξ₀ - ξ₁) ^ (2 : ℕ)

/-- The three distinct local Freudenthal length-chain endpoint identities
underlying the seven positive displacement classes. -/
def FreudenthalLocalThreeLengthChainEndpointTemplateTarget
    (F : Fin 7 → ℝ → ℝ → ℝ) : Prop :=
  FreudenthalLocalDispLengthChainEndpointTemplateTarget 0 (F 0) ∧
    FreudenthalLocalDispLengthChainEndpointTemplateTarget 3 (F 3) ∧
    FreudenthalLocalDispLengthChainEndpointTemplateTarget 6 (F 6)

/-- The base/displacement-filtered periodic zero-deficit target follows from
the seven local displacement-class angle-template identities. -/
theorem canonicalPeriodicBaseDispFilteredLocalSlotTripleAngleSumTarget_of_localDispAngleTemplates
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hAngle : FreudenthalLocalDispAngleTemplateTarget) :
    CanonicalPeriodicBaseDispFilteredLocalSlotTripleAngleSumTarget Nx Ny Nz := by
  intro edge
  rw [canonicalPeriodicBaseDispFilteredLocalSlotTripleSum_eq_angleTemplate edge]
  exact hAngle edge.disp

/-- The base/displacement-filtered periodic zero-deficit target holds for the
canonical Freudenthal local angles. -/
theorem canonicalPeriodicBaseDispFilteredLocalSlotTripleAngleSumTarget_holds
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    CanonicalPeriodicBaseDispFilteredLocalSlotTripleAngleSumTarget Nx Ny Nz :=
  canonicalPeriodicBaseDispFilteredLocalSlotTripleAngleSumTarget_of_localDispAngleTemplates
    Nx Ny Nz freudenthalLocalDispAngleTemplateTarget

/-- Exact finite multiplicity table for the local Freudenthal edge slots by
positive displacement class. -/
theorem freudenthalLocalPairDisp_fiber_card (d : Fin 7) :
    ((Finset.univ : Finset FreudenthalLocalPair).filter
      (fun pair => freudenthalLocalPairDisp pair = d)).card =
      freudenthalLocalDispMultiplicity d := by
  fin_cases d <;> native_decide

/-- Every positive displacement class occurs among the local Freudenthal
edge slots. -/
theorem freudenthalLocalDispMultiplicity_pos (d : Fin 7) :
    0 < freudenthalLocalDispMultiplicity d := by
  fin_cases d <;> native_decide

/-- The seven local displacement-class multiplicities account for all
`6 × 6 = 36` local Freudenthal `(tet, edge-slot)` pairs. -/
theorem freudenthalLocalDispMultiplicity_sum :
    (∑ d : Fin 7, freudenthalLocalDispMultiplicity d) =
      Fintype.card FreudenthalLocalPair := by
  native_decide

/-- Slot-witness-filter version of the incident angle-sum target.  This names
the form in which every incident summand carries an explicit local edge slot
`f`. -/
def CanonicalPeriodicSlotWitnessFilteredEdgeAngleSumTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] : Prop :=
  ∀ edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz,
    (∑ cellTet ∈
      (Finset.univ.filter
        (fun cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz =>
          canonicalPeriodicTypedEdgeIncidentSlotWitness edge cellTet)),
      canonicalPeriodicTypedEdgeAngleContribution edge cellTet) =
      2 * Real.pi

/-- The slot-witness filtered angle-sum target implies the `isSome` incident
filtered target. -/
theorem canonicalPeriodicIncidentFilteredEdgeAngleSumTarget_of_slotWitnessFiltered
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hSlot :
      CanonicalPeriodicSlotWitnessFilteredEdgeAngleSumTarget Nx Ny Nz) :
    CanonicalPeriodicIncidentFilteredEdgeAngleSumTarget Nx Ny Nz := by
  intro edge
  have hFilter :
      (Finset.univ.filter
        (fun cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz =>
          canonicalPeriodicTypedEdgeIncident edge cellTet)) =
      (Finset.univ.filter
        (fun cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz =>
          canonicalPeriodicTypedEdgeIncidentSlotWitness edge cellTet)) := by
    ext cellTet
    simp [canonicalPeriodicTypedEdgeIncident_iff_slotWitness edge cellTet]
  rw [hFilter]
  exact hSlot edge

/-- The geometric `localEdgeOf` filtered target implies the slot-witness
filtered target. -/
theorem canonicalPeriodicSlotWitnessFilteredEdgeAngleSumTarget_of_localEdgeOfFiltered
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hLocal :
      CanonicalPeriodicLocalEdgeOfFilteredEdgeAngleSumTarget Nx Ny Nz) :
    CanonicalPeriodicSlotWitnessFilteredEdgeAngleSumTarget Nx Ny Nz := by
  intro edge
  have hFilter :
      (Finset.univ.filter
        (fun cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz =>
          canonicalPeriodicTypedEdgeIncidentSlotWitness edge cellTet)) =
      (Finset.univ.filter
        (fun cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz =>
          canonicalPeriodicTypedEdgeLocalEdgeOfWitness edge cellTet)) := by
    ext cellTet
    simp [canonicalPeriodicTypedEdgeIncidentSlotWitness_iff_localEdgeOf edge cellTet]
  rw [hFilter]
  exact hLocal edge

/-- The explicit triple-sum target implies the direct typed cell/tetrahedron
angle-sum target. -/
theorem canonicalPeriodicDirectTypedEdgeAngleSumTarget_of_localSlotTriple
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hTriple : CanonicalPeriodicLocalSlotTripleAngleSumTarget Nx Ny Nz) :
    CanonicalPeriodicDirectTypedEdgeAngleSumTarget Nx Ny Nz := by
  intro edge
  calc
    (∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
        canonicalPeriodicTypedEdgeAngleContribution edge cellTet)
        =
      ∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
        ∑ f : Fin 6,
          if edge = localEdgeOf cellTet.1 cellTet.2 f then
            freudenthalLocalDihedralAngle f else 0 := by
        refine Finset.sum_congr rfl ?_
        intro cellTet _
        exact canonicalPeriodicTypedEdgeAngleContribution_eq_sum_localSlots edge cellTet
    _ = 2 * Real.pi := hTriple edge

/-- The displacement-filtered triple-sum target implies the raw local-slot
triple-sum target because displacement-mismatched slots cannot equal the typed
edge. -/
theorem canonicalPeriodicLocalSlotTripleAngleSumTarget_of_dispFiltered
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hDisp :
      CanonicalPeriodicDispFilteredLocalSlotTripleAngleSumTarget Nx Ny Nz) :
    CanonicalPeriodicLocalSlotTripleAngleSumTarget Nx Ny Nz := by
  intro edge
  calc
    (∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
      ∑ f : Fin 6,
        if edge = localEdgeOf cellTet.1 cellTet.2 f then
          freudenthalLocalDihedralAngle f else 0) =
      (∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
        ∑ f ∈ (Finset.univ.filter
          (fun f : Fin 6 => edge.disp = cubeEdgeDisp
            (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))),
          if edge = localEdgeOf cellTet.1 cellTet.2 f then
            freudenthalLocalDihedralAngle f else 0) := by
        refine Finset.sum_congr rfl ?_
        intro cellTet _
        exact canonicalPeriodicLocalSlotSum_eq_dispFiltered edge cellTet
    _ = 2 * Real.pi := hDisp edge

/-- The base-and-displacement filtered target implies the displacement-filtered
target because, within a displacement class, full edge equality is equivalent
to the base-offset equation. -/
theorem canonicalPeriodicDispFilteredLocalSlotTripleAngleSumTarget_of_baseDispFiltered
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hBase :
      CanonicalPeriodicBaseDispFilteredLocalSlotTripleAngleSumTarget Nx Ny Nz) :
    CanonicalPeriodicDispFilteredLocalSlotTripleAngleSumTarget Nx Ny Nz := by
  intro edge
  calc
    (∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
      ∑ f ∈ (Finset.univ.filter
        (fun f : Fin 6 => edge.disp = cubeEdgeDisp
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))),
        if edge = localEdgeOf cellTet.1 cellTet.2 f then
          freudenthalLocalDihedralAngle f else 0) =
      (∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
        ∑ f ∈ (Finset.univ.filter
          (fun f : Fin 6 => edge.disp = cubeEdgeDisp
            (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))),
          if edge.base = addVertexBits cellTet.1
            (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f)) then
            freudenthalLocalDihedralAngle f else 0) := by
        refine Finset.sum_congr rfl ?_
        intro cellTet _
        exact canonicalPeriodicDispFilteredLocalSlotSum_eq_baseFiltered edge cellTet
    _ = 2 * Real.pi := hBase edge

/-- The incident-filter angle-sum target implies the direct typed target because
nonincident typed cell/tetrahedron pairs contribute zero. -/
theorem canonicalPeriodicDirectTypedEdgeAngleSumTarget_of_incidentFiltered
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hIncident : CanonicalPeriodicIncidentFilteredEdgeAngleSumTarget Nx Ny Nz) :
    CanonicalPeriodicDirectTypedEdgeAngleSumTarget Nx Ny Nz := by
  intro edge
  have hAllToFilter :
      (∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
        canonicalPeriodicTypedEdgeAngleContribution edge cellTet) =
      ∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
        if canonicalPeriodicTypedEdgeIncident edge cellTet then
          canonicalPeriodicTypedEdgeAngleContribution edge cellTet else 0 := by
    refine Finset.sum_congr rfl ?_
    intro cellTet _
    by_cases hInc : canonicalPeriodicTypedEdgeIncident edge cellTet
    · simp [hInc]
    · have hnone : canonicalEdgeSlot? edge cellTet.1 cellTet.2 = none := by
        unfold canonicalPeriodicTypedEdgeIncident at hInc
        cases hslot : canonicalEdgeSlot? edge cellTet.1 cellTet.2 with
        | none => rfl
        | some f => simp [hslot] at hInc
      simp [canonicalPeriodicTypedEdgeAngleContribution, hnone, hInc]
  have hFilter :
      (∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
        if canonicalPeriodicTypedEdgeIncident edge cellTet then
          canonicalPeriodicTypedEdgeAngleContribution edge cellTet else 0) =
      ∑ cellTet ∈
        (Finset.univ.filter
          (fun cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz =>
            canonicalPeriodicTypedEdgeIncident edge cellTet)),
        canonicalPeriodicTypedEdgeAngleContribution edge cellTet := by
    rw [Finset.sum_filter]
  rw [hAllToFilter, hFilter]
  exact hIncident edge

/-- The direct typed-cell/tetrahedron angle-sum target implies the typed-edge
target with the canonical tetrahedron finite-index encoder. -/
theorem canonicalPeriodicTypedEdgeAngleSumTarget_of_directTyped
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hDirect : CanonicalPeriodicDirectTypedEdgeAngleSumTarget Nx Ny Nz) :
    CanonicalPeriodicTypedEdgeAngleSumTarget Nx Ny Nz := by
  intro edge
  have hReindex :
      (∑ τ : Fin (Fintype.card (Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz)),
        canonicalPeriodicTypedEdgeAngleContribution edge (tetFinEquiv Nx Ny Nz τ)) =
        ∑ cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz,
          canonicalPeriodicTypedEdgeAngleContribution edge cellTet :=
    Fintype.sum_equiv (tetFinEquiv Nx Ny Nz)
      (fun τ : Fin (Fintype.card (Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz)) =>
        canonicalPeriodicTypedEdgeAngleContribution edge (tetFinEquiv Nx Ny Nz τ))
      (fun cellTet : Geometry.PeriodicFreudenthalTorus.PeriodicTet Nx Ny Nz =>
        canonicalPeriodicTypedEdgeAngleContribution edge cellTet)
      (fun _τ => rfl)
  rw [hReindex]
  exact hDirect edge

/-- The displacement-filtered local-slot triple target holds for the canonical
Freudenthal local angles. -/
theorem canonicalPeriodicDispFilteredLocalSlotTripleAngleSumTarget_holds
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    CanonicalPeriodicDispFilteredLocalSlotTripleAngleSumTarget Nx Ny Nz :=
  canonicalPeriodicDispFilteredLocalSlotTripleAngleSumTarget_of_baseDispFiltered
    Nx Ny Nz
    (canonicalPeriodicBaseDispFilteredLocalSlotTripleAngleSumTarget_holds
      Nx Ny Nz)

/-- The raw local-slot triple target holds for the canonical Freudenthal local
angles. -/
theorem canonicalPeriodicLocalSlotTripleAngleSumTarget_holds
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    CanonicalPeriodicLocalSlotTripleAngleSumTarget Nx Ny Nz :=
  canonicalPeriodicLocalSlotTripleAngleSumTarget_of_dispFiltered
    Nx Ny Nz
    (canonicalPeriodicDispFilteredLocalSlotTripleAngleSumTarget_holds
      Nx Ny Nz)

/-- The direct typed edge angle-sum target holds for the canonical Freudenthal
local angles. -/
theorem canonicalPeriodicDirectTypedEdgeAngleSumTarget_holds
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    CanonicalPeriodicDirectTypedEdgeAngleSumTarget Nx Ny Nz :=
  canonicalPeriodicDirectTypedEdgeAngleSumTarget_of_localSlotTriple
    Nx Ny Nz
    (canonicalPeriodicLocalSlotTripleAngleSumTarget_holds Nx Ny Nz)

/-- The typed-edge angle-sum target holds for the canonical Freudenthal local
angles. -/
theorem canonicalPeriodicTypedEdgeAngleSumTarget_holds
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz] :
    CanonicalPeriodicTypedEdgeAngleSumTarget Nx Ny Nz :=
  canonicalPeriodicTypedEdgeAngleSumTarget_of_directTyped
    Nx Ny Nz
    (canonicalPeriodicDirectTypedEdgeAngleSumTarget_holds Nx Ny Nz)

/-- Canonical periodic Freudenthal zero-deficit target, sharpened to the exact
incident local edge slots.  The remaining geometric task is to prove this sum:
for every encoded periodic edge, the Freudenthal dihedral angles contributed by
all incident tetrahedra add to `2π`. -/
def CanonicalPeriodicZeroDeficitAngleSumTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ e : Fin P.K.nE,
    (∑ τ : Fin P.K.nT,
      match P.K.edgeInTet e τ with
      | some f => freudenthalLocalDihedralAngle f
      | none => 0) =
      2 * Real.pi

/-- The typed-edge angle-sum target implies the canonical encoded
finite-index target. -/
theorem canonicalPeriodicZeroDeficitAngleSumTarget_of_typedEdgeAngleSum
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hTyped : CanonicalPeriodicTypedEdgeAngleSumTarget Nx Ny Nz) :
    CanonicalPeriodicZeroDeficitAngleSumTarget Nx Ny Nz hx hy hz := by
  intro e
  have h := hTyped (edgeFinEquiv Nx Ny Nz e)
  simpa [CanonicalPeriodicTypedEdgeAngleSumTarget,
    canonicalPeriodicTypedEdgeAngleContribution,
    CanonicalPeriodicZeroDeficitAngleSumTarget,
    canonicalEncodedPeriodicFreudenthalTorus,
    canonicalEncodedPeriodicFreudenthalTorus_of_endpoint,
    canonicalEncodedPeriodicFreudenthalTorus_of_incidence,
    canonicalPeriodicTriangulation,
    canonicalEdgeInTet] using h

/-- The canonical encoded zero-deficit angle-sum target holds for the
periodic Freudenthal torus. -/
theorem canonicalPeriodicZeroDeficitAngleSumTarget_holds
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicZeroDeficitAngleSumTarget Nx Ny Nz hx hy hz :=
  canonicalPeriodicZeroDeficitAngleSumTarget_of_typedEdgeAngleSum
    Nx Ny Nz hx hy hz
    (canonicalPeriodicTypedEdgeAngleSumTarget_holds Nx Ny Nz)

/-- The canonical incident-angle-sum target is exactly the flat
`localDeficitAngleContribution` sum after evaluating the conformal chart at the
zero potential. -/
theorem canonicalPeriodicFlatDeficitAngleSumTarget_of_incidentAngleSum
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hSum : CanonicalPeriodicZeroDeficitAngleSumTarget Nx Ny Nz hx hy hz) :
    FlatDeficitAngleSumTarget
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K := by
  intro e
  have h := hSum e
  simpa [CanonicalPeriodicZeroDeficitAngleSumTarget,
    FlatDeficitAngleSumTarget,
    localDeficitAngleContribution,
    tetDihedralAngleUnderConformal,
    conformalTetSqEdges_zero,
    canonicalEncodedPeriodicFreudenthalTorus,
    canonicalEncodedPeriodicFreudenthalTorus_of_endpoint,
    canonicalEncodedPeriodicFreudenthalTorus_of_incidence,
    canonicalPeriodicTriangulation] using h

/-- Canonical periodic Freudenthal flat-deficit zero, reduced to the exact
incident Freudenthal dihedral-angle sum. -/
theorem canonicalPeriodicFlatDeficitZeroTarget_of_incidentAngleSum
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hSum : CanonicalPeriodicZeroDeficitAngleSumTarget Nx Ny Nz hx hy hz) :
    FlatDeficitZeroTarget
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K :=
  flatDeficitZeroTarget_of_angleSum
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalPeriodicFlatDeficitAngleSumTarget_of_incidentAngleSum
      Nx Ny Nz hx hy hz hSum)

/-- The global zero-deficit input for the canonical periodic Freudenthal torus,
reduced to the exact incident Freudenthal dihedral-angle sum. -/
theorem canonicalPeriodicGlobalZeroDeficitAtFlat_of_incidentAngleSum
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hSum : CanonicalPeriodicZeroDeficitAngleSumTarget Nx Ny Nz hx hy hz) :
    GlobalZeroDeficitAtFlat
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K :=
  globalZeroDeficitAtFlat_of_angleSum
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalPeriodicFlatDeficitAngleSumTarget_of_incidentAngleSum
      Nx Ny Nz hx hy hz hSum)

/-- Canonical periodic Freudenthal flat-deficit zero. -/
theorem canonicalPeriodicFlatDeficitZeroTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    FlatDeficitZeroTarget
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K :=
  canonicalPeriodicFlatDeficitZeroTarget_of_incidentAngleSum
    Nx Ny Nz hx hy hz
    (canonicalPeriodicZeroDeficitAngleSumTarget_holds Nx Ny Nz hx hy hz)

/-- Canonical periodic Freudenthal global zero-deficit at the flat
configuration. -/
theorem canonicalPeriodicGlobalZeroDeficitAtFlat
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    GlobalZeroDeficitAtFlat
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K :=
  canonicalPeriodicGlobalZeroDeficitAtFlat_of_incidentAngleSum
    Nx Ny Nz hx hy hz
    (canonicalPeriodicZeroDeficitAngleSumTarget_holds Nx Ny Nz hx hy hz)

/-- If every flat deficit angle vanishes, then the Regge action at the flat
potential is zero.  This is the finite-sum reduction behind the flat-action
zero input used by the scaled quadratic normalization layer. -/
theorem reggeAction_zeroPotential_eq_zero_of_flatDeficit
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hDeficit : FlatDeficitZeroTarget K) :
    reggeAction K hK (zeroPotential K) = 0 := by
  unfold reggeAction
  apply Finset.sum_eq_zero
  intro e _he
  rw [hDeficit e, mul_zero]

/-- Canonical periodic-Freudenthal flat-action normalization, reduced exactly to
flat deficit zero on the encoded periodic torus. -/
theorem canonicalPeriodicReggeAction_zeroPotential_eq_zero_of_flatDeficit
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hDeficit :
      FlatDeficitZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    reggeAction
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (zeroPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) = 0 :=
  reggeAction_zeroPotential_eq_zero_of_flatDeficit
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
    hDeficit

/-- Flat-action normalization from the standard flat-configuration package. -/
theorem reggeAction_zeroPotential_eq_zero_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    reggeAction K hK (zeroPotential K) = 0 :=
  reggeAction_zeroPotential_eq_zero_of_flatDeficit K hK
    (FlatDeficitZeroTarget.of_flatConfiguration K hK hFlat)

/-- Canonical periodic-Freudenthal flat-action normalization from the standard
flat-configuration package. -/
theorem canonicalPeriodicReggeAction_zeroPotential_eq_zero_of_flatConfiguration
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFlat :
      FlatConfiguration
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK) :
    reggeAction
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (zeroPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) = 0 :=
  canonicalPeriodicReggeAction_zeroPotential_eq_zero_of_flatDeficit
    Nx Ny Nz hx hy hz
    (FlatDeficitZeroTarget.of_flatConfiguration
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
      hFlat)

/-- The exact remaining data needed to build the canonical periodic
`FlatConfiguration`: a local analytic chart for the encoded Freudenthal torus
and global zero-deficit at the flat potential.  Smoothness is not included
because it is already constructed from the local chart by
`reggeActionContDiffFromLocalChart_of_localChart`. -/
structure CanonicalPeriodicFlatConfigurationInputs
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) where
  localChart :
    LocalAnalyticFlatChart
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
  global_zero_deficit :
    GlobalZeroDeficitAtFlat
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K

/-- The local analytic chart for the canonical periodic Freudenthal torus
reduces to a single realized nondegenerate copy of the one-cube Freudenthal
tetrahedron, since every encoded periodic tetrahedron is the same local
Freudenthal tetrahedron. -/
def canonicalPeriodicLocalAnalyticFlatChart_of_realizedFreudenthalTet
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (T : Geometry.AffineIndepInterior.RealizedNonDegenerateTet)
    (hT : T.tet = Geometry.FreudenthalCubeTriangulation.freudenthalTet) :
    LocalAnalyticFlatChart
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K where
  realizedTet := fun _τ => T
  realizes_tet := by
    intro τ
    rw [hT]
    rfl

/-- Build the realized nondegenerate Freudenthal tetrahedron package from a
concrete Euclidean realization whose six squared edges match the one-cube
Freudenthal edge tuple. -/
def realizedFreudenthalTet_of_sqEdgeOfPoints
    (R : Geometry.TetrahedronRealization.RealizedTet)
    (hSq :
      Geometry.TetrahedronRealization.sqEdgeOfPoints R =
        Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges) :
    Geometry.AffineIndepInterior.RealizedNonDegenerateTet where
  tet := Geometry.FreudenthalCubeTriangulation.freudenthalTet
  realization := R
  realizes := by
    rw [hSq]
    rfl

/-- Explicit Euclidean coordinates for the one-cube Freudenthal tetrahedron
with vertices `(0,0,0)`, `(1,0,0)`, `(1,1,0)`, and `(1,1,1)`.  In the
tetrahedral edge order this gives squared lengths `(1,2,3,1,2,1)`. -/
def freudenthalRealizationPoints : Fin 4 → EuclideanSpace ℝ (Fin 3)
  | 0 => 0
  | 1 => EuclideanSpace.single 0 (1 : ℝ)
  | 2 => EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 : ℝ)
  | 3 =>
      EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 : ℝ) +
        EuclideanSpace.single 2 (1 : ℝ)

/-- Reindex the three nonzero vertices of the Freudenthal tetrahedron by
`Fin 3`, sending `0,1,2` to vertices `1,2,3`. -/
private def freudenthalNonzeroVertexEquiv : Fin 3 ≃ {j : Fin 4 // j ≠ 0} where
  toFun i := ⟨i.succ, Fin.succ_ne_zero i⟩
  invFun j := j.1.pred j.2
  left_inv i := Fin.pred_succ i
  right_inv j := Subtype.ext (Fin.succ_pred j.1 j.2)

/-- The explicit one-cube Freudenthal tetrahedron coordinates are affinely
independent.  After reindexing the nonzero vertices, the coordinate matrix is
upper triangular with diagonal entries `1`. -/
theorem freudenthalRealizationPoints_affineIndependent :
    AffineIndependent ℝ freudenthalRealizationPoints := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ freudenthalRealizationPoints (0 : Fin 4)]
  apply (linearIndependent_equiv freudenthalNonzeroVertexEquiv).mp
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hcoord := congrArg (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)) hg
  simp [freudenthalNonzeroVertexEquiv, freudenthalRealizationPoints, Fin.sum_univ_three] at hcoord
  have h2 := congrFun hcoord (2 : Fin 3)
  have h1 := congrFun hcoord (1 : Fin 3)
  have h0 := congrFun hcoord (0 : Fin 3)
  fin_cases i <;> simp at h0 h1 h2 ⊢ <;> linarith

/-- The explicit Freudenthal coordinates as a `RealizedTet`, once affine
independence of the four points is supplied. -/
def freudenthalRealizedTet_of_affineIndependent
    (hAffine : AffineIndependent ℝ freudenthalRealizationPoints) :
    Geometry.TetrahedronRealization.RealizedTet where
  p := freudenthalRealizationPoints
  nondegenerate := hAffine

/-- The explicit coordinate realization has the Freudenthal squared-edge tuple.
This leaves only affine independence as the local geometric proof needed to
build a `RealizedTet`. -/
theorem freudenthalRealizedTet_of_affineIndependent_sqEdgeOfPoints
    (hAffine : AffineIndependent ℝ freudenthalRealizationPoints) :
    Geometry.TetrahedronRealization.sqEdgeOfPoints
        (freudenthalRealizedTet_of_affineIndependent hAffine) =
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges := by
  funext e
  fin_cases e <;>
    simp [freudenthalRealizedTet_of_affineIndependent, freudenthalRealizationPoints,
      Geometry.TetrahedronRealization.sqEdgeOfPoints,
      Geometry.TetrahedronRealization.vertexSqDist,
      Geometry.TetrahedronRealization.edgeVector,
      Geometry.TetrahedronRealization.edgeVertices3,
      Geometry.ReggeRigorousFoundation.edgeVertices,
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges,
      EuclideanSpace.norm_sq_eq, Fin.sum_univ_three] <;>
    norm_num

/-- The explicit Freudenthal coordinate tetrahedron, with affine independence
proved from the triangular coordinate matrix. -/
def freudenthalRealizedTet : Geometry.TetrahedronRealization.RealizedTet :=
  freudenthalRealizedTet_of_affineIndependent freudenthalRealizationPoints_affineIndependent

/-- The fully explicit coordinate realization has the Freudenthal squared-edge
tuple, with no remaining affine-independence hypothesis. -/
theorem freudenthalRealizedTet_sqEdgeOfPoints :
    Geometry.TetrahedronRealization.sqEdgeOfPoints freudenthalRealizedTet =
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges :=
  freudenthalRealizedTet_of_affineIndependent_sqEdgeOfPoints
    freudenthalRealizationPoints_affineIndependent

/-- Package the two geometric inputs for canonical periodic flatness after the
local analytic chart has been reduced to one realized Freudenthal tetrahedron.
The remaining global input is the zero-deficit angle sum around each encoded
periodic edge. -/
def canonicalPeriodicFlatConfigurationInputs_of_realizedFreudenthalTet_zeroDeficit
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (T : Geometry.AffineIndepInterior.RealizedNonDegenerateTet)
    (hT : T.tet = Geometry.FreudenthalCubeTriangulation.freudenthalTet)
    (hZero :
      GlobalZeroDeficitAtFlat
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    CanonicalPeriodicFlatConfigurationInputs Nx Ny Nz hx hy hz where
  localChart :=
    canonicalPeriodicLocalAnalyticFlatChart_of_realizedFreudenthalTet
      Nx Ny Nz hx hy hz T hT
  global_zero_deficit := hZero

/-- Construct the canonical periodic flat configuration from its two geometric
inputs. -/
def CanonicalPeriodicFlatConfigurationInputs.toFlatConfiguration
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {hx : 2 < Nx} {hy : 2 < Ny} {hz : 2 < Nz}
    (I : CanonicalPeriodicFlatConfigurationInputs Nx Ny Nz hx hy hz) :
    FlatConfiguration
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK :=
  flatConfiguration_of_localChart_zeroDeficit
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
    I.localChart
    I.global_zero_deficit
    (reggeActionContDiffFromLocalChart_of_localChart
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
      I.localChart)

/-- Direct canonical periodic flat configuration from one realized Freudenthal
tetrahedron plus global zero-deficit. -/
def canonicalPeriodicFlatConfiguration_of_realizedFreudenthalTet_zeroDeficit
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (T : Geometry.AffineIndepInterior.RealizedNonDegenerateTet)
    (hT : T.tet = Geometry.FreudenthalCubeTriangulation.freudenthalTet)
    (hZero :
      GlobalZeroDeficitAtFlat
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    FlatConfiguration
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK :=
  (canonicalPeriodicFlatConfigurationInputs_of_realizedFreudenthalTet_zeroDeficit
    Nx Ny Nz hx hy hz T hT hZero).toFlatConfiguration

/-- Canonical periodic flat-configuration inputs with both geometric sides
discharged: the local chart comes from the explicit Freudenthal coordinate
tetrahedron and global zero deficit comes from the certified periodic
angle-sum chain. -/
def canonicalPeriodicFlatConfigurationInputs
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicFlatConfigurationInputs Nx Ny Nz hx hy hz :=
  canonicalPeriodicFlatConfigurationInputs_of_realizedFreudenthalTet_zeroDeficit
    Nx Ny Nz hx hy hz
    (realizedFreudenthalTet_of_sqEdgeOfPoints
      freudenthalRealizedTet freudenthalRealizedTet_sqEdgeOfPoints)
    rfl
    (canonicalPeriodicGlobalZeroDeficitAtFlat Nx Ny Nz hx hy hz)

/-- Canonical periodic Freudenthal flat configuration, with no remaining local
chart or global zero-deficit input. -/
def canonicalPeriodicFlatConfiguration
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    FlatConfiguration
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK :=
  (canonicalPeriodicFlatConfigurationInputs Nx Ny Nz hx hy hz).toFlatConfiguration

/-- Periodic edge-stencil local correspondence from the canonical flat
configuration plus the two standard remainder jets. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalFlat_and_remainderJets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFirst :
      ReggeActionRemainderFirstVariationInput
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalReggeHessian
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK))
    (hSecond :
      ReggeActionRemainderSecondVariationInput
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_flat_and_remainderJets
    Nx Ny Nz hx hy hz
    (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz)
    hFirst hSecond

/-- Periodic edge-stencil local correspondence from canonical flatness, the
remainder first-variation jet, and the nonlinear directional Hessian theorem. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalFlat_first_and_directionalHessian
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFirst :
      ReggeActionRemainderFirstVariationInput
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalReggeHessian
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK))
    (hHessian :
      NonlinearReggeDirectionalHessianTheorem
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_flat_first_and_directionalHessian
    Nx Ny Nz hx hy hz
    (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz)
    hFirst hHessian

/-- Periodic edge-stencil local correspondence from the standard first-variation
package and the nonlinear directional Hessian theorem.  The separate remainder
first-variation jet is derived from the full first-variation input by
`reggeActionRemainderFirstVariationInput_of_firstVariation`. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalFlat_firstVariationInput_and_directionalHessian
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFirst :
      ReggeActionFirstVariationInput
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hHessian :
      NonlinearReggeDirectionalHessianTheorem
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  exact canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalFlat_first_and_directionalHessian
    Nx Ny Nz hx hy hz
    (reggeActionRemainderFirstVariationInput_of_firstVariation
      P.K P.hK
      (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz)
      (canonicalReggeHessian P.K P.hK)
      hFirst)
    hHessian

/-- Periodic edge-stencil local correspondence from the standard first-variation
package plus the two lower-level geometric Hessian inputs.  This replaces the
nonlinear directional Hessian theorem by the already-proved reduction through
weighted deficit-derivative eventual zero and mixed hinge-deficit edge-stencil
equality. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalFlat_firstVariationInput_eventuallyZero_and_edgeStencil
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFirst :
      ReggeActionFirstVariationInput
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (D : DeficitAngleDirectionalDerivativePackage
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixed :
      MixedHingeDeficitEdgeStencilTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        D) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  exact
    canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalFlat_firstVariationInput_and_directionalHessian
      Nx Ny Nz hx hy hz hFirst
      (nonlinearDirectionalHessian_of_eventuallyZero_and_edgeStencil
        P.K P.hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz)
        D hZero hMixed
        (canonicalPeriodicEdgeStencilTarget Nx Ny Nz hx hy hz))

/-- Standard Regge first variation for the canonical periodic Freudenthal torus.
The input is discharged by the encoded periodic edge-slot partition. -/
def canonicalPeriodicFirstVariationInput
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    ReggeActionFirstVariationInput
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
      (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz) :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  reggeActionFirstVariationInput_of_edgeSlotPartition P.K P.hK
    (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz)
    (edgeSlotPartition_of_encodedPeriodicFreudenthalTorus P)

/-- Periodic edge-stencil local correspondence from only the two remaining
geometric Hessian-side inputs.  Canonical flatness, first variation, edge-stencil
Dirichlet equality, and the Taylor/remainder first-variation bridges are all
supplied by preceding theorems. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_eventuallyZero_and_edgeStencilTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : DeficitAngleDirectionalDerivativePackage
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixed :
      MixedHingeDeficitEdgeStencilTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        D) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalFlat_firstVariationInput_eventuallyZero_and_edgeStencil
    Nx Ny Nz hx hy hz
    (canonicalPeriodicFirstVariationInput Nx Ny Nz hx hy hz)
    D hZero hMixed

/-- Canonical local angle chain-rule package for the periodic Freudenthal torus. -/
def canonicalPeriodicLocalAngleLengthChainRulePackage
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    LocalAngleLengthChainRulePackage
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  localAngleLengthChainRulePackage_of_sqEdge P.K P.hK
    (localAngleSqEdgeChainRulePackage_of_flat P.K P.hK
      (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))

/-- Canonical local dihedral-angle derivative package for the periodic
Freudenthal torus. -/
def canonicalPeriodicLocalDihedralDerivativePackage
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    LocalDihedralDirectionalDerivativePackage
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  localDihedralDirectionalDerivativePackage_of_lengthChain P.K P.hK
    (canonicalPeriodicLocalAngleLengthChainRulePackage Nx Ny Nz hx hy hz)

/-- Canonical deficit-derivative package for the periodic Freudenthal torus.
It is built from the flat local angle chain rule and the encoded periodic
edge-slot partition, so the deficit package is no longer arbitrary in the
canonical Track 1.B branch. -/
def canonicalPeriodicDeficitDerivativePackage
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    DeficitAngleDirectionalDerivativePackage
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  let L := canonicalPeriodicLocalAngleLengthChainRulePackage Nx Ny Nz hx hy hz
  let A := canonicalPeriodicLocalDihedralDerivativePackage Nx Ny Nz hx hy hz
  deficitPackage_of_conformalSchlaefliCancellation P.K P.hK A
    (conformalSchlaefliCancellation_of_lengthChain_of_bookkeeping P.K P.hK L
      (conformalSchlaefliIncidenceBookkeeping_of_edgeSlotBookkeeping P.K P.hK A
        (edgeSlotBookkeeping_of_encodedPeriodicFreudenthalTorus P)))

theorem canonicalPeriodicDeficitDerivativePackage_deficitDeriv
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ :
      VertexPotential
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (e : Fin (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K.nE) :
    (canonicalPeriodicDeficitDerivativePackage Nx Ny Nz hx hy hz).deficitDeriv ξ e =
      deficitDirectionalDerivFromLocalAngles
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalPeriodicLocalDihedralDerivativePackage Nx Ny Nz hx hy hz)
        ξ e := by
  rfl

/-- Local-angle finite-sum form of the canonical mixed hinge-deficit target. -/
def CanonicalPeriodicMixedHingeDeficitLocalAngleTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ ξ : VertexPotential P.K,
    (∑ e : Fin P.K.nE,
      hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        deficitDirectionalDerivFromLocalAngles P.K
          (canonicalPeriodicLocalDihedralDerivativePackage Nx Ny Nz hx hy hz) ξ e) =
      canonicalEdgeStencilDirichletEnergy P.K P.hK ξ

/-- Length-chain finite-sum form of the canonical mixed hinge-deficit target.
This unfolds the canonical local dihedral derivative package to the explicit
`localAngleLengthChainDeriv` sum over incident tetrahedron slots. -/
def CanonicalPeriodicMixedHingeDeficitLengthChainTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ ξ : VertexPotential P.K,
    (∑ e : Fin P.K.nE,
      hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ τ : Fin P.K.nT,
          match P.K.edgeInTet e τ with
          | none => 0
          | some f => localAngleLengthChainDeriv P.K P.hK ξ τ f)) =
      canonicalEdgeStencilDirichletEnergy P.K P.hK ξ

/-- Corrected Session 202 mixed hinge-deficit target.  The exact finite audit
shows the mixed length-chain quadratic matches the rational axis stencil, not
the full seven-class square-root edge stencil used by the older target above. -/
def CanonicalPeriodicMixedHingeDeficitAxisStencilTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ ξ : VertexPotential P.K,
    (∑ e : Fin P.K.nE,
      hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ τ : Fin P.K.nT,
          match P.K.edgeInTet e τ with
          | none => 0
          | some f => localAngleLengthChainDeriv P.K P.hK ξ τ f)) =
      canonicalPeriodicMixedAxisStencilAction Nx Ny Nz hx hy hz ξ

/-- Fully expanded finite-sum form of the canonical mixed hinge-deficit target.
This exposes the local Schläfli derivative coefficients and the conformal
local edge-length directional derivatives. -/
def CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ ξ : VertexPotential P.K,
    (∑ e : Fin P.K.nE,
      hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ τ : Fin P.K.nT,
          match P.K.edgeInTet e τ with
          | none => 0
          | some f =>
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k)) =
      canonicalEdgeStencilDirichletEnergy P.K P.hK ξ

/-- Per-edge form of the expanded mixed hinge-deficit target.  This is the
finite local identity that remains before summing over global edges. -/
def CanonicalPeriodicMixedHingeDeficitExpandedLengthChainPerEdgeTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (e : Fin P.K.nE),
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ τ : Fin P.K.nT,
          match P.K.edgeInTet e τ with
          | none => 0
          | some f =>
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k) =
      Real.sqrt (P.hK.globalSqEdge e) *
        (ξ (P.K.edgeVerts e).1 - ξ (P.K.edgeVerts e).2) ^ (2 : ℕ)

/-- Typed periodic-edge form of the expanded per-edge mixed target.  This
removes the anonymous `Fin nE` edge index from the remaining local identity. -/
def CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEdgeTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ τ : Fin P.K.nT,
          match P.K.edgeInTet e τ with
          | none => 0
          | some f =>
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k) =
      Real.sqrt (P.hK.globalSqEdge e) *
        (ξ (P.K.edgeVerts e).1 - ξ (P.K.edgeVerts e).2) ^ (2 : ℕ)

/-- Typed endpoint form of the expanded mixed target.  The right-hand side is
now written directly from the typed periodic edge displacement and endpoints. -/
def CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ τ : Fin P.K.nT,
          match P.K.edgeInTet e τ with
          | none => 0
          | some f =>
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k) =
      Real.sqrt (periodicDispSqEdge edge.disp) *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

/-- Typed slot-guarded form of the expanded mixed target.  This replaces
`edgeInTet` by an explicit six-slot guarded sum using the typed equation
`edge = localEdgeOf cell tet f`. -/
def CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedSlotTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ τ : Fin P.K.nT,
          ∑ f : Fin 6,
            if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k
            else 0) =
      Real.sqrt (periodicDispSqEdge edge.disp) *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

/-- Displacement-filtered form of the typed slot-guarded mixed target.  Local
slots whose positive displacement differs from the typed edge cannot contribute. -/
def CanonicalPeriodicMixedHingeDeficitExpandedLengthChainDispFilteredTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ τ : Fin P.K.nT,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f))),
            if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k
            else 0) =
      Real.sqrt (periodicDispSqEdge edge.disp) *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

/-- Base-and-displacement-filtered form of the expanded mixed target.  After
the displacement filter, the remaining edge-equality guard is equivalent to a
periodic base-offset equation. -/
def CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispFilteredTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ τ : Fin P.K.nT,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f))),
            if edge.base = addVertexBits (P.tetEquiv τ).1
                (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f)) then
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k
            else 0) =
      Real.sqrt (periodicDispSqEdge edge.disp) *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

/-- Typed-cell/tetrahedron form of the base-and-displacement-filtered mixed
target.  This removes the anonymous `Fin nT` tetrahedron index. -/
def CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispTypedTetTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ cellTet : PeriodicTet Nx Ny Nz,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))),
            if edge.base = addVertexBits cellTet.1
                (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f)) then
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm cellTet)).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm cellTet) k
            else 0) =
      Real.sqrt (periodicDispSqEdge edge.disp) *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

/-- Product-split version of the typed-tetrahedron mixed target.  The sum over
`PeriodicTet = Vertex × Fin 6` is written as an explicit cell sum followed by a
local-tetrahedron sum. -/
def CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispCellTetTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ cell : Vertex Nx Ny Nz,
          ∑ tet : Fin 6,
            ∑ f ∈ (Finset.univ.filter
              (fun f : Fin 6 => edge.disp = cubeEdgeDisp
                (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
              if edge.base = addVertexBits cell
                  (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f)) then
                ∑ k : Fin 6,
                  ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                    (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
                    localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k
              else 0) =
      Real.sqrt (periodicDispSqEdge edge.disp) *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

/-- The unique periodic cell whose translated local base vertex equals a target
base vertex. -/
noncomputable def periodicMatchingBaseCell
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (a : Fin 8) (target : Vertex Nx Ny Nz) : Vertex Nx Ny Nz :=
  Classical.choose (existsUnique_addVertexBits_eq a target)

theorem periodicMatchingBaseCell_spec
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (a : Fin 8) (target : Vertex Nx Ny Nz) :
    target = addVertexBits (periodicMatchingBaseCell a target) a :=
  (Classical.choose_spec (existsUnique_addVertexBits_eq a target)).1

theorem periodicMatchingBaseCell_unique
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (a : Fin 8) (target : Vertex Nx Ny Nz)
    {cell : Vertex Nx Ny Nz}
    (h : target = addVertexBits cell a) :
    cell = periodicMatchingBaseCell a target :=
  (Classical.choose_spec (existsUnique_addVertexBits_eq a target)).2 cell h

/-- Collapse a finite sum over periodic cells guarded by a base-offset equation
to the unique matching cell. -/
theorem sum_ite_eq_of_addVertexBits_apply
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (a : Fin 8) (target : Vertex Nx Ny Nz)
    (F : Vertex Nx Ny Nz → ℝ) :
    (∑ cell : Vertex Nx Ny Nz,
      if target = addVertexBits cell a then F cell else 0) =
      F (periodicMatchingBaseCell a target) := by
  classical
  rw [Finset.sum_eq_single (periodicMatchingBaseCell a target)]
  · rw [if_pos (periodicMatchingBaseCell_spec a target)]
  · intro cell _ hne
    have hnot : target ≠ addVertexBits cell a := by
      intro h
      exact hne (periodicMatchingBaseCell_unique a target h)
    simp [hnot]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- Local-pair form of the base/displacement-filtered mixed target.  The
periodic cell sum has been collapsed to the unique cell solving the base-offset
equation for each local pair. -/
def CanonicalPeriodicMixedHingeDeficitExpandedLengthChainLocalPairTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ tet : Fin 6,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
              let cell :=
                periodicMatchingBaseCell
                  (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))
                  edge.base
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k) =
      Real.sqrt (periodicDispSqEdge edge.disp) *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

/-- Single-filtered-local-pair form of the mixed target.  This is the same
local-pair content as `CanonicalPeriodicMixedHingeDeficitExpandedLengthChainLocalPairTarget`,
but written over the explicit displacement fiber of `FreudenthalLocalPair`. -/
def CanonicalPeriodicMixedHingeDeficitExpandedLengthChainLocalPairFiberTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ pair ∈ ((Finset.univ : Finset FreudenthalLocalPair).filter
          (fun pair => freudenthalLocalPairDisp pair = edge.disp)),
              let cell :=
                periodicMatchingBaseCell
                  (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2))
                  edge.base
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm (cell, pair.1))).dihedralDeriv pair.2 k *
                  localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, pair.1)) k) =
      Real.sqrt (periodicDispSqEdge edge.disp) *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

/-- Explicit table-fiber form of the mixed target, using the precomputed
`freudenthalLocalPairDispFiber` table for the typed edge's displacement. -/
def CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
              let cell :=
                periodicMatchingBaseCell
                  (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2))
                  edge.base
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm (cell, pair.1))).dihedralDeriv pair.2 k *
                  localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, pair.1)) k) =
      Real.sqrt (periodicDispSqEdge edge.disp) *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainLocalPairFiberTarget_of_explicitFiber
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hExplicit :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainLocalPairFiberTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  rw [← freudenthalLocalPairDispFiber_eq_filter edge.disp]
  exact hExplicit ξ edge

/-- At canonical periodic flatness every encoded tetrahedron carries the
one-cube Freudenthal squared-edge tuple. -/
theorem canonicalPeriodicFlat_tet_sqEdge_eq_freudenthal
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (cell : Vertex Nx Ny Nz) (tet : Fin 6) (k : Fin 6) :
    ((canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K.tet
        ((canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).tetEquiv.symm (cell, tet))).sqEdge k =
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  change (P.K.tet (P.tetEquiv.symm (cell, tet))).sqEdge k = _
  let τ := P.tetEquiv.symm (cell, tet)
  let hChart := (canonicalPeriodicFlatConfigurationInputs Nx Ny Nz hx hy hz).localChart
  have ht := hChart.realizes_tet τ
  rw [← ht]
  have hconst : (hChart.realizedTet τ).tet =
      Geometry.FreudenthalCubeTriangulation.freudenthalTet := by
    simp [hChart, canonicalPeriodicFlatConfigurationInputs,
      canonicalPeriodicFlatConfigurationInputs_of_realizedFreudenthalTet_zeroDeficit,
      canonicalPeriodicLocalAnalyticFlatChart_of_realizedFreudenthalTet,
      realizedFreudenthalTet_of_sqEdgeOfPoints, freudenthalRealizedTet]
  rw [hconst]
  simp only [Geometry.FreudenthalCubeTriangulation.freudenthalTet]

/-- The unique periodic cell selected by the explicit Freudenthal fiber entry
for a typed periodic edge and local `(tet, slot)` pair. -/
noncomputable def freudenthalExplicitFiberPairSelectedCell
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) : Vertex Nx Ny Nz :=
  periodicMatchingBaseCell
    (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2))
    edge.base

theorem freudenthalExplicitFiberPairSelectedCell_base_eq
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) :
    edge.base = addVertexBits (freudenthalExplicitFiberPairSelectedCell edge pair)
      (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2)) :=
  periodicMatchingBaseCell_spec
    (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2))
    edge.base

theorem periodicEdge_eq_of_base_disp
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {e1 e2 : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz}
    (hbase : e1.base = e2.base) (hdisp : e1.disp = e2.disp) : e1 = e2 := by
  cases e1
  cases e2
  rw [PeriodicEdge.mk.injEq]
  exact ⟨hbase, hdisp⟩

theorem freudenthalExplicitFiber_localEdgeOf_eq_edge
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair)
    (hdisp : freudenthalLocalPairDisp pair = edge.disp) :
    localEdgeOf (freudenthalExplicitFiberPairSelectedCell edge pair) pair.1 pair.2 = edge := by
  apply periodicEdge_eq_of_base_disp
  · dsimp [localEdgeOf, freudenthalExplicitFiberPairSelectedCell]
    exact (periodicMatchingBaseCell_spec
      (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2))
      edge.base).symm
  · dsimp [localEdgeOf, freudenthalLocalPairDisp]
    exact hdisp

theorem freudenthalExplicitFiber_addVertexBits_tetVerts_edgeSlot_eq_edgeEndpoints
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair)
    (hdisp : freudenthalLocalPairDisp pair = edge.disp) :
    let cell := freudenthalExplicitFiberPairSelectedCell edge pair
    let tv := edgeVertices pair.2
    (addVertexBits cell (Geometry.FreudenthalCubeTriangulation.tetVerts pair.1 tv.1) =
        edge.endpoints.1 ∧
      addVertexBits cell (Geometry.FreudenthalCubeTriangulation.tetVerts pair.1 tv.2) =
        edge.endpoints.2) ∨
      (addVertexBits cell (Geometry.FreudenthalCubeTriangulation.tetVerts pair.1 tv.1) =
          edge.endpoints.2 ∧
        addVertexBits cell (Geometry.FreudenthalCubeTriangulation.tetVerts pair.1 tv.2) =
          edge.endpoints.1) := by
  have hL := freudenthalExplicitFiber_localEdgeOf_eq_edge edge pair hdisp
  have hmatch :=
    localEdgeOf_endpoints_match_tetVerts (Nx := Nx) (Ny := Ny) (Nz := Nz)
      (freudenthalExplicitFiberPairSelectedCell edge pair) pair.1 pair.2
  dsimp only at hmatch ⊢
  rw [hL] at hmatch
  exact hmatch

/-- Expanded Schläfli/length-chain summand for one explicit-fiber local pair. -/
noncomputable def freudenthalExplicitFiberPairExpandedSummand
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) : ℝ :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  let cell := freudenthalExplicitFiberPairSelectedCell edge pair
  let τ := P.tetEquiv.symm (cell, pair.1)
  ∑ k : Fin 6,
    ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv pair.2 k *
      localEdgeLengthDirectionalDeriv P.K ξ τ k

/-- The expanded explicit-fiber summand is exactly the local angle-length
chain derivative at the selected encoded tetrahedron and slot. -/
theorem freudenthalExplicitFiberPairExpandedSummand_eq_angleChain
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) :
    freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair =
      localAngleLengthChainDeriv
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        ξ
        ((canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).tetEquiv.symm
          (freudenthalExplicitFiberPairSelectedCell edge pair, pair.1))
        pair.2 := by
  rfl

/-- Flat Freudenthal local edge-length directional derivative on an encoded
periodic tetrahedron, with the squared-edge factor unfolded to
`freudenthalTetSqEdges`. -/
noncomputable def freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (cell : Vertex Nx Ny Nz) (tet : Fin 6) (k : Fin 6) : ℝ :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  let τ := P.tetEquiv.symm (cell, tet)
  let uv := Geometry.ReggeRigorousFoundation.edgeVertices k
  Real.sqrt (Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k) *
    ((ξ (P.K.tetVerts τ uv.1) + ξ (P.K.tetVerts τ uv.2)) / 2)

theorem freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv_eq
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (cell : Vertex Nx Ny Nz) (tet : Fin 6) (k : Fin 6) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k =
      freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv
        hx hy hz ξ cell tet k := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  show localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k =
    freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv hx hy hz ξ cell tet k
  simp only [localEdgeLengthDirectionalDeriv,
    freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv]
  rw [canonicalPeriodicFlat_tet_sqEdge_eq_freudenthal Nx Ny Nz hx hy hz cell tet k]

/-- At canonical periodic flatness every encoded tetrahedron uses the closed-form
Freudenthal Schläfli edge-length derivative table. -/
theorem canonicalPeriodicFlat_tet_dihedralDeriv_eq_freudenthalClosed
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (cell : Vertex Nx Ny Nz) (tet : Fin 6) (f k : Fin 6) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    let τ := P.tetEquiv.symm (cell, tet)
    ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k =
      dihedralClosedDerivLength Geometry.FreudenthalCubeTriangulation.freudenthalTet f k := by
  dsimp [triangulationSchlaefliData_of_incidence, tetraSchlaefliDerivativeData_closedForm,
    tetraSchlaefliDerivativeData_of_equation, canonicalEncodedPeriodicFreudenthalTorus,
    canonicalEncodedPeriodicFreudenthalTorus_of_endpoint,
    canonicalEncodedPeriodicFreudenthalTorus_of_incidence, canonicalPeriodicTriangulation]

/-- Closed-form Schläfli/length-chain summand for one local Freudenthal pair,
with caller-supplied conformal edge-length directional derivatives. -/
noncomputable def freudenthalLocalPairClosedFormExpandedSummand
    (pair : FreudenthalLocalPair) (edgeLengthDir : Fin 6 → ℝ) : ℝ :=
  ∑ k : Fin 6,
    dihedralClosedDerivLength Geometry.FreudenthalCubeTriangulation.freudenthalTet pair.2 k *
      edgeLengthDir k

theorem freudenthalLocalPairClosedFormExpandedSummand_eq_lengthChainSummand
    (pair : FreudenthalLocalPair) (edgeLengthDir : Fin 6 → ℝ) :
    freudenthalLocalPairClosedFormExpandedSummand pair edgeLengthDir =
      freudenthalLocalPairLengthChainSummand pair edgeLengthDir := by
  rfl

theorem freudenthalLocalPairClosedFormExpandedSummand_add
    (pair : FreudenthalLocalPair) (f g : Fin 6 → ℝ) :
    freudenthalLocalPairClosedFormExpandedSummand pair (f + g) =
      freudenthalLocalPairClosedFormExpandedSummand pair f +
        freudenthalLocalPairClosedFormExpandedSummand pair g := by
  unfold freudenthalLocalPairClosedFormExpandedSummand
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  simp only [Pi.add_apply, mul_add]

/-- Closed-form explicit-fiber expanded summand for one local pair. -/
noncomputable def freudenthalExplicitFiberPairClosedFormExpandedSummand
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) : ℝ :=
  let cell := freudenthalExplicitFiberPairSelectedCell edge pair
  freudenthalLocalPairClosedFormExpandedSummand pair fun k =>
    freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv hx hy hz ξ cell pair.1 k

/-- Flat-unfolded expanded summand for one explicit-fiber local pair. -/
noncomputable def freudenthalExplicitFiberPairFlatExpandedSummand
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) : ℝ :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  let cell := freudenthalExplicitFiberPairSelectedCell edge pair
  let τ := P.tetEquiv.symm (cell, pair.1)
  ∑ k : Fin 6,
    ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv pair.2 k *
      freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv hx hy hz ξ cell pair.1 k

theorem freudenthalExplicitFiberPairFlatExpandedSummand_eq_expanded
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) :
    freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz ξ edge pair =
      freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair := by
  unfold freudenthalExplicitFiberPairFlatExpandedSummand
    freudenthalExplicitFiberPairExpandedSummand
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv_eq hx hy hz ξ
    (freudenthalExplicitFiberPairSelectedCell edge pair) pair.1 k]

theorem freudenthalExplicitFiberPairClosedFormExpandedSummand_eq_flat
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) :
    freudenthalExplicitFiberPairClosedFormExpandedSummand hx hy hz ξ edge pair =
      freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz ξ edge pair := by
  unfold freudenthalExplicitFiberPairClosedFormExpandedSummand
    freudenthalExplicitFiberPairFlatExpandedSummand
    freudenthalLocalPairClosedFormExpandedSummand
  let cell := freudenthalExplicitFiberPairSelectedCell edge pair
  refine Finset.sum_congr rfl ?_
  intro k _
  change
    dihedralClosedDerivLength Geometry.FreudenthalCubeTriangulation.freudenthalTet pair.2 k *
        freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv hx hy hz ξ cell pair.1 k =
      ((triangulationSchlaefliData_of_incidence
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK).tetData
          ((canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).tetEquiv.symm (cell, pair.1))).dihedralDeriv
        pair.2 k *
      freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv hx hy hz ξ cell pair.1 k
  rw [← canonicalPeriodicFlat_tet_dihedralDeriv_eq_freudenthalClosed hx hy hz cell pair.1 pair.2 k]

/-- The explicit-fiber table inner slot sum (Schläfli × local edge-length deriv)
matches the flat-unfolded per-pair summand at the selected matching cell. -/
theorem freudenthalExplicitFiberTablePairInnerSum_eq_flatExpandedSummand
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    let cell := freudenthalExplicitFiberPairSelectedCell edge pair
    (∑ k : Fin 6,
        ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
            (P.tetEquiv.symm (cell, pair.1))).dihedralDeriv pair.2 k *
          localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, pair.1)) k) =
      freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz ξ edge pair := by
  dsimp [freudenthalExplicitFiberPairFlatExpandedSummand]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv_eq hx hy hz ξ
    (freudenthalExplicitFiberPairSelectedCell edge pair) pair.1 k]

/-- The explicit-fiber table inner sum matches the expanded summand at the
selected matching cell. -/
theorem freudenthalExplicitFiberPairExplicitInnerSum_eq_expandedSummand
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    let cell := freudenthalExplicitFiberPairSelectedCell edge pair
    (∑ k : Fin 6,
        ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
            (P.tetEquiv.symm (cell, pair.1))).dihedralDeriv pair.2 k *
          localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, pair.1)) k) =
      freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair := by
  rfl

theorem freudenthalExplicitFiberDispTableSum_eq_expandedSummandSum
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        let cell :=
          periodicMatchingBaseCell
            (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2))
            edge.base
        ∑ k : Fin 6,
          ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
              (P.tetEquiv.symm (cell, pair.1))).dihedralDeriv pair.2 k *
            localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, pair.1)) k) =
      ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair := by
  refine Finset.sum_congr rfl ?_
  intro pair _
  dsimp [freudenthalExplicitFiberPairSelectedCell]
  exact freudenthalExplicitFiberPairExplicitInnerSum_eq_expandedSummand hx hy hz ξ edge pair

/-- Corrected explicit-fiber global form of the mixed hinge-deficit target.
Unlike the old per-edge endpoint target, this keeps the global sum over typed
periodic edges and compares it to the rational axis stencil found by the finite
audit. -/
def CanonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ ξ : VertexPotential P.K,
    (∑ edge : PeriodicEdge Nx Ny Nz,
      let e := P.edgeEquiv.symm edge
      hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair)) =
      canonicalPeriodicMixedAxisStencilAction Nx Ny Nz hx hy hz ξ

theorem periodicMatchingBaseCell_eq_of_addVertexBits
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (a : Fin 8)
    (target cell : Geometry.PeriodicFreudenthalTorus.Vertex Nx Ny Nz)
    (h : target = Geometry.PeriodicFreudenthalTorus.addVertexBits cell a) :
    cell = periodicMatchingBaseCell a target :=
  periodicMatchingBaseCell_unique a target h

theorem canonicalPeriodicTypedEdge_eq_localEdgeOf_of_base_and_disp
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (cell : Geometry.PeriodicFreudenthalTorus.Vertex Nx Ny Nz) (tet : Fin 6) (f : Fin 6)
    (hbase :
      edge.base = Geometry.PeriodicFreudenthalTorus.addVertexBits cell
        (Geometry.PeriodicFreudenthalTorus.cubeEdgeBase
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f)))
    (hdisp :
      edge.disp = Geometry.PeriodicFreudenthalTorus.cubeEdgeDisp
        (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f)) :
    edge = localEdgeOf cell tet f := by
  exact (canonicalPeriodicTypedEdge_eq_localEdgeOf_iff_base_and_disp edge (cell, tet) f).2
    ⟨hbase, hdisp⟩

/-- Angle-chain form of the explicit-fiber mixed target. -/
def CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberAngleChainTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          localAngleLengthChainDeriv P.K P.hK ξ
            (P.tetEquiv.symm (freudenthalExplicitFiberPairSelectedCell edge pair, pair.1))
            pair.2) =
      Real.sqrt (periodicDispSqEdge edge.disp) *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget_of_angleChain
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hAngleChain :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberAngleChainTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  have hsum :
      (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair) =
        ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          localAngleLengthChainDeriv P.K P.hK ξ
            (P.tetEquiv.symm (freudenthalExplicitFiberPairSelectedCell edge pair, pair.1))
            pair.2 := by
    refine Finset.sum_congr rfl ?_
    intro pair _
    exact freudenthalExplicitFiberPairExpandedSummand_eq_angleChain hx hy hz ξ edge pair
  simpa [CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget,
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberAngleChainTarget,
    freudenthalExplicitFiberPairExpandedSummand, hsum, P] using hAngleChain ξ edge

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberAngleChainTarget_of_explicit
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hExplicit :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberAngleChainTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  have hsum :
      (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          localAngleLengthChainDeriv P.K P.hK ξ
            (P.tetEquiv.symm (freudenthalExplicitFiberPairSelectedCell edge pair, pair.1))
            pair.2) =
        ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair := by
    refine Finset.sum_congr rfl ?_
    intro pair _
    exact (freudenthalExplicitFiberPairExpandedSummand_eq_angleChain hx hy hz ξ edge pair).symm
  simpa [CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget,
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberAngleChainTarget,
    freudenthalExplicitFiberPairExpandedSummand, hsum, P] using hExplicit ξ edge

/-- Flat-unfolded explicit-fiber mixed target: the fiber sum uses
`freudenthalExplicitFiberPairFlatExpandedSummand` entry by entry. -/
def CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz ξ edge pair) =
      Real.sqrt (periodicDispSqEdge edge.disp) *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

/-- Closed-form explicit-fiber mixed target: the fiber sum uses
`freudenthalExplicitFiberPairClosedFormExpandedSummand` entry by entry. -/
def CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
        (-∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairClosedFormExpandedSummand hx hy hz ξ edge pair) =
      Real.sqrt (periodicDispSqEdge edge.disp) *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

theorem edgeFinEquiv_symm_apply
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (edge : PeriodicEdge Nx Ny Nz) :
    edgeFinEquiv Nx Ny Nz ((edgeFinEquiv Nx Ny Nz).symm edge) = edge := by
  simp

/-- Global squared edge length for an encoded periodic edge is the typed
displacement class table entry. -/
theorem canonicalEncodedPeriodic_globalSqEdge_eq_periodicDispSqEdge
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {hx : 2 < Nx} {hy : 2 < Ny} {hz : 2 < Nz}
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    P.hK.globalSqEdge (P.edgeEquiv.symm edge) = periodicDispSqEdge edge.disp := by
  dsimp [canonicalEncodedPeriodicFreudenthalTorus,
    canonicalEncodedPeriodicFreudenthalTorus_of_endpoint,
    canonicalEncodedPeriodicFreudenthalTorus_of_incidence,
    canonicalPeriodicTriangulation, canonicalPeriodicEdgeEquiv,
    canonicalGlobalSqEdge, canonicalPeriodicIncidenceConsistent_of_endpoint,
    canonicalPeriodicIncidenceConsistent]
  rw [edgeFinEquiv_symm_apply edge]

/-- Encoded edge vertex indices are the typed periodic edge endpoints. -/
theorem canonicalEncodedPeriodic_edgeVerts_eq_periodic_endpoints
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {hx : 2 < Nx} {hy : 2 < Ny} {hz : 2 < Nz}
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    P.K.edgeVerts (P.edgeEquiv.symm edge) =
      ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1,
        (vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2) := by
  dsimp [canonicalEncodedPeriodicFreudenthalTorus,
    canonicalEncodedPeriodicFreudenthalTorus_of_endpoint,
    canonicalEncodedPeriodicFreudenthalTorus_of_incidence,
    canonicalPeriodicTriangulation, canonicalPeriodicEdgeEquiv,
    canonicalEdgeVerts]
  rw [edgeFinEquiv_symm_apply edge]

/-- Hinge-length directional derivative in typed periodic coordinates. -/
theorem hingeMeasureDirectionalDeriv_canonicalEncodedPeriodic_edge
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {hx : 2 < Nx} {hy : 2 < Ny} {hz : 2 < Nz}
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    hingeMeasureDirectionalDeriv P.K P.hK ξ (P.edgeEquiv.symm edge) =
      Real.sqrt (periodicDispSqEdge edge.disp) *
        (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) +
          ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) / 2 := by
  dsimp [hingeMeasureDirectionalDeriv]
  rw [canonicalEncodedPeriodic_globalSqEdge_eq_periodicDispSqEdge edge,
    canonicalEncodedPeriodic_edgeVerts_eq_periodic_endpoints edge]
  ring

/-- Closed-form fiber sum for one positive displacement class. -/
noncomputable def freudenthalExplicitFiberClosedFormFiberSum
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (d : Fin 7) : ℝ :=
  ∑ pair ∈ freudenthalLocalPairDispFiber d,
    freudenthalExplicitFiberPairClosedFormExpandedSummand hx hy hz ξ edge pair

theorem freudenthalExplicitFiberClosedFormFiberSum_eq_disp_fiber
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge edge.disp =
      ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        freudenthalExplicitFiberPairClosedFormExpandedSummand hx hy hz ξ edge pair := by
  rfl

theorem freudenthalExplicitFiberFlatDispFiberSum_eq_closedFormFiberSum
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz ξ edge pair) =
      freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge edge.disp := by
  rw [freudenthalExplicitFiberClosedFormFiberSum_eq_disp_fiber]
  refine Finset.sum_congr rfl ?_
  intro pair _
  exact (freudenthalExplicitFiberPairClosedFormExpandedSummand_eq_flat hx hy hz ξ edge pair).symm

theorem freudenthalExplicitFiberExpandedDispFiberSum_eq_closedFormFiberSum
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair) =
      freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge edge.disp :=
  Eq.trans
    (Finset.sum_congr rfl fun pair _ =>
      (freudenthalExplicitFiberPairFlatExpandedSummand_eq_expanded hx hy hz ξ edge pair).symm)
    (freudenthalExplicitFiberFlatDispFiberSum_eq_closedFormFiberSum hx hy hz ξ edge)

theorem freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv_add
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ η : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (cell : Vertex Nx Ny Nz) (tet : Fin 6) (k : Fin 6) :
    freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv hx hy hz (ξ + η) cell tet k =
      freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv hx hy hz ξ cell tet k +
        freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv hx hy hz η cell tet k := by
  simp only [freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv, Pi.add_apply]
  ring

theorem freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv_smul
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (c : ℝ)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (cell : Vertex Nx Ny Nz) (tet : Fin 6) (k : Fin 6) :
    freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv hx hy hz (c • ξ) cell tet k =
      c * freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv hx hy hz ξ cell tet k := by
  simp only [freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv, Pi.smul_apply, smul_eq_mul]
  ring

theorem freudenthalExplicitFiberPairFlatExpandedSummand_smul
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (c : ℝ)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) :
    freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz (c • ξ) edge pair =
      c * freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz ξ edge pair := by
  unfold freudenthalExplicitFiberPairFlatExpandedSummand
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv_smul hx hy hz c ξ
    (freudenthalExplicitFiberPairSelectedCell edge pair) pair.1 k]
  ring

theorem freudenthalExplicitFiberPairClosedFormExpandedSummand_smul
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (c : ℝ)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) :
    freudenthalExplicitFiberPairClosedFormExpandedSummand hx hy hz (c • ξ) edge pair =
      c * freudenthalExplicitFiberPairClosedFormExpandedSummand hx hy hz ξ edge pair := by
  rw [freudenthalExplicitFiberPairClosedFormExpandedSummand_eq_flat hx hy hz (c • ξ) edge pair,
    freudenthalExplicitFiberPairClosedFormExpandedSummand_eq_flat hx hy hz ξ edge pair]
  exact freudenthalExplicitFiberPairFlatExpandedSummand_smul hx hy hz c ξ edge pair

theorem freudenthalExplicitFiberClosedFormFiberSum_smul_basis
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (c : ℝ)
    (i : Fin (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K.nV)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) (d : Fin 7) :
    freudenthalExplicitFiberClosedFormFiberSum hx hy hz
        (c • Pi.single (M := fun _ : Fin _ => ℝ) i (1 : ℝ)) edge d =
      c * freudenthalExplicitFiberClosedFormFiberSum hx hy hz
        (Pi.single (M := fun _ : Fin _ => ℝ) i (1 : ℝ)) edge d := by
  unfold freudenthalExplicitFiberClosedFormFiberSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro pair _
  exact freudenthalExplicitFiberPairClosedFormExpandedSummand_smul hx hy hz c _ edge pair

theorem freudenthalExplicitFiberPairFlatExpandedSummand_add
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ η : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) :
    freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz (ξ + η) edge pair =
      freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz ξ edge pair +
        freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz η edge pair := by
  unfold freudenthalExplicitFiberPairFlatExpandedSummand
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  simp only [freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv_add hx hy hz ξ η
    (freudenthalExplicitFiberPairSelectedCell edge pair) pair.1 k, mul_add]

theorem freudenthalExplicitFiberPairClosedFormExpandedSummand_add
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ η : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) :
    freudenthalExplicitFiberPairClosedFormExpandedSummand hx hy hz (ξ + η) edge pair =
      freudenthalExplicitFiberPairClosedFormExpandedSummand hx hy hz ξ edge pair +
        freudenthalExplicitFiberPairClosedFormExpandedSummand hx hy hz η edge pair := by
  rw [freudenthalExplicitFiberPairClosedFormExpandedSummand_eq_flat hx hy hz (ξ + η) edge pair,
    freudenthalExplicitFiberPairClosedFormExpandedSummand_eq_flat hx hy hz ξ edge pair,
    freudenthalExplicitFiberPairClosedFormExpandedSummand_eq_flat hx hy hz η edge pair]
  exact freudenthalExplicitFiberPairFlatExpandedSummand_add hx hy hz ξ η edge pair

theorem freudenthalExplicitFiberClosedFormFiberSum_add
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ η : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) (d : Fin 7) :
    freudenthalExplicitFiberClosedFormFiberSum hx hy hz (ξ + η) edge d =
      freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge d +
        freudenthalExplicitFiberClosedFormFiberSum hx hy hz η edge d := by
  unfold freudenthalExplicitFiberClosedFormFiberSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro pair _
  exact freudenthalExplicitFiberPairClosedFormExpandedSummand_add hx hy hz ξ η edge pair

theorem finRealLinearFunctional_map_finset_sum
    {ι : Type*} [DecidableEq ι] (f : (ι → ℝ) → ℝ)
    (hf_add : ∀ ξ η, f (ξ + η) = f ξ + f η)
    (hf_smul_basis :
      ∀ (c : ℝ) (i : ι),
        f (c • Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)) =
          c * f (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))
    {s : Finset ι} (g : ι → ℝ) :
    f (∑ i ∈ s, g i • Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)) =
      ∑ i ∈ s, g i * f (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)) := by
  have hf0 : f 0 = 0 := by
    have h := hf_add 0 0
    simp at h
    linarith
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact hf0
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, hf_add, ih, hf_smul_basis]
      simp [Finset.sum_insert ha]

/-- A finite-dimensional `ℝ`-linear functional on coordinate potentials is determined
by its values on coordinate basis vectors. -/
theorem finRealLinearFunctional_eq_sum_coord
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℝ)
    (hf_add : ∀ ξ η, f (ξ + η) = f ξ + f η)
    (hf_smul_basis :
      ∀ (c : ℝ) (i : ι),
        f (c • Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)) =
          c * f (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)))
    (ξ : ι → ℝ) :
    f ξ = ∑ i : ι, ξ i * f (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)) := by
  have hv :
      (∑ i : ι, Pi.single (M := fun _ : ι => ℝ) i (ξ i)) = ξ :=
    Finset.univ_sum_single ξ
  have hsingle :
      ∀ i : ι,
        Pi.single (M := fun _ : ι => ℝ) i (ξ i) =
          ξ i • Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ) := by
    intro i
    funext j
    by_cases hij : j = i
    · subst hij
      simp [Pi.single_eq_same]
    · simp [hij]
  have hv_smul :
      (∑ i : ι, Pi.single (M := fun _ : ι => ℝ) i (ξ i)) =
        ∑ i : ι, ξ i • Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ) :=
    Finset.sum_congr rfl fun i _ => hsingle i
  calc
    f ξ = f (∑ i : ι, Pi.single (M := fun _ : ι => ℝ) i (ξ i)) := by rw [hv]
    _ = f (∑ i : ι, ξ i • Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)) := by
      rw [hv_smul]
    _ = ∑ i : ι, ξ i * f (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ)) := by
      have hmap :=
        finRealLinearFunctional_map_finset_sum f hf_add hf_smul_basis (s := Finset.univ) (g := ξ)
      simpa using hmap

/-- Coordinate-basis coefficient of the explicit-fiber closed-form sum at one
displacement class. -/
noncomputable def freudenthalExplicitFiberClosedFormVertexCoeff
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) (d : Fin 7)
    (i : Fin (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K.nV) : ℝ :=
  freudenthalExplicitFiberClosedFormFiberSum hx hy hz
    (Pi.single (M := fun _ : Fin _ => ℝ) i (1 : ℝ)) edge d

theorem freudenthalExplicitFiberClosedFormFiberSum_eq_sum_vertexCoeffs
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) (d : Fin 7) :
    freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge d =
      ∑ i : Fin (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K.nV,
        ξ i * freudenthalExplicitFiberClosedFormVertexCoeff hx hy hz edge d i :=
  finRealLinearFunctional_eq_sum_coord
    (f := fun η => freudenthalExplicitFiberClosedFormFiberSum hx hy hz η edge d)
    (hf_add := fun η₁ η₂ =>
      freudenthalExplicitFiberClosedFormFiberSum_add hx hy hz η₁ η₂ edge d)
    (hf_smul_basis := fun c i =>
      freudenthalExplicitFiberClosedFormFiberSum_smul_basis hx hy hz c i edge d)
    ξ

theorem freudenthalExplicitFiberClosedFormFiberSum_smul
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (c : ℝ)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) (d : Fin 7) :
    freudenthalExplicitFiberClosedFormFiberSum hx hy hz (c • ξ) edge d =
      c * freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge d := by
  rw [freudenthalExplicitFiberClosedFormFiberSum_eq_sum_vertexCoeffs hx hy hz (c • ξ) edge d,
    freudenthalExplicitFiberClosedFormFiberSum_eq_sum_vertexCoeffs hx hy hz ξ edge d]
  simp only [Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [freudenthalExplicitFiberClosedFormVertexCoeff, smul_eq_mul, mul_assoc]

/-- Explicit-fiber length-chain sum in closed template form: each fiber entry
uses the flat edge-length directional derivative at its selected periodic cell. -/
noncomputable def freudenthalExplicitFiberDispLengthChainSumTemplate
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (d : Fin 7) : ℝ :=
  ∑ pair ∈ freudenthalLocalPairDispFiber d,
    freudenthalLocalPairLengthChainSummand pair fun k =>
      freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv hx hy hz ξ
        (freudenthalExplicitFiberPairSelectedCell edge pair) pair.1 k

theorem freudenthalExplicitFiberClosedFormFiberSum_eq_disp_lengthChainTemplate
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge edge.disp =
      freudenthalExplicitFiberDispLengthChainSumTemplate hx hy hz ξ edge edge.disp := by
  unfold freudenthalExplicitFiberClosedFormFiberSum
    freudenthalExplicitFiberDispLengthChainSumTemplate
  refine Finset.sum_congr rfl ?_
  intro pair _
  unfold freudenthalExplicitFiberPairClosedFormExpandedSummand
  rw [freudenthalLocalPairClosedFormExpandedSummand_eq_lengthChainSummand]

/-- Encoded tetrahedron vertices are `addVertexBits cell` applied to local cube vertices. -/
theorem freudenthalExplicitFiber_canonicalTetVerts_eq
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair) (v : Fin 4) :
    let cell := freudenthalExplicitFiberPairSelectedCell edge pair
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K.tetVerts
        ((canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).tetEquiv.symm (cell, pair.1)) v =
      (vertexFinEquiv Nx Ny Nz).symm
        (addVertexBits cell (Geometry.FreudenthalCubeTriangulation.tetVerts pair.1 v)) := by
  exact canonicalEncodedPeriodic_tetVerts_addVertexBits Nx Ny Nz hx hy hz
    (freudenthalExplicitFiberPairSelectedCell edge pair) pair.1 v

/-- The slot-`pair.2` vertices of the selected encoded tetrahedron coincide with the typed
periodic edge endpoints up to orientation. -/
theorem freudenthalExplicitFiber_tetVerts_edgeSlot_eq_edgeEndpoints
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (pair : FreudenthalLocalPair)
    (hdisp : freudenthalLocalPairDisp pair = edge.disp) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    let cell := freudenthalExplicitFiberPairSelectedCell edge pair
    let tv := Geometry.ReggeRigorousFoundation.edgeVertices pair.2
    (P.K.tetVerts (P.tetEquiv.symm (cell, pair.1)) tv.1 =
        (vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1 ∧
      P.K.tetVerts (P.tetEquiv.symm (cell, pair.1)) tv.2 =
        (vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2) ∨
      (P.K.tetVerts (P.tetEquiv.symm (cell, pair.1)) tv.1 =
          (vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2 ∧
        P.K.tetVerts (P.tetEquiv.symm (cell, pair.1)) tv.2 =
          (vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) := by
  dsimp only
  let tv := Geometry.ReggeRigorousFoundation.edgeVertices pair.2
  rcases freudenthalExplicitFiber_addVertexBits_tetVerts_edgeSlot_eq_edgeEndpoints edge pair hdisp with
    hdir | hrev
  · left
    constructor
    · rw [freudenthalExplicitFiber_canonicalTetVerts_eq hx hy hz edge pair tv.1]
      exact congrArg _ hdir.1
    · rw [freudenthalExplicitFiber_canonicalTetVerts_eq hx hy hz edge pair tv.2]
      exact congrArg _ hdir.2
  · right
    constructor
    · rw [freudenthalExplicitFiber_canonicalTetVerts_eq hx hy hz edge pair tv.1]
      exact congrArg _ hrev.1
    · rw [freudenthalExplicitFiber_canonicalTetVerts_eq hx hy hz edge pair tv.2]
      exact congrArg _ hrev.2

/-- Per positive-displacement-class closed-form explicit-fiber mixed target.

The endpoint-only packaging (`∃ F : ℝ → ℝ → ℝ` with fiber sum `= F ξ₀ ξ₁`) is
blocked for d ∈ {0,3} by the proved vertex expansion together with the finite audit
in `scripts/freudenthal_explicit_fiber_endpoint_analysis.py` (interior coefficients
do not vanish; at (ξ₀,ξ₁)=(1,1) the fiber sum is −4 while the template forces
`F(1,1)=0`; see
`FreudenthalLocalDispLengthChainEndpointTemplateTarget_F_eq_zero_at_one_one`).
The load-bearing replacement is the global mixed target
`CanonicalPeriodicMixedHingeDeficitLengthChainTarget` (sum over edges), not this
pointwise endpoint-quadratic ansatz with `fiberSum = F(ξ₀,ξ₁)`. -/
def CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) (d : Fin 7) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    edge.disp = d →
      Real.sqrt (periodicDispSqEdge d) *
          (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) +
            ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) / 2 *
          (-freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge d) =
        Real.sqrt (periodicDispSqEdge d) *
          (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
            ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ)

/-- The closed-form explicit-fiber sum for one displacement class depends only
on the two endpoint potentials of the typed periodic edge.

This is the load-bearing combinatorial step for the bilinear endpoint template:
the length-chain sum is `ℝ`-linear in `VertexPotential` (see
`freudenthalExplicitFiberClosedFormFiberSum_add`), so endpoint dependence is
equivalent to vanishing coefficients on all non-endpoint torus vertices in that
linear expansion.  A finite coefficient audit (see
`scripts/freudenthal_explicit_fiber_endpoint_analysis.py`) shows nonzero
non-endpoint coefficients for axis and face-diagonal classes; the remaining
work is a Lean certificate of those cancellations or a revised target. -/
def FreudenthalExplicitFiberEndpointDependenceTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) (d : Fin 7) : Prop :=
  ∃ F : ℝ → ℝ → ℝ,
    ∀ (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
      (edge : PeriodicEdge Nx Ny Nz),
      edge.disp = d →
        freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge d =
          F (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1))
            (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2))

/-- Per-edge vertex-coefficient expansion of the explicit-fiber closed-form sum:
`fiberSum ξ = ∑_v c_{edge}(v) · ξ(v)`.  This is the honest linear form before any
endpoint-only ansatz; a finite audit lives in
`scripts/freudenthal_explicit_fiber_endpoint_analysis.py`. -/
def FreudenthalExplicitFiberVertexCoefficientExpansionTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) (d : Fin 7) : Prop :=
  ∀ (edge : PeriodicEdge Nx Ny Nz),
    edge.disp = d →
      ∃ coeffs : Fin (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K.nV → ℝ,
        ∀ (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K),
          freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge d =
            ∑ i : Fin (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K.nV,
              coeffs i * ξ i

theorem FreudenthalExplicitFiberVertexCoefficientExpansionTarget_holds
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) (d : Fin 7) :
    FreudenthalExplicitFiberVertexCoefficientExpansionTarget Nx Ny Nz hx hy hz d := by
  intro edge hdisp
  refine
    ⟨fun i => freudenthalExplicitFiberClosedFormVertexCoeff hx hy hz edge d i, ?_⟩
  intro ξ
  rw [freudenthalExplicitFiberClosedFormFiberSum_eq_sum_vertexCoeffs hx hy hz ξ edge d]
  simp [mul_comm]

/-- Uniform affine endpoint coefficients on a displacement class imply
`FreudenthalExplicitFiberEndpointDependenceTarget` with
`F ξ₀ ξ₁ = c₀ ξ₀ + c₁ ξ₁`.  The global `F` is sharp: auxiliary-vertex zeros per edge are
not enough unless `(c₀,c₁)` are constant across all edges of class `d`. -/
theorem FreudenthalExplicitFiberEndpointDependenceTarget_of_uniformAffineCoeffs
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) (d : Fin 7) (c₀ c₁ : ℝ)
    (hSum :
      ∀ (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (edge : PeriodicEdge Nx Ny Nz),
        edge.disp = d →
          freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge d =
            c₀ * ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) +
              c₁ * ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) :
    FreudenthalExplicitFiberEndpointDependenceTarget Nx Ny Nz hx hy hz d := by
  refine ⟨fun ξ₀ ξ₁ => c₀ * ξ₀ + c₁ * ξ₁, ?_⟩
  intro ξ edge hdisp
  simpa [hdisp] using hSum ξ edge hdisp

/-- Per-displacement-class packaged target: endpoint dependence of the fiber sum plus the
local endpoint-template polynomial identity.

**Status:** blocked for the explicit closed-form fiber sum when `F(ξ₀,ξ₁)` is
identified with the fiber sum on endpoint-only potentials: the template forces
`F(1,1)=0` while the finite audit reports a nonzero diagonal fiber sum for
classes `0` and `3` (see
`FreudenthalLocalDispLengthChainEndpointTemplateTarget_F_eq_zero_at_one_one`).
Discharge via interior-vertex cancellation or abandon the
`fiberSum = F(ξ₀,ξ₁)` identification. -/
def FreudenthalExplicitFiberBilinearEndpointTemplateTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) (d : Fin 7) : Prop :=
  ∃ F : ℝ → ℝ → ℝ,
    FreudenthalLocalDispLengthChainEndpointTemplateTarget d F ∧
      ∀ (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (edge : PeriodicEdge Nx Ny Nz),
        edge.disp = d →
          freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge d =
            F (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1))
              (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2))

theorem periodicDispSqEdge_pos (d : Fin 7) : 0 < periodicDispSqEdge d := by
  fin_cases d <;> simp [periodicDispSqEdge]

theorem periodicDispSqEdge_sqrt_ne_zero (d : Fin 7) :
    Real.sqrt (periodicDispSqEdge d) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (periodicDispSqEdge_pos d))

/-- Any function `F` satisfying the length-chain endpoint template must vanish on
the diagonal `(ξ₀,ξ₁) = (1,1)`. -/
theorem FreudenthalLocalDispLengthChainEndpointTemplateTarget_F_eq_zero_at_one_one
    (d : Fin 7) (F : ℝ → ℝ → ℝ)
    (hF : FreudenthalLocalDispLengthChainEndpointTemplateTarget d F) :
    F 1 1 = 0 := by
  have hEq := hF 1 1
  have hs := periodicDispSqEdge_sqrt_ne_zero d
  have hCancel :
      Real.sqrt (periodicDispSqEdge d) * (1 + 1) / 2 * (-F 1 1) =
        Real.sqrt (periodicDispSqEdge d) * (1 - 1) ^ (2 : ℕ) := hEq
  simp at hCancel
  have hFactor : Real.sqrt (periodicDispSqEdge d) * (-F 1 1) = 0 := by
    simpa using hCancel
  rcases mul_eq_zero.mp hFactor with hsZero | hF0
  · exact absurd hsZero hs
  · simpa using neg_eq_zero.mp hF0

/-- The template forces `F(1,0) = -2`. -/
theorem FreudenthalLocalDispLengthChainEndpointTemplateTarget_F_eq_neg_two_at_one_zero
    (d : Fin 7) (F : ℝ → ℝ → ℝ)
    (hF : FreudenthalLocalDispLengthChainEndpointTemplateTarget d F) :
    F 1 0 = -2 := by
  have hEq := hF 1 0
  have hs := periodicDispSqEdge_sqrt_ne_zero d
  have hCancel :
      Real.sqrt (periodicDispSqEdge d) * (1 + 0) / 2 * (-F 1 0) =
        Real.sqrt (periodicDispSqEdge d) * (1 - 0) ^ (2 : ℕ) := hEq
  rw [pow_two] at hCancel
  have hFactor :
      Real.sqrt (periodicDispSqEdge d) / 2 * (-F 1 0) = Real.sqrt (periodicDispSqEdge d) := by
    simpa using hCancel
  have hTwo : Real.sqrt (periodicDispSqEdge d) * (-F 1 0) = 2 * Real.sqrt (periodicDispSqEdge d) := by
    linarith
  have hRearr :
      Real.sqrt (periodicDispSqEdge d) * (-F 1 0) =
        Real.sqrt (periodicDispSqEdge d) * (2 : ℝ) := by
    rw [hTwo, mul_comm (2 : ℝ) (Real.sqrt (periodicDispSqEdge d))]
  have hNeg : -F 1 0 = 2 := mul_left_cancel₀ hs hRearr
  linarith

/-! ### Axis class-0 explicit-fiber obstruction (`Nx = Ny = Nz = 5`)

Finite audit at base `(1,0,0)` (`scripts/freudenthal_explicit_fiber_endpoint_analysis.py`):
endpoint-unit closed-form fiber sum is `-4` while the length-chain endpoint template forces
`F(1,1) = 0`.  The audit sum below is proved by `norm_num`; the global torus identification
is the named target `FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget`. -/

namespace AxisDisp0EndpointUnitWitness5

abbrev WitnessNx := (5 : ℕ)
abbrev WitnessNy := (5 : ℕ)
abbrev WitnessNz := (5 : ℕ)

instance witnessNeNx : NeZero WitnessNx := ⟨by decide⟩
instance witnessNeNy : NeZero WitnessNy := ⟨by decide⟩
instance witnessNeNz : NeZero WitnessNz := ⟨by decide⟩

def witnessHx : 2 < WitnessNx := by decide
def witnessHy : 2 < WitnessNy := by decide
def witnessHz : 2 < WitnessNz := by decide

def axisWitnessEdge : PeriodicEdge WitnessNx WitnessNy WitnessNz :=
  { base := (1, 0, 0), disp := 0 }

def axisWitnessEndpoint0 : Vertex WitnessNx WitnessNy WitnessNz := (1, 0, 0)
def axisWitnessEndpoint1 : Vertex WitnessNx WitnessNy WitnessNz := (2, 0, 0)

theorem axisWitness_edge_endpoints :
    axisWitnessEdge.endpoints = (axisWitnessEndpoint0, axisWitnessEndpoint1) := by
  native_decide

/-- Audit-mirrored per-pair contributions for axis class `0` at endpoint-unit data
(base `(1,0,0)`, `N = 5`).  Matches `scripts/freudenthal_explicit_fiber_endpoint_analysis.py`. -/
def freudenthalAxisDisp0EndpointUnitAuditSum : ℝ :=
  (-1 / 2 : ℝ) + (-1 / 2) + (-1) + (-1 / 2) + (-1) + (-1 / 2)

theorem freudenthalAxisDisp0EndpointUnitAuditSum_eq_neg_four :
    freudenthalAxisDisp0EndpointUnitAuditSum = (-4 : ℝ) := by
  unfold freudenthalAxisDisp0EndpointUnitAuditSum
  norm_num

open Geometry.FreudenthalCubeTriangulation

/-- Explicit matching cell per local pair for the axis witness edge (audit table). -/
def axisWitnessCell (pair : FreudenthalLocalPair) : Vertex WitnessNx WitnessNy WitnessNz :=
  match pair.1, pair.2 with
  | 0, 0 => (1, 0, 0)
  | 1, 0 => (1, 0, 0)
  | 2, 3 => (1, 4, 0)
  | 3, 5 => (1, 4, 4)
  | 4, 3 => (1, 0, 4)
  | 5, 5 => (1, 4, 4)
  | _, _ => (0, 0, 0)

theorem axisWitnessCell_base_offset (pair : FreudenthalLocalPair)
    (hp : pair ∈ freudenthalLocalPairDispFiber 0) :
    axisWitnessEdge.base = addVertexBits (axisWitnessCell pair)
      (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2)) := by
  have hmem :
      pair = (0, 0) ∨ pair = (1, 0) ∨ pair = (2, 3) ∨ pair = (3, 5) ∨ pair = (4, 3) ∨
        pair = (5, 5) := by
    simpa [freudenthalLocalPairDispFiber] using hp
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

theorem axisWitness_selectedCell_eq (pair : FreudenthalLocalPair)
    (hp : pair ∈ freudenthalLocalPairDispFiber 0) :
    freudenthalExplicitFiberPairSelectedCell axisWitnessEdge pair = axisWitnessCell pair := by
  dsimp [freudenthalExplicitFiberPairSelectedCell]
  symm
  exact periodicMatchingBaseCell_unique _ _ (axisWitnessCell_base_offset pair hp)

def axisWitnessEndpointUnitPotential :
    VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus WitnessNx WitnessNy WitnessNz witnessHx witnessHy
        witnessHz).K :=
  fun i =>
    if i = (vertexFinEquiv WitnessNx WitnessNy WitnessNz).symm axisWitnessEndpoint0 ∨
        i = (vertexFinEquiv WitnessNx WitnessNy WitnessNz).symm axisWitnessEndpoint1 then
      1
    else 0

theorem axisWitnessEndpointUnitPotential_apply (v : Vertex WitnessNx WitnessNy WitnessNz) :
    axisWitnessEndpointUnitPotential ((vertexFinEquiv WitnessNx WitnessNy WitnessNz).symm v) =
      if v = axisWitnessEndpoint0 ∨ v = axisWitnessEndpoint1 then 1 else 0 := by
  dsimp [axisWitnessEndpointUnitPotential]
  simp_rw [(vertexFinEquiv WitnessNx WitnessNy WitnessNz).symm.injective.eq_iff]

def axisWitnessEndpointXi (v : Vertex WitnessNx WitnessNy WitnessNz) : ℝ :=
  if v = axisWitnessEndpoint0 ∨ v = axisWitnessEndpoint1 then 1 else 0

theorem axisWitnessEndpointUnitPotential_apply_eq_xi (v : Vertex WitnessNx WitnessNy WitnessNz) :
    axisWitnessEndpointUnitPotential ((vertexFinEquiv WitnessNx WitnessNy WitnessNz).symm v) =
      axisWitnessEndpointXi v := by
  rw [axisWitnessEndpointUnitPotential_apply]
  rfl

def axisWitnessFlatEdgeLengthDir (pair : FreudenthalLocalPair) (k : Fin 6) : ℝ :=
  let cell := axisWitnessCell pair
  let uv := Geometry.ReggeRigorousFoundation.edgeVertices k
  let v0 := addVertexBits cell (Geometry.FreudenthalCubeTriangulation.tetVerts pair.1 uv.1)
  let v1 := addVertexBits cell (Geometry.FreudenthalCubeTriangulation.tetVerts pair.1 uv.2)
  Real.sqrt (Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges k) *
    (axisWitnessEndpointXi v0 + axisWitnessEndpointXi v1) / 2

def axisWitnessPairSummand (pair : FreudenthalLocalPair) : ℝ :=
  ∑ k : Fin 6,
    freudenthalLocalPairClosedFormSchlaefliCoeff pair k * axisWitnessFlatEdgeLengthDir pair k

private lemma axisWitness_tetVertPotential_eq_xi (pair : FreudenthalLocalPair) (u : Fin 4) :
    axisWitnessEndpointUnitPotential
        ((canonicalEncodedPeriodicFreudenthalTorus WitnessNx WitnessNy WitnessNz witnessHx witnessHy
            witnessHz).K.tetVerts
          ((canonicalEncodedPeriodicFreudenthalTorus WitnessNx WitnessNy WitnessNz witnessHx witnessHy
              witnessHz).tetEquiv.symm (axisWitnessCell pair, pair.1)) u) =
      axisWitnessEndpointXi
        (addVertexBits (axisWitnessCell pair)
          (Geometry.FreudenthalCubeTriangulation.tetVerts pair.1 u)) := by
  rw [canonicalEncodedPeriodic_tetVerts_addVertexBits, axisWitnessEndpointUnitPotential_apply_eq_xi]

private lemma axisWitness_flatEdgeLengthDir_eq_explicit (pair : FreudenthalLocalPair) (k : Fin 6) :
    freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv witnessHx witnessHy witnessHz
        axisWitnessEndpointUnitPotential (axisWitnessCell pair) pair.1 k =
      axisWitnessFlatEdgeLengthDir pair k := by
  dsimp [freudenthalExplicitFiberFlatLocalEdgeLengthDirectionalDeriv, axisWitnessFlatEdgeLengthDir]
  simp only [Geometry.ReggeRigorousFoundation.edgeVertices]
  rw [axisWitness_tetVertPotential_eq_xi pair, axisWitness_tetVertPotential_eq_xi pair]
  ring_nf

private theorem axisWitness_explicitPairSummand_eq_local (pair : FreudenthalLocalPair)
    (hp : pair ∈ freudenthalLocalPairDispFiber 0) :
    freudenthalExplicitFiberPairClosedFormExpandedSummand witnessHx witnessHy witnessHz
        axisWitnessEndpointUnitPotential axisWitnessEdge pair =
      axisWitnessPairSummand pair := by
  dsimp [freudenthalExplicitFiberPairClosedFormExpandedSummand, axisWitnessPairSummand,
    freudenthalLocalPairClosedFormExpandedSummand]
  rw [axisWitness_selectedCell_eq pair hp]
  refine Finset.sum_congr rfl ?_
  intro k _
  dsimp [freudenthalLocalPairClosedFormSchlaefliCoeff]
  rw [axisWitness_flatEdgeLengthDir_eq_explicit pair k]

def axisWitnessDisp0LocalFiberSum : ℝ :=
  ∑ pair ∈ freudenthalLocalPairDispFiber 0, axisWitnessPairSummand pair

/-- Local combinatorial fiber sum matches the finite audit table. -/
def FreudenthalAxisDisp0LocalFiberSumEqAuditTarget : Prop :=
  axisWitnessDisp0LocalFiberSum = freudenthalAxisDisp0EndpointUnitAuditSum

/-- Per-pair audit values for class-0 axis witness (Python
`scripts/freudenthal_explicit_fiber_endpoint_analysis.py`).  Discharge of
`FreudenthalAxisDisp0LocalFiberSumEqAuditTarget` is via six
`Finset.sum_eq_single` + `norm_num` certificates; generator:
`scripts/generate_axis_disp0_summand_proofs.py`. -/
def axisWitnessPairSummandAudit (pair : FreudenthalLocalPair) : ℝ :=
  match pair with
  | (0, 0) => -1 / 2
  | (1, 0) => -1 / 2
  | (2, 3) => -1
  | (3, 5) => -1 / 2
  | (4, 3) => -1
  | (5, 5) => -1 / 2
  | _ => 0

def FreudenthalAxisDisp0PairSummandEqAuditTarget (pair : FreudenthalLocalPair)
    (_hp : pair ∈ freudenthalLocalPairDispFiber 0) : Prop :=
  axisWitnessPairSummand pair = axisWitnessPairSummandAudit pair

def FreudenthalAxisDisp0AllPairSummandsEqAuditTarget : Prop :=
  ∀ pair (hp : pair ∈ freudenthalLocalPairDispFiber 0),
    FreudenthalAxisDisp0PairSummandEqAuditTarget pair hp

open FreudenthalLengthChainEndpointCert

set_option maxHeartbeats 2000000 in

private lemma axisWitness_neg_sqrt_half_product :
    (-Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = -1 / 2 := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  field_simp [hne]
  nlinarith [hsq]

private lemma axisWitnessSchlaefli_zero_iff (pair : FreudenthalLocalPair) (k : Fin 6)
    (hk : freudenthalSchlaefliPolySummandNormTable pair.2 k = 0) :
    freudenthalLocalPairClosedFormSchlaefliCoeff pair k = 0 := by
  rw [freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table, hk]
  simp

private lemma axisWitnessFlatEdgeLengthDir_zero_of_xi_zero
    (pair : FreudenthalLocalPair) (k : Fin 6)
    (hv0 : axisWitnessEndpointXi (addVertexBits (axisWitnessCell pair)
      (Geometry.FreudenthalCubeTriangulation.tetVerts pair.1
        (Geometry.ReggeRigorousFoundation.edgeVertices k).1)) = 0)
    (hv1 : axisWitnessEndpointXi (addVertexBits (axisWitnessCell pair)
      (Geometry.FreudenthalCubeTriangulation.tetVerts pair.1
        (Geometry.ReggeRigorousFoundation.edgeVertices k).2)) = 0) :
    axisWitnessFlatEdgeLengthDir pair k = 0 := by
  dsimp [axisWitnessFlatEdgeLengthDir]
  simp [hv0, hv1]

private lemma axisWitnessPairSummand_00 :
    axisWitnessPairSummand (0, 0) = (-1 / 2 : ℝ) := by
  dsimp [axisWitnessPairSummand]
  rw [Finset.sum_eq_single (4 : Fin 6)]
  · dsimp [axisWitnessFlatEdgeLengthDir]
    simp only [Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
      addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
      Geometry.ReggeRigorousFoundation.edgeVertices,
      freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
      freudenthalSchlaefliPolySummandNormTable, axisWitnessEndpoint0,
      axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
    field_simp
    ring_nf
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
  · intro b _ hb
    fin_cases b
    all_goals
      dsimp [axisWitnessFlatEdgeLengthDir]
      first
      | exact (hb rfl).elim
      | simp only [
          Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
          addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
          Geometry.ReggeRigorousFoundation.edgeVertices,
          freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
          freudenthalSchlaefliPolySummandNormTable, Real.sqrt_eq_rpow, axisWitnessEndpoint0,
          axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
        norm_num
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

private lemma axisWitnessPairSummand_10 :
    axisWitnessPairSummand (1, 0) = (-1 / 2 : ℝ) := by
  dsimp [axisWitnessPairSummand]
  rw [Finset.sum_eq_single (4 : Fin 6)]
  · dsimp [axisWitnessFlatEdgeLengthDir]
    simp only [Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
      addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
      Geometry.ReggeRigorousFoundation.edgeVertices,
      freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
      freudenthalSchlaefliPolySummandNormTable, axisWitnessEndpoint0,
      axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
    field_simp
    ring_nf
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
  · intro b _ hb
    fin_cases b
    all_goals
      dsimp [axisWitnessFlatEdgeLengthDir]
      first
      | exact (hb rfl).elim
      | simp only [
          Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
          addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
          Geometry.ReggeRigorousFoundation.edgeVertices,
          freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
          freudenthalSchlaefliPolySummandNormTable, Real.sqrt_eq_rpow, axisWitnessEndpoint0,
          axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
        norm_num
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

private lemma axisWitnessPairSummand_35 :
    axisWitnessPairSummand (3, 5) = (-1 / 2 : ℝ) := by
  dsimp [axisWitnessPairSummand]
  rw [Finset.sum_eq_single (1 : Fin 6)]
  · dsimp [axisWitnessFlatEdgeLengthDir]
    simp only [Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
      addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
      Geometry.ReggeRigorousFoundation.edgeVertices,
      freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
      freudenthalSchlaefliPolySummandNormTable, axisWitnessEndpoint0,
      axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
    field_simp
    ring_nf
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
  · intro b _ hb
    fin_cases b
    all_goals
      dsimp [axisWitnessFlatEdgeLengthDir]
      first
      | exact (hb rfl).elim
      | simp only [
          Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
          addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
          Geometry.ReggeRigorousFoundation.edgeVertices,
          freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
          freudenthalSchlaefliPolySummandNormTable, Real.sqrt_eq_rpow, axisWitnessEndpoint0,
          axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
        norm_num
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

private lemma axisWitnessPairSummand_55 :
    axisWitnessPairSummand (5, 5) = (-1 / 2 : ℝ) := by
  dsimp [axisWitnessPairSummand]
  rw [Finset.sum_eq_single (1 : Fin 6)]
  · dsimp [axisWitnessFlatEdgeLengthDir]
    simp only [Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
      addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
      Geometry.ReggeRigorousFoundation.edgeVertices,
      freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
      freudenthalSchlaefliPolySummandNormTable, axisWitnessEndpoint0,
      axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
    field_simp
    ring_nf
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
  · intro b _ hb
    fin_cases b
    all_goals
      dsimp [axisWitnessFlatEdgeLengthDir]
      first
      | exact (hb rfl).elim
      | simp only [
          Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
          addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
          Geometry.ReggeRigorousFoundation.edgeVertices,
          freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
          freudenthalSchlaefliPolySummandNormTable, Real.sqrt_eq_rpow, axisWitnessEndpoint0,
          axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
        norm_num
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

private lemma axisWitnessPairSummand_23_inactive (k : Fin 6)
    (hk : k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 4) :
    freudenthalLocalPairClosedFormSchlaefliCoeff (2, 3) k *
        axisWitnessFlatEdgeLengthDir (2, 3) k = 0 := by
  fin_cases k
  · dsimp [axisWitnessFlatEdgeLengthDir]
    simp only [
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
      addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
      Geometry.ReggeRigorousFoundation.edgeVertices,
      freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
      freudenthalSchlaefliPolySummandNormTable, axisWitnessEndpoint0,
      axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
    norm_num
  · exact (hk.1 rfl).elim
  · dsimp [axisWitnessFlatEdgeLengthDir]
    simp only [
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
      addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
      Geometry.ReggeRigorousFoundation.edgeVertices,
      freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
      freudenthalSchlaefliPolySummandNormTable, axisWitnessEndpoint0,
      axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
    norm_num
  · exact (hk.2.1 rfl).elim
  · exact (hk.2.2 rfl).elim
  · dsimp [axisWitnessFlatEdgeLengthDir]
    simp only [
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
      addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
      Geometry.ReggeRigorousFoundation.edgeVertices,
      freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
      freudenthalSchlaefliPolySummandNormTable, axisWitnessEndpoint0,
      axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
    norm_num

private lemma axisWitnessFin6_ne_of_not_mem_134 (k : Fin 6)
    (hk : k ∉ ({1, 3, 4} : Finset (Fin 6))) : k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 4 := by
  fin_cases k <;> simp [Finset.mem_insert, Finset.mem_singleton] at hk ⊢

private lemma axisWitnessPairSummand_23 :
    axisWitnessPairSummand (2, 3) = (-1 : ℝ) := by
  dsimp [axisWitnessPairSummand]
  have hsum :
      ∑ k : Fin 6, freudenthalLocalPairClosedFormSchlaefliCoeff (2, 3) k *
          axisWitnessFlatEdgeLengthDir (2, 3) k =
        freudenthalLocalPairClosedFormSchlaefliCoeff (2, 3) 1 *
            axisWitnessFlatEdgeLengthDir (2, 3) 1 +
          freudenthalLocalPairClosedFormSchlaefliCoeff (2, 3) 3 *
            axisWitnessFlatEdgeLengthDir (2, 3) 3 +
          freudenthalLocalPairClosedFormSchlaefliCoeff (2, 3) 4 *
            axisWitnessFlatEdgeLengthDir (2, 3) 4 := by
    rw [← Finset.sum_subset (Finset.subset_univ ({1, 3, 4} : Finset (Fin 6)))
      fun k _ hk =>
        axisWitnessPairSummand_23_inactive k (axisWitnessFin6_ne_of_not_mem_134 k hk)]
    rw [show ({1, 3, 4} : Finset (Fin 6)) = insert 1 (insert 3 {4}) from by decide]
    simp [Finset.sum_insert, Finset.sum_singleton]
    ring_nf
  rw [hsum]
  dsimp [axisWitnessFlatEdgeLengthDir]
  simp only [
    Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
    addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
    Geometry.ReggeRigorousFoundation.edgeVertices,
    freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
    freudenthalSchlaefliPolySummandNormTable, axisWitnessEndpoint0,
    axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
  field_simp
  ring_nf
  norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private lemma axisWitnessPairSummand_43_inactive (k : Fin 6)
    (hk : k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 4) :
    freudenthalLocalPairClosedFormSchlaefliCoeff (4, 3) k *
        axisWitnessFlatEdgeLengthDir (4, 3) k = 0 := by
  fin_cases k
  · dsimp [axisWitnessFlatEdgeLengthDir]
    simp only [
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
      addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
      Geometry.ReggeRigorousFoundation.edgeVertices,
      freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
      freudenthalSchlaefliPolySummandNormTable, axisWitnessEndpoint0,
      axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
    norm_num
  · exact (hk.1 rfl).elim
  · dsimp [axisWitnessFlatEdgeLengthDir]
    simp only [
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
      addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
      Geometry.ReggeRigorousFoundation.edgeVertices,
      freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
      freudenthalSchlaefliPolySummandNormTable, axisWitnessEndpoint0,
      axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
    norm_num
  · exact (hk.2.1 rfl).elim
  · exact (hk.2.2 rfl).elim
  · dsimp [axisWitnessFlatEdgeLengthDir]
    simp only [
      Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
      addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
      Geometry.ReggeRigorousFoundation.edgeVertices,
      freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
      freudenthalSchlaefliPolySummandNormTable, axisWitnessEndpoint0,
      axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
    norm_num

private lemma axisWitnessPairSummand_43 :
    axisWitnessPairSummand (4, 3) = (-1 : ℝ) := by
  dsimp [axisWitnessPairSummand]
  have hsum :
      ∑ k : Fin 6, freudenthalLocalPairClosedFormSchlaefliCoeff (4, 3) k *
          axisWitnessFlatEdgeLengthDir (4, 3) k =
        freudenthalLocalPairClosedFormSchlaefliCoeff (4, 3) 1 *
            axisWitnessFlatEdgeLengthDir (4, 3) 1 +
          freudenthalLocalPairClosedFormSchlaefliCoeff (4, 3) 3 *
            axisWitnessFlatEdgeLengthDir (4, 3) 3 +
          freudenthalLocalPairClosedFormSchlaefliCoeff (4, 3) 4 *
            axisWitnessFlatEdgeLengthDir (4, 3) 4 := by
    rw [← Finset.sum_subset (Finset.subset_univ ({1, 3, 4} : Finset (Fin 6)))
      fun k _ hk =>
        axisWitnessPairSummand_43_inactive k (axisWitnessFin6_ne_of_not_mem_134 k hk)]
    rw [show ({1, 3, 4} : Finset (Fin 6)) = insert 1 (insert 3 {4}) from by decide]
    simp [Finset.sum_insert, Finset.sum_singleton]
    ring_nf
  rw [hsum]
  dsimp [axisWitnessFlatEdgeLengthDir]
  simp only [
    Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges, addVertexBits, addBits,
    addBit, bit, vertexBits, Geometry.FreudenthalCubeTriangulation.tetVerts,
    Geometry.ReggeRigorousFoundation.edgeVertices,
    freudenthalLocalPairClosedFormSchlaefliCoeff_eq_table,
    freudenthalSchlaefliPolySummandNormTable, axisWitnessEndpoint0,
    axisWitnessEndpoint1, axisWitnessEndpointXi, axisWitnessCell, Fin.ext_iff, Prod.mk.injEq]
  field_simp
  ring_nf
  norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem FreudenthalAxisDisp0AllPairSummandsEqAuditTarget_holds :
    FreudenthalAxisDisp0AllPairSummandsEqAuditTarget := by
  intro pair hp
  dsimp [FreudenthalAxisDisp0PairSummandEqAuditTarget, axisWitnessPairSummandAudit]
  have hp' :
      pair = (0, 0) ∨ pair = (1, 0) ∨ pair = (2, 3) ∨ pair = (3, 5) ∨ pair = (4, 3) ∨
        pair = (5, 5) := by
    simpa [freudenthalLocalPairDispFiber] using hp
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact axisWitnessPairSummand_00
  · exact axisWitnessPairSummand_10
  · exact axisWitnessPairSummand_23
  · exact axisWitnessPairSummand_35
  · exact axisWitnessPairSummand_43
  · exact axisWitnessPairSummand_55

theorem FreudenthalAxisDisp0LocalFiberSumEqAuditTarget_holds :
    FreudenthalAxisDisp0LocalFiberSumEqAuditTarget := by
  dsimp [FreudenthalAxisDisp0LocalFiberSumEqAuditTarget, axisWitnessDisp0LocalFiberSum]
  have hfiber :
      ∑ pair ∈ freudenthalLocalPairDispFiber 0, axisWitnessPairSummand pair =
        axisWitnessPairSummand (0, 0) + axisWitnessPairSummand (1, 0) +
          axisWitnessPairSummand (2, 3) + axisWitnessPairSummand (3, 5) +
          axisWitnessPairSummand (4, 3) + axisWitnessPairSummand (5, 5) := by
    simp [freudenthalLocalPairDispFiber, Finset.sum_insert, Finset.sum_singleton]
    ring_nf
  rw [hfiber, axisWitnessPairSummand_00, axisWitnessPairSummand_10, axisWitnessPairSummand_23,
    axisWitnessPairSummand_35, axisWitnessPairSummand_43, axisWitnessPairSummand_55,
    freudenthalAxisDisp0EndpointUnitAuditSum]

/-- Per-pair identification: explicit-fiber closed-form summand equals the local
flat length-chain audit summand on the axis witness at endpoint-unit data. -/
def FreudenthalAxisDisp0PairExplicitSummandEqLocalTarget
    (pair : FreudenthalLocalPair) (_hp : pair ∈ freudenthalLocalPairDispFiber 0) : Prop :=
  freudenthalExplicitFiberPairClosedFormExpandedSummand witnessHx witnessHy witnessHz
      axisWitnessEndpointUnitPotential axisWitnessEdge pair =
    axisWitnessPairSummand pair

def FreudenthalAxisDisp0AllPairExplicitSummandsEqLocalTarget : Prop :=
  ∀ pair (hp : pair ∈ freudenthalLocalPairDispFiber 0),
    FreudenthalAxisDisp0PairExplicitSummandEqLocalTarget pair hp

theorem FreudenthalAxisDisp0AllPairExplicitSummandsEqLocalTarget_holds :
    FreudenthalAxisDisp0AllPairExplicitSummandsEqLocalTarget := by
  intro pair hp
  dsimp [FreudenthalAxisDisp0PairExplicitSummandEqLocalTarget]
  exact axisWitness_explicitPairSummand_eq_local pair hp

/-- Global closed-form fiber sum at the endpoint-unit potential on the axis witness edge. -/
def FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget : Prop :=
  freudenthalExplicitFiberClosedFormFiberSum witnessHx witnessHy witnessHz
      axisWitnessEndpointUnitPotential axisWitnessEdge 0 =
    (-4 : ℝ)

/-- Bridge: global explicit-fiber sum equals the local audit sum on the axis witness. -/
def FreudenthalAxisDisp0GlobalFiberSumEqLocalTarget : Prop :=
  freudenthalExplicitFiberClosedFormFiberSum witnessHx witnessHy witnessHz
      axisWitnessEndpointUnitPotential axisWitnessEdge 0 =
    axisWitnessDisp0LocalFiberSum

theorem FreudenthalAxisDisp0GlobalFiberSumEqLocalTarget_of_all_pair_explicit
    (hAll : FreudenthalAxisDisp0AllPairExplicitSummandsEqLocalTarget) :
    FreudenthalAxisDisp0GlobalFiberSumEqLocalTarget := by
  dsimp [FreudenthalAxisDisp0GlobalFiberSumEqLocalTarget, axisWitnessDisp0LocalFiberSum, axisWitnessEdge]
  refine Eq.trans
    (freudenthalExplicitFiberClosedFormFiberSum_eq_disp_fiber witnessHx witnessHy witnessHz
      axisWitnessEndpointUnitPotential axisWitnessEdge) ?_
  refine Finset.sum_congr rfl ?_
  intro pair hp
  exact hAll pair hp

theorem FreudenthalAxisDisp0GlobalFiberSumEqLocalTarget_holds :
    FreudenthalAxisDisp0GlobalFiberSumEqLocalTarget :=
  FreudenthalAxisDisp0GlobalFiberSumEqLocalTarget_of_all_pair_explicit
    FreudenthalAxisDisp0AllPairExplicitSummandsEqLocalTarget_holds

theorem FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget_of_local_and_audit
    (hLocal : FreudenthalAxisDisp0GlobalFiberSumEqLocalTarget)
    (hAudit : FreudenthalAxisDisp0LocalFiberSumEqAuditTarget) :
    FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget := by
  dsimp [FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget,
    FreudenthalAxisDisp0GlobalFiberSumEqLocalTarget, FreudenthalAxisDisp0LocalFiberSumEqAuditTarget]
  rw [hLocal, hAudit, freudenthalAxisDisp0EndpointUnitAuditSum_eq_neg_four]

theorem FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget_of_local
    (hLocal : FreudenthalAxisDisp0GlobalFiberSumEqLocalTarget) :
    FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget :=
  FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget_of_local_and_audit hLocal
    FreudenthalAxisDisp0LocalFiberSumEqAuditTarget_holds

theorem FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget_of_all_pair_explicit
    (hAll : FreudenthalAxisDisp0AllPairExplicitSummandsEqLocalTarget) :
    FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget :=
  FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget_of_local
    (FreudenthalAxisDisp0GlobalFiberSumEqLocalTarget_of_all_pair_explicit hAll)

theorem FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget_holds :
    FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget :=
  FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget_of_local
    FreudenthalAxisDisp0GlobalFiberSumEqLocalTarget_holds

/-- Bilinear endpoint template is inconsistent with a certified endpoint-unit fiber sum `-4`. -/
theorem FreudenthalExplicitFiberBilinearEndpointTemplateTarget_false_of_endpointUnitSum_neg_four
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (edge : PeriodicEdge Nx Ny Nz)
    (hdisp : edge.disp = 0)
    (endpoint0 endpoint1 : Vertex Nx Ny Nz)
    (hend : edge.endpoints = (endpoint0, endpoint1))
    (hSum :
      freudenthalExplicitFiberClosedFormFiberSum hx hy hz
          (fun i =>
            if i = (vertexFinEquiv Nx Ny Nz).symm endpoint0 ∨
                i = (vertexFinEquiv Nx Ny Nz).symm endpoint1 then
              1
            else 0)
          edge 0 =
        (-4 : ℝ))
    (hBilinear :
      FreudenthalExplicitFiberBilinearEndpointTemplateTarget Nx Ny Nz hx hy hz 0) :
    False := by
  rcases hBilinear with ⟨F, hTemplate, hFiber⟩
  have hF11 :=
    FreudenthalLocalDispLengthChainEndpointTemplateTarget_F_eq_zero_at_one_one 0 F hTemplate
  let ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K :=
    fun i =>
      if i = (vertexFinEquiv Nx Ny Nz).symm endpoint0 ∨
          i = (vertexFinEquiv Nx Ny Nz).symm endpoint1 then
        1
      else 0
  have hsum := hFiber ξ edge hdisp
  have hξ0 : ξ ((vertexFinEquiv Nx Ny Nz).symm endpoint0) = 1 := by
    dsimp only [ξ]
    rw [if_pos (Or.inl rfl)]
  have hξ1 : ξ ((vertexFinEquiv Nx Ny Nz).symm endpoint1) = 1 := by
    dsimp only [ξ]
    rw [if_pos (Or.inr rfl)]
  have hend1 : edge.endpoints.1 = endpoint0 := by simp [hend]
  have hend2 : edge.endpoints.2 = endpoint1 := by simp [hend]
  have hsum' :
      freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge 0 =
        F (ξ ((vertexFinEquiv Nx Ny Nz).symm endpoint0))
          (ξ ((vertexFinEquiv Nx Ny Nz).symm endpoint1)) := by
    simpa [hend1, hend2] using hsum
  rw [hξ0, hξ1, hF11] at hsum'
  linarith

theorem FreudenthalExplicitFiberBilinearEndpointTemplateTarget_false_at_disp0_of_globalWitness
    (hGlobal : FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget)
    (hBilinear :
      FreudenthalExplicitFiberBilinearEndpointTemplateTarget WitnessNx WitnessNy WitnessNz
        witnessHx witnessHy witnessHz 0) :
    False :=
  FreudenthalExplicitFiberBilinearEndpointTemplateTarget_false_of_endpointUnitSum_neg_four
    witnessHx witnessHy witnessHz axisWitnessEdge (by rfl) axisWitnessEndpoint0 axisWitnessEndpoint1
    axisWitness_edge_endpoints
    (by simpa [FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget] using hGlobal) hBilinear

theorem FreudenthalExplicitFiberBilinearEndpointTemplateTarget_false_at_disp0 :
    FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget →
      FreudenthalExplicitFiberBilinearEndpointTemplateTarget WitnessNx WitnessNy WitnessNz
        witnessHx witnessHy witnessHz 0 → False :=
  FreudenthalExplicitFiberBilinearEndpointTemplateTarget_false_at_disp0_of_globalWitness

theorem FreudenthalExplicitFiberBilinearEndpointTemplateTarget_false_at_disp0_unconditional :
    FreudenthalExplicitFiberBilinearEndpointTemplateTarget WitnessNx WitnessNy WitnessNz
        witnessHx witnessHy witnessHz 0 → False :=
  FreudenthalExplicitFiberBilinearEndpointTemplateTarget_false_at_disp0
    FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget_holds

/-- The per-disp explicit-fiber mixed identity fails at axis class `0` on the
endpoint-unit counterexample: fiber sum `-4` forces LHS `4` while RHS is `0`. -/
theorem FreudenthalAxisDisp0ExplicitFiberClosedFormPerDispTarget_zero_false :
    ¬ CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget
      WitnessNx WitnessNy WitnessNz witnessHx witnessHy witnessHz 0 := by
  intro h
  have hc := h axisWitnessEndpointUnitPotential axisWitnessEdge rfl
  have hsum := FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget_holds
  rw [axisWitness_edge_endpoints, hsum,
    axisWitnessEndpointUnitPotential_apply_eq_xi axisWitnessEndpoint0,
    axisWitnessEndpointUnitPotential_apply_eq_xi axisWitnessEndpoint1] at hc
  have hξ0 : axisWitnessEndpointXi axisWitnessEndpoint0 = 1 := by
    simp [axisWitnessEndpointXi, axisWitnessEndpoint0]
  have hξ1 : axisWitnessEndpointXi axisWitnessEndpoint1 = 1 := by
    simp [axisWitnessEndpointXi, axisWitnessEndpoint1, axisWitnessEndpoint0]
  rw [hξ0, hξ1] at hc
  have hs := periodicDispSqEdge_sqrt_ne_zero (0 : Fin 7)
  have hFourMul :
      Real.sqrt (periodicDispSqEdge 0) * (4 : ℝ) = 0 := by
    calc
      Real.sqrt (periodicDispSqEdge 0) * (4 : ℝ) =
          Real.sqrt (periodicDispSqEdge 0) * (1 + 1) / 2 * (-(-4 : ℝ)) := by ring
      _ = Real.sqrt (periodicDispSqEdge 0) * (1 - 1) ^ (2 : ℕ) := hc
      _ = 0 := by norm_num
  rw [mul_eq_zero] at hFourMul
  rcases hFourMul with hsZero | hFourZero
  · exact False.elim (hs hsZero)
  · norm_num at hFourZero

theorem FreudenthalAxisDisp0ExplicitFiberFlatUnfoldedTarget_false :
    ¬ CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget
      WitnessNx WitnessNy WitnessNz witnessHx witnessHy witnessHz := by
  intro h
  have hc := h axisWitnessEndpointUnitPotential axisWitnessEdge
  have hsum := FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget_holds
  have hflatSum :
      (∑ pair ∈ freudenthalLocalPairDispFiber axisWitnessEdge.disp,
          freudenthalExplicitFiberPairFlatExpandedSummand witnessHx witnessHy witnessHz
            axisWitnessEndpointUnitPotential axisWitnessEdge pair) =
        (-4 : ℝ) := by
    rw [freudenthalExplicitFiberFlatDispFiberSum_eq_closedFormFiberSum]
    dsimp [FreudenthalAxisDisp0GlobalEndpointUnitFiberSumTarget] at hsum
    exact hsum
  dsimp [CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget] at hc
  rw [hingeMeasureDirectionalDeriv_canonicalEncodedPeriodic_edge,
    axisWitness_edge_endpoints,
    axisWitnessEndpointUnitPotential_apply_eq_xi axisWitnessEndpoint0,
    axisWitnessEndpointUnitPotential_apply_eq_xi axisWitnessEndpoint1,
    hflatSum] at hc
  have hs := periodicDispSqEdge_sqrt_ne_zero (0 : Fin 7)
  have hFourMul : Real.sqrt (periodicDispSqEdge 0) * (4 : ℝ) = 0 := by
    calc
      Real.sqrt (periodicDispSqEdge 0) * (4 : ℝ) =
          Real.sqrt (periodicDispSqEdge 0) * (1 + 1) / 2 * (-(-4 : ℝ)) := by ring
      _ = Real.sqrt (periodicDispSqEdge 0) * (1 - 1) ^ (2 : ℕ) := hc
      _ = 0 := by norm_num
  rw [mul_eq_zero] at hFourMul
  rcases hFourMul with hsZero | hFourZero
  · exact False.elim (hs hsZero)
  · norm_num at hFourZero

end AxisDisp0EndpointUnitWitness5

theorem FreudenthalExplicitFiberEndpointDependenceTarget_of_bilinearEndpoint
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) (d : Fin 7)
    (hBilinear : FreudenthalExplicitFiberBilinearEndpointTemplateTarget Nx Ny Nz hx hy hz d) :
    FreudenthalExplicitFiberEndpointDependenceTarget Nx Ny Nz hx hy hz d := by
  rcases hBilinear with ⟨F, _, hFiber⟩
  exact ⟨F, hFiber⟩

/-- Alias for the per-displacement explicit-fiber bilinear target (bilinear form). -/
def CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispBilinearTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) (d : Fin 7) : Prop :=
  CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget
    Nx Ny Nz hx hy hz d

/-- The three distinct explicit-fiber bilinear identities (axis, face-diagonal,
body-diagonal). -/
def CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormThreeBilinearTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispBilinearTarget
      Nx Ny Nz hx hy hz 0 ∧
    CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispBilinearTarget
      Nx Ny Nz hx hy hz 3 ∧
    CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispBilinearTarget
      Nx Ny Nz hx hy hz 6

theorem CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget_of_endpointTemplate
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) (d : Fin 7)
    (F : ℝ → ℝ → ℝ)
    (hFiberSum :
      ∀ (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (edge : PeriodicEdge Nx Ny Nz),
        edge.disp = d →
          freudenthalExplicitFiberClosedFormFiberSum hx hy hz ξ edge d =
            F (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1))
              (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)))
    (hTemplate : FreudenthalLocalDispLengthChainEndpointTemplateTarget d F) :
    CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget
      Nx Ny Nz hx hy hz d := by
  intro ξ edge hdisp
  have hsum := hFiberSum ξ edge hdisp
  have htemp := hTemplate
    (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1))
    (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2))
  simpa [CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget,
    hingeMeasureDirectionalDeriv_canonicalEncodedPeriodic_edge, hdisp, hsum] using htemp

theorem CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget_of_bilinearEndpoint
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) (d : Fin 7)
    (hBilinear : FreudenthalExplicitFiberBilinearEndpointTemplateTarget Nx Ny Nz hx hy hz d) :
    CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget
      Nx Ny Nz hx hy hz d := by
  rcases hBilinear with ⟨F, hTemplate, hFiber⟩
  exact CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget_of_endpointTemplate
    Nx Ny Nz hx hy hz d F hFiber hTemplate

/-- All seven displacement classes satisfy the explicit-fiber bilinear identity. -/
def CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormAllBilinearTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  ∀ d : Fin 7,
    CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispBilinearTarget
      Nx Ny Nz hx hy hz d

theorem FreudenthalAxisDisp0ExplicitFiberClosedFormAllBilinearTarget_false :
    ¬ CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormAllBilinearTarget
      AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
      AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
      AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz :=
  fun h =>
    AxisDisp0EndpointUnitWitness5.FreudenthalAxisDisp0ExplicitFiberClosedFormPerDispTarget_zero_false
      (h 0)

theorem canonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget_of_allBilinear
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hAll :
      CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormAllBilinearTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  have hdisp := hAll edge.disp ξ edge rfl
  simpa [CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget,
    hingeMeasureDirectionalDeriv_canonicalEncodedPeriodic_edge,
    freudenthalExplicitFiberClosedFormFiberSum_eq_disp_fiber, P] using hdisp

theorem canonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget_of_perDisp
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hPerDisp :
      ∀ d : Fin 7,
        CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget
          Nx Ny Nz hx hy hz d) :
    CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  have hdisp := hPerDisp edge.disp ξ edge rfl
  simpa [CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget,
    hingeMeasureDirectionalDeriv_canonicalEncodedPeriodic_edge,
    freudenthalExplicitFiberClosedFormFiberSum_eq_disp_fiber, P] using hdisp

theorem canonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget_of_closedForm
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (d : Fin 7)
    (hClosedForm :
      CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget
      Nx Ny Nz hx hy hz d := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge hdisp
  have hfull := hClosedForm ξ edge
  simpa [CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget,
    CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget,
    hingeMeasureDirectionalDeriv_canonicalEncodedPeriodic_edge,
    freudenthalExplicitFiberClosedFormFiberSum_eq_disp_fiber, hdisp, P] using hfull

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget_of_flatUnfolded
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFlatUnfolded :
      CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  have hsum :
      (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz ξ edge pair) =
        ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair := by
    refine Finset.sum_congr rfl ?_
    intro pair _
    exact freudenthalExplicitFiberPairFlatExpandedSummand_eq_expanded hx hy hz ξ edge pair
  simpa [CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget,
    CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget, hsum, P] using
    hFlatUnfolded ξ edge

theorem canonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget_of_expandedLengthChainExplicitFiber
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hExplicit :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  have hsum :
      (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair) =
        ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz ξ edge pair := by
    refine Finset.sum_congr rfl ?_
    intro pair _
    exact (freudenthalExplicitFiberPairFlatExpandedSummand_eq_expanded hx hy hz ξ edge pair).symm
  simpa [CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget,
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget, hsum, P] using
    hExplicit ξ edge

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget_iff_flatUnfolded
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget
      Nx Ny Nz hx hy hz ↔
      CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget
        Nx Ny Nz hx hy hz :=
  ⟨canonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget_of_flatUnfolded
      Nx Ny Nz hx hy hz,
    canonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget_of_expandedLengthChainExplicitFiber
      Nx Ny Nz hx hy hz⟩

theorem FreudenthalAxisDisp0ExplicitFiberExpandedLengthChainExplicitFiberTarget_false :
    ¬ CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget
      AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
      AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
      AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz :=
  fun h =>
    AxisDisp0EndpointUnitWitness5.FreudenthalAxisDisp0ExplicitFiberFlatUnfoldedTarget_false
      (canonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget_of_expandedLengthChainExplicitFiber
        AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
        AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
        AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz h)

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_not_of_closedFormPerDisp_at_axisWitness
    (hPerDisp :
      ∀ d : Fin 7,
        CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget
          AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
          AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
          AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz d) :
    False :=
  AxisDisp0EndpointUnitWitness5.FreudenthalAxisDisp0ExplicitFiberClosedFormPerDispTarget_zero_false
    (hPerDisp 0)

/-- Canonical periodic Track 1.B second-order Schläfli stationarity, packaged at
the flat configuration already discharged for the encoded Freudenthal torus. -/
def CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  WeightedDeficitDerivativeStationaryTarget
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
    (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz)

def CanonicalPeriodicSecondSchlaefliAlongLineTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  SecondSchlaefliAlongLineTarget
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
    (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz)

/-- Typed-periodic-edge form of the second-order Schläfli target.  This is the
same stationarity identity as `CanonicalPeriodicSecondSchlaefliAlongLineTarget`,
but reindexed from anonymous encoded edge indices to `PeriodicEdge` records.
Track `1B-SCH` should use this form for finite-table stationarity work. -/
def CanonicalPeriodicSecondSchlaefliTypedEdgeTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ ξ : VertexPotential P.K,
    (∑ edge : PeriodicEdge Nx Ny Nz,
      let e := P.edgeEquiv.symm edge
      (hingeLineDeriv P.K P.hK ξ e 0 * deficitLineDeriv P.K ξ e 0 +
        hingeMeasureUnderConformal P.K P.hK
          (Geometry.ReggeActionSecondVariation.linePotential P.K ξ 0) e *
          deficitLineSecondDeriv P.K ξ e 0)) = 0

def canonicalPeriodicSecondSchlaefliTypedEdgeSummand
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : PeriodicEdge Nx Ny Nz) : ℝ :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  let e := P.edgeEquiv.symm edge
  hingeLineDeriv P.K P.hK ξ e 0 * deficitLineDeriv P.K ξ e 0 +
    hingeMeasureUnderConformal P.K P.hK
      (Geometry.ReggeActionSecondVariation.linePotential P.K ξ 0) e *
      deficitLineSecondDeriv P.K ξ e 0

/-- Fixed-displacement-class form of the typed second-order Schläfli target. -/
def CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) (d : Fin 7) : Prop :=
  ∀ ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
    (∑ edge ∈ ((Finset.univ : Finset (PeriodicEdge Nx Ny Nz)).filter
        (fun edge => edge.disp = d)),
      canonicalPeriodicSecondSchlaefliTypedEdgeSummand Nx Ny Nz hx hy hz ξ edge) = 0

/-- Per-displacement form of the typed second-order Schläfli target.  This is
the `1B-SCH` finite cancellation table: each of the seven periodic displacement
classes contributes zero separately. -/
def CanonicalPeriodicSecondSchlaefliTypedEdgePerDispTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  ∀ (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (d : Fin 7),
    (∑ edge ∈ ((Finset.univ : Finset (PeriodicEdge Nx Ny Nz)).filter
        (fun edge => edge.disp = d)),
      canonicalPeriodicSecondSchlaefliTypedEdgeSummand Nx Ny Nz hx hy hz ξ edge) = 0

theorem canonicalPeriodicSecondSchlaefliTypedEdgeTarget_of_perDisp
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hDisp : CanonicalPeriodicSecondSchlaefliTypedEdgePerDispTarget Nx Ny Nz hx hy hz) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeTarget Nx Ny Nz hx hy hz := by
  classical
  intro ξ
  let f : PeriodicEdge Nx Ny Nz → ℝ :=
    canonicalPeriodicSecondSchlaefliTypedEdgeSummand Nx Ny Nz hx hy hz ξ
  have hpartition :
      (∑ d : Fin 7,
        ∑ edge ∈ ((Finset.univ : Finset (PeriodicEdge Nx Ny Nz)).filter
          (fun edge => edge.disp = d)), f edge) =
        ∑ edge : PeriodicEdge Nx Ny Nz, f edge := by
    simpa [f] using
      (Finset.sum_fiberwise
        (s := (Finset.univ : Finset (PeriodicEdge Nx Ny Nz)))
        (g := fun edge : PeriodicEdge Nx Ny Nz => edge.disp)
        (f := f))
  have hzero :
      (∑ d : Fin 7,
        ∑ edge ∈ ((Finset.univ : Finset (PeriodicEdge Nx Ny Nz)).filter
          (fun edge => edge.disp = d)), f edge) = 0 := by
    simp [f, hDisp ξ]
  change (∑ edge : PeriodicEdge Nx Ny Nz, f edge) = 0
  rw [← hpartition]
  exact hzero

theorem canonicalPeriodicSecondSchlaefliAlongLineTarget_iff_typedEdge
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicSecondSchlaefliAlongLineTarget Nx Ny Nz hx hy hz ↔
      CanonicalPeriodicSecondSchlaefliTypedEdgeTarget Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  constructor
  · intro hSch ξ
    let F : Fin P.K.nE → ℝ := fun e =>
      hingeLineDeriv P.K P.hK ξ e 0 * deficitLineDeriv P.K ξ e 0 +
        hingeMeasureUnderConformal P.K P.hK
          (Geometry.ReggeActionSecondVariation.linePotential P.K ξ 0) e *
          deficitLineSecondDeriv P.K ξ e 0
    have hreindex :
        (∑ edge : PeriodicEdge Nx Ny Nz, F (P.edgeEquiv.symm edge)) =
          ∑ e : Fin P.K.nE, F e := by
      simpa [F] using (Equiv.sum_comp P.edgeEquiv.symm F)
    rw [hreindex]
    simpa [CanonicalPeriodicSecondSchlaefliAlongLineTarget,
      SecondSchlaefliAlongLineTarget, P, F] using hSch ξ
  · intro hTyped ξ
    let F : Fin P.K.nE → ℝ := fun e =>
      hingeLineDeriv P.K P.hK ξ e 0 * deficitLineDeriv P.K ξ e 0 +
        hingeMeasureUnderConformal P.K P.hK
          (Geometry.ReggeActionSecondVariation.linePotential P.K ξ 0) e *
          deficitLineSecondDeriv P.K ξ e 0
    have hreindex :
        (∑ edge : PeriodicEdge Nx Ny Nz, F (P.edgeEquiv.symm edge)) =
          ∑ e : Fin P.K.nE, F e := by
      simpa [F] using (Equiv.sum_comp P.edgeEquiv.symm F)
    have h0 : (∑ edge : PeriodicEdge Nx Ny Nz, F (P.edgeEquiv.symm edge)) = 0 := by
      simpa [CanonicalPeriodicSecondSchlaefliTypedEdgeTarget, P, F] using hTyped ξ
    have h0e : (∑ e : Fin P.K.nE, F e) = 0 := hreindex.symm.trans h0
    simpa [CanonicalPeriodicSecondSchlaefliAlongLineTarget,
      SecondSchlaefliAlongLineTarget, P, F] using h0e

theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTarget_iff_secondSchlaefli
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget Nx Ny Nz hx hy hz ↔
      CanonicalPeriodicSecondSchlaefliAlongLineTarget Nx Ny Nz hx hy hz := by
  dsimp [CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget,
    CanonicalPeriodicSecondSchlaefliAlongLineTarget]
  exact
    weightedDeficitDerivativeStationaryTarget_iff_secondSchlaefliAlongLine
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
      (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz)

theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTarget_iff_typedEdge
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget Nx Ny Nz hx hy hz ↔
      CanonicalPeriodicSecondSchlaefliTypedEdgeTarget Nx Ny Nz hx hy hz := by
  exact
    (canonicalPeriodicWeightedDeficitDerivativeStationaryTarget_iff_secondSchlaefli
      Nx Ny Nz hx hy hz).trans
      (canonicalPeriodicSecondSchlaefliAlongLineTarget_iff_typedEdge
        Nx Ny Nz hx hy hz)

/-- Stronger punctured-neighbourhood Schläfli form at the canonical periodic flat
configuration.  Implies `CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget`. -/
def CanonicalPeriodicWeightedDeficitDerivativeEventuallyZeroTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  WeightedDeficitDerivativeEventuallyZeroTarget
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
    (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz)

theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTarget_of_eventuallyZero
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      CanonicalPeriodicWeightedDeficitDerivativeEventuallyZeroTarget Nx Ny Nz hx hy hz) :
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget Nx Ny Nz hx hy hz := by
  dsimp [CanonicalPeriodicWeightedDeficitDerivativeEventuallyZeroTarget,
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget] at hZero ⊢
  exact
    weightedDeficitDerivativeStationary_of_eventuallyZero
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
      (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz) hZero

theorem canonicalPeriodicSecondSchlaefliAlongLineTarget_of_eventuallyZero
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      CanonicalPeriodicWeightedDeficitDerivativeEventuallyZeroTarget Nx Ny Nz hx hy hz) :
    CanonicalPeriodicSecondSchlaefliAlongLineTarget Nx Ny Nz hx hy hz :=
  (canonicalPeriodicWeightedDeficitDerivativeStationaryTarget_iff_secondSchlaefli Nx Ny Nz hx hy
      hz).1
    (canonicalPeriodicWeightedDeficitDerivativeStationaryTarget_of_eventuallyZero Nx Ny Nz hx hy
      hz hZero)

/-- The conformal Schläfli identity along the full conformal line on the
canonical periodic Freudenthal torus.  This says `V(t) = 0` for ALL `t`,
where `V(t) = ∑_e h(t•ξ, e) * deficitLineDeriv(ξ, e, t)`.

Proving this single geometric hypothesis (a consequence of the classical
Schläfli differential identity `∑_{e∈τ} ℓ_e dθ_{e,τ} = 0` applied at every
parameter `t` and summed over all tetrahedra) directly closes the full
`CanonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5` without any
per-displacement-class decomposition. -/
def CanonicalPeriodicConformalSchlaefliAlongLineTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  ConformalSchlaefliAlongLineTarget
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK

/-- Canonical periodic local non-flat Schläfli target along conformal lines. -/
def CanonicalPeriodicLocalConformalSchlaefliAlongLineTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  LocalConformalSchlaefliAlongLineTarget
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K

/-- Canonical periodic non-flat expansion/reindexing target for
`∑_e h_e δ'_e` along conformal lines. -/
def CanonicalPeriodicConformalSchlaefliAlongLineExpansionTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  ConformalSchlaefliAlongLineExpansionTarget
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK

/-- Canonical periodic local near-flat non-flat Schläfli target along conformal
lines.  This is the domain-correct version needed for the Hessian proof. -/
def CanonicalPeriodicLocalConformalSchlaefliNearZeroTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  LocalConformalSchlaefliNearZeroTarget
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K

/-- Canonical periodic near-flat expansion/reindexing target for
`∑_e h_e δ'_e` along conformal lines. -/
def CanonicalPeriodicConformalSchlaefliNearZeroExpansionTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  ConformalSchlaefliNearZeroExpansionTarget
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK

/-- Canonical periodic non-flat local angle chain rule, in squared-edge
coordinates and localized near the flat point. -/
def CanonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  LocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTarget
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K

/-- Canonical periodic closed-form local Schläfli zero at the deformed
squared-edge tuple, localized near the flat point. -/
def CanonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  LocalConformalSchlaefliClosedFormZeroNearZeroTarget
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K

/-- The near-flat expansion plus local Schläfli target directly closes the
canonical stationarity target. -/
theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTarget_of_nearZeroSchlaefli
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hExpand :
      CanonicalPeriodicConformalSchlaefliNearZeroExpansionTarget Nx Ny Nz hx hy hz)
    (hLocal :
      CanonicalPeriodicLocalConformalSchlaefliNearZeroTarget Nx Ny Nz hx hy hz) :
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget Nx Ny Nz hx hy hz := by
  dsimp [CanonicalPeriodicConformalSchlaefliNearZeroExpansionTarget,
    CanonicalPeriodicLocalConformalSchlaefliNearZeroTarget,
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget] at hExpand hLocal ⊢
  exact
    weightedDeficitDerivativeStationary_of_nearZeroExpansion_and_local
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
      (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz)
      hExpand hLocal

/-- The canonical along-line Schläfli target follows from the two localized
non-flat targets: local tetrahedral Schläfli at every line parameter plus the
global expansion/reindexing of `∑ h δ'` into those local sums. -/
theorem canonicalPeriodicConformalSchlaefliAlongLineTarget_of_expansion_and_local
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hExpand :
      CanonicalPeriodicConformalSchlaefliAlongLineExpansionTarget Nx Ny Nz hx hy hz)
    (hLocal :
      CanonicalPeriodicLocalConformalSchlaefliAlongLineTarget Nx Ny Nz hx hy hz) :
    CanonicalPeriodicConformalSchlaefliAlongLineTarget Nx Ny Nz hx hy hz := by
  dsimp [CanonicalPeriodicConformalSchlaefliAlongLineTarget,
    CanonicalPeriodicConformalSchlaefliAlongLineExpansionTarget,
    CanonicalPeriodicLocalConformalSchlaefliAlongLineTarget] at hExpand hLocal ⊢
  exact
    conformalSchlaefliAlongLine_of_expansion_and_local
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
      hExpand hLocal

theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTarget_of_conformalSchlaefli
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hSchlaefli :
      CanonicalPeriodicConformalSchlaefliAlongLineTarget Nx Ny Nz hx hy hz) :
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget Nx Ny Nz hx hy hz := by
  dsimp [CanonicalPeriodicConformalSchlaefliAlongLineTarget,
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget] at hSchlaefli ⊢
  exact
    weightedDeficitDerivativeStationary_of_conformalSchlaefliAlongLine
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
      (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz) hSchlaefli

/-- At `N=5`: the conformal Schläfli identity along the line closes the full
stationarity target, bypassing all per-displacement-class machinery. -/
abbrev CanonicalPeriodicConformalSchlaefliAlongLineTargetAtN5 : Prop :=
  CanonicalPeriodicConformalSchlaefliAlongLineTarget
    5 5 5 (by decide) (by decide) (by decide)

abbrev CanonicalPeriodicLocalConformalSchlaefliNearZeroTargetAtN5 : Prop :=
  CanonicalPeriodicLocalConformalSchlaefliNearZeroTarget
    5 5 5 (by decide) (by decide) (by decide)

abbrev CanonicalPeriodicConformalSchlaefliNearZeroExpansionTargetAtN5 : Prop :=
  CanonicalPeriodicConformalSchlaefliNearZeroExpansionTarget
    5 5 5 (by decide) (by decide) (by decide)

abbrev CanonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTargetAtN5 : Prop :=
  CanonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTarget
    5 5 5 (by decide) (by decide) (by decide)

abbrev CanonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTargetAtN5 : Prop :=
  CanonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTarget
    5 5 5 (by decide) (by decide) (by decide)

theorem canonicalPeriodicLocalConformalSchlaefliNearZeroTarget_of_sqEdgeChainRule_and_closedFormZero
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hChain :
      CanonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTarget
        Nx Ny Nz hx hy hz)
    (hZero :
      CanonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicLocalConformalSchlaefliNearZeroTarget Nx Ny Nz hx hy hz := by
  dsimp [CanonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTarget,
    CanonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTarget,
    CanonicalPeriodicLocalConformalSchlaefliNearZeroTarget] at hChain hZero ⊢
  exact
    localConformalSchlaefliNearZero_of_sqEdgeChainRule_and_closedFormZero
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      hChain hZero

theorem canonicalPeriodicLocalConformalSchlaefliNearZeroTargetAtN5_of_sqEdgeChainRule_and_closedFormZero
    (hChain :
      CanonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTargetAtN5)
    (hZero :
      CanonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTargetAtN5) :
    CanonicalPeriodicLocalConformalSchlaefliNearZeroTargetAtN5 :=
  canonicalPeriodicLocalConformalSchlaefliNearZeroTarget_of_sqEdgeChainRule_and_closedFormZero
    5 5 5 (by decide) (by decide) (by decide) hChain hZero

/-- The near-flat global Schläfli expansion/reindexing target is closed for the
canonical periodic Freudenthal torus.  The proof differentiates the finite
deficit-angle sum near zero and uses the encoded edge-slot partition to reindex
global edge incidences into local tetrahedral edge slots. -/
theorem canonicalPeriodicConformalSchlaefliNearZeroExpansionTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicConformalSchlaefliNearZeroExpansionTarget Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  dsimp [CanonicalPeriodicConformalSchlaefliNearZeroExpansionTarget]
  exact
    conformalSchlaefliNearZeroExpansion_of_angleDiff_and_partition
      P.K P.hK
      (edgeSlotPartition_of_encodedPeriodicFreudenthalTorus P)
      (localDihedralAngleLineDifferentiabilityNearZero_of_flatConfiguration
        P.K P.hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))

theorem canonicalPeriodicConformalSchlaefliNearZeroExpansionTargetAtN5 :
    CanonicalPeriodicConformalSchlaefliNearZeroExpansionTargetAtN5 :=
  canonicalPeriodicConformalSchlaefliNearZeroExpansionTarget
    5 5 5 (by decide) (by decide) (by decide)

/-- The non-flat squared-edge chain rule half of the local conformal Schläfli
identity is closed for every canonical periodic Freudenthal torus, localized
near the flat point. -/
theorem canonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  dsimp [CanonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTarget]
  exact
    localConformalSchlaefliAngleSqEdgeChainRuleNearZero_of_flatConfiguration
      P.K P.hK
      (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz)

theorem canonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTargetAtN5 :
    CanonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTargetAtN5 :=
  canonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTarget
    5 5 5 (by decide) (by decide) (by decide)

/-- The closed-form algebraic Schläfli-zero half of the local conformal
identity is closed for every canonical periodic Freudenthal torus. -/
theorem canonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTarget
      Nx Ny Nz hx hy hz := by
  dsimp [CanonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTarget]
  exact
    localConformalSchlaefliClosedFormZeroNearZero
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K

theorem canonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTargetAtN5 :
    CanonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTargetAtN5 :=
  canonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTarget
    5 5 5 (by decide) (by decide) (by decide)

theorem canonicalPeriodicLocalConformalSchlaefliNearZeroTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicLocalConformalSchlaefliNearZeroTarget Nx Ny Nz hx hy hz :=
  canonicalPeriodicLocalConformalSchlaefliNearZeroTarget_of_sqEdgeChainRule_and_closedFormZero
    Nx Ny Nz hx hy hz
    (canonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTarget
      Nx Ny Nz hx hy hz)
    (canonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTarget
      Nx Ny Nz hx hy hz)

theorem canonicalPeriodicLocalConformalSchlaefliNearZeroTargetAtN5 :
    CanonicalPeriodicLocalConformalSchlaefliNearZeroTargetAtN5 :=
  canonicalPeriodicLocalConformalSchlaefliNearZeroTarget
    5 5 5 (by decide) (by decide) (by decide)

theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_of_nearZeroSchlaefli
    (hExpand : CanonicalPeriodicConformalSchlaefliNearZeroExpansionTargetAtN5)
    (hLocal : CanonicalPeriodicLocalConformalSchlaefliNearZeroTargetAtN5) :
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget
      5 5 5 (by decide) (by decide) (by decide) :=
  canonicalPeriodicWeightedDeficitDerivativeStationaryTarget_of_nearZeroSchlaefli
    5 5 5 (by decide) (by decide) (by decide) hExpand hLocal

theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_of_sqEdgeChainRule_and_closedFormZero
    (hChain :
      CanonicalPeriodicLocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTargetAtN5)
    (hZero :
      CanonicalPeriodicLocalConformalSchlaefliClosedFormZeroNearZeroTargetAtN5) :
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget
      5 5 5 (by decide) (by decide) (by decide) :=
  canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_of_nearZeroSchlaefli
    canonicalPeriodicConformalSchlaefliNearZeroExpansionTargetAtN5
    (canonicalPeriodicLocalConformalSchlaefliNearZeroTargetAtN5_of_sqEdgeChainRule_and_closedFormZero
      hChain hZero)

theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_from_nearZeroSchlaefli :
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget
      5 5 5 (by decide) (by decide) (by decide) :=
  canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_of_nearZeroSchlaefli
    canonicalPeriodicConformalSchlaefliNearZeroExpansionTargetAtN5
    canonicalPeriodicLocalConformalSchlaefliNearZeroTargetAtN5

abbrev CanonicalPeriodicLocalConformalSchlaefliAlongLineTargetAtN5 : Prop :=
  CanonicalPeriodicLocalConformalSchlaefliAlongLineTarget
    5 5 5 (by decide) (by decide) (by decide)

abbrev CanonicalPeriodicConformalSchlaefliAlongLineExpansionTargetAtN5 : Prop :=
  CanonicalPeriodicConformalSchlaefliAlongLineExpansionTarget
    5 5 5 (by decide) (by decide) (by decide)

theorem CanonicalPeriodicConformalSchlaefliAlongLineTargetAtN5_of_expansion_and_local
    (hExpand : CanonicalPeriodicConformalSchlaefliAlongLineExpansionTargetAtN5)
    (hLocal : CanonicalPeriodicLocalConformalSchlaefliAlongLineTargetAtN5) :
    CanonicalPeriodicConformalSchlaefliAlongLineTargetAtN5 :=
  canonicalPeriodicConformalSchlaefliAlongLineTarget_of_expansion_and_local
    5 5 5 (by decide) (by decide) (by decide) hExpand hLocal

theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_of_conformalSchlaefli
    (h : CanonicalPeriodicConformalSchlaefliAlongLineTargetAtN5) :
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget
      5 5 5 (by decide) (by decide) (by decide) :=
  canonicalPeriodicWeightedDeficitDerivativeStationaryTarget_of_conformalSchlaefli
    5 5 5 (by decide) (by decide) (by decide) h

/-- The two remaining load-bearing Track 1.B inputs at `(Nx,Ny,Nz)` before
`CanonicalPeriodicEdgeStencilLocalCorrespondence`. -/
def CanonicalPeriodicTrack1BClosureTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  CanonicalPeriodicSecondSchlaefliAlongLineTarget Nx Ny Nz hx hy hz ∧
    CanonicalPeriodicMixedHingeDeficitLengthChainTarget Nx Ny Nz hx hy hz

structure CanonicalPeriodicTrack1BOpenInputs
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) where
  secondSchlaefli : CanonicalPeriodicSecondSchlaefliAlongLineTarget Nx Ny Nz hx hy hz
  lengthChain : CanonicalPeriodicMixedHingeDeficitLengthChainTarget Nx Ny Nz hx hy hz

/-- Track 1.B open inputs with the Schläfli side in the typed periodic-edge
form used by lane `1B-SCH`. -/
structure CanonicalPeriodicTrack1BTypedEdgeOpenInputs
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) where
  typedSecondSchlaefli : CanonicalPeriodicSecondSchlaefliTypedEdgeTarget Nx Ny Nz hx hy hz
  lengthChain : CanonicalPeriodicMixedHingeDeficitLengthChainTarget Nx Ny Nz hx hy hz

def CanonicalPeriodicTrack1BOpenInputs.ofTypedEdge
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {hx : 2 < Nx} {hy : 2 < Ny} {hz : 2 < Nz}
    (h : CanonicalPeriodicTrack1BTypedEdgeOpenInputs Nx Ny Nz hx hy hz) :
    CanonicalPeriodicTrack1BOpenInputs Nx Ny Nz hx hy hz where
  secondSchlaefli :=
    (canonicalPeriodicSecondSchlaefliAlongLineTarget_iff_typedEdge Nx Ny Nz hx hy hz).2
      h.typedSecondSchlaefli
  lengthChain := h.lengthChain

structure CanonicalPeriodicTrack1BEventuallyZeroInputs
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) where
  eventuallyZero : CanonicalPeriodicWeightedDeficitDerivativeEventuallyZeroTarget Nx Ny Nz hx hy hz
  lengthChain : CanonicalPeriodicMixedHingeDeficitLengthChainTarget Nx Ny Nz hx hy hz

theorem canonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget_of_closedForm
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hClosedForm :
      CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  have hsum :
      (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairClosedFormExpandedSummand hx hy hz ξ edge pair) =
        ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz ξ edge pair := by
    refine Finset.sum_congr rfl ?_
    intro pair _
    exact freudenthalExplicitFiberPairClosedFormExpandedSummand_eq_flat hx hy hz ξ edge pair
  simpa [CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget,
    CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget, hsum, P] using
    hClosedForm ξ edge

theorem FreudenthalAxisDisp0ExplicitFiberClosedFormTarget_false :
    ¬ CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget
      AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
      AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
      AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz :=
  fun h =>
    AxisDisp0EndpointUnitWitness5.FreudenthalAxisDisp0ExplicitFiberFlatUnfoldedTarget_false
      (canonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget_of_closedForm
        AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
        AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
        AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz h)

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_not_of_explicitFiberClosedFormTarget_at_N5
    (hClosed :
      CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget
        AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
        AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
        AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz) :
    False :=
  FreudenthalAxisDisp0ExplicitFiberClosedFormTarget_false hClosed

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_not_of_explicitFiberFlatUnfoldedTarget_at_N5
    (hFlat :
      CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget
        AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
        AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
        AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz) :
    False :=
  AxisDisp0EndpointUnitWitness5.FreudenthalAxisDisp0ExplicitFiberFlatUnfoldedTarget_false hFlat

theorem canonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget_of_flatUnfolded
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFlatUnfolded :
      CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  have hsum :
      (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairFlatExpandedSummand hx hy hz ξ edge pair) =
        ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairClosedFormExpandedSummand hx hy hz ξ edge pair := by
    refine Finset.sum_congr rfl ?_
    intro pair _
    exact (freudenthalExplicitFiberPairClosedFormExpandedSummand_eq_flat hx hy hz ξ edge pair).symm
  simpa [CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget,
    CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget, hsum, P] using
    hFlatUnfolded ξ edge

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainLocalPairTarget_of_fiber
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFiber :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainLocalPairFiberTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainLocalPairTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  have hsum :
      (∑ tet : Fin 6,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
              let cell :=
                periodicMatchingBaseCell
                  (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))
                  edge.base
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k) =
        ∑ pair ∈ ((Finset.univ : Finset FreudenthalLocalPair).filter
          (fun pair => freudenthalLocalPairDisp pair = edge.disp)),
              let cell :=
                periodicMatchingBaseCell
                  (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2))
                  edge.base
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm (cell, pair.1))).dihedralDeriv pair.2 k *
                  localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, pair.1)) k := by
    unfold FreudenthalLocalPair freudenthalLocalPairDisp
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_filter]
    rw [Finset.sum_product]
    simp [Finset.sum_filter, eq_comm]
  rw [hsum]
  exact hFiber ξ edge

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispCellTetTarget_of_localPair
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocalPair :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainLocalPairTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispCellTetTarget
      Nx Ny Nz hx hy hz := by
  classical
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  have hcollapse :
      (∑ cell : Vertex Nx Ny Nz,
          ∑ tet : Fin 6,
            ∑ f ∈ (Finset.univ.filter
              (fun f : Fin 6 => edge.disp = cubeEdgeDisp
                (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
              if edge.base = addVertexBits cell
                  (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f)) then
                ∑ k : Fin 6,
                  ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                    (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
                    localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k
              else 0) =
        ∑ tet : Fin 6,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
              let cell :=
                periodicMatchingBaseCell
                  (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))
                  edge.base
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro tet _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro f _hf
    exact sum_ite_eq_of_addVertexBits_apply
      (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))
      edge.base
      (fun cell : Vertex Nx Ny Nz =>
        ∑ k : Fin 6,
          ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
            (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
            localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k)
  rw [hcollapse]
  exact hLocalPair ξ edge

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispTypedTetTarget_of_cellTet
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hCellTet :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispCellTetTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispTypedTetTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  have hsplit :
      (∑ cellTet : PeriodicTet Nx Ny Nz,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))),
            if edge.base = addVertexBits cellTet.1
                (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f)) then
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm cellTet)).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm cellTet) k
            else 0) =
        ∑ cell : Vertex Nx Ny Nz,
          ∑ tet : Fin 6,
            ∑ f ∈ (Finset.univ.filter
              (fun f : Fin 6 => edge.disp = cubeEdgeDisp
                (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
              if edge.base = addVertexBits cell
                  (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f)) then
                ∑ k : Fin 6,
                  ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                    (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
                    localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k
              else 0 := by
    unfold PeriodicTet
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [hsplit]
  exact hCellTet ξ edge

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispFilteredTarget_of_typedTet
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hTyped :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispTypedTetTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispFilteredTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  let e := P.edgeEquiv.symm edge
  have hsum :
      (∑ cellTet : PeriodicTet Nx Ny Nz,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f))),
            if edge.base = addVertexBits cellTet.1
                (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf cellTet.2 f)) then
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm cellTet)).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm cellTet) k
            else 0) =
        (∑ τ : Fin P.K.nT,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f))),
            if edge.base = addVertexBits (P.tetEquiv τ).1
                (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f)) then
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k
            else 0) := by
    simpa using
      (Equiv.sum_comp P.tetEquiv.symm
        (fun τ : Fin P.K.nT =>
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f))),
            if edge.base = addVertexBits (P.tetEquiv τ).1
                (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f)) then
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k
            else 0))
  rw [← hsum]
  exact hTyped ξ edge

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainDispFilteredTarget_of_baseDisp
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hBase :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispFilteredTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainDispFilteredTarget
      Nx Ny Nz hx hy hz := by
  classical
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  let e := P.edgeEquiv.symm edge
  have hbase :
      ∀ τ : Fin P.K.nT,
        (∑ f ∈ (Finset.univ.filter
          (fun f : Fin 6 => edge.disp = cubeEdgeDisp
            (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f))),
          if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k
          else 0) =
        ∑ f ∈ (Finset.univ.filter
          (fun f : Fin 6 => edge.disp = cubeEdgeDisp
            (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f))),
          if edge.base = addVertexBits (P.tetEquiv τ).1
              (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f)) then
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k
          else 0 := by
    intro τ
    refine Finset.sum_congr rfl ?_
    intro f hf
    have hDisp :
        edge.disp = cubeEdgeDisp
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f) :=
      (Finset.mem_filter.mp hf).2
    have hiff : (edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f) ↔
        edge.base = addVertexBits (P.tetEquiv τ).1
          (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f)) := by
      constructor
      · intro hEdge
        exact canonicalPeriodicTypedEdge_base_eq_of_localEdgeOf hEdge
      · intro hBaseEq
        exact (canonicalPeriodicTypedEdge_eq_localEdgeOf_iff_base_and_disp edge
          (P.tetEquiv τ) f).2 ⟨hBaseEq, hDisp⟩
    by_cases hBaseEq :
        edge.base = addVertexBits (P.tetEquiv τ).1
          (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f))
    · have hEq : edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f := hiff.2 hBaseEq
      have hLocalBase :
          (localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f).base =
            addVertexBits (P.tetEquiv τ).1
              (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f)) := by
        simp [localEdgeOf]
      simp [hEq, hLocalBase]
    · have hEq : edge ≠ localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f := by
        intro hEdge
        exact hBaseEq (hiff.1 hEdge)
      simp [hEq, hBaseEq]
  simpa [CanonicalPeriodicMixedHingeDeficitExpandedLengthChainDispFilteredTarget,
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispFilteredTarget,
    hbase, P, e] using hBase ξ edge

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedSlotTarget_of_dispFiltered
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hDisp :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainDispFilteredTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedSlotTarget
      Nx Ny Nz hx hy hz := by
  classical
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  let e := P.edgeEquiv.symm edge
  have hfilter :
      ∀ τ : Fin P.K.nT,
        (∑ f : Fin 6,
          if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k
          else 0) =
        ∑ f ∈ (Finset.univ.filter
          (fun f : Fin 6 => edge.disp = cubeEdgeDisp
            (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f))),
          if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k
          else 0 := by
    intro τ
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro f _hf
    by_cases hMatch :
        edge.disp = cubeEdgeDisp
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv τ).2 f)
    · simp [hMatch]
    · have hne : edge ≠ localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f := by
        intro hEdge
        exact hMatch (canonicalPeriodicTypedEdge_disp_eq_of_localEdgeOf hEdge)
      simp [hMatch, hne]
  simpa [CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedSlotTarget,
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainDispFilteredTarget,
    hfilter, P, e] using hDisp ξ edge

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget_of_typedSlot
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hSlot :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedSlotTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget
      Nx Ny Nz hx hy hz := by
  classical
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  let e : Fin P.K.nE := P.edgeEquiv.symm edge
  have heq : P.edgeEquiv e = edge := by
    simp [e]
  have hslot_sum :
      ∀ τ : Fin P.K.nT,
        (match P.K.edgeInTet e τ with
          | none => 0
          | some f =>
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k) =
        ∑ f : Fin 6,
          if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k
          else 0 := by
    intro τ
    cases hInc : P.K.edgeInTet e τ with
    | none =>
        change (0 : ℝ) =
          ∑ f : Fin 6,
            if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k
            else 0
        symm
        apply Finset.sum_eq_zero
        intro f _hf
        have hne : edge ≠ localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f := by
          intro hEdge
          have hSome : P.K.edgeInTet e τ = some f := by
            exact (P.edgeInTet_iff e τ f).2 (by simpa [heq] using hEdge)
          rw [hInc] at hSome
          contradiction
        simp [hne]
    | some f0 =>
        rw [Finset.sum_eq_single f0]
        · have hEdge : edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f0 := by
            have h := (P.edgeInTet_iff e τ f0).1 hInc
            simpa [heq] using h
          simp [hEdge]
        · intro f _hf hf_ne
          have hne : edge ≠ localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f := by
            intro hEdge
            have hSome : P.K.edgeInTet e τ = some f := by
              exact (P.edgeInTet_iff e τ f).2 (by simpa [heq] using hEdge)
            rw [hInc] at hSome
            exact hf_ne (Option.some.inj hSome.symm)
          simp [hne]
        · intro hnot
          exact (hnot (Finset.mem_univ f0)).elim
  simpa [CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget,
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedSlotTarget,
    hslot_sum, P, e] using hSlot ξ edge

theorem canonicalPeriodicTypedEdge_perTet_edgeInTetExpanded_eq_slotGuarded
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz)
    (τ : Fin (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K.nT) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    let e := P.edgeEquiv.symm edge
    (match P.K.edgeInTet e τ with
      | none => 0
      | some f =>
          ∑ k : Fin 6,
            ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
              localEdgeLengthDirectionalDeriv P.K ξ τ k) =
      ∑ f : Fin 6,
        if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
          ∑ k : Fin 6,
            ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
              localEdgeLengthDirectionalDeriv P.K ξ τ k
        else 0 := by
  classical
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  let e := P.edgeEquiv.symm edge
  have heq : P.edgeEquiv e = edge := by simp [e]
  show
      (match P.K.edgeInTet e τ with
        | none => 0
        | some f =>
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k) =
        ∑ f : Fin 6,
          if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k
          else 0
  cases hInc : P.K.edgeInTet e τ with
  | none =>
      change (0 : ℝ) =
        ∑ f : Fin 6,
          if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k
          else 0
      symm
      apply Finset.sum_eq_zero
      intro f _hf
      have hne : edge ≠ localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f := by
        intro hEdge
        have hSome : P.K.edgeInTet e τ = some f := by
          exact (P.edgeInTet_iff e τ f).2 (by simpa [heq] using hEdge)
        rw [hInc] at hSome
        contradiction
      simp [hne]
  | some f0 =>
      rw [Finset.sum_eq_single f0]
      · have hEdge : edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f0 := by
          have h := (P.edgeInTet_iff e τ f0).1 hInc
          simpa [heq] using h
        simp [hEdge]
      · intro f _hf hf_ne
        have hne : edge ≠ localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f := by
          intro hEdge
          have hSome : P.K.edgeInTet e τ = some f := by
            exact (P.edgeInTet_iff e τ f).2 (by simpa [heq] using hEdge)
          rw [hInc] at hSome
          exact hf_ne (Option.some.inj hSome.symm)
        simp [hne]
      · intro hnot
        exact (hnot (Finset.mem_univ f0)).elim

theorem canonicalPeriodicTypedEdge_edgeInTetExpandedInnerSum_eq_slotGuardedInnerSum
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    let e := P.edgeEquiv.symm edge
    (∑ τ : Fin P.K.nT,
        match P.K.edgeInTet e τ with
        | none => 0
        | some f =>
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k) =
      ∑ τ : Fin P.K.nT,
        ∑ f : Fin 6,
          if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k
          else 0 := by
  classical
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  let e := P.edgeEquiv.symm edge
  refine Finset.sum_congr rfl ?_
  intro τ _
  exact canonicalPeriodicTypedEdge_perTet_edgeInTetExpanded_eq_slotGuarded hx hy hz ξ edge τ

theorem freudenthalExplicitFiberDispTableExpandedSum_eq_localPairExpandedInnerSum
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair) =
      ∑ tet : Fin 6,
        ∑ f ∈ (Finset.univ.filter
          (fun f : Fin 6 => edge.disp = cubeEdgeDisp
            (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
          let cell :=
            periodicMatchingBaseCell
              (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))
              edge.base
          ∑ k : Fin 6,
            ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
              localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  have hsum :
      (∑ tet : Fin 6,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
              let cell :=
                periodicMatchingBaseCell
                  (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))
                  edge.base
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k) =
        ∑ pair ∈ ((Finset.univ : Finset FreudenthalLocalPair).filter
          (fun pair => freudenthalLocalPairDisp pair = edge.disp)),
              let cell :=
                periodicMatchingBaseCell
                  (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2))
                  edge.base
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm (cell, pair.1))).dihedralDeriv pair.2 k *
                  localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, pair.1)) k := by
    unfold FreudenthalLocalPair freudenthalLocalPairDisp
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_filter]
    rw [Finset.sum_product]
    simp [Finset.sum_filter, eq_comm]
  calc
    (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair) =
        ∑ pair ∈ ((Finset.univ : Finset FreudenthalLocalPair).filter
          (fun pair => freudenthalLocalPairDisp pair = edge.disp)),
          let cell :=
            periodicMatchingBaseCell
              (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2))
              edge.base
          ∑ k : Fin 6,
            ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                (P.tetEquiv.symm (cell, pair.1))).dihedralDeriv pair.2 k *
              localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, pair.1)) k :=
      by
        rw [freudenthalLocalPairDispFiber_eq_filter edge.disp]
        refine Finset.sum_congr rfl ?_
        intro pair _
        dsimp [freudenthalExplicitFiberPairExpandedSummand, freudenthalExplicitFiberPairSelectedCell]
    _ =
        ∑ tet : Fin 6,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
            let cell :=
              periodicMatchingBaseCell
                (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))
                edge.base
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k :=
      hsum.symm

theorem canonicalPeriodicTypedEdge_localPairExpandedInnerSum_eq_slotGuardedInnerSum
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    (∑ tet : Fin 6,
        ∑ f ∈ (Finset.univ.filter
          (fun f : Fin 6 => edge.disp = cubeEdgeDisp
            (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
          let cell :=
            periodicMatchingBaseCell
              (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))
              edge.base
          ∑ k : Fin 6,
            ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
              localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k) =
      ∑ τ : Fin P.K.nT,
        ∑ f : Fin 6,
          if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k
          else 0 := by
  classical
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  let pairInnerSum (pair : Fin 6 × Fin 6) : ℝ :=
    let cell := freudenthalExplicitFiberPairSelectedCell edge pair
    ∑ k : Fin 6,
      ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
          (P.tetEquiv.symm (cell, pair.1))).dihedralDeriv pair.2 k *
        localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, pair.1)) k
  let slotInnerSum (p : Fin P.K.nT × Fin 6) : ℝ :=
    ∑ k : Fin 6,
      ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData p.1).dihedralDeriv p.2 k *
        localEdgeLengthDirectionalDeriv P.K ξ p.1 k
  let sPair :=
    (Finset.univ : Finset (Fin 6 × Fin 6)).filter
      (fun pair => edge.disp = cubeEdgeDisp
        (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2))
  let sSlot :=
    (Finset.univ : Finset (Fin P.K.nT × Fin 6)).filter
      (fun p => edge = localEdgeOf (P.tetEquiv p.1).1 (P.tetEquiv p.1).2 p.2)
  have hsum_pair :
      (∑ tet : Fin 6,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
            let cell :=
              periodicMatchingBaseCell
                (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))
                edge.base
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k) =
        ∑ pair ∈ ((Finset.univ : Finset FreudenthalLocalPair).filter
          (fun pair => freudenthalLocalPairDisp pair = edge.disp)),
          pairInnerSum pair := by
    unfold FreudenthalLocalPair freudenthalLocalPairDisp
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_filter]
    rw [Finset.sum_product]
    simp [Finset.sum_filter, eq_comm, pairInnerSum, freudenthalExplicitFiberPairSelectedCell]
  have hsPair_eq :
      sPair =
        (Finset.univ.filter
          (fun pair : Fin 6 × Fin 6 => freudenthalLocalPairDisp pair = edge.disp)) := by
    ext pair
    simp [sPair, freudenthalLocalPairDisp, eq_comm]
  have hlocal :
      (∑ tet : Fin 6,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
            let cell :=
              periodicMatchingBaseCell
                (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))
                edge.base
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k) =
        sPair.sum pairInnerSum := by
    rw [hsPair_eq, hsum_pair]
  have hsum_slot :
      (∑ τ : Fin P.K.nT,
          ∑ f : Fin 6,
            if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k
            else 0) =
        ∑ p ∈ sSlot, slotInnerSum p := by
    symm
    dsimp [sSlot]
    rw [Finset.sum_filter]
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_product]
  have hslot :
      (∑ τ : Fin P.K.nT,
          ∑ f : Fin 6,
            if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k
            else 0) =
        sSlot.sum slotInnerSum := hsum_slot
  have hbij : sPair.sum pairInnerSum = sSlot.sum slotInnerSum := by
    apply Finset.sum_bij'
      (fun pair _ =>
        (P.tetEquiv.symm
          (freudenthalExplicitFiberPairSelectedCell edge pair, pair.1), pair.2))
      (fun p _ => ((P.tetEquiv p.1).2, p.2))
    · intro pair hp
      simp only [sSlot, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [sPair, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hEdge :=
        canonicalPeriodicTypedEdge_eq_localEdgeOf_of_base_and_disp edge
          (freudenthalExplicitFiberPairSelectedCell edge pair) pair.1 pair.2
          (freudenthalExplicitFiberPairSelectedCell_base_eq edge pair) hp
      rw [P.tetEquiv.apply_symm_apply (freudenthalExplicitFiberPairSelectedCell edge pair, pair.1)]
      exact hEdge
    · intro p hp
      simp only [sSlot, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [sPair, Finset.mem_filter, Finset.mem_univ, true_and]
      exact
        canonicalPeriodicTypedEdge_disp_eq_of_localEdgeOf (Nx := Nx) (Ny := Ny) (Nz := Nz)
          (edge := edge) (cellTet := P.tetEquiv p.1) (f := p.2) hp
    · intro pair _hp
      apply Prod.ext
      · exact congrArg Prod.snd
          (P.tetEquiv.apply_symm_apply (freudenthalExplicitFiberPairSelectedCell edge pair, pair.1))
      · rfl
    · intro p hp
      apply Prod.ext
      · simp only [sSlot, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        have hbase := canonicalPeriodicTypedEdge_base_eq_of_localEdgeOf hp
        have hcell :
            (P.tetEquiv p.1).1 =
              freudenthalExplicitFiberPairSelectedCell edge ((P.tetEquiv p.1).2, p.2) :=
          periodicMatchingBaseCell_eq_of_addVertexBits
            (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf (P.tetEquiv p.1).2 p.2))
            edge.base (P.tetEquiv p.1).1 hbase
        have harg :
            (freudenthalExplicitFiberPairSelectedCell edge ((P.tetEquiv p.1).2, p.2),
                (P.tetEquiv p.1).2) =
              P.tetEquiv p.1 := by
          apply Prod.ext
          · exact hcell.symm
          · rfl
        rw [harg]
        exact P.tetEquiv.symm_apply_apply p.1
      · rfl
    · intro pair _hp
      simp [freudenthalExplicitFiberPairSelectedCell]
  calc
    (∑ tet : Fin 6,
        ∑ f ∈ (Finset.univ.filter
          (fun f : Fin 6 => edge.disp = cubeEdgeDisp
            (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
          let cell :=
            periodicMatchingBaseCell
              (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))
              edge.base
          ∑ k : Fin 6,
            ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
              localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k) =
        sPair.sum pairInnerSum := hlocal
    _ = sSlot.sum slotInnerSum := hbij
    _ =
        ∑ τ : Fin P.K.nT,
          ∑ f : Fin 6,
            if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k
            else 0 := hslot.symm

theorem freudenthalExplicitFiberDispTableExpandedSum_eq_typedEdgeInTetExpandedIncidentSum
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (edge : Geometry.PeriodicFreudenthalTorus.PeriodicEdge Nx Ny Nz) :
    let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
    let e := P.edgeEquiv.symm edge
    (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair) =
      ∑ τ : Fin P.K.nT,
        match P.K.edgeInTet e τ with
        | none => 0
        | some f =>
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  let e := P.edgeEquiv.symm edge
  calc
    (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair) =
        ∑ tet : Fin 6,
          ∑ f ∈ (Finset.univ.filter
            (fun f : Fin 6 => edge.disp = cubeEdgeDisp
              (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))),
            let cell :=
              periodicMatchingBaseCell
                (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf tet f))
                edge.base
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm (cell, tet))).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, tet)) k :=
      freudenthalExplicitFiberDispTableExpandedSum_eq_localPairExpandedInnerSum hx hy hz ξ edge
    _ =
        ∑ τ : Fin P.K.nT,
          ∑ f : Fin 6,
            if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k
            else 0 :=
      canonicalPeriodicTypedEdge_localPairExpandedInnerSum_eq_slotGuardedInnerSum hx hy hz ξ edge
    _ =
        ∑ τ : Fin P.K.nT,
          match P.K.edgeInTet e τ with
          | none => 0
          | some f =>
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k := by
      refine Finset.sum_congr rfl ?_
      intro τ _
      show
          (∑ f : Fin 6,
              if edge = localEdgeOf (P.tetEquiv τ).1 (P.tetEquiv τ).2 f then
                ∑ k : Fin 6,
                  ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                    localEdgeLengthDirectionalDeriv P.K ξ τ k
              else 0) =
            match P.K.edgeInTet e τ with
            | none => 0
            | some f =>
                ∑ k : Fin 6,
                  ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                    localEdgeLengthDirectionalDeriv P.K ξ τ k
      exact (canonicalPeriodicTypedEdge_perTet_edgeInTetExpanded_eq_slotGuarded hx hy hz ξ edge τ).symm

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget_of_explicitFiber
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hExplicit :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  let e := P.edgeEquiv.symm edge
  have hinner :
      (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          let cell :=
            periodicMatchingBaseCell
              (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2))
              edge.base
          ∑ k : Fin 6,
            ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                (P.tetEquiv.symm (cell, pair.1))).dihedralDeriv pair.2 k *
              localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, pair.1)) k) =
        ∑ τ : Fin P.K.nT,
          match P.K.edgeInTet e τ with
          | none => 0
          | some f =>
              ∑ k : Fin 6,
                ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                  localEdgeLengthDirectionalDeriv P.K ξ τ k := by
    have htable :
        (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
            freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair) =
          ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
            let cell :=
              periodicMatchingBaseCell
                (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2))
                edge.base
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                  (P.tetEquiv.symm (cell, pair.1))).dihedralDeriv pair.2 k *
                localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, pair.1)) k := by
      refine Finset.sum_congr rfl ?_
      intro pair _
      dsimp [freudenthalExplicitFiberPairExpandedSummand, freudenthalExplicitFiberPairSelectedCell]
    rw [← htable]
    exact freudenthalExplicitFiberDispTableExpandedSum_eq_typedEdgeInTetExpandedIncidentSum hx hy hz ξ edge
  simpa [CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget,
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget, hinner, P, e] using
    hExplicit ξ edge

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget_of_typedEndpoint
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hTyped :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  let e := P.edgeEquiv.symm edge
  have hinner :=
    freudenthalExplicitFiberDispTableExpandedSum_eq_typedEdgeInTetExpandedIncidentSum hx hy hz ξ edge
  have htable :
      (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair) =
        ∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
          let cell :=
            periodicMatchingBaseCell
              (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf pair.1 pair.2))
              edge.base
          ∑ k : Fin 6,
            ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData
                (P.tetEquiv.symm (cell, pair.1))).dihedralDeriv pair.2 k *
              localEdgeLengthDirectionalDeriv P.K ξ (P.tetEquiv.symm (cell, pair.1)) k := by
    refine Finset.sum_congr rfl ?_
    intro pair _
    dsimp [freudenthalExplicitFiberPairExpandedSummand, freudenthalExplicitFiberPairSelectedCell]
  have hfiberInner := htable.trans hinner
  have hnegInner := congr_arg Neg.neg hfiberInner
  have htyped' :
      hingeMeasureDirectionalDeriv P.K P.hK ξ e *
          (-∑ τ : Fin P.K.nT,
            match P.K.edgeInTet e τ with
            | none => 0
            | some f =>
                ∑ k : Fin 6,
                  ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                    localEdgeLengthDirectionalDeriv P.K ξ τ k) =
        Real.sqrt (periodicDispSqEdge edge.disp) *
          (ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.1) -
            ξ ((vertexFinEquiv Nx Ny Nz).symm edge.endpoints.2)) ^ (2 : ℕ) := by
    simpa [CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget, P, e] using
      hTyped ξ edge
  rw [← hnegInner] at htyped'
  simpa [CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget, P, e] using htyped'

theorem FreudenthalAxisDisp0ExpandedLengthChainTypedEndpointTarget_false :
    ¬ CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget
      AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
      AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
      AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz := by
  intro hTyped
  exact FreudenthalAxisDisp0ExplicitFiberExpandedLengthChainExplicitFiberTarget_false
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget_of_typedEndpoint
      AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
      AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
      AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz hTyped)

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_not_of_typedEndpoint_at_N5
    (hTyped :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget
        AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
        AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
        AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz) :
    False :=
  FreudenthalAxisDisp0ExpandedLengthChainTypedEndpointTarget_false hTyped

/-- Generic finite reindexing target for the Track 1.B flat Freudenthal lane:
the explicit displacement-fiber table sum is the encoded `edgeInTet` incident
sum for every typed periodic edge. -/
def CanonicalPeriodicTrack1BFiniteReindexingTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  ∀ (ξ : VertexPotential P.K) (edge : PeriodicEdge Nx Ny Nz),
    let e := P.edgeEquiv.symm edge
    (∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
        freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair) =
      ∑ τ : Fin P.K.nT,
        match P.K.edgeInTet e τ with
        | none => 0
        | some f =>
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k

theorem canonicalPeriodicTrack1BFiniteReindexingTarget_holds
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicTrack1BFiniteReindexingTarget Nx Ny Nz hx hy hz := by
  intro ξ edge
  exact freudenthalExplicitFiberDispTableExpandedSum_eq_typedEdgeInTetExpandedIncidentSum
    hx hy hz ξ edge

/-- The corrected mixed axis-stencil target follows from the global
explicit-fiber axis-stencil identity.  This is the safe replacement for the
false typed-endpoint route: it keeps the typed-edge sum global, then uses the
proved finite reindexing theorem to return to the canonical `edgeInTet` form. -/
theorem canonicalPeriodicMixedHingeDeficitAxisStencilTarget_of_explicitFiberAxis
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hExplicit :
      CanonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitAxisStencilTarget Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ
  let F : Fin P.K.nE → ℝ := fun e =>
    hingeMeasureDirectionalDeriv P.K P.hK ξ e *
      (-∑ τ : Fin P.K.nT,
        match P.K.edgeInTet e τ with
        | none => 0
        | some f =>
            ∑ k : Fin 6,
              ((triangulationSchlaefliData_of_incidence P.K P.hK).tetData τ).dihedralDeriv f k *
                localEdgeLengthDirectionalDeriv P.K ξ τ k)
  have hreindex :
      (∑ edge : PeriodicEdge Nx Ny Nz, F (P.edgeEquiv.symm edge)) =
        ∑ e : Fin P.K.nE, F e := by
    simpa [F] using (Equiv.sum_comp P.edgeEquiv.symm F)
  change (∑ e : Fin P.K.nE, F e) =
    canonicalPeriodicMixedAxisStencilAction Nx Ny Nz hx hy hz ξ
  rw [← hreindex]
  have hsum :
      (∑ edge : PeriodicEdge Nx Ny Nz, F (P.edgeEquiv.symm edge)) =
        ∑ edge : PeriodicEdge Nx Ny Nz,
          let e := P.edgeEquiv.symm edge
          hingeMeasureDirectionalDeriv P.K P.hK ξ e *
            (-∑ pair ∈ freudenthalLocalPairDispFiber edge.disp,
              freudenthalExplicitFiberPairExpandedSummand hx hy hz ξ edge pair) := by
    refine Finset.sum_congr rfl ?_
    intro edge _
    have hinner :=
      freudenthalExplicitFiberDispTableExpandedSum_eq_typedEdgeInTetExpandedIncidentSum
        hx hy hz ξ edge
    dsimp [F]
    rw [← hinner]
  rw [hsum]
  simpa [CanonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTarget, P] using hExplicit ξ

/-- N=5 finite-lane obstruction target: the typed-endpoint mixed target is
false on the certified axis disp-0 endpoint-unit witness. -/
def CanonicalPeriodicTrack1BFiniteN5TypedEndpointObstructionTarget : Prop :=
  ¬ CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget
      AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
      AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
      AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz

theorem canonicalPeriodicTrack1BFiniteN5TypedEndpointObstructionTarget_holds :
    CanonicalPeriodicTrack1BFiniteN5TypedEndpointObstructionTarget :=
  FreudenthalAxisDisp0ExpandedLengthChainTypedEndpointTarget_false

/-- Track 1.B finite-lane closure certificate.  This does not close Track 1.B:
it records that the flat finite Freudenthal reindexing and N=5 typed-endpoint
obstruction have closed, leaving stationarity to the `1B-SCH` lane. -/
structure CanonicalPeriodicTrack1BFiniteLaneCert : Prop where
  reindexing :
    CanonicalPeriodicTrack1BFiniteReindexingTarget
      AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
      AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
      AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz
  typedEndpointObstruction :
    CanonicalPeriodicTrack1BFiniteN5TypedEndpointObstructionTarget

theorem canonicalPeriodicTrack1BFiniteLaneCert :
    CanonicalPeriodicTrack1BFiniteLaneCert :=
  ⟨canonicalPeriodicTrack1BFiniteReindexingTarget_holds
      AxisDisp0EndpointUnitWitness5.WitnessNx AxisDisp0EndpointUnitWitness5.WitnessNy
      AxisDisp0EndpointUnitWitness5.WitnessNz AxisDisp0EndpointUnitWitness5.witnessHx
      AxisDisp0EndpointUnitWitness5.witnessHy AxisDisp0EndpointUnitWitness5.witnessHz,
    canonicalPeriodicTrack1BFiniteN5TypedEndpointObstructionTarget_holds⟩

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEdgeTarget_of_typedEndpoint
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hEndpoint :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEdgeTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ edge
  have hSq :
      (canonicalPeriodicIncidenceConsistent_of_endpoint Nx Ny Nz
          (canonicalPeriodicEndpointIncidence Nx Ny Nz)).globalSqEdge
        ((edgeFinEquiv Nx Ny Nz).symm edge) =
        periodicDispSqEdge edge.disp := by
    change
      periodicDispSqEdge
          ((edgeFinEquiv Nx Ny Nz) ((edgeFinEquiv Nx Ny Nz).symm edge)).disp =
        periodicDispSqEdge edge.disp
    rw [(edgeFinEquiv Nx Ny Nz).apply_symm_apply edge]
  simpa [CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEdgeTarget,
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget,
    canonicalEncodedPeriodicFreudenthalTorus,
      canonicalEncodedPeriodicFreudenthalTorus_of_endpoint,
      canonicalEncodedPeriodicFreudenthalTorus_of_incidence,
    canonicalPeriodicEdgeEquiv, canonicalPeriodicTriangulation, canonicalGlobalSqEdge,
    canonicalEdgeVerts, hSq, P] using hEndpoint ξ edge

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainPerEdgeTarget_of_typed
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hTyped :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEdgeTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainPerEdgeTarget
      Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ e
  simpa [P] using hTyped ξ (P.edgeEquiv e)

theorem canonicalPeriodicMixedHingeDeficitExpandedLengthChainTarget_of_perEdge
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hEdge :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainPerEdgeTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTarget Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ
  simpa [canonicalEdgeStencilDirichletEnergy, P] using
    Finset.sum_congr rfl (fun e _ => hEdge ξ e)

theorem canonicalPeriodicMixedHingeDeficitLengthChainTarget_of_expanded
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hExpanded :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTarget Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitLengthChainTarget Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ
  simpa [CanonicalPeriodicMixedHingeDeficitLengthChainTarget,
    CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTarget,
    localAngleLengthChainDeriv, P] using hExpanded ξ

theorem canonicalPeriodicMixedHingeDeficitLocalAngleTarget_of_lengthChainTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLength :
      CanonicalPeriodicMixedHingeDeficitLengthChainTarget Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitLocalAngleTarget Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ
  simpa [CanonicalPeriodicMixedHingeDeficitLocalAngleTarget,
    CanonicalPeriodicMixedHingeDeficitLengthChainTarget,
    deficitDirectionalDerivFromLocalAngles,
    canonicalPeriodicLocalDihedralDerivativePackage, P] using hLength ξ

theorem canonicalPeriodicMixedHingeDeficitLengthChainTarget_of_localAngleTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal :
      CanonicalPeriodicMixedHingeDeficitLocalAngleTarget Nx Ny Nz hx hy hz) :
    CanonicalPeriodicMixedHingeDeficitLengthChainTarget Nx Ny Nz hx hy hz := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ
  simpa [CanonicalPeriodicMixedHingeDeficitLengthChainTarget,
    CanonicalPeriodicMixedHingeDeficitLocalAngleTarget,
    deficitDirectionalDerivFromLocalAngles,
    canonicalPeriodicLocalDihedralDerivativePackage, P] using hLocal ξ

theorem canonicalPeriodicMixedHingeDeficitLengthChainTarget_iff_localAngleTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicMixedHingeDeficitLengthChainTarget Nx Ny Nz hx hy hz ↔
      CanonicalPeriodicMixedHingeDeficitLocalAngleTarget Nx Ny Nz hx hy hz :=
  ⟨canonicalPeriodicMixedHingeDeficitLocalAngleTarget_of_lengthChainTarget Nx Ny Nz hx hy hz,
    canonicalPeriodicMixedHingeDeficitLengthChainTarget_of_localAngleTarget Nx Ny Nz hx hy hz⟩

theorem canonicalPeriodicMixedHingeDeficitEdgeStencilTarget_of_localAngleTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal :
      CanonicalPeriodicMixedHingeDeficitLocalAngleTarget Nx Ny Nz hx hy hz) :
    MixedHingeDeficitEdgeStencilTarget
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
      (canonicalPeriodicDeficitDerivativePackage Nx Ny Nz hx hy hz) := by
  let P := canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz
  intro ξ
  simpa [P, canonicalPeriodicDeficitDerivativePackage_deficitDeriv]
    using hLocal ξ

/-- Canonical local-correspondence endpoint with the deficit package fixed to
the periodic Freudenthal one.  The only remaining inputs are now concrete
statements about that canonical deficit package: near-flat weighted
deficit-derivative vanishing and mixed hinge-deficit equality with the concrete
edge-stencil Dirichlet energy. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixed :
      MixedHingeDeficitEdgeStencilTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicDeficitDerivativePackage Nx Ny Nz hx hy hz)) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_eventuallyZero_and_edgeStencilTargets
    Nx Ny Nz hx hy hz
    (canonicalPeriodicDeficitDerivativePackage Nx Ny Nz hx hy hz)
    hZero hMixed

/-- Canonical local-correspondence endpoint with the mixed target expressed as a
finite local-angle identity. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitLocalAngleTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedLocal :
      CanonicalPeriodicMixedHingeDeficitLocalAngleTarget Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitTargets
    Nx Ny Nz hx hy hz hZero
    (canonicalPeriodicMixedHingeDeficitEdgeStencilTarget_of_localAngleTarget
      Nx Ny Nz hx hy hz hMixedLocal)

/-- Canonical local-correspondence endpoint with the mixed target expressed as
the explicit length-chain finite-sum identity. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitLengthChainTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedLength :
      CanonicalPeriodicMixedHingeDeficitLengthChainTarget Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitLocalAngleTargets
    Nx Ny Nz hx hy hz hZero
    (canonicalPeriodicMixedHingeDeficitLocalAngleTarget_of_lengthChainTarget
      Nx Ny Nz hx hy hz hMixedLength)

/-- Canonical local-correspondence endpoint with the mixed target expressed as
the fully expanded length-chain finite-sum identity. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitExpandedLengthChainTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedExpanded :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTarget Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitLengthChainTargets
    Nx Ny Nz hx hy hz hZero
    (canonicalPeriodicMixedHingeDeficitLengthChainTarget_of_expanded
      Nx Ny Nz hx hy hz hMixedExpanded)

/-- Canonical local-correspondence endpoint with the mixed target reduced to a
per-edge expanded finite identity. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitPerEdgeTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedPerEdge :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainPerEdgeTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitExpandedLengthChainTargets
    Nx Ny Nz hx hy hz hZero
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainTarget_of_perEdge
      Nx Ny Nz hx hy hz hMixedPerEdge)

/-- Canonical local-correspondence endpoint with the mixed target reduced to a
typed periodic-edge finite identity. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitTypedEdgeTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedTyped :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEdgeTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitPerEdgeTargets
    Nx Ny Nz hx hy hz hZero
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainPerEdgeTarget_of_typed
      Nx Ny Nz hx hy hz hMixedTyped)

/-- Canonical local-correspondence endpoint with the mixed target written in
typed endpoint/displacement form. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitTypedEndpointTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedEndpoint :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitTypedEdgeTargets
    Nx Ny Nz hx hy hz hZero
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEdgeTarget_of_typedEndpoint
      Nx Ny Nz hx hy hz hMixedEndpoint)

/-- Canonical local-correspondence endpoint with the mixed target written in
typed slot-guarded form. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitTypedSlotTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedSlot :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedSlotTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitTypedEndpointTargets
    Nx Ny Nz hx hy hz hZero
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget_of_typedSlot
      Nx Ny Nz hx hy hz hMixedSlot)

/-- Canonical local-correspondence endpoint with the mixed target in
displacement-filtered typed-slot form. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitDispFilteredTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedDisp :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainDispFilteredTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitTypedSlotTargets
    Nx Ny Nz hx hy hz hZero
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedSlotTarget_of_dispFiltered
      Nx Ny Nz hx hy hz hMixedDisp)

/-- Canonical local-correspondence endpoint with the mixed target in
base-and-displacement-filtered form. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitBaseDispTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedBase :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispFilteredTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitDispFilteredTargets
    Nx Ny Nz hx hy hz hZero
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainDispFilteredTarget_of_baseDisp
      Nx Ny Nz hx hy hz hMixedBase)

/-- Canonical local-correspondence endpoint with the mixed target in typed
cell/tetrahedron form. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitTypedTetTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedTypedTet :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispTypedTetTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitBaseDispTargets
    Nx Ny Nz hx hy hz hZero
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispFilteredTarget_of_typedTet
      Nx Ny Nz hx hy hz hMixedTypedTet)

/-- Canonical local-correspondence endpoint with the mixed target in explicit
cell/local-tetrahedron product form. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitCellTetTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hZero :
      WeightedDeficitDerivativeEventuallyZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedCellTet :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispCellTetTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitTypedTetTargets
    Nx Ny Nz hx hy hz hZero
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispTypedTetTarget_of_cellTet
      Nx Ny Nz hx hy hz hMixedCellTet)

/-- Canonical local-correspondence endpoint using the weaker weighted-stationary
Schläfli input rather than the stronger eventual-zero input. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_stationary_and_cellTetTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hStat :
      WeightedDeficitDerivativeStationaryTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedCellTet :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispCellTetTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz := by
  exact
    canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalFlat_firstVariationInput_and_directionalHessian
      Nx Ny Nz hx hy hz
      (canonicalPeriodicFirstVariationInput Nx Ny Nz hx hy hz)
      (nonlinearDirectionalHessian_of_weightedStationary_and_edgeStencil
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz)
        (canonicalPeriodicDeficitDerivativePackage Nx Ny Nz hx hy hz)
        hStat
        (canonicalPeriodicMixedHingeDeficitEdgeStencilTarget_of_localAngleTarget
          Nx Ny Nz hx hy hz
          (canonicalPeriodicMixedHingeDeficitLocalAngleTarget_of_lengthChainTarget
            Nx Ny Nz hx hy hz
            (canonicalPeriodicMixedHingeDeficitLengthChainTarget_of_expanded
              Nx Ny Nz hx hy hz
              (canonicalPeriodicMixedHingeDeficitExpandedLengthChainTarget_of_perEdge
                Nx Ny Nz hx hy hz
                (canonicalPeriodicMixedHingeDeficitExpandedLengthChainPerEdgeTarget_of_typed
                  Nx Ny Nz hx hy hz
                  (canonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEdgeTarget_of_typedEndpoint
                    Nx Ny Nz hx hy hz
                    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedEndpointTarget_of_typedSlot
                      Nx Ny Nz hx hy hz
                      (canonicalPeriodicMixedHingeDeficitExpandedLengthChainTypedSlotTarget_of_dispFiltered
                        Nx Ny Nz hx hy hz
                        (canonicalPeriodicMixedHingeDeficitExpandedLengthChainDispFilteredTarget_of_baseDisp
                          Nx Ny Nz hx hy hz
                          (canonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispFilteredTarget_of_typedTet
                            Nx Ny Nz hx hy hz
                            (canonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispTypedTetTarget_of_cellTet
                              Nx Ny Nz hx hy hz hMixedCellTet)))))))))))
        (canonicalPeriodicEdgeStencilTarget Nx Ny Nz hx hy hz))

/-- Shortest honest Track 1.B local-correspondence endpoint: second-order Schläfli
stationarity plus the global length-chain mixed identity, without routing through
per-edge endpoint-quadratic or explicit-fiber packaging. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_stationary_and_lengthChainTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hStat :
      CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget Nx Ny Nz hx hy hz)
    (hLength :
      CanonicalPeriodicMixedHingeDeficitLengthChainTarget Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz := by
  dsimp [CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget] at hStat
  exact
    canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalFlat_firstVariationInput_and_directionalHessian
      Nx Ny Nz hx hy hz
      (canonicalPeriodicFirstVariationInput Nx Ny Nz hx hy hz)
      (nonlinearDirectionalHessian_of_weightedStationary_and_edgeStencil
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz)
        (canonicalPeriodicDeficitDerivativePackage Nx Ny Nz hx hy hz)
        hStat
        (canonicalPeriodicMixedHingeDeficitEdgeStencilTarget_of_localAngleTarget
          Nx Ny Nz hx hy hz
          (canonicalPeriodicMixedHingeDeficitLocalAngleTarget_of_lengthChainTarget
            Nx Ny Nz hx hy hz hLength))
        (canonicalPeriodicEdgeStencilTarget Nx Ny Nz hx hy hz))

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_track1BOpenInputs
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (h : CanonicalPeriodicTrack1BOpenInputs Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_stationary_and_lengthChainTargets
    Nx Ny Nz hx hy hz
    ((canonicalPeriodicWeightedDeficitDerivativeStationaryTarget_iff_secondSchlaefli Nx Ny Nz hx hy
        hz).2 h.secondSchlaefli)
    h.lengthChain

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_track1BTypedEdgeOpenInputs
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (h : CanonicalPeriodicTrack1BTypedEdgeOpenInputs Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_track1BOpenInputs
    Nx Ny Nz hx hy hz
    { secondSchlaefli :=
        (canonicalPeriodicSecondSchlaefliAlongLineTarget_iff_typedEdge Nx Ny Nz hx hy hz).2
          h.typedSecondSchlaefli
      lengthChain := h.lengthChain }

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_track1BEventuallyZeroInputs
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (h : CanonicalPeriodicTrack1BEventuallyZeroInputs Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitLengthChainTargets
    Nx Ny Nz hx hy hz h.eventuallyZero h.lengthChain

theorem canonicalPeriodicTrack1BClosureTarget_iff_openInputs
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicTrack1BClosureTarget Nx Ny Nz hx hy hz ↔
      Nonempty (CanonicalPeriodicTrack1BOpenInputs Nx Ny Nz hx hy hz) := by
  constructor
  · intro h
    exact ⟨{ secondSchlaefli := h.1, lengthChain := h.2 }⟩
  · intro h
    rcases h with ⟨hOpen⟩
    exact ⟨hOpen.secondSchlaefli, hOpen.lengthChain⟩

/-- Track 1.B closure target at the canonical `(Nx,Ny,Nz) = (5,5,5)` certificate scale. -/
abbrev CanonicalPeriodicTrack1BClosureTargetAtN5 : Prop :=
  CanonicalPeriodicTrack1BClosureTarget 5 5 5 (by decide) (by decide) (by decide)

/-- The `1B-SCH` target at the canonical `(Nx,Ny,Nz) = (5,5,5)` certificate scale,
in the typed periodic-edge form used for the finite stationarity calculation. -/
abbrev CanonicalPeriodicSecondSchlaefliTypedEdgeTargetAtN5 : Prop :=
  CanonicalPeriodicSecondSchlaefliTypedEdgeTarget 5 5 5 (by decide) (by decide) (by decide)

/-- Seven-displacement-class version of the `1B-SCH` stationarity target at
the canonical `N=5` certificate scale. -/
abbrev CanonicalPeriodicSecondSchlaefliTypedEdgePerDispTargetAtN5 : Prop :=
  CanonicalPeriodicSecondSchlaefliTypedEdgePerDispTarget 5 5 5 (by decide) (by decide) (by decide)

/-- Seven named `N=5` displacement-class obligations for `1B-SCH`.  These are
the parallelizable leaves under `CanonicalPeriodicSecondSchlaefliTypedEdgePerDispTargetAtN5`. -/
structure CanonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5 : Prop where
  disp0 : CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
    5 5 5 (by decide) (by decide) (by decide) (0 : Fin 7)
  disp1 : CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
    5 5 5 (by decide) (by decide) (by decide) (1 : Fin 7)
  disp2 : CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
    5 5 5 (by decide) (by decide) (by decide) (2 : Fin 7)
  disp3 : CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
    5 5 5 (by decide) (by decide) (by decide) (3 : Fin 7)
  disp4 : CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
    5 5 5 (by decide) (by decide) (by decide) (4 : Fin 7)
  disp5 : CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
    5 5 5 (by decide) (by decide) (by decide) (5 : Fin 7)
  disp6 : CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
    5 5 5 (by decide) (by decide) (by decide) (6 : Fin 7)

theorem canonicalPeriodicSecondSchlaefliTypedEdgePerDispTargetAtN5_of_sevenDisp
    (h : CanonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5) :
    CanonicalPeriodicSecondSchlaefliTypedEdgePerDispTargetAtN5 := by
  intro ξ d
  fin_cases d
  · exact h.disp0 ξ
  · exact h.disp1 ξ
  · exact h.disp2 ξ
  · exact h.disp3 ξ
  · exact h.disp4 ξ
  · exact h.disp5 ξ
  · exact h.disp6 ξ

theorem canonicalPeriodicSecondSchlaefliTypedEdgeTargetAtN5_of_perDisp
    (hDisp : CanonicalPeriodicSecondSchlaefliTypedEdgePerDispTargetAtN5) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeTargetAtN5 :=
  canonicalPeriodicSecondSchlaefliTypedEdgeTarget_of_perDisp
    5 5 5 (by decide) (by decide) (by decide) hDisp

theorem canonicalPeriodicSecondSchlaefliTypedEdgeTargetAtN5_of_sevenDisp
    (h : CanonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeTargetAtN5 :=
  canonicalPeriodicSecondSchlaefliTypedEdgeTargetAtN5_of_perDisp
    (canonicalPeriodicSecondSchlaefliTypedEdgePerDispTargetAtN5_of_sevenDisp h)

/-- The `N=5` typed-edge Schläfli target, re-expressed as the weighted-deficit
stationarity target consumed by the nonlinear Hessian route. -/
abbrev CanonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5 : Prop :=
  CanonicalPeriodicWeightedDeficitDerivativeStationaryTarget
    5 5 5 (by decide) (by decide) (by decide)

/-- The mixed hinge-deficit length-chain target at the canonical `N=5`
certificate scale.  Session 202 finite audits show that this edge-stencil
surface is wrong-weighted as stated; keep the abbreviation for existing
packaging theorems while the corrected mixed/Hessian target is named. -/
abbrev CanonicalPeriodicMixedHingeDeficitLengthChainTargetAtN5 : Prop :=
  CanonicalPeriodicMixedHingeDeficitLengthChainTarget
    5 5 5 (by decide) (by decide) (by decide)

/-- Scalar obstruction exposed by the Session 202 exact finite audit.

The single-vertex `N=5` audit gives mixed LHS `12`, while the current
edge-stencil RHS gives `6 + 6sqrt(2) + 2sqrt(3)`.  This theorem records that
those audited scalar values cannot be equal; the next finite-lane task is to
promote the audit evaluator itself to a Lean counterexample or corrected
quadratic target. -/
theorem canonicalPeriodicMixedLengthSingleVertexAudit_scalar_mismatch :
    (12 : ℝ) ≠ 6 + 6 * Real.sqrt 2 + 2 * Real.sqrt 3 := by
  intro h
  have h2 : (1 : ℝ) < Real.sqrt 2 := by
    norm_num [Real.lt_sqrt]
  have h3 : (0 : ℝ) < Real.sqrt 3 := by
    positivity
  nlinarith

/-- Corrected mixed hinge-deficit target at the canonical `N=5` certificate
scale. -/
abbrev CanonicalPeriodicMixedHingeDeficitAxisStencilTargetAtN5 : Prop :=
  CanonicalPeriodicMixedHingeDeficitAxisStencilTarget
    5 5 5 (by decide) (by decide) (by decide)

/-- Global explicit-fiber coefficient-table target whose closure proves the
corrected mixed axis-stencil target at `N=5`. -/
abbrev CanonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTargetAtN5 : Prop :=
  CanonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTarget
    5 5 5 (by decide) (by decide) (by decide)

/-- `N=5` packaging theorem for the corrected mixed axis-stencil target. -/
theorem canonicalPeriodicMixedHingeDeficitAxisStencilTargetAtN5_of_explicitFiberAxis
    (hExplicit :
      CanonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTargetAtN5) :
    CanonicalPeriodicMixedHingeDeficitAxisStencilTargetAtN5 :=
  canonicalPeriodicMixedHingeDeficitAxisStencilTarget_of_explicitFiberAxis
    5 5 5 (by decide) (by decide) (by decide) hExplicit

/-- The Track 1.B local Regge/J-cost correspondence target at the canonical
`N=5` certificate scale. -/
abbrev CanonicalPeriodicEdgeStencilLocalCorrespondenceAtN5 : Prop :=
  CanonicalPeriodicEdgeStencilLocalCorrespondence
    5 5 5 (by decide) (by decide) (by decide)

theorem canonicalPeriodicEdgeStencilLocalCorrespondenceAtN5_of_mixedLengthChain
    (hLength : CanonicalPeriodicMixedHingeDeficitLengthChainTargetAtN5) :
    CanonicalPeriodicEdgeStencilLocalCorrespondenceAtN5 :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_stationary_and_lengthChainTargets
    5 5 5 (by decide) (by decide) (by decide)
    canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_from_nearZeroSchlaefli
    hLength

/-- Seven displacement-class Schläfli leaves imply the canonical `N=5`
weighted-deficit stationarity target.  This is the direct `1B-SCH` handoff into
the Track 1.B local-correspondence/Hessian machinery. -/
theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_of_sevenDisp
    (h : CanonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5) :
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5 :=
  (canonicalPeriodicWeightedDeficitDerivativeStationaryTarget_iff_typedEdge
    5 5 5 (by decide) (by decide) (by decide)).2
    (canonicalPeriodicSecondSchlaefliTypedEdgeTargetAtN5_of_sevenDisp h)

/-- The `disp = 0` filtered typed-edge sum is exactly the unfiltered base-vertex
sum over axis-x periodic edges.  This is the reindexing step needed before the
finite stationarity table can be reduced to a periodic base-vertex identity. -/
theorem canonicalPeriodicSecondSchlaefliTypedEdgeDisp0_sum_eq_base_sum
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (f : PeriodicEdge Nx Ny Nz → ℝ) :
    (∑ edge ∈ ((Finset.univ : Finset (PeriodicEdge Nx Ny Nz)).filter
        (fun edge => edge.disp = (0 : Fin 7))), f edge) =
      ∑ base : Vertex Nx Ny Nz, f ({ base := base, disp := (0 : Fin 7) } :
        PeriodicEdge Nx Ny Nz) := by
  classical
  refine Finset.sum_bij
    (fun edge hedge => edge.base)
    ?mem ?inj ?surj ?eq
  · intro edge hedge
    exact Finset.mem_univ edge.base
  · intro edge₁ hedge₁ edge₂ hedge₂ hbase
    have hdisp₁ : edge₁.disp = (0 : Fin 7) := (Finset.mem_filter.mp hedge₁).2
    have hdisp₂ : edge₂.disp = (0 : Fin 7) := (Finset.mem_filter.mp hedge₂).2
    cases edge₁ with
    | mk base₁ disp₁ =>
      cases edge₂ with
      | mk base₂ disp₂ =>
        dsimp at hbase hdisp₁ hdisp₂ ⊢
        cases hbase
        cases hdisp₁
        cases hdisp₂
        rfl
  · intro base _hbase
    refine ⟨({ base := base, disp := (0 : Fin 7) } :
      PeriodicEdge Nx Ny Nz), ?_, ?_⟩
    · simp
    · rfl
  · intro edge hedge
    have hdisp : edge.disp = (0 : Fin 7) := (Finset.mem_filter.mp hedge).2
    cases edge with
    | mk base disp =>
        dsimp at hdisp ⊢
        cases hdisp
        rfl

/-- Base-vertex form of the canonical `N=5`, `disp0` Schläfli stationarity
leaf.  The remaining work is now the finite periodic axis-edge cancellation
over the 125 base vertices, with no filtered `PeriodicEdge` bookkeeping. -/
def CanonicalPeriodicSecondSchlaefliTypedEdgeDisp0BaseVertexTargetAtN5 : Prop :=
  ∀ ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)).K,
    (∑ base : Vertex 5 5 5,
      canonicalPeriodicSecondSchlaefliTypedEdgeSummand
        5 5 5 (by decide) (by decide) (by decide) ξ
        ({ base := base, disp := (0 : Fin 7) } : PeriodicEdge 5 5 5)) = 0

/-- The partial weighted deficit-derivative sum over the canonical `disp0`
axis-edge class at `N=5`.  Its derivative at zero is exactly the base-vertex
second-Schläfli target above. -/
noncomputable def canonicalPeriodicDisp0WeightedDeficitDerivativeBaseSumAtN5
    (ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)).K)
    (t : ℝ) : ℝ :=
  let P := canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)
  ∑ base : Vertex 5 5 5,
    let edge : PeriodicEdge 5 5 5 := { base := base, disp := (0 : Fin 7) }
    let e := P.edgeEquiv.symm edge
    hingeMeasureUnderConformal P.K P.hK
      (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
      deficitLineDeriv P.K ξ e t

/-- Stationarity of the partial `disp0` weighted deficit-derivative sum.  This
is now the precise remaining analytic/combinatorial content for the `disp0`
leaf. -/
def CanonicalPeriodicDisp0WeightedDeficitDerivativeBaseStationaryTargetAtN5 : Prop :=
  ∀ ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)).K,
    HasDerivAt (canonicalPeriodicDisp0WeightedDeficitDerivativeBaseSumAtN5 ξ) 0 0

set_option maxHeartbeats 10000000

/-- The derivative of the partial `disp0` weighted deficit-derivative sum is
the base-vertex second-Schläfli summand. -/
theorem canonicalPeriodicDisp0WeightedDeficitDerivativeBaseSumAtN5_hasDerivAt
    (ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)).K) :
    HasDerivAt
      (canonicalPeriodicDisp0WeightedDeficitDerivativeBaseSumAtN5 ξ)
      (∑ base : Vertex 5 5 5,
        canonicalPeriodicSecondSchlaefliTypedEdgeSummand
          5 5 5 (by decide) (by decide) (by decide) ξ
          ({ base := base, disp := (0 : Fin 7) } : PeriodicEdge 5 5 5)) 0 := by
  let P := canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)
  have hSecond :=
    hingeDeficitSecondLineDifferentiabilityAtZero_of_flatConfiguration P.K P.hK
      (canonicalPeriodicFlatConfiguration 5 5 5 (by decide) (by decide) (by decide))
  have hBase : ∀ base : Vertex 5 5 5,
      HasDerivAt
        (fun t : ℝ =>
          let edge : PeriodicEdge 5 5 5 := { base := base, disp := (0 : Fin 7) }
          let e := P.edgeEquiv.symm edge
          hingeMeasureUnderConformal P.K P.hK
            (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
            deficitLineDeriv P.K ξ e t)
        (canonicalPeriodicSecondSchlaefliTypedEdgeSummand
          5 5 5 (by decide) (by decide) (by decide) ξ
          ({ base := base, disp := (0 : Fin 7) } : PeriodicEdge 5 5 5)) 0 := by
    intro base
    let edge : PeriodicEdge 5 5 5 := { base := base, disp := (0 : Fin 7) }
    let e := P.edgeEquiv.symm edge
    have hHinge0 : DifferentiableAt ℝ
        (fun t : ℝ => hingeMeasureUnderConformal P.K P.hK
          (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e) 0 :=
      (hingeLine_contDiffAt_zero P.K P.hK ξ e).differentiableAt (by simp)
    have hHingeLine : HasDerivAt
        (fun t : ℝ => hingeMeasureUnderConformal P.K P.hK
          (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e)
        (hingeLineDeriv P.K P.hK ξ e 0) 0 := by
      simpa [hingeLineDeriv] using hHinge0.hasDerivAt
    have hDefDeriv : HasDerivAt (fun t : ℝ => deficitLineDeriv P.K ξ e t)
        (deficitLineSecondDeriv P.K ξ e 0) 0 := by
      simpa [deficitLineSecondDeriv] using (hSecond ξ e).2.hasDerivAt
    change HasDerivAt
      (fun t : ℝ =>
        hingeMeasureUnderConformal P.K P.hK
          (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
          deficitLineDeriv P.K ξ e t)
      (hingeLineDeriv P.K P.hK ξ e 0 * deficitLineDeriv P.K ξ e 0 +
        hingeMeasureUnderConformal P.K P.hK
          (Geometry.ReggeActionSecondVariation.linePotential P.K ξ 0) e *
          deficitLineSecondDeriv P.K ξ e 0) 0
    convert hDefDeriv.mul hHingeLine using 1
    · ext t
      simp only [Pi.mul_apply]
      ring
    · ring_nf
  have hsum := HasDerivAt.sum
    (u := Finset.univ)
    (A := fun base t =>
      let edge : PeriodicEdge 5 5 5 := { base := base, disp := (0 : Fin 7) }
      let e := P.edgeEquiv.symm edge
      hingeMeasureUnderConformal P.K P.hK
        (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
        deficitLineDeriv P.K ξ e t)
    (A' := fun base =>
      canonicalPeriodicSecondSchlaefliTypedEdgeSummand
        5 5 5 (by decide) (by decide) (by decide) ξ
        ({ base := base, disp := (0 : Fin 7) } : PeriodicEdge 5 5 5))
    (x := 0)
    (fun base _ => hBase base)
  change HasDerivAt
    (fun t : ℝ =>
      ∑ base : Vertex 5 5 5,
        (let edge : PeriodicEdge 5 5 5 := { base := base, disp := (0 : Fin 7) }
         let e := P.edgeEquiv.symm edge
         hingeMeasureUnderConformal P.K P.hK
          (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
          deficitLineDeriv P.K ξ e t))
    (∑ base : Vertex 5 5 5,
      canonicalPeriodicSecondSchlaefliTypedEdgeSummand
        5 5 5 (by decide) (by decide) (by decide) ξ
        ({ base := base, disp := (0 : Fin 7) } : PeriodicEdge 5 5 5)) 0
  rw [show
      (fun t : ℝ =>
        ∑ base : Vertex 5 5 5,
          (let edge : PeriodicEdge 5 5 5 := { base := base, disp := (0 : Fin 7) }
           let e := P.edgeEquiv.symm edge
           hingeMeasureUnderConformal P.K P.hK
            (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
            deficitLineDeriv P.K ξ e t)) =
      (∑ base : Vertex 5 5 5,
        fun t : ℝ =>
          (let edge : PeriodicEdge 5 5 5 := { base := base, disp := (0 : Fin 7) }
           let e := P.edgeEquiv.symm edge
           hingeMeasureUnderConformal P.K P.hK
            (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
            deficitLineDeriv P.K ξ e t)) by
    funext t
    simp only [Finset.sum_apply]]
  exact hsum

set_option maxRecDepth 100000

/-- Stationarity of the partial `disp0` weighted deficit-derivative sum closes
the base-vertex `disp0` second-Schläfli target. -/
theorem CanonicalPeriodicSecondSchlaefliTypedEdgeDisp0BaseVertexTargetAtN5_of_stationary
    (hStat : CanonicalPeriodicDisp0WeightedDeficitDerivativeBaseStationaryTargetAtN5) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeDisp0BaseVertexTargetAtN5 := by
  intro ξ
  have hcalc := canonicalPeriodicDisp0WeightedDeficitDerivativeBaseSumAtN5_hasDerivAt ξ
  have hzero := hcalc.unique (hStat ξ)
  exact hzero

/-- The base-vertex axis-edge cancellation implies the actual `disp0` leaf in
`CanonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5`. -/
theorem canonicalPeriodicSecondSchlaefliTypedEdgeDisp0TargetAtN5_of_baseVertexTarget
    (h : CanonicalPeriodicSecondSchlaefliTypedEdgeDisp0BaseVertexTargetAtN5) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
      5 5 5 (by decide) (by decide) (by decide) (0 : Fin 7) := by
  intro ξ
  rw [canonicalPeriodicSecondSchlaefliTypedEdgeDisp0_sum_eq_base_sum]
  exact h ξ

/-! ### Parametric `disp d` reductions for all seven displacement classes

The disp0 chain (Sessions 191/194/195) reduces the axis displacement leaf to
a single stationarity claim.  This block generalizes that chain to any
`d : Fin 7`, exposing one uniform proof template for all seven leaves of
`CanonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5`.  Each
remaining open content is now a single `HasDerivAt _ _ 0` stationarity claim
for the partial weighted deficit-derivative sum over the corresponding
displacement class. -/

/-- Generic version of the `disp = 0` filtered typed-edge sum identity: for
any `d : Fin 7`, the filtered typed-edge sum is the unfiltered base-vertex
sum over the corresponding axis-edge class. -/
theorem canonicalPeriodicSecondSchlaefliTypedEdgeDisp_sum_eq_base_sum
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (d : Fin 7)
    (f : PeriodicEdge Nx Ny Nz → ℝ) :
    (∑ edge ∈ ((Finset.univ : Finset (PeriodicEdge Nx Ny Nz)).filter
        (fun edge => edge.disp = d)), f edge) =
      ∑ base : Vertex Nx Ny Nz, f ({ base := base, disp := d } :
        PeriodicEdge Nx Ny Nz) := by
  classical
  refine Finset.sum_bij
    (fun edge _ => edge.base)
    ?mem ?inj ?surj ?eq
  · intro edge _hedge
    exact Finset.mem_univ edge.base
  · intro edge₁ hedge₁ edge₂ hedge₂ hbase
    have hdisp₁ : edge₁.disp = d := (Finset.mem_filter.mp hedge₁).2
    have hdisp₂ : edge₂.disp = d := (Finset.mem_filter.mp hedge₂).2
    cases edge₁ with
    | mk base₁ disp₁ =>
      cases edge₂ with
      | mk base₂ disp₂ =>
        dsimp at hbase hdisp₁ hdisp₂ ⊢
        cases hbase
        cases hdisp₁
        cases hdisp₂
        rfl
  · intro base _hbase
    refine ⟨({ base := base, disp := d } :
      PeriodicEdge Nx Ny Nz), ?_, ?_⟩
    · simp
    · rfl
  · intro edge hedge
    have hdisp : edge.disp = d := (Finset.mem_filter.mp hedge).2
    cases edge with
    | mk base disp =>
        dsimp at hdisp ⊢
        cases hdisp
        rfl

/-- Generic base-vertex form of the canonical `N=5` displacement-class
Schläfli stationarity leaf. -/
def CanonicalPeriodicSecondSchlaefliTypedEdgeDispBaseVertexTargetAtN5
    (d : Fin 7) : Prop :=
  ∀ ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)).K,
    (∑ base : Vertex 5 5 5,
      canonicalPeriodicSecondSchlaefliTypedEdgeSummand
        5 5 5 (by decide) (by decide) (by decide) ξ
        ({ base := base, disp := d } : PeriodicEdge 5 5 5)) = 0

/-- Generic base-vertex target implies the matching `DispTarget` at `N=5`. -/
theorem canonicalPeriodicSecondSchlaefliTypedEdgeDispTargetAtN5_of_baseVertexTarget
    (d : Fin 7)
    (h : CanonicalPeriodicSecondSchlaefliTypedEdgeDispBaseVertexTargetAtN5 d) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
      5 5 5 (by decide) (by decide) (by decide) d := by
  intro ξ
  rw [canonicalPeriodicSecondSchlaefliTypedEdgeDisp_sum_eq_base_sum]
  exact h ξ

/-- The partial weighted deficit-derivative sum over the canonical
displacement class `d` at `N=5`.  Its derivative at zero is the matching
base-vertex second-Schläfli summand. -/
noncomputable def canonicalPeriodicDispWeightedDeficitDerivativeBaseSumAtN5
    (d : Fin 7)
    (ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)).K)
    (t : ℝ) : ℝ :=
  let P := canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)
  ∑ base : Vertex 5 5 5,
    let edge : PeriodicEdge 5 5 5 := { base := base, disp := d }
    let e := P.edgeEquiv.symm edge
    hingeMeasureUnderConformal P.K P.hK
      (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
      deficitLineDeriv P.K ξ e t

/-- Stationarity of the partial `disp d` weighted deficit-derivative sum.
This is the precise remaining analytic/combinatorial content for each
displacement leaf. -/
def CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5
    (d : Fin 7) : Prop :=
  ∀ ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)).K,
    HasDerivAt (canonicalPeriodicDispWeightedDeficitDerivativeBaseSumAtN5 d ξ) 0 0

set_option maxHeartbeats 10000000 in
/-- The derivative of the partial `disp d` weighted deficit-derivative sum is
the matching base-vertex second-Schläfli summand. -/
theorem canonicalPeriodicDispWeightedDeficitDerivativeBaseSumAtN5_hasDerivAt
    (d : Fin 7)
    (ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)).K) :
    HasDerivAt
      (canonicalPeriodicDispWeightedDeficitDerivativeBaseSumAtN5 d ξ)
      (∑ base : Vertex 5 5 5,
        canonicalPeriodicSecondSchlaefliTypedEdgeSummand
          5 5 5 (by decide) (by decide) (by decide) ξ
          ({ base := base, disp := d } : PeriodicEdge 5 5 5)) 0 := by
  let P := canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)
  have hSecond :=
    hingeDeficitSecondLineDifferentiabilityAtZero_of_flatConfiguration P.K P.hK
      (canonicalPeriodicFlatConfiguration 5 5 5 (by decide) (by decide) (by decide))
  have hBase : ∀ base : Vertex 5 5 5,
      HasDerivAt
        (fun t : ℝ =>
          let edge : PeriodicEdge 5 5 5 := { base := base, disp := d }
          let e := P.edgeEquiv.symm edge
          hingeMeasureUnderConformal P.K P.hK
            (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
            deficitLineDeriv P.K ξ e t)
        (canonicalPeriodicSecondSchlaefliTypedEdgeSummand
          5 5 5 (by decide) (by decide) (by decide) ξ
          ({ base := base, disp := d } : PeriodicEdge 5 5 5)) 0 := by
    intro base
    let edge : PeriodicEdge 5 5 5 := { base := base, disp := d }
    let e := P.edgeEquiv.symm edge
    have hHinge0 : DifferentiableAt ℝ
        (fun t : ℝ => hingeMeasureUnderConformal P.K P.hK
          (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e) 0 :=
      (hingeLine_contDiffAt_zero P.K P.hK ξ e).differentiableAt (by simp)
    have hHingeLine : HasDerivAt
        (fun t : ℝ => hingeMeasureUnderConformal P.K P.hK
          (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e)
        (hingeLineDeriv P.K P.hK ξ e 0) 0 := by
      simpa [hingeLineDeriv] using hHinge0.hasDerivAt
    have hDefDeriv : HasDerivAt (fun t : ℝ => deficitLineDeriv P.K ξ e t)
        (deficitLineSecondDeriv P.K ξ e 0) 0 := by
      simpa [deficitLineSecondDeriv] using (hSecond ξ e).2.hasDerivAt
    change HasDerivAt
      (fun t : ℝ =>
        hingeMeasureUnderConformal P.K P.hK
          (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
          deficitLineDeriv P.K ξ e t)
      (hingeLineDeriv P.K P.hK ξ e 0 * deficitLineDeriv P.K ξ e 0 +
        hingeMeasureUnderConformal P.K P.hK
          (Geometry.ReggeActionSecondVariation.linePotential P.K ξ 0) e *
          deficitLineSecondDeriv P.K ξ e 0) 0
    convert hDefDeriv.mul hHingeLine using 1
    · ext t
      simp only [Pi.mul_apply]
      ring
    · ring_nf
  have hsum := HasDerivAt.sum
    (u := Finset.univ)
    (A := fun base t =>
      let edge : PeriodicEdge 5 5 5 := { base := base, disp := d }
      let e := P.edgeEquiv.symm edge
      hingeMeasureUnderConformal P.K P.hK
        (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
        deficitLineDeriv P.K ξ e t)
    (A' := fun base =>
      canonicalPeriodicSecondSchlaefliTypedEdgeSummand
        5 5 5 (by decide) (by decide) (by decide) ξ
        ({ base := base, disp := d } : PeriodicEdge 5 5 5))
    (x := 0)
    (fun base _ => hBase base)
  change HasDerivAt
    (fun t : ℝ =>
      ∑ base : Vertex 5 5 5,
        (let edge : PeriodicEdge 5 5 5 := { base := base, disp := d }
         let e := P.edgeEquiv.symm edge
         hingeMeasureUnderConformal P.K P.hK
          (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
          deficitLineDeriv P.K ξ e t))
    (∑ base : Vertex 5 5 5,
      canonicalPeriodicSecondSchlaefliTypedEdgeSummand
        5 5 5 (by decide) (by decide) (by decide) ξ
        ({ base := base, disp := d } : PeriodicEdge 5 5 5)) 0
  rw [show
      (fun t : ℝ =>
        ∑ base : Vertex 5 5 5,
          (let edge : PeriodicEdge 5 5 5 := { base := base, disp := d }
           let e := P.edgeEquiv.symm edge
           hingeMeasureUnderConformal P.K P.hK
            (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
            deficitLineDeriv P.K ξ e t)) =
      (∑ base : Vertex 5 5 5,
        fun t : ℝ =>
          (let edge : PeriodicEdge 5 5 5 := { base := base, disp := d }
           let e := P.edgeEquiv.symm edge
           hingeMeasureUnderConformal P.K P.hK
            (Geometry.ReggeActionSecondVariation.linePotential P.K ξ t) e *
            deficitLineDeriv P.K ξ e t)) by
    funext t
    simp only [Finset.sum_apply]]
  exact hsum

/-- Stationarity of the partial `disp d` weighted deficit-derivative sum
closes the matching base-vertex `disp` second-Schläfli target. -/
theorem CanonicalPeriodicSecondSchlaefliTypedEdgeDispBaseVertexTargetAtN5_of_stationary
    (d : Fin 7)
    (hStat : CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 d) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeDispBaseVertexTargetAtN5 d := by
  intro ξ
  have hcalc := canonicalPeriodicDispWeightedDeficitDerivativeBaseSumAtN5_hasDerivAt d ξ
  have hzero := hcalc.unique (hStat ξ)
  exact hzero

/-- The seven `disp d` stationarity claims, one for each displacement class.
This is the parametric bundle that supersedes the disp0-only stationarity
target.  Each field is a single `HasDerivAt _ _ 0` claim for the partial
weighted deficit-derivative sum over the corresponding displacement class. -/
structure CanonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5 : Prop where
  disp0 : CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (0 : Fin 7)
  disp1 : CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (1 : Fin 7)
  disp2 : CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (2 : Fin 7)
  disp3 : CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (3 : Fin 7)
  disp4 : CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (4 : Fin 7)
  disp5 : CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (5 : Fin 7)
  disp6 : CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (6 : Fin 7)

/-- A single quantified displacement-stationarity proof supplies the seven
named stationarity leaves.  This is the preferred next proof interface: prove
`∀ d : Fin 7, CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 d`,
then this theorem packages the seven fields without repeated bookkeeping. -/
theorem canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall
    (h : ∀ d : Fin 7,
      CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 d) :
    CanonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5 where
  disp0 := h (0 : Fin 7)
  disp1 := h (1 : Fin 7)
  disp2 := h (2 : Fin 7)
  disp3 := h (3 : Fin 7)
  disp4 := h (4 : Fin 7)
  disp5 := h (5 : Fin 7)
  disp6 := h (6 : Fin 7)

/-- Session 558 projection: the uniform displacement-stationarity proof supplies
the `disp0` stationarity leaf. -/
theorem canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall_disp0
    (h : ∀ d : Fin 7,
      CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 d) :
    CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (0 : Fin 7) :=
  (canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall h).disp0

/-- Session 558 projection: the uniform displacement-stationarity proof supplies
the `disp1` stationarity leaf. -/
theorem canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall_disp1
    (h : ∀ d : Fin 7,
      CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 d) :
    CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (1 : Fin 7) :=
  (canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall h).disp1

/-- Session 558 projection: the uniform displacement-stationarity proof supplies
the `disp2` stationarity leaf. -/
theorem canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall_disp2
    (h : ∀ d : Fin 7,
      CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 d) :
    CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (2 : Fin 7) :=
  (canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall h).disp2

/-- Session 558 projection: the uniform displacement-stationarity proof supplies
the `disp3` stationarity leaf. -/
theorem canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall_disp3
    (h : ∀ d : Fin 7,
      CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 d) :
    CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (3 : Fin 7) :=
  (canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall h).disp3

/-- Session 558 projection: the uniform displacement-stationarity proof supplies
the `disp4` stationarity leaf. -/
theorem canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall_disp4
    (h : ∀ d : Fin 7,
      CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 d) :
    CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (4 : Fin 7) :=
  (canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall h).disp4

/-- Session 558 projection: the uniform displacement-stationarity proof supplies
the `disp5` stationarity leaf. -/
theorem canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall_disp5
    (h : ∀ d : Fin 7,
      CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 d) :
    CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (5 : Fin 7) :=
  (canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall h).disp5

/-- Session 558 projection: the uniform displacement-stationarity proof supplies
the `disp6` stationarity leaf. -/
theorem canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall_disp6
    (h : ∀ d : Fin 7,
      CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 d) :
    CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 (6 : Fin 7) :=
  (canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall h).disp6

/-- Session 558 audit count for the seven uniform-stationarity packaging
projections: `disp0` through `disp6`. -/
def canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5ForallProjectionCount :
    ℕ := 7

theorem canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5ForallProjectionCount_eq_seven :
    canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5ForallProjectionCount = 7 := rfl

/-- The seven displacement-class stationarity claims imply the seven
displacement-class typed-edge Schläfli leaves consumed by
`canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_of_sevenDisp`. -/
theorem canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity
    (h : CanonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5 where
  disp0 :=
    canonicalPeriodicSecondSchlaefliTypedEdgeDispTargetAtN5_of_baseVertexTarget (0 : Fin 7)
      (CanonicalPeriodicSecondSchlaefliTypedEdgeDispBaseVertexTargetAtN5_of_stationary
        (0 : Fin 7) h.disp0)
  disp1 :=
    canonicalPeriodicSecondSchlaefliTypedEdgeDispTargetAtN5_of_baseVertexTarget (1 : Fin 7)
      (CanonicalPeriodicSecondSchlaefliTypedEdgeDispBaseVertexTargetAtN5_of_stationary
        (1 : Fin 7) h.disp1)
  disp2 :=
    canonicalPeriodicSecondSchlaefliTypedEdgeDispTargetAtN5_of_baseVertexTarget (2 : Fin 7)
      (CanonicalPeriodicSecondSchlaefliTypedEdgeDispBaseVertexTargetAtN5_of_stationary
        (2 : Fin 7) h.disp2)
  disp3 :=
    canonicalPeriodicSecondSchlaefliTypedEdgeDispTargetAtN5_of_baseVertexTarget (3 : Fin 7)
      (CanonicalPeriodicSecondSchlaefliTypedEdgeDispBaseVertexTargetAtN5_of_stationary
        (3 : Fin 7) h.disp3)
  disp4 :=
    canonicalPeriodicSecondSchlaefliTypedEdgeDispTargetAtN5_of_baseVertexTarget (4 : Fin 7)
      (CanonicalPeriodicSecondSchlaefliTypedEdgeDispBaseVertexTargetAtN5_of_stationary
        (4 : Fin 7) h.disp4)
  disp5 :=
    canonicalPeriodicSecondSchlaefliTypedEdgeDispTargetAtN5_of_baseVertexTarget (5 : Fin 7)
      (CanonicalPeriodicSecondSchlaefliTypedEdgeDispBaseVertexTargetAtN5_of_stationary
        (5 : Fin 7) h.disp5)
  disp6 :=
    canonicalPeriodicSecondSchlaefliTypedEdgeDispTargetAtN5_of_baseVertexTarget (6 : Fin 7)
      (CanonicalPeriodicSecondSchlaefliTypedEdgeDispBaseVertexTargetAtN5_of_stationary
        (6 : Fin 7) h.disp6)

/-- Session 559 projection: seven stationarity leaves supply the `disp0`
typed-edge Schläfli leaf. -/
theorem canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity_disp0
    (h : CanonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
      5 5 5 (by decide) (by decide) (by decide) (0 : Fin 7) :=
  (canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity h).disp0

/-- Session 559 projection: seven stationarity leaves supply the `disp1`
typed-edge Schläfli leaf. -/
theorem canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity_disp1
    (h : CanonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
      5 5 5 (by decide) (by decide) (by decide) (1 : Fin 7) :=
  (canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity h).disp1

/-- Session 559 projection: seven stationarity leaves supply the `disp2`
typed-edge Schläfli leaf. -/
theorem canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity_disp2
    (h : CanonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
      5 5 5 (by decide) (by decide) (by decide) (2 : Fin 7) :=
  (canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity h).disp2

/-- Session 559 projection: seven stationarity leaves supply the `disp3`
typed-edge Schläfli leaf. -/
theorem canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity_disp3
    (h : CanonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
      5 5 5 (by decide) (by decide) (by decide) (3 : Fin 7) :=
  (canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity h).disp3

/-- Session 559 projection: seven stationarity leaves supply the `disp4`
typed-edge Schläfli leaf. -/
theorem canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity_disp4
    (h : CanonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
      5 5 5 (by decide) (by decide) (by decide) (4 : Fin 7) :=
  (canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity h).disp4

/-- Session 559 projection: seven stationarity leaves supply the `disp5`
typed-edge Schläfli leaf. -/
theorem canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity_disp5
    (h : CanonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
      5 5 5 (by decide) (by decide) (by decide) (5 : Fin 7) :=
  (canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity h).disp5

/-- Session 559 projection: seven stationarity leaves supply the `disp6`
typed-edge Schläfli leaf. -/
theorem canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity_disp6
    (h : CanonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5) :
    CanonicalPeriodicSecondSchlaefliTypedEdgeDispTarget
      5 5 5 (by decide) (by decide) (by decide) (6 : Fin 7) :=
  (canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity h).disp6

/-- Session 559 audit count for the seven stationarity-to-Schläfli leaf
projections: `disp0` through `disp6`. -/
def canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5SevenStationarityProjectionCount :
    ℕ := 7

theorem canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5SevenStationarityProjectionCount_eq_seven :
    canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5SevenStationarityProjectionCount = 7 := rfl

/-- The seven parametric stationarity claims chain directly to the
canonical `N=5` weighted-deficit stationarity target consumed by
`CanonicalPeriodicEdgeStencilLocalCorrespondence`.  This is the parametric
endpoint of the entire `1B-SCH` reduction: the remaining open content is
exactly the seven `HasDerivAt _ _ 0` stationarity claims. -/
theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_of_sevenStationarity
    (h : CanonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5) :
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5 :=
  canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_of_sevenDisp
    (canonicalPeriodicSecondSchlaefliTypedEdgeSevenDispTargetsAtN5_of_sevenStationarity h)

/-- Session 561 endpoint: a uniform proof of all seven displacement-class
stationarity claims closes the canonical `N=5` weighted-deficit stationarity
target directly. -/
theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_of_forallDispStationarity
    (h : ∀ d : Fin 7,
      CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 d) :
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5 :=
  canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_of_sevenStationarity
    (canonicalPeriodicDispWeightedDeficitDerivativeSevenBaseStationaryTargetsAtN5_of_forall h)

/-- Session 561 audit count for the direct uniform-stationarity endpoint. -/
def canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5ForallDispEndpointCount :
    ℕ := 1

theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5ForallDispEndpointCount_eq_one :
    canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5ForallDispEndpointCount = 1 := rfl

/-- Session 567 target: the sum over all seven displacement-class partial
weighted deficit-derivative sums is stationary at the flat point. -/
def CanonicalPeriodicDispWeightedDeficitDerivativeBaseSumTotalStationaryTargetAtN5 : Prop :=
  ∀ ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)).K,
    HasDerivAt
      (fun t : ℝ =>
        ∑ d : Fin 7, canonicalPeriodicDispWeightedDeficitDerivativeBaseSumAtN5 d ξ t)
      0 0

/-- Session 567 target: all seven displacement-class partial weighted
deficit-derivative sums are the same one-variable function.  This is the finite
translation/cube-symmetry content needed after the total stationarity claim. -/
def CanonicalPeriodicDispWeightedDeficitDerivativeBaseSumDispSymmetryTargetAtN5 : Prop :=
  ∀ (d : Fin 7)
    (ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)).K),
    (fun t : ℝ => canonicalPeriodicDispWeightedDeficitDerivativeBaseSumAtN5 d ξ t) =
      (fun t : ℝ =>
        canonicalPeriodicDispWeightedDeficitDerivativeBaseSumAtN5 (0 : Fin 7) ξ t)

/-- Session 567 reduction: total stationarity plus displacement-class symmetry
closes the uniform seven-displacement stationarity target. -/
theorem canonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5_of_totalStationary_and_dispSymmetry
    (hTotal : CanonicalPeriodicDispWeightedDeficitDerivativeBaseSumTotalStationaryTargetAtN5)
    (hSym : CanonicalPeriodicDispWeightedDeficitDerivativeBaseSumDispSymmetryTargetAtN5) :
    ∀ d : Fin 7, CanonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5 d := by
  intro d ξ
  let f0 : ℝ → ℝ :=
    fun t => canonicalPeriodicDispWeightedDeficitDerivativeBaseSumAtN5 (0 : Fin 7) ξ t
  have hsum_eq :
      (fun t : ℝ =>
        ∑ e : Fin 7, canonicalPeriodicDispWeightedDeficitDerivativeBaseSumAtN5 e ξ t) =
        (fun t : ℝ => (7 : ℝ) * f0 t) := by
    funext t
    calc
      (∑ e : Fin 7, canonicalPeriodicDispWeightedDeficitDerivativeBaseSumAtN5 e ξ t) =
          ∑ _e : Fin 7, f0 t := by
            apply Finset.sum_congr rfl
            intro e _he
            exact congrFun (hSym e ξ) t
      _ = (7 : ℝ) * f0 t := by
            simp [f0]
  have hscaled : HasDerivAt (fun t : ℝ => (7 : ℝ) * f0 t) 0 0 := by
    simpa [hsum_eq] using hTotal ξ
  have h0 : HasDerivAt f0 0 0 := by
    have hdiv := hscaled.const_mul ((7 : ℝ)⁻¹)
    simpa [f0, mul_assoc] using hdiv
  convert h0 using 1
  funext t
  simpa [f0] using congrFun (hSym d ξ) t

/-- Session 567 audit count for the total-plus-symmetry stationarity reduction:
total stationarity, displacement symmetry, and the reduction theorem. -/
def canonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTotalSymmetryReductionCount :
    ℕ := 3

theorem canonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTotalSymmetryReductionCount_eq_three :
    canonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTotalSymmetryReductionCount = 3 := rfl

/-- Session 571 direct endpoint: total stationarity plus displacement-class
symmetry closes the canonical `N=5` weighted-deficit stationarity target without
requiring callers to route through the uniform `∀ d` statement manually. -/
theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_of_totalStationary_and_dispSymmetry
    (hTotal : CanonicalPeriodicDispWeightedDeficitDerivativeBaseSumTotalStationaryTargetAtN5)
    (hSym : CanonicalPeriodicDispWeightedDeficitDerivativeBaseSumDispSymmetryTargetAtN5) :
    CanonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5 :=
  canonicalPeriodicWeightedDeficitDerivativeStationaryTargetAtN5_of_forallDispStationarity
    (canonicalPeriodicDispWeightedDeficitDerivativeBaseStationaryTargetAtN5_of_totalStationary_and_dispSymmetry
      hTotal hSym)

/-- Session 571 audit count for the direct total-plus-symmetry stationarity endpoint. -/
def canonicalPeriodicWeightedDeficitDerivativeStationaryTotalSymmetryEndpointCount :
    ℕ := 1

theorem canonicalPeriodicWeightedDeficitDerivativeStationaryTotalSymmetryEndpointCount_eq_one :
    canonicalPeriodicWeightedDeficitDerivativeStationaryTotalSymmetryEndpointCount = 1 := rfl

/-- Track 1.B typed-edge open-input package at the canonical `N=5` certificate scale. -/
abbrev CanonicalPeriodicTrack1BTypedEdgeOpenInputsAtN5 : Prop :=
  Nonempty (CanonicalPeriodicTrack1BTypedEdgeOpenInputs 5 5 5 (by decide) (by decide) (by decide))

/-- Canonical local-correspondence endpoint with the mixed target reduced to
the local-pair displacement-filtered form. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitLocalPairTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hStat :
      WeightedDeficitDerivativeStationaryTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedLocalPair :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainLocalPairTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_stationary_and_cellTetTargets
    Nx Ny Nz hx hy hz hStat
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainBaseDispCellTetTarget_of_localPair
      Nx Ny Nz hx hy hz hMixedLocalPair)

/-- Canonical local-correspondence endpoint with the mixed target in explicit
local-pair displacement-fiber form. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitLocalPairFiberTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hStat :
      WeightedDeficitDerivativeStationaryTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedFiber :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainLocalPairFiberTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitLocalPairTargets
    Nx Ny Nz hx hy hz hStat
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainLocalPairTarget_of_fiber
      Nx Ny Nz hx hy hz hMixedFiber)

/-- Canonical local-correspondence endpoint with the mixed target over the
explicit precomputed Freudenthal local-pair displacement fiber. -/
theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitExplicitFiberTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hStat :
      WeightedDeficitDerivativeStationaryTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedExplicit :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitLocalPairFiberTargets
    Nx Ny Nz hx hy hz hStat
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainLocalPairFiberTarget_of_explicitFiber
      Nx Ny Nz hx hy hz hMixedExplicit)

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitExplicitFiberFlatUnfoldedTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hStat :
      WeightedDeficitDerivativeStationaryTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedFlatUnfolded :
      CanonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitExplicitFiberTargets
    Nx Ny Nz hx hy hz hStat
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget_of_flatUnfolded
      Nx Ny Nz hx hy hz hMixedFlatUnfolded)

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitExplicitFiberClosedFormTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hStat :
      WeightedDeficitDerivativeStationaryTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedClosedForm :
      CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitExplicitFiberFlatUnfoldedTargets
    Nx Ny Nz hx hy hz hStat
    (canonicalPeriodicMixedHingeDeficitExplicitFiberFlatUnfoldedTarget_of_closedForm
      Nx Ny Nz hx hy hz hMixedClosedForm)

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitExplicitFiberClosedFormPerDispTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hStat :
      WeightedDeficitDerivativeStationaryTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hPerDisp :
      ∀ d : Fin 7,
        CanonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormPerDispTarget
          Nx Ny Nz hx hy hz d) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitExplicitFiberClosedFormTargets
    Nx Ny Nz hx hy hz hStat
    (canonicalPeriodicMixedHingeDeficitExplicitFiberClosedFormTarget_of_perDisp
      Nx Ny Nz hx hy hz hPerDisp)

theorem canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitExplicitFiberAngleChainTargets
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hStat :
      WeightedDeficitDerivativeStationaryTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    (hMixedAngleChain :
      CanonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberAngleChainTarget
        Nx Ny Nz hx hy hz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz :=
  canonicalPeriodicEdgeStencilLocalCorrespondence_of_canonicalDeficitExplicitFiberTargets
    Nx Ny Nz hx hy hz hStat
    (canonicalPeriodicMixedHingeDeficitExpandedLengthChainExplicitFiberTarget_of_angleChain
      Nx Ny Nz hx hy hz hMixedAngleChain)

/-- The input bundle exposes the flat-deficit target needed by the previous
normalization bridge. -/
theorem CanonicalPeriodicFlatConfigurationInputs.flatDeficitZeroTarget
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    {hx : 2 < Nx} {hy : 2 < Ny} {hz : 2 < Nz}
    (I : CanonicalPeriodicFlatConfigurationInputs Nx Ny Nz hx hy hz) :
    FlatDeficitZeroTarget
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K :=
  (flatDeficitZeroTarget_iff_globalZeroDeficitAtFlat
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K).2
    I.global_zero_deficit

/-- Canonical periodic flat-action normalization from the two-input flat
configuration bundle. -/
theorem canonicalPeriodicReggeAction_zeroPotential_eq_zero_of_flatConfigurationInputs
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (I : CanonicalPeriodicFlatConfigurationInputs Nx Ny Nz hx hy hz) :
    reggeAction
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (zeroPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) = 0 :=
  canonicalPeriodicReggeAction_zeroPotential_eq_zero_of_flatConfiguration
    Nx Ny Nz hx hy hz I.toFlatConfiguration

/-- Exact quadratic normalization for the second-order Regge action.  If the
flat action is normalized to zero, then the spacing-scaled second-order action
on `a • ξ`, divided by `||a||^2`, is exactly the quadratic form
`(1 / 2) * H(ξ, ξ)` for every nonzero spacing `a`. -/
theorem reggeActionSecondOrder_spacing_scaled_div_norm_sq_eq_quadratic_of_flat_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (H : Fin K.nV → Fin K.nV → ℝ)
    (hFlat : reggeAction K hK (zeroPotential K) = 0)
    (a : ℝ) (ha : a ≠ 0) (ξ : VertexPotential K) :
    reggeActionSecondOrder K hK H (a • ξ) / ‖a‖ ^ (2 : ℕ) =
      (1 / 2) * hessianQuadratic H ξ := by
  have hquad : hessianQuadratic H (a • ξ) =
      a ^ (2 : ℕ) * hessianQuadratic H ξ := by
    rw [← Geometry.ReggeActionCubicTaylorBound.linePotential_eq_smul K ξ a]
    exact Geometry.ReggeActionSecondVariation.hessianQuadratic_linePotential K H ξ a
  have hnorm_sq : ‖a‖ ^ (2 : ℕ) = a ^ (2 : ℕ) := by
    rw [Real.norm_eq_abs, sq_abs]
  unfold reggeActionSecondOrder
  rw [hFlat, hquad, hnorm_sq]
  field_simp [ha]
  ring

/-- Filter form of the exact quadratic normalization.  The conclusion is an
eventual equality to a constant, so no continuity or rate hypothesis is needed;
the only filter hypothesis is eventual nonzero spacing. -/
theorem reggeActionSecondOrder_spacing_scaled_div_norm_sq_tendsto_quadratic_of_flat_zero
    {α : Type*} {l : Filter α}
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (H : Fin K.nV → Fin K.nV → ℝ)
    (hFlat : reggeAction K hK (zeroPotential K) = 0)
    (spacing : α → ℝ)
    (ξ : VertexPotential K)
    (hSpacing_ne : ∀ᶠ t : α in l, spacing t ≠ 0) :
    Filter.Tendsto
      (fun t : α =>
        reggeActionSecondOrder K hK H (spacing t • ξ) /
          ‖spacing t‖ ^ (2 : ℕ))
      l (nhds ((1 / 2) * hessianQuadratic H ξ)) := by
  have hEq :
      (fun t : α =>
        reggeActionSecondOrder K hK H (spacing t • ξ) /
          ‖spacing t‖ ^ (2 : ℕ)) =ᶠ[l]
        (fun _t : α => (1 / 2) * hessianQuadratic H ξ) :=
    hSpacing_ne.mono (fun t ht =>
      reggeActionSecondOrder_spacing_scaled_div_norm_sq_eq_quadratic_of_flat_zero
        K hK H hFlat (spacing t) ht ξ)
  exact tendsto_const_nhds.congr' hEq.symm

/-- Canonical finite mesh-weighted second-order aggregate after exact quadratic
normalization.  This is the supplied pointwise normalization of session 32
instantiated by quadratic homogeneity and flat-action zero-normalization. -/
theorem canonicalPeriodicSecondOrder_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_quadratic_of_flat_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFlat :
      reggeAction
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (zeroPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) = 0)
    {n : ℕ}
    (spacing : α → ℝ)
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (weight : α → Fin n → ℝ)
    (limitWeight : Fin n → ℝ)
    (hWeight :
      ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i)))
    (hSpacing_ne : ∀ᶠ t : α in l, spacing t ≠ 0) :
    Filter.Tendsto
      (fun t : α =>
        ∑ i : Fin n,
          weight t i *
            (reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (spacing t • probe i) /
              ‖spacing t‖ ^ (2 : ℕ)))
      l
      (nhds
        (∑ i : Fin n,
          limitWeight i *
            ((1 / 2) *
              hessianQuadratic
                (canonicalReggeHessian
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                (probe i)))) :=
  canonicalPeriodicSecondOrder_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto
    Nx Ny Nz hx hy hz spacing probe weight limitWeight
    (fun i : Fin n =>
      (1 / 2) *
        hessianQuadratic
          (canonicalReggeHessian
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
          (probe i))
    hWeight
    (fun i =>
      reggeActionSecondOrder_spacing_scaled_div_norm_sq_tendsto_quadratic_of_flat_zero
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (canonicalReggeHessian
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
        hFlat spacing (probe i) hSpacing_ne)

/-- Dirichlet-energy form of the canonical finite mesh-weighted second-order
aggregate after exact quadratic normalization.  This rewrites the raw Hessian
limit using the already-proved canonical Regge Hessian / Dirichlet identity. -/
theorem canonicalPeriodicSecondOrder_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flat_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFlat :
      reggeAction
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (zeroPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) = 0)
    {n : ℕ}
    (spacing : α → ℝ)
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (weight : α → Fin n → ℝ)
    (limitWeight : Fin n → ℝ)
    (hWeight :
      ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i)))
    (hSpacing_ne : ∀ᶠ t : α in l, spacing t ≠ 0) :
    Filter.Tendsto
      (fun t : α =>
        ∑ i : Fin n,
          weight t i *
            (reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (spacing t • probe i) /
              ‖spacing t‖ ^ (2 : ℕ)))
      l
      (nhds
        (∑ i : Fin n,
          limitWeight i *
            ((1 / 2) *
              canonicalDirichletEnergy
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                (probe i)))) := by
  simpa [canonicalReggeHessian_quadratic_eq_dirichlet] using
    canonicalPeriodicSecondOrder_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_quadratic_of_flat_zero
      Nx Ny Nz hx hy hz hFlat spacing probe weight limitWeight hWeight hSpacing_ne

/-- Dirichlet-energy finite second-order aggregate from the sharper geometric
input: flat deficits vanish at the canonical periodic background. -/
theorem canonicalPeriodicSecondOrder_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flatDeficit
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hDeficit :
      FlatDeficitZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    {n : ℕ}
    (spacing : α → ℝ)
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (weight : α → Fin n → ℝ)
    (limitWeight : Fin n → ℝ)
    (hWeight :
      ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i)))
    (hSpacing_ne : ∀ᶠ t : α in l, spacing t ≠ 0) :
    Filter.Tendsto
      (fun t : α =>
        ∑ i : Fin n,
          weight t i *
            (reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (spacing t • probe i) /
              ‖spacing t‖ ^ (2 : ℕ)))
      l
      (nhds
        (∑ i : Fin n,
          limitWeight i *
            ((1 / 2) *
              canonicalDirichletEnergy
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                (probe i)))) :=
  canonicalPeriodicSecondOrder_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flat_zero
    Nx Ny Nz hx hy hz
    (canonicalPeriodicReggeAction_zeroPotential_eq_zero_of_flatDeficit
      Nx Ny Nz hx hy hz hDeficit)
    spacing probe weight limitWeight hWeight hSpacing_ne

/-- Dirichlet-energy finite second-order aggregate from the standard
flat-configuration package. -/
theorem canonicalPeriodicSecondOrder_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flatConfiguration
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hFlat :
      FlatConfiguration
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
    {n : ℕ}
    (spacing : α → ℝ)
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (weight : α → Fin n → ℝ)
    (limitWeight : Fin n → ℝ)
    (hWeight :
      ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i)))
    (hSpacing_ne : ∀ᶠ t : α in l, spacing t ≠ 0) :
    Filter.Tendsto
      (fun t : α =>
        ∑ i : Fin n,
          weight t i *
            (reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (spacing t • probe i) /
              ‖spacing t‖ ^ (2 : ℕ)))
      l
      (nhds
        (∑ i : Fin n,
          limitWeight i *
            ((1 / 2) *
              canonicalDirichletEnergy
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                (probe i)))) :=
  canonicalPeriodicSecondOrder_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flatDeficit
    Nx Ny Nz hx hy hz
    (FlatDeficitZeroTarget.of_flatConfiguration
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
      hFlat)
    spacing probe weight limitWeight hWeight hSpacing_ne

/-- Dirichlet-energy finite second-order aggregate from the canonical
two-input flat-configuration bundle. -/
theorem canonicalPeriodicSecondOrder_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flatConfigurationInputs
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (I : CanonicalPeriodicFlatConfigurationInputs Nx Ny Nz hx hy hz)
    {n : ℕ}
    (spacing : α → ℝ)
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (weight : α → Fin n → ℝ)
    (limitWeight : Fin n → ℝ)
    (hWeight :
      ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i)))
    (hSpacing_ne : ∀ᶠ t : α in l, spacing t ≠ 0) :
    Filter.Tendsto
      (fun t : α =>
        ∑ i : Fin n,
          weight t i *
            (reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (spacing t • probe i) /
              ‖spacing t‖ ^ (2 : ℕ)))
      l
      (nhds
        (∑ i : Fin n,
          limitWeight i *
            ((1 / 2) *
              canonicalDirichletEnergy
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                (probe i)))) :=
  canonicalPeriodicSecondOrder_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flatConfiguration
    Nx Ny Nz hx hy hz I.toFlatConfiguration
    spacing probe weight limitWeight hWeight hSpacing_ne

/-- Composition interface for the scaled full nonlinear Regge aggregate.  Once a
finite mesh-weighted second-order aggregate, scaled by `||spacing(t)||^2`, has a
supplied limit, the full nonlinear Regge aggregate has the same limit because
the scaled nonlinear residual vanishes. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_of_secondOrder
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ)
        (limit : ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeActionSecondOrder
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (canonicalReggeHessian
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l (nhds limit) →
                Filter.Tendsto
                  (fun t : α =>
                    ∑ i : Fin n,
                      weight t i *
                        (reggeAction
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (spacing t • probe i) /
                          ‖spacing t‖ ^ (2 : ℕ)))
                  l (nhds limit) := by
  rcases canonicalPeriodicNonlinearResidual_variable_weighted_finite_probe_spacing_scaled_to_secondOrder_div_spacing_norm_sq_tendsto_zero
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hScaledResidual⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n spacing probe weight limitWeight limit hWeight hSpacing hSpacing_ne hSecondOrder
  have hResidual :=
    hScaledResidual spacing probe weight limitWeight hWeight hSpacing hSpacing_ne
  have hCombined := hSecondOrder.add hResidual
  have hCombinedLimit :
      Filter.Tendsto
        (fun t : α =>
          (∑ i : Fin n,
            weight t i *
              (reggeActionSecondOrder
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                (canonicalReggeHessian
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                (spacing t • probe i) /
                ‖spacing t‖ ^ (2 : ℕ))) +
            ∑ i : Fin n,
              weight t i *
                ((reggeAction
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (spacing t • probe i) -
                  reggeActionSecondOrder
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (canonicalReggeHessian
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                    (spacing t • probe i)) /
                  ‖spacing t‖ ^ (2 : ℕ)))
        l (nhds limit) := by
    simpa using hCombined
  convert hCombinedLimit using 1
  funext t
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Full nonlinear Regge finite aggregate convergence from pointwise scaled
second-order limits.  This composes the quadratic finite Riemann-sum interface
with the scaled nonlinear residual bridge; the only continuum-normalization
input is the explicit pointwise limit of each scaled second-order probe. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_of_pointwise_secondOrder
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ)
        (secondOrderLimit : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              (∀ i : Fin n,
                Filter.Tendsto
                  (fun t : α =>
                    reggeActionSecondOrder
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                      (canonicalReggeHessian
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                      (spacing t • probe i) /
                      ‖spacing t‖ ^ (2 : ℕ))
                  l (nhds (secondOrderLimit i))) →
                Filter.Tendsto
                  (fun t : α =>
                    ∑ i : Fin n,
                      weight t i *
                        (reggeAction
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (spacing t • probe i) /
                          ‖spacing t‖ ^ (2 : ℕ)))
                  l (nhds (∑ i : Fin n, limitWeight i * secondOrderLimit i)) := by
  rcases canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_of_secondOrder
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hTransfer⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n spacing probe weight limitWeight secondOrderLimit hWeight hSpacing hSpacing_ne hSecondOrder
  have hSecondOrderAggregate :
      Filter.Tendsto
        (fun t : α =>
          ∑ i : Fin n,
            weight t i *
              (reggeActionSecondOrder
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                (canonicalReggeHessian
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                (spacing t • probe i) /
                ‖spacing t‖ ^ (2 : ℕ)))
        l (nhds (∑ i : Fin n, limitWeight i * secondOrderLimit i)) :=
    canonicalPeriodicSecondOrder_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto
      Nx Ny Nz hx hy hz spacing probe weight limitWeight secondOrderLimit hWeight hSecondOrder
  exact
    hTransfer spacing probe weight limitWeight
      (∑ i : Fin n, limitWeight i * secondOrderLimit i)
      hWeight hSpacing hSpacing_ne hSecondOrderAggregate

/-- Full nonlinear Regge finite aggregate after exact quadratic normalization.
This is the first closed nonzero scaled finite limit: under flat-action
zero-normalization, the finite full-Regge aggregate has the same scaled limit as
the canonical quadratic form.  This remains finite and local; it does not yet
identify the quadratic form with the global EH integrand or pass to an
integral. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_quadratic_of_flat_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hFlat :
      reggeAction
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (zeroPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) = 0) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        hessianQuadratic
                          (canonicalReggeHessian
                            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                          (probe i)))) := by
  rcases canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_of_pointwise_secondOrder
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hFull⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n spacing probe weight limitWeight hWeight hSpacing hSpacing_ne
  exact
    hFull spacing probe weight limitWeight
      (fun i : Fin n =>
        (1 / 2) *
          hessianQuadratic
            (canonicalReggeHessian
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
            (probe i))
      hWeight hSpacing hSpacing_ne
      (fun i =>
        reggeActionSecondOrder_spacing_scaled_div_norm_sq_tendsto_quadratic_of_flat_zero
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
          (canonicalReggeHessian
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
          hFlat spacing (probe i) hSpacing_ne)

/-- Dirichlet-energy form of the full nonlinear Regge finite aggregate after
exact quadratic normalization.  The full-Regge scaled aggregate has the finite
Dirichlet limit under the same local residual and flat-action-zero hypotheses. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flat_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hFlat :
      reggeAction
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (zeroPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) = 0) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) := by
  rcases canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_quadratic_of_flat_zero
      Nx Ny Nz hx hy hz hLocal hFlat with
    ⟨r, C, hr, hC, hFull⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n spacing probe weight limitWeight hWeight hSpacing hSpacing_ne
  simpa [canonicalReggeHessian_quadratic_eq_dirichlet] using
    hFull spacing probe weight limitWeight hWeight hSpacing hSpacing_ne

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
sharper geometric input: flat deficits vanish at the canonical periodic
background. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flatDeficit
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hDeficit :
      FlatDeficitZeroTarget
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flat_zero
    Nx Ny Nz hx hy hz hLocal
    (canonicalPeriodicReggeAction_zeroPotential_eq_zero_of_flatDeficit
      Nx Ny Nz hx hy hz hDeficit)

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
standard flat-configuration package. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flatConfiguration
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hFlat :
      FlatConfiguration
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flatDeficit
    Nx Ny Nz hx hy hz hLocal
    (FlatDeficitZeroTarget.of_flatConfiguration
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
      hFlat)

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
canonical two-input flat-configuration bundle. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flatConfigurationInputs
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (I : CanonicalPeriodicFlatConfigurationInputs Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flatConfiguration
    Nx Ny Nz hx hy hz hLocal I.toFlatConfiguration

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from one
realized Freudenthal tetrahedron plus the remaining global zero-deficit input. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_realizedFreudenthalTet_zeroDeficit
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (T : Geometry.AffineIndepInterior.RealizedNonDegenerateTet)
    (hT : T.tet = Geometry.FreudenthalCubeTriangulation.freudenthalTet)
    (hZero :
      GlobalZeroDeficitAtFlat
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_flatConfigurationInputs
    Nx Ny Nz hx hy hz hLocal
    (canonicalPeriodicFlatConfigurationInputs_of_realizedFreudenthalTet_zeroDeficit
      Nx Ny Nz hx hy hz T hT hZero)

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from a
concrete Euclidean realization of the one-cube Freudenthal tetrahedron plus the
remaining global zero-deficit input. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_realizedTet_sqEdge_zeroDeficit
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (R : Geometry.TetrahedronRealization.RealizedTet)
    (hSq :
      Geometry.TetrahedronRealization.sqEdgeOfPoints R =
        Geometry.FreudenthalCubeTriangulation.freudenthalTetSqEdges)
    (hZero :
      GlobalZeroDeficitAtFlat
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_realizedFreudenthalTet_zeroDeficit
    Nx Ny Nz hx hy hz hLocal
    (realizedFreudenthalTet_of_sqEdgeOfPoints R hSq)
    rfl
    hZero

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
explicit Freudenthal coordinate realization, assuming affine independence of
those four points and the remaining global zero-deficit input. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealizationAffine_zeroDeficit
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hAffine : AffineIndependent ℝ freudenthalRealizationPoints)
    (hZero :
      GlobalZeroDeficitAtFlat
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_realizedTet_sqEdge_zeroDeficit
    Nx Ny Nz hx hy hz hLocal
    (freudenthalRealizedTet_of_affineIndependent hAffine)
    (freudenthalRealizedTet_of_affineIndependent_sqEdgeOfPoints hAffine)
    hZero

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
explicit Freudenthal coordinate realization.  The local chart side is now
fully discharged; the remaining geometric input is global zero deficit. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_zeroDeficit
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hZero :
      GlobalZeroDeficitAtFlat
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealizationAffine_zeroDeficit
    Nx Ny Nz hx hy hz hLocal
    freudenthalRealizationPoints_affineIndependent
    hZero

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
explicit Freudenthal coordinate realization, with both the local realized-chart
input and canonical global zero-deficit discharged.  This is the strongest
current finite scaled Track 1.B theorem before the remaining EH-integrand and
finite-to-integral layers. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_zeroDeficit
    Nx Ny Nz hx hy hz hLocal
    (canonicalPeriodicGlobalZeroDeficitAtFlat Nx Ny Nz hx hy hz)

/-- A finite physical/EH limit action on vertex-potential probes for the
canonical periodic Freudenthal torus.  This is the finite-probe target that the
later integral theorem will replace by an actual manifold integral. -/
abbrev CanonicalPeriodicFinitePhysicalLimitAction
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :=
  VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K → ℝ

/-- The finite physical/EH limit action agrees with the currently proved
canonical finite Dirichlet limit.  Instantiating this target with the true EH
integrand approximation is the next Track 1.B mathematical task. -/
def CanonicalPeriodicFiniteDirichletPhysicalLimitTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (A : CanonicalPeriodicFinitePhysicalLimitAction Nx Ny Nz hx hy hz) : Prop :=
  ∀ ξ : VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
    A ξ =
      (1 / 2) *
        canonicalDirichletEnergy
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
          ξ

/-- Normalized full nonlinear Regge finite aggregates converge to any supplied
finite physical/EH limit action that has been identified with the canonical
finite Dirichlet limit.  This separates the already closed Regge-to-Dirichlet
finite theorem from the still-open EH-integrand identification. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_physicalLimit_of_finiteDirichletTarget
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (A : CanonicalPeriodicFinitePhysicalLimitAction Nx Ny Nz hx hy hz)
    (hA : CanonicalPeriodicFiniteDirichletPhysicalLimitTarget Nx Ny Nz hx hy hz A) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds (∑ i : Fin n, limitWeight i * A (probe i))) := by
  rcases
    canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hFull⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n spacing probe weight limitWeight hWeight hSpacing hSpacing_ne
  have hTarget :
      (∑ i : Fin n,
        limitWeight i *
          ((1 / 2) *
            canonicalDirichletEnergy
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (probe i))) =
        ∑ i : Fin n, limitWeight i * A (probe i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hA (probe i)]
  rw [← hTarget]
  exact hFull spacing probe weight limitWeight hWeight hSpacing hSpacing_ne

/-- Residual form of the finite physical/EH limit interface: once the supplied
finite physical limit action is identified with the canonical finite Dirichlet
limit, the normalized full-Regge aggregate minus the finite physical aggregate
tends to zero. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_physicalLimit_residual_tendsto_zero_of_finiteDirichletTarget
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (A : CanonicalPeriodicFinitePhysicalLimitAction Nx Ny Nz hx hy hz)
    (hA : CanonicalPeriodicFiniteDirichletPhysicalLimitTarget Nx Ny Nz hx hy hz A) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  (∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ))) -
                    ∑ i : Fin n, limitWeight i * A (probe i))
                l (nhds 0) := by
  rcases
    canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_physicalLimit_of_finiteDirichletTarget
      Nx Ny Nz hx hy hz hLocal A hA with
    ⟨r, C, hr, hC, hFull⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n spacing probe weight limitWeight hWeight hSpacing hSpacing_ne
  let target : ℝ := ∑ i : Fin n, limitWeight i * A (probe i)
  have hConst : Filter.Tendsto (fun _t : α => target) l (nhds target) :=
    tendsto_const_nhds
  simpa [target] using
    (hFull spacing probe weight limitWeight hWeight hSpacing hSpacing_ne).sub hConst

/-- The canonical finite EH/Dirichlet limit action currently available at the
periodic Freudenthal finite-probe level.  It is the already proved finite
Dirichlet integrand approximation; the remaining Track 1.B work is to lift
this finite action to a genuine manifold integral. -/
def CanonicalPeriodicFiniteEHDirichletLimitAction
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicFinitePhysicalLimitAction Nx Ny Nz hx hy hz :=
  fun ξ =>
    (1 / 2) *
      canonicalDirichletEnergy
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        ξ

/-- The canonical finite EH/Dirichlet action instantiates the finite physical
limit interface by definition. -/
theorem canonicalPeriodicFiniteEHDirichletLimitTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicFiniteDirichletPhysicalLimitTarget Nx Ny Nz hx hy hz
      (CanonicalPeriodicFiniteEHDirichletLimitAction Nx Ny Nz hx hy hz) := by
  intro ξ
  rfl

/-- Normalized full nonlinear Regge finite aggregates converge to the canonical
finite EH/Dirichlet action.  This is still a finite-probe theorem, not the
full finite-to-integral or manifold Einstein-Hilbert convergence theorem. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_finiteEHDirichletLimit
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      CanonicalPeriodicFiniteEHDirichletLimitAction Nx Ny Nz hx hy hz
                        (probe i))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_physicalLimit_of_finiteDirichletTarget
    Nx Ny Nz hx hy hz hLocal
    (CanonicalPeriodicFiniteEHDirichletLimitAction Nx Ny Nz hx hy hz)
    (canonicalPeriodicFiniteEHDirichletLimitTarget Nx Ny Nz hx hy hz)

/-- Residual form against the canonical finite EH/Dirichlet action. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_finiteEHDirichletLimit_residual_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  (∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ))) -
                    ∑ i : Fin n,
                      limitWeight i *
                        CanonicalPeriodicFiniteEHDirichletLimitAction Nx Ny Nz hx hy hz
                          (probe i))
                l (nhds 0) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_physicalLimit_residual_tendsto_zero_of_finiteDirichletTarget
    Nx Ny Nz hx hy hz hLocal
    (CanonicalPeriodicFiniteEHDirichletLimitAction Nx Ny Nz hx hy hz)
    (canonicalPeriodicFiniteEHDirichletLimitTarget Nx Ny Nz hx hy hz)

/-- A supplied continuum Einstein-Hilbert integral value for the canonical
periodic Freudenthal finite-to-integral interface.  It is intentionally just a
real number here: the analytic work lives in the Riemann-sum hypothesis that
identifies finite EH/Dirichlet aggregates with this value. -/
abbrev CanonicalPeriodicContinuumEHIntegral := ℝ

/-- The finite EH/Dirichlet aggregate associated to a fixed finite probe family
and a weight vector.  This is the object whose refinement-indexed versions are
expected to converge to the continuum EH integral. -/
def CanonicalPeriodicFiniteEHDirichletAggregate
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    {n : ℕ}
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (weight : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    weight i *
      CanonicalPeriodicFiniteEHDirichletLimitAction Nx Ny Nz hx hy hz
        (probe i)

/-- If the finite mesh weights converge componentwise, the corresponding finite
EH/Dirichlet aggregates converge to the limiting weighted aggregate. -/
theorem canonicalPeriodicFiniteEHDirichletAggregate_tendsto_of_weights
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    {n : ℕ}
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (weight : α → Fin n → ℝ)
    (limitWeight : Fin n → ℝ)
    (hWeight : ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) :
    Filter.Tendsto
      (fun t : α =>
        CanonicalPeriodicFiniteEHDirichletAggregate Nx Ny Nz hx hy hz probe (weight t))
      l
      (nhds
        (CanonicalPeriodicFiniteEHDirichletAggregate Nx Ny Nz hx hy hz probe limitWeight)) := by
  classical
  unfold CanonicalPeriodicFiniteEHDirichletAggregate
  simpa using
    (tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (f := fun i (t : α) =>
        weight t i *
          CanonicalPeriodicFiniteEHDirichletLimitAction Nx Ny Nz hx hy hz (probe i))
      (a := fun i =>
        limitWeight i *
          CanonicalPeriodicFiniteEHDirichletLimitAction Nx Ny Nz hx hy hz (probe i))
      (by
        intro i _hi
        exact (hWeight i).mul tendsto_const_nhds))

/-- Residual form against the variable finite EH/Dirichlet aggregate.  The
session-60 theorem compared full Regge to the limiting finite aggregate; this
version subtracts the mesh-weighted finite EH aggregate at the same refinement
index. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_finiteEHDirichletVariableAggregate_residual_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  (∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ))) -
                    CanonicalPeriodicFiniteEHDirichletAggregate
                      Nx Ny Nz hx hy hz probe (weight t))
                l (nhds 0) := by
  rcases
    canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_finiteEHDirichletLimit
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hFull⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n spacing probe weight limitWeight hWeight hSpacing hSpacing_ne
  have hFinite :
      Filter.Tendsto
        (fun t : α =>
          CanonicalPeriodicFiniteEHDirichletAggregate Nx Ny Nz hx hy hz probe (weight t))
        l
        (nhds
          (CanonicalPeriodicFiniteEHDirichletAggregate Nx Ny Nz hx hy hz probe limitWeight)) :=
    canonicalPeriodicFiniteEHDirichletAggregate_tendsto_of_weights
      Nx Ny Nz hx hy hz probe weight limitWeight hWeight
  have hFull' :=
    hFull spacing probe weight limitWeight hWeight hSpacing hSpacing_ne
  simpa [CanonicalPeriodicFiniteEHDirichletAggregate] using hFull'.sub hFinite

/-- Riemann-sum target for the finite-to-integral bridge: the mesh-weighted
finite EH/Dirichlet aggregate converges to the supplied continuum EH integral.
This is the explicit analytic hypothesis needed before claiming a manifold
integral. -/
def CanonicalPeriodicFiniteEHDirichletToContinuumIntegralTarget
    {α : Type*} (l : Filter α)
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    {n : ℕ}
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (weight : α → Fin n → ℝ)
    (continuumIntegral : CanonicalPeriodicContinuumEHIntegral) : Prop :=
  Filter.Tendsto
    (fun t : α =>
      CanonicalPeriodicFiniteEHDirichletAggregate Nx Ny Nz hx hy hz probe (weight t))
    l
    (nhds continuumIntegral)

/-- Stronger finite-integral identification at the limiting finite aggregate:
after the mesh weights converge, this equality is enough to supply the
finite-to-integral target above. -/
def CanonicalPeriodicFiniteEHDirichletLimitWeightIntegralTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    {n : ℕ}
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (limitWeight : Fin n → ℝ)
    (continuumIntegral : CanonicalPeriodicContinuumEHIntegral) : Prop :=
  CanonicalPeriodicFiniteEHDirichletAggregate
    Nx Ny Nz hx hy hz probe limitWeight = continuumIntegral

/-- Componentwise mesh-weight convergence plus identification of the limiting
finite EH/Dirichlet aggregate with the continuum integral supplies the
Riemann-sum target used by the session-61 bridge. -/
theorem canonicalPeriodicFiniteEHDirichletToContinuumIntegralTarget_of_limitWeightIntegralTarget
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    {n : ℕ}
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (weight : α → Fin n → ℝ)
    (limitWeight : Fin n → ℝ)
    (continuumIntegral : CanonicalPeriodicContinuumEHIntegral)
    (hWeight : ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i)))
    (hLimit :
      CanonicalPeriodicFiniteEHDirichletLimitWeightIntegralTarget
        Nx Ny Nz hx hy hz probe limitWeight continuumIntegral) :
    CanonicalPeriodicFiniteEHDirichletToContinuumIntegralTarget
      l Nx Ny Nz hx hy hz probe weight continuumIntegral := by
  have hAgg :=
    canonicalPeriodicFiniteEHDirichletAggregate_tendsto_of_weights
      Nx Ny Nz hx hy hz probe weight limitWeight hWeight
  have hEq :
      CanonicalPeriodicFiniteEHDirichletAggregate
        Nx Ny Nz hx hy hz probe limitWeight = continuumIntegral := by
    simpa [CanonicalPeriodicFiniteEHDirichletLimitWeightIntegralTarget] using hLimit
  rw [hEq] at hAgg
  exact hAgg

/-- Refinement data for the finite-to-integral Track 1.B bridge.  The fields are
only the theorem-grade ingredients currently needed: a spacing schedule, finite
probe family, mesh weights with limiting weights, nonzero quadratic scaling, and
the Riemann-sum convergence to a supplied continuum EH integral. -/
structure CanonicalPeriodicFiniteEHDirichletIntegralRefinementData
    {α : Type*} (l : Filter α)
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) where
  n : ℕ
  spacing : α → ℝ
  probe :
    Fin n →
      VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
  weight : α → Fin n → ℝ
  limitWeight : Fin n → ℝ
  continuumIntegral : CanonicalPeriodicContinuumEHIntegral
  weight_tendsto :
    ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))
  spacing_tendsto_zero : Filter.Tendsto spacing l (nhds 0)
  spacing_eventually_ne_zero : ∀ᶠ t : α in l, spacing t ≠ 0
  finite_to_integral :
    CanonicalPeriodicFiniteEHDirichletToContinuumIntegralTarget
      l Nx Ny Nz hx hy hz probe weight continuumIntegral

/-- A refinement package whose integral identification is stated at the limiting
finite EH/Dirichlet aggregate.  This is often the more usable theorem shape:
prove the mesh weights converge, then prove the limiting finite aggregate is
the desired continuum integral. -/
structure CanonicalPeriodicFiniteEHDirichletLimitWeightRefinementData
    {α : Type*} (l : Filter α)
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) where
  n : ℕ
  spacing : α → ℝ
  probe :
    Fin n →
      VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
  weight : α → Fin n → ℝ
  limitWeight : Fin n → ℝ
  continuumIntegral : CanonicalPeriodicContinuumEHIntegral
  weight_tendsto :
    ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))
  spacing_tendsto_zero : Filter.Tendsto spacing l (nhds 0)
  spacing_eventually_ne_zero : ∀ᶠ t : α in l, spacing t ≠ 0
  limit_weight_integral :
    CanonicalPeriodicFiniteEHDirichletLimitWeightIntegralTarget
      Nx Ny Nz hx hy hz probe limitWeight continuumIntegral

/-- Convert the limiting-aggregate package into the explicit Riemann-sum package
by applying finite EH aggregate convergence of the mesh weights. -/
def CanonicalPeriodicFiniteEHDirichletLimitWeightRefinementData.toIntegralRefinementData
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFiniteEHDirichletLimitWeightRefinementData l Nx Ny Nz hx hy hz) :
    CanonicalPeriodicFiniteEHDirichletIntegralRefinementData l Nx Ny Nz hx hy hz where
  n := D.n
  spacing := D.spacing
  probe := D.probe
  weight := D.weight
  limitWeight := D.limitWeight
  continuumIntegral := D.continuumIntegral
  weight_tendsto := D.weight_tendsto
  spacing_tendsto_zero := D.spacing_tendsto_zero
  spacing_eventually_ne_zero := D.spacing_eventually_ne_zero
  finite_to_integral :=
    canonicalPeriodicFiniteEHDirichletToContinuumIntegralTarget_of_limitWeightIntegralTarget
      Nx Ny Nz hx hy hz D.probe D.weight D.limitWeight D.continuumIntegral
      D.weight_tendsto D.limit_weight_integral

/-- Finite-to-integral bridge theorem for the current Track 1.B finite EH layer.
Given a refinement data package whose finite EH/Dirichlet aggregates converge
to a supplied continuum integral, the normalized full nonlinear Regge finite
aggregates converge to the same continuum integral.  This does not assert the
final manifold EH theorem; it composes the closed finite Regge theorem with the
explicit Riemann-sum hypothesis. -/
theorem CanonicalPeriodicFiniteEHDirichletIntegralRefinementData.fullRegge_tendsto_continuumIntegral
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (D : CanonicalPeriodicFiniteEHDirichletIntegralRefinementData l Nx Ny Nz hx hy hz) :
    Filter.Tendsto
      (fun t : α =>
        ∑ i : Fin D.n,
          D.weight t i *
            (reggeAction
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (D.spacing t • D.probe i) /
              ‖D.spacing t‖ ^ (2 : ℕ)))
      l
      (nhds D.continuumIntegral) := by
  rcases
    canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_finiteEHDirichletVariableAggregate_residual_tendsto_zero
      Nx Ny Nz hx hy hz hLocal with
    ⟨_r, _C, _hr, _hC, hResidual⟩
  have hRes :=
    hResidual D.spacing D.probe D.weight D.limitWeight
      D.weight_tendsto D.spacing_tendsto_zero D.spacing_eventually_ne_zero
  have hInt : Filter.Tendsto
      (fun t : α =>
        CanonicalPeriodicFiniteEHDirichletAggregate
          Nx Ny Nz hx hy hz D.probe (D.weight t))
      l
      (nhds D.continuumIntegral) :=
    D.finite_to_integral
  simpa [CanonicalPeriodicFiniteEHDirichletAggregate, sub_add_cancel] using hRes.add hInt

/-- Finite-to-integral bridge from the limiting-aggregate data package.  This is
the same full-Regge conclusion as the explicit Riemann-sum package, but its
analytic input is split into mesh-weight convergence plus a limiting finite
aggregate equality. -/
theorem CanonicalPeriodicFiniteEHDirichletLimitWeightRefinementData.fullRegge_tendsto_continuumIntegral
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (D : CanonicalPeriodicFiniteEHDirichletLimitWeightRefinementData l Nx Ny Nz hx hy hz) :
    Filter.Tendsto
      (fun t : α =>
        ∑ i : Fin D.n,
          D.weight t i *
            (reggeAction
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (D.spacing t • D.probe i) /
              ‖D.spacing t‖ ^ (2 : ℕ)))
      l
      (nhds D.continuumIntegral) :=
  CanonicalPeriodicFiniteEHDirichletIntegralRefinementData.fullRegge_tendsto_continuumIntegral
    Nx Ny Nz hx hy hz hLocal
    (CanonicalPeriodicFiniteEHDirichletLimitWeightRefinementData.toIntegralRefinementData
      Nx Ny Nz hx hy hz D)

/-- A named finite EH/Dirichlet quadrature rule on the canonical periodic
Freudenthal torus: a finite probe family plus fixed quadrature weights.  This is
still finite data, not a manifold integral. -/
structure CanonicalPeriodicFiniteEHDirichletQuadratureRule
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) where
  n : ℕ
  probe :
    Fin n →
      VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
  weight : Fin n → ℝ

/-- The finite continuum-integral proxy represented by a quadrature rule.  It is
definitionally the finite EH/Dirichlet aggregate for the rule's probes and
weights. -/
def CanonicalPeriodicFiniteEHDirichletQuadratureRule.continuumIntegral
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (Q : CanonicalPeriodicFiniteEHDirichletQuadratureRule Nx Ny Nz hx hy hz) :
    CanonicalPeriodicContinuumEHIntegral :=
  CanonicalPeriodicFiniteEHDirichletAggregate
    Nx Ny Nz hx hy hz Q.probe Q.weight

/-- The named finite quadrature proxy supplies the limiting-aggregate integral
target by definition. -/
theorem CanonicalPeriodicFiniteEHDirichletQuadratureRule.limitWeightIntegralTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (Q : CanonicalPeriodicFiniteEHDirichletQuadratureRule Nx Ny Nz hx hy hz) :
    CanonicalPeriodicFiniteEHDirichletLimitWeightIntegralTarget
      Nx Ny Nz hx hy hz Q.probe Q.weight
      (Q.continuumIntegral Nx Ny Nz hx hy hz) := by
  rfl

/-- Refinement data toward a named finite EH/Dirichlet quadrature rule.  The
mesh-dependent weights converge to the rule's weights; the quadrature rule
itself supplies the finite integral proxy. -/
structure CanonicalPeriodicFiniteEHDirichletQuadratureRefinementData
    {α : Type*} (l : Filter α)
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) where
  rule : CanonicalPeriodicFiniteEHDirichletQuadratureRule Nx Ny Nz hx hy hz
  spacing : α → ℝ
  weight : α → Fin rule.n → ℝ
  weight_tendsto :
    ∀ i : Fin rule.n, Filter.Tendsto (fun t : α => weight t i) l (nhds (rule.weight i))
  spacing_tendsto_zero : Filter.Tendsto spacing l (nhds 0)
  spacing_eventually_ne_zero : ∀ᶠ t : α in l, spacing t ≠ 0

/-- Convert a named quadrature refinement package into the limit-weight package
from session 62. -/
def CanonicalPeriodicFiniteEHDirichletQuadratureRefinementData.toLimitWeightRefinementData
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFiniteEHDirichletQuadratureRefinementData l Nx Ny Nz hx hy hz) :
    CanonicalPeriodicFiniteEHDirichletLimitWeightRefinementData l Nx Ny Nz hx hy hz where
  n := D.rule.n
  spacing := D.spacing
  probe := D.rule.probe
  weight := D.weight
  limitWeight := D.rule.weight
  continuumIntegral := D.rule.continuumIntegral Nx Ny Nz hx hy hz
  weight_tendsto := D.weight_tendsto
  spacing_tendsto_zero := D.spacing_tendsto_zero
  spacing_eventually_ne_zero := D.spacing_eventually_ne_zero
  limit_weight_integral :=
    D.rule.limitWeightIntegralTarget Nx Ny Nz hx hy hz

/-- Normalized full nonlinear Regge aggregates converge to the finite
EH/Dirichlet quadrature proxy when the mesh-dependent weights converge to the
rule's weights.  This is a named finite/quadrature theorem, not the final
manifold Einstein-Hilbert limit. -/
theorem CanonicalPeriodicFiniteEHDirichletQuadratureRefinementData.fullRegge_tendsto_quadratureIntegral
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (D : CanonicalPeriodicFiniteEHDirichletQuadratureRefinementData l Nx Ny Nz hx hy hz) :
    Filter.Tendsto
      (fun t : α =>
        ∑ i : Fin D.rule.n,
          D.weight t i *
            (reggeAction
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (D.spacing t • D.rule.probe i) /
              ‖D.spacing t‖ ^ (2 : ℕ)))
      l
      (nhds (D.rule.continuumIntegral Nx Ny Nz hx hy hz)) :=
  CanonicalPeriodicFiniteEHDirichletLimitWeightRefinementData.fullRegge_tendsto_continuumIntegral
    Nx Ny Nz hx hy hz hLocal
    (CanonicalPeriodicFiniteEHDirichletQuadratureRefinementData.toLimitWeightRefinementData
      Nx Ny Nz hx hy hz D)

/-- Geometric quadrature over the actual typed periodic Freudenthal tetrahedra.
The weights are carried on `PeriodicTet` itself, then encoded through
`tetFinEquiv` only when feeding the finite quadrature theorem. -/
structure CanonicalPeriodicTetGeometricQuadratureRule
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) where
  tetProbe :
    PeriodicTet Nx Ny Nz →
      VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
  tetVolumeWeight : PeriodicTet Nx Ny Nz → ℝ

/-- Encode a typed periodic-tetrahedron quadrature rule as the finite
`Fin n` quadrature rule used by the current Track 1.B interface. -/
def CanonicalPeriodicTetGeometricQuadratureRule.toFiniteQuadratureRule
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (Q : CanonicalPeriodicTetGeometricQuadratureRule Nx Ny Nz hx hy hz) :
    CanonicalPeriodicFiniteEHDirichletQuadratureRule Nx Ny Nz hx hy hz where
  n := Fintype.card (PeriodicTet Nx Ny Nz)
  probe := fun τ => Q.tetProbe (tetFinEquiv Nx Ny Nz τ)
  weight := fun τ => Q.tetVolumeWeight (tetFinEquiv Nx Ny Nz τ)

/-- The finite EH/Dirichlet integral proxy for a typed periodic-tetrahedron
quadrature rule. -/
def CanonicalPeriodicTetGeometricQuadratureRule.continuumIntegral
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (Q : CanonicalPeriodicTetGeometricQuadratureRule Nx Ny Nz hx hy hz) :
    CanonicalPeriodicContinuumEHIntegral :=
  (Q.toFiniteQuadratureRule Nx Ny Nz hx hy hz).continuumIntegral Nx Ny Nz hx hy hz

/-- Typed periodic-tetrahedron quadrature supplies the finite limit-weight
integral target after applying `tetFinEquiv`. -/
theorem CanonicalPeriodicTetGeometricQuadratureRule.limitWeightIntegralTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (Q : CanonicalPeriodicTetGeometricQuadratureRule Nx Ny Nz hx hy hz) :
    CanonicalPeriodicFiniteEHDirichletLimitWeightIntegralTarget
      Nx Ny Nz hx hy hz
      (fun τ => Q.tetProbe (tetFinEquiv Nx Ny Nz τ))
      (fun τ => Q.tetVolumeWeight (tetFinEquiv Nx Ny Nz τ))
      (Q.continuumIntegral Nx Ny Nz hx hy hz) := by
  rfl

/-- Refinement data toward a typed periodic-tetrahedron quadrature rule.  The
mesh-dependent weights are expressed on `PeriodicTet`, not an anonymous finite
index. -/
structure CanonicalPeriodicTetGeometricQuadratureRefinementData
    {α : Type*} (l : Filter α)
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) where
  rule : CanonicalPeriodicTetGeometricQuadratureRule Nx Ny Nz hx hy hz
  spacing : α → ℝ
  tetWeight : α → PeriodicTet Nx Ny Nz → ℝ
  tetWeight_tendsto :
    ∀ τ : PeriodicTet Nx Ny Nz,
      Filter.Tendsto (fun t : α => tetWeight t τ) l (nhds (rule.tetVolumeWeight τ))
  spacing_tendsto_zero : Filter.Tendsto spacing l (nhds 0)
  spacing_eventually_ne_zero : ∀ᶠ t : α in l, spacing t ≠ 0

/-- Encode typed tetrahedron refinement data as the finite quadrature refinement
data used by the current theorem. -/
def CanonicalPeriodicTetGeometricQuadratureRefinementData.toFiniteQuadratureRefinementData
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicTetGeometricQuadratureRefinementData l Nx Ny Nz hx hy hz) :
    CanonicalPeriodicFiniteEHDirichletQuadratureRefinementData l Nx Ny Nz hx hy hz where
  rule := D.rule.toFiniteQuadratureRule Nx Ny Nz hx hy hz
  spacing := D.spacing
  weight := fun t τ => D.tetWeight t (tetFinEquiv Nx Ny Nz τ)
  weight_tendsto := by
    intro τ
    exact D.tetWeight_tendsto (tetFinEquiv Nx Ny Nz τ)
  spacing_tendsto_zero := D.spacing_tendsto_zero
  spacing_eventually_ne_zero := D.spacing_eventually_ne_zero

/-- Full-Regge convergence to the typed periodic-tetrahedron finite quadrature
proxy.  This gives the abstract quadrature theorem actual periodic
Freudenthal-tetrahedron indices, while still remaining finite. -/
theorem CanonicalPeriodicTetGeometricQuadratureRefinementData.fullRegge_tendsto_geometricQuadratureIntegral
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (D : CanonicalPeriodicTetGeometricQuadratureRefinementData l Nx Ny Nz hx hy hz) :
    Filter.Tendsto
      (fun t : α =>
        ∑ τ : Fin (Fintype.card (PeriodicTet Nx Ny Nz)),
          D.tetWeight t (tetFinEquiv Nx Ny Nz τ) *
            (reggeAction
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (D.spacing t • D.rule.tetProbe (tetFinEquiv Nx Ny Nz τ)) /
              ‖D.spacing t‖ ^ (2 : ℕ)))
      l
      (nhds (D.rule.continuumIntegral Nx Ny Nz hx hy hz)) :=
  CanonicalPeriodicFiniteEHDirichletQuadratureRefinementData.fullRegge_tendsto_quadratureIntegral
    Nx Ny Nz hx hy hz hLocal
    (CanonicalPeriodicTetGeometricQuadratureRefinementData.toFiniteQuadratureRefinementData
      Nx Ny Nz hx hy hz D)

/-- Canonical Freudenthal six-tet volume weight: each tetrahedron in a cubic
cell receives one sixth of the cell-volume weight. -/
def canonicalPeriodicFreudenthalTetVolumeWeight
    (Nx Ny Nz : ℕ) (_cellVolume : ℝ)
    (_τ : PeriodicTet Nx Ny Nz) : ℝ :=
  _cellVolume / 6

theorem canonicalPeriodicFreudenthalTetVolumeWeight_nonneg
    (Nx Ny Nz : ℕ) (cellVolume : ℝ)
    (hCell : 0 ≤ cellVolume)
    (τ : PeriodicTet Nx Ny Nz) :
    0 ≤ canonicalPeriodicFreudenthalTetVolumeWeight Nx Ny Nz cellVolume τ := by
  unfold canonicalPeriodicFreudenthalTetVolumeWeight
  exact div_nonneg hCell (by norm_num : (0 : ℝ) ≤ 6)

/-- If the cell-volume weights converge, then the induced six-tet
Freudenthal tetrahedron weights converge. -/
theorem canonicalPeriodicFreudenthalTetVolumeWeight_tendsto
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ)
    (cellVolume : α → ℝ)
    (limitCellVolume : ℝ)
    (hCellVolume :
      Filter.Tendsto cellVolume l (nhds limitCellVolume)) :
    ∀ τ : PeriodicTet Nx Ny Nz,
      Filter.Tendsto
        (fun t : α =>
          canonicalPeriodicFreudenthalTetVolumeWeight Nx Ny Nz (cellVolume t) τ)
        l
        (nhds
          (canonicalPeriodicFreudenthalTetVolumeWeight
            Nx Ny Nz limitCellVolume τ)) := by
  intro τ
  unfold canonicalPeriodicFreudenthalTetVolumeWeight
  simpa [div_eq_mul_inv] using hCellVolume.mul tendsto_const_nhds

/-- The canonical six-tet cell-volume quadrature rule over typed periodic
Freudenthal tetrahedra.  The only geometric weight formula in this finite layer
is the Freudenthal cell split `cellVolume / 6`; the probe assignment remains the
supplied field being quadrature-sampled. -/
def canonicalPeriodicTetSixTetVolumeQuadratureRule
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (cellVolume : ℝ)
    (tetProbe :
      PeriodicTet Nx Ny Nz →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    CanonicalPeriodicTetGeometricQuadratureRule Nx Ny Nz hx hy hz where
  tetProbe := tetProbe
  tetVolumeWeight :=
    canonicalPeriodicFreudenthalTetVolumeWeight Nx Ny Nz cellVolume

/-- Refinement data for the canonical six-tet volume quadrature rule.  The
mesh-dependent cell-volume weights converge to the limiting cell-volume weight;
tetrahedron weights are then fixed by the Freudenthal `1/6` split. -/
structure CanonicalPeriodicTetSixTetVolumeQuadratureRefinementData
    {α : Type*} (l : Filter α)
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) where
  limitCellVolume : ℝ
  cellVolume : α → ℝ
  cellVolume_tendsto :
    Filter.Tendsto cellVolume l (nhds limitCellVolume)
  tetProbe :
    PeriodicTet Nx Ny Nz →
      VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
  spacing : α → ℝ
  spacing_tendsto_zero : Filter.Tendsto spacing l (nhds 0)
  spacing_eventually_ne_zero : ∀ᶠ t : α in l, spacing t ≠ 0

/-- Convert canonical six-tet volume refinement data into the typed geometric
quadrature refinement package. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureRefinementData.toTetGeometricQuadratureRefinementData
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementData l Nx Ny Nz hx hy hz) :
    CanonicalPeriodicTetGeometricQuadratureRefinementData l Nx Ny Nz hx hy hz where
  rule :=
    canonicalPeriodicTetSixTetVolumeQuadratureRule
      Nx Ny Nz hx hy hz D.limitCellVolume D.tetProbe
  spacing := D.spacing
  tetWeight := fun t =>
    canonicalPeriodicFreudenthalTetVolumeWeight Nx Ny Nz (D.cellVolume t)
  tetWeight_tendsto :=
    canonicalPeriodicFreudenthalTetVolumeWeight_tendsto
      Nx Ny Nz D.cellVolume D.limitCellVolume D.cellVolume_tendsto
  spacing_tendsto_zero := D.spacing_tendsto_zero
  spacing_eventually_ne_zero := D.spacing_eventually_ne_zero

/-- Full-Regge convergence to the finite quadrature proxy with the canonical
Freudenthal `cellVolume / 6` tetrahedron weights.  This is the first
geometrically weighted version of the finite quadrature theorem; it is not yet
a varying-cardinality or manifold integral theorem. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureRefinementData.fullRegge_tendsto_sixTetVolumeQuadratureIntegral
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementData l Nx Ny Nz hx hy hz) :
    Filter.Tendsto
      (fun t : α =>
        ∑ τ : Fin (Fintype.card (PeriodicTet Nx Ny Nz)),
          canonicalPeriodicFreudenthalTetVolumeWeight
              Nx Ny Nz (D.cellVolume t) (tetFinEquiv Nx Ny Nz τ) *
            (reggeAction
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (D.spacing t • D.tetProbe (tetFinEquiv Nx Ny Nz τ)) /
              ‖D.spacing t‖ ^ (2 : ℕ)))
      l
      (nhds
        ((canonicalPeriodicTetSixTetVolumeQuadratureRule
          Nx Ny Nz hx hy hz D.limitCellVolume D.tetProbe).continuumIntegral
            Nx Ny Nz hx hy hz)) :=
  CanonicalPeriodicTetGeometricQuadratureRefinementData.fullRegge_tendsto_geometricQuadratureIntegral
    Nx Ny Nz hx hy hz hLocal
    (CanonicalPeriodicTetSixTetVolumeQuadratureRefinementData.toTetGeometricQuadratureRefinementData
      Nx Ny Nz hx hy hz D)

/-- One slice of a varying-cardinality periodic Freudenthal refinement family.
Each slice carries its own side lengths, nonzero witnesses, local nonlinear
correspondence, and finite six-tet quadrature data. -/
structure CanonicalPeriodicTetSixTetVolumeQuadratureSlice
    {α : Type*} (l : Filter α) where
  Nx : ℕ
  Ny : ℕ
  Nz : ℕ
  instNx : NeZero Nx
  instNy : NeZero Ny
  instNz : NeZero Nz
  hx : 2 < Nx
  hy : 2 < Ny
  hz : 2 < Nz
  hLocal :
    letI : NeZero Nx := instNx
    letI : NeZero Ny := instNy
    letI : NeZero Nz := instNz
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz
  data :
    letI : NeZero Nx := instNx
    letI : NeZero Ny := instNy
    letI : NeZero Nz := instNz
    CanonicalPeriodicTetSixTetVolumeQuadratureRefinementData
      l Nx Ny Nz hx hy hz

/-- The normalized full-Regge aggregate for a varying-cardinality slice. -/
noncomputable def CanonicalPeriodicTetSixTetVolumeQuadratureSlice.fullReggeAggregate
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : α → ℝ := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  exact
    fun t : α =>
      ∑ τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)),
        canonicalPeriodicFreudenthalTetVolumeWeight
            S.Nx S.Ny S.Nz (S.data.cellVolume t)
            (tetFinEquiv S.Nx S.Ny S.Nz τ) *
          (reggeAction
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
            (S.data.spacing t • S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)) /
            S.data.spacing t ^ (2 : ℕ))

/-- The finite six-tet quadrature proxy attached to a varying-cardinality
slice. -/
noncomputable def CanonicalPeriodicTetSixTetVolumeQuadratureSlice.quadratureIntegral
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : ℝ := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  exact
    ((canonicalPeriodicTetSixTetVolumeQuadratureRule
      S.Nx S.Ny S.Nz S.hx S.hy S.hz
      S.data.limitCellVolume S.data.tetProbe).continuumIntegral
        S.Nx S.Ny S.Nz S.hx S.hy S.hz)

/-- Every varying-cardinality slice feeds the finite six-tet volume quadrature
theorem.  This theorem is per-slice; it does not yet compare different
cardinalities in one limit. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSlice.fullRegge_tendsto_quadratureIntegral
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    Filter.Tendsto
      (S.fullReggeAggregate)
      l
      (nhds S.quadratureIntegral) := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  simpa [CanonicalPeriodicTetSixTetVolumeQuadratureSlice.fullReggeAggregate,
    CanonicalPeriodicTetSixTetVolumeQuadratureSlice.quadratureIntegral] using
    CanonicalPeriodicTetSixTetVolumeQuadratureRefinementData.fullRegge_tendsto_sixTetVolumeQuadratureIntegral
      S.Nx S.Ny S.Nz S.hx S.hy S.hz S.hLocal S.data

/-- A varying-cardinality family is a collection of finite six-tet quadrature
slices indexed by a refinement parameter type. -/
structure CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily
    {α : Type*} (l : Filter α) (ρ : Type*) where
  slice : ρ → CanonicalPeriodicTetSixTetVolumeQuadratureSlice l

/-- Each slice of a varying-cardinality family inherits the finite six-tet
full-Regge convergence theorem.  The next analytic step is to put a filter on
the `ρ`-index and compare these slice limits across cardinalities. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily.slice_fullRegge_tendsto_quadratureIntegral
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (r : ρ) :
    Filter.Tendsto
      ((F.slice r).fullReggeAggregate)
      l
      (nhds ((F.slice r).quadratureIntegral)) :=
  CanonicalPeriodicTetSixTetVolumeQuadratureSlice.fullRegge_tendsto_quadratureIntegral
    (F.slice r)

/-- Cross-cardinality finite-to-integral target for a varying-cardinality
six-tet quadrature family.  It compares the finite quadrature proxies attached
to each slice along a refinement-index filter. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ)
    (continuumIntegral : ℝ) : Prop :=
  Filter.Tendsto
    (fun r : ρ => (F.slice r).quadratureIntegral)
    refinementFilter
    (nhds continuumIntegral)

/-- Cross-cardinality data: every finite slice has the full-Regge-to-quadrature
theorem, and the finite quadrature proxies converge along the refinement-index
filter to a supplied continuum integral.  This is a staged interface, not a
single product-filter or uniform convergence theorem. -/
structure CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData
    {α ρ : Type*} (l : Filter α) where
  family : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ
  refinementFilter : Filter ρ
  continuumIntegral : ℝ
  quadrature_tendsto :
    CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
      family refinementFilter continuumIntegral

/-- The per-slice full-Regge convergence supplied by cross-cardinality data. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData.slice_fullRegge_tendsto_quadratureIntegral
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData l)
    (r : ρ) :
    Filter.Tendsto
      ((D.family.slice r).fullReggeAggregate)
      l
      (nhds ((D.family.slice r).quadratureIntegral)) :=
  D.family.slice_fullRegge_tendsto_quadratureIntegral r

/-- The cross-cardinality quadrature convergence supplied by the data package. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData.quadratureIntegral_tendsto_continuum
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData l) :
    Filter.Tendsto
      (fun r : ρ => (D.family.slice r).quadratureIntegral)
      D.refinementFilter
      (nhds D.continuumIntegral) :=
  D.quadrature_tendsto

/-- Staged cross-cardinality conclusion: finite full-Regge aggregates converge
to each slice's finite quadrature proxy, and those proxies converge along the
refinement-index filter to the supplied continuum integral.  A future theorem
must add uniformity or a product-filter argument before collapsing this staged
statement into one global limit. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData.staged_fullRegge_to_continuum
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData l) :
    (∀ r : ρ,
      Filter.Tendsto
        ((D.family.slice r).fullReggeAggregate)
        l
        (nhds ((D.family.slice r).quadratureIntegral))) ∧
      Filter.Tendsto
        (fun r : ρ => (D.family.slice r).quadratureIntegral)
        D.refinementFilter
        (nhds D.continuumIntegral) := by
  exact ⟨
    fun r => D.slice_fullRegge_tendsto_quadratureIntegral r,
    D.quadratureIntegral_tendsto_continuum⟩

/-- Product-indexed full-Regge aggregate for a varying-cardinality family.  The
first coordinate chooses the finite cardinality slice; the second coordinate is
the within-slice refinement parameter. -/
noncomputable def CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ) :
    ρ × α → ℝ :=
  fun p => ((F.slice p.1).fullReggeAggregate) p.2

/-- Product-indexed finite quadrature proxy for a varying-cardinality family. -/
noncomputable def CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ) :
    ρ × α → ℝ :=
  fun p => (F.slice p.1).quadratureIntegral

/-- Uniform two-scale residual target.  This is the extra hypothesis needed to
collapse the staged cross-cardinality statement into one product-filter limit:
the full-Regge-to-quadrature residual must vanish on the product filter, not
merely on each fixed slice. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) : Prop :=
  Filter.Tendsto
    (fun p : ρ × α =>
      CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate F p -
        CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral F p)
    (refinementFilter ×ˢ l)
    (nhds 0)

/-- A bounded-envelope criterion for the product uniform residual target.  It
is enough to bound the absolute full-Regge-to-quadrature residual by an envelope
that tends to zero on the product filter. -/
theorem canonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget_of_abs_bound
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ)
    (envelope : ρ × α → ℝ)
    (hEnvelope :
      Filter.Tendsto envelope (refinementFilter ×ˢ l : Filter (ρ × α)) (nhds 0))
    (hBound :
      ∀ᶠ p : ρ × α in (refinementFilter ×ˢ l),
        |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate F p -
          CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral F p| ≤
          envelope p) :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget
      F refinementFilter := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hAbs :
      Filter.Tendsto
        (fun p : ρ × α =>
          |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate F p -
            CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral F p|)
        (refinementFilter ×ˢ l)
        (nhds 0) := by
    exact squeeze_zero' (Filter.Eventually.of_forall (fun p => abs_nonneg _)) hBound hEnvelope
  simpa [
    CanonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget,
    Real.dist_eq,
    sub_zero] using hAbs

/-- Cross-slice envelope criterion for the product uniform residual target.  If
one envelope depending only on the within-slice refinement parameter controls
every slice along the product filter, then the residual is uniform in the
cardinality index. -/
theorem canonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget_of_snd_abs_bound
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ)
    (envelope : α → ℝ)
    (hEnvelope : Filter.Tendsto envelope l (nhds 0))
    (hBound :
      ∀ᶠ p : ρ × α in (refinementFilter ×ˢ l),
        |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate F p -
          CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral F p| ≤
          envelope p.2) :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget
      F refinementFilter :=
  canonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget_of_abs_bound
    F refinementFilter (fun p : ρ × α => envelope p.2)
    (hEnvelope.comp
      (Filter.tendsto_snd :
        Filter.Tendsto (Prod.snd : ρ × α → α)
          (refinementFilter ×ˢ l) l))
    hBound

/-- Global cross-slice envelope criterion.  A pointwise bound for all slice
indices and all within-slice refinement parameters gives the eventual product
bound required by the cross-slice envelope theorem. -/
theorem canonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget_of_forall_snd_abs_bound
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ)
    (envelope : α → ℝ)
    (hEnvelope : Filter.Tendsto envelope l (nhds 0))
    (hBound :
      ∀ (r : ρ) (t : α),
        |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate F (r, t) -
          CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral F (r, t)| ≤
          envelope t) :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget
      F refinementFilter :=
  canonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget_of_snd_abs_bound
    F refinementFilter envelope hEnvelope
    (Filter.Eventually.of_forall (fun p : ρ × α => hBound p.1 p.2))

/-- Product-filter bridge from uniform residual plus cross-cardinality
quadrature convergence to a single continuum limit for the full nonlinear
Regge aggregate. -/
theorem canonicalPeriodicTetSixTetVolumeQuadratureProduct_fullRegge_tendsto_continuum
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ)
    (continuumIntegral : ℝ)
    (hQuadrature :
      CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
        F refinementFilter continuumIntegral)
    (hResidual :
      CanonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget
        F refinementFilter) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate F)
      (refinementFilter ×ˢ l)
      (nhds continuumIntegral) := by
  have hResidual' :
      Filter.Tendsto
        (fun p : ρ × α =>
          CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate F p -
            CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral F p)
        (refinementFilter ×ˢ l)
        (nhds 0) := by
    simpa [CanonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget] using hResidual
  have hQuadrature' :
      Filter.Tendsto
        (CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral F)
        (refinementFilter ×ˢ l)
        (nhds continuumIntegral) := by
    have h :=
      hQuadrature.comp
        (Filter.tendsto_fst :
          Filter.Tendsto (Prod.fst : ρ × α → ρ)
            (refinementFilter ×ˢ l) refinementFilter)
    simpa [
      CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget,
      CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral,
      Function.comp] using h
  have hSum := hResidual'.add hQuadrature'
  simpa [
    CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate,
    CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral] using hSum

/-- Data package for the product-filter version of the six-tet volume
quadrature limit.  Unlike the staged cross-cardinality package, this includes
the uniform product residual required to obtain one global limit. -/
structure CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData
    {α ρ : Type*} (l : Filter α) where
  family : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ
  refinementFilter : Filter ρ
  continuumIntegral : ℝ
  quadrature_tendsto :
    CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
      family refinementFilter continuumIntegral
  uniform_residual :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget
      family refinementFilter

/-- Forget the product-filter uniformity hypothesis and retain the staged
cross-cardinality package. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData.toCrossCardinalityData
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l where
  family := D.family
  refinementFilter := D.refinementFilter
  continuumIntegral := D.continuumIntegral
  quadrature_tendsto := D.quadrature_tendsto

/-- Upgrade staged cross-cardinality data to product-filter data when a
uniform residual proof is supplied separately. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData.toProductFilterData_of_uniformResidual
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l)
    (hResidual :
      CanonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget
        D.family D.refinementFilter) :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l where
  family := D.family
  refinementFilter := D.refinementFilter
  continuumIntegral := D.continuumIntegral
  quadrature_tendsto := D.quadrature_tendsto
  uniform_residual := hResidual

/-- Upgrade staged cross-cardinality data to product-filter data from an
absolute residual envelope tending to zero on the product filter. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData.toProductFilterData_of_residualEnvelope
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l)
    (envelope : ρ × α → ℝ)
    (hEnvelope :
      Filter.Tendsto envelope (D.refinementFilter ×ˢ l : Filter (ρ × α)) (nhds 0))
    (hBound :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate D.family p -
          CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral D.family p| ≤
          envelope p) :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l :=
  D.toProductFilterData_of_uniformResidual
    (canonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget_of_abs_bound
      D.family D.refinementFilter envelope hEnvelope hBound)

/-- Upgrade staged cross-cardinality data to product-filter data from a
cross-slice residual envelope depending only on the within-slice refinement
parameter. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData.toProductFilterData_of_sndResidualEnvelope
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l)
    (envelope : α → ℝ)
    (hEnvelope : Filter.Tendsto envelope l (nhds 0))
    (hBound :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate D.family p -
          CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral D.family p| ≤
          envelope p.2) :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l :=
  D.toProductFilterData_of_uniformResidual
    (canonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget_of_snd_abs_bound
      D.family D.refinementFilter envelope hEnvelope hBound)

/-- Upgrade staged cross-cardinality data to product-filter data from a global
cross-slice residual envelope. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData.toProductFilterData_of_forallSndResidualEnvelope
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l)
    (envelope : α → ℝ)
    (hEnvelope : Filter.Tendsto envelope l (nhds 0))
    (hBound :
      ∀ (r : ρ) (t : α),
        |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate D.family (r, t) -
          CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral D.family (r, t)| ≤
          envelope t) :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l :=
  D.toProductFilterData_of_uniformResidual
    (canonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget_of_forall_snd_abs_bound
      D.family D.refinementFilter envelope hEnvelope hBound)

/-- Named package for the first concrete global residual estimate still needed
for the six-tet product-filter path.  Future geometry only has to fill these
fields: an envelope on the within-slice refinement parameter, convergence of
that envelope to zero, and a slice-uniform absolute residual bound. -/
structure CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l) where
  envelope : α → ℝ
  envelope_tendsto_zero : Filter.Tendsto envelope l (nhds 0)
  global_residual_bound :
    ∀ (r : ρ) (t : α),
      |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate D.family (r, t) -
        CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral D.family (r, t)| ≤
        envelope t

/-- Convert a named global residual envelope package into product-filter data. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData.toProductFilterData
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (E : CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData D) :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l :=
  D.toProductFilterData_of_forallSndResidualEnvelope
    E.envelope E.envelope_tendsto_zero E.global_residual_bound

/-- A named global residual envelope package gives product-filter convergence of
the normalized full-Regge aggregate to the supplied continuum integral. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData.fullReggeProduct_tendsto_continuum
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (E : CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData D) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) D.family)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds D.continuumIntegral) :=
  canonicalPeriodicTetSixTetVolumeQuadratureProduct_fullRegge_tendsto_continuum
    (α := α) (ρ := ρ) D.family D.refinementFilter D.continuumIntegral
    D.quadrature_tendsto
    (canonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget_of_forall_snd_abs_bound
      D.family D.refinementFilter E.envelope E.envelope_tendsto_zero
      E.global_residual_bound)

/-- The actual product full-Regge-to-quadrature residual magnitude.  Naming this
keeps future geometric estimates from restating the long product aggregate
expression. -/
noncomputable def CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ) :
    ρ → α → ℝ :=
  fun r t =>
    |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate F (r, t) -
      CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral F (r, t)|

theorem canonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude_nonneg
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (r : ρ) (t : α) :
    0 ≤ CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude F r t := by
  simp [CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude]

theorem canonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude_bounds_residual
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (r : ρ) (t : α) :
    |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate F (r, t) -
      CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral F (r, t)| ≤
      CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude F r t := by
  rfl

/-- Two-stage residual-bound package.  This is useful when the geometric proof
first produces a slice-dependent residual bound and only afterward proves that
the bound is dominated by a slice-independent vanishing envelope. -/
structure CanonicalPeriodicTetSixTetVolumeQuadratureResidualBoundEnvelopeData
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l) where
  residualBound : ρ → α → ℝ
  envelope : α → ℝ
  envelope_tendsto_zero : Filter.Tendsto envelope l (nhds 0)
  residual_le_bound :
    ∀ (r : ρ) (t : α),
      |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate D.family (r, t) -
        CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral D.family (r, t)| ≤
        residualBound r t
  bound_le_envelope :
    ∀ (r : ρ) (t : α), residualBound r t ≤ envelope t

/-- Collapse a two-stage residual-bound package into the single-envelope data
package consumed by the product-filter theorem. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureResidualBoundEnvelopeData.toGlobalResidualEnvelopeData
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (B : CanonicalPeriodicTetSixTetVolumeQuadratureResidualBoundEnvelopeData D) :
    CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData D where
  envelope := B.envelope
  envelope_tendsto_zero := B.envelope_tendsto_zero
  global_residual_bound := fun r t =>
    le_trans (B.residual_le_bound r t) (B.bound_le_envelope r t)

/-- A two-stage residual-bound package gives product-filter convergence of the
normalized full-Regge aggregate to the supplied continuum integral. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureResidualBoundEnvelopeData.fullReggeProduct_tendsto_continuum
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (B : CanonicalPeriodicTetSixTetVolumeQuadratureResidualBoundEnvelopeData D) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) D.family)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds D.continuumIntegral) :=
  B.toGlobalResidualEnvelopeData.fullReggeProduct_tendsto_continuum

/-- Residual-magnitude envelope package.  The remaining analytic work is just to
prove that the named product residual magnitude is dominated by a vanishing
envelope. -/
structure CanonicalPeriodicTetSixTetVolumeQuadratureResidualMagnitudeEnvelopeData
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l) where
  envelope : α → ℝ
  envelope_tendsto_zero : Filter.Tendsto envelope l (nhds 0)
  magnitude_le_envelope :
    ∀ (r : ρ) (t : α),
      CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude D.family r t ≤ envelope t

/-- Convert residual-magnitude domination into the two-stage residual-bound
package by taking the residual bound to be the residual magnitude itself. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureResidualMagnitudeEnvelopeData.toResidualBoundEnvelopeData
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (M : CanonicalPeriodicTetSixTetVolumeQuadratureResidualMagnitudeEnvelopeData D) :
    CanonicalPeriodicTetSixTetVolumeQuadratureResidualBoundEnvelopeData D where
  residualBound := CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude D.family
  envelope := M.envelope
  envelope_tendsto_zero := M.envelope_tendsto_zero
  residual_le_bound :=
    canonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude_bounds_residual D.family
  bound_le_envelope := M.magnitude_le_envelope

/-- A residual-magnitude envelope package gives product-filter convergence of
the normalized full-Regge aggregate to the supplied continuum integral. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureResidualMagnitudeEnvelopeData.fullReggeProduct_tendsto_continuum
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (M : CanonicalPeriodicTetSixTetVolumeQuadratureResidualMagnitudeEnvelopeData D) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) D.family)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds D.continuumIntegral) :=
  M.toResidualBoundEnvelopeData.fullReggeProduct_tendsto_continuum

/-- The product quadrature proxy converges to the supplied continuum integral. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData.quadratureProduct_tendsto_continuum
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral
        (α := α) (ρ := ρ) D.family)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds D.continuumIntegral) := by
  have h :=
    D.quadrature_tendsto.comp
      (Filter.tendsto_fst :
        Filter.Tendsto (Prod.fst : ρ × α → ρ)
          (D.refinementFilter ×ˢ l) D.refinementFilter)
  simpa [
    CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget,
    CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral,
    Function.comp] using h

/-- Product-filter full-Regge convergence to the supplied continuum integral. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData.fullReggeProduct_tendsto_continuum
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) D.family)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds D.continuumIntegral) :=
  canonicalPeriodicTetSixTetVolumeQuadratureProduct_fullRegge_tendsto_continuum
    (α := α) (ρ := ρ) D.family D.refinementFilter D.continuumIntegral
    D.quadrature_tendsto D.uniform_residual

/-- Direct product-filter convergence theorem from staged cross-cardinality
data plus a cross-slice residual envelope. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData.fullReggeProduct_tendsto_continuum_of_sndResidualEnvelope
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l)
    (envelope : α → ℝ)
    (hEnvelope : Filter.Tendsto envelope l (nhds 0))
    (hBound :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate D.family p -
          CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral D.family p| ≤
          envelope p.2) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) D.family)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds D.continuumIntegral) :=
  (D.toProductFilterData_of_sndResidualEnvelope envelope hEnvelope hBound).fullReggeProduct_tendsto_continuum

/-- Direct product-filter convergence theorem from staged cross-cardinality
data plus a global cross-slice residual envelope. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData.fullReggeProduct_tendsto_continuum_of_forallSndResidualEnvelope
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l)
    (envelope : α → ℝ)
    (hEnvelope : Filter.Tendsto envelope l (nhds 0))
    (hBound :
      ∀ (r : ρ) (t : α),
        |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate D.family (r, t) -
          CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral D.family (r, t)| ≤
          envelope t) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) D.family)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds D.continuumIntegral) :=
  (D.toProductFilterData_of_forallSndResidualEnvelope envelope hEnvelope hBound).fullReggeProduct_tendsto_continuum

/-- Diagonal-filter corollary: any diagonal schedule into the product filter
inherits the product-filter full-Regge continuum limit. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData.fullReggeDiagonal_tendsto_continuum
    {α ρ δ : Type*} {l : Filter α} {m : Filter δ}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (diagonal : δ → ρ × α)
    (hDiagonal :
      Filter.Tendsto diagonal m (D.refinementFilter ×ˢ l : Filter (ρ × α))) :
    Filter.Tendsto
      (fun s : δ =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
          (α := α) (ρ := ρ) D.family (diagonal s))
      m
      (nhds D.continuumIntegral) := by
  simpa [Function.comp] using
    (CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData.fullReggeProduct_tendsto_continuum
      (α := α) (ρ := ρ) D).comp hDiagonal

/-- Absolute spacing size for a six-tet quadrature slice. -/
noncomputable def CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : α → ℝ := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  exact fun t : α => |S.data.spacing t|

/-- Absolute cell-volume error against the limiting cell volume for a six-tet
quadrature slice. -/
noncomputable def CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : α → ℝ := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  exact fun t : α => |S.data.cellVolume t - S.data.limitCellVolume|

/-- The named slice spacing magnitude vanishes along the within-slice
refinement filter. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude_tendsto_zero
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    Filter.Tendsto S.spacingMagnitude l (nhds 0) := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  simpa [CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude] using
    S.data.spacing_tendsto_zero.abs

/-- The named slice cell-volume error vanishes along the within-slice
refinement filter. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError_tendsto_zero
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    Filter.Tendsto S.cellVolumeError l (nhds 0) := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  have hSub :
      Filter.Tendsto
        (fun t : α => S.data.cellVolume t - S.data.limitCellVolume)
        l
        (nhds 0) := by
    simpa using
      S.data.cellVolume_tendsto.sub
        (tendsto_const_nhds (x := S.data.limitCellVolume))
  simpa [CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError] using hSub.abs

/-- Uniform spacing/cell-volume envelope used by the product residual estimate.
The coefficient is supplied by the future geometric estimate; the two envelope
terms are the uniform spacing and cell-volume error controls. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellEnvelope
    {α : Type*}
    (coefficient : ℝ)
    (spacingEnvelope cellVolumeEnvelope : α → ℝ) : α → ℝ :=
  fun t : α => coefficient * (spacingEnvelope t + cellVolumeEnvelope t)

/-- If the spacing and cell-volume envelopes vanish, then their coefficient
weighted sum vanishes. -/
theorem canonicalPeriodicTetSixTetVolumeQuadratureSpacingCellEnvelope_tendsto_zero
    {α : Type*} {l : Filter α}
    (coefficient : ℝ)
    (spacingEnvelope cellVolumeEnvelope : α → ℝ)
    (hSpacing : Filter.Tendsto spacingEnvelope l (nhds 0))
    (hCell : Filter.Tendsto cellVolumeEnvelope l (nhds 0)) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellEnvelope
        coefficient spacingEnvelope cellVolumeEnvelope)
      l
      (nhds 0) := by
  have hSum : Filter.Tendsto (fun t : α => spacingEnvelope t + cellVolumeEnvelope t) l (nhds 0) := by
    simpa using hSpacing.add hCell
  simpa [CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellEnvelope] using
    hSum.const_mul coefficient

/-- A fixed slice's spacing/cell-volume envelope vanishes using only the slice's
own refinement data.  Cross-slice uniformity is still a separate product-filter
obligation. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingCellEnvelope_tendsto_zero
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (coefficient : ℝ) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellEnvelope
        coefficient S.spacingMagnitude S.cellVolumeError)
      l
      (nhds 0) :=
  canonicalPeriodicTetSixTetVolumeQuadratureSpacingCellEnvelope_tendsto_zero
    coefficient S.spacingMagnitude S.cellVolumeError
    S.spacingMagnitude_tendsto_zero
    S.cellVolumeError_tendsto_zero

/-- Raw spacing schedule carried by a six-tet quadrature slice, with the slice's
side-length instances installed locally. -/
noncomputable def CanonicalPeriodicTetSixTetVolumeQuadratureSlice.rawSpacingSchedule
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : α → ℝ := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  exact S.data.spacing

/-- Raw cell-volume schedule carried by a six-tet quadrature slice, with the
slice's side-length instances installed locally. -/
noncomputable def CanonicalPeriodicTetSixTetVolumeQuadratureSlice.rawCellVolumeSchedule
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : α → ℝ := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  exact S.data.cellVolume

/-- Raw limiting cell volume carried by a six-tet quadrature slice, with the
slice's side-length instances installed locally. -/
noncomputable def CanonicalPeriodicTetSixTetVolumeQuadratureSlice.rawLimitCellVolume
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : ℝ := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  exact S.data.limitCellVolume

/-- The named spacing magnitude is the absolute value of the raw slice spacing
schedule. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude_eq_abs_rawSpacingSchedule
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (t : α) :
    S.spacingMagnitude t = |S.rawSpacingSchedule t| := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  simp [
    CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude,
    CanonicalPeriodicTetSixTetVolumeQuadratureSlice.rawSpacingSchedule]

/-- The named cell-volume error is the absolute difference between the raw
cell-volume schedule and the raw limiting cell volume. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError_eq_abs_rawCellVolumeSchedule_sub_rawLimitCellVolume
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (t : α) :
    S.cellVolumeError t = |S.rawCellVolumeSchedule t - S.rawLimitCellVolume| := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  simp [
    CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError,
    CanonicalPeriodicTetSixTetVolumeQuadratureSlice.rawCellVolumeSchedule,
    CanonicalPeriodicTetSixTetVolumeQuadratureSlice.rawLimitCellVolume]

/-- Eventual residual-magnitude envelope package.  This is the proof shape
expected from geometric estimates: after passing far enough along the product
refinement filter, the named residual magnitude is bounded by one
slice-independent envelope tending to zero. -/
structure CanonicalPeriodicTetSixTetVolumeQuadratureEventuallyResidualMagnitudeEnvelopeData
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l) where
  envelope : α → ℝ
  envelope_tendsto_zero : Filter.Tendsto envelope l (nhds 0)
  eventually_magnitude_le_envelope :
    ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
      CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude D.family p.1 p.2 ≤
        envelope p.2

/-- Convert eventual residual-magnitude domination into product-filter data. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureEventuallyResidualMagnitudeEnvelopeData.toProductFilterData
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (M : CanonicalPeriodicTetSixTetVolumeQuadratureEventuallyResidualMagnitudeEnvelopeData D) :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l :=
  D.toProductFilterData_of_sndResidualEnvelope
    M.envelope M.envelope_tendsto_zero
    (M.eventually_magnitude_le_envelope.mono (fun p hp => by
      exact le_trans
        (canonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude_bounds_residual
          D.family p.1 p.2)
        hp))

/-- Eventual residual-magnitude domination gives product-filter full-Regge
convergence to the supplied continuum integral. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureEventuallyResidualMagnitudeEnvelopeData.fullReggeProduct_tendsto_continuum
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (M : CanonicalPeriodicTetSixTetVolumeQuadratureEventuallyResidualMagnitudeEnvelopeData D) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) D.family)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds D.continuumIntegral) :=
  M.toProductFilterData.fullReggeProduct_tendsto_continuum

/-- Any diagonal schedule into the product filter inherits convergence from an
eventual residual-magnitude envelope. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureEventuallyResidualMagnitudeEnvelopeData.fullReggeDiagonal_tendsto_continuum
    {α ρ δ : Type*} {l : Filter α} {m : Filter δ}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (M : CanonicalPeriodicTetSixTetVolumeQuadratureEventuallyResidualMagnitudeEnvelopeData D)
    (diagonal : δ → ρ × α)
    (hDiagonal :
      Filter.Tendsto diagonal m (D.refinementFilter ×ˢ l : Filter (ρ × α))) :
    Filter.Tendsto
      (fun s : δ =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
          (α := α) (ρ := ρ) D.family (diagonal s))
      m
      (nhds D.continuumIntegral) :=
  M.toProductFilterData.fullReggeDiagonal_tendsto_continuum diagonal hDiagonal

/-- Eventual residual-magnitude domination also gives direct product-filter
vanishing of the named residual magnitude itself. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureEventuallyResidualMagnitudeEnvelopeData.residualMagnitude_tendsto_zero
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (M : CanonicalPeriodicTetSixTetVolumeQuadratureEventuallyResidualMagnitudeEnvelopeData D) :
    Filter.Tendsto
      (fun p : ρ × α =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
          D.family p.1 p.2)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds 0) := by
  exact squeeze_zero'
    (Filter.Eventually.of_forall (fun p : ρ × α =>
      canonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude_nonneg
        D.family p.1 p.2))
    M.eventually_magnitude_le_envelope
    (M.envelope_tendsto_zero.comp
      (Filter.tendsto_snd :
        Filter.Tendsto (Prod.snd : ρ × α → α)
          (D.refinementFilter ×ˢ l) l))

/-- Any diagonal schedule into the product filter inherits residual-magnitude
vanishing from an eventual residual-magnitude envelope. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureEventuallyResidualMagnitudeEnvelopeData.residualMagnitudeDiagonal_tendsto_zero
    {α ρ δ : Type*} {l : Filter α} {m : Filter δ}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (M : CanonicalPeriodicTetSixTetVolumeQuadratureEventuallyResidualMagnitudeEnvelopeData D)
    (diagonal : δ → ρ × α)
    (hDiagonal :
      Filter.Tendsto diagonal m (D.refinementFilter ×ˢ l : Filter (ρ × α))) :
    Filter.Tendsto
      (fun s : δ =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
          D.family (diagonal s).1 (diagonal s).2)
      m
      (nhds 0) := by
  simpa [Function.comp] using
    M.residualMagnitude_tendsto_zero.comp hDiagonal

/-- Cross-slice schedule envelope data.  This separates the uniform
spacing/cell-volume schedule control from the later geometric residual
inequality. -/
structure CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l) where
  spacingEnvelope : α → ℝ
  cellVolumeEnvelope : α → ℝ
  spacingEnvelope_tendsto_zero : Filter.Tendsto spacingEnvelope l (nhds 0)
  cellVolumeEnvelope_tendsto_zero : Filter.Tendsto cellVolumeEnvelope l (nhds 0)
  eventually_spacingMagnitude_le_envelope :
    ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
      CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
        (D.family.slice p.1) p.2 ≤ spacingEnvelope p.2
  eventually_cellVolumeError_le_envelope :
    ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
      CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
        (D.family.slice p.1) p.2 ≤ cellVolumeEnvelope p.2

/-- The cross-slice spacing/cell-volume envelope supplied by schedule data
vanishes along the within-slice filter. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData.spacingCellEnvelope_tendsto_zero
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData D)
    (coefficient : ℝ) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellEnvelope
        coefficient S.spacingEnvelope S.cellVolumeEnvelope)
      l
      (nhds 0) :=
  canonicalPeriodicTetSixTetVolumeQuadratureSpacingCellEnvelope_tendsto_zero
    coefficient S.spacingEnvelope S.cellVolumeEnvelope
    S.spacingEnvelope_tendsto_zero
    S.cellVolumeEnvelope_tendsto_zero

/-- Common spacing/cell-volume schedule data for a genuinely varying-cardinality
family.  The side lengths may vary with the slice index, but eventually on the
product filter all slices use the same within-slice spacing schedule, the same
cell-volume schedule, and the same limiting cell volume. -/
structure CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l) where
  spacingSchedule : α → ℝ
  cellVolumeSchedule : α → ℝ
  limitCellVolume : ℝ
  spacingSchedule_tendsto_zero :
    Filter.Tendsto spacingSchedule l (nhds 0)
  cellVolumeSchedule_tendsto_limit :
    Filter.Tendsto cellVolumeSchedule l (nhds limitCellVolume)
  eventually_spacingMagnitude_eq_schedule :
    ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
      CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
        (D.family.slice p.1) p.2 = |spacingSchedule p.2|
  eventually_cellVolumeError_eq_schedule :
    ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
      CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
        (D.family.slice p.1) p.2 =
          |cellVolumeSchedule p.2 - limitCellVolume|

/-- A common spacing/cell-volume schedule supplies the cross-slice schedule
envelopes required by the product-filter bridge. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData.toSpacingCellScheduleEnvelopeData
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (C : CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData D) :
    CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData D where
  spacingEnvelope := fun t : α => |C.spacingSchedule t|
  cellVolumeEnvelope := fun t : α => |C.cellVolumeSchedule t - C.limitCellVolume|
  spacingEnvelope_tendsto_zero := by
    simpa using C.spacingSchedule_tendsto_zero.abs
  cellVolumeEnvelope_tendsto_zero := by
    have hSub :
        Filter.Tendsto
          (fun t : α => C.cellVolumeSchedule t - C.limitCellVolume)
          l
          (nhds 0) := by
      simpa using
        C.cellVolumeSchedule_tendsto_limit.sub
          (tendsto_const_nhds (x := C.limitCellVolume))
    simpa using hSub.abs
  eventually_spacingMagnitude_le_envelope :=
    C.eventually_spacingMagnitude_eq_schedule.mono (fun _ hp => le_of_eq hp)
  eventually_cellVolumeError_le_envelope :=
    C.eventually_cellVolumeError_eq_schedule.mono (fun _ hp => le_of_eq hp)

/-- The spacing/cell envelope from a common varying-cardinality schedule
vanishes along the within-slice filter. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData.spacingCellEnvelope_tendsto_zero
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (C : CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData D)
    (coefficient : ℝ) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellEnvelope
        coefficient
        (fun t : α => |C.spacingSchedule t|)
        (fun t : α => |C.cellVolumeSchedule t - C.limitCellVolume|))
      l
      (nhds 0) := by
  simpa using
    C.toSpacingCellScheduleEnvelopeData.spacingCellEnvelope_tendsto_zero coefficient

/-- Build common schedule-envelope data from raw slice schedules.  This is the
handoff wanted by explicit side-length families: they can state eventual
agreement of each slice's raw spacing, raw cell-volume schedule, and raw limit
cell volume with one common schedule, while this constructor handles the named
absolute-value error quantities used by the product-filter bridge. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData.ofRawSchedules
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l)
    (spacingSchedule cellVolumeSchedule : α → ℝ)
    (limitCellVolume : ℝ)
    (hSpacingTendsto :
      Filter.Tendsto spacingSchedule l (nhds 0))
    (hCellTendsto :
      Filter.Tendsto cellVolumeSchedule l (nhds limitCellVolume))
    (hSpacing :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureSlice.rawSpacingSchedule
          (D.family.slice p.1) p.2 = spacingSchedule p.2)
    (hCell :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureSlice.rawCellVolumeSchedule
          (D.family.slice p.1) p.2 = cellVolumeSchedule p.2)
    (hLimit :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureSlice.rawLimitCellVolume
          (D.family.slice p.1) = limitCellVolume) :
    CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData D where
  spacingSchedule := spacingSchedule
  cellVolumeSchedule := cellVolumeSchedule
  limitCellVolume := limitCellVolume
  spacingSchedule_tendsto_zero := hSpacingTendsto
  cellVolumeSchedule_tendsto_limit := hCellTendsto
  eventually_spacingMagnitude_eq_schedule :=
    hSpacing.mono (fun p hp => by
      calc
        CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
            (D.family.slice p.1) p.2 =
            |CanonicalPeriodicTetSixTetVolumeQuadratureSlice.rawSpacingSchedule
              (D.family.slice p.1) p.2| :=
          CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude_eq_abs_rawSpacingSchedule
            (D.family.slice p.1) p.2
        _ = |spacingSchedule p.2| := by simp [hp])
  eventually_cellVolumeError_eq_schedule :=
    ((hCell.and hLimit).mono (fun p h => by
      rcases h with ⟨hCellEq, hLimitEq⟩
      calc
        CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
            (D.family.slice p.1) p.2 =
            |CanonicalPeriodicTetSixTetVolumeQuadratureSlice.rawCellVolumeSchedule
                (D.family.slice p.1) p.2 -
              CanonicalPeriodicTetSixTetVolumeQuadratureSlice.rawLimitCellVolume
                (D.family.slice p.1)| :=
          CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError_eq_abs_rawCellVolumeSchedule_sub_rawLimitCellVolume
            (D.family.slice p.1) p.2
        _ = |cellVolumeSchedule p.2 - limitCellVolume| := by
          simp [hCellEq, hLimitEq]))

/-- Spacing/cell-volume residual envelope package.  This is the first interface
that names the concrete geometric quantities expected to control the residual:
the slice spacing magnitude and the slice cell-volume error.  The future
geometric estimate supplies the coefficient and the residual bound by those two
quantities; this package adds uniform vanishing envelopes for both quantities. -/
structure CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellResidualEnvelopeData
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l) where
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  spacingEnvelope : α → ℝ
  cellVolumeEnvelope : α → ℝ
  spacingEnvelope_tendsto_zero : Filter.Tendsto spacingEnvelope l (nhds 0)
  cellVolumeEnvelope_tendsto_zero : Filter.Tendsto cellVolumeEnvelope l (nhds 0)
  eventually_spacingMagnitude_le_envelope :
    ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
      CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
        (D.family.slice p.1) p.2 ≤ spacingEnvelope p.2
  eventually_cellVolumeError_le_envelope :
    ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
      CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
        (D.family.slice p.1) p.2 ≤ cellVolumeEnvelope p.2
  eventually_magnitude_le_spacing_cell :
    ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
      CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
          D.family p.1 p.2 ≤
        coefficient *
          (CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
              (D.family.slice p.1) p.2 +
            CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
              (D.family.slice p.1) p.2)

/-- Add the geometric residual estimate to cross-slice schedule envelope data,
producing the full spacing/cell-volume residual package. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData.toSpacingCellResidualEnvelopeData
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData D)
    (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient)
    (hMagnitude :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
            D.family p.1 p.2 ≤
          coefficient *
            (CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
                (D.family.slice p.1) p.2 +
              CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
                (D.family.slice p.1) p.2)) :
    CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellResidualEnvelopeData D where
  coefficient := coefficient
  coefficient_nonneg := coefficient_nonneg
  spacingEnvelope := S.spacingEnvelope
  cellVolumeEnvelope := S.cellVolumeEnvelope
  spacingEnvelope_tendsto_zero := S.spacingEnvelope_tendsto_zero
  cellVolumeEnvelope_tendsto_zero := S.cellVolumeEnvelope_tendsto_zero
  eventually_spacingMagnitude_le_envelope := S.eventually_spacingMagnitude_le_envelope
  eventually_cellVolumeError_le_envelope := S.eventually_cellVolumeError_le_envelope
  eventually_magnitude_le_spacing_cell := hMagnitude

/-- Convert spacing/cell-volume residual control into the eventual residual
magnitude envelope package. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellResidualEnvelopeData.toEventuallyResidualMagnitudeEnvelopeData
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (M : CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellResidualEnvelopeData D) :
    CanonicalPeriodicTetSixTetVolumeQuadratureEventuallyResidualMagnitudeEnvelopeData D where
  envelope :=
    CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellEnvelope
      M.coefficient M.spacingEnvelope M.cellVolumeEnvelope
  envelope_tendsto_zero :=
    canonicalPeriodicTetSixTetVolumeQuadratureSpacingCellEnvelope_tendsto_zero
      M.coefficient M.spacingEnvelope M.cellVolumeEnvelope
      M.spacingEnvelope_tendsto_zero M.cellVolumeEnvelope_tendsto_zero
  eventually_magnitude_le_envelope := by
    exact
      ((M.eventually_magnitude_le_spacing_cell.and
          M.eventually_spacingMagnitude_le_envelope).and
        M.eventually_cellVolumeError_le_envelope).mono
        (fun p h => by
          rcases h with ⟨⟨hMagnitude, hSpacing⟩, hCell⟩
          have hSum :
              CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
                  (D.family.slice p.1) p.2 +
                CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
                  (D.family.slice p.1) p.2 ≤
              M.spacingEnvelope p.2 + M.cellVolumeEnvelope p.2 := by
            exact add_le_add hSpacing hCell
          have hMul :=
            mul_le_mul_of_nonneg_left hSum M.coefficient_nonneg
          exact le_trans hMagnitude hMul)

/-- Spacing/cell-volume residual control gives product-filter full-Regge
convergence to the supplied continuum integral. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellResidualEnvelopeData.fullReggeProduct_tendsto_continuum
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (M : CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellResidualEnvelopeData D) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) D.family)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds D.continuumIntegral) :=
  M.toEventuallyResidualMagnitudeEnvelopeData.fullReggeProduct_tendsto_continuum

/-- A diagonal schedule into the product filter inherits convergence from
spacing/cell-volume residual control. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellResidualEnvelopeData.fullReggeDiagonal_tendsto_continuum
    {α ρ δ : Type*} {l : Filter α} {m : Filter δ}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (M : CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellResidualEnvelopeData D)
    (diagonal : δ → ρ × α)
    (hDiagonal :
      Filter.Tendsto diagonal m (D.refinementFilter ×ˢ l : Filter (ρ × α))) :
    Filter.Tendsto
      (fun s : δ =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
          (α := α) (ρ := ρ) D.family (diagonal s))
      m
      (nhds D.continuumIntegral) :=
  M.toEventuallyResidualMagnitudeEnvelopeData.fullReggeDiagonal_tendsto_continuum
    diagonal hDiagonal

/-- Spacing/cell-volume residual control gives direct product-filter vanishing
of the named residual magnitude. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellResidualEnvelopeData.residualMagnitude_tendsto_zero
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (M : CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellResidualEnvelopeData D) :
    Filter.Tendsto
      (fun p : ρ × α =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
          D.family p.1 p.2)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds 0) :=
  M.toEventuallyResidualMagnitudeEnvelopeData.residualMagnitude_tendsto_zero

/-- A diagonal schedule inherits residual-magnitude vanishing from
spacing/cell-volume residual control. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellResidualEnvelopeData.residualMagnitudeDiagonal_tendsto_zero
    {α ρ δ : Type*} {l : Filter α} {m : Filter δ}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (M : CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellResidualEnvelopeData D)
    (diagonal : δ → ρ × α)
    (hDiagonal :
      Filter.Tendsto diagonal m (D.refinementFilter ×ˢ l : Filter (ρ × α))) :
    Filter.Tendsto
      (fun s : δ =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
          D.family (diagonal s).1 (diagonal s).2)
      m
      (nhds 0) :=
  M.toEventuallyResidualMagnitudeEnvelopeData.residualMagnitudeDiagonal_tendsto_zero
    diagonal hDiagonal

/-- Cross-slice schedule envelope data plus the geometric residual estimate gives
product-filter full-Regge convergence. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData.fullReggeProduct_tendsto_continuum
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData D)
    (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient)
    (hMagnitude :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
            D.family p.1 p.2 ≤
          coefficient *
            (CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
                (D.family.slice p.1) p.2 +
              CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
                (D.family.slice p.1) p.2)) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) D.family)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds D.continuumIntegral) :=
  (S.toSpacingCellResidualEnvelopeData
    coefficient coefficient_nonneg hMagnitude).fullReggeProduct_tendsto_continuum

/-- A diagonal schedule into the product filter inherits convergence from
cross-slice schedule envelope data plus the geometric residual estimate. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData.fullReggeDiagonal_tendsto_continuum
    {α ρ δ : Type*} {l : Filter α} {m : Filter δ}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData D)
    (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient)
    (hMagnitude :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
            D.family p.1 p.2 ≤
          coefficient *
            (CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
                (D.family.slice p.1) p.2 +
              CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
                (D.family.slice p.1) p.2))
    (diagonal : δ → ρ × α)
    (hDiagonal :
      Filter.Tendsto diagonal m (D.refinementFilter ×ˢ l : Filter (ρ × α))) :
    Filter.Tendsto
      (fun s : δ =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
          (α := α) (ρ := ρ) D.family (diagonal s))
      m
      (nhds D.continuumIntegral) :=
  (S.toSpacingCellResidualEnvelopeData
    coefficient coefficient_nonneg hMagnitude).fullReggeDiagonal_tendsto_continuum
      diagonal hDiagonal

/-- Cross-slice schedule envelope data plus the geometric residual estimate gives
direct product-filter vanishing of the named residual magnitude. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData.residualMagnitude_tendsto_zero
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData D)
    (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient)
    (hMagnitude :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
            D.family p.1 p.2 ≤
          coefficient *
            (CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
                (D.family.slice p.1) p.2 +
              CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
                (D.family.slice p.1) p.2)) :
    Filter.Tendsto
      (fun p : ρ × α =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
          D.family p.1 p.2)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds 0) :=
  (S.toSpacingCellResidualEnvelopeData
    coefficient coefficient_nonneg hMagnitude).residualMagnitude_tendsto_zero

/-- A diagonal schedule inherits residual-magnitude vanishing from cross-slice
schedule envelope data plus the geometric residual estimate. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData.residualMagnitudeDiagonal_tendsto_zero
    {α ρ δ : Type*} {l : Filter α} {m : Filter δ}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData D)
    (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient)
    (hMagnitude :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
            D.family p.1 p.2 ≤
          coefficient *
            (CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
                (D.family.slice p.1) p.2 +
              CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
                (D.family.slice p.1) p.2))
    (diagonal : δ → ρ × α)
    (hDiagonal :
      Filter.Tendsto diagonal m (D.refinementFilter ×ˢ l : Filter (ρ × α))) :
    Filter.Tendsto
      (fun s : δ =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
          D.family (diagonal s).1 (diagonal s).2)
      m
      (nhds 0) :=
  (S.toSpacingCellResidualEnvelopeData
    coefficient coefficient_nonneg hMagnitude).residualMagnitudeDiagonal_tendsto_zero
      diagonal hDiagonal

/-- Common varying-cardinality schedule data plus the geometric residual estimate
gives product-filter full-Regge convergence. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData.fullReggeProduct_tendsto_continuum
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (C : CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData D)
    (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient)
    (hMagnitude :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
            D.family p.1 p.2 ≤
          coefficient *
            (CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
                (D.family.slice p.1) p.2 +
              CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
                (D.family.slice p.1) p.2)) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) D.family)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds D.continuumIntegral) :=
  C.toSpacingCellScheduleEnvelopeData.fullReggeProduct_tendsto_continuum
    coefficient coefficient_nonneg hMagnitude

/-- Common varying-cardinality schedule data plus the geometric residual estimate
gives diagonal full-Regge convergence for any schedule into the product filter. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData.fullReggeDiagonal_tendsto_continuum
    {α ρ δ : Type*} {l : Filter α} {m : Filter δ}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (C : CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData D)
    (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient)
    (hMagnitude :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
            D.family p.1 p.2 ≤
          coefficient *
            (CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
                (D.family.slice p.1) p.2 +
              CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
                (D.family.slice p.1) p.2))
    (diagonal : δ → ρ × α)
    (hDiagonal :
      Filter.Tendsto diagonal m (D.refinementFilter ×ˢ l : Filter (ρ × α))) :
    Filter.Tendsto
      (fun s : δ =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
          (α := α) (ρ := ρ) D.family (diagonal s))
      m
      (nhds D.continuumIntegral) :=
  C.toSpacingCellScheduleEnvelopeData.fullReggeDiagonal_tendsto_continuum
    coefficient coefficient_nonneg hMagnitude diagonal hDiagonal

/-- Common varying-cardinality schedule data plus the geometric residual estimate
also gives direct product-filter vanishing of the named residual magnitude. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData.residualMagnitude_tendsto_zero
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (C : CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData D)
    (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient)
    (hMagnitude :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
            D.family p.1 p.2 ≤
          coefficient *
            (CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
                (D.family.slice p.1) p.2 +
              CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
                (D.family.slice p.1) p.2)) :
    Filter.Tendsto
      (fun p : ρ × α =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
          D.family p.1 p.2)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds 0) :=
  C.toSpacingCellScheduleEnvelopeData.residualMagnitude_tendsto_zero
    coefficient coefficient_nonneg hMagnitude

/-- Any diagonal schedule into the product filter inherits residual-magnitude
vanishing from common varying-cardinality schedule data plus the residual
estimate. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData.residualMagnitudeDiagonal_tendsto_zero
    {α ρ δ : Type*} {l : Filter α} {m : Filter δ}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := ρ) l}
    (C : CanonicalPeriodicTetSixTetVolumeQuadratureCommonScheduleEnvelopeData D)
    (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient)
    (hMagnitude :
      ∀ᶠ p : ρ × α in (D.refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
            D.family p.1 p.2 ≤
          coefficient *
            (CanonicalPeriodicTetSixTetVolumeQuadratureSlice.spacingMagnitude
                (D.family.slice p.1) p.2 +
              CanonicalPeriodicTetSixTetVolumeQuadratureSlice.cellVolumeError
                (D.family.slice p.1) p.2))
    (diagonal : δ → ρ × α)
    (hDiagonal :
      Filter.Tendsto diagonal m (D.refinementFilter ×ˢ l : Filter (ρ × α))) :
    Filter.Tendsto
      (fun s : δ =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
          D.family (diagonal s).1 (diagonal s).2)
      m
      (nhds 0) :=
  C.toSpacingCellScheduleEnvelopeData.residualMagnitudeDiagonal_tendsto_zero
    coefficient coefficient_nonneg hMagnitude diagonal hDiagonal

/-- The single-slice varying-cardinality family.  This is the first concrete
schedule-envelope instantiation: no cross-cardinality variation is present, so
the slice's own spacing and cell-volume error functions are the uniform
envelopes. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceRefinementFamily
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l PUnit where
  slice := fun _ => S

/-- A single-slice family has constant quadrature proxy along any
refinement-index filter on `PUnit`. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSlice.singleSlice_crossCardinalityTarget
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (refinementFilter : Filter PUnit) :
    CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
      S.toSingleSliceRefinementFamily refinementFilter S.quadratureIntegral := by
  simpa [
    CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget,
    CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceRefinementFamily] using
    (tendsto_const_nhds :
      Filter.Tendsto
        (fun _ : PUnit => S.quadratureIntegral)
        refinementFilter
        (nhds S.quadratureIntegral))

/-- Cross-cardinality data for the single-slice family. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceCrossCardinalityData
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (refinementFilter : Filter PUnit) :
    CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData (α := α) (ρ := PUnit) l where
  family := S.toSingleSliceRefinementFamily
  refinementFilter := refinementFilter
  continuumIntegral := S.quadratureIntegral
  quadrature_tendsto := S.singleSlice_crossCardinalityTarget refinementFilter

/-- Product-filter data for the single-slice family.

Since the cardinality index is `PUnit`, there is no genuine cross-cardinality
variation.  The product-filter residual is just the existing per-slice
full-Regge-to-quadrature residual pulled back along `Prod.snd`. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceProductFilterData
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (refinementFilter : Filter PUnit) :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := PUnit) l where
  family := S.toSingleSliceRefinementFamily
  refinementFilter := refinementFilter
  continuumIntegral := S.quadratureIntegral
  quadrature_tendsto := S.singleSlice_crossCardinalityTarget refinementFilter
  uniform_residual := by
    have hFull := S.fullRegge_tendsto_quadratureIntegral
    have hResidual :
        Filter.Tendsto
          (fun t : α => S.fullReggeAggregate t - S.quadratureIntegral)
          l
          (nhds 0) := by
      simpa using hFull.sub (tendsto_const_nhds (x := S.quadratureIntegral))
    have hProduct :=
      hResidual.comp
        (Filter.tendsto_snd :
          Filter.Tendsto (Prod.snd : PUnit × α → α)
            (refinementFilter ×ˢ l) l)
    simpa [
      CanonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget,
      CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate,
      CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral,
      CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceRefinementFamily]
      using hProduct

/-- The single-slice schedule envelope package, using the slice's own
`spacingMagnitude` and `cellVolumeError` as the envelopes. -/
def CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceScheduleEnvelopeData
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (refinementFilter : Filter PUnit) :
    CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellScheduleEnvelopeData
      (S.toSingleSliceCrossCardinalityData refinementFilter) where
  spacingEnvelope := S.spacingMagnitude
  cellVolumeEnvelope := S.cellVolumeError
  spacingEnvelope_tendsto_zero := S.spacingMagnitude_tendsto_zero
  cellVolumeEnvelope_tendsto_zero := S.cellVolumeError_tendsto_zero
  eventually_spacingMagnitude_le_envelope :=
    Filter.Eventually.of_forall (fun p : PUnit × α => by
      simp [
        CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceCrossCardinalityData,
        CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceRefinementFamily])
  eventually_cellVolumeError_le_envelope :=
    Filter.Eventually.of_forall (fun p : PUnit × α => by
      simp [
        CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceCrossCardinalityData,
        CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceRefinementFamily])

/-- In the single-slice case, the explicit spacing/cell-volume residual estimate
implies that the named product residual magnitude tends to zero along the
within-slice filter. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSlice.singleSlice_residualMagnitude_tendsto_zero_of_residualEstimate
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (coefficient : ℝ)
    (hMagnitude :
      ∀ᶠ t : α in l,
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
            S.toSingleSliceRefinementFamily PUnit.unit t ≤
          coefficient * (S.spacingMagnitude t + S.cellVolumeError t)) :
    Filter.Tendsto
      (fun t : α =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
          S.toSingleSliceRefinementFamily PUnit.unit t)
      l
      (nhds 0) := by
  have hUpper :
      Filter.Tendsto
        (CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellEnvelope
          coefficient S.spacingMagnitude S.cellVolumeError)
        l
        (nhds 0) :=
    S.spacingCellEnvelope_tendsto_zero coefficient
  exact squeeze_zero'
    (Filter.Eventually.of_forall (fun t : α =>
      canonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude_nonneg
        S.toSingleSliceRefinementFamily PUnit.unit t))
    hMagnitude
    (by
      simpa [CanonicalPeriodicTetSixTetVolumeQuadratureSpacingCellEnvelope] using hUpper)

/-- Single-slice product-filter convergence from the explicit spacing/cell-volume
residual estimate.  This is the complete single-slice schedule path; the only
remaining input is the geometric residual bound itself. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSlice.singleSlice_fullReggeProduct_tendsto_continuum_of_residualEstimate
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (refinementFilter : Filter PUnit)
    (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient)
    (hMagnitude :
      ∀ᶠ p : PUnit × α in (refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
            S.toSingleSliceRefinementFamily p.1 p.2 ≤
          coefficient * (S.spacingMagnitude p.2 + S.cellVolumeError p.2)) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := PUnit) S.toSingleSliceRefinementFamily)
      (refinementFilter ×ˢ l : Filter (PUnit × α))
      (nhds S.quadratureIntegral) :=
  (S.toSingleSliceScheduleEnvelopeData refinementFilter).fullReggeProduct_tendsto_continuum
    coefficient coefficient_nonneg
    (by
      simpa [
        CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceCrossCardinalityData,
        CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceRefinementFamily] using hMagnitude)

/-- Single-slice diagonal convergence from the explicit spacing/cell-volume
residual estimate. -/
theorem CanonicalPeriodicTetSixTetVolumeQuadratureSlice.singleSlice_fullReggeDiagonal_tendsto_continuum_of_residualEstimate
    {α δ : Type*} {l : Filter α} {m : Filter δ}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (refinementFilter : Filter PUnit)
    (coefficient : ℝ)
    (coefficient_nonneg : 0 ≤ coefficient)
    (hMagnitude :
      ∀ᶠ p : PUnit × α in (refinementFilter ×ˢ l),
        CanonicalPeriodicTetSixTetVolumeQuadratureProductResidualMagnitude
            S.toSingleSliceRefinementFamily p.1 p.2 ≤
          coefficient * (S.spacingMagnitude p.2 + S.cellVolumeError p.2))
    (diagonal : δ → PUnit × α)
    (hDiagonal :
      Filter.Tendsto diagonal m (refinementFilter ×ˢ l : Filter (PUnit × α))) :
    Filter.Tendsto
      (fun s : δ =>
        CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
          (α := α) (ρ := PUnit) S.toSingleSliceRefinementFamily (diagonal s))
      m
      (nhds S.quadratureIntegral) :=
  (S.toSingleSliceScheduleEnvelopeData refinementFilter).fullReggeDiagonal_tendsto_continuum
    coefficient coefficient_nonneg
    (by
      simpa [
        CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceCrossCardinalityData,
        CanonicalPeriodicTetSixTetVolumeQuadratureSlice.toSingleSliceRefinementFamily] using hMagnitude)
    diagonal hDiagonal

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
explicit Freudenthal coordinate realization, with the remaining flatness input
stated as the exact incident Freudenthal dihedral-angle sum. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_angleSum
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hAngleSum : CanonicalPeriodicZeroDeficitAngleSumTarget Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_zeroDeficit
    Nx Ny Nz hx hy hz hLocal
    (canonicalPeriodicGlobalZeroDeficitAtFlat_of_incidentAngleSum
      Nx Ny Nz hx hy hz hAngleSum)

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
explicit Freudenthal coordinate realization, with the remaining flatness input
stated as the typed periodic-edge angle-sum target. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_typedEdgeAngleSum
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hTyped : CanonicalPeriodicTypedEdgeAngleSumTarget Nx Ny Nz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_angleSum
    Nx Ny Nz hx hy hz hLocal
    (canonicalPeriodicZeroDeficitAngleSumTarget_of_typedEdgeAngleSum
      Nx Ny Nz hx hy hz hTyped)

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
explicit Freudenthal coordinate realization, with the remaining flatness input
stated as the direct typed cell/tetrahedron angle-sum target. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_directTypedAngleSum
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hDirect : CanonicalPeriodicDirectTypedEdgeAngleSumTarget Nx Ny Nz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_typedEdgeAngleSum
    Nx Ny Nz hx hy hz hLocal
    (canonicalPeriodicTypedEdgeAngleSumTarget_of_directTyped Nx Ny Nz hDirect)

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
explicit Freudenthal coordinate realization, with the remaining flatness input
stated as the explicit local-slot triple-sum angle target. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_localSlotTripleAngleSum
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hTriple : CanonicalPeriodicLocalSlotTripleAngleSumTarget Nx Ny Nz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_directTypedAngleSum
    Nx Ny Nz hx hy hz hLocal
    (canonicalPeriodicDirectTypedEdgeAngleSumTarget_of_localSlotTriple
      Nx Ny Nz hTriple)

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
explicit Freudenthal coordinate realization, with the remaining flatness input
stated as the displacement-filtered local-slot triple-sum angle target. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_dispFilteredLocalSlotTripleAngleSum
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hDisp :
      CanonicalPeriodicDispFilteredLocalSlotTripleAngleSumTarget Nx Ny Nz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_localSlotTripleAngleSum
    Nx Ny Nz hx hy hz hLocal
    (canonicalPeriodicLocalSlotTripleAngleSumTarget_of_dispFiltered
      Nx Ny Nz hDisp)

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
explicit Freudenthal coordinate realization, with the remaining flatness input
stated as the base-and-displacement filtered local-slot triple-sum angle
target. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_baseDispFilteredLocalSlotTripleAngleSum
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hBase :
      CanonicalPeriodicBaseDispFilteredLocalSlotTripleAngleSumTarget Nx Ny Nz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_dispFilteredLocalSlotTripleAngleSum
    Nx Ny Nz hx hy hz hLocal
    (canonicalPeriodicDispFilteredLocalSlotTripleAngleSumTarget_of_baseDispFiltered
      Nx Ny Nz hBase)

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
explicit Freudenthal coordinate realization, with the remaining flatness input
stated as the filtered incident typed cell/tetrahedron angle-sum target. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_incidentFilteredAngleSum
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hIncident : CanonicalPeriodicIncidentFilteredEdgeAngleSumTarget Nx Ny Nz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_directTypedAngleSum
    Nx Ny Nz hx hy hz hLocal
    (canonicalPeriodicDirectTypedEdgeAngleSumTarget_of_incidentFiltered
      Nx Ny Nz hIncident)

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
explicit Freudenthal coordinate realization, with the remaining flatness input
stated as the slot-witness filtered incident angle-sum target. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_slotWitnessFilteredAngleSum
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hSlot :
      CanonicalPeriodicSlotWitnessFilteredEdgeAngleSumTarget Nx Ny Nz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_incidentFilteredAngleSum
    Nx Ny Nz hx hy hz hLocal
    (canonicalPeriodicIncidentFilteredEdgeAngleSumTarget_of_slotWitnessFiltered
      Nx Ny Nz hSlot)

/-- Full nonlinear Regge finite aggregate in Dirichlet-energy form from the
explicit Freudenthal coordinate realization, with the remaining flatness input
stated as the geometric `localEdgeOf` filtered angle-sum target. -/
theorem canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_localEdgeOfFilteredAngleSum
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hEdgeOf :
      CanonicalPeriodicLocalEdgeOfFilteredEdgeAngleSumTarget Nx Ny Nz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  ∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ)))
                l
                (nhds
                  (∑ i : Fin n,
                    limitWeight i *
                      ((1 / 2) *
                        canonicalDirichletEnergy
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (probe i)))) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_tendsto_dirichlet_of_freudenthalRealization_slotWitnessFilteredAngleSum
    Nx Ny Nz hx hy hz hLocal
    (canonicalPeriodicSlotWitnessFilteredEdgeAngleSumTarget_of_localEdgeOfFiltered
      Nx Ny Nz hEdgeOf)

/-- Spacing-scaled finite residual from canonical second-order Regge aggregates
to a supplied fixed physical action.  This uses only the fixed-action `C a^2`
estimate in `D`; it does not assume continuity or homogeneity of the supplied
fixed action. -/
theorem CanonicalPeriodicFixedPhysicalActionComparisonData.variable_weighted_finite_probe_spacing_scaled_secondOrder_residual_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedPhysicalActionComparisonData l Nx Ny Nz hx hy hz)
    {n : ℕ}
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (weight : α → Fin n → ℝ)
    (limitWeight : Fin n → ℝ)
    (hWeight :
      ∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) :
    Filter.Tendsto
      (fun t : α =>
        (∑ i : Fin n,
          weight t i *
            reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (D.spacing t • probe i)) -
          ∑ i : Fin n,
            weight t i *
              D.fixedAction (D.spacing t • probe i))
      l (nhds 0) := by
  classical
  have hEnvelope :
      Filter.Tendsto
        (fun t : α => D.errorConstant t * D.spacing t ^ (2 : ℕ))
        l (nhds 0) := by
    apply squeeze_zero
    · intro t
      exact mul_nonneg (D.error_nonneg t) (sq_nonneg (D.spacing t))
    · intro t
      exact mul_le_mul_of_nonneg_right (D.error_bound t) (sq_nonneg (D.spacing t))
    · have hcont : Continuous (fun a : ℝ => D.errorBound * a ^ (2 : ℕ)) := by
        continuity
      have ht := hcont.tendsto (0 : ℝ)
      simpa using ht.comp D.spacing_tendsto_zero
  have hSum :
      Filter.Tendsto
        (fun t : α =>
          ∑ i : Fin n,
            weight t i *
              (reggeActionSecondOrder
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                (canonicalReggeHessian
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                  (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                (D.spacing t • probe i) -
              D.fixedAction (D.spacing t • probe i)))
        l (nhds 0) := by
    simpa using
      (tendsto_finset_sum (Finset.univ : Finset (Fin n))
        (f := fun i (t : α) =>
          weight t i *
            (reggeActionSecondOrder
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (canonicalReggeHessian
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
              (D.spacing t • probe i) -
            D.fixedAction (D.spacing t • probe i)))
        (a := fun _i => 0)
        (by
          intro i _hi
          have hAbs :
              Filter.Tendsto
                (fun t : α =>
                  |reggeActionSecondOrder
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (canonicalReggeHessian
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                    (D.spacing t • probe i) -
                    D.fixedAction (D.spacing t • probe i)|)
                l (nhds 0) := by
            apply squeeze_zero
            · intro t
              exact abs_nonneg _
            · intro t
              exact D.estimate t (D.spacing t • probe i)
            · exact hEnvelope
          have hScalar :
              Filter.Tendsto
                (fun t : α =>
                  reggeActionSecondOrder
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (canonicalReggeHessian
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK)
                    (D.spacing t • probe i) -
                  D.fixedAction (D.spacing t • probe i))
                l (nhds 0) := by
            apply tendsto_iff_dist_tendsto_zero.mpr
            simpa [Real.dist_eq] using hAbs
          simpa using (hWeight i).mul hScalar))
  simpa [Finset.sum_sub_distrib, mul_sub] using hSum

/-- Total finite variable-weight residual from full nonlinear Regge aggregates
to a supplied fixed physical action, for spacing-scaled probes.  This composes
the local nonlinear residual layer with the fixed-action `C a^2` comparison
layer.  The target remains finite and local; no global EH integral statement is
claimed here. -/
theorem CanonicalPeriodicFixedPhysicalActionComparisonData.variable_weighted_finite_probe_spacing_scaled_full_regge_residual_tendsto_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedPhysicalActionComparisonData l Nx Ny Nz hx hy hz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto
            (fun t : α =>
              (∑ i : Fin n,
                weight t i *
                  reggeAction
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (D.spacing t • probe i)) -
                ∑ i : Fin n,
                  weight t i *
                    D.fixedAction (D.spacing t • probe i))
            l (nhds 0) := by
  rcases canonicalPeriodicNonlinearAggregate_variable_weighted_finite_probe_spacing_scaled_to_secondOrder_residual_tendsto_zero
      Nx Ny Nz hx hy hz hLocal with
    ⟨r, C, hr, hC, hNonlinear⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n probe weight limitWeight hWeight
  have hFirst :=
    hNonlinear D.spacing probe weight limitWeight hWeight D.spacing_tendsto_zero
  have hSecond :=
    CanonicalPeriodicFixedPhysicalActionComparisonData.variable_weighted_finite_probe_spacing_scaled_secondOrder_residual_tendsto_zero
      Nx Ny Nz hx hy hz D probe weight limitWeight hWeight
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hFirst.add hSecond

/-- If the supplied fixed physical action is continuous at the zero
perturbation, the spacing-scaled finite full-Regge aggregate converges to the
corresponding zero-perturbation fixed-action aggregate.  This is the next
interface toward a fixed-continuum Riemann-sum statement; it only adds the
explicit continuity-at-zero hypothesis and still does not identify the global
Einstein-Hilbert integral. -/
theorem CanonicalPeriodicFixedPhysicalActionComparisonData.variable_weighted_finite_probe_spacing_scaled_full_regge_tendsto_fixed_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedPhysicalActionComparisonData l Nx Ny Nz hx hy hz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hFixedContinuousAtZero : ContinuousAt D.fixedAction 0) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto
            (fun t : α =>
              (∑ i : Fin n,
                weight t i *
                  reggeAction
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (D.spacing t • probe i)) -
                ∑ i : Fin n,
                  limitWeight i * D.fixedAction 0)
            l (nhds 0) := by
  classical
  rcases CanonicalPeriodicFixedPhysicalActionComparisonData.variable_weighted_finite_probe_spacing_scaled_full_regge_residual_tendsto_zero
      Nx Ny Nz hx hy hz D hLocal with
    ⟨r, C, hr, hC, hFullResidual⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n probe weight limitWeight hWeight
  have hResidual := hFullResidual probe weight limitWeight hWeight
  have hFixedAggregate :
      Filter.Tendsto
        (fun t : α =>
          ∑ i : Fin n,
            weight t i * D.fixedAction (D.spacing t • probe i))
        l (nhds (∑ i : Fin n, limitWeight i * D.fixedAction 0)) := by
    simpa using
      (tendsto_finset_sum (Finset.univ : Finset (Fin n))
        (f := fun i (t : α) =>
          weight t i * D.fixedAction (D.spacing t • probe i))
        (a := fun i => limitWeight i * D.fixedAction 0)
        (by
          intro i _hi
          have hScaledNorm :
              Filter.Tendsto
                (fun t : α => ‖D.spacing t • probe i‖) l (nhds 0) := by
            have hSpacingNorm :
                Filter.Tendsto (fun t : α => ‖D.spacing t‖) l (nhds (0 : ℝ)) := by
              simpa using D.spacing_tendsto_zero.norm
            have hMul :
                Filter.Tendsto (fun t : α => ‖D.spacing t‖ * ‖probe i‖) l
                  (nhds ((0 : ℝ) * ‖probe i‖)) :=
              hSpacingNorm.mul tendsto_const_nhds
            simpa [norm_smul] using hMul
          have hScaled :
              Filter.Tendsto (fun t : α => D.spacing t • probe i) l (nhds 0) := by
            apply Metric.tendsto_nhds.mpr
            intro ε hε
            have hDist := (Metric.tendsto_nhds.mp hScaledNorm) ε hε
            exact hDist.mono (fun t ht => by
              simpa [Real.dist_eq, dist_zero_right] using ht)
          have hAction :
              Filter.Tendsto
                (fun t : α => D.fixedAction (D.spacing t • probe i))
                l (nhds (D.fixedAction 0)) :=
            hFixedContinuousAtZero.tendsto.comp hScaled
          exact (hWeight i).mul hAction))
  let limitSum : ℝ := ∑ i : Fin n, limitWeight i * D.fixedAction 0
  have hConst : Filter.Tendsto (fun _t : α => limitSum) l (nhds limitSum) :=
    tendsto_const_nhds
  have hFixedResidual :
      Filter.Tendsto
        (fun t : α =>
          (∑ i : Fin n,
            weight t i * D.fixedAction (D.spacing t • probe i)) - limitSum)
        l (nhds 0) := by
    simpa [limitSum] using hFixedAggregate.sub hConst
  simpa [limitSum, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    hResidual.add hFixedResidual

/-- Zero-normalized form of the finite spacing-scaled full-Regge aggregate
limit.  If the supplied fixed physical action is continuous at zero and
vanishes at zero, the finite mesh-weighted full nonlinear Regge aggregate on
spacing-scaled probes tends to zero. -/
theorem CanonicalPeriodicFixedPhysicalActionComparisonData.variable_weighted_finite_probe_spacing_scaled_full_regge_tendsto_zero_of_fixed_zero
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (D : CanonicalPeriodicFixedPhysicalActionComparisonData l Nx Ny Nz hx hy hz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hFixedContinuousAtZero : ContinuousAt D.fixedAction 0)
    (hFixedZero : D.fixedAction 0 = 0) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (probe :
          Fin n →
            VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto
            (fun t : α =>
              ∑ i : Fin n,
                weight t i *
                  reggeAction
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                    (D.spacing t • probe i))
            l (nhds 0) := by
  rcases CanonicalPeriodicFixedPhysicalActionComparisonData.variable_weighted_finite_probe_spacing_scaled_full_regge_tendsto_fixed_zero
      Nx Ny Nz hx hy hz D hLocal hFixedContinuousAtZero with
    ⟨r, C, hr, hC, hFixedZeroLimit⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro n probe weight limitWeight hWeight
  simpa [hFixedZero] using hFixedZeroLimit probe weight limitWeight hWeight

theorem exactPeriodicFreudenthalComparisonCertificate_hessian_is_dirichlet
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz) :
    (exactPeriodicFreudenthalComparisonCertificate P).canonicalHessian_is_dirichlet :=
  canonicalHessianIsDirichlet_of_encodedPeriodicFreudenthal P

theorem exactPeriodicFreudenthalComparisonCertificate_physicalFiniteDifference_identification
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz) :
    PhysicalFiniteDifferenceDirichletTarget P
      (exactPeriodicFreudenthalComparisonCertificate P).physicalFiniteDifferenceAction :=
  (exactPeriodicFreudenthalComparisonCertificate P).physicalFiniteDifference_identification

def exactPhysicalSixTetModel_of_encodedPeriodicFreudenthal
    {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (P : EncodedPeriodicFreudenthalTorus Nx Ny Nz) :
    PhysicalSixTetCubicDirichletModel P.K P.hK :=
  physicalSixTetModel_of_periodicFreudenthalCertificate
    (exactPeriodicFreudenthalComparisonCertificate P)

theorem canonicalPeriodicEdgeStencilComparisonCertificate_physicalFiniteDifference
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    PhysicalFiniteDifferenceDirichletTarget
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz)
      (canonicalPeriodicEdgeStencilComparisonCertificate Nx Ny Nz hx hy hz).physicalFiniteDifferenceAction :=
  (canonicalPeriodicEdgeStencilComparisonCertificate Nx Ny Nz hx hy hz).physicalFiniteDifference_identification

def physicalSixTetModel_of_canonicalPeriodicEdgeStencil
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    PhysicalSixTetCubicDirichletModel
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK :=
  physicalSixTetModel_of_periodicFreudenthalCertificate
    (canonicalPeriodicEdgeStencilComparisonCertificate Nx Ny Nz hx hy hz)

end

end PhysicalSixTetCubicDirichletInstance
end Gravity
end IndisputableMonolith
