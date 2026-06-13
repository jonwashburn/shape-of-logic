import Mathlib
import IndisputableMonolith.Geometry.AffineIndepInterior
import IndisputableMonolith.Geometry.CofactorDerivatives
import IndisputableMonolith.Geometry.ReggeActionConcrete

/-!
# Smoothness Inputs for the Nonlinear Regge Action

The closed second-order component theorem works with an exact quadratic
truncation.  The full nonlinear action needs analytic input: the conformal
edge chart must stay in the nondegenerate tetrahedral cone, the arccos
arguments must stay away from `±1`, and the finite Regge action must be
smooth at the flat potential.

This module records those analytic requirements as a named configuration
rather than hiding them as axioms.  The lower-level polynomial and strict
interior facts already proved in the geometry stack are exposed as supporting
lemmas.
-/

namespace IndisputableMonolith
namespace Geometry
namespace ReggeActionSmoothness

open ReggeTriangulation3D
open ReggeHessian3D
open Triangulation3DConsistency
open ReggeActionConcrete
open DihedralCayleyMenger
open CofactorDerivatives
open AffineIndepInterior

noncomputable section

/-- Global zero-deficit flatness is an assembled-triangulation condition.  It
does not follow from local nondegeneracy of each tetrahedron. -/
def GlobalZeroDeficitAtFlat (K : Triangulation3D) : Prop :=
  ∀ e : Fin K.nE, deficitAngle K (zeroPotential K) e = 0

/-- Local analytic chart data supplied by Euclidean realizations of every
tetrahedron in the triangulation.  This is the local ingredient behind strict
arccos endpoint avoidance. -/
structure LocalAnalyticFlatChart (K : Triangulation3D) where
  realizedTet : ∀ _τ : Fin K.nT, RealizedNonDegenerateTet
  realizes_tet : ∀ τ : Fin K.nT, (realizedTet τ).tet = K.tet τ

theorem LocalAnalyticFlatChart.local_arccos_endpoint_free
    {K : Triangulation3D} (hChart : LocalAnalyticFlatChart K) :
    ∀ τ : Fin K.nT, ∀ f : Fin 6,
      dihedralCos3Sq ((K.tet τ).sqEdge) f ≠ -1 ∧
        dihedralCos3Sq ((K.tet τ).sqEdge) f ≠ 1 := by
  intro τ f
  have hstrict := (hChart.realizedTet τ).dihedralCos3_strict_interior f
  have ht : (hChart.realizedTet τ).tet = K.tet τ := hChart.realizes_tet τ
  have hstrict' :
      -1 < dihedralCos3Sq ((K.tet τ).sqEdge) f ∧
        dihedralCos3Sq ((K.tet τ).sqEdge) f < 1 := by
    simpa [dihedralCos3, ht] using hstrict
  exact DihedralDerivatives.arccos_endpoint_hypotheses_of_interior hstrict'.1 hstrict'.2

/-- Smoothness closure for the full nonlinear action from a local analytic
chart.  This is the next lower-level target: prove it from the explicit
`exp`/cofactor/`sqrt`/`arccos` chain. -/
structure ReggeActionContDiffFromLocalChart
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (_hChart : LocalAnalyticFlatChart K) where
  action_contDiff_at_zero :
    ContDiffAt ℝ (⊤ : ℕ∞) (reggeAction K hK) (zeroPotential K)

/-- A flat analytic configuration for the nonlinear Regge action.  The first
field is the arccos endpoint condition at the base point.  The second field is
the zero-deficit flatness condition.  The final field is the smoothness fact
needed to invoke Taylor theory for the full nonlinear action. -/
structure FlatConfiguration (K : Triangulation3D) (hK : IncidenceConsistent K) where
  local_arccos_endpoint_free :
    ∀ τ : Fin K.nT, ∀ f : Fin 6,
      dihedralCos3Sq ((K.tet τ).sqEdge) f ≠ -1 ∧
        dihedralCos3Sq ((K.tet τ).sqEdge) f ≠ 1
  flat_deficit_zero :
    ∀ e : Fin K.nE, deficitAngle K (zeroPotential K) e = 0
  action_contDiff_at_zero :
    ContDiffAt ℝ (⊤ : ℕ∞) (reggeAction K hK) (zeroPotential K)

/-- Construct the current flat-configuration package from local realized
tetrahedra, a separately stated global zero-deficit condition, and the
smoothness theorem for the local chart. -/
def flatConfiguration_of_localChart_zeroDeficit
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hChart : LocalAnalyticFlatChart K)
    (hZero : GlobalZeroDeficitAtFlat K)
    (hSmooth : ReggeActionContDiffFromLocalChart K hK hChart) :
    FlatConfiguration K hK where
  local_arccos_endpoint_free := hChart.local_arccos_endpoint_free
  flat_deficit_zero := hZero
  action_contDiff_at_zero := hSmooth.action_contDiff_at_zero

/-- Nondegenerate tetrahedra already give positive polynomial cofactor
denominators for every local dihedral angle. -/
theorem local_dihedralDenom3Poly_pos
    (K : Triangulation3D) (τ : Fin K.nT) (f : Fin 6) :
    0 < dihedralDenom3Poly ((K.tet τ).sqEdge) f :=
  dihedralDenom3Poly_pos_of_nonDegenerate (K.tet τ) f

/-- Nondegenerate tetrahedra already give nonzero polynomial cofactor
denominators for every local dihedral angle. -/
theorem local_dihedralDenom3Poly_ne_zero
    (K : Triangulation3D) (τ : Fin K.nT) (f : Fin 6) :
    dihedralDenom3Poly ((K.tet τ).sqEdge) f ≠ 0 :=
  ne_of_gt (local_dihedralDenom3Poly_pos K τ f)

theorem local_dihedralDenom3_ne_zero
    (K : Triangulation3D) (τ : Fin K.nT) (f : Fin 6) :
    dihedralDenom3 ((K.tet τ).sqEdge) f ≠ 0 := by
  rw [dihedralDenom3_eq_poly]
  exact local_dihedralDenom3Poly_ne_zero K τ f

theorem dihedralDenom3_continuousAt
    (a : CayleyMengerPolynomial.SqEdges) (f : Fin 6) :
    ContinuousAt (fun x : CayleyMengerPolynomial.SqEdges => dihedralDenom3 x f) a := by
  unfold dihedralDenom3
  let p := (DihedralCayleyMenger.oppositeCMVertices f).1
  let q := (DihedralCayleyMenger.oppositeCMVertices f).2
  have hp : ContinuousAt (fun x : CayleyMengerPolynomial.SqEdges =>
      CayleyMengerMatrix.cmCofactor3 x p p) a :=
    (CayleyMengerMatrix.cmCofactor3_contDiff 0 p p).continuous.continuousAt
  have hq : ContinuousAt (fun x : CayleyMengerPolynomial.SqEdges =>
      CayleyMengerMatrix.cmCofactor3 x q q) a :=
    (CayleyMengerMatrix.cmCofactor3_contDiff 0 q q).continuous.continuousAt
  simpa [p, q] using (hp.mul hq).sqrt

theorem dihedralCos3Sq_continuousAt_of_den_ne_zero
    (a : CayleyMengerPolynomial.SqEdges) (f : Fin 6)
    (hden : dihedralDenom3 a f ≠ 0) :
    ContinuousAt (fun x : CayleyMengerPolynomial.SqEdges => dihedralCos3Sq x f) a := by
  unfold dihedralCos3Sq
  exact (CayleyMengerMatrix.cmCofactor3_contDiff 0
      (DihedralCayleyMenger.oppositeCMVertices f).1
      (DihedralCayleyMenger.oppositeCMVertices f).2).continuous.continuousAt.div
    (dihedralDenom3_continuousAt a f) hden

theorem local_dihedralCos3Sq_continuousAt
    (K : Triangulation3D) (τ : Fin K.nT) (f : Fin 6) :
    ContinuousAt (fun x : CayleyMengerPolynomial.SqEdges => dihedralCos3Sq x f)
      ((K.tet τ).sqEdge) :=
  dihedralCos3Sq_continuousAt_of_den_ne_zero ((K.tet τ).sqEdge) f
    (local_dihedralDenom3_ne_zero K τ f)

theorem conformalLocalSqEdge_contDiff
    (K : Triangulation3D) (τ : Fin K.nT) (f : Fin 6) (n : ℕ∞) :
    ContDiff ℝ n (fun ξ : VertexPotential K => conformalLocalSqEdge K ξ τ f) := by
  unfold conformalLocalSqEdge
  fun_prop

theorem conformalLocalSqEdge_contDiffAt_zero
    (K : Triangulation3D) (τ : Fin K.nT) (f : Fin 6) (n : ℕ∞) :
    ContDiffAt ℝ n
      (fun ξ : VertexPotential K => conformalLocalSqEdge K ξ τ f)
      (zeroPotential K) :=
  (conformalLocalSqEdge_contDiff K τ f n).contDiffAt

theorem conformalTetSqEdges_contDiff
    (K : Triangulation3D) (τ : Fin K.nT) (n : ℕ∞) :
    ContDiff ℝ n (fun ξ : VertexPotential K => conformalTetSqEdges K ξ τ) := by
  rw [contDiff_pi]
  intro f
  exact conformalLocalSqEdge_contDiff K τ f n

theorem conformalTetSqEdges_zero
    (K : Triangulation3D) (τ : Fin K.nT) :
    conformalTetSqEdges K (zeroPotential K) τ = (K.tet τ).sqEdge := by
  funext f
  unfold conformalTetSqEdges conformalLocalSqEdge zeroPotential
  simp [Real.exp_zero]

theorem dihedralCos3Sq_conformal_continuousAt_zero
    (K : Triangulation3D) (τ : Fin K.nT) (f : Fin 6) :
    ContinuousAt (fun ξ : VertexPotential K =>
      dihedralCos3Sq (conformalTetSqEdges K ξ τ) f) (zeroPotential K) := by
  have hbase := local_dihedralCos3Sq_continuousAt K τ f
  have hchart : ContinuousAt (fun ξ : VertexPotential K =>
      conformalTetSqEdges K ξ τ) (zeroPotential K) :=
    (conformalTetSqEdges_contDiff K τ 0).continuous.continuousAt
  have hbase' : ContinuousAt
      (fun x : CayleyMengerPolynomial.SqEdges => dihedralCos3Sq x f)
      (conformalTetSqEdges K (zeroPotential K) τ) := by
    simpa [conformalTetSqEdges_zero K τ] using hbase
  exact ContinuousAt.comp
    (f := fun ξ : VertexPotential K => conformalTetSqEdges K ξ τ)
    (g := fun x : CayleyMengerPolynomial.SqEdges => dihedralCos3Sq x f)
    (x := zeroPotential K)
    hbase' hchart

theorem cmCofactor3_conformal_contDiff
    (K : Triangulation3D) (τ : Fin K.nT) (r c : Fin 5) (n : ℕ∞) :
    ContDiff ℝ n (fun ξ : VertexPotential K =>
      CayleyMengerMatrix.cmCofactor3 (conformalTetSqEdges K ξ τ) r c) :=
  (CayleyMengerMatrix.cmCofactor3_contDiff n r c).comp
    (conformalTetSqEdges_contDiff K τ n)

theorem cmCofactor3_conformal_contDiffAt_zero
    (K : Triangulation3D) (τ : Fin K.nT) (r c : Fin 5) (n : ℕ∞) :
    ContDiffAt ℝ n (fun ξ : VertexPotential K =>
      CayleyMengerMatrix.cmCofactor3 (conformalTetSqEdges K ξ τ) r c)
      (zeroPotential K) :=
  (cmCofactor3_conformal_contDiff K τ r c n).contDiffAt

theorem dihedralDenom3_conformal_contDiffAt_zero
    (K : Triangulation3D) (τ : Fin K.nT) (f : Fin 6) (n : ℕ∞) :
    ContDiffAt ℝ n (fun ξ : VertexPotential K =>
      dihedralDenom3 (conformalTetSqEdges K ξ τ) f) (zeroPotential K) := by
  unfold dihedralDenom3
  let p := (DihedralCayleyMenger.oppositeCMVertices f).1
  let q := (DihedralCayleyMenger.oppositeCMVertices f).2
  have hp := cmCofactor3_conformal_contDiffAt_zero K τ p p n
  have hq := cmCofactor3_conformal_contDiffAt_zero K τ q q n
  have hprod : ContDiffAt ℝ n (fun ξ : VertexPotential K =>
      CayleyMengerMatrix.cmCofactor3 (conformalTetSqEdges K ξ τ) p p *
        CayleyMengerMatrix.cmCofactor3 (conformalTetSqEdges K ξ τ) q q)
      (zeroPotential K) :=
    hp.mul hq
  have hne :
      CayleyMengerMatrix.cmCofactor3 (conformalTetSqEdges K (zeroPotential K) τ) p p *
        CayleyMengerMatrix.cmCofactor3 (conformalTetSqEdges K (zeroPotential K) τ) q q ≠ 0 := by
    have hden := local_dihedralDenom3_ne_zero K τ f
    unfold dihedralDenom3 at hden
    intro hprod_zero
    apply hden
    rw [conformalTetSqEdges_zero K τ] at hprod_zero
    simp [p, q, hprod_zero]
  simpa [p, q] using hprod.sqrt hne

theorem dihedralCos3Sq_conformal_contDiffAt_zero
    (K : Triangulation3D) (τ : Fin K.nT) (f : Fin 6) (n : ℕ∞) :
    ContDiffAt ℝ n (fun ξ : VertexPotential K =>
      dihedralCos3Sq (conformalTetSqEdges K ξ τ) f) (zeroPotential K) := by
  unfold dihedralCos3Sq
  let p := (DihedralCayleyMenger.oppositeCMVertices f).1
  let q := (DihedralCayleyMenger.oppositeCMVertices f).2
  have hnum := cmCofactor3_conformal_contDiffAt_zero K τ p q n
  have hden := dihedralDenom3_conformal_contDiffAt_zero K τ f n
  have hden_ne :
      dihedralDenom3 (conformalTetSqEdges K (zeroPotential K) τ) f ≠ 0 := by
    simpa [conformalTetSqEdges_zero K τ] using local_dihedralDenom3_ne_zero K τ f
  simpa [p, q] using hnum.div hden hden_ne

theorem tetDihedralAngleUnderConformal_contDiffAt_zero
    (K : Triangulation3D) (τ : Fin K.nT) (f : Fin 6) (n : ℕ∞)
    (hEndpoint :
      dihedralCos3Sq ((K.tet τ).sqEdge) f ≠ -1 ∧
        dihedralCos3Sq ((K.tet τ).sqEdge) f ≠ 1) :
    ContDiffAt ℝ n (fun ξ : VertexPotential K =>
      tetDihedralAngleUnderConformal K ξ τ f) (zeroPotential K) := by
  unfold tetDihedralAngleUnderConformal DihedralDerivatives.dihedralAngle3Sq
  have hcos := dihedralCos3Sq_conformal_contDiffAt_zero K τ f n
  have hm :
      dihedralCos3Sq (conformalTetSqEdges K (zeroPotential K) τ) f ≠ -1 := by
    simpa [conformalTetSqEdges_zero K τ] using hEndpoint.1
  have hp :
      dihedralCos3Sq (conformalTetSqEdges K (zeroPotential K) τ) f ≠ 1 := by
    simpa [conformalTetSqEdges_zero K τ] using hEndpoint.2
  have hacos : ContDiffAt ℝ n Real.arccos
      (dihedralCos3Sq (conformalTetSqEdges K (zeroPotential K) τ) f) :=
    Real.contDiffAt_arccos hm hp
  simpa [Function.comp_def] using
    (ContDiffAt.comp (x := zeroPotential K) hacos hcos)

theorem localDeficitAngleContribution_contDiffAt_zero
    (K : Triangulation3D) (e : Fin K.nE) (τ : Fin K.nT) (n : ℕ∞)
    (hEndpoint :
      ∀ f : Fin 6,
        dihedralCos3Sq ((K.tet τ).sqEdge) f ≠ -1 ∧
          dihedralCos3Sq ((K.tet τ).sqEdge) f ≠ 1) :
    ContDiffAt ℝ n (fun ξ : VertexPotential K =>
      localDeficitAngleContribution K ξ e τ) (zeroPotential K) := by
  unfold localDeficitAngleContribution
  cases h : K.edgeInTet e τ with
  | none =>
      simpa [h]
        using (contDiffAt_const :
          ContDiffAt ℝ n (fun _ξ : VertexPotential K => (0 : ℝ)) (zeroPotential K))
  | some f =>
      simpa [h] using tetDihedralAngleUnderConformal_contDiffAt_zero
        K τ f n (hEndpoint f)

theorem deficitAngle_contDiffAt_zero
    (K : Triangulation3D) (e : Fin K.nE) (n : ℕ∞)
    (hEndpoint :
      ∀ τ : Fin K.nT, ∀ f : Fin 6,
        dihedralCos3Sq ((K.tet τ).sqEdge) f ≠ -1 ∧
          dihedralCos3Sq ((K.tet τ).sqEdge) f ≠ 1) :
    ContDiffAt ℝ n (fun ξ : VertexPotential K => deficitAngle K ξ e)
      (zeroPotential K) := by
  unfold deficitAngle
  have hsum : ContDiffAt ℝ n
      (fun ξ : VertexPotential K =>
        ∑ τ : Fin K.nT, localDeficitAngleContribution K ξ e τ)
      (zeroPotential K) := by
    simpa using
      (ContDiffAt.sum
        (s := Finset.univ)
        (f := fun τ ξ => localDeficitAngleContribution K ξ e τ)
        (x := zeroPotential K)
        (fun τ _ => localDeficitAngleContribution_contDiffAt_zero
          K e τ n (hEndpoint τ)))
  exact (contDiffAt_const.sub hsum)

theorem hingeMeasureUnderConformal_contDiff
    (K : Triangulation3D) (hK : IncidenceConsistent K) (e : Fin K.nE) (n : ℕ∞) :
    ContDiff ℝ n (fun ξ : VertexPotential K =>
      hingeMeasureUnderConformal K hK ξ e) := by
  unfold hingeMeasureUnderConformal
  fun_prop

theorem hingeMeasureUnderConformal_contDiffAt_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K) (e : Fin K.nE) (n : ℕ∞) :
    ContDiffAt ℝ n (fun ξ : VertexPotential K =>
      hingeMeasureUnderConformal K hK ξ e) (zeroPotential K) :=
  (hingeMeasureUnderConformal_contDiff K hK e n).contDiffAt

theorem reggeAction_contDiffAt_zero_of_endpoint_free
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hEndpoint :
      ∀ τ : Fin K.nT, ∀ f : Fin 6,
        dihedralCos3Sq ((K.tet τ).sqEdge) f ≠ -1 ∧
          dihedralCos3Sq ((K.tet τ).sqEdge) f ≠ 1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (reggeAction K hK) (zeroPotential K) := by
  unfold reggeAction
  simpa using
    (ContDiffAt.sum
      (s := Finset.univ)
      (f := fun e ξ =>
        hingeMeasureUnderConformal K hK ξ e * deficitAngle K ξ e)
      (x := zeroPotential K)
      (fun e _ =>
        (hingeMeasureUnderConformal_contDiffAt_zero K hK e (⊤ : ℕ∞)).mul
          (deficitAngle_contDiffAt_zero K e ⊤ hEndpoint)))

theorem reggeAction_contDiffAt_zero_of_localChart
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hChart : LocalAnalyticFlatChart K) :
    ContDiffAt ℝ (⊤ : ℕ∞) (reggeAction K hK) (zeroPotential K) :=
  reggeAction_contDiffAt_zero_of_endpoint_free K hK
    hChart.local_arccos_endpoint_free

def reggeActionContDiffFromLocalChart_of_localChart
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hChart : LocalAnalyticFlatChart K) :
    ReggeActionContDiffFromLocalChart K hK hChart where
  action_contDiff_at_zero :=
    reggeAction_contDiffAt_zero_of_localChart K hK hChart

/-- Phase-A smoothness theorem for the nonlinear action, conditional on the
named flat analytic configuration. -/
theorem reggeAction_contDiff_at_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK) :
    ContDiffAt ℝ (⊤ : ℕ∞) (reggeAction K hK) (zeroPotential K) :=
  h_flat.action_contDiff_at_zero

/-- Flat configurations have zero deficit at the base potential. -/
theorem deficitAngle_zero_of_flat
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK) :
    ∀ e : Fin K.nE, deficitAngle K (zeroPotential K) e = 0 :=
  h_flat.flat_deficit_zero

end

end ReggeActionSmoothness
end Geometry
end IndisputableMonolith
