import Mathlib
import IndisputableMonolith.Geometry.ReggeActionSmoothness
import IndisputableMonolith.Geometry.SchlaefliTetrahedronProof
import IndisputableMonolith.Geometry.SchlaefliTriangulation3D

/-!
# First Variation of the Nonlinear Regge Action

The target theorem is the vanishing of the first variation of the full
nonlinear Regge action at the flat conformal potential.  The geometric proof
is Schläfli cancellation plus zero deficit.  This module records the exact
analytic statement and the named input needed until the full derivative
calculation is expanded from the closed-form local Schläfli identities.
-/

namespace IndisputableMonolith
namespace Geometry
namespace ReggeActionFirstVariation

open ReggeTriangulation3D
open ReggeHessian3D
open Triangulation3DConsistency
open ReggeActionConcrete
open ReggeActionSmoothness
open SchlaefliTetrahedronProof
open SchlaefliTriangulation3D
open DihedralCayleyMenger

noncomputable section

/-- The line through the flat potential in direction `η`.  This local copy
keeps the first-variation module independent of the second-variation module. -/
def linePotential (K : Triangulation3D) (η : VertexPotential K) (t : ℝ) :
    VertexPotential K :=
  fun i => t * η i

theorem linePotential_zero
    (K : Triangulation3D) (η : VertexPotential K) :
    linePotential K η 0 = zeroPotential K := by
  funext i
  simp [linePotential, zeroPotential]

/-- Every vector in `Fin 6 → ℝ` is the sum of its coordinate basis pieces,
and a continuous linear functional is determined by those six values. -/
theorem continuousLinearMap_apply_eq_sum_single
    (L : (Fin 6 → ℝ) →L[ℝ] ℝ) (v : Fin 6 → ℝ) :
    L v = ∑ k : Fin 6, v k * L (Pi.single (M := fun _ : Fin 6 => ℝ) k (1 : ℝ)) := by
  have hv : (∑ k : Fin 6, Pi.single (M := fun _ : Fin 6 => ℝ) k (v k)) = v :=
    Finset.univ_sum_single v
  calc
    L v = L (∑ k : Fin 6, Pi.single (M := fun _ : Fin 6 => ℝ) k (v k)) := by rw [hv]
    _ = ∑ k : Fin 6, L (Pi.single (M := fun _ : Fin 6 => ℝ) k (v k)) := by
      rw [map_sum]
    _ = ∑ k : Fin 6, v k * L (Pi.single (M := fun _ : Fin 6 => ℝ) k (1 : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      have hsingle :
          Pi.single (M := fun _ : Fin 6 => ℝ) k (v k) =
            v k • Pi.single (M := fun _ : Fin 6 => ℝ) k (1 : ℝ) := by
        funext i
        by_cases hik : i = k
        · subst i
          simp [Pi.single_eq_same]
        · simp [hik]
      rw [hsingle, map_smul]
      simp [smul_eq_mul]

theorem functionUpdate_hasDerivAt_single
    (a : Fin 6 → ℝ) (k : Fin 6) :
    HasDerivAt (fun t : ℝ => Function.update a k t)
      (Pi.single (M := fun _ : Fin 6 => ℝ) k (1 : ℝ)) (a k) := by
  rw [hasDerivAt_pi]
  intro i
  by_cases hik : i = k
  · subst i
    simpa [Function.update] using (hasDerivAt_id (a k))
  · have hconst : (fun t : ℝ => Function.update a k t i) = fun _t : ℝ => a i := by
      funext t
      simp [Function.update, hik]
    rw [hconst]
    simpa [Pi.single_eq_of_ne hik] using hasDerivAt_const (a k) (a i)

/-- Directional derivative of a local conformal squared-edge coordinate at the
flat potential. -/
def conformalLocalSqEdgeDirectionalDeriv
    (K : Triangulation3D) (η : VertexPotential K)
    (τ : Fin K.nT) (f : Fin 6) : ℝ :=
  let uv := ReggeRigorousFoundation.edgeVertices f
  (K.tet τ).sqEdge f * (η (K.tetVerts τ uv.1) + η (K.tetVerts τ uv.2))

theorem conformalLocalSqEdge_hasDerivAt_line_zero
    (K : Triangulation3D) (η : VertexPotential K)
    (τ : Fin K.nT) (f : Fin 6) :
    HasDerivAt
      (fun t : ℝ => conformalLocalSqEdge K (linePotential K η t) τ f)
      (conformalLocalSqEdgeDirectionalDeriv K η τ f) 0 := by
  unfold conformalLocalSqEdge conformalLocalSqEdgeDirectionalDeriv linePotential
  let uv := ReggeRigorousFoundation.edgeVertices f
  have hlin : HasDerivAt
      (fun t : ℝ => t * η (K.tetVerts τ uv.1) + t * η (K.tetVerts τ uv.2))
      (η (K.tetVerts τ uv.1) + η (K.tetVerts τ uv.2)) 0 := by
    have h1 : HasDerivAt
        (fun t : ℝ => t * η (K.tetVerts τ uv.1))
        (η (K.tetVerts τ uv.1)) 0 :=
      by simpa using (hasDerivAt_id 0).mul_const (η (K.tetVerts τ uv.1))
    have h2 : HasDerivAt
        (fun t : ℝ => t * η (K.tetVerts τ uv.2))
        (η (K.tetVerts τ uv.2)) 0 :=
      by simpa using (hasDerivAt_id 0).mul_const (η (K.tetVerts τ uv.2))
    exact h1.add h2
  have hexp : HasDerivAt
      (fun t : ℝ =>
        Real.exp (t * η (K.tetVerts τ uv.1) + t * η (K.tetVerts τ uv.2)))
      (η (K.tetVerts τ uv.1) + η (K.tetVerts τ uv.2)) 0 := by
    have h := (Real.hasDerivAt_exp
      (0 * η (K.tetVerts τ uv.1) + 0 * η (K.tetVerts τ uv.2))).comp 0 hlin
    simpa [Real.exp_zero] using h
  simpa [uv, Real.exp_zero, mul_comm, mul_left_comm, mul_assoc] using
    hexp.const_mul ((K.tet τ).sqEdge f)

theorem conformalTetSqEdges_hasDerivAt_line_zero
    (K : Triangulation3D) (η : VertexPotential K) (τ : Fin K.nT) :
    HasDerivAt
      (fun t : ℝ => conformalTetSqEdges K (linePotential K η t) τ)
      (fun f : Fin 6 => conformalLocalSqEdgeDirectionalDeriv K η τ f) 0 := by
  rw [hasDerivAt_pi]
  intro f
  exact conformalLocalSqEdge_hasDerivAt_line_zero K η τ f

theorem dihedralDenom3_contDiffAt_nonDegenerate
    (T : ReggeRigorousFoundation.NonDegenerateTet) (f : Fin 6) (n : ℕ∞) :
    ContDiffAt ℝ n (fun a : CayleyMengerPolynomial.SqEdges => dihedralDenom3 a f)
      T.sqEdge := by
  unfold dihedralDenom3
  let p := (oppositeCMVertices f).1
  let q := (oppositeCMVertices f).2
  have hpp : ContDiffAt ℝ n
      (fun a : CayleyMengerPolynomial.SqEdges => CayleyMengerMatrix.cmCofactor3 a p p)
      T.sqEdge :=
    (CayleyMengerMatrix.cmCofactor3_contDiff n p p).contDiffAt
  have hqq : ContDiffAt ℝ n
      (fun a : CayleyMengerPolynomial.SqEdges => CayleyMengerMatrix.cmCofactor3 a q q)
      T.sqEdge :=
    (CayleyMengerMatrix.cmCofactor3_contDiff n q q).contDiffAt
  have hprod : ContDiffAt ℝ n (fun a : CayleyMengerPolynomial.SqEdges =>
      CayleyMengerMatrix.cmCofactor3 a p p * CayleyMengerMatrix.cmCofactor3 a q q)
      T.sqEdge :=
    hpp.mul hqq
  have hden : dihedralDenom3 T.sqEdge f ≠ 0 := by
    rw [CofactorDerivatives.dihedralDenom3_eq_poly]
    exact CofactorDerivatives.dihedralDenom3Poly_ne_zero_of_nonDegenerate T f
  have hprod_ne :
      CayleyMengerMatrix.cmCofactor3 T.sqEdge p p *
        CayleyMengerMatrix.cmCofactor3 T.sqEdge q q ≠ 0 := by
    intro hzero
    apply hden
    simp [dihedralDenom3, p, q, hzero]
  simpa [p, q] using hprod.sqrt hprod_ne

theorem dihedralCos3Sq_contDiffAt_nonDegenerate
    (T : ReggeRigorousFoundation.NonDegenerateTet) (f : Fin 6) (n : ℕ∞) :
    ContDiffAt ℝ n (fun a : CayleyMengerPolynomial.SqEdges => dihedralCos3Sq a f)
      T.sqEdge := by
  unfold dihedralCos3Sq
  let p := (oppositeCMVertices f).1
  let q := (oppositeCMVertices f).2
  have hnum : ContDiffAt ℝ n
      (fun a : CayleyMengerPolynomial.SqEdges => CayleyMengerMatrix.cmCofactor3 a p q)
      T.sqEdge :=
    (CayleyMengerMatrix.cmCofactor3_contDiff n p q).contDiffAt
  have hden := dihedralDenom3_contDiffAt_nonDegenerate T f n
  have hden_ne : dihedralDenom3 T.sqEdge f ≠ 0 := by
    rw [CofactorDerivatives.dihedralDenom3_eq_poly]
    exact CofactorDerivatives.dihedralDenom3Poly_ne_zero_of_nonDegenerate T f
  simpa [p, q] using hnum.div hden hden_ne

theorem dihedralAngle3Sq_contDiffAt_nonDegenerate
    (T : ReggeRigorousFoundation.NonDegenerateTet) (f : Fin 6) (n : ℕ∞)
    (hEndpoint : dihedralCos3Sq T.sqEdge f ≠ -1 ∧ dihedralCos3Sq T.sqEdge f ≠ 1) :
    ContDiffAt ℝ n
      (fun a : CayleyMengerPolynomial.SqEdges => DihedralDerivatives.dihedralAngle3Sq a f)
      T.sqEdge := by
  unfold DihedralDerivatives.dihedralAngle3Sq
  have hcos := dihedralCos3Sq_contDiffAt_nonDegenerate T f n
  have hacos : ContDiffAt ℝ n Real.arccos (dihedralCos3Sq T.sqEdge f) :=
    Real.contDiffAt_arccos hEndpoint.1 hEndpoint.2
  simpa [Function.comp_def] using
    (ContDiffAt.comp (x := T.sqEdge) hacos hcos)

theorem fderiv_dihedralAngle3Sq_apply_single
    (T : ReggeRigorousFoundation.NonDegenerateTet) (f k : Fin 6)
    (hEndpoint : dihedralCos3Sq T.sqEdge f ≠ -1 ∧ dihedralCos3Sq T.sqEdge f ≠ 1) :
    (fderiv ℝ
      (fun a : CayleyMengerPolynomial.SqEdges => DihedralDerivatives.dihedralAngle3Sq a f)
      T.sqEdge) (Pi.single (M := fun _ : Fin 6 => ℝ) k (1 : ℝ)) =
      dihedralClosedDerivSq T f k := by
  have hAngle : ContDiffAt ℝ 1
      (fun a : CayleyMengerPolynomial.SqEdges => DihedralDerivatives.dihedralAngle3Sq a f)
      T.sqEdge :=
    dihedralAngle3Sq_contDiffAt_nonDegenerate T f 1 hEndpoint
  have hDiff : DifferentiableAt ℝ
      (fun a : CayleyMengerPolynomial.SqEdges => DihedralDerivatives.dihedralAngle3Sq a f)
      T.sqEdge :=
    hAngle.differentiableAt (by simp)
  have hF : HasFDerivAt
      (fun a : CayleyMengerPolynomial.SqEdges => DihedralDerivatives.dihedralAngle3Sq a f)
      (fderiv ℝ
        (fun a : CayleyMengerPolynomial.SqEdges => DihedralDerivatives.dihedralAngle3Sq a f)
        T.sqEdge)
      T.sqEdge :=
    hDiff.hasFDerivAt
  have hbase : Function.update T.sqEdge k (T.sqEdge k) = T.sqEdge := by
    funext i
    by_cases hik : i = k <;> simp [Function.update, hik]
  have hF' : HasFDerivAt
      (fun a : CayleyMengerPolynomial.SqEdges => DihedralDerivatives.dihedralAngle3Sq a f)
      (fderiv ℝ
        (fun a : CayleyMengerPolynomial.SqEdges => DihedralDerivatives.dihedralAngle3Sq a f)
        T.sqEdge)
      (Function.update T.sqEdge k (T.sqEdge k)) := by
    simpa [hbase] using hF
  have hupdate := functionUpdate_hasDerivAt_single T.sqEdge k
  have hcomp := HasFDerivAt.comp_hasDerivAt
    (x := T.sqEdge k)
    (f := fun t : ℝ => Function.update T.sqEdge k t)
    (l := fun a : CayleyMengerPolynomial.SqEdges => DihedralDerivatives.dihedralAngle3Sq a f)
    hF' hupdate
  let p := (oppositeCMVertices f).1
  let q := (oppositeCMVertices f).2
  have hden : dihedralDenom3 T.sqEdge f ≠ 0 := by
    rw [CofactorDerivatives.dihedralDenom3_eq_poly]
    exact CofactorDerivatives.dihedralDenom3Poly_ne_zero_of_nonDegenerate T f
  have hprod_ne :
      CayleyMengerMatrix.cmCofactor3 T.sqEdge p p *
        CayleyMengerMatrix.cmCofactor3 T.sqEdge q q ≠ 0 := by
    intro hzero
    apply hden
    simp [dihedralDenom3, p, q, hzero]
  have hcoord :=
    DihedralDerivatives.hasDerivAt_dihedralAngle3Sq_explicit
      T.sqEdge f k hprod_ne hden hEndpoint.1 hEndpoint.2
  have hunique := hcomp.unique hcoord
  simpa [dihedralClosedDerivSq, Function.comp_def] using hunique

/-- Directional derivative of the conformal hinge length at the flat
potential. -/
def hingeMeasureDirectionalDeriv
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (η : VertexPotential K) (e : Fin K.nE) : ℝ :=
  let uv := K.edgeVerts e
  Real.sqrt (hK.globalSqEdge e) * ((η uv.1 + η uv.2) / 2)

theorem hingeMeasureUnderConformal_hasDerivAt_line_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (η : VertexPotential K) (e : Fin K.nE) :
    HasDerivAt
      (fun t : ℝ => hingeMeasureUnderConformal K hK (linePotential K η t) e)
      (hingeMeasureDirectionalDeriv K hK η e) 0 := by
  unfold hingeMeasureUnderConformal hingeMeasureDirectionalDeriv linePotential
  let uv := K.edgeVerts e
  have hlin : HasDerivAt
      (fun t : ℝ => (t * η uv.1 + t * η uv.2) / 2)
      ((η uv.1 + η uv.2) / 2) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * η uv.1) (η uv.1) 0 :=
      by simpa using (hasDerivAt_id 0).mul_const (η uv.1)
    have h2 : HasDerivAt (fun t : ℝ => t * η uv.2) (η uv.2) 0 :=
      by simpa using (hasDerivAt_id 0).mul_const (η uv.2)
    simpa [add_div] using (h1.add h2).div_const 2
  have hexp : HasDerivAt
      (fun t : ℝ => Real.exp ((t * η uv.1 + t * η uv.2) / 2))
      ((η uv.1 + η uv.2) / 2) 0 := by
    have h := (Real.hasDerivAt_exp ((0 * η uv.1 + 0 * η uv.2) / 2)).comp 0 hlin
    simpa [Real.exp_zero] using h
  simpa [uv, Real.exp_zero, mul_comm, mul_left_comm, mul_assoc] using
    hexp.const_mul (Real.sqrt (hK.globalSqEdge e))

theorem linePotential_hasDerivAt_zero
    (K : Triangulation3D) (η : VertexPotential K) :
    HasDerivAt (fun t : ℝ => linePotential K η t) η 0 := by
  rw [hasDerivAt_pi]
  intro i
  unfold linePotential
  simpa using (hasDerivAt_id 0).mul_const (η i)

theorem reggeAction_along_line_hasDerivAt_fderiv
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK) (η : VertexPotential K) :
    HasDerivAt
      (fun t : ℝ => reggeAction K hK (linePotential K η t))
      ((fderiv ℝ (reggeAction K hK) (zeroPotential K)) η) 0 := by
  have hdiff : DifferentiableAt ℝ (reggeAction K hK) (zeroPotential K) :=
    h_flat.action_contDiff_at_zero.differentiableAt (by simp)
  have hF : HasFDerivAt (reggeAction K hK)
      (fderiv ℝ (reggeAction K hK) (zeroPotential K)) (zeroPotential K) :=
    hdiff.hasFDerivAt
  have hF' : HasFDerivAt (reggeAction K hK)
      (fderiv ℝ (reggeAction K hK) (zeroPotential K)) (linePotential K η 0) := by
    simpa [linePotential_zero K η] using hF
  have hline := linePotential_hasDerivAt_zero K η
  have hcomp := HasFDerivAt.comp_hasDerivAt
    (x := (0 : ℝ))
    (f := fun t : ℝ => linePotential K η t)
    (l := reggeAction K hK)
    hF' hline
  simpa [Function.comp_def, linePotential_zero K η] using hcomp

/-- The nonlinear Regge action is critical at the flat potential. -/
def ReggeActionCriticalAtZero
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  fderiv ℝ (reggeAction K hK) (zeroPotential K) = 0

/-- Directional form of criticality, useful while deriving the first
variation by differentiating along lines. -/
def ReggeActionDirectionalCriticalAtZero
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ η : VertexPotential K,
    (fderiv ℝ (reggeAction K hK) (zeroPotential K)) η = 0

theorem reggeActionCriticalAtZero_of_directional
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hdir : ReggeActionDirectionalCriticalAtZero K hK) :
    ReggeActionCriticalAtZero K hK := by
  unfold ReggeActionCriticalAtZero
  ext η
  exact hdir η

/-- Explicit first-variation formula in directional form.  The hard analytic
work left in the nonlinear action is to derive this formula by differentiating
the hinge and dihedral terms and applying global Schläfli to the angle term. -/
structure ReggeActionFirstVariationFormula
    (K : Triangulation3D) (hK : IncidenceConsistent K) where
  firstVariation_formula :
    ∀ η : VertexPotential K,
      (fderiv ℝ (reggeAction K hK) (zeroPotential K)) η =
        ∑ e : Fin K.nE,
          hingeMeasureDirectionalDeriv K hK η e *
            deficitAngle K (zeroPotential K) e

/-- Directional first-variation formula along every line through the flat
potential.  This is the form produced directly by one-variable product-rule
calculations. -/
structure ReggeActionDirectionalFirstVariationFormula
    (K : Triangulation3D) (hK : IncidenceConsistent K) where
  directional_formula :
    ∀ η : VertexPotential K,
      HasDerivAt
        (fun t : ℝ => reggeAction K hK (linePotential K η t))
        (∑ e : Fin K.nE,
          hingeMeasureDirectionalDeriv K hK η e *
            deficitAngle K (zeroPotential K) e) 0

/-- Local dihedral-angle directional derivatives under the conformal ansatz.
This is the precise local cofactor/arccos derivative target left to prove. -/
structure LocalDihedralDirectionalDerivativePackage
    (K : Triangulation3D) where
  angleDeriv : VertexPotential K → Fin K.nT → Fin 6 → ℝ
  angle_hasDerivAt :
    ∀ (η : VertexPotential K) (τ : Fin K.nT) (f : Fin 6),
      HasDerivAt
        (fun t : ℝ => tetDihedralAngleUnderConformal K (linePotential K η t) τ f)
        (angleDeriv η τ f) 0

def localDihedralDirectionalDerivativePackage_of_flat
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK) :
    LocalDihedralDirectionalDerivativePackage K where
  angleDeriv := fun η τ f =>
    deriv (fun t : ℝ => tetDihedralAngleUnderConformal K (linePotential K η t) τ f) 0
  angle_hasDerivAt := by
    intro η τ f
    have hAngle : ContDiffAt ℝ 1
        (fun ξ : VertexPotential K => tetDihedralAngleUnderConformal K ξ τ f)
        (zeroPotential K) :=
      ReggeActionSmoothness.tetDihedralAngleUnderConformal_contDiffAt_zero
        K τ f 1 (h_flat.local_arccos_endpoint_free τ f)
    have hDiffAt : DifferentiableAt ℝ
        (fun ξ : VertexPotential K => tetDihedralAngleUnderConformal K ξ τ f)
        (zeroPotential K) :=
      hAngle.differentiableAt (by simp)
    have hF : HasFDerivAt
        (fun ξ : VertexPotential K => tetDihedralAngleUnderConformal K ξ τ f)
        (fderiv ℝ (fun ξ : VertexPotential K => tetDihedralAngleUnderConformal K ξ τ f)
          (zeroPotential K))
        (zeroPotential K) :=
      hDiffAt.hasFDerivAt
    have hF' : HasFDerivAt
        (fun ξ : VertexPotential K => tetDihedralAngleUnderConformal K ξ τ f)
        (fderiv ℝ (fun ξ : VertexPotential K => tetDihedralAngleUnderConformal K ξ τ f)
          (zeroPotential K))
        (linePotential K η 0) := by
      simpa [linePotential_zero K η] using hF
    have hline := linePotential_hasDerivAt_zero K η
    have hcomp := HasFDerivAt.comp_hasDerivAt
      (x := (0 : ℝ))
      (f := fun t : ℝ => linePotential K η t)
      (l := fun ξ : VertexPotential K => tetDihedralAngleUnderConformal K ξ τ f)
      hF' hline
    convert hcomp using 1
    exact hcomp.deriv

/-- Directional derivative of the local edge length `sqrt a_f` induced by a
vertex-conformal potential direction. -/
def localEdgeLengthDirectionalDeriv
    (K : Triangulation3D) (η : VertexPotential K)
    (τ : Fin K.nT) (f : Fin 6) : ℝ :=
  let uv := ReggeRigorousFoundation.edgeVertices f
  Real.sqrt ((K.tet τ).sqEdge f) *
    ((η (K.tetVerts τ uv.1) + η (K.tetVerts τ uv.2)) / 2)

/-- The angle derivative predicted by the local edge-length chain rule and the
closed Schläfli derivative data. -/
def localAngleLengthChainDeriv
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (η : VertexPotential K) (τ : Fin K.nT) (f : Fin 6) : ℝ :=
  ∑ k : Fin 6,
    ((triangulationSchlaefliData_of_incidence K hK).tetData τ).dihedralDeriv f k *
      localEdgeLengthDirectionalDeriv K η τ k

/-- The same local angle derivative written in squared-edge coordinates. -/
def localAngleSqEdgeChainDeriv
    (K : Triangulation3D) (η : VertexPotential K)
    (τ : Fin K.nT) (f : Fin 6) : ℝ :=
  ∑ k : Fin 6,
    dihedralClosedDerivSq (K.tet τ) f k *
      conformalLocalSqEdgeDirectionalDeriv K η τ k

theorem localAngleLengthChainDeriv_eq_sqEdgeChainDeriv
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (η : VertexPotential K) (τ : Fin K.nT) (f : Fin 6) :
    localAngleLengthChainDeriv K hK η τ f =
      localAngleSqEdgeChainDeriv K η τ f := by
  unfold localAngleLengthChainDeriv localAngleSqEdgeChainDeriv
  refine Finset.sum_congr rfl ?_
  intro k _
  have htet :
      ((triangulationSchlaefliData_of_incidence K hK).tetData τ).dihedralDeriv f k =
        dihedralClosedDerivLength (K.tet τ) f k := by
    rfl
  rw [htet]
  unfold localEdgeLengthDirectionalDeriv conformalLocalSqEdgeDirectionalDeriv
    dihedralClosedDerivLength
  let uv := ReggeRigorousFoundation.edgeVertices k
  have hsqrt_sq :
      Real.sqrt ((K.tet τ).sqEdge k) * Real.sqrt ((K.tet τ).sqEdge k) =
        (K.tet τ).sqEdge k := by
    rw [← sq]
    exact Real.sq_sqrt (le_of_lt ((K.tet τ).sqEdge_pos k))
  have hsqrt_sq_pow :
      Real.sqrt ((K.tet τ).sqEdge k) ^ 2 = (K.tet τ).sqEdge k := by
    simpa [pow_two] using hsqrt_sq
  rw [mul_assoc]
  ring_nf
  rw [hsqrt_sq_pow]
  ring

/-- Local Schläfli cancellation for the conformal length direction on a single
tetrahedron.  This is pure finite-sum algebra plus the already proved local
Schläfli identity. -/
theorem local_conformal_schlaefli_cancellation
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (η : VertexPotential K) (τ : Fin K.nT) :
    (∑ f : Fin 6,
      Real.sqrt ((K.tet τ).sqEdge f) *
        localAngleLengthChainDeriv K hK η τ f) = 0 := by
  unfold localAngleLengthChainDeriv
  calc
    (∑ f : Fin 6,
      Real.sqrt ((K.tet τ).sqEdge f) *
        (∑ k : Fin 6,
          ((triangulationSchlaefliData_of_incidence K hK).tetData τ).dihedralDeriv f k *
            localEdgeLengthDirectionalDeriv K η τ k))
        =
      ∑ k : Fin 6,
        localEdgeLengthDirectionalDeriv K η τ k *
          (∑ f : Fin 6,
            Real.sqrt ((K.tet τ).sqEdge f) *
              ((triangulationSchlaefliData_of_incidence K hK).tetData τ).dihedralDeriv f k) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro k _
          refine Finset.sum_congr rfl ?_
          intro f _
          ring
    _ = ∑ k : Fin 6, localEdgeLengthDirectionalDeriv K η τ k * 0 := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [((triangulationSchlaefliData_of_incidence K hK).tetData τ).schlaefli k]
    _ = 0 := by simp

/-- A local angle package whose values are the edge-length chain-rule values.
The remaining local analytic obligation is the `HasDerivAt` proof tying the
actual cofactor/arccos angle to this closed-form chain-rule value. -/
structure LocalAngleLengthChainRulePackage
    (K : Triangulation3D) (hK : IncidenceConsistent K) where
  angle_hasDerivAt :
    ∀ (η : VertexPotential K) (τ : Fin K.nT) (f : Fin 6),
      HasDerivAt
        (fun t : ℝ => tetDihedralAngleUnderConformal K (linePotential K η t) τ f)
        (localAngleLengthChainDeriv K hK η τ f) 0

/-- The squared-edge chain-rule form that follows directly from the explicit
cofactor/arccos coordinate derivative formulas. -/
structure LocalAngleSqEdgeChainRulePackage
    (K : Triangulation3D) where
  angle_hasDerivAt :
    ∀ (η : VertexPotential K) (τ : Fin K.nT) (f : Fin 6),
      HasDerivAt
        (fun t : ℝ => tetDihedralAngleUnderConformal K (linePotential K η t) τ f)
        (localAngleSqEdgeChainDeriv K η τ f) 0

def localAngleSqEdgeChainRulePackage_of_flat
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK) :
    LocalAngleSqEdgeChainRulePackage K where
  angle_hasDerivAt := by
    intro η τ f
    let T := K.tet τ
    let F : CayleyMengerPolynomial.SqEdges → ℝ :=
      fun a => DihedralDerivatives.dihedralAngle3Sq a f
    let v : CayleyMengerPolynomial.SqEdges :=
      fun k => conformalLocalSqEdgeDirectionalDeriv K η τ k
    have hEndpoint : dihedralCos3Sq T.sqEdge f ≠ -1 ∧ dihedralCos3Sq T.sqEdge f ≠ 1 := by
      simpa [T] using h_flat.local_arccos_endpoint_free τ f
    have hAngle : ContDiffAt ℝ 1 F T.sqEdge := by
      simpa [F, T] using dihedralAngle3Sq_contDiffAt_nonDegenerate (K.tet τ) f 1
        (h_flat.local_arccos_endpoint_free τ f)
    have hDiff : DifferentiableAt ℝ F T.sqEdge :=
      hAngle.differentiableAt (by simp)
    have hF : HasFDerivAt F (fderiv ℝ F T.sqEdge) T.sqEdge :=
      hDiff.hasFDerivAt
    have hbase : conformalTetSqEdges K (linePotential K η 0) τ = T.sqEdge := by
      simpa [linePotential_zero K η, T] using
        ReggeActionSmoothness.conformalTetSqEdges_zero K τ
    have hF' : HasFDerivAt F (fderiv ℝ F T.sqEdge)
        (conformalTetSqEdges K (linePotential K η 0) τ) := by
      simpa [hbase] using hF
    have hgamma : HasDerivAt
        (fun t : ℝ => conformalTetSqEdges K (linePotential K η t) τ) v 0 := by
      simpa [v] using conformalTetSqEdges_hasDerivAt_line_zero K η τ
    have hcomp := HasFDerivAt.comp_hasDerivAt
      (x := (0 : ℝ))
      (f := fun t : ℝ => conformalTetSqEdges K (linePotential K η t) τ)
      (l := F)
      hF' hgamma
    have hvalue :
        (fderiv ℝ F T.sqEdge) v = localAngleSqEdgeChainDeriv K η τ f := by
      unfold localAngleSqEdgeChainDeriv
      calc
        (fderiv ℝ F T.sqEdge) v
            = ∑ k : Fin 6,
                v k * (fderiv ℝ F T.sqEdge)
                  (Pi.single (M := fun _ : Fin 6 => ℝ) k (1 : ℝ)) := by
              exact continuousLinearMap_apply_eq_sum_single (fderiv ℝ F T.sqEdge) v
        _ = ∑ k : Fin 6,
                dihedralClosedDerivSq (K.tet τ) f k *
                  conformalLocalSqEdgeDirectionalDeriv K η τ k := by
              refine Finset.sum_congr rfl ?_
              intro k _
              have hcoord :=
                fderiv_dihedralAngle3Sq_apply_single (K.tet τ) f k
                  (h_flat.local_arccos_endpoint_free τ f)
              simp [F, T, v, hcoord, mul_comm]
    rw [hvalue] at hcomp
    simpa [F, Function.comp_def, tetDihedralAngleUnderConformal] using hcomp

def localAngleLengthChainRulePackage_of_sqEdge
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (S : LocalAngleSqEdgeChainRulePackage K) :
    LocalAngleLengthChainRulePackage K hK where
  angle_hasDerivAt := by
    intro η τ f
    have h := S.angle_hasDerivAt η τ f
    rw [localAngleLengthChainDeriv_eq_sqEdgeChainDeriv K hK η τ f]
    exact h

def localDihedralDirectionalDerivativePackage_of_lengthChain
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (L : LocalAngleLengthChainRulePackage K hK) :
    LocalDihedralDirectionalDerivativePackage K where
  angleDeriv := localAngleLengthChainDeriv K hK
  angle_hasDerivAt := L.angle_hasDerivAt

def deficitDirectionalDerivFromLocalAngles
    (K : Triangulation3D) (A : LocalDihedralDirectionalDerivativePackage K)
    (η : VertexPotential K) (e : Fin K.nE) : ℝ :=
  - ∑ τ : Fin K.nT,
      match K.edgeInTet e τ with
      | none => 0
      | some f => A.angleDeriv η τ f

/-- Directional derivative package for deficit angles.  The cancellation field
is exactly the global Schläfli contribution in the conformal direction. -/
structure DeficitAngleDirectionalDerivativePackage
    (K : Triangulation3D) (hK : IncidenceConsistent K) where
  deficitDeriv : VertexPotential K → Fin K.nE → ℝ
  deficit_hasDerivAt :
    ∀ (η : VertexPotential K) (e : Fin K.nE),
      HasDerivAt (fun t : ℝ => deficitAngle K (linePotential K η t) e)
        (deficitDeriv η e) 0
  schlaefli_cancellation :
    ∀ η : VertexPotential K,
      (∑ e : Fin K.nE,
        hingeMeasureUnderConformal K hK (zeroPotential K) e * deficitDeriv η e) = 0

theorem localDeficitAngleContribution_hasDerivAt_from_localAngles
    (K : Triangulation3D) (A : LocalDihedralDirectionalDerivativePackage K)
    (η : VertexPotential K) (e : Fin K.nE) (τ : Fin K.nT) :
    HasDerivAt
      (fun t : ℝ => localDeficitAngleContribution K (linePotential K η t) e τ)
      (match K.edgeInTet e τ with
       | none => 0
       | some f => A.angleDeriv η τ f) 0 := by
  unfold localDeficitAngleContribution
  cases h : K.edgeInTet e τ with
  | none =>
      simpa [h] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  | some f =>
      simpa [h] using A.angle_hasDerivAt η τ f

theorem deficitAngle_hasDerivAt_from_localAngles
    (K : Triangulation3D) (A : LocalDihedralDirectionalDerivativePackage K)
    (η : VertexPotential K) (e : Fin K.nE) :
    HasDerivAt
      (fun t : ℝ => deficitAngle K (linePotential K η t) e)
      (deficitDirectionalDerivFromLocalAngles K A η e) 0 := by
  unfold deficitAngle deficitDirectionalDerivFromLocalAngles
  have hsum : HasDerivAt
      (∑ τ : Fin K.nT,
        fun t : ℝ => localDeficitAngleContribution K (linePotential K η t) e τ)
      (∑ τ : Fin K.nT,
        match K.edgeInTet e τ with
        | none => 0
        | some f => A.angleDeriv η τ f) 0 := by
    have hsum' :=
      HasDerivAt.sum
        (u := Finset.univ)
        (A := fun τ t => localDeficitAngleContribution K (linePotential K η t) e τ)
        (A' := fun τ =>
          match K.edgeInTet e τ with
          | none => 0
          | some f => A.angleDeriv η τ f)
        (x := 0)
        (fun τ _ => localDeficitAngleContribution_hasDerivAt_from_localAngles K A η e τ)
    simpa using hsum'
  have hconst : HasDerivAt (fun _t : ℝ => 2 * Real.pi) 0 0 :=
    hasDerivAt_const 0 (2 * Real.pi)
  have hsub := hconst.sub hsum
  convert hsub using 1
  · ext t
    simp [Pi.sub_apply, Finset.sum_apply]
  · ring

def deficitPackage_of_localAngles
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (A : LocalDihedralDirectionalDerivativePackage K)
    (hCancel :
      ∀ η : VertexPotential K,
        (∑ e : Fin K.nE,
          hingeMeasureUnderConformal K hK (zeroPotential K) e *
            deficitDirectionalDerivFromLocalAngles K A η e) = 0) :
    DeficitAngleDirectionalDerivativePackage K hK where
  deficitDeriv := deficitDirectionalDerivFromLocalAngles K A
  deficit_hasDerivAt := deficitAngle_hasDerivAt_from_localAngles K A
  schlaefli_cancellation := hCancel

/-- The exact Schläfli cancellation needed by the conformal first variation
after the local dihedral directional derivatives have been constructed. -/
def ConformalSchlaefliCancellation
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (A : LocalDihedralDirectionalDerivativePackage K) : Prop :=
  ∀ η : VertexPotential K,
    (∑ e : Fin K.nE,
      hingeMeasureUnderConformal K hK (zeroPotential K) e *
        deficitDirectionalDerivFromLocalAngles K A η e) = 0

/-- Global incidence bookkeeping needed to turn the edge-indexed deficit
variation into the sum of local tetrahedral Schläfli sums. -/
def ConformalSchlaefliIncidenceBookkeeping
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (A : LocalDihedralDirectionalDerivativePackage K) : Prop :=
  ∀ η : VertexPotential K,
    (∑ e : Fin K.nE,
      hingeMeasureUnderConformal K hK (zeroPotential K) e *
        deficitDirectionalDerivFromLocalAngles K A η e) =
      - ∑ τ : Fin K.nT,
          ∑ f : Fin 6,
            Real.sqrt ((K.tet τ).sqEdge f) * A.angleDeriv η τ f

/-- Incidence partition certificate: summing a local edge-slot weight over
global edges and tetrahedra is the same as summing it directly over local
tetrahedral edge slots, with matching flat edge lengths.

`IncidenceConsistent.localEdge_complete` gives existence of a global edge for
each local slot.  Exact reindexing also needs uniqueness/no-duplication, so it
is recorded here as the actual bookkeeping theorem needed downstream. -/
structure IncidenceEdgeSlotBookkeeping
    (K : Triangulation3D) (hK : IncidenceConsistent K) where
  sum_match :
    ∀ w : Fin K.nT → Fin 6 → ℝ,
      (∑ e : Fin K.nE,
        globalEdgeLength K hK e *
          (∑ τ : Fin K.nT,
            match K.edgeInTet e τ with
            | none => 0
            | some f => w τ f)) =
        ∑ τ : Fin K.nT,
          ∑ f : Fin 6,
            Real.sqrt ((K.tet τ).sqEdge f) * w τ f

/-- The intended concrete incidence class for edge-slot bookkeeping: every
local tetrahedral edge slot `(τ,f)` is represented by exactly one global edge,
and the incidence map hits that slot iff the global edge is that representative. -/
structure IncidenceEdgeSlotPartition
    (K : Triangulation3D) (hK : IncidenceConsistent K) where
  localEdgeOf : Fin K.nT → Fin 6 → Fin K.nE
  edgeInTet_iff :
    ∀ e τ f, K.edgeInTet e τ = some f ↔ e = localEdgeOf τ f

theorem IncidenceEdgeSlotPartition.localEdgeOf_incident
    {K : Triangulation3D} {hK : IncidenceConsistent K}
    (P : IncidenceEdgeSlotPartition K hK) (τ : Fin K.nT) (f : Fin 6) :
    K.edgeInTet (P.localEdgeOf τ f) τ = some f :=
  (P.edgeInTet_iff (P.localEdgeOf τ f) τ f).2 rfl

theorem IncidenceEdgeSlotPartition.global_length_localEdgeOf
    {K : Triangulation3D} {hK : IncidenceConsistent K}
    (P : IncidenceEdgeSlotPartition K hK) (τ : Fin K.nT) (f : Fin 6) :
    globalEdgeLength K hK (P.localEdgeOf τ f) =
      Real.sqrt ((K.tet τ).sqEdge f) := by
  unfold globalEdgeLength
  rw [← hK.local_sqEdge_eq_global (P.localEdgeOf τ f) τ f
    (P.localEdgeOf_incident τ f)]

theorem IncidenceEdgeSlotPartition.edge_sum_for_tet
    {K : Triangulation3D} {hK : IncidenceConsistent K}
    (P : IncidenceEdgeSlotPartition K hK)
    (w : Fin K.nT → Fin 6 → ℝ) (τ : Fin K.nT) :
    (∑ e : Fin K.nE,
      globalEdgeLength K hK e *
        (match K.edgeInTet e τ with
        | none => 0
        | some f => w τ f)) =
      ∑ f : Fin 6, Real.sqrt ((K.tet τ).sqEdge f) * w τ f := by
  calc
    (∑ e : Fin K.nE,
      globalEdgeLength K hK e *
        (match K.edgeInTet e τ with
        | none => 0
        | some f => w τ f))
        =
      ∑ e : Fin K.nE,
        ∑ f : Fin 6,
          if K.edgeInTet e τ = some f then
            globalEdgeLength K hK e * w τ f
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e _
          cases h : K.edgeInTet e τ with
          | none =>
              simp
          | some f0 =>
              simp
    _ = ∑ f : Fin 6,
        ∑ e : Fin K.nE,
          if K.edgeInTet e τ = some f then
            globalEdgeLength K hK e * w τ f
          else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ f : Fin 6,
        globalEdgeLength K hK (P.localEdgeOf τ f) * w τ f := by
          refine Finset.sum_congr rfl ?_
          intro f _
          have hsum := Finset.sum_eq_single
            (s := Finset.univ)
            (f := fun e : Fin K.nE =>
              (if K.edgeInTet e τ = some f then
                globalEdgeLength K hK e * w τ f
              else 0 : ℝ))
            (P.localEdgeOf τ f) ?_ ?_
          · simpa [P.localEdgeOf_incident τ f] using hsum
          · intro e _ he_ne
            have hnot : K.edgeInTet e τ ≠ some f := by
              intro h
              exact he_ne ((P.edgeInTet_iff e τ f).1 h)
            simp [hnot]
          · intro hnot_mem
            exact (hnot_mem (Finset.mem_univ _)).elim
    _ = ∑ f : Fin 6, Real.sqrt ((K.tet τ).sqEdge f) * w τ f := by
          refine Finset.sum_congr rfl ?_
          intro f _
          rw [P.global_length_localEdgeOf τ f]

def incidenceEdgeSlotBookkeeping_of_partition
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (P : IncidenceEdgeSlotPartition K hK) :
    IncidenceEdgeSlotBookkeeping K hK where
  sum_match := by
    intro w
    calc
      (∑ e : Fin K.nE,
        globalEdgeLength K hK e *
          (∑ τ : Fin K.nT,
            match K.edgeInTet e τ with
            | none => 0
            | some f => w τ f))
          =
        ∑ e : Fin K.nE,
          ∑ τ : Fin K.nT,
            globalEdgeLength K hK e *
              (match K.edgeInTet e τ with
              | none => 0
              | some f => w τ f) := by
            refine Finset.sum_congr rfl ?_
            intro e _
            rw [Finset.mul_sum]
      _ = ∑ τ : Fin K.nT,
          ∑ e : Fin K.nE,
            globalEdgeLength K hK e *
              (match K.edgeInTet e τ with
              | none => 0
              | some f => w τ f) := by
            rw [Finset.sum_comm]
      _ = ∑ τ : Fin K.nT,
          ∑ f : Fin 6,
            Real.sqrt ((K.tet τ).sqEdge f) * w τ f := by
            refine Finset.sum_congr rfl ?_
            intro τ _
            exact P.edge_sum_for_tet w τ

theorem conformalSchlaefliIncidenceBookkeeping_of_edgeSlotBookkeeping
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (A : LocalDihedralDirectionalDerivativePackage K)
    (hBook : IncidenceEdgeSlotBookkeeping K hK) :
    ConformalSchlaefliIncidenceBookkeeping K hK A := by
  intro η
  unfold deficitDirectionalDerivFromLocalAngles
  calc
    (∑ e : Fin K.nE,
      hingeMeasureUnderConformal K hK (zeroPotential K) e *
        (-∑ τ : Fin K.nT,
          match K.edgeInTet e τ with
          | none => 0
          | some f => A.angleDeriv η τ f))
        =
      - (∑ e : Fin K.nE,
        globalEdgeLength K hK e *
          (∑ τ : Fin K.nT,
            match K.edgeInTet e τ with
            | none => 0
            | some f => A.angleDeriv η τ f)) := by
          unfold hingeMeasureUnderConformal globalEdgeLength zeroPotential
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro e _
          simp
    _ = - (∑ τ : Fin K.nT,
          ∑ f : Fin 6,
            Real.sqrt ((K.tet τ).sqEdge f) * A.angleDeriv η τ f) := by
          rw [hBook.sum_match (fun τ f => A.angleDeriv η τ f)]

theorem conformalSchlaefliCancellation_of_lengthChain_of_bookkeeping
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (L : LocalAngleLengthChainRulePackage K hK)
    (hBook :
      ConformalSchlaefliIncidenceBookkeeping K hK
        (localDihedralDirectionalDerivativePackage_of_lengthChain K hK L)) :
    ConformalSchlaefliCancellation K hK
      (localDihedralDirectionalDerivativePackage_of_lengthChain K hK L) := by
  intro η
  rw [hBook η]
  have hlocal : ∀ τ : Fin K.nT,
      (∑ f : Fin 6,
        Real.sqrt ((K.tet τ).sqEdge f) *
          (localDihedralDirectionalDerivativePackage_of_lengthChain K hK L).angleDeriv η τ f) = 0 := by
    intro τ
    exact local_conformal_schlaefli_cancellation K hK η τ
  simp_rw [hlocal]
  simp

def deficitPackage_of_conformalSchlaefliCancellation
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (A : LocalDihedralDirectionalDerivativePackage K)
    (hCancel : ConformalSchlaefliCancellation K hK A) :
    DeficitAngleDirectionalDerivativePackage K hK :=
  deficitPackage_of_localAngles K hK A hCancel

theorem directionalFirstVariationFormula_of_deficitPackage
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (D : DeficitAngleDirectionalDerivativePackage K hK) :
    ReggeActionDirectionalFirstVariationFormula K hK where
  directional_formula := by
    intro η
    unfold reggeAction
    have hedge :
        ∀ e : Fin K.nE,
          HasDerivAt
            (fun t : ℝ =>
              hingeMeasureUnderConformal K hK (linePotential K η t) e *
                deficitAngle K (linePotential K η t) e)
            (hingeMeasureDirectionalDeriv K hK η e *
                deficitAngle K (zeroPotential K) e +
              hingeMeasureUnderConformal K hK (zeroPotential K) e *
                D.deficitDeriv η e) 0 := by
      intro e
      have hL := hingeMeasureUnderConformal_hasDerivAt_line_zero K hK η e
      have hδ := D.deficit_hasDerivAt η e
      have hprod := hL.mul hδ
      simpa [linePotential_zero K η, mul_comm, mul_left_comm, mul_assoc] using hprod
    have hsum : HasDerivAt
        (∑ e : Fin K.nE,
          fun t : ℝ =>
            hingeMeasureUnderConformal K hK (linePotential K η t) e *
              deficitAngle K (linePotential K η t) e)
        (∑ e : Fin K.nE,
          (hingeMeasureDirectionalDeriv K hK η e *
              deficitAngle K (zeroPotential K) e +
            hingeMeasureUnderConformal K hK (zeroPotential K) e *
              D.deficitDeriv η e)) 0 := by
      have hsum' :=
        HasDerivAt.sum
            (u := Finset.univ)
            (A := fun e t =>
              hingeMeasureUnderConformal K hK (linePotential K η t) e *
                deficitAngle K (linePotential K η t) e)
            (A' := fun e =>
              hingeMeasureDirectionalDeriv K hK η e *
                  deficitAngle K (zeroPotential K) e +
                hingeMeasureUnderConformal K hK (zeroPotential K) e *
                  D.deficitDeriv η e)
            (x := 0)
            (fun e _ => hedge e)
      simpa [Finset.sum_apply] using hsum'
    have htarget :
        (∑ e : Fin K.nE,
          (hingeMeasureDirectionalDeriv K hK η e *
              deficitAngle K (zeroPotential K) e +
            hingeMeasureUnderConformal K hK (zeroPotential K) e *
              D.deficitDeriv η e)) =
        ∑ e : Fin K.nE,
          hingeMeasureDirectionalDeriv K hK η e *
            deficitAngle K (zeroPotential K) e := by
      rw [Finset.sum_add_distrib, D.schlaefli_cancellation η]
      ring
    rw [htarget] at hsum
    convert hsum using 1
    ext t
    simp

theorem firstVariationFormula_of_directionalFormula
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (hdir : ReggeActionDirectionalFirstVariationFormula K hK) :
    ReggeActionFirstVariationFormula K hK where
  firstVariation_formula := by
    intro η
    have hleft := reggeAction_along_line_hasDerivAt_fderiv K hK h_flat η
    have hright := hdir.directional_formula η
    exact hleft.unique hright

theorem directionalCritical_of_firstVariationFormula_of_zeroDeficit
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hZero : GlobalZeroDeficitAtFlat K)
    (hFormula : ReggeActionFirstVariationFormula K hK) :
    ReggeActionDirectionalCriticalAtZero K hK := by
  intro η
  rw [hFormula.firstVariation_formula η]
  apply Finset.sum_eq_zero
  intro e _
  rw [hZero e]
  ring

theorem reggeActionCriticalAtZero_of_firstVariationFormula_of_zeroDeficit
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hZero : GlobalZeroDeficitAtFlat K)
    (hFormula : ReggeActionFirstVariationFormula K hK) :
    ReggeActionCriticalAtZero K hK :=
  reggeActionCriticalAtZero_of_directional K hK
    (directionalCritical_of_firstVariationFormula_of_zeroDeficit K hK hZero hFormula)

/-- Named first-variation input.  The intended lower-level proof is:
differentiate the hinge-length factor and local dihedral factors, use zero
deficit for the hinge term, then use the global Schläfli identity for the
dihedral term. -/
structure ReggeActionFirstVariationInput
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (_h_flat : FlatConfiguration K hK) where
  firstVariation_zero : ReggeActionCriticalAtZero K hK

def reggeActionFirstVariationInput_of_directional
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (hdir : ReggeActionDirectionalCriticalAtZero K hK) :
    ReggeActionFirstVariationInput K hK h_flat where
  firstVariation_zero := reggeActionCriticalAtZero_of_directional K hK hdir

def reggeActionFirstVariationInput_of_firstVariationFormula
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (hFormula : ReggeActionFirstVariationFormula K hK) :
    ReggeActionFirstVariationInput K hK h_flat where
  firstVariation_zero :=
    reggeActionCriticalAtZero_of_firstVariationFormula_of_zeroDeficit
      K hK h_flat.flat_deficit_zero hFormula

def reggeActionFirstVariationInput_of_localAngles
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (A : LocalDihedralDirectionalDerivativePackage K)
    (hCancel : ConformalSchlaefliCancellation K hK A) :
    ReggeActionFirstVariationInput K hK h_flat :=
  reggeActionFirstVariationInput_of_firstVariationFormula K hK h_flat
    (firstVariationFormula_of_directionalFormula K hK h_flat
      (directionalFirstVariationFormula_of_deficitPackage K hK
        (deficitPackage_of_conformalSchlaefliCancellation K hK A hCancel)))

def reggeActionFirstVariationInput_of_conformalSchlaefliCancellation
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (hCancel : ConformalSchlaefliCancellation K hK
      (localDihedralDirectionalDerivativePackage_of_flat K hK h_flat)) :
    ReggeActionFirstVariationInput K hK h_flat :=
  reggeActionFirstVariationInput_of_localAngles K hK h_flat
    (localDihedralDirectionalDerivativePackage_of_flat K hK h_flat) hCancel

def reggeActionFirstVariationInput_of_incidenceBookkeeping
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (hBook : ConformalSchlaefliIncidenceBookkeeping K hK
      (localDihedralDirectionalDerivativePackage_of_lengthChain K hK
        (localAngleLengthChainRulePackage_of_sqEdge K hK
          (localAngleSqEdgeChainRulePackage_of_flat K hK h_flat)))) :
    ReggeActionFirstVariationInput K hK h_flat :=
  reggeActionFirstVariationInput_of_localAngles K hK h_flat
    (localDihedralDirectionalDerivativePackage_of_lengthChain K hK
      (localAngleLengthChainRulePackage_of_sqEdge K hK
        (localAngleSqEdgeChainRulePackage_of_flat K hK h_flat)))
    (conformalSchlaefliCancellation_of_lengthChain_of_bookkeeping K hK
      (localAngleLengthChainRulePackage_of_sqEdge K hK
        (localAngleSqEdgeChainRulePackage_of_flat K hK h_flat))
      hBook)

def reggeActionFirstVariationInput_of_edgeSlotBookkeeping
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (hBook : IncidenceEdgeSlotBookkeeping K hK) :
    ReggeActionFirstVariationInput K hK h_flat :=
  reggeActionFirstVariationInput_of_incidenceBookkeeping K hK h_flat
    (conformalSchlaefliIncidenceBookkeeping_of_edgeSlotBookkeeping K hK
      (localDihedralDirectionalDerivativePackage_of_lengthChain K hK
        (localAngleLengthChainRulePackage_of_sqEdge K hK
          (localAngleSqEdgeChainRulePackage_of_flat K hK h_flat)))
      hBook)

def reggeActionFirstVariationInput_of_edgeSlotPartition
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (P : IncidenceEdgeSlotPartition K hK) :
    ReggeActionFirstVariationInput K hK h_flat :=
  reggeActionFirstVariationInput_of_edgeSlotBookkeeping K hK h_flat
    (incidenceEdgeSlotBookkeeping_of_partition K hK P)

/-- Phase-C first-variation theorem, conditional on the named analytic
first-variation input. -/
theorem reggeAction_firstVariation_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (h_first : ReggeActionFirstVariationInput K hK h_flat) :
    fderiv ℝ (reggeAction K hK) (zeroPotential K) = 0 :=
  h_first.firstVariation_zero

/-- First variation of the nonlinear remainder.  This is recorded as a
separate named input because proving it directly requires the derivative of
the finite-dimensional quadratic form at zero in the same analytic universe
as the full action. -/
structure ReggeActionRemainderFirstVariationInput
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (H : Fin K.nV → Fin K.nV → ℝ) where
  remainder_firstVariation_zero :
    fderiv ℝ (reggeActionRemainder K hK H) (zeroPotential K) = 0

theorem reggeActionRemainder_fderiv_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (H : Fin K.nV → Fin K.nV → ℝ)
    (h_rem : ReggeActionRemainderFirstVariationInput K hK H) :
    fderiv ℝ (reggeActionRemainder K hK H) (zeroPotential K) = 0 :=
  h_rem.remainder_firstVariation_zero

private theorem hasFDerivAt_finset_sum_zero
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (f : ι → E → ℝ) (x : E)
    (hf : ∀ i ∈ s, HasFDerivAt (f i) (0 : E →L[ℝ] ℝ) x) :
    HasFDerivAt (fun y => s.sum (fun i => f i y)) (0 : E →L[ℝ] ℝ) x := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    change HasFDerivAt (fun _y : E => (0 : ℝ)) (0 : E →L[ℝ] ℝ) x
    simpa using
      (hasFDerivAt_const (x := x) (c := (0 : ℝ)))
  · intro a s ha ih hf
    have hfa : HasFDerivAt (f a) (0 : E →L[ℝ] ℝ) x :=
      hf a (by simp [ha])
    have hfs : HasFDerivAt (fun y => s.sum (fun i => f i y)) (0 : E →L[ℝ] ℝ) x :=
      ih (by
        intro i hi
        exact hf i (by simp [hi]))
    simpa [ha] using hfa.add hfs

private theorem hessianQuadratic_term_hasFDerivAt_zero
    (K : Triangulation3D) (H : Fin K.nV → Fin K.nV → ℝ)
    (i j : Fin K.nV) :
    HasFDerivAt
      (fun ξ : VertexPotential K => H i j * ξ i * ξ j)
      (0 : VertexPotential K →L[ℝ] ℝ)
      (zeroPotential K) := by
  let evalI : VertexPotential K →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K.nV => ℝ) i
  let evalJ : VertexPotential K →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K.nV => ℝ) j
  have hi : HasFDerivAt (fun ξ : VertexPotential K => ξ i) evalI (zeroPotential K) := by
    simpa [evalI] using evalI.hasFDerivAt
  have hj : HasFDerivAt (fun ξ : VertexPotential K => ξ j) evalJ (zeroPotential K) := by
    simpa [evalJ] using evalJ.hasFDerivAt
  have hHi : HasFDerivAt (fun ξ : VertexPotential K => H i j * ξ i)
      (H i j • evalI) (zeroPotential K) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hi.const_mul (H i j)
  have h := hHi.mul hj
  convert h using 1
  · ext η
    simp [zeroPotential]

/-- The quadratic Hessian form has zero first derivative at the zero potential. -/
theorem hessianQuadratic_hasFDerivAt_zero
    (K : Triangulation3D) (H : Fin K.nV → Fin K.nV → ℝ) :
    HasFDerivAt
      (fun ξ : VertexPotential K => hessianQuadratic H ξ)
      (0 : VertexPotential K →L[ℝ] ℝ)
      (zeroPotential K) := by
  unfold hessianQuadratic zeroPotential
  apply hasFDerivAt_finset_sum_zero
  intro i _hi
  apply hasFDerivAt_finset_sum_zero
  intro j _hj
  simpa [zeroPotential] using hessianQuadratic_term_hasFDerivAt_zero K H i j

/-- The scaled quadratic Hessian term used in the Regge Taylor split also has
zero first derivative at the zero potential. -/
theorem half_hessianQuadratic_hasFDerivAt_zero
    (K : Triangulation3D) (H : Fin K.nV → Fin K.nV → ℝ) :
    HasFDerivAt
      (fun ξ : VertexPotential K => (1 / 2 : ℝ) * hessianQuadratic H ξ)
      (0 : VertexPotential K →L[ℝ] ℝ)
      (zeroPotential K) := by
  simpa using (hessianQuadratic_hasFDerivAt_zero K H).const_mul (1 / 2 : ℝ)

/-- The nonlinear remainder first-variation input follows from the full Regge
first-variation input.  The subtracted constant has zero derivative and the
subtracted quadratic Hessian term has zero derivative at the flat point. -/
def reggeActionRemainderFirstVariationInput_of_firstVariation
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (H : Fin K.nV → Fin K.nV → ℝ)
    (h_first : ReggeActionFirstVariationInput K hK h_flat) :
    ReggeActionRemainderFirstVariationInput K hK H where
  remainder_firstVariation_zero := by
    have hActionDiff : DifferentiableAt ℝ (reggeAction K hK) (zeroPotential K) :=
      h_flat.action_contDiff_at_zero.differentiableAt (by simp)
    have hAction :
        HasFDerivAt (reggeAction K hK)
          (0 : VertexPotential K →L[ℝ] ℝ) (zeroPotential K) := by
      have h := hActionDiff.hasFDerivAt
      rw [h_first.firstVariation_zero] at h
      exact h
    have hConst : HasFDerivAt
        (fun _ξ : VertexPotential K => reggeAction K hK (zeroPotential K))
        (0 : VertexPotential K →L[ℝ] ℝ)
        (zeroPotential K) := by
      simpa using
        (hasFDerivAt_const
          (x := zeroPotential K)
          (c := reggeAction K hK (zeroPotential K)))
    have hQuad := half_hessianQuadratic_hasFDerivAt_zero K H
    have hRemRaw :=
      (hAction.sub hConst).sub hQuad
    have hRem :
        HasFDerivAt
          (fun ξ : VertexPotential K =>
            reggeAction K hK ξ -
              reggeAction K hK (zeroPotential K) -
              (1 / 2 : ℝ) * hessianQuadratic H ξ)
          (0 : VertexPotential K →L[ℝ] ℝ)
          (zeroPotential K) := by
      convert hRemRaw using 1
      · simp
    convert hRem.fderiv using 1

end

end ReggeActionFirstVariation
end Geometry
end IndisputableMonolith
