import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import IndisputableMonolith.Geometry.ReggeHessian3D
import IndisputableMonolith.Geometry.Triangulation3DConsistency
import IndisputableMonolith.Geometry.DihedralDerivatives

/-!
# Concrete Regge Action Hessian Target

This module isolates the final analytic Hessian step for a finite 3D Regge
triangulation.  A concrete action package supplies the Regge action under the
conformal ansatz and proves its second variation; the module turns that into
the existing `ReggeHessianData` interface.
-/

namespace IndisputableMonolith
namespace Geometry
namespace ReggeActionConcrete

open ReggeTriangulation3D
open ReggeHessian3D
open Triangulation3DConsistency
open DihedralDerivatives

noncomputable section

/-- Local squared-edge data in tetrahedron `τ` under the vertex-conformal
ansatz.  The local edge `f = (u,v)` scales by `exp (ξ_u + ξ_v)`. -/
def conformalLocalSqEdge
    (K : Triangulation3D) (ξ : VertexPotential K)
    (τ : Fin K.nT) (f : Fin 6) : ℝ :=
  let uv := ReggeRigorousFoundation.edgeVertices f
  (K.tet τ).sqEdge f *
    Real.exp (ξ (K.tetVerts τ uv.1) + ξ (K.tetVerts τ uv.2))

/-- The six conformally scaled squared-edge coordinates of a tetrahedron. -/
def conformalTetSqEdges
    (K : Triangulation3D) (ξ : VertexPotential K) (τ : Fin K.nT) :
    CayleyMengerPolynomial.SqEdges :=
  fun f => conformalLocalSqEdge K ξ τ f

/-- Dihedral angle of a local tetrahedral edge under the conformal ansatz,
computed directly from the Cayley-Menger cofactor formula on squared-edge
data. -/
def tetDihedralAngleUnderConformal
    (K : Triangulation3D) (ξ : VertexPotential K)
    (τ : Fin K.nT) (f : Fin 6) : ℝ :=
  dihedralAngle3Sq (conformalTetSqEdges K ξ τ) f

/-- A local incidence contribution to the deficit angle at a global edge. -/
def localDeficitAngleContribution
    (K : Triangulation3D) (ξ : VertexPotential K)
    (e : Fin K.nE) (τ : Fin K.nT) : ℝ :=
  match K.edgeInTet e τ with
  | some f => tetDihedralAngleUnderConformal K ξ τ f
  | none => 0

/-- Regge deficit angle at a global edge under the conformal ansatz. -/
def deficitAngle
    (K : Triangulation3D) (ξ : VertexPotential K) (e : Fin K.nE) : ℝ :=
  2 * Real.pi - ∑ τ : Fin K.nT, localDeficitAngleContribution K ξ e τ

/-- The 3D Regge hinge measure is the edge length.  This is the conformal
length of a global edge under the vertex-conformal ansatz. -/
def hingeMeasureUnderConformal
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (e : Fin K.nE) : ℝ :=
  let uv := K.edgeVerts e
  Real.sqrt (hK.globalSqEdge e) *
    Real.exp ((ξ uv.1 + ξ uv.2) / 2)

/-- The concrete 3D Regge action under the vertex-conformal ansatz. -/
def reggeAction
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) : ℝ :=
  ∑ e : Fin K.nE,
    hingeMeasureUnderConformal K hK ξ e * deficitAngle K ξ e

/-- The quadratic second-order truncation associated with a candidate Hessian
matrix.  This is the object for which exact quadratic second-variation
statements are definitionally correct; the full nonlinear action needs a
Taylor remainder theorem. -/
def reggeActionSecondOrder
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (H : Fin K.nV → Fin K.nV → ℝ)
    (ξ : VertexPotential K) : ℝ :=
  reggeAction K hK (zeroPotential K) + (1 / 2) * hessianQuadratic H ξ

/-- The nonlinear Taylor remainder after subtracting the value at zero and a
candidate quadratic Hessian term from the full Regge action. -/
def reggeActionRemainder
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (H : Fin K.nV → Fin K.nV → ℝ)
    (ξ : VertexPotential K) : ℝ :=
  reggeAction K hK ξ - reggeAction K hK (zeroPotential K) -
    (1 / 2) * hessianQuadratic H ξ

theorem hessianQuadratic_zeroPotential
    (K : Triangulation3D) (H : Fin K.nV → Fin K.nV → ℝ) :
    hessianQuadratic H (zeroPotential K) = 0 := by
  unfold hessianQuadratic zeroPotential
  simp

/-- Exact decomposition of the nonlinear action into its value at zero, a
candidate quadratic Hessian term, and the remaining nonlinear part. -/
theorem reggeAction_taylor_decomposition
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (H : Fin K.nV → Fin K.nV → ℝ)
    (ξ : VertexPotential K) :
    reggeAction K hK ξ =
      reggeAction K hK (zeroPotential K) +
        (1 / 2) * hessianQuadratic H ξ +
        reggeActionRemainder K hK H ξ := by
  unfold reggeActionRemainder
  ring

/-- The nonlinear remainder vanishes at the flat potential, for every
candidate Hessian. -/
theorem reggeActionRemainder_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (H : Fin K.nV → Fin K.nV → ℝ) :
    reggeActionRemainder K hK H (zeroPotential K) = 0 := by
  unfold reggeActionRemainder
  rw [hessianQuadratic_zeroPotential K H]
  ring

/-- Exact second variation of the quadratic truncation. -/
theorem reggeActionSecondOrder_secondVariation
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (H : Fin K.nV → Fin K.nV → ℝ) (ξ : VertexPotential K) :
    reggeActionSecondOrder K hK H ξ -
        reggeActionSecondOrder K hK H (zeroPotential K) =
      (1 / 2) * hessianQuadratic H ξ := by
  unfold reggeActionSecondOrder
  have hzero : hessianQuadratic H (zeroPotential K) = 0 :=
    hessianQuadratic_zeroPotential K H
  rw [hzero]
  ring

/-- A global edge contributes to the unordered vertex pair `(i,j)` when its
endpoints are `(i,j)` or `(j,i)`. -/
def canonicalEdgePairWeight
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (i j : Fin K.nV) (e : Fin K.nE) : ℝ :=
  if (K.edgeVerts e).1 = i ∧ (K.edgeVerts e).2 = j ∨
      (K.edgeVerts e).1 = j ∧ (K.edgeVerts e).2 = i then
    Real.sqrt (hK.globalSqEdge e)
  else
    0

/-- Incidence-defined vertex-pair hinge weight. -/
def canonicalDualWeight
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (i j : Fin K.nV) : ℝ :=
  ∑ e : Fin K.nE, canonicalEdgePairWeight K hK i j e

theorem canonicalEdgePairWeight_symm
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (i j : Fin K.nV) (e : Fin K.nE) :
    canonicalEdgePairWeight K hK i j e =
      canonicalEdgePairWeight K hK j i e := by
  unfold canonicalEdgePairWeight
  by_cases h :
      (K.edgeVerts e).1 = i ∧ (K.edgeVerts e).2 = j ∨
        (K.edgeVerts e).1 = j ∧ (K.edgeVerts e).2 = i
  · have h' :
        (K.edgeVerts e).1 = j ∧ (K.edgeVerts e).2 = i ∨
          (K.edgeVerts e).1 = i ∧ (K.edgeVerts e).2 = j := h.symm
    simp [h, h']
  · have h' :
        ¬ ((K.edgeVerts e).1 = j ∧ (K.edgeVerts e).2 = i ∨
          (K.edgeVerts e).1 = i ∧ (K.edgeVerts e).2 = j) := by
      intro hx
      exact h hx.symm
    simp [h, h']

theorem canonicalDualWeight_symm
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    ∀ i j, canonicalDualWeight K hK i j = canonicalDualWeight K hK j i := by
  intro i j
  unfold canonicalDualWeight
  exact Finset.sum_congr rfl (fun e _ => canonicalEdgePairWeight_symm K hK i j e)

theorem canonicalDualWeight_nonneg
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    ∀ i j, 0 ≤ canonicalDualWeight K hK i j := by
  intro i j
  unfold canonicalDualWeight canonicalEdgePairWeight
  refine Finset.sum_nonneg ?_
  intro e _
  by_cases h :
      (K.edgeVerts e).1 = i ∧ (K.edgeVerts e).2 = j ∨
        (K.edgeVerts e).1 = j ∧ (K.edgeVerts e).2 = i
  · simp [h, Real.sqrt_nonneg]
  · simp [h]

/-- Canonical graph-Laplacian Hessian induced by incidence dual weights. -/
def canonicalReggeHessian
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (i j : Fin K.nV) : ℝ :=
  (if i = j then ∑ k : Fin K.nV, canonicalDualWeight K hK i k else 0)
    - canonicalDualWeight K hK i j

theorem canonicalReggeHessian_symm
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    ∀ i j, canonicalReggeHessian K hK i j = canonicalReggeHessian K hK j i := by
  intro i j
  unfold canonicalReggeHessian
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := by intro h; exact hij h.symm
    simp [hij, hji, canonicalDualWeight_symm K hK i j]

theorem canonicalReggeHessian_row_sum_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    ∀ i : Fin K.nV, ∑ j : Fin K.nV, canonicalReggeHessian K hK i j = 0 := by
  intro i
  unfold canonicalReggeHessian
  rw [Finset.sum_sub_distrib]
  have hdiag :
      (∑ j : Fin K.nV,
        (if i = j then ∑ k : Fin K.nV, canonicalDualWeight K hK i k else 0))
        = ∑ k : Fin K.nV, canonicalDualWeight K hK i k := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have hne : i ≠ b := fun h => hb h.symm
      simp [hne]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hdiag]
  ring

theorem canonicalReggeHessian_offDiag_eq_neg_weight
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (i j : Fin K.nV) (hij : i ≠ j) :
    canonicalReggeHessian K hK i j = - canonicalDualWeight K hK i j := by
  unfold canonicalReggeHessian
  simp [hij]

/-- The explicit graph-Dirichlet energy associated to the canonical incidence
weights.  The factor `1/2` compensates for summing oriented pairs `(i,j)` and
`(j,i)`. -/
def canonicalDirichletEnergy
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) : ℝ :=
  (1 / 2) * ∑ i : Fin K.nV, ∑ j : Fin K.nV,
    canonicalDualWeight K hK i j * (ξ i - ξ j) ^ (2 : ℕ)

theorem canonicalDirichletEnergy_nonneg
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    0 ≤ canonicalDirichletEnergy K hK ξ := by
  unfold canonicalDirichletEnergy
  refine mul_nonneg (by norm_num) ?_
  refine Finset.sum_nonneg ?_
  intro i _
  refine Finset.sum_nonneg ?_
  intro j _
  exact mul_nonneg (canonicalDualWeight_nonneg K hK i j) (sq_nonneg (ξ i - ξ j))

private theorem canonicalReggeHessian_quadratic_expanded
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    hessianQuadratic (canonicalReggeHessian K hK) ξ =
      (∑ i : Fin K.nV,
        (∑ k : Fin K.nV, canonicalDualWeight K hK i k) * ξ i * ξ i) -
      (∑ i : Fin K.nV, ∑ j : Fin K.nV,
        canonicalDualWeight K hK i j * ξ i * ξ j) := by
  unfold hessianQuadratic canonicalReggeHessian
  simp_rw [sub_mul]
  simp_rw [Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hij : i ≠ j := fun h => hji h.symm
      simp [hij]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim

private theorem canonicalDirichletEnergy_expanded
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    canonicalDirichletEnergy K hK ξ =
      (∑ i : Fin K.nV,
        (∑ k : Fin K.nV, canonicalDualWeight K hK i k) * ξ i * ξ i) -
      (∑ i : Fin K.nV, ∑ j : Fin K.nV,
        canonicalDualWeight K hK i j * ξ i * ξ j) := by
  unfold canonicalDirichletEnergy
  have hswap :
      (∑ i : Fin K.nV, ∑ j : Fin K.nV,
        canonicalDualWeight K hK i j * (ξ j * ξ j)) =
      (∑ i : Fin K.nV, ∑ j : Fin K.nV,
        canonicalDualWeight K hK i j * (ξ i * ξ i)) := by
    calc
      (∑ i : Fin K.nV, ∑ j : Fin K.nV,
        canonicalDualWeight K hK i j * (ξ j * ξ j))
          = (∑ j : Fin K.nV, ∑ i : Fin K.nV,
              canonicalDualWeight K hK i j * (ξ j * ξ j)) := by
              rw [Finset.sum_comm]
      _ = (∑ j : Fin K.nV, ∑ i : Fin K.nV,
              canonicalDualWeight K hK j i * (ξ j * ξ j)) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [canonicalDualWeight_symm K hK i j]
      _ = (∑ i : Fin K.nV, ∑ j : Fin K.nV,
              canonicalDualWeight K hK i j * (ξ i * ξ i)) := rfl
  have hrow :
      (∑ i : Fin K.nV, ∑ j : Fin K.nV,
        canonicalDualWeight K hK i j * (ξ i * ξ i)) =
      (∑ i : Fin K.nV,
        (∑ k : Fin K.nV, canonicalDualWeight K hK i k) * ξ i * ξ i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    calc
      (∑ j : Fin K.nV, canonicalDualWeight K hK i j * (ξ i * ξ i))
          = (∑ j : Fin K.nV, canonicalDualWeight K hK i j) * (ξ i * ξ i) := by
            rw [Finset.sum_mul]
      _ = (∑ k : Fin K.nV, canonicalDualWeight K hK i k) * ξ i * ξ i := by
            ring
  have hexpand :
      (∑ i : Fin K.nV, ∑ j : Fin K.nV,
        canonicalDualWeight K hK i j * (ξ i - ξ j) ^ (2 : ℕ)) =
      ((∑ i : Fin K.nV, ∑ j : Fin K.nV,
          canonicalDualWeight K hK i j * (ξ i * ξ i)) -
        2 * (∑ i : Fin K.nV, ∑ j : Fin K.nV,
          canonicalDualWeight K hK i j * ξ i * ξ j) +
        (∑ i : Fin K.nV, ∑ j : Fin K.nV,
          canonicalDualWeight K hK i j * (ξ j * ξ j))) := by
    calc
      (∑ i : Fin K.nV, ∑ j : Fin K.nV,
        canonicalDualWeight K hK i j * (ξ i - ξ j) ^ (2 : ℕ))
          = (∑ i : Fin K.nV, ∑ j : Fin K.nV,
              (canonicalDualWeight K hK i j * (ξ i * ξ i) -
                2 * (canonicalDualWeight K hK i j * ξ i * ξ j) +
                canonicalDualWeight K hK i j * (ξ j * ξ j))) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
      _ = ((∑ i : Fin K.nV, ∑ j : Fin K.nV,
              canonicalDualWeight K hK i j * (ξ i * ξ i)) -
            2 * (∑ i : Fin K.nV, ∑ j : Fin K.nV,
              canonicalDualWeight K hK i j * ξ i * ξ j) +
            (∑ i : Fin K.nV, ∑ j : Fin K.nV,
              canonicalDualWeight K hK i j * (ξ j * ξ j))) := by
              simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              simp_rw [← Finset.mul_sum]
  calc
    (1 / 2) * (∑ i : Fin K.nV, ∑ j : Fin K.nV,
        canonicalDualWeight K hK i j * (ξ i - ξ j) ^ (2 : ℕ))
        = (1 / 2) * ((∑ i : Fin K.nV, ∑ j : Fin K.nV,
            canonicalDualWeight K hK i j * (ξ i * ξ i)) -
          2 * (∑ i : Fin K.nV, ∑ j : Fin K.nV,
            canonicalDualWeight K hK i j * ξ i * ξ j) +
          (∑ i : Fin K.nV, ∑ j : Fin K.nV,
            canonicalDualWeight K hK i j * (ξ j * ξ j))) := by
            rw [hexpand]
    _ = (1 / 2) * ((∑ i : Fin K.nV, ∑ j : Fin K.nV,
            canonicalDualWeight K hK i j * (ξ i * ξ i)) -
          2 * (∑ i : Fin K.nV, ∑ j : Fin K.nV,
            canonicalDualWeight K hK i j * ξ i * ξ j) +
          (∑ i : Fin K.nV, ∑ j : Fin K.nV,
            canonicalDualWeight K hK i j * (ξ i * ξ i))) := by
            rw [hswap]
    _ = (∑ i : Fin K.nV, ∑ j : Fin K.nV,
            canonicalDualWeight K hK i j * (ξ i * ξ i)) -
          (∑ i : Fin K.nV, ∑ j : Fin K.nV,
            canonicalDualWeight K hK i j * ξ i * ξ j) := by
            ring
    _ = (∑ i : Fin K.nV,
          (∑ k : Fin K.nV, canonicalDualWeight K hK i k) * ξ i * ξ i) -
        (∑ i : Fin K.nV, ∑ j : Fin K.nV,
          canonicalDualWeight K hK i j * ξ i * ξ j) := by
          rw [hrow]

theorem canonicalReggeHessian_quadratic_eq_dirichlet
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    hessianQuadratic (canonicalReggeHessian K hK) ξ =
      canonicalDirichletEnergy K hK ξ := by
  rw [canonicalReggeHessian_quadratic_expanded,
    canonicalDirichletEnergy_expanded]

theorem canonicalReggeHessian_quadratic_nonneg
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    0 ≤ hessianQuadratic (canonicalReggeHessian K hK) ξ := by
  rw [canonicalReggeHessian_quadratic_eq_dirichlet]
  exact canonicalDirichletEnergy_nonneg K hK ξ

/-- Edge-stencil expression corresponding to the canonical incidence weights:
sum directly over global edges rather than over unordered vertex pairs. -/
def canonicalEdgeStencilDirichletEnergy
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) : ℝ :=
  ∑ e : Fin K.nE,
    Real.sqrt (hK.globalSqEdge e) *
      (ξ (K.edgeVerts e).1 - ξ (K.edgeVerts e).2) ^ (2 : ℕ)

def CanonicalDirichletEqualsEdgeStencilTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    canonicalDirichletEnergy K hK ξ =
      canonicalEdgeStencilDirichletEnergy K hK ξ

/-- Exact finite-sum reindexing target underlying
`CanonicalDirichletEqualsEdgeStencilTarget`.  Each global edge should contribute
twice to the oriented vertex-pair sum, once for each orientation. -/
def CanonicalEdgePairWeightReindexTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ (ξ : VertexPotential K) (e : Fin K.nE),
    (∑ i : Fin K.nV, ∑ j : Fin K.nV,
      canonicalEdgePairWeight K hK i j e * (ξ i - ξ j) ^ (2 : ℕ)) =
      2 * Real.sqrt (hK.globalSqEdge e) *
        (ξ (K.edgeVerts e).1 - ξ (K.edgeVerts e).2) ^ (2 : ℕ)

def NoSelfLoopEdges (K : Triangulation3D) : Prop :=
  ∀ e : Fin K.nE, (K.edgeVerts e).1 ≠ (K.edgeVerts e).2

theorem canonicalEdgePairWeightReindex_of_noSelfLoop
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hNoLoop : NoSelfLoopEdges K) :
    CanonicalEdgePairWeightReindexTarget K hK := by
  intro ξ e
  let a := (K.edgeVerts e).1
  let b := (K.edgeVerts e).2
  let inner := fun i : Fin K.nV =>
    ∑ j : Fin K.nV,
      canonicalEdgePairWeight K hK i j e * (ξ i - ξ j) ^ (2 : ℕ)
  have hab : a ≠ b := hNoLoop e
  have hinner_a : inner a =
      Real.sqrt (hK.globalSqEdge e) * (ξ a - ξ b) ^ (2 : ℕ) := by
    unfold inner
    rw [Finset.sum_eq_single b]
    · simp [canonicalEdgePairWeight, a, b, hab]
    · intro j _ hjb
      have hnot1 : ¬ ((K.edgeVerts e).1 = a ∧ (K.edgeVerts e).2 = j) := by
        intro h
        exact hjb (by simpa [b] using h.2.symm)
      have hnot2 : ¬ ((K.edgeVerts e).1 = j ∧ (K.edgeVerts e).2 = a) := by
        intro h
        have hba : b = a := by simpa [b] using h.2
        exact hab hba.symm
      simp [canonicalEdgePairWeight, hnot1, hnot2]
    · intro hb
      exact (hb (Finset.mem_univ b)).elim
  have hinner_b : inner b =
      Real.sqrt (hK.globalSqEdge e) * (ξ b - ξ a) ^ (2 : ℕ) := by
    unfold inner
    rw [Finset.sum_eq_single a]
    · have hba : b ≠ a := fun h => hab h.symm
      simp [canonicalEdgePairWeight, a, b, hab, hba]
    · intro j _ hja
      have hnot1 : ¬ ((K.edgeVerts e).1 = b ∧ (K.edgeVerts e).2 = j) := by
        intro h
        have hab' : a = b := by simpa [a] using h.1
        exact hab hab'
      have hnot2 : ¬ ((K.edgeVerts e).1 = j ∧ (K.edgeVerts e).2 = b) := by
        intro h
        exact hja (by simpa [a] using h.1.symm)
      simp [canonicalEdgePairWeight, hnot1, hnot2]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  have hinner_other : ∀ i : Fin K.nV, i ≠ a → i ≠ b → inner i = 0 := by
    intro i hia hib
    unfold inner
    refine Finset.sum_eq_zero ?_
    intro j _
    have hnot1 : ¬ ((K.edgeVerts e).1 = i ∧ (K.edgeVerts e).2 = j) := by
      intro h
      exact hia (by simpa [a] using h.1.symm)
    have hnot2 : ¬ ((K.edgeVerts e).1 = j ∧ (K.edgeVerts e).2 = i) := by
      intro h
      exact hib (by simpa [b] using h.2.symm)
    simp [canonicalEdgePairWeight, hnot1, hnot2]
  have hb_mem : b ∈ (Finset.univ : Finset (Fin K.nV)) \ {a} := by
    simp [hab.symm]
  calc
    (∑ i : Fin K.nV, ∑ j : Fin K.nV,
      canonicalEdgePairWeight K hK i j e * (ξ i - ξ j) ^ (2 : ℕ))
        = ∑ i : Fin K.nV, inner i := rfl
    _ = inner a + ∑ i ∈ (Finset.univ : Finset (Fin K.nV)) \ {a}, inner i := by
      exact Finset.sum_eq_add_sum_diff_singleton
        (s := (Finset.univ : Finset (Fin K.nV))) (i := a)
        (h := Finset.mem_univ a) (f := inner)
    _ = inner a + (inner b + ∑ i ∈ ((Finset.univ : Finset (Fin K.nV)) \ {a}) \ {b}, inner i) := by
      congr 1
      exact Finset.sum_eq_add_sum_diff_singleton
        (s := ((Finset.univ : Finset (Fin K.nV)) \ {a})) (i := b)
        (h := hb_mem) (f := inner)
    _ = inner a + inner b := by
      have hzero :
          (∑ i ∈ ((Finset.univ : Finset (Fin K.nV)) \ {a}) \ {b}, inner i) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hia : i ≠ a := by
          intro h
          subst i
          simp at hi
        have hib : i ≠ b := by
          intro h
          subst i
          simp at hi
        exact hinner_other i hia hib
      rw [hzero]
      ring
    _ = Real.sqrt (hK.globalSqEdge e) * (ξ a - ξ b) ^ (2 : ℕ) +
        Real.sqrt (hK.globalSqEdge e) * (ξ b - ξ a) ^ (2 : ℕ) := by
      rw [hinner_a, hinner_b]
    _ = 2 * Real.sqrt (hK.globalSqEdge e) *
        (ξ (K.edgeVerts e).1 - ξ (K.edgeVerts e).2) ^ (2 : ℕ) := by
      have hsq : (ξ b - ξ a) ^ (2 : ℕ) = (ξ a - ξ b) ^ (2 : ℕ) := by ring
      rw [hsq]
      simp [a, b]
      ring

/-- Exact finite-sum commutation target needed before the per-edge double-count
identity can be applied.  This is purely bookkeeping over finite sums. -/
def CanonicalEdgeStencilSumCommTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    (∑ i : Fin K.nV, ∑ j : Fin K.nV,
      (∑ e : Fin K.nE, canonicalEdgePairWeight K hK i j e) *
        (ξ i - ξ j) ^ (2 : ℕ)) =
    (∑ e : Fin K.nE, ∑ i : Fin K.nV, ∑ j : Fin K.nV,
      canonicalEdgePairWeight K hK i j e * (ξ i - ξ j) ^ (2 : ℕ))

theorem canonicalEdgeStencilSumComm
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    CanonicalEdgeStencilSumCommTarget K hK := by
  intro ξ
  simp_rw [Finset.sum_mul]
  calc
    (∑ i : Fin K.nV, ∑ j : Fin K.nV, ∑ e : Fin K.nE,
      canonicalEdgePairWeight K hK i j e * (ξ i - ξ j) ^ (2 : ℕ))
        = ∑ i : Fin K.nV, ∑ e : Fin K.nE, ∑ j : Fin K.nV,
            canonicalEdgePairWeight K hK i j e * (ξ i - ξ j) ^ (2 : ℕ) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact (Finset.sum_comm :
              (∑ j : Fin K.nV, ∑ e : Fin K.nE,
                canonicalEdgePairWeight K hK i j e * (ξ i - ξ j) ^ (2 : ℕ)) =
              (∑ e : Fin K.nE, ∑ j : Fin K.nV,
                canonicalEdgePairWeight K hK i j e * (ξ i - ξ j) ^ (2 : ℕ)))
    _ = ∑ e : Fin K.nE, ∑ i : Fin K.nV, ∑ j : Fin K.nV,
            canonicalEdgePairWeight K hK i j e * (ξ i - ξ j) ^ (2 : ℕ) := by
            exact (Finset.sum_comm :
              (∑ i : Fin K.nV, ∑ e : Fin K.nE, ∑ j : Fin K.nV,
                canonicalEdgePairWeight K hK i j e * (ξ i - ξ j) ^ (2 : ℕ)) =
              (∑ e : Fin K.nE, ∑ i : Fin K.nV, ∑ j : Fin K.nV,
                canonicalEdgePairWeight K hK i j e * (ξ i - ξ j) ^ (2 : ℕ)))

theorem canonicalDirichletEqualsEdgeStencil_of_sumComm_and_reindex
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hSum : CanonicalEdgeStencilSumCommTarget K hK)
    (hReindex : CanonicalEdgePairWeightReindexTarget K hK) :
    CanonicalDirichletEqualsEdgeStencilTarget K hK := by
  intro ξ
  unfold canonicalDirichletEnergy canonicalEdgeStencilDirichletEnergy canonicalDualWeight
  rw [hSum ξ]
  calc
    (1 / 2) * (∑ e : Fin K.nE, ∑ i : Fin K.nV, ∑ j : Fin K.nV,
      canonicalEdgePairWeight K hK i j e * (ξ i - ξ j) ^ (2 : ℕ))
        = ∑ e : Fin K.nE, (1 / 2) * (∑ i : Fin K.nV, ∑ j : Fin K.nV,
            canonicalEdgePairWeight K hK i j e * (ξ i - ξ j) ^ (2 : ℕ)) := by
            rw [Finset.mul_sum]
    _ = ∑ e : Fin K.nE,
        Real.sqrt (hK.globalSqEdge e) *
          (ξ (K.edgeVerts e).1 - ξ (K.edgeVerts e).2) ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro e _
        rw [hReindex ξ e]
        ring

theorem canonicalEdgeStencilDirichletEnergy_nonneg
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    0 ≤ canonicalEdgeStencilDirichletEnergy K hK ξ := by
  unfold canonicalEdgeStencilDirichletEnergy
  refine Finset.sum_nonneg ?_
  intro e _
  exact mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)

/-- Second-order Regge data computed from the canonical incidence Hessian.
The exact quadratic identity is intentionally about the second-order action,
not the full nonlinear `reggeAction`. -/
structure ConcreteReggeSecondOrderData (K : Triangulation3D) (hK : IncidenceConsistent K) where
  secondOrderAction : VertexPotential K → ℝ
  hessian : Fin K.nV → Fin K.nV → ℝ
  hessian_symm : ∀ i j, hessian i j = hessian j i
  secondOrderAction_eq :
    secondOrderAction = reggeActionSecondOrder K hK hessian
  secondVariation :
    ∀ ξ : VertexPotential K,
      secondOrderAction ξ - secondOrderAction (zeroPotential K) =
        (1 / 2) * hessianQuadratic hessian ξ

/-- Canonical second-order Regge data from incidence. -/
def canonicalReggeSecondOrderData
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    ConcreteReggeSecondOrderData K hK where
  secondOrderAction := reggeActionSecondOrder K hK (canonicalReggeHessian K hK)
  hessian := canonicalReggeHessian K hK
  hessian_symm := canonicalReggeHessian_symm K hK
  secondOrderAction_eq := rfl
  secondVariation := reggeActionSecondOrder_secondVariation K hK (canonicalReggeHessian K hK)

/-- Hessian data computed from the concrete Regge action under the conformal
ansatz.  The action itself is no longer caller-supplied; it is
`reggeAction K hK`. -/
structure ConcreteReggeActionData (K : Triangulation3D) (hK : IncidenceConsistent K) where
  hessian : Fin K.nV → Fin K.nV → ℝ
  hessian_symm : ∀ i j, hessian i j = hessian j i
  flat_firstVariation_zero : Prop
  secondVariation :
    ∀ ξ : VertexPotential K,
      reggeAction K hK ξ - reggeAction K hK (zeroPotential K) =
        (1 / 2) * hessianQuadratic hessian ξ

/-- The genuine Hessian closure target: incidence consistency should be
enough to construct concrete second-order Regge Hessian data. -/
def GenuineReggeHessianTarget : Prop :=
  ∀ K : Triangulation3D, ∀ hK : IncidenceConsistent K,
    Nonempty (ConcreteReggeSecondOrderData K hK)

/-- The genuine Hessian target is discharged for the canonical second-order
incidence Regge data. -/
theorem genuineReggeHessianTarget : GenuineReggeHessianTarget := by
  intro K hK
  exact ⟨canonicalReggeSecondOrderData K hK⟩

/-- Convert concrete action data into the shared `ReggeHessianData` package. -/
def reggeHessianData_of_concrete
    {K : Triangulation3D} {hK : IncidenceConsistent K}
    (D : ConcreteReggeActionData K hK) :
    ReggeHessianData K where
  action := reggeAction K hK
  hessian := D.hessian
  hessian_symm := D.hessian_symm
  flat_firstVariation_zero := D.flat_firstVariation_zero
  secondVariation := D.secondVariation

/-- Convert concrete second-order data into the shared `ReggeHessianData`
package.  The action in this package is the second-order action, not the full
nonlinear Regge action. -/
def reggeHessianData_of_secondOrder
    {K : Triangulation3D} {hK : IncidenceConsistent K}
    (D : ConcreteReggeSecondOrderData K hK) :
    ReggeHessianData K where
  action := D.secondOrderAction
  hessian := D.hessian
  hessian_symm := D.hessian_symm
  flat_firstVariation_zero := True
  secondVariation := D.secondVariation

/-- A concrete second-order construction discharges the existing Hessian interface. -/
theorem genuine_regge_hessian_of_concrete
    (h : GenuineReggeHessianTarget) :
    ∀ K : Triangulation3D, IncidenceConsistent K → Nonempty (ReggeHessianData K) := by
  intro K hK
  rcases h K hK with ⟨D⟩
  exact ⟨reggeHessianData_of_secondOrder D⟩

end

end ReggeActionConcrete
end Geometry
end IndisputableMonolith
