import IndisputableMonolith.Gravity.ReggeComponentTheorem3D
import IndisputableMonolith.Geometry.ReggeActionConcrete

/-!
# Final Regge Component Comparison Target

This module separates the independent dual-weight construction from the
weak-field coefficient matrix and records the theorem that turns that
geometric computation into `ReggeComponentComparison`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace ReggeComponentTheorem3DProof

open Geometry.ReggeTriangulation3D
open Geometry.ReggeActionConcrete
open Geometry.Triangulation3DConsistency
open ReggeComponentTheorem3D
open WeakFieldConformalRegge
open Foundation.SimplicialLedger.EdgeLengthFromPsi

noncomputable section

/-- Independent dual weights attached to vertex pairs of a triangulation.
These are geometric data, not defined by negating the Regge coefficient
matrix. -/
structure IndependentDualWeights (K : Triangulation3D) where
  weight : Fin K.nV → Fin K.nV → ℝ
  weight_symm : ∀ i j, weight i j = weight j i
  weight_nonneg : ∀ i j, 0 ≤ weight i j

/-- A global edge contributes to the unordered vertex pair `(i,j)` exactly
when its endpoints are `(i,j)` or `(j,i)`. -/
def edgePairIncidenceWeight
    (K : Triangulation3D) (hK : IncidenceGeometry K)
    (i j : Fin K.nV) (e : Fin K.nE) : ℝ :=
  if (K.edgeVerts e).1 = i ∧ (K.edgeVerts e).2 = j ∨
      (K.edgeVerts e).1 = j ∧ (K.edgeVerts e).2 = i then
    Real.sqrt (hK.globalSqEdge e)
  else
    0

/-- Independent dual/hinge weight for a vertex pair, defined directly from
the incidence-level edge-length chart.  It is not defined by negating a
Regge Hessian coefficient. -/
def vertexPairHingeWeight
    (K : Triangulation3D) (hK : IncidenceGeometry K)
    (i j : Fin K.nV) : ℝ :=
  ∑ e : Fin K.nE, edgePairIncidenceWeight K hK i j e

theorem edgePairIncidenceWeight_symm
    (K : Triangulation3D) (hK : IncidenceGeometry K)
    (i j : Fin K.nV) (e : Fin K.nE) :
    edgePairIncidenceWeight K hK i j e =
      edgePairIncidenceWeight K hK j i e := by
  unfold edgePairIncidenceWeight
  by_cases h :
      (K.edgeVerts e).1 = i ∧ (K.edgeVerts e).2 = j ∨
        (K.edgeVerts e).1 = j ∧ (K.edgeVerts e).2 = i
  · have h' :
        (K.edgeVerts e).1 = j ∧ (K.edgeVerts e).2 = i ∨
          (K.edgeVerts e).1 = i ∧ (K.edgeVerts e).2 = j := by
      exact h.symm
    simp [h, h']
  · have h' :
        ¬ ((K.edgeVerts e).1 = j ∧ (K.edgeVerts e).2 = i ∨
          (K.edgeVerts e).1 = i ∧ (K.edgeVerts e).2 = j) := by
      intro hx
      exact h hx.symm
    simp [h, h']

theorem vertexPairHingeWeight_symm
    (K : Triangulation3D) (hK : IncidenceGeometry K)
    (i j : Fin K.nV) :
    vertexPairHingeWeight K hK i j = vertexPairHingeWeight K hK j i := by
  unfold vertexPairHingeWeight
  refine Finset.sum_congr rfl ?_
  intro e _
  exact edgePairIncidenceWeight_symm K hK i j e

/-- Nonnegativity of the independent incidence-defined weights, assuming the
global squared-edge chart is nonnegative. -/
theorem vertexPairHingeWeight_nonneg
    (K : Triangulation3D) (hK : IncidenceGeometry K)
    (i j : Fin K.nV) :
    0 ≤ vertexPairHingeWeight K hK i j := by
  unfold vertexPairHingeWeight edgePairIncidenceWeight
  refine Finset.sum_nonneg ?_
  intro e _
  by_cases h :
      (K.edgeVerts e).1 = i ∧ (K.edgeVerts e).2 = j ∨
        (K.edgeVerts e).1 = j ∧ (K.edgeVerts e).2 = i
  · simp [h, Real.sqrt_nonneg]
  · simp [h]

/-- Incidence-defined independent dual weights. -/
def independentDualWeightsOfIncidence
    (K : Triangulation3D) (hK : IncidenceGeometry K) :
    IndependentDualWeights K where
  weight := vertexPairHingeWeight K hK
  weight_symm := vertexPairHingeWeight_symm K hK
  weight_nonneg := vertexPairHingeWeight_nonneg K hK

/-- Independent dual weights built from an `IncidenceConsistent` chart using
the canonical geometry-layer incidence weights. -/
def independentDualWeightsOfConsistent
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    IndependentDualWeights K where
  weight := Geometry.ReggeActionConcrete.canonicalDualWeight K hK
  weight_symm := Geometry.ReggeActionConcrete.canonicalDualWeight_symm K hK
  weight_nonneg := Geometry.ReggeActionConcrete.canonicalDualWeight_nonneg K hK

/-- Canonical weak-field Regge data induced by the incidence dual weights. -/
def canonicalWeakFieldDataOfIncidence
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    WeakFieldReggeData K.nV :=
  laplacianReggeData
    (Geometry.ReggeActionConcrete.canonicalDualWeight K hK)
    (Geometry.ReggeActionConcrete.canonicalDualWeight_symm K hK)

theorem canonicalWeakFieldData_bilinearCoefficient
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (i j : Fin K.nV) :
    bilinearCoefficient (canonicalWeakFieldDataOfIncidence K hK) i j =
      Geometry.ReggeActionConcrete.canonicalReggeHessian K hK i j := by
  unfold canonicalWeakFieldDataOfIncidence
  rw [bilinearCoefficient_laplacianReggeData]
  rfl

theorem canonicalWeakFieldData_rowSum
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    SchlaefliRowSum (canonicalWeakFieldDataOfIncidence K hK) :=
  schlaefliRowSum_laplacianReggeData
    (Geometry.ReggeActionConcrete.canonicalDualWeight K hK)
    (Geometry.ReggeActionConcrete.canonicalDualWeight_symm K hK)

theorem canonicalWeakFieldData_offDiag_component_match
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (i j : Fin K.nV) (hij : i ≠ j) :
    bilinearCoefficient (canonicalWeakFieldDataOfIncidence K hK) i j =
      - (independentDualWeightsOfConsistent K hK).weight i j := by
  rw [canonicalWeakFieldData_bilinearCoefficient]
  exact Geometry.ReggeActionConcrete.canonicalReggeHessian_offDiag_eq_neg_weight K hK i j hij

/-- A concrete component computation from the genuine Regge Hessian. -/
structure ConcreteComponentComparison (K : Triangulation3D) where
  W : WeakFieldReggeData K.nV
  dual : IndependentDualWeights K
  offDiag_component_match :
    ∀ i j, i ≠ j → bilinearCoefficient W i j = - dual.weight i j
  schlaefli_row_sum : SchlaefliRowSum W

/-- The final arbitrary-triangulation component theorem target. -/
def FinalReggeComponentTarget : Prop :=
  ∀ K : Triangulation3D, IncidenceConsistent K →
    Nonempty (ConcreteComponentComparison K)

/-- Concrete component comparison built from canonical incidence weights. -/
def concreteComponentComparisonOfIncidence
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    ConcreteComponentComparison K where
  W := canonicalWeakFieldDataOfIncidence K hK
  dual := independentDualWeightsOfConsistent K hK
  offDiag_component_match := canonicalWeakFieldData_offDiag_component_match K hK
  schlaefli_row_sum := canonicalWeakFieldData_rowSum K hK

/-- The arbitrary-triangulation component target is discharged for the
canonical incidence/Laplacian second-order Regge data. -/
theorem finalReggeComponentTarget : FinalReggeComponentTarget := by
  intro K hK
  exact ⟨concreteComponentComparisonOfIncidence K hK⟩

/-- A concrete component comparison constructs the existing genuine package. -/
def genuineComponentPackage_of_concrete
    {K : Triangulation3D} (C : ConcreteComponentComparison K) :
    GenuineComponentPackage K where
  W := C.W
  geometricArea := C.dual.weight
  geometricArea_symm := C.dual.weight_symm
  geometricArea_nonneg := C.dual.weight_nonneg
  offDiag_component_match := C.offDiag_component_match
  schlaefli_row_sum := C.schlaefli_row_sum

/-- A final concrete component proof discharges `GenuineComponentPackage`. -/
theorem genuine_component_package_of_final
    (h : FinalReggeComponentTarget) :
    ∀ K : Triangulation3D, IncidenceConsistent K →
      Nonempty (GenuineComponentPackage K) := by
  intro K hK
  rcases h K hK with ⟨C⟩
  exact ⟨genuineComponentPackage_of_concrete C⟩

/-- Once the final component package is constructed, the existing Dirichlet
reduction applies immediately. -/
theorem genuine_component_dirichlet_reduction_from_final
    {K : Triangulation3D} (C : ConcreteComponentComparison K)
    (ε : LogPotential K.nV) :
    secondOrderReggeAction C.W ε =
      (1 / 2) * dirichletForm (edgeArea C.W) ε :=
  genuine_component_dirichlet_reduction (genuineComponentPackage_of_concrete C) ε

end

end ReggeComponentTheorem3DProof
end Gravity
end IndisputableMonolith
