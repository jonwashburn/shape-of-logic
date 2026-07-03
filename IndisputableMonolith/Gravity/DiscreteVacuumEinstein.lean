import Mathlib
import IndisputableMonolith.Geometry.ReggeActionSecondVariation

/-!
# Discrete Vacuum Einstein Equation for the Nonlinear Regge Action

The Regge vacuum equation is zero deficit at every hinge.  For the conformal
nonlinear action, the forward direction follows from zero deficit plus global
Schläfli cancellation; the reverse direction needs a rank/nondegeneracy input
for the conformal edge-incidence derivative.  This module records the exact
equivalence as a named input rather than an axiom.
-/

namespace IndisputableMonolith
namespace Gravity
namespace DiscreteVacuumEinstein

open Geometry.ReggeTriangulation3D
open Geometry.ReggeHessian3D
open Geometry.Triangulation3DConsistency
open Geometry.ReggeActionConcrete
open Geometry.ReggeActionSmoothness
open Geometry.ReggeActionFirstVariation

noncomputable section

/-- Zero Regge deficit at every global edge of the flat potential. -/
def ZeroDeficitAtFlat (K : Triangulation3D) : Prop :=
  ∀ e : Fin K.nE, deficitAngle K (zeroPotential K) e = 0

/-- The nonlinear Regge action is critical at the flat potential. -/
def CriticalAtFlat
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ReggeActionCriticalAtZero K hK

/-- Vertex-edge incidence coefficient for the conformal derivative of a global
edge length: each endpoint contributes `1/2`. -/
def vertexEdgeIncidenceDerivative
    (K : Triangulation3D) (e : Fin K.nE) (i : Fin K.nV) : ℝ :=
  if (K.edgeVerts e).1 = i ∨ (K.edgeVerts e).2 = i then (1 / 2 : ℝ) else 0

/-- Directional length coefficient for edge `e` in vertex-potential direction
`η`, without the constant edge-length factor. -/
def directionalLengthCoefficient
    (K : Triangulation3D) (η : VertexPotential K) (e : Fin K.nE) : ℝ :=
  ∑ i : Fin K.nV, vertexEdgeIncidenceDerivative K e i * η i

/-- Compatibility between the geometric hinge derivative and the endpoint
incidence coefficient used in the vacuum equation.  This isolates the
normalization issue: the geometric derivative includes the flat edge length,
whereas the incidence formula is dimensionless. -/
def HingeDerivativeMatchesIncidence
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ η : VertexPotential K, ∀ e : Fin K.nE,
    Geometry.ReggeActionFirstVariation.hingeMeasureDirectionalDeriv K hK η e =
      deficitAngle K (zeroPotential K) e * 0 +
        Real.sqrt (hK.globalSqEdge e) * directionalLengthCoefficient K η e

theorem hingeDerivative_matches_incidence_simplified
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hMatch : HingeDerivativeMatchesIncidence K hK) :
    ∀ η : VertexPotential K, ∀ e : Fin K.nE,
      Geometry.ReggeActionFirstVariation.hingeMeasureDirectionalDeriv K hK η e =
        Real.sqrt (hK.globalSqEdge e) * directionalLengthCoefficient K η e := by
  intro η e
  simpa using hMatch η e

/-- Incidence rank/separation condition: a deficit vector whose pairing with
every conformal edge-length direction vanishes is zero.  This is a real
condition on the triangulation, not a consequence of local tetrahedron
nondegeneracy. -/
def IncidenceDeficitSeparating (K : Triangulation3D) : Prop :=
  ∀ δ : Fin K.nE → ℝ,
    (∀ η : VertexPotential K,
      ∑ e : Fin K.nE, δ e * directionalLengthCoefficient K η e = 0) →
    δ = 0

/-- Concrete recovery/rank certificate for incidence separation.  The scalar
observations are the directional pairings against vertex-basis potentials. -/
def IncidenceDeficitRecovering (K : Triangulation3D) : Prop :=
  ∃ recover : Fin K.nE → Fin K.nV → ℝ,
    ∀ δ : Fin K.nE → ℝ, ∀ e : Fin K.nE,
      δ e =
        ∑ i : Fin K.nV,
          recover e i *
            (∑ e' : Fin K.nE,
              δ e' * directionalLengthCoefficient K
                (fun j : Fin K.nV => if j = i then (1 : ℝ) else 0) e')

theorem incidenceDeficitSeparating_of_recovering
    (K : Triangulation3D)
    (hRecover : IncidenceDeficitRecovering K) :
    IncidenceDeficitSeparating K := by
  rcases hRecover with ⟨recover, hrecover⟩
  intro δ hpair
  funext e
  rw [hrecover δ e]
  apply Finset.sum_eq_zero
  intro i _
  rw [hpair (fun j : Fin K.nV => if j = i then (1 : ℝ) else 0)]
  ring

/-- Intended triangulation class for the reverse vacuum implication: the
vertex-edge incidence observations recover every edge-deficit vector. -/
structure RecoveringIncidenceTriangulation (K : Triangulation3D) where
  recovery : IncidenceDeficitRecovering K

theorem RecoveringIncidenceTriangulation.separating
    {K : Triangulation3D} (R : RecoveringIncidenceTriangulation K) :
    IncidenceDeficitSeparating K :=
  incidenceDeficitSeparating_of_recovering K R.recovery

/-- First-variation formula before imposing zero deficit: the derivative of
the action pairs the deficit vector with conformal edge-length directions. -/
structure ReggeFirstVariationFormula
    (K : Triangulation3D) (hK : IncidenceConsistent K) where
  variation_formula :
    ∀ η : VertexPotential K,
      fderiv ℝ (reggeAction K hK) (zeroPotential K) η =
        ∑ e : Fin K.nE,
          deficitAngle K (zeroPotential K) e *
            directionalLengthCoefficient K η e

/-- Convert the geometry-layer first-variation formula into the dimensionless
vacuum formula when the hinge-length normalization is known to be harmless.
The cleanest case is unit flat edge length, encoded as
`sqrt (globalSqEdge e) = 1`. -/
def ReggeFirstVariationFormula.ofGeometryFormula_unitEdges
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hGeom : Geometry.ReggeActionFirstVariation.ReggeActionFirstVariationFormula K hK)
    (hUnit : ∀ e : Fin K.nE, Real.sqrt (hK.globalSqEdge e) = 1)
    (hCoeff :
      ∀ η : VertexPotential K, ∀ e : Fin K.nE,
        Geometry.ReggeActionFirstVariation.hingeMeasureDirectionalDeriv K hK η e =
          Real.sqrt (hK.globalSqEdge e) * directionalLengthCoefficient K η e) :
    ReggeFirstVariationFormula K hK where
  variation_formula := by
    intro η
    rw [hGeom.firstVariation_formula η]
    refine Finset.sum_congr rfl ?_
    intro e _
    rw [hCoeff η e, hUnit e]
    ring

theorem zero_deficit_of_flat_configuration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK) :
    ZeroDeficitAtFlat K :=
  h_flat.flat_deficit_zero

/-- Named discrete-vacuum-Einstein input.  The nontrivial reverse implication
is the incidence-rank theorem: if all conformal first variations vanish, then
each edge deficit is zero. -/
structure DiscreteVacuumEinsteinInput
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (_h_flat : FlatConfiguration K hK) where
  critical_iff_zero_deficit :
    CriticalAtFlat K hK ↔ ZeroDeficitAtFlat K

/-- Phase-F discrete vacuum Einstein equivalence. -/
theorem reggeAction_critical_iff_zero_deficit
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (h_einstein : DiscreteVacuumEinsteinInput K hK h_flat) :
    CriticalAtFlat K hK ↔ ZeroDeficitAtFlat K :=
  h_einstein.critical_iff_zero_deficit

theorem zero_deficit_of_critical_of_variationFormula_of_separating
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFormula : ReggeFirstVariationFormula K hK)
    (hSep : IncidenceDeficitSeparating K)
    (hCrit : CriticalAtFlat K hK) :
    ZeroDeficitAtFlat K := by
  unfold CriticalAtFlat ReggeActionCriticalAtZero at hCrit
  unfold ZeroDeficitAtFlat
  have hdelta :
      (fun e : Fin K.nE => deficitAngle K (zeroPotential K) e) = 0 := by
    apply hSep
    intro η
    have happly := congrArg (fun L : VertexPotential K →L[ℝ] ℝ => L η) hCrit
    have hzero :
        (fderiv ℝ (reggeAction K hK) (zeroPotential K)) η = 0 := by
      simpa using happly
    have hformula := hFormula.variation_formula η
    rw [hformula] at hzero
    simpa using hzero
  intro e
  exact congrFun hdelta e

/-- Construct the old vacuum-Einstein input from an explicit first-variation
formula, a first-variation theorem for zero-deficit flat backgrounds, and the
incidence separation/rank condition. -/
def discreteVacuumEinsteinInput_of_variationFormula_of_separating
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (hFirst : ReggeActionFirstVariationInput K hK h_flat)
    (hFormula : ReggeFirstVariationFormula K hK)
    (hSep : IncidenceDeficitSeparating K) :
    DiscreteVacuumEinsteinInput K hK h_flat where
  critical_iff_zero_deficit := by
    constructor
    · intro hCrit
      exact zero_deficit_of_critical_of_variationFormula_of_separating
        K hK hFormula hSep hCrit
    · intro _hZero
      exact hFirst.firstVariation_zero

def discreteVacuumEinsteinInput_of_recoveringIncidence
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (hFirst : ReggeActionFirstVariationInput K hK h_flat)
    (hFormula : ReggeFirstVariationFormula K hK)
    (R : RecoveringIncidenceTriangulation K) :
    DiscreteVacuumEinsteinInput K hK h_flat :=
  discreteVacuumEinsteinInput_of_variationFormula_of_separating
    K hK h_flat hFirst hFormula R.separating

end

end DiscreteVacuumEinstein
end Gravity
end IndisputableMonolith
