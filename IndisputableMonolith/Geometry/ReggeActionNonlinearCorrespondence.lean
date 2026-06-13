import IndisputableMonolith.Geometry.ReggeActionCubicTaylorBound
import IndisputableMonolith.Cost.FunctionalEquation

/-!
# Nonlinear Regge/J-Cost Correspondence Target

The first Recognition Gravity paper closes the weak-field quadratic bridge.
This module states the follow-on nonlinear target without claiming global exact
equality between the full Regge action and a summed J-cost action.

The theorem surface is local: near a flat configuration, the full nonlinear
Regge action equals its flat value plus the canonical J/Dirichlet quadratic
term, with an explicitly bounded cubic Taylor remainder.
-/

namespace IndisputableMonolith
namespace Geometry
namespace ReggeActionNonlinearCorrespondence

open ReggeTriangulation3D
open ReggeHessian3D
open Triangulation3DConsistency
open ReggeActionConcrete
open ReggeActionSmoothness
open ReggeActionSecondVariation
open ReggeActionNonlinearHessianProof
open ReggeActionCubicTaylorBound

noncomputable section

/-- J-cost in log coordinates. -/
def jCostLog (t : ℝ) : ℝ :=
  Cost.Jcost (Real.exp t)

theorem jCostLog_eq_cosh_sub_one (t : ℝ) :
    jCostLog t = Real.cosh t - 1 := by
  simpa [jCostLog, Cost.FunctionalEquation.G] using
    Cost.FunctionalEquation.Jcost_G_eq_cosh_sub_one t

theorem jCostLog_neg (t : ℝ) :
    jCostLog (-t) = jCostLog t := by
  rw [jCostLog_eq_cosh_sub_one, jCostLog_eq_cosh_sub_one]
  rw [Real.cosh_neg]

/-- The full weighted J-cost edge action associated to the canonical incidence
weights.  This is the nonlinear J-cost expression; the present local theorem
uses only its quadratic jet. -/
def weightedJCostAction
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) : ℝ :=
  ∑ i : Fin K.nV, ∑ j : Fin K.nV,
    canonicalDualWeight K hK i j * jCostLog (ξ i - ξ j)

theorem weightedJCostAction_neg
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    weightedJCostAction K hK (-ξ) = weightedJCostAction K hK ξ := by
  unfold weightedJCostAction
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  change canonicalDualWeight K hK i j * jCostLog ((-ξ) i - (-ξ) j) =
    canonicalDualWeight K hK i j * jCostLog (ξ i - ξ j)
  congr 1
  have harg : ((-ξ) i - (-ξ) j) = -(ξ i - ξ j) := by
    simp
    ring
  rw [harg, jCostLog_neg]

theorem weightedJCostAction_along_line_even
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    Function.Even
      (fun t : ℝ => weightedJCostAction K hK (linePotential K ξ t)) := by
  intro t
  change weightedJCostAction K hK (linePotential K ξ (-t)) =
    weightedJCostAction K hK (linePotential K ξ t)
  have hline : linePotential K ξ (-t) = -(linePotential K ξ t) := by
    funext i
    simp [linePotential]
  rw [hline]
  exact weightedJCostAction_neg K hK (linePotential K ξ t)

/-- The canonical quadratic J/Dirichlet term supplied by the Regge incidence
Hessian.  This is the term that the full nonlinear Regge action sees to second
order at a flat background. -/
def canonicalJQuadraticTerm
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) : ℝ :=
  (1 / 2) * hessianQuadratic (canonicalReggeHessian K hK) ξ

theorem canonicalJQuadraticTerm_eq_dirichlet
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    canonicalJQuadraticTerm K hK ξ =
      (1 / 2) * canonicalDirichletEnergy K hK ξ := by
  unfold canonicalJQuadraticTerm
  rw [canonicalReggeHessian_quadratic_eq_dirichlet]

theorem canonicalJQuadraticTerm_nonneg
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    0 ≤ canonicalJQuadraticTerm K hK ξ := by
  rw [canonicalJQuadraticTerm_eq_dirichlet]
  exact mul_nonneg (by norm_num) (canonicalDirichletEnergy_nonneg K hK ξ)

/-- Exact algebraic split of the full nonlinear Regge action into the flat
value, the canonical quadratic J/Dirichlet term, and the nonlinear remainder. -/
theorem nonlinearRegge_exact_canonical_split
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    reggeAction K hK ξ =
      reggeAction K hK (zeroPotential K) +
        canonicalJQuadraticTerm K hK ξ +
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ := by
  simpa [canonicalJQuadraticTerm] using
    reggeAction_taylor_decomposition K hK (canonicalReggeHessian K hK) ξ

/-- Local nonlinear Regge/J-cost correspondence: the full action differs from
its flat value plus the canonical J/Dirichlet quadratic jet by a cubic
remainder. -/
def NonlinearReggeJCostLocalCorrespondence
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
    ∀ ξ : VertexPotential K, ‖ξ‖ < r →
      ‖reggeAction K hK ξ -
          reggeAction K hK (zeroPotential K) -
          canonicalJQuadraticTerm K hK ξ‖ ≤
        C * ‖ξ‖ ^ (3 : ℕ)

/-- The strongest true nonlinear Regge/J-cost replacement theorem surface.

This is deliberately local and quadratic-core: it says the full nonlinear
Regge action equals its flat value plus the canonical J/Dirichlet quadratic
term up to a controlled cubic remainder.  It does not assert literal equality
with the full weighted J-cost action. -/
def StrongestTrueReggeJCostReplacement
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  NonlinearReggeJCostLocalCorrespondence K hK

theorem strongestTrueReggeJCostReplacement_iff_localCorrespondence
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    StrongestTrueReggeJCostReplacement K hK ↔
      NonlinearReggeJCostLocalCorrespondence K hK :=
  Iff.rfl

theorem nonlinearRegge_localCorrespondence_of_cubicBound
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hBound : LocalCubicRemainderBound K hK) :
    NonlinearReggeJCostLocalCorrespondence K hK := by
  rcases hBound with ⟨r, C, hr, hC, hineq⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro ξ hξ
  simpa [NonlinearReggeJCostLocalCorrespondence, canonicalJQuadraticTerm,
    reggeActionRemainder, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using hineq ξ hξ

theorem nonlinearRegge_localCorrespondence_of_taylorTheorem
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hTaylor : NonlinearReggeCubicTaylorTheorem K hK) :
    NonlinearReggeJCostLocalCorrespondence K hK :=
  nonlinearRegge_localCorrespondence_of_cubicBound K hK hTaylor

theorem nonlinearRegge_localCorrespondence_of_localHessianTaylorInputs
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hInputs : NonlinearReggeLocalHessianTaylorInputs K hK hFlat) :
    NonlinearReggeJCostLocalCorrespondence K hK :=
  nonlinearRegge_localCorrespondence_of_cubicBound K hK
    hInputs.cubic_remainder.cubic_bound

theorem nonlinearRegge_localCorrespondence_of_eventuallyZero_edgeStencil_and_taylor
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hZero : WeightedDeficitDerivativeEventuallyZeroTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK)
    (hTaylor : NonlinearReggeCubicTaylorTheorem K hK) :
    NonlinearReggeJCostLocalCorrespondence K hK :=
  nonlinearRegge_localCorrespondence_of_localHessianTaylorInputs K hK hFlat
    (nonlinearReggeLocalHessianTaylorInputs_of_eventuallyZero_edgeStencil_and_taylor
      K hK hFlat D hZero hEdge hStencil hTaylor)

theorem strongestTrueReggeJCostReplacement_of_eventuallyZero_edgeStencil_and_taylor
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hZero : WeightedDeficitDerivativeEventuallyZeroTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK)
    (hTaylor : NonlinearReggeCubicTaylorTheorem K hK) :
    StrongestTrueReggeJCostReplacement K hK :=
  nonlinearRegge_localCorrespondence_of_eventuallyZero_edgeStencil_and_taylor
    K hK hFlat D hZero hEdge hStencil hTaylor

theorem nonlinearRegge_localCorrespondence_of_remainder_identically_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hZero :
      ∀ ξ : VertexPotential K,
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ = 0) :
    NonlinearReggeJCostLocalCorrespondence K hK :=
  nonlinearRegge_localCorrespondence_of_taylorTheorem K hK
    (nonlinearReggeCubicTaylorTheorem_of_identically_zero K hK hZero)

end

end ReggeActionNonlinearCorrespondence
end Geometry
end IndisputableMonolith
