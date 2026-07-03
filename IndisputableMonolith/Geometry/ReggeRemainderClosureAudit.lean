import IndisputableMonolith.Geometry.ReggeActionCubicTaylorBound
import IndisputableMonolith.Geometry.ReggeActionNonlinearCorrespondence

/-!
# Regge Remainder Closure Audit

Lane-local audit for Track 1B-REM.  The broad
`ReggeClosureProgressAudit` imports the active finite-Freudenthal
combinatorics module, so this file gives the analytic-remainder branch its own
buildable closure certificate.
-/

namespace IndisputableMonolith
namespace Geometry
namespace ReggeRemainderClosureAudit

open Triangulation3DConsistency
open ReggeHessian3D
open ReggeActionConcrete
open ReggeActionSmoothness
open ReggeActionSecondVariation
open ReggeActionNonlinearHessianProof
open ReggeActionNonlinearCorrespondence

/-- The 1B-REM proof surface needed downstream: every local analytic remainder
target is closed from `FlatConfiguration` plus the standard first- and
second-variation remainder jet inputs. -/
structure RemainderAnalyticClosed where
  closure :
    ∀ (K : ReggeTriangulation3D.Triangulation3D) (hK : IncidenceConsistent K),
      ReggeActionCubicTaylorBound.CanonicalRemainderAnalyticClosureCert K hK

/-- Lane-local theorem-valued certificate for Track 1B-REM. -/
def remainderAnalyticClosed : RemainderAnalyticClosed where
  closure := ReggeActionCubicTaylorBound.canonicalRemainderAnalyticClosureCert

/-- Explicit theorem form for agents that only need the third-derivative bound
and should not import the broad progress audit. -/
theorem canonicalRemainderLineThirdDerivBound_closed
    (K : ReggeTriangulation3D.Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    ReggeActionCubicTaylorBound.CanonicalRemainderLineThirdDerivBoundTarget K hK :=
  (remainderAnalyticClosed.closure K hK).line_third_deriv_bound_from_flat hFlat

/-- Explicit theorem form for the full cubic Taylor theorem endpoint. -/
theorem nonlinearReggeCubicTaylorTheorem_closed
    (K : ReggeTriangulation3D.Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hFirst : ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
      (canonicalReggeHessian K hK))
    (hSecond : ReggeActionRemainderSecondVariationInput K hK) :
    ReggeActionCubicTaylorBound.NonlinearReggeCubicTaylorTheorem K hK :=
  (remainderAnalyticClosed.closure K hK).cubic_taylor_from_flat_and_jets
    hFlat hFirst hSecond

/-- Direct handoff theorem from the closed analytic-remainder certificate to the
local Hessian/Taylor input package used by the nonlinear correspondence layer.
The only inputs left are the non-remainder data: flatness, the nonlinear
Hessian theorem, and first-variation vanishing for the canonical remainder. -/
theorem nonlinearReggeLocalHessianTaylorInputs_closed
    (K : ReggeTriangulation3D.Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hHessian : NonlinearReggeDirectionalHessianTheorem K hK)
    (hFirst : ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
      (canonicalReggeHessian K hK)) :
    ReggeActionCubicTaylorBound.NonlinearReggeLocalHessianTaylorInputs K hK hFlat := by
  let hSecond : ReggeActionRemainderSecondVariationInput K hK :=
    reggeActionRemainderSecondVariationInput_of_flat_nonlinearHessian K hK hFlat
      hHessian
  exact ReggeActionCubicTaylorBound.nonlinearReggeLocalHessianTaylorInputs_of_hessian_and_taylor
    K hK hFlat hHessian
    (nonlinearReggeCubicTaylorTheorem_closed K hK hFlat hFirst hSecond)

/-- Direct local-correspondence endpoint from the closed 1B-REM certificate.
This keeps downstream users out of the line-Taylor split; they supply only the
non-remainder Hessian theorem and canonical remainder first-variation input. -/
theorem nonlinearReggeJCostLocalCorrespondence_closed
    (K : ReggeTriangulation3D.Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hHessian : NonlinearReggeDirectionalHessianTheorem K hK)
    (hFirst : ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
      (canonicalReggeHessian K hK)) :
    NonlinearReggeJCostLocalCorrespondence K hK :=
  nonlinearRegge_localCorrespondence_of_localHessianTaylorInputs K hK hFlat
    (nonlinearReggeLocalHessianTaylorInputs_closed K hK hFlat hHessian hFirst)

/-- Alias at the strongest true replacement surface: local quadratic-core
correspondence with a controlled cubic remainder. -/
theorem strongestTrueReggeJCostReplacement_closed
    (K : ReggeTriangulation3D.Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hHessian : NonlinearReggeDirectionalHessianTheorem K hK)
    (hFirst : ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
      (canonicalReggeHessian K hK)) :
    StrongestTrueReggeJCostReplacement K hK :=
  nonlinearReggeJCostLocalCorrespondence_closed K hK hFlat hHessian hFirst

end ReggeRemainderClosureAudit
end Geometry
end IndisputableMonolith
