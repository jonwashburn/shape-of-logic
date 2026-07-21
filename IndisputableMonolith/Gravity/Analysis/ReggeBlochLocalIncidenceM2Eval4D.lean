import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeBlochLocalIncidence4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbitM2Eval4D
import IndisputableMonolith.Gravity.Analysis.Regge4DContinuumPreflight
import IndisputableMonolith.Gravity.Analysis.Regge4DTorusContinuumLimit

/-!
# Path B vs distinct-hinge witness comparison

Mean-local Path B equals distinct-hinge on every ray (vacuous).
Position-resolved Path B does **not** hit EH and does **not** restore
isotropy (MEASURED receipt
`state/qg_full_theory/probe_pathB_local_incidence_20260721.json`).

Does **not** flip `gap_action_recovery`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeBlochLocalIncidenceM2Eval4D

open BigOperators
open ReggeBlochLocalIncidence4D
open ReggeBlochTransportedAllOrbit4D
open ReggeBlochTransportedAllOrbitM2Eval4D
open ReggeBlochM2Symbol4D
open Regge4DContinuumPreflight
open Regge4DTorusContinuumLimit
open EdgeTTDecomposition4D

noncomputable section

theorem m2PathB_meanLocal_axisTTPlus_symbolDir :
    m2MeanLocalAllOrbitMoment axisTTPlus symbolDir = (-1 / 4 : ℝ) := by
  rw [m2MeanLocalAllOrbitMoment_eq_distinctHinge,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTPlus_symbolDir]

theorem m2PathB_meanLocal_axisTTCross_symbolDir :
    m2MeanLocalAllOrbitMoment axisTTCross symbolDir = (-1 / 4 : ℝ) := by
  rw [m2MeanLocalAllOrbitMoment_eq_distinctHinge,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTCross_symbolDir]

theorem m2PathB_meanLocal_axisTTPlus_e0Dir :
    m2MeanLocalAllOrbitMoment axisTTPlus e0Dir = (0 : ℝ) := by
  rw [m2MeanLocalAllOrbitMoment_eq_distinctHinge,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTPlus_e0Dir]

theorem m2PathB_meanLocal_axisTTCross_e0Dir :
    m2MeanLocalAllOrbitMoment axisTTCross e0Dir = (-1 / 8 : ℝ) := by
  rw [m2MeanLocalAllOrbitMoment_eq_distinctHinge,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTCross_e0Dir]

theorem m2PathB_meanLocal_plus_cross_disagree_e0Dir :
    m2MeanLocalAllOrbitMoment axisTTPlus e0Dir ≠
      m2MeanLocalAllOrbitMoment axisTTCross e0Dir := by
  rw [m2PathB_meanLocal_axisTTPlus_e0Dir, m2PathB_meanLocal_axisTTCross_e0Dir]
  norm_num

private lemma symbolDir_normSq :
    (∑ i : Fin 4, symbolDir i * symbolDir i) = (2 : ℝ) := by
  simp [symbolDir, Fin.sum_univ_four]; norm_num

theorem continuumFace_meanLocal_normalizedPlus_symbolDir :
    m2MeanLocalAllOrbitMoment ((Real.sqrt 2)⁻¹ • axisTTPlus) symbolDir /
      (∑ i : Fin 4, symbolDir i * symbolDir i) =
      (-1 / 16 : ℝ) := by
  rw [m2MeanLocalAllOrbitMoment_smul,
    m2PathB_meanLocal_axisTTPlus_symbolDir, symbolDir_normSq,
    inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem meanLocal_pinned_face_ne_eh :
    m2MeanLocalAllOrbitMoment ((Real.sqrt 2)⁻¹ • axisTTPlus) symbolDir /
      (∑ i : Fin 4, symbolDir i * symbolDir i) ≠
      einsteinHilbertTTCoefficient4D := by
  rw [continuumFace_meanLocal_normalizedPlus_symbolDir,
    einsteinHilbertTTCoefficient4D_eq]
  norm_num

theorem pathB_vs_distinctHinge_witness_table :
    m2MeanLocalAllOrbitMoment axisTTPlus symbolDir =
        m2TransportedAllOrbitMomentDistinctHinge axisTTPlus symbolDir ∧
      m2MeanLocalAllOrbitMoment axisTTCross symbolDir =
        m2TransportedAllOrbitMomentDistinctHinge axisTTCross symbolDir ∧
      m2MeanLocalAllOrbitMoment axisTTPlus e0Dir =
        m2TransportedAllOrbitMomentDistinctHinge axisTTPlus e0Dir ∧
      m2MeanLocalAllOrbitMoment axisTTCross e0Dir =
        m2TransportedAllOrbitMomentDistinctHinge axisTTCross e0Dir ∧
      m2MeanLocalAllOrbitMoment axisTTPlus symbolDir = (-1 / 4 : ℝ) ∧
      m2MeanLocalAllOrbitMoment axisTTCross symbolDir = (-1 / 4 : ℝ) ∧
      m2MeanLocalAllOrbitMoment axisTTPlus e0Dir = (0 : ℝ) ∧
      m2MeanLocalAllOrbitMoment axisTTCross e0Dir = (-1 / 8 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact m2MeanLocalAllOrbitMoment_eq_distinctHinge _ _
  · exact m2MeanLocalAllOrbitMoment_eq_distinctHinge _ _
  · exact m2MeanLocalAllOrbitMoment_eq_distinctHinge _ _
  · exact m2MeanLocalAllOrbitMoment_eq_distinctHinge _ _
  · exact m2PathB_meanLocal_axisTTPlus_symbolDir
  · exact m2PathB_meanLocal_axisTTCross_symbolDir
  · exact m2PathB_meanLocal_axisTTPlus_e0Dir
  · exact m2PathB_meanLocal_axisTTCross_e0Dir

/-- Position-resolved Path B does not close EH (status false / OPEN). -/
theorem pathB_positionResolved_does_not_close_eh :
    Regge4DPathBPositionResolvedClosesEH = False :=
  Regge4DPathBPositionResolvedClosesEH_status_open

theorem pathB_does_not_inhabit_eh :
    regge4DTorusContinuumLimitStatus.ehTendstoInhabited = false :=
  rfl

structure ReggeBlochLocalIncidenceM2Eval4DStatus where
  meanLocalEqualsDistinctHingeOnWitnesses : Bool
  e0AnisotropyPersistsUnderMeanLocal : Bool
  factor4ResidualPersistsUnderMeanLocal : Bool
  positionResolvedClosesEH : Bool
  gapActionRecovery : Bool

def reggeBlochLocalIncidenceM2Eval4DStatus :
    ReggeBlochLocalIncidenceM2Eval4DStatus where
  meanLocalEqualsDistinctHingeOnWitnesses := true
  e0AnisotropyPersistsUnderMeanLocal := true
  factor4ResidualPersistsUnderMeanLocal := true
  positionResolvedClosesEH := false
  gapActionRecovery := false

theorem reggeBlochLocalIncidenceM2Eval4DStatus_flags :
    reggeBlochLocalIncidenceM2Eval4DStatus.meanLocalEqualsDistinctHingeOnWitnesses =
        true ∧
      reggeBlochLocalIncidenceM2Eval4DStatus.e0AnisotropyPersistsUnderMeanLocal =
        true ∧
        reggeBlochLocalIncidenceM2Eval4DStatus.factor4ResidualPersistsUnderMeanLocal =
          true ∧
          reggeBlochLocalIncidenceM2Eval4DStatus.positionResolvedClosesEH =
            false ∧
            reggeBlochLocalIncidenceM2Eval4DStatus.gapActionRecovery =
              false := by
  decide

theorem does_not_flip_gap_action_recovery :
    reggeBlochLocalIncidenceM2Eval4DStatus.gapActionRecovery = false :=
  rfl

end

end ReggeBlochLocalIncidenceM2Eval4D
end Analysis
end Gravity
end IndisputableMonolith
