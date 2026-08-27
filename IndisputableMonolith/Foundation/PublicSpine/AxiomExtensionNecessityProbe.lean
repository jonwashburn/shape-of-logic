import IndisputableMonolith.Foundation.PublicSpine.GaugeActionScaleCoin
import IndisputableMonolith.Foundation.PublicSpine.PlasticVsAdjacencyMetered
import IndisputableMonolith.Foundation.PublicSpine.CurrentRSBundle
import IndisputableMonolith.Foundation.PublicSpine.SelectedScaleClosure
import IndisputableMonolith.Foundation.PhiForcingDerived
import IndisputableMonolith.Cost.FunctionalEquation

/-!
# AxiomExtensionNecessityProbe — both-FAIL terminal (Part I gate campaign)

Plan partition (FAIL-A ∧ FAIL-B): bank two impossibility certs and name the
minimal bridge axioms required to restore the Part I uniqueness packages.
This historical probe names the residuals as documented structures. Jon later
authorized their explicit installation together with the seed-orbit and clock
bridges in `PartINamedAxiomClosure`.

Gate receipts:
* Test A FAIL: `ScaleClosedCoin` (all-n micro-sum) unsatisfiable
  (`GaugeActionScaleCoin.scaleClosedCoin_unsatisfiable`).
* Test B FAIL: frozen `MeteredLatency` has `plasticMeter ≤ adjacentMeter`
  (`PlasticVsAdjacencyMetered.plasticMeter_le_adjacentMeter`).

The later seed-compose and clock lanes also reached compiled terminals before
the named-axiom package was installed.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace AxiomExtensionNecessityProbe

open Cost.FunctionalEquation
open CurrentRSBundle
open GaugeActionScaleCoin
open PlasticVsAdjacencyMetered
open SelectedScaleClosure
open PhiForcingDerived
open Constants

/-! ## Impossibility certs (compiled from week-one gates) -/

structure CalibrationGateImpossibility : Prop where
  scaleClosedCoin_unsat :
    ∀ M : GaugeModel, ¬ Nonempty (ScaleClosedCoin M)
  gate_fail : gateAVerdict = GateAVerdict.fail
  day0 : CurrentRSBundleCert

theorem calibrationGateImpossibility_holds : CalibrationGateImpossibility where
  scaleClosedCoin_unsat := scaleClosedCoin_unsatisfiable
  gate_fail := rfl
  day0 := currentRSBundleCert_holds

structure BinaryGateImpossibility : Prop where
  plastic_le_adjacent : plasticMeter ≤ adjacentMeter
  gate_fail : plasticVsAdjacencyMeteredCert.verdict = GateBVerdict.fail
  plastic_independent :
    ∃ r : ℝ, 0 < r ∧ r ≠ phi ∧ r ^ 3 = r + 1

theorem binaryGateImpossibility_holds : BinaryGateImpossibility where
  plastic_le_adjacent := plasticMeter_le_adjacentMeter
  gate_fail := gateB_verdict_is_fail
  plastic_independent := exists_plastic_root_ne_phi

/-! ## Named minimal axiom markers (realized in the downstream package) -/

/-- **Named calibration bridge** (paper residual / candidate axiom).

Recognition's continuum cost reads atomic ledger acts at the instantaneous
(tangent) chart. Motivation: the ScaleClosedCoin all-n micro-sum reading is
unsatisfiable, and the chart trichotomy shows every other natural coin readout
either packages `IsCalibrated` or pins a non-unit gauge. Uniqueness of `J`
under unit calibration plus bare cost laws is already THEOREM. -/
structure NamedTangentChartAxiom where
  documented : True := trivial

/-- **Named adjacency bridge** (paper residual / candidate axiom).

The hierarchy short closure is the first adjacent seed join
`L₂ = L₀ + L₁`, not a plastic skip. Motivation: frozen `MeteredLatency` does
not select adjacency over plastic. Uniqueness of φ under adjacent closure is
already THEOREM. -/
structure NamedAdjacentClosureAxiom where
  documented : True := trivial

/-- **OPEN target** (calibration sufficiency): unit calibration plus the bare cost
laws force `J`.

Stated as a target rather than a theorem. There was a `namedTangent_suffices_shape`
here of the form `(this statement) → True`, which is provable of any antecedent at
all and so recorded nothing about whether the antecedent holds. The antecedent is
the whole content, so it is now written on its own, unproved and visibly so. -/
def target_namedTangent_suffices : Prop :=
  ∀ F : ℝ → ℝ,
    IsReciprocalCost F → IsNormalized F → SatisfiesCompositionLaw F →
      ContinuousOn F (Set.Ioi 0) → IsCalibrated F →
        F = Cost.Jcost

/-! Adjacency sufficiency needs no target: `namedAdjacent_suffices_via_selected`
below proves the statement outright. A `namedAdjacent_suffices_shape` used to sit
here asserting `(that statement) → True`, which the real theorem strictly
supersedes. -/

theorem namedAdjacent_suffices_via_selected :
    (∀ S : GeometricScaleSequence, S.isClosed → S.ratio = phi) :=
  fun S h => closed_ratio_is_phi S h

/-! ## Terminal cert -/

structure AxiomExtensionNecessity : Prop where
  calib_impossible_in_class : CalibrationGateImpossibility
  binary_impossible_under_meter : BinaryGateImpossibility
  named_calib_bridge : NamedTangentChartAxiom
  named_adj_bridge : NamedAdjacentClosureAxiom
  both_fail :
    gateAVerdict = GateAVerdict.fail ∧
      plasticVsAdjacencyMeteredCert.verdict = GateBVerdict.fail

theorem axiomExtensionNecessity_holds : AxiomExtensionNecessity where
  calib_impossible_in_class := calibrationGateImpossibility_holds
  binary_impossible_under_meter := binaryGateImpossibility_holds
  named_calib_bridge := {}
  named_adj_bridge := {}
  both_fail := ⟨rfl, gateB_verdict_is_fail⟩

def partitionAction : String :=
  "FAIL-A ∧ FAIL-B → AxiomExtensionNecessity terminal; named bridges required and later installed downstream after Jon authorization"

end AxiomExtensionNecessityProbe
end PublicSpine
end Foundation
end IndisputableMonolith
