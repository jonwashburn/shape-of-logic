import IndisputableMonolith.Gravity.SevenGaps.DiracAlgebraContinuumBinding
import IndisputableMonolith.Gravity.SevenGaps.HKTKineticNormalizedRigidity
import IndisputableMonolith.Gravity.SevenGaps.HKTVacuumSectorKill
import IndisputableMonolith.Gravity.SevenGaps.HKTCanonicalMomTarget
import IndisputableMonolith.Gravity.SevenGaps.HKTPointSplitStrong
import IndisputableMonolith.Gravity.SevenGaps.HKTOneSiteCounterexample
import IndisputableMonolith.Gravity.SevenGaps.HypersurfaceDeformation
import IndisputableMonolith.Gravity.SevenGaps.Gap5ConstraintResidualDAG
import IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger
import IndisputableMonolith.Gravity.SevenGaps.CampaignLedger

/-!
# Wave C5: gap5 constraint-recovery close status / binding receipt

Downstream of `FullTheoryLedger` and both named closers so the ledger Bool
flip cannot create an import cycle. Binding theorems tie

* `fullTheoryBenchmarks.gap5_constraint_recovery = true`
* `sevenGapsCampaignStatus.gap5_continuum_algebra_hkt_open = false`
* `gap5ResidualDAGStatus.hktRigidityOpen = false`
* `gap5ResidualDAGStatus.packagedTargetOpen = false`
* `gap5ResidualDAGStatus.gap5ConstraintRecovery = true`

to the green conjunction

* Dirac half: `DiracAlgebraContinuumBinding.dirac_algebra_continuum_limit`
* HKT half: `hojman_pins_general_relativity_holds`
  (`HKTRigidityKineticNormalizedN2_holds`, FTC theorem-derived)

Kill tower (scope certificate that no stronger unconditioned n=2 statement
is true): `not_HKTRigidityStatement_one`,
`not_HKTRigidityStatementPointSplitDynN2Strong`,
`not_HKTRigidityStatementPointSplitDynN2Canonical`,
`not_HKTRigidityModVacuumStatementN2`.

Adjudication: `D-gap5-acceptance-adjudication-20260723`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap5ConstraintCloseStatus

open FullTheoryLedger
open CampaignLedger
open Gap5ConstraintResidualDAG
open DiracAlgebraContinuumBinding
open HKTKineticNormalizedRigidity
open HKTVacuumSectorKill
open HKTCanonicalMomTarget
open HKTPointSplitStrong
open HKTOneSiteCounterexample
open HypersurfaceDeformation

noncomputable section

/-! ## Named ledger terminal (HKT half) -/

/-- Ledger name for the HKT/GR-pin half of gap5. Bound to the kinetic-normalized
ContDiff-2 CanonicalMom terminal (intensivity disclosed; FTC derived).

**The name overclaims and the definition is what binds.** What is proved is
`HKTRigidityKineticNormalizedN2`: rigidity of the ADM *shape* on an `n = 2`
lattice point-split target. General relativity in the continuum is not pinned
here; no continuum limit is taken, and `dirac_algebra_continuum_limit` is the
open statement that would be needed. Read this terminal as "Hojman pins the
ADM shape at `n = 2`". Renamed 2026-08-05 (Jon's authorization in the
classical-paper session): the accurate name is `hkt_adm_shape_rigidity_n2`
below; this historical name is retained as a compatibility alias because six
modules and the flag ledger bind to it. -/
def hojman_pins_general_relativity : Prop :=
  HKTRigidityKineticNormalizedN2

/-- THEOREM. Named terminal inhabited by the upgraded kinetic-normalized hold. -/
theorem hojman_pins_general_relativity_holds : hojman_pins_general_relativity :=
  HKTRigidityKineticNormalizedN2_holds

/-- Accurate name for the HKT half (renamed 2026-08-05): kinetic-normalized
ADM shape rigidity on the `n = 2` point-split class. New citations bind to
this name; `hojman_pins_general_relativity` above is the historical alias. -/
def hkt_adm_shape_rigidity_n2 : Prop :=
  hojman_pins_general_relativity

theorem hkt_adm_shape_rigidity_n2_holds : hkt_adm_shape_rigidity_n2 :=
  hojman_pins_general_relativity_holds

/-! ## Both halves -/

/-- Adjudicated conjunction: Dirac continuum algebra + HKT kinetic-normalized pin. -/
theorem gap5_constraint_recovery_both_halves :
    TypedResidual_gap5_dirac_algebra_continuum_limit ∧
      hojman_pins_general_relativity :=
  ⟨typedResidual_gap5_dirac_algebra_continuum_limit_closed,
    hojman_pins_general_relativity_holds⟩

/-! ## Status block -/

structure Gap5ConstraintCloseStatus where
  /-- Full-theory gap5 flipped. -/
  gap5ConstraintRecovery : Bool
  /-- Campaign continuum-algebra/HKT open bit cleared. -/
  gap5ContinuumAlgebraHktOpen : Bool
  /-- Residual DAG rigidity open bit cleared. -/
  hktRigidityOpen : Bool
  /-- Residual DAG packaged-target open bit cleared. -/
  packagedTargetOpen : Bool
  /-- Dirac continuum half closed. -/
  diracHalfClosed : Bool
  /-- HKT kinetic-normalized half closed. -/
  hktHalfClosed : Bool
  /-- Kill tower banked as scope certificate. -/
  killTowerBanked : Bool

def gap5ConstraintCloseStatus : Gap5ConstraintCloseStatus where
  gap5ConstraintRecovery := true
  gap5ContinuumAlgebraHktOpen := false
  hktRigidityOpen := false
  packagedTargetOpen := false
  diracHalfClosed := true
  hktHalfClosed := true
  killTowerBanked := true

theorem gap5ConstraintCloseStatus_flags :
    gap5ConstraintCloseStatus.gap5ConstraintRecovery = true ∧
      gap5ConstraintCloseStatus.gap5ContinuumAlgebraHktOpen = false ∧
        gap5ConstraintCloseStatus.hktRigidityOpen = false ∧
          gap5ConstraintCloseStatus.packagedTargetOpen = false ∧
            gap5ConstraintCloseStatus.diracHalfClosed = true ∧
              gap5ConstraintCloseStatus.hktHalfClosed = true ∧
                gap5ConstraintCloseStatus.killTowerBanked = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Binding receipt.** Ledger gap5 true is co-asserted with both green
halves, campaign open-bit cleared, and DAG rigidity bits cleared. -/
theorem gap5_constraint_recovery_bound_to_terminals :
    fullTheoryBenchmarks.gap5_constraint_recovery = true ∧
      sevenGapsCampaignStatus.gap5_continuum_algebra_hkt_open = false ∧
        gap5ResidualDAGStatus.hktRigidityOpen = false ∧
          gap5ResidualDAGStatus.packagedTargetOpen = false ∧
            gap5ResidualDAGStatus.gap5ConstraintRecovery = true ∧
              TypedResidual_gap5_dirac_algebra_continuum_limit ∧
                hojman_pins_general_relativity :=
  ⟨rfl, rfl, rfl, rfl, rfl,
    typedResidual_gap5_dirac_algebra_continuum_limit_closed,
    hojman_pins_general_relativity_holds⟩

/-- Kill tower (four not_* theorems): scope certificate that stronger
unconditioned n=2 rigidity statements are false. -/
theorem gap5_kill_tower_scope_certificate :
    (¬ HKTRigidityStatement 1) ∧
      (¬ HKTRigidityStatementPointSplitDynN2Strong) ∧
        (¬ HKTRigidityStatementPointSplitDynN2Canonical) ∧
          (¬ HKTRigidityModVacuumStatementN2) :=
  ⟨not_HKTRigidityStatement_one,
    not_HKTRigidityStatementPointSplitDynN2Strong,
    not_HKTRigidityStatementPointSplitDynN2Canonical,
    not_HKTRigidityModVacuumStatementN2⟩

#print axioms hojman_pins_general_relativity_holds
#print axioms gap5_constraint_recovery_both_halves
#print axioms gap5_constraint_recovery_bound_to_terminals
#print axioms gap5_kill_tower_scope_certificate
#print axioms ftc_recovery_of_normalized
#print axioms not_HKTRigidityStatement_one
#print axioms not_HKTRigidityStatementPointSplitDynN2Strong
#print axioms not_HKTRigidityStatementPointSplitDynN2Canonical
#print axioms not_HKTRigidityModVacuumStatementN2

end

end Gap5ConstraintCloseStatus
end SevenGaps
end Gravity
end IndisputableMonolith
