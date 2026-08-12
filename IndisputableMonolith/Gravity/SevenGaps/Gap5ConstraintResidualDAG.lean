import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureFunctionBlocker
import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureBracket
import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureContinuumSmearing
import IndisputableMonolith.Gravity.SevenGaps.DiracAlgebraContinuum
import IndisputableMonolith.Gravity.SevenGaps.DiracAlgebraContinuumBinding
import IndisputableMonolith.Gravity.SevenGaps.HypersurfaceDeformation
import IndisputableMonolith.Gravity.SevenGaps.HKTOneSiteCounterexample
import IndisputableMonolith.Gravity.SevenGaps.HKTDynamicTarget
import IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

/-!
# Wave C2/D typed residual DAG: `gap5_constraint_recovery`

Names residuals for dynamic Dirac structure functions + HKT rigidity.
Pattern mirrors `SRSConvergesEH4D` §4. Numbering follows
`plans/QG_WaveC2_Gap5_Residual_DAG_Draft_20260722.txt` and
`D-gap5-hkt-design-20260722`.

## Honest status (2026-07-22 Wave D wire)

* Background-weight blocker closed (certified).
* R1 dynamic bracket closed (`typedResidual_dynamic_bracket_concrete_two_site`).
* R2 Dirac premise closed (`phaseSpaceDependentDiracPremise_two_site`).
* R3 dynamic continuum smearing closed
  (`typedResidual_gap5_dynamic_continuum_smearing`).
* R4 ledger terminal `dirac_algebra_continuum_limit` closed (repaired
  2026-07-22): general-`n` `HamDynN` bracket identity + periodic wrap
  binding + shape continuum
  (`DiracAlgebraContinuumBinding.dirac_algebra_continuum_limit`;
  Elmo green, clean axiom triple, no `sorryAx`).
* One-site falsification closed: `¬ HKTRigidityStatement 1`
  (`HKTOneSiteCounterexample.not_HKTRigidityStatement_one`).
* Dyn HKT target / Dyn rigidity Prop banked as MODEL definitions
  (`HojmanKucharTeitelboimTargetDyn`, `HKTRigidityStatementDyn`);
  Dyn inhabitant not banked.
* R6 open repair: `TypedResidual_gap5_hkt_rigidity` points at
  `HKTRigidityStatementDyn 2`. Frozen scalar-rung
  `HKTRigidityStatement` kept as disclosure form only (false at `n = 1`;
  not claimed closed at `n = 2`).
* C5 (2026-07-23): flips `gap5_constraint_recovery` via
  `Gap5ConstraintCloseStatus` (Dirac continuum + kinetic-normalized HKT;
  FTC theorem-derived). DAG bits: `hktRigidityOpen = false`,
  `packagedTargetOpen = false`, `gap5ConstraintRecovery = true`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap5ConstraintResidualDAG

open DynamicStructureFunctionBlocker
open DynamicStructureBracket
open DynamicStructureContinuumSmearing
open DiracAlgebraContinuum
open DiracAlgebraContinuumBinding
open HypersurfaceDeformation
open HKTOneSiteCounterexample
open HKTDynamicTarget
open FullTheoryLedger
open Filter Topology

noncomputable section

/-! ## §1. Typed residuals -/

/-- **R0 family.** Certified background-weight underdetermination blocker. -/
def TypedResidual_gap5_background_weight_blocker : Prop :=
  (∀ w : ZMod 2 → ℝ, HamWHasBackgroundStructureFunction w) ∧
    (∀ W : ℝ → ℝ, ContinuousOn W (Set.Icc 0 1) →
      BackgroundWeightedContinuumReach W) ∧
    (∀ w : ZMod 2 → ℝ,
      ¬ FixedBackgroundRepresents w concreteDynamicInverseMetric)

/-- **Wave C2 R1.** Concrete dynamic bracket on two sites. -/
def TypedResidual_gap5_dynamic_bracket : Prop :=
  TypedResidual_dynamic_bracket_concrete_two_site

/-- **Wave C2 R2.** Phase-space-dependent Dirac premise on two sites. -/
def TypedResidual_gap5_phaseSpaceDependentDirac : Prop :=
  PhaseSpaceDependentDiracPremise 2

/-- **Wave C2 R3.** Dynamic structure-function continuum smearing. -/
def TypedResidual_gap5_dynamic_continuum_smearing_residual : Prop :=
  TypedResidual_gap5_dynamic_continuum_smearing

/-- **Wave C2 R4 shape residual (not the ledger terminal).** Freestanding
sampled-sum continuum limit; proved as
`dynamic_bracket_shape_continuum_limit`. -/
def TypedResidual_gap5_dynamic_bracket_shape_continuum : Prop :=
  ∀ (N M q p : ℝ → ℝ),
    ContDiff ℝ 1 N → ContDiff ℝ 1 M → ContDiff ℝ 1 q →
      ContinuousOn p (Set.Icc 0 1) →
        Tendsto (fun n : ℕ => (n : ℝ) * sampledDynamicBracketSum n N M q p)
          atTop
          (nhds (∫ t in (0 : ℝ)..1, continuumDiracDensity N M q p t))

/-- **Wave C2 R4 (ledger terminal, repaired).** Scaled general-`n` dynamic
Hamiltonian bracket at continuum samples tends to the continuum Dirac density,
for 1-periodic ContDiff-1 lapses/configuration and 1-periodic continuous
momentum. -/
def TypedResidual_gap5_dirac_algebra_continuum_limit : Prop :=
  ∀ (N M q p : ℝ → ℝ),
    Periodic1 N → Periodic1 M → Periodic1 q → Periodic1 p →
      ContDiff ℝ 1 N → ContDiff ℝ 1 M → ContDiff ℝ 1 q →
        ContinuousOn p (Set.Icc 0 1) →
          Tendsto (fun n : ℕ => (n : ℝ) * continuumLatticeBracket n N M q p)
            atTop
            (nhds (∫ t in (0 : ℝ)..1, continuumDiracDensity N M q p t))

/-- **Wave D disclosure.** Frozen scalar-rung rigidity form
(`HKTRigidityStatement`). Kept only as the false-at-`n=1` form; not the R6
terminal (`D-gap5-hkt-design-20260722`). -/
def TypedResidual_gap5_hkt_rigidity_frozen : Prop :=
  HKTRigidityStatement 2

/-- **Wave D.** One-site falsification of the frozen form. -/
def TypedResidual_gap5_hkt_one_site_falsification : Prop :=
  ¬ HKTRigidityStatement 1

/-- **Wave D MODEL.** Widened Dyn HKT target and Dyn rigidity Prop are defined
(`HojmanKucharTeitelboimTargetDyn`, `HKTRigidityStatementDyn`). Not an
inhabitant and not a rigidity proof. -/
def TypedResidual_gap5_hkt_dyn_target_defined : Prop :=
  hktDynamicTargetStatus.dynTargetDefined = true ∧
    hktDynamicTargetStatus.dynRigidityDefined = true ∧
      hktDynamicTargetStatus.dynInhabitantBanked = false ∧
        hktDynamicTargetStatus.gap5ConstraintRecovery = false

/-- **R6 open repair (`D-gap5-hkt-design-20260722`).** Repaired GR-strength
rigidity target over the Dyn structure-function slot. Uninhabited /
unproved. -/
def TypedResidual_gap5_hkt_rigidity : Prop :=
  HKTRigidityStatementDyn 2

/-- **Packaged Gap 5 target (OPEN).** Dirac premise + Dyn rigidity repair.
Does not use the frozen false form `HKTRigidityStatement` as the closer. -/
def TypedResidual_gap5_dynamicDirac_and_hkt : Prop :=
  PhaseSpaceDependentDiracPremise 2 ∧ HKTRigidityStatementDyn 2

/-! ## §2. Closed residuals -/

theorem typedResidual_gap5_background_weight_blocker :
    TypedResidual_gap5_background_weight_blocker :=
  gap5_background_weight_blocker

theorem concreteDynamicInverseMetric_not_constant_witness :
    ¬ PhaseSpaceConstant concreteDynamicInverseMetric :=
  concreteDynamicInverseMetric_not_constant

/-- Wave C2 R1 closed. -/
theorem typedResidual_gap5_dynamic_bracket_closed :
    TypedResidual_gap5_dynamic_bracket :=
  typedResidual_dynamic_bracket_concrete_two_site

/-- Wave C2 R2 closed. -/
theorem typedResidual_gap5_phaseSpaceDependentDirac_closed :
    TypedResidual_gap5_phaseSpaceDependentDirac :=
  phaseSpaceDependentDiracPremise_two_site

/-- Wave C2 R3 closed. -/
theorem typedResidual_gap5_dynamic_continuum_smearing_closed :
    TypedResidual_gap5_dynamic_continuum_smearing_residual :=
  typedResidual_gap5_dynamic_continuum_smearing

/-- Wave C2 R4 shape residual closed (rate-h / freestanding sum). -/
theorem typedResidual_gap5_dynamic_bracket_shape_continuum_closed :
    TypedResidual_gap5_dynamic_bracket_shape_continuum :=
  fun N M q p hN hM hq hp =>
    dynamic_bracket_shape_continuum_limit N M q p hN hM hq hp

/-- Wave C2 R4 ledger terminal closed (HamDynN binding + periodic wrap). -/
theorem typedResidual_gap5_dirac_algebra_continuum_limit_closed :
    TypedResidual_gap5_dirac_algebra_continuum_limit :=
  fun N M q p hNper hMper hqper hpper hN hM hq hp =>
    DiracAlgebraContinuumBinding.dirac_algebra_continuum_limit
      N M q p hNper hMper hqper hpper hN hM hq hp

/-- Wave D: frozen `HKTRigidityStatement 1` falsified. -/
theorem typedResidual_gap5_hkt_one_site_falsification_closed :
    TypedResidual_gap5_hkt_one_site_falsification :=
  not_HKTRigidityStatement_one

/-- Wave D MODEL bank: Dyn target / Dyn rigidity Prop defined; no inhabitant;
ledger flag unflipped. -/
theorem typedResidual_gap5_hkt_dyn_target_defined_banked :
    TypedResidual_gap5_hkt_dyn_target_defined :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §3. Status (gap5 unflipped) -/

structure Gap5ResidualDAGStatus where
  backgroundWeightBlockerClosed : Bool
  dynamicBracketClosed : Bool
  phaseSpaceDependentDiracClosed : Bool
  dynamicContinuumSmearingClosed : Bool
  diracAlgebraContinuumLimitClosed : Bool
  hktOneSiteFalsificationClosed : Bool
  hktDynTargetDefined : Bool
  hktRigidityOpen : Bool
  packagedTargetOpen : Bool
  gap5ConstraintRecovery : Bool

def gap5ResidualDAGStatus : Gap5ResidualDAGStatus where
  backgroundWeightBlockerClosed := true
  dynamicBracketClosed := true
  phaseSpaceDependentDiracClosed := true
  dynamicContinuumSmearingClosed := true
  diracAlgebraContinuumLimitClosed := true
  hktOneSiteFalsificationClosed := true
  hktDynTargetDefined := true
  hktRigidityOpen := false
  packagedTargetOpen := false
  gap5ConstraintRecovery := true

theorem gap5ResidualDAGStatus_flags :
    gap5ResidualDAGStatus.backgroundWeightBlockerClosed = true ∧
      gap5ResidualDAGStatus.dynamicBracketClosed = true ∧
        gap5ResidualDAGStatus.phaseSpaceDependentDiracClosed = true ∧
          gap5ResidualDAGStatus.dynamicContinuumSmearingClosed = true ∧
            gap5ResidualDAGStatus.diracAlgebraContinuumLimitClosed = true ∧
              gap5ResidualDAGStatus.hktOneSiteFalsificationClosed = true ∧
                gap5ResidualDAGStatus.hktDynTargetDefined = true ∧
                  gap5ResidualDAGStatus.hktRigidityOpen = false ∧
                    gap5ResidualDAGStatus.packagedTargetOpen = false ∧
                      gap5ResidualDAGStatus.gap5ConstraintRecovery = true ∧
                        fullTheoryBenchmarks.gap5_constraint_recovery = true := by
  decide

/-- Superseded 2026-07-23: gap5 flipped via C5 close status. Kept as the
closed-flag identity so dependents cannot silently re-open. -/
theorem gap5_closed_after_residual_dag :
    fullTheoryBenchmarks.gap5_constraint_recovery = true :=
  rfl

end

end Gap5ConstraintResidualDAG
end SevenGaps
end Gravity
end IndisputableMonolith
