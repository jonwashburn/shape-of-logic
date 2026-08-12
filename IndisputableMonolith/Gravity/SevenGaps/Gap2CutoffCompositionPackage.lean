import IndisputableMonolith.Gravity.SevenGaps.CapShellBridge
import IndisputableMonolith.Gravity.SevenGaps.ZqShellBalanceBlocker

/-!
# Wave C1 R1: gap2 cutoff composition package

Banks the hours-tier conditional positive named in
`plans/QG_WaveC1_Gap2_Residual_DAG_Draft_20260722.txt` residual R1:

```
TypedResidual_gap2_cutoff_composition_package :
  ∀ phase, OscillatoryTail phase →
    HasPhasedZqComplexityLimit (capPhaseFamily phase)
```

This is a universally quantified conditional (NOT a `True`-shell): it packages
the already-banked canonical transport
`CapShellBridge.capShellCompatibility` with the already-banked IFF
`ZqContinuumBlocker.hasPhasedZqLimit_iff_exactShellTail_of_compatibility`
(and the banked Cauchy / ordered-tail chain that identifies `OscillatoryTail`
with `ExactShellTailCancellation`). Later substrate-phase work (R2–R4) plugs
an `OscillatoryTail` witness into this interface to obtain the capped
complexity-cutoff limit on `capPhaseFamily phase`.

## Divergence from the DAG draft (none on signatures)

Ground-truthed names match the DAG assumptions:

* `ZqContinuumBlocker.hasPhasedZqLimit_iff_exactShellTail_of_compatibility`
  : `CapShellCompatibility P phase →
     HasPhasedZqComplexityLimit P ↔ ExactShellTailCancellation phase`
* `CapShellBridge.capShellCompatibility`
  : `∀ phase, CapShellCompatibility (capPhaseFamily phase) phase`
* `CapShellBridge.capPhaseFamily` / `gap2_capshell_bridge_discharged` (ledger)

Minor indexing note (documented, not a signature mismatch): `OscillatoryTail`
quantifies contiguous blocks as `Ico m n` (Zcap / `range B` form), while
`ExactShellTailCancellation` quantifies `Ico (m+1) (n+1)` (ordered-cutoff
form). They are identified here via the banked equalities
`exactComplexityCutoff phase B = Zcap phase (B+1)`,
`cauchySeq_Zcap_iff_oscillatoryTail`, completeness of `ℂ`, and
`hasExactComplexityCutoffLimit_iff_tailCancellation`.

## Honesty

Does NOT flip `gap2_continuum_and_measure`. Does NOT supply a substrate
phase. Decy anchors re-export the dead classes any future phase must escape
(`ShellConstant`, `EventuallyZeroPhase`, and the zero-phase discriminant).

No `sorry`, `admit`, new axiom, or `native_decide`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps

open ExactShellGaugeUV
open ZqContinuumBlocker
open CapShellBridge
open ZqShellBalanceBlocker

noncomputable section

/-! ## §1. Banked indexing bridge (Zcap ↔ exactComplexityCutoff) -/

/-- Definitional: the ordered exact-shell cutoff through shell `B` is the
panel-locked `Zcap` evaluated at `B + 1`. -/
theorem exactComplexityCutoff_eq_Zcap_succ
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) (B : ℕ) :
    exactComplexityCutoff phase B = Zcap phase (B + 1) :=
  rfl

/-- `OscillatoryTail` is equivalent to ordered `ExactShellTailCancellation`,
via the banked Zcap Cauchy criterion, completeness of `ℂ`, and the banked
ordered-tail IFF (plus the definitional cutoff shift above). -/
theorem oscillatoryTail_iff_exactShellTailCancellation
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) :
    OscillatoryTail phase ↔ ExactShellTailCancellation phase := by
  constructor
  · intro htail
    have hCauchy : CauchySeq (Zcap phase) :=
      (cauchySeq_Zcap_iff_oscillatoryTail phase).mpr htail
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hCutoff :
        Filter.Tendsto (exactComplexityCutoff phase) Filter.atTop (nhds L) := by
      have hEq : exactComplexityCutoff phase = fun B => Zcap phase (B + 1) :=
        funext fun B => exactComplexityCutoff_eq_Zcap_succ phase B
      rw [hEq]
      -- `tendsto_add_atTop_iff_nat`: Tendsto (fun n => f (n+k)) ↔ Tendsto f
      exact (Filter.tendsto_add_atTop_iff_nat (f := Zcap phase) 1).mpr hL
    exact (hasExactComplexityCutoffLimit_iff_tailCancellation phase).mp ⟨L, hCutoff⟩
  · intro htail
    have hLimit : HasExactComplexityCutoffLimit phase :=
      (hasExactComplexityCutoffLimit_iff_tailCancellation phase).mpr htail
    obtain ⟨L, hCutoff⟩ := hLimit
    have hZ :
        Filter.Tendsto (Zcap phase) Filter.atTop (nhds L) := by
      have hEq : exactComplexityCutoff phase = fun B => Zcap phase (B + 1) :=
        funext fun B => exactComplexityCutoff_eq_Zcap_succ phase B
      have hSucc :
          Filter.Tendsto (fun B => Zcap phase (B + 1)) Filter.atTop (nhds L) := by
        simpa [hEq] using hCutoff
      exact (Filter.tendsto_add_atTop_iff_nat (f := Zcap phase) 1).mp hSucc
    have hCauchy : CauchySeq (Zcap phase) := hZ.cauchySeq
    exact (cauchySeq_Zcap_iff_oscillatoryTail phase).mp hCauchy

/-! ## §2. R1 composition (DAG residual) -/

/-- **DAG R1 residual Prop.** Any phase functional with oscillatory late-shell
cancellation yields the capped complexity-cutoff limit on the canonical
transported family `capPhaseFamily phase`. -/
def TypedResidual_gap2_cutoff_composition_package : Prop :=
  ∀ phase : ∀ n : ℕ, ExactPathClass n → ℝ,
    OscillatoryTail phase →
      HasPhasedZqComplexityLimit (capPhaseFamily phase)

/-- **HEADLINE.** Composition of banked `capShellCompatibility` with banked
`hasPhasedZqLimit_iff_exactShellTail_of_compatibility`, after identifying
`OscillatoryTail` with `ExactShellTailCancellation`. -/
theorem oscillatoryTail_implies_hasPhasedZqComplexityLimit_capPhaseFamily
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ)
    (htail : OscillatoryTail phase) :
    HasPhasedZqComplexityLimit (capPhaseFamily phase) := by
  have hExact : ExactShellTailCancellation phase :=
    (oscillatoryTail_iff_exactShellTailCancellation phase).mp htail
  exact (hasPhasedZqLimit_iff_exactShellTail_of_compatibility
      (capPhaseFamily phase) phase (capShellCompatibility phase)).mpr hExact

theorem typedResidual_gap2_cutoff_composition_package_closed :
    TypedResidual_gap2_cutoff_composition_package :=
  oscillatoryTail_implies_hasPhasedZqComplexityLimit_capPhaseFamily

theorem TypedResidual_gap2_cutoff_composition_package_closed :
    TypedResidual_gap2_cutoff_composition_package :=
  typedResidual_gap2_cutoff_composition_package_closed

/-! ## §3. Decoy anchors (dead classes any future phase must escape) -/

/-- Re-export: shell-constant (complexity-only) phases refute `OscillatoryTail`. -/
theorem decoy_shellConstant_not_oscillatoryTail
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ)
    (hconst : ShellConstant phase) :
    ¬ OscillatoryTail phase :=
  shellConstant_not_oscillatoryTail phase hconst

/-- Re-export: eventually-zero (finite-cap repair) phases refute `OscillatoryTail`. -/
theorem decoy_eventuallyZeroPhase_not_oscillatoryTail
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ)
    (hfin : EventuallyZeroPhase phase) :
    ¬ OscillatoryTail phase :=
  eventuallyZeroPhase_not_oscillatoryTail phase hfin

/-- Re-export: zero phase is a concrete `OscillatoryTail` discriminant. -/
theorem decoy_zeroPhase_not_oscillatoryTail :
    ¬ OscillatoryTail zeroPhase :=
  zeroPhase_not_oscillatoryTail

/-- Package-level decoy certificate: the composition interface is discriminating
against the certified dead classes. -/
theorem gap2_cutoff_composition_decoy_anchors :
    (¬ OscillatoryTail zeroPhase) ∧
      (∀ phase : ∀ n : ℕ, ExactPathClass n → ℝ,
        ShellConstant phase → ¬ OscillatoryTail phase) ∧
      (∀ phase : ∀ n : ℕ, ExactPathClass n → ℝ,
        EventuallyZeroPhase phase → ¬ OscillatoryTail phase) :=
  ⟨decoy_zeroPhase_not_oscillatoryTail,
    decoy_shellConstant_not_oscillatoryTail,
    decoy_eventuallyZeroPhase_not_oscillatoryTail⟩

/-! ## §4. Status (R1 closed; gap2 unflipped) -/

structure Gap2CutoffCompositionPackageStatus where
  r1CompositionClosed : Bool
  gap2ContinuumAndMeasure : Bool

def gap2CutoffCompositionPackageStatus :
    Gap2CutoffCompositionPackageStatus where
  r1CompositionClosed := true
  gap2ContinuumAndMeasure := false

theorem gap2CutoffCompositionPackageStatus_flags :
    gap2CutoffCompositionPackageStatus.r1CompositionClosed = true ∧
      gap2CutoffCompositionPackageStatus.gap2ContinuumAndMeasure = false := by
  decide

/-- R2 interface exposed by this package: inhabit `OscillatoryTail` for a
substrate-derived phase; this package then supplies
`HasPhasedZqComplexityLimit (capPhaseFamily phase)`. -/
def r2_interface_oscillatoryTail_to_capped_limit : Prop :=
  TypedResidual_gap2_cutoff_composition_package

theorem r2_interface_ready :
    r2_interface_oscillatoryTail_to_capped_limit :=
  typedResidual_gap2_cutoff_composition_package_closed

end

end SevenGaps
end Gravity
end IndisputableMonolith
