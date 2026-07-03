import Mathlib
import IndisputableMonolith.Masses.MassEpistemics
import IndisputableMonolith.Masses.QuarkPDGRatioAudit
import IndisputableMonolith.Masses.QuarkAbsoluteBridgeScoreCard

/-!
# Quark Observable Bridge

This module closes the taxonomic part of U5. It does not invent a QCD running operator.
It proves the bridge's allowed shape:

1. confined quark PDG "masses" are scheme parameters, not direct observed rest masses;
2. anchor-frame same-family ratios are theorem-grade intrinsic RS targets;
3. any MS-bar display bridge that uses one uniform first-generation factor is impossible,
   because charm/up and strange/down require opposite signs from the same anchor exponent `φ^11`.

The remaining physics target is now exact: either produce a scheme-free quark observable, or
derive a sector-dependent recognition-to-MS-bar display map. A direct, uniform PDG bridge is
machine-forbidden.

Lean status: 0 sorry.
-/

namespace IndisputableMonolith.Masses.QuarkObservableBridge

open IndisputableMonolith.Masses
open IndisputableMonolith.Masses.QuarkPDGRatioAudit
open IndisputableMonolith.Masses.QuarkAbsoluteBridgeScoreCard
open IndisputableMonolith.Masses.MassEpistemics
open IndisputableMonolith.Constants

noncomputable section

/-- The possible target types for a quark comparison row. -/
inductive QuarkObservableTarget where
  /-- Intrinsic RS anchor ratio, e.g. `c/u = φ^11`. -/
  | intrinsicAnchorRatio
  /-- A future scheme-free observable, such as a hadron or threshold quantity that cancels the scheme. -/
  | schemeFreeObservable
  /-- A scheme-tagged MS-bar bridge with a sector-dependent display operator. -/
  | sectorDependentMSbar
  /-- The forbidden shortcut: one direct, uniform MS-bar factor for both first-generation sectors. -/
  | uniformDirectMSbar
  deriving DecidableEq, Repr

/-- The first-generation uniform display claim: one factor `F` maps both anchor ratios to PDG
display ratios. The ratios are already divided by their shared anchor `φ^11`, so equality to one
factor is exactly the uniform-bridge assertion. -/
def UniformFirstGenDisplayFactor (F : ℝ) : Prop :=
  PDG_ratio_cu / phi ^ (11 : ℕ) = F ∧
  PDG_ratio_sd / phi ^ (11 : ℕ) = F

/-- A direct uniform MS-bar bridge is the forbidden first-generation display factor. -/
def DirectUniformMSbarBridge (F : ℝ) : Prop :=
  UniformFirstGenDisplayFactor F

/-- The intrinsic anchor bridge is already theorem-grade for the equal-Z charm/up row. -/
theorem intrinsic_charm_up_ratio_closed :
    IndisputableMonolith.Masses.Verification.charm_quark_pred /
      IndisputableMonolith.Masses.Verification.up_quark_pred =
      IndisputableMonolith.RSBridge.massAtAnchor .c /
        IndisputableMonolith.RSBridge.massAtAnchor .u :=
  row_charm_up_structural_anchor_agree

/-- The intrinsic anchor bridge is already theorem-grade for the equal-Z top/charm row. -/
theorem intrinsic_top_charm_ratio_closed :
    IndisputableMonolith.Masses.Verification.top_quark_pred /
      IndisputableMonolith.Masses.Verification.charm_quark_pred =
      IndisputableMonolith.RSBridge.massAtAnchor .t /
        IndisputableMonolith.RSBridge.massAtAnchor .c :=
  row_top_charm_structural_anchor_agree

/-- The quark PDG rows are scheme parameters in the mass-epistemics registry. -/
theorem quark_pdg_rows_are_scheme_parameters :
    confinedQuarks.all
      (fun p => isSchemeParameter (datum p ObservedSignal.hadronSpectrumFit
        InferenceDepth.schemeParameter)) = true :=
  confined_quarks_are_scheme

/-- No confined quark PDG mass is a direct observed rest mass. -/
theorem quark_pdg_rows_not_directly_observed :
    confinedQuarks.all
      (fun p => !directlyObserved (datum p ObservedSignal.hadronSpectrumFit
        InferenceDepth.schemeParameter)) = true :=
  confined_quarks_not_directly_observed

/-- **No uniform first-generation display factor.** If one factor `F` mapped both `c/u` and
`s/d` from the shared anchor `φ^11` to the PDG frame, that same `F` would have to be both above
one and below one. -/
theorem no_uniform_first_gen_display_factor (F : ℝ) :
    ¬ UniformFirstGenDisplayFactor F := by
  intro h
  have hcu : (1 : ℝ) < F := by
    rw [← h.1]
    exact cu_display_shift_above_one
  have hsd : F < (1 : ℝ) := by
    rw [← h.2]
    exact sd_display_shift_below_one
  linarith

/-- Direct uniform MS-bar display is forbidden. -/
theorem no_direct_uniform_msbar_bridge (F : ℝ) :
    ¬ DirectUniformMSbarBridge F :=
  no_uniform_first_gen_display_factor F

/-- A target is admissible if it is either intrinsic, genuinely scheme-free, or explicitly
sector-dependent. The direct uniform MS-bar shortcut is excluded. -/
def targetAdmissible : QuarkObservableTarget → Prop
  | .intrinsicAnchorRatio => True
  | .schemeFreeObservable => True
  | .sectorDependentMSbar => True
  | .uniformDirectMSbar => False

theorem uniform_direct_msbar_target_not_admissible :
    ¬ targetAdmissible .uniformDirectMSbar := by
  simp [targetAdmissible]

theorem intrinsic_anchor_target_admissible :
    targetAdmissible .intrinsicAnchorRatio := by
  simp [targetAdmissible]

theorem sector_dependent_msbar_target_admissible :
    targetAdmissible .sectorDependentMSbar := by
  simp [targetAdmissible]

/-- The U5 closure certificate: the direct comparison is barred, and the two remaining
physical options are explicit. -/
structure QuarkObservableBridgeCert where
  quarks_are_scheme :
    confinedQuarks.all
      (fun p => isSchemeParameter (datum p ObservedSignal.hadronSpectrumFit
        InferenceDepth.schemeParameter)) = true
  quarks_not_direct :
    confinedQuarks.all
      (fun p => !directlyObserved (datum p ObservedSignal.hadronSpectrumFit
        InferenceDepth.schemeParameter)) = true
  intrinsic_cu_closed :
    IndisputableMonolith.Masses.Verification.charm_quark_pred /
      IndisputableMonolith.Masses.Verification.up_quark_pred =
      IndisputableMonolith.RSBridge.massAtAnchor .c /
        IndisputableMonolith.RSBridge.massAtAnchor .u
  intrinsic_tc_closed :
    IndisputableMonolith.Masses.Verification.top_quark_pred /
      IndisputableMonolith.Masses.Verification.charm_quark_pred =
      IndisputableMonolith.RSBridge.massAtAnchor .t /
        IndisputableMonolith.RSBridge.massAtAnchor .c
  no_uniform_msbar : ∀ F : ℝ, ¬ DirectUniformMSbarBridge F
  uniform_target_forbidden : ¬ targetAdmissible .uniformDirectMSbar
  intrinsic_allowed : targetAdmissible .intrinsicAnchorRatio
  sector_dependent_allowed : targetAdmissible .sectorDependentMSbar

theorem quarkObservableBridgeCert_holds :
    Nonempty QuarkObservableBridgeCert :=
  ⟨{ quarks_are_scheme := quark_pdg_rows_are_scheme_parameters
     quarks_not_direct := quark_pdg_rows_not_directly_observed
     intrinsic_cu_closed := intrinsic_charm_up_ratio_closed
     intrinsic_tc_closed := intrinsic_top_charm_ratio_closed
     no_uniform_msbar := no_direct_uniform_msbar_bridge
     uniform_target_forbidden := uniform_direct_msbar_target_not_admissible
     intrinsic_allowed := intrinsic_anchor_target_admissible
     sector_dependent_allowed := sector_dependent_msbar_target_admissible }⟩

end

end IndisputableMonolith.Masses.QuarkObservableBridge
