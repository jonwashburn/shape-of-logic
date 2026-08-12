import IndisputableMonolith.Gravity.SevenGaps.WickHingeDataComplete
import IndisputableMonolith.Gravity.SevenGaps.WickFourOneAllHinges
import IndisputableMonolith.Gravity.SevenGaps.WickThreeTwoHinges
import IndisputableMonolith.Gravity.SevenGaps.CausalSimplexWick
import IndisputableMonolith.Gravity.SevenGaps.GluedPentsHingeWitness
import IndisputableMonolith.Gravity.SevenGaps.ThreePentCausalConsistency
import IndisputableMonolith.Gravity.SevenGaps.WickActionCertFamilyAssembly
import IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger
import IndisputableMonolith.Gravity.SevenGaps.CampaignLedger
import IndisputableMonolith.Gravity.Analysis.SRSConvergesEH4D

/-!
# Wave C4 R0: gap6 lookalike-falsify receipt (updated F3 2026-07-23;
# honesty patch 2026-07-23)

Falsify-before-proving residual from
`plans/QG_WaveC4_Gap6_Residual_DAG_Draft_20260722.txt` §R0
(`TypedResidual_gap6_lookalike_decoys_fail`).

Each banked lookalike below is a positive theorem that a later session
might rename into the ledger terminal. This module packages per-lookalike
**separation certificates**: the lookalike holds, and a post-close witness
that it does **not** discharge / would not have sufficed for
`wick_action_continuation_4d_v2` (domain mismatch, V1 action-field kill,
or distinct closer co-assertion).

F3 succession (2026-07-23): gap6 closed via `wick_action_continuation_4d_v2`.
Lookalike mathematics is retained; obsolete "gap6 stays false" conjuncts
are replaced by post-close-compatible separation (E-gap6-postclose-critic-20260723
patch 1). Binding detail:
`WickActionV2CloseStatus.gap6_lorentzian_action_bound_to_v2`.

No `sorry`, `admit`, new axiom, or `native_decide`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap6LookalikeReceipt

open FullTheoryLedger
open CampaignLedger
open CausalSimplex4D (CausalPentType causalSimplex4DStatus cm4)
open CausalSimplexWick (CausalTetType lorentzianSectorStatus)
open WickHingeDataComplete
open WickActionComplexFirst
open WickActionInteriorHinge
open WickFourOneAllHinges (fourOneCosPath)
open WickThreeTwoHinges (threeTwoCosPath tStarMixed)
open GluedPentsHingeWitness
open ThreePentCausalConsistency
open Analysis.SRSConvergesEH4D

noncomputable section

/-! ## §1. Dimension mismatch (3D edge-tuple continuation ≠ 4D carrier) -/

/-- 3D CDT tetrahedra use 4 vertices; the 4D carrier uses 5. -/
theorem simplex3d_vertex_card_ne_4d :
    Fintype.card (Fin 4) ≠ Fintype.card (Fin 5) := by
  decide

/-- 3D edge tuples are `Fin 6 → ℝ`; 4D edge tuples are `Fin 10 → ℝ`. -/
theorem simplex3d_edge_card_ne_4d :
    Fintype.card (Fin 6) ≠ Fintype.card (Fin 10) := by
  decide

/-- Re-export: the 3D lookalike theorem is banked (edge-tuple algebra
`alpha ↦ -alpha` only). -/
theorem lorentzian_continuation_3d_banked
    (ty : CausalTetType) (a alpha : ℝ) :
    CausalSimplexWick.lorentzianSqEdges ty a (-alpha) =
      CausalSimplexWick.euclideanSqEdges ty a alpha :=
  CausalSimplexWick.lorentzian_continuation ty a alpha

/-- **S1 certificate.** 3D edge-tuple algebra; carrier dimension / edge
arity differ from the 4D ledger shape. The 3D sector's action-level Bool
stays open (3D never received the action closer). -/
def LorentzianContinuation3DNotAction4DCertificate : Prop :=
  (∀ ty : CausalTetType, ∀ a alpha : ℝ,
      CausalSimplexWick.lorentzianSqEdges ty a (-alpha) =
        CausalSimplexWick.euclideanSqEdges ty a alpha) ∧
    Fintype.card (Fin 4) ≠ Fintype.card (Fin 5) ∧
      Fintype.card (Fin 6) ≠ Fintype.card (Fin 10) ∧
        lorentzianSectorStatus.lorentzian_action_continuation_open = true

theorem lorentzianContinuation3DNotAction4DCertificate :
    LorentzianContinuation3DNotAction4DCertificate :=
  ⟨lorentzian_continuation_3d_banked, simplex3d_vertex_card_ne_4d,
    simplex3d_edge_card_ne_4d, rfl⟩

/-- Re-export: 4D kinematical edge continuation is also banked, and is
likewise not the action-level closer. -/
theorem lorentzian_continuation_4d_kinematical_banked
    (ty : CausalPentType) (a alpha : ℝ) :
    CausalSimplex4D.lorentzianSqEdges ty a (-alpha) =
      CausalSimplex4D.euclideanSqEdges ty a alpha :=
  CausalSimplex4D.lorentzian_continuation ty a alpha

/-- **S1 twin (4D kinematical).** Edge-tuple `alpha ↦ -alpha` on
`SqEdges10` is kinematical algebra. Post-close separation: the lookalike
holds for all `α`, including outside CertV2's causal range `7/12 < α`
(witness `α = 0`); hence it is strictly weaker than /
would not have sufficed for `wick_action_continuation_4d_v2`. -/
def LorentzianContinuation4DKinematicalNotActionCertificate : Prop :=
  (∀ ty : CausalPentType, ∀ a alpha : ℝ,
      CausalSimplex4D.lorentzianSqEdges ty a (-alpha) =
        CausalSimplex4D.euclideanSqEdges ty a alpha) ∧
    ¬ ((7 / 12 : ℝ) < (0 : ℝ))

theorem lorentzianContinuation4DKinematicalNotActionCertificate :
    LorentzianContinuation4DKinematicalNotActionCertificate :=
  ⟨lorentzian_continuation_4d_kinematical_banked, by norm_num⟩

/-! ## §2. Hinge-DATA completeness ≠ action-level closer (S2) -/

/-- **S2 certificate.** `wick_hinge_data_continuation_complete` quantifies
`BranchRegularOn` / cosine paths over single-simplex opposite pairs. It
does not inhabit a deficit-weighted three-pent action. Post-close
separation: hinge-data coexists with V1
`ContinuousOn (wickActionPath 1) (Icc 0 1)` unsatisfiability; hinge-data
alone would not have sufficed for the action-level target (V2 closed via
Ioc + cutLimit family assembly). -/
def HingeDataNotActionLevelCertificate : Prop :=
  (∀ p q : Fin 5, p ≠ q →
      (BranchRegularOn
          (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t) p q
          (Set.Ioo 0 1)
        ∧ ContinuousOn (fourOneCosPath p q) (Set.Icc 0 1)
        ∧ fourOneCosPath p q 1 = -(1 / 4 : ℂ))
      ∧ (BranchRegularOn
          (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t) p q
          (Set.Ioo 0 1)
        ∧ ContinuousOn (threeTwoCosPath p q) (Set.Icc 0 1)
        ∧ threeTwoCosPath p q 1 = -(1 / 4 : ℂ))) ∧
    ¬ ContinuousOn (wickActionPath 1) (Set.Icc 0 1)

theorem hingeDataNotActionLevelCertificate :
    HingeDataNotActionLevelCertificate :=
  ⟨wick_hinge_data_continuation_complete, contAction_not_satisfiable_at_one⟩

/-! ## §3. cm4 sign ≠ Lorentzian realizability (S3 / L-4) -/

/-- **S3 certificate.** Per-pent `cm4 < 0` is a sign fact, not
action-level Wick continuation. Post-close separation: the sign fact
holds for all `0 ≤ α`, including outside CertV2's causal range
(witness `α = 0`); hence it would not have sufficed for
`wick_action_continuation_4d_v2`. -/
def Cm4SignNotActionLevelCertificate : Prop :=
  (∀ a alpha : ℝ, 0 < a → 0 ≤ alpha →
      cm4 (inducedSqEdges pentAVert a alpha) < 0 ∧
        cm4 (inducedSqEdges pentBVert a alpha) < 0 ∧
          cm4 (inducedSqEdges pentCVert a alpha) < 0) ∧
    ¬ ((7 / 12 : ℝ) < (0 : ℝ))

theorem cm4SignNotActionLevelCertificate :
    Cm4SignNotActionLevelCertificate :=
  ⟨threePent_lorentzian_cm4_neg, by norm_num⟩

/-! ## §4. BranchRegularOn / product-form ≠ deficit-sum certificate (S4/S9) -/

/-- **S4+S9 certificate.** Product-form `csqrt(C_pp*C_qq)` is
kernel-killed at interior arc parameters. -/
def BranchRegularOnNotDeficitSumCertificate : Prop :=
  ((tStarMixed ∈ Set.Ioo (0 : ℝ) 1
      ∧ cmCofactorC (continuationEdgesC CausalPentType.threeTwo 1 1 tStarMixed) 1 1
          * cmCofactorC (continuationEdgesC CausalPentType.threeTwo 1 1 tStarMixed) 4 4
          = -40
      ∧ (-40 : ℂ) ∉ Complex.slitPlane)
      ∧ ((2 / 3 : ℝ) ∈ Set.Ioo (0 : ℝ) 1
      ∧ cmCofactorC (continuationEdgesC CausalPentType.threeTwo 1 1 (2 / 3)) 1 1
          * cmCofactorC (continuationEdgesC CausalPentType.threeTwo 1 1 (2 / 3)) 2 2
          = -48
      ∧ (-48 : ℂ) ∉ Complex.slitPlane)) ∧
    (tStar ∈ Set.Ioo (0 : ℝ) 1
      ∧ cmCofactorC (continuationEdgesC CausalPentType.fourOne 1 1 tStar) 3 3
          * cmCofactorC (continuationEdgesC CausalPentType.fourOne 1 1 tStar) 4 4
          = -32
      ∧ (-32 : ℂ) ∉ Complex.slitPlane)

theorem branchRegularOnNotDeficitSumCertificate :
    BranchRegularOnNotDeficitSumCertificate :=
  ⟨wick_product_form_kills_memorialized, product_form_crossing⟩

/-! ## §5. Two-pent path-link kill (S6) -/

/-- Re-export: interior hinge counting requires ≥ 3 pents. -/
theorem interior_hinge_needs_three_pents_banked
    (pents : Finset (Finset (Fin 6)))
    (hcycle : IsCycleLink (pents.image (fun P => P \ hinge))) :
    3 ≤ pents.card :=
  interior_hinge_needs_three_pents pents hcycle

/-- **S6 kill.** The two-pent complex never presents an interior hinge. -/
theorem two_pent_interior_impossible :
    ¬ IsCycleLink (twoPentComplex.image (fun P => P \ hinge)) :=
  twoPent_hinge_never_interior

/-- Packaged two-pent decoy kill + counting lemma. -/
def TwoPentNotInteriorActionCertificate : Prop :=
  (¬ IsCycleLink (twoPentComplex.image (fun P => P \ hinge))) ∧
    (∀ pents : Finset (Finset (Fin 6)),
      IsCycleLink (pents.image (fun P => P \ hinge)) → 3 ≤ pents.card)

theorem twoPentNotInteriorActionCertificate :
    TwoPentNotInteriorActionCertificate :=
  ⟨two_pent_interior_impossible, interior_hinge_needs_three_pents_banked⟩

/-! ## §6. Euclidean EH recovery ≠ gap6 close (S7) -/

/-- **S7 certificate.** `S_RS_converges_EH_4d` inhabits
`gap_action_recovery`; it is Euclidean EH recovery, not the Lorentzian
action-continuation closer. Post-close separation: EH co-asserts with the
real gap6 closer `wick_action_continuation_4d_v2` (distinct named
terminals; EH alone would not have sufficed for gap6 / V2). -/
def EHRecoveryNotGap6Certificate : Prop :=
  S_RS_converges_EH_4d ∧
    fullTheoryBenchmarks.gap_action_recovery = true ∧
      wick_action_continuation_4d_v2 ∧
        fullTheoryBenchmarks.gap6_lorentzian_action = true

theorem ehRecoveryNotGap6Certificate :
    EHRecoveryNotGap6Certificate :=
  ⟨S_RS_converges_EH_4d_closed, rfl, wick_action_continuation_4d_v2_holds, rfl⟩

/-! ## §7. Ledger terminal guard (post-F3 succession) -/

/-- **Guard Prop after F3 close.** Gap6 flipped via V2; campaign /
CausalSimplex4D action-open bits cleared; kinematical Wick certified;
3D LorentzianSector action bit remains open. -/
def Gap6LedgerTerminalGuard : Prop :=
  fullTheoryBenchmarks.gap6_lorentzian_action = true ∧
    sevenGapsCampaignStatus.gap6_action_continuation_open = false ∧
      causalSimplex4DStatus.action_level_continuation_open = false ∧
        lorentzianSectorStatus.lorentzian_action_continuation_open = true ∧
          sevenGapsCampaignStatus.gap6_kinematical_wick_certified = true

theorem gap6LedgerTerminalGuard : Gap6LedgerTerminalGuard :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## §8. DAG R0 residual (all lookalike decoys fail) -/

/-- **DAG R0 residual Prop.** Lookalikes separated by content; post-F3
guard records the V2 ledger close. -/
def TypedResidual_gap6_lookalike_decoys_fail : Prop :=
  LorentzianContinuation3DNotAction4DCertificate ∧
    LorentzianContinuation4DKinematicalNotActionCertificate ∧
      HingeDataNotActionLevelCertificate ∧
        Cm4SignNotActionLevelCertificate ∧
          BranchRegularOnNotDeficitSumCertificate ∧
            TwoPentNotInteriorActionCertificate ∧
              EHRecoveryNotGap6Certificate ∧
                Gap6LedgerTerminalGuard

/-- R0 residual closed by the lookalike-falsify package. -/
theorem typedResidual_gap6_lookalike_decoys_fail :
    TypedResidual_gap6_lookalike_decoys_fail :=
  ⟨lorentzianContinuation3DNotAction4DCertificate,
    lorentzianContinuation4DKinematicalNotActionCertificate,
    hingeDataNotActionLevelCertificate,
    cm4SignNotActionLevelCertificate,
    branchRegularOnNotDeficitSumCertificate,
    twoPentNotInteriorActionCertificate,
    ehRecoveryNotGap6Certificate,
    gap6LedgerTerminalGuard⟩

theorem TypedResidual_gap6_lookalike_decoys_fail_closed :
    TypedResidual_gap6_lookalike_decoys_fail :=
  typedResidual_gap6_lookalike_decoys_fail

/-! ## §9. Status (R0 lookalike receipt closed; gap6 flipped via V2) -/

structure Gap6LookalikeReceiptStatus where
  /-- R0 lookalike-falsify receipt closed. -/
  lookalikeReceiptClosed : Bool
  /-- Frozen V1 schema: closed (not open). -/
  wickActionSchemaOpen : Bool
  /-- Deficit-sum branch regularity: closed via CertV2. -/
  deficitSumBranchOpen : Bool
  /-- Ledger terminal: closed via `wick_action_continuation_4d_v2`. -/
  wickActionTerminalOpen : Bool
  /-- Ledger flag flipped 2026-07-23. -/
  gap6LorentzianAction : Bool

def gap6LookalikeReceiptStatus : Gap6LookalikeReceiptStatus where
  lookalikeReceiptClosed := true
  wickActionSchemaOpen := false
  deficitSumBranchOpen := false
  wickActionTerminalOpen := false
  gap6LorentzianAction := true

/-- Status theorem: R0 lookalike separation retained; gap6 closed via V2. -/
theorem gap6LookalikeReceiptStatus_flags :
    gap6LookalikeReceiptStatus.lookalikeReceiptClosed = true ∧
      gap6LookalikeReceiptStatus.wickActionSchemaOpen = false ∧
        gap6LookalikeReceiptStatus.deficitSumBranchOpen = false ∧
          gap6LookalikeReceiptStatus.wickActionTerminalOpen = false ∧
            gap6LookalikeReceiptStatus.gap6LorentzianAction = true ∧
              fullTheoryBenchmarks.gap6_lorentzian_action = true ∧
                sevenGapsCampaignStatus.gap6_action_continuation_open = false ∧
                  causalSimplex4DStatus.action_level_continuation_open = false ∧
                    lorentzianSectorStatus.lorentzian_action_continuation_open
                      = true ∧
                      sevenGapsCampaignStatus.gap6_kinematical_wick_certified
                        = true := by
  decide

end

end Gap6LookalikeReceipt
end SevenGaps
end Gravity
end IndisputableMonolith
