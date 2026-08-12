import IndisputableMonolith.Gravity.SevenGaps.Gap2EnrichedCarrierPhase
import IndisputableMonolith.Gravity.SevenGaps.Gap2CertifiedFin8PhaseClose
import IndisputableMonolith.Gravity.SevenGaps.Gap2AntipodalBalanceBridge
import IndisputableMonolith.Gravity.SevenGaps.Gap2TickPhaseTailBlocker

/-!
# Gap2 posting-cocycle carrier: forgetful map + STOP A residual

Implements the carrier half of `D-qg-gap2-posting-cocycle-20260723`.

The RS eight-tick recognition-posting cocycle already exists as a period-8
transaction
(`Foundation.PairKernelGap2aPhaseBearingTransactionResidual.phaseBearingActualTransaction_cert`).
`CertifiedGap2Fin8PhaseClose` wants a Fin-8 tick on `ExactPathClass`.
Those live on different carriers: PairKernel phase is transaction state;
`ExactComplex` / `ExactPathClass` carry only incidence (`edgeVerts` /
`tetVerts`).

## Landed this module

* `PostingEnrichedPathClass` / `PostingEnrichedExactHistory`: product
  enrichment adjoining an external Fin-8 posting phase.
* `forgetPostingPhase` / `postingPhase` and exact-history analogs.
* **THEOREM** `carrier_forgets_posting_phase` /
  `postingPhase_not_factors_through_forget`: forgetful descent erases
  the posting coordinate; the coordinate itself does not descend.
* **CLOSED blocker residual**
  `TypedResidual_carrier_forgets_posting_phase` (STOP A receipt).
* **OPEN** `TypedResidual_posting_cocycle_bridge`: non-forgetful
  GE-invariant antipodal bridge still required for certified close.

## Explicit refusal

Do **not** invent an incidence hash, mod-2 parity, or product-section
`⟨c, tau c⟩` and call it the posting cocycle. Prefer this STOP A bank
over a fake descent. Does **not** flip `gap2_continuum_and_measure`.
No `sorry`, `admit`, new axiom, or `native_decide`. Does **not** touch CPL.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2PostingCocycleCarrier

open ExactShellGaugeUV
open Gap2TickPhaseTailBlocker
open Gap2EnrichedCarrierPhase
open Gap2CertifiedFin8PhaseClose
open Gap2AntipodalBalanceBridge

noncomputable section

/-! ## §1. Product enrichment and forgetful map -/

/-- Exact path class with an adjoined Fin-8 posting-phase coordinate.
This is the honest product enrichment of the Gap2 shell carrier by the
transaction phase type from the RS eight-tick posting cocycle. -/
structure PostingEnrichedPathClass (n : ℕ) where
  underlying : ExactPathClass n
  postingPhase : Fin 8

/-- Forget the posting phase; retain the exact path class. -/
def forgetPostingPhase {n : ℕ} (H : PostingEnrichedPathClass n) :
    ExactPathClass n :=
  H.underlying

/-- Read the adjoined posting-phase coordinate. -/
def postingPhase {n : ℕ} (H : PostingEnrichedPathClass n) : Fin 8 :=
  H.postingPhase

theorem forgetPostingPhase_mk {n : ℕ} (c : ExactPathClass n) (p : Fin 8) :
    forgetPostingPhase ⟨c, p⟩ = c :=
  rfl

theorem postingPhase_mk {n : ℕ} (c : ExactPathClass n) (p : Fin 8) :
    postingPhase ⟨c, p⟩ = p :=
  rfl

/-- A family on enriched histories factors through the forgetful map when
it depends only on the underlying exact path class. -/
def FactorsThroughPostingForget
    (f : ∀ n : ℕ, PostingEnrichedPathClass n → Fin 8) : Prop :=
  ∃ tau : ∀ n : ℕ, ExactPathClass n → Fin 8,
    ∀ (n : ℕ) (H : PostingEnrichedPathClass n),
      f n H = tau n (forgetPostingPhase H)

/-! ## §2. Carrier forgets posting phase (STOP A) -/

/-- **THEOREM.** Descent through `forgetPostingPhase` erases the posting
coordinate: any factoring family is constant in `postingPhase`. -/
theorem carrier_forgets_posting_phase
    (f : ∀ n : ℕ, PostingEnrichedPathClass n → Fin 8)
    (h : FactorsThroughPostingForget f)
    (n : ℕ) (c : ExactPathClass n) (p q : Fin 8) :
    f n ⟨c, p⟩ = f n ⟨c, q⟩ := by
  obtain ⟨tau, htau⟩ := h
  calc
    f n ⟨c, p⟩ = tau n (forgetPostingPhase ⟨c, p⟩) := htau n ⟨c, p⟩
    _ = tau n c := by rw [forgetPostingPhase_mk]
    _ = tau n (forgetPostingPhase ⟨c, q⟩) := by rw [forgetPostingPhase_mk]
    _ = f n ⟨c, q⟩ := (htau n ⟨c, q⟩).symm

/-- The posting-phase coordinate does not factor through the forgetful map. -/
theorem postingPhase_not_factors_through_forget :
    ¬ FactorsThroughPostingForget fun _n H => postingPhase H := by
  rintro ⟨tau, htau⟩
  let c0 : ExactPathClass 0 := isolatedClass 0
  have h0 := htau 0 ⟨c0, 0⟩
  have h1 := htau 0 ⟨c0, 1⟩
  have hEq : (0 : Fin 8) = 1 := by
    calc
      (0 : Fin 8) = postingPhase (⟨c0, 0⟩ : PostingEnrichedPathClass 0) := rfl
      _ = tau 0 (forgetPostingPhase ⟨c0, 0⟩) := h0
      _ = tau 0 c0 := by rw [forgetPostingPhase_mk]
      _ = tau 0 (forgetPostingPhase ⟨c0, 1⟩) := by rw [forgetPostingPhase_mk]
      _ = postingPhase (⟨c0, 1⟩ : PostingEnrichedPathClass 0) := h1.symm
      _ = 1 := rfl
  exact (by decide : ¬ ((0 : Fin 8) = 1)) hEq

/-- Same forgetfulness at labeled exact-complex product level. -/
structure PostingEnrichedExactHistory (v e t : ℕ) where
  K : ExactComplex v e t
  postingPhase : Fin 8

def forgetExactHistory {v e t : ℕ} (H : PostingEnrichedExactHistory v e t) :
    ExactComplex v e t :=
  H.K

def FactorsThroughExactHistoryForget
    (f : ∀ v e t : ℕ, PostingEnrichedExactHistory v e t → Fin 8) : Prop :=
  ∃ lab : LabeledTick,
    ∀ v e t (H : PostingEnrichedExactHistory v e t),
      f v e t H = lab v e t (forgetExactHistory H)

theorem exact_carrier_forgets_posting_phase
    (f : ∀ v e t : ℕ, PostingEnrichedExactHistory v e t → Fin 8)
    (h : FactorsThroughExactHistoryForget f)
    (v e t : ℕ) (K : ExactComplex v e t) (p q : Fin 8) :
    f v e t ⟨K, p⟩ = f v e t ⟨K, q⟩ := by
  obtain ⟨lab, hlab⟩ := h
  calc
    f v e t ⟨K, p⟩ = lab v e t (forgetExactHistory ⟨K, p⟩) := hlab v e t ⟨K, p⟩
    _ = lab v e t K := rfl
    _ = lab v e t (forgetExactHistory ⟨K, q⟩) := rfl
    _ = f v e t ⟨K, q⟩ := (hlab v e t ⟨K, q⟩).symm

theorem exact_postingPhase_not_factors_through_forget :
    ¬ FactorsThroughExactHistoryForget
        fun _v _e _t H => H.postingPhase := by
  rintro ⟨lab, hlab⟩
  let K0 : ExactComplex 0 0 0 := isolatedVertices 0
  have h0 := hlab 0 0 0 ⟨K0, 0⟩
  have h1 := hlab 0 0 0 ⟨K0, 1⟩
  have hEq : (0 : Fin 8) = 1 := by
    calc
      (0 : Fin 8) = (⟨K0, 0⟩ : PostingEnrichedExactHistory 0 0 0).postingPhase :=
        rfl
      _ = lab 0 0 0 (forgetExactHistory ⟨K0, 0⟩) := h0
      _ = lab 0 0 0 K0 := rfl
      _ = lab 0 0 0 (forgetExactHistory ⟨K0, 1⟩) := rfl
      _ = (⟨K0, 1⟩ : PostingEnrichedExactHistory 0 0 0).postingPhase := h1.symm
      _ = 1 := rfl
  exact (by decide : ¬ ((0 : Fin 8) = 1)) hEq

/-! ## §3. Residuals: CLOSED forgetfulness + OPEN non-forgetful bridge -/

/-- **CLOSED STOP A residual.** The posting-phase coordinate on product
enrichment does not descend through the forgetful map to `ExactPathClass`. -/
def TypedResidual_carrier_forgets_posting_phase : Prop :=
  ¬ FactorsThroughPostingForget fun _n H => postingPhase H

theorem typedResidual_carrier_forgets_posting_phase :
    TypedResidual_carrier_forgets_posting_phase :=
  postingPhase_not_factors_through_forget

/-- **OPEN package.** A GE-invariant labeled tick with antipodal mass
balance, i.e. a non-forgetful inhabit route toward
`CertifiedGap2Fin8PhaseClose`. Product enrichment cannot supply this via
`forgetPostingPhase` (see STOP A). A future session must derive `lab`
from exact incidence using period-8 posting semantics, not glue an
external Fin-8 coordinate. -/
structure PostingCocycleExactPathBridge where
  lab : LabeledTick
  invariant : GlobalEquivalentInvariant lab
  not_shellSig : ¬ ShellSigTick (descendedTick lab invariant)
  antipodalBalance :
    EventuallyTickFiberAntipodalMassBalanced (descendedTick lab invariant)

/-- Descended class-level tick of a bridge (defined when inhabited). -/
def bridgeClassTick (B : PostingCocycleExactPathBridge) :
    ∀ n : ℕ, ExactPathClass n → Fin 8 :=
  descendedTick B.lab B.invariant

/-- **OPEN residual.** Nonempty non-forgetful posting-cocycle bridge. -/
def TypedResidual_posting_cocycle_bridge : Prop :=
  Nonempty PostingCocycleExactPathBridge

/-- Packaging helper: a bridge yields a certified recipe package with API
honesty markers. Does not inhabit the close. -/
def certifiedRecipe_of_bridge (B : PostingCocycleExactPathBridge) :
    CertifiedTickRecipe (bridgeClassTick B) where
  kind := CertifiedTickRecipeKind.mixedAutMassBalancer
  globalEquivalentProvenance := trivial
  notAmplitudeOracle := trivial
  notShellwiseClassicalAssembly := trivial
  tickDerived := trivial

/-! ## §4. Status (STOP A banked; gap2 unflipped) -/

structure Gap2PostingCocycleCarrierStatus where
  enrichedProductCarrierBanked : Bool
  forgetfulMapBanked : Bool
  carrierForgetsPhaseProved : Bool
  postingPhaseDoesNotDescend : Bool
  carrierForgetsPhaseResidualClosed : Bool
  bridgeResidualDefinedOpen : Bool
  certifiedCloseInhabited : Bool
  gap2ContinuumAndMeasure : Bool

def gap2PostingCocycleCarrierStatus : Gap2PostingCocycleCarrierStatus where
  enrichedProductCarrierBanked := true
  forgetfulMapBanked := true
  carrierForgetsPhaseProved := true
  postingPhaseDoesNotDescend := true
  carrierForgetsPhaseResidualClosed := true
  bridgeResidualDefinedOpen := true
  certifiedCloseInhabited := false
  gap2ContinuumAndMeasure := false

theorem gap2PostingCocycleCarrierStatus_flags :
    gap2PostingCocycleCarrierStatus.enrichedProductCarrierBanked = true ∧
      gap2PostingCocycleCarrierStatus.forgetfulMapBanked = true ∧
      gap2PostingCocycleCarrierStatus.carrierForgetsPhaseProved = true ∧
      gap2PostingCocycleCarrierStatus.postingPhaseDoesNotDescend = true ∧
      gap2PostingCocycleCarrierStatus.carrierForgetsPhaseResidualClosed =
        true ∧
      gap2PostingCocycleCarrierStatus.bridgeResidualDefinedOpen = true ∧
      gap2PostingCocycleCarrierStatus.certifiedCloseInhabited = false ∧
      gap2PostingCocycleCarrierStatus.gap2ContinuumAndMeasure = false := by
  decide

end

end Gap2PostingCocycleCarrier
end SevenGaps
end Gravity
end IndisputableMonolith
