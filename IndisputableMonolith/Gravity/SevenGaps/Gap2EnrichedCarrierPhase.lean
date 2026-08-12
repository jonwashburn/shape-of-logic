import IndisputableMonolith.Gravity.SevenGaps.Gap2TickPhaseTailBlocker
import IndisputableMonolith.Gravity.SevenGaps.Gap2SignatureBlockerAttack

/-!
# Wave C R5 attack: enriched-carrier phase below `ExactPathClass`

Implements decision `D-qg-c1-r4-enriched-carrier-20260722` on the
continuum R5 residual

    TypedResidual_continuum_substrate_oscillatoryTail
      := ∃ phase, OscillatoryTail phase ∧ ¬ OscillatoryTail zeroPhase

after the signature-level Fin-8 attack stalled (mesoscopic-only cube
dominance; `SignatureFin8OscillatoryTailBlocker` DEFINED unproved).

## Choice this session: A attempted → C terminal

Route A (enriched carrier forcing eventual mass balance / identical-zero
late amplitudes) is the design-correct attack surface. This module banks
the carrier API, descent, and a concrete quotient-internal tick that
escapes `ShellSigTick`. Proving eventual fiber-mass balance (or
identical-zero late amplitudes) for that tick refused in one Elmo
session: no honest partition of Burnside masses is available from the
self-loop invariant alone.

Route B (`SignatureFin8OscillatoryTailBlocker`) refused: late-shell mass
fragmentation makes the blocker less plausible, not more; the prior
session already killed dominance as a proof strategy.

Therefore the credit-bearing terminal is route C: a sharper typed
residual naming the enriched-carrier obligation, plus characterization
and bridge lemmas. R5 itself stays OPEN (uninhabited).

Does NOT flip `gap2_continuum_and_measure`. No `sorry`, `admit`, new
axiom, or `native_decide`. Does NOT edit `Gap2ContinuumMeasureResidualDAG`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2EnrichedCarrierPhase

open ExactShellGaugeUV
open ZqContinuumBlocker
open Gap2TickPhaseSubstrate
open Gap2TickPhaseTailBlocker
open Gap2SignatureBlockerAttack

noncomputable section

/-! ## §1. Enriched labeled tick (GlobalEquivalent-invariant) -/

/-- A Fin-8 tick on labeled exact complexes. -/
abbrev LabeledTick := ∀ v e t : ℕ, ExactComplex v e t → Fin 8

/-- **Enrichment hyp.** Tick is constant on `GlobalEquivalent` orbits. -/
def GlobalEquivalentInvariant (lab : LabeledTick) : Prop :=
  ∀ (v e t : ℕ) (K K' : ExactComplex v e t),
    GlobalEquivalent K K' → lab v e t K = lab v e t K'

/-- Descent of an invariant labeled tick to exact path classes. -/
noncomputable def descendedTick
    (lab : LabeledTick) (hInv : GlobalEquivalentInvariant lab) :
    ∀ n : ℕ, ExactPathClass n → Fin 8 :=
  fun _n c =>
    Quotient.lift (lab (sigV c.1) (sigE c.1) (sigT c.1))
      (fun K K' h => hInv _ _ _ K K' h) c.2

theorem descendedTick_mk
    (lab : LabeledTick) (hInv : GlobalEquivalentInvariant lab)
    {n : ℕ} (s : ShellSig n) (K : ExactComplex (sigV s) (sigE s) (sigT s)) :
    descendedTick lab hInv n ⟨s, Quotient.mk _ K⟩ =
      lab (sigV s) (sigE s) (sigT s) K :=
  rfl

/-- Derived real phase of an enriched labeled tick. -/
def enrichedPhase
    (lab : LabeledTick) (hInv : GlobalEquivalentInvariant lab) :
    ∀ n : ℕ, ExactPathClass n → ℝ :=
  tickDerivedPhase (descendedTick lab hInv)

/-! ## §2. Concrete enriched invariant: self-loop count mod 8 -/

/-- Number of loop edges (both endpoints equal). -/
noncomputable def selfLoopCount {v e t : ℕ} (K : ExactComplex v e t) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun i : Fin e => (K.edgeVerts i).1 = (K.edgeVerts i).2)).card

theorem selfLoopCount_congr {v e t : ℕ} {K K' : ExactComplex v e t}
    (r : ExactRelabel K K') :
    selfLoopCount K = selfLoopCount K' := by
  classical
  unfold selfLoopCount
  let ε := r.eEquiv
  have hiff : ∀ i : Fin e,
      ((K.edgeVerts i).1 = (K.edgeVerts i).2) ↔
        ((K'.edgeVerts (ε i)).1 = (K'.edgeVerts (ε i)).2) := by
    intro i
    have h := r.edge_comm i
    constructor
    · intro hloop
      have : r.vEquiv (K.edgeVerts i).1 = r.vEquiv (K.edgeVerts i).2 := by
        simp [hloop]
      have hK' : K'.edgeVerts (ε i) =
          (r.vEquiv (K.edgeVerts i).1, r.vEquiv (K.edgeVerts i).2) := by
        simpa [Prod.map] using h
      simpa [hK'] using this
    · intro hloop
      have hK' : K'.edgeVerts (ε i) =
          (r.vEquiv (K.edgeVerts i).1, r.vEquiv (K.edgeVerts i).2) := by
        simpa [Prod.map] using h
      have : r.vEquiv (K.edgeVerts i).1 = r.vEquiv (K.edgeVerts i).2 := by
        simpa [hK'] using hloop
      exact r.vEquiv.injective this
  have himg :
      Finset.univ.filter
          (fun i : Fin e => (K'.edgeVerts i).1 = (K'.edgeVerts i).2) =
        (Finset.univ.filter
          (fun i : Fin e => (K.edgeVerts i).1 = (K.edgeVerts i).2)).image ε := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      refine ⟨ε.symm j, ?_, ε.apply_symm_apply j⟩
      exact (hiff (ε.symm j)).mpr (by simpa [ε.apply_symm_apply] using hj)
    · rintro ⟨i, hi, rfl⟩
      exact (hiff i).mp hi
  rw [himg, Finset.card_image_of_injective _ ε.injective]

theorem selfLoopCount_ge_invariant {v e t : ℕ} {K K' : ExactComplex v e t}
    (h : GlobalEquivalent K K') :
    selfLoopCount K = selfLoopCount K' := by
  obtain ⟨r⟩ := h
  exact selfLoopCount_congr r

/-- Labeled tick: self-loop count mod 8. -/
noncomputable def selfLoopTick : LabeledTick :=
  fun _v _e _t K =>
    ⟨selfLoopCount K % 8, Nat.mod_lt _ (by norm_num : (0 : ℕ) < 8)⟩

theorem selfLoopTick_invariant : GlobalEquivalentInvariant selfLoopTick := by
  intro v e t K K' h
  apply Fin.ext
  change selfLoopCount K % 8 = selfLoopCount K' % 8
  rw [selfLoopCount_ge_invariant h]

/-- Descended class-level tick from self-loop counts. -/
def selfLoopClassTick : ∀ n : ℕ, ExactPathClass n → Fin 8 :=
  descendedTick selfLoopTick selfLoopTick_invariant

def selfLoopPhase : ∀ n : ℕ, ExactPathClass n → ℝ :=
  tickDerivedPhase selfLoopClassTick

/-! ## §3. Witness: self-loop tick is NOT a `ShellSigTick` -/

/-- Two loops at vertex 0, signature `(2,2,0)`. -/
def twoLoopsComplex : ExactComplex 2 2 0 where
  edgeVerts := fun _ => (0, 0)
  tetVerts := fun i => i.elim0

/-- Two parallel non-loop edges `(0,1)`, signature `(2,2,0)`. -/
def twoBridgesComplex : ExactComplex 2 2 0 where
  edgeVerts := fun _ => (0, 1)
  tetVerts := fun i => i.elim0

theorem selfLoopCount_twoLoops : selfLoopCount twoLoopsComplex = 2 := by
  classical
  unfold selfLoopCount twoLoopsComplex
  have h :
      (Finset.univ.filter
        (fun i : Fin 2 =>
          (((fun _ : Fin 2 => ((0 : Fin 2), (0 : Fin 2))) i).1 =
            ((fun _ : Fin 2 => ((0 : Fin 2), (0 : Fin 2))) i).2))) =
        (Finset.univ : Finset (Fin 2)) := by
    ext i
    simp
  rw [h]
  simp

theorem selfLoopCount_twoBridges : selfLoopCount twoBridgesComplex = 0 := by
  classical
  unfold selfLoopCount twoBridgesComplex
  have h :
      (Finset.univ.filter
        (fun i : Fin 2 =>
          (((fun _ : Fin 2 => ((0 : Fin 2), (1 : Fin 2))) i).1 =
            ((fun _ : Fin 2 => ((0 : Fin 2), (1 : Fin 2))) i).2))) =
        (∅ : Finset (Fin 2)) := by
    ext i
    simp
  rw [h]
  simp

theorem not_ge_twoLoops_twoBridges :
    ¬ GlobalEquivalent twoLoopsComplex twoBridgesComplex := by
  intro h
  have := selfLoopCount_ge_invariant h
  rw [selfLoopCount_twoLoops, selfLoopCount_twoBridges] at this
  exact (by decide : ¬ (2 = 0)) this

/-- Shell signature `(2,2,0)`. -/
def doubleEdgeSig : ShellSig 2 :=
  ⟨(⟨2, by norm_num⟩, ⟨2, by norm_num⟩, ⟨0, by norm_num⟩), by
    change max (2 : ℕ) (max 2 0) = 2
    rw [Nat.max_zero, max_self]⟩

def twoLoopsClass : ExactPathClass 2 :=
  ⟨doubleEdgeSig, Quotient.mk _ twoLoopsComplex⟩

def twoBridgesClass : ExactPathClass 2 :=
  ⟨doubleEdgeSig, Quotient.mk _ twoBridgesComplex⟩

theorem selfLoopClassTick_twoLoops :
    selfLoopClassTick 2 twoLoopsClass = ⟨2, by norm_num⟩ := by
  simp only [selfLoopClassTick, twoLoopsClass, descendedTick_mk, selfLoopTick,
    selfLoopCount_twoLoops]

theorem selfLoopClassTick_twoBridges :
    selfLoopClassTick 2 twoBridgesClass = ⟨0, by norm_num⟩ := by
  simp only [selfLoopClassTick, twoBridgesClass, descendedTick_mk, selfLoopTick,
    selfLoopCount_twoBridges]

/-- **THEOREM.** The self-loop tick uses quotient-internal incidence data:
it does not factor through shell signature alone. -/
theorem selfLoopClassTick_not_ShellSigTick :
    ¬ ShellSigTick selfLoopClassTick := by
  rintro ⟨sigma, hσ⟩
  have hL := hσ 2 twoLoopsClass
  have hB := hσ 2 twoBridgesClass
  have hσEq : sigma 2 twoLoopsClass.1 = sigma 2 twoBridgesClass.1 := rfl
  have hne : selfLoopClassTick 2 twoLoopsClass ≠
      selfLoopClassTick 2 twoBridgesClass := by
    rw [selfLoopClassTick_twoLoops, selfLoopClassTick_twoBridges]
    decide
  exact hne (hL.trans (hσEq.trans hB.symm))

/-! ## §4. Bridges toward R5 (do not inhabit R5) -/

/-- Enriched eventual mass balance closes the bare continuum R5 residual
shape. Primary wiring target when a future session inhabits the hyp. -/
theorem oscillatoryTail_of_enriched_eventual_balance
    (lab : LabeledTick) (hInv : GlobalEquivalentInvariant lab)
    (hbal : EventuallyTickFiberMassBalanced (descendedTick lab hInv)) :
    OscillatoryTail (enrichedPhase lab hInv) ∧
      ¬ OscillatoryTail zeroPhase :=
  ⟨eventuallyTickFiberMassBalanced_implies_oscillatoryTail
      (descendedTick lab hInv) hbal,
    zeroPhase_not_oscillatoryTail⟩

/-- Identical-zero amplitudes also close the bare R5 shape. -/
theorem oscillatoryTail_of_enriched_identically_zero
    (lab : LabeledTick) (hInv : GlobalEquivalentInvariant lab)
    (hzero : ∀ n : ℕ, exactShellAmplitude (enrichedPhase lab hInv) n = 0) :
    OscillatoryTail (enrichedPhase lab hInv) ∧
      ¬ OscillatoryTail zeroPhase := by
  refine ⟨?_, zeroPhase_not_oscillatoryTail⟩
  intro ε hε
  refine ⟨0, fun m n _hm _hmn => ?_⟩
  have hamp :
      ∀ k ∈ Finset.Ico m n, exactShellAmplitude (enrichedPhase lab hInv) k = 0 :=
    fun k _ => hzero k
  rw [Finset.sum_eq_zero hamp, norm_zero]
  exact hε

/-! ## §5. Sharper typed residual (credit-bearing C terminal) -/

/-- **Sharpened R5 residual.** A `GlobalEquivalent`-invariant labeled tick
whose descent has `OscillatoryTail` and is not a bare signature coloring.

Strictly stronger than bare
`TypedResidual_continuum_substrate_oscillatoryTail`. Decision
`D-qg-c1-r4-enriched-carrier-20260722` redirects the attack here. -/
def TypedResidual_enriched_carrier_oscillatoryTail : Prop :=
  ∃ (lab : LabeledTick) (hInv : GlobalEquivalentInvariant lab),
    OscillatoryTail (enrichedPhase lab hInv) ∧
      ¬ ShellSigTick (descendedTick lab hInv)

/-- Bare R5 shape (DAG-owned; quoted here for wiring docs only). -/
def TypedResidual_continuum_substrate_oscillatoryTail : Prop :=
  ∃ phase : ∀ n : ℕ, ExactPathClass n → ℝ,
    OscillatoryTail phase ∧ ¬ OscillatoryTail zeroPhase

/-- Enriched residual implies the bare DAG R5 residual. -/
theorem bare_r5_of_enriched_carrier_oscillatoryTail
    (h : TypedResidual_enriched_carrier_oscillatoryTail) :
    TypedResidual_continuum_substrate_oscillatoryTail := by
  obtain ⟨lab, hInv, htail, _⟩ := h
  exact ⟨enrichedPhase lab hInv, htail, zeroPhase_not_oscillatoryTail⟩

/-- Primary close theorem name to wire into the DAG when inhabited. -/
theorem typedResidual_continuum_substrate_oscillatoryTail_of_enriched
    (h : TypedResidual_enriched_carrier_oscillatoryTail) :
    TypedResidual_continuum_substrate_oscillatoryTail :=
  bare_r5_of_enriched_carrier_oscillatoryTail h

/-- Primary close theorem from eventual balance on any enriched tick. -/
theorem typedResidual_continuum_substrate_oscillatoryTail_of_enriched_eventual_balance
    (lab : LabeledTick) (hInv : GlobalEquivalentInvariant lab)
    (hbal : EventuallyTickFiberMassBalanced (descendedTick lab hInv)) :
    TypedResidual_continuum_substrate_oscillatoryTail :=
  ⟨enrichedPhase lab hInv,
    oscillatoryTail_of_enriched_eventual_balance lab hInv hbal⟩

/-- Schema package: enriched API inhabited; analytic tail OPEN. -/
structure EnrichedCarrierPhaseSubstrate where
  lab : LabeledTick
  invariant : GlobalEquivalentInvariant lab
  not_shellSigTick : ¬ ShellSigTick (descendedTick lab invariant)

def selfLoopEnrichedSubstrate : EnrichedCarrierPhaseSubstrate where
  lab := selfLoopTick
  invariant := selfLoopTick_invariant
  not_shellSigTick := selfLoopClassTick_not_ShellSigTick

theorem enrichedCarrierPhaseSubstrate_nonempty :
    Nonempty EnrichedCarrierPhaseSubstrate :=
  ⟨selfLoopEnrichedSubstrate⟩

theorem signatureBlocker_iff_no_shellSig_oscillatoryTail :
    SignatureFin8OscillatoryTailBlocker ↔
      ¬ ∃ tau : ∀ n : ℕ, ExactPathClass n → Fin 8,
          ShellSigTick tau ∧ OscillatoryTail (tickDerivedPhase tau) :=
  Iff.rfl

/-! ## §6. Status (R5 open; gap2 unflipped) -/

structure Gap2EnrichedCarrierPhaseStatus where
  enrichedApiLanded : Bool
  selfLoopWitnessEscapesShellSig : Bool
  r5BridgeLanded : Bool
  enrichedResidualDefinedUninhabited : Bool
  eventualBalanceForWitnessProved : Bool
  signatureBlockerProved : Bool
  bareR5Closed : Bool
  gap2ContinuumAndMeasure : Bool

def gap2EnrichedCarrierPhaseStatus : Gap2EnrichedCarrierPhaseStatus where
  enrichedApiLanded := true
  selfLoopWitnessEscapesShellSig := true
  r5BridgeLanded := true
  enrichedResidualDefinedUninhabited := true
  eventualBalanceForWitnessProved := false
  signatureBlockerProved := false
  bareR5Closed := false
  gap2ContinuumAndMeasure := false

theorem gap2EnrichedCarrierPhaseStatus_flags :
    gap2EnrichedCarrierPhaseStatus.enrichedApiLanded = true ∧
      gap2EnrichedCarrierPhaseStatus.selfLoopWitnessEscapesShellSig = true ∧
      gap2EnrichedCarrierPhaseStatus.r5BridgeLanded = true ∧
      gap2EnrichedCarrierPhaseStatus.enrichedResidualDefinedUninhabited =
        true ∧
      gap2EnrichedCarrierPhaseStatus.eventualBalanceForWitnessProved =
        false ∧
      gap2EnrichedCarrierPhaseStatus.signatureBlockerProved = false ∧
      gap2EnrichedCarrierPhaseStatus.bareR5Closed = false ∧
      gap2EnrichedCarrierPhaseStatus.gap2ContinuumAndMeasure = false := by
  decide

end

end Gap2EnrichedCarrierPhase
end SevenGaps
end Gravity
end IndisputableMonolith
