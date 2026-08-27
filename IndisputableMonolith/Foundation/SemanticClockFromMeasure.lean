import Mathlib
import IndisputableMonolith.Foundation.PublicSpine.PartINamedAxiomClosure
import IndisputableMonolith.Foundation.CompletenessFromMeasure
import IndisputableMonolith.Patterns.GrayCycle

/-!
# SemanticClockLaw from the eight-tick measure

Posting-derived predicates do not force Boolean surjection
(`PostingPhase3Wall`). That wall stands.

The eight-tick measure does: a complete walk has period exactly `2^d`,
is bijective onto the cube, and steps by one bit. Gray-8 inhabits that
predicate. The compiled six-cycle has the wrong period. The jump cover
is a surjection that is not one-bit.

That predicate inhabits `SemanticClockLaw`.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace SemanticClockFromMeasure

open Patterns
open PublicSpine
open PublicSpine.PartINamedAxiomClosure
open PublicSpine.ClockDischargeProbe
open PublicSpine.PostingPhase3Wall

/-- Eight-tick measure of a complete pass: Nyquist period, bijection, one-bit. -/
def EightTickComplete {d T : ℕ} (pass : Fin T → Pattern d) : Prop :=
  ∃ _ : NeZero T,
    T = 2 ^ d ∧ Function.Bijective pass ∧
      ∀ i : Fin T, OneBitDiff (pass i) (pass (i + 1))

theorem eightTick_gray8 : EightTickComplete grayCycle3Path :=
  ⟨inferInstance, by decide, grayCycle3_bijective, grayCycle3_oneBit_step⟩

theorem eightTick_forces_surjective
    {d T : ℕ} {pass : Fin T → Pattern d}
    (h : EightTickComplete pass) : Function.Surjective pass := by
  obtain ⟨_, _, hbij, _⟩ := h
  exact hbij.surjective

theorem eightTick_rejects_six :
    ¬ EightTickComplete balancedSixPostingPass := by
  intro h
  obtain ⟨_, hT, _, _⟩ := h
  exact (by decide : ¬ 6 = 8) (hT.trans (by decide : 2 ^ 3 = 8))

theorem eightTick_implies_gray
    {d T : ℕ} {pass : Fin T → Pattern d}
    (h : EightTickComplete pass) : GrayCoverSemanticModel pass := by
  obtain ⟨inst, _, hbij, hbit⟩ := h
  refine ⟨inst, ⟨hbij.surjective, ?_⟩⟩
  haveI := inst
  exact hbit

theorem eightTick_rejects_jump :
    ¬ EightTickComplete jumpCover := by
  intro h
  obtain ⟨inst, _, hbij, hbit⟩ := h
  haveI := inst
  exact jumpCover_not_grayCover ⟨hbij.surjective, hbit⟩

/-- The eight-tick measure inhabits the semantic clock law. -/
def semanticClockLawFromMeasure : SemanticClockLaw where
  completePass := fun {_ _} pass => EightTickComplete pass
  gray8_complete := eightTick_gray8
  forces_surjective := fun {_ _} _pass h => eightTick_forces_surjective h
  six_post_rejected := eightTick_rejects_six
  nonGray_surjection_rejected :=
    ⟨jumpCover_surjective, jumpCover_not_grayCover, eightTick_rejects_jump⟩

def semanticClockLaw_from_eight_tick : SemanticClockLaw :=
  semanticClockLawFromMeasure

theorem semanticClockLaw_from_eight_tick_nonempty : Nonempty SemanticClockLaw :=
  ⟨semanticClockLawFromMeasure⟩

theorem measure_clock_rejects_six :
    ¬ semanticClockLawFromMeasure.completePass balancedSixPostingPass :=
  eightTick_rejects_six

end SemanticClockFromMeasure
end Foundation
end IndisputableMonolith
