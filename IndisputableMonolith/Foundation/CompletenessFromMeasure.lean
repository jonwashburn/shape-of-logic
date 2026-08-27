import Mathlib
import IndisputableMonolith.Foundation.PublicSpine
import IndisputableMonolith.Foundation.PublicSpine.PostingPhase3Wall

/-!
# Completeness from phase count, not from posting

`PostingPhase3Wall` already proved that no predicate derived from the current
posting class forces Boolean surjection; `balancedSixPostingPass` is the
compiled six-cycle countermodel. That wall stands. This module does not
re-walk it.

A different operational premise does reject the six-cycle: an 8-tick
schedule needs 8 distinct phase states. The image of a 6-cycle has at most
6 points, so it cannot injectively carry `Fin 8`. Independently, any
surjective periodic walk on the 3-cube has period at least 8
(`PublicSpine.cubePeriodEight_holds`), so a 6-periodic walk cannot cover
the cube.

`SemanticClockLaw` remains a named law for posting-derived completeness.
The phase-count principle is a separate THEOREM.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CompletenessFromMeasure

open PublicSpine
open PublicSpine.PostingPhase3Wall
open Patterns

noncomputable instance : Fintype (Set.range balancedSixPostingPass) :=
  (Set.finite_range balancedSixPostingPass).fintype

/-- The six-cycle visits at most 6 parity states. -/
theorem six_cycle_range_card_le_six :
    Fintype.card (Set.range balancedSixPostingPass) ≤ 6 :=
  Fintype.card_range_le balancedSixPostingPass

/-- An 8-tick labeling cannot inject into the six-cycle image. -/
theorem no_injection_eight_ticks_into_six_cycle :
    ¬ ∃ f : Fin 8 → Set.range balancedSixPostingPass, Function.Injective f := by
  intro h
  obtain ⟨f, hf⟩ := h
  have hcard := Fintype.card_le_of_injective f hf
  have h8 : Fintype.card (Fin 8) = 8 := Fintype.card_fin 8
  have : 8 ≤ 6 := by
    rw [h8] at hcard
    exact le_trans hcard six_cycle_range_card_le_six
  exact (by decide : ¬ 8 ≤ 6) this

/-- The existing posting wall: the six-cycle is a legal closed pass and is
not surjective. Cited, not re-proved. -/
theorem posting_six_cycle_is_not_surjective :
    ¬ Function.Surjective balancedSixPostingPass :=
  balancedSixPostingPass_not_surjective

/-- Any 6-periodic walk on the 3-cube fails to cover all 8 corners. -/
theorem six_period_cannot_cover_cube
    (walk : ℕ → (Fin 3 → Bool))
    (hper : ∀ n, walk (n + 6) = walk n) :
    ¬ Function.Surjective walk := by
  intro hsurj
  have h := cubePeriodEight_holds walk 6 (by decide) hper hsurj
  exact (by decide : ¬ 8 ≤ 6) h

/-- The eight-tick pigeonhole bound, re-exported as the phase-count law. -/
theorem eight_tick_surjective_walk_period_ge_eight : CubePeriodEight :=
  cubePeriodEight_holds

/-- The phase-count principle rejects the six-cycle without discharging
`SemanticClockLaw` in the posting layer. -/
theorem phase_count_rejects_six_cycle :
    (¬ Function.Surjective balancedSixPostingPass) ∧
      (¬ ∃ f : Fin 8 → Set.range balancedSixPostingPass, Function.Injective f) :=
  ⟨posting_six_cycle_is_not_surjective, no_injection_eight_ticks_into_six_cycle⟩

end CompletenessFromMeasure
end Foundation
end IndisputableMonolith
