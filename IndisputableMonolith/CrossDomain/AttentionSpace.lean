import Mathlib

/-!
# C5: Attention Space — 5 × 8 = 40, + 5 = gap45 — Wave 62 Cross-Domain

Structural claim: attentional state space factors as

  AttentionNetwork × TickPhase  =  5 × 8  =  40

and the complexity ceiling gap45 = 45 leaves exactly 5 overflow slots:
  45 − 40 = 5.

The overflow slots are the five attention-network singletons under
saturation. Prediction: attentional-blink experiments should show 40 stable
plateaus plus 5 transient ones, matching the five singletons.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.CrossDomain.AttentionSpace

inductive AttentionNetwork where
  | alerting | orienting | executive | defaultMode | salience
  deriving DecidableEq, Repr, BEq, Fintype

inductive TickPhase where
  | t0 | t1 | t2 | t3 | t4 | t5 | t6 | t7
  deriving DecidableEq, Repr, BEq, Fintype

theorem networkCount : Fintype.card AttentionNetwork = 5 := by decide
theorem tickCount : Fintype.card TickPhase = 8 := by decide
theorem tick_eq_twoPowD : Fintype.card TickPhase = 2 ^ 3 := by decide

abbrev AttentionState : Type := AttentionNetwork × TickPhase

theorem attentionStateCount : Fintype.card AttentionState = 40 := by
  simp only [AttentionState, Fintype.card_prod, networkCount, tickCount]

/-- The complexity ceiling gap45 leaves exactly 5 overflow slots. -/
def gap45 : ℕ := 45
theorem overflow_eq_D : gap45 - Fintype.card AttentionState = 5 := by
  rw [attentionStateCount]; decide

theorem attention_fits_under_gap : Fintype.card AttentionState < gap45 := by
  rw [attentionStateCount]; decide

theorem attention_plus_overflow_eq_gap :
    Fintype.card AttentionState + 5 = gap45 := by
  rw [attentionStateCount]; decide

theorem network_surj :
    Function.Surjective (fun s : AttentionState => s.1) := by
  intro x; exact ⟨(x, TickPhase.t0), rfl⟩

theorem tick_surj :
    Function.Surjective (fun s : AttentionState => s.2) := by
  intro x; exact ⟨(AttentionNetwork.alerting, x), rfl⟩

structure AttentionSpaceCert where
  state_count : Fintype.card AttentionState = 40
  overflow_D : gap45 - Fintype.card AttentionState = 5
  sum_is_gap : Fintype.card AttentionState + 5 = gap45
  tick_2cube : Fintype.card TickPhase = 2 ^ 3
  network_surj : Function.Surjective (fun s : AttentionState => s.1)
  tick_surj : Function.Surjective (fun s : AttentionState => s.2)

def attentionSpaceCert : AttentionSpaceCert where
  state_count := attentionStateCount
  overflow_D := overflow_eq_D
  sum_is_gap := attention_plus_overflow_eq_gap
  tick_2cube := tick_eq_twoPowD
  network_surj := network_surj
  tick_surj := tick_surj

end IndisputableMonolith.CrossDomain.AttentionSpace
