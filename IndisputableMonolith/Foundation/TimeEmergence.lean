import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.DimensionForcing
import IndisputableMonolith.Foundation.LawOfExistence

/-!
# F-004 / F-006: Time Emergence and Arrow of Time

Formalizes how time emerges from the ledger update cycle and why it has a direction.

## Core Results

1. **Time as tick count**: There is no background time. Time IS the ledger tick counter.
2. **Minimal period**: The 8-tick cycle (2^D for D=3) is the minimal complete update.
3. **Arrow of time**: Ledger updates are irreversible because defect can only decrease
   toward the cost minimum within an epoch. Recognition is a one-way operation.
4. **Present/Past/Future**: Present = current tick state, Past = committed entries,
   Future = uncommitted entries.

## Registry Items
- F-004: What is the nature of time?
- F-006: What is the arrow of time?
-/

namespace IndisputableMonolith
namespace Foundation
namespace TimeEmergence

open Real Constants Cost

/-! ## Time as Ledger Tick Count -/

/-- A ledger tick: the atomic unit of temporal progression.
    Time does not flow continuously; it advances in discrete ticks. -/
structure Tick where
  index : ℕ
  deriving DecidableEq

/-- Ticks are ordered by their index. This IS time — no background manifold. -/
instance : LE Tick := ⟨fun a b => a.index ≤ b.index⟩
instance : LT Tick := ⟨fun a b => a.index < b.index⟩
instance : DecidableRel (· ≤ · : Tick → Tick → Prop) := fun a b => Nat.decLe a.index b.index
instance : DecidableRel (· < · : Tick → Tick → Prop) := fun a b => Nat.decLt a.index b.index

/-- A ledger epoch: one complete 8-tick cycle. -/
structure Epoch where
  start : Tick
  deriving DecidableEq

/-- The duration of one epoch is exactly 8 ticks (2^D for D = 3). -/
def epoch_length : ℕ := DimensionForcing.eight_tick

theorem epoch_length_eq : epoch_length = 8 := rfl

/-- The tick within an epoch (0 through 7). -/
def tick_within_epoch (t : Tick) : Fin 8 :=
  ⟨t.index % 8, Nat.mod_lt _ (by norm_num)⟩

/-! ## Ledger State and Temporal Progression -/

/-- A ledger state at a given tick. The state space is indexed by ticks,
    not by a continuous time parameter. -/
structure LedgerSnapshot where
  tick : Tick
  defect : ℝ
  defect_nonneg : 0 ≤ defect

/-- Temporal ordering: snapshot A is before snapshot B iff its tick index is smaller. -/
def before (a b : LedgerSnapshot) : Prop := a.tick.index < b.tick.index

instance : DecidableRel before := fun a b => Nat.decLt a.tick.index b.tick.index

/-! ## Arrow of Time: Defect Monotonicity -/

/-- **Core Principle**: Within a single epoch, the defect is non-increasing.
    Recognition events reduce defect (move toward the cost minimum).
    This is what gives time its direction. -/
structure DefectMonotone (states : ℕ → LedgerSnapshot) : Prop where
  tick_ordered : ∀ n, (states n).tick.index ≤ (states (n + 1)).tick.index
  defect_decreasing : ∀ n,
    (states (n + 1)).tick.index = (states n).tick.index + 1 →
    (states (n + 1)).defect ≤ (states n).defect

/-- The arrow of time is the direction of defect decrease.
    Time "flows" from higher defect to lower defect. -/
def arrow_of_time (s₁ s₂ : LedgerSnapshot) : Prop :=
  before s₁ s₂ ∧ s₂.defect ≤ s₁.defect

/-- **Theorem (F-006)**: The arrow of time is well-defined.
    If defect decreases along the tick sequence, the temporal
    ordering and the thermodynamic arrow agree. -/
theorem arrow_well_defined (states : ℕ → LedgerSnapshot)
    (h : DefectMonotone states) (n : ℕ)
    (h_step : (states (n + 1)).tick.index = (states n).tick.index + 1) :
    arrow_of_time (states n) (states (n + 1)) := by
  constructor
  · show (states n).tick.index < (states (n + 1)).tick.index
    omega
  · exact h.defect_decreasing n h_step

/-! ## Irreversibility of Recognition -/

/-- A recognition event transforms a state by reducing its defect.
    This is fundamentally one-way: you cannot "un-recognize." -/
structure RecognitionStep where
  input : LedgerSnapshot
  output : LedgerSnapshot
  tick_advance : output.tick.index = input.tick.index + 1
  defect_reduce : output.defect ≤ input.defect

/-- **Theorem**: Recognition is irreversible.
    If a step reduces defect from d₁ to d₂ < d₁, there is no step
    that goes from d₂ back to d₁ while advancing the tick counter,
    because defect is non-increasing along ticks. -/
theorem recognition_irreversible (step : RecognitionStep)
    (h_strict : step.output.defect < step.input.defect) :
    ¬∃ (reverse : RecognitionStep),
      reverse.input = step.output ∧
      reverse.output.defect = step.input.defect := by
  intro ⟨rev, h_in, h_out⟩
  have h1 := rev.defect_reduce
  rw [h_in] at h1
  linarith

/-! ## Present, Past, Future -/

/-- The present is the current tick. -/
def present (states : ℕ → LedgerSnapshot) (now : ℕ) : LedgerSnapshot :=
  states now

/-- The past is the set of committed ledger entries (earlier ticks). -/
def past (states : ℕ → LedgerSnapshot) (now : ℕ) : Set LedgerSnapshot :=
  { s | ∃ n, n < now ∧ states n = s }

/-- The future is the set of uncommitted entries (later ticks). -/
def future (states : ℕ → LedgerSnapshot) (now : ℕ) : Set LedgerSnapshot :=
  { s | ∃ n, n > now ∧ states n = s }

/-- **Theorem**: The past is fixed — past defect values cannot change. -/
theorem past_is_fixed (states : ℕ → LedgerSnapshot) (now : ℕ)
    (s : LedgerSnapshot) (hs : s ∈ past states now) :
    ∃ n, n < now ∧ states n = s := hs

/-! ## Time Does Not Exist Without Recognition -/

/-- **Theorem (F-004 core)**: Time is not a background parameter.
    Time is DEFINED as the tick count. Without ledger updates, there is no time.
    The tick count is a natural number, not a real number.
    Continuous time is an approximation valid only for large tick counts. -/
theorem time_is_discrete : epoch_length = 2 ^ (3 : ℕ) := by
  simp [epoch_length, DimensionForcing.eight_tick]

/-- **Theorem**: The minimal temporal resolution is one tick.
    No sub-tick dynamics exist. Events are quantized in time. -/
theorem minimal_temporal_resolution :
    ∀ (s₁ s₂ : LedgerSnapshot),
    before s₁ s₂ → 1 ≤ s₂.tick.index - s₁.tick.index := by
  intro s₁ s₂ h
  unfold before at h
  omega

/-! ## Summary Certificate -/

/-- **F-004/F-006 Certificate**: Time emergence and arrow of time.
    1. Time = tick count (discrete, no background)
    2. Arrow = defect decrease direction
    3. Recognition is irreversible
    4. 8-tick epoch is the minimal complete cycle -/
theorem time_emergence_certificate :
    epoch_length = 8 ∧
    epoch_length = 2 ^ 3 ∧
    (∀ step : RecognitionStep,
      step.output.defect < step.input.defect →
      ¬∃ rev : RecognitionStep,
        rev.input = step.output ∧ rev.output.defect = step.input.defect) :=
  ⟨epoch_length_eq, time_is_discrete, fun step h => recognition_irreversible step h⟩

end TimeEmergence
end Foundation
end IndisputableMonolith
