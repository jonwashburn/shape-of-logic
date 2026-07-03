import IndisputableMonolith.Recognition

/-!
# RRF Core: Recognition (Re-export)

This module re-exports the existing Recognition definitions under the RRF namespace,
providing a bridge between the existing `IndisputableMonolith.Recognition` module
and the new RRF framework.

Key concepts from Recognition.lean:
- `Recognize`: The fundamental pairing of recognizer and recognized
- `MP` (Metaphysical Primitive): Nothing cannot recognize itself
- `RecognitionStructure`: A type with a recognition relation
- `Chain`: A sequence of recognition steps
- `Ledger`: Double-entry bookkeeping for recognition
- `AtomicTick`: Discrete time structure
-/


namespace IndisputableMonolith
namespace RRF.Core

-- Re-export core Recognition types under RRF namespace

/-- Re-export: The fundamental recognition pairing. -/
abbrev Recognize := Recognition.Recognize

/-- Re-export: The metaphysical primitive (MP). -/
abbrev MP := Recognition.MP

/-- Re-export: MP holds. -/
theorem mp_holds : MP := Recognition.mp_holds

/-- Re-export: Nothing cannot recognize itself. -/
abbrev NothingCannotRecognizeItself := Recognition.NothingCannotRecognizeItself

theorem nothing_cannot_recognize_itself : NothingCannotRecognizeItself :=
  Recognition.nothing_cannot_recognize_itself

/-- Re-export: Recognition structure. -/
abbrev RecognitionStructure := Recognition.RecognitionStructure

/-- Re-export: Chain of recognition steps. -/
abbrev Chain := Recognition.Chain

/-- Re-export: Ledger for double-entry. -/
abbrev RecogLedger := Recognition.Ledger

/-- Re-export: Phi (net balance) function. -/
def phi {M : RecognitionStructure} (L : Recognition.Ledger M) : M.U → ℤ :=
  Recognition.phi L

/-- Re-export: Chain flux. -/
def chainFlux {M : RecognitionStructure} (L : Recognition.Ledger M) (ch : Recognition.Chain M) : ℤ :=
  Recognition.chainFlux L ch

/-- Re-export: Atomic tick class. -/
abbrev AtomicTick := Recognition.AtomicTick

/-- Re-export: Atomicity theorem (T2). -/
theorem T2_atomicity {M : RecognitionStructure} [Recognition.AtomicTick M] :
    ∀ t u v, Recognition.AtomicTick.postedAt (M:=M) t u → Recognition.AtomicTick.postedAt (M:=M) t v → u = v :=
  Recognition.T2_atomicity

/-- The bridge theorem: chainFlux is zero for balanced ledgers. -/
theorem chainFlux_zero_of_balanced {M : RecognitionStructure} (L : Recognition.Ledger M)
    (ch : Recognition.Chain M) (hbal : ∀ u, L.debit u = L.credit u) :
    Recognition.chainFlux L ch = 0 :=
  Recognition.chainFlux_zero_of_balanced L ch hbal

end RRF.Core
end IndisputableMonolith
