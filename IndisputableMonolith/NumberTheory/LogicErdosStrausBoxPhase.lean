import Mathlib
import IndisputableMonolith.Foundation.ArithmeticFromLogic
import IndisputableMonolith.NumberTheory.ErdosStrausBoxPhase
import IndisputableMonolith.NumberTheory.LogicErdosStrausRCL

/-!
  LogicErdosStrausBoxPhase.lean

  Logic-native adapter for the Erdős-Straus square-budget box phase.

  The native combinatorial structures are given over `LogicNat`; the final
  theorem transports to the existing `ℕ` box-phase theorem, then returns the
  result as a `LogicRat` representation via `LogicErdosStrausRCL`.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace LogicErdosStrausBoxPhase

open Foundation.ArithmeticFromLogic
open Foundation.ArithmeticFromLogic.LogicNat
open Foundation.RationalsFromLogic.LogicRat
open LogicErdosStrausRCL

/-- Divisibility over recovered naturals. -/
def DvdL (a b : LogicNat) : Prop := ∃ k : LogicNat, b = a * k

/-- A recovered divisor exponent-box point. -/
structure DivisorExponentBoxLogic (N : LogicNat) where
  d : LogicNat
  e : LogicNat
  d_pos : 0 < d
  e_pos : 0 < e
  square_budget : d * e = N * N

def boxDivisorLogic {N : LogicNat} (box : DivisorExponentBoxLogic N) : LogicNat :=
  box.d

def boxComplementLogic {N : LogicNat} (box : DivisorExponentBoxLogic N) : LogicNat :=
  box.e

theorem box_logic_toNat_square_budget {N : LogicNat} (box : DivisorExponentBoxLogic N) :
    toNat box.d * toNat box.e = toNat N ^ 2 := by
  have h := congrArg toNat box.square_budget
  rw [toNat_mul, toNat_mul] at h
  simpa [pow_two] using h

/-- Logic-native box-phase hit, transported to the current classical hit
predicate. This keeps the finite phase proof surface stable while recording
that the carrier is recovered from the Law of Logic. -/
def HitsBalancedPhaseLogic (n c : LogicNat) : Prop :=
  ErdosStrausBoxPhase.HitsBalancedPhase (toNat n) (toNat c)

theorem hitsBalancedPhaseLogic_iff_classical (n c : LogicNat) :
    HitsBalancedPhaseLogic n c ↔
      ErdosStrausBoxPhase.HitsBalancedPhase (toNat n) (toNat c) :=
  Iff.rfl

/-- A recovered box-phase hit gives the logic-native rational
Erdős-Straus representation. -/
theorem box_phase_hit_gives_repr_logic {n c : LogicNat}
    (h : HitsBalancedPhaseLogic n c) :
    HasRationalErdosStrausReprLogic (fromRat (toNat n : ℚ)) := by
  apply reprLogic_fromRat_of_classical
  exact ErdosStrausBoxPhase.box_phase_hit_gives_repr h

end LogicErdosStrausBoxPhase
end NumberTheory
end IndisputableMonolith
