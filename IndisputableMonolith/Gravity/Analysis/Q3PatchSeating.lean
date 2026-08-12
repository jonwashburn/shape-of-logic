import Mathlib
import IndisputableMonolith.Patterns

/-!
# Canonical three-cube × record-time seating into the Fin 16 patch

Frozen world G1 of
`holography/plans/OrderSensitive_Gravity_Proposition_20260802.html`.

Packs Pattern 3 axes into patch bits 0,1,2 and record-time into bit 3.
Does not import the heavy gravity analysis chain.

## Honesty

* THEOREM: bijectivity and the time-bit involution.
* MODEL: treating the fourth bit as record time.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace Q3PatchSeating

open IndisputableMonolith.Patterns

@[simp] def bitNat : Bool → ℕ
  | true => 1
  | false => 0

theorem bitNat_le_one (b : Bool) : bitNat b ≤ 1 := by
  cases b <;> simp [bitNat]

def seatNat (p : Pattern 3) (t : Bool) : ℕ :=
  bitNat (p 0) + 2 * bitNat (p 1) + 4 * bitNat (p 2) + 8 * bitNat t

theorem seatNat_lt (p : Pattern 3) (t : Bool) : seatNat p t < 16 := by
  have h0 := bitNat_le_one (p 0)
  have h1 := bitNat_le_one (p 1)
  have h2 := bitNat_le_one (p 2)
  have ht := bitNat_le_one t
  unfold seatNat
  omega

def seat (p : Pattern 3) (t : Bool) : Fin 16 :=
  ⟨seatNat p t, seatNat_lt p t⟩

def unseat (v : Fin 16) : Pattern 3 × Bool :=
  (fun
    | 0 => v.val.testBit 0
    | 1 => v.val.testBit 1
    | 2 => v.val.testBit 2,
   v.val.testBit 3)

def flipTime (v : Fin 16) : Fin 16 :=
  ⟨v.val ^^^ 8, by
    have := v.isLt
    interval_cases v.val <;> decide⟩

theorem seat_unseat (v : Fin 16) :
    seat (unseat v).1 (unseat v).2 = v := by
  apply Fin.ext
  fin_cases v <;> rfl

/-- Packing four bits into a Nat recovers them by `testBit`. -/
private theorem pack4_testBit (b0 b1 b2 b3 : Bool) :
    let n := bitNat b0 + 2 * bitNat b1 + 4 * bitNat b2 + 8 * bitNat b3
    n.testBit 0 = b0 ∧ n.testBit 1 = b1 ∧ n.testBit 2 = b2 ∧ n.testBit 3 = b3 := by
  revert b0 b1 b2 b3
  decide

theorem unseat_seat (p : Pattern 3) (t : Bool) :
    unseat (seat p t) = (p, t) := by
  have h := pack4_testBit (p 0) (p 1) (p 2) t
  refine Prod.ext ?_ ?_
  · funext i
    fin_cases i
    · simpa [unseat, seat, seatNat] using h.1
    · simpa [unseat, seat, seatNat] using h.2.1
    · simpa [unseat, seat, seatNat] using h.2.2.1
  · simpa [unseat, seat, seatNat] using h.2.2.2

theorem seat_injective (p₁ p₂ : Pattern 3) (t₁ t₂ : Bool)
    (h : seat p₁ t₁ = seat p₂ t₂) : p₁ = p₂ ∧ t₁ = t₂ := by
  have := congrArg unseat h
  simpa [unseat_seat] using this

theorem seat_surjective (v : Fin 16) :
    ∃ (p : Pattern 3) (t : Bool), seat p t = v :=
  ⟨(unseat v).1, (unseat v).2, seat_unseat v⟩

theorem seat_bijective :
    Function.Bijective (fun pt : Pattern 3 × Bool => seat pt.1 pt.2) := by
  refine ⟨?_, ?_⟩
  · intro ⟨p₁, t₁⟩ ⟨p₂, t₂⟩ h
    have := seat_injective p₁ p₂ t₁ t₂ h
    exact Prod.ext this.1 this.2
  · intro v
    exact ⟨⟨(unseat v).1, (unseat v).2⟩, seat_unseat v⟩

private theorem xor8_lt_eight {n : ℕ} (hn : n < 8) : n ^^^ 8 = n + 8 := by
  interval_cases n <;> decide

private theorem xor8_add_eight {n : ℕ} (hn : n < 8) : (n + 8) ^^^ 8 = n := by
  interval_cases n <;> decide

theorem seat_flipTime (p : Pattern 3) (t : Bool) :
    seat p (!t) = flipTime (seat p t) := by
  apply Fin.ext
  have ha : bitNat (p 0) + 2 * bitNat (p 1) + 4 * bitNat (p 2) < 8 := by
    have h0 := bitNat_le_one (p 0)
    have h1 := bitNat_le_one (p 1)
    have h2 := bitNat_le_one (p 2)
    omega
  cases t
  · -- t = false, !t = true
    simp only [seat, flipTime, seatNat, bitNat, Bool.not_false]
    exact (xor8_lt_eight ha).symm
  · simp only [seat, flipTime, seatNat, bitNat, Bool.not_true]
    -- LHS: a + 0, RHS: (a + 8) ^^^ 8
    simpa [Nat.add_assoc] using (xor8_add_eight ha).symm

theorem flipTime_involutive (v : Fin 16) : flipTime (flipTime v) = v := by
  apply Fin.ext
  change (v.val ^^^ 8) ^^^ 8 = v.val
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem timeSlice_is_patch_symmetry :
    (∀ v, flipTime (flipTime v) = v) ∧
      (∀ p t, seat p (!t) = flipTime (seat p t)) :=
  ⟨flipTime_involutive, seat_flipTime⟩

end Q3PatchSeating
end Analysis
end Gravity
end IndisputableMonolith
