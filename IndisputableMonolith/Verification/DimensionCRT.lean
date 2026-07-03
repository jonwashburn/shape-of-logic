import Mathlib
import IndisputableMonolith.RecogSpec.Bands

/-(
Dimension forcing via CRT logic (8↔45 hinge)

Reframe: the minimal period 2^D co‑synchronizes with the 45‑fold structure
only at 360. Conclude the only D with lcm(2^D, 45) = 360 (respecting atomic
ledger periods) is D = 3.
)-/

namespace IndisputableMonolith
namespace Verification
namespace DimensionCRT

open Nat

/-- Synchronization period used in dimensional rigidity arithmetic: `S(D) = lcm(2^D,45)`. -/
def syncPeriod (D : ℕ) : ℕ := Nat.lcm (2 ^ D) 45

/-- Closed form of the synchronization period: since `45` is odd, `gcd(2^D,45)=1`. -/
theorem syncPeriod_eq_mul (D : ℕ) : syncPeriod D = (2 ^ D) * 45 := by
  unfold syncPeriod
  have h2 : Nat.Coprime 2 45 := by decide
  have h : Nat.Coprime (2 ^ D) 45 := h2.pow_left D
  simpa using h.lcm_eq_mul

/-- Unique minimization statement for synchronization:
among all `D ≥ 3`, `S(D)` is minimized at `D = 3`. -/
theorem syncPeriod_minimized_at_three {D : ℕ} (hD : 3 ≤ D) :
    syncPeriod 3 ≤ syncPeriod D ∧ (syncPeriod D = syncPeriod 3 → D = 3) := by
  constructor
  · have h3 : syncPeriod 3 = (2 ^ 3) * 45 := syncPeriod_eq_mul 3
    have hD' : syncPeriod D = (2 ^ D) * 45 := syncPeriod_eq_mul D
    rcases Nat.exists_eq_add_of_le hD with ⟨k, rfl⟩
    have hk : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    have hpow : 2 ^ 3 ≤ 2 ^ (3 + k) := by
      calc
        2 ^ 3 = 2 ^ 3 * 1 := by ring
        _ ≤ 2 ^ 3 * 2 ^ k := Nat.mul_le_mul_left (2 ^ 3) hk
        _ = 2 ^ (3 + k) := by simp [Nat.pow_add]
    have hmul : (2 ^ 3) * 45 ≤ (2 ^ (3 + k)) * 45 := by
      have : 45 * (2 ^ 3) ≤ 45 * (2 ^ (3 + k)) := Nat.mul_le_mul_left 45 hpow
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    simpa [h3, hD', Nat.add_assoc] using hmul
  · intro heq
    rcases Nat.exists_eq_add_of_le hD with ⟨k, rfl⟩
    cases k with
    | zero =>
        simp
    | succ k =>
        have hlt : 3 < 3 + Nat.succ k := Nat.lt_add_of_pos_right (Nat.succ_pos _)
        have hpowlt : 2 ^ 3 < 2 ^ (3 + Nat.succ k) :=
          Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hlt
        have h3 : syncPeriod 3 = (2 ^ 3) * 45 := syncPeriod_eq_mul 3
        have hD' : syncPeriod (3 + Nat.succ k) = (2 ^ (3 + Nat.succ k)) * 45 :=
          syncPeriod_eq_mul (3 + Nat.succ k)
        have hmul : syncPeriod 3 < syncPeriod (3 + Nat.succ k) := by
          have : 45 * (2 ^ 3) < 45 * (2 ^ (3 + Nat.succ k)) :=
            (Nat.mul_lt_mul_left (by decide : 0 < 45)).2 hpowlt
          have : (2 ^ 3) * 45 < (2 ^ (3 + Nat.succ k)) * 45 := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
          simpa [h3, hD'] using this
        exfalso
        exact (Nat.ne_of_lt hmul) (heq.symm)

/-- Numeric witness for the synchronization minimum. -/
theorem syncPeriod_3_eq_360 : syncPeriod 3 = 360 := by
  native_decide

/-- Chinese‑remainder style dimension forcing: only D=3 satisfies
    lcm(2^D, 45) = 360. This packages the 8↔45 hinge as an arithmetic lemma. -/
theorem lcm_pow2_45_forces_D3 (D : ℕ)
    (h : Nat.lcm (2 ^ D) 45 = 360) : D = 3 := by
  -- Reuse the canonical equivalence provided by the RS stack.
  exact (IndisputableMonolith.RecogSpec.lcm_pow2_45_eq_iff D).mp h

/-- Equivalence form convenient for automation. -/
theorem lcm_pow2_45_eq_360_iff (D : ℕ) :
    Nat.lcm (2 ^ D) 45 = 360 ↔ D = 3 :=
  IndisputableMonolith.RecogSpec.lcm_pow2_45_eq_iff D

end DimensionCRT
end Verification
end IndisputableMonolith
