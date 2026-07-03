import Mathlib

/-!
# Sync Period Minimization: Why 45 Is Uniquely Selected

This module formalizes **constraint (S)** from the Dimensional Rigidity paper
(Washburn/Zlatanović/Allahyarov, 2026): among odd spatial dimensions D ≥ 3,
D = 3 uniquely minimizes the synchronization period `lcm(2^D, T(D²))`.

## The Argument

For dimension D:
- The 8-tick period generalizes to `2^D`
- The parity matrix of the hypercube Q_D has `D²` entries
- Cumulative phase = `T(D²)` (triangular number)
- Sync period = `lcm(2^D, T(D²))`

For **even D**, `T(D²)` is even, so `gcd(2^D, T(D²)) > 1` — the periods
partially align, reducing the uncomputability barrier. Only **odd D** gives
full coprimality (T(D²) is odd when D is odd).

Among odd D ≥ 3:
- D = 3: T(9)  = 45,   sync = lcm(8,   45)   = 360
- D = 5: T(25) = 325,  sync = lcm(32,  325)  = 10400
- D = 7: T(49) = 1225, sync = lcm(128, 1225) = 156800

D = 3 gives the **minimal** sync period, uniquely. This is WHY 45 is selected:
it is T(D²) at the dimension that minimizes synchronization cost.
-/

namespace IndisputableMonolith
namespace Gap45
namespace SyncMinimization

/-! ## Triangular Numbers -/

/-- The n-th triangular number: T(n) = n(n+1)/2. -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

@[simp] theorem T_0 : T 0 = 0 := rfl
@[simp] theorem T_1 : T 1 = 1 := rfl
@[simp] theorem T_9 : T 9 = 45 := by native_decide
@[simp] theorem T_25 : T 25 = 325 := by native_decide
@[simp] theorem T_49 : T 49 = 1225 := by native_decide
@[simp] theorem T_81 : T 81 = 3321 := by native_decide
@[simp] theorem T_121 : T 121 = 7381 := by native_decide
@[simp] theorem T_4 : T 4 = 10 := by native_decide
@[simp] theorem T_16 : T 16 = 136 := by native_decide

/-! ## Parity of T(D²) -/

/-- T(D²) for a given dimension. -/
def phasePeriod (D : ℕ) : ℕ := T (D * D)

@[simp] theorem phasePeriod_3 : phasePeriod 3 = 45 := by native_decide
@[simp] theorem phasePeriod_5 : phasePeriod 5 = 325 := by native_decide
@[simp] theorem phasePeriod_7 : phasePeriod 7 = 1225 := by native_decide
@[simp] theorem phasePeriod_9 : phasePeriod 9 = 3321 := by native_decide
@[simp] theorem phasePeriod_11 : phasePeriod 11 = 7381 := by native_decide

/-- For even D, T(D²) is even: no coprimality with 2^D. Verified for D ∈ {2,4,6,8,10}. -/
theorem phasePeriod_even_2 : 2 ∣ phasePeriod 2 := by native_decide
theorem phasePeriod_even_4 : 2 ∣ phasePeriod 4 := by native_decide
theorem phasePeriod_even_6 : 2 ∣ phasePeriod 6 := by native_decide
theorem phasePeriod_even_8 : 2 ∣ phasePeriod 8 := by native_decide
theorem phasePeriod_even_10 : 2 ∣ phasePeriod 10 := by native_decide

/-- For odd D, T(D²) is odd. -/
theorem phasePeriod_odd_3 : ¬ 2 ∣ phasePeriod 3 := by native_decide
theorem phasePeriod_odd_5 : ¬ 2 ∣ phasePeriod 5 := by native_decide
theorem phasePeriod_odd_7 : ¬ 2 ∣ phasePeriod 7 := by native_decide
theorem phasePeriod_odd_9 : ¬ 2 ∣ phasePeriod 9 := by native_decide
theorem phasePeriod_odd_11 : ¬ 2 ∣ phasePeriod 11 := by native_decide

/-! ## Coprimality with 2^D -/

theorem coprime_3 : Nat.Coprime (2^3) (phasePeriod 3) := by native_decide
theorem coprime_5 : Nat.Coprime (2^5) (phasePeriod 5) := by native_decide
theorem coprime_7 : Nat.Coprime (2^7) (phasePeriod 7) := by native_decide
theorem coprime_9 : Nat.Coprime (2^9) (phasePeriod 9) := by native_decide
theorem coprime_11 : Nat.Coprime (2^11) (phasePeriod 11) := by native_decide

/-! ## Sync Periods -/

/-- The synchronization period for dimension D. -/
def syncPeriod (D : ℕ) : ℕ := Nat.lcm (2^D) (phasePeriod D)

@[simp] theorem syncPeriod_3 : syncPeriod 3 = 360 := by native_decide
@[simp] theorem syncPeriod_5 : syncPeriod 5 = 10400 := by native_decide
@[simp] theorem syncPeriod_7 : syncPeriod 7 = 156800 := by native_decide
@[simp] theorem syncPeriod_9 : syncPeriod 9 = 1700352 := by native_decide
@[simp] theorem syncPeriod_11 : syncPeriod 11 = 15116288 := by native_decide

/-! ## The Minimization Theorem (Constraint S) -/

/-- D = 3 has strictly smaller sync period than D = 5. -/
theorem sync_3_lt_5 : syncPeriod 3 < syncPeriod 5 := by native_decide

/-- D = 3 has strictly smaller sync period than D = 7. -/
theorem sync_3_lt_7 : syncPeriod 3 < syncPeriod 7 := by native_decide

/-- D = 3 has strictly smaller sync period than D = 9. -/
theorem sync_3_lt_9 : syncPeriod 3 < syncPeriod 9 := by native_decide

/-- D = 3 has strictly smaller sync period than D = 11. -/
theorem sync_3_lt_11 : syncPeriod 3 < syncPeriod 11 := by native_decide

/-- **CONSTRAINT (S)**: Among odd dimensions D ∈ {3,5,7,9,11},
    D = 3 uniquely minimizes the synchronization period lcm(2^D, T(D²)).

    This is the formalization of constraint (S) from the Dimensional Rigidity
    paper (Washburn/Zlatanović/Allahyarov 2026). It answers:
    "Why 45 specifically?" — because 45 = T(9) = T(3²) is the phase period
    at the dimension that minimizes synchronization cost.

    The sync periods grow super-exponentially:
    - D=3:  360
    - D=5:  10400      (28.9× larger)
    - D=7:  156800     (435.6× larger)
    - D=9:  1700352    (4723.2× larger)
    - D=11: 15116288   (41989.7× larger) -/
theorem constraint_S_minimization :
    ∀ D ∈ ({5, 7, 9, 11} : Finset ℕ), syncPeriod 3 < syncPeriod D := by
  intro D hD
  fin_cases hD <;> native_decide

/-- D = 3 is the unique minimizer: for all odd D with 3 ≤ D ≤ 11 and D ≠ 3,
    the sync period at D strictly exceeds that at D = 3. -/
theorem D3_unique_minimizer :
    ∀ D : ℕ, D % 2 = 1 → 3 ≤ D → D ≤ 11 → D ≠ 3 →
    syncPeriod 3 < syncPeriod D := by
  intro D hodd hge hle hne
  interval_cases D <;> simp_all [syncPeriod, phasePeriod, T] <;> native_decide

/-- Even dimensions fail coprimality: 2 | T(D²) when 2 | D, so the
    uncomputability barrier is weakened. Verified for D ∈ {2,4,6,8,10}. -/
theorem even_D_not_coprime :
    ∀ D ∈ ({2, 4, 6, 8, 10} : Finset ℕ),
    ¬ Nat.Coprime (2^D) (phasePeriod D) := by
  intro D hD
  fin_cases hD <;> native_decide

/-! ## Monotonicity (sync period grows with D for odd D) -/

/-- The sync period is strictly increasing along odd dimensions. -/
theorem sync_strictly_increasing_odd :
    syncPeriod 3 < syncPeriod 5 ∧
    syncPeriod 5 < syncPeriod 7 ∧
    syncPeriod 7 < syncPeriod 9 ∧
    syncPeriod 9 < syncPeriod 11 := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-! ## Complete Certificate -/

/-- The full constraint (S) certificate packaging the dimensional selection of 45. -/
structure ConstraintS_Cert where
  phase_at_D3 : phasePeriod 3 = 45
  sync_at_D3 : syncPeriod 3 = 360
  coprime_at_D3 : Nat.Coprime (2^3) (phasePeriod 3)
  even_D_fails : ∀ D ∈ ({2, 4, 6, 8, 10} : Finset ℕ),
    ¬ Nat.Coprime (2^D) (phasePeriod D)
  D3_minimizes : ∀ D : ℕ, D % 2 = 1 → 3 ≤ D → D ≤ 11 → D ≠ 3 →
    syncPeriod 3 < syncPeriod D
  monotone_odd : syncPeriod 3 < syncPeriod 5 ∧
    syncPeriod 5 < syncPeriod 7 ∧
    syncPeriod 7 < syncPeriod 9 ∧
    syncPeriod 9 < syncPeriod 11

/-- The verified constraint (S) certificate. -/
def constraintS : ConstraintS_Cert where
  phase_at_D3 := by native_decide
  sync_at_D3 := by native_decide
  coprime_at_D3 := by native_decide
  even_D_fails := even_D_not_coprime
  D3_minimizes := D3_unique_minimizer
  monotone_odd := sync_strictly_increasing_odd

end SyncMinimization
end Gap45
end IndisputableMonolith
