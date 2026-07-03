import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.MainTheorem

/-!
# Finite Boolean bridge to positive ratios

This module gives a modest discrete-to-continuous bridge: finite Boolean
events with positive weights compare by likelihood ratios, and those ratios
are positive whenever both event weights are positive.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

/-- A finite weighted Boolean reality over `Fin n`. -/
structure FiniteBooleanReality (n : Nat) where
  weight : Fin n → ℝ
  positive_weight : ∀ i, 0 < weight i

namespace FiniteBooleanReality

/-- The weight of an event. -/
noncomputable def eventWeight {n : Nat} (R : FiniteBooleanReality n)
    (event : Fin n → Bool) : ℝ :=
  ∑ i, if event i then R.weight i else 0

/-- A positive witness for an event. -/
def EventNonempty {n : Nat} (event : Fin n → Bool) : Prop :=
  ∃ i, event i = true

/-- Nonempty finite Boolean events have positive weight. -/
theorem eventWeight_pos {n : Nat} (R : FiniteBooleanReality n)
    (event : Fin n → Bool) (hNonempty : EventNonempty event) :
    0 < R.eventWeight event := by
  rcases hNonempty with ⟨i₀, hi₀⟩
  unfold eventWeight
  have h_nonneg : ∀ i : Fin n, 0 ≤ (if event i then R.weight i else 0) := by
    intro i
    by_cases h : event i
    · simp [h, le_of_lt (R.positive_weight i)]
    · simp [h]
  have h_i0_pos : 0 < (if event i₀ then R.weight i₀ else 0) := by
    simp [hi₀, R.positive_weight i₀]
  have h_le_sum :
      (if event i₀ then R.weight i₀ else 0) ≤
        ∑ i, if event i then R.weight i else 0 := by
    exact Finset.single_le_sum (fun i _ => h_nonneg i) (Finset.mem_univ i₀)
  exact lt_of_lt_of_le h_i0_pos h_le_sum

/-- Likelihood ratio of two events. -/
noncomputable def eventRatio {n : Nat} (R : FiniteBooleanReality n)
    (A B : Fin n → Bool) : ℝ :=
  R.eventWeight A / R.eventWeight B

/-- Nonempty event comparisons land in positive ratios. -/
theorem eventRatio_pos {n : Nat} (R : FiniteBooleanReality n)
    (A B : Fin n → Bool)
    (hA : EventNonempty A) (hB : EventNonempty B) :
    0 < R.eventRatio A B := by
  unfold eventRatio
  exact div_pos (eventWeight_pos R A hA) (eventWeight_pos R B hB)

/-- Finite Boolean comparison embeds into the positive-ratio domain whenever
both compared events have positive measure. -/
theorem finite_boolean_logic_embeds_into_positive_ratios {n : Nat}
    (R : FiniteBooleanReality n)
    (A B : Fin n → Bool)
    (hA : EventNonempty A) (hB : EventNonempty B) :
    ∃ r : ℝ, 0 < r ∧ r = R.eventRatio A B :=
  ⟨R.eventRatio A B, eventRatio_pos R A B hA hB, rfl⟩

end FiniteBooleanReality

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith
