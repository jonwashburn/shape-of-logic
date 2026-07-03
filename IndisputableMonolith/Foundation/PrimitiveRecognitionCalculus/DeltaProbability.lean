/-
  PrimitiveRecognitionCalculus/DeltaProbability.lean

  Delta-native probability.

  Probability is not introduced as a real-valued measure on an arbitrary
  sigma-algebra. The native object here is finite: a finite distinction space,
  events as finite tests, and rational probabilities computed by counting.

  This is the first probability layer needed by Delta-native analysis:

  * `Event N`       : a finite distinction event on `Fin (N+1)`;
  * `prob E`        : the uniform rational probability of `E`;
  * `prob_empty`    : impossible event has probability zero;
  * `prob_univ`     : certain event has probability one;
  * `prob_nonneg`   : finite probabilities are nonnegative;
  * `prob_le_one`   : finite probabilities are bounded by one;
  * `prob_mono`     : finite probabilities are monotone under event inclusion;
  * `prob_disjoint_or`: finite additivity for disjoint events;
  * `expectation`   : finite rational expectation;
  * `delta_probability_headline` : exact finite-counting status.

  No project-local axioms. No sorry.
-/

import Mathlib

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace DeltaProbability

/-- A finite distinction event on the nonempty finite space `Fin (N+1)`. -/
abbrev Event (N : ℕ) := Fin (N + 1) → Prop

/-- Count the points satisfying a finite event. -/
noncomputable def count {N : ℕ} (E : Event N) : ℕ :=
  by
    classical
    exact (Finset.univ.filter fun i : Fin (N + 1) => E i).card

/-- The finite set selected by an event. -/
noncomputable def eventFinset {N : ℕ} (E : Event N) : Finset (Fin (N + 1)) :=
  by
    classical
    exact Finset.univ.filter fun i : Fin (N + 1) => E i

/-- Uniform finite probability, as a rational counting ratio. -/
noncomputable def prob {N : ℕ} (E : Event N) : ℚ :=
  (count E : ℚ) / (N + 1 : ℚ)

theorem count_empty (N : ℕ) : count (N := N) (fun _ => False) = 0 := by
  classical
  simp [count]

theorem count_univ (N : ℕ) : count (N := N) (fun _ => True) = N + 1 := by
  classical
  simp [count]

theorem count_eq_card {N : ℕ} (E : Event N) : count E = (eventFinset E).card := by
  rfl

/-- The impossible event has probability zero. -/
theorem prob_empty (N : ℕ) : prob (N := N) (fun _ => False) = 0 := by
  classical
  simp [prob, count_empty]

/-- The certain event has probability one. -/
theorem prob_univ (N : ℕ) : prob (N := N) (fun _ => True) = 1 := by
  classical
  have h : ((N + 1 : ℚ) ≠ 0) := by positivity
  rw [prob, count_univ]
  rw [show (((N + 1 : ℕ) : ℚ)) = (N + 1 : ℚ) by norm_num]
  exact div_self h

/-- Finite distinction probabilities are nonnegative. -/
theorem prob_nonneg {N : ℕ} (E : Event N) : 0 ≤ prob E := by
  classical
  unfold prob
  positivity

/-- Finite distinction probabilities are bounded by one. -/
theorem prob_le_one {N : ℕ} (E : Event N) : prob E ≤ 1 := by
  classical
  unfold prob count
  have hcard : (Finset.univ.filter fun i : Fin (N + 1) => E i).card ≤ (Finset.univ : Finset (Fin (N + 1))).card :=
    Finset.card_filter_le _ _
  have hcard' : (Finset.univ.filter fun i : Fin (N + 1) => E i).card ≤ N + 1 := by
    simpa using hcard
  have hden : (0 : ℚ) < (N + 1 : ℚ) := by positivity
  have hcast : (((Finset.univ.filter fun i : Fin (N + 1) => E i).card : ℚ) ≤ ((N + 1 : ℕ) : ℚ)) := by
    exact_mod_cast hcard'
  rw [div_le_iff₀ hden]
  simpa using hcast

/-- Event inclusion gives count monotonicity. -/
theorem count_mono {N : ℕ} {E F : Event N} (h : ∀ i, E i → F i) : count E ≤ count F := by
  classical
  unfold count
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact h i hi

/-- Event inclusion gives probability monotonicity. -/
theorem prob_mono {N : ℕ} {E F : Event N} (h : ∀ i, E i → F i) : prob E ≤ prob F := by
  unfold prob
  have hden : (0 : ℚ) < (N + 1 : ℚ) := by positivity
  have hcount : ((count E : ℚ) ≤ (count F : ℚ)) := by
    exact_mod_cast count_mono h
  exact div_le_div_of_nonneg_right hcount (le_of_lt hden)

/-- Disjoint finite events have additive counts. -/
theorem count_disjoint_or {N : ℕ} {E F : Event N}
    (hdisj : ∀ i, ¬ (E i ∧ F i)) :
    count (fun i => E i ∨ F i) = count E + count F := by
  classical
  have hunion : eventFinset (fun i : Fin (N + 1) => E i ∨ F i) = eventFinset E ∪ eventFinset F := by
    ext i
    simp [eventFinset, and_or_left]
  have hdf : Disjoint (eventFinset E) (eventFinset F) := by
    rw [Finset.disjoint_left]
    intro i hiE hiF
    simp [eventFinset] at hiE hiF
    exact hdisj i ⟨hiE, hiF⟩
  rw [count_eq_card, count_eq_card, count_eq_card, hunion]
  exact Finset.card_union_of_disjoint hdf

/-- Disjoint finite events have additive probability. -/
theorem prob_disjoint_or {N : ℕ} {E F : Event N}
    (hdisj : ∀ i, ¬ (E i ∧ F i)) :
    prob (fun i => E i ∨ F i) = prob E + prob F := by
  unfold prob
  rw [count_disjoint_or hdisj]
  rw [Nat.cast_add]
  ring

/-- Finite rational expectation of an observable on a finite distinction space. -/
noncomputable def expectation {N : ℕ} (X : Fin (N + 1) → ℚ) : ℚ :=
  ((Finset.univ.sum X) : ℚ) / (N + 1 : ℚ)

theorem expectation_const {N : ℕ} (c : ℚ) :
    expectation (N := N) (fun _ => c) = c := by
  have h : ((N + 1 : ℚ) ≠ 0) := by positivity
  simp [expectation, Finset.sum_const]
  field_simp [h]

/-- **Delta-native probability headline.** Probability at the native finite layer
is rational counting over finite distinction alternatives: impossible event zero,
certain event one, and every event has probability in `[0,1]`. -/
theorem delta_probability_headline (N : ℕ) :
    prob (N := N) (fun _ => False) = 0
      ∧ prob (N := N) (fun _ => True) = 1
      ∧ (∀ E : Event N, 0 ≤ prob E ∧ prob E ≤ 1)
      ∧ (∀ E F : Event N, (∀ i, E i → F i) → prob E ≤ prob F)
      ∧ (∀ E F : Event N, (∀ i, ¬ (E i ∧ F i)) →
          prob (fun i => E i ∨ F i) = prob E + prob F) :=
  ⟨prob_empty N, prob_univ N, fun E => ⟨prob_nonneg E, prob_le_one E⟩,
    fun _ _ h => prob_mono h, fun _ _ h => prob_disjoint_or h⟩

end DeltaProbability
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
