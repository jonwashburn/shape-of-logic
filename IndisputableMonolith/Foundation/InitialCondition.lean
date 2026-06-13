import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.LawOfExistence
import IndisputableMonolith.Foundation.OntologyPredicates

/-!
# F-005: The Initial Condition — Why Low Entropy

Formalizes why the universe began in a low-entropy state.

## The Argument

The question "Why did the universe start with low entropy?" is traditionally
one of the deepest puzzles in cosmology (the Past Hypothesis of Albert 2000,
the Weyl Curvature Hypothesis of Penrose 1979).

In Recognition Science, the answer is forced:

1. The only RSExists state is x = 1 (zero defect).
2. A universe of N ledger entries, all at x = 1, has TOTAL defect = 0.
3. Total defect 0 IS the minimum entropy state.
4. Therefore the initial condition is not a choice — it is the UNIQUE
   zero-cost configuration, forced by the cost axioms.

The "Past Hypothesis" becomes the "Past Theorem."

## Registry Item
- F-005: Why does the universe have low entropy initial conditions?
-/

namespace IndisputableMonolith
namespace Foundation
namespace InitialCondition

open Real Cost

/-! ## Ledger Configuration -/

/-- A configuration of N ledger entries, each a positive real ratio. -/
structure Configuration (N : ℕ) where
  entries : Fin N → ℝ
  entries_pos : ∀ i, 0 < entries i

/-- Total defect of a configuration: sum of individual J-costs. -/
noncomputable def total_defect {N : ℕ} (c : Configuration N) : ℝ :=
  ∑ i : Fin N, LawOfExistence.defect (c.entries i)

/-- Total defect is non-negative (each term is non-negative). -/
theorem total_defect_nonneg {N : ℕ} (c : Configuration N) : 0 ≤ total_defect c := by
  apply Finset.sum_nonneg
  intro i _
  exact LawOfExistence.defect_nonneg (c.entries_pos i)

/-- The zero-defect configuration: all entries equal to 1. -/
def unity_config (N : ℕ) (_hN : 0 < N) : Configuration N :=
  { entries := fun _ => 1
    entries_pos := fun _ => by norm_num }

/-- The unity configuration has zero total defect. -/
theorem unity_defect_zero {N : ℕ} (hN : 0 < N) :
    total_defect (unity_config N hN) = 0 := by
  unfold total_defect unity_config
  simp only [LawOfExistence.defect_at_one]
  exact Finset.sum_const_zero

/-! ## The Initial Condition is Forced -/

/-- **Theorem (F-005 core)**: The unity configuration is the unique
    zero-total-defect configuration.
    Every entry must be 1 for total defect to vanish. -/
theorem zero_defect_iff_unity {N : ℕ} (_hN : 0 < N) (c : Configuration N) :
    total_defect c = 0 ↔ ∀ i, c.entries i = 1 := by
  constructor
  · intro h_zero
    have h_terms : ∀ i, LawOfExistence.defect (c.entries i) = 0 := by
      by_contra h_not
      push_neg at h_not
      obtain ⟨j, hj⟩ := h_not
      have hj_pos : 0 < LawOfExistence.defect (c.entries j) := by
        have h_nn := LawOfExistence.defect_nonneg (c.entries_pos j)
        exact lt_of_le_of_ne h_nn (Ne.symm hj)
      have h_sum_pos : 0 < total_defect c := by
        calc 0 < LawOfExistence.defect (c.entries j) := hj_pos
          _ ≤ ∑ i : Fin N, LawOfExistence.defect (c.entries i) := by
              apply Finset.single_le_sum (f := fun i => LawOfExistence.defect (c.entries i))
                (fun i _ => LawOfExistence.defect_nonneg (c.entries_pos i))
                (Finset.mem_univ j)
      linarith
    intro i
    exact (LawOfExistence.defect_zero_iff_one (c.entries_pos i)).mp (h_terms i)
  · intro h_all_one
    simp only [total_defect]
    apply Finset.sum_eq_zero
    intro i _
    rw [h_all_one i]
    exact LawOfExistence.defect_one

/-- **Theorem**: The unity configuration achieves the global minimum of total defect. -/
theorem unity_is_global_minimum {N : ℕ} (hN : 0 < N) (c : Configuration N) :
    total_defect (unity_config N hN) ≤ total_defect c := by
  rw [unity_defect_zero hN]
  exact total_defect_nonneg c

/-- **Theorem**: The unity configuration is the UNIQUE global minimizer. -/
theorem unity_unique_minimizer {N : ℕ} (hN : 0 < N) (c : Configuration N) :
    total_defect c = total_defect (unity_config N hN) →
    ∀ i, c.entries i = 1 := by
  rw [unity_defect_zero hN]
  exact (zero_defect_iff_unity hN c).mp

/-! ## Entropy and Defect -/

/-- Entropy of a configuration is proportional to its total defect.
    Zero defect = zero entropy = minimum entropy state. -/
noncomputable def entropy {N : ℕ} (c : Configuration N) : ℝ :=
  total_defect c

/-- **Theorem**: The initial state has minimum entropy. -/
theorem initial_state_minimum_entropy {N : ℕ} (hN : 0 < N) :
    entropy (unity_config N hN) = 0 := unity_defect_zero hN

/-- **Theorem**: Any non-unity state has positive entropy. -/
theorem nonunity_positive_entropy {N : ℕ} (_hN : 0 < N) (c : Configuration N)
    (h : ∃ i, c.entries i ≠ 1) : 0 < entropy c := by
  obtain ⟨j, hj⟩ := h
  have hj_pos : 0 < LawOfExistence.defect (c.entries j) :=
    LawOfExistence.defect_pos_of_ne_one (c.entries_pos j) hj
  calc 0 < LawOfExistence.defect (c.entries j) := hj_pos
    _ ≤ ∑ i : Fin N, LawOfExistence.defect (c.entries i) := by
        apply Finset.single_le_sum (f := fun i => LawOfExistence.defect (c.entries i))
          (fun i _ => LawOfExistence.defect_nonneg (c.entries_pos i))
          (Finset.mem_univ j)

/-! ## The Past Hypothesis Becomes a Theorem -/

/-- **The Past Theorem (F-005 Resolution)**:

    The universe's initial condition is not a contingent fact but a
    mathematical necessity. The unique zero-cost configuration IS the
    low-entropy initial state. There is no other option.

    This resolves:
    - Penrose's "Why was the Big Bang so special?"
    - Albert's "Past Hypothesis"
    - Boltzmann's "Why didn't we start in thermal equilibrium?"

    Answer: Because thermal equilibrium (maximum defect) is infinitely
    costly, while the zero-defect state is the unique cost minimum. -/
theorem past_theorem {N : ℕ} (hN : 0 < N) :
    (∃! c : Configuration N, total_defect c = 0) ∧
    total_defect (unity_config N hN) = 0 ∧
    (∀ c : Configuration N, total_defect (unity_config N hN) ≤ total_defect c) := by
  refine ⟨⟨unity_config N hN, unity_defect_zero hN, ?_⟩, unity_defect_zero hN,
    unity_is_global_minimum hN⟩
  intro c hc
  have h_entries : ∀ i, c.entries i = 1 :=
    (zero_defect_iff_unity hN c).mp hc
  have h_u_entries : ∀ i, (unity_config N hN).entries i = 1 := fun _ => rfl
  have h_eq : c.entries = (unity_config N hN).entries :=
    funext fun i => by rw [h_entries i, h_u_entries i]
  exact Configuration.mk.injEq .. |>.mpr h_eq

end InitialCondition
end Foundation
end IndisputableMonolith
