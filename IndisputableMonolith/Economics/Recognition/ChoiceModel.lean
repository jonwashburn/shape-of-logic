import IndisputableMonolith.Economics.Recognition.RecognitionUtility

/-!
# Finite Distinction Choice Model

The native choice functional is finite: expected payoff over admitted
distinguishable alternatives minus the cost of the distinctions required by the
action. The expectation is the δ-native rational average from
`DeltaProbability`.
-/

namespace IndisputableMonolith
namespace Economics
namespace Recognition

noncomputable section

/-- A finite action evaluated on a finite distinction space. -/
structure FiniteAction (N : ℕ) where
  payoff : Fin (N + 1) → ℚ
  distinctionCost : ℚ

/-- Recognition choice value: δ-expectation of payoff minus distinction cost. -/
def choiceValue {N : ℕ} (a : FiniteAction N) : ℚ :=
  deltaExpectation a.payoff - a.distinctionCost

/-- An action is optimal in a finite action menu when it maximizes recognition
choice value over that menu. -/
def IsChoiceMaximizer {N : ℕ} (menu : Finset (FiniteAction N)) (a : FiniteAction N) : Prop :=
  a ∈ menu ∧ ∀ b ∈ menu, choiceValue b ≤ choiceValue a

/-- Expected-utility maximizer over a finite δ-native menu. -/
def ExpectedUtilityMaximizer {N : ℕ} (menu : Finset (FiniteAction N)) (a : FiniteAction N) :
    Prop :=
  a ∈ menu ∧ ∀ b ∈ menu, deltaExpectation b.payoff ≤ deltaExpectation a.payoff

/-- The whole menu has zero distinction cost. -/
def ZeroDistinctionMenu {N : ℕ} (menu : Finset (FiniteAction N)) : Prop :=
  ∀ a ∈ menu, a.distinctionCost = 0

/-- With zero distinction cost, recognition choice value reduces to δ-expected
payoff. This is the finite expected-utility limit at the native layer. -/
theorem choiceValue_zero_distinction_cost {N : ℕ} (payoff : Fin (N + 1) → ℚ) :
    choiceValue ({ payoff := payoff, distinctionCost := 0 } : FiniteAction N)
      = deltaExpectation payoff := by
  unfold choiceValue
  simp

/-- Constant-payoff actions evaluate to payoff minus distinction cost. -/
theorem choiceValue_const_payoff {N : ℕ} (c k : ℚ) :
    choiceValue ({ payoff := fun _ => c, distinctionCost := k } : FiniteAction N)
      = c - k := by
  unfold choiceValue deltaExpectation
  rw [IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaProbability.expectation_const]

/-- Adding the same distinction cost to two actions preserves their value order
exactly when the underlying δ-expected payoff order holds. -/
theorem common_distinction_cost_order {N : ℕ}
    (p q : Fin (N + 1) → ℚ) (k : ℚ) :
    choiceValue ({ payoff := p, distinctionCost := k } : FiniteAction N)
      ≤ choiceValue ({ payoff := q, distinctionCost := k } : FiniteAction N)
      ↔ deltaExpectation p ≤ deltaExpectation q := by
  unfold choiceValue
  constructor <;> intro h <;> linarith

/-- Expected utility is the zero-distinction-cost limit of recognition choice. -/
theorem eu_limit {N : ℕ} (menu : Finset (FiniteAction N)) (a : FiniteAction N)
    (hzero : ZeroDistinctionMenu menu) :
    IsChoiceMaximizer menu a ↔ ExpectedUtilityMaximizer menu a := by
  unfold IsChoiceMaximizer ExpectedUtilityMaximizer ZeroDistinctionMenu choiceValue at *
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro b hb
    have hb0 : b.distinctionCost = 0 := hzero b hb
    have ha0 : a.distinctionCost = 0 := hzero a h.1
    have horder := h.2 b hb
    rw [hb0, ha0] at horder
    simpa using horder
  · intro h
    refine ⟨h.1, ?_⟩
    intro b hb
    have hb0 : b.distinctionCost = 0 := hzero b hb
    have ha0 : a.distinctionCost = 0 := hzero a h.1
    have horder := h.2 b hb
    rw [hb0, ha0]
    simpa using horder

/-- A coarse-partition action is the same finite payoff object with its
information/distinction cost made explicit. -/
structure CoarsePartitionAction (N : ℕ) where
  payoff : Fin (N + 1) → ℚ
  informationCost : ℚ

/-- Rational-inattention form: expected payoff minus information cost. -/
def rationalInattentionForm {N : ℕ} (a : CoarsePartitionAction N) : ℚ :=
  deltaExpectation a.payoff - a.informationCost

/-- Translation from the recognition finite-action form to the coarse-partition
form used in rational-inattention models. -/
def toCoarsePartitionAction {N : ℕ} (a : FiniteAction N) : CoarsePartitionAction N where
  payoff := a.payoff
  informationCost := a.distinctionCost

/-- Recognition choice is already in rational-inattention form once the
distinction cost is read as information cost. -/
theorem ri_limit {N : ℕ} (a : FiniteAction N) :
    choiceValue a = rationalInattentionForm (toCoarsePartitionAction a) := by
  rfl

end

end Recognition
end Economics
end IndisputableMonolith
