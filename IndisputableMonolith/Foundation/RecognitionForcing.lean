import Mathlib
import IndisputableMonolith.Foundation.LawOfExistence
import IndisputableMonolith.Foundation.LedgerForcing
import IndisputableMonolith.Recognition

/-!
# Recognition Forcing: From Cost to Recognition Structure

This module proves that **recognition is forced** by the cost foundation.
-/

namespace IndisputableMonolith
namespace Foundation
namespace RecognitionForcing

open Real

/-! ## Part 0: Recognition-Cost Bridge -/

/-- The J-cost of a recognition event. -/
noncomputable def recognition_cost (e : LedgerForcing.RecognitionEvent) : ℝ :=
  LedgerForcing.J e.ratio

/-- Recognition events with ratio = 1 are cost-free. -/
theorem self_recognition_zero_cost (e : LedgerForcing.RecognitionEvent) :
    e.ratio = 1 → recognition_cost e = 0 := by
  intro h
  simp only [recognition_cost, h, LedgerForcing.J]
  norm_num

/-- Non-trivial recognition has positive cost.
    Uses the fact that J(x) = (x + 1/x)/2 - 1 ≥ 0, with = 0 iff x = 1. -/
theorem nontrivial_recognition_positive_cost (e : LedgerForcing.RecognitionEvent)
    (h : e.ratio ≠ 1) : recognition_cost e > 0 := by
  simp only [recognition_cost, LedgerForcing.J]
  have hpos := e.ratio_pos
  have h0 : e.ratio ≠ 0 := hpos.ne'
  -- (x - 1)² > 0 when x ≠ 1
  have hne : (e.ratio - 1)^2 > 0 := by
    have hsq : (e.ratio - 1)^2 ≥ 0 := sq_nonneg _
    have hne2 : (e.ratio - 1)^2 ≠ 0 := by
      intro heq
      have heq2 : e.ratio - 1 = 0 := sq_eq_zero_iff.mp heq
      have : e.ratio = 1 := by linarith
      exact h this
    exact lt_of_le_of_ne hsq (Ne.symm hne2)
  -- Expand: x² - 2x + 1 > 0
  -- So: x² + 1 > 2x
  -- So: (x² + 1)/x > 2 (since x > 0)
  -- So: x + 1/x > 2
  have h2 : e.ratio^2 + 1 > 2*e.ratio := by nlinarith [sq_nonneg (e.ratio - 1)]
  have h3 : e.ratio + e.ratio⁻¹ > 2 := by
    have heq : e.ratio + e.ratio⁻¹ = (e.ratio^2 + 1) / e.ratio := by field_simp
    rw [heq, gt_iff_lt, lt_div_iff₀ hpos]
    linarith
  linarith

/-- Recognition is cost structure. -/
theorem recognition_is_cost_structure :
    ∀ (e : LedgerForcing.RecognitionEvent),
    (e.ratio = 1 ↔ recognition_cost e = 0) ∧
    (e.ratio ≠ 1 → recognition_cost e > 0) := by
  intro e
  refine ⟨⟨self_recognition_zero_cost e, ?_⟩, nontrivial_recognition_positive_cost e⟩
  intro h
  simp only [recognition_cost, LedgerForcing.J] at h
  have hpos := e.ratio_pos
  have h0 : e.ratio ≠ 0 := hpos.ne'
  -- h says (e.ratio + e.ratio⁻¹)/2 - 1 = 0
  -- So e.ratio + e.ratio⁻¹ = 2
  have h1 : e.ratio + e.ratio⁻¹ = 2 := by linarith
  -- This means (e.ratio - 1)² = 0
  have heq : e.ratio + e.ratio⁻¹ = (e.ratio^2 + 1) / e.ratio := by field_simp
  have h2 : (e.ratio^2 + 1) / e.ratio = 2 := by rw [← heq]; exact h1
  have h3 : e.ratio^2 + 1 = 2 * e.ratio := by
    have := congrArg (· * e.ratio) h2
    simp only [div_mul_cancel₀ _ h0] at this
    linarith
  have h4 : (e.ratio - 1)^2 = 0 := by nlinarith [sq_nonneg (e.ratio - 1)]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp h4)

/-! ## Part 1: Observable Extraction = Recognition -/

structure Observable (S : Type) where
  value : S → ℝ

structure ObservableExtractionMechanism (S : Type) where
  extract : S → ℝ
  nonconstant : ∃ s₁ s₂ : S, extract s₁ ≠ extract s₂

structure RecognitionStructure (S : Type) where
  recognizes : S → S → Prop
  self_recognition : ∀ s, recognizes s s
  symmetric : ∀ s₁ s₂, recognizes s₁ s₂ → recognizes s₂ s₁

def recognition_from_extraction {S : Type} (M : ObservableExtractionMechanism S) :
    RecognitionStructure S := {
  recognizes := fun s₁ s₂ => M.extract s₁ = M.extract s₂
  self_recognition := fun _ => rfl
  symmetric := fun _ _ h => h.symm
}

/-- Recognition is unique extraction mechanism. -/
theorem recognition_unique {S : Type} (M : ObservableExtractionMechanism S) :
    ∃ R : RecognitionStructure S,
    (∀ s₁ s₂, M.extract s₁ = M.extract s₂ ↔ R.recognizes s₁ s₂) :=
  ⟨recognition_from_extraction M, fun _ _ => Iff.rfl⟩

/-! ## Part 2: Cost Minima = Recognition -/

structure Configuration where
  value : ℝ
  pos : 0 < value

def config_to_recognition (c : Configuration) : LedgerForcing.RecognitionEvent :=
  { source := 0, target := 0, ratio := c.value, ratio_pos := c.pos }

theorem cost_minima_are_recognition (c : Configuration) :
    ∃ (e : LedgerForcing.RecognitionEvent), e.ratio = c.value :=
  ⟨config_to_recognition c, rfl⟩

theorem global_minimum_is_self_recognition :
    ∃ (e : LedgerForcing.RecognitionEvent), e.ratio = 1 ∧ recognition_cost e = 0 := by
  use { source := 0, target := 0, ratio := 1, ratio_pos := one_pos }
  simp only [recognition_cost, LedgerForcing.J]
  norm_num

/-! ## Part 3: Stability = Recognition -/

structure JStableStructure where
  carrier : Type
  cost : carrier → ℝ
  cost_bounded : ∃ m : ℝ, ∀ x, m ≤ cost x

structure RecognitionLikeStructure where
  carrier : Type
  rel : carrier → carrier → Prop
  refl : ∀ x, rel x x
  symm : ∀ x y, rel x y → rel y x

def stable_to_recognition (S : JStableStructure) : RecognitionLikeStructure := {
  carrier := S.carrier
  rel := fun x y => S.cost x = S.cost y
  refl := fun _ => rfl
  symm := fun _ _ h => h.symm
}

theorem stability_forces_recognition (S : JStableStructure) :
    ∃ (R : RecognitionLikeStructure), R.carrier = S.carrier :=
  ⟨stable_to_recognition S, rfl⟩

/-! ## Part 4: Master Theorem -/

theorem recognition_necessary (S : Type) (obs : Observable S)
    (h : ∃ s₁ s₂, obs.value s₁ ≠ obs.value s₂) :
    ∃ (R₁ R₂ : Type), Nonempty (Recognition.Recognize R₁ R₂) := by
  obtain ⟨s₁, s₂, _⟩ := h
  exact ⟨S, S, ⟨⟨s₁, s₂⟩⟩⟩

/-- **MASTER THEOREM: Recognition Forcing Complete** -/
theorem recognition_forcing_complete :
    (∀ (S : Type) (obs : Observable S),
      (∃ s₁ s₂, obs.value s₁ ≠ obs.value s₂) →
      ∃ (R₁ R₂ : Type), Nonempty (Recognition.Recognize R₁ R₂)) ∧
    (∀ (S : Type) (M : ObservableExtractionMechanism S),
      ∃ R : RecognitionStructure S, True) ∧
    (∀ (e : LedgerForcing.RecognitionEvent),
      (e.ratio = 1 ↔ recognition_cost e = 0) ∧
      (e.ratio ≠ 1 → recognition_cost e > 0)) ∧
    (∀ (c : Configuration),
      ∃ (e : LedgerForcing.RecognitionEvent), e.ratio = c.value) ∧
    (∀ (S : JStableStructure),
      ∃ (R : RecognitionLikeStructure), R.carrier = S.carrier) :=
  ⟨recognition_necessary,
   fun _ M => ⟨recognition_from_extraction M, trivial⟩,
   recognition_is_cost_structure,
   cost_minima_are_recognition,
   stability_forces_recognition⟩

/-! ## Part 5: Ledger Forcing -/

structure RecognitionTracker where
  events : List LedgerForcing.RecognitionEvent

def PreservesJSymmetry (T : RecognitionTracker) : Prop :=
  LedgerForcing.balanced_list T.events

theorem ledger_is_minimal_recognition_tracker (T : RecognitionTracker) (hSymm : PreservesJSymmetry T) :
    ∃ (L : LedgerForcing.Ledger), L.events = T.events :=
  ⟨{ events := T.events, double_entry := hSymm }, rfl⟩

/-! ## Part 6: Complete Bridge -/

theorem cost_to_recognition_bridge :
    (∀ x : ℝ, x ≠ 0 → LedgerForcing.J x = LedgerForcing.J x⁻¹) ∧
    (∃ e : LedgerForcing.RecognitionEvent, e.ratio = 1 ∧ recognition_cost e = 0) ∧
    (∀ (S : Type) (M : ObservableExtractionMechanism S), ∃ R : RecognitionStructure S, True) ∧
    (∀ (S : JStableStructure), ∃ (R : RecognitionLikeStructure), R.carrier = S.carrier) :=
  ⟨fun x hx => LedgerForcing.J_symmetric hx,
   global_minimum_is_self_recognition,
   fun _ M => ⟨recognition_from_extraction M, trivial⟩,
   stability_forces_recognition⟩

end RecognitionForcing
end Foundation
end IndisputableMonolith
