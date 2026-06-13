import Mathlib
import IndisputableMonolith.RecogGeom.Quotient

/-!
# Recognition Geometry: Composition of Recognizers (RG6)

Physical measurement does not happen in isolation. Multiple recognizers can act
on the same configuration space. This module develops the theory of composite
recognizers and proves the fundamental **Refinement Theorem**.

## The Key Insight

When we combine two recognizers R₁ and R₂, we get a composite recognizer R₁₂
that can distinguish configurations that either R₁ or R₂ can distinguish.
This means:
- The indistinguishability relation becomes finer
- The recognition quotient becomes larger (more classes)
- We see "more" of the configuration space

This is how richer geometry emerges from simpler measurements.

## Main Results

- `CompositeRecognizer`: The product recognizer R₁₂(c) = (R₁(c), R₂(c))
- `composite_refines`: R₁₂ distinguishes at least as much as R₁ or R₂
- `composite_indistinguishable_iff`: c₁ ~₁₂ c₂ ↔ (c₁ ~₁ c₂) ∧ (c₁ ~₂ c₂)
- `refinement_theorem`: Composite quotient refines both component quotients

-/

namespace IndisputableMonolith
namespace RecogGeom

variable {C E₁ E₂ : Type*}

/-! ## Composite Recognizer Definition -/

/-- The composite of two recognizers produces events in the product space.
    This is RG6: composition of recognizers. -/
def CompositeRecognizer (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂) :
    Recognizer C (E₁ × E₂) where
  R := fun c => (r₁.R c, r₂.R c)
  nontrivial := by
    -- Use nontriviality of r₁ to construct distinct events
    obtain ⟨c₁, c₂, hne⟩ := r₁.nontrivial
    use c₁, c₂
    intro heq
    apply hne
    exact (Prod.mk.injEq _ _ _ _).mp heq |>.1

/-- Notation for composite recognizer -/
infixl:70 " ⊗ " => CompositeRecognizer

/-! ## Refinement Properties -/

/-- The composite recognizer's map is the product of component maps -/
theorem composite_R_eq (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂) (c : C) :
    (r₁ ⊗ r₂).R c = (r₁.R c, r₂.R c) := rfl

/-- Indistinguishability under composite iff indistinguishable under both -/
theorem composite_indistinguishable_iff (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂)
    (c₁ c₂ : C) :
    Indistinguishable (r₁ ⊗ r₂) c₁ c₂ ↔
    Indistinguishable r₁ c₁ c₂ ∧ Indistinguishable r₂ c₁ c₂ := by
  simp only [Indistinguishable, composite_R_eq, Prod.mk.injEq]

/-- If configs are indistinguishable under composite, they are under r₁ -/
theorem composite_refines_left (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂)
    {c₁ c₂ : C} (h : Indistinguishable (r₁ ⊗ r₂) c₁ c₂) :
    Indistinguishable r₁ c₁ c₂ :=
  ((composite_indistinguishable_iff r₁ r₂ c₁ c₂).mp h).1

/-- If configs are indistinguishable under composite, they are under r₂ -/
theorem composite_refines_right (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂)
    {c₁ c₂ : C} (h : Indistinguishable (r₁ ⊗ r₂) c₁ c₂) :
    Indistinguishable r₂ c₁ c₂ :=
  ((composite_indistinguishable_iff r₁ r₂ c₁ c₂).mp h).2

/-- The composite distinguishes configs that either component distinguishes -/
theorem composite_distinguishes (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂)
    {c₁ c₂ : C} (h : Distinguishable r₁ c₁ c₂ ∨ Distinguishable r₂ c₁ c₂) :
    Distinguishable (r₁ ⊗ r₂) c₁ c₂ := by
  unfold Distinguishable at *
  intro heq
  rw [composite_R_eq] at heq
  have ⟨h1, h2⟩ := (Prod.mk.injEq _ _ _ _).mp heq
  cases h with
  | inl h₁ => exact h₁ h1
  | inr h₂ => exact h₂ h2

/-! ## Resolution Cell Refinement -/

/-- Resolution cells under composite are intersections of component cells -/
theorem composite_resolutionCell (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂) (c : C) :
    ResolutionCell (r₁ ⊗ r₂) c = ResolutionCell r₁ c ∩ ResolutionCell r₂ c := by
  ext c'
  simp only [ResolutionCell, Set.mem_setOf_eq, Set.mem_inter_iff,
             composite_indistinguishable_iff]

/-- Composite resolution cells are subsets of either component cell -/
theorem composite_cell_subset_left (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂) (c : C) :
    ResolutionCell (r₁ ⊗ r₂) c ⊆ ResolutionCell r₁ c := by
  rw [composite_resolutionCell]
  exact Set.inter_subset_left

theorem composite_cell_subset_right (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂) (c : C) :
    ResolutionCell (r₁ ⊗ r₂) c ⊆ ResolutionCell r₂ c := by
  rw [composite_resolutionCell]
  exact Set.inter_subset_right

/-! ## Quotient Maps -/

/-- There is a natural map from the composite quotient to the r₁ quotient -/
def quotientMapLeft (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂) :
    RecognitionQuotient (r₁ ⊗ r₂) → RecognitionQuotient r₁ :=
  Quotient.lift (recognitionQuotientMk r₁) (fun c₁ c₂ h =>
    (quotientMk_eq_iff r₁).mpr (composite_refines_left r₁ r₂ h))

/-- There is a natural map from the composite quotient to the r₂ quotient -/
def quotientMapRight (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂) :
    RecognitionQuotient (r₁ ⊗ r₂) → RecognitionQuotient r₂ :=
  Quotient.lift (recognitionQuotientMk r₂) (fun c₁ c₂ h =>
    (quotientMk_eq_iff r₂).mpr (composite_refines_right r₁ r₂ h))

/-- The quotient maps are surjective -/
theorem quotientMapLeft_surjective (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂) :
    Function.Surjective (quotientMapLeft r₁ r₂) := by
  intro q
  obtain ⟨c, rfl⟩ := Quotient.exists_rep q
  use recognitionQuotientMk (r₁ ⊗ r₂) c
  rfl

theorem quotientMapRight_surjective (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂) :
    Function.Surjective (quotientMapRight r₁ r₂) := by
  intro q
  obtain ⟨c, rfl⟩ := Quotient.exists_rep q
  use recognitionQuotientMk (r₁ ⊗ r₂) c
  rfl

/-! ## The Refinement Theorem -/

/-- **Refinement Theorem**: The composite quotient refines both component quotients.

    This is the fundamental theorem of recognition composition. It says that
    combining recognizers gives us a "finer" view of configuration space.
    The composite quotient C_{R₁₂} maps onto both C_{R₁} and C_{R₂}.

    Mathematically: there exist surjective maps
      π₁ : C_{R₁₂} → C_{R₁}
      π₂ : C_{R₁₂} → C_{R₂}

    This means the composite recognizer "sees" at least as much structure as
    either component recognizer. -/
theorem refinement_theorem (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂) :
    Function.Surjective (quotientMapLeft r₁ r₂) ∧
    Function.Surjective (quotientMapRight r₁ r₂) :=
  ⟨quotientMapLeft_surjective r₁ r₂, quotientMapRight_surjective r₁ r₂⟩

/-! ## Associativity and Commutativity -/

/-- Composition is commutative up to isomorphism on events -/
theorem composite_comm_events (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂) (c : C) :
    (r₁ ⊗ r₂).R c = Prod.swap ((r₂ ⊗ r₁).R c) := by
  simp [composite_R_eq]

/-- Indistinguishability is symmetric under swap -/
theorem composite_comm_indistinguishable (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂)
    (c₁ c₂ : C) :
    Indistinguishable (r₁ ⊗ r₂) c₁ c₂ ↔ Indistinguishable (r₂ ⊗ r₁) c₁ c₂ := by
  rw [composite_indistinguishable_iff, composite_indistinguishable_iff]
  exact And.comm

/-! ## N-ary Composition -/

/-- Triple composite recognizer -/
def CompositeRecognizer₃ {E₃ : Type*}
    (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂) (r₃ : Recognizer C E₃) :
    Recognizer C (E₁ × E₂ × E₃) where
  R := fun c => (r₁.R c, r₂.R c, r₃.R c)
  nontrivial := by
    obtain ⟨c₁, c₂, hne⟩ := r₁.nontrivial
    use c₁, c₂
    intro heq
    apply hne
    simp only [Prod.mk.injEq] at heq
    exact heq.1

/-! ## Information Content -/

/-- The composite recognizer has at least as much information as either component.
    "Information" here means the ability to distinguish configurations. -/
theorem composite_info_monotone_left (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂)
    {c₁ c₂ : C} (h : Distinguishable r₁ c₁ c₂) :
    Distinguishable (r₁ ⊗ r₂) c₁ c₂ :=
  composite_distinguishes r₁ r₂ (Or.inl h)

theorem composite_info_monotone_right (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂)
    {c₁ c₂ : C} (h : Distinguishable r₂ c₁ c₂) :
    Distinguishable (r₁ ⊗ r₂) c₁ c₂ :=
  composite_distinguishes r₁ r₂ (Or.inr h)

/-! ## Module Status -/

def composition_status : String :=
  "✓ CompositeRecognizer defined (RG6)\n" ++
  "✓ composite_indistinguishable_iff: c₁ ~₁₂ c₂ ↔ (c₁ ~₁ c₂) ∧ (c₁ ~₂ c₂)\n" ++
  "✓ composite_refines_left/right: composite refines both components\n" ++
  "✓ composite_resolutionCell: cells are intersections\n" ++
  "✓ quotientMapLeft/Right: surjective quotient maps\n" ++
  "✓ REFINEMENT THEOREM: composite quotient refines both components\n" ++
  "✓ composite_comm: composition is commutative\n" ++
  "✓ Information monotonicity theorems\n" ++
  "\n" ++
  "COMPOSITION (RG6) COMPLETE"

#eval composition_status

end RecogGeom
end IndisputableMonolith
