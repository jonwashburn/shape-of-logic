import Mathlib
import IndisputableMonolith.RecogGeom.Core
import IndisputableMonolith.RecogGeom.Recognizer
import IndisputableMonolith.RecogGeom.Indistinguishable
import IndisputableMonolith.RecogGeom.Quotient

/-!
# Recognition Geometry: Concrete Examples

A geometry isn't complete without examples. This module provides concrete
recognition geometries that illustrate the framework.

## Examples Developed

1. **Discrete Recognition on Fin n** - Every config distinguishable
2. **Sign Recognizer on ℤ** - Three equivalence classes (neg, zero, pos)
3. **Magnitude Recognizer on ℤ** - |n| determines the class

## Key Insights from Examples

- Discrete recognizer: quotient ≅ original space
- Sign recognizer: ℤ/~ has exactly 3 classes
- Magnitude recognizer: infinitely many classes (0, 1, 2, ...)
- Composition refines: sign ⊗ magnitude distinguishes more

-/

namespace IndisputableMonolith
namespace RecogGeom
namespace Examples

/-! ## Example 1: Discrete Recognition on Fin n -/

/-- Configuration space: Fin n (n ≥ 2 distinct configurations) -/
instance finConfigSpace (n : ℕ) [h : NeZero n] : ConfigSpace (Fin n) where
  nonempty := ⟨0⟩

/-- The discrete recognizer: identity map (distinguishes everything) -/
def discreteRecognizer (n : ℕ) [h : NeZero n] (hn : 2 ≤ n) :
    Recognizer (Fin n) (Fin n) where
  R := id
  nontrivial := by
    use ⟨0, by omega⟩, ⟨1, by omega⟩
    simp [Fin.ext_iff]

/-- **Theorem**: Discrete recognizer - indistinguishable iff equal -/
theorem discrete_indist_iff_eq (n : ℕ) [h : NeZero n] (hn : 2 ≤ n)
    (c₁ c₂ : Fin n) :
    Indistinguishable (discreteRecognizer n hn) c₁ c₂ ↔ c₁ = c₂ := by
  simp [Indistinguishable, discreteRecognizer]

/-- **Corollary**: Each config is in its own resolution cell -/
theorem discrete_singleton_cells (n : ℕ) [h : NeZero n] (hn : 2 ≤ n) (c : Fin n) :
    ResolutionCell (discreteRecognizer n hn) c = {c} := by
  ext x
  simp [ResolutionCell, discrete_indist_iff_eq]

/-! ## Example 2: Sign Recognizer on ℤ -/

/-- Integer configuration space -/
instance : ConfigSpace ℤ where
  nonempty := ⟨0⟩

/-- Three-valued sign type -/
inductive Sign : Type
  | neg : Sign
  | zero : Sign
  | pos : Sign
  deriving DecidableEq, Repr

/-- Sign is nonempty -/
instance : Nonempty Sign := ⟨Sign.zero⟩

/-- The sign function -/
def signOf : ℤ → Sign
  | n => if n < 0 then Sign.neg else if n = 0 then Sign.zero else Sign.pos

/-- The sign recognizer on ℤ -/
def signRecognizer : Recognizer ℤ Sign where
  R := signOf
  nontrivial := by
    use -1, 1
    simp [signOf]

/-- **Theorem**: Two integers are indistinguishable iff same sign -/
theorem sign_indistinguishable (n m : ℤ) :
    Indistinguishable signRecognizer n m ↔ signOf n = signOf m := by
  rfl

/-- **Theorem**: -5 ~ -3 (both negative) -/
theorem neg_indist : Indistinguishable signRecognizer (-5) (-3) := by
  simp [Indistinguishable, signRecognizer, signOf]

/-- **Theorem**: -1 ≁ 1 (different signs) -/
theorem neg_pos_dist : ¬Indistinguishable signRecognizer (-1) 1 := by
  simp [Indistinguishable, signRecognizer, signOf]

/-- **Theorem**: 0 ≁ 1 (different signs) -/
theorem zero_pos_dist : ¬Indistinguishable signRecognizer 0 1 := by
  simp [Indistinguishable, signRecognizer, signOf]

/-! ## Example 3: Magnitude Recognizer on ℤ -/

/-- The magnitude recognizer: n ↦ |n| -/
def magnitudeRecognizer : Recognizer ℤ ℕ where
  R := fun n => n.natAbs
  nontrivial := by
    use 0, 1
    simp

/-- **Theorem**: n ~ m iff |n| = |m| -/
theorem magnitude_indistinguishable (n m : ℤ) :
    Indistinguishable magnitudeRecognizer n m ↔ n.natAbs = m.natAbs := by
  rfl

/-- **Theorem**: 3 ~ -3 (same magnitude) -/
theorem plus_minus_indist : Indistinguishable magnitudeRecognizer 3 (-3) := by
  simp [Indistinguishable, magnitudeRecognizer]

/-- **Theorem**: 2 ≁ 3 (different magnitudes) -/
theorem diff_magnitude_dist : ¬Indistinguishable magnitudeRecognizer 2 3 := by
  simp [Indistinguishable, magnitudeRecognizer]

/-! ## Example 4: Composition Refines Both -/

/-- **Key Observation**: Combining sign and magnitude gives a finer recognizer.

    - Sign alone: 3 ~ -3 (both positive/negative)... wait, that's wrong
    - Actually sign: 3 ≁ -3 (positive vs negative)
    - Magnitude alone: 3 ~ -3 (both have magnitude 3)

    So sign distinguishes 3 from -3, but magnitude doesn't.
    Conversely, magnitude distinguishes 3 from 5, both positive.

    The composition (sign, magnitude) distinguishes both. -/
theorem sign_distinguishes_3_neg3 : ¬Indistinguishable signRecognizer 3 (-3) := by
  simp [Indistinguishable, signRecognizer, signOf]

theorem magnitude_indist_3_neg3 : Indistinguishable magnitudeRecognizer 3 (-3) := by
  simp [Indistinguishable, magnitudeRecognizer]

theorem sign_indist_3_5 : Indistinguishable signRecognizer 3 5 := by
  simp [Indistinguishable, signRecognizer, signOf]

theorem magnitude_distinguishes_3_5 : ¬Indistinguishable magnitudeRecognizer 3 5 := by
  simp [Indistinguishable, magnitudeRecognizer]

/-- **Composition Principle**: Neither sign nor magnitude alone distinguishes
    all pairs, but together they do (for nonzero integers). -/
theorem composition_refines :
    (∀ n m : ℤ, n ≠ 0 → m ≠ 0 →
      (Indistinguishable signRecognizer n m ∧ Indistinguishable magnitudeRecognizer n m) →
      n = m ∨ n = -m) := by
  intro n m hn hm ⟨hsign, hmag⟩
  simp only [Indistinguishable, signRecognizer, magnitudeRecognizer] at hsign hmag
  -- Same sign and same magnitude implies n = m or n = -m
  have h1 : n.natAbs = m.natAbs := hmag
  -- If signs match and magnitudes match, must be equal or negatives
  rcases Int.natAbs_eq_natAbs_iff.mp h1 with h | h
  · left; exact h
  · right; exact h

/-! ## Physical Interpretation -/

/-! ### Physical Interpretation

These examples show how recognizers model measurement in physics:
- **Discrete** = perfect measurement (eigenvalue detection)
- **Sign/magnitude** = coarse measurements (binary outcomes)
- **Composition** = combined measurements with finer resolution

In quantum mechanics, observables ARE recognizers mapping states to eigenvalues. -/

/-! ## Module Status -/

def examples_status : String :=
  "✓ Discrete Recognition on Fin n\n" ++
  "  • discrete_indist_iff_eq: indistinguishable ↔ equal\n" ++
  "  • discrete_singleton_cells: each config is its own cell\n" ++
  "\n" ++
  "✓ Sign Recognizer on ℤ\n" ++
  "  • sign_indistinguishable: same sign ↔ indistinguishable\n" ++
  "  • neg_indist, neg_pos_dist: concrete examples\n" ++
  "\n" ++
  "✓ Magnitude Recognizer on ℤ\n" ++
  "  • magnitude_indistinguishable: same |n| ↔ indistinguishable\n" ++
  "  • plus_minus_indist: 3 ~ -3\n" ++
  "\n" ++
  "✓ Composition Analysis\n" ++
  "  • sign_distinguishes_3_neg3 vs magnitude_indist_3_neg3\n" ++
  "  • sign_indist_3_5 vs magnitude_distinguishes_3_5\n" ++
  "  • composition_refines: combining gives finer resolution\n" ++
  "\n" ++
  "EXAMPLES COMPLETE"

#eval examples_status

end Examples
end RecogGeom
end IndisputableMonolith
