import Mathlib
import IndisputableMonolith.Cost

/-!
# Law of Existence: Rigorous Formalization

This module provides a **sharp, literal** formalization of the Law of Existence:

  **x exists ⟺ defect(x) = 0**

## Key Theorems

1. `defect_zero_iff_one`: defect(x) = 0 ⟺ x = 1
2. `law_of_existence`: Exists x ⟺ DefectCollapse x
3. `unity_unique_existent`: 1 is the unique existent
4. `nothing_cannot_exist`: ∀ C, ∃ ε > 0, ∀ x ∈ (0,ε), defect(x) > C
5. `existence_economically_inevitable`: ∃! x > 0, x minimizes defect
-/

namespace IndisputableMonolith
namespace Foundation
namespace LawOfExistence

open Real

/-! ## The Cost/Defect Functional -/

/-- The canonical cost functional J(x) = ½(x + x⁻¹) - 1. -/
noncomputable def J (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

/-- The defect functional. Equals J for positive x. -/
noncomputable def defect (x : ℝ) : ℝ := J x

/-- Defect at unity is zero. -/
@[simp] theorem defect_at_one : defect 1 = 0 := by simp [defect, J]

/-- Defect is non-negative for positive arguments. -/
theorem defect_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ defect x := by
  simp only [defect, J]
  have hx0 : x ≠ 0 := hx.ne'
  have h : 0 ≤ (x - 1)^2 / x := by positivity
  calc (x + x⁻¹) / 2 - 1 = ((x - 1)^2 / x) / 2 := by field_simp; ring
    _ ≥ 0 := by positivity

/-! ## The Existence Predicate -/

/-- **Existence Predicate**: x exists in the RS framework iff x > 0 and defect(x) = 0. -/
structure Exists (x : ℝ) : Prop where
  pos : 0 < x
  defect_zero : defect x = 0

/-- **Defect Collapse Predicate**: Equivalent formulation. -/
def DefectCollapse (x : ℝ) : Prop := 0 < x ∧ defect x = 0

/-! ## Core Equivalence Theorems -/

/-- **Defect Zero Characterization**: defect(x) = 0 ⟺ x = 1 (for x > 0). -/
theorem defect_zero_iff_one {x : ℝ} (hx : 0 < x) : defect x = 0 ↔ x = 1 := by
  simp only [defect, J]
  constructor
  · intro h
    have hx0 : x ≠ 0 := hx.ne'
    -- (x + 1/x)/2 - 1 = 0 implies (x + 1/x) = 2
    have h1 : x + x⁻¹ = 2 := by linarith
    -- Multiply by x: x² + 1 = 2x, so (x-1)² = 0
    have h2 : x * (x + x⁻¹) = x * 2 := by rw [h1]
    have h3 : x^2 + 1 = 2 * x := by field_simp at h2; linarith
    nlinarith [sq_nonneg (x - 1)]
  · intro h; simp [h]

/-- **Law of Existence (Forward)**: Existence implies defect is zero. -/
theorem exists_implies_defect_zero {x : ℝ} (h : Exists x) : defect x = 0 :=
  h.defect_zero

/-- **Law of Existence (Backward)**: Zero defect (with x > 0) implies existence. -/
theorem defect_zero_implies_exists {x : ℝ} (hpos : 0 < x) (hdef : defect x = 0) :
    Exists x := ⟨hpos, hdef⟩

/-- **Law of Existence (Biconditional)**: x exists ⟺ defect collapses. -/
theorem law_of_existence (x : ℝ) : Exists x ↔ DefectCollapse x :=
  ⟨fun ⟨hpos, hdef⟩ => ⟨hpos, hdef⟩, fun ⟨hpos, hdef⟩ => ⟨hpos, hdef⟩⟩

/-- **Existence Characterization**: x exists ⟺ x = 1. -/
theorem exists_iff_unity {x : ℝ} (hx : 0 < x) : Exists x ↔ x = 1 :=
  ⟨fun ⟨_, hdef⟩ => (defect_zero_iff_one hx).mp hdef,
   fun h => ⟨hx, (defect_zero_iff_one hx).mpr h⟩⟩

/-- **Unity is Unique Existent**: ∀ x, Exists x ⟺ x = 1. -/
theorem unity_unique_existent : ∀ x : ℝ, Exists x ↔ x = 1 := by
  intro x
  constructor
  · intro ⟨hpos, hdef⟩; exact (defect_zero_iff_one hpos).mp hdef
  · intro h; subst h; exact ⟨one_pos, defect_at_one⟩

/-- Alias for `defect_at_one`. -/
theorem defect_one : defect 1 = 0 := defect_at_one

/-- Defect is strictly positive for x ≠ 1. -/
theorem defect_pos_of_ne_one {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) : 0 < defect x := by
  have h_nn := defect_nonneg hx
  have h_ne_zero : defect x ≠ 0 := fun h => hne ((defect_zero_iff_one hx).mp h)
  exact lt_of_le_of_ne h_nn (Ne.symm h_ne_zero)

/-! ## Nothing Cannot Exist: J(0) → ∞ -/

/-- As x → 0⁺, defect(x) → +∞.

Technical proof: J(x) = (x + 1/x)/2 - 1 ≥ 1/(2x) - 1 → +∞ as x → 0⁺. -/
theorem defect_tendsto_atTop_at_zero :
    Filter.Tendsto defect (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  unfold defect J
  -- The proof uses that 1/x → +∞ as x → 0⁺, and (x + 1/x)/2 - 1 ≥ 1/(2x) - 1
  have hinv : Filter.Tendsto (fun x : ℝ => x⁻¹) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  rw [Filter.tendsto_atTop]
  intro r
  rw [Filter.tendsto_atTop] at hinv
  have hev := hinv (2 * (r + 2))
  -- On nhdsWithin 0 (Ioi 0), x is positive. Combine with x⁻¹ ≥ 2(r+2)
  have hpos : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < x := eventually_mem_nhdsWithin
  apply Filter.Eventually.mono (hev.and hpos)
  intro x ⟨hinvx, hx0⟩
  have h1 : (x + x⁻¹) / 2 - 1 ≥ x⁻¹ / 2 - 1 := by linarith
  have h2 : x⁻¹ / 2 - 1 ≥ (2 * (r + 2)) / 2 - 1 := by linarith
  linarith

/-- **Nothing Cannot Exist**: For any cost bound C, defect exceeds C near zero.

This is the **sharp** statement that "Nothing costs infinity." -/
theorem nothing_cannot_exist (C : ℝ) :
    ∃ ε > 0, ∀ x, 0 < x → x < ε → C < defect x := by
  -- Choose ε = 1/(2(|C|+2)) so that 1/x > 2(|C|+2) when x < ε
  use 1 / (2 * (|C| + 2))
  constructor
  · positivity
  · intro x hxpos hxlt
    -- x < 1/(2(|C|+2)) implies 1/x > 2(|C|+2)
    have hbound : 0 < 2 * (|C| + 2) := by positivity
    have hinv : 2 * (|C| + 2) < x⁻¹ := by
      rw [inv_eq_one_div, lt_one_div hbound hxpos]
      exact hxlt
    simp only [defect, J]
    have hxinv_pos : 0 < x⁻¹ := inv_pos.mpr hxpos
    -- (x + 1/x)/2 - 1 ≥ 1/x / 2 - 1 > (2(|C|+2))/2 - 1 = |C| + 1 ≥ C + 1 > C
    have h1 : x⁻¹ / 2 > |C| + 1 := by linarith
    have h2 : (x + x⁻¹) / 2 ≥ x⁻¹ / 2 := by
      have : x ≥ 0 := le_of_lt hxpos
      linarith
    have h3 : |C| ≥ C := le_abs_self C
    linarith

/-! ## Structured Set -/

/-- The structured set S = {x ∈ ℝ₊ : defect(x) = 0} = {1}. -/
def StructuredSet : Set ℝ := {x : ℝ | 0 < x ∧ defect x = 0}

theorem structured_set_singleton : StructuredSet = {1} := by
  ext x
  simp only [StructuredSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨hpos, hdef⟩; exact (defect_zero_iff_one hpos).mp hdef
  · intro h; subst h; exact ⟨one_pos, defect_at_one⟩

/-- Membership in structured set ⟺ existence. -/
theorem mem_structured_iff_exists {x : ℝ} : x ∈ StructuredSet ↔ Exists x :=
  ⟨fun ⟨hpos, hdef⟩ => ⟨hpos, hdef⟩, fun ⟨hpos, hdef⟩ => ⟨hpos, hdef⟩⟩

/-! ## Economic Inevitability -/

/-- **Existence is Economically Inevitable**: 1 is the unique minimizer of defect. -/
theorem existence_economically_inevitable :
    ∃! x : ℝ, 0 < x ∧ ∀ y, 0 < y → defect x ≤ defect y := by
  refine ⟨1, ⟨one_pos, ?_⟩, ?_⟩
  · intro y hy
    rw [defect_at_one]
    exact defect_nonneg hy
  · intro z ⟨hzpos, hzmin⟩
    have h1 : defect z ≤ defect 1 := hzmin 1 one_pos
    rw [defect_at_one] at h1
    have h2 : defect z = 0 := le_antisymm h1 (defect_nonneg hzpos)
    exact (defect_zero_iff_one hzpos).mp h2

/-! ## Complete Law of Existence -/

/-- **Complete Law of Existence**: The following are equivalent for x > 0:
1. Exists x
2. defect(x) = 0
3. x ∈ StructuredSet
4. x = 1 -/
theorem complete_law_of_existence {x : ℝ} (hx : 0 < x) :
    Exists x ↔ defect x = 0 ∧ x ∈ StructuredSet ∧ x = 1 := by
  constructor
  · intro hex
    refine ⟨hex.defect_zero, mem_structured_iff_exists.mpr hex, ?_⟩
    exact (exists_iff_unity hx).mp hex
  · intro ⟨_, _, h3⟩
    subst h3
    exact ⟨one_pos, defect_at_one⟩

end LawOfExistence
end Foundation
end IndisputableMonolith
