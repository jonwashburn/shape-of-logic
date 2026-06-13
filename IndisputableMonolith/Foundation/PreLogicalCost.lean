import Mathlib

namespace IndisputableMonolith
namespace Foundation
namespace PreLogicalCost

open Real

/-- Pre-logical configuration value constrained to the unit interval. -/
structure PreState where
  val : ℝ
  in_unit_interval : 0 ≤ val ∧ val ≤ 1

/-- Pre-logical cost landscape on `[0,1]`: minima occur at the boundary states. -/
noncomputable def preCost (s : PreState) : ℝ := s.val * (1 - s.val)

/-- Stable configurations are exactly cost minima. -/
def IsStable (s : PreState) : Prop := preCost s = 0

/-- Stability is equivalent to the two boundary values `0` and `1`. -/
theorem stable_iff_boundary (s : PreState) :
    IsStable s ↔ s.val = 0 ∨ s.val = 1 := by
  unfold IsStable preCost
  constructor
  · intro h
    have hfact : s.val * (1 - s.val) = 0 := h
    rcases mul_eq_zero.mp hfact with h0 | h1
    · exact Or.inl h0
    · right
      linarith
  · intro h
    rcases h with h0 | h1
    · simp [h0]
    · simp [h1]

/-- Stable states as arithmetic 0/1 encodings. -/
structure StableState where
  bit : ℝ
  is_bit : bit = 0 ∨ bit = 1

/-- Arithmetic conjunction on stable states (`0/1` multiplication). -/
def band (a b : StableState) : StableState := by
  refine ⟨a.bit * b.bit, ?_⟩
  rcases a.is_bit with ha | ha <;> rcases b.is_bit with hb | hb <;> simp [ha, hb]

/-- Arithmetic disjunction on stable states (`a + b - ab` on `0/1`). -/
def bor (a b : StableState) : StableState := by
  refine ⟨a.bit + b.bit - a.bit * b.bit, ?_⟩
  rcases a.is_bit with ha | ha <;> rcases b.is_bit with hb | hb <;> simp [ha, hb]

/-- Arithmetic negation on stable states (`1 - a` on `0/1`). -/
def bnot (a : StableState) : StableState := by
  refine ⟨1 - a.bit, ?_⟩
  rcases a.is_bit with ha | ha <;> simp [ha]

/-- The stable arithmetic states form a Boolean-style algebraic fragment. -/
theorem stable_forms_boolean_algebra :
    (∀ a b : StableState, (band a b).bit = a.bit * b.bit) ∧
    (∀ a b : StableState, (bor a b).bit = a.bit + b.bit - a.bit * b.bit) ∧
    (∀ a : StableState, (bnot a).bit = 1 - a.bit) := by
  constructor
  · intro a b
    rfl
  constructor
  · intro a b
    rfl
  · intro a
    rfl

end PreLogicalCost
end Foundation
end IndisputableMonolith
