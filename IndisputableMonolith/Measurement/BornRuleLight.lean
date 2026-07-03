import Mathlib

/-!
# Born Rule (Lightweight)

Minimal algebraic lemma used in paper exports; avoids heavy dependencies.
-/

namespace IndisputableMonolith
namespace Measurement

open Real Complex

/-- Born rule normalized: from recognition weights to normalized probabilities. -/
theorem born_rule_normalized (C₁ C₂ : ℝ) (α₁ α₂ : ℂ)
  (h₁ : Real.exp (-C₁) / (Real.exp (-C₁) + Real.exp (-C₂)) = ‖α₁‖ ^ 2)
  (h₂ : Real.exp (-C₂) / (Real.exp (-C₁) + Real.exp (-C₂)) = ‖α₂‖ ^ 2) :
  ‖α₁‖ ^ 2 + ‖α₂‖ ^ 2 = 1 := by
  have hdenom : Real.exp (-C₁) + Real.exp (-C₂) ≠ 0 :=
    (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
  calc ‖α₁‖ ^ 2 + ‖α₂‖ ^ 2
      = Real.exp (-C₁) / (Real.exp (-C₁) + Real.exp (-C₂)) +
        Real.exp (-C₂) / (Real.exp (-C₁) + Real.exp (-C₂)) := by
          rw [← h₁, ← h₂]
      _ = (Real.exp (-C₁) + Real.exp (-C₂)) / (Real.exp (-C₁) + Real.exp (-C₂)) := by
          rw [div_add_div_same]
      _ = 1 := div_self hdenom

end Measurement
end IndisputableMonolith
