import Mathlib.Logic.Basic

namespace IndisputableMonolith.PRCGrow.DeltaForcedNoEnumeration

/-- The constructive Cantor theorem: the binary-sequence space `ℕ → Bool` cannot be
δ-enumerated. This is the choice-free heart of `¬ DeltaForced ℝ`: a forced
(δ-enumerable) carrier cannot surject onto the binary sequences, so the continuum
is not forced. -/
theorem no_enumeration_seq : ¬ ∃ f : ℕ → (ℕ → Bool), Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨n, hn⟩ := hf (fun k => !(f k k))
  have := congrFun hn n
  simp at this

end IndisputableMonolith.PRCGrow.DeltaForcedNoEnumeration
