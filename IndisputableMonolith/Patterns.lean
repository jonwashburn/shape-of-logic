import Mathlib

namespace IndisputableMonolith
namespace Patterns

open Classical
open Function

@[simp] def Pattern (d : Nat) := (Fin d → Bool)

instance instFintypePattern (d : Nat) : Fintype (Pattern d) := by
  dsimp [Pattern]
  infer_instance

structure CompleteCover (d : Nat) where
  period : ℕ
  path   : Fin period → Pattern d
  complete : Function.Surjective path

/-- There exists a complete cover of exact length `2^d` for d‑dimensional patterns. -/
theorem cover_exact_pow (d : Nat) : ∃ w : CompleteCover d, w.period = 2 ^ d := by
  classical
  let e := (Fintype.equivFin (Pattern d)).symm
  refine ⟨{ period := Fintype.card (Pattern d)
          , path := fun i => e i
          , complete := (Fintype.equivFin (Pattern d)).symm.surjective }, ?_⟩
  have : Fintype.card (Pattern d) = 2 ^ d := by
    simp [Pattern, Fintype.card_bool, Fintype.card_fin]
  exact this

/-- There exists an 8‑tick complete cover for 3‑bit patterns. -/
 theorem period_exactly_8 : ∃ w : CompleteCover 3, w.period = 8 := by
  simpa using cover_exact_pow 3

/-- Cardinality of the pattern space. -/
lemma card_pattern (d : Nat) : Fintype.card (Pattern d) = 2 ^ d := by
  classical
  simp [Pattern, Fintype.card_fin] at*

/-- No surjection to all d-bit patterns if T < 2^d. -/
lemma no_surj_small (T d : Nat) (hT : T < 2 ^ d) :
  ¬ ∃ f : Fin T → Pattern d, Function.Surjective f := by
  classical
  intro h; rcases h with ⟨f, hf⟩
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  have hginj : Injective g := by
    intro y₁ y₂ hgy
    have : f (g y₁) = f (g y₂) := by simp [hgy]
    simpa [RightInverse, hg y₁, hg y₂] using this
  have hcard : Fintype.card (Pattern d) ≤ Fintype.card (Fin T) :=
    Fintype.card_le_of_injective _ hginj
  have : 2 ^ d ≤ T := by
    simpa [Fintype.card_fin, card_pattern d] using hcard
  exact (lt_of_le_of_lt this hT).false

/-- Minimal ticks lower bound for a complete cover. -/
lemma min_ticks_cover {d T : Nat}
  (pass : Fin T → Pattern d) (covers : Function.Surjective pass) : 2 ^ d ≤ T := by
  classical
  by_contra h
  exact (no_surj_small T d (lt_of_not_ge h)) ⟨pass, covers⟩

/-- For 3-bit patterns, any complete pass has length at least 8. -/
lemma eight_tick_min {T : Nat}
  (pass : Fin T → Pattern 3) (covers : Function.Surjective pass) : 8 ≤ T := by
  simpa using (min_ticks_cover (d := 3) (T := T) pass covers)

/-- Nyquist-style obstruction: if T < 2^D, no surjection to D-bit patterns. -/
theorem T7_nyquist_obstruction {T D : Nat}
  (hT : T < 2 ^ D) : ¬ ∃ f : Fin T → Pattern D, Function.Surjective f :=
  no_surj_small T D hT

/-- At threshold T=2^D there is a bijection (no aliasing). -/
theorem T7_threshold_bijection (D : Nat) : ∃ f : Fin (2 ^ D) → Pattern D, Function.Bijective f := by
  classical
  let e := (Fintype.equivFin (Pattern D))
  have hcard : Fintype.card (Pattern D) = 2 ^ D := by exact card_pattern D
  -- Manual cast equivalence between Fin (2^D) and Fin (Fintype.card (Pattern D))
  let castTo : Fin (2 ^ D) → Fin (Fintype.card (Pattern D)) :=
    fun i => ⟨i.1, by
      -- rewrite the goal via hcard and close with i.2
      have : i.1 < 2 ^ D := i.2
      simp [this]⟩
  let castFrom : Fin (Fintype.card (Pattern D)) → Fin (2 ^ D) :=
    fun j => ⟨j.1, by simpa [hcard] using j.2⟩
  have hLeft : Function.LeftInverse castFrom castTo := by intro i; cases i; rfl
  have hRight : Function.RightInverse castFrom castTo := by intro j; cases j; rfl
  have hCastBij : Function.Bijective castTo := ⟨hLeft.injective, hRight.surjective⟩
  refine ⟨fun i => (e.symm) (castTo i), ?_⟩
  exact (e.symm).bijective.comp hCastBij

/-‑ ## T6 alias theorems -/
 theorem T6_exist_exact_2pow (d : Nat) : ∃ w : CompleteCover d, w.period = 2 ^ d :=
  cover_exact_pow d

 theorem T6_exist_8 : ∃ w : CompleteCover 3, w.period = 8 :=
  period_exactly_8

/-‑ ## Minimal counting facts and eight‑tick lower bound -/

/-- For any dimension `d`, the exact cover of period `2^d` has positive period. -/
 theorem T6_exist_exact_pos (d : Nat) : ∃ w : CompleteCover d, 0 < w.period := by
  obtain ⟨w, hp⟩ := cover_exact_pow d
  have : 0 < (2 : ℕ) ^ d := by
    exact pow_pos (by decide : 0 < (2 : ℕ)) d
  exact ⟨w, by simp [hp]⟩

/-- The 3‑bit complete cover of period 8 has positive period. -/
 theorem period_exactly_8_pos : ∃ w : CompleteCover 3, 0 < w.period := by
  obtain ⟨w, hp⟩ := period_exactly_8
  have : 0 < (8 : ℕ) := by decide
  exact ⟨w, by simp [hp]⟩

end Patterns
end IndisputableMonolith
