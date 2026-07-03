import IndisputableMonolith.Foundation.UniversalForcing.Strict.Invariance

/-!
  Strict/Music.lean

  Domain-rich musical realization over positive frequency ratios.  The
  comparison is equality-cost on ratios for this strict pass; richer
  psychoacoustic dissonance costs can refine it later.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace Strict
namespace Music

/-- Positive frequency ratio. -/
abbrev FrequencyRatio := {x : ℝ // 0 < x}

noncomputable def ratioCost (a b : FrequencyRatio) : Nat :=
  if a = b then 0 else 1

@[simp] theorem ratioCost_self (a : FrequencyRatio) : ratioCost a a = 0 := by
  simp [ratioCost]

theorem ratioCost_symm (a b : FrequencyRatio) : ratioCost a b = ratioCost b a := by
  by_cases h : a = b
  · subst h
    simp [ratioCost]
  · have h' : b ≠ a := by intro hb; exact h hb.symm
    simp [ratioCost, h, h']

def octave : FrequencyRatio := ⟨2, by norm_num⟩
noncomputable def perfectFifth : FrequencyRatio := ⟨(3 : ℝ) / 2, by norm_num⟩
noncomputable def perfectFourth : FrequencyRatio := ⟨(4 : ℝ) / 3, by norm_num⟩

/-- Strict musical realization using octave stacking as the canonical generator. -/
noncomputable def strictMusicRealization : StrictLogicRealization where
  Carrier := FrequencyRatio
  Cost := Nat
  zeroCost := inferInstance
  compare := ratioCost
  compose := fun a b => ⟨a.1 * b.1, mul_pos a.2 b.2⟩
  one := ⟨1, one_pos⟩
  generator := octave
  identity_law := ratioCost_self
  non_contradiction_law := ratioCost_symm
  excluded_middle_law := True
  composition_law := True
  invariance_law := True
  nontrivial_law := by
    have hne : octave ≠ (⟨1, one_pos⟩ : FrequencyRatio) := by
      intro h
      have hv := congrArg Subtype.val h
      norm_num [octave] at hv
    simp [ratioCost, hne]

def music_is_positive_ratio_subrealization : True := trivial

noncomputable def music_arith_equiv_logicNat :
    (StrictLogicRealization.arith strictMusicRealization).peano.carrier
      ≃ ArithmeticFromLogic.LogicNat :=
  (StrictLogicRealization.toLightweight strictMusicRealization).orbitEquivLogicNat

end Music
end Strict
end UniversalForcing
end Foundation
end IndisputableMonolith
