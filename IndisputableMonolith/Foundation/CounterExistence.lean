import Mathlib
import IndisputableMonolith.Recognition
import IndisputableMonolith.Causality.Basic
import IndisputableMonolith.Potential

/-!
# Existence of the clock: the books grade the history

`Potential.lean` carries the rigidity half of the clock story: two
δ-counters agree on a reach component once they agree at the base point
(`T4_unique_on_component`), and any counter advances by exactly `n·δ`
along an `n`-act chain (`increment_on_ReachN`).

This module carries the existence half (the proposition "the books grade
the history" in *Three Plus One from Double-Entry Recognition*, 2026).
Fix a base event `x0` and an increment `δ ≠ 0`:

* `counter_exists_iff_grading`: a δ-counter exists on the history of
  `x0` (the states its acts reach), normalized to `p x0 = 0`, **iff**
  any two chains from `x0` to the same state have equal length;
* `no_revisit_on_clocked_history`: a history that carries a counter
  never revisits a state: every circuit at a reachable state has
  length zero.
-/

namespace IndisputableMonolith
namespace Potential

variable {M : Recognition.RecognitionStructure}

/-- Chains compose: an `n`-chain from `x` to `y` followed by an
`m`-chain from `y` to `z` is an `(n+m)`-chain from `x` to `z`. -/
lemma reachN_trans {α : Type} {K : Causality.Kinematics α}
    {n m : ℕ} {x y z : α}
    (hxy : Causality.ReachN K n x y) (hyz : Causality.ReachN K m y z) :
    Causality.ReachN K (n + m) x z := by
  induction hyz with
  | zero => simpa using hxy
  | @succ m' y0 w z0 h1 h2 ih => exact Causality.ReachN.succ (ih hxy) h2

/-- A δ-counter on the history of `x0`: the edge rule holds on every act
whose source is reachable from `x0`. -/
def DEOn (δ : ℤ) (p : Pot M) (x0 : M.U) : Prop :=
  ∀ {a b : M.U}, Causality.Reaches (Kin M) x0 a → M.R a b → p b - p a = δ

/-- A global δ-counter restricts to one on every history. -/
lemma DEOn_of_DE {δ : ℤ} {p : Pot M} (hp : DE (M:=M) δ p) (x0 : M.U) :
    DEOn (M:=M) δ p x0 := fun _ h => hp h

/-- The grading condition: any two chains from `x0` to the same state
have equal length. -/
def Graded (x0 : M.U) : Prop :=
  ∀ {n m : ℕ} {y : M.U}, Causality.ReachN (Kin M) n x0 y →
    Causality.ReachN (Kin M) m x0 y → n = m

/-- Along an `n`-act chain inside the history of `x0`, a counter
advances by exactly `n·δ`. -/
lemma increment_on_history {δ : ℤ} {p : Pot M} {x0 : M.U}
    (hp : DEOn (M:=M) δ p x0) :
    ∀ {n : ℕ} {a b : M.U}, Causality.Reaches (Kin M) x0 a →
      Causality.ReachN (Kin M) n a b → p b - p a = (n : ℤ) * δ := by
  intro n a b hx0a h
  induction h with
  | zero => simp
  | @succ n' a' y' z' h1 h2 ih =>
      have hy : Causality.Reaches (Kin M) x0 y' := by
        obtain ⟨k, hk⟩ := hx0a
        exact ⟨k + n', reachN_trans hk h1⟩
      have hzy : p z' - p y' = δ := hp hy h2
      have hya : p y' - p a' = (n' : ℤ) * δ := ih hx0a
      have hsplit : p z' - p a' = (p z' - p y') + (p y' - p a') := by ring
      rw [hsplit, hzy, hya]
      push_cast
      ring

/-- The counter's value on the history is the chain length times the
increment, once the base value is fixed. -/
theorem counter_value_on_history {δ : ℤ} {p : Pot M} {x0 : M.U}
    (hp : DEOn (M:=M) δ p x0) {n : ℕ} {y : M.U}
    (h : Causality.ReachN (Kin M) n x0 y) : p y - p x0 = (n : ℤ) * δ :=
  increment_on_history (M:=M) hp ⟨0, Causality.ReachN.zero⟩ h

/-- **The books grade the history.** A δ-counter (normalized to
`p x0 = 0`) exists on the history of `x0` iff any two chains from `x0`
to the same state have equal length. -/
theorem counter_exists_iff_grading (x0 : M.U) {δ : ℤ} (hδ : δ ≠ 0) :
    (∃ p : Pot M, DEOn (M:=M) δ p x0 ∧ p x0 = 0) ↔ Graded (M:=M) x0 := by
  constructor
  · rintro ⟨p, hp, _⟩ n m y hn hm
    have h1 : p y - p x0 = (n : ℤ) * δ :=
      counter_value_on_history (M:=M) hp hn
    have h2 : p y - p x0 = (m : ℤ) * δ :=
      counter_value_on_history (M:=M) hp hm
    have hnm : (n : ℤ) = (m : ℤ) :=
      mul_right_cancel₀ hδ (h1.symm.trans h2)
    exact_mod_cast hnm
  · intro hg
    classical
    refine ⟨fun y =>
      if h : Causality.Reaches (Kin M) x0 y then (h.choose : ℤ) * δ else 0,
      ?_, ?_⟩
    · intro a b ha hab
      have hb : Causality.Reaches (Kin M) x0 b :=
        ⟨ha.choose + 1, Causality.ReachN.succ ha.choose_spec hab⟩
      have hnb : hb.choose = ha.choose + 1 :=
        hg hb.choose_spec (Causality.ReachN.succ ha.choose_spec hab)
      simp only [dif_pos ha, dif_pos hb, hnb]
      push_cast
      ring
    · have hx0 : Causality.Reaches (Kin M) x0 x0 := ⟨0, Causality.ReachN.zero⟩
      have h0 : hx0.choose = 0 := hg hx0.choose_spec Causality.ReachN.zero
      simp [dif_pos hx0, h0]

/-- **Clocked histories never revisit a state.** If a δ-counter exists
on the history of `x0`, every circuit at a reachable state has length
zero. -/
theorem no_revisit_on_clocked_history {δ : ℤ} {p : Pot M} {x0 : M.U}
    (hδ : δ ≠ 0) (hp : DEOn (M:=M) δ p x0) {z : M.U}
    (hz : Causality.Reaches (Kin M) x0 z) {l : ℕ}
    (hcirc : Causality.ReachN (Kin M) l z z) : l = 0 := by
  have h : p z - p z = (l : ℤ) * δ := increment_on_history (M:=M) hp hz hcirc
  have h0 : (l : ℤ) * δ = 0 := by simpa using h.symm
  have hl : (l : ℤ) = 0 := by
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact h'
    · exact absurd h' hδ
  exact_mod_cast hl

end Potential
end IndisputableMonolith
