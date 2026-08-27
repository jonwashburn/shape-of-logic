import IndisputableMonolith.Patterns
import IndisputableMonolith.Patterns.GrayCycle

/-!
# ContextualReciprocityComplete — off-cert clock / complete-pass prototype

Completeness for passes on `Pattern d` for arbitrary finite `d` (never hard-coded
only `d = 3`). The premise is per-bit true/false count balance over a closed
pass: **not** `Function.Surjective` by definition.

Mandatory falsifier: the period-2 one-bit bounce must fail the premise.
Separation: the all-false ↔ all-true period-2 pass satisfies the premise for
`d ≥ 2` yet is not surjective. Act-completeness (directed edges) is recorded as
a stronger edge witness that does force surjection.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace ContextualReciprocityComplete

open Patterns
open Classical

/-- Times in a pass at which bit `i` equals `b`. -/
def bitTimes {d T : ℕ} (pass : Fin T → Pattern d) (i : Fin d) (b : Bool) : Finset (Fin T) :=
  Finset.univ.filter (fun t => pass t i = b)

/-- True-count and false-count partition the period. -/
theorem bitTimes_card_sum {d T : ℕ} (pass : Fin T → Pattern d) (i : Fin d) :
    (bitTimes pass i true).card + (bitTimes pass i false).card = T := by
  have hpart :
      (bitTimes pass i true) ∪ (bitTimes pass i false) =
        (Finset.univ : Finset (Fin T)) := by
    ext t
    constructor
    · intro _; exact Finset.mem_univ t
    · intro _
      by_cases hb : pass t i = true
      · exact Finset.mem_union_left _ (by simp [bitTimes, hb])
      · have hb' : pass t i = false := Bool.eq_false_iff.mpr hb
        exact Finset.mem_union_right _ (by simp [bitTimes, hb'])
  have hdis : Disjoint (bitTimes pass i true) (bitTimes pass i false) := by
    refine Finset.disjoint_left.mpr ?_
    intro t htTrue htFalse
    simp only [bitTimes, Finset.mem_filter, Finset.mem_univ, true_and] at htTrue htFalse
    exact Bool.noConfusion (htTrue.symm.trans htFalse)
  calc
    (bitTimes pass i true).card + (bitTimes pass i false).card
        = ((bitTimes pass i true) ∪ (bitTimes pass i false)).card :=
          (Finset.card_union_of_disjoint hdis).symm
    _ = (Finset.univ : Finset (Fin T)).card := by rw [hpart]
    _ = T := Finset.card_fin T

/-- **Contextual reciprocity completeness** on `Pattern d`.

For every context bit `i`, over the closed pass the true-count equals the
false-count. Parameterized by arbitrary finite `d` and period `T`.

This is not definitional surjection. -/
def PassContextualReciprocity {d T : ℕ} (pass : Fin T → Pattern d) : Prop :=
  ∀ i : Fin d, (bitTimes pass i true).card = (bitTimes pass i false).card

/-- First lemma: reciprocity forces uniform per-bit counts `T / 2`. -/
theorem conditional_reciprocity_counts_uniform {d T : ℕ}
    (pass : Fin T → Pattern d) (h : PassContextualReciprocity pass) (i : Fin d) :
    (bitTimes pass i true).card = T / 2 ∧
    (bitTimes pass i false).card = T / 2 ∧
    Even T := by
  have hbal := h i
  have hsum := bitTimes_card_sum pass i
  have hEven : Even T := by
    have : T = 2 * (bitTimes pass i true).card := by
      linarith
    rw [this]
    exact even_two_mul _
  have hhalf : (bitTimes pass i true).card = T / 2 := by
    have : 2 * (bitTimes pass i true).card = T := by linarith
    exact (Nat.mul_div_cancel_left _ (by decide : 0 < 2)).symm.trans
      (congrArg (fun n => n / 2) this)
  refine ⟨hhalf, ?_, hEven⟩
  rw [← hbal, hhalf]

/-! ## Period-2 bounce (mandatory fail witness) -/

/-- Period-2 bounce: all-false ↔ only bit 0 true. Parameterized by `d`. -/
def bounceA (d : ℕ) : Pattern d := fun _ => false
def bounceB (d : ℕ) : Pattern d := fun j => decide (j.val = 0)
def bouncePass (d : ℕ) : Fin 2 → Pattern d
  | ⟨0, _⟩ => bounceA d
  | ⟨1, _⟩ => bounceB d

private lemma bounce_bit1_never_true {d : ℕ} (hd : 2 ≤ d) (t : Fin 2) :
    bouncePass d t ⟨1, Nat.lt_of_succ_le hd⟩ = false := by
  fin_cases t <;> simp [bouncePass, bounceA, bounceB]

/-- For `d ≥ 2`, bounce never sets bit 1, so reciprocity fails. -/
theorem bouncePass_not_contextualReciprocity {d : ℕ} (hd : 2 ≤ d) :
    ¬ PassContextualReciprocity (bouncePass d) := by
  intro h
  let i : Fin d := ⟨1, Nat.lt_of_succ_le hd⟩
  have hbal := h i
  have hTrue : (bitTimes (bouncePass d) i true).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    simp [bitTimes] at ht
    have hb := bounce_bit1_never_true hd t
    exact Bool.noConfusion (ht.symm.trans hb)
  have hsum := bitTimes_card_sum (bouncePass d) i
  have hFalse : (bitTimes (bouncePass d) i false).card = 2 := by omega
  omega

/-- Explicit: bounce on `Pattern 3` fails `P`. -/
theorem bouncePass3_not_contextualReciprocity :
    ¬ PassContextualReciprocity (bouncePass 3) :=
  bouncePass_not_contextualReciprocity (by decide : 2 ≤ 3)

/-! ## Separation from surjection (P is not Surjective) -/

/-- All-false ↔ all-true period-2 pass (distinct from one-bit bounce). -/
def altA (d : ℕ) : Pattern d := fun _ => false
def altB (d : ℕ) : Pattern d := fun _ => true
def altPass (d : ℕ) : Fin 2 → Pattern d
  | ⟨0, _⟩ => altA d
  | ⟨1, _⟩ => altB d

theorem altPass_contextualReciprocity (d : ℕ) :
    PassContextualReciprocity (altPass d) := by
  intro i
  have hTrue : (bitTimes (altPass d) i true) = {⟨1, by decide⟩} := by
    ext t
    simp [bitTimes]
    constructor
    · intro ht
      fin_cases t
      · simp [altPass, altA] at ht
      · simp
    · intro ht
      simp at ht
      cases ht
      simp [altPass, altB]
  have hFalse : (bitTimes (altPass d) i false) = {⟨0, by decide⟩} := by
    ext t
    simp [bitTimes]
    constructor
    · intro ht
      fin_cases t
      · simp
      · simp [altPass, altB] at ht
    · intro ht
      simp at ht
      cases ht
      simp [altPass, altA]
  simp [hTrue, hFalse]

theorem altPass_not_surjective {d : ℕ} (hd : 2 ≤ d) :
    ¬ Function.Surjective (altPass d) := by
  intro h
  let p : Pattern d := fun j => decide (j.val = 0)
  obtain ⟨t, ht⟩ := h p
  fin_cases t
  · have := congrFun ht ⟨0, by omega⟩
    simp [altPass, altA, p] at this
  · have := congrFun ht ⟨1, Nat.lt_of_succ_le hd⟩
    simp [altPass, altB, p] at this

/-- Explicit separation: `P` does not imply surjection (for `d ≥ 2`). -/
theorem contextualReciprocity_separates_from_surjection {d : ℕ} (hd : 2 ≤ d) :
    ∃ (T : ℕ) (pass : Fin T → Pattern d),
      PassContextualReciprocity pass ∧ ¬ Function.Surjective pass :=
  ⟨2, altPass d, altPass_contextualReciprocity d, altPass_not_surjective hd⟩

/-- Bounce fails `P` while altPass satisfies `P`. -/
theorem bounce_fails_while_alt_satisfies {d : ℕ} (hd : 2 ≤ d) :
    ¬ PassContextualReciprocity (bouncePass d) ∧
      PassContextualReciprocity (altPass d) :=
  ⟨bouncePass_not_contextualReciprocity hd, altPass_contextualReciprocity d⟩

/-! ## ActCompleteness — directed-edge witness (not the definition of P) -/

/-- Flip bit `i` of a pattern. -/
def flipBit {d : ℕ} (p : Pattern d) (i : Fin d) : Pattern d :=
  fun j => if j = i then !p j else p j

/-- Act-completeness: every directed one-bit edge of the `d`-cube appears as a
consecutive step of the closed pass. For `d = 3` this is 24 directed edges. -/
def ActCompleteness {d T : ℕ} [NeZero T] (pass : Fin T → Pattern d) : Prop :=
  ∀ (p : Pattern d) (i : Fin d),
    ∃ t : Fin T, pass t = p ∧ pass (t + 1) = flipBit p i

/-- Act-completeness forces surjection (every vertex is a step source). -/
theorem actCompleteness_implies_surjective {d T : ℕ} [NeZero T]
    {pass : Fin T → Pattern d} (h : ActCompleteness pass) :
    Function.Surjective pass := by
  intro p
  by_cases hd : d = 0
  · subst hd
    refine ⟨0, ?_⟩
    funext j
    exact j.elim0
  · have hpos : 0 < d := Nat.pos_of_ne_zero hd
    obtain ⟨t, ht, _⟩ := h p ⟨0, hpos⟩
    exact ⟨t, ht⟩

/-- Bounce fails act-completeness for `d ≥ 2`. -/
theorem bouncePass_not_actComplete {d : ℕ} (hd : 2 ≤ d) :
    ¬ ActCompleteness (bouncePass d) := by
  intro h
  let p : Pattern d := fun _ => false
  let i : Fin d := ⟨1, Nat.lt_of_succ_le hd⟩
  obtain ⟨t, ht, hflip⟩ := h p i
  fin_cases t
  · have hb := congrFun hflip i
    simp [bouncePass, bounceB, flipBit, p, i] at hb
  · have hb := congrFun ht ⟨0, by omega⟩
    simp [bouncePass, bounceB, p] at hb

/-- Cube edge count: `d * 2^d` directed one-bit edges (`d = 3` ⇒ 24). -/
theorem directed_edge_count (d : ℕ) :
    Fintype.card (Pattern d × Fin d) = d * 2 ^ d := by
  rw [Fintype.card_prod, card_pattern, Fintype.card_fin, Nat.mul_comm]

theorem directed_edge_count_d3 :
    Fintype.card (Pattern 3 × Fin 3) = 24 :=
  directed_edge_count 3

/-! ## Phase-2 clock wall: reciprocity is too weak; act coverage is too strong -/

/-- A closed one-bit six-cycle:
`000 → 001 → 011 → 111 → 110 → 100 → 000`. -/
def balancedSixPass : Fin 6 → Pattern 3
  | ⟨0, _⟩ => pattern3 0
  | ⟨1, _⟩ => pattern3 1
  | ⟨2, _⟩ => pattern3 3
  | ⟨3, _⟩ => pattern3 7
  | ⟨4, _⟩ => pattern3 6
  | ⟨5, _⟩ => pattern3 4

/-- The six-cycle is contextually reciprocal. -/
theorem balancedSixPass_contextualReciprocity :
    PassContextualReciprocity balancedSixPass := by
  intro i
  fin_cases i <;> decide

/-- Every step of the six-cycle, including wrap-around, flips one bit. -/
theorem balancedSixPass_oneBit :
    ∀ i : Fin 6, OneBitDiff (balancedSixPass i) (balancedSixPass (i + 1)) := by
  intro i
  fin_cases i
  · refine ⟨⟨0, by decide⟩, ?_, ?_⟩
    · simp [balancedSixPass, pattern3]
    · intro k hk
      fin_cases k <;> simp [balancedSixPass, pattern3] at hk ⊢
  · refine ⟨⟨1, by decide⟩, ?_, ?_⟩
    · simp [balancedSixPass, pattern3]
    · intro k hk
      fin_cases k <;> simp [balancedSixPass, pattern3] at hk ⊢
  · refine ⟨⟨2, by decide⟩, ?_, ?_⟩
    · simp [balancedSixPass, pattern3]
    · intro k hk
      fin_cases k <;> simp [balancedSixPass, pattern3] at hk ⊢
  · refine ⟨⟨0, by decide⟩, ?_, ?_⟩
    · simp [balancedSixPass, pattern3]
    · intro k hk
      fin_cases k <;> simp [balancedSixPass, pattern3] at hk ⊢
  · refine ⟨⟨1, by decide⟩, ?_, ?_⟩
    · simp [balancedSixPass, pattern3]
    · intro k hk
      fin_cases k <;> simp [balancedSixPass, pattern3] at hk ⊢
  · refine ⟨⟨2, by decide⟩, ?_, ?_⟩
    · simp [balancedSixPass, pattern3]
    · intro k hk
      fin_cases k <;> simp [balancedSixPass, pattern3] at hk ⊢

/-- Six ticks cannot cover all eight Boolean patterns. -/
theorem balancedSixPass_not_surjective :
    ¬ Function.Surjective balancedSixPass := by
  intro h
  have hmin := Patterns.eight_tick_min balancedSixPass h
  omega

/-- Gray-8 is itself contextually reciprocal. -/
theorem grayCycle3_contextualReciprocity :
    PassContextualReciprocity grayCycle3Path := by
  intro i
  fin_cases i <;> decide

/-- Gray-8 is not act-complete: at `000`, its successor flips bit 0, so the
directed act that flips bit 1 is absent from that occurrence. -/
theorem grayCycle3_not_actComplete :
    ¬ ActCompleteness grayCycle3Path := by
  intro h
  obtain ⟨t, ht, hnext⟩ :=
    h (grayCycle3Path 0) ⟨1, by decide⟩
  have ht0 : t = 0 := grayCycle3_injective ht
  subst t
  have hb := congrFun hnext ⟨1, by decide⟩
  simp [grayCycle3Path, gray8At, pattern3, flipBit] at hb

/-- For a fixed pattern, flipping a coordinate identifies that coordinate. -/
theorem flipBit_injective_index {d : ℕ} (p : Pattern d) :
    Function.Injective (flipBit p) := by
  intro i j h
  by_contra hij
  have hb := congrFun h i
  cases hpi : p i <;> simp [flipBit, hij, hpi] at hb

/-- Act-completeness requires a distinct tick for every directed one-bit edge. -/
theorem actCompleteness_min_ticks {d T : ℕ} [NeZero T]
    {pass : Fin T → Pattern d} (h : ActCompleteness pass) :
    d * 2 ^ d ≤ T := by
  let witness : Pattern d × Fin d → Fin T :=
    fun e => (h e.1 e.2).choose
  have hs (e : Pattern d × Fin d) : pass (witness e) = e.1 :=
    (h e.1 e.2).choose_spec.1
  have ht (e : Pattern d × Fin d) :
      pass (witness e + 1) = flipBit e.1 e.2 :=
    (h e.1 e.2).choose_spec.2
  have hinj : Function.Injective witness := by
    rintro ⟨p, i⟩ ⟨q, j⟩ hw
    have hp : p = q := by
      calc
        p = pass (witness (p, i)) := (hs (p, i)).symm
        _ = pass (witness (q, j)) := congrArg pass hw
        _ = q := hs (q, j)
    subst q
    have hf : flipBit p i = flipBit p j := by
      calc
        flipBit p i = pass (witness (p, i) + 1) := (ht (p, i)).symm
        _ = pass (witness (p, j) + 1) :=
          congrArg (fun t => pass (t + 1)) hw
        _ = flipBit p j := ht (p, j)
    rw [flipBit_injective_index p hf]
  calc
    d * 2 ^ d = Fintype.card (Pattern d × Fin d) :=
      (directed_edge_count d).symm
    _ ≤ Fintype.card (Fin T) :=
      Fintype.card_le_of_injective witness hinj
    _ = T := Fintype.card_fin T

/-- Phase-2 typed wall. Contextual reciprocity plus one-bit dynamics still
misses vertices, while act-completeness changes the three-cube object from
eight vertices to its 24 directed edges. -/
structure ClockPhase2Wall : Prop where
  reciprocal_oneBit_gap :
    ∃ pass : Fin 6 → Pattern 3,
      PassContextualReciprocity pass ∧
        (∀ t, OneBitDiff (pass t) (pass (t + 1))) ∧
        ¬ Function.Surjective pass
  gray_surjective : Function.Surjective grayCycle3Path
  gray_reciprocal : PassContextualReciprocity grayCycle3Path
  gray_not_actComplete : ¬ ActCompleteness grayCycle3Path
  act_floor :
    ∀ {T : ℕ} [NeZero T] (pass : Fin T → Pattern 3),
      ActCompleteness pass → 24 ≤ T

theorem clockPhase2Wall_holds : ClockPhase2Wall where
  reciprocal_oneBit_gap :=
    ⟨balancedSixPass, balancedSixPass_contextualReciprocity,
      balancedSixPass_oneBit, balancedSixPass_not_surjective⟩
  gray_surjective := grayCycle3_surjective
  gray_reciprocal := grayCycle3_contextualReciprocity
  gray_not_actComplete := grayCycle3_not_actComplete
  act_floor := by
    intro T _ pass h
    simpa using (actCompleteness_min_ticks (d := 3) h)

/-- Prototype binder. -/
structure ContextualReciprocityPrototype : Prop where
  /-- Reciprocity is not definitional surjection. -/
  not_def_surj :
    ∃ (d T : ℕ) (pass : Fin T → Pattern d),
      PassContextualReciprocity pass ∧ ¬ Function.Surjective pass
  /-- Period-2 bounce fails the premise (for some `d ≥ 2`). -/
  bounce_fails :
    ∃ d : ℕ, 2 ≤ d ∧ ¬ PassContextualReciprocity (bouncePass d)
  /-- Uniform count lemma. -/
  uniform_counts :
    ∀ {d T : ℕ} (pass : Fin T → Pattern d),
      PassContextualReciprocity pass →
        ∀ i : Fin d, (bitTimes pass i true).card = T / 2
  /-- Act-completeness forces surjection. -/
  act_forces_surj :
    ∀ {d T : ℕ} [NeZero T] (pass : Fin T → Pattern d),
      ActCompleteness pass → Function.Surjective pass

theorem contextualReciprocityPrototype_holds : ContextualReciprocityPrototype where
  not_def_surj := by
    obtain ⟨T, pass, hP, hS⟩ :=
      contextualReciprocity_separates_from_surjection (d := 2) (by decide)
    exact ⟨2, T, pass, hP, hS⟩
  bounce_fails := ⟨3, by decide, bouncePass3_not_contextualReciprocity⟩
  uniform_counts := fun pass h i =>
    (conditional_reciprocity_counts_uniform pass h i).1
  act_forces_surj := fun pass h => actCompleteness_implies_surjective h

end ContextualReciprocityComplete
end PublicSpine
end Foundation
end IndisputableMonolith
