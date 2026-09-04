import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow4Ledger

/-!
# Cutset A2: a level is the join of two distinct earlier levels

## The sentence

Row 4 (`CutsetRow4Ledger`) left one sentence: a level's size is the join of two
earlier levels, and least count picks the adjacent pair (`AdjacentJoin`). Under
similarity (derived, 4a) the adjacent join forces `φ`.

## Is the ladder the tower?

No, and this was measured before this arc (`CutsetRow4Hierarchy`,
`towerCount_no_realized_hierarchy`): the octave tower read as a ladder has ratio
`2^D` per floor and does not post additively. Every `φ`-equation in the tree
takes `s 2 = s 1 + s 0` as a hypothesis. A2 is a sentence about the cost ladder;
the address tower (A1) does not decide it.

## The family of two-part joins

A uniform two-part join with lags `a ≤ b` behind the new level is
`TwoPartJoin s a b : s (n + b + 1) = s (n + (b - a)) + s n`. Row 4's `LagJoin s k`
is `TwoPartJoin s 0 k` (`lagJoin_iff_twoPartJoin`), and the adjacent join is
`TwoPartJoin s 0 1` (`adjacentJoin_iff_twoPartJoin`).

* **Equal parts** (`a = b`): the new level is two copies of one level. Under
  similarity the ratio satisfies `ρ^(b+1) = 2` (`equalLag_ratio`): doubling at
  `b = 0`, `√2` at `b = 1`, and so on. `φ` is never such a ratio
  (`phi_not_equalLag`), so the equal-part family is the doubling family
  generalized and none of it is the hierarchy.
* **Distinct parts** (`a < b`): the least pair is `(0, 1)` (`least_distinct_pair`),
  the adjacent join, and `ρ = φ` (`phi_of_similarity_adjacentJoin`).

## What remains

The word "distinct": that the two parts of a level are different levels. Two
parts is T1 (a join is binary), uniform lag is one rule at every floor, least
count is T2, and `φ` is then a theorem. The equal-part alternative is not
incoherent (it is a root-of-two ladder); it is excluded only by the word
"hierarchy" (levels made of *different* earlier levels). No floor fact in the
tree reaches it, and this module says so rather than adding one. A2 stays the
one sentence of row 4, said precisely.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace RowA2Join

open ClosedFramework LadderCensus Row4Ladder Row4Ledger

noncomputable section

/-! ## Two-part joins -/

/-- The new level is the join of the levels `a` and `b` steps behind its
predecessor (`a ≤ b`). -/
def TwoPartJoin (s : ℕ → ℝ) (a b : ℕ) : Prop :=
  ∀ n, s (n + b + 1) = s (n + (b - a)) + s n

theorem lagJoin_iff_twoPartJoin (s : ℕ → ℝ) (k : ℕ) : LagJoin s k ↔ TwoPartJoin s 0 k := by
  simp [LagJoin, TwoPartJoin]

theorem adjacentJoin_iff_twoPartJoin (s : ℕ → ℝ) : AdjacentJoin s ↔ TwoPartJoin s 0 1 :=
  lagJoin_iff_twoPartJoin s 1

/-! ## Equal parts: the doubling family -/

/-- **Equal parts give a root of two.** Under similarity, a level made of two
copies of the level `b` steps behind has `ρ^(b+1) = 2`. -/
theorem equalLag_ratio {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (b : ℕ)
    (hj : TwoPartJoin (orbitLevels' F base) b b) : ρ ^ (b + 1) = 2 := by
  have h := hj 0
  simp only [zero_add, Nat.sub_self] at h
  rw [similarity_levels_pow hρ base (b + 1)] at h
  have h0 := orbitLevels_pos F base 0
  have : (ρ ^ (b + 1) - 2) * orbitLevels' F base 0 = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 h0.ne'

/-- Doubling is the equal-part join at `b = 0`. -/
theorem doubling_equalLag : TwoPartJoin (fun n => (2 : ℝ) ^ n) 0 0 := by
  intro n
  simp only [add_zero, Nat.sub_self]
  ring

/-- **`φ` is never an equal-part ratio.** -/
theorem phi_not_equalLag (b : ℕ) : Constants.phi ^ (b + 1) ≠ 2 := by
  rcases b with _ | _ | b
  · simp only [zero_add, pow_one]
    exact Constants.phi_lt_two.ne
  · rw [Constants.phi_sq_eq]
    intro h
    exact Constants.phi_ne_one (by linarith)
  · intro h
    have h3 : Constants.phi ^ 3 ≤ Constants.phi ^ (b + 2 + 1) :=
      pow_le_pow_right₀ Constants.one_lt_phi.le (by omega)
    rw [Constants.phi_cubed_eq, h] at h3
    linarith [Constants.one_lt_phi]

/-- No similarity ladder with an equal-part join has ratio `φ`. -/
theorem equalLag_not_phi {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (b : ℕ)
    (hj : TwoPartJoin (orbitLevels' F base) b b) : ρ ≠ Constants.phi := by
  intro heq
  exact phi_not_equalLag b (heq ▸ equalLag_ratio hρ base b hj)

/-! ## Distinct parts: least count is the adjacent join -/

/-- Among pairs of distinct lags, `(0, 1)` is least in both entries. -/
theorem least_distinct_pair (a b : ℕ) (hab : a < b) : 0 ≤ a ∧ 1 ≤ b :=
  ⟨Nat.zero_le a, by omega⟩

/-- The adjacent join is the distinct pair of least count, and it forces `φ`. -/
theorem phi_of_least_distinct {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S)
    (hj : TwoPartJoin (orbitLevels' F base) 0 1) : ρ = Constants.phi :=
  phi_of_similarity_adjacentJoin hρ base ((adjacentJoin_iff_twoPartJoin _).2 hj)

/-- The lag-two ladder is a distinct pair that is not least, and its ratio is
not `φ` (row 4). -/
theorem lag_two_distinct_not_least : (0 : ℕ) < 2 ∧ ¬ (2 ≤ 1) ∧
    Constants.phi ^ 3 ≠ Constants.phi ^ 2 + 1 :=
  ⟨by norm_num, by norm_num, phi_not_lag_two⟩

/-! ## Certificate -/

structure Cert : Prop where
  /-- Row 4's lag joins are the `a = 0` two-part joins. -/
  lag_is_twoPart : ∀ (s : ℕ → ℝ) (k : ℕ), LagJoin s k ↔ TwoPartJoin s 0 k
  /-- Equal parts give a root of two. -/
  equal_parts_root_two : ∀ (F : ClosedObservableFramework) (ρ : ℝ) (base : F.S) (b : ℕ),
    (∀ s, F.r (F.T s) = ρ * F.r s) → TwoPartJoin (orbitLevels' F base) b b → ρ ^ (b + 1) = 2
  /-- Doubling is the equal-part join at lag zero. -/
  doubling_is_equal : TwoPartJoin (fun n => (2 : ℝ) ^ n) 0 0
  /-- `φ` is never an equal-part ratio. -/
  phi_not_equal : ∀ b : ℕ, Constants.phi ^ (b + 1) ≠ 2
  /-- Distinct parts of least count force `φ`. -/
  phi_of_distinct_least : ∀ (F : ClosedObservableFramework) (ρ : ℝ) (base : F.S),
    (∀ s, F.r (F.T s) = ρ * F.r s) → TwoPartJoin (orbitLevels' F base) 0 1 → ρ = Constants.phi
  /-- The lag-two ladder is distinct, not least, not `φ`. -/
  lag_two : (0 : ℕ) < 2 ∧ ¬ (2 ≤ 1) ∧ Constants.phi ^ 3 ≠ Constants.phi ^ 2 + 1

theorem cert : Cert where
  lag_is_twoPart := lagJoin_iff_twoPartJoin
  equal_parts_root_two := fun _ _ base b hρ hj => equalLag_ratio hρ base b hj
  doubling_is_equal := doubling_equalLag
  phi_not_equal := phi_not_equalLag
  phi_of_distinct_least := fun _ _ base hρ hj => phi_of_least_distinct hρ base hj
  lag_two := lag_two_distinct_not_least

end

end RowA2Join
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
