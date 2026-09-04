import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.KernelClosure.CutsetRowA2Join

/-!
# Cutset A2, the cost of the join: distinct parts are the costly join

## The sentence

Row 4's remaining word (`CutsetRowA2Join`): a level is the join of two *distinct*
earlier levels, `TwoPartJoin s a b` with `a < b`. The equal-part join (`a = b`) is
coherent: a root-of-two ladder, never `φ`.

## The new object

The two parts of a join stand in a ratio, and that ratio has a recognition cost:
`joinCost s a b n = J (s (n + (b - a)) / s n)`, the cost the join posts as a
comparison of its own two sides. Two floor facts decide it: `J 1 = 0` (balance
costs nothing) and `J x > 0` for `x ≠ 1`.

* Equal parts: the ratio is `1` and the join cost is `0`, at every lag
  (`joinCost_equal_zero`). The join compares two equal sides and posts nothing.
* Distinct parts: under similarity the ratio is `ρ^(b-a)` with `ρ > 1`; growth is
  derived from the join itself (`twoPartJoin_growth`), so the ratio is not `1` and
  the join cost is positive (`joinCost_distinct_pos`).
* So a join is costly iff its parts are distinct (`costly_iff_distinct`).

## What this locates

The equal-part alternative is not a world without hierarchy; it is the theory's
own other ladder. The floor tower's scale ladder `2^F` (a cell of the floor above
is two cells below) is the lag-zero equal-part join (`doubling_equalLag`) and its
join cost is `0` (`tower_join_balanced`): the balanced, cost-free ladder. Space is
the cost-free join; the rung ladder is the costly one.

## What remains

The word moves. Before: "a hierarchy's levels are distinct". After: "a level's
join is a recognition" (its two sides are compared at a cost); "distinct" is then
a theorem of `J 1 = 0`. That a rung of the recognition hierarchy is a recognition
is what the ladder is; it is still a definition, and the ledger row says so. The
row 4 tag does not change; its sentence gets shorter and its alternative gets a
name inside the theory.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace RowA2JoinCost

open ClosedFramework LadderCensus Row4Ladder Row4Ledger RowA2Join

noncomputable section

/-! ## The ratio and the cost of a join -/

/-- The ratio between the two parts of the join at level `n`: the part `b - a`
levels above `n` against the part at `n`. -/
def joinRatio (s : ℕ → ℝ) (a b n : ℕ) : ℝ := s (n + (b - a)) / s n

/-- The recognition cost the join posts as a comparison of its two sides. -/
def joinCost (s : ℕ → ℝ) (a b n : ℕ) : ℝ := Cost.Jcost (joinRatio s a b n)

/-! ## Equal parts are balanced -/

/-- G1. Equal parts have ratio one. -/
theorem joinRatio_equal (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (b n : ℕ) :
    joinRatio s b b n = 1 := by
  unfold joinRatio
  rw [Nat.sub_self, Nat.add_zero]
  exact div_self (hs n).ne'

/-- G2. **Equal parts cost nothing as a join**, at every lag. -/
theorem joinCost_equal_zero (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (b n : ℕ) :
    joinCost s b b n = 0 := by
  unfold joinCost
  rw [joinRatio_equal s hs b n]
  exact Cost.Jcost_unit0

/-! ## Growth is derived from the join -/

/-- G3. **A two-part join grows.** Under similarity, any two-part join forces
`1 < ρ`: the new level exceeds its larger part. -/
theorem twoPartJoin_growth {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (a b : ℕ)
    (hj : TwoPartJoin (orbitLevels' F base) a b) : 1 < ρ := by
  have h := hj 0
  simp only [zero_add] at h
  rw [similarity_levels_pow hρ base (b + 1), similarity_levels_pow hρ base (b - a)] at h
  have h0 := orbitLevels_pos F base 0
  have hρpos := similarity_ratio_pos hρ base
  by_contra hle
  push_neg at hle
  have hpow : ρ ^ (b + 1) ≤ ρ ^ (b - a) :=
    pow_le_pow_of_le_one hρpos.le hle (by omega)
  have : ρ ^ (b + 1) * orbitLevels' F base 0 ≤ ρ ^ (b - a) * orbitLevels' F base 0 :=
    mul_le_mul_of_nonneg_right hpow h0.le
  linarith

/-! ## Distinct parts are costly -/

/-- Under similarity the join ratio is `ρ^(b-a)`. -/
theorem joinRatio_similarity {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (a b n : ℕ) :
    joinRatio (orbitLevels' F base) a b n = ρ ^ (b - a) := by
  unfold joinRatio
  rw [similarity_levels_pow hρ base (n + (b - a)), similarity_levels_pow hρ base n, pow_add]
  have h0 := (orbitLevels_pos F base 0).ne'
  have hρ0 := (similarity_ratio_pos hρ base).ne'
  field_simp

/-- G4. **Distinct parts cost.** -/
theorem joinCost_distinct_pos {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (a b n : ℕ)
    (hj : TwoPartJoin (orbitLevels' F base) a b) (hab : a < b) :
    0 < joinCost (orbitLevels' F base) a b n := by
  unfold joinCost
  rw [joinRatio_similarity hρ base a b n]
  have hρ1 := twoPartJoin_growth hρ base a b hj
  have hpos : 0 < ρ ^ (b - a) := by positivity
  apply Cost.Jcost_pos_of_ne_one _ hpos
  have : 1 < ρ ^ (b - a) := one_lt_pow₀ hρ1 (by omega)
  exact this.ne'

/-- G5. **A join is costly iff its parts are distinct.** -/
theorem costly_iff_distinct {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (a b n : ℕ) (hab : a ≤ b)
    (hj : TwoPartJoin (orbitLevels' F base) a b) :
    0 < joinCost (orbitLevels' F base) a b n ↔ a < b := by
  constructor
  · intro hpos
    rcases hab.lt_or_eq with h | h
    · exact h
    · subst h
      rw [joinCost_equal_zero _ (orbitLevels_pos F base) a n] at hpos
      exact absurd hpos (lt_irrefl 0)
  · exact joinCost_distinct_pos hρ base a b n hj

/-! ## The tower is the balanced ladder -/

/-- G6. **The floor tower's scale ladder is a balanced join.** `2^F` is the
lag-zero equal-part join and its join cost is zero: space's floor step is the
cost-free join. -/
theorem tower_join_balanced (n : ℕ) : joinCost (fun F => (2 : ℝ) ^ F) 0 0 n = 0 :=
  joinCost_equal_zero _ (fun _ => by positivity) 0 n

/-! ## Decoys -/

/-- Planted positive: the adjacent join under similarity has ratio `φ` and cost
`J φ > 0`. -/
theorem adjacent_join_cost_pos {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (n : ℕ)
    (hj : TwoPartJoin (orbitLevels' F base) 0 1) :
    joinRatio (orbitLevels' F base) 0 1 n = Constants.phi ∧
      0 < joinCost (orbitLevels' F base) 0 1 n := by
  have hphi := phi_of_least_distinct hρ base hj
  refine ⟨?_, joinCost_distinct_pos hρ base 0 1 n hj (by norm_num)⟩
  rw [joinRatio_similarity hρ base 0 1 n, hphi]
  simp

/-- The lag-two distinct join passes this blade (cost positive) and is excluded
only by least count, as in row 4: the blade is about distinctness alone. -/
theorem lag_two_costly {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (n : ℕ)
    (hj : TwoPartJoin (orbitLevels' F base) 0 2) :
    0 < joinCost (orbitLevels' F base) 0 2 n :=
  joinCost_distinct_pos hρ base 0 2 n hj (by norm_num)

/-- Empty case: a ladder without growth admits no two-part join at all, so the
gate has nothing to pass there (excluded upstream, not passed vacuously). -/
theorem no_join_without_growth {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (a b : ℕ) (hle : ρ ≤ 1) :
    ¬ TwoPartJoin (orbitLevels' F base) a b :=
  fun hj => absurd (twoPartJoin_growth hρ base a b hj) (not_lt.mpr hle)

/-! ## Certificate -/

structure Cert : Prop where
  /-- Equal parts have ratio one. -/
  equal_ratio_one : ∀ (s : ℕ → ℝ), (∀ n, 0 < s n) → ∀ b n, joinRatio s b b n = 1
  /-- Equal parts cost nothing as a join. -/
  equal_cost_zero : ∀ (s : ℕ → ℝ), (∀ n, 0 < s n) → ∀ b n, joinCost s b b n = 0
  /-- A two-part join grows. -/
  growth : ∀ (F : ClosedObservableFramework) (ρ : ℝ) (base : F.S) (a b : ℕ),
    (∀ s, F.r (F.T s) = ρ * F.r s) → TwoPartJoin (orbitLevels' F base) a b → 1 < ρ
  /-- Distinct parts cost. -/
  distinct_cost_pos : ∀ (F : ClosedObservableFramework) (ρ : ℝ) (base : F.S) (a b n : ℕ),
    (∀ s, F.r (F.T s) = ρ * F.r s) → TwoPartJoin (orbitLevels' F base) a b → a < b →
      0 < joinCost (orbitLevels' F base) a b n
  /-- A join is costly iff its parts are distinct. -/
  costly_iff : ∀ (F : ClosedObservableFramework) (ρ : ℝ) (base : F.S) (a b n : ℕ), a ≤ b →
    (∀ s, F.r (F.T s) = ρ * F.r s) → TwoPartJoin (orbitLevels' F base) a b →
      (0 < joinCost (orbitLevels' F base) a b n ↔ a < b)
  /-- The tower's scale ladder is the balanced join. -/
  tower_balanced : TwoPartJoin (fun n => (2 : ℝ) ^ n) 0 0 ∧
    ∀ n, joinCost (fun F => (2 : ℝ) ^ F) 0 0 n = 0
  /-- Planted positive: the adjacent join has ratio `φ` and positive cost. -/
  adjacent : ∀ (F : ClosedObservableFramework) (ρ : ℝ) (base : F.S) (n : ℕ),
    (∀ s, F.r (F.T s) = ρ * F.r s) → TwoPartJoin (orbitLevels' F base) 0 1 →
      joinRatio (orbitLevels' F base) 0 1 n = Constants.phi ∧
        0 < joinCost (orbitLevels' F base) 0 1 n
  /-- Empty case excluded upstream: no growth, no join. -/
  no_join_no_growth : ∀ (F : ClosedObservableFramework) (ρ : ℝ) (base : F.S) (a b : ℕ),
    (∀ s, F.r (F.T s) = ρ * F.r s) → ρ ≤ 1 → ¬ TwoPartJoin (orbitLevels' F base) a b

theorem cert : Cert where
  equal_ratio_one := joinRatio_equal
  equal_cost_zero := joinCost_equal_zero
  growth := fun _ _ base a b hρ hj => twoPartJoin_growth hρ base a b hj
  distinct_cost_pos := fun _ _ base a b n hρ hj hab => joinCost_distinct_pos hρ base a b n hj hab
  costly_iff := fun _ _ base a b n hab hρ hj => costly_iff_distinct hρ base a b n hab hj
  tower_balanced := ⟨doubling_equalLag, tower_join_balanced⟩
  adjacent := fun _ _ base n hρ hj => adjacent_join_cost_pos hρ base n hj
  no_join_no_growth := fun _ _ base a b hρ hle => no_join_without_growth hρ base a b hle

end

end RowA2JoinCost
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
