import Mathlib

/-!
# RS-Coupled Axes

Infrastructure for cross-domain combination theorems.

The main point is that two finite axes of the same cardinality are not
automatically independent. In RS they count as independent only when they are
tagged by different recognition primitives.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace RSCoupledAxis

/-- The five RS primitives used to tag domain axes. -/
inductive RSPrimitive where
  | jCost
  | phiLadder
  | sigmaCharge
  | q3Lattice
  | gap45
  deriving DecidableEq, Repr, Fintype

theorem rsPrimitive_count : Fintype.card RSPrimitive = 5 := by
  decide

/-- A finite domain axis, tagged by the RS primitive that carries its meaning. -/
structure CoupledAxis (n : ℕ) where
  Ix : Type
  finite : Fintype Ix
  card_eq : @Fintype.card Ix finite = n
  primitive : RSPrimitive

/-- RS-independence means the axes are carried by different primitives. -/
def independent {n m : ℕ} (A : CoupledAxis n) (B : CoupledAxis m) : Prop :=
  A.primitive ≠ B.primitive

/-- Pairwise independent triple of same-size axes. -/
structure RSIndependentTriple (n : ℕ) where
  axis1 : CoupledAxis n
  axis2 : CoupledAxis n
  axis3 : CoupledAxis n
  indep12 : independent axis1 axis2
  indep13 : independent axis1 axis3
  indep23 : independent axis2 axis3

/-- Pairwise independent disjoint sum of same-size axes. -/
structure RSDisjointSum3 (n : ℕ) where
  axis1 : CoupledAxis n
  axis2 : CoupledAxis n
  axis3 : CoupledAxis n
  indep12 : independent axis1 axis2
  indep13 : independent axis1 axis3
  indep23 : independent axis2 axis3

/-- Product of the cardinalities of three same-size RS-independent axes. -/
def tripleProductCard {n : ℕ} (T : RSIndependentTriple n) : ℕ :=
  @Fintype.card T.axis1.Ix T.axis1.finite *
    @Fintype.card T.axis2.Ix T.axis2.finite *
    @Fintype.card T.axis3.Ix T.axis3.finite

/-- The tensor-product count of three same-size RS-independent axes is n^3. -/
theorem triple_card {n : ℕ} (T : RSIndependentTriple n) :
    tripleProductCard T = n * n * n := by
  unfold tripleProductCard
  rw [T.axis1.card_eq, T.axis2.card_eq, T.axis3.card_eq]

/-- Cardinality of the disjoint sum of three same-size RS-independent axes. -/
theorem disjoint_sum_card {n : ℕ} (S : RSDisjointSum3 n) :
    @Fintype.card S.axis1.Ix S.axis1.finite +
      @Fintype.card S.axis2.Ix S.axis2.finite +
      @Fintype.card S.axis3.Ix S.axis3.finite = 3 * n := by
  rw [S.axis1.card_eq, S.axis2.card_eq, S.axis3.card_eq]
  ring

/-- The gap-45 complexity ceiling. -/
def gap45 : ℕ := 45

theorem gap45_eq : gap45 = 45 := rfl

end RSCoupledAxis
end Foundation
end IndisputableMonolith
