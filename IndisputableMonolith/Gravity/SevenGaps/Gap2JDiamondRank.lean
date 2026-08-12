import IndisputableMonolith.Gravity.SevenGaps.Gap2JEhrhartSpan

/-!
# Gap 2 / C15: the J-diamond rank lattice

`Gap2JEhrhartSpan` killed the census-inversion route to the three per-kind rates:
the recognition cost `J` built from vertex-level ledger imbalance has no fixed
kind totals, is not a valuation, and its moment vector lies outside the census
span.  This module runs the successor test that A15 named and did not build: the
rank and consistency test on **J-diamonds**, the four-term inclusion-exclusion
defect of `J` on overlapping regions.

## §1. What a J-diamond is

A **subcomplex** of a posting graph is a subset of its edges together with a
vertex subset closed under their endpoints.  A **J-diamond** on `K` is an
unordered pair of proper subcomplexes whose union is `K`; it is the stand-off
between two accumulation orders of the same complex: evaluate `J` directly on
`K`, or evaluate it on the two sides and subtract the interface (the
inclusion-exclusion order).  The **diamond defect** is the four-term difference

    D(A, B; I)  =  SJ(A) + SJ(B) - SJ(I) - SJ(K),

where `SJ = 2 * kappa * J` is the integer squared-imbalance total.  A valuation
has `D = 0` on every diamond; `J` is not a valuation (A15), so defects are
nonzero in general.  The A15 witness, two edges glued along one vertex with
defect `1 / kappa`, is the smallest nonzero diamond (`seed_diamond_defect`,
`diamond_J_seed`).

## §2. The defect is the interface imbalance coupling (the localization theorem)

The main theorem, `diamondDefect_eq_neg_two_inner`: for an edge-partition of `K`
into two subcomplexes, the defect factors through the two imbalance fields as

    D  =  -2 * sum over interface vertices v of m_A(v) * m_B(v).

Two consequences.  Gluing along an empty interface is always exact
(`diamondDefect_eq_zero_of_inter_empty`), so disjoint union never fails
inclusion-exclusion.  And a diamond whose interface carries no two-sided
imbalance cannot fail (`diamondDefect_eq_zero_of_interface_balanced`): the
gluing asymmetry of `J` accrues only where the ledger imbalance lives.  The
panel's Euler-gauge lemma says the boundary strata are the only unexcluded
domicile for asymmetry; this is an independent, finite proof of the same
localization content for posting-graph diamonds, not a re-proof of the Pachner
statement.  A parity consequence of the same algebra: `SJ(K)` is always even
(`imbalanceSq_even`), matching the measured defect spectrum, which is supported
on even integers.

## §5-§6. The relation lattice and its rank

Each accumulation order of each complex at the smallest caps gives one row
`a . C = b` on the scaled rate triple `C = 2 * kappa * (c_V, c_E, c_T)`: `a` is
the count vector of the complex produced (identical for the two orders of a
diamond, since counts are valuations) and `b` is the measured accumulated cost.
The rows were enumerated exactly at caps 1 to 4
(`scripts/qg/qg_j_diamond_rank_20260730.py`, receipt
`scripts/qg/out/j_diamond_rank_20260730.json`; MEASURED).  The kernel checks the
decisive finite facts:

* the left-hand rank is exactly 2 (`lattice_lhs_rank_two`): every measured row
  has zero `c_T` coefficient, because `J` charges top-cell letters nothing
  (`jCost_tet`), so the tet rate direction is structurally invisible to every
  J-relation;
* the augmented rank is 3 (`seed_augmented_independent`), so the right-hand
  sides carry information the left-hand side cannot: the system is
  **inconsistent**, and the four seed rows already show it
  (`lattice_inconsistent_seed`: the two orders of the A15 diamond demand
  `3 C_V + 2 C_E = 2` and `= 4` at once);
* the conflict precedes any gluing: the count vector `(2, 1, 0)` is carried by
  two complexes with different costs (`jCost_not_a_function_of_counts`), so `J`
  is not a function of the three counts at all.

**Verdict (scoped).**  Outcome three of the C15 charge fires: inconsistent RHS,
so the vertex-imbalance `J` induces no additive letter cost, with the A15
diamond as the exhibited witness.  The lattice rank is 2, the augmented rank 3.
The scope is exactly the J-relation lattice at the enumerated caps: it says
nothing about referents other than vertex-level imbalance (C12's oriented-face
route is untouched), and it does not claim the rates are underivable in general.

## §7. Measured tallies

Cap-by-cap enumeration tallies are mirrored as rational data with provenance,
and each decisive tally is restated as a kernel-checked fact
(`measured_rank_cap4`, `measured_bilinear_perfect`,
`measured_no_localization_violations`).  The positive control in the script (a
genuinely additive statistic through the same machinery) returns a consistent
system with the right solution, so the instrument discriminates.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2JDiamondRank

open PathSumMeasure GaugeHistoryMeasure Gap2PostingCostDerivation Gap2JEhrhartSpan

variable {B : ℕ}

/-! ## §1. Subcomplexes, the sub-imbalance, and the diamond defect -/

/-- A **subcomplex** of a bounded complex: a subset of the edges together with a
vertex subset closed under their endpoints. -/
structure Subcomplex (K : BoundedComplex B) where
  verts : Finset (Fin K.nV)
  edges : Finset (Fin K.nE)
  tail_mem : ∀ e ∈ edges, (K.edgeVerts e).1 ∈ verts
  head_mem : ∀ e ∈ edges, (K.edgeVerts e).2 ∈ verts

/-- In-postings of a vertex within an edge subset. -/
def subIndeg (K : BoundedComplex B) (E : Finset (Fin K.nE)) (v : Fin K.nV) : ℕ :=
  (E.filter fun e => (K.edgeVerts e).2 = v).card

/-- Out-postings of a vertex within an edge subset. -/
def subOutdeg (K : BoundedComplex B) (E : Finset (Fin K.nE)) (v : Fin K.nV) : ℕ :=
  (E.filter fun e => (K.edgeVerts e).1 = v).card

/-- The imbalance an edge subset assigns to a vertex: its own in-postings minus
its own out-postings.  Vanishes off the vertex set of any subcomplex owning the
edges, by endpoint closure. -/
def subImbalance (K : BoundedComplex B) (E : Finset (Fin K.nE)) (v : Fin K.nV) : ℤ :=
  (subIndeg K E v : ℤ) - (subOutdeg K E v : ℤ)

/-- The integer recognition charge of a subcomplex: the squared-imbalance total
over its vertices.  In units of `1 / (2 * kappa)` this is its `J`. -/
def subCharge (K : BoundedComplex B) (S : Subcomplex K) : ℤ :=
  ∑ v ∈ S.verts, (subImbalance K S.edges v) ^ 2

/-- The **diamond defect** of a pair of subcomplexes: the four-term
inclusion-exclusion defect `SJ(A) + SJ(B) - SJ(I) - SJ(K)`, where the interface
charge is written explicitly so the definition needs no disjointness. -/
def diamondDefect (K : BoundedComplex B) (A Bd : Subcomplex K) : ℤ :=
  subCharge K A + subCharge K Bd
    - (∑ v ∈ A.verts ∩ Bd.verts, (subImbalance K (A.edges ∩ Bd.edges) v) ^ 2)
    - imbalanceSq K

theorem subImbalance_eq_zero_of_not_mem (K : BoundedComplex B) (S : Subcomplex K)
    {v : Fin K.nV} (hv : v ∉ S.verts) :
    subImbalance K S.edges v = 0 := by
  classical
  have h1 : ∀ e ∈ S.edges, (K.edgeVerts e).2 ≠ v := by
    intro e he hh
    exact hv (hh ▸ S.head_mem e he)
  have h2 : ∀ e ∈ S.edges, (K.edgeVerts e).1 ≠ v := by
    intro e he hh
    exact hv (hh ▸ S.tail_mem e he)
  unfold subImbalance subIndeg subOutdeg
  rw [Finset.filter_eq_empty_iff.mpr h1, Finset.filter_eq_empty_iff.mpr h2]
  simp

/-- **Edge-partition additivity.**  Splitting the edge set splits the imbalance
at every vertex: each posting lands on exactly one side. -/
theorem subImbalance_union (K : BoundedComplex B) {A Bd : Finset (Fin K.nE)}
    (h : Disjoint A Bd) (v : Fin K.nV) :
    subImbalance K (A ∪ Bd) v = subImbalance K A v + subImbalance K Bd v := by
  classical
  unfold subImbalance subIndeg subOutdeg
  rw [Finset.filter_union, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) h),
    Finset.card_union_of_disjoint
      (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) h)]
  push_cast
  ring

/-! ## §2. The localization theorem: the defect is the interface imbalance coupling -/

/-- **THEOREM (the diamond defect is the interface imbalance coupling).**  For an
edge-partition of `K` into two subcomplexes, the four-term defect equals minus
twice the inner product of the two imbalance fields, summed over the interface.
In particular the defect is supported where both sides carry imbalance. -/
theorem diamondDefect_eq_neg_two_inner (K : BoundedComplex B) (A Bd : Subcomplex K)
    (he : A.edges ∪ Bd.edges = Finset.univ) (hd : Disjoint A.edges Bd.edges) :
    diamondDefect K A Bd
      = -2 * ∑ v ∈ A.verts ∩ Bd.verts,
          subImbalance K A.edges v * subImbalance K Bd.edges v := by
  classical
  have hI : A.edges ∩ Bd.edges = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd
  have key : ∀ v : Fin K.nV, vertexImbalance K v
      = subImbalance K A.edges v + subImbalance K Bd.edges v := by
    intro v
    have hu : subImbalance K Finset.univ v
        = subImbalance K A.edges v + subImbalance K Bd.edges v := by
      rw [← he]
      exact subImbalance_union K hd v
    exact hu
  have hsK : imbalanceSq K
      = ∑ v : Fin K.nV, (subImbalance K A.edges v + subImbalance K Bd.edges v) ^ 2 := by
    show (∑ v : Fin K.nV, (vertexImbalance K v) ^ 2) = _
    exact Finset.sum_congr rfl (fun v _ => by rw [key v])
  have supp : ∀ (S : Subcomplex K),
      (∑ v : Fin K.nV, (subImbalance K S.edges v) ^ 2) = subCharge K S := by
    intro S
    show (∑ v : Fin K.nV, (subImbalance K S.edges v) ^ 2)
      = ∑ v ∈ S.verts, (subImbalance K S.edges v) ^ 2
    exact (Finset.sum_subset (Finset.subset_univ S.verts) (fun x _ hx => by
      rw [subImbalance_eq_zero_of_not_mem K S hx]
      norm_num)).symm
  have prodsupp :
      (∑ v : Fin K.nV, subImbalance K A.edges v * subImbalance K Bd.edges v)
        = ∑ v ∈ A.verts ∩ Bd.verts,
            subImbalance K A.edges v * subImbalance K Bd.edges v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    rw [Finset.mem_inter, not_and] at hx
    by_cases hA : x ∈ A.verts
    · have hB : x ∉ Bd.verts := hx hA
      rw [subImbalance_eq_zero_of_not_mem K Bd hB, mul_zero]
    · rw [subImbalance_eq_zero_of_not_mem K A hA, zero_mul]
  have hIz : (∑ v ∈ A.verts ∩ Bd.verts,
      (subImbalance K (∅ : Finset (Fin K.nE)) v) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    have hz : subImbalance K (∅ : Finset (Fin K.nE)) v = 0 := by
      simp [subImbalance, subIndeg, subOutdeg]
    rw [hz]
    norm_num
  have mid : (∑ v : Fin K.nV, 2 * subImbalance K A.edges v * subImbalance K Bd.edges v)
      = 2 * (∑ v : Fin K.nV, subImbalance K A.edges v * subImbalance K Bd.edges v) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => mul_assoc _ _ _)
  have expand : (∑ v : Fin K.nV, (subImbalance K A.edges v + subImbalance K Bd.edges v) ^ 2)
      = (∑ v : Fin K.nV, (subImbalance K A.edges v) ^ 2)
        + (∑ v : Fin K.nV, (subImbalance K Bd.edges v) ^ 2)
        + 2 * (∑ v : Fin K.nV, subImbalance K A.edges v * subImbalance K Bd.edges v) := by
    rw [Finset.sum_congr rfl (fun v _ => add_sq _ _)]
    simp only [Finset.sum_add_distrib]
    rw [mid]
    ring
  unfold diamondDefect
  rw [hI, hIz, sub_zero, hsK, ← supp A, ← supp Bd, expand, prodsupp]
  ring

/-- **Empty interface, exact gluing.**  A disjoint union never fails
inclusion-exclusion: there is no shared vertex for the two imbalance fields to
meet at. -/
theorem diamondDefect_eq_zero_of_inter_empty (K : BoundedComplex B) (A Bd : Subcomplex K)
    (he : A.edges ∪ Bd.edges = Finset.univ) (hd : Disjoint A.edges Bd.edges)
    (hi : A.verts ∩ Bd.verts = ∅) :
    diamondDefect K A Bd = 0 := by
  rw [diamondDefect_eq_neg_two_inner K A Bd he hd, hi, Finset.sum_empty, mul_zero]

/-- **The localization, Euler-gauge form.**  A diamond whose interface carries no
two-sided imbalance cannot fail.  The gluing asymmetry of `J` accrues only where
the ledger imbalance lives: the boundary strata are the only domicile for the
defect, which is the localization content of the panel's Euler-gauge lemma,
proved here independently and finitely for posting-graph diamonds. -/
theorem diamondDefect_eq_zero_of_interface_balanced (K : BoundedComplex B)
    (A Bd : Subcomplex K)
    (he : A.edges ∪ Bd.edges = Finset.univ) (hd : Disjoint A.edges Bd.edges)
    (hb : ∀ v ∈ A.verts ∩ Bd.verts,
      subImbalance K A.edges v = 0 ∨ subImbalance K Bd.edges v = 0) :
    diamondDefect K A Bd = 0 := by
  rw [diamondDefect_eq_neg_two_inner K A Bd he hd]
  rw [Finset.sum_eq_zero (fun v hv => by
    obtain h | h := hb v hv
    · rw [h, zero_mul]
    · rw [h, mul_zero])]
  ring

/-! ## §3. The spectrum is even

Every edge contributes one debit and one credit, so the imbalances sum to zero,
and a sum of squares of integers summing to zero is even.  The measured defect
spectrum at caps 2 to 4 is supported on even integers, exactly as this forces. -/

/-- **The imbalance fields sum to zero.**  Each posting debits one vertex and
credits one, so the totals cancel vertex by vertex summed over all vertices. -/
theorem sum_vertexImbalance (K : BoundedComplex B) :
    (∑ v : Fin K.nV, vertexImbalance K v) = 0 := by
  classical
  have headsum : ∀ e : Fin K.nE,
      (∑ v : Fin K.nV, (if (K.edgeVerts e).2 = v then (1 : ℤ) else 0)) = 1 := by
    intro e
    rw [Finset.sum_ite_eq Finset.univ (K.edgeVerts e).2 (fun _ => (1 : ℤ))]
    simp
  have tailsum : ∀ e : Fin K.nE,
      (∑ v : Fin K.nV, (if (K.edgeVerts e).1 = v then (1 : ℤ) else 0)) = 1 := by
    intro e
    rw [Finset.sum_ite_eq Finset.univ (K.edgeVerts e).1 (fun _ => (1 : ℤ))]
    simp
  have h2 : (∑ v : Fin K.nV, ((Finset.univ.filter fun e => (K.edgeVerts e).2 = v).card : ℤ))
      = (K.nE : ℤ) := by
    simp only [Finset.card_filter]
    push_cast
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun e _ => headsum e)]
    simp
  have h1 : (∑ v : Fin K.nV, ((Finset.univ.filter fun e => (K.edgeVerts e).1 = v).card : ℤ))
      = (K.nE : ℤ) := by
    simp only [Finset.card_filter]
    push_cast
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun e _ => tailsum e)]
    simp
  unfold vertexImbalance indeg outdeg
  rw [Finset.sum_sub_distrib, h2, h1, sub_self]

/-- **THEOREM (the charge spectrum is even).**  `SJ(K)` is divisible by two for
every bounded complex, matching the measured defect histograms, whose support is
entirely even. -/
theorem imbalanceSq_even (K : BoundedComplex B) : 2 ∣ imbalanceSq K := by
  have hsum := sum_vertexImbalance K
  have h : (∑ v : Fin K.nV, (vertexImbalance K v) ^ 2)
      = (∑ v : Fin K.nV, (vertexImbalance K v) ^ 2)
        - (∑ v : Fin K.nV, vertexImbalance K v) := by rw [hsum, sub_zero]
  have hsq : imbalanceSq K
      = ∑ v : Fin K.nV, (vertexImbalance K v * (vertexImbalance K v - 1)) := by
    show (∑ v : Fin K.nV, (vertexImbalance K v) ^ 2) = _
    rw [h, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  rw [hsq]
  apply Finset.dvd_sum
  intro v _
  rcases Int.even_or_odd (vertexImbalance K v) with h | h
  · obtain ⟨k, hk⟩ := h
    exact ⟨k * (k + k - 1), by rw [hk]; ring⟩
  · obtain ⟨k, hk⟩ := h
    exact ⟨(2 * k + 1) * k, by rw [hk]; ring⟩

/-! ## §4. The explicit witnesses at cap 4

The A15 complexes (`pointComplex`, `edgeComplex`, `pathComplex`, `twoEdgeComplex`)
plus four more: the two-edge out-fork, the three-edge path, the three-edge
out-star, and the loop with an isolated vertex (the second carrier of the count
vector `(2, 1, 0)`). -/

/-- A two-edge out-fork `1 <- 0 -> 2`. -/
def forkComplex : BoundedComplex 4 where
  nV := 3
  nE := 2
  nT := 0
  hV := by decide
  hE := by decide
  hT := by decide
  edgeVerts := fun e => if e = 0 then (0, 1) else (0, 2)
  tetVerts := fun t => t.elim0

/-- A three-edge path `0 -> 1 -> 2 -> 3`. -/
def threePathComplex : BoundedComplex 4 where
  nV := 4
  nE := 3
  nT := 0
  hV := by decide
  hE := by decide
  hT := by decide
  edgeVerts := fun e => if e = 0 then (0, 1) else if e = 1 then (1, 2) else (2, 3)
  tetVerts := fun t => t.elim0

/-- A three-edge out-star `0 -> 1`, `0 -> 2`, `0 -> 3`. -/
def outStarComplex : BoundedComplex 4 where
  nV := 4
  nE := 3
  nT := 0
  hV := by decide
  hE := by decide
  hT := by decide
  edgeVerts := fun e => if e = 0 then (0, 1) else if e = 1 then (0, 2) else (0, 3)
  tetVerts := fun t => t.elim0

/-- One loop at vertex `0` with one isolated vertex.  Its count vector is
`(2, 1, 0)`, the same as the proper edge, but every posting balances at its own
vertex, so it pays nothing. -/
def loopPointComplex : BoundedComplex 4 where
  nV := 2
  nE := 1
  nT := 0
  hV := by decide
  hE := by decide
  hT := by decide
  edgeVerts := fun _ => (0, 0)
  tetVerts := fun t => t.elim0

theorem imbalance_fork_zero : vertexImbalance forkComplex (0 : Fin 3) = -2 := by decide

theorem imbalance_fork_one : vertexImbalance forkComplex (1 : Fin 3) = 1 := by decide

theorem imbalance_fork_two : vertexImbalance forkComplex (2 : Fin 3) = 1 := by decide

theorem imbalance_threePath_zero : vertexImbalance threePathComplex (0 : Fin 4) = -1 := by decide

theorem imbalance_threePath_one : vertexImbalance threePathComplex (1 : Fin 4) = 0 := by decide

theorem imbalance_threePath_two : vertexImbalance threePathComplex (2 : Fin 4) = 0 := by decide

theorem imbalance_threePath_three : vertexImbalance threePathComplex (3 : Fin 4) = 1 := by decide

theorem imbalance_outStar_zero : vertexImbalance outStarComplex (0 : Fin 4) = -3 := by decide

theorem imbalance_outStar_one : vertexImbalance outStarComplex (1 : Fin 4) = 1 := by decide

theorem imbalance_outStar_two : vertexImbalance outStarComplex (2 : Fin 4) = 1 := by decide

theorem imbalance_outStar_three : vertexImbalance outStarComplex (3 : Fin 4) = 1 := by decide

theorem imbalance_twoEdge_zero : vertexImbalance twoEdgeComplex (0 : Fin 4) = -1 := by decide

theorem imbalance_twoEdge_one : vertexImbalance twoEdgeComplex (1 : Fin 4) = 1 := by decide

theorem imbalance_twoEdge_two : vertexImbalance twoEdgeComplex (2 : Fin 4) = -1 := by decide

theorem imbalance_twoEdge_three : vertexImbalance twoEdgeComplex (3 : Fin 4) = 1 := by decide

theorem imbalance_loopPoint_zero : vertexImbalance loopPointComplex (0 : Fin 2) = 0 := by decide

theorem imbalance_loopPoint_one : vertexImbalance loopPointComplex (1 : Fin 2) = 0 := by decide

theorem imbalanceSq_fork : imbalanceSq forkComplex = 6 := by decide

theorem imbalanceSq_threePath : imbalanceSq threePathComplex = 2 := by decide

theorem imbalanceSq_outStar : imbalanceSq outStarComplex = 12 := by decide

theorem imbalanceSq_twoEdge : imbalanceSq twoEdgeComplex = 4 := by decide

theorem imbalanceSq_loopPoint : imbalanceSq loopPointComplex = 0 := by decide

noncomputable section

/-- The history cost of `jCost` is the integer charge over twice the Casimir. -/
theorem historyCost_jCost_eq (kappa : ℝ) (B : ℕ) (K : BoundedComplex B) :
    historyCost (jCost kappa) B K = (imbalanceSq K : ℝ) / (2 * kappa) := by
  rw [historyCost_jCost]
  unfold imbalanceSq
  push_cast
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun v _ => jCost_inl kappa B K v)

theorem historyCost_edge (kappa : ℝ) (hk : kappa ≠ 0) :
    historyCost (jCost kappa) 4 edgeComplex = 1 / kappa := by
  rw [historyCost_jCost, blockSum_edge kappa hk]

theorem historyCost_path (kappa : ℝ) (hk : kappa ≠ 0) :
    historyCost (jCost kappa) 4 pathComplex = 1 / kappa := by
  rw [historyCost_jCost, blockSum_path kappa hk]

theorem historyCost_point (kappa : ℝ) :
    historyCost (jCost kappa) 4 pointComplex = 0 := by
  rw [historyCost_jCost, blockSum_point kappa]

theorem imbalanceSq_emptyComplex : imbalanceSq (emptyComplex 4) = 0 := by decide

theorem historyCost_empty (kappa : ℝ) :
    historyCost (jCost kappa) 4 (emptyComplex 4) = 0 := by
  rw [historyCost_jCost_eq, imbalanceSq_emptyComplex]
  norm_num

theorem blockSum_twoEdge (kappa : ℝ) (hk : kappa ≠ 0) :
    (∑ v : Fin twoEdgeComplex.nV, jCost kappa 4 twoEdgeComplex (Sum.inl v)) = 2 / kappa := by
  show (∑ v : Fin 4, jCost kappa 4 twoEdgeComplex (Sum.inl v)) = 2 / kappa
  rw [Fin.sum_univ_four]
  simp only [jCost_inl, imbalance_twoEdge_zero, imbalance_twoEdge_one,
    imbalance_twoEdge_two, imbalance_twoEdge_three]
  push_cast
  field_simp <;> norm_num

theorem historyCost_twoEdge (kappa : ℝ) (hk : kappa ≠ 0) :
    historyCost (jCost kappa) 4 twoEdgeComplex = 2 / kappa := by
  rw [historyCost_jCost, blockSum_twoEdge kappa hk]

theorem blockSum_fork (kappa : ℝ) (hk : kappa ≠ 0) :
    (∑ v : Fin forkComplex.nV, jCost kappa 4 forkComplex (Sum.inl v)) = 3 / kappa := by
  show (∑ v : Fin 3, jCost kappa 4 forkComplex (Sum.inl v)) = 3 / kappa
  rw [Fin.sum_univ_three]
  simp only [jCost_inl, imbalance_fork_zero, imbalance_fork_one, imbalance_fork_two]
  push_cast
  field_simp <;> norm_num

theorem historyCost_fork (kappa : ℝ) (hk : kappa ≠ 0) :
    historyCost (jCost kappa) 4 forkComplex = 3 / kappa := by
  rw [historyCost_jCost, blockSum_fork kappa hk]

theorem blockSum_threePath (kappa : ℝ) (hk : kappa ≠ 0) :
    (∑ v : Fin threePathComplex.nV, jCost kappa 4 threePathComplex (Sum.inl v)) = 1 / kappa := by
  show (∑ v : Fin 4, jCost kappa 4 threePathComplex (Sum.inl v)) = 1 / kappa
  rw [Fin.sum_univ_four]
  simp only [jCost_inl, imbalance_threePath_zero, imbalance_threePath_one,
    imbalance_threePath_two, imbalance_threePath_three]
  push_cast
  field_simp <;> norm_num

theorem historyCost_threePath (kappa : ℝ) (hk : kappa ≠ 0) :
    historyCost (jCost kappa) 4 threePathComplex = 1 / kappa := by
  rw [historyCost_jCost, blockSum_threePath kappa hk]

theorem blockSum_outStar (kappa : ℝ) (hk : kappa ≠ 0) :
    (∑ v : Fin outStarComplex.nV, jCost kappa 4 outStarComplex (Sum.inl v)) = 6 / kappa := by
  show (∑ v : Fin 4, jCost kappa 4 outStarComplex (Sum.inl v)) = 6 / kappa
  rw [Fin.sum_univ_four]
  simp only [jCost_inl, imbalance_outStar_zero, imbalance_outStar_one,
    imbalance_outStar_two, imbalance_outStar_three]
  push_cast
  field_simp <;> norm_num

theorem historyCost_outStar (kappa : ℝ) (hk : kappa ≠ 0) :
    historyCost (jCost kappa) 4 outStarComplex = 6 / kappa := by
  rw [historyCost_jCost, blockSum_outStar kappa hk]

theorem historyCost_loopPoint (kappa : ℝ) :
    historyCost (jCost kappa) 4 loopPointComplex = 0 := by
  rw [historyCost_jCost]
  show (∑ v : Fin 2, jCost kappa 4 loopPointComplex (Sum.inl v)) = 0
  rw [Fin.sum_univ_two]
  simp only [jCost_inl, imbalance_loopPoint_zero, imbalance_loopPoint_one]
  norm_num

/-- **The seed diamond, exact value.**  The two orders of the A15 witness: two
edges glued along their shared vertex against the two-edge path directly.  The
glued order accumulates `2 / kappa`, the direct order `1 / kappa`, and the defect
is exactly `1 / kappa`.  (A15 proved the two orders differ; this gives the
value.) -/
theorem diamond_J_seed (kappa : ℝ) (hk : kappa ≠ 0) :
    historyCost (jCost kappa) 4 edgeComplex
      + historyCost (jCost kappa) 4 edgeComplex
      - historyCost (jCost kappa) 4 pointComplex
      - historyCost (jCost kappa) 4 pathComplex = 1 / kappa := by
  rw [historyCost_edge kappa hk, historyCost_point kappa, historyCost_path kappa hk]
  field_simp <;> norm_num

/-- **A second diamond, same sign.**  The three-edge path split as its front
two-edge path plus its last edge along the middle vertex: glued `2 / kappa`,
direct `1 / kappa`. -/
theorem diamond_J_threePath (kappa : ℝ) (hk : kappa ≠ 0) :
    historyCost (jCost kappa) 4 pathComplex
      + historyCost (jCost kappa) 4 edgeComplex
      - historyCost (jCost kappa) 4 pointComplex
      - historyCost (jCost kappa) 4 threePathComplex = 1 / kappa := by
  rw [historyCost_path kappa hk, historyCost_edge kappa hk, historyCost_point kappa,
    historyCost_threePath kappa hk]
  field_simp <;> norm_num

/-- **A third diamond, negative.**  The three-edge out-star split as its front
out-fork plus its last edge along the hub: glued `3 / kappa + 1 / kappa`, direct
`6 / kappa`, defect `-2 / kappa`.  Defects come in both signs. -/
theorem diamond_J_outStar (kappa : ℝ) (hk : kappa ≠ 0) :
    historyCost (jCost kappa) 4 forkComplex
      + historyCost (jCost kappa) 4 edgeComplex
      - historyCost (jCost kappa) 4 pointComplex
      - historyCost (jCost kappa) 4 outStarComplex = -2 / kappa := by
  rw [historyCost_fork kappa hk, historyCost_edge kappa hk, historyCost_point kappa,
    historyCost_outStar kappa hk]
  field_simp <;> norm_num

/-- **The control.**  Disjoint union is exact: two disjoint edges accumulate
`2 / kappa` either way.  Not every diamond fails. -/
theorem diamond_J_disjoint (kappa : ℝ) (hk : kappa ≠ 0) :
    historyCost (jCost kappa) 4 edgeComplex
      + historyCost (jCost kappa) 4 edgeComplex
      - historyCost (jCost kappa) 4 (emptyComplex 4)
      - historyCost (jCost kappa) 4 twoEdgeComplex = 0 := by
  rw [historyCost_edge kappa hk, historyCost_empty kappa, historyCost_twoEdge kappa hk]
  field_simp <;> norm_num

/-- **J is not a function of the three counts.**  The count vector `(2, 1, 0)`
is carried by two complexes whose costs differ: the proper edge pays `1 / kappa`,
the loop with an isolated vertex pays nothing.  The lattice conflict therefore
precedes any gluing diamond. -/
theorem jCost_not_a_function_of_counts (kappa : ℝ) (hk : kappa ≠ 0) :
    edgeComplex.nV = loopPointComplex.nV ∧ edgeComplex.nE = loopPointComplex.nE
      ∧ edgeComplex.nT = loopPointComplex.nT
      ∧ historyCost (jCost kappa) 4 edgeComplex
        ≠ historyCost (jCost kappa) 4 loopPointComplex := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [historyCost_edge kappa hk, historyCost_loopPoint kappa]
  exact one_div_ne_zero hk

end

/-! ### The seed diamonds in subcomplex form, with the localization identity checked

Finset union and intersection values do not reduce in the kernel (they carry
nodup proof terms), and finset equality and disjointness decidability route
through quotient instances the kernel cannot unfold, so the cover, disjointness,
and interface facts below are proved propositionally.  Only the sub-imbalance
values, which are filter-and-card computations, are kernel-decided. -/

/-- The left edge of the two-edge path, with its two vertices. -/
def pathLeft : Subcomplex pathComplex where
  verts := ({0, 1} : Finset (Fin 3))
  edges := ({0} : Finset (Fin 2))
  tail_mem := by
    intro e he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_insert_self _ _
  head_mem := by
    intro e he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The right edge of the two-edge path, with its two vertices. -/
def pathRight : Subcomplex pathComplex where
  verts := ({1, 2} : Finset (Fin 3))
  edges := ({1} : Finset (Fin 2))
  tail_mem := by
    intro e he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_insert_self _ _
  head_mem := by
    intro e he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem seed_edges_cover : pathLeft.edges ∪ pathRight.edges = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro e
  fin_cases e <;> simp [pathLeft, pathRight]

theorem seed_edges_disjoint : Disjoint pathLeft.edges pathRight.edges := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  obtain rfl := Finset.mem_singleton.mp (show a ∈ ({0} : Finset (Fin 2)) from ha)
  obtain rfl := Finset.mem_singleton.mp (show b ∈ ({1} : Finset (Fin 2)) from hb)
  exact Fin.zero_ne_one

theorem seed_interface : pathLeft.verts ∩ pathRight.verts = ({1} : Finset (Fin 3)) := by
  ext v
  fin_cases v <;> simp [pathLeft, pathRight]

theorem subImbalance_pathLeft_one :
    subImbalance pathComplex pathLeft.edges (1 : Fin 3) = 1 := by decide

theorem subImbalance_pathRight_one :
    subImbalance pathComplex pathRight.edges (1 : Fin 3) = -1 := by decide

/-- **The seed diamond, kernel-computed.**  The A15 witness in its lattice form:
defect `2` in units of `1 / (2 * kappa)`, i.e. `1 / kappa` in `J` units. -/
theorem seed_diamond_defect : diamondDefect pathComplex pathLeft pathRight = 2 := by
  rw [diamondDefect_eq_neg_two_inner _ _ _ seed_edges_cover seed_edges_disjoint,
    seed_interface, Finset.sum_singleton, subImbalance_pathLeft_one,
    subImbalance_pathRight_one] <;> norm_num

/-- The interface imbalance coupling on the seed: the shared vertex carries
`m_A = 1` and `m_B = -1`, and `-2 * (1 * -1) = 2` is the defect. -/
theorem seed_diamond_localized :
    diamondDefect pathComplex pathLeft pathRight
      = -2 * ∑ v ∈ pathLeft.verts ∩ pathRight.verts,
          subImbalance pathComplex pathLeft.edges v
            * subImbalance pathComplex pathRight.edges v :=
  diamondDefect_eq_neg_two_inner pathComplex pathLeft pathRight
    seed_edges_cover seed_edges_disjoint

theorem seed_inner_product :
    (∑ v ∈ pathLeft.verts ∩ pathRight.verts,
      subImbalance pathComplex pathLeft.edges v
        * subImbalance pathComplex pathRight.edges v) = -1 := by
  rw [seed_interface, Finset.sum_singleton, subImbalance_pathLeft_one,
    subImbalance_pathRight_one] <;> norm_num

/-- The front two edges of the three-edge path. -/
def threePathLeft : Subcomplex threePathComplex where
  verts := ({0, 1, 2} : Finset (Fin 4))
  edges := ({0, 1} : Finset (Fin 3))
  tail_mem := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | h
    · exact Finset.mem_insert_self _ _
    · obtain rfl := Finset.mem_singleton.mp h
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  head_mem := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | h
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · obtain rfl := Finset.mem_singleton.mp h
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- The last edge of the three-edge path. -/
def threePathRight : Subcomplex threePathComplex where
  verts := ({2, 3} : Finset (Fin 4))
  edges := ({2} : Finset (Fin 3))
  tail_mem := by
    intro e he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_insert_self _ _
  head_mem := by
    intro e he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem threePath_edges_cover : threePathLeft.edges ∪ threePathRight.edges = Finset.univ := by
  show (({0, 1} : Finset (Fin 3)) ∪ ({2} : Finset (Fin 3))) = Finset.univ
  rw [Finset.eq_univ_iff_forall]
  intro e
  fin_cases e <;> simp

theorem threePath_edges_disjoint : Disjoint threePathLeft.edges threePathRight.edges := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  have ha' : a ∈ ({0, 1} : Finset (Fin 3)) := ha
  rcases Finset.mem_insert.mp ha' with rfl | h
  · obtain rfl := Finset.mem_singleton.mp (show b ∈ ({2} : Finset (Fin 3)) from hb)
    decide
  · obtain rfl := Finset.mem_singleton.mp h
    obtain rfl := Finset.mem_singleton.mp (show b ∈ ({2} : Finset (Fin 3)) from hb)
    decide

theorem threePath_interface :
    threePathLeft.verts ∩ threePathRight.verts = ({2} : Finset (Fin 4)) := by
  show (({0, 1, 2} : Finset (Fin 4)) ∩ ({2, 3} : Finset (Fin 4))) = {2}
  ext v
  fin_cases v <;> simp

theorem subImbalance_threePathLeft_two :
    subImbalance threePathComplex threePathLeft.edges (2 : Fin 4) = 1 := by decide

theorem subImbalance_threePathRight_two :
    subImbalance threePathComplex threePathRight.edges (2 : Fin 4) = -1 := by decide

/-- The three-edge path diamond, kernel-computed: defect `2`.  The middle vertex
carries `m_A = 1` and `m_B = -1`. -/
theorem threePath_diamond_defect :
    diamondDefect threePathComplex threePathLeft threePathRight = 2 := by
  rw [diamondDefect_eq_neg_two_inner _ _ _ threePath_edges_cover threePath_edges_disjoint,
    threePath_interface, Finset.sum_singleton, subImbalance_threePathLeft_two,
    subImbalance_threePathRight_two] <;> norm_num

/-- The front fork of the out-star. -/
def outStarFork : Subcomplex outStarComplex where
  verts := ({0, 1, 2} : Finset (Fin 4))
  edges := ({0, 1} : Finset (Fin 3))
  tail_mem := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | h
    · exact Finset.mem_insert_self _ _
    · obtain rfl := Finset.mem_singleton.mp h
      exact Finset.mem_insert_self _ _
  head_mem := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | h
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · obtain rfl := Finset.mem_singleton.mp h
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- The last spur of the out-star. -/
def outStarSpur : Subcomplex outStarComplex where
  verts := ({0, 3} : Finset (Fin 4))
  edges := ({2} : Finset (Fin 3))
  tail_mem := by
    intro e he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_insert_self _ _
  head_mem := by
    intro e he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem outStar_edges_cover : outStarFork.edges ∪ outStarSpur.edges = Finset.univ := by
  show (({0, 1} : Finset (Fin 3)) ∪ ({2} : Finset (Fin 3))) = Finset.univ
  rw [Finset.eq_univ_iff_forall]
  intro e
  fin_cases e <;> simp

theorem outStar_edges_disjoint : Disjoint outStarFork.edges outStarSpur.edges := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  have ha' : a ∈ ({0, 1} : Finset (Fin 3)) := ha
  rcases Finset.mem_insert.mp ha' with rfl | h
  · obtain rfl := Finset.mem_singleton.mp (show b ∈ ({2} : Finset (Fin 3)) from hb)
    decide
  · obtain rfl := Finset.mem_singleton.mp h
    obtain rfl := Finset.mem_singleton.mp (show b ∈ ({2} : Finset (Fin 3)) from hb)
    decide

theorem outStar_interface :
    outStarFork.verts ∩ outStarSpur.verts = ({0} : Finset (Fin 4)) := by
  show (({0, 1, 2} : Finset (Fin 4)) ∩ ({0, 3} : Finset (Fin 4))) = {0}
  ext v
  fin_cases v <;> simp

theorem subImbalance_outStarFork_zero :
    subImbalance outStarComplex outStarFork.edges (0 : Fin 4) = -2 := by decide

theorem subImbalance_outStarSpur_zero :
    subImbalance outStarComplex outStarSpur.edges (0 : Fin 4) = -1 := by decide

/-- The out-star diamond, kernel-computed: defect `-4` in units of
`1 / (2 * kappa)`, i.e. `-2 / kappa` in `J` units.  The hub carries `m_A = -2`
and `m_B = -1`, and `-2 * ((-2) * (-1)) = -4`. -/
theorem outStar_diamond_defect :
    diamondDefect outStarComplex outStarFork outStarSpur = -4 := by
  rw [diamondDefect_eq_neg_two_inner _ _ _ outStar_edges_cover outStar_edges_disjoint,
    outStar_interface, Finset.sum_singleton, subImbalance_outStarFork_zero,
    subImbalance_outStarSpur_zero] <;> norm_num

theorem outStar_localized :
    diamondDefect outStarComplex outStarFork outStarSpur
      = -2 * ∑ v ∈ outStarFork.verts ∩ outStarSpur.verts,
          subImbalance outStarComplex outStarFork.edges v
            * subImbalance outStarComplex outStarSpur.edges v :=
  diamondDefect_eq_neg_two_inner outStarComplex outStarFork outStarSpur
    outStar_edges_cover outStar_edges_disjoint

theorem outStar_inner_product :
    (∑ v ∈ outStarFork.verts ∩ outStarSpur.verts,
      subImbalance outStarComplex outStarFork.edges v
        * subImbalance outStarComplex outStarSpur.edges v) = 2 := by
  rw [outStar_interface, Finset.sum_singleton, subImbalance_outStarFork_zero,
    subImbalance_outStarSpur_zero] <;> norm_num

/-- The first edge of the two disjoint edges. -/
def twoEdgeLeft : Subcomplex twoEdgeComplex where
  verts := ({0, 1} : Finset (Fin 4))
  edges := ({0} : Finset (Fin 2))
  tail_mem := by
    intro e he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_insert_self _ _
  head_mem := by
    intro e he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The second of the two disjoint edges. -/
def twoEdgeRight : Subcomplex twoEdgeComplex where
  verts := ({2, 3} : Finset (Fin 4))
  edges := ({1} : Finset (Fin 2))
  tail_mem := by
    intro e he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_insert_self _ _
  head_mem := by
    intro e he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem twoEdge_edges_cover : twoEdgeLeft.edges ∪ twoEdgeRight.edges = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro e
  fin_cases e <;> simp [twoEdgeLeft, twoEdgeRight]

theorem twoEdge_edges_disjoint : Disjoint twoEdgeLeft.edges twoEdgeRight.edges := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  obtain rfl := Finset.mem_singleton.mp (show a ∈ ({0} : Finset (Fin 2)) from ha)
  obtain rfl := Finset.mem_singleton.mp (show b ∈ ({1} : Finset (Fin 2)) from hb)
  exact Fin.zero_ne_one

theorem twoEdge_interface_empty : twoEdgeLeft.verts ∩ twoEdgeRight.verts = ∅ := by
  ext v
  fin_cases v <;> simp [twoEdgeLeft, twoEdgeRight]

/-- The disjoint control, kernel-computed: defect `0`, as the empty-interface
corollary forces. -/
theorem twoEdge_diamond_defect :
    diamondDefect twoEdgeComplex twoEdgeLeft twoEdgeRight = 0 :=
  diamondDefect_eq_zero_of_inter_empty twoEdgeComplex twoEdgeLeft twoEdgeRight
    twoEdge_edges_cover twoEdge_edges_disjoint twoEdge_interface_empty

/-! ## §5. The relation lattice: rank, the null direction, and the inconsistency -/

/-- **MEASURED: the distinct left-hand rows of the cap-4 J-diamond lattice.**
Every realized count vector: the empty complex, and `(nV, nE, 0)` for
`1 ≤ nV ≤ 4`, `0 ≤ nE ≤ 4`.  Provenance: `scripts/qg/out/j_diamond_rank_20260730.json`.
Every row has zero `c_T` coefficient because `J` charges top-cell letters nothing
(`jCost_tet`), so no J-relation can ever see the tet rate. -/
def latticeLHS : List (ℚ × ℚ × ℚ) :=
  [(0, 0, 0),
    (1, 0, 0), (1, 1, 0), (1, 2, 0), (1, 3, 0), (1, 4, 0),
    (2, 0, 0), (2, 1, 0), (2, 2, 0), (2, 3, 0), (2, 4, 0),
    (3, 0, 0), (3, 1, 0), (3, 2, 0), (3, 3, 0), (3, 4, 0),
    (4, 0, 0), (4, 1, 0), (4, 2, 0), (4, 3, 0), (4, 4, 0)]

theorem latticeLHS_count : latticeLHS.length = 21 := rfl

/-- Every measured row has zero `c_T` coefficient: the tet rate is a structural
null direction of the whole lattice. -/
theorem latticeLHS_cT_null : ∀ r ∈ latticeLHS, r.2.2 = 0 := by decide

/-- The two directions every row lies along: the point and the single loop. -/
def rowU : ℚ × ℚ × ℚ := (1, 0, 0)

/-- The single loop at a vertex. -/
def rowW : ℚ × ℚ × ℚ := (1, 1, 0)

theorem latticeLHS_mem_U : rowU ∈ latticeLHS := by decide

theorem latticeLHS_mem_W : rowW ∈ latticeLHS := by decide

theorem lattice_lhs_in_span : ∀ r ∈ latticeLHS,
    r = (r.1 - r.2.1) • rowU + r.2.1 • rowW := by
  intro r hr
  obtain ⟨a, b, c⟩ := r
  have hc : c = 0 := latticeLHS_cT_null _ hr
  subst hc
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨?_, ?_, ?_⟩ <;> simp [rowU, rowW] <;> ring

theorem lattice_rows_independent (x y : ℚ)
    (h : x • rowU + y • rowW = 0) : x = 0 ∧ y = 0 := by
  have h1 := congrArg (fun p : ℚ × ℚ × ℚ => p.1) h
  have h2 := congrArg (fun p : ℚ × ℚ × ℚ => p.2.1) h
  simp only [rowU, rowW, Prod.fst, Prod.snd, smul_eq_mul] at h1 h2
  simp at h1 h2
  constructor <;> linarith

/-- **The left-hand rank of the lattice is exactly two.**  Every measured row
lies in the span of two measured rows, and those two are independent.  The
missing third direction is the tet rate, which `J` cannot see. -/
theorem lattice_lhs_rank_two :
    (∀ r ∈ latticeLHS, r = (r.1 - r.2.1) • rowU + r.2.1 • rowW)
      ∧ (∀ x y : ℚ, x • rowU + y • rowW = 0 → x = 0 ∧ y = 0)
      ∧ rowU ∈ latticeLHS ∧ rowW ∈ latticeLHS :=
  ⟨lattice_lhs_in_span, lattice_rows_independent, latticeLHS_mem_U, latticeLHS_mem_W⟩

/-- The augmented seed row of the point: `C_V = 0`. -/
def augPoint : ℚ × ℚ × ℚ × ℚ := (1, 0, 0, 0)

/-- The augmented seed row of the edge: `2 C_V + C_E = 2`. -/
def augEdge : ℚ × ℚ × ℚ × ℚ := (2, 1, 0, 2)

/-- The augmented seed row of the two-edge path, direct order:
`3 C_V + 2 C_E = 2`. -/
def augPath : ℚ × ℚ × ℚ × ℚ := (3, 2, 0, 2)

/-- **The augmented rank is three.**  The point, edge, and path rows with their
right-hand sides attached are independent, so the right-hand side carries
information the three left-hand directions cannot: the system overshoots the
left-hand rank by exactly one. -/
theorem seed_augmented_independent (x y z : ℚ)
    (h : x • augPoint + y • augEdge + z • augPath = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  have h0 := congrArg (fun p : ℚ × ℚ × ℚ × ℚ => p.1) h
  have h1 := congrArg (fun p : ℚ × ℚ × ℚ × ℚ => p.2.1) h
  have h3 := congrArg (fun p : ℚ × ℚ × ℚ × ℚ => p.2.2.2) h
  simp only [augPoint, augEdge, augPath, Prod.fst, Prod.snd, smul_eq_mul] at h0 h1 h3
  simp at h0 h1 h3
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- **HEADLINE (the lattice is inconsistent).**  No rational rate triple solves
the four seed rows: the point forces `C_V = 0`, the edge forces `C_E = 2`, the
direct path then demands `2 = 2` while the glued path demands `2 = 4`.  The two
accumulation orders of the A15 diamond cannot both be paid by any additive
letter cost. -/
theorem lattice_inconsistent_seed :
    ¬ ∃ C : Fin 3 → ℚ,
        C 0 = 0
        ∧ 2 * C 0 + C 1 = 2
        ∧ 3 * C 0 + 2 * C 1 = 2
        ∧ 3 * C 0 + 2 * C 1 = 4 := by
  rintro ⟨C, h0, h1, h2, h3⟩
  linarith

/-- **The conflict precedes any gluing.**  The count vector `(2, 1, 0)` alone
demands `2 C_V + C_E` equal both `0` (loop with an isolated vertex) and `2`
(proper edge): `J` is not even a function of the three counts. -/
theorem lattice_inconsistent_counts :
    ¬ ∃ C : Fin 3 → ℚ,
        C 0 = 0 ∧ 2 * C 0 + C 1 = 2 ∧ 2 * C 0 + C 1 = 0 := by
  rintro ⟨C, h0, h1, h2⟩
  linarith

/-! ## §6. The measured tallies, mirrored

Exact integer enumeration, `scripts/qg/qg_j_diamond_rank_20260730.py`, receipt
`scripts/qg/out/j_diamond_rank_20260730.json`.  Every tally below is MEASURED;
each decisive one is restated as a kernel-checked fact immediately after. -/

/-- Per-cap enumeration tallies.  `rankA` is the left-hand rank of the lattice
at that cap, `rankAug` the augmented rank; the two differ exactly when the
lattice is inconsistent. -/
structure CapTally where
  classes : ℕ
  wide : ℕ
  genuine : ℕ
  genuineNonzero : ℕ
  elementary : ℕ
  elementaryNonzero : ℕ
  bilinearChecked : ℕ
  bilinearOk : ℕ
  localizationViolations : ℕ
  maxAbsDefect : ℤ
  rankA : ℕ
  rankAug : ℕ

/-- MEASURED tallies at caps 1, 2, 3, 4. -/
def measuredCaps : Fin 4 → CapTally :=
  ![{ classes := 3, wide := 0, genuine := 0, genuineNonzero := 0,
      elementary := 0, elementaryNonzero := 0,
      bilinearChecked := 0, bilinearOk := 0, localizationViolations := 0,
      maxAbsDefect := 0, rankA := 2, rankAug := 2 },
    { classes := 13, wide := 21, genuine := 14, genuineNonzero := 2,
      elementary := 7, elementaryNonzero := 0,
      bilinearChecked := 19, bilinearOk := 19, localizationViolations := 0,
      maxAbsDefect := 4, rankA := 2, rankAug := 3 },
    { classes := 68, wide := 1051, genuine := 814, genuineNonzero := 258,
      elementary := 146, elementaryNonzero := 17,
      bilinearChecked := 619, bilinearOk := 619, localizationViolations := 0,
      maxAbsDefect := 8, rankA := 2, rankAug := 3 },
    { classes := 437, wide := 42823, genuine := 36079, genuineNonzero := 15359,
      elementary := 2132, elementaryNonzero := 389,
      bilinearChecked := 16988, bilinearOk := 16988, localizationViolations := 0,
      maxAbsDefect := 16, rankA := 2, rankAug := 3 }]

/-- MEASURED, restated in the kernel: at cap 4 the left-hand rank is 2 and the
augmented rank is 3, so the lattice is inconsistent there. -/
theorem measured_rank_cap4 :
    (measuredCaps 3).rankA = 2 ∧ (measuredCaps 3).rankAug = 3 := ⟨rfl, rfl⟩

/-- MEASURED, restated: the bilinear identity held on every edge-disjoint
diamond enumerated, at every cap.  This is the measured half of
`diamondDefect_eq_neg_two_inner`. -/
theorem measured_bilinear_perfect :
    ∀ i : Fin 4, (measuredCaps i).bilinearChecked = (measuredCaps i).bilinearOk := by
  decide

/-- MEASURED, restated: no nonzero edge-disjoint defect lacked a two-sided
imbalanced interface vertex, at any cap.  The measured half of
`diamondDefect_eq_zero_of_interface_balanced`. -/
theorem measured_no_localization_violations :
    ∀ i : Fin 4, (measuredCaps i).localizationViolations = 0 := by decide

/-- MEASURED, restated: the seed diamond enters at cap 3, where 17 of the 146
elementary diamonds are nonzero; the verdict is already inconsistent at cap 2
through the count conflict. -/
theorem measured_seed_enters_cap3 :
    (measuredCaps 1).rankAug = 3
      ∧ (measuredCaps 2).elementary = 146
      ∧ (measuredCaps 2).elementaryNonzero = 17 := ⟨rfl, rfl, rfl⟩

/-! ## §7. The verdict -/

/-- **The C15 J-diamond lattice verdict.**  The localization theorem and its two
corollaries; the evenness of the spectrum; the three kernel-computed J-unit
diamonds and the disjoint control; the count conflict; the rank facts; and the
inconsistency of the seed rows. -/
structure JDiamondRankVerdict : Prop where
  defect_is_interface_coupling : ∀ (K : BoundedComplex 4) (A Bd : Subcomplex K),
    A.edges ∪ Bd.edges = Finset.univ → Disjoint A.edges Bd.edges →
      diamondDefect K A Bd
        = -2 * ∑ v ∈ A.verts ∩ Bd.verts,
            subImbalance K A.edges v * subImbalance K Bd.edges v
  interface_localization : ∀ (K : BoundedComplex 4) (A Bd : Subcomplex K),
    A.edges ∪ Bd.edges = Finset.univ → Disjoint A.edges Bd.edges →
      (∀ v ∈ A.verts ∩ Bd.verts,
        subImbalance K A.edges v = 0 ∨ subImbalance K Bd.edges v = 0) →
        diamondDefect K A Bd = 0
  empty_interface_exact : ∀ (K : BoundedComplex 4) (A Bd : Subcomplex K),
    A.edges ∪ Bd.edges = Finset.univ → Disjoint A.edges Bd.edges →
      A.verts ∩ Bd.verts = ∅ → diamondDefect K A Bd = 0
  spectrum_even : ∀ K : BoundedComplex 4, 2 ∣ imbalanceSq K
  seed_defect_kernel : diamondDefect pathComplex pathLeft pathRight = 2
  seed_diamond_J : ∀ kappa : ℝ, kappa ≠ 0 →
    historyCost (jCost kappa) 4 edgeComplex
      + historyCost (jCost kappa) 4 edgeComplex
      - historyCost (jCost kappa) 4 pointComplex
      - historyCost (jCost kappa) 4 pathComplex = 1 / kappa
  negative_diamond_J : ∀ kappa : ℝ, kappa ≠ 0 →
    historyCost (jCost kappa) 4 forkComplex
      + historyCost (jCost kappa) 4 edgeComplex
      - historyCost (jCost kappa) 4 pointComplex
      - historyCost (jCost kappa) 4 outStarComplex = -2 / kappa
  disjoint_control_J : ∀ kappa : ℝ, kappa ≠ 0 →
    historyCost (jCost kappa) 4 edgeComplex
      + historyCost (jCost kappa) 4 edgeComplex
      - historyCost (jCost kappa) 4 (emptyComplex 4)
      - historyCost (jCost kappa) 4 twoEdgeComplex = 0
  not_a_function_of_counts : ∀ kappa : ℝ, kappa ≠ 0 →
    edgeComplex.nV = loopPointComplex.nV ∧ edgeComplex.nE = loopPointComplex.nE
      ∧ edgeComplex.nT = loopPointComplex.nT
      ∧ historyCost (jCost kappa) 4 edgeComplex
        ≠ historyCost (jCost kappa) 4 loopPointComplex
  lhs_null_direction : ∀ r ∈ latticeLHS, r.2.2 = 0
  lhs_rank_two :
    (∀ r ∈ latticeLHS, r = (r.1 - r.2.1) • rowU + r.2.1 • rowW)
      ∧ (∀ x y : ℚ, x • rowU + y • rowW = 0 → x = 0 ∧ y = 0)
      ∧ rowU ∈ latticeLHS ∧ rowW ∈ latticeLHS
  augmented_rank_three : ∀ x y z : ℚ,
    x • augPoint + y • augEdge + z • augPath = 0 → x = 0 ∧ y = 0 ∧ z = 0
  inconsistent_seed :
    ¬ ∃ C : Fin 3 → ℚ,
        C 0 = 0
        ∧ 2 * C 0 + C 1 = 2
        ∧ 3 * C 0 + 2 * C 1 = 2
        ∧ 3 * C 0 + 2 * C 1 = 4
  inconsistent_counts :
    ¬ ∃ C : Fin 3 → ℚ,
        C 0 = 0 ∧ 2 * C 0 + C 1 = 2 ∧ 2 * C 0 + C 1 = 0
  measured_rank : (measuredCaps 3).rankA = 2 ∧ (measuredCaps 3).rankAug = 3
  measured_bilinear : ∀ i : Fin 4,
    (measuredCaps i).bilinearChecked = (measuredCaps i).bilinearOk
  measured_localization : ∀ i : Fin 4, (measuredCaps i).localizationViolations = 0

theorem jDiamondRankVerdict : JDiamondRankVerdict where
  defect_is_interface_coupling := diamondDefect_eq_neg_two_inner
  interface_localization := diamondDefect_eq_zero_of_interface_balanced
  empty_interface_exact := diamondDefect_eq_zero_of_inter_empty
  spectrum_even := imbalanceSq_even
  seed_defect_kernel := seed_diamond_defect
  seed_diamond_J := diamond_J_seed
  negative_diamond_J := diamond_J_outStar
  disjoint_control_J := diamond_J_disjoint
  not_a_function_of_counts := jCost_not_a_function_of_counts
  lhs_null_direction := latticeLHS_cT_null
  lhs_rank_two := lattice_lhs_rank_two
  augmented_rank_three := seed_augmented_independent
  inconsistent_seed := lattice_inconsistent_seed
  inconsistent_counts := lattice_inconsistent_counts
  measured_rank := measured_rank_cap4
  measured_bilinear := measured_bilinear_perfect
  measured_localization := measured_no_localization_violations

/-! ## Axiom audit -/

#print axioms subImbalance_eq_zero_of_not_mem
#print axioms subImbalance_union
#print axioms diamondDefect_eq_neg_two_inner
#print axioms diamondDefect_eq_zero_of_inter_empty
#print axioms diamondDefect_eq_zero_of_interface_balanced
#print axioms sum_vertexImbalance
#print axioms imbalanceSq_even
#print axioms historyCost_jCost_eq
#print axioms historyCost_edge
#print axioms historyCost_twoEdge
#print axioms historyCost_fork
#print axioms historyCost_outStar
#print axioms historyCost_loopPoint
#print axioms historyCost_empty
#print axioms diamond_J_seed
#print axioms diamond_J_threePath
#print axioms diamond_J_outStar
#print axioms diamond_J_disjoint
#print axioms jCost_not_a_function_of_counts
#print axioms seed_edges_cover
#print axioms seed_edges_disjoint
#print axioms seed_interface
#print axioms subImbalance_pathLeft_one
#print axioms subImbalance_pathRight_one
#print axioms seed_diamond_defect
#print axioms seed_diamond_localized
#print axioms seed_inner_product
#print axioms threePath_edges_cover
#print axioms threePath_edges_disjoint
#print axioms threePath_interface
#print axioms threePath_diamond_defect
#print axioms outStar_edges_cover
#print axioms outStar_edges_disjoint
#print axioms outStar_interface
#print axioms outStar_diamond_defect
#print axioms outStar_localized
#print axioms outStar_inner_product
#print axioms twoEdge_edges_cover
#print axioms twoEdge_edges_disjoint
#print axioms twoEdge_interface_empty
#print axioms twoEdge_diamond_defect
#print axioms latticeLHS_cT_null
#print axioms lattice_lhs_in_span
#print axioms lattice_rows_independent
#print axioms lattice_lhs_rank_two
#print axioms seed_augmented_independent
#print axioms lattice_inconsistent_seed
#print axioms lattice_inconsistent_counts
#print axioms measured_rank_cap4
#print axioms measured_bilinear_perfect
#print axioms measured_no_localization_violations
#print axioms measured_seed_enters_cap3
#print axioms jDiamondRankVerdict

end Gap2JDiamondRank
end SevenGaps
end Gravity
end IndisputableMonolith
