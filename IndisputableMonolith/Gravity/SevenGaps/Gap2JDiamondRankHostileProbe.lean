import IndisputableMonolith.Gravity.SevenGaps.Gap2JDiamondRank

/-!
# Hostile probe for the C15 J-diamond rank lattice (review 2026-07-30)

Adversarial module against `Gap2JDiamondRank`. Edits nothing in the reviewed
module. Every attack that fails to land is evidence for the reviewed claim.

1. **Witness arithmetic, kernel-checked.** Seed diamond SJ costs (direct 2,
   glued 4, defect 2); out-star defect `-4`; disjoint control `0`; count-vector
   conflict on `(2,1,0)` with SJ costs `2` vs `0`.
2. **J-unit defects.** Re-check `diamond_J_*` at a concrete Casimir.
3. **Inconsistency really is unsatisfiability.** The seed and count systems
   have no rational solution; the last two seed equations alone already clash.
4. **Localization identity on the seed.** Interface coupling equals the defect.
5. **Axiom re-audit** on the headline and the two inconsistency witnesses.
6. **Scope pressure.** The inconsistency theorems quantify over `Fin 3 → ℚ`
   rate triples, not over library `LetterCost`; the probe records that gap as a
   prose scope note, not a false theorem.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2JDiamondRankHostileProbe

open PathSumMeasure GaugeHistoryMeasure Gap2PostingCostDerivation Gap2JEhrhartSpan
open Gap2JDiamondRank

/-! ## 1. Count-vector carriers and SJ costs -/

theorem probe_edge_counts :
    edgeComplex.nV = 2 ∧ edgeComplex.nE = 1 ∧ edgeComplex.nT = 0 :=
  ⟨rfl, rfl, rfl⟩

theorem probe_loopPoint_counts :
    loopPointComplex.nV = 2 ∧ loopPointComplex.nE = 1 ∧ loopPointComplex.nT = 0 :=
  ⟨rfl, rfl, rfl⟩

theorem probe_same_count_vector :
    edgeComplex.nV = loopPointComplex.nV
      ∧ edgeComplex.nE = loopPointComplex.nE
      ∧ edgeComplex.nT = loopPointComplex.nT :=
  ⟨rfl, rfl, rfl⟩

theorem probe_edge_SJ : imbalanceSq edgeComplex = 2 := by decide

theorem probe_loopPoint_SJ : imbalanceSq loopPointComplex = 0 :=
  imbalanceSq_loopPoint

theorem probe_path_SJ : imbalanceSq pathComplex = 2 := by decide

theorem probe_twoEdge_SJ : imbalanceSq twoEdgeComplex = 4 :=
  imbalanceSq_twoEdge

theorem probe_outStar_SJ : imbalanceSq outStarComplex = 12 :=
  imbalanceSq_outStar

theorem probe_fork_SJ : imbalanceSq forkComplex = 6 :=
  imbalanceSq_fork

/-! ## 2. Seed / out-star / disjoint defects in SJ and J units -/

theorem probe_seed_defect_SJ :
    diamondDefect pathComplex pathLeft pathRight = 2 :=
  seed_diamond_defect

theorem probe_seed_localized :
    diamondDefect pathComplex pathLeft pathRight
      = -2 * ∑ v ∈ pathLeft.verts ∩ pathRight.verts,
          subImbalance pathComplex pathLeft.edges v
            * subImbalance pathComplex pathRight.edges v :=
  seed_diamond_localized

theorem probe_seed_inner_product :
    (∑ v ∈ pathLeft.verts ∩ pathRight.verts,
      subImbalance pathComplex pathLeft.edges v
        * subImbalance pathComplex pathRight.edges v) = -1 :=
  seed_inner_product

theorem probe_outStar_defect_SJ :
    diamondDefect outStarComplex outStarFork outStarSpur = -4 :=
  outStar_diamond_defect

theorem probe_disjoint_defect_SJ :
    diamondDefect twoEdgeComplex twoEdgeLeft twoEdgeRight = 0 :=
  twoEdge_diamond_defect

theorem probe_seed_J_at_one :
    historyCost (jCost 1) 4 edgeComplex
      + historyCost (jCost 1) 4 edgeComplex
      - historyCost (jCost 1) 4 pointComplex
      - historyCost (jCost 1) 4 pathComplex = (1 : ℝ) / 1 :=
  diamond_J_seed 1 (by norm_num)

theorem probe_outStar_J_at_one :
    historyCost (jCost 1) 4 forkComplex
      + historyCost (jCost 1) 4 edgeComplex
      - historyCost (jCost 1) 4 pointComplex
      - historyCost (jCost 1) 4 outStarComplex = (-2 : ℝ) / 1 :=
  diamond_J_outStar 1 (by norm_num)

theorem probe_disjoint_J_at_one :
    historyCost (jCost 1) 4 edgeComplex
      + historyCost (jCost 1) 4 edgeComplex
      - historyCost (jCost 1) 4 (emptyComplex 4)
      - historyCost (jCost 1) 4 twoEdgeComplex = 0 :=
  diamond_J_disjoint 1 (by norm_num)

theorem probe_count_conflict_J_at_one :
    historyCost (jCost 1) 4 edgeComplex = (1 : ℝ) / 1
      ∧ historyCost (jCost 1) 4 loopPointComplex = 0 := by
  constructor
  · exact historyCost_edge (1 : ℝ) (by norm_num)
  · exact historyCost_loopPoint (1 : ℝ)

/-! ## 3. Unsatisfiability of the rate systems -/

/-- The two path equations alone already contradict; the point/edge rows are
not needed for the clash. -/
theorem probe_seed_clash_from_path_rows_alone :
    ¬ ∃ C : Fin 3 → ℚ,
        3 * C 0 + 2 * C 1 = 2 ∧ 3 * C 0 + 2 * C 1 = 4 := by
  rintro ⟨C, h2, h4⟩
  linarith

theorem probe_count_clash_alone :
    ¬ ∃ C : Fin 3 → ℚ, 2 * C 0 + C 1 = 2 ∧ 2 * C 0 + C 1 = 0 := by
  rintro ⟨C, h2, h0⟩
  linarith

theorem probe_inconsistent_seed :
    ¬ ∃ C : Fin 3 → ℚ,
        C 0 = 0
        ∧ 2 * C 0 + C 1 = 2
        ∧ 3 * C 0 + 2 * C 1 = 2
        ∧ 3 * C 0 + 2 * C 1 = 4 :=
  lattice_inconsistent_seed

theorem probe_inconsistent_counts :
    ¬ ∃ C : Fin 3 → ℚ,
        C 0 = 0 ∧ 2 * C 0 + C 1 = 2 ∧ 2 * C 0 + C 1 = 0 :=
  lattice_inconsistent_counts

theorem probe_not_function_of_counts :
    edgeComplex.nV = loopPointComplex.nV ∧ edgeComplex.nE = loopPointComplex.nE
      ∧ edgeComplex.nT = loopPointComplex.nT
      ∧ historyCost (jCost 1) 4 edgeComplex
        ≠ historyCost (jCost 1) 4 loopPointComplex :=
  jCost_not_a_function_of_counts 1 (by norm_num)

/-! ## 4. Rank facts on the hardcoded LHS list -/

theorem probe_lhs_length : latticeLHS.length = 21 := latticeLHS_count

theorem probe_lhs_rank_two :
    (∀ r ∈ latticeLHS, r = (r.1 - r.2.1) • rowU + r.2.1 • rowW)
      ∧ (∀ x y : ℚ, x • rowU + y • rowW = 0 → x = 0 ∧ y = 0)
      ∧ rowU ∈ latticeLHS ∧ rowW ∈ latticeLHS :=
  lattice_lhs_rank_two

theorem probe_aug_independent :
    ∀ x y z : ℚ, x • augPoint + y • augEdge + z • augPath = 0 →
      x = 0 ∧ y = 0 ∧ z = 0 :=
  seed_augmented_independent

/-! ## 5. Corollaries really follow from the localization identity -/

theorem probe_empty_iface_is_corollary
    (K : BoundedComplex 4) (A Bd : Subcomplex K)
    (he : A.edges ∪ Bd.edges = Finset.univ) (hd : Disjoint A.edges Bd.edges)
    (hi : A.verts ∩ Bd.verts = ∅) :
    diamondDefect K A Bd = 0 :=
  diamondDefect_eq_zero_of_inter_empty K A Bd he hd hi

theorem probe_balanced_iface_is_corollary
    (K : BoundedComplex 4) (A Bd : Subcomplex K)
    (he : A.edges ∪ Bd.edges = Finset.univ) (hd : Disjoint A.edges Bd.edges)
    (hb : ∀ v ∈ A.verts ∩ Bd.verts,
      subImbalance K A.edges v = 0 ∨ subImbalance K Bd.edges v = 0) :
    diamondDefect K A Bd = 0 :=
  diamondDefect_eq_zero_of_interface_balanced K A Bd he hd hb

theorem probe_verdict : JDiamondRankVerdict := jDiamondRankVerdict

/-! ## 6. Axiom re-audit -/

#print axioms jDiamondRankVerdict
#print axioms lattice_inconsistent_seed
#print axioms lattice_inconsistent_counts
#print axioms jCost_not_a_function_of_counts
#print axioms diamondDefect_eq_neg_two_inner
#print axioms diamond_J_seed
#print axioms diamond_J_outStar
#print axioms diamond_J_disjoint
#print axioms seed_diamond_defect
#print axioms probe_seed_clash_from_path_rows_alone
#print axioms probe_count_clash_alone
#print axioms probe_seed_J_at_one
#print axioms probe_outStar_J_at_one
#print axioms probe_count_conflict_J_at_one
#print axioms probe_verdict

end Gap2JDiamondRankHostileProbe
end SevenGaps
end Gravity
end IndisputableMonolith
