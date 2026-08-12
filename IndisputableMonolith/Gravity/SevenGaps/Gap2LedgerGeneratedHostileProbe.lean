import IndisputableMonolith.Gravity.SevenGaps.Gap2LedgerGenerated

/-!
# Hostile probe for C14 LedgerGenerated (review 2026-07-30)

Adversarial module against `Gap2LedgerGenerated`. Edits nothing in the reviewed
module. Leave uncommitted.

Attacks:
1. Witness arithmetic: jCost letterwise equals fV(m)=m²/(2κ) with null edges/tets.
2. Decoy discrimination: censusVertexCost fails the global predicate.
3. Gaming cost: SJ-share on vertices is not ledger-generated (same m, different shares).
4. C27 trigger shape: LedgerGeneratedAt ∧ ∃ nonzero historyCost at the cap.
5. Flag unmoved index.
6. Axiom re-audit on the load-bearing certificates.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2LedgerGeneratedHostileProbe

open PathSumMeasure GaugeHistoryMeasure Gap2PostingCostDerivation
open Gap2JEhrhartSpan Gap2JDiamondRank Gap2GluingDerivation Gap2LedgerGenerated

noncomputable section

/-! ## 1. Witness equals jCost letterwise -/

theorem probe_jCost_vertex_matches_charge (kappa : ℝ) (B : ℕ) (K : BoundedComplex B)
    (v : Fin K.nV) :
    jCost kappa B K (Sum.inl v) = jCostVertexCharge kappa (vertexImbalance K v) := by
  simp only [jCost_inl, jCostVertexCharge]

theorem probe_jCost_edge_zero (kappa : ℝ) (B : ℕ) (K : BoundedComplex B)
    (e : Fin K.nE) :
    jCost kappa B K (Sum.inr (Sum.inl e)) = (0 : ℝ) :=
  jCost_edge kappa B K e

theorem probe_jCost_tet_zero (kappa : ℝ) (B : ℕ) (K : BoundedComplex B)
    (t : Fin K.nT) :
    jCost kappa B K (Sum.inr (Sum.inr t)) = (0 : ℝ) :=
  jCost_tet kappa B K t

theorem probe_jCost_ledgerGenerated :
    LedgerGenerated (jCost 1) :=
  jCost_ledgerGenerated (by norm_num : (1 : ℝ) ≠ 0)

/-! ## 2. Decoy fails -/

theorem probe_decoy_fails : ¬ LedgerGenerated censusVertexCost :=
  censusVertexCost_not_ledgerGenerated

/-! ## 3. Gaming: SJ-share is not a function of imbalance alone -/

/-- Intuitively non-local: each vertex is charged the complex's total SJ. -/
def sjTotalVertexCost : LetterCost := fun _ K a =>
  match a with
  | Sum.inl _ => (imbalanceSq K : ℝ)
  | Sum.inr _ => 0

theorem probe_sjTotal_not_ledgerGenerated :
    ¬ LedgerGenerated sjTotalVertexCost := by
  rintro ⟨fV, cE, cT, hV, hE, hT⟩
  -- point: SJ = 0, every vertex row m = 0, charge 0
  have hp := hV 4 pointComplex ⟨0, by decide⟩
  have mp : vertexImbalance pointComplex (⟨0, by decide⟩ : Fin 1) = 0 := by decide
  -- edge: vertices have m = ±1, but also compare two m = 0 carriers of different SJ:
  -- loopPoint has SJ = 0 at m = 0; path's middle vertex has m = 0 and SJ = 2.
  have hlp := hV 4 loopPointComplex ⟨1, by decide⟩
  have mlp : vertexImbalance loopPointComplex (⟨1, by decide⟩ : Fin 2) = 0 := by
    decide
  have hmid := hV 4 pathComplex ⟨1, by decide⟩
  have mmid : vertexImbalance pathComplex (⟨1, by decide⟩ : Fin 3) = 0 := by decide
  simp only [sjTotalVertexCost] at hp hlp hmid
  have eq0 : (0 : ℝ) = fV 0 := by
    have : imbalanceSq pointComplex = 0 := by decide
    simpa [mp, this] using hp
  have eq_lp : (0 : ℝ) = fV 0 := by
    have : imbalanceSq loopPointComplex = 0 := by decide
    simpa [mlp, this] using hlp
  have eq_path : (2 : ℝ) = fV 0 := by
    have : imbalanceSq pathComplex = 2 := by decide
    simpa [mmid, this] using hmid
  linarith [eq0, eq_path]

/-! ## 4. Seed history costs and C27 shape -/

theorem probe_seed_history :
    historyCost (jCost 1) 4 edgeComplex = 1
      ∧ historyCost (jCost 1) 4 loopPointComplex = 0
      ∧ historyCost (jCost 1) 4 pathComplex = 1
      ∧ historyCost (jCost 1) 4 forkComplex = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact historyCost_jCost_one_edge
  · exact historyCost_jCost_one_loopPoint
  · exact historyCost_jCost_one_path
  · exact historyCost_jCost_one_fork

theorem probe_C27_shape_cap2 : C27TriggerAt 2 (jCost 1) :=
  C27_trigger_armed_cap2

theorem probe_C27_hard_stop_bool : C27_hard_stop_armed = true :=
  C27_hard_stop_armed_eq

theorem probe_flag_unmoved : ledgerGeneratedIndex.measure_flag_moved = false :=
  index_flag_unmoved

theorem probe_verdict : LedgerGeneratedVerdict :=
  ledgerGeneratedVerdict

end

#print axioms probe_jCost_ledgerGenerated
#print axioms probe_decoy_fails
#print axioms probe_sjTotal_not_ledgerGenerated
#print axioms probe_C27_shape_cap2
#print axioms probe_verdict

end Gap2LedgerGeneratedHostileProbe
end SevenGaps
end Gravity
end IndisputableMonolith
