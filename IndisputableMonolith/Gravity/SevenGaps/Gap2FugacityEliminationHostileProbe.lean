import IndisputableMonolith.Gravity.SevenGaps.Gap2FugacityElimination
import IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

/-!
# Hostile probe for Gap2FugacityElimination (A19 / C17)

Uncommitted. Rebuilds from source on the bigbird tree; re-checks axioms,
inhabits the A1.4 class, re-verifies the three widening witnesses, and
exposes the theorem-3 dependency / vacuity shape for attack B.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2FugacityEliminationHostileProbe

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume
open Gap2GluingDerivation Gap2PostingCostDerivation Gap2NonEquivariantPosting
open Gap2SizeBlindnessReach Gap2FugacityPostingGluing Gap2LabelErasure
open Gap2LetterCostDichotomy Gap2FugacityElimination FullTheoryLedger

noncomputable section

/-! ## F. Class of theorem 1 is inhabited (gibbsSize / characterCost 1 1 1) -/

theorem a14_class_inhabited_by_unit_character :
    (∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
        classMass (postedWeight (characterCost 1 1 1) B')
          (Quotient.mk (relabelSetoid B') K) = mu K)
      ∧ (∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
          classMass (postedWeight (characterCost 1 1 1) B')
            (Quotient.mk (relabelSetoid B') K)
          = classMass (sizeWeight (characterSize 1 1 1))
            (Quotient.mk (relabelSetoid B') K))
      ∧ UnitFugacity (characterSize 1 1 1) := by
  have hz : (0 : ℝ) < 1 := by norm_num
  have hposts := (characterCost_posts_mu_iff hz hz hz).mpr ⟨rfl, rfl, rfl⟩
  refine ⟨fun B' K _ _ => hposts B' K,
    fun B' K _ _ => by rw [postedWeight_characterCost_eq hz hz hz B'],
    ?_⟩
  exact unit_fugacity_forced_after_erasure (characterCost 1 1 1) (characterSize 1 1 1)
    (fun B' K _ _ => hposts B' K)
    (fun B' K _ _ => by rw [postedWeight_characterCost_eq hz hz hz B'])

theorem gibbsSize_witnesses_unit_fugacity : UnitFugacity gibbsSize :=
  gibbsSize_unitFugacity

/-! ## C. Witness recomputation -/

theorem witness_tilted_posts_mu_and_not_sizeWeight :
    (∀ (B' : ℕ) (K : BoundedComplex B'),
        classMass (postedWeight (tiltedCost (1 / 2)) B')
          (Quotient.mk (relabelSetoid B') K) = mu K)
      ∧ (¬ ∃ f : ℕ → ℕ → ℕ → ℝ,
            ∀ K : BoundedComplex 3,
              postedWeight (tiltedCost (1 / 2)) 3 K = sizeWeight f K) := by
  have ht : |(1 / 2 : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> norm_num
  have ht0 : (1 / 2 : ℝ) ≠ 0 := by norm_num
  exact ⟨fun B' K => tiltedCost_posts_mu ht B' K,
    postedWeight_tiltedCost_not_sizeWeight ht ht0⟩

theorem witness_characterCost_continuum (zV zE zT : ℝ)
    (hzV : 0 < zV) (hzE : 0 < zE) (hzT : 0 < zT)
    (hne : ¬ (zV = 1 ∧ zE = 1 ∧ zT = 1)) :
    KindOnly (characterCost zV zE zT)
      ∧ Equivariant (characterCost zV zE zT)
      ∧ SizeBlind (postedWeight (characterCost zV zE zT))
      ∧ CarrierShuffle (characterSize zV zE zT)
      ∧ ¬ UnitFugacity (characterSize zV zE zT) := by
  refine ⟨characterCost_kindOnly zV zE zT, characterCost_equivariant zV zE zT,
    postedWeight_characterCost_sizeBlind zV zE zT,
    characterSize_carrierShuffle hzV hzE hzT, ?_⟩
  intro hUF
  exact hne (unitFugacity_characterSize_iff.mp hUF)

theorem witness_surfaceCost_escapes_kindTotals (F : CensusDilateFamily) :
    Equivariant (surfaceCost (1 : ℝ))
      ∧ SurfaceTotal F (surfaceCost (1 : ℝ)) 1 0
      ∧ ¬ FixedKindTotals (surfaceCost (1 : ℝ))
      ∧ historyCost (surfaceCost (1 : ℝ)) 16 (dust 16) ≠ 0 :=
  widening_blocked_without_kindTotals F (by norm_num : (1 : ℝ) ≠ 0)

/-! ## B. Theorem-3 dependency trace

`unit_fugacity_forced_by_surface_and_kindTotals` binders name only
`FixedKindTotals` and `SurfaceTotal`.  Its proof cites
`the_measure_is_exactly_the_gauge_divisor`, whose *conclusion* names `mu`
(and equals the gauge divisor).  The first conjunct `UnitFugacity gibbsSize`
is discharged by `gibbsSize_unitFugacity` and does not use those binders.
The load-bearing content is the posted-weight and class-mass conjuncts,
which are A1.7's content re-exported.
-/

theorem thm3_first_conjunct_is_hypothesis_free :
    UnitFugacity gibbsSize :=
  gibbsSize_unitFugacity

theorem thm3_load_bearing_is_a17
    (F : CensusDilateFamily) {c : LetterCost} {a e : ℝ}
    (h : FixedKindTotals c) (hs : SurfaceTotal F c a e)
    (B' : ℕ) (K : BoundedComplex B') :
    postedWeight c B' K = sizeWeight gibbsSize K
      ∧ classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K) = mu K := by
  have hdiv := the_measure_is_exactly_the_gauge_divisor F h hs B' K
  refine ⟨?_, hdiv.2.2.2⟩
  rw [hdiv.2.1, gibbsWeight_eq_gibbsSize]
  rfl

/-- `a17_lands_in_a14_elimination` concludes a hypothesis-free fact. -/
theorem a17_lands_ignores_binders
    (F : CensusDilateFamily) {c : LetterCost} {a e : ℝ}
    (_h : FixedKindTotals c) (_hs : SurfaceTotal F c a e) :
    a17_lands_in_a14_elimination F _h _hs = gibbsSize_unitFugacity := by
  rfl

/-! ## D. Full-posting force is pointwise on realized triples, hypotheses on face -/

theorem full_posting_force_is_pointwise
    {c : LetterCost} (hc : Equivariant c) (f : ℕ → ℕ → ℕ → ℝ)
    (hpost : ∀ (B' : ℕ) (K : BoundedComplex B'),
      classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K) = mu K)
    (hrep : ∀ (B' : ℕ) (K : BoundedComplex B'),
      classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K)
        = classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') K))
    (B : ℕ) (K : BoundedComplex B) :
    f K.nV K.nE K.nT = gibbsSize K.nV K.nE K.nT :=
  (erasure_and_full_posting_force_gibbsSize hc f hpost hrep K).1

/-! ## A / alias check: theorem 1 is definitionally A1.4 -/

theorem thm1_is_a14_alias (c : LetterCost) (f : ℕ → ℕ → ℕ → ℝ)
    (hpost : ∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
      classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K) = mu K)
    (hrep : ∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
      classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K)
        = classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') K)) :
    unit_fugacity_forced_after_erasure c f hpost hrep
      = no_posting_countermodel_with_nonunit_fugacity c f hpost hrep :=
  rfl

/-! ## E / G. Flag and ledger -/

theorem flag_unmoved_rfl :
    Gap2FugacityElimination.fugacityEliminationIndex.measure_flag_moved = false :=
  Gap2FugacityElimination.index_flag_unmoved

theorem ledger_gap2_now_true :
    fullTheoryBenchmarks.gap2_measure_derived = true := by
  simp [fullTheoryBenchmarks]

/-! ## Axiom audit (every named C17 theorem + probe locals) -/

#print axioms unit_fugacity_forced_after_erasure
#print axioms three_fugacities_collapse_on_posting_mu
#print axioms three_fugacities_collapse_via_characterCost
#print axioms unit_fugacity_forced_by_surface_and_kindTotals
#print axioms a17_lands_in_a14_elimination
#print axioms erasure_and_unit_fugacity_compose_to_mu
#print axioms erasure_and_full_posting_force_gibbsSize
#print axioms erasure_and_a17_compose_to_mu_no_fugacity
#print axioms widening_blocked_by_non_sizeWeight_posting
#print axioms widening_blocked_without_naming_mu
#print axioms widening_blocked_without_kindTotals
#print axioms fugacity_elimination_verdict
#print axioms a14_class_inhabited_by_unit_character
#print axioms witness_tilted_posts_mu_and_not_sizeWeight
#print axioms witness_characterCost_continuum
#print axioms witness_surfaceCost_escapes_kindTotals
#print axioms thm1_is_a14_alias
#print axioms thm3_load_bearing_is_a17
#print axioms full_posting_force_is_pointwise
#print axioms ledger_gap2_now_true
#print axioms flag_unmoved_rfl

end

end Gap2FugacityEliminationHostileProbe
end SevenGaps
end Gravity
end IndisputableMonolith
