import IndisputableMonolith.Gravity.SevenGaps.Gap2MeasureDerivation
import IndisputableMonolith.Gravity.SevenGaps.MeasureInvarianceNoGo

/-!
# Hostile probe: Gap2MeasureDerivation flag-8 synthesis (2026-07-30)

Attacks B-iii (wrong labeled weight), D (axiom prints), E (load-bearing
premises), F (blocker iff / certificate connection). Verdict MINOR; the one
finding (report prose naming C16 as if load-bearing) was repaired in A27 §5
and the flip docstring, and the flag then flipped in-session.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2MeasureDerivationHostileProbe

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume
open Gap2LabelErasure Gap2PostingCostDerivation Gap2LetterCostDichotomy
open Gap2FugacityPostingGluing Gap2FugacityElimination
open Gap2MeasureDerivation MeasureSubstrateBlocker
open MeasureInvarianceNoGo
open scoped Classical

noncomputable section

/-! ## A. Type fidelity: conclusion uses library `GaugeCountingPrinciple` -/

#check GaugeCountingPrinciple
#check MeasureSubstrateBlocker.GaugeCountingPrinciple
#check gap2_gauge_counting_gibbsWeight
#check gaugeCountingPrinciple_iff_mu_on_representatives
#check substrate_measure_blocker_certificate

/-- Closing theorem's `GaugeCountingPrinciple` is definitionally the blocker's. -/
theorem gcp_closing_is_blocker_gcp (B : ℕ) :
    GaugeCountingPrinciple
        (classMass (gibbsWeight : BoundedComplex B → ℝ))
      = MeasureSubstrateBlocker.GaugeCountingPrinciple
        (classMass (gibbsWeight : BoundedComplex B → ℝ)) :=
  rfl

/-! ## B. Circularity controls

(i) `gibbsWeight` is letter-level factorials (definitional).
(ii) `classMass gibbsWeight = mu` routes through C4, not `rfl`.
(iii) Uniform labeled weight `1` fails the principle (instrument not vacuous).
-/

theorem gibbsWeight_def_no_aut (K : BoundedComplex 2) :
    gibbsWeight K
      = 1 / ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ) :=
  rfl

/-- Not definitional: the bridge theorem is a real rewrite through C4. -/
theorem classMass_gibbs_eq_mu_is_not_rfl (K : BoundedComplex 2) :
    classMass (gibbsWeight : BoundedComplex 2 → ℝ) (erase 2 K) = mu K :=
  classMass_gibbs_eq_mu_via_erasure K

/-- Fiber sum of the constant labeled weight is the orbit cardinality. -/
theorem classMass_one_eq_orbit (c : TriangulationClass 2) :
    classMass (fun _ : BoundedComplex 2 => (1 : ℝ)) c = (orbitCardClass c : ℝ) := by
  rw [classMass_of_invariant _ (fun _ _ _ => rfl) c, mul_one]

/-- two-point orbit card is 1: `|Aut|=2`, factorials `2`, orbit-stabilizer. -/
theorem twoPoint_orbitCard : gaugeOrbitCard (twoPointComplex 2 (by decide)) = 1 := by
  have hOS := orbitCard_mul_autCard (twoPointComplex 2 (by decide))
  rw [autCard_twoPointComplex 2 (by decide)] at hOS
  -- abbrev sizes: nV=2, nE=0, nT=0 ⇒ RHS = 2
  norm_num [Nat.factorial] at hOS
  omega

/-- **B-iii control.** The module's target principle fails for the wrong labeled
weight `1` (class mass = fibre size = 1 on the two-point class; `mu = 1/2`). -/
theorem wrong_labeled_weight_fails_gaugeCounting :
    ¬ GaugeCountingPrinciple
      (classMass (fun _ : BoundedComplex 2 => (1 : ℝ))) := by
  intro h
  have hmu :=
    (gaugeCountingPrinciple_iff_mu_on_representatives
      (classMass (fun _ : BoundedComplex 2 => (1 : ℝ)))).mp h
      (twoPointComplex 2 (by decide))
  rw [classMass_one_eq_orbit, orbitCardClass_mk, twoPoint_orbitCard,
    mu_twoPointComplex 2 (by decide)] at hmu
  norm_num at hmu

/-- Uniqueness already in the library: only `gibbsWeight` among invariant labeled
weights induces the principle. Control that the instrument is selective. -/
theorem only_gibbs_among_invariant :
    ∀ (w : BoundedComplex 2 → ℝ),
      (∀ K K', Equivalent K K' → w K = w K') →
        GaugeCountingPrinciple (classMass w) →
          ∀ K, w K = gibbsWeight K :=
  fun w hinv h => (invariant_weight_gives_measure_iff w hinv).mp h

/-! ## E. Load-bearing dependency (proof-term inspection helpers)

The closing theorem's proof cites only the blocker iff and the C4 bridge.
These theorems exist independently of the premises certificate structure.
Cap-3 / cap-4 / C16 fields are not hypotheses of the closing declarations.
-/

#check classMass_gibbs_eq_mu_via_erasure
#check mu_eq_gibbs_mul_erasePush_one
#check pushforward_labeledWeight_eq_gauge_divisor
#check unit_fugacity_forced_by_surface_and_kindTotals
#check measureDerivationPremises
#check measureDerivationPremises_inhabited

/-- Closing theorem does not take `MeasureDerivationPremises` as an argument. -/
theorem closing_has_no_premises_arg (B : ℕ) :
    GaugeCountingPrinciple
      (classMass (gibbsWeight : BoundedComplex B → ℝ)) :=
  gap2_gauge_counting_gibbsWeight B

/-- Flag-relevant composition still does not mention cap-3/cap-4. -/
theorem composition_load_bearing_shape
    (F : CensusDilateFamily) {c : LetterCost} {a e : ℝ}
    (hc : Equivariant c) (h : FixedKindTotals c) (hs : SurfaceTotal F c a e)
    (B : ℕ) :
    GaugeCountingPrinciple (classMass (postedWeight c B))
      ∧ GaugeCountingPrinciple
          (classMass (gibbsWeight : BoundedComplex B → ℝ)) :=
  ⟨(gap2_measure_from_c4_c17 F hc h hs B).1,
    (gap2_measure_from_c4_c17 F hc h hs B).2.1⟩

/-! ## F. Exactness: blocker certificate connection -/

theorem closing_via_blocker_iff (B : ℕ) :
    GaugeCountingPrinciple
        (classMass (gibbsWeight : BoundedComplex B → ℝ))
      ↔ ∀ K : BoundedComplex B,
          classMass (gibbsWeight : BoundedComplex B → ℝ)
            (Quotient.mk (relabelSetoid B) K) = mu K :=
  gaugeCountingPrinciple_iff_mu_on_representatives _

theorem closing_lands_on_mu (B : ℕ) (K : BoundedComplex B) :
    classMass (gibbsWeight : BoundedComplex B → ℝ)
      (Quotient.mk (relabelSetoid B) K) = mu K :=
  (closing_via_blocker_iff B).mp (gap2_gauge_counting_gibbsWeight B) K

theorem blocker_certificate_available (B : ℕ) (hB : 2 ≤ B) :
    GaugeCountingPrinciple
        (gaugeOrbitMass : TriangulationClass B → ℝ) ∧
      (∀ ν : TriangulationClass B → ℝ,
        GaugeCountingPrinciple ν ↔
          ∀ K : BoundedComplex B,
            ν (Quotient.mk (relabelSetoid B) K) = mu K) ∧
      ¬ GaugeCountingPrinciple
        (uniformClassMass : TriangulationClass B → ℝ) :=
  substrate_measure_blocker_certificate B hB

/-! ## Index / flag hygiene

The flip landed 2026-07-30 in-session after this probe's verdict (MINOR, prose
repaired in A27 §5 and the flip docstring). -/

theorem flag_moved :
    Gap2MeasureDerivation.measureDerivationIndex.measure_flag_moved = true :=
  Gap2MeasureDerivation.index_flag_moved

end

/-! ## D. Independent axiom audit -/

#print axioms gap2_gauge_counting_gibbsWeight
#print axioms gap2_gauge_counting_from_surface_and_kindTotals
#print axioms gap2_measure_from_c4_c17
#print axioms classMass_gibbs_eq_mu_via_erasure
#print axioms wrong_labeled_weight_fails_gaugeCounting
#print axioms measureDerivationPremises_inhabited
#print axioms closing_lands_on_mu
#print axioms gcp_closing_is_blocker_gcp
#print axioms Gap2MeasureDerivation.index_flag_moved

end Gap2MeasureDerivationHostileProbe
end SevenGaps
end Gravity
end IndisputableMonolith
