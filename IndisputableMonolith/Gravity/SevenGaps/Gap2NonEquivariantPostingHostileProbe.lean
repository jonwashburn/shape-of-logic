import IndisputableMonolith.Gravity.SevenGaps.Gap2NonEquivariantPosting

/-!
# Hostile review probe for `Gap2NonEquivariantPosting` (2026-07-29)

Not part of any build target and not imported by anything.  Six adversarial checks that the
module under review does not itself make, each written to fail loudly if the module's machinery
is vacuous or its hypotheses are decoration:

1. `probe_criterion_discriminates`: the orbit-mean-one criterion is NOT satisfied by every cost.
   A cost the library already proved does not post `mu` (`incidenceCost 1`) must fail it.
2. `probe_twist_moves_loopAndBridge`: the twist is not the identity at the witness complex, so
   the cancelling pair is two distinct labeled complexes.
3. `probe_orbit_nontrivial`: the gauge orbit of the witness complex has more than one member,
   so "orbit mean one" is not secretly "the single term is one".
4. `probe_witness_not_gibbs`: the witness's labeled weight really differs from `gibbsWeight`.
5. `probe_family_distinguishable`: distinct tilts give distinct LABELED WEIGHTS, not merely
   distinct numerators, so the family does not collapse.
6. `probe_tilt_one_breaks_the_identity`: the `|t| < 1` hypothesis is load-bearing; at `t = 1`
   the numerator identity is false.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2NonEquivariantPostingHostileProbe

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume Gap2GluingDerivation
open GaugeHistoryMeasure Gap2SizeBlindnessReach Gap2PostingCostDerivation
open Gap2NonEquivariantPosting

noncomputable section

/-- **DISCRIMINATION.**  The criterion is not vacuously true.  `incidenceCost 1` is a cost the
library already proved does not post `mu` at the two-bridge class, so the criterion must report
a numerator mass different from the orbit count there. -/
theorem probe_criterion_discriminates :
    numeratorMass (incidenceCost 1) 2 (Quotient.mk (relabelSetoid 2) twoBridges)
      ≠ (gaugeOrbitCard twoBridges : ℝ) := by
  intro h
  exact incidencePosting_classMass_ne_mu (one_ne_zero)
    ((posts_mu_iff_numeratorMass_eq_orbitCard (incidenceCost 1) 2 twoBridges).mpr h)

/-- The twist genuinely moves the witness complex. -/
theorem probe_twist_moves_loopAndBridge : twist loopAndBridge ≠ loopAndBridge := by
  intro h
  have h1 : edgeSign (twist loopAndBridge) = -edgeSign loopAndBridge :=
    edgeSign_twist loopAndBridge
  rw [h, edgeSign_loopAndBridge] at h1
  norm_num at h1

/-- The gauge orbit of the witness complex has at least two labeled members. -/
theorem probe_orbit_nontrivial : 1 < gaugeOrbitCard loopAndBridge := by
  have hne : twist loopAndBridge ≠ loopAndBridge := probe_twist_moves_loopAndBridge
  haveI hnt : Nontrivial {K' : BoundedComplex 3 // Equivalent loopAndBridge K'} := by
    refine ⟨⟨⟨loopAndBridge, ⟨Relabel.refl _⟩⟩,
      ⟨twist loopAndBridge, twist_equivalent loopAndBridge⟩, ?_⟩⟩
    intro hEq
    exact hne (congrArg Subtype.val hEq).symm
  unfold gaugeOrbitCard
  first
    | exact Finite.one_lt_card_iff_nontrivial.mpr hnt
    | exact Nat.one_lt_card_iff_nontrivial.mpr hnt
    | exact Nat.one_lt_card_iff_nontrivial.2 hnt

/-- The witness's labeled weight is not the Gibbs weight. -/
theorem probe_witness_not_gibbs {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0) :
    postedWeight (tiltedCost t) 3 loopAndBridge ≠ gibbsWeight loopAndBridge := by
  intro h
  rw [postedWeight_tiltedCost ht, tiltedNumer_loopAndBridge] at h
  have hg : (0 : ℝ) < gibbsWeight loopAndBridge := gibbsWeight_positive loopAndBridge
  have h1 : (1 + t) * gibbsWeight loopAndBridge = 1 * gibbsWeight loopAndBridge := by
    rw [one_mul]; exact h
  have h2 : (1 : ℝ) + t = 1 := mul_right_cancel₀ (ne_of_gt hg) h1
  exact ht0 (by linarith)

/-- Distinct tilts give distinct labeled weights, so the family is not invisible at the weight. -/
theorem probe_family_distinguishable {t s : ℝ} (ht : |t| < 1) (hs : |s| < 1) (hts : t ≠ s) :
    postedWeight (tiltedCost t) 3 loopAndBridge
      ≠ postedWeight (tiltedCost s) 3 loopAndBridge := by
  intro h
  rw [postedWeight_tiltedCost ht, postedWeight_tiltedCost hs] at h
  have hg : (0 : ℝ) < gibbsWeight loopAndBridge := gibbsWeight_positive loopAndBridge
  exact hts (family_injective_at_loopAndBridge (mul_right_cancel₀ (ne_of_gt hg) h))

/-- The `|t| < 1` hypothesis is load-bearing: at `t = 1` the numerator identity fails, because
the twisted witness has numerator `0` and an exponential is never `0`. -/
theorem probe_tilt_one_breaks_the_identity :
    Real.exp (-(historyCost (tiltedCost 1) 3 (twist loopAndBridge)))
      ≠ tiltedNumer 1 (twist loopAndBridge) := by
  have hs : edgeSign (twist loopAndBridge) = -1 := by
    rw [edgeSign_twist, edgeSign_loopAndBridge]
  have hnum : tiltedNumer (1 : ℝ) (twist loopAndBridge) = 0 := by
    unfold tiltedNumer
    rw [hs]
    norm_num
  rw [hnum]
  exact (Real.exp_pos _).ne'

end

#print axioms probe_criterion_discriminates
#print axioms probe_twist_moves_loopAndBridge
#print axioms probe_orbit_nontrivial
#print axioms probe_witness_not_gibbs
#print axioms probe_family_distinguishable
#print axioms probe_tilt_one_breaks_the_identity

end Gap2NonEquivariantPostingHostileProbe
end SevenGaps
end Gravity
end IndisputableMonolith
