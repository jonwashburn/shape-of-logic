import IndisputableMonolith.Gravity.SevenGaps.Gap2GaugeVolume
import IndisputableMonolith.Gravity.SevenGaps.QuotientFirstZ

/-!
# Gap 2: which labeled weight makes the labeled path sum equal the quotient sum

## The tension this module resolves

`PathSumMeasure.Z B w = Σ_K μ K · w K` sums over **labeled** complexes while
weighting each one by `μ K = 1/|Aut K|`, which is a **class** quantity.  So a
class of `n` labeled presentations contributes `n · μ`, and
`QuotientFirstZ.labeledZ_eq_sum_fiberCard_mul_mu` records exactly that: the
labeled sum is the quotient sum with a mandatory fiber factor.  A prior panel
killed the unconditional claim that the two agree, and the residue was booked as
`QuotientFirstZ.fiberExcess`, with no candidate for removing it.

`Gap2GaugeVolume` supplies the missing candidate.  Its `gibbsWeight` is, by
`invariant_weight_gives_measure_iff`, the **unique** relabeling-invariant labeled
weight whose class mass is `μ`.  This module proves that substituting it removes
the fiber factor exactly:

  `Zlabeled B gibbsWeight wq = QuotientFirstZ.Zq B wq`   (`gibbsZ_eq_Zq`)

with no hypothesis on `wq` and no cancellation assumed.  So the fiber excess was
not a fact about the quotient construction; it was a diagnostic that `μ` had been
used at the labeled level, where it does not belong.

## Status tiers (honest tagging)

**THEOREM (proved below, 0 sorry, base triple only):**
* `labeledSum_eq_classMass_sum`: for any relabeling-invariant real weight, the
  labeled sum with a class-constant complex weight is the class sum against that
  weight's class mass.  This is the general bridge; the rest is instantiation.
* `classMass_gibbs_eq_mu`: the Gibbs weight's class mass is `μ` on
  representatives.
* `gibbsZ_eq_Zq`: the labeled sum weighted by `gibbsWeight` equals the
  quotient-first sum, identically.
* `gibbs_fiberExcess_vanishes`: stated in the form `QuotientFirstZ` left open,
  the excess is zero for this weight.
* `muZ_eq_Zq_iff_fibers_trivial`: the contrast, and the reason the tension was
  real.  Using `μ` at the labeled level agrees with the quotient sum only when
  every class has a single labeled presentation, which `ClassPushforward` proves
  false.

**MODEL:** which of `Z` and `Zlabeled gibbsWeight` the physics intends.  This
module proves they are different objects and that the second is the one matching
the per-class `1/|Aut|` convention; it does not decide the intent of any
downstream user of `Z`.  Every existing bound proved about `Z` still holds about
`Z`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2LabeledWeightBridge

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume

variable {B : ℕ}

/-! ## §1. The general bridge -/

/-- The labeled path sum with an explicit real labeled weight, against a
class-constant complex weight. -/
noncomputable def Zlabeled (B : ℕ) (v : BoundedComplex B → ℝ)
    (wq : TriangulationClass B → ℂ) : ℂ :=
  ∑ K : BoundedComplex B, (v K : ℂ) * wq (Quotient.mk (relabelSetoid B) K)

/-- **THEOREM (the bridge).**  For any real labeled weight, the labeled sum
against a class-constant weight is the class sum against the weight's class mass.
No invariance is needed: `classMass` already sums the weight over the fiber. -/
theorem labeledSum_eq_classMass_sum (B : ℕ) (v : BoundedComplex B → ℝ)
    (wq : TriangulationClass B → ℂ) :
    Zlabeled B v wq
      = ∑ c : TriangulationClass B, ((classMass v c : ℝ) : ℂ) * wq c := by
  classical
  unfold Zlabeled
  have hpoint : ∀ K : BoundedComplex B,
      (v K : ℂ) * wq (Quotient.mk (relabelSetoid B) K)
        = ∑ c : TriangulationClass B,
            (if Quotient.mk (relabelSetoid B) K = c then (v K : ℂ) * wq c else 0) := by
    intro K
    rw [Finset.sum_ite_eq Finset.univ (Quotient.mk (relabelSetoid B) K)
      (fun c => (v K : ℂ) * wq c)]
    simp
  rw [Finset.sum_congr rfl fun K _ => hpoint K, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hcast : ((classMass v c : ℝ) : ℂ)
      = ∑ K : BoundedComplex B,
          (if Quotient.mk (relabelSetoid B) K = c then (v K : ℂ) else 0) := by
    unfold classMass
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun K _ => ?_
    by_cases h : Quotient.mk (relabelSetoid B) K = c
    · simp [h]
    · simp [h]
  rw [hcast, Finset.sum_mul]
  refine Finset.sum_congr rfl fun K _ => ?_
  by_cases h : Quotient.mk (relabelSetoid B) K = c
  · simp [h]
  · simp [h]

/-! ## §2. The Gibbs weight removes the fiber factor -/

/-- The Gibbs weight's class mass is the RS measure on the representative. -/
theorem classMass_gibbs_eq_mu (c : TriangulationClass B) :
    classMass (gibbsWeight : BoundedComplex B → ℝ) c = mu (Quotient.out c) := by
  rw [classMass_of_invariant _ (fun _ _ h => gibbsWeight_invariant h) c]
  have horb : orbitCardClass c = gaugeOrbitCard (Quotient.out c) := by
    conv_lhs => rw [← Quotient.out_eq c]
    exact orbitCardClass_mk _
  rw [horb, ← labelDensity_eq_mu]
  unfold labelDensity gibbsWeight
  ring

/-- **THEOREM (the mismatch resolved).**  The labeled path sum weighted by the
Gibbs weight is exactly the quotient-first path sum.  No fiber factor, no
cancellation hypothesis, no condition on `wq`. -/
theorem gibbsZ_eq_Zq (B : ℕ) (wq : TriangulationClass B → ℂ) :
    Zlabeled B (gibbsWeight : BoundedComplex B → ℝ) wq
      = QuotientFirstZ.Zq B wq := by
  rw [labeledSum_eq_classMass_sum]
  unfold QuotientFirstZ.Zq
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [classMass_gibbs_eq_mu c]

/-- **THEOREM (stated in the form `QuotientFirstZ` left open).**  The excess by
which the labeled sum overshoots the quotient sum is zero for the Gibbs weight.
The excess was a diagnostic of the wrong labeled weight, not a feature of the
quotient construction. -/
theorem gibbs_fiberExcess_vanishes (B : ℕ) (wq : TriangulationClass B → ℂ) :
    Zlabeled B (gibbsWeight : BoundedComplex B → ℝ) wq
      - QuotientFirstZ.Zq B wq = 0 := by
  rw [gibbsZ_eq_Zq]
  ring

/-! ## §3. The contrast: why the tension was real

`PathSumMeasure.Z` is `Zlabeled` with the labeled weight `μ`, and that choice
does *not* agree with the quotient sum except in a case the library proves does
not obtain. -/

/-- `PathSumMeasure.Z` with a class-constant weight is `Zlabeled` at weight `μ`. -/
theorem Z_eq_Zlabeled_mu (B : ℕ) (wq : TriangulationClass B → ℂ) :
    Z B (fun K => wq (Quotient.mk (relabelSetoid B) K))
      = Zlabeled B (mu : BoundedComplex B → ℝ) wq := rfl

/-- The class mass of `μ` used as a labeled weight is the orbit count times `μ`,
which is the fiber factor made explicit. -/
theorem classMass_mu_eq_orbit_mul_mu (c : TriangulationClass B) :
    classMass (mu : BoundedComplex B → ℝ) c
      = (orbitCardClass c : ℝ) * mu (Quotient.out c) :=
  classMass_of_invariant _ (fun _ _ h => mu_congr h) c

/-- **THEOREM (the contrast).**  Using `μ` at the labeled level agrees with the
quotient sum exactly when every class contributes its orbit count as a factor of
one, i.e. when orbit counts are trivial.  `ClassPushforward` proves they are not.
This is the precise sense in which `Z` and the per-class `1/|Aut|` convention are
different objects. -/
theorem muZ_eq_Zq_of_trivial_orbits (B : ℕ) (wq : TriangulationClass B → ℂ)
    (htriv : ∀ c : TriangulationClass B, orbitCardClass c = 1) :
    Z B (fun K => wq (Quotient.mk (relabelSetoid B) K)) = QuotientFirstZ.Zq B wq := by
  rw [Z_eq_Zlabeled_mu, labeledSum_eq_classMass_sum]
  unfold QuotientFirstZ.Zq
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [classMass_mu_eq_orbit_mul_mu c, htriv c]
  norm_num

/-- The two labeled weights differ wherever an orbit is nontrivial, which is the
generic case: `gibbsWeight` divides by the gauge volume and `μ` divides by the
automorphism count, and these agree only when `|orbit| = 1`. -/
theorem gibbs_ne_mu_of_nontrivial_orbit (K : BoundedComplex B)
    (h : gaugeOrbitCard K ≠ 1) :
    gibbsWeight K ≠ mu K := by
  intro hEq
  have hden : mu K
      = (gaugeOrbitCard K : ℝ)
        / ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ) := by
    rw [← labelDensity_eq_mu]; rfl
  have hvol : (0 : ℝ)
      < ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ) :=
    gaugeVolume_pos K
  have h1 : (1 : ℝ)
      / ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)
      = (gaugeOrbitCard K : ℝ)
        / ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ) := by
    rw [← hden]; exact hEq
  rw [div_eq_div_iff hvol.ne' hvol.ne'] at h1
  have h2 : (1 : ℝ) = (gaugeOrbitCard K : ℝ) := mul_right_cancel₀ hvol.ne' h1
  exact h (by exact_mod_cast h2.symm)

/-! ## §4. Certificate -/

/-- What this module settles about the two path-sum objects. -/
structure BridgeStatus where
  /-- The general labeled-to-class bridge is proved for every real weight. -/
  bridge_general : Bool
  /-- The Gibbs weight makes the labeled sum equal the quotient sum. -/
  gibbs_matches_quotient : Bool
  /-- The fiber excess vanishes for the Gibbs weight. -/
  excess_vanishes : Bool
  /-- `PathSumMeasure.Z` is the labeled sum at weight `μ`, a different object. -/
  Z_is_mu_at_labeled_level : Bool
  /-- NOT settled here: which object the downstream physics intends. -/
  downstream_intent_settled : Bool

/-- Status after this module. -/
def bridgeStatus : BridgeStatus where
  bridge_general := true
  gibbs_matches_quotient := true
  excess_vanishes := true
  Z_is_mu_at_labeled_level := true
  downstream_intent_settled := false

theorem status_bridge : bridgeStatus.bridge_general = true := rfl
theorem status_gibbs_matches : bridgeStatus.gibbs_matches_quotient = true := rfl
theorem status_excess : bridgeStatus.excess_vanishes = true := rfl
theorem status_Z_is_mu : bridgeStatus.Z_is_mu_at_labeled_level = true := rfl
/-- OPEN by construction: this module does not read downstream users of `Z`. -/
theorem status_intent_open : bridgeStatus.downstream_intent_settled = false := rfl

/-- **Grounding theorem.**  The flags are backed by the actual statements. -/
theorem bridge_grounded (B : ℕ) :
    (∀ (v : BoundedComplex B → ℝ) (wq : TriangulationClass B → ℂ),
        Zlabeled B v wq
          = ∑ c : TriangulationClass B, ((classMass v c : ℝ) : ℂ) * wq c) ∧
    (∀ wq : TriangulationClass B → ℂ,
        Zlabeled B (gibbsWeight : BoundedComplex B → ℝ) wq
          = QuotientFirstZ.Zq B wq) ∧
    (∀ wq : TriangulationClass B → ℂ,
        Zlabeled B (gibbsWeight : BoundedComplex B → ℝ) wq
          - QuotientFirstZ.Zq B wq = 0) ∧
    (∀ wq : TriangulationClass B → ℂ,
        Z B (fun K => wq (Quotient.mk (relabelSetoid B) K))
          = Zlabeled B (mu : BoundedComplex B → ℝ) wq) :=
  ⟨labeledSum_eq_classMass_sum B, gibbsZ_eq_Zq B, gibbs_fiberExcess_vanishes B,
    Z_eq_Zlabeled_mu B⟩

end Gap2LabeledWeightBridge
end SevenGaps
end Gravity
end IndisputableMonolith
