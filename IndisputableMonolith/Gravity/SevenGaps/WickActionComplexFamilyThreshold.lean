import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import IndisputableMonolith.Gravity.SevenGaps.CausalSimplex4D
import IndisputableMonolith.Gravity.SevenGaps.WickActionCertAssembly

/-!
# Work item 5 (outcome b): Wick continuation threshold is complex-dependent

Pillar 1 strengthen campaign, 2026-07-25. The action-level Wick certificate
(`WickActionContinuationCertV2`) hardcodes the causal range `α > 7/12` on one
fixed three-pent one-hinge complex of type `threeTwo`. Referees correctly
objected that this does not generalize as a complex-independent constant.

This module converts that scope caveat into a structural finding: the
kinematical Wick Euclidean-admission threshold for causal 4-simplices is
already type-dependent in `CausalSimplex4D.alphaMin`, with

* `alphaMin fourOne = 3/8`,
* `alphaMin threeTwo = 7/12`,

and these are exact (iff) gates for `cm4 > 0` after Wick. The action-level
hardcoded `7/12` is therefore the `threeTwo` member of this threshold
function, not a universal constant. Outcome (a) (action-level continuation
for a genuine multi-complex family) is not attempted here: the CertV2
surface is specialized to the collapsed threeTwo one-hinge Möbius path, and
generalizing that analytic chain is a separate campaign.

Two statements carry the weight, and they point opposite ways, which is the
honest picture. `universal_sufficient_threshold_eq_max` says `7/12` *is* a
complex-independent **sufficient** threshold: above it every type in the class
continues, because it is the maximum of the two type thresholds.
`no_common_typewise_exact_threshold` says it is not a complex-independent
**exact** gate: no constant is equivalent to admission for every type, since
`fourOne` continues down to `3/8`. So the hardcoded constant is defensible as a
sufficient condition and indefensible as a threshold, and the window
`(3/8, 7/12)` is where the difference is visible.

The action-level consequence is `no_certV2_in_fourOne_only_window`: in that
window a `fourOne` simplex admits Euclidean continuation and no
`WickActionContinuationCertV2` exists at all, since the certificate's
`causalRange` field is `7/12 < α` by construction.

Honesty:
* THEOREM: every declared theorem below is sorry-free; axioms are the
  standard Mathlib trio only.
* SCOPE: kinematical Wick Euclidean admission (`cm4 > 0` after `wick` of the
  Lorentzian causal tuple). This is the gate that decides which causal
  complexes admit Euclidean continuation; it is not a re-proof of the
  action-level `carccos` cut-limit chain.
* STRENGTH: the class has exactly two members, the two CDT causal 4-simplex
  types, so "non-constant threshold" is witnessed by one pair `(3/8, 7/12)`
  and the gap window `(3/8, 7/12)` is a single interval, not a family trend.
  Two members suffice to refute universality and do not establish a law.
  `alphaMin` and `cm4_euclidean_pos_iff` were both already banked; what is new
  here is the non-existence statement, the window, and the projection of the
  certificate's constant.
* OPEN, and this is why the referee objection is **not** closed: the
  action-level `WickActionContinuationCertV2` chain remains proved only on the
  collapsed `threeTwo` one-hinge Möbius path. Extending the `carccos` branch
  and cut-limit control to `fourOne` is the repair the referee actually asked
  for, and it is not attempted here. Kinematical non-degeneracy supplies none
  of that analytic content.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace WickActionComplexFamilyThreshold

open CausalSimplex4D

noncomputable section

/-! ## §1. Common class and general threshold function -/

/-- Index of the class whose Wick Euclidean-admission threshold is tracked: the
two CDT causal 4-simplex types.

Read this honestly. It is a one-field wrapper over a two-constructor enum. It
carries no simplices, no incidence, and no gluing, so it is a label for "which
causal type", not a model of a complex. The geometric content lives entirely in
`lorentzianSqEdges` and `cm4`, which the threshold theorems below call. -/
structure CausalWickComplex where
  ty : CausalPentType

/-- The two inhabitants of the common class. -/
def fourOneComplex : CausalWickComplex := ⟨CausalPentType.fourOne⟩

def threeTwoComplex : CausalWickComplex := ⟨CausalPentType.threeTwo⟩

/-- General threshold function on the common class: the exact cm4
non-degeneracy gate after Wick Euclideanization. -/
def wickContinuationThreshold (K : CausalWickComplex) : ℝ :=
  alphaMin K.ty

/-- Type-level form of the same threshold function (convenient for
quantification over `CausalPentType`). -/
def wickContinuationThresholdOf (ty : CausalPentType) : ℝ :=
  alphaMin ty

theorem wickContinuationThreshold_eq_alphaMin (K : CausalWickComplex) :
    wickContinuationThreshold K = alphaMin K.ty :=
  rfl

theorem wickContinuationThreshold_fourOne :
    wickContinuationThreshold fourOneComplex = (3 / 8 : ℝ) := by
  simp only [wickContinuationThreshold, fourOneComplex, alphaMin_fourOne]

theorem wickContinuationThreshold_threeTwo :
    wickContinuationThreshold threeTwoComplex = (7 / 12 : ℝ) := by
  simp only [wickContinuationThreshold, threeTwoComplex, alphaMin_threeTwo]

/-! ## §2. The thresholds differ -/

/-- THEOREM (outcome b, core): the two members of the common class have
provably different continuation thresholds. -/
theorem wickContinuationThresholds_differ :
    wickContinuationThreshold fourOneComplex ≠
      wickContinuationThreshold threeTwoComplex := by
  rw [wickContinuationThreshold_fourOne, wickContinuationThreshold_threeTwo]
  norm_num

/-- Strict inequality form used by gap witnesses. -/
theorem wickContinuationThreshold_fourOne_lt_threeTwo :
    wickContinuationThreshold fourOneComplex <
      wickContinuationThreshold threeTwoComplex := by
  rw [wickContinuationThreshold_fourOne, wickContinuationThreshold_threeTwo]
  norm_num

/-- The class has at least two distinct inhabitants (distinct types). -/
theorem causalWickComplex_two_inhabitants :
    fourOneComplex.ty ≠ threeTwoComplex.ty := by
  simp only [fourOneComplex, threeTwoComplex]
  intro h
  cases h

/-! ## §3. Exact gate: admission iff above the type's threshold -/

/-- Kinematical Wick Euclidean admission: after Wick of the Lorentzian
causal tuple, the cm4 positivity criterion holds. -/
def WickEuclideanAdmissible (ty : CausalPentType) (a α : ℝ) : Prop :=
  0 < cm4 (wick ty (lorentzianSqEdges ty a α))

/-- THEOREM: for every causal type and every positive spacelike scale, Wick
Euclidean admission holds if and only if the CDT ratio strictly exceeds that
type's threshold. This is the general threshold function made load-bearing. -/
theorem wickEuclideanAdmissible_iff (ty : CausalPentType) (a α : ℝ)
    (ha : 0 < a) :
    WickEuclideanAdmissible ty a α ↔
      wickContinuationThresholdOf ty < α := by
  unfold WickEuclideanAdmissible wickContinuationThresholdOf
  rw [wick_lorentzian]
  exact cm4_euclidean_pos_iff ty a α ha

/-- Forward direction packaged for direct use. -/
theorem wickEuclideanAdmissible_of_gt_threshold (ty : CausalPentType)
    (a α : ℝ) (ha : 0 < a)
    (hα : wickContinuationThresholdOf ty < α) :
    WickEuclideanAdmissible ty a α :=
  (wickEuclideanAdmissible_iff ty a α ha).mpr hα

/-- Degeneracy exactly at threshold (exactness of the gate). -/
theorem wickEuclideanAdmissible_false_at_threshold (ty : CausalPentType)
    (a : ℝ) (ha : 0 < a) :
    ¬ WickEuclideanAdmissible ty a (wickContinuationThresholdOf ty) := by
  intro h
  have hiff := (wickEuclideanAdmissible_iff ty a
    (wickContinuationThresholdOf ty) ha).mp h
  exact lt_irrefl _ hiff

/-! ## §4. Gap witness: one ratio admits fourOne and rejects threeTwo -/

/-- THEOREM (outcome b, structural witness): there exists a CDT ratio at which
the fourOne complex admits Wick Euclidean continuation and the threeTwo
complex does not. Concrete value `α = 1/2`, which lies strictly between
`3/8` and `7/12`. -/
theorem wickThreshold_gap_witness :
    ∃ α : ℝ,
      wickContinuationThreshold fourOneComplex < α ∧
        α < wickContinuationThreshold threeTwoComplex ∧
          (∀ a : ℝ, 0 < a → WickEuclideanAdmissible CausalPentType.fourOne a α) ∧
            ∀ a : ℝ, 0 < a →
              ¬ WickEuclideanAdmissible CausalPentType.threeTwo a α := by
  refine ⟨(1 / 2 : ℝ), ?_, ?_, ?_, ?_⟩
  · rw [wickContinuationThreshold_fourOne]; norm_num
  · rw [wickContinuationThreshold_threeTwo]; norm_num
  · intro a ha
    exact wickEuclideanAdmissible_of_gt_threshold CausalPentType.fourOne a (1 / 2)
      ha (by simp only [wickContinuationThresholdOf, alphaMin_fourOne]; norm_num)
  · intro a ha hAdm
    have hiff :=
      (wickEuclideanAdmissible_iff CausalPentType.threeTwo a (1 / 2) ha).mp hAdm
    simp only [wickContinuationThresholdOf, alphaMin_threeTwo] at hiff
    linarith

/-! ## §5. No complex-independent threshold exists -/

/-- The threshold function is not constant on the class. -/
theorem wickContinuationThresholdOf_not_constant :
    ¬ ∃ c : ℝ, ∀ ty : CausalPentType, wickContinuationThresholdOf ty = c := by
  rintro ⟨c, h⟩
  have h41 := h CausalPentType.fourOne
  have h32 := h CausalPentType.threeTwo
  simp only [wickContinuationThresholdOf, alphaMin_fourOne, alphaMin_threeTwo]
    at h41 h32
  rw [← h32] at h41
  norm_num at h41

/-- **THEOREM.** No single real constant is *equivalent* to Wick Euclidean
admission for every causal type. Read the name literally: this refutes a
constant **exact** gate, and it does not refute a constant sufficient one, which
§6 supplies. A number written as "the" continuation threshold is a fact about
one type. -/
theorem no_common_typewise_exact_threshold :
    ¬ ∃ c : ℝ, ∀ (ty : CausalPentType) (a α : ℝ), 0 < a →
      (WickEuclideanAdmissible ty a α ↔ c < α) := by
  rintro ⟨c, h⟩
  have hone : (0 : ℝ) < 1 := one_pos
  have hadm41 : WickEuclideanAdmissible CausalPentType.fourOne 1 (1 / 2) :=
    wickEuclideanAdmissible_of_gt_threshold CausalPentType.fourOne 1 (1 / 2) hone
      (by simp only [wickContinuationThresholdOf, alphaMin_fourOne]; norm_num)
  have hc : c < 1 / 2 :=
    (h CausalPentType.fourOne 1 (1 / 2) hone).mp hadm41
  have hadm32 : WickEuclideanAdmissible CausalPentType.threeTwo 1 (1 / 2) :=
    (h CausalPentType.threeTwo 1 (1 / 2) hone).mpr hc
  have hlt :=
    (wickEuclideanAdmissible_iff CausalPentType.threeTwo 1 (1 / 2) hone).mp hadm32
  simp only [wickContinuationThresholdOf, alphaMin_threeTwo] at hlt
  linarith

/-! ## §6. The constant `7/12` is sufficient for the class, exact for one type -/

/-- Arithmetic identification of the constant with the `threeTwo` threshold.
This is a numeric fact about two rationals; it is **not** evidence that the
certificate's constant was derived from `alphaMin`. In
`WickActionCertAssembly` the field `causalRange : 7/12 < α` is a hardcoded
literal. The projection theorem `certV2_above_threeTwo_threshold` in §7 is what
actually connects the two. -/
theorem hardcodedConstant_eq_threeTwo_threshold :
    (7 / 12 : ℝ) = wickContinuationThreshold threeTwoComplex :=
  wickContinuationThreshold_threeTwo.symm

/-- THEOREM: that constant is strictly larger than the fourOne threshold, so a
complex-independent reading of `7/12` as *the* threshold overstates the fourOne
gate. -/
theorem hardcodedConstant_gt_fourOne_threshold :
    wickContinuationThreshold fourOneComplex < (7 / 12 : ℝ) := by
  rw [hardcodedConstant_eq_threeTwo_threshold]
  exact wickContinuationThreshold_fourOne_lt_threeTwo

/-- **THEOREM: `7/12` is a genuine complex-independent SUFFICIENT threshold.**
Joint admission of both types is equivalent to `7/12 < α`, which is the maximum
of the two type thresholds. This is the positive companion of
`no_common_typewise_exact_threshold`, and it is why the hardcoded constant is
defensible as a sufficient condition even though it is not the threshold. -/
theorem joint_wickEuclideanAdmissible_iff (a α : ℝ) (ha : 0 < a) :
    (WickEuclideanAdmissible CausalPentType.fourOne a α ∧
      WickEuclideanAdmissible CausalPentType.threeTwo a α) ↔
      (7 / 12 : ℝ) < α := by
  constructor
  · intro ⟨_, h32⟩
    have := (wickEuclideanAdmissible_iff CausalPentType.threeTwo a α ha).mp h32
    simpa [wickContinuationThresholdOf, alphaMin_threeTwo] using this
  · intro hα
    exact ⟨
      wickEuclideanAdmissible_of_gt_threshold CausalPentType.fourOne a α ha
        (by simp only [wickContinuationThresholdOf, alphaMin_fourOne]; linarith),
      wickEuclideanAdmissible_of_gt_threshold CausalPentType.threeTwo a α ha
        (by simp only [wickContinuationThresholdOf, alphaMin_threeTwo]; exact hα)⟩

/-- Named form of the same fact: the complex-independent sufficient threshold is
the maximum of the type thresholds. -/
theorem universal_sufficient_threshold_eq_max (a α : ℝ) (ha : 0 < a) :
    (WickEuclideanAdmissible CausalPentType.fourOne a α ∧
      WickEuclideanAdmissible CausalPentType.threeTwo a α) ↔
      max (wickContinuationThreshold fourOneComplex)
        (wickContinuationThreshold threeTwoComplex) < α := by
  rw [joint_wickEuclideanAdmissible_iff a α ha,
    max_eq_right (le_of_lt wickContinuationThreshold_fourOne_lt_threeTwo),
    wickContinuationThreshold_threeTwo]

/-! ## §7. Projecting the certificate's own constant -/

/-- **THEOREM: every action-level certificate lives strictly above the
`threeTwo` kinematical threshold.** This consumes the certificate's
`causalRange` field, so unlike the arithmetic identification in §6 it is a
statement about `WickActionContinuationCertV2` itself. -/
theorem certV2_above_threeTwo_threshold {α : ℝ}
    (h : WickActionInteriorHinge.WickActionContinuationCertV2 α) :
    wickContinuationThreshold threeTwoComplex < α := by
  rw [wickContinuationThreshold_threeTwo]
  exact h.causalRange

/-- **THEOREM: the window is real at the action level too.** For any CDT ratio
strictly between the two thresholds, a `fourOne` simplex admits Euclidean
continuation and no action-level certificate exists. This is the precise sense
in which `7/12` is a scope boundary of the certificate rather than of the
geometry. -/
theorem no_certV2_in_fourOne_only_window {α : ℝ}
    (h2 : α < wickContinuationThreshold threeTwoComplex) :
    ¬ WickActionInteriorHinge.WickActionContinuationCertV2 α := by
  intro h
  exact absurd (certV2_above_threeTwo_threshold h) (not_lt.mpr (le_of_lt h2))

/-- Concrete witness of that window at `α = 1/2`: `fourOne` continues for every
positive spacelike scale, and no certificate exists. -/
theorem fourOne_only_window_witness :
    (∀ a : ℝ, 0 < a → WickEuclideanAdmissible CausalPentType.fourOne a (1 / 2)) ∧
      ¬ WickActionInteriorHinge.WickActionContinuationCertV2 (1 / 2) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · exact wickEuclideanAdmissible_of_gt_threshold CausalPentType.fourOne a (1 / 2)
      ha (by simp only [wickContinuationThresholdOf, alphaMin_fourOne]; norm_num)
  · refine no_certV2_in_fourOne_only_window ?_
    rw [wickContinuationThreshold_threeTwo]
    norm_num

end

/-! ## Axiom audit

Expected for each: `[propext, Classical.choice, Quot.sound]`. -/

#print axioms wickContinuationThreshold_eq_alphaMin
#print axioms wickContinuationThreshold_fourOne
#print axioms wickContinuationThreshold_threeTwo
#print axioms wickContinuationThresholds_differ
#print axioms wickContinuationThreshold_fourOne_lt_threeTwo
#print axioms causalWickComplex_two_inhabitants
#print axioms wickEuclideanAdmissible_iff
#print axioms wickEuclideanAdmissible_of_gt_threshold
#print axioms wickEuclideanAdmissible_false_at_threshold
#print axioms wickThreshold_gap_witness
#print axioms wickContinuationThresholdOf_not_constant
#print axioms no_common_typewise_exact_threshold
#print axioms hardcodedConstant_eq_threeTwo_threshold
#print axioms hardcodedConstant_gt_fourOne_threshold
#print axioms joint_wickEuclideanAdmissible_iff
#print axioms universal_sufficient_threshold_eq_max
#print axioms certV2_above_threeTwo_threshold
#print axioms no_certV2_in_fourOne_only_window
#print axioms fourOne_only_window_witness

end WickActionComplexFamilyThreshold
end SevenGaps
end Gravity
end IndisputableMonolith
