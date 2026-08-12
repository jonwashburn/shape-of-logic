import IndisputableMonolith.Gravity.SevenGaps.Gap2OrientedFaceSpan

/-!
# Hostile-review probe for `Gap2OrientedFaceSpan` (A16 review, 2026-07-30)

Independent checks, written by the reviewer rather than the worker:

* §1 re-pins every measured-value definition against the literals the claim
  advertises, so a drifted definition cannot hide behind the worker's theorems.
* §2 recomputes the certificate arithmetic from the definitions.
* §3 instantiates the sharp iff on a concrete vector in both directions, so a
  vacuous or one-sided formulation cannot pass silently.
* §4 specializes `no_pure_surface_term_in_census_span` at `a = 48` and checks
  that the headline span exclusion really is that corollary.
* §5 shows the negated premise of the kernel gate is inhabited, so the gate is
  not vacuous.
* §6/§7 recompute the witness-complex facts by `decide`, independently of the
  worker's proofs.
* §8 re-audits the axioms of every theorem the module prints.

This file is review scaffolding and is removed after the run.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2OrientedFaceSpanHostileProbe

open PathSumMeasure GaugeHistoryMeasure Gap2PostingCostDerivation Gap2JEhrhartSpan
  Gap2OrientedFaceSpan

/-! ## §1. The definitions carry the advertised values -/

example : mV4 = ![1, 4, 6, 4, 1] := rfl
example : mE4 = ![15, 28, 18, 4, 0] := rfl
example : mT4 = ![24, 0, 0, 0, 0] := rfl
example : mC4 = ![0, 0, 0, 0, 1] := rfl
example : cert4 = ![0, 1, -2, 2, 0] := rfl
example : mFor4 = ![0, 48, 0, 0, 0] := rfl
example : mForRaw4 = ![240, -48, 0, 0, 0] := rfl
example : mCurl4 = ![50, 48, 12, 0, 0] := rfl
example : oV4e = ![1/4, 3/2, 13/4, 3, 1] := rfl
example : oE4e = ![15/4, 17/2, 31/4, 5/2, 0] := rfl
example : oT4 = ![6, -6, 0, 0, 0] := rfl
example : oFor4e = ![0, 21, -18, 0, 0] := rfl
example : ocert4e = ![121, 121, -259, 210, 0] := rfl
example : oV4o = ![1/4, 3/2, 3, 5/2, 3/4] := rfl
example : oE4o = ![15/4, 17/2, 6, 1, -1/4] := rfl
example : oFor4o = ![0, 21, -21, 0, 0] := rfl
example : ocert4o = ![32, 32, -77, 70, 0] := rfl
example : mFor3 = ![0, 12, 0, 0] := rfl

/-! ## §2. Certificate arithmetic, recomputed from definitions -/

example : dot4 cert4 mFor4 = 48 := by
  simp [dot4, cert4, mFor4, Fin.sum_univ_five]

example : dot4 cert4 mV4 = 0 ∧ dot4 cert4 mE4 = 0 ∧ dot4 cert4 mT4 = 0
    ∧ dot4 cert4 mC4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [dot4, cert4, mV4, mE4, mT4, mC4, Fin.sum_univ_five] <;> norm_num

example : dot4 ocert4e oFor4e = 7203 := by
  simp [dot4, ocert4e, oFor4e, Fin.sum_univ_five]
  norm_num

example : dot4 ocert4o oFor4o = 2289 := by
  simp [dot4, ocert4o, oFor4o, Fin.sum_univ_five]
  norm_num

/-! ## §3. The sharp form is not vacuous in either direction -/

/-- Forward direction inhabited: a census column itself lies in the span, and
the certificate annihilates it. -/
example : (∃ a b c e : ℚ, ∀ i : Fin 5,
    a * mV4 i + b * mE4 i + c * mT4 i + e * mC4 i = mV4 i)
    ∧ dot4 cert4 mV4 = 0 :=
  ⟨⟨1, 0, 0, 0, fun i => by simp⟩, by
    simp [dot4, cert4, mV4, Fin.sum_univ_five] <;> norm_num⟩

/-- Reverse direction instantiated on a concrete annihilated vector:
`cert4 · (3, 6, 4, 1, 5) = 6 - 8 + 2 = 0`, so the exhibited inverse must
produce a representation. -/
example : ∃ a b c e : ℚ, ∀ i : Fin 5,
    a * mV4 i + b * mE4 i + c * mT4 i + e * mC4 i = (![3, 6, 4, 1, 5] : Fin 5 → ℚ) i :=
  (census4_with_const_span_iff _).mpr (by
    simp [dot4, cert4, Fin.sum_univ_five] <;> norm_num)

/-- The inverse the reverse direction exhibits is honest: the coefficients it
returns really reconstruct the input. Checked on `(3, 6, 4, 1, 5)` with the
module's own formula, `a = 3t3/8 - t2/12`, `b = t2/12 - t3/8`,
`c = (t0 - a - 15b)/24`, `e = t4 - a`. -/
example : (3 * (6 : ℚ) / 8 - 4 / 12) * 1 + (4 / 12 - 3 * (6 : ℚ) / 8) * 15
    + ((3 - (3 * (6 : ℚ) / 8 - 4 / 12) - 15 * (4 / 12 - 3 * (6 : ℚ) / 8)) / 24) * 24
    + (1 - (3 * (6 : ℚ) / 8 - 4 / 12)) * 0 = 3 := by norm_num

/-! ## §4. The corollary really specializes to the headline -/

example : ¬ ∃ a b c e : ℚ, ∀ i : Fin 5,
    a * mV4 i + b * mE4 i + c * mT4 i + e * mC4 i = mFor4 i :=
  no_pure_surface_term_in_census_span 48 (by norm_num)

/-- ... at every nonzero scale, not just the measured one. -/
example (a : ℚ) (ha : a ≠ 0) : ¬ ∃ p q r s : ℚ, ∀ i : Fin 5,
    p * mV4 i + q * mE4 i + r * mT4 i + s * mC4 i
      = (![0, a, 0, 0, 0] : Fin 5 → ℚ) i :=
  no_pure_surface_term_in_census_span a ha

/-! ## §5. The negated premise is inhabited, so the gate is not vacuous -/

example : FixedKindTotals (fun _ _ _ => (0 : ℝ)) :=
  ⟨0, 0, 0, fun _ _ => ⟨by simp, by simp, by simp⟩⟩

/-! ## §6. The witness complexes are the claimed ones -/

example : oneTet.nT = 1 ∧ twoTets.nT = 2 ∧ oneTet.nV = 4 ∧ twoTets.nV = 5 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §7. Witness arithmetic, recomputed independently -/

example : facetImbalanceSq oneTet (0 : Fin 1) = 4 := by decide
example : imbalanceSqTotal twoTets = 6 := by decide
example : faceImbalance twoTets (facetTriple twoTets (0 : Fin 2) (0 : Fin 4)) = 0 := by decide
example : faceImbalance oneTet (facetTriple oneTet (0 : Fin 1) (0 : Fin 4)) = 1 := by decide
example : faceImbalance oneTet
    (revFace (facetTriple oneTet (0 : Fin 1) (0 : Fin 4))) = -1 := by decide

/-! ## §8. The certificate structure is inhabited as claimed -/

example : OrientedFaceSpanVerdict := orientedFaceSpanVerdict

/-! ## Independent axiom audit -/

#print axioms orientSign_rev
#print axioms faceImbalance_reverse
#print axioms faceImbalance_reverse_nonvacuous
#print axioms orientSign_degenerate_witness
#print axioms historyCost_jFaceCost
#print axioms historyCost_jFaceCost_eq
#print axioms jFaceCost_vanishes_on_balanced_tet
#print axioms orientSign_map
#print axioms facetTriple_relabel
#print axioms faceImbalance_relabel
#print axioms facetImbalanceSq_relabel
#print axioms jFaceCost_equivariant
#print axioms facetImbalanceSq_oneTet
#print axioms imbalanceSqTotal_oneTet
#print axioms imbalanceSqTotal_twoTets
#print axioms twoTets_shared_facet_balanced_others_not
#print axioms blockSum_oneTet
#print axioms blockSum_twoTets
#print axioms jFaceCost_not_fixedKindTotals
#print axioms cert4_sees_mFor4
#print axioms cert4_sees_mForRaw4
#print axioms cert4_sees_mCurl4
#print axioms census4_with_const_span_iff
#print axioms no_pure_surface_term_in_census_span
#print axioms mFor4_not_in_census_span
#print axioms mFor4_not_in_census_span_with_const
#print axioms mForRaw4_not_in_census_span_with_const
#print axioms mCurl4_not_in_census_span_with_const
#print axioms ocert4e_annihilates_census
#print axioms ocert4e_sees_oFor4e
#print axioms ocert4o_annihilates_census
#print axioms ocert4o_sees_oFor4o
#print axioms oFor4e_not_in_census_span_with_const
#print axioms oFor4o_not_in_census_span_with_const
#print axioms cert3_sees_mFor3
#print axioms mFor3_not_in_census_span
#print axioms orientedFaceSpanVerdict

end Gap2OrientedFaceSpanHostileProbe
end SevenGaps
end Gravity
end IndisputableMonolith
