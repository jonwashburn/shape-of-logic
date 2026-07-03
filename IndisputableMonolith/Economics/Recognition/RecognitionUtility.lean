import IndisputableMonolith.Cost.AczelProof
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Economics.Recognition.Core

/-!
# Recognition Utility Representation

This module gives the economics-facing wrapper around the already-proved
Law-of-Logic cost theorem. It states the axioms as comparison-cost assumptions
for economic ratios and concludes that the calibrated comparison cost is exactly
`Jcost`.
-/

namespace IndisputableMonolith
namespace Economics
namespace Recognition

open IndisputableMonolith.Cost

noncomputable section

/-- Economic comparison-cost axioms. These are intentionally the same load-bearing
conditions as the Law-of-Logic theorem, but named in decision-theoretic language.

`monotone_mismatch` is recorded for the economics interface; the uniqueness proof
uses the RCL, reciprocity, normalization, calibration, and continuity fields. -/
structure ComparisonCostAxioms (C : ℝ → ℝ) : Prop where
  reciprocal : IndisputableMonolith.Cost.FunctionalEquation.IsReciprocalCost C
  self_zero : IndisputableMonolith.Cost.FunctionalEquation.IsNormalized C
  compositional : IndisputableMonolith.Cost.FunctionalEquation.SatisfiesCompositionLaw C
  calibrated : IndisputableMonolith.Cost.FunctionalEquation.IsCalibrated C
  continuous : ContinuousOn C (Set.Ioi 0)
  monotone_mismatch : MonotoneOn (fun t : ℝ => C (Real.exp t)) (Set.Ici 0)

/-- **Recognition Utility Representation Theorem (cost form).**

Any calibrated economic comparison cost satisfying reciprocal symmetry, zero
self-comparison, the Recognition Composition Law, and continuity is the canonical
reciprocal cost on positive ratios. -/
theorem recognition_utility_representation (C : ℝ → ℝ)
    (h : ComparisonCostAxioms C) :
    ∀ x : ℝ, 0 < x → C x = Jcost x :=
  IndisputableMonolith.Cost.FunctionalEquation.law_of_logic_forces_jcost C
    h.reciprocal h.self_zero h.compositional h.calibrated h.continuous

/-- The canonical J-cost satisfies the representation conclusion trivially. -/
theorem recognition_utility_representation_jcost :
    ∀ x : ℝ, 0 < x → Jcost x = Jcost x := by
  intro x _hx
  rfl

/-- If a cost satisfies the economic comparison axioms, its induced exchange cost
agrees with Recognition Economics `exchangeCost` for positive price data. -/
theorem represented_exchangeCost (C : ℝ → ℝ)
    (h : ComparisonCostAxioms C) {p e : ℝ} (hp : 0 < p) (he : 0 < e) :
    C (p / e) = exchangeCost p e := by
  unfold exchangeCost
  exact recognition_utility_representation C h (p / e) (div_pos hp he)

end

end Recognition
end Economics
end IndisputableMonolith
