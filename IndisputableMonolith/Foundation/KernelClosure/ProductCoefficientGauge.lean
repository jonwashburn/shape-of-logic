import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.RowZeroReconciliation
import IndisputableMonolith.Foundation.DAlembert.FactorizationForcing

/-!
# Kernel premise closure census, row 1: the product coefficient is a gauge

**Premise.** The composition law
`F (x * y) + F (x / y) = 2 * F x * F y + 2 * F x + 2 * F y` carries two
numerals. The linear coefficient `2` is forced
(`KernelIndependence.linear_coefficient_forced`). The product coefficient `2`
is not (`KernelIndependence.product_coefficient_is_a_choice`): the cost
`quarterCoshTwoCost` is normalized, calibrated, continuous, satisfies the law
with product coefficient `8`, and is not `Jcost`.

**Verdict: GAUGE.** The product coefficient is the amplitude coordinate of the
cost unit. Concretely:

* **Orbit.** For every `c ≠ 0`, `F` satisfies the law with product coefficient
  `c` exactly when `(c / 2) * F` satisfies it with product coefficient `2`.
  The solution set at coefficient `c` is the amplitude rescaling of the
  solution set at coefficient `2`, and nothing else.
* **Invariance.** Amplitude rescaling by `a > 0` preserves every ratio of
  costs, the order of costs, the zero set, normalization, and reciprocity; and
  the non-cost half of the spine (scale, dimension, tick, measure) never reads
  the cost at all (`RowZeroReconciliation.nonCostKernel_forces_nonCostSpine`).
* **Consumer audit.** Two things are not invariant and inherit the unit: the
  absolute value of a cost (358 files in the tree state one, all in cost units)
  and the calibration value, which scales by `a`. That second fact is why the
  census treats calibration separately in row 2: once the amplitude is fixed
  by convention, calibration is the exponent coordinate, and that one is not
  a gauge (`exponent_change_is_not_amplitude_gauge` below).

**Decoys.** Three, each a shape the same argument must reject.

1. The linear coefficient is not a gauge: a wrong `d` kills every normalized
   calibrated solution rather than rescaling it.
2. The exponent gauge `x ↦ F (x ^ k)` is not an amplitude rescaling: it
   changes cost ratios, exhibited at the ratios `2` and `4`.
3. The `P(1,1) = 6` diagonal of the d'Alembert factorization gate is the same
   amplitude convention: without it the gate forces only the bilinear family
   with a free product coefficient (`gate_forces_bilinear_family`), and any
   coefficient is admissible.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace ProductCoefficientGauge

open Cost.FunctionalEquation
open KernelIndependence

noncomputable section

/-! ## The orbit -/

/-- **Orbit theorem.** The solutions of the composition law with product
coefficient `c ≠ 0` are exactly the amplitude rescalings by `2 / c` of the
solutions with product coefficient `2`. -/
theorem compositionGen_iff_rescaled (c : ℝ) (hc : c ≠ 0) (F : ℝ → ℝ) :
    SatisfiesCompositionLawGen c F ↔
      SatisfiesCompositionLaw (amplitudeRescale (c / 2) F) := by
  constructor
  · intro h
    exact compositionGen_scaled c F h
  · intro h
    have hs : c / 2 ≠ 0 := div_ne_zero hc two_ne_zero
    have h' := compositionGen_of_scaled (c / 2) F hs h
    have e : (2 : ℝ) * (c / 2) = c := by ring
    rw [e] at h'
    exact h'

/-- The orbit theorem in the direction the kernel uses: a coefficient-`c`
solution, rescaled by `c / 2`, is a coefficient-`2` solution, and the map back
is rescaling by `2 / c`. -/
theorem rescale_roundtrip (c : ℝ) (hc : c ≠ 0) (F : ℝ → ℝ) :
    amplitudeRescale (2 / c) (amplitudeRescale (c / 2) F) = F := by
  funext x
  simp only [amplitudeRescale]
  field_simp

/-! ## Invariants of amplitude rescaling -/

/-- Cost ratios are invariant. -/
theorem ratio_invariant (a : ℝ) (ha : a ≠ 0) (F : ℝ → ℝ) (x y : ℝ) :
    amplitudeRescale a F x / amplitudeRescale a F y = F x / F y := by
  simp only [amplitudeRescale]
  exact mul_div_mul_left (F x) (F y) ha

/-- The order of costs is invariant. -/
theorem order_invariant (a : ℝ) (ha : 0 < a) (F : ℝ → ℝ) (x y : ℝ) :
    amplitudeRescale a F x ≤ amplitudeRescale a F y ↔ F x ≤ F y := by
  simp only [amplitudeRescale]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- The zero set is invariant. -/
theorem zero_set_invariant (a : ℝ) (ha : a ≠ 0) (F : ℝ → ℝ) (x : ℝ) :
    amplitudeRescale a F x = 0 ↔ F x = 0 := by
  simp [amplitudeRescale, ha]

/-- Normalization is invariant. -/
theorem normalized_invariant (a : ℝ) (ha : a ≠ 0) (F : ℝ → ℝ) :
    IsNormalized (amplitudeRescale a F) ↔ IsNormalized F := by
  simp [IsNormalized, amplitudeRescale, ha]

/-- Reciprocity is invariant. -/
theorem reciprocal_invariant (a : ℝ) (ha : a ≠ 0) (F : ℝ → ℝ) :
    IsReciprocalCost (amplitudeRescale a F) ↔ IsReciprocalCost F := by
  constructor
  · intro h x hx
    have := h x hx
    simp only [amplitudeRescale] at this
    exact mul_left_cancel₀ ha this
  · intro h x hx
    simp only [amplitudeRescale]
    rw [h x hx]

/-! ## What is not invariant: the consumer audit -/

/-- **Absolute cost values are in cost units.** Away from the zero set, a
nontrivial rescaling changes every absolute value. -/
theorem absolute_value_not_invariant (a : ℝ) (ha : a ≠ 1) (F : ℝ → ℝ) (x : ℝ)
    (hx : F x ≠ 0) : amplitudeRescale a F x ≠ F x := by
  simp only [amplitudeRescale]
  intro h
  have : (a - 1) * F x = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact ha (by linarith)
  · exact hx h1

/-- **Calibration is in cost units.** The log-curvature at the unit scales
with the amplitude, so a calibration value is a cost-unit datum. This is the
handoff to row 2. -/
theorem calibration_transforms (a : ℝ) (F : ℝ → ℝ) :
    deriv (deriv (G (amplitudeRescale a F))) 0 = a * deriv (deriv (G F)) 0 :=
  logCurvature_amplitudeRescale a F

/-! ## Decoys -/

/-- **Decoy 1: the linear coefficient is not a gauge.** A wrong linear
coefficient admits no normalized calibrated solution at all; there is no orbit
to rescale. Re-exported from `KernelIndependence.linear_coefficient_forced`. -/
theorem linear_coefficient_is_not_gauge (c d : ℝ) (F : ℝ → ℝ)
    (hFam : SatisfiesCompositionLawFamily c d F)
    (hNorm : IsNormalized F) (hCalib : IsCalibrated F) : d = 2 :=
  linear_coefficient_forced c d F hFam hNorm hCalib

/-- **Decoy 2: the exponent gauge is not an amplitude gauge.** The exponent-two
member `coshTwoCost x = Jcost (x ^ 2)` is a bona fide composition-law solution
but changes cost ratios: at the ratios `2` and `4` it gives `4 / 25` where
`Jcost` gives `2 / 9`. So an argument that made the exponent content-free would
prove too much; the exponent is the substantive coordinate, attacked in row 2. -/
theorem exponent_change_is_not_amplitude_gauge :
    SatisfiesCompositionLaw coshTwoCost ∧
      coshTwoCost 2 / coshTwoCost 4 ≠ Cost.Jcost 2 / Cost.Jcost 4 := by
  refine ⟨coshTwoCost_composition, ?_⟩
  simp only [coshTwoCost, Cost.Jcost]
  norm_num

/-- **Decoy 3: the d'Alembert unit diagonal is the same convention.** Without
`P 1 1 = 6`, the factorization gate forces only the bilinear family with a free
product coefficient, and every coefficient is realized by some symmetric,
right-affine combiner with the correct zero boundary. With it, the coefficient
is `2`. One unit choice, stated once. -/
theorem unit_diagonal_is_the_amplitude_convention :
    (∀ c : ℝ, ∃ P : ℝ → ℝ → ℝ,
      (∀ u v, P u v = P v u) ∧
      (∀ u, ∃ α β, ∀ v, P u v = α * v + β) ∧
      (∀ u, P u 0 = 2 * u) ∧
      (∀ u v, P u v = c * u * v + 2 * u + 2 * v)) ∧
    (∀ P : ℝ → ℝ → ℝ, DAlembert.FactorizationForcing.FactorizationAssociativityGate P →
      ∀ u v, P u v = 2 * u * v + 2 * u + 2 * v) := by
  refine ⟨?_, DAlembert.FactorizationForcing.gate_forces_rcl⟩
  intro c
  refine ⟨fun u v => c * u * v + 2 * u + 2 * v, ?_, ?_, ?_, fun _ _ => rfl⟩
  · intro u v; ring
  · intro u
    exact ⟨c * u + 2, 2 * u, fun v => by ring⟩
  · intro u; ring

/-! ## The verdict -/

/-- **Row 1 certificate: the product coefficient is a gauge.** -/
structure ProductCoefficientGaugeCert : Prop where
  orbit : ∀ (c : ℝ), c ≠ 0 → ∀ F : ℝ → ℝ,
    SatisfiesCompositionLawGen c F ↔ SatisfiesCompositionLaw (amplitudeRescale (c / 2) F)
  ratios_invariant : ∀ (a : ℝ), a ≠ 0 → ∀ (F : ℝ → ℝ) (x y : ℝ),
    amplitudeRescale a F x / amplitudeRescale a F y = F x / F y
  order_invariant : ∀ (a : ℝ), 0 < a → ∀ (F : ℝ → ℝ) (x y : ℝ),
    (amplitudeRescale a F x ≤ amplitudeRescale a F y ↔ F x ≤ F y)
  zero_set_invariant : ∀ (a : ℝ), a ≠ 0 → ∀ (F : ℝ → ℝ) (x : ℝ),
    (amplitudeRescale a F x = 0 ↔ F x = 0)
  noncost_spine_untouched : ∀ (D : ℕ) (w : ℕ → ℝ)
    (Fr : ClosedFramework.ClosedObservableFramework) (H : HierarchyRealization.RealizedHierarchy Fr),
    NonCostKernel D w Fr H → NonCostSpine D w Fr H
  absolute_values_in_cost_units : ∀ (a : ℝ), a ≠ 1 → ∀ (F : ℝ → ℝ) (x : ℝ),
    F x ≠ 0 → amplitudeRescale a F x ≠ F x
  calibration_in_cost_units : ∀ (a : ℝ) (F : ℝ → ℝ),
    deriv (deriv (G (amplitudeRescale a F))) 0 = a * deriv (deriv (G F)) 0
  decoy_linear_coefficient : ∀ (c d : ℝ) (F : ℝ → ℝ),
    SatisfiesCompositionLawFamily c d F → IsNormalized F → IsCalibrated F → d = 2
  decoy_exponent : SatisfiesCompositionLaw coshTwoCost ∧
    coshTwoCost 2 / coshTwoCost 4 ≠ Cost.Jcost 2 / Cost.Jcost 4
  decoy_unit_diagonal : ∀ P : ℝ → ℝ → ℝ,
    DAlembert.FactorizationForcing.FactorizationAssociativityGate P →
      ∀ u v, P u v = 2 * u * v + 2 * u + 2 * v

theorem productCoefficientGaugeCert_holds : ProductCoefficientGaugeCert where
  orbit := compositionGen_iff_rescaled
  ratios_invariant := ratio_invariant
  order_invariant := order_invariant
  zero_set_invariant := zero_set_invariant
  noncost_spine_untouched := fun _ _ _ _ K => nonCostKernel_forces_nonCostSpine K
  absolute_values_in_cost_units := absolute_value_not_invariant
  calibration_in_cost_units := calibration_transforms
  decoy_linear_coefficient := linear_coefficient_is_not_gauge
  decoy_exponent := exponent_change_is_not_amplitude_gauge
  decoy_unit_diagonal := DAlembert.FactorizationForcing.gate_forces_rcl

/-! ## Audits -/

#print axioms compositionGen_iff_rescaled
#print axioms ratio_invariant
#print axioms order_invariant
#print axioms exponent_change_is_not_amplitude_gauge
#print axioms unit_diagonal_is_the_amplitude_convention
#print axioms productCoefficientGaugeCert_holds

end

end ProductCoefficientGauge
end KernelClosure
end Foundation
end IndisputableMonolith
