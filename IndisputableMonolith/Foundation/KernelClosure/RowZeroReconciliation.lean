import Mathlib
import IndisputableMonolith.Foundation.RecognitionKernel
import IndisputableMonolith.Foundation.KernelIndependenceCore
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCNativeCostUniqueness
import IndisputableMonolith.Cost.UnitForcedFromCarrier
import IndisputableMonolith.Foundation.PublicSpineNativeCostClosure
import IndisputableMonolith.Foundation.HierarchyRealizationObstruction
import IndisputableMonolith.Foundation.LinkingNecessity
import IndisputableMonolith.Foundation.RecognitionToLinkingSeam

/-!
# Kernel premise closure census: row zero (reconciliation)

The Recognition Kernel (`Foundation.RecognitionKernel`) names six free
hypotheses over unknown carriers, plus the realized hierarchy carried in its
parameters. Before any premise is attacked, this module reconciles the kernel's
own reading of its members with what the rest of the tree has already proved
about them, so the census that follows starts from the tree's actual frontier
rather than the kernel's docstrings.

## What this module establishes

1. **The cost sector is decoupled from the rest of the spine.**
   `kernel_forces_spine` consumes the unknown cost `F` in exactly one field,
   `cost_is_jcost`. The scale, dimension, tick, and measure conclusions consume
   only the non-cost members. This is proved by inhabiting the non-cost half of
   the spine from a `NonCostKernel` that never mentions `F`. Consequence: the
   two numerals in the cost sector (the product coefficient `2` and the
   calibration value `1`) reach only the cost's own identity and, downstream,
   any theorem that states an absolute cost value.

2. **The two cost numerals are the two coordinates of one unit choice.**
   Every reciprocal, normalized solution of the composition law with monotone
   log-profile is `costLambda k` for some exponent `k`
   (`PRCNativeCostUniqueness.composition_law_monotone_forces_costLambda`), and
   amplitude rescaling by `a > 0` moves the product coefficient to `2 / a`
   while the log-curvature becomes `a * k ^ 2`. So the pair
   (product coefficient, calibration) is the pair (amplitude, exponent), and
   pinning both numerals is exactly `a = 1 ∧ k = 1`. Row 1 of the census
   attacks the amplitude coordinate; row 2 attacks the exponent coordinate.

3. **What the tree already proves about each member**, re-exported under row
   labels so the ledger can cite one surface:
   * the exponent coordinate is forced by two qualitative postulates on the
     carrier plus the six exponentials theorem (`Cost.UnitForcedFromCarrier`);
   * the golden step is not available on the countable carrier
     (`PublicSpine.phi_scale_is_a_purchase`);
   * a closed observable framework does not force the hierarchy fields
     (`hierarchy_premise_is_load_bearing`);
   * the deformation-erasure principle is not forced by a spatial realization
     (`LinkingNecessity.unlinkedKinematics_refutes_dep` at `D = 4`).

## Consumer census (grep, 2026-09-01, `IndisputableMonolith/**/*.lean`)

The census that decides what a GAUGE verdict may cover.

* `RecognitionKernel` / `kernel_forces_spine`: 7 files, all in `Foundation`
  and `Skeleton`. No downstream physics consumes the kernel object directly.
* `IsCalibrated`: 65 files; 14 outside the cost sector (downstream
  application energies, gravity seven-gaps class lengths, alpha genesis resummation,
  `Constants.LambdaRecDerivation`). These consume the exponent coordinate.
* Absolute cost values `Jcost φ` and kin: 358 files. Every one of these is in
  cost units and changes under amplitude rescaling. Ratios of costs, argmin
  sets, and orderings do not.
* `latticeWeight` / `RecognitionWeightRule`: 29 files; outside `Foundation`
  the consumers are holography (Born depth, ladder measure bridges), alpha
  genesis seed seams, cosmology occupancy dilution, and economics discounting.
  These consume the forced measure, hence the ladder rows.
* `RealizedHierarchy`: 31 files; outside `Foundation` only downstream
  φ-ladder forcing. These consume the hierarchy premise.
* `detectsNontrivialLinking_three`: 9 files. Dimension consumers cite `D = 3`
  through the public spine rather than the kernel.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure

open Cost.FunctionalEquation
open ClosedFramework
open HierarchyRealization
open MeasureForcing
open PrimitiveRecognitionCalculus
open PrimitiveRecognitionCalculus.PRCJCost

noncomputable section

/-! ## 1. The cost sector is decoupled from the rest of the spine -/

/-- The kernel with the cost sector deleted: linking detection and the three
weight members, over the same unknown carriers. -/
structure NonCostKernel
    (D : ℕ) (w : ℕ → ℝ)
    (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr) : Prop where
  linking_detection : PublicSpine.DetectsNontrivialLinking D
  weight_pos : ∀ n : ℕ, 0 < w n
  weight_factorizes : ∀ m n : ℕ, w (m + n) = w m * w n
  step_self_similar : w 1 = 1 / (1 + w 1)

/-- Every kernel restricts to a non-cost kernel. -/
theorem NonCostKernel.of_kernel
    {F : ℝ → ℝ} {D : ℕ} {w : ℕ → ℝ}
    {Fr : ClosedObservableFramework} {H : RealizedHierarchy Fr}
    (K : RecognitionKernel F D w Fr H) : NonCostKernel D w Fr H where
  linking_detection := K.linking_detection
  weight_pos := K.weight_pos
  weight_factorizes := K.weight_factorizes
  step_self_similar := K.step_self_similar

/-- The non-cost half of the spine: everything `KernelSpine` concludes except
the cost's identity. -/
structure NonCostSpine
    (D : ℕ) (w : ℕ → ℝ)
    (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr) : Prop where
  t_minus2_distinction :
    NothingToDistinction.Nothing ≠ NothingToDistinction.Something
  scale_is_phi : (HierarchyRealization.realized_to_ladder Fr H).ratio = PhiForcing.φ
  dimension_is_three : D = 3
  eight_tick : DimensionForcing.EightTickFromDimension D = 8
  weight_is_forced : ∀ n : ℕ, w n = MeasureForcing.latticeWeight n

/-- **Decoupling.** The non-cost kernel forces the non-cost spine. The unknown
cost `F`, the composition law, and calibration appear nowhere in the statement
or the proof. -/
theorem nonCostKernel_forces_nonCostSpine
    {D : ℕ} {w : ℕ → ℝ}
    {Fr : ClosedObservableFramework} {H : RealizedHierarchy Fr}
    (K : NonCostKernel D w Fr H) : NonCostSpine D w Fr H where
  t_minus2_distinction := NothingToDistinction.nothing_ne_something
  scale_is_phi := HierarchyRealization.realized_hierarchy_forces_phi Fr H
  dimension_is_three := PublicSpineLinkingClosure.forces_D3 D K.linking_detection
  eight_tick := by
    rw [PublicSpineLinkingClosure.forces_D3 D K.linking_detection]
    rfl
  weight_is_forced := fun n =>
    MeasureForcing.RecognitionWeightRule.weight_forced
      { w := w
      , w_pos := K.weight_pos
      , factorizes := K.weight_factorizes
      , step_self_similar := K.step_self_similar } n

/-- **Decoy for the decoupling.** The non-cost kernel does not reach the cost
conclusion: the zero cost sits under a non-cost kernel and is not `Jcost`. So
the decoupling is a genuine split, not a restatement of `kernel_forces_spine`. -/
theorem nonCostKernel_does_not_force_cost
    (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr) :
    NonCostKernel 3 MeasureForcing.latticeWeight Fr H ∧
      ¬ (∀ x : ℝ, 0 < x → (fun _ : ℝ => (0 : ℝ)) x = Cost.Jcost x) := by
  refine ⟨NonCostKernel.of_kernel (recognitionKernel_canonical Fr H), ?_⟩
  intro h
  have h2 := h 2 (by norm_num)
  simp only [Cost.Jcost] at h2
  norm_num at h2

/-! ## 2. The two cost numerals are the two coordinates of one unit choice

`costLambda k x = (x ^ k + x ^ (-k)) / 2 - 1` is the exponent-`k` member of the
gauge orbit; `a * costLambda k` is the amplitude-`a` rescaling of it. -/

/-- Amplitude rescaling of a cost. -/
def amplitudeRescale (a : ℝ) (F : ℝ → ℝ) : ℝ → ℝ := fun x => a * F x

/-- The log-profile of a rescaled cost is the rescaled log-profile. -/
theorem G_amplitudeRescale (a : ℝ) (F : ℝ → ℝ) :
    G (amplitudeRescale a F) = fun t => a * G F t := by
  funext t
  simp [G, amplitudeRescale]

/-- The log-curvature at the unit scales with the amplitude. -/
theorem logCurvature_amplitudeRescale (a : ℝ) (F : ℝ → ℝ) :
    deriv (deriv (G (amplitudeRescale a F))) 0 = a * deriv (deriv (G F)) 0 := by
  rw [G_amplitudeRescale]
  have h1 : deriv (fun t : ℝ => a * G F t) = fun t : ℝ => a * deriv (G F) t := by
    funext t
    exact deriv_const_mul_field a
  rw [h1]
  exact deriv_const_mul_field a

/-- **Amplitude coordinate.** Rescaling a composition-law solution by `a ≠ 0`
moves the product coefficient to `2 / a`. -/
theorem compositionGen_amplitudeRescale (a : ℝ) (ha : a ≠ 0) (F : ℝ → ℝ)
    (hF : SatisfiesCompositionLaw F) :
    KernelIndependence.SatisfiesCompositionLawGen (2 / a) (amplitudeRescale a F) := by
  have hs : (1 / a) ≠ 0 := one_div_ne_zero ha
  have hscaled : SatisfiesCompositionLaw (fun x => (1 / a) * amplitudeRescale a F x) := by
    have : (fun x => (1 / a) * amplitudeRescale a F x) = F := by
      funext x
      simp only [amplitudeRescale]
      rw [← mul_assoc, one_div, inv_mul_cancel₀ ha, one_mul]
    rw [this]
    exact hF
  have h := KernelIndependence.compositionGen_of_scaled (1 / a) (amplitudeRescale a F) hs hscaled
  have e : (2 : ℝ) * (1 / a) = 2 / a := by ring
  rw [e] at h
  exact h

/-- **Exponent coordinate.** The log-curvature of `a * costLambda k` at the
unit is `a * k ^ 2`. -/
theorem logCurvature_amplitude_costLambda (a k : ℝ) :
    deriv (deriv (G (amplitudeRescale a (costLambda k)))) 0 = a * k ^ 2 := by
  rw [logCurvature_amplitudeRescale, calibration_value_costLambda]

/-- **The two numerals pin the two coordinates.** For `a, k > 0`, the member
`a * costLambda k` has product coefficient `2` and calibration `1` exactly when
`a = 1` and `k = 1`. The kernel's two numeric premises are therefore one
two-parameter unit choice, and the census splits it: row 1 is the amplitude
`a` (target GAUGE), row 2 is the exponent `k` (target DERIVED from the
carrier). -/
theorem two_numerals_pin_two_coordinates {a k : ℝ} (ha : 0 < a) (hk : 0 < k) :
    (KernelIndependence.SatisfiesCompositionLawGen 2 (amplitudeRescale a (costLambda k)) ∧
        IsCalibrated (amplitudeRescale a (costLambda k)))
      ↔ (a = 1 ∧ k = 1) := by
  have hRCL : SatisfiesCompositionLaw (costLambda k) :=
    (composition_law_admits_full_scale_family k hk).2.2.1
  constructor
  · rintro ⟨hGen, hCal⟩
    have hcal' : a * k ^ 2 = 1 := by
      have := logCurvature_amplitude_costLambda a k
      unfold IsCalibrated at hCal
      linarith
    have hGen' : KernelIndependence.SatisfiesCompositionLawGen (2 / a)
        (amplitudeRescale a (costLambda k)) :=
      compositionGen_amplitudeRescale a (ne_of_gt ha) (costLambda k) hRCL
    -- Both `Gen 2` and `Gen (2 / a)` hold of the same nonzero function: the
    -- product coefficients agree at a point where `F x * F y ≠ 0`.
    have h2 := hGen 2 2 (by norm_num) (by norm_num)
    have h2' := hGen' 2 2 (by norm_num) (by norm_num)
    have hne : amplitudeRescale a (costLambda k) 2 ≠ 0 := by
      simp only [amplitudeRescale]
      refine mul_ne_zero (ne_of_gt ha) ?_
      have hpos : 0 < costLambda k 2 := by
        have h2k : (1 : ℝ) < (2 : ℝ) ^ k :=
          Real.one_lt_rpow (by norm_num) hk
        have hinv : (2 : ℝ) ^ (-k) = ((2 : ℝ) ^ k)⁻¹ := Real.rpow_neg (by norm_num) k
        unfold costLambda
        rw [hinv]
        have hu : 0 < (2 : ℝ) ^ k := by linarith
        have key : 2 < (2 : ℝ) ^ k + ((2 : ℝ) ^ k)⁻¹ := by
          -- u + 1/u - 2 = (u - 1)^2 / u > 0 for u > 1.
          set u : ℝ := (2 : ℝ) ^ k with hu_def
          have hne : u ≠ 0 := ne_of_gt hu
          have hid : u + u⁻¹ - 2 = (u - 1) ^ 2 / u := by
            field_simp
            ring
          have hpos' : 0 < (u - 1) ^ 2 / u := by
            have : (u - 1) ≠ 0 := by linarith
            positivity
          linarith
        linarith
      exact ne_of_gt hpos
    have hsq : amplitudeRescale a (costLambda k) 2 * amplitudeRescale a (costLambda k) 2 ≠ 0 :=
      mul_ne_zero hne hne
    have hcoef : (2 : ℝ) = 2 / a := by
      have e : (2 - 2 / a) * (amplitudeRescale a (costLambda k) 2 *
          amplitudeRescale a (costLambda k) 2) = 0 := by
        linear_combination h2' - h2
      rcases mul_eq_zero.mp e with h | h
      · linarith
      · exact absurd h hsq
    have ha1 : a = 1 := by
      field_simp at hcoef
      linarith
    refine ⟨ha1, ?_⟩
    subst ha1
    have : k ^ 2 = 1 := by linarith
    nlinarith [sq_nonneg (k - 1), sq_nonneg (k + 1), hk]
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · have h := compositionGen_amplitudeRescale 1 one_ne_zero (costLambda 1) hRCL
      simpa using h
    · unfold IsCalibrated
      rw [logCurvature_amplitude_costLambda]
      norm_num

/-! ## 3. Re-exports under row labels -/

/-- **Row 2 frontier (re-export).** The exponent coordinate is forced by two
qualitative postulates on the carrier, carrier-valuedness and an automorphism
character, given the six exponentials input. Neither postulate names a number. -/
theorem row2_exponent_forced_from_carrier
    (hsix : Cost.TraceRationalExponent.SixExponentialsTraceInput) {c : ℝ} (hc : 0 < c)
    (hcar : Cost.UnitForcedFromCarrier.CarrierValued c)
    (haut : Cost.UnitForcedFromCarrier.CharacterIsAutomorphism c) : c = 1 :=
  Cost.UnitForcedFromCarrier.unit_forced_by_automorphism hsix hc hcar haut

/-- **Row 2 frontier (re-export).** Both postulates are load-bearing: the
exponent-two gauge is carrier-valued, and the half gauge is least among the
integer gauges, and neither is the unit. -/
theorem row2_both_postulates_load_bearing :
    Cost.UnitForcedFromCarrier.CarrierValued ((2 : ℕ) : ℝ) ∧
      Cost.UnitForcedFromCarrier.LeastAmongIntegerGauges (1 / 2) ∧
      ¬ Cost.UnitForcedFromCarrier.CarrierValued (1 / 2) :=
  ⟨Cost.UnitForcedFromCarrier.carrierValued_two,
    Cost.UnitForcedFromCarrier.leastAmongIntegerGauges_half,
    Cost.UnitForcedFromCarrier.half_not_carrierValued⟩

/-- **Ladder frontier (re-export).** The golden step is not on the countable
carrier: the ladder census cannot land at `deltaOnly` and targets
`traceClosure`. -/
theorem ladder_phi_is_a_purchase :
    PublicSpine.Tagged StrengthTag.deltaOnly
      (¬ ∃ q : RatioOrbit, 0 < q.toRat ∧ 1 + (q.toRat)⁻¹ = q.toRat) :=
  PublicSpine.phi_scale_is_a_purchase

/-- **Ladder frontier (re-export).** A closed observable framework alone does
not carry the hierarchy fields; the Boolean framework is the countermodel. -/
theorem ladder_hierarchy_premise_load_bearing :
    ∃ (F0 : ClosedObservableFramework) (base : F0.S),
      (¬ (∀ k,
        F0.r (F0.T^[k + 2] base) / F0.r (F0.T^[k + 1] base) =
          F0.r (F0.T^[k + 1] base) / F0.r (F0.T^[k] base))) ∧
      (¬ (F0.r (F0.T^[2] base) = F0.r (F0.T^[1] base) + F0.r base)) :=
  hierarchy_premise_is_load_bearing

/-- **Row 3 frontier (re-export).** Detection at the unknown dimension forces
`D = 3` unconditionally, and the deformation-erasure principle is refuted by a
spatial realization at `D = 4`, so DEP is a genuine input rather than a
consequence of realization. -/
theorem row3_frontier :
    (∀ D : ℕ, PublicSpine.DetectsNontrivialLinking D → D = 3) ∧
      ∃ (D : DimensionForcing.Dimension) (R : LinkingNecessity.SpatialDualPairRealization D),
        ¬ LinkingNecessity.DeformationErasurePrinciple R.kin :=
  ⟨PublicSpineLinkingClosure.forces_D3, ⟨4, LinkingNecessity.fourDimRealization,
    LinkingNecessity.unlinkedKinematics_refutes_dep⟩⟩

/-! ## Audits -/

#print axioms nonCostKernel_forces_nonCostSpine
#print axioms nonCostKernel_does_not_force_cost
#print axioms compositionGen_amplitudeRescale
#print axioms logCurvature_amplitude_costLambda
#print axioms two_numerals_pin_two_coordinates
#print axioms row2_exponent_forced_from_carrier
#print axioms ladder_phi_is_a_purchase
#print axioms row3_frontier

end

end KernelClosure
end Foundation
end IndisputableMonolith
