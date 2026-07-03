/-
  PrimitiveRecognitionCalculus/PRCJCost.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html
    δ/Logic_Functional_Equation.tex

  Spec anchors:
    Build Order steps 5-7: ratio cost surface, RCL surface, and the strongest
    currently provable bridge to the existing J-cost uniqueness theorem.

  Strength: δ-only for the rational cost object. The bridge to `Cost.Jcost`
  and `law_of_logic_forces_jcost` is a classical-extension transport surface
  because it lives on continuous positive real ratios.
-/

import Mathlib
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.OrbitEuclidean

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

namespace PRCJCost

/-! ## A rational PRC cost object -/

/-- The two-step orbit position. -/
def twoOrbit : DistinctionNat :=
  DistinctionNat.succ DistinctionNat.one

@[simp] theorem twoOrbit_toNat :
    twoOrbit.toNat = 2 := by
  rfl

/-- The ratio orbit `2`. -/
def two : RatioOrbit where
  num := SignedOrbit.ofOrbit twoOrbit
  den := DistinctionNat.one
  den_ne_zero := DistinctionNat.one_ne_zero

@[simp] theorem two_toRat :
    two.toRat = 2 := by
  unfold two RatioOrbit.toRat
  simp [twoOrbit_toNat, SignedOrbit.ofOrbit_toInt, DistinctionNat.one_toNat]

/-- The ratio orbit `1/2`. -/
def half : RatioOrbit where
  num := SignedOrbit.ofOrbit DistinctionNat.one
  den := twoOrbit
  den_ne_zero := by
    intro h
    have hnat := congrArg DistinctionNat.toNat h
    rw [twoOrbit_toNat, DistinctionNat.toNat_zero] at hnat
    norm_num at hnat

@[simp] theorem half_toRat :
    half.toRat = (1 / 2 : ℚ) := by
  unfold half RatioOrbit.toRat
  simp [twoOrbit_toNat, SignedOrbit.ofOrbit_toInt, DistinctionNat.one_toNat]

/-- PRC's rational J-cost object on a ratio orbit:
`J(q) = ((q + q⁻¹) / 2) - 1`.

This is a ratio-orbit object. It is not the real analytic uniqueness theorem;
that theorem is bridged below. -/
def onRatioOrbit (q : RatioOrbit) : RatioOrbit :=
  RatioOrbit.sub (RatioOrbit.mul (RatioOrbit.add q (RatioOrbit.recip q)) half) RatioOrbit.one

theorem onRatioOrbit_toRat (q : RatioOrbit) :
    (onRatioOrbit q).toRat = (q.toRat + q.toRat⁻¹) / 2 - 1 := by
  unfold onRatioOrbit
  rw [RatioOrbit.sub_toRat, RatioOrbit.mul_toRat, RatioOrbit.add_toRat,
    RatioOrbit.recip_toRat, half_toRat, RatioOrbit.one_toRat]
  ring

/-- The PRC rational cost transports to the existing real `Cost.Jcost`
formula on the verifier display. -/
theorem onRatioOrbit_toReal_jcost (q : RatioOrbit) :
    ((onRatioOrbit q).toRat : ℝ) = Cost.Jcost ((q.toRat : ℚ) : ℝ) := by
  rw [onRatioOrbit_toRat]
  unfold Cost.Jcost
  rw [Rat.cast_sub, Rat.cast_div, Rat.cast_add, Rat.cast_inv]
  norm_num

/-- Reciprocal symmetry of the PRC rational cost. -/
theorem reciprocal_symmetric (q : RatioOrbit) :
    RatioOrbit.crossEq (onRatioOrbit q) (onRatioOrbit (RatioOrbit.recip q)) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq]
  rw [onRatioOrbit_toRat, onRatioOrbit_toRat, RatioOrbit.recip_toRat]
  by_cases hq : q.toRat = 0
  · simp [hq]
  · field_simp [hq]
    ring

/-- Normalizing a ratio representative by native orbit GCD preserves the PRC
cost. -/
theorem normalized_invariant (q : RatioOrbit) :
    RatioOrbit.crossEq (onRatioOrbit q)
      (onRatioOrbit (DistinctionNat.normalizeRatio q)) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq]
  rw [onRatioOrbit_toRat, onRatioOrbit_toRat, DistinctionNat.normalizeRatio_toRat]

/-- Division of ratio orbits, defined from multiplication and reciprocal. -/
def div (q r : RatioOrbit) : RatioOrbit :=
  RatioOrbit.mul q (RatioOrbit.recip r)

theorem div_toRat (q r : RatioOrbit) :
    (div q r).toRat = q.toRat / r.toRat := by
  unfold div
  rw [RatioOrbit.mul_toRat, RatioOrbit.recip_toRat]
  rfl

private def rclLHS (x y : RatioOrbit) : RatioOrbit :=
  RatioOrbit.add (onRatioOrbit (RatioOrbit.mul x y)) (onRatioOrbit (div x y))

private def rclRHS (x y : RatioOrbit) : RatioOrbit :=
  RatioOrbit.add
    (RatioOrbit.add
      (RatioOrbit.mul two (RatioOrbit.mul (onRatioOrbit x) (onRatioOrbit y)))
      (RatioOrbit.mul two (onRatioOrbit x)))
    (RatioOrbit.mul two (onRatioOrbit y))

/-- Canonical PRC J-cost satisfies the RCL algebraically on nonzero ratio
orbits. This is the rational surface of the composition law, not the
continuous-real uniqueness theorem. -/
theorem canonical_rcl_surface {x y : RatioOrbit}
    (hx : x.toRat ≠ 0) (hy : y.toRat ≠ 0) :
    RatioOrbit.crossEq (rclLHS x y) (rclRHS x y) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq]
  unfold rclLHS rclRHS
  rw [RatioOrbit.add_toRat, RatioOrbit.add_toRat, RatioOrbit.add_toRat,
    RatioOrbit.mul_toRat, RatioOrbit.mul_toRat, RatioOrbit.mul_toRat,
    RatioOrbit.mul_toRat,
    onRatioOrbit_toRat, onRatioOrbit_toRat, onRatioOrbit_toRat,
    onRatioOrbit_toRat, div_toRat]
  simp [two_toRat]
  rw [RatioOrbit.mul_toRat]
  have hxy : x.toRat * y.toRat ≠ 0 := mul_ne_zero hx hy
  field_simp [hx, hy, hxy]
  ring_nf

/-! ## Bridge to the existing continuous positive-real uniqueness theorem -/

/-- Hypotheses for the later PRC-native cost-classification theorem. The
`two_calibrated` field rules out the identically-zero cost on the discrete
rational surface, playing the role of the continuous theorem's unit
log-curvature calibration until the internal real completion exists. -/
structure PRCNativeCostHypotheses (F : RatioOrbit → RatioOrbit) : Prop where
  reciprocal :
    ∀ q, RatioOrbit.crossEq (F q) (F (RatioOrbit.recip q))
  normalized_invariant :
    ∀ q, RatioOrbit.crossEq (F q) (F (DistinctionNat.normalizeRatio q))
  canonical_rcl :
    ∀ {x y : RatioOrbit}, x.toRat ≠ 0 → y.toRat ≠ 0 →
      RatioOrbit.crossEq
        (RatioOrbit.add (F (RatioOrbit.mul x y)) (F (div x y)))
        (RatioOrbit.add
          (RatioOrbit.add
            (RatioOrbit.mul two (RatioOrbit.mul (F x) (F y)))
            (RatioOrbit.mul two (F x)))
          (RatioOrbit.mul two (F y)))
  unit_zero :
    F RatioOrbit.one = RatioOrbit.zero
  two_calibrated :
    RatioOrbit.crossEq (F two) (onRatioOrbit two)

/-- Exact missing native theorem for a later pass: classify every admissible
PRC cost on normalized ratio orbits, then transport to the continuous
positive-real theorem as a corollary rather than using the real theorem as
the premise. -/
def PRCNativeCostUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCNativeCostHypotheses F →
    ∀ q : RatioOrbit, RatioOrbit.crossEq (F q) (onRatioOrbit q)

/-- The real-domain uniqueness theorem currently used by PRC. The quantified
`AczelSmoothnessPackage` keeps the Aczél regularity commitment explicit. -/
theorem bridge_to_existing_jcost_uniqueness
    (F : ℝ → ℝ)
    (hAczel : Cost.FunctionalEquation.AczelSmoothnessPackage)
    (hRecip : Cost.FunctionalEquation.IsReciprocalCost F)
    (hNorm : Cost.FunctionalEquation.IsNormalized F)
    (hComp : Cost.FunctionalEquation.SatisfiesCompositionLaw F)
    (hCalib : Cost.FunctionalEquation.IsCalibrated F)
    (hCont : ContinuousOn F (Set.Ioi 0)) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  let _ : Cost.FunctionalEquation.AczelSmoothnessPackage := hAczel
  exact Cost.FunctionalEquation.law_of_logic_forces_jcost
    F hRecip hNorm hComp hCalib hCont

/-- Certificate for the PRC cost pass. -/
structure PRCJCostCertificate : Prop where
  rational_formula :
    ∀ q : RatioOrbit,
      (onRatioOrbit q).toRat = (q.toRat + q.toRat⁻¹) / 2 - 1
  real_jcost_bridge :
    ∀ q : RatioOrbit,
      ((onRatioOrbit q).toRat : ℝ) = Cost.Jcost ((q.toRat : ℚ) : ℝ)
  reciprocal :
    ∀ q : RatioOrbit,
      RatioOrbit.crossEq (onRatioOrbit q) (onRatioOrbit (RatioOrbit.recip q))
  normalization :
    ∀ q : RatioOrbit,
      RatioOrbit.crossEq (onRatioOrbit q)
        (onRatioOrbit (DistinctionNat.normalizeRatio q))
  canonical_rcl :
    ∀ {x y : RatioOrbit}, x.toRat ≠ 0 → y.toRat ≠ 0 →
      RatioOrbit.crossEq (rclLHS x y) (rclRHS x y)
  existing_real_uniqueness :
    ∀ (F : ℝ → ℝ),
      Cost.FunctionalEquation.AczelSmoothnessPackage →
      Cost.FunctionalEquation.IsReciprocalCost F →
      Cost.FunctionalEquation.IsNormalized F →
      Cost.FunctionalEquation.SatisfiesCompositionLaw F →
      Cost.FunctionalEquation.IsCalibrated F →
      ContinuousOn F (Set.Ioi 0) →
      ∀ x : ℝ, 0 < x → F x = Cost.Jcost x
  native_uniqueness_target_named :
    PRCNativeCostUniquenessTarget = PRCNativeCostUniquenessTarget

/-- The PRC rational cost surface is closed through canonical RCL and bridges
honestly to the existing continuous-real uniqueness theorem. -/
theorem prc_jcost_certificate : PRCJCostCertificate where
  rational_formula := onRatioOrbit_toRat
  real_jcost_bridge := onRatioOrbit_toReal_jcost
  reciprocal := reciprocal_symmetric
  normalization := normalized_invariant
  canonical_rcl := by
    intro x y hx hy
    exact canonical_rcl_surface hx hy
  existing_real_uniqueness := by
    intro F hA hR hN hC hCal hCont x hx
    exact bridge_to_existing_jcost_uniqueness F hA hR hN hC hCal hCont x hx
  native_uniqueness_target_named := rfl

end PRCJCost

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
