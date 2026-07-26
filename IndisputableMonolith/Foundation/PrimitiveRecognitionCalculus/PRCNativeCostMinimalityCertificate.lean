/-
  PrimitiveRecognitionCalculus/PRCNativeCostMinimalityCertificate.lean

  Round-trip source:
    δ/plans/JCost_SlimLedger_Minimality_Certificate_Prereg_20260724.json (frozen)
    plans/Delta_JCost_Slim_Ledger_Minimality_Certificate_Session_Prompt_20260724.txt

  Field-by-field minimality certificate for the slim native-cost ledger
  (P-delta-jfree, round 3). Round 2 (`PRCNativeCostMinimality.lean`) proved
  that the slim ledger (base: reciprocity, normalization invariance, nonzero
  RCL, unit-zero, two-calibration; plus prime-pair products, signed unit, and
  zero orbit) forces the canonical J-cost on `RatioOrbit`, and that the
  all-prime axis family is redundant. This module settles what remained: every
  removable calibration field of the slim ledger is NECESSARY. For each such
  field we define the class "slim minus this field" (connected to the slim
  ledger by a bridging iff) and refute its uniqueness target with an explicit
  countermodel:

  * TWO-POINT ANCHOR (`two_calibrated`), the new construction of this round:
    the Liouville sign twist. `liouvilleSign t = (-1)^(Ω num + Ω den)` is the
    parity of the total prime-exponent sum of the reduced fraction (Mathlib
    totalizes `Ω 0 = 0`, so the sign is `+1` at `0`, where it is harmless);
    the twisted cost displays `J(liouvilleSign t · t)`. The sign is completely
    multiplicative on nonzero rationals (the reduced-fraction cross identity
    keeps the parity), equal to `-1` on every prime, hence `+1` on every
    product of two primes and at the signed unit. The twisted cost therefore
    passes reciprocity, normalization invariance, the nonzero RCL, unit-zero,
    prime-pair products, the signed unit, and the zero orbit, and fails
    exactly the two-point anchor: it displays `J(-2) = -9/4` at orbit 2
    against the canonical `J(2) = 1/4`.

  * PAIR FIELD (`prime_pair_product_cost`): the parent module's two-adic
    axis-twist cost. It satisfies the full base (including two-calibration:
    J-reciprocity hides the inversion on its own axis); this module adds the
    signed-unit and zero-orbit fields (the twist fixes `-1` and `0` since
    both have zero 2-adic valuation displays), and the parent already proves
    it fails prime-pair products at the mixed (2,3) orbit.

  * SIGNED UNIT (`signed_unit`): the parent module's absolute-value cost.
    The parent already proves base + pairs + zero-orbit calibration and the
    failure at `-1`; this round only repackages against the sans-sign class.

  * ZERO ORBIT (`zero_calibrated`): round 2's refutation of
    `PRCSignedStrengthenedNativeCostUniquenessTarget` by the zero-flat
    witness, reused verbatim.

  The terminal deposit `SlimLedgerMinimalityCertificate` bundles the round-2
  uniqueness theorem with the four necessity refutations. Tag deliberation:
  the prompt allowed `classicalExtension` (round 1's wall convention), but
  all cost domains and codomains here are `RatioOrbit` and all display
  arithmetic is discrete; the stock witnesses are arithmetically explicit,
  although some parent wrappers use eliminable classical equality tests, and
  the targets quantify over the function type `RatioOrbit → RatioOrbit`
  exactly as the round-1/2 deposits already tagged `deltaOnly` do. No
  completed carrier, continuum object, or continuity premise appears in any
  statement or witness; round 1's wall was `classicalExtension` because its
  subject was the continuum price, which is absent here. The certificate is
  therefore minted at `deltaOnly`; the axiom audit (standard basis) is
  printed at the bottom. (Cross-family review: Codex gpt-5.6-sol xhigh,
  2026-07-24, verdict MINT; tag reasoning endorsed with this wording.)

  Preregistered bonus (Part 5b): the nonzero RCL core is ALSO necessary,
  witnessed by the `5`-spike (canonical J displays everywhere except the
  `5`- and `1/5`-displays, sent to `0`): no retained calibration probe
  reaches orbit `5`, so the spike inhabits "slim minus RCL" and differs from
  J there. The frozen certificate keeps its preregistered five-field shape;
  the bonus is a separate deposit (`PRCSlimSansRclUniquenessTarget_refuted`).

  Scope note: the remaining base structural fields (reciprocity,
  normalization invariance, unit-zero) define what a native cost IS rather
  than calibrating it against J; their individual necessity is out of scope
  here and stays OPEN (recorded in the prereg).

  Scope: reads `PRCNativeCostMinimality.lean` (and through it the round-1
  module and the parent). It edits none of them and never touches
  `cost_selection_holds`, `cost_selection_native_holds`,
  `cost_selection_native_slim_holds`, or their tags.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCNativeCostMinimality

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace PRCJCost

open scoped ArithmeticFunction.Omega

/-! ## Part 1: the Liouville sign twist

The two-point-anchor necessity witness. `liouvilleSign` reads the parity of
the total prime-exponent count of the reduced fraction; the twist multiplies
each display by that sign. -/

/-- The Liouville-type sign of a rational display: `(-1)` to the total number
of prime factors (with multiplicity) of numerator and denominator of the
reduced fraction; Mathlib's `cardFactors` totalizes `Ω 0 = 0`, so the sign is
`+1` at `0`. `-1` on every prime, `±1` everywhere. -/
def liouvilleSign (t : ℚ) : ℚ :=
  (-1) ^ (Ω t.num.natAbs + Ω t.den)

/-- The twisted display `liouvilleSign t · t`. -/
def liouvilleTwistDisplay (t : ℚ) : ℚ :=
  liouvilleSign t * t

theorem liouvilleSign_mul_self (t : ℚ) :
    liouvilleSign t * liouvilleSign t = 1 := by
  rw [liouvilleSign, ← pow_add, ← two_mul, pow_mul]
  norm_num

theorem liouvilleSign_ne_zero (t : ℚ) : liouvilleSign t ≠ 0 := by
  rw [liouvilleSign]
  positivity

theorem liouvilleSign_one : liouvilleSign 1 = 1 := by
  rw [liouvilleSign]
  norm_num

theorem liouvilleSign_neg_one : liouvilleSign (-1) = 1 := by
  rw [liouvilleSign]
  norm_num

/-- The reduced-fraction cross identity for products: numerators and
denominators of `t₁ * t₂` differ from the raw products only by a common
cancelled factor. -/
theorem rat_mul_num_den_cross (t₁ t₂ : ℚ) :
    (t₁ * t₂).num * ((t₁.den : ℤ) * (t₂.den : ℤ)) =
      t₁.num * t₂.num * ((t₁ * t₂).den : ℤ) := by
  have h1 : ((t₁ * t₂).num : ℚ) = (t₁ * t₂) * (((t₁ * t₂).den : ℚ)) :=
    (div_eq_iff (by exact_mod_cast (t₁ * t₂).den_ne_zero)).mp
      (Rat.num_div_den (t₁ * t₂))
  have h2 : (t₁.num : ℚ) = t₁ * ((t₁.den : ℚ)) :=
    (div_eq_iff (by exact_mod_cast t₁.den_ne_zero)).mp (Rat.num_div_den t₁)
  have h3 : (t₂.num : ℚ) = t₂ * ((t₂.den : ℚ)) :=
    (div_eq_iff (by exact_mod_cast t₂.den_ne_zero)).mp (Rat.num_div_den t₂)
  have key : ((t₁ * t₂).num : ℚ) * ((t₁.den : ℚ) * (t₂.den : ℚ)) =
      (t₁.num : ℚ) * (t₂.num : ℚ) * (((t₁ * t₂).den : ℚ)) := by
    rw [h1, h2, h3]
    ring
  exact_mod_cast key

/-- Complete multiplicativity of the Liouville sign on nonzero rationals:
cancellation removes the same factors from numerator and denominator, so the
total parity is preserved. -/
theorem liouvilleSign_mul {t₁ t₂ : ℚ} (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) :
    liouvilleSign (t₁ * t₂) = liouvilleSign t₁ * liouvilleSign t₂ := by
  have hA : (t₁ * t₂).num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr (mul_ne_zero h₁ h₂))
  have hn₁ : t₁.num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr h₁)
  have hn₂ : t₂.num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr h₂)
  have hd₁ : t₁.den ≠ 0 := t₁.den_ne_zero
  have hd₂ : t₂.den ≠ 0 := t₂.den_ne_zero
  have hD : (t₁ * t₂).den ≠ 0 := (t₁ * t₂).den_ne_zero
  have hcross : (t₁ * t₂).num.natAbs * (t₁.den * t₂.den) =
      t₁.num.natAbs * t₂.num.natAbs * (t₁ * t₂).den := by
    have h := congrArg Int.natAbs (rat_mul_num_den_cross t₁ t₂)
    simpa [Int.natAbs_mul] using h
  have hexp : Ω (t₁ * t₂).num.natAbs + (Ω t₁.den + Ω t₂.den) =
      (Ω t₁.num.natAbs + Ω t₂.num.natAbs) + Ω (t₁ * t₂).den := by
    have hL : Ω ((t₁ * t₂).num.natAbs * (t₁.den * t₂.den)) =
        Ω (t₁ * t₂).num.natAbs + (Ω t₁.den + Ω t₂.den) := by
      rw [ArithmeticFunction.cardFactors_mul hA (mul_ne_zero hd₁ hd₂),
        ArithmeticFunction.cardFactors_mul hd₁ hd₂]
    have hR : Ω (t₁.num.natAbs * t₂.num.natAbs * (t₁ * t₂).den) =
        (Ω t₁.num.natAbs + Ω t₂.num.natAbs) + Ω (t₁ * t₂).den := by
      rw [ArithmeticFunction.cardFactors_mul (mul_ne_zero hn₁ hn₂) hD,
        ArithmeticFunction.cardFactors_mul hn₁ hn₂]
    rw [← hL, ← hR, hcross]
  have hmod : (Ω (t₁ * t₂).num.natAbs + Ω (t₁ * t₂).den) % 2 =
      (Ω t₁.num.natAbs + Ω t₁.den + (Ω t₂.num.natAbs + Ω t₂.den)) % 2 := by
    omega
  rw [liouvilleSign, liouvilleSign, liouvilleSign, ← pow_add,
    neg_one_pow_eq_pow_mod_two, hmod, ← neg_one_pow_eq_pow_mod_two]

theorem liouvilleSign_inv {t : ℚ} (h : t ≠ 0) :
    liouvilleSign t⁻¹ = liouvilleSign t := by
  have hmul := liouvilleSign_mul h (inv_ne_zero h)
  rw [mul_inv_cancel₀ h, liouvilleSign_one] at hmul
  calc liouvilleSign t⁻¹
      = liouvilleSign t * liouvilleSign t * liouvilleSign t⁻¹ := by
        rw [liouvilleSign_mul_self, one_mul]
    _ = liouvilleSign t * (liouvilleSign t * liouvilleSign t⁻¹) := by ring
    _ = liouvilleSign t := by rw [← hmul, mul_one]

theorem liouvilleSign_natCast_prime {p : ℕ} (hp : p.Prime) :
    liouvilleSign (p : ℚ) = -1 := by
  rw [liouvilleSign, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast,
    ArithmeticFunction.cardFactors_apply_prime hp,
    ArithmeticFunction.cardFactors_one]
  norm_num

/-! ### Twist-value lemmas -/

theorem liouvilleTwistDisplay_zero : liouvilleTwistDisplay 0 = 0 := by
  rw [liouvilleTwistDisplay, mul_zero]

theorem liouvilleTwistDisplay_one : liouvilleTwistDisplay 1 = 1 := by
  rw [liouvilleTwistDisplay, liouvilleSign_one, mul_one]

theorem liouvilleTwistDisplay_neg_one : liouvilleTwistDisplay (-1) = -1 := by
  rw [liouvilleTwistDisplay, liouvilleSign_neg_one, one_mul]

theorem liouvilleTwistDisplay_two : liouvilleTwistDisplay 2 = -2 := by
  have h2 : liouvilleSign (2 : ℚ) = -1 := by
    have := liouvilleSign_natCast_prime (p := 2) Nat.prime_two
    simpa using this
  rw [liouvilleTwistDisplay, h2]
  norm_num

theorem liouvilleTwistDisplay_ne_zero {t : ℚ} (h : t ≠ 0) :
    liouvilleTwistDisplay t ≠ 0 :=
  mul_ne_zero (liouvilleSign_ne_zero t) h

theorem liouvilleTwistDisplay_mul {t₁ t₂ : ℚ} (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) :
    liouvilleTwistDisplay (t₁ * t₂) =
      liouvilleTwistDisplay t₁ * liouvilleTwistDisplay t₂ := by
  rw [liouvilleTwistDisplay, liouvilleTwistDisplay, liouvilleTwistDisplay,
    liouvilleSign_mul h₁ h₂]
  ring

theorem liouvilleTwistDisplay_inv (t : ℚ) :
    liouvilleTwistDisplay t⁻¹ = (liouvilleTwistDisplay t)⁻¹ := by
  by_cases h : t = 0
  · rw [h]
    simp [liouvilleTwistDisplay_zero]
  · rw [liouvilleTwistDisplay, liouvilleTwistDisplay, liouvilleSign_inv h,
      mul_inv]
    have hs := liouvilleSign_mul_self t
    have hne := liouvilleSign_ne_zero t
    have hinv : (liouvilleSign t)⁻¹ = liouvilleSign t := by
      field_simp
      nlinarith [hs]
    rw [hinv]

/-- Signs cancel on products of two primes (including `p = r`). -/
theorem liouvilleTwistDisplay_prime_pair {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) :
    liouvilleTwistDisplay ((p : ℚ) * (r : ℚ)) = (p : ℚ) * (r : ℚ) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne_zero
  rw [liouvilleTwistDisplay, liouvilleSign_mul hp0 hr0,
    liouvilleSign_natCast_prime hp, liouvilleSign_natCast_prime hr]
  ring

/-! ### The Liouville-twisted native cost -/

/-- The Liouville-twisted native cost: displays `J(liouvilleSign t · t)` on
every orbit, with the unit display sent to the literal zero representative
(the standard exact-unit wrapper). -/
def liouvilleTwistNativeCost (q : RatioOrbit) : RatioOrbit :=
  if q.toRat = 1 then RatioOrbit.zero
  else onRatioOrbit (ratioOrbitOfRat (liouvilleTwistDisplay q.toRat))

theorem liouvilleTwistNativeCost_toRat (q : RatioOrbit) :
    (liouvilleTwistNativeCost q).toRat =
      (liouvilleTwistDisplay q.toRat +
        (liouvilleTwistDisplay q.toRat)⁻¹) / 2 - 1 := by
  rw [liouvilleTwistNativeCost]
  by_cases h : q.toRat = 1
  · rw [if_pos h, RatioOrbit.zero_toRat, h, liouvilleTwistDisplay_one]
    norm_num
  · rw [if_neg h, onRatioOrbit_toRat, ratioOrbitOfRat_toRat]

/-! ## Part 2: the sans-two-calibration class and its refutation -/

/-- The base native-cost fields WITHOUT the two-point anchor. -/
structure PRCNativeCostHypothesesSansTwoCalibration
    (F : RatioOrbit → RatioOrbit) : Prop where
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

/-- Slim ledger minus the two-point anchor: base-sans-two + pairs + sign +
zero. -/
structure PRCSlimSansTwoCalibrationHypotheses
    (F : RatioOrbit → RatioOrbit) : Prop where
  base_sans_two : PRCNativeCostHypothesesSansTwoCalibration F
  prime_pair_product_cost : PRCNativeCostPrimePairProductCalibrated F
  signed_unit : PRCNativeCostSignedUnitCalibrated F
  zero_calibrated :
    PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F)

/-- Uniqueness target for the sans-two-calibration class. -/
def PRCSlimSansTwoCalibrationUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCSlimSansTwoCalibrationHypotheses F →
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (F q) (onRatioOrbit q)

/-- Bridging iff: the slim ledger is exactly the sans-two class plus the
two-point anchor, so the refutation below is a necessity statement about the
slim ledger's own field. -/
theorem slim_iff_sansTwo_and_two_calibrated (F : RatioOrbit → RatioOrbit) :
    PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses F ↔
      (PRCSlimSansTwoCalibrationHypotheses F ∧
        RatioOrbit.crossEq (F two) (onRatioOrbit two)) := by
  constructor
  · intro h
    exact ⟨⟨⟨h.signed_strengthened.strengthened.native.reciprocal,
        h.signed_strengthened.strengthened.native.normalized_invariant,
        h.signed_strengthened.strengthened.native.canonical_rcl,
        h.signed_strengthened.strengthened.native.unit_zero⟩,
      h.signed_strengthened.strengthened.prime_pair_product_cost,
      h.signed_strengthened.signed_unit,
      h.zero_calibrated⟩,
      h.signed_strengthened.strengthened.native.two_calibrated⟩
  · rintro ⟨h, htwo⟩
    exact ⟨⟨⟨⟨h.base_sans_two.reciprocal, h.base_sans_two.normalized_invariant,
        h.base_sans_two.canonical_rcl, h.base_sans_two.unit_zero, htwo⟩,
      h.prime_pair_product_cost⟩, h.signed_unit⟩, h.zero_calibrated⟩

/-- Non-vacuity of the sans-two class: the canonical witness inhabits it. -/
theorem canonicalSelectedNativeCost_sans_two_hypotheses :
    PRCSlimSansTwoCalibrationHypotheses canonicalSelectedNativeCost :=
  ((slim_iff_sansTwo_and_two_calibrated canonicalSelectedNativeCost).mp
    canonicalSelectedNativeCost_slim_hypotheses).1

/-- The Liouville twist satisfies every slim field except the two-point
anchor. -/
theorem liouvilleTwistNativeCost_sans_two_hypotheses :
    PRCSlimSansTwoCalibrationHypotheses liouvilleTwistNativeCost where
  base_sans_two :=
    { reciprocal := by
        intro q
        rw [RatioOrbit.crossEq_iff_toRat_eq, liouvilleTwistNativeCost_toRat,
          liouvilleTwistNativeCost_toRat, RatioOrbit.recip_toRat,
          liouvilleTwistDisplay_inv, inv_inv]
        ring
      normalized_invariant := by
        intro q
        rw [RatioOrbit.crossEq_iff_toRat_eq, liouvilleTwistNativeCost_toRat,
          liouvilleTwistNativeCost_toRat, DistinctionNat.normalizeRatio_toRat]
      canonical_rcl := by
        intro x y hx hy
        rw [RatioOrbit.crossEq_iff_toRat_eq]
        simp only [RatioOrbit.add_toRat, RatioOrbit.mul_toRat,
          liouvilleTwistNativeCost_toRat, div_toRat, two_toRat]
        have hdiv : x.toRat / y.toRat = x.toRat * y.toRat⁻¹ :=
          div_eq_mul_inv _ _
        rw [liouvilleTwistDisplay_mul hx hy, hdiv,
          liouvilleTwistDisplay_mul hx (inv_ne_zero hy),
          liouvilleTwistDisplay_inv]
        have ha : liouvilleTwistDisplay x.toRat ≠ 0 :=
          liouvilleTwistDisplay_ne_zero hx
        have hb : liouvilleTwistDisplay y.toRat ≠ 0 :=
          liouvilleTwistDisplay_ne_zero hy
        field_simp
        ring
      unit_zero := by
        rw [liouvilleTwistNativeCost, if_pos RatioOrbit.one_toRat] }
  prime_pair_product_cost := by
    intro p hp r hr
    rw [RatioOrbit.crossEq_iff_toRat_eq, liouvilleTwistNativeCost_toRat,
      onRatioOrbit_toRat, RatioOrbit.mul_toRat, primeDirection_toRat,
      primeDirection_toRat,
      liouvilleTwistDisplay_prime_pair (natPrime_toNat_of_primeOrbit hp)
        (natPrime_toNat_of_primeOrbit hr)]
  signed_unit := by
    rw [PRCNativeCostSignedUnitCalibrated, RatioOrbit.crossEq_iff_toRat_eq,
      liouvilleTwistNativeCost_toRat, onRatioOrbit_toRat,
      negativeOneRatio_toRat, liouvilleTwistDisplay_neg_one]
  zero_calibrated := by
    rw [PRCDoubledTraceZeroCalibrated, RatioOrbit.crossEq_iff_toRat_eq]
    simp only [nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.mul_toRat,
      RatioOrbit.add_toRat, two_toRat, RatioOrbit.one_toRat,
      liouvilleTwistNativeCost_toRat, RatioOrbit.zero_toRat,
      liouvilleTwistDisplay_zero]
    norm_num

/-- The Liouville twist fails the two-point anchor: it displays `J(-2) = -9/4`
at orbit 2 against the canonical `J(2) = 1/4`. -/
theorem liouvilleTwistNativeCost_two_not_canonical :
    ¬ RatioOrbit.crossEq (liouvilleTwistNativeCost two) (onRatioOrbit two) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, liouvilleTwistNativeCost_toRat,
    onRatioOrbit_toRat, two_toRat, liouvilleTwistDisplay_two]
  norm_num

/-- **Two-point-anchor necessity.** Slim minus two-calibration admits the
Liouville twist, so the anchor cannot be dropped. -/
theorem PRCSlimSansTwoCalibrationUniquenessTarget_refuted :
    ¬ PRCSlimSansTwoCalibrationUniquenessTarget := by
  intro huniq
  exact liouvilleTwistNativeCost_two_not_canonical
    (huniq liouvilleTwistNativeCost
      liouvilleTwistNativeCost_sans_two_hypotheses two)

/-! ## Part 3: the sans-pair class and its refutation -/

/-- Slim ledger minus prime-pair products: full base + sign + zero. -/
structure PRCSlimSansPairHypotheses
    (F : RatioOrbit → RatioOrbit) : Prop where
  native : PRCNativeCostHypotheses F
  signed_unit : PRCNativeCostSignedUnitCalibrated F
  zero_calibrated :
    PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F)

/-- Uniqueness target for the sans-pair class. -/
def PRCSlimSansPairUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCSlimSansPairHypotheses F →
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (F q) (onRatioOrbit q)

/-- Bridging iff for the pair field. -/
theorem slim_iff_sansPair_and_pair_calibrated (F : RatioOrbit → RatioOrbit) :
    PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses F ↔
      (PRCSlimSansPairHypotheses F ∧
        PRCNativeCostPrimePairProductCalibrated F) := by
  constructor
  · intro h
    exact ⟨⟨h.signed_strengthened.strengthened.native,
      h.signed_strengthened.signed_unit, h.zero_calibrated⟩,
      h.signed_strengthened.strengthened.prime_pair_product_cost⟩
  · rintro ⟨h, hpair⟩
    exact ⟨⟨⟨h.native, hpair⟩, h.signed_unit⟩, h.zero_calibrated⟩

/-- Non-vacuity of the sans-pair class. -/
theorem canonicalSelectedNativeCost_sans_pair_hypotheses :
    PRCSlimSansPairHypotheses canonicalSelectedNativeCost :=
  ((slim_iff_sansPair_and_pair_calibrated canonicalSelectedNativeCost).mp
    canonicalSelectedNativeCost_slim_hypotheses).1

/-- The two-adic twist fixes the display `0` (its numerator kills the
product). -/
theorem twoAdicTwistRat_zero : twoAdicTwistRat 0 = 0 := by
  unfold twoAdicTwistRat
  exact zero_mul _

/-- The two-adic twist fixes the signed unit: `-1` has zero 2-adic
valuation. -/
theorem twoAdicTwistRat_neg_one : twoAdicTwistRat (-1) = -1 := by
  unfold twoAdicTwistRat
  have h : padicValRat 2 (-1 : ℚ) = 0 := by
    rw [padicValRat.neg]
    norm_num [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd]
  rw [h]
  norm_num

/-- The two-adic axis-twist cost calibrates the signed unit. -/
theorem twoAdicGeneratedNativeCost_signed_unit :
    PRCNativeCostSignedUnitCalibrated twoAdicGeneratedNativeCost := by
  rw [PRCNativeCostSignedUnitCalibrated]
  refine RatioOrbit.crossEq_trans
    (twoAdicGeneratedNativeCost_crossEq_generated negativeOneRatio) ?_
  rw [RatioOrbit.crossEq_iff_toRat_eq, costFromCharacter_toRat,
    twoAdicAxisTwistCharacter_toRat, onRatioOrbit_toRat,
    negativeOneRatio_toRat, twoAdicTwistRat_neg_one]

/-- The two-adic axis-twist cost calibrates the zero orbit. -/
theorem twoAdicGeneratedNativeCost_zero_calibrated :
    PRCDoubledTraceZeroCalibrated
      (nativeCostDoubledTrace twoAdicGeneratedNativeCost) := by
  rw [PRCDoubledTraceZeroCalibrated, RatioOrbit.crossEq_iff_toRat_eq]
  have hgen := twoAdicGeneratedNativeCost_crossEq_generated RatioOrbit.zero
  rw [RatioOrbit.crossEq_iff_toRat_eq, costFromCharacter_toRat,
    twoAdicAxisTwistCharacter_toRat, RatioOrbit.zero_toRat,
    twoAdicTwistRat_zero] at hgen
  simp only [nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.mul_toRat,
    RatioOrbit.add_toRat, two_toRat, RatioOrbit.one_toRat,
    RatioOrbit.zero_toRat, hgen]
  norm_num

/-- The two-adic twist inhabits the sans-pair class. -/
theorem twoAdicGeneratedNativeCost_sans_pair_hypotheses :
    PRCSlimSansPairHypotheses twoAdicGeneratedNativeCost where
  native := twoAdicGeneratedNativeCost_hypotheses
  signed_unit := twoAdicGeneratedNativeCost_signed_unit
  zero_calibrated := twoAdicGeneratedNativeCost_zero_calibrated

/-- **Pair-field necessity.** Base + sign + zero admit the two-adic twist,
which the parent module proves fails prime-pair products at the mixed (2,3)
orbit; the pair field cannot be dropped. -/
theorem PRCSlimSansPairUniquenessTarget_refuted :
    ¬ PRCSlimSansPairUniquenessTarget := by
  intro huniq
  apply twoAdicGeneratedNativeCost_not_prime_pair_product_calibrated
  intro p hp r hr
  exact huniq twoAdicGeneratedNativeCost
    twoAdicGeneratedNativeCost_sans_pair_hypotheses
    (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr))

/-! ## Part 4: the sans-sign class and its refutation -/

/-- Slim ledger minus the signed unit: strengthened (base + pairs) + zero. -/
structure PRCSlimSansSignHypotheses
    (F : RatioOrbit → RatioOrbit) : Prop where
  strengthened : PRCStrengthenedNativeCostHypotheses F
  zero_calibrated :
    PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F)

/-- Uniqueness target for the sans-sign class. -/
def PRCSlimSansSignUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCSlimSansSignHypotheses F →
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (F q) (onRatioOrbit q)

/-- Bridging iff for the signed-unit field. -/
theorem slim_iff_sansSign_and_signed_unit (F : RatioOrbit → RatioOrbit) :
    PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses F ↔
      (PRCSlimSansSignHypotheses F ∧
        PRCNativeCostSignedUnitCalibrated F) := by
  constructor
  · intro h
    exact ⟨⟨h.signed_strengthened.strengthened, h.zero_calibrated⟩,
      h.signed_strengthened.signed_unit⟩
  · rintro ⟨h, hsign⟩
    exact ⟨⟨h.strengthened, hsign⟩, h.zero_calibrated⟩

/-- Non-vacuity of the sans-sign class. -/
theorem canonicalSelectedNativeCost_sans_sign_hypotheses :
    PRCSlimSansSignHypotheses canonicalSelectedNativeCost :=
  ((slim_iff_sansSign_and_signed_unit canonicalSelectedNativeCost).mp
    canonicalSelectedNativeCost_slim_hypotheses).1

/-- The absolute-value cost inhabits the sans-sign class (all fields already
proved in the parent module). -/
theorem absValueGeneratedNativeCost_sans_sign_hypotheses :
    PRCSlimSansSignHypotheses absValueGeneratedNativeCost where
  strengthened := absValueGeneratedNativeCost_strengthened_hypotheses
  zero_calibrated := absValueGeneratedNativeCost_doubled_trace_zero_calibrated

/-- **Signed-unit necessity.** Base + pairs + zero admit the absolute-value
cost, which the parent module proves fails at the signed unit; the sign field
cannot be dropped. -/
theorem PRCSlimSansSignUniquenessTarget_refuted :
    ¬ PRCSlimSansSignUniquenessTarget := by
  intro huniq
  exact absValueGeneratedNativeCost_negative_one_not_canonical
    (huniq absValueGeneratedNativeCost
      absValueGeneratedNativeCost_sans_sign_hypotheses negativeOneRatio)

/-! ## Part 5: the sans-zero class (round-2 reuse)

Slim minus the zero-orbit field IS `PRCSignedStrengthenedNativeCostHypotheses`
verbatim, and its uniqueness target was refuted in round 2 by the zero-flat
witness. Only the bridging iff is new. -/

/-- Bridging iff for the zero-orbit field (definitional). -/
theorem slim_iff_sansZero_and_zero_calibrated (F : RatioOrbit → RatioOrbit) :
    PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses F ↔
      (PRCSignedStrengthenedNativeCostHypotheses F ∧
        PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F)) :=
  ⟨fun h => ⟨h.signed_strengthened, h.zero_calibrated⟩,
    fun h => ⟨h.1, h.2⟩⟩

/-- Non-vacuity of the sans-zero class. -/
theorem canonicalSelectedNativeCost_sans_zero_hypotheses :
    PRCSignedStrengthenedNativeCostHypotheses canonicalSelectedNativeCost :=
  canonicalSelectedNativeCost_slim_hypotheses.signed_strengthened

/-! ## Part 5b (preregistered bonus): the RCL core is necessary

The prereg allowed one bonus beyond the four removable calibration fields:
necessity of the nonzero RCL itself, witnessed by a spike at an orbit no
retained field can reach. Orbit `5` qualifies: the calibration probes are
`2` (two-point anchor), products of two primes (never a prime), `-1`, `0`,
and `1`, and the reciprocity/normalization fields only move a spike between
`5` and `1/5`. The spiked cost (canonical J displays everywhere except the
`5`- and `1/5`-displays, which are sent to `0`) inhabits "slim minus RCL"
and differs from J at `5`. This does NOT extend to the remaining structural
fields (reciprocity, normalization invariance, unit-zero), whose necessity
stays OPEN. The frozen certificate structure below keeps its preregistered
shape; this section is a separate deposit. -/

/-- The base native-cost fields WITHOUT the nonzero RCL. -/
structure PRCNativeCostHypothesesSansRcl
    (F : RatioOrbit → RatioOrbit) : Prop where
  reciprocal :
    ∀ q, RatioOrbit.crossEq (F q) (F (RatioOrbit.recip q))
  normalized_invariant :
    ∀ q, RatioOrbit.crossEq (F q) (F (DistinctionNat.normalizeRatio q))
  unit_zero :
    F RatioOrbit.one = RatioOrbit.zero
  two_calibrated :
    RatioOrbit.crossEq (F two) (onRatioOrbit two)

/-- Slim ledger minus the nonzero RCL. -/
structure PRCSlimSansRclHypotheses
    (F : RatioOrbit → RatioOrbit) : Prop where
  base_sans_rcl : PRCNativeCostHypothesesSansRcl F
  prime_pair_product_cost : PRCNativeCostPrimePairProductCalibrated F
  signed_unit : PRCNativeCostSignedUnitCalibrated F
  zero_calibrated :
    PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F)

/-- Uniqueness target for the sans-RCL class. -/
def PRCSlimSansRclUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCSlimSansRclHypotheses F →
      ∀ q : RatioOrbit,
        RatioOrbit.crossEq (F q) (onRatioOrbit q)

/-- Bridging iff for the RCL field (explicit binders on the RCL component). -/
theorem slim_iff_sansRcl_and_rcl (F : RatioOrbit → RatioOrbit) :
    PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses F ↔
      (PRCSlimSansRclHypotheses F ∧
        (∀ x y : RatioOrbit, x.toRat ≠ 0 → y.toRat ≠ 0 →
          RatioOrbit.crossEq
            (RatioOrbit.add (F (RatioOrbit.mul x y)) (F (div x y)))
            (RatioOrbit.add
              (RatioOrbit.add
                (RatioOrbit.mul two (RatioOrbit.mul (F x) (F y)))
                (RatioOrbit.mul two (F x)))
              (RatioOrbit.mul two (F y))))) := by
  constructor
  · intro h
    exact ⟨⟨⟨h.signed_strengthened.strengthened.native.reciprocal,
        h.signed_strengthened.strengthened.native.normalized_invariant,
        h.signed_strengthened.strengthened.native.unit_zero,
        h.signed_strengthened.strengthened.native.two_calibrated⟩,
      h.signed_strengthened.strengthened.prime_pair_product_cost,
      h.signed_strengthened.signed_unit,
      h.zero_calibrated⟩,
      fun _ _ hx hy =>
        h.signed_strengthened.strengthened.native.canonical_rcl hx hy⟩
  · rintro ⟨h, hrcl⟩
    exact ⟨⟨⟨⟨h.base_sans_rcl.reciprocal,
        h.base_sans_rcl.normalized_invariant,
        fun {x y} hx hy => hrcl x y hx hy,
        h.base_sans_rcl.unit_zero,
        h.base_sans_rcl.two_calibrated⟩,
      h.prime_pair_product_cost⟩, h.signed_unit⟩, h.zero_calibrated⟩

/-- Non-vacuity of the sans-RCL class. -/
theorem canonicalSelectedNativeCost_sans_rcl_hypotheses :
    PRCSlimSansRclHypotheses canonicalSelectedNativeCost :=
  ((slim_iff_sansRcl_and_rcl canonicalSelectedNativeCost).mp
    canonicalSelectedNativeCost_slim_hypotheses).1

/-- The RCL-spike witness: canonical J displays everywhere except the `5`-
and `1/5`-displays, which are sent to the zero representative. -/
def rclSpikeNativeCost (q : RatioOrbit) : RatioOrbit :=
  if q.toRat = 5 ∨ q.toRat = 5⁻¹ then RatioOrbit.zero
  else canonicalSelectedNativeCost q

theorem rclSpikeNativeCost_toRat (q : RatioOrbit) :
    (rclSpikeNativeCost q).toRat =
      if q.toRat = 5 ∨ q.toRat = 5⁻¹ then 0
      else (q.toRat + q.toRat⁻¹) / 2 - 1 := by
  rw [rclSpikeNativeCost]
  split_ifs with h
  · exact RatioOrbit.zero_toRat
  · exact canonicalSelectedNativeCost_toRat q

/-- The spike set is closed under display inversion. -/
theorem rclSpike_inv_iff (t : ℚ) :
    (t⁻¹ = 5 ∨ t⁻¹ = 5⁻¹) ↔ (t = 5 ∨ t = 5⁻¹) := by
  constructor
  · rintro (h | h)
    · right
      rw [inv_eq_iff_eq_inv] at h
      exact h
    · left
      exact inv_inj.mp (by rw [h])
  · rintro (h | h)
    · right
      rw [h]
    · left
      rw [h, inv_inv]

theorem rclSpikeNativeCost_sans_rcl_hypotheses :
    PRCSlimSansRclHypotheses rclSpikeNativeCost where
  base_sans_rcl :=
    { reciprocal := by
        intro q
        rw [RatioOrbit.crossEq_iff_toRat_eq, rclSpikeNativeCost_toRat,
          rclSpikeNativeCost_toRat, RatioOrbit.recip_toRat]
        by_cases h : q.toRat = 5 ∨ q.toRat = 5⁻¹
        · rw [if_pos h, if_pos ((rclSpike_inv_iff q.toRat).mpr h)]
        · rw [if_neg h, if_neg (fun hc => h ((rclSpike_inv_iff q.toRat).mp hc))]
          by_cases hq : q.toRat = 0
          · rw [hq]
            norm_num
          · field_simp
            ring
      normalized_invariant := by
        intro q
        rw [RatioOrbit.crossEq_iff_toRat_eq, rclSpikeNativeCost_toRat,
          rclSpikeNativeCost_toRat, DistinctionNat.normalizeRatio_toRat]
      unit_zero := by
        rw [rclSpikeNativeCost,
          if_neg (by rw [RatioOrbit.one_toRat]; norm_num)]
        exact canonicalSelectedNativeCost_native_hypotheses.unit_zero
      two_calibrated := by
        have h : rclSpikeNativeCost two = canonicalSelectedNativeCost two := by
          rw [rclSpikeNativeCost, if_neg (by rw [two_toRat]; norm_num)]
        rw [h]
        exact canonicalSelectedNativeCost_native_hypotheses.two_calibrated }
  prime_pair_product_cost := by
    intro p hp r hr
    have hpP : Nat.Prime p.toNat := natPrime_toNat_of_primeOrbit hp
    have hrP : Nat.Prime r.toNat := natPrime_toNat_of_primeOrbit hr
    have hnospike :
        ¬ ((RatioOrbit.mul (primeDirection p hp)
            (primeDirection r hr)).toRat = 5 ∨
          (RatioOrbit.mul (primeDirection p hp)
            (primeDirection r hr)).toRat = 5⁻¹) := by
      rw [RatioOrbit.mul_toRat, primeDirection_toRat, primeDirection_toRat]
      rintro (h | h)
      · have hnat : p.toNat * r.toNat = 5 := by exact_mod_cast h
        have h5 : Nat.Prime 5 := by norm_num
        rcases (h5.eq_one_or_self_of_dvd p.toNat ⟨r.toNat, hnat.symm⟩) with
          h1 | h5p
        · exact hpP.one_lt.ne' h1
        · rw [h5p] at hnat
          have : r.toNat = 1 := by omega
          exact hrP.one_lt.ne' this
      · have hnat : p.toNat * r.toNat * 5 = 1 := by
          have h1 : ((p.toNat : ℚ) * (r.toNat : ℚ)) * 5 = 1 := by
            rw [h]
            norm_num
          exact_mod_cast h1
        omega
    have heq :
        rclSpikeNativeCost
            (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)) =
          canonicalSelectedNativeCost
            (RatioOrbit.mul (primeDirection p hp) (primeDirection r hr)) := by
      rw [rclSpikeNativeCost, if_neg hnospike]
    rw [heq]
    exact canonicalSelectedNativeCost_crossEq_onRatioOrbit _
  signed_unit := by
    rw [PRCNativeCostSignedUnitCalibrated]
    have h : rclSpikeNativeCost negativeOneRatio =
        canonicalSelectedNativeCost negativeOneRatio := by
      rw [rclSpikeNativeCost,
        if_neg (by rw [negativeOneRatio_toRat]; norm_num)]
    rw [h]
    exact canonicalSelectedNativeCost_crossEq_onRatioOrbit negativeOneRatio
  zero_calibrated := by
    have h : rclSpikeNativeCost RatioOrbit.zero =
        canonicalSelectedNativeCost RatioOrbit.zero := by
      rw [rclSpikeNativeCost,
        if_neg (by rw [RatioOrbit.zero_toRat]; norm_num)]
    rw [PRCDoubledTraceZeroCalibrated, nativeCostDoubledTrace, h]
    exact canonicalSelectedNativeCost_full_hypotheses.zero_calibrated

/-- The spike differs from the canonical cost at the `5`-display orbit. -/
theorem rclSpikeNativeCost_five_not_canonical :
    ¬ RatioOrbit.crossEq (rclSpikeNativeCost (ratioOrbitOfRat 5))
      (onRatioOrbit (ratioOrbitOfRat 5)) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, rclSpikeNativeCost_toRat,
    onRatioOrbit_toRat, ratioOrbitOfRat_toRat,
    if_pos (Or.inl rfl)]
  norm_num

/-- **RCL-core necessity (bonus).** Slim minus the nonzero RCL admits the
`5`-spike, so the RCL field cannot be dropped either. -/
theorem PRCSlimSansRclUniquenessTarget_refuted :
    ¬ PRCSlimSansRclUniquenessTarget := by
  intro huniq
  exact rclSpikeNativeCost_five_not_canonical
    (huniq rclSpikeNativeCost rclSpikeNativeCost_sans_rcl_hypotheses
      (ratioOrbitOfRat 5))

/-! ## Part 6: the certificate -/

/-- **Field-by-field minimality certificate for the slim ledger.** The slim
ledger forces the canonical J-cost (round 2), and each of its four removable
calibration fields is necessary: dropping any one admits a kernel-checked
impostor (Liouville twist, two-adic twist, absolute-value cost, zero-flat
cost respectively). -/
structure SlimLedgerMinimalityCertificate : Prop where
  slim_uniqueness :
    PRCZeroCalibratedSignedStrengthenedNativeCostUniquenessTarget
  two_point_anchor_necessary :
    ¬ PRCSlimSansTwoCalibrationUniquenessTarget
  pair_field_necessary :
    ¬ PRCSlimSansPairUniquenessTarget
  signed_unit_necessary :
    ¬ PRCSlimSansSignUniquenessTarget
  zero_orbit_necessary :
    ¬ PRCSignedStrengthenedNativeCostUniquenessTarget

theorem slimLedgerMinimalityCertificate_holds :
    SlimLedgerMinimalityCertificate where
  slim_uniqueness :=
    PRCZeroCalibratedSignedStrengthenedNativeCostUniquenessTarget_proved
  two_point_anchor_necessary :=
    PRCSlimSansTwoCalibrationUniquenessTarget_refuted
  pair_field_necessary :=
    PRCSlimSansPairUniquenessTarget_refuted
  signed_unit_necessary :=
    PRCSlimSansSignUniquenessTarget_refuted
  zero_orbit_necessary :=
    PRCSignedStrengthenedNativeCostUniquenessTarget_refuted

/-- The certificate deposit. `deltaOnly`: all cost domains and codomains are
`RatioOrbit` and all display arithmetic is discrete; the witnesses are
arithmetically explicit (some parent wrappers use eliminable classical
equality tests), and no completed carrier, continuum object, or continuity
premise appears in any statement or witness (see the header for the
deliberation against the wall convention). -/
theorem slim_ledger_minimality_certificate_tagged :
    PublicSpine.Tagged StrengthTag.deltaOnly SlimLedgerMinimalityCertificate
    where
  holds := slimLedgerMinimalityCertificate_holds

/-! ## Axiom audit (standard basis only) -/

#print axioms slimLedgerMinimalityCertificate_holds
#print axioms slim_ledger_minimality_certificate_tagged
#print axioms PRCSlimSansTwoCalibrationUniquenessTarget_refuted
#print axioms PRCSlimSansPairUniquenessTarget_refuted
#print axioms PRCSlimSansSignUniquenessTarget_refuted
#print axioms slim_iff_sansTwo_and_two_calibrated
#print axioms slim_iff_sansPair_and_pair_calibrated
#print axioms slim_iff_sansSign_and_signed_unit
#print axioms slim_iff_sansZero_and_zero_calibrated
#print axioms PRCSlimSansRclUniquenessTarget_refuted
#print axioms slim_iff_sansRcl_and_rcl

end PRCJCost
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
