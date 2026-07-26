/-
# Real-valued character factorization for the anchor-free cost ledger

The carrier-valued factorization target is the wrong type
(`TraceRationalExponent.no_rational_character_at_trace_three`). What a cost
exposes is the TRACE. This module records the corrected target and connects it
to the algebraic core in `RealTraceRoot`.

Imports are kept light (Uniqueness already has a local olean) so the module can
build under laptop memory pressure. The SansAnchor pack is restated by fields;
it matches `PRCStructuralNativeCostHypothesesSansAnchor` in the structural
ledger when that module is available.
-/

import IndisputableMonolith.Cost.RealTraceRoot
import IndisputableMonolith.Cost.TraceRationalExponent
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCNativeCostUniqueness

namespace IndisputableMonolith
namespace Cost
namespace RealCharacterFactorization

open Foundation.PrimitiveRecognitionCalculus
open Foundation.PrimitiveRecognitionCalculus.PRCJCost
open RealTraceRoot
open TraceRationalExponent

export RealTraceRoot (realTraceRoot realTraceRoot_mul realTraceRoot_add_inv
  realTraceRoot_ge_one larger_trace_of_diff_sq)

/-! ## Doubled trace from RCL alone -/

/-- The doubled-trace form of the composition law needs only the RCL. The anchor
at two is not used. -/
theorem doubledTrace_dAlembert_of_rcl
    {F : RatioOrbit → RatioOrbit}
    (hrcl : ∀ {x y : RatioOrbit}, x.toRat ≠ 0 → y.toRat ≠ 0 →
      RatioOrbit.crossEq
        (RatioOrbit.add (F (RatioOrbit.mul x y)) (F (div x y)))
        (RatioOrbit.add
          (RatioOrbit.add
            (RatioOrbit.mul two (RatioOrbit.mul (F x) (F y)))
            (RatioOrbit.mul two (F x)))
          (RatioOrbit.mul two (F y))))
    {x y : RatioOrbit} (hx : x.toRat ≠ 0) (hy : y.toRat ≠ 0) :
    RatioOrbit.crossEq
      (RatioOrbit.add (nativeCostDoubledTrace F (RatioOrbit.mul x y))
        (nativeCostDoubledTrace F (div x y)))
      (RatioOrbit.mul (nativeCostDoubledTrace F x) (nativeCostDoubledTrace F y)) := by
  have h := hrcl hx hy
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h ⊢
  simp only [nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.mul_toRat,
    RatioOrbit.add_toRat, two_toRat, RatioOrbit.one_toRat] at h ⊢
  linarith

/-- Same theorem specialized to the native cost pack, using only its RCL field. -/
theorem doubledTrace_dAlembert_of_native
    {F : RatioOrbit → RatioOrbit}
    (hF : PRCNativeCostHypotheses F)
    {x y : RatioOrbit} (hx : x.toRat ≠ 0) (hy : y.toRat ≠ 0) :
    RatioOrbit.crossEq
      (RatioOrbit.add (nativeCostDoubledTrace F (RatioOrbit.mul x y))
        (nativeCostDoubledTrace F (div x y)))
      (RatioOrbit.mul (nativeCostDoubledTrace F x) (nativeCostDoubledTrace F y)) :=
  doubledTrace_dAlembert_of_rcl hF.canonical_rcl hx hy

/-! ## Anchor-free hypotheses, restated lightly -/

def IsPosIntOrbit (q : RatioOrbit) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ q.toRat = (n : ℚ)

def natOrbit (n : ℕ) : RatioOrbit := ratioOrbitOfRat (n : ℚ)

theorem natOrbit_toRat (n : ℕ) : (natOrbit n).toRat = (n : ℚ) :=
  ratioOrbitOfRat_toRat _

def PRCNativeCostSignReversing (F : RatioOrbit → RatioOrbit) : Prop :=
  ∀ q r : RatioOrbit, r.toRat = -q.toRat →
    (F r).toRat = -(F q).toRat - 2

def PRCNativeCostMonotone (F : RatioOrbit → RatioOrbit) : Prop :=
  ∀ a b : RatioOrbit, IsPosIntOrbit a → IsPosIntOrbit b →
    a.toRat ≤ b.toRat → (F a).toRat ≤ (F b).toRat

/-- Base sans the two-point anchor: the RCL pack without `two_calibrated`. -/
structure BaseSansTwo (F : RatioOrbit → RatioOrbit) : Prop where
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

/-- Anchor-free pack matching `PRCStructuralNativeCostHypothesesSansAnchor`. -/
structure SansAnchorHypotheses (F : RatioOrbit → RatioOrbit) : Prop where
  base_sans_two : BaseSansTwo F
  sign_reversing : PRCNativeCostSignReversing F
  monotone : PRCNativeCostMonotone F
  zero_calibrated : PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F)

theorem doubledTrace_dAlembert_of_sansAnchor
    {F : RatioOrbit → RatioOrbit}
    (hF : SansAnchorHypotheses F)
    {x y : RatioOrbit} (hx : x.toRat ≠ 0) (hy : y.toRat ≠ 0) :
    RatioOrbit.crossEq
      (RatioOrbit.add (nativeCostDoubledTrace F (RatioOrbit.mul x y))
        (nativeCostDoubledTrace F (div x y)))
      (RatioOrbit.mul (nativeCostDoubledTrace F x) (nativeCostDoubledTrace F y)) :=
  doubledTrace_dAlembert_of_rcl hF.base_sans_two.canonical_rcl hx hy

/-! ## The corrected factorization target -/

structure PRCRealRatioCharacter (χ : RatioOrbit → ℝ) : Prop where
  unit : χ RatioOrbit.one = 1
  multiplicative :
    ∀ x y : RatioOrbit,
      x.toRat ≠ 0 → y.toRat ≠ 0 →
        χ (RatioOrbit.mul x y) = χ x * χ y
  reciprocal :
    ∀ x : RatioOrbit, x.toRat ≠ 0 → χ (RatioOrbit.recip x) = (χ x)⁻¹
  nonzero :
    ∀ x : RatioOrbit, x.toRat ≠ 0 → χ x ≠ 0
  principal_on_pos_int :
    ∀ n : ℕ, 1 ≤ n → 1 ≤ χ (natOrbit n)

noncomputable def costFromRealCharacter (χ : RatioOrbit → ℝ) (q : RatioOrbit) : ℝ :=
  (χ q + (χ q)⁻¹) / 2 - 1

noncomputable def exponentOfCharacter (χ : RatioOrbit → ℝ) : ℝ :=
  Real.log (χ (natOrbit 2)) / Real.log 2

/-- **The corrected factorization target.** Every inhabitant of the anchor-free
ledger factors through a real-valued character whose traces at the small bases
are rational (so the exponent step can fire). -/
def SansAnchorRealCharacterFactorizationTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    SansAnchorHypotheses F →
      ∃ χ : RatioOrbit → ℝ,
        PRCRealRatioCharacter χ ∧
          (∀ q : RatioOrbit, 0 < q.toRat →
            ((F q).toRat : ℝ) = costFromRealCharacter χ q) ∧
          (∀ n : ℕ, 2 ≤ n → n ≤ 5 →
            ∃ t : ℚ, χ (natOrbit n) + (χ (natOrbit n))⁻¹ = (t : ℝ))

abbrev SansAnchorRealCharacterFactorizationInput : Prop :=
  SansAnchorRealCharacterFactorizationTarget

/-! ## Real display and quotient-independent rational trace -/

/-- The real display of the carrier-valued doubled trace. -/
noncomputable def traceDisplay
    (F : RatioOrbit → RatioOrbit) (q : RatioOrbit) : ℝ :=
  ((nativeCostDoubledTrace F q).toRat : ℝ)

theorem traceDisplay_one
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F) :
    traceDisplay F RatioOrbit.one = 2 := by
  simp only [traceDisplay, nativeCostDoubledTrace, doubledTraceValue,
    hF.base_sans_two.unit_zero, RatioOrbit.mul_toRat, RatioOrbit.add_toRat,
    RatioOrbit.zero_toRat, RatioOrbit.one_toRat, two_toRat]
  norm_num

theorem traceDisplay_recip
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (q : RatioOrbit) :
    traceDisplay F (RatioOrbit.recip q) = traceDisplay F q := by
  have h := doubledTraceValue_congr (hF.base_sans_two.reciprocal q)
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h
  simp only [traceDisplay, nativeCostDoubledTrace]
  exact_mod_cast h.symm

theorem traceDisplay_dAlembert
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    {x y : RatioOrbit} (hx : x.toRat ≠ 0) (hy : y.toRat ≠ 0) :
    traceDisplay F (RatioOrbit.mul x y) + traceDisplay F (div x y) =
      traceDisplay F x * traceDisplay F y := by
  have h := doubledTrace_dAlembert_of_sansAnchor hF hx hy
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.add_toRat,
    RatioOrbit.mul_toRat] at h
  simp only [traceDisplay]
  exact_mod_cast h

theorem traceDisplay_posInt_ge_two
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    {q : RatioOrbit} (hq : IsPosIntOrbit q) :
    2 ≤ traceDisplay F q := by
  have hone : IsPosIntOrbit RatioOrbit.one :=
    ⟨1, by norm_num, by rw [RatioOrbit.one_toRat]; norm_num⟩
  obtain ⟨n, hn, hqn⟩ := hq
  have hqone : RatioOrbit.one.toRat ≤ q.toRat := by
    rw [RatioOrbit.one_toRat, hqn]
    exact_mod_cast hn
  have hm := hF.monotone RatioOrbit.one q hone ⟨n, hn, hqn⟩ hqone
  rw [hF.base_sans_two.unit_zero, RatioOrbit.zero_toRat] at hm
  simp only [traceDisplay, nativeCostDoubledTrace, doubledTraceValue,
    RatioOrbit.mul_toRat, RatioOrbit.add_toRat, two_toRat,
    RatioOrbit.one_toRat]
  norm_num at hm ⊢
  exact_mod_cast (show (0 : ℚ) ≤ (F q).toRat from hm)

theorem traceDisplay_two_ge_two
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F) :
    2 ≤ traceDisplay F two :=
  traceDisplay_posInt_ge_two hF ⟨2, by norm_num, two_toRat⟩

theorem traceDisplay_eq_of_crossEq
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    {q r : RatioOrbit} (hqr : RatioOrbit.crossEq q r) :
    traceDisplay F q = traceDisplay F r := by
  have hq := doubledTraceValue_congr (hF.base_sans_two.normalized_invariant q)
  have hr := doubledTraceValue_congr (hF.base_sans_two.normalized_invariant r)
  have hnorm :
      DistinctionNat.normalizeRatio q = DistinctionNat.normalizeRatio r :=
    PRCNormalizeRatioCanonicalTarget_proved q r hqr
  rw [hnorm] at hq
  have htrace := RatioOrbit.crossEq_trans hq (RatioOrbit.crossEq_symm hr)
  rw [RatioOrbit.crossEq_iff_toRat_eq] at htrace
  simp only [traceDisplay, nativeCostDoubledTrace]
  exact_mod_cast htrace

/-- The doubled trace as an honest function on rational displays. -/
noncomputable def rationalTrace
    (F : RatioOrbit → RatioOrbit) (x : ℚ) : ℝ :=
  traceDisplay F (ratioOrbitOfRat x)

theorem rationalTrace_eq_traceDisplay
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (q : RatioOrbit) :
    rationalTrace F q.toRat = traceDisplay F q := by
  apply traceDisplay_eq_of_crossEq hF
  rw [RatioOrbit.crossEq_iff_toRat_eq, ratioOrbitOfRat_toRat]

theorem rationalTrace_one
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F) :
    rationalTrace F 1 = 2 := by
  calc
    rationalTrace F 1 = traceDisplay F RatioOrbit.one := by
      rw [rationalTrace]
      apply traceDisplay_eq_of_crossEq hF
      rw [RatioOrbit.crossEq_iff_toRat_eq, ratioOrbitOfRat_toRat,
        RatioOrbit.one_toRat]
    _ = 2 := traceDisplay_one hF

theorem rationalTrace_recip
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (x : ℚ) :
    rationalTrace F x⁻¹ = rationalTrace F x := by
  rw [rationalTrace, rationalTrace]
  calc
    traceDisplay F (ratioOrbitOfRat x⁻¹) =
        traceDisplay F (RatioOrbit.recip (ratioOrbitOfRat x)) := by
          apply traceDisplay_eq_of_crossEq hF
          rw [RatioOrbit.crossEq_iff_toRat_eq, ratioOrbitOfRat_toRat,
            RatioOrbit.recip_toRat, ratioOrbitOfRat_toRat]
    _ = traceDisplay F (ratioOrbitOfRat x) := traceDisplay_recip hF _

theorem rationalTrace_dAlembert
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    rationalTrace F (x * y) + rationalTrace F (x / y) =
      rationalTrace F x * rationalTrace F y := by
  let ox := ratioOrbitOfRat x
  let oy := ratioOrbitOfRat y
  have hox : ox.toRat ≠ 0 := by
    change (ratioOrbitOfRat x).toRat ≠ 0
    rw [ratioOrbitOfRat_toRat]
    exact hx
  have hoy : oy.toRat ≠ 0 := by
    change (ratioOrbitOfRat y).toRat ≠ 0
    rw [ratioOrbitOfRat_toRat]
    exact hy
  have hd := traceDisplay_dAlembert hF hox hoy
  have hmul :
      traceDisplay F (RatioOrbit.mul ox oy) = rationalTrace F (x * y) := by
    symm
    apply traceDisplay_eq_of_crossEq hF
    rw [RatioOrbit.crossEq_iff_toRat_eq, ratioOrbitOfRat_toRat,
      RatioOrbit.mul_toRat]
    change x * y = (ratioOrbitOfRat x).toRat * (ratioOrbitOfRat y).toRat
    rw [ratioOrbitOfRat_toRat, ratioOrbitOfRat_toRat]
  have hdiv :
      traceDisplay F (div ox oy) = rationalTrace F (x / y) := by
    symm
    apply traceDisplay_eq_of_crossEq hF
    rw [RatioOrbit.crossEq_iff_toRat_eq, ratioOrbitOfRat_toRat, div_toRat]
    change x / y = (ratioOrbitOfRat x).toRat / (ratioOrbitOfRat y).toRat
    rw [ratioOrbitOfRat_toRat, ratioOrbitOfRat_toRat]
  simpa [rationalTrace, ox, oy, hmul, hdiv] using hd

theorem rationalTrace_neg
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (x : ℚ) :
    rationalTrace F (-x) = -rationalTrace F x := by
  have hsign := hF.sign_reversing (ratioOrbitOfRat x) (ratioOrbitOfRat (-x))
    (by simp only [ratioOrbitOfRat_toRat])
  simp only [rationalTrace, traceDisplay, nativeCostDoubledTrace,
    doubledTraceValue, RatioOrbit.mul_toRat, RatioOrbit.add_toRat,
    ratioOrbitOfRat_toRat, two_toRat, RatioOrbit.one_toRat]
  norm_cast
  linarith

theorem rationalTrace_nat_ge_two
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    {n : ℕ} (hn : 1 ≤ n) :
    2 ≤ rationalTrace F n := by
  change 2 ≤ traceDisplay F (ratioOrbitOfRat (n : ℚ))
  exact traceDisplay_posInt_ge_two hF
    ⟨n, hn, ratioOrbitOfRat_toRat (n : ℚ)⟩

/-! ## Symbolic linear extraction -/

/-- Linear extraction from a nondegenerate anchor whose chosen root is `r`. -/
noncomputable def linearExtraction
    (T : ℚ → ℝ) (r : ℝ) (x : ℚ) : ℝ :=
  (r * T (2 * x) - T x) / (r ^ 2 - 1)

private theorem linearExtraction_unit
    {T : ℚ → ℝ} {r : ℝ}
    (h1 : T 1 = 2) (hr0 : r ≠ 0) (hrden : r ^ 2 - 1 ≠ 0)
    (hrtrace : r + r⁻¹ = T 2) :
    linearExtraction T r 1 = 1 := by
  have hA : T 2 = (r ^ 2 + 1) / r := by
    rw [← hrtrace, eq_div_iff hr0]
    field_simp [hr0]
  rw [linearExtraction, show (2 : ℚ) * 1 = 2 by norm_num, h1, hA]
  field_simp [hr0, hrden]
  ring

private theorem linearExtraction_multiplicative
    {T : ℚ → ℝ} {r : ℝ}
    (hrec : ∀ x : ℚ, T x⁻¹ = T x)
    (hd : ∀ {x y : ℚ}, x ≠ 0 → y ≠ 0 →
      T (x * y) + T (x / y) = T x * T y)
    (hr0 : r ≠ 0) (hrden : r ^ 2 - 1 ≠ 0)
    (hrtrace : r + r⁻¹ = T 2)
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    linearExtraction T r (x * y) =
      linearExtraction T r x * linearExtraction T r y := by
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hxdy : x / y ≠ 0 := div_ne_zero hx hy
  have h2x : (2 : ℚ) * x ≠ 0 := mul_ne_zero htwo hx
  have h2y : (2 : ℚ) * y ≠ 0 := mul_ne_zero htwo hy
  have h2xy : (2 : ℚ) * (x * y) ≠ 0 := mul_ne_zero htwo hxy
  have hx2y : x / ((2 : ℚ) * y) ≠ 0 := div_ne_zero hx h2y
  have hCC := hd hx hy
  have hDDraw := hd h2x h2y
  have hDDprod :
      ((2 : ℚ) * x) * ((2 : ℚ) * y) = 2 * (2 * (x * y)) := by ring
  have hDDquot :
      ((2 : ℚ) * x) / ((2 : ℚ) * y) = x / y := by
    field_simp [hy]
  rw [hDDprod, hDDquot] at hDDraw
  have hanchorRaw := hd htwo h2xy
  have hanchorProd :
      (2 : ℚ) * (2 * (x * y)) = 2 * (2 * (x * y)) := rfl
  have hanchorQuot :
      (2 : ℚ) / (2 * (x * y)) = (x * y)⁻¹ := by
    field_simp [hx, hy]
  rw [hanchorProd, hanchorQuot, hrec (x * y)] at hanchorRaw
  have hDD :
      T (2 * x) * T (2 * y) =
        T 2 * T (2 * (x * y)) - T (x * y) + T (x / y) := by
    linarith
  have hDCraw := hd h2x hy
  have hDCprod : ((2 : ℚ) * x) * y = 2 * (x * y) := by ring
  have hDCquot : ((2 : ℚ) * x) / y = 2 * (x / y) := by
    field_simp [hy]
  rw [hDCprod, hDCquot] at hDCraw
  have hCDraw := hd hx h2y
  have hCDprod : x * ((2 : ℚ) * y) = 2 * (x * y) := by ring
  rw [hCDprod] at hCDraw
  have hcrossRaw := hd htwo hxdy
  have hcrossProd : (2 : ℚ) * (x / y) = 2 * (x / y) := rfl
  have hcrossQuot :
      (2 : ℚ) / (x / y) = (x / ((2 : ℚ) * y))⁻¹ := by
    field_simp [hx, hy]
  rw [hcrossProd, hcrossQuot, hrec (x / ((2 : ℚ) * y))] at hcrossRaw
  have hcross :
      T (2 * x) * T y + T x * T (2 * y) =
        2 * T (2 * (x * y)) + T 2 * T (x / y) := by
    linarith
  have hA : T 2 = (r ^ 2 + 1) / r := by
    rw [← hrtrace, eq_div_iff hr0]
    field_simp [hr0]
  have hnum :
      (r * T (2 * x) - T x) * (r * T (2 * y) - T y) =
        (r ^ 2 - 1) * (r * T (2 * (x * y)) - T (x * y)) := by
    calc
      (r * T (2 * x) - T x) * (r * T (2 * y) - T y) =
          r ^ 2 * (T (2 * x) * T (2 * y)) -
            r * (T (2 * x) * T y + T x * T (2 * y)) +
              T x * T y := by ring
      _ = r ^ 2 *
            (T 2 * T (2 * (x * y)) - T (x * y) + T (x / y)) -
          r * (2 * T (2 * (x * y)) + T 2 * T (x / y)) +
            (T (x * y) + T (x / y)) := by rw [hDD, hcross, ← hCC]
      _ = (r ^ 2 - 1) * (r * T (2 * (x * y)) - T (x * y)) := by
        rw [hA]
        field_simp [hr0]
        ring
  rw [linearExtraction, linearExtraction, linearExtraction,
    show (2 : ℚ) * (x * y) = 2 * (x * y) by rfl]
  field_simp [hrden]
  convert hnum.symm using 1 <;> ring

private theorem linearExtraction_recip_sum
    {T : ℚ → ℝ} {r : ℝ}
    (hrec : ∀ x : ℚ, T x⁻¹ = T x)
    (hd : ∀ {x y : ℚ}, x ≠ 0 → y ≠ 0 →
      T (x * y) + T (x / y) = T x * T y)
    (hr0 : r ≠ 0) (hrden : r ^ 2 - 1 ≠ 0)
    (hrtrace : r + r⁻¹ = T 2)
    {x : ℚ} (hx : x ≠ 0) :
    linearExtraction T r x⁻¹ + linearExtraction T r x = T x := by
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  have hinvx : x⁻¹ ≠ 0 := inv_ne_zero hx
  have hda := hd htwo hx
  have hmul : (2 : ℚ) * x = 2 * x := rfl
  have hquot : (2 : ℚ) / x = 2 * x⁻¹ := by
    rw [div_eq_mul_inv]
  rw [hmul, hquot] at hda
  have hA : T 2 = (r ^ 2 + 1) / r := by
    rw [← hrtrace, eq_div_iff hr0]
    field_simp [hr0]
  rw [hA] at hda
  rw [linearExtraction, linearExtraction, hrec x]
  have htworecip :
      (2 : ℚ) * x⁻¹ = 2 * x⁻¹ := rfl
  rw [htworecip]
  have hnum :
      r * T (2 * x⁻¹) - T x + (r * T (2 * x) - T x) =
        (r ^ 2 - 1) * T x := by
    calc
      r * T (2 * x⁻¹) - T x + (r * T (2 * x) - T x) =
          r * (T (2 * x) + T (2 * x⁻¹)) - 2 * T x := by ring
      _ = r * (((r ^ 2 + 1) / r) * T x) - 2 * T x := by rw [hda]
      _ = (r ^ 2 - 1) * T x := by
        field_simp [hr0]
        ring
  field_simp [hr0, hrden]
  convert hnum using 1 <;> ring

/-- Principal root at the distinguished positive integer two. -/
noncomputable def anchorRoot (F : RatioOrbit → RatioOrbit) : ℝ :=
  realTraceRoot (rationalTrace F 2)

/-- The nondegenerate symbolic extraction from the trace at two. -/
noncomputable def nontrivialCharacterValue
    (F : RatioOrbit → RatioOrbit) (x : ℚ) : ℝ :=
  linearExtraction (rationalTrace F) (anchorRoot F) x

theorem anchorRoot_ge_one
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F) :
    1 ≤ anchorRoot F :=
  realTraceRoot_ge_one (by
    simpa [rationalTrace] using traceDisplay_two_ge_two hF)

theorem anchorRoot_add_inv
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F) :
    anchorRoot F + (anchorRoot F)⁻¹ = rationalTrace F 2 :=
  realTraceRoot_add_inv (by
    simpa [rationalTrace] using traceDisplay_two_ge_two hF)

theorem anchorRoot_gt_one
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (hnontrivial : rationalTrace F 2 ≠ 2) :
    1 < anchorRoot F := by
  refine lt_of_le_of_ne (anchorRoot_ge_one hF) ?_
  intro h
  have hr : anchorRoot F = 1 := h.symm
  have ht := anchorRoot_add_inv hF
  rw [hr] at ht
  norm_num at ht
  exact hnontrivial ht.symm

theorem anchorRoot_ne_zero
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F) :
    anchorRoot F ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (anchorRoot_ge_one hF))

theorem anchorRoot_sq_sub_one_ne_zero
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (hnontrivial : rationalTrace F 2 ≠ 2) :
    anchorRoot F ^ 2 - 1 ≠ 0 := by
  have hr := anchorRoot_gt_one hF hnontrivial
  nlinarith

theorem nontrivialCharacterValue_one
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (hnontrivial : rationalTrace F 2 ≠ 2) :
    nontrivialCharacterValue F 1 = 1 :=
  linearExtraction_unit (rationalTrace_one hF) (anchorRoot_ne_zero hF)
    (anchorRoot_sq_sub_one_ne_zero hF hnontrivial) (anchorRoot_add_inv hF)

theorem nontrivialCharacterValue_mul
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (hnontrivial : rationalTrace F 2 ≠ 2)
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    nontrivialCharacterValue F (x * y) =
      nontrivialCharacterValue F x * nontrivialCharacterValue F y :=
  linearExtraction_multiplicative (rationalTrace_recip hF)
    (@rationalTrace_dAlembert F hF) (anchorRoot_ne_zero hF)
    (anchorRoot_sq_sub_one_ne_zero hF hnontrivial) (anchorRoot_add_inv hF) hx hy

theorem nontrivialCharacterValue_recip_sum
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (hnontrivial : rationalTrace F 2 ≠ 2)
    {x : ℚ} (hx : x ≠ 0) :
    nontrivialCharacterValue F x⁻¹ + nontrivialCharacterValue F x =
      rationalTrace F x :=
  linearExtraction_recip_sum (rationalTrace_recip hF)
    (@rationalTrace_dAlembert F hF) (anchorRoot_ne_zero hF)
    (anchorRoot_sq_sub_one_ne_zero hF hnontrivial) (anchorRoot_add_inv hF) hx

/-! ## The degenerate anchor -/

theorem rationalTrace_nat_mono
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    rationalTrace F m ≤ rationalTrace F n := by
  have hn : 1 ≤ n := le_trans hm hmn
  have hmono := hF.monotone (natOrbit m) (natOrbit n)
    ⟨m, hm, natOrbit_toRat m⟩ ⟨n, hn, natOrbit_toRat n⟩
    (by
      rw [natOrbit_toRat, natOrbit_toRat]
      exact_mod_cast hmn)
  change
    (F (ratioOrbitOfRat (m : ℚ))).toRat ≤
      (F (ratioOrbitOfRat (n : ℚ))).toRat at hmono
  have hmonoR :
      ((F (ratioOrbitOfRat (m : ℚ))).toRat : ℝ) ≤
        ((F (ratioOrbitOfRat (n : ℚ))).toRat : ℝ) := by
    exact_mod_cast hmono
  simp only [rationalTrace, natOrbit, traceDisplay, nativeCostDoubledTrace,
    doubledTraceValue, RatioOrbit.mul_toRat, RatioOrbit.add_toRat,
    two_toRat, RatioOrbit.one_toRat]
  push_cast
  linarith

theorem rationalTrace_two_pow_eq_two
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (htwo : rationalTrace F 2 = 2) :
    ∀ k : ℕ, rationalTrace F ((2 : ℚ) ^ k) = 2 := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      simpa using rationalTrace_one hF
  | one =>
      simpa using htwo
  | more m ih0 ih1 =>
      have hx : (2 : ℚ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hd := rationalTrace_dAlembert hF hx (by norm_num : (2 : ℚ) ≠ 0)
      have hprod :
          (2 : ℚ) ^ (m + 1) * 2 = (2 : ℚ) ^ (m + 2) := by
        simp [pow_succ]
      have hquot :
          (2 : ℚ) ^ (m + 1) / 2 = (2 : ℚ) ^ m := by
        rw [show m + 1 = m + 1 by rfl, pow_succ]
        field_simp
      rw [hprod, hquot, ih0, ih1, htwo] at hd
      linarith

theorem rationalTrace_nat_eq_two_of_two_eq_two
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (htwo : rationalTrace F 2 = 2) :
    ∀ n : ℕ, 1 ≤ n → rationalTrace F n = 2 := by
  have hpow2 : ∀ n : ℕ, n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
        have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have hp : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
        omega
  intro n hn
  have hlow : 2 ≤ rationalTrace F n := rationalTrace_nat_ge_two hF hn
  have hup := rationalTrace_nat_mono hF hn (hpow2 n)
  have hcast :
      (((2 ^ n : ℕ) : ℚ)) = (2 : ℚ) ^ n := by norm_num
  rw [hcast, rationalTrace_two_pow_eq_two hF htwo n] at hup
  linarith

theorem rationalTrace_pos_eq_two_of_two_eq_two
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (htwo : rationalTrace F 2 = 2)
    {x : ℚ} (hx : 0 < x) :
    rationalTrace F x = 2 := by
  let a := x.num.toNat
  let b := x.den
  have hnumpos : 0 < x.num := Rat.num_pos.mpr hx
  have hapos : 0 < a := by
    change 0 < x.num.toNat
    omega
  have hbpos : 0 < b := by
    change 0 < x.den
    exact x.pos
  have ha1 : 1 ≤ a := hapos
  have hb1 : 1 ≤ b := hbpos
  have haa : (a : ℚ) ≠ 0 := by exact_mod_cast hapos.ne'
  have hbb : (b : ℚ) ≠ 0 := by exact_mod_cast hbpos.ne'
  have hxrep : (a : ℚ) / (b : ℚ) = x := by
    change ((x.num.toNat : ℕ) : ℚ) / (x.den : ℚ) = x
    have hnum :
        ((x.num.toNat : ℕ) : ℚ) = ((x.num : ℤ) : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (le_of_lt hnumpos)
    rw [hnum]
    exact Rat.num_div_den x
  have hd := rationalTrace_dAlembert hF (x := (a : ℚ)) (y := (b : ℚ))
    haa hbb
  have hmulNat : (a : ℚ) * (b : ℚ) = ((a * b : ℕ) : ℚ) := by norm_num
  rw [hmulNat, hxrep, rationalTrace_nat_eq_two_of_two_eq_two hF htwo a ha1,
    rationalTrace_nat_eq_two_of_two_eq_two hF htwo b hb1,
    rationalTrace_nat_eq_two_of_two_eq_two hF htwo (a * b)
      (by exact Nat.mul_pos hapos hbpos)] at hd
  linarith

/-! ## The assembled real character -/

/-- The real sign character, extended by zero at zero. -/
def rationalSignCharacter (x : ℚ) : ℝ :=
  if x = 0 then 0 else if 0 < x then 1 else -1

theorem rationalSignCharacter_one : rationalSignCharacter 1 = 1 := by
  simp [rationalSignCharacter]

theorem rationalSignCharacter_mul (x y : ℚ) :
    rationalSignCharacter (x * y) =
      rationalSignCharacter x * rationalSignCharacter y := by
  by_cases hx : x = 0
  · subst x
    simp [rationalSignCharacter]
  by_cases hy : y = 0
  · subst y
    simp [rationalSignCharacter]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · have hxypos : 0 < x * y := mul_pos_of_neg_of_neg hxneg hyneg
      simp [rationalSignCharacter, hx, hy, hxy, hxneg.not_gt, hyneg.not_gt,
        hxypos]
    · have hxyneg : x * y < 0 := mul_neg_of_neg_of_pos hxneg hypos
      simp [rationalSignCharacter, hx, hy, hxy, hxneg.not_gt, hypos,
        hxyneg.not_gt]
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · have hxyneg : x * y < 0 := mul_neg_of_pos_of_neg hxpos hyneg
      simp [rationalSignCharacter, hx, hy, hxy, hxpos, hyneg.not_gt,
        hxyneg.not_gt]
    · have hxypos : 0 < x * y := mul_pos hxpos hypos
      simp [rationalSignCharacter, hx, hy, hxy, hxpos, hypos, hxypos]

theorem rationalSignCharacter_recip {x : ℚ} (hx : x ≠ 0) :
    rationalSignCharacter x⁻¹ = (rationalSignCharacter x)⁻¹ := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hinvneg : x⁻¹ < 0 := inv_lt_zero.mpr hxneg
    simp [rationalSignCharacter, hx, inv_ne_zero hx, hxneg.not_gt,
      hinvneg.not_gt]
  · have hinvpos : 0 < x⁻¹ := inv_pos.mpr hxpos
    simp [rationalSignCharacter, hx, inv_ne_zero hx, hxpos, hinvpos]

theorem rationalSignCharacter_nonzero {x : ℚ} (hx : x ≠ 0) :
    rationalSignCharacter x ≠ 0 := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · simp [rationalSignCharacter, hx, hxneg.not_gt]
  · simp [rationalSignCharacter, hx, hxpos]

theorem rationalSignCharacter_of_pos {x : ℚ} (hx : 0 < x) :
    rationalSignCharacter x = 1 := by
  simp [rationalSignCharacter, ne_of_gt hx, hx]

/-- The real character extracted from the doubled trace. The degenerate anchor
is the sign character; otherwise the generalized linear extraction is used. -/
noncomputable def realCharacterCandidate
    (F : RatioOrbit → RatioOrbit) (q : RatioOrbit) : ℝ :=
  if rationalTrace F 2 = 2 then
    rationalSignCharacter q.toRat
  else if q.toRat = 0 then
    0
  else
    nontrivialCharacterValue F q.toRat

theorem nontrivialCharacterValue_nonzero
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (hnontrivial : rationalTrace F 2 ≠ 2)
    {x : ℚ} (hx : x ≠ 0) :
    nontrivialCharacterValue F x ≠ 0 := by
  have hmul := nontrivialCharacterValue_mul hF hnontrivial hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, nontrivialCharacterValue_one hF hnontrivial] at hmul
  intro hz
  rw [hz, zero_mul] at hmul
  norm_num at hmul

theorem nontrivialCharacterValue_recip
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (hnontrivial : rationalTrace F 2 ≠ 2)
    {x : ℚ} (hx : x ≠ 0) :
    nontrivialCharacterValue F x⁻¹ =
      (nontrivialCharacterValue F x)⁻¹ := by
  have hmul := nontrivialCharacterValue_mul hF hnontrivial hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, nontrivialCharacterValue_one hF hnontrivial] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

theorem nontrivialCharacterValue_trace
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (hnontrivial : rationalTrace F 2 ≠ 2)
    {x : ℚ} (hx : x ≠ 0) :
    nontrivialCharacterValue F x +
        (nontrivialCharacterValue F x)⁻¹ =
      rationalTrace F x := by
  have hsum := nontrivialCharacterValue_recip_sum hF hnontrivial hx
  rw [nontrivialCharacterValue_recip hF hnontrivial hx] at hsum
  linarith

theorem nontrivialCharacterValue_two
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (hnontrivial : rationalTrace F 2 ≠ 2) :
    nontrivialCharacterValue F 2 = anchorRoot F := by
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  have hd := rationalTrace_dAlembert hF htwo htwo
  have hprod : (2 : ℚ) * 2 = 4 := by norm_num
  have hquot : (2 : ℚ) / 2 = 1 := by norm_num
  rw [hprod, hquot, rationalTrace_one hF] at hd
  have hfour :
      rationalTrace F 4 = rationalTrace F 2 ^ 2 - 2 := by
    nlinarith [hd]
  have hr0 := anchorRoot_ne_zero hF
  have hrden := anchorRoot_sq_sub_one_ne_zero hF hnontrivial
  have hA : rationalTrace F 2 =
      (anchorRoot F ^ 2 + 1) / anchorRoot F := by
    rw [← anchorRoot_add_inv hF, eq_div_iff hr0]
    field_simp [hr0]
  rw [nontrivialCharacterValue, linearExtraction,
    show (2 : ℚ) * 2 = 4 by norm_num, hfour, hA]
  field_simp [hr0, hrden]
  ring

theorem nontrivialCharacterValue_pow
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (hnontrivial : rationalTrace F 2 ≠ 2)
    {x : ℚ} (hx : x ≠ 0) :
    ∀ k : ℕ,
      nontrivialCharacterValue F (x ^ k) =
        nontrivialCharacterValue F x ^ k := by
  intro k
  induction k with
  | zero =>
      simpa using nontrivialCharacterValue_one hF hnontrivial
  | succ k ih =>
      rw [pow_succ, nontrivialCharacterValue_mul hF hnontrivial
        (pow_ne_zero k hx) hx, ih, pow_succ]

theorem nontrivialCharacterValue_pos_on_nat
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (hnontrivial : rationalTrace F 2 ≠ 2)
    {n : ℕ} (hn : 1 ≤ n) :
    0 < nontrivialCharacterValue F n := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hne := nontrivialCharacterValue_nonzero hF hnontrivial hnq
  have htrace := nontrivialCharacterValue_trace hF hnontrivial hnq
  have hge := rationalTrace_nat_ge_two hF hn
  by_contra hpos
  have hle : nontrivialCharacterValue F n ≤ 0 := le_of_not_gt hpos
  have hneg : nontrivialCharacterValue F n < 0 :=
    lt_of_le_of_ne hle hne
  have hinvneg : (nontrivialCharacterValue F n)⁻¹ < 0 :=
    inv_lt_zero.mpr hneg
  linarith

private theorem exists_pow_trace_decrease
    {u r : ℝ} (hu : 0 < u) (hu1 : u < 1) (hr : 1 < r) :
    ∃ k : ℕ,
      r * u ^ k + (r * u ^ k)⁻¹ < u ^ k + (u ^ k)⁻¹ := by
  have hu2pos : 0 < u ^ 2 := sq_pos_of_pos hu
  have hu2lt : u ^ 2 < 1 := by nlinarith
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have heps : 0 < r⁻¹ := inv_pos.mpr hrpos
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one heps hu2lt
  refine ⟨k, ?_⟩
  let v := u ^ k
  have hv : 0 < v := pow_pos hu k
  have hsmall : v ^ 2 < r⁻¹ := by
    have hid : v ^ 2 = (u ^ 2) ^ k := by
      simp only [v, ← pow_mul]
      rw [Nat.mul_comm]
    rw [hid]
    exact hk
  have hrvlt : r * v ^ 2 < 1 := by
    have hm := mul_lt_mul_of_pos_left hsmall hrpos
    rw [mul_inv_cancel₀ (ne_of_gt hrpos)] at hm
    exact hm
  have hid :
      (r * v) * (r * v + (r * v)⁻¹ - (v + v⁻¹)) =
        (r - 1) * (r * v ^ 2 - 1) := by
    field_simp [ne_of_gt hrpos, ne_of_gt hv]
    ring
  have hneg :
      (r - 1) * (r * v ^ 2 - 1) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hdiff :
      r * v + (r * v)⁻¹ - (v + v⁻¹) < 0 := by
    have hrvpos : 0 < r * v := mul_pos hrpos hv
    have hscaled :
        (r * v) * (r * v + (r * v)⁻¹ - (v + v⁻¹)) < 0 := by
      rw [hid]
      exact hneg
    nlinarith
  change r * v + (r * v)⁻¹ < v + v⁻¹
  linarith

theorem nontrivialCharacterValue_nat_trace_mono
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (hnontrivial : rationalTrace F 2 ≠ 2)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    nontrivialCharacterValue F m +
        (nontrivialCharacterValue F m)⁻¹ ≤
      nontrivialCharacterValue F n +
        (nontrivialCharacterValue F n)⁻¹ := by
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hnq : (n : ℚ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hmtrace := nontrivialCharacterValue_trace hF hnontrivial hmq
  have hntrace := nontrivialCharacterValue_trace hF hnontrivial hnq
  have hmono := rationalTrace_nat_mono hF hm hmn
  rw [← hmtrace, ← hntrace] at hmono
  exact hmono

theorem nontrivialCharacterValue_principal_on_nat
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (hnontrivial : rationalTrace F 2 ≠ 2) :
    ∀ n : ℕ, 1 ≤ n → 1 ≤ nontrivialCharacterValue F n := by
  intro n hn
  let u := nontrivialCharacterValue F n
  let r := anchorRoot F
  have hu : 0 < u := nontrivialCharacterValue_pos_on_nat hF hnontrivial hn
  have hr : 1 < r := anchorRoot_gt_one hF hnontrivial
  by_contra hprincipal
  have hu1 : u < 1 := lt_of_not_ge hprincipal
  obtain ⟨k, hdecrease⟩ := exists_pow_trace_decrease hu hu1 hr
  have hnpowPos : 0 < n ^ k := pow_pos (by omega) k
  have hnpowOne : 1 ≤ n ^ k := hnpowPos
  have hnatMono :=
    nontrivialCharacterValue_nat_trace_mono hF hnontrivial
      hnpowOne (by omega : n ^ k ≤ 2 * n ^ k)
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpowq : (n : ℚ) ^ k ≠ 0 := pow_ne_zero k hnq
  have hcharPow := nontrivialCharacterValue_pow hF hnontrivial hnq k
  have hcharTwoPow :=
    nontrivialCharacterValue_mul hF hnontrivial
      (by norm_num : (2 : ℚ) ≠ 0) hpowq
  have hcastPow : (((n ^ k : ℕ) : ℚ)) = (n : ℚ) ^ k := by norm_num
  have hcastTwoPow :
      (((2 * n ^ k : ℕ) : ℚ)) = (2 : ℚ) * (n : ℚ) ^ k := by norm_num
  rw [hcastPow, hcastTwoPow, hcharPow, hcharTwoPow,
    nontrivialCharacterValue_two hF hnontrivial, hcharPow] at hnatMono
  change u ^ k + (u ^ k)⁻¹ ≤
    r * u ^ k + (r * u ^ k)⁻¹ at hnatMono
  exact (not_lt_of_ge hnatMono) hdecrease

theorem realCharacterCandidate_unit
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F) :
    realCharacterCandidate F RatioOrbit.one = 1 := by
  by_cases ht : rationalTrace F 2 = 2
  · simp [realCharacterCandidate, ht, RatioOrbit.one_toRat,
      rationalSignCharacter_one]
  · simp [realCharacterCandidate, ht, RatioOrbit.one_toRat,
      nontrivialCharacterValue_one hF ht]

theorem realCharacterCandidate_mul
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    {x y : RatioOrbit} (hx : x.toRat ≠ 0) (hy : y.toRat ≠ 0) :
    realCharacterCandidate F (RatioOrbit.mul x y) =
      realCharacterCandidate F x * realCharacterCandidate F y := by
  have hxy : x.toRat * y.toRat ≠ 0 := mul_ne_zero hx hy
  by_cases ht : rationalTrace F 2 = 2
  · simp [realCharacterCandidate, ht, RatioOrbit.mul_toRat,
      rationalSignCharacter_mul]
  · simp only [realCharacterCandidate, ht, if_false,
      RatioOrbit.mul_toRat, hx, hy, hxy]
    exact nontrivialCharacterValue_mul hF ht hx hy

theorem realCharacterCandidate_recip
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    {x : RatioOrbit} (hx : x.toRat ≠ 0) :
    realCharacterCandidate F (RatioOrbit.recip x) =
      (realCharacterCandidate F x)⁻¹ := by
  have hinv : x.toRat⁻¹ ≠ 0 := inv_ne_zero hx
  by_cases ht : rationalTrace F 2 = 2
  · simp [realCharacterCandidate, ht, RatioOrbit.recip_toRat,
      rationalSignCharacter_recip hx]
  · simp only [realCharacterCandidate, ht, if_false,
      RatioOrbit.recip_toRat, hx, hinv]
    exact nontrivialCharacterValue_recip hF ht hx

theorem realCharacterCandidate_nonzero
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    {x : RatioOrbit} (hx : x.toRat ≠ 0) :
    realCharacterCandidate F x ≠ 0 := by
  by_cases ht : rationalTrace F 2 = 2
  · simp only [realCharacterCandidate, ht, if_true]
    exact rationalSignCharacter_nonzero hx
  · simp only [realCharacterCandidate, ht, if_false, hx]
    exact nontrivialCharacterValue_nonzero hF ht hx

theorem realCharacterCandidate_principal_on_pos_int
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F) :
    ∀ n : ℕ, 1 ≤ n → 1 ≤ realCharacterCandidate F (natOrbit n) := by
  intro n hn
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnne : (n : ℚ) ≠ 0 := ne_of_gt hnpos
  by_cases ht : rationalTrace F 2 = 2
  · rw [realCharacterCandidate, if_pos ht, natOrbit_toRat,
      rationalSignCharacter_of_pos hnpos]
  · rw [realCharacterCandidate, if_neg ht, natOrbit_toRat, if_neg hnne]
    exact nontrivialCharacterValue_principal_on_nat hF ht n hn

theorem realCharacterCandidate_is_character
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F) :
    PRCRealRatioCharacter (realCharacterCandidate F) where
  unit := realCharacterCandidate_unit hF
  multiplicative := fun _ _ hx hy => realCharacterCandidate_mul hF hx hy
  reciprocal := fun _ hx => realCharacterCandidate_recip hF hx
  nonzero := fun _ hx => realCharacterCandidate_nonzero hF hx
  principal_on_pos_int := realCharacterCandidate_principal_on_pos_int hF

theorem realCharacterCandidate_trace_of_pos
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    {q : RatioOrbit} (hq : 0 < q.toRat) :
    realCharacterCandidate F q + (realCharacterCandidate F q)⁻¹ =
      traceDisplay F q := by
  have hqne : q.toRat ≠ 0 := ne_of_gt hq
  have hdisplay := rationalTrace_eq_traceDisplay hF q
  by_cases ht : rationalTrace F 2 = 2
  · have htrivial := rationalTrace_pos_eq_two_of_two_eq_two hF ht hq
    rw [htrivial] at hdisplay
    rw [realCharacterCandidate, if_pos ht,
      rationalSignCharacter_of_pos hq, ← hdisplay]
    norm_num
  · have htrace := nontrivialCharacterValue_trace hF ht hqne
    rw [realCharacterCandidate, if_neg ht, if_neg hqne, htrace, hdisplay]

theorem realCharacterCandidate_cost_agrees
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F)
    (q : RatioOrbit) (hq : 0 < q.toRat) :
    ((F q).toRat : ℝ) =
      costFromRealCharacter (realCharacterCandidate F) q := by
  rw [costFromRealCharacter, realCharacterCandidate_trace_of_pos hF hq]
  simp only [traceDisplay, nativeCostDoubledTrace, doubledTraceValue,
    RatioOrbit.mul_toRat, RatioOrbit.add_toRat, two_toRat,
    RatioOrbit.one_toRat]
  push_cast
  ring

theorem realCharacterCandidate_small_traces_rational
    {F : RatioOrbit → RatioOrbit} (hF : SansAnchorHypotheses F) :
    ∀ n : ℕ, 2 ≤ n → n ≤ 5 →
      ∃ t : ℚ,
        realCharacterCandidate F (natOrbit n) +
            (realCharacterCandidate F (natOrbit n))⁻¹ =
          (t : ℝ) := by
  intro n hn _
  refine ⟨(nativeCostDoubledTrace F (natOrbit n)).toRat, ?_⟩
  exact realCharacterCandidate_trace_of_pos hF
    (by rw [natOrbit_toRat]; exact_mod_cast (show 0 < n by omega))

/-- The anchor-free doubled trace always factors through a real-valued
principal character. -/
theorem SansAnchorRealCharacterFactorizationTarget_proved :
    SansAnchorRealCharacterFactorizationTarget := by
  intro F hF
  exact ⟨realCharacterCandidate F, realCharacterCandidate_is_character hF,
    realCharacterCandidate_cost_agrees hF,
    realCharacterCandidate_small_traces_rational hF⟩

#print axioms doubledTrace_dAlembert_of_rcl
#print axioms doubledTrace_dAlembert_of_sansAnchor
#print axioms SansAnchorRealCharacterFactorizationTarget_proved

end RealCharacterFactorization
end Cost
end IndisputableMonolith
