/-
  PrimitiveRecognitionCalculus/PRCNativeCostStructuralLedger.lean

  Round-trip source:
    plans/Delta_JCost_FreeSide_Program_Plan_20260724.html

  The judge for everything below is `lake`. There is no preregistered empirical
  gate here and none is claimed: these are kernel-checked theorems, and the
  countermodels are exhibited functions, not measurements.

  Rounds 4 to 6 of P-delta-jfree: replace the free-side calibration ledger by a
  STRUCTURAL ledger. Rounds 1 to 3 proved that the slim ledger forces the
  canonical cost on `RatioOrbit` and that it is field-by-field minimal, but four
  of its eight fields are of the form "F agrees with J here", one of them over
  the infinite family of prime pairs. This module removes the two substantive
  ones and replaces them with statements about what a cost IS:

  * SIGN REVERSAL (round 4). `PRCNativeCostSignReversing`: reversing the
    orientation of a distinction negates its doubled trace, i.e. the display
    identity `F(-q) = -F(q) - 2`. This is ledger antisymmetry (a debit read
    backwards is a credit). Applied at the unit it DERIVES the signed-unit
    calibration, so `signed_unit` leaves the ledger.

  * MONOTONICITY (round 5). `PRCNativeCostMonotone`: on positive integer
    orbits, a larger imbalance costs at least as much. This replaces the whole
    prime-pair product family. The mathematics is Erdős 1946 (a monotone
    completely additive arithmetic function is `c log n`), and in the
    completely multiplicative case the proof is a squeeze on integer exponents
    with no analysis in it: if `2^m ≤ a^n` then monotonicity transports the
    inequality to the character values, so the character value at `a` cuts the
    powers of two exactly where `a` does, and two positive rationals with the
    same cut are equal. `cut_pins` below is that argument, stated with no
    logarithm, no limit, and no real number anywhere.

  What survives is `two_calibrated`, and round 6 shows that what survives is
  exactly a UNIT GAUGE and not a hidden assumption of the answer:

  * `structural_gauge_rigidity`: two inhabitants of the anchor-free structural
    ledger that agree at the single orbit `2` agree on every orbit.
  * `cubeGeneratedNativeCost`: the cost `J(q³)` inhabits the anchor-free
    structural ledger and fails the anchor, so the gauge orbit is genuinely
    inhabited and the anchor is a real choice rather than a redundancy. (The
    Liouville and two-adic impostors of round 3 are NOT monotone, so they do
    not witness this; the odd power family is what is left.)

  Read together: on the countable carrier the FORM of the cost is forced by
  arithmetic (reciprocity, normalization invariance, the composition law,
  unit-zero, sign reversal, monotonicity, and the zero-orbit convention), and
  the only residual freedom is the size of the unit, fixed by one anchor. That
  is the same stratification the continuous theorem delivers, obtained without
  buying continuity, smoothness, or the completed line.

  Scope: reads the round-1/2/3 modules and the parent. It edits none of them.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCNativeCostMinimalityCertificate

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace PRCJCost

/-! ## Part 0: the cost display on rationals

Everything below is stated on displays (`RatioOrbit.toRat`), which is legitimate
because `crossEq a b ↔ a.toRat = b.toRat`. -/

/-- Read a cross-equivalence as an equality of displays. -/
theorem crossDisp {a b : RatioOrbit} (h : RatioOrbit.crossEq a b) :
    a.toRat = b.toRat := (RatioOrbit.crossEq_iff_toRat_eq a b).mp h

/-- Read an equality of displays as a cross-equivalence. -/
theorem dispCross {a b : RatioOrbit} (h : a.toRat = b.toRat) :
    RatioOrbit.crossEq a b := (RatioOrbit.crossEq_iff_toRat_eq a b).mpr h

/-- The J display on a rational. -/
def jq (t : ℚ) : ℚ := (t + t⁻¹) / 2 - 1

@[simp] theorem jq_onRatioOrbit (q : RatioOrbit) :
    (onRatioOrbit q).toRat = jq q.toRat := onRatioOrbit_toRat q

theorem costFromCharacter_jq (χ : RatioOrbit → RatioOrbit) (q : RatioOrbit) :
    (costFromCharacter χ q).toRat = jq ((χ q).toRat) := costFromCharacter_toRat χ q

@[simp] theorem jq_one : jq 1 = 0 := by norm_num [jq]

@[simp] theorem jq_zero : jq 0 = -1 := by norm_num [jq]

theorem jq_closed {t : ℚ} (ht : t ≠ 0) : jq t = (t - 1) ^ 2 / (2 * t) := by
  unfold jq
  field_simp
  ring

theorem jq_nonneg {t : ℚ} (ht : 0 < t) : 0 ≤ jq t := by
  rw [jq_closed (ne_of_gt ht)]
  positivity

theorem jq_lt_zero {t : ℚ} (ht : t < 0) : jq t < 0 := by
  rw [jq_closed (ne_of_lt ht)]
  apply div_neg_of_pos_of_neg
  · exact pow_two_pos_of_ne_zero (by linarith)
  · linarith

/-- The unit is the only zero-cost orbit. -/
theorem jq_eq_zero {t : ℚ} (ht : t ≠ 0) (h : jq t = 0) : t = 1 := by
  rw [jq_closed ht] at h
  rcases div_eq_zero_iff.mp h with h1 | h1
  · have : t - 1 = 0 := by
      have h2 : (t - 1) ^ 2 = 0 := h1
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linarith
  · exact absurd h1 (by simpa using ht)

/-- Sign reversal on displays: reversing a distinction negates its doubled
trace. -/
theorem jq_neg (t : ℚ) : jq (-t) = -jq t - 2 := by
  simp only [jq, inv_neg]
  ring

/-- `jq` is reciprocal-symmetric. -/
theorem jq_inv (t : ℚ) : jq t⁻¹ = jq t := by
  rcases eq_or_ne t 0 with h | h
  · simp [h]
  · unfold jq
    rw [inv_inv]
    ring

theorem jq_mono {s t : ℚ} (hs : 1 ≤ s) (hst : s ≤ t) : jq s ≤ jq t := by
  have hs0 : (0:ℚ) < s := lt_of_lt_of_le zero_lt_one hs
  have ht0 : (0:ℚ) < t := lt_of_lt_of_le hs0 hst
  have hkey : t + t⁻¹ - (s + s⁻¹) = (t - s) * (s * t - 1) / (s * t) := by
    field_simp
    ring
  have hnum : 0 ≤ (t - s) * (s * t - 1) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have : 0 ≤ t + t⁻¹ - (s + s⁻¹) := by
    rw [hkey]
    exact div_nonneg hnum (by positivity)
  unfold jq
  linarith

theorem jq_strictMono {s t : ℚ} (hs : 1 ≤ s) (hst : s < t) : jq s < jq t := by
  have hs0 : (0:ℚ) < s := lt_of_lt_of_le zero_lt_one hs
  have ht0 : (0:ℚ) < t := lt_trans hs0 hst
  have hst1 : 1 < s * t := by nlinarith
  have hkey : t + t⁻¹ - (s + s⁻¹) = (t - s) * (s * t - 1) / (s * t) := by
    field_simp
    ring
  have hnum : 0 < (t - s) * (s * t - 1) := by
    apply mul_pos (by linarith)
    linarith
  have : 0 < t + t⁻¹ - (s + s⁻¹) := by
    rw [hkey]
    exact div_pos hnum (by positivity)
  unfold jq
  linarith

/-- Order reflection: on the region at or above the unit, `jq` sees the order. -/
theorem jq_le_reflect {s t : ℚ} (_hs : 1 ≤ s) (ht : 1 ≤ t) (h : jq s ≤ jq t) :
    s ≤ t := by
  by_contra hc
  push_neg at hc
  exact absurd h (not_le.mpr (jq_strictMono ht hc))

/-- The composition law, on displays. `jq` satisfies it for every nonzero pair,
which is what makes the whole power family available to the gauge orbit. -/
theorem jq_rcl {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    jq (x * y) + jq (x / y) = 2 * (jq x * jq y) + 2 * jq x + 2 * jq y := by
  simp only [jq]
  field_simp
  ring

/-- `jq` at a value strictly between the unit and `2` is below `jq 2`. -/

theorem jq_two : jq 2 = 1 / 4 := by norm_num [jq]

/-- The two solutions of `jq x = jq 2`. -/
theorem jq_eq_two_cases {x : ℚ} (hx : x ≠ 0) (h : jq x = jq 2) :
    x = 2 ∨ x = 2⁻¹ := by
  rw [jq_two] at h
  unfold jq at h
  have h4 : 4 * (x + x⁻¹) - 8 = 2 := by
    field_simp at h ⊢
    linarith
  have hquad : (x - 2) * (2 * x - 1) = 0 := by
    have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
    field_simp at h4
    nlinarith [h4, hxx]
  rcases mul_eq_zero.mp hquad with h1 | h1
  · left; linarith
  · right
    have : x = 1 / 2 := by linarith
    rw [this]; norm_num

/-! ## Part 1: positive integer orbits -/

/-- The orbit whose display is the natural number `n`. -/
def natOrbit (n : ℕ) : RatioOrbit := ratioOrbitOfRat (n : ℚ)

@[simp] theorem natOrbit_toRat (n : ℕ) : (natOrbit n).toRat = (n : ℚ) :=
  ratioOrbitOfRat_toRat _

/-- An orbit displaying a positive integer. -/
def IsPosIntOrbit (q : RatioOrbit) : Prop := ∃ n : ℕ, 1 ≤ n ∧ q.toRat = (n : ℚ)

theorem natOrbit_isPosInt {n : ℕ} (hn : 1 ≤ n) : IsPosIntOrbit (natOrbit n) :=
  ⟨n, hn, natOrbit_toRat n⟩

theorem two_isPosInt : IsPosIntOrbit two := ⟨2, by norm_num, by simp [two_toRat]⟩

theorem primeDirection_isPosInt {p : DistinctionNat}
    (hp : DistinctionNat.primeOrbit p) : IsPosIntOrbit (primeDirection p hp) := by
  refine ⟨p.toNat, ?_, by rw [primeDirection_toRat]⟩
  have h := primeDirection_toRat_ne_zero p hp
  rw [primeDirection_toRat] at h
  exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h)

/-! ## Part 2: the two structural axioms

Neither mentions the canonical cost. The first says a cost read backwards is
the negated cost (ledger antisymmetry); the second says a bigger imbalance
costs at least as much. -/

/-- **Sign reversal.** Reversing the orientation of a distinction negates its
doubled trace: with `T = 2(F+1)`, this is `T(-q) = -T(q)`, written on displays
as `F(-q) = -F(q) - 2`. -/
def PRCNativeCostSignReversing (F : RatioOrbit → RatioOrbit) : Prop :=
  ∀ q r : RatioOrbit, r.toRat = -q.toRat →
    (F r).toRat = -(F q).toRat - 2

/-- **Monotonicity.** On positive integer orbits, cost does not decrease as the
imbalance grows. -/
def PRCNativeCostMonotone (F : RatioOrbit → RatioOrbit) : Prop :=
  ∀ a b : RatioOrbit, IsPosIntOrbit a → IsPosIntOrbit b →
    a.toRat ≤ b.toRat → (F a).toRat ≤ (F b).toRat

/-- **Positivity.** Recognizing a difference never pays; this is DERIVED below,
not assumed. -/
def PRCNativeCostPositive (F : RatioOrbit → RatioOrbit) : Prop :=
  ∀ q : RatioOrbit, 0 < q.toRat → 0 ≤ (F q).toRat

/-! ## Part 3: the canonical cost satisfies both structural axioms -/

theorem canonicalSelectedNativeCost_jq (q : RatioOrbit) :
    (canonicalSelectedNativeCost q).toRat = jq q.toRat :=
  canonicalSelectedNativeCost_toRat q

theorem canonicalSelectedNativeCost_signReversing :
    PRCNativeCostSignReversing canonicalSelectedNativeCost := by
  intro q r hr
  rw [canonicalSelectedNativeCost_jq, canonicalSelectedNativeCost_jq, hr]
  rcases eq_or_ne q.toRat 0 with h | h
  · rw [h]
    norm_num
  · simp only [jq, inv_neg]
    ring

theorem canonicalSelectedNativeCost_monotone :
    PRCNativeCostMonotone canonicalSelectedNativeCost := by
  rintro a b ⟨m, hm, ham⟩ ⟨n, hn, hbn⟩ hab
  rw [canonicalSelectedNativeCost_jq, canonicalSelectedNativeCost_jq]
  apply jq_mono
  · rw [ham]; exact_mod_cast hm
  · exact hab

theorem canonicalSelectedNativeCost_positive :
    PRCNativeCostPositive canonicalSelectedNativeCost := by
  intro q hq
  rw [canonicalSelectedNativeCost_jq]
  exact jq_nonneg hq

/-! ## Part 4 (ROUND 4): sign reversal derives the signed-unit calibration -/

/-- **The signed-unit field is not an assumption.** Ledger antisymmetry applied
at the unit produces it. -/
theorem signReversing_forces_signed_unit {F : RatioOrbit → RatioOrbit}
    (hunit : F RatioOrbit.one = RatioOrbit.zero)
    (hsign : PRCNativeCostSignReversing F) :
    PRCNativeCostSignedUnitCalibrated F := by
  have hneg : negativeOneRatio.toRat = -(RatioOrbit.one.toRat) := by
    rw [negativeOneRatio_toRat, RatioOrbit.one_toRat]
  have h := hsign RatioOrbit.one negativeOneRatio hneg
  rw [PRCNativeCostSignedUnitCalibrated, RatioOrbit.crossEq_iff_toRat_eq,
    jq_onRatioOrbit, negativeOneRatio_toRat, h, hunit, RatioOrbit.zero_toRat]
  norm_num [jq]

/-- The round-4 class: base plus prime pairs plus SIGN REVERSAL plus the zero
orbit. Compared with the round-2 slim ledger, the signed-unit calibration is
gone and an intrinsic antisymmetry axiom stands in its place. -/
structure PRCSignReversingNativeCostHypotheses
    (F : RatioOrbit → RatioOrbit) : Prop where
  strengthened : PRCStrengthenedNativeCostHypotheses F
  sign_reversing : PRCNativeCostSignReversing F
  zero_calibrated : PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F)

def PRCSignReversingNativeCostUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCSignReversingNativeCostHypotheses F →
      ∀ q : RatioOrbit, RatioOrbit.crossEq (F q) (onRatioOrbit q)

/-- Round 4 terminal: the sign-reversing ledger forces the canonical cost. -/
theorem PRCSignReversingNativeCostUniquenessTarget_proved :
    PRCSignReversingNativeCostUniquenessTarget := by
  intro F hF q
  refine PRCZeroCalibratedSignedStrengthenedNativeCostUniquenessTarget_proved F ?_ q
  exact
    { signed_strengthened :=
        { strengthened := hF.strengthened
          signed_unit :=
            signReversing_forces_signed_unit
              hF.strengthened.native.unit_zero hF.sign_reversing }
      zero_calibrated := hF.zero_calibrated }

/-- Non-vacuity of the round-4 class. -/
theorem canonicalSelectedNativeCost_signReversing_hypotheses :
    PRCSignReversingNativeCostHypotheses canonicalSelectedNativeCost :=
  { strengthened :=
      canonicalSelectedNativeCost_slim_hypotheses.signed_strengthened.strengthened
    sign_reversing := canonicalSelectedNativeCost_signReversing
    zero_calibrated := canonicalSelectedNativeCost_slim_hypotheses.zero_calibrated }

/-- The exchange is real in both directions: the round-4 class and the round-2
slim ledger carve out the same costs. Sign reversal is therefore a strictly
better-behaved stand-in for the signed-unit calibration, not a weakening. -/
theorem signReversing_class_forces_slim (F : RatioOrbit → RatioOrbit)
    (hF : PRCSignReversingNativeCostHypotheses F) :
    PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses F :=
  { signed_strengthened :=
      { strengthened := hF.strengthened
        signed_unit :=
          signReversing_forces_signed_unit
            hF.strengthened.native.unit_zero hF.sign_reversing }
    zero_calibrated := hF.zero_calibrated }

/-- The absolute-value cost is the round-3 witness that the signed-unit field
was load bearing; it is excluded by sign reversal directly, with no reference
to the canonical cost's value anywhere. -/
theorem absValueGeneratedNativeCost_not_signReversing :
    ¬ PRCNativeCostSignReversing absValueGeneratedNativeCost := by
  intro h
  have hneg : negativeOneRatio.toRat = -(RatioOrbit.one.toRat) := by
    rw [negativeOneRatio_toRat, RatioOrbit.one_toRat]
  have hval := h RatioOrbit.one negativeOneRatio hneg
  have hone : (absValueGeneratedNativeCost RatioOrbit.one).toRat = 0 := by
    unfold absValueGeneratedNativeCost
    simp
  have hminus : (absValueGeneratedNativeCost negativeOneRatio).toRat = 0 := by
    have := absValueGeneratedNativeCost_negative_one_zero
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.zero_toRat] at this
    exact this
  rw [hminus, hone] at hval
  norm_num at hval

/-! ## Part 5: the squeeze

Erdős's 1946 monotonicity rigidity, in the completely multiplicative case,
written with no logarithm and no real number. The content is that a positive
rational is determined by where its powers fall among the powers of a fixed
base: two rationals with the same cut are equal. -/

/-- Archimedean growth for rational powers, from Bernoulli's inequality. -/
private lemma exists_pow_gt_rat {b : ℚ} (hb : 1 < b) (c : ℚ) :
    ∃ n : ℕ, c < b ^ n := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((c - 1) / (b - 1))
  refine ⟨n, ?_⟩
  have hb1 : (0:ℚ) < b - 1 := by linarith
  have hbern : 1 + (n : ℚ) * (b - 1) ≤ (1 + (b - 1)) ^ n :=
    one_add_mul_le_pow (by linarith) n
  have hlt : c - 1 < (n : ℚ) * (b - 1) := by
    rw [div_lt_iff₀ hb1] at hn
    exact hn
  have hsimp : (1 : ℚ) + (b - 1) = b := by ring
  rw [hsimp] at hbern
  linarith

/-- One side of the cut squeeze. -/
private lemma cut_pins_aux {u v α γ γ' : ℚ}
    (hα : 1 < α) (hγ : 1 ≤ γ) (hlt : γ < γ')
    (hf : ∀ m n : ℕ, u ^ m ≤ v ^ n → α ^ m ≤ γ ^ n)
    (hb' : ∀ m n : ℕ, v ^ n ≤ u ^ m → γ' ^ n ≤ α ^ m) :
    False := by
  classical
  have hγ0 : (0:ℚ) < γ := lt_of_lt_of_le zero_lt_one hγ
  have hα0 : (0:ℚ) < α := lt_trans zero_lt_one hα
  have hratio : 1 < γ' / γ := (one_lt_div hγ0).mpr hlt
  obtain ⟨n, hn⟩ := exists_pow_gt_rat hratio α
  have hγn : (0:ℚ) < γ ^ n := pow_pos hγ0 n
  have hkey : α * γ ^ n < γ' ^ n := by
    rw [div_pow, lt_div_iff₀ hγn] at hn
    linarith
  have hex : ∃ m : ℕ, γ ^ n < α ^ m := exists_pow_gt_rat hα (γ ^ n)
  set m := Nat.find hex with hmdef
  have hmspec : γ ^ n < α ^ m := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hmspec
    exact absurd (one_le_pow₀ hγ) (not_le.mpr hmspec)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hmin : ¬ (γ ^ n < α ^ j) := Nat.find_min hex (by omega)
  push_neg at hmin
  have hαm : α ^ m ≤ α * γ ^ n := by
    calc α ^ m = α ^ j * α := by rw [hj, pow_succ]
      _ ≤ γ ^ n * α := mul_le_mul_of_nonneg_right hmin (le_of_lt hα0)
      _ = α * γ ^ n := by ring
  have hlt2 : α ^ m < γ' ^ n := lt_of_le_of_lt hαm hkey
  rcases le_total (u ^ m) (v ^ n) with h | h
  · exact absurd (hf m n h) (not_le.mpr hmspec)
  · exact absurd (hb' m n h) (not_le.mpr hlt2)

/-- **The cut lemma.** Two rationals at or above the unit that transport the
same integer-exponent comparisons against a common reference cut are equal.
This is the whole of the Erdős squeeze, and there is no analysis in it. -/
theorem cut_pins {u v α γ γ' : ℚ}
    (hα : 1 < α) (hγ : 1 ≤ γ) (hγ' : 1 ≤ γ')
    (hf  : ∀ m n : ℕ, u ^ m ≤ v ^ n → α ^ m ≤ γ ^ n)
    (hb  : ∀ m n : ℕ, v ^ n ≤ u ^ m → γ ^ n ≤ α ^ m)
    (hf' : ∀ m n : ℕ, u ^ m ≤ v ^ n → α ^ m ≤ γ' ^ n)
    (hb' : ∀ m n : ℕ, v ^ n ≤ u ^ m → γ' ^ n ≤ α ^ m) :
    γ = γ' := by
  rcases lt_trichotomy γ γ' with h | h | h
  · exact (cut_pins_aux hα hγ h hf hb').elim
  · exact h
  · exact (cut_pins_aux hα hγ' h hf' hb).elim

/-- The arithmetic data a monotone character leaves on the positive integers:
completely multiplicative, nowhere zero, with nondecreasing cost. -/
structure MonoMult (h : ℕ → ℚ) : Prop where
  ne : ∀ n : ℕ, 1 ≤ n → h n ≠ 0
  one : h 1 = 1
  mul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → h (m * n) = h m * h n
  mono : ∀ m n : ℕ, 1 ≤ m → m ≤ n → jq (h m) ≤ jq (h n)

namespace MonoMult

theorem pow {h : ℕ → ℚ} (H : MonoMult h) (a k : ℕ) (ha : 1 ≤ a) :
    h (a ^ k) = (h a) ^ k := by
  induction k with
  | zero => simpa using H.one
  | succ k ih =>
      have h1 : 1 ≤ a ^ k := Nat.one_le_pow _ _ ha
      rw [pow_succ, H.mul _ _ h1 ha, ih, pow_succ]

/-- Monotonicity alone rules out negative values above the unit. -/
theorem pos {h : ℕ → ℚ} (H : MonoMult h) (hα : 0 < h 2) :
    ∀ n : ℕ, 2 ≤ n → 0 < h n := by
  intro n hn
  rcases lt_trichotomy (h n) 0 with hlt | heq | hgt
  · exfalso
    have hmm := H.mono 2 n (by norm_num) hn
    have h1 := jq_lt_zero hlt
    have h2 := jq_nonneg hα
    linarith
  · exact absurd heq (H.ne n (by omega))
  · exact hgt

/-- A monotone character whose anchor exceeds the unit exceeds it everywhere
above the unit. Interpolating an anchor power into the dip is the contradiction:
if some value fell below the unit, some larger integer would cost less than
`2` does. -/
theorem ge_one {h : ℕ → ℚ} (H : MonoMult h) (hα : 1 < h 2) :
    ∀ n : ℕ, 2 ≤ n → 1 ≤ h n := by
  classical
  intro n hn
  by_contra hc
  push_neg at hc
  have hα0 : (0:ℚ) < h 2 := lt_trans zero_lt_one hα
  have hn0 : 0 < h n := H.pos hα0 n hn
  have hex : ∃ k : ℕ, (1:ℚ) ≤ (h 2) ^ k * h n := by
    obtain ⟨k, hk⟩ := exists_pow_gt_rat hα ((h n)⁻¹)
    refine ⟨k, ?_⟩
    have hmul' := mul_lt_mul_of_pos_right hk hn0
    rw [inv_mul_cancel₀ (ne_of_gt hn0)] at hmul'
    exact le_of_lt hmul'
  set k := Nat.find hex with hkdef
  have hkspec : (1:ℚ) ≤ (h 2) ^ k * h n := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero, one_mul] at hkspec
    linarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hmin : ¬ ((1:ℚ) ≤ (h 2) ^ j * h n) := Nat.find_min hex (by omega)
  push_neg at hmin
  have hupper : (h 2) ^ k * h n < h 2 := by
    have hrw : (h 2) ^ k * h n = h 2 * ((h 2) ^ j * h n) := by
      rw [hj, pow_succ]; ring
    have hstep := mul_lt_mul_of_pos_left hmin hα0
    rw [hrw, mul_one] at *
    linarith
  have hval : h (2 ^ k * n) = (h 2) ^ k * h n := by
    rw [H.mul _ _ (Nat.one_le_pow _ _ (by norm_num)) (by omega),
      H.pow 2 k (by norm_num)]
  have hbig : 2 ≤ 2 ^ k * n := by
    have h2k : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 * 1 ≤ 2 ^ k * n := Nat.mul_le_mul (by simpa using h2k) (by omega)
    simpa using this
  have hmm := H.mono 2 (2 ^ k * n) (by norm_num) hbig
  rw [hval] at hmm
  have hstrict := jq_strictMono hkspec hupper
  linarith

theorem transfer_le {h : ℕ → ℚ} (H : MonoMult h) (hα : 1 < h 2)
    {n : ℕ} (hn : 2 ≤ n) (m k : ℕ) (hmk : (2:ℚ) ^ m ≤ (n : ℚ) ^ k) :
    (h 2) ^ m ≤ (h n) ^ k := by
  have hnat : 2 ^ m ≤ n ^ k := by exact_mod_cast hmk
  have hmm := H.mono (2 ^ m) (n ^ k) (Nat.one_le_pow _ _ (by norm_num)) hnat
  rw [H.pow 2 m (by norm_num), H.pow n k (by omega)] at hmm
  exact jq_le_reflect (one_le_pow₀ (le_of_lt hα))
    (one_le_pow₀ (H.ge_one hα n hn)) hmm

theorem transfer_ge {h : ℕ → ℚ} (H : MonoMult h) (hα : 1 < h 2)
    {n : ℕ} (hn : 2 ≤ n) (m k : ℕ) (hmk : (n : ℚ) ^ k ≤ (2:ℚ) ^ m) :
    (h n) ^ k ≤ (h 2) ^ m := by
  have hnat : n ^ k ≤ 2 ^ m := by exact_mod_cast hmk
  have hmm := H.mono (n ^ k) (2 ^ m) (Nat.one_le_pow _ _ (by omega)) hnat
  rw [H.pow 2 m (by norm_num), H.pow n k (by omega)] at hmm
  exact jq_le_reflect (one_le_pow₀ (H.ge_one hα n hn))
    (one_le_pow₀ (le_of_lt hα)) hmm

/-- The degenerate gauge member: anchoring at the unit collapses the whole
cost. This is the sign character, the `c = 0` member of the power family. -/
theorem trivial_of_two_eq_one {h : ℕ → ℚ} (H : MonoMult h) (hα : h 2 = 1) :
    ∀ n : ℕ, 1 ≤ n → h n = 1 := by
  have hpow2 : ∀ n : ℕ, n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
        have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
        omega
  intro n hn
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    rw [hn1, H.one]
  · have hlow := H.mono 2 n (by norm_num) h2
    rw [hα, jq_one] at hlow
    have hup := H.mono n (2 ^ n) (by omega) (hpow2 n)
    rw [H.pow 2 n (by norm_num), hα, one_pow, jq_one] at hup
    exact jq_eq_zero (H.ne n hn) (le_antisymm hup hlow)

end MonoMult

/-- **The gauge theorem (Erdős 1946, completely multiplicative case).** Two
monotone characters that agree at the single index `2` agree at every positive
index. No logarithm, no limit, no real number: the anchor value fixes the whole
arithmetic function through the cut squeeze. -/
theorem monoMult_gauge {h₁ h₂ : ℕ → ℚ} (H₁ : MonoMult h₁) (H₂ : MonoMult h₂)
    (hanchor : h₁ 2 = h₂ 2) (hα : 1 ≤ h₁ 2) :
    ∀ n : ℕ, 1 ≤ n → h₁ n = h₂ n := by
  rcases eq_or_lt_of_le hα with heq | hlt
  · intro n hn
    rw [H₁.trivial_of_two_eq_one heq.symm n hn,
      H₂.trivial_of_two_eq_one (by rw [← hanchor]; exact heq.symm) n hn]
  · intro n hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      rw [hn1, H₁.one, H₂.one]
    · have hlt2 : 1 < h₂ 2 := by rw [← hanchor]; exact hlt
      refine cut_pins hlt (H₁.ge_one hlt n h2) (H₂.ge_one hlt2 n h2)
        (H₁.transfer_le hlt h2) (H₁.transfer_ge hlt h2) ?_ ?_
      · intro m k hmk
        rw [hanchor]
        exact H₂.transfer_le hlt2 h2 m k hmk
      · intro m k hmk
        rw [hanchor]
        exact H₂.transfer_ge hlt2 h2 m k hmk

theorem natCast_monoMult : MonoMult (fun n : ℕ => (n : ℚ)) where
  ne := fun n hn => by
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  one := by norm_num
  mul := fun m n _ _ => by push_cast; ring
  mono := fun m n hm hmn => by
    exact jq_mono (by exact_mod_cast hm) (by exact_mod_cast hmn)

/-- **Monotone rigidity.** A monotone character sending `2` to `2` is the
identity on the positive integers. The round-5 engine, and the special case of
the gauge theorem in which the second character is the identity. -/
theorem monotone_multiplicative_pins {h : ℕ → ℚ} (H : MonoMult h)
    (htwo : h 2 = 2) :
    ∀ n : ℕ, 1 ≤ n → h n = (n : ℚ) :=
  monoMult_gauge H natCast_monoMult (by rw [htwo]; norm_num)
    (by rw [htwo]; norm_num)

/-! ## Part 6 (ROUND 5): the structural ledger forces the canonical cost -/

/-- **The structural ledger.** Base (reciprocity, normalization invariance, the
nonzero composition law, unit-zero, and the single orbit-2 anchor) plus SIGN
REVERSAL plus MONOTONICITY plus the zero-orbit convention. Compared with the
round-2 slim ledger, the countable prime-pair product family and the signed-unit
calibration are both gone; nothing that replaced them mentions the canonical
cost. -/
structure PRCStructuralNativeCostHypotheses
    (F : RatioOrbit → RatioOrbit) : Prop where
  native : PRCNativeCostHypotheses F
  sign_reversing : PRCNativeCostSignReversing F
  monotone : PRCNativeCostMonotone F
  zero_calibrated : PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F)

def PRCStructuralNativeCostUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCStructuralNativeCostHypotheses F →
      ∀ q : RatioOrbit, RatioOrbit.crossEq (F q) (onRatioOrbit q)

/-- The character attached to a structural cost is the identity in display on
every positive integer orbit, up to the global reciprocal orientation that the
cost cannot see. This is the round-5 engine. -/
theorem structural_character_calibrated_on_positive_integers
    {F χ : RatioOrbit → RatioOrbit}
    (hF : PRCStructuralNativeCostHypotheses F)
    (hχ : PRCRatioCharacter χ)
    (hFχ : ∀ q : RatioOrbit, RatioOrbit.crossEq (F q) (costFromCharacter χ q)) :
    ∀ n : ℕ, 1 ≤ n → jq ((χ (natOrbit n)).toRat) = jq ((n : ℚ)) := by
  classical
  have hresp : PRCCharacterRespectsCrossEq χ :=
    PRCCharacterRespectsCrossEq_of_normalizeRatio_canonical hχ
      PRCNormalizeRatioCanonicalTarget_proved
  have hchi : ∀ a b : RatioOrbit, a.toRat = b.toRat →
      (χ a).toRat = (χ b).toRat := by
    intro a b hab
    exact crossDisp
      (hresp a b (dispCross hab))
  set g : ℕ → ℚ := fun n => (χ (natOrbit n)).toRat with hgdef
  -- the cost display of F at any orbit
  have hFdisp : ∀ q : RatioOrbit, (F q).toRat = jq ((χ q).toRat) := by
    intro q
    rw [crossDisp (hFχ q), costFromCharacter_jq]
  have hone : g 1 = 1 := by
    have h1 : (natOrbit 1).toRat = RatioOrbit.one.toRat := by
      rw [natOrbit_toRat, RatioOrbit.one_toRat]; norm_num
    have h2 := hchi _ _ h1
    show (χ (natOrbit 1)).toRat = 1
    rw [h2, crossDisp hχ.unit, RatioOrbit.one_toRat]
  have hmulg : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → g (m * n) = g m * g n := by
    intro m n _ _
    have hdisp : (natOrbit (m * n)).toRat =
        (RatioOrbit.mul (natOrbit m) (natOrbit n)).toRat := by
      rw [natOrbit_toRat, RatioOrbit.mul_toRat, natOrbit_toRat, natOrbit_toRat]
      push_cast
      ring
    have h1 := hchi _ _ hdisp
    have h2 := crossDisp
      (hχ.multiplicative (natOrbit m) (natOrbit n))
    show (χ (natOrbit (m * n))).toRat
        = (χ (natOrbit m)).toRat * (χ (natOrbit n)).toRat
    rw [h1, h2, RatioOrbit.mul_toRat]
  have hne : ∀ n : ℕ, 1 ≤ n → g n ≠ 0 := by
    intro n hn
    refine hχ.nonzero_preserving ?_
    rw [natOrbit_toRat]
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hmonog : ∀ m n : ℕ, 1 ≤ m → m ≤ n → jq (g m) ≤ jq (g n) := by
    intro m n hm hmn
    have := hF.monotone (natOrbit m) (natOrbit n) (natOrbit_isPosInt hm)
      (natOrbit_isPosInt (le_trans hm hmn)) (by
        rw [natOrbit_toRat, natOrbit_toRat]; exact_mod_cast hmn)
    rw [hFdisp, hFdisp] at this
    exact this
  have hg2 : g 2 = 2 ∨ g 2 = 2⁻¹ := by
    have hdisp : (natOrbit 2).toRat = two.toRat := by
      rw [natOrbit_toRat, two_toRat]; norm_num
    have hval : jq (g 2) = jq 2 := by
      have hcal := crossDisp hF.native.two_calibrated
      rw [hFdisp, jq_onRatioOrbit, two_toRat] at hcal
      show jq ((χ (natOrbit 2)).toRat) = jq 2
      rw [hchi _ _ hdisp]
      exact hcal
    exact jq_eq_two_cases (hne 2 (by norm_num)) hval
  have Hg : MonoMult g := ⟨hne, hone, hmulg, hmonog⟩
  have Hginv : MonoMult (fun k => (g k)⁻¹) :=
    { ne := fun k hk => inv_ne_zero (hne k hk)
      one := by rw [hone]; norm_num
      mul := fun a b ha hb => by rw [hmulg a b ha hb, mul_inv]
      mono := fun a b ha hab => by
        rw [jq_inv, jq_inv]
        exact hmonog a b ha hab }
  intro n hn
  show jq (g n) = jq ((n : ℚ))
  rcases hg2 with h2 | h2
  · rw [monotone_multiplicative_pins Hg h2 n hn]
  · have hinvtwo : (fun k => (g k)⁻¹) 2 = 2 := by show (g 2)⁻¹ = 2; rw [h2]; norm_num
    have hres := monotone_multiplicative_pins Hginv hinvtwo n hn
    calc jq (g n) = jq ((g n)⁻¹) := (jq_inv (g n)).symm
      _ = jq ((n : ℚ)) := by rw [hres]

/-- **Round 5 terminal.** The structural ledger forces the canonical cost. -/
theorem PRCStructuralNativeCostUniquenessTarget_proved :
    PRCStructuralNativeCostUniquenessTarget := by
  intro F hF q
  obtain ⟨χ, hχ, hFχ⟩ :=
    PRCZeroCalibratedNativeCostCharacterFactorizationTarget_proved F hF.native
      hF.zero_calibrated
  have hcal := structural_character_calibrated_on_positive_integers hF hχ hFχ
  have hresp : PRCCharacterRespectsCrossEq χ :=
    PRCCharacterRespectsCrossEq_of_normalizeRatio_canonical hχ
      PRCNormalizeRatioCanonicalTarget_proved
  have hchi : ∀ a b : RatioOrbit, a.toRat = b.toRat →
      (χ a).toRat = (χ b).toRat := by
    intro a b hab
    exact crossDisp
      (hresp a b (dispCross hab))
  -- every positive integer orbit is calibrated
  have hposcal : ∀ (a : RatioOrbit), IsPosIntOrbit a →
      RatioOrbit.crossEq (costFromCharacter χ a) (onRatioOrbit a) := by
    rintro a ⟨n, hn, han⟩
    have hdisp : a.toRat = (natOrbit n).toRat := by rw [natOrbit_toRat, han]
    rw [RatioOrbit.crossEq_iff_toRat_eq, costFromCharacter_jq, jq_onRatioOrbit,
      han]
    have hn' := hcal n hn
    rw [← hchi a (natOrbit n) hdisp] at hn'
    exact hn'
  have hprime : PRCCharacterPrimeDirectionCalibrated χ := fun p hp =>
    hposcal _ (primeDirection_isPosInt hp)
  have hpair : PRCCharacterPrimePairProductCostConsistent χ := by
    intro p hp r hr
    refine hposcal _ ⟨p.toNat * r.toNat, ?_, ?_⟩
    · obtain ⟨a, ha, _⟩ := primeDirection_isPosInt hp
      obtain ⟨b, hb, _⟩ := primeDirection_isPosInt hr
      have hpn : 1 ≤ p.toNat := by
        have h := primeDirection_toRat_ne_zero p hp
        rw [primeDirection_toRat] at h
        exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h)
      have hrn : 1 ≤ r.toNat := by
        have h := primeDirection_toRat_ne_zero r hr
        rw [primeDirection_toRat] at h
        exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h)
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · rw [RatioOrbit.mul_toRat, primeDirection_toRat, primeDirection_toRat]
      push_cast
      ring
  have hsignCost :
      RatioOrbit.crossEq (costFromCharacter χ negativeOneRatio)
        (onRatioOrbit negativeOneRatio) :=
    RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm (hFχ negativeOneRatio))
      (signReversing_forces_signed_unit hF.native.unit_zero hF.sign_reversing)
  have hsign : PRCCharacterSignedUnitCalibrated χ :=
    costFromCharacter_negativeOne_forces_signed_unit hχ hsignCost
  exact RatioOrbit.crossEq_trans (hFχ q)
    (PRCNativeCostSignedAdmissibleCharacterRigidityTarget_proved χ
      ⟨⟨hχ, hprime, hpair⟩, hsign⟩ q)

/-- Non-vacuity of the structural ledger. -/
theorem canonicalSelectedNativeCost_structural_hypotheses :
    PRCStructuralNativeCostHypotheses canonicalSelectedNativeCost :=
  { native :=
      canonicalSelectedNativeCost_slim_hypotheses.signed_strengthened.strengthened.native
    sign_reversing := canonicalSelectedNativeCost_signReversing
    monotone := canonicalSelectedNativeCost_monotone
    zero_calibrated := canonicalSelectedNativeCost_slim_hypotheses.zero_calibrated }

/-- **The prime-pair product family is redundant against monotonicity.** Every
inhabitant of the structural ledger satisfies it, and the whole round-1 and
round-2 ledger besides. -/
theorem structural_forces_slim (F : RatioOrbit → RatioOrbit)
    (hF : PRCStructuralNativeCostHypotheses F) :
    PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses F := by
  have hJ := PRCStructuralNativeCostUniquenessTarget_proved F hF
  exact
    { signed_strengthened :=
        { strengthened :=
            { native := hF.native
              prime_pair_product_cost := fun p hp r hr => hJ _ }
          signed_unit :=
            signReversing_forces_signed_unit hF.native.unit_zero hF.sign_reversing }
      zero_calibrated := hF.zero_calibrated }

/-- **Positivity is a theorem, not an axiom.** Recognizing a positive imbalance
never pays. -/
theorem structural_forces_positive (F : RatioOrbit → RatioOrbit)
    (hF : PRCStructuralNativeCostHypotheses F) :
    PRCNativeCostPositive F := by
  intro q hq
  have hJ := crossDisp
    (PRCStructuralNativeCostUniquenessTarget_proved F hF q)
  rw [hJ, jq_onRatioOrbit]
  exact jq_nonneg hq

/-! ## Part 7 (ROUND 6): the surviving anchor is a unit gauge

Two claims, and together they are the free-side stratification. The gauge orbit
is genuinely inhabited, so the anchor is a real choice and not a redundancy;
and the anchor value determines everything else, so it is the ONLY choice. -/

/-- The structural ledger with the anchor removed. -/
structure PRCStructuralNativeCostHypothesesSansAnchor
    (F : RatioOrbit → RatioOrbit) : Prop where
  base_sans_two : PRCNativeCostHypothesesSansTwoCalibration F
  sign_reversing : PRCNativeCostSignReversing F
  monotone : PRCNativeCostMonotone F
  zero_calibrated : PRCDoubledTraceZeroCalibrated (nativeCostDoubledTrace F)

def PRCStructuralSansAnchorUniquenessTarget : Prop :=
  ∀ F : RatioOrbit → RatioOrbit,
    PRCStructuralNativeCostHypothesesSansAnchor F →
      ∀ q : RatioOrbit, RatioOrbit.crossEq (F q) (onRatioOrbit q)

/-- The structural ledger is exactly the anchor-free ledger plus the anchor, so
what follows is a statement about the structural ledger's own last field. -/
theorem structural_iff_sansAnchor_and_two_calibrated
    (F : RatioOrbit → RatioOrbit) :
    PRCStructuralNativeCostHypotheses F ↔
      (PRCStructuralNativeCostHypothesesSansAnchor F ∧
        RatioOrbit.crossEq (F two) (onRatioOrbit two)) := by
  constructor
  · intro h
    exact ⟨⟨⟨h.native.reciprocal, h.native.normalized_invariant,
        h.native.canonical_rcl, h.native.unit_zero⟩,
      h.sign_reversing, h.monotone, h.zero_calibrated⟩,
      h.native.two_calibrated⟩
  · rintro ⟨h, htwo⟩
    exact ⟨⟨h.base_sans_two.reciprocal, h.base_sans_two.normalized_invariant,
        h.base_sans_two.canonical_rcl, h.base_sans_two.unit_zero, htwo⟩,
      h.sign_reversing, h.monotone, h.zero_calibrated⟩

/-! ### The odd power family inhabits the gauge orbit

The round-3 impostors do not survive here: the Liouville twist and the two-adic
twist are both non-monotone, which is exactly why monotonicity could replace the
pair family. What is left is the ODD power family `q ↦ q^(2k+1)`, whose members
are multiplicative, orientation-reversing, and monotone. The exponent must be
odd: an even power destroys sign reversal, since it cannot tell `-q` from `q`.

Every member of the family inhabits the anchor-free ledger, and distinct members
disagree at the anchor. So the gauge orbit is not just nonempty, it is infinite,
and the anchor is what picks one point of it. This is the free-side statement of
"the form is forced, the unit is a choice": the choice is a discrete
one-parameter family and the anchor is the coordinate on it. -/

/-- The cost generated by the power `q ↦ q^n`. Stated for every exponent, not
just the odd ones, because the parity is exactly what decides membership: every
field below holds for all `n ≥ 1`, and sign reversal is the one that splits. -/
def powerGeneratedNativeCost (n : ℕ) (q : RatioOrbit) : RatioOrbit :=
  if q.toRat = 1 then RatioOrbit.zero
  else onRatioOrbit (ratioOrbitOfRat (q.toRat ^ n))

theorem powerGeneratedNativeCost_toRat (n : ℕ) (q : RatioOrbit) :
    (powerGeneratedNativeCost n q).toRat = jq (q.toRat ^ n) := by
  rw [powerGeneratedNativeCost]
  by_cases h : q.toRat = 1
  · rw [if_pos h, RatioOrbit.zero_toRat, h, one_pow]
    norm_num [jq]
  · rw [if_neg h, jq_onRatioOrbit, ratioOrbitOfRat_toRat]

theorem powerGeneratedNativeCost_base (n : ℕ) :
    PRCNativeCostHypothesesSansTwoCalibration (powerGeneratedNativeCost n) where
  reciprocal := by
    intro q
    rw [RatioOrbit.crossEq_iff_toRat_eq, powerGeneratedNativeCost_toRat,
      powerGeneratedNativeCost_toRat, RatioOrbit.recip_toRat, inv_pow, jq_inv]
  normalized_invariant := by
    intro q
    rw [RatioOrbit.crossEq_iff_toRat_eq, powerGeneratedNativeCost_toRat,
      powerGeneratedNativeCost_toRat, DistinctionNat.normalizeRatio_toRat]
  canonical_rcl := by
    intro x y hx hy
    rw [RatioOrbit.crossEq_iff_toRat_eq]
    simp only [RatioOrbit.add_toRat, RatioOrbit.mul_toRat,
      powerGeneratedNativeCost_toRat, div_toRat, two_toRat]
    rw [mul_pow, div_pow]
    exact jq_rcl (pow_ne_zero _ hx) (pow_ne_zero _ hy)
  unit_zero := by
    rw [powerGeneratedNativeCost, if_pos RatioOrbit.one_toRat]

theorem powerGeneratedNativeCost_monotone (n : ℕ) :
    PRCNativeCostMonotone (powerGeneratedNativeCost n) := by
  rintro a b ⟨m, hm, ham⟩ ⟨_, _, _⟩ hab
  rw [powerGeneratedNativeCost_toRat, powerGeneratedNativeCost_toRat]
  have ha1 : (1:ℚ) ≤ a.toRat := by rw [ham]; exact_mod_cast hm
  refine jq_mono (one_le_pow₀ ha1) ?_
  exact pow_le_pow_left₀ (le_trans zero_le_one ha1) hab _

theorem powerGeneratedNativeCost_zero_calibrated {n : ℕ} (hn : n ≠ 0) :
    PRCDoubledTraceZeroCalibrated
      (nativeCostDoubledTrace (powerGeneratedNativeCost n)) := by
  rw [PRCDoubledTraceZeroCalibrated, RatioOrbit.crossEq_iff_toRat_eq]
  simp only [nativeCostDoubledTrace, doubledTraceValue, RatioOrbit.mul_toRat,
    RatioOrbit.add_toRat, two_toRat, RatioOrbit.one_toRat,
    powerGeneratedNativeCost_toRat, RatioOrbit.zero_toRat]
  rw [zero_pow hn]
  norm_num [jq]

/-- Odd exponents reverse orientation, because an odd power remembers the sign. -/
theorem powerGeneratedNativeCost_signReversing {n : ℕ} (hn : Odd n) :
    PRCNativeCostSignReversing (powerGeneratedNativeCost n) := by
  intro q r hr
  rw [powerGeneratedNativeCost_toRat, powerGeneratedNativeCost_toRat, hr,
    hn.neg_pow, jq_neg]

/-- The cost generated by the odd power `q ↦ q^(2k+1)`. `k = 0` is the canonical
cost; every `k ≥ 1` is a distinct point of the gauge orbit. -/
def oddPowerGeneratedNativeCost (k : ℕ) : RatioOrbit → RatioOrbit :=
  powerGeneratedNativeCost (2 * k + 1)

theorem oddPowerGeneratedNativeCost_toRat (k : ℕ) (q : RatioOrbit) :
    (oddPowerGeneratedNativeCost k q).toRat = jq (q.toRat ^ (2 * k + 1)) :=
  powerGeneratedNativeCost_toRat (2 * k + 1) q

theorem oddPowerGeneratedNativeCost_sansAnchor (k : ℕ) :
    PRCStructuralNativeCostHypothesesSansAnchor (oddPowerGeneratedNativeCost k) where
  base_sans_two := powerGeneratedNativeCost_base (2 * k + 1)
  sign_reversing :=
    powerGeneratedNativeCost_signReversing (n := 2 * k + 1) ⟨k, by ring⟩
  monotone := powerGeneratedNativeCost_monotone (2 * k + 1)
  zero_calibrated :=
    powerGeneratedNativeCost_zero_calibrated (n := 2 * k + 1) (by omega)

/-- The anchor value separates the family. The cost at the orbit `2` is
`J(2^(2k+1))`, and `jq` is strictly increasing at or above the unit, so distinct
exponents are distinct costs. -/
theorem oddPowerGeneratedNativeCost_anchor_injective {k k' : ℕ} (h : k ≠ k') :
    ¬ RatioOrbit.crossEq (oddPowerGeneratedNativeCost k two)
      (oddPowerGeneratedNativeCost k' two) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, oddPowerGeneratedNativeCost_toRat,
    oddPowerGeneratedNativeCost_toRat, two_toRat]
  have hstrict : ∀ i j : ℕ, i < j →
      jq ((2:ℚ) ^ (2 * i + 1)) < jq ((2:ℚ) ^ (2 * j + 1)) := by
    intro i j hij
    refine jq_strictMono (one_le_pow₀ (by norm_num)) ?_
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact ne_of_lt (hstrict k k' hlt)
  · exact ne_of_gt (hstrict k' k hgt)

/-- The first nontrivial member: the cube cost `J(q³)`. It charges `J(8) = 49/16`
for the orbit `2` where the canonical cost charges `J(2) = 1/4`. -/
def cubeGeneratedNativeCost : RatioOrbit → RatioOrbit :=
  oddPowerGeneratedNativeCost 1

theorem cubeGeneratedNativeCost_toRat (q : RatioOrbit) :
    (cubeGeneratedNativeCost q).toRat = jq (q.toRat ^ 3) :=
  oddPowerGeneratedNativeCost_toRat 1 q

theorem cubeGeneratedNativeCost_sansAnchor :
    PRCStructuralNativeCostHypothesesSansAnchor cubeGeneratedNativeCost :=
  oddPowerGeneratedNativeCost_sansAnchor 1

/-- The canonical cost is the `k = 0` member, so the family really is a family of
gauge choices around the answer rather than a family of impostors. -/
theorem oddPowerGeneratedNativeCost_zero (q : RatioOrbit) :
    (oddPowerGeneratedNativeCost 0 q).toRat = (onRatioOrbit q).toRat := by
  rw [oddPowerGeneratedNativeCost_toRat, jq_onRatioOrbit]
  norm_num

theorem cubeGeneratedNativeCost_two_not_canonical :
    ¬ RatioOrbit.crossEq (cubeGeneratedNativeCost two) (onRatioOrbit two) := by
  have h := oddPowerGeneratedNativeCost_anchor_injective (k := 1) (k' := 0)
    (by norm_num)
  intro hcross
  refine h ?_
  rw [RatioOrbit.crossEq_iff_toRat_eq, oddPowerGeneratedNativeCost_zero]
  exact crossDisp hcross

/-! #### The reverse inclusion, and where the gap actually is

CORRECTED TWICE ON 2026-07-25, so read the correction history as part of the
content. The first version of this comment called the reverse inclusion a
transcendence problem and advised against attacking it. The second version
withdrew that, correctly, but then located the gap at the zero orbit: it said the
open question was whether the anchor-free structural ledger implies
`PRCDoubledTraceZeroCalibrated`. That is not a question at all.
`PRCStructuralNativeCostHypothesesSansAnchor` carries `zero_calibrated` as its
fourth FIELD. The ledger assumes it. Nothing is open there.

The claim is that the odd power family is the WHOLE gauge orbit, stated below as
`GaugeOrbitIsOddPowerFamily`. The two steps and their real statuses:

STEP ONE, factorization, is where the whole difficulty sits, and the reason is a
TYPE. `PRCRatioCharacter χ` has `χ : RatioOrbit → RatioOrbit`, so it demands a
character valued in the carrier, hence rational. The d'Alembert solution of the
composition law does not provide one. What a cost exposes is the TRACE
`χ(q) + χ(q)⁻¹`, and carrier-valuedness of the cost is exactly rationality of the
traces, which is strictly weaker than rationality of `χ`.
`Cost.TraceRationalExponent.no_rational_character_at_trace_three` proves the gap
is real and not hypothetical: the equation `r + r⁻¹ = 3` has NO rational
solution, so a cost charging the perfectly rational `1/2` at the orbit two has no
rational character there. The real solution is the square of the golden ratio
(`golden_square_has_trace_three`), which the carrier provably does not contain
(`no_native_golden_scale`).

This also explains why the proved repair does not reach the anchor-free case.
`PRCZeroCalibratedNativeCostCharacterFactorizationTarget_proved` assumes
`PRCNativeCostHypotheses`, which INCLUDES `two_calibrated`. The extraction
`traceRootCandidate T q = (2·T(2q) - T(q))/3` is the specialization to `χ(2) = 2`
of `χ(q) = (T(2q) - r⁻¹T(q))/(r - r⁻¹)` with `r = χ(2)`; the anchor is what makes
`r` known and rational. Drop the anchor and `r` is an unknown root of
`x² - T(2)x + 1`, which need not lie in the carrier at all. So step one is: prove
factorization through a REAL-valued character. The carrier-valued target is not
merely unproved, it is the wrong target.

STEP TWO, the exponent, is now in better shape than any previous version of this
comment recorded, and its arithmetic core is PROVED in
`IndisputableMonolith.Cost.TraceRationalExponent`. Given a real character, the
round-5 cut argument makes `χ(2)` determine everything, so `χ(n) = n^c`, and an
inhabitant outside the family is a real `c` that is not an odd integer with
`n^c + n^(-c)` rational for every `n`. Note the weakening: TRACE rational, not
`n^c` rational. Every previous version of this comment demanded the latter, which
was too strong for the same reason step one was. The chain:

* trace rational makes `n^c` algebraic of degree at most two, for every `n`;
* six exponentials, applied to `{log 2, log 3, log 5}` and `{1, c}`, forces `c`
  rational, needing only that `2^c, 3^c, 5^c` be ALGEBRAIC;
* `int_of_rat_exponent_of_trace_rat` then forces `c` to be an integer, via
  `rat_of_trace_rat_of_pow_rat`: a real above one with rational trace that has
  any rational power is itself rational, so the quadratic case cannot survive.

And there the chain stops: `c` is a nonnegative INTEGER and no parity cut follows.
Earlier versions of this comment added a fourth bullet claiming
`evenPowerGeneratedNativeCost_not_sansAnchor` kills the even integers. It does not.
That theorem says the FUNCTION `q ↦ J(q^(2k+2))` fails sign reversal, which is true
because an even power forgets the sign of its argument. The even EXPONENT is carried
by a different character, `x ↦ sgn(x)·|x|^(2k+2)`, which reverses orientation and is
an inhabitant (`Cost.GaugeOrbitFromRealCharacter.signedPowerNativeCost_sansAnchor`).
Sign reversal constrains `χ(-1)` and nothing else, so it never touched the parity.

Only the six exponentials input is external, named as
`Cost.TraceRationalExponent.SixExponentialsTraceInput` rather than hidden, and
`exponent_is_positive_integer` is the packaged conditional.

The Alaoglu-Erdős note stands and is worth keeping. They asked the TWO-base
version in 1944, whether `2^c` and `3^c` both rational forces `c` integral, and
that is genuinely open since it needs four exponentials. Our reduction supplies
every base, so it lands on the proved side.

Net status (2026-07-26 close). The composition is DONE. Erdős's power-function step, which
this comment previously listed as a second external import, is now a theorem
(`Cost.MonotonePower.exists_exponent`, Howe's proof), and the classification is
`Cost.GaugeOrbitClassification.GaugeOrbitIsSignedPowerFamily_of_sixExponentials` with the
six exponentials input as its only hypothesis. What follows is the state of the chain as it
stood the day before, kept because it names the pieces.

STEP ONE is a THEOREM:
`Cost.RealCharacterFactorization.SansAnchorRealCharacterFactorizationTarget_proved`.
Every anchor-free inhabitant factors through `realCharacterCandidate`, a real
character extracted by the symbolic linear root
`χ(q) = (r·T(2q) - T(q))/(r² - 1)` with `r = realTraceRoot(T(2))` (or the sign
character when `T(2) = 2`). Multiplicativity is pure d'Alembert algebra;
principal orientation on positive integers uses monotone cut. The algebraic
core (`Cost.RealTraceRoot`) and the doubled-trace RCL without the anchor remain
in place. What remains for the orbit claim is COMPOSITION: feed that character
into the MonoMult/cut gauge and apply `Cost.TraceRationalExponent` (six
exponentials as a named input) to force the exponent to a nonnegative integer.

Why this matters: `Cost.UnitFromMinimality` shows the power family has a least
member at every exponent (`jcost_lt_pow`, `isLeastPower_iff_canonical`) and that
the surviving anchor is exactly the leastness condition, so closing the
composition would replace the last stipulation in the cost ledger with a
selection principle plus a nondegeneracy condition. -/

/-- **REFUTED** as stated, and so was its first correction. Factorization through a
real character is
`Cost.RealCharacterFactorization.SansAnchorRealCharacterFactorizationTarget_proved`,
but the reverse inclusion into the odd-power family alone is false: the
zero-exponent sign member inhabits the anchor-free ledger and is not any
`oddPowerGeneratedNativeCost k` (`GaugeOrbitIsOddPowerFamily_refuted` in
`Cost/GaugeOrbitFromRealCharacter.lean`). The disjunction that replaced it,
`GaugeOrbitIsSignOrOddPowerFamily`, is false too, by the exponent-two member
`signedPowerNativeCost 1` (`GaugeOrbitIsSignOrOddPowerFamily_refuted`). What replaced
both is `GaugeOrbitIsSignedPowerFamily`, one inhabitant per nonnegative integer
exponent with character `sgn(x)·|x|^c`, and that one is PROVED, on the six
exponentials input alone
(`Cost.GaugeOrbitClassification.GaugeOrbitIsSignedPowerFamily_of_sixExponentials`).
Forward inclusion at every exponent is `gauge_orbit_contains_every_odd_power`
together with `signedPowerNativeCost_sansAnchor`. -/
def GaugeOrbitIsOddPowerFamily : Prop :=
  ∀ F : RatioOrbit → RatioOrbit, PRCStructuralNativeCostHypothesesSansAnchor F →
    ∃ k : ℕ, ∀ q : RatioOrbit,
      RatioOrbit.crossEq (F q) (oddPowerGeneratedNativeCost k q)

/-- **The gauge orbit is infinite.** Every odd exponent gives an inhabitant of
the anchor-free ledger, and distinct exponents disagree at the anchor. -/
theorem gauge_orbit_contains_every_odd_power :
    ∀ k : ℕ, PRCStructuralNativeCostHypothesesSansAnchor
        (oddPowerGeneratedNativeCost k) ∧
      ∀ k' : ℕ, k ≠ k' → ¬ RatioOrbit.crossEq (oddPowerGeneratedNativeCost k two)
        (oddPowerGeneratedNativeCost k' two) :=
  fun k => ⟨oddPowerGeneratedNativeCost_sansAnchor k,
    fun _ h => oddPowerGeneratedNativeCost_anchor_injective h⟩

/-- **The anchor is a genuine unit gauge.** The anchor-free structural ledger
does NOT force the canonical cost. Everything else in the ledger is structure;
the last field is a choice of unit. -/
theorem PRCStructuralSansAnchorUniquenessTarget_refuted :
    ¬ PRCStructuralSansAnchorUniquenessTarget := by
  intro huniq
  exact cubeGeneratedNativeCost_two_not_canonical
    (huniq cubeGeneratedNativeCost cubeGeneratedNativeCost_sansAnchor two)

/-! ### The carrier is strictly more rigid than the line

`composition_law_admits_full_scale_family` says that on the completed line the
composition law admits `costLambda l x = J(x^l)` for EVERY real `l > 0`: the
continuum gauge orbit is uncountable, and `calibrationAxiom` has to collapse all
of it. The free side does not inherit that whole family. What is proved below is
one exclusion, and it is proved without calibration:

* The function `q ↦ J(q^(2k+2))` is a perfectly good carrier function. It
  satisfies every field of the anchor-free structural ledger EXCEPT sign
  reversal, and sign reversal kills it, with no anchor and no calibration
  anywhere. Read this as a statement about that function and NOT about even
  exponents: the character `sgn(x)·|x|^(2k+2)` has the same absolute value, does
  reverse orientation, and is an inhabitant
  (`Cost.GaugeOrbitFromRealCharacter.signedPowerNativeCost_sansAnchor`).
  Conflating the two cost this program a false classification for two years.

`l = 2` is the sharp case, because it is the continuum's own headline
countermodel: `composition_law_without_calibration_does_not_force_jcost`
exhibits `costLambdaTwo` as a function satisfying every continuum hypothesis
except calibration. On the carrier that same cost is not merely uncalibrated, it
is REFUTED, by an axiom that says a debit read backwards is a credit.

WHAT IS NOT PROVED HERE, stated so that nobody reads the above as more than it
is. The non-integer exponents are NOT excluded in this module. It is tempting to
say they cannot define a carrier function because the carrier is rational, and
that is wrong twice over: `2 ^ (logb 2 3) = 3` is rational at a non-integer
exponent, and in any case the carrier only constrains the TRACE `n^c + n^(-c)`,
not `n^c` itself. The correct question is whether the trace can stay rational at
every `n` without `c` being an integer. Corrected 2026-07-25: that is no longer
the wall. `Cost.TraceRationalExponent.int_of_rat_exponent_of_trace_rat` settles
the rational-exponent case outright, and six exponentials settles the irrational
one, so the exponent is an integer. The surviving wall is the factorization step
recorded above at `GaugeOrbitIsOddPowerFamily`, and the comparison below is the
even-exponent exclusion plus the odd-power witnesses, nothing wider.

Within that scope the answer to "is the calibration axiom the price of the
continuum or the price of calibration as such" is: at least partly the former.
The line admits a family the carrier provably does not, and the axiom is paying
for the difference. -/

/-- The cost generated by the even power `q ↦ q^(2k+2)`. -/
def evenPowerGeneratedNativeCost (k : ℕ) : RatioOrbit → RatioOrbit :=
  powerGeneratedNativeCost (2 * k + 2)

/-- The carrier analogue of the continuum countermodel `costLambdaTwo`. -/
def squareGeneratedNativeCost : RatioOrbit → RatioOrbit :=
  evenPowerGeneratedNativeCost 0

/-- **Even powers fail sign reversal, and nothing else.** An even power cannot
tell `-q` from `q`, so orientation reversal would force the cost to be constantly
`-1`, which it is not at the anchor. -/
theorem powerGeneratedNativeCost_not_signReversing {n : ℕ} (hn : Even n) :
    ¬ PRCNativeCostSignReversing (powerGeneratedNativeCost n) := by
  intro h
  have hr : (ratioOrbitOfRat (-2 : ℚ)).toRat = -two.toRat := by
    rw [ratioOrbitOfRat_toRat, two_toRat]
  have hsign := h two (ratioOrbitOfRat (-2 : ℚ)) hr
  have hneg : ((-2 : ℚ)) ^ n = (2 : ℚ) ^ n := hn.neg_pow 2
  rw [powerGeneratedNativeCost_toRat, powerGeneratedNativeCost_toRat,
    ratioOrbitOfRat_toRat, two_toRat, hneg] at hsign
  have hpos : (0 : ℚ) < 2 ^ n := by positivity
  have hnn := jq_nonneg hpos
  linarith

/-- Everything except orientation. The even-power costs satisfy the whole
anchor-free ledger apart from sign reversal, so the exclusion is attributable to
exactly one field. -/
theorem evenPowerGeneratedNativeCost_sans_signReversing (k : ℕ) :
    PRCNativeCostHypothesesSansTwoCalibration (evenPowerGeneratedNativeCost k) ∧
      PRCNativeCostMonotone (evenPowerGeneratedNativeCost k) ∧
      PRCDoubledTraceZeroCalibrated
        (nativeCostDoubledTrace (evenPowerGeneratedNativeCost k)) :=
  ⟨powerGeneratedNativeCost_base (2 * k + 2),
    powerGeneratedNativeCost_monotone (2 * k + 2),
    powerGeneratedNativeCost_zero_calibrated (n := 2 * k + 2) (by omega)⟩

theorem evenPowerGeneratedNativeCost_not_sansAnchor (k : ℕ) :
    ¬ PRCStructuralNativeCostHypothesesSansAnchor
      (evenPowerGeneratedNativeCost k) := by
  intro h
  exact powerGeneratedNativeCost_not_signReversing
    (n := 2 * k + 2) ⟨k + 1, by ring⟩ h.sign_reversing

/-- **The free side refutes the continuum's countermodel without calibrating.**
The `λ = 2` cost is the exact function the continuum theorem cannot exclude
without the calibration hypothesis. Its carrier analogue satisfies every other
structural field and is excluded by orientation reversal alone. -/
theorem native_ledger_refutes_the_square_cost :
    (PRCNativeCostHypothesesSansTwoCalibration squareGeneratedNativeCost ∧
        PRCNativeCostMonotone squareGeneratedNativeCost ∧
        PRCDoubledTraceZeroCalibrated
          (nativeCostDoubledTrace squareGeneratedNativeCost)) ∧
      ¬ PRCStructuralNativeCostHypothesesSansAnchor squareGeneratedNativeCost :=
  ⟨evenPowerGeneratedNativeCost_sans_signReversing 0,
    evenPowerGeneratedNativeCost_not_sansAnchor 0⟩

/-- **The continuum scale family does not transport.** On the line every
positive real exponent is an admissible cost. On the carrier the even exponents
are refuted outright, so part of what `calibrationAxiom` collapses is freedom
that exists only after completion.

This does NOT say the carrier orbit is smaller as a cardinality. It says one
identified subfamily of the continuum orbit is absent from the carrier orbit.
The odd exponents are present (`gauge_orbit_contains_every_odd_power`), and
whether anything else is present is the named transcendence wall above. -/
theorem continuum_gauge_exceeds_native_gauge :
    (∀ l : ℝ, 0 < l →
        Cost.FunctionalEquation.IsReciprocalCost (costLambda l) ∧
          Cost.FunctionalEquation.IsNormalized (costLambda l) ∧
          Cost.FunctionalEquation.SatisfiesCompositionLaw (costLambda l) ∧
          ContinuousOn (costLambda l) (Set.Ioi 0)) ∧
      (∀ k : ℕ, ¬ PRCStructuralNativeCostHypothesesSansAnchor
        (evenPowerGeneratedNativeCost k)) :=
  ⟨fun l hl => composition_law_admits_full_scale_family l hl,
    evenPowerGeneratedNativeCost_not_sansAnchor⟩

/-- The continuum gauge orbit, as a set of functions on the line. -/
def continuumScaleFamily : Set (ℝ → ℝ) :=
  {F | ∃ l : ℝ, 0 < l ∧ F = costLambda l}

/-- **The continuum gauge orbit is uncountable.** Distinct positive exponents
give distinct costs (`costLambda_injective`) and the positive reals are
uncountable, so what `calibrationAxiom` collapses on the line is not a discrete
list of impostors. Stated here rather than left as a remark, because the size of
the collapsed family is the quantitative half of the comparison with the
carrier. -/
theorem continuum_scale_family_uncountable :
    ¬ continuumScaleFamily.Countable := by
  intro hc
  haveI : Countable continuumScaleFamily := hc.to_subtype
  have hinj : Function.Injective
      (fun l : Set.Ioi (0 : ℝ) =>
        (⟨costLambda (l : ℝ), ⟨(l : ℝ), Set.mem_Ioi.mp l.2, rfl⟩⟩ :
          continuumScaleFamily)) := by
    rintro ⟨l, hl⟩ ⟨m, hm⟩ h
    have hfun : costLambda l = costLambda m := congrArg Subtype.val h
    exact Subtype.ext (costLambda_injective (Set.mem_Ioi.mp hl) (Set.mem_Ioi.mp hm)
      (fun x => congrFun hfun x))
  haveI : Countable (Set.Ioi (0 : ℝ)) := hinj.countable
  have hexp : Function.Injective
      (fun x : ℝ => (⟨Real.exp x, Set.mem_Ioi.mpr (Real.exp_pos x)⟩ :
        Set.Ioi (0 : ℝ))) := by
    intro a b h
    exact Real.exp_injective (congrArg Subtype.val h)
  exact real_not_countable hexp.countable

/-- **The line's monotone class is exactly the scale family.** One name for both
inclusions: every positive exponent is admissible and continuous, and
conversely any reciprocal, normalized, composition-obeying cost that is monotone
is `costLambda c` for a single real `c`. The converse needs no continuity and no
completeness, so the honest continuum comparison is monotone against monotone,
not monotone against continuous. -/
theorem continuum_monotone_class_is_the_scale_family :
    (∀ l : ℝ, 0 < l →
        Cost.FunctionalEquation.IsReciprocalCost (costLambda l) ∧
          Cost.FunctionalEquation.IsNormalized (costLambda l) ∧
          Cost.FunctionalEquation.SatisfiesCompositionLaw (costLambda l) ∧
          ContinuousOn (costLambda l) (Set.Ioi 0)) ∧
      (∀ F : ℝ → ℝ,
        Cost.FunctionalEquation.IsReciprocalCost F →
          Cost.FunctionalEquation.IsNormalized F →
            Cost.FunctionalEquation.SatisfiesCompositionLaw F →
              MonotoneOn (Cost.FunctionalEquation.H F) (Set.Ici (0 : ℝ)) →
                ∃ c : ℝ, ∀ x : ℝ, 0 < x → F x = costLambda c x) :=
  ⟨fun l hl => composition_law_admits_full_scale_family l hl,
    fun F hR hN hC hM => composition_law_monotone_forces_costLambda F hR hN hC hM⟩

/-- The square cost also misses the anchor, since `J(4) ≠ J(2)`. Sign reversal
already refutes it, so this is the redundant second failure, recorded because
the paper states it. -/
theorem squareGeneratedNativeCost_two_not_canonical :
    ¬ RatioOrbit.crossEq (squareGeneratedNativeCost two) (onRatioOrbit two) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, jq_onRatioOrbit,
    squareGeneratedNativeCost, evenPowerGeneratedNativeCost,
    powerGeneratedNativeCost_toRat, two_toRat]
  norm_num [jq]

/-! ### Gauge rigidity: the anchor is the only choice -/

theorem character_display {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ) {a b : RatioOrbit} (hab : a.toRat = b.toRat) :
    (χ a).toRat = (χ b).toRat :=
  crossDisp
    (PRCCharacterRespectsCrossEq_of_normalizeRatio_canonical hχ
      PRCNormalizeRatioCanonicalTarget_proved a b (dispCross hab))

/-- The arithmetic data a monotone factorized cost leaves on the positive
integers. -/
theorem monoMult_of_character {F χ : RatioOrbit → RatioOrbit}
    (hmono : PRCNativeCostMonotone F)
    (hχ : PRCRatioCharacter χ)
    (hFχ : ∀ q : RatioOrbit, RatioOrbit.crossEq (F q) (costFromCharacter χ q)) :
    MonoMult (fun n : ℕ => (χ (natOrbit n)).toRat) := by
  have hFdisp : ∀ q : RatioOrbit, (F q).toRat = jq ((χ q).toRat) := by
    intro q
    rw [crossDisp (hFχ q), costFromCharacter_jq]
  refine
    { ne := ?_, one := ?_, mul := ?_, mono := ?_ }
  · intro n hn
    refine hχ.nonzero_preserving ?_
    rw [natOrbit_toRat]
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  · show (χ (natOrbit 1)).toRat = 1
    have h1 : (natOrbit 1).toRat = RatioOrbit.one.toRat := by
      rw [natOrbit_toRat, RatioOrbit.one_toRat]; norm_num
    rw [character_display hχ h1, crossDisp hχ.unit, RatioOrbit.one_toRat]
  · intro m n _ _
    show (χ (natOrbit (m * n))).toRat
        = (χ (natOrbit m)).toRat * (χ (natOrbit n)).toRat
    have hdisp : (natOrbit (m * n)).toRat =
        (RatioOrbit.mul (natOrbit m) (natOrbit n)).toRat := by
      rw [natOrbit_toRat, RatioOrbit.mul_toRat, natOrbit_toRat, natOrbit_toRat]
      push_cast
      ring
    rw [character_display hχ hdisp,
      crossDisp (hχ.multiplicative (natOrbit m) (natOrbit n)),
      RatioOrbit.mul_toRat]
  · intro m n hm hmn
    have hstep := hmono (natOrbit m) (natOrbit n) (natOrbit_isPosInt hm)
      (natOrbit_isPosInt (le_trans hm hmn)) (by
        rw [natOrbit_toRat, natOrbit_toRat]; exact_mod_cast hmn)
    rw [hFdisp, hFdisp] at hstep
    exact hstep

/-- The reciprocal of a monotone character is a monotone character with the
same cost. -/
theorem MonoMult.inv {h : ℕ → ℚ} (H : MonoMult h) :
    MonoMult (fun k => (h k)⁻¹) where
  ne := fun k hk => inv_ne_zero (H.ne k hk)
  one := by show (h 1)⁻¹ = 1; rw [H.one]; norm_num
  mul := fun a b ha hb => by
    show (h (a * b))⁻¹ = (h a)⁻¹ * (h b)⁻¹
    rw [H.mul a b ha hb, mul_inv]
  mono := fun a b ha hab => by
    show jq ((h a)⁻¹) ≤ jq ((h b)⁻¹)
    rw [jq_inv, jq_inv]
    exact H.mono a b ha hab

/-- The anchor of a monotone character is positive. A negative anchor would make
the fourth orbit cost more than the eighth. -/
theorem MonoMult.two_pos {h : ℕ → ℚ} (H : MonoMult h) : 0 < h 2 := by
  rcases lt_trichotomy (h 2) 0 with hlt | heq | hgt
  · exfalso
    have h4 : h 4 = (h 2) ^ 2 := by
      have he : (4:ℕ) = 2 ^ 2 := by norm_num
      rw [he, H.pow 2 2 (by norm_num)]
    have h8 : h 8 = (h 2) ^ 3 := by
      have he : (8:ℕ) = 2 ^ 3 := by norm_num
      rw [he, H.pow 2 3 (by norm_num)]
    have hmm := H.mono 4 8 (by norm_num) (by norm_num)
    rw [h4, h8] at hmm
    have hp4 : (0:ℚ) < (h 2) ^ 2 := pow_two_pos_of_ne_zero (H.ne 2 (by norm_num))
    have hn8 : (h 2) ^ 3 < 0 := by nlinarith
    have hj4 := jq_nonneg hp4
    have hj8 := jq_lt_zero hn8
    linarith
  · exact absurd heq (H.ne 2 (by norm_num))
  · exact hgt

/-- Orientation: replacing a monotone character by its reciprocal changes no
cost, and one of the two carries its anchor at or above the unit. -/
theorem MonoMult.orient {h : ℕ → ℚ} (H : MonoMult h) :
    ∃ h' : ℕ → ℚ, MonoMult h' ∧ 1 ≤ h' 2 ∧ ∀ n : ℕ, jq (h' n) = jq (h n) := by
  rcases le_or_gt 1 (h 2) with hle | hlt
  · exact ⟨h, H, hle, fun _ => rfl⟩
  · refine ⟨fun k => (h k)⁻¹, H.inv, ?_, fun n => jq_inv (h n)⟩
    show (1:ℚ) ≤ (h 2)⁻¹
    have h2pos := H.two_pos
    have hcancel : h 2 * (h 2)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h2pos)
    nlinarith [inv_pos.mpr h2pos]

theorem jq_inj_ge_one {s t : ℚ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hj : jq s = jq t) :
    s = t :=
  le_antisymm (jq_le_reflect hs ht (le_of_eq hj))
    (jq_le_reflect ht hs (le_of_eq hj.symm))

/-- **Gauge rigidity.** Two monotone costs that factor through characters and
agree at the single orbit `2` agree on every positive integer orbit. Combined
with the cube witness: the anchor is a real choice, and it is the only one. That
is the free-side stratification, form forced and unit free. -/
theorem structural_gauge_rigidity
    {F₁ F₂ χ₁ χ₂ : RatioOrbit → RatioOrbit}
    (hm₁ : PRCNativeCostMonotone F₁) (hm₂ : PRCNativeCostMonotone F₂)
    (hχ₁ : PRCRatioCharacter χ₁) (hχ₂ : PRCRatioCharacter χ₂)
    (hf₁ : ∀ q : RatioOrbit, RatioOrbit.crossEq (F₁ q) (costFromCharacter χ₁ q))
    (hf₂ : ∀ q : RatioOrbit, RatioOrbit.crossEq (F₂ q) (costFromCharacter χ₂ q))
    (hanchor : RatioOrbit.crossEq (F₁ two) (F₂ two)) :
    ∀ a : RatioOrbit, IsPosIntOrbit a → RatioOrbit.crossEq (F₁ a) (F₂ a) := by
  have hd₁ : ∀ q : RatioOrbit, (F₁ q).toRat = jq ((χ₁ q).toRat) := fun q => by
    rw [crossDisp (hf₁ q), costFromCharacter_jq]
  have hd₂ : ∀ q : RatioOrbit, (F₂ q).toRat = jq ((χ₂ q).toRat) := fun q => by
    rw [crossDisp (hf₂ q), costFromCharacter_jq]
  obtain ⟨k₁, Hk₁, hk₁, hj₁⟩ := (monoMult_of_character hm₁ hχ₁ hf₁).orient
  obtain ⟨k₂, Hk₂, hk₂, hj₂⟩ := (monoMult_of_character hm₂ hχ₂ hf₂).orient
  have htwodisp : (natOrbit 2).toRat = two.toRat := by
    rw [natOrbit_toRat, two_toRat]; norm_num
  have hanch : jq (k₁ 2) = jq (k₂ 2) := by
    rw [hj₁ 2, hj₂ 2]
    show jq ((χ₁ (natOrbit 2)).toRat) = jq ((χ₂ (natOrbit 2)).toRat)
    rw [character_display hχ₁ htwodisp, character_display hχ₂ htwodisp,
      ← hd₁ two, ← hd₂ two, crossDisp hanchor]
  have hkeq := monoMult_gauge Hk₁ Hk₂ (jq_inj_ge_one hk₁ hk₂ hanch) hk₁
  rintro a ⟨n, hn, han⟩
  have hdisp : a.toRat = (natOrbit n).toRat := by rw [natOrbit_toRat, han]
  refine dispCross ?_
  rw [hd₁, hd₂, character_display hχ₁ hdisp, character_display hχ₂ hdisp]
  show jq ((fun m : ℕ => (χ₁ (natOrbit m)).toRat) n)
      = jq ((fun m : ℕ => (χ₂ (natOrbit m)).toRat) n)
  rw [← hj₁ n, ← hj₂ n, hkeq n hn]

/-! ### The round-6 certificate -/

/-- **The free-side stratification.** On the countable carrier the form of the
cost is forced by arithmetic alone and the only residual freedom is the size of
the unit, fixed by one anchor. -/
structure StructuralStratificationCertificate : Prop where
  /-- The structural ledger forces the canonical cost. -/
  uniqueness : PRCStructuralNativeCostUniquenessTarget
  /-- Two of its four fields never mention the canonical cost, and the ledger it
  replaces is recovered in full. -/
  contracts_slim :
    ∀ F : RatioOrbit → RatioOrbit, PRCStructuralNativeCostHypotheses F →
      PRCZeroCalibratedSignedStrengthenedNativeCostHypotheses F
  /-- Positivity is derived, not assumed. -/
  positivity :
    ∀ F : RatioOrbit → RatioOrbit, PRCStructuralNativeCostHypotheses F →
      PRCNativeCostPositive F
  /-- The remaining anchor is a genuine unit gauge: without it the ledger admits
  the cube cost. -/
  gauge_inhabited : ¬ PRCStructuralSansAnchorUniquenessTarget
  /-- And the gauge orbit is infinite: one inhabitant per odd exponent, pairwise
  distinguished by their value at the anchor. -/
  gauge_orbit_infinite :
    ∀ k : ℕ, PRCStructuralNativeCostHypothesesSansAnchor
        (oddPowerGeneratedNativeCost k) ∧
      ∀ k' : ℕ, k ≠ k' → ¬ RatioOrbit.crossEq (oddPowerGeneratedNativeCost k two)
        (oddPowerGeneratedNativeCost k' two)
  /-- And it is the only gauge: the anchor value determines every positive
  integer orbit. -/
  gauge_rigid :
    ∀ F₁ F₂ χ₁ χ₂ : RatioOrbit → RatioOrbit,
      PRCNativeCostMonotone F₁ → PRCNativeCostMonotone F₂ →
        PRCRatioCharacter χ₁ → PRCRatioCharacter χ₂ →
          (∀ q, RatioOrbit.crossEq (F₁ q) (costFromCharacter χ₁ q)) →
            (∀ q, RatioOrbit.crossEq (F₂ q) (costFromCharacter χ₂ q)) →
              RatioOrbit.crossEq (F₁ two) (F₂ two) →
                ∀ a : RatioOrbit, IsPosIntOrbit a →
                  RatioOrbit.crossEq (F₁ a) (F₂ a)
  /-- The class is inhabited. -/
  nonvacuous : PRCStructuralNativeCostHypotheses canonicalSelectedNativeCost

/-! ## Part 8 (ROUND 8): where the completion is actually bought

The public spine tags the reciprocal-generator claim at `traceClosure` because
the certificate lives on ℝ. Three of its four facts do not need to. The
involution, the reciprocal symmetry of the cost, and the characterization of the
unit as the unique zero-cost orbit are all δ-native, and are proved here on the
carrier. The fourth is where the completion is genuinely bought, and this
section proves exactly that: the self-similar scale `1 + 1/x = x` has NO
solution in the δ-native carrier. Same shape as the cost result. The form is
forced; the completion is a purchase, and now the purchase has a receipt. -/

theorem native_recip_involutive (q : RatioOrbit) :
    (RatioOrbit.recip (RatioOrbit.recip q)).toRat = q.toRat := by
  rw [RatioOrbit.recip_toRat, RatioOrbit.recip_toRat, inv_inv]

theorem native_cost_recip_symmetric (q : RatioOrbit) :
    (onRatioOrbit (RatioOrbit.recip q)).toRat = (onRatioOrbit q).toRat := by
  rw [jq_onRatioOrbit, jq_onRatioOrbit, RatioOrbit.recip_toRat, jq_inv]

/-- On the positive cone the reciprocal fixes exactly the zero-cost orbit: the
unit is the only thing that costs nothing, and it is the only self-reciprocal
positive orbit. -/
theorem native_recip_fixed_iff_cost_zero {q : RatioOrbit} (hq : 0 < q.toRat) :
    (RatioOrbit.recip q).toRat = q.toRat ↔ (onRatioOrbit q).toRat = 0 := by
  rw [RatioOrbit.recip_toRat, jq_onRatioOrbit]
  constructor
  · intro h
    have hne : q.toRat ≠ 0 := ne_of_gt hq
    have hsq : q.toRat * q.toRat = 1 := by
      field_simp at h
      linarith [h]
    have ht : q.toRat = 1 := by nlinarith [hq, hsq]
    rw [ht, jq_one]
  · intro h
    rw [jq_eq_zero (ne_of_gt hq) h]
    norm_num

/-- **The golden scale has no δ-native solution.** Elementary and choice-free:
clearing denominators gives `a² = b(a+b)` in lowest terms, so the denominator
divides `a²` and is therefore `1`, and no integer solves `a² = a + 1`. -/
theorem no_rat_golden_scale {t : ℚ} (ht : 0 < t) : 1 + t⁻¹ ≠ t := by
  intro h
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hsq : t * t = t + 1 := by
    field_simp at h
    linarith [h]
  have hdpos : (0:ℚ) < (t.den : ℚ) := by exact_mod_cast t.pos
  have hnd : (t.num : ℚ) = t * (t.den : ℚ) :=
    (div_eq_iff (ne_of_gt hdpos)).mp (Rat.num_div_den t)
  have hkey : (t.num : ℚ) * (t.num : ℚ)
      = (t.num : ℚ) * (t.den : ℚ) + (t.den : ℚ) * (t.den : ℚ) := by
    rw [hnd]
    linear_combination ((t.den : ℚ) * (t.den : ℚ)) * hsq
  have hZ : t.num * t.num = t.num * (t.den : ℤ) + (t.den : ℤ) * (t.den : ℤ) := by
    exact_mod_cast hkey
  have hdvd : (t.den : ℤ) ∣ t.num * t.num := ⟨t.num + (t.den : ℤ), by
    rw [hZ]; ring⟩
  have hdvdN : t.den ∣ t.num.natAbs * t.num.natAbs := by
    have hstep := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa [Int.natAbs_mul] using hstep
  have hcop : Nat.Coprime t.den (t.num.natAbs * t.num.natAbs) :=
    Nat.Coprime.mul_right t.reduced.symm t.reduced.symm
  have hd1 : t.den = 1 := by
    have hg : Nat.gcd t.den (t.num.natAbs * t.num.natAbs) = t.den :=
      Nat.gcd_eq_left hdvdN
    rw [Nat.Coprime] at hcop
    rw [hcop] at hg
    exact hg.symm
  rw [hd1] at hZ
  push_cast at hZ
  have hpos : 0 < t.num := Rat.num_pos.mpr ht
  have hb : t.num ≤ 2 := by nlinarith [hZ, sq_nonneg (t.num - 1)]
  have hcase : t.num = 1 ∨ t.num = 2 := by omega
  rcases hcase with hc | hc <;> rw [hc] at hZ <;> norm_num at hZ

/-- The carrier statement: no orbit is the self-similar scale. -/
theorem no_native_golden_scale :
    ¬ ∃ q : RatioOrbit, 0 < q.toRat ∧ 1 + (q.toRat)⁻¹ = q.toRat := by
  rintro ⟨q, hq, h⟩
  exact no_rat_golden_scale hq h

/-- **The φ split.** Everything the reciprocal generator says about the cost is
δ-native; only the fixed point is bought. -/
structure NativeReciprocalGeneratorSplit : Prop where
  involutive : ∀ q : RatioOrbit,
    (RatioOrbit.recip (RatioOrbit.recip q)).toRat = q.toRat
  cost_symmetric : ∀ q : RatioOrbit,
    (onRatioOrbit (RatioOrbit.recip q)).toRat = (onRatioOrbit q).toRat
  unit_is_cost_zero : ∀ q : RatioOrbit, 0 < q.toRat →
    ((RatioOrbit.recip q).toRat = q.toRat ↔ (onRatioOrbit q).toRat = 0)
  scale_is_a_purchase :
    ¬ ∃ q : RatioOrbit, 0 < q.toRat ∧ 1 + (q.toRat)⁻¹ = q.toRat

theorem nativeReciprocalGeneratorSplit_holds : NativeReciprocalGeneratorSplit where
  involutive := native_recip_involutive
  cost_symmetric := native_cost_recip_symmetric
  unit_is_cost_zero := fun _ hq => native_recip_fixed_iff_cost_zero hq
  scale_is_a_purchase := no_native_golden_scale

theorem structuralStratificationCertificate_holds :
    StructuralStratificationCertificate where
  uniqueness := PRCStructuralNativeCostUniquenessTarget_proved
  contracts_slim := structural_forces_slim
  positivity := structural_forces_positive
  gauge_inhabited := PRCStructuralSansAnchorUniquenessTarget_refuted
  gauge_orbit_infinite := gauge_orbit_contains_every_odd_power
  gauge_rigid := fun _ _ _ _ hm₁ hm₂ hχ₁ hχ₂ hf₁ hf₂ ha =>
    structural_gauge_rigidity hm₁ hm₂ hχ₁ hχ₂ hf₁ hf₂ ha
  nonvacuous := canonicalSelectedNativeCost_structural_hypotheses

/-! ### Axiom audit

The load-bearing results of this module, printed so the build log carries the
receipt. Anything beyond `propext`, `Classical.choice`, and `Quot.sound` (in
particular `sorryAx`) means a claim resting on this file is not proved. -/

#print axioms PRCStructuralNativeCostUniquenessTarget_proved
#print axioms PRCSignReversingNativeCostUniquenessTarget_proved
#print axioms PRCStructuralSansAnchorUniquenessTarget_refuted
#print axioms gauge_orbit_contains_every_odd_power
#print axioms oddPowerGeneratedNativeCost_sansAnchor
#print axioms powerGeneratedNativeCost_signReversing
#print axioms powerGeneratedNativeCost_not_signReversing
#print axioms native_ledger_refutes_the_square_cost
#print axioms continuum_gauge_exceeds_native_gauge
#print axioms continuum_scale_family_uncountable
#print axioms continuum_monotone_class_is_the_scale_family
#print axioms squareGeneratedNativeCost_two_not_canonical
#print axioms no_native_golden_scale
#print axioms nativeReciprocalGeneratorSplit_holds
#print axioms structuralStratificationCertificate_holds

end PRCJCost
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
