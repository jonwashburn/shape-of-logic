/-
  PrimitiveRecognitionCalculus/DeltaReal.lean

  Phase 1 of the Delta-Native Analysis frontier: ℝδ.

  A Delta-real is not a completed point on an uncountable continuum. It is a
  lawful rational-interval refinement protocol: a rule that, at every finite
  precision, returns a rational interval containing the intended quantity, with
  width shrinking to zero and each interval nested inside the previous one.

  This module builds that object directly over the rationals and proves:

  * `value`            : the unique real lying in every interval of a protocol;
  * `value_mem`        : the protocol's intervals all contain its value;
  * `value_unique`     : any real in every interval is the value (squeeze);
  * `ObsEq`            : observational equality = interval overlap at every
                         precision, proved equivalent to equal value;
  * `ofRat`            : the rational embedding, with `value (ofRat q) = q`;
  * `add`, `neg`, `sub`: native protocol operations, with `value` a homomorphism;
  * `value_surjective` : every real is the value of a (dyadic) protocol;
  * `display_real_forgetful` : the headline. The classical real is the forgetful
                         value of a protocol; protocol-reals present ℝ faithfully
                         (ObsEq ⇔ equal value) and natively (operations are
                         interval rules, not relabelled reals), with ℚ embedded.

  The honest separation: `DeltaReal` is the protocol interface used for analysis.
  Its `value` in ℝ is the display. The classical completion (RealCompletion.lean)
  is the separate completed object; this module does not need it.

  No project-local axioms. No sorry.
-/

import Mathlib

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace DeltaReal

/-! ## Rational intervals -/

/-- A closed rational interval. -/
structure RatInterval where
  lo : ℚ
  hi : ℚ
  le : lo ≤ hi

namespace RatInterval

/-- The rational width of an interval. -/
def width (I : RatInterval) : ℚ := I.hi - I.lo

theorem width_nonneg (I : RatInterval) : 0 ≤ I.width := by
  have := I.le; unfold width; linarith

/-- `I ⊆ J`: `J` contains `I`. -/
def Subset (I J : RatInterval) : Prop := J.lo ≤ I.lo ∧ I.hi ≤ J.hi

/-- Two intervals overlap when neither lies strictly to one side of the other. -/
def Overlap (I J : RatInterval) : Prop := I.lo ≤ J.hi ∧ J.lo ≤ I.hi

end RatInterval

/-! ## Delta-reals as refinement protocols -/

/-- A Delta-real: a nested family of rational intervals with width controlled by
`1/(n+1)` at precision `n`. The intended quantity is the unique real common to
all the intervals. -/
structure Protocol where
  approx : ℕ → RatInterval
  nested : ∀ n, (approx (n + 1)).Subset (approx n)
  width_bound : ∀ n, (approx n).width ≤ 1 / (n + 1)

namespace Protocol

/-- Lower endpoints as reals. -/
def lo (x : Protocol) (n : ℕ) : ℝ := ((x.approx n).lo : ℝ)

/-- Upper endpoints as reals. -/
def hi (x : Protocol) (n : ℕ) : ℝ := ((x.approx n).hi : ℝ)

theorem lo_le_hi (x : Protocol) (n : ℕ) : x.lo n ≤ x.hi n := by
  have := (x.approx n).le; unfold lo hi; exact_mod_cast this

theorem lo_mono (x : Protocol) : Monotone x.lo := by
  apply monotone_nat_of_le_succ
  intro n
  have h := (x.nested n).1
  unfold lo; exact_mod_cast h

theorem hi_anti (x : Protocol) : Antitone x.hi := by
  apply antitone_nat_of_succ_le
  intro n
  have h := (x.nested n).2
  unfold hi; exact_mod_cast h

/-- Any lower endpoint is below any upper endpoint. -/
theorem lo_le_hi_cross (x : Protocol) (a b : ℕ) : x.lo a ≤ x.hi b := by
  have h1 : x.lo a ≤ x.lo (max a b) := x.lo_mono (le_max_left a b)
  have h2 : x.lo (max a b) ≤ x.hi (max a b) := x.lo_le_hi _
  have h3 : x.hi (max a b) ≤ x.hi b := x.hi_anti (le_max_right a b)
  linarith

theorem bddAbove_lo (x : Protocol) : BddAbove (Set.range x.lo) := by
  refine ⟨x.hi 0, ?_⟩
  rintro y ⟨n, rfl⟩
  exact x.lo_le_hi_cross n 0

/-- The real value denoted by a protocol: the supremum of its lower endpoints,
equivalently the unique real in every interval. -/
noncomputable def value (x : Protocol) : ℝ := ⨆ n, x.lo n

theorem lo_le_value (x : Protocol) (n : ℕ) : x.lo n ≤ x.value :=
  le_ciSup x.bddAbove_lo n

theorem value_le_hi (x : Protocol) (n : ℕ) : x.value ≤ x.hi n :=
  ciSup_le (fun k => x.lo_le_hi_cross k n)

/-- The value lies in every interval. -/
theorem value_mem (x : Protocol) (n : ℕ) : x.lo n ≤ x.value ∧ x.value ≤ x.hi n :=
  ⟨x.lo_le_value n, x.value_le_hi n⟩

theorem width_real_bound (x : Protocol) (n : ℕ) : x.hi n - x.lo n ≤ 1 / (n + 1) := by
  have h := x.width_bound n
  unfold RatInterval.width at h
  unfold lo hi
  have : ((x.approx n).hi : ℝ) - ((x.approx n).lo : ℝ) = (((x.approx n).hi - (x.approx n).lo : ℚ) : ℝ) := by
    push_cast; ring
  rw [this]
  have hc : (((x.approx n).hi - (x.approx n).lo : ℚ) : ℝ) ≤ ((1 / (n + 1) : ℚ) : ℝ) := by
    exact_mod_cast h
  refine hc.trans ?_
  push_cast; rfl

/-- A nonnegative real bounded by `1/(n+1)` for all `n` is zero. -/
theorem tiny_le_zero {a : ℝ} (h0 : 0 ≤ a) (hsmall : ∀ n : ℕ, a ≤ 1 / (n + 1)) : a = 0 := by
  by_contra hne
  have hpos : 0 < a := lt_of_le_of_ne h0 (Ne.symm hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / a)
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  have : 1 / a < (n + 1 : ℝ) := lt_trans hn (by linarith)
  have hcontra : 1 / (n + 1 : ℝ) < a := by
    rw [div_lt_iff₀ hnpos]
    rw [div_lt_iff₀ hpos] at this
    linarith
  exact absurd (hsmall n) (not_le.mpr hcontra)

/-- Squeeze: any real in every interval equals the value. -/
theorem value_unique (x : Protocol) (y : ℝ)
    (hy : ∀ n, x.lo n ≤ y ∧ y ≤ x.hi n) : y = x.value := by
  have hbound : ∀ n : ℕ, |y - x.value| ≤ 1 / (n + 1) := by
    intro n
    obtain ⟨h1l, h1r⟩ := hy n
    obtain ⟨h2l, h2r⟩ := x.value_mem n
    have hw := x.width_real_bound n
    rw [abs_le]
    constructor <;> linarith
  have : |y - x.value| = 0 := tiny_le_zero (abs_nonneg _) hbound
  have := abs_eq_zero.mp this
  linarith

/-! ## Observational equality -/

/-- Observational equality: intervals overlap at every precision. -/
def ObsEq (x y : Protocol) : Prop := ∀ n, (x.approx n).Overlap (y.approx n)

/-- Observational equality is exactly equality of value. This is the central
faithfulness statement: the protocol distinguishes two reals iff their values
differ. -/
theorem obsEq_iff_value (x y : Protocol) : ObsEq x y ↔ x.value = y.value := by
  constructor
  · intro h
    have hbound : ∀ n : ℕ, |x.value - y.value| ≤ 2 * (1 / ((n : ℝ) + 1)) := by
      intro n
      obtain ⟨hxy, hyx⟩ := h n
      obtain ⟨hxl, hxr⟩ := x.value_mem n
      obtain ⟨hyl, hyr⟩ := y.value_mem n
      have hxw := x.width_real_bound n
      have hyw := y.width_real_bound n
      have ov1 : x.lo n ≤ y.hi n := by unfold Protocol.lo Protocol.hi; exact_mod_cast hxy
      have ov2 : y.lo n ≤ x.hi n := by unfold Protocol.lo Protocol.hi; exact_mod_cast hyx
      rw [abs_le]
      constructor <;> linarith
    have : |x.value - y.value| = 0 := by
      apply tiny_le_zero (abs_nonneg _)
      intro n
      have hb := hbound (2 * n + 1)
      have heq : 2 * (1 / ((↑(2 * n + 1) : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by
        have hne : (n : ℝ) + 1 ≠ 0 := by positivity
        push_cast
        field_simp
        ring
      rw [heq] at hb
      exact hb
    have := abs_eq_zero.mp this
    linarith
  · intro h n
    have hx := x.value_mem n
    have hy := y.value_mem n
    rw [h] at hx
    refine ⟨?_, ?_⟩
    · -- (x.approx n).lo ≤ (y.approx n).hi
      have : x.lo n ≤ y.hi n := le_trans hx.1 (y.value_le_hi n)
      unfold Protocol.lo Protocol.hi at this; exact_mod_cast this
    · -- (y.approx n).lo ≤ (x.approx n).hi
      have h1 := hy.1   -- y.lo n ≤ y.value
      have h2 := hx.2   -- y.value ≤ x.hi n
      have : y.lo n ≤ x.hi n := by linarith
      unfold Protocol.lo Protocol.hi at this; exact_mod_cast this

theorem obsEq_refl (x : Protocol) : ObsEq x x := (obsEq_iff_value x x).mpr rfl

theorem obsEq_symm {x y : Protocol} (h : ObsEq x y) : ObsEq y x :=
  (obsEq_iff_value y x).mpr ((obsEq_iff_value x y).mp h).symm

theorem obsEq_trans {x y z : Protocol} (hxy : ObsEq x y) (hyz : ObsEq y z) : ObsEq x z :=
  (obsEq_iff_value x z).mpr (((obsEq_iff_value x y).mp hxy).trans ((obsEq_iff_value y z).mp hyz))

/-- Observational equality as a `Setoid`. The quotient is the display real line. -/
def obsSetoid : Setoid Protocol where
  r := ObsEq
  iseqv := ⟨obsEq_refl, obsEq_symm, obsEq_trans⟩

/-! ## Rational embedding -/

/-- The constant protocol at a rational. -/
def ofRat (q : ℚ) : Protocol where
  approx := fun _ => ⟨q, q, le_refl q⟩
  nested := fun _ => ⟨le_refl q, le_refl q⟩
  width_bound := fun n => by
    unfold RatInterval.width
    simp only [sub_self]
    positivity

@[simp] theorem value_ofRat (q : ℚ) : (ofRat q).value = (q : ℝ) := by
  unfold value Protocol.lo ofRat
  simp

/-- The rational embedding is faithful: two rational protocols are observationally
equal iff the rationals are equal. -/
theorem ofRat_obsEq_iff (q r : ℚ) : ObsEq (ofRat q) (ofRat r) ↔ q = r := by
  rw [obsEq_iff_value, value_ofRat, value_ofRat]
  exact_mod_cast Iff.rfl

/-! ## Native operations -/

/-- Addition of protocols. At precision `n` it reads both operands at precision
`2n+1`, so the combined width is again `≤ 1/(n+1)`. -/
def add (x y : Protocol) : Protocol where
  approx := fun n =>
    let k := 2 * n + 1
    ⟨(x.approx k).lo + (y.approx k).lo, (x.approx k).hi + (y.approx k).hi, by
      have := (x.approx k).le; have := (y.approx k).le; linarith⟩
  nested := fun n => by
    refine ⟨?_, ?_⟩
    · have hx : (x.approx (2 * n + 1)).lo ≤ (x.approx (2 * (n + 1) + 1)).lo := by
        have : 2 * n + 1 ≤ 2 * (n + 1) + 1 := by omega
        have hm := x.lo_mono this
        unfold Protocol.lo at hm; exact_mod_cast hm
      have hy : (y.approx (2 * n + 1)).lo ≤ (y.approx (2 * (n + 1) + 1)).lo := by
        have : 2 * n + 1 ≤ 2 * (n + 1) + 1 := by omega
        have hm := y.lo_mono this
        unfold Protocol.lo at hm; exact_mod_cast hm
      simp only; linarith
    · have hx : (x.approx (2 * (n + 1) + 1)).hi ≤ (x.approx (2 * n + 1)).hi := by
        have : 2 * n + 1 ≤ 2 * (n + 1) + 1 := by omega
        have hm := x.hi_anti this
        unfold Protocol.hi at hm; exact_mod_cast hm
      have hy : (y.approx (2 * (n + 1) + 1)).hi ≤ (y.approx (2 * n + 1)).hi := by
        have : 2 * n + 1 ≤ 2 * (n + 1) + 1 := by omega
        have hm := y.hi_anti this
        unfold Protocol.hi at hm; exact_mod_cast hm
      simp only; linarith
  width_bound := fun n => by
    have hx := x.width_bound (2 * n + 1)
    have hy := y.width_bound (2 * n + 1)
    unfold RatInterval.width at hx hy ⊢
    simp only
    have hsum : (x.approx (2*n+1)).hi + (y.approx (2*n+1)).hi
        - ((x.approx (2*n+1)).lo + (y.approx (2*n+1)).lo)
        = ((x.approx (2*n+1)).hi - (x.approx (2*n+1)).lo)
          + ((y.approx (2*n+1)).hi - (y.approx (2*n+1)).lo) := by ring
    rw [hsum]
    have hkey : (1 : ℚ) / (2 * n + 1 + 1) + 1 / (2 * n + 1 + 1) = 1 / (n + 1) := by
      have hne : (n : ℚ) + 1 ≠ 0 := by positivity
      field_simp; ring
    calc ((x.approx (2*n+1)).hi - (x.approx (2*n+1)).lo)
            + ((y.approx (2*n+1)).hi - (y.approx (2*n+1)).lo)
          ≤ 1 / (2 * (n:ℚ) + 1 + 1) + 1 / (2 * (n:ℚ) + 1 + 1) := by
            have hx' : ((x.approx (2*n+1)).hi - (x.approx (2*n+1)).lo) ≤ 1 / (2 * (n:ℚ) + 1 + 1) := by
              have : ((2 * n + 1 : ℕ) : ℚ) + 1 = 2 * (n:ℚ) + 1 + 1 := by push_cast; ring
              rw [← this]; exact hx
            have hy' : ((y.approx (2*n+1)).hi - (y.approx (2*n+1)).lo) ≤ 1 / (2 * (n:ℚ) + 1 + 1) := by
              have : ((2 * n + 1 : ℕ) : ℚ) + 1 = 2 * (n:ℚ) + 1 + 1 := by push_cast; ring
              rw [← this]; exact hy
            linarith
      _ = 1 / (n + 1) := hkey

theorem value_add (x y : Protocol) : (add x y).value = x.value + y.value := by
  symm
  apply value_unique
  intro n
  refine ⟨?_, ?_⟩
  · show (add x y).lo n ≤ x.value + y.value
    unfold Protocol.lo add
    simp only
    have hx := x.lo_le_value (2 * n + 1)
    have hy := y.lo_le_value (2 * n + 1)
    unfold Protocol.lo at hx hy
    push_cast
    linarith
  · show x.value + y.value ≤ (add x y).hi n
    unfold Protocol.hi add
    simp only
    have hx := x.value_le_hi (2 * n + 1)
    have hy := y.value_le_hi (2 * n + 1)
    unfold Protocol.hi at hx hy
    push_cast
    linarith

/-- Negation of a protocol. -/
def neg (x : Protocol) : Protocol where
  approx := fun n => ⟨-(x.approx n).hi, -(x.approx n).lo, by have := (x.approx n).le; linarith⟩
  nested := fun n => by
    refine ⟨?_, ?_⟩
    · have := (x.nested n).2; simp only; linarith
    · have := (x.nested n).1; simp only; linarith
  width_bound := fun n => by
    have h := x.width_bound n
    unfold RatInterval.width at h ⊢
    simp only
    linarith

theorem value_neg (x : Protocol) : (neg x).value = -x.value := by
  symm
  apply value_unique
  intro n
  refine ⟨?_, ?_⟩
  · show (neg x).lo n ≤ -x.value
    unfold Protocol.lo neg
    simp only
    have := x.value_le_hi n
    unfold Protocol.hi at this
    push_cast; linarith
  · show -x.value ≤ (neg x).hi n
    unfold Protocol.hi neg
    simp only
    have := x.lo_le_value n
    unfold Protocol.lo at this
    push_cast; linarith

/-- Subtraction. -/
def sub (x y : Protocol) : Protocol := add x (neg y)

theorem value_sub (x y : Protocol) : (sub x y).value = x.value - y.value := by
  unfold sub
  rw [value_add, value_neg]
  ring

/-! ## Surjectivity: every real is a protocol value -/

/-- The doubling bound on dyadic floors: `⌊r·2ⁿ⁺¹⌋ ∈ {2⌊r·2ⁿ⌋, 2⌊r·2ⁿ⌋+1}`.
This is exactly why the dyadic intervals are nested. -/
theorem floor_double (r : ℝ) (n : ℕ) :
    2 * ⌊r * 2 ^ n⌋ ≤ ⌊r * 2 ^ (n + 1)⌋ ∧ ⌊r * 2 ^ (n + 1)⌋ ≤ 2 * ⌊r * 2 ^ n⌋ + 1 := by
  have hk : (⌊r * 2 ^ n⌋ : ℝ) ≤ r * 2 ^ n := Int.floor_le _
  have hk1 : r * 2 ^ n < (⌊r * 2 ^ n⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hpow : r * 2 ^ (n + 1) = (r * 2 ^ n) * 2 := by rw [pow_succ]; ring
  constructor
  · apply Int.le_floor.mpr
    push_cast
    rw [hpow]; nlinarith [hk]
  · have hlt : ⌊r * 2 ^ (n + 1)⌋ < 2 * ⌊r * 2 ^ n⌋ + 2 := by
      apply Int.floor_lt.mpr
      push_cast
      rw [hpow]; nlinarith [hk1]
    omega

/-- The canonical dyadic protocol of a real: at precision `n` it returns the
dyadic interval `[⌊r·2ⁿ⌋/2ⁿ, (⌊r·2ⁿ⌋+1)/2ⁿ]`. -/
noncomputable def canonical (r : ℝ) : Protocol where
  approx := fun n =>
    ⟨(⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n, ((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n, by
      have h2 : (0 : ℚ) < 2 ^ n := by positivity
      have hpos : (0 : ℚ) < 1 / 2 ^ n := by positivity
      have heq : ((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n - (⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n = 1 / 2 ^ n := by
        rw [div_sub_div_same]; congr 1; ring
      linarith⟩
  nested := fun n => by
    obtain ⟨hlow, hhigh⟩ := floor_double r n
    have hq2 : (0 : ℚ) < 2 ^ n := by positivity
    have hq2' : (0 : ℚ) < 2 ^ (n + 1) := by positivity
    have hpowq : (2 : ℚ) ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
    refine ⟨?_, ?_⟩
    · -- (approx n).lo ≤ (approx (n+1)).lo
      show (⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n ≤ (⌊r * 2 ^ (n + 1)⌋ : ℚ) / 2 ^ (n + 1)
      rw [div_le_div_iff₀ hq2 hq2', hpowq]
      have hlowq : (2 * (⌊r * 2 ^ n⌋ : ℤ) : ℚ) ≤ ((⌊r * 2 ^ (n + 1)⌋ : ℤ) : ℚ) := by
        exact_mod_cast hlow
      push_cast at hlowq ⊢
      nlinarith [hlowq, hq2]
    · -- (approx (n+1)).hi ≤ (approx n).hi
      show ((⌊r * 2 ^ (n + 1)⌋ : ℚ) + 1) / 2 ^ (n + 1) ≤ ((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n
      rw [div_le_div_iff₀ hq2' hq2, hpowq]
      have hhighq : ((⌊r * 2 ^ (n + 1)⌋ : ℤ) : ℚ) ≤ (2 * (⌊r * 2 ^ n⌋ : ℤ) + 1 : ℤ) := by
        exact_mod_cast hhigh
      push_cast at hhighq ⊢
      nlinarith [hhighq, hq2]
  width_bound := fun n => by
    show ((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n - (⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n ≤ 1 / (n + 1)
    have hq2 : (0 : ℚ) < 2 ^ n := by positivity
    have hw : ((⌊r * 2 ^ n⌋ : ℚ) + 1) / 2 ^ n - (⌊r * 2 ^ n⌋ : ℚ) / 2 ^ n = 1 / 2 ^ n := by
      rw [div_sub_div_same]; congr 1; ring
    rw [hw]
    have hnat : ∀ m : ℕ, m + 1 ≤ 2 ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ k ih =>
          have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
          have hpk : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
          omega
    have hle : ((n : ℚ) + 1) ≤ 2 ^ n := by
      have := hnat n
      calc ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
        _ ≤ ((2 ^ n : ℕ) : ℚ) := by exact_mod_cast this
        _ = 2 ^ n := by push_cast; ring
    have hnpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
    rw [div_le_div_iff₀ hq2 hnpos]
    linarith

theorem value_canonical (r : ℝ) : (canonical r).value = r := by
  symm
  apply value_unique
  intro n
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hflo : (⌊r * 2 ^ n⌋ : ℝ) ≤ r * 2 ^ n := Int.floor_le _
  have hflo1 : r * 2 ^ n < (⌊r * 2 ^ n⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · show (canonical r).lo n ≤ r
    simp only [canonical, Protocol.lo]
    push_cast
    rw [div_le_iff₀ h2]
    linarith
  · show r ≤ (canonical r).hi n
    simp only [canonical, Protocol.hi]
    push_cast
    rw [le_div_iff₀ h2]
    linarith

/-- `value` is surjective onto ℝ. -/
theorem value_surjective : Function.Surjective Protocol.value :=
  fun r => ⟨canonical r, value_canonical r⟩

/-! ## The headline: classical ℝ is the forgetful display of ℝδ -/

/-- **Phase 1 headline.** The classical real line is the forgetful value of a
Delta-real protocol. Concretely:

1. every real is the value of a protocol (`value_surjective`);
2. the rational embedding `ofRat` has `value (ofRat q) = q`, so ℚ sits inside;
3. observational equality of protocols is exactly equality of value
   (`obsEq_iff_value`), so the presentation is faithful;
4. the protocol operations are native interval rules whose value is a ring
   homomorphism (`value_add`, `value_neg`, `value_sub`).

So ℝ is not a primitive completed object here; it is recovered as the value
display of refinement protocols, and nothing in analysis needs more than the
protocol that produces rational data to any requested precision. -/
theorem display_real_forgetful :
    Function.Surjective Protocol.value
      ∧ (∀ q : ℚ, (ofRat q).value = (q : ℝ))
      ∧ (∀ x y : Protocol, ObsEq x y ↔ x.value = y.value)
      ∧ (∀ x y : Protocol, (add x y).value = x.value + y.value)
      ∧ (∀ x : Protocol, (neg x).value = -x.value)
      ∧ (∀ x y : Protocol, (sub x y).value = x.value - y.value) :=
  ⟨value_surjective, value_ofRat, obsEq_iff_value, value_add, value_neg, value_sub⟩

end Protocol
end DeltaReal
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
