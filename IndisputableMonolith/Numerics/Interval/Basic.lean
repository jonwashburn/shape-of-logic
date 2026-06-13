import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Verified Interval Arithmetic

This module provides rigorous interval arithmetic for computing bounds on
transcendental functions. The key insight is that we use rational endpoints
(which Lean can compute exactly) to bound real values.
-/

namespace IndisputableMonolith.Numerics

/-- A closed interval with rational endpoints. -/
structure Interval where
  lo : ℚ
  hi : ℚ
  valid : lo ≤ hi
  deriving DecidableEq

namespace Interval

/-- Containment: a real number x is in interval I if lo ≤ x ≤ hi -/
def contains (I : Interval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- Point interval containing a single rational -/
def point (q : ℚ) : Interval where
  lo := q
  hi := q
  valid := le_refl q

theorem contains_point (q : ℚ) : (point q).contains (q : ℝ) :=
  ⟨le_refl _, le_refl _⟩

/-- Interval from explicit bounds -/
def mk' (lo hi : ℚ) (h : lo ≤ hi := by decide) : Interval where
  lo := lo
  hi := hi
  valid := h

/-! ## Interval Arithmetic Operations -/

/-- Addition of intervals: [a,b] + [c,d] = [a+c, b+d] -/
def add (I J : Interval) : Interval where
  lo := I.lo + J.lo
  hi := I.hi + J.hi
  valid := add_le_add I.valid J.valid

instance : Add Interval where
  add := add

@[simp] theorem add_lo (I J : Interval) : (I + J).lo = I.lo + J.lo := rfl
@[simp] theorem add_hi (I J : Interval) : (I + J).hi = I.hi + J.hi := rfl

theorem add_contains_add {x y : ℝ} {I J : Interval}
    (hx : I.contains x) (hy : J.contains y) : (I + J).contains (x + y) := by
  constructor
  · simp only [add_lo, Rat.cast_add]
    exact add_le_add hx.1 hy.1
  · simp only [add_hi, Rat.cast_add]
    exact add_le_add hx.2 hy.2

/-- Negation of intervals: -[a,b] = [-b, -a] -/
def neg (I : Interval) : Interval where
  lo := -I.hi
  hi := -I.lo
  valid := neg_le_neg I.valid

instance : Neg Interval where
  neg := neg

@[simp] theorem neg_lo (I : Interval) : (-I).lo = -I.hi := rfl
@[simp] theorem neg_hi (I : Interval) : (-I).hi = -I.lo := rfl

theorem neg_contains_neg {x : ℝ} {I : Interval} (hx : I.contains x) : (-I).contains (-x) := by
  constructor
  · simp only [neg_lo, Rat.cast_neg]
    exact neg_le_neg hx.2
  · simp only [neg_hi, Rat.cast_neg]
    exact neg_le_neg hx.1

/-- Subtraction of intervals: [a,b] - [c,d] = [a-d, b-c] -/
def sub (I J : Interval) : Interval where
  lo := I.lo - J.hi
  hi := I.hi - J.lo
  valid := by linarith [I.valid, J.valid]

instance : Sub Interval where
  sub := sub

@[simp] theorem sub_lo (I J : Interval) : (I - J).lo = I.lo - J.hi := rfl
@[simp] theorem sub_hi (I J : Interval) : (I - J).hi = I.hi - J.lo := rfl

theorem sub_contains_sub {x y : ℝ} {I J : Interval}
    (hx : I.contains x) (hy : J.contains y) : (I - J).contains (x - y) := by
  constructor
  · simp only [sub_lo, Rat.cast_sub]
    exact sub_le_sub hx.1 hy.2
  · simp only [sub_hi, Rat.cast_sub]
    exact sub_le_sub hx.2 hy.1

/-- Multiplication for positive intervals -/
def mulPos (I J : Interval) (hI : 0 < I.lo) (hJ : 0 < J.lo) : Interval where
  lo := I.lo * J.lo
  hi := I.hi * J.hi
  valid := by
    apply mul_le_mul I.valid J.valid
    · exact le_of_lt hJ
    · linarith [I.valid]

theorem mulPos_contains_mul {x y : ℝ} {I J : Interval}
    (hIpos : 0 < I.lo) (hJpos : 0 < J.lo)
    (hx : I.contains x) (hy : J.contains y) : (mulPos I J hIpos hJpos).contains (x * y) := by
  have hIlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast hIpos
  have hJlo_pos : (0 : ℝ) < J.lo := by exact_mod_cast hJpos
  have hx_pos : 0 < x := lt_of_lt_of_le hIlo_pos hx.1
  have hy_pos : 0 < y := lt_of_lt_of_le hJlo_pos hy.1
  have hIhi_pos : (0 : ℝ) ≤ I.hi := le_trans (le_of_lt hIlo_pos) (by exact_mod_cast I.valid)
  constructor
  · simp only [mulPos, Rat.cast_mul]
    exact mul_le_mul hx.1 hy.1 (le_of_lt hJlo_pos) (le_trans (le_of_lt hIlo_pos) hx.1)
  · simp only [mulPos, Rat.cast_mul]
    exact mul_le_mul hx.2 hy.2 (le_of_lt hy_pos) hIhi_pos

/-- Scalar multiplication by a positive rational -/
def smulPos (q : ℚ) (I : Interval) (hq : 0 < q) : Interval where
  lo := q * I.lo
  hi := q * I.hi
  valid := mul_le_mul_of_nonneg_left I.valid (le_of_lt hq)

theorem smulPos_contains_smul {q : ℚ} {x : ℝ} {I : Interval}
    (hq : 0 < q) (hx : I.contains x) : (smulPos q I hq).contains ((q : ℝ) * x) := by
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · simp only [smulPos, Rat.cast_mul]
    exact mul_le_mul_of_nonneg_left hx.1 (le_of_lt hq_pos)
  · simp only [smulPos, Rat.cast_mul]
    exact mul_le_mul_of_nonneg_left hx.2 (le_of_lt hq_pos)

/-- Power by natural number for positive intervals -/
def npow (I : Interval) (n : ℕ) (hI : 0 < I.lo) : Interval where
  lo := I.lo ^ n
  hi := I.hi ^ n
  valid := by
    apply pow_le_pow_left₀ (le_of_lt hI) I.valid

theorem npow_contains_pow {x : ℝ} {I : Interval} {n : ℕ}
    (hIpos : 0 < I.lo) (hx : I.contains x) : (npow I n hIpos).contains (x ^ n) := by
  have hIlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast hIpos
  have hx_pos : 0 < x := lt_of_lt_of_le hIlo_pos hx.1
  constructor
  · simp only [npow, Rat.cast_pow]
    exact pow_le_pow_left₀ (le_of_lt hIlo_pos) hx.1 n
  · simp only [npow, Rat.cast_pow]
    exact pow_le_pow_left₀ (le_of_lt hx_pos) hx.2 n

/-! ## Bounds Checking -/

/-- If b < I.lo, then all x in I satisfy b < x -/
theorem lo_gt_implies_contains_gt {I : Interval} {b : ℚ} (h : b < I.lo) {x : ℝ}
    (hx : I.contains x) : (b : ℝ) < x :=
  lt_of_lt_of_le (by exact_mod_cast h) hx.1

/-- If I.hi < b, then all x in I satisfy x < b -/
theorem hi_lt_implies_contains_lt {I : Interval} {b : ℚ} (h : I.hi < b) {x : ℝ}
    (hx : I.contains x) : x < (b : ℝ) :=
  lt_of_le_of_lt hx.2 (by exact_mod_cast h)

/-- If b ≤ I.lo, then all x in I satisfy b ≤ x -/
theorem lo_ge_implies_contains_ge {I : Interval} {b : ℚ} (h : b ≤ I.lo) {x : ℝ}
    (hx : I.contains x) : (b : ℝ) ≤ x :=
  le_trans (by exact_mod_cast h) hx.1

/-- If I.hi ≤ b, then all x in I satisfy x ≤ b -/
theorem hi_le_implies_contains_le {I : Interval} {b : ℚ} (h : I.hi ≤ b) {x : ℝ}
    (hx : I.contains x) : x ≤ (b : ℝ) :=
  le_trans hx.2 (by exact_mod_cast h)

end Interval

end IndisputableMonolith.Numerics
