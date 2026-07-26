/-
# Principal branch of the doubled-trace root

Algebraic core for real-valued character extraction. A doubled trace `t ≥ 2`
has principal root `realTraceRoot t = (t + √(t² − 4))/2 ≥ 1`, recovering the
character value whose trace is `t`. Under the cosh-addition formula the branch
multiplies. Mathlib only; no PRC imports.
-/

import Mathlib

namespace IndisputableMonolith
namespace Cost
namespace RealTraceRoot

/-- The principal (≥ 1) root of `X² - t X + 1 = 0`, for `t ≥ 2`. -/
noncomputable def realTraceRoot (t : ℝ) : ℝ :=
  (t + Real.sqrt (t ^ 2 - 4)) / 2

theorem realTraceRoot_sq_sub_four_nonneg {t : ℝ} (ht : 2 ≤ t) :
    0 ≤ t ^ 2 - 4 := by nlinarith

theorem realTraceRoot_one : realTraceRoot 2 = 1 := by
  simp [realTraceRoot, show (2 : ℝ) ^ 2 - 4 = 0 by norm_num, Real.sqrt_zero]

theorem realTraceRoot_ge_one {t : ℝ} (ht : 2 ≤ t) : 1 ≤ realTraceRoot t := by
  have hs : 0 ≤ Real.sqrt (t ^ 2 - 4) := Real.sqrt_nonneg _
  simp only [realTraceRoot]
  linarith

theorem realTraceRoot_pos {t : ℝ} (ht : 2 ≤ t) : 0 < realTraceRoot t :=
  lt_of_lt_of_le zero_lt_one (realTraceRoot_ge_one ht)

theorem realTraceRoot_add_inv {t : ℝ} (ht : 2 ≤ t) :
    realTraceRoot t + (realTraceRoot t)⁻¹ = t := by
  have hsq : Real.sqrt (t ^ 2 - 4) ^ 2 = t ^ 2 - 4 :=
    Real.sq_sqrt (realTraceRoot_sq_sub_four_nonneg ht)
  have hne : realTraceRoot t ≠ 0 := ne_of_gt (realTraceRoot_pos ht)
  have hinv : (realTraceRoot t)⁻¹ = (t - Real.sqrt (t ^ 2 - 4)) / 2 := by
    have hprod :
        realTraceRoot t * ((t - Real.sqrt (t ^ 2 - 4)) / 2) = 1 := by
      simp only [realTraceRoot]
      field_simp
      nlinarith [hsq]
    have := congrArg (fun z : ℝ => z / realTraceRoot t) hprod
    field_simp [hne] at this ⊢
    linarith
  rw [hinv]
  simp only [realTraceRoot]
  ring

/-- **Multiplication of principal branches.** If `a, b ≥ 2` and
`u = (a b + √(a²−4)√(b²−4))/2`, then
`realTraceRoot u = realTraceRoot a * realTraceRoot b`. -/
theorem realTraceRoot_mul {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    realTraceRoot ((a * b + Real.sqrt (a ^ 2 - 4) * Real.sqrt (b ^ 2 - 4)) / 2) =
      realTraceRoot a * realTraceRoot b := by
  set sa := Real.sqrt (a ^ 2 - 4)
  set sb := Real.sqrt (b ^ 2 - 4)
  have hsa : 0 ≤ sa := Real.sqrt_nonneg _
  have hsb : 0 ≤ sb := Real.sqrt_nonneg _
  have hsqa : sa ^ 2 = a ^ 2 - 4 := by
    simpa [sa] using Real.sq_sqrt (realTraceRoot_sq_sub_four_nonneg ha)
  have hsqb : sb ^ 2 = b ^ 2 - 4 := by
    simpa [sb] using Real.sq_sqrt (realTraceRoot_sq_sub_four_nonneg hb)
  set u := (a * b + sa * sb) / 2
  -- √(u² − 4) = (a sb + b sa) / 2
  have hdisc : u ^ 2 - 4 = ((a * sb + b * sa) / 2) ^ 2 := by
    have h : 4 * (u ^ 2 - 4) = (a * sb + b * sa) ^ 2 := by
      simp only [u]
      nlinarith [hsqa, hsqb]
    have h4 : (4 : ℝ) ≠ 0 := by norm_num
    calc
      u ^ 2 - 4 = (4 * (u ^ 2 - 4)) / 4 := by ring
      _ = (a * sb + b * sa) ^ 2 / 4 := by rw [h]
      _ = ((a * sb + b * sa) / 2) ^ 2 := by ring
  have hsqrt : Real.sqrt (u ^ 2 - 4) = (a * sb + b * sa) / 2 := by
    have hnn : 0 ≤ (a * sb + b * sa) / 2 := by positivity
    rw [hdisc]
    exact Real.sqrt_sq hnn
  -- both sides equal (ab + a sb + b sa + sa sb) / 4
  simp only [realTraceRoot, hsqrt, u, sa, sb]
  field_simp
  ring

/-- Given `u + v = a b` and `(u - v)² = (a²−4)(b²−4)` with `v ≤ u`, the larger
trace is the cosh-addition value. -/
theorem larger_trace_of_diff_sq {a b u v : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hsum : u + v = a * b)
    (hdiffsq : (u - v) ^ 2 = (a ^ 2 - 4) * (b ^ 2 - 4))
    (hulev : v ≤ u) :
    u = (a * b + Real.sqrt (a ^ 2 - 4) * Real.sqrt (b ^ 2 - 4)) / 2 := by
  have hnonnega : 0 ≤ a ^ 2 - 4 := realTraceRoot_sq_sub_four_nonneg ha
  have hprod_sqrt :
      Real.sqrt ((a ^ 2 - 4) * (b ^ 2 - 4)) =
        Real.sqrt (a ^ 2 - 4) * Real.sqrt (b ^ 2 - 4) :=
    Real.sqrt_mul hnonnega (b ^ 2 - 4)
  have huv : u - v = Real.sqrt (a ^ 2 - 4) * Real.sqrt (b ^ 2 - 4) := by
    have := congrArg Real.sqrt hdiffsq
    rwa [Real.sqrt_sq (sub_nonneg.mpr hulev), hprod_sqrt] at this
  linarith

/-! ## Multiplicative d'Alembert algebra (doubled-trace units)

Pure algebra for `g (x*y) + g (x/y) = 2 * g x * g y` with `g 1 = 1`, and the
trace form `T (x*y) + T (x/y) = T x * T y` with `T 1 = 2` via `g = T/2`. -/

/-- **Multiplicative duplication.** From the product law at `(x, x)` with `g 1 = 1`. -/
theorem mulDAlembert_duplication {g : ℝ → ℝ}
    (hd : ∀ x y, x ≠ 0 → y ≠ 0 → g (x * y) + g (x / y) = 2 * g x * g y)
    (h1 : g 1 = 1) :
    ∀ x, x ≠ 0 → g (x * x) = 2 * (g x) ^ 2 - 1 := by
  intro x hx
  have h := hd x x hx hx
  rw [div_self hx, h1] at h
  linarith

/-- **Product identity.** Apply the law to arguments `(x*y)` and `(x/y)`. -/
theorem mulDAlembert_prod {g : ℝ → ℝ}
    (hd : ∀ x y, x ≠ 0 → y ≠ 0 → g (x * y) + g (x / y) = 2 * g x * g y) :
    ∀ x y, x ≠ 0 → y ≠ 0 →
      g (x * x) + g (y * y) = 2 * g (x * y) * g (x / y) := by
  intro x y hx hy
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hxdy : x / y ≠ 0 := div_ne_zero hx hy
  have h := hd (x * y) (x / y) hxy hxdy
  have hprod : (x * y) * (x / y) = x * x := by field_simp [hy]
  have hquot : (x * y) / (x / y) = y * y := by field_simp [hy]
  rw [hprod, hquot] at h
  linarith

/-- **Difference square.** Sum law, product identity, and duplication on `x`, `y`. -/
theorem mulDAlembert_diff_sq {g : ℝ → ℝ}
    (hd : ∀ x y, x ≠ 0 → y ≠ 0 → g (x * y) + g (x / y) = 2 * g x * g y)
    (h1 : g 1 = 1) :
    ∀ x y, x ≠ 0 → y ≠ 0 →
      (g (x * y) - g (x / y)) ^ 2
        = 4 * ((g x) ^ 2 - 1) * ((g y) ^ 2 - 1) := by
  intro x y hx hy
  have hsum := hd x y hx hy
  have hprod := mulDAlembert_prod hd x y hx hy
  have hdx := mulDAlembert_duplication hd h1 x hx
  have hdy := mulDAlembert_duplication hd h1 y hy
  rw [hdx, hdy] at hprod
  have expand : (g (x * y) - g (x / y)) ^ 2
      = (g (x * y) + g (x / y)) ^ 2 - 2 * (2 * g (x * y) * g (x / y)) := by ring
  rw [expand, hsum, ← hprod]
  ring

/-- **Difference square in doubled-trace units** (`T 1 = 2`, reduce via `g = T/2`). -/
theorem mulDAlembert_diff_sq_trace {T : ℝ → ℝ}
    (hd : ∀ x y, x ≠ 0 → y ≠ 0 → T (x * y) + T (x / y) = T x * T y)
    (h2 : T 1 = 2) :
    ∀ x y, x ≠ 0 → y ≠ 0 →
      (T (x * y) - T (x / y)) ^ 2
        = (T x ^ 2 - 4) * (T y ^ 2 - 4) := by
  intro x y hx hy
  set g := fun z => T z / 2
  have hg :
      ∀ u v, u ≠ 0 → v ≠ 0 → g (u * v) + g (u / v) = 2 * g u * g v := by
    intro u v hu hv
    simp only [g]
    have := hd u v hu hv
    field_simp
    linarith
  have hg1 : g 1 = 1 := by simp [g, h2]
  have hsq := mulDAlembert_diff_sq hg hg1 x y hx hy
  simp only [g] at hsq
  have hl : (T (x * y) / 2 - T (x / y) / 2) ^ 2
      = (T (x * y) - T (x / y)) ^ 2 / 4 := by ring
  have hr : 4 * ((T x / 2) ^ 2 - 1) * ((T y / 2) ^ 2 - 1)
      = (T x ^ 2 - 4) * (T y ^ 2 - 4) / 4 := by ring
  rw [hl, hr] at hsq
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  field_simp at hsq
  exact hsq

#print axioms realTraceRoot_mul
#print axioms realTraceRoot_add_inv
#print axioms larger_trace_of_diff_sq
#print axioms mulDAlembert_duplication
#print axioms mulDAlembert_prod
#print axioms mulDAlembert_diff_sq
#print axioms mulDAlembert_diff_sq_trace

end RealTraceRoot
end Cost
end IndisputableMonolith
