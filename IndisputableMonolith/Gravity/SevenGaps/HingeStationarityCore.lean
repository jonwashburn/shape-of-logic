import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Gravity.SevenGaps.LedgerEnergyBridge

/-!
# Seven Gaps: hinge stationarity core (the sourced stationary ratio)

## Status: THEOREM for every proved statement below (0 sorry, 0 RS-internal
axiom, no `native_decide`). The import set is exactly: Mathlib,
`IndisputableMonolith.Cost`, and
`IndisputableMonolith.Gravity.SevenGaps.LedgerEnergyBridge` (which
transitively brings `Gravity.RecognitionLedger` and the bridge's own
hinge-data definitions such as `quadraticCurvatureEnergy`); no
Regge/mesh/simplicial geometry module is imported. MODEL for the sourced
coupling term itself, as flagged below.

This module records, kernel-checked, exactly how much of the paper's bridge
relation "log x_sigma = kappa_sigma * delta_sigma + O(h^3)" is derivable
from J-cost stationarity, and exactly where a constitutive MODEL input
enters. The panel-adjudicated verdict:

* **Kill record C6 (raw Stokes route).**
  `closedCycle_coboundary_sum_eq_zero` proves that exact/coboundary
  substrate strains telescope to ZERO around every closed cycle of cells.
  A nonzero hinge deficit can never be sourced by summing coboundary
  strains around a closed hinge link. This is the kernel-checked
  obstruction that killed the raw Stokes route.

* **Kill record raw 1b (budget circularity).**
  `budget_implies_ratio_without_stationarity` proves that the naive
  formulation (impose the holonomy budget sum t_i = kappa*delta, minimize,
  conclude the ratio) is CIRCULAR: the budget hypothesis already IS the
  conclusion, and stationarity contributes nothing. The proof term is the
  budget hypothesis itself, which is the whole point.

* **The honest mechanism (sourced stationary ratio).** Minimizing
  Phi(t) = sum_i (cosh t_i - 1) - (kappa*delta/n) * sum_i t_i
  (J-cost plus an explicit deficit-source coupling; the cost term IS the
  summed J-cost of the exponential strain ratios by the kernel equation
  `sourcedAction_eq_jcost_sum`) has the unique global
  minimizer t_i = arsinh(kappa*delta/n) (`sourced_unique_minimizer`),
  giving n * arsinh(kappa*delta/n) = kappa*delta + O((kappa*delta)^3) with
  the explicit constant 1/6 (`sourced_ratio_cubic_error`). The constrained
  variant (equal split under a fixed budget) is
  `constrained_equal_split` / `constrained_equal_split_eq_iff`.

* **The admissibility target is a uniform small-h FAMILY predicate**
  (`RecognitionRatioFamily.IsAdmissible`): constants are quantified
  OUTSIDE the mesh scale, per the panel; a fixed-h existential-constant
  form is vacuous and is not stated here. The sourced construction closes
  it end-to-end (`sourced_ratio_isAdmissible`) with the explicit constant
  C_R = |kappa|^3 * C_K^3 * h0^3 / (6 n^2). Two disclosures, spelled out
  in that theorem's docstring: the curvature conjunct of the conclusion is
  a passthrough of the curvature hypothesis, and no 0 < h0 hypothesis is
  taken because for h0 <= 0 the predicate is vacuously true, so the
  theorem carries content exactly when 0 < h0.

## Honest tiers

* **THEOREM**: every named statement in this file (items 1 through 8 of
  the lane spec): `closedCycle_coboundary_sum_eq_zero`,
  `budget_implies_ratio_without_stationarity`,
  `sourced_unique_minimizer` (with `sourced_minimizer_le`,
  `sourced_minimizer_unique`), `sourced_ratio_cubic_error`,
  `constrained_equal_split`, `constrained_equal_split_eq_iff`,
  `sourced_ratio_isAdmissible`, `J_exp_quadratic_band`, `valueFn_deriv`
  (with `sourced_costTerm_hasDerivAt`), together with the supporting
  lemmas (`cosh_tangent_line_le`/`lt`, `sourced_pointwise_le`/`lt`,
  `arsinh_le_self_of_nonneg`, `self_sub_cube_le_arsinh`,
  `abs_arsinh_sub_self_le`, `sourcedAction_eq_sum`,
  `sourcedAction_eq_jcost_sum`, `sourcedValue_eq_action_min`).
* **MODEL**: the sourced coupling term -(kappa*delta/n) * sum_i t_i inside
  `sourcedAction` is an explicit deficit-source constitutive choice. It is
  NOT derived from the bare RecognitionLedger, and no such derivation is
  claimed anywhere in this file.

Any promotion language must read: derived from an explicit deficit-source
constitutive action plus J-stationarity, never: derived from the bare
RecognitionLedger. The J-cost identification inside that phrase is itself
a kernel equation (`sourcedAction_eq_jcost_sum`), not a docstring gloss.

## Constants achieved (spec deviations, recorded honestly)

* Item 4: the target constant 1/6 IS achieved:
  |arsinh y - y| <= |y|^3 / 6 (`abs_arsinh_sub_self_le`), hence
  |n * arsinh(c/n) - c| <= |c|^3 / (6 n^2).
* Item 7: the spec's optional constant cosh(r)/24 was not pursued; the
  achieved two-sided band constant is cosh(r)/4 on |u| <= r
  (`J_exp_quadratic_band`), via `cosh_remainder_le`. The spec marks the
  exact constant as not load-bearing.
* Item 8: the spec's suggested derivative value
  kappa * sinh(arsinh(kappa*delta/n)) for the optimal-cost term is not the
  chain-rule value; the correct derivative is
  kappa * tanh(arsinh(kappa*delta/n)) = kappa*(kappa*delta/n)/sqrt(1+...)
  (`sourced_costTerm_hasDerivAt`). The clean envelope identity that does
  come out is for the full optimal VALUE V(delta) = Phi(t*):
  V'(delta) = -kappa * arsinh(kappa*delta/n) (`valueFn_deriv`), which is
  exactly the envelope-theorem partial of the coupling term at the
  minimizer. Recorded as the panel requested; it never promotes alone.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps

/-! ## §1. Kill record C6: the closed-cycle coboundary obstruction -/

/-- **THEOREM (kill record C6, the raw Stokes route).** For a coboundary
strain s i j = f i - f j and any cyclic chain of cells v 0, v 1, ..., v m
with v m = v 0, the sum of strains around the cycle telescopes to zero.
Exact/coboundary substrate strains can NEVER sum to a nonzero deficit
around a closed hinge link: the raw Stokes route to the bridge relation is
dead, kernel-checked. -/
theorem closedCycle_coboundary_sum_eq_zero {Λ : Type*} {s : Λ → Λ → ℝ}
    (hs : IsCoboundary s) (v : ℕ → Λ) (m : ℕ) (hcycle : v m = v 0) :
    ∑ k ∈ Finset.range m, s (v k) (v (k + 1)) = 0 := by
  obtain ⟨f, hf⟩ := hs
  calc ∑ k ∈ Finset.range m, s (v k) (v (k + 1))
      = ∑ k ∈ Finset.range m,
          ((fun j => f (v j)) k - (fun j => f (v j)) (k + 1)) :=
        Finset.sum_congr rfl fun k _ => hf (v k) (v (k + 1))
    _ = f (v 0) - f (v m) := Finset.sum_range_sub' (fun j => f (v j)) m
    _ = 0 := by rw [hcycle]; ring

/-! ## §2. Kill record raw 1b: the budget circularity -/

/-- The naive "log ratio" of the raw 1b formulation: nothing but the sum
of the per-tick strains. -/
def naiveLogRatio (n : ℕ) (t : Fin n → ℝ) : ℝ := ∑ i, t i

/-- **THEOREM (kill record raw 1b, the budget circularity).** If the
holonomy budget sum_i t_i = kappa*delta is IMPOSED, then the "conclusion"
log ratio = kappa*delta holds with NO optimization used: the proof term is
the budget hypothesis itself. This records, kernel-checked, that the naive
1b formulation (impose budget, minimize, conclude ratio) is CIRCULAR: the
budget already contains the conclusion; stationarity added nothing. -/
theorem budget_implies_ratio_without_stationarity {n : ℕ} (t : Fin n → ℝ)
    (kappa delta : ℝ) (hbudget : ∑ i, t i = kappa * delta) :
    naiveLogRatio n t = kappa * delta := hbudget

/-! ## §3. The tangent-line core of cosh (strict convexity, elementary)

cosh t >= cosh u + sinh u * (t - u), strict for t ≠ u. Proved from the
exponential tangent bound exp z >= 1 + z (strict for z ≠ 0); no integrals,
no convexity library. -/

/-- **THEOREM (cosh tangent-line bound).** For all u, t:
cosh u + sinh u * (t - u) <= cosh t. -/
theorem cosh_tangent_line_le (u t : ℝ) :
    Real.cosh u + Real.sinh u * (t - u) ≤ Real.cosh t := by
  have h1 : Real.exp u * (1 + (t - u)) ≤ Real.exp t := by
    calc Real.exp u * (1 + (t - u)) = Real.exp u * (t - u + 1) := by ring
      _ ≤ Real.exp u * Real.exp (t - u) :=
          mul_le_mul_of_nonneg_left (Real.add_one_le_exp (t - u))
            (Real.exp_pos u).le
      _ = Real.exp t := by rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-u) * (1 - (t - u)) ≤ Real.exp (-t) := by
    calc Real.exp (-u) * (1 - (t - u)) = Real.exp (-u) * (u - t + 1) := by
          ring
      _ ≤ Real.exp (-u) * Real.exp (u - t) :=
          mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u - t))
            (Real.exp_pos (-u)).le
      _ = Real.exp (-t) := by rw [← Real.exp_add]; congr 1; ring
  rw [Real.cosh_eq, Real.sinh_eq, Real.cosh_eq]
  nlinarith [h1, h2]

/-- **THEOREM (strict cosh tangent-line bound).** For t ≠ u:
cosh u + sinh u * (t - u) < cosh t. This is the strict-convexity kernel
behind uniqueness of every minimizer in this file. -/
theorem cosh_tangent_line_lt (u t : ℝ) (hne : t ≠ u) :
    Real.cosh u + Real.sinh u * (t - u) < Real.cosh t := by
  have h1 : Real.exp u * (1 + (t - u)) < Real.exp t := by
    calc Real.exp u * (1 + (t - u)) = Real.exp u * (t - u + 1) := by ring
      _ < Real.exp u * Real.exp (t - u) :=
          mul_lt_mul_of_pos_left
            (Real.add_one_lt_exp (sub_ne_zero.mpr hne)) (Real.exp_pos u)
      _ = Real.exp t := by rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-u) * (1 - (t - u)) ≤ Real.exp (-t) := by
    calc Real.exp (-u) * (1 - (t - u)) = Real.exp (-u) * (u - t + 1) := by
          ring
      _ ≤ Real.exp (-u) * Real.exp (u - t) :=
          mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u - t))
            (Real.exp_pos (-u)).le
      _ = Real.exp (-t) := by rw [← Real.exp_add]; congr 1; ring
  rw [Real.cosh_eq, Real.sinh_eq, Real.cosh_eq]
  nlinarith [h1, h2]

/-- **THEOREM (one-variable sourced minimum).** For every source strength
a, the map t ↦ cosh t - 1 - a*t attains its global minimum at
t = arsinh a (where sinh t = a). -/
theorem sourced_pointwise_le (a t : ℝ) :
    Real.cosh (Real.arsinh a) - 1 - a * Real.arsinh a
      ≤ Real.cosh t - 1 - a * t := by
  have h := cosh_tangent_line_le (Real.arsinh a) t
  rw [Real.sinh_arsinh] at h
  nlinarith [h]

/-- **THEOREM (one-variable sourced minimum, strict).** The minimum of
t ↦ cosh t - 1 - a*t is attained ONLY at t = arsinh a. -/
theorem sourced_pointwise_lt (a t : ℝ) (hne : t ≠ Real.arsinh a) :
    Real.cosh (Real.arsinh a) - 1 - a * Real.arsinh a
      < Real.cosh t - 1 - a * t := by
  have h := cosh_tangent_line_lt (Real.arsinh a) t hne
  rw [Real.sinh_arsinh] at h
  nlinarith [h]

/-! ## §4. The sourced stationary ratio (item 3)

MODEL input flag: the coupling term -(c/n) * sum_i t_i below is an
explicit deficit-source constitutive choice, not derived from the bare
RecognitionLedger. Everything proved ABOUT `sourcedAction` is THEOREM. -/

/-- The sourced action Phi(t) = sum_i (cosh t_i - 1) - (c/n) * sum_i t_i:
the J-cost of the per-tick strains (via J(exp t) = cosh t - 1,
`Cost.Jcost_exp_cosh`) plus an explicit deficit-source coupling of total
strength c = kappa*delta, split evenly across the n ticks. The coupling
term is the MODEL input; see the module header. -/
noncomputable def sourcedAction (n : ℕ) (c : ℝ) (t : Fin n → ℝ) : ℝ :=
  (∑ i, (Real.cosh (t i) - 1)) - c / n * ∑ i, t i

/-- The claimed unique minimizer of the sourced action: the uniform
configuration t_i = arsinh(c/n). -/
noncomputable def sourcedMinimizer (n : ℕ) (c : ℝ) : Fin n → ℝ :=
  fun _ => Real.arsinh (c / n)

/-- **THEOREM.** The sourced action decomposes into independent per-tick
terms cosh t_i - 1 - (c/n) * t_i. -/
theorem sourcedAction_eq_sum (n : ℕ) (c : ℝ) (t : Fin n → ℝ) :
    sourcedAction n c t
      = ∑ i, (Real.cosh (t i) - 1 - c / n * t i) := by
  unfold sourcedAction
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- **THEOREM (kernel J-cost identification).** The cost term of the
sourced action IS the summed J-cost of the exponential per-tick strain
ratios: Phi(t) = sum_i J(exp t_i) - (c/n) * sum_i t_i, via
`Cost.Jcost_exp_cosh` (J(exp t) = cosh t - 1). This puts the promotion
phrase "derived from an explicit deficit-source constitutive action plus
J-stationarity" on a kernel equation rather than a docstring gloss: the
J-cost part of the action is identified with `Cost.Jcost` inside the
kernel, and ONLY the coupling term remains MODEL. -/
theorem sourcedAction_eq_jcost_sum (n : ℕ) (c : ℝ) (t : Fin n → ℝ) :
    sourcedAction n c t
      = (∑ i, Cost.Jcost (Real.exp (t i))) - c / n * ∑ i, t i := by
  unfold sourcedAction
  simp only [Cost.Jcost_exp_cosh]

/-- **THEOREM (global minimality).** The uniform configuration
t_i = arsinh(c/n) minimizes the sourced action over ALL configurations. -/
theorem sourced_minimizer_le (n : ℕ) (c : ℝ) (t : Fin n → ℝ) :
    sourcedAction n c (sourcedMinimizer n c) ≤ sourcedAction n c t := by
  rw [sourcedAction_eq_sum, sourcedAction_eq_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [sourcedMinimizer]
  exact sourced_pointwise_le (c / n) (t i)

/-- **THEOREM (uniqueness).** Any configuration achieving the minimum of
the sourced action IS the uniform configuration t_i = arsinh(c/n). -/
theorem sourced_minimizer_unique (n : ℕ) (c : ℝ) (t : Fin n → ℝ)
    (heq : sourcedAction n c t = sourcedAction n c (sourcedMinimizer n c)) :
    t = sourcedMinimizer n c := by
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hne
  have hlt : sourcedAction n c (sourcedMinimizer n c)
      < sourcedAction n c t := by
    rw [sourcedAction_eq_sum, sourcedAction_eq_sum]
    simp only [sourcedMinimizer]
    refine Finset.sum_lt_sum (fun i _ => sourced_pointwise_le (c / n) (t i))
      ⟨i₀, Finset.mem_univ i₀, ?_⟩
    exact sourced_pointwise_lt (c / n) (t i₀) hi₀
  linarith [heq, hlt]

/-- **THEOREM (item 3, sourced unique minimizer).** For every n (no
n >= 1 hypothesis is needed; at n = 0 both conjuncts are trivially true
on the empty tick set) and every total source strength c, the sourced
action
Phi(t) = sum_i (cosh t_i - 1) - (c/n) * sum_i t_i over t : Fin n → ℝ has
the unique global minimizer t_i = arsinh(c/n) for all i. The stationarity
condition sinh t_i = c/n is genuinely FORCED here (contrast with the
circular raw 1b route, `budget_implies_ratio_without_stationarity`), but
only because the deficit-source coupling was supplied as a MODEL input. -/
theorem sourced_unique_minimizer (n : ℕ) (c : ℝ) (t : Fin n → ℝ) :
    sourcedAction n c (sourcedMinimizer n c) ≤ sourcedAction n c t ∧
      (sourcedAction n c t = sourcedAction n c (sourcedMinimizer n c) →
        t = sourcedMinimizer n c) :=
  ⟨sourced_minimizer_le n c t, sourced_minimizer_unique n c t⟩

/-! ## §5. The cubic error of the sourced ratio (item 4) -/

/-- **THEOREM.** arsinh y <= y for y >= 0 (since y <= sinh y and arsinh is
monotone). -/
theorem arsinh_le_self_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    Real.arsinh y ≤ y := by
  calc Real.arsinh y ≤ Real.arsinh (Real.sinh y) :=
        Real.arsinh_le_arsinh.mpr (Real.self_le_sinh_iff.mpr hy)
    _ = y := Real.arsinh_sinh y

/-- **THEOREM (cubic lower bound).** y - y^3/6 <= arsinh y for y >= 0.
Proved by showing x ↦ arsinh x - x + x^3/6 is monotone (its derivative
1/sqrt(1+x^2) - 1 + x^2/2 is nonnegative everywhere) and vanishes at 0. -/
theorem self_sub_cube_le_arsinh {y : ℝ} (hy : 0 ≤ y) :
    y - y ^ 3 / 6 ≤ Real.arsinh y := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun z => Real.arsinh z - z + z ^ 3 / 6)
        ((Real.sqrt (1 + x ^ 2))⁻¹ - 1 + (3 : ℕ) * x ^ 2 / 6) x := by
    intro x
    have h1 := Real.hasDerivAt_arsinh x
    have h2 : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
    have h3 : HasDerivAt (fun z : ℝ => z ^ 3 / 6)
        ((3 : ℕ) * x ^ 2 / 6) x := by
      have h := (hasDerivAt_pow 3 x).div_const 6
      norm_num at h ⊢
      exact h
    exact (h1.sub h2).add h3
  have hmono : Monotone (fun z : ℝ => Real.arsinh z - z + z ^ 3 / 6) := by
    refine monotone_of_deriv_nonneg (fun x => (hderiv x).differentiableAt)
      fun x => ?_
    rw [(hderiv x).deriv]
    have hs_pos : 0 < Real.sqrt (1 + x ^ 2) :=
      Real.sqrt_pos.mpr (by positivity)
    have hs_sq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hs_inv : Real.sqrt (1 + x ^ 2) * (Real.sqrt (1 + x ^ 2))⁻¹ = 1 :=
      mul_inv_cancel₀ hs_pos.ne'
    rcases le_or_gt (1 - x ^ 2 / 2) 0 with hcase | hcase
    · have hpos : 0 < (Real.sqrt (1 + x ^ 2))⁻¹ := inv_pos.mpr hs_pos
      push_cast
      nlinarith [hpos, hcase]
    · have hx2 : x ^ 2 < 2 := by nlinarith [hcase]
      have hP : Real.sqrt (1 + x ^ 2) * (1 - x ^ 2 / 2) ≤ 1 := by
        nlinarith [hs_sq, hs_pos.le, sq_nonneg x, sq_nonneg (x ^ 2),
          sq_nonneg (Real.sqrt (1 + x ^ 2) * (1 - x ^ 2 / 2) - 1)]
      push_cast
      nlinarith [hP, hs_inv, hs_pos]
  have h0 : (fun z : ℝ => Real.arsinh z - z + z ^ 3 / 6) 0 = 0 := by
    simp only [Real.arsinh_zero]
    norm_num
  have hle := hmono hy
  rw [h0] at hle
  simp only at hle
  linarith [hle]

/-- **THEOREM (cubic error of arsinh, constant 1/6).**
|arsinh y - y| <= |y|^3 / 6 for ALL y (nonnegative branch from the two
bounds above, negative branch by oddness of arsinh). -/
theorem abs_arsinh_sub_self_le (y : ℝ) :
    |Real.arsinh y - y| ≤ |y| ^ 3 / 6 := by
  rcases le_or_gt 0 y with hy | hy
  · have h1 := arsinh_le_self_of_nonneg hy
    have h2 := self_sub_cube_le_arsinh hy
    rw [abs_of_nonneg hy,
      abs_of_nonpos (by linarith : Real.arsinh y - y ≤ 0)]
    linarith
  · have hy' : 0 ≤ -y := by linarith
    have h1 := arsinh_le_self_of_nonneg hy'
    have h2 := self_sub_cube_le_arsinh hy'
    rw [Real.arsinh_neg] at h1 h2
    have hcube : (-y) ^ 3 = -(y ^ 3) := by ring
    rw [hcube] at h2
    rw [abs_of_neg hy,
      abs_of_nonneg (by linarith : 0 ≤ Real.arsinh y - y)]
    have hgoal : (-y) ^ 3 = -(y ^ 3) := by ring
    rw [hgoal]
    linarith

/-- **THEOREM (item 4, cubic error of the sourced ratio, constant 1/6).**
|n * arsinh(c/n) - c| <= |c|^3 / (6 n^2) for n >= 1. This is the honest
form of the bridge expansion: the sourced stationary log ratio
n * arsinh(c/n) equals the deficit source c = kappa*delta up to an
explicitly bounded cubic error. -/
theorem sourced_ratio_cubic_error (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    |(n : ℝ) * Real.arsinh (c / n) - c|
      ≤ |c| ^ 3 / (6 * (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hkey : (n : ℝ) * Real.arsinh (c / n) - c
      = (n : ℝ) * (Real.arsinh (c / n) - c / n) := by
    field_simp
  rw [hkey, abs_mul, abs_of_pos hn0]
  have hcn : |c / (n : ℝ)| ^ 3 = |c| ^ 3 / (n : ℝ) ^ 3 := by
    rw [abs_div, abs_of_pos hn0, div_pow]
  calc (n : ℝ) * |Real.arsinh (c / n) - c / n|
      ≤ (n : ℝ) * (|c / (n : ℝ)| ^ 3 / 6) :=
        mul_le_mul_of_nonneg_left (abs_arsinh_sub_self_le (c / n)) hn0.le
    _ = |c| ^ 3 / (6 * (n : ℝ) ^ 2) := by
        rw [hcn]
        field_simp

/-! ## §6. The constrained equal split (item 5) -/

/-- **THEOREM (item 5, constrained equal split, lower bound).** Over the
constraint set {t | sum_i t_i = c}, the J-cost sum_i (cosh t_i - 1) is at
least n * (cosh(c/n) - 1): the equal split is optimal. Proved by summing
the tangent-line bound of cosh at c/n; the linear terms cancel against the
budget. NOTE the honest reading: this theorem extracts the equal-split
VALUE from the budget; it does not, and cannot, produce the budget itself
(see `budget_implies_ratio_without_stationarity`). -/
theorem constrained_equal_split (n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (t : Fin n → ℝ) (hbudget : ∑ i, t i = c) :
    (n : ℝ) * (Real.cosh (c / n) - 1) ≤ ∑ i, (Real.cosh (t i) - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hL : ∑ _i : Fin n,
      (Real.cosh (c / n) - Real.sinh (c / n) * (c / n))
      = (n : ℝ) * (Real.cosh (c / n) - Real.sinh (c / n) * (c / n)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum : ∑ i : Fin n,
      (Real.cosh (c / n) + Real.sinh (c / n) * (t i - c / n))
      ≤ ∑ i : Fin n, Real.cosh (t i) :=
    Finset.sum_le_sum fun i _ => cosh_tangent_line_le (c / n) (t i)
  have hsplit : ∑ i : Fin n,
      (Real.cosh (c / n) + Real.sinh (c / n) * (t i - c / n))
      = (n : ℝ) * Real.cosh (c / n) := by
    calc ∑ i : Fin n,
        (Real.cosh (c / n) + Real.sinh (c / n) * (t i - c / n))
        = ∑ i : Fin n,
            ((Real.cosh (c / n) - Real.sinh (c / n) * (c / n))
              + Real.sinh (c / n) * t i) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = (n : ℝ) * (Real.cosh (c / n) - Real.sinh (c / n) * (c / n))
            + Real.sinh (c / n) * c := by
          rw [Finset.sum_add_distrib, hL, ← Finset.mul_sum, hbudget]
      _ = (n : ℝ) * Real.cosh (c / n) := by
          field_simp
          ring
  have hR : ∑ i : Fin n, (Real.cosh (t i) - 1)
      = (∑ i : Fin n, Real.cosh (t i)) - (n : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hR]
  rw [hsplit] at hsum
  nlinarith [hsum]

/-- **THEOREM (item 5, equality characterization).** Under the budget
constraint, the constrained minimum n * (cosh(c/n) - 1) is attained IFF
the configuration is exactly the equal split t_i = c/n. -/
theorem constrained_equal_split_eq_iff (n : ℕ) (hn : 1 ≤ n) (c : ℝ)
    (t : Fin n → ℝ) (hbudget : ∑ i, t i = c) :
    (∑ i, (Real.cosh (t i) - 1) = (n : ℝ) * (Real.cosh (c / n) - 1)) ↔
      t = fun _ => c / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  constructor
  · intro heq
    by_contra hnef
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hnef
    have hlt : ∑ i : Fin n,
        (Real.cosh (c / n) + Real.sinh (c / n) * (t i - c / n))
        < ∑ i : Fin n, Real.cosh (t i) :=
      Finset.sum_lt_sum (fun i _ => cosh_tangent_line_le (c / n) (t i))
        ⟨i₀, Finset.mem_univ i₀,
          cosh_tangent_line_lt (c / n) (t i₀) hi₀⟩
    have hL : ∑ _i : Fin n,
        (Real.cosh (c / n) - Real.sinh (c / n) * (c / n))
        = (n : ℝ) * (Real.cosh (c / n) - Real.sinh (c / n) * (c / n)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have hsplit : ∑ i : Fin n,
        (Real.cosh (c / n) + Real.sinh (c / n) * (t i - c / n))
        = (n : ℝ) * Real.cosh (c / n) := by
      calc ∑ i : Fin n,
          (Real.cosh (c / n) + Real.sinh (c / n) * (t i - c / n))
          = ∑ i : Fin n,
              ((Real.cosh (c / n) - Real.sinh (c / n) * (c / n))
                + Real.sinh (c / n) * t i) :=
            Finset.sum_congr rfl fun i _ => by ring
        _ = (n : ℝ) * (Real.cosh (c / n) - Real.sinh (c / n) * (c / n))
              + Real.sinh (c / n) * c := by
            rw [Finset.sum_add_distrib, hL, ← Finset.mul_sum, hbudget]
        _ = (n : ℝ) * Real.cosh (c / n) := by
            field_simp
            ring
    have hR : ∑ i : Fin n, (Real.cosh (t i) - 1)
        = (∑ i : Fin n, Real.cosh (t i)) - (n : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [hsplit] at hlt
    rw [hR] at heq
    nlinarith [hlt, heq]
  · intro ht
    subst ht
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## §7. The uniform small-h admissible family (item 6)

Per the panel: the admissibility target is a FAMILY predicate with the
constants quantified OUTSIDE the mesh scale h. A fixed-h
existential-constant form is vacuous (any single h admits fitted
constants) and is deliberately NOT stated in this file. -/

/-- A family of hinge ratio data indexed by mesh scale h: the recognition
ratio x(h) and the hinge deficit delta(h). -/
structure RecognitionRatioFamily where
  /-- The recognition ratio x(h) at mesh scale h. -/
  ratio : ℝ → ℝ
  /-- The hinge deficit delta(h) at mesh scale h. -/
  deficit : ℝ → ℝ

/-- **The uniform small-h admissibility predicate (item 6).** A family is
admissible for (h0, kappa, C_K, C_R) iff UNIFORMLY over all mesh scales
h in (0, h0): the deficit obeys the curvature bound |delta(h)| <= C_K h^2
AND the bridge relation holds with cubic error
|log x(h) - kappa * delta(h)| <= C_R h^3. The constants are quantified
outside the family, per the panel; this is what makes the predicate
non-vacuous. -/
def RecognitionRatioFamily.IsAdmissible (F : RecognitionRatioFamily)
    (h₀ kappa C_K C_R : ℝ) : Prop :=
  ∀ h ∈ Set.Ioo (0 : ℝ) h₀,
    |F.deficit h| ≤ C_K * h ^ 2 ∧
      |Real.log (F.ratio h) - kappa * F.deficit h| ≤ C_R * h ^ 3

/-- The sourced-stationary ratio family: at each mesh scale h, the ratio
is x(h) = exp(n * arsinh(kappa * delta(h) / n)), i.e. the exponential of
the optimal total strain of the sourced action with source
c = kappa * delta(h) (`sourced_unique_minimizer`). -/
noncomputable def sourcedRatioFamily (n : ℕ) (kappa : ℝ) (δ : ℝ → ℝ) :
    RecognitionRatioFamily where
  ratio := fun h => Real.exp ((n : ℝ) * Real.arsinh (kappa * δ h / n))
  deficit := δ

/-- **THEOREM (item 6, end-to-end admissibility of the sourced ratio).**
Under the curvature bound |delta(h)| <= C_K h^2 on (0, h0), the
sourced-stationary construction yields an admissible family with the
EXPLICIT uniform constant C_R = |kappa|^3 * C_K^3 * h0^3 / (6 n^2),
computed from the cubic error bound `sourced_ratio_cubic_error`:
|log x(h) - kappa*delta(h)| = |n*arsinh(kappa*delta(h)/n) - kappa*delta(h)|
<= |kappa*delta(h)|^3/(6n^2) <= (|kappa| C_K h^2)^3/(6n^2)
<= (|kappa|^3 C_K^3 h0^3/(6n^2)) * h^3 for h in (0, h0).

Two honest disclosures. (a) The curvature conjunct |delta(h)| <= C_K h^2
of the conclusion is a PASSTHROUGH of the hypothesis `hδ`, restated inside
the predicate only so the admissibility record is self-contained; the new
content of this theorem is entirely the bridge conjunct. (b) There is no
0 < h0 hypothesis: for h0 <= 0 the interval (0, h0) is empty and the
predicate is vacuously true, so adding positivity would not strengthen
the conclusion; the statement carries content exactly when 0 < h0. -/
theorem sourced_ratio_isAdmissible (n : ℕ) (hn : 1 ≤ n)
    (h₀ kappa C_K : ℝ) (δ : ℝ → ℝ)
    (hδ : ∀ h ∈ Set.Ioo (0 : ℝ) h₀, |δ h| ≤ C_K * h ^ 2) :
    (sourcedRatioFamily n kappa δ).IsAdmissible h₀ kappa C_K
      (|kappa| ^ 3 * C_K ^ 3 * h₀ ^ 3 / (6 * (n : ℝ) ^ 2)) := by
  intro h hh
  obtain ⟨hh1, hh2⟩ := hh
  have hδh := hδ h ⟨hh1, hh2⟩
  refine ⟨hδh, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hCK : 0 ≤ C_K := by
    have hsq : (0 : ℝ) < h ^ 2 := by positivity
    nlinarith [abs_nonneg (δ h), hδh, hsq]
  have hh3 : h ^ 3 ≤ h₀ ^ 3 := pow_le_pow_left₀ hh1.le hh2.le 3
  show |Real.log (Real.exp ((n : ℝ) * Real.arsinh (kappa * δ h / n)))
      - kappa * δ h| ≤ _
  rw [Real.log_exp]
  have hnum : |kappa * δ h| ^ 3
      ≤ |kappa| ^ 3 * C_K ^ 3 * h₀ ^ 3 * h ^ 3 := by
    have h1 : |kappa * δ h| ^ 3 = |kappa| ^ 3 * |δ h| ^ 3 := by
      rw [abs_mul, mul_pow]
    have h2 : |δ h| ^ 3 ≤ (C_K * h ^ 2) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) hδh 3
    have h3 : (C_K * h ^ 2) ^ 3 = C_K ^ 3 * (h ^ 3 * h ^ 3) := by ring
    have h4 : C_K ^ 3 * (h ^ 3 * h ^ 3) ≤ C_K ^ 3 * (h₀ ^ 3 * h ^ 3) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right hh3 (by positivity)
    calc |kappa * δ h| ^ 3 = |kappa| ^ 3 * |δ h| ^ 3 := h1
      _ ≤ |kappa| ^ 3 * (C_K ^ 3 * (h₀ ^ 3 * h ^ 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc |δ h| ^ 3 ≤ (C_K * h ^ 2) ^ 3 := h2
            _ = C_K ^ 3 * (h ^ 3 * h ^ 3) := h3
            _ ≤ C_K ^ 3 * (h₀ ^ 3 * h ^ 3) := h4
      _ = |kappa| ^ 3 * C_K ^ 3 * h₀ ^ 3 * h ^ 3 := by ring
  calc |(n : ℝ) * Real.arsinh (kappa * δ h / n) - kappa * δ h|
      ≤ |kappa * δ h| ^ 3 / (6 * (n : ℝ) ^ 2) :=
        sourced_ratio_cubic_error n hn (kappa * δ h)
    _ ≤ (|kappa| ^ 3 * C_K ^ 3 * h₀ ^ 3 * h ^ 3) / (6 * (n : ℝ) ^ 2) := by
        have hden : (0 : ℝ) ≤ (6 * (n : ℝ) ^ 2)⁻¹ := by positivity
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hnum hden
    _ = |kappa| ^ 3 * C_K ^ 3 * h₀ ^ 3 / (6 * (n : ℝ) ^ 2) * h ^ 3 := by
        ring

/-! ## §8. The two-sided quadratic band (item 7) -/

/-- **THEOREM (item 7, two-sided quadratic band, constant cosh(r)/4).**
|J(exp u) - u^2/2| <= (cosh r / 4) * u^4 for |u| <= r. Generalizes the
radius of `Jcost_exp_sub_half_sq_abs_le` (which is the case r = 1 with
the numeric constant 1/2) via `cosh_remainder_le`. The spec's optional
sharper constant cosh(r)/24 was not pursued; the constant is recorded and
is not load-bearing. -/
theorem J_exp_quadratic_band (r u : ℝ) (hu : |u| ≤ r) :
    |Cost.Jcost (Real.exp u) - u ^ 2 / 2| ≤ Real.cosh r / 4 * u ^ 4 := by
  rw [Cost.Jcost_exp_cosh]
  have h0 := cosh_remainder_nonneg u
  have h1 := cosh_remainder_le u
  have hr0 : 0 ≤ r := le_trans (abs_nonneg u) hu
  have hcosh : Real.cosh u ≤ Real.cosh r := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hr0]
    exact hu
  rw [abs_of_nonneg h0]
  have h2 : u ^ 4 / 4 * Real.cosh u ≤ u ^ 4 / 4 * Real.cosh r :=
    mul_le_mul_of_nonneg_left hcosh (by positivity)
  nlinarith [h1, h2]

/-! ## §9. The envelope corollary (item 8)

The panel wants the derivative structure of the optimal value recorded;
it never promotes alone. The spec's suggested derivative
kappa * sinh(arsinh(kappa*delta/n)) for the cost term is not the
chain-rule value; the correct values are proved below and the correction
is recorded in the module header. -/

/-- The optimal VALUE of the sourced problem as a function of the deficit:
V(delta) = Phi(t*) = n*(cosh(arsinh(kappa*delta/n)) - 1)
- kappa*delta*arsinh(kappa*delta/n). -/
noncomputable def sourcedValue (n : ℕ) (kappa : ℝ) (d : ℝ) : ℝ :=
  (n : ℝ) * (Real.cosh (Real.arsinh (kappa * d / n)) - 1)
    - kappa * d * Real.arsinh (kappa * d / n)

/-- **THEOREM.** The optimal value function IS the sourced action
evaluated at its unique minimizer (with source c = kappa*d). -/
theorem sourcedValue_eq_action_min (n : ℕ) (hn : 1 ≤ n) (kappa d : ℝ) :
    sourcedValue n kappa d
      = sourcedAction n (kappa * d) (sourcedMinimizer n (kappa * d)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  unfold sourcedValue sourcedAction sourcedMinimizer
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  field_simp

/-- **THEOREM (chain-rule derivative of the optimal cost term).** The
derivative of delta ↦ n*(cosh(arsinh(kappa*delta/n)) - 1) is
kappa * tanh(arsinh(kappa*delta/n)) = kappa*(kappa*delta/n)/sqrt(1+(kappa*delta/n)^2).
This CORRECTS the spec's suggested value kappa*sinh(arsinh(.)): the
arsinh chain factor 1/sqrt(1+y^2) turns sinh into tanh. -/
theorem sourced_costTerm_hasDerivAt (n : ℕ) (hn : 1 ≤ n) (kappa d : ℝ) :
    HasDerivAt
      (fun z => (n : ℝ) * (Real.cosh (Real.arsinh (kappa * z / n)) - 1))
      (kappa * Real.tanh (Real.arsinh (kappa * d / n))) d := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hs_pos : 0 < Real.sqrt (1 + (kappa * d / n) ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hinner : HasDerivAt (fun z : ℝ => kappa * z / (n : ℝ))
      (kappa / n) d := by
    have h := ((hasDerivAt_id d).const_mul kappa).div_const (n : ℝ)
    simpa using h
  have harsinh := hinner.arsinh
  have hcosh := harsinh.cosh
  have htotal := (hcosh.sub_const 1).const_mul (n : ℝ)
  convert htotal using 1
  rw [Real.tanh_arsinh, smul_eq_mul, Real.sinh_arsinh]
  field_simp

/-- **THEOREM (item 8, the envelope corollary).** The optimal value
V(delta) of the sourced problem is differentiable in the deficit with
V'(delta) = -kappa * arsinh(kappa*delta/n): exactly the envelope-theorem
partial derivative of the MODEL coupling term
-(kappa*delta/n) * sum_i t_i at the minimizer t_i = arsinh(kappa*delta/n)
(the direct derivatives of the cost term cancel against the coupling
term's dependence through t*). Recorded per the panel; it never promotes
alone. -/
theorem valueFn_deriv (n : ℕ) (hn : 1 ≤ n) (kappa d : ℝ) :
    HasDerivAt (fun z => sourcedValue n kappa z)
      (-(kappa * Real.arsinh (kappa * d / n))) d := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hs_pos : 0 < Real.sqrt (1 + (kappa * d / n) ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hinner : HasDerivAt (fun z : ℝ => kappa * z / (n : ℝ))
      (kappa / n) d := by
    have h := ((hasDerivAt_id d).const_mul kappa).div_const (n : ℝ)
    simpa using h
  have harsinh := hinner.arsinh
  have hcosh := harsinh.cosh
  have hterm1 := (hcosh.sub_const 1).const_mul (n : ℝ)
  have hlin : HasDerivAt (fun z : ℝ => kappa * z) kappa d := by
    have h := (hasDerivAt_id d).const_mul kappa
    simpa using h
  have hterm2 := hlin.mul harsinh
  have htotal := hterm1.sub hterm2
  simp only [sourcedValue]
  convert htotal using 1
  rw [smul_eq_mul, Real.sinh_arsinh]
  field_simp
  ring

end SevenGaps
end Gravity
end IndisputableMonolith
