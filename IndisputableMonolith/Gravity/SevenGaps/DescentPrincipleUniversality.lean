import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.StrainDescent

/-!
# The descent principle: the metric is a choice, and the choice cannot matter

## The question

The carrier dynamics is a theorem: the gradient step on a hinge link's
strain space converges to the sourced least-cost carrier
(`StrainDescent`). That reduced the C2 stationarity premise to one
dynamical principle, that the substrate's strain state follows the steepest
descent of its total recognition cost. This module asks what that principle
actually costs, and answers in two parts.

## Part one: "steepest" names a family, not a map

Steepest descent is defined only relative to a metric on the strain space:
the flow of a cost `Φ` under a metric with positive weight `w` is
`ṫ = -w(t)·Φ'(t)`. Every positive `w` gives a flow with the same rest point
and the same descent sign, and different weights give different flows
(`metric_not_forced`: the Euclidean weight and the cost's own Hessian weight
`cosh` differ). So no derivation can single out "the" steepest descent
without first forcing a metric, and the metric is not fixed by the cost.

## Part two: the choice cannot matter

The reason this does not matter is the module's main theorem
(`cost_decreasing_dynamics_converges'`). Let `Φ` be the per-channel sourced
cost and `t* = arsinh a` its least-cost point. For **any** continuous map
`S` on the strain space with

* `Φ (S t) < Φ t` whenever `t ≠ t*` (the dynamics strictly spends cost off
  the least-cost state),

**every** orbit `S^[k] s₀` converges to `t*`, from every initial state.
No metric, no step size, no gradient, no convexity of `S`, and no rate.
The proof is a Lyapunov argument: the cost is coercive
(`sourceCost1_coercive`), so an orbit that never raises its cost is trapped
in a compact set; every limit point of the orbit has the same cost as its
own image, which by the descent hypothesis forces it to be `t*`.

That the least-cost state is a rest state is not a further assumption:
continuity plus descent forces it (`rest_state_forced`). Continuity is the
one hypothesis doing real work, and it is load-bearing rather than
decorative: `continuity_is_load_bearing` exhibits a discontinuous dynamics
that spends cost strictly off the least-cost state, yet abandons that state
and oscillates forever.

## What is proved (all THEOREM; 0 sorry, 0 admit, no new axiom, no
`native_decide`)

* `sourceCost1_hasDerivAt`, `deriv_sourceCost1`: the cost's derivative is
  the residual `sinh t - a`, that is the recognition phase minus the source.
* `self_le_sinh`, `one_add_sq_div_two_le_cosh`: the growth bounds, from the
  integral machinery of `StrainDescent`.
* `sourceCost1_strictAntiOn` / `sourceCost1_strictMonoOn` /
  `sourceCost1_lt_of_ne`: the cost falls to `t*` and rises after it, so
  `t*` is the strict global minimum.
* `sourceCost1_coercive`: an explicit `N` beyond which the cost exceeds any
  named level.
* `descentField_zero_iff`, `descentField_descends`, `metric_not_forced`:
  part one.
* `cost_decreasing_dynamics_converges` and its minimal form
  `cost_decreasing_dynamics_converges'`: part two, the main theorem.
* `rest_state_forced`, `continuity_is_load_bearing`: the hypothesis
  accounting for part two.
* `strainStep1_continuous` and `strainStep1_converges_by_universality`: the
  banked gradient step is an instance of the main theorem, so the theorem
  is not vacuous and its hypotheses are inhabited by a real dynamics.
* `descent_principle_residue`: the two hypotheses bundled as the exact
  remaining adoption.

## The honest verdict for (A3)

The premise the C2 bridge still adopts is not "steepest descent", and not a
metric, and not a rate. It is exactly this: **the substrate's dynamics is
continuous and spends recognition cost off the least-cost state.** Every
such dynamics reaches the sourced least-cost carrier. Whether that residue
is itself derivable from the recognition kernel, rather than adopted as the
framework's variational posture, is OPEN, and it is now stated in the
weakest form under which the bridge's conclusion still follows.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace StrainDescent

open Real Set Filter
open scoped Topology

noncomputable section

/-! ## §1. The per-channel cost: derivative, shape, growth -/

/-- The cost's derivative is the residual: the recognition phase minus the
source. -/
theorem sourceCost1_hasDerivAt (a s : ℝ) :
    HasDerivAt (sourceCost1 a) (strainResidual a s) s := by
  have h1 : HasDerivAt (fun s : ℝ => Real.cosh s - 1) (Real.sinh s) s :=
    (Real.hasDerivAt_cosh s).sub_const 1
  have h2 : HasDerivAt (fun s : ℝ => a * s) a s := by
    simpa using (hasDerivAt_id s).const_mul a
  have h := h1.sub h2
  simpa [sourceCost1, strainResidual] using h

theorem deriv_sourceCost1 (a : ℝ) : deriv (sourceCost1 a) = strainResidual a := by
  funext s
  exact (sourceCost1_hasDerivAt a s).deriv

theorem sourceCost1_continuous (a : ℝ) : Continuous (sourceCost1 a) := by
  unfold sourceCost1
  fun_prop

/-- For `x ≥ 0`, `x ≤ sinh x`: the integral of `cosh ≥ 1`. -/
theorem self_le_sinh {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.sinh x := by
  have hrepr : Real.sinh x - x = ∫ t in (0:ℝ)..x, (Real.cosh t - 1) := by
    rw [intervalIntegral.integral_sub
        (Real.continuous_cosh.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _),
      integral_cosh, intervalIntegral.integral_const]
    simp
  have hnn : (0:ℝ) ≤ ∫ t in (0:ℝ)..x, (Real.cosh t - 1) := by
    apply intervalIntegral.integral_nonneg hx
    intro t _
    have h1 : (1:ℝ) ≤ Real.cosh t := Real.one_le_cosh t
    simp [h1]
  linarith [hrepr, hnn]

/-- The quadratic lower bound `1 + x²/2 ≤ cosh x`, all `x`. -/
theorem one_add_sq_div_two_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have main : ∀ y : ℝ, 0 ≤ y → 1 + y ^ 2 / 2 ≤ Real.cosh y := by
    intro y hy
    have hrepr : Real.cosh y - 1 = ∫ t in (0:ℝ)..y, Real.sinh t := (integral_sinh y).symm
    have hmono : ∫ t in (0:ℝ)..y, (t : ℝ) ≤ ∫ t in (0:ℝ)..y, Real.sinh t := by
      apply intervalIntegral.integral_mono_on hy
        (continuous_id.intervalIntegrable _ _)
        (Real.continuous_sinh.intervalIntegrable _ _)
      intro t ht
      exact self_le_sinh ht.1
    rw [integral_id_half_sq] at hmono
    linarith [hrepr, hmono]
  rcases le_or_gt 0 x with hx | hx
  · exact main x hx
  · have h0 : 0 ≤ -x := le_of_lt (neg_pos.mpr hx)
    have h := main (-x) h0
    rw [Real.cosh_neg] at h
    norm_num at h
    exact h

/-- Every level of the cost is exceeded outside an explicit interval. -/
theorem sourceCost1_coercive (a c : ℝ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ t : ℝ, N ≤ |t| → c < sourceCost1 a t := by
  refine ⟨2 * (|a| + |c| + 2), by positivity, ?_⟩
  intro t ht
  have hq : |t| ^ 2 / 2 - |a| * |t| ≤ sourceCost1 a t := by
    have h1 := one_add_sq_div_two_le_cosh t
    have h2 : a * t ≤ |a| * |t| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h3 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    unfold sourceCost1
    linarith [h1, h2, h3]
  have habs : (0:ℝ) ≤ |t| := abs_nonneg t
  have hc : c ≤ |c| := le_abs_self c
  nlinarith [hq, ht, habs, hc, abs_nonneg a, abs_nonneg c]

/-- The cost strictly rises above the least-cost point. -/
theorem sourceCost1_strictMonoOn (a : ℝ) :
    StrictMonoOn (sourceCost1 a) (Ici (Real.arsinh a)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
    (sourceCost1_continuous a).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  rw [deriv_sourceCost1]
  unfold strainResidual
  have h : Real.sinh (Real.arsinh a) < Real.sinh x := Real.sinh_strictMono hx
  rw [Real.sinh_arsinh] at h
  linarith

/-- The cost strictly falls up to the least-cost point. -/
theorem sourceCost1_strictAntiOn (a : ℝ) :
    StrictAntiOn (sourceCost1 a) (Iic (Real.arsinh a)) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic _)
    (sourceCost1_continuous a).continuousOn
  intro x hx
  rw [interior_Iic] at hx
  rw [deriv_sourceCost1]
  unfold strainResidual
  have h : Real.sinh x < Real.sinh (Real.arsinh a) := Real.sinh_strictMono hx
  rw [Real.sinh_arsinh] at h
  linarith

/-- **THEOREM.** `arsinh a` is the strict global minimum of the cost. -/
theorem sourceCost1_lt_of_ne (a t : ℝ) (h : t ≠ Real.arsinh a) :
    sourceCost1 a (Real.arsinh a) < sourceCost1 a t := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact sourceCost1_strictAntiOn a (mem_Iic.mpr hlt.le) (mem_Iic.mpr le_rfl) hlt
  · exact sourceCost1_strictMonoOn a (mem_Ici.mpr le_rfl) (mem_Ici.mpr hgt.le) hgt

theorem sourceCost1_min_le (a t : ℝ) :
    sourceCost1 a (Real.arsinh a) ≤ sourceCost1 a t := by
  by_cases h : t = Real.arsinh a
  · rw [h]
  · exact (sourceCost1_lt_of_ne a t h).le

/-! ## §2. Part one: the metric is a choice -/

/-- The descent field of the cost under a metric with weight `w`:
`ṫ = -w(t)·Φ'(t)`. The Euclidean metric is `w = 1`; the cost's own Hessian
metric is `w = cosh`. -/
def descentField (w : ℝ → ℝ) (a : ℝ) : ℝ → ℝ :=
  fun t => -(w t) * strainResidual a t

/-- Every positive weight gives a field resting exactly at the least-cost
point. -/
theorem descentField_zero_iff {w : ℝ → ℝ} (hw : ∀ t, 0 < w t) (a t : ℝ) :
    descentField w a t = 0 ↔ t = Real.arsinh a := by
  unfold descentField
  constructor
  · intro h
    have hres : strainResidual a t = 0 := by
      rcases mul_eq_zero.mp h with h1 | h2
      · exact absurd h1 (by simpa using (hw t).ne')
      · exact h2
    unfold strainResidual at hres
    have : Real.sinh t = Real.sinh (Real.arsinh a) := by
      rw [Real.sinh_arsinh]
      linarith
    exact Real.sinh_injective this
  · intro h
    rw [h]
    unfold strainResidual
    rw [Real.sinh_arsinh]
    simp

/-- Every positive weight gives a field that never raises the cost: the
field and the cost's derivative always have opposite signs. -/
theorem descentField_descends {w : ℝ → ℝ} (hw : ∀ t, 0 < w t) (a t : ℝ) :
    deriv (sourceCost1 a) t * descentField w a t ≤ 0 := by
  rw [deriv_sourceCost1]
  unfold descentField
  have h : strainResidual a t * (-(w t) * strainResidual a t)
      = -(w t) * strainResidual a t ^ 2 := by ring
  rw [h]
  have h1 : (0:ℝ) ≤ w t * strainResidual a t ^ 2 :=
    mul_nonneg (hw t).le (sq_nonneg _)
  linarith

/-- **THEOREM (part one).** The metric is not forced: two positive weights,
the Euclidean one and the cost's own Hessian, give genuinely different
descent fields. So "steepest descent" names a family of dynamics, not one
map, and no derivation can produce a unique flow without first fixing a
metric. -/
theorem metric_not_forced :
    ∃ w₁ w₂ : ℝ → ℝ, (∀ t, 0 < w₁ t) ∧ (∀ t, 0 < w₂ t) ∧
      descentField w₁ 0 ≠ descentField w₂ 0 := by
  refine ⟨fun _ => 1, Real.cosh, fun _ => one_pos,
    fun t => lt_of_lt_of_le one_pos (Real.one_le_cosh t), ?_⟩
  intro hcon
  have h := congrFun hcon 1
  unfold descentField strainResidual at h
  simp only [sub_zero, neg_one_mul] at h
  -- h : -sinh 1 = -cosh 1 * sinh 1
  have hs : 0 < Real.sinh 1 := by
    have := self_le_sinh (show (0:ℝ) ≤ 1 by norm_num)
    linarith
  have hc : (1:ℝ) < Real.cosh 1 := by
    have := one_add_sq_div_two_le_cosh 1
    norm_num at this
    linarith
  nlinarith [h, hs, hc]

/-! ## §3. Part two: any cost-decreasing dynamics reaches the carrier -/

/-- **THEOREM (the main result).** Let `S` be any continuous dynamics on the
strain space that rests at the least-cost point and strictly spends cost
everywhere else. Then every orbit converges to the least-cost point.

No metric, no step size, no gradient structure, no rate, and no convexity
of `S` is assumed. This is what makes the metric choice of part one
irrelevant: every member of the steepest-descent family, and every other
cost-decreasing dynamics whatsoever, reaches the same carrier. -/
theorem cost_decreasing_dynamics_converges (a : ℝ) (S : ℝ → ℝ)
    (hcont : Continuous S)
    (hrest : S (Real.arsinh a) = Real.arsinh a)
    (hdesc : ∀ t, t ≠ Real.arsinh a → sourceCost1 a (S t) < sourceCost1 a t)
    (s₀ : ℝ) :
    Tendsto (fun k => S^[k] s₀) atTop (𝓝 (Real.arsinh a)) := by
  set tstar := Real.arsinh a with htstar
  set Φ := sourceCost1 a with hΦ
  set u : ℕ → ℝ := fun k => S^[k] s₀ with hu
  have hΦcont : Continuous Φ := sourceCost1_continuous a
  have hstep : ∀ k, u (k + 1) = S (u k) := by
    intro k
    simp [hu, Function.iterate_succ_apply']
  -- The cost never rises along an orbit.
  have hle : ∀ t, Φ (S t) ≤ Φ t := by
    intro t
    by_cases h : t = tstar
    · rw [h, hrest]
    · exact (hdesc t h).le
  have hanti : Antitone (fun k => Φ (u k)) := by
    apply antitone_nat_of_succ_le
    intro k
    rw [hstep k]
    exact hle (u k)
  have hlb : ∀ k, Φ tstar ≤ Φ (u k) := fun k => sourceCost1_min_le a (u k)
  have hbdd : BddBelow (range fun k => Φ (u k)) := ⟨Φ tstar, by
    rintro y ⟨k, rfl⟩
    exact hlb k⟩
  -- The cost along the orbit converges to some level L.
  set L := ⨅ k, Φ (u k) with hL
  have hconv : Tendsto (fun k => Φ (u k)) atTop (𝓝 L) :=
    tendsto_atTop_ciInf hanti hbdd
  -- The orbit is trapped in a compact interval.
  obtain ⟨N, hN0, hNc⟩ := sourceCost1_coercive a (Φ s₀)
  have hmem : ∀ k, u k ∈ Icc (-N) N := by
    intro k
    have hcost : Φ (u k) ≤ Φ s₀ := by
      have h0 : Φ (u 0) = Φ s₀ := by simp [hu]
      calc Φ (u k) ≤ Φ (u 0) := hanti (Nat.zero_le k)
        _ = Φ s₀ := h0
    have habs : |u k| < N := by
      by_contra hcon
      push_neg at hcon
      exact absurd hcost (not_le.mpr (hNc (u k) hcon))
    rw [mem_Icc]
    constructor
    · linarith [neg_abs_le (u k), habs]
    · linarith [le_abs_self (u k), habs]
  -- Every limit point of the orbit is the least-cost point.
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨z, hzmem, ms, hms, hlim⟩ :=
    isCompact_Icc.tendsto_subseq (x := fun n => u (ns n)) (fun n => hmem (ns n))
  have hidx : Tendsto (fun n => ns (ms n)) atTop atTop :=
    hns.comp hms.tendsto_atTop
  -- The subsequence's cost tends to both Φ z and L, so Φ z = L.
  have hΦz : Tendsto (fun n => Φ (u (ns (ms n)))) atTop (𝓝 (Φ z)) :=
    (hΦcont.tendsto z).comp hlim
  have hΦL : Tendsto (fun n => Φ (u (ns (ms n)))) atTop (𝓝 L) := hconv.comp hidx
  have hzL : Φ z = L := tendsto_nhds_unique hΦz hΦL
  -- The shifted subsequence's cost tends to both Φ (S z) and L.
  have hshiftlim : Tendsto (fun n => u (ns (ms n) + 1)) atTop (𝓝 (S z)) := by
    have : (fun n => u (ns (ms n) + 1)) = fun n => S (u (ns (ms n))) := by
      funext n
      exact hstep (ns (ms n))
    rw [this]
    exact (hcont.tendsto z).comp hlim
  have hΦSz : Tendsto (fun n => Φ (u (ns (ms n) + 1))) atTop (𝓝 (Φ (S z))) :=
    (hΦcont.tendsto (S z)).comp hshiftlim
  have hΦSL : Tendsto (fun n => Φ (u (ns (ms n) + 1))) atTop (𝓝 L) := by
    apply hconv.comp
    exact tendsto_atTop_mono (fun n => Nat.le_succ (ns (ms n))) hidx
  have hSzL : Φ (S z) = L := tendsto_nhds_unique hΦSz hΦSL
  -- Equal cost before and after the step forces the least-cost point.
  have hz : z = tstar := by
    by_contra hcon
    have := hdesc z hcon
    rw [hSzL, hzL] at this
    exact lt_irrefl L this
  rw [hz] at hlim
  exact ⟨ms, hlim⟩

/-! ## §3b. The rest state is not a separate assumption -/

/-- **THEOREM.** A continuous dynamics that spends cost off the least-cost
state must rest at it. So the rest hypothesis of the main theorem is not an
extra adoption: it is a consequence of the other two. -/
theorem rest_state_forced (a : ℝ) (S : ℝ → ℝ)
    (hcont : Continuous S)
    (hdesc : ∀ t, t ≠ Real.arsinh a → sourceCost1 a (S t) < sourceCost1 a t) :
    S (Real.arsinh a) = Real.arsinh a := by
  set tstar := Real.arsinh a with htstar
  set Φ := sourceCost1 a with hΦ
  have hΦcont : Continuous Φ := sourceCost1_continuous a
  set p : ℕ → ℝ := fun n => tstar + 1 / (n + 1) with hp
  have hpne : ∀ n, p n ≠ tstar := by
    intro n hcon
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [hp] at hcon
    linarith
  have hptend : Tendsto p atTop (𝓝 tstar) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [hp] using (tendsto_const_nhds (x := tstar) (f := atTop)).add h0
  have hA : Tendsto (fun n => Φ (S (p n))) atTop (𝓝 (Φ (S tstar))) :=
    ((hΦcont.comp hcont).tendsto tstar).comp hptend
  have hB : Tendsto (fun n => Φ (p n)) atTop (𝓝 (Φ tstar)) :=
    (hΦcont.tendsto tstar).comp hptend
  have hle : Φ (S tstar) ≤ Φ tstar :=
    le_of_tendsto_of_tendsto' hA hB (fun n => (hdesc (p n) (hpne n)).le)
  by_contra hcon
  exact absurd hle (not_le.mpr (sourceCost1_lt_of_ne a (S tstar) hcon))

/-- **THEOREM (the main result, minimal form).** Continuity plus strict cost
spending off the least-cost state is by itself enough: every orbit
converges to the sourced least-cost carrier. -/
theorem cost_decreasing_dynamics_converges' (a : ℝ) (S : ℝ → ℝ)
    (hcont : Continuous S)
    (hdesc : ∀ t, t ≠ Real.arsinh a → sourceCost1 a (S t) < sourceCost1 a t)
    (s₀ : ℝ) :
    Tendsto (fun k => S^[k] s₀) atTop (𝓝 (Real.arsinh a)) :=
  cost_decreasing_dynamics_converges a S hcont (rest_state_forced a S hcont hdesc)
    hdesc s₀

/-- **THEOREM.** Continuity is load-bearing, not decoration. Dropping it
breaks both the rest state and the conclusion: this dynamics spends cost
strictly off the least-cost state, yet abandons that state and oscillates
forever. -/
theorem continuity_is_load_bearing :
    ∃ S : ℝ → ℝ,
      (∀ t, t ≠ Real.arsinh 0 → sourceCost1 0 (S t) < sourceCost1 0 t) ∧
      S (Real.arsinh 0) ≠ Real.arsinh 0 ∧
      ¬ Tendsto (fun k => S^[k] (Real.arsinh 0)) atTop (𝓝 (Real.arsinh 0)) := by
  classical
  have harsinh : Real.arsinh 0 = 0 := by
    simpa using Real.arsinh_zero
  refine ⟨fun t => if t = 0 then 5 else 0, ?_, ?_, ?_⟩
  · intro t ht
    rw [harsinh] at ht
    have h2 : (1:ℝ) < Real.cosh t := by
      have hq := one_add_sq_div_two_le_cosh t
      have hsq : 0 < t ^ 2 := by positivity
      linarith
    have hgoal : sourceCost1 0 (0:ℝ) < sourceCost1 0 t := by
      unfold sourceCost1
      rw [Real.cosh_zero]
      linarith
    simpa only [if_neg ht] using hgoal
  · rw [harsinh]
    norm_num
  · rw [harsinh]
    intro hcon
    -- the orbit alternates 0, 5, 0, 5, ... so it also tends to 5
    have hodd : ∀ k : ℕ, (fun t : ℝ => if t = 0 then 5 else 0)^[2 * k + 1] 0 = 5 := by
      intro k
      induction k with
      | zero => norm_num
      | succ m ih =>
        have h2 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
        have hff : (fun t : ℝ => if t = 0 then 5 else 0)^[2] 0 = 0 := by norm_num
        rw [h2, Function.iterate_add_apply, hff, ih]
    have hidx : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
      tendsto_atTop_mono (fun k => by omega : ∀ k : ℕ, k ≤ 2 * k + 1) tendsto_id
    have hsub := hcon.comp hidx
    rw [Function.comp_def] at hsub
    simp only [hodd] at hsub
    have := tendsto_nhds_unique hsub (tendsto_const_nhds (x := (5:ℝ)) (f := atTop))
    norm_num at this

/-! ## §4. The banked gradient step is an instance -/

theorem strainResidual_continuous (a : ℝ) : Continuous (strainResidual a) := by
  unfold strainResidual
  fun_prop

theorem strainEnvelope_continuous (a : ℝ) : Continuous (strainEnvelope a) := by
  unfold strainEnvelope
  have h := strainResidual_continuous a
  fun_prop

theorem strainStepSize_continuous (a : ℝ) : Continuous (strainStepSize a) := by
  unfold strainStepSize
  exact (strainEnvelope_continuous a).inv₀ (fun s => (strainEnvelope_pos a s).ne')

/-- The banked gradient step is continuous. -/
theorem strainStep1_continuous (a : ℝ) : Continuous (strainStep1 a) := by
  unfold strainStep1
  exact continuous_id.sub
    ((strainStepSize_continuous a).mul (strainResidual_continuous a))

/-- **THEOREM.** The banked gradient step satisfies the main theorem's
hypotheses, so the theorem is inhabited by a real dynamics and its
conclusion reproduces the convergence proved directly in `StrainDescent`. -/
theorem strainStep1_converges_by_universality (a s₀ : ℝ) :
    Tendsto (fun k => (strainStep1 a)^[k] s₀) atTop (𝓝 (Real.arsinh a)) := by
  apply cost_decreasing_dynamics_converges a (strainStep1 a)
    (strainStep1_continuous a)
  · exact (step_fixed_iff_arsinh a (Real.arsinh a)).mpr rfl
  · intro t ht
    apply descent_one_dim_lt a t
    intro hres
    apply ht
    exact (step_fixed_iff_arsinh a t).mp (by
      unfold strainStep1
      rw [hres]
      ring)

/-! ## §5. The residue: what the C2 bridge still adopts -/

/-- **THEOREM (the exact remaining adoption).** The C2 stationarity premise
is discharged by exactly these three properties of the substrate's strain
dynamics: continuity, resting at least cost, and never gaining cost off
that rest state. Nothing about metrics, gradients, rates, or steepest
descent survives into the residue. -/
theorem descent_principle_residue (a : ℝ) (S : ℝ → ℝ)
    (hcont : Continuous S)
    (hrest : S (Real.arsinh a) = Real.arsinh a)
    (hdesc : ∀ t, t ≠ Real.arsinh a → sourceCost1 a (S t) < sourceCost1 a t) :
    ∀ s₀ : ℝ, Tendsto (fun k => S^[k] s₀) atTop (𝓝 (Real.arsinh a)) ∧
      (∀ k : ℕ, sourceCost1 a (S^[k + 1] s₀) ≤ sourceCost1 a (S^[k] s₀)) := by
  intro s₀
  refine ⟨cost_decreasing_dynamics_converges a S hcont hrest hdesc s₀, ?_⟩
  intro k
  rw [Function.iterate_succ_apply']
  by_cases h : (S^[k] s₀) = Real.arsinh a
  · rw [h, hrest]
  · exact (hdesc _ h).le

/-- The link's componentwise reading: each channel of a hinge reaches the
sourced minimizer under any cost-decreasing dynamics on its strain. -/
theorem link_channels_converge (n : ℕ) (c : ℝ) (S : ℝ → ℝ)
    (hcont : Continuous S)
    (hrest : S (Real.arsinh (c / n)) = Real.arsinh (c / n))
    (hdesc : ∀ t, t ≠ Real.arsinh (c / n) →
      sourceCost1 (c / n) (S t) < sourceCost1 (c / n) t)
    (t : Fin n → ℝ) (i : Fin n) :
    Tendsto (fun k => S^[k] (t i)) atTop (𝓝 (sourcedMinimizer n c i)) :=
  cost_decreasing_dynamics_converges (c / n) S hcont hrest hdesc (t i)

end

end StrainDescent
end SevenGaps
end Gravity
end IndisputableMonolith
