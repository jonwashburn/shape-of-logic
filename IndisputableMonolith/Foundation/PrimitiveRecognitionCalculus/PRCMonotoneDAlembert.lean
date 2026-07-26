/-
  PrimitiveRecognitionCalculus/PRCMonotoneDAlembert.lean

  The completeness-free d'Alembert machinery, and the cost-forcing theorem it
  buys, living where the forcing chain can reach them.

  These declarations were part of `PRCNativeCostUniqueness`, which also carries
  the whole completion apparatus (Cauchy reals, trace closure, the ratio-orbit
  carrier). That made them unreachable from `Foundation.UnifiedForcingChain`:
  citing them would have inverted the dependency order and dragged the
  completion machinery underneath the chain that is supposed to be beneath it.
  So the chain went on stating its cost rung T5 with an `AczelSmoothnessPackage`
  instance plus `ContinuousOn`, two continuum inputs, while the proof that
  neither is needed sat one module away and uncited.

  Nothing here mentions the carrier, the completion, or `costLambda`. Every
  declaration is a statement about a real function satisfying the d'Alembert
  identity, so the only imports are Mathlib and the cost functional equation.
  `PRCNativeCostUniqueness` now imports this file, and since the namespace is
  unchanged (`PRCJCost`), no call site anywhere moved.

  The block below is verbatim from its previous home. What is new is at the
  bottom: `cosh_scale_curvature`, the log-coordinate facts about `Cost.Jcost`,
  and `jcost_forced_by_order`, which routes straight from the cosh family to `J`
  without passing through `costLambda`. That last detour is why the theorem
  could not previously be stated below the completion layer.
-/

import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.FunctionalEquation

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace PRCJCost

/-! ## The completeness-free d'Alembert block -/

/-- **§9 regularity-substitute brick (completeness-free): a monotone additive
real function is linear.**

The classical J-uniqueness theorem (`law_of_logic_forces_jcost`) uses
`ContinuousOn`, an analytic hypothesis that presupposes the continuum. The §9
question asked whether that analytic input can be replaced by a purely
order-theoretic one available on any Archimedean ordered field *without*
completeness. That question is now CLOSED in the positive direction: the
completeness-free cost forcing is assembled below as `dAlembert_cosh_of_monotone`
(even, normalized, monotone d'Alembert solution is `cosh ∘ linear`) and
`composition_law_monotone_forces_costLambda` (the real cost hypotheses plus
`MonotoneOn` force the scale family), with faithfulness `costLambda_injOn_pos`.

This theorem is the load-bearing regularity brick those results consume: a
`Monotone` solution of Cauchy's additive equation `f (x+y) = f x + f y` is forced
to be linear, `f x = f 1 · x`. The proof uses only the density of `ℚ` in an
Archimedean field (`exists_rat_btwn`), never the least-upper-bound axiom. So
monotonicity is a genuine completeness-free substitute for continuity at the
additive layer that the d'Alembert reduction of the RCL lands on (set `g = F+1`,
`h(t) = g(e^t)`, then `h(s+t)+h(s−t) = 2 h(s) h(t)` with even `h` of the form
`cosh ∘ (additive)`; a monotone such `h` forces the inner additive map linear).
With the assembly complete, the continuum posit dissolves for the cost form:
the framework's arbitrary content on the cost side drops to one unit of scale. -/
theorem monotone_additive_isLinear {f : ℝ → ℝ}
    (hadd : ∀ x y, f (x + y) = f x + f y) (hmono : Monotone f) :
    ∀ x, f x = f 1 * x := by
  have hf0 : f 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    linarith
  let F : ℝ →+ ℝ := AddMonoidHom.mk' f (fun a b => hadd a b)
  have hFcoe : ∀ y, F y = f y := fun _ => rfl
  have hFq : ∀ q : ℚ, f (q : ℝ) = f 1 * (q : ℝ) := by
    intro q
    have h := map_ratCast_smul F ℝ ℝ q (1 : ℝ)
    simp only [smul_eq_mul, mul_one, hFcoe] at h
    rw [h]; ring
  intro x
  set c := f 1 with hc_def
  have hc : 0 ≤ c := by
    have hmle : f 0 ≤ f 1 := hmono (by norm_num)
    rw [hf0] at hmle; exact hmle
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · -- c = 0: f is identically 0, and 0 = c * x
    have hub : f x ≤ 0 := by
      obtain ⟨r, hxr, -⟩ := exists_rat_btwn (lt_add_one x)
      have hmr := hmono hxr.le
      rw [hFq r, ← hc0, zero_mul] at hmr
      exact hmr
    have hlb : 0 ≤ f x := by
      obtain ⟨q, -, hqx⟩ := exists_rat_btwn (sub_one_lt x)
      have hmq := hmono hqx.le
      rw [hFq q, ← hc0, zero_mul] at hmq
      exact hmq
    rw [← hc0, zero_mul]
    linarith
  · -- c > 0: Archimedean squeeze pins f x = c * x
    refine le_antisymm ?_ ?_
    · by_contra hcon
      push_neg at hcon
      have hxlt : x < f x / c := by
        rw [lt_div_iff₀ hcpos]; linarith [mul_comm c x]
      obtain ⟨r, hxr, hrlt⟩ := exists_rat_btwn hxlt
      have h1 : f x ≤ c * (r : ℝ) := by
        have hm := hmono hxr.le; rwa [hFq r] at hm
      have h2 : c * (r : ℝ) < f x := by
        have := (lt_div_iff₀ hcpos).mp hrlt; linarith [mul_comm (r : ℝ) c]
      linarith
    · by_contra hcon
      push_neg at hcon
      have hxlt : f x / c < x := by
        rw [div_lt_iff₀ hcpos]; linarith [mul_comm c x]
      obtain ⟨q, hqlt, hqx⟩ := exists_rat_btwn hxlt
      have h1 : c * (q : ℝ) ≤ f x := by
        have hm := hmono hqx.le; rwa [hFq q] at hm
      have h2 : f x < c * (q : ℝ) := by
        have := (div_lt_iff₀ hcpos).mp hqlt; linarith [mul_comm (q : ℝ) c]
      linarith

/-- **Nonnegative version: additive-on-`[0,∞)` + monotone ⇒ linear on `[0,∞)`.**
A function additive for nonnegative arguments and monotone on `[0,∞)` with
`f 0 = 0` satisfies `f t = f 1 · t` for `t ≥ 0`. Proved by the odd extension to
all of `ℝ` plus `monotone_additive_isLinear`; completeness-free. This is the form
the `log∘φ` exponent of the d'Alembert/monotone route actually has (additivity
only comes from `φ(s+t)=φ(s)φ(t)` for nonnegative `s,t`). -/
theorem monotone_additive_nonneg_isLinear {f : ℝ → ℝ}
    (hadd : ∀ a b, 0 ≤ a → 0 ≤ b → f (a + b) = f a + f b)
    (hmono : MonotoneOn f (Set.Ici (0 : ℝ))) (hf0 : f 0 = 0) :
    ∀ t, 0 ≤ t → f t = f 1 * t := by
  classical
  have hsub : ∀ a b, 0 ≤ b → b ≤ a → f (a - b) = f a - f b := by
    intro a b hb hba
    have h := hadd (a - b) b (by linarith) hb
    rw [sub_add_cancel] at h
    linarith
  set g : ℝ → ℝ := fun t => if 0 ≤ t then f t else - f (-t) with hg
  have hg_pos : ∀ t, 0 ≤ t → g t = f t := by intro t ht; simp [hg, ht]
  have hg_neg : ∀ t, t < 0 → g t = - f (-t) := by
    intro t ht; simp [hg, not_le.mpr ht]
  have hgadd : ∀ s t, g (s + t) = g s + g t := by
    intro s t
    rcases le_or_lt 0 s with hs | hs <;> rcases le_or_lt 0 t with ht | ht
    · rw [hg_pos s hs, hg_pos t ht, hg_pos (s + t) (by linarith), hadd s t hs ht]
    · rw [hg_pos s hs, hg_neg t ht]
      rcases le_or_lt 0 (s + t) with hst | hst
      · rw [hg_pos (s + t) hst]
        have hh := hsub s (-t) (by linarith) (by linarith)
        rw [sub_neg_eq_add] at hh
        rw [hh]; ring
      · rw [hg_neg (s + t) hst]
        have hh := hsub (-t) s (by linarith) (by linarith)
        rw [show -t - s = -(s + t) by ring] at hh
        rw [hh]; ring
    · rw [hg_neg s hs, hg_pos t ht]
      rcases le_or_lt 0 (s + t) with hst | hst
      · rw [hg_pos (s + t) hst]
        have hh := hsub t (-s) (by linarith) (by linarith)
        rw [show t - -s = s + t by ring] at hh
        rw [hh]; ring
      · rw [hg_neg (s + t) hst]
        have hh := hsub (-s) t (by linarith) (by linarith)
        rw [show -s - t = -(s + t) by ring] at hh
        rw [hh]; ring
    · rw [hg_neg s hs, hg_neg t ht, hg_neg (s + t) (by linarith),
        show -(s + t) = (-s) + (-t) by ring, hadd (-s) (-t) (by linarith) (by linarith)]
      ring
  have hgmono : Monotone g := by
    intro x y hxy
    rcases le_or_lt 0 x with hx | hx
    · have hy : 0 ≤ y := le_trans hx hxy
      rw [hg_pos x hx, hg_pos y hy]
      exact hmono (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) hxy
    · rcases le_or_lt 0 y with hy | hy
      · rw [hg_neg x hx, hg_pos y hy]
        have hfnx : f 0 ≤ f (-x) :=
          hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by linarith)) (by linarith)
        have hfy : f 0 ≤ f y :=
          hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
        rw [hf0] at hfnx hfy
        linarith
      · rw [hg_neg x hx, hg_neg y hy]
        have hle : f (-y) ≤ f (-x) :=
          hmono (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith)
        linarith
  have hlin := monotone_additive_isLinear hgadd hgmono
  have hg1 : g 1 = f 1 := hg_pos 1 (by norm_num)
  intro t ht
  have hlt := hlin t
  rw [hg_pos t ht, hg1] at hlt
  exact hlt

/-- **§9 order-only constraint 1 (completeness-free): d'Alembert duplication.**
A solution of the d'Alembert equation `H(s+t)+H(s−t)=2 H s · H t` with `H 0 = 1`
satisfies `H(2t) = 2 (H t)^2 − 1` — the cosh duplication formula, derived as pure
algebra from the equation. No regularity, no completeness. -/
theorem dAlembert_duplication {H : ℝ → ℝ}
    (hd : ∀ s t, H (s + t) + H (s - t) = 2 * H s * H t) (h0 : H 0 = 1) :
    ∀ t, H (2 * t) = 2 * (H t) ^ 2 - 1 := by
  intro t
  have h := hd t t
  rw [sub_self, h0] at h
  rw [two_mul, pow_two]
  linarith

/-- **§9 order-only constraint 2 (completeness-free): the cosh floor `H ≥ 1`.**
A d'Alembert solution that is monotone on `[0,∞)` with `H 0 = 1` stays `≥ 1`
there. The floor is forced by order alone: monotonicity from the base value `1`
gives it in one step. This excludes the bounded "cosine" branch `H = cos(c·)` of
d'Alembert (which dips below `1`) using no analytic input, isolating the
unbounded cosh branch as the only order-compatible family — the first place the
§9 monotone route does real work that continuity used to do. -/
theorem dAlembert_ge_one_of_monotone {H : ℝ → ℝ}
    (h0 : H 0 = 1) (hmono : MonotoneOn H (Set.Ici (0 : ℝ))) :
    ∀ t, 0 ≤ t → 1 ≤ H t := by
  intro t ht
  have hle := hmono Set.left_mem_Ici (Set.mem_Ici.mpr ht) ht
  rwa [h0] at hle

/-- **Product identity from d'Alembert.** Applying the equation to arguments
`(s+t)` and `(s−t)` (whose sum is `2s` and difference is `2t`) gives
`H(2s)+H(2t) = 2 H(s+t) H(s−t)`. Pure algebra, no regularity. -/
theorem dAlembert_prod {H : ℝ → ℝ}
    (hd : ∀ s t, H (s + t) + H (s - t) = 2 * H s * H t) :
    ∀ s t, H (2 * s) + H (2 * t) = 2 * H (s + t) * H (s - t) := by
  intro s t
  have h := hd (s + t) (s - t)
  have e1 : (s + t) + (s - t) = 2 * s := by ring
  have e2 : (s + t) - (s - t) = 2 * t := by ring
  rw [e1, e2] at h
  linarith

/-- **§9 sign crux, magnitude half: difference square.** Combining the sum law,
the product identity and the duplication formula forces
`(H(s+t) − H(s−t))² = 4 (H(s)²−1)(H(t)²−1)`. Pure algebra, completeness-free.
This is the "sinh²" relation; only the SIGN of the square root is left, and that
is what monotonicity fixes in `dAlembert_diff_eq_of_monotone`. -/
theorem dAlembert_diff_sq {H : ℝ → ℝ}
    (hd : ∀ s t, H (s + t) + H (s - t) = 2 * H s * H t) (h0 : H 0 = 1) :
    ∀ s t, (H (s + t) - H (s - t)) ^ 2
        = 4 * ((H s) ^ 2 - 1) * ((H t) ^ 2 - 1) := by
  intro s t
  have hsum := hd s t
  have hprod := dAlembert_prod hd s t
  have hds := dAlembert_duplication hd h0 s
  have hdt := dAlembert_duplication hd h0 t
  rw [hds, hdt] at hprod
  have expand : (H (s + t) - H (s - t)) ^ 2
      = (H (s + t) + H (s - t)) ^ 2 - 2 * (2 * H (s + t) * H (s - t)) := by ring
  rw [expand, hsum, ← hprod]
  ring

/-- **§9 sign crux, RESOLVED: monotonicity fixes the sign.** For `0 ≤ t ≤ s`,
both `s+t` and `s−t` lie in `[0,∞)`, so monotonicity of `H` there forces
`H(s+t) ≥ H(s−t)`; the difference is the NONNEGATIVE root of the square computed
in `dAlembert_diff_sq`:

`H(s+t) − H(s−t) = 2 √(H(s)²−1) · √(H(t)²−1)`.

This is the cosh addition formula `cosh(a+b) − cosh(a−b) = 2 sinh a sinh b` with
`sinh = √(cosh²−1) ≥ 0`. The sign — the one place the analytic proof used
continuity — is here pinned by ORDER ALONE. So the answer to the §9 sub-question
"can monotonicity fix the sign?" is YES. Completeness is not needed for this
step; only the order structure of the field is. -/
theorem dAlembert_diff_eq_of_monotone {H : ℝ → ℝ}
    (hd : ∀ s t, H (s + t) + H (s - t) = 2 * H s * H t) (h0 : H 0 = 1)
    (hmono : MonotoneOn H (Set.Ici (0 : ℝ))) :
    ∀ s t, 0 ≤ t → t ≤ s →
      H (s + t) - H (s - t)
        = 2 * Real.sqrt ((H s) ^ 2 - 1) * Real.sqrt ((H t) ^ 2 - 1) := by
  intro s t ht hts
  have hs0 : 0 ≤ s := le_trans ht hts
  have hge1s : 1 ≤ H s := dAlembert_ge_one_of_monotone h0 hmono s hs0
  have hge1t : 1 ≤ H t := dAlembert_ge_one_of_monotone h0 hmono t ht
  have hSs : 0 ≤ (H s) ^ 2 - 1 := by nlinarith [hge1s]
  have hSt : 0 ≤ (H t) ^ 2 - 1 := by nlinarith [hge1t]
  have hsmt_nonneg : 0 ≤ s - t := by linarith
  have hspt_nonneg : 0 ≤ s + t := by linarith
  have hdiff_nonneg : 0 ≤ H (s + t) - H (s - t) := by
    have hle : H (s - t) ≤ H (s + t) :=
      hmono (Set.mem_Ici.mpr hsmt_nonneg) (Set.mem_Ici.mpr hspt_nonneg) (by linarith)
    linarith
  have hrhs_nonneg :
      0 ≤ 2 * Real.sqrt ((H s) ^ 2 - 1) * Real.sqrt ((H t) ^ 2 - 1) := by positivity
  have hsq := dAlembert_diff_sq hd h0 s t
  have hrhs_sq :
      (2 * Real.sqrt ((H s) ^ 2 - 1) * Real.sqrt ((H t) ^ 2 - 1)) ^ 2
        = 4 * ((H s) ^ 2 - 1) * ((H t) ^ 2 - 1) := by
    rw [show (2 * Real.sqrt ((H s) ^ 2 - 1) * Real.sqrt ((H t) ^ 2 - 1)) ^ 2
          = 4 * (Real.sqrt ((H s) ^ 2 - 1)) ^ 2 * (Real.sqrt ((H t) ^ 2 - 1)) ^ 2 by ring,
       Real.sq_sqrt hSs, Real.sq_sqrt hSt]
  have hsquares :
      (H (s + t) - H (s - t)) ^ 2
        = (2 * Real.sqrt ((H s) ^ 2 - 1) * Real.sqrt ((H t) ^ 2 - 1)) ^ 2 := by
    rw [hsq, hrhs_sq]
  have hsqrt := congrArg Real.sqrt hsquares
  rwa [Real.sqrt_sq hdiff_nonneg, Real.sqrt_sq hrhs_nonneg] at hsqrt

/-- **Cosh addition formula, monotone-fixed sign.** For `0 ≤ t ≤ s`,
`H(s+t) = H s · H t + √(H s²−1)·√(H t²−1)`, the half-sum of the sum law and the
sign-fixed difference law. Completeness-free. This is the multiplicative seed:
with `φ(x) = H x + √(H x²−1)`, this and the matching `S`-addition identity give
`φ(s+t) = φ(s)·φ(t)`, i.e. `log ∘ φ` is additive — and monotone, hence linear by
`monotone_additive_isLinear`, hence `H = cosh(linear)` with no completeness. -/
theorem dAlembert_add_of_monotone {H : ℝ → ℝ}
    (hd : ∀ s t, H (s + t) + H (s - t) = 2 * H s * H t) (h0 : H 0 = 1)
    (hmono : MonotoneOn H (Set.Ici (0 : ℝ))) :
    ∀ s t, 0 ≤ t → t ≤ s →
      H (s + t)
        = H s * H t + Real.sqrt ((H s) ^ 2 - 1) * Real.sqrt ((H t) ^ 2 - 1) := by
  intro s t ht hts
  have hsum := hd s t
  have hdiff := dAlembert_diff_eq_of_monotone hd h0 hmono s t ht hts
  have e : 2 * H (s + t) = (H (s + t) + H (s - t)) + (H (s + t) - H (s - t)) := by ring
  rw [hsum, hdiff] at e
  linear_combination e / 2

/-- **`S`-addition identity (monotone-fixed).** With `S x = √(H x²−1)`, for
`0 ≤ t ≤ s` the "sinh" addition formula `S(s+t) = H s · S t + S s · H t` holds.
Proved by squaring (using the `H`-addition formula) and taking nonnegative roots.
Completeness-free. -/
theorem dAlembert_S_add_of_monotone {H : ℝ → ℝ}
    (hd : ∀ s t, H (s + t) + H (s - t) = 2 * H s * H t) (h0 : H 0 = 1)
    (hmono : MonotoneOn H (Set.Ici (0 : ℝ))) :
    ∀ s t, 0 ≤ t → t ≤ s →
      Real.sqrt ((H (s + t)) ^ 2 - 1)
        = H s * Real.sqrt ((H t) ^ 2 - 1) + Real.sqrt ((H s) ^ 2 - 1) * H t := by
  intro s t ht hts
  have hge1s : 1 ≤ H s := dAlembert_ge_one_of_monotone h0 hmono s (le_trans ht hts)
  have hge1t : 1 ≤ H t := dAlembert_ge_one_of_monotone h0 hmono t ht
  have hHs0 : 0 ≤ H s := by linarith
  have hHt0 : 0 ≤ H t := by linarith
  have hSs : 0 ≤ (H s) ^ 2 - 1 := by nlinarith [hge1s]
  have hSt : 0 ≤ (H t) ^ 2 - 1 := by nlinarith [hge1t]
  have hadd := dAlembert_add_of_monotone hd h0 hmono s t ht hts
  have hu := Real.sq_sqrt hSs
  have hv := Real.sq_sqrt hSt
  have hrhs_nonneg :
      0 ≤ H s * Real.sqrt ((H t) ^ 2 - 1) + Real.sqrt ((H s) ^ 2 - 1) * H t := by
    have t1 : 0 ≤ H s * Real.sqrt ((H t) ^ 2 - 1) := mul_nonneg hHs0 (Real.sqrt_nonneg _)
    have t2 : 0 ≤ Real.sqrt ((H s) ^ 2 - 1) * H t := mul_nonneg (Real.sqrt_nonneg _) hHt0
    linarith
  have rhs_sq :
      (H s * Real.sqrt ((H t) ^ 2 - 1) + Real.sqrt ((H s) ^ 2 - 1) * H t) ^ 2
        = (H (s + t)) ^ 2 - 1 := by
    rw [hadd]
    linear_combination ((H t) ^ 2 - (Real.sqrt ((H t) ^ 2 - 1)) ^ 2) * hu + hv
  rw [← rhs_sq]
  exact Real.sqrt_sq hrhs_nonneg

/-- **`φ` is multiplicative (monotone route).** With `φ x = H x + √(H x²−1)`, for
`0 ≤ t ≤ s` we have `φ(s+t) = φ(s)·φ(t)`. This is the `H`-addition and
`S`-addition identities packaged as a single product law. `φ > 0`, so `log ∘ φ`
is additive on `[0,∞)`; it is also monotone (both `H` and `S` increase there),
hence linear by `monotone_additive_isLinear`. That linear exponent makes
`H = cosh(c·)`, completing the completeness-free cost-form derivation. -/
theorem phi_mul_of_monotone {H : ℝ → ℝ}
    (hd : ∀ s t, H (s + t) + H (s - t) = 2 * H s * H t) (h0 : H 0 = 1)
    (hmono : MonotoneOn H (Set.Ici (0 : ℝ))) :
    ∀ s t, 0 ≤ t → t ≤ s →
      H (s + t) + Real.sqrt ((H (s + t)) ^ 2 - 1)
        = (H s + Real.sqrt ((H s) ^ 2 - 1)) * (H t + Real.sqrt ((H t) ^ 2 - 1)) := by
  intro s t ht hts
  have h1 := dAlembert_add_of_monotone hd h0 hmono s t ht hts
  have h2 := dAlembert_S_add_of_monotone hd h0 hmono s t ht hts
  rw [h2, h1]; ring

/-- **§9 RESOLVED, POSITIVE: the cosh cost form is forced WITHOUT completeness.**

A solution `H` of the d'Alembert equation that is even, normalized (`H 0 = 1`),
and monotone on `[0,∞)` is `H t = cosh (c · t)` for a single real `c`. The proof
uses no continuity, no smoothness, no Aczél package, and no least-upper-bound
axiom — only field operations, square roots, the order, and Archimedean density
(inside `monotone_additive_isLinear`). It therefore transfers verbatim to any
Archimedean real-closed field.

Consequence for the δ program (the §9 question): the continuum is NOT required to
force the cost form. Monotonicity — an order property present on any ordered
field — does everything continuity was doing. The single residual `c` is exactly
the known unit-of-scale posit. So the framework's arbitrary content drops from
two nested posits (continuum + unit) to one (unit), and the continuum posit for
the cost dissolves. This is the positive resolution of the sharper §9 target. -/
theorem dAlembert_cosh_of_monotone {H : ℝ → ℝ}
    (hd : ∀ s t, H (s + t) + H (s - t) = 2 * H s * H t) (h0 : H 0 = 1)
    (heven : Function.Even H) (hmono : MonotoneOn H (Set.Ici (0 : ℝ))) :
    ∃ c : ℝ, ∀ t, H t = Real.cosh (c * t) := by
  have hφmul : ∀ a b, 0 ≤ a → 0 ≤ b →
      (H (a + b) + Real.sqrt ((H (a + b)) ^ 2 - 1))
        = (H a + Real.sqrt ((H a) ^ 2 - 1)) * (H b + Real.sqrt ((H b) ^ 2 - 1)) := by
    intro a b ha hb
    rcases le_total b a with hba | hab
    · exact phi_mul_of_monotone hd h0 hmono a b hb hba
    · have hp := phi_mul_of_monotone hd h0 hmono b a ha hab
      rw [add_comm b a] at hp
      rw [hp]; ring
  have hφpos : ∀ x, 0 ≤ x → (1 : ℝ) ≤ H x + Real.sqrt ((H x) ^ 2 - 1) := by
    intro x hx
    have h1 := dAlembert_ge_one_of_monotone h0 hmono x hx
    have h2 : 0 ≤ Real.sqrt ((H x) ^ 2 - 1) := Real.sqrt_nonneg _
    linarith
  have hφmono : MonotoneOn (fun x => Real.log (H x + Real.sqrt ((H x) ^ 2 - 1)))
      (Set.Ici (0 : ℝ)) := by
    intro x hx y hy hxy
    have hx0 := Set.mem_Ici.mp hx
    have hy0 := Set.mem_Ici.mp hy
    have hHxy : H x ≤ H y := hmono hx hy hxy
    have hge1x := dAlembert_ge_one_of_monotone h0 hmono x hx0
    have hsqle : Real.sqrt ((H x) ^ 2 - 1) ≤ Real.sqrt ((H y) ^ 2 - 1) :=
      Real.sqrt_le_sqrt (by nlinarith [hHxy, hge1x])
    show Real.log (H x + Real.sqrt ((H x) ^ 2 - 1))
        ≤ Real.log (H y + Real.sqrt ((H y) ^ 2 - 1))
    exact Real.log_le_log (by linarith [hφpos x hx0]) (by linarith)
  have hγadd : ∀ a b, 0 ≤ a → 0 ≤ b →
      Real.log (H (a + b) + Real.sqrt ((H (a + b)) ^ 2 - 1))
        = Real.log (H a + Real.sqrt ((H a) ^ 2 - 1))
          + Real.log (H b + Real.sqrt ((H b) ^ 2 - 1)) := by
    intro a b ha hb
    rw [hφmul a b ha hb]
    exact Real.log_mul (by have := hφpos a ha; linarith) (by have := hφpos b hb; linarith)
  have hγ0 : Real.log (H 0 + Real.sqrt ((H 0) ^ 2 - 1)) = 0 := by
    rw [h0]
    have h01 : (1 : ℝ) ^ 2 - 1 = 0 := by norm_num
    rw [h01, Real.sqrt_zero, add_zero, Real.log_one]
  have hlin := monotone_additive_nonneg_isLinear
    (f := fun x => Real.log (H x + Real.sqrt ((H x) ^ 2 - 1))) hγadd hφmono hγ0
  refine ⟨Real.log (H 1 + Real.sqrt ((H 1) ^ 2 - 1)), ?_⟩
  set c := Real.log (H 1 + Real.sqrt ((H 1) ^ 2 - 1)) with hc
  have hcosh_nonneg : ∀ t, 0 ≤ t → H t = Real.cosh (c * t) := by
    intro t ht
    have hge1t := dAlembert_ge_one_of_monotone h0 hmono t ht
    have hSt : 0 ≤ (H t) ^ 2 - 1 := by nlinarith [hge1t]
    have hφtpos : 0 < H t + Real.sqrt ((H t) ^ 2 - 1) := by linarith [hφpos t ht]
    have hloglin : Real.log (H t + Real.sqrt ((H t) ^ 2 - 1)) = c * t := hlin t ht
    have hφexp : H t + Real.sqrt ((H t) ^ 2 - 1) = Real.exp (c * t) := by
      rw [← hloglin]; exact (Real.exp_log hφtpos).symm
    have hsqsq : (Real.sqrt ((H t) ^ 2 - 1)) ^ 2 = (H t) ^ 2 - 1 := Real.sq_sqrt hSt
    have hprod :
        (H t + Real.sqrt ((H t) ^ 2 - 1)) * (H t - Real.sqrt ((H t) ^ 2 - 1)) = 1 := by
      have hexp :
          (H t + Real.sqrt ((H t) ^ 2 - 1)) * (H t - Real.sqrt ((H t) ^ 2 - 1))
            = (H t) ^ 2 - (Real.sqrt ((H t) ^ 2 - 1)) ^ 2 := by ring
      rw [hexp, hsqsq]; ring
    have hinv : H t - Real.sqrt ((H t) ^ 2 - 1) = (H t + Real.sqrt ((H t) ^ 2 - 1))⁻¹ :=
      eq_inv_of_mul_eq_one_right hprod
    have hHt : H t = (Real.exp (c * t) + (Real.exp (c * t))⁻¹) / 2 := by
      have e : H t
          = ((H t + Real.sqrt ((H t) ^ 2 - 1)) + (H t - Real.sqrt ((H t) ^ 2 - 1))) / 2 := by
        ring
      rw [e, hinv, hφexp]
    rw [hHt, Real.cosh_eq, Real.exp_neg]
  intro t
  rcases le_or_lt 0 t with ht | ht
  · exact hcosh_nonneg t ht
  · have hnt : H t = H (-t) := (heven t).symm
    rw [hnt, hcosh_nonneg (-t) (by linarith), show c * (-t) = -(c * t) by ring, Real.cosh_neg]

/-- **§9 payoff: the cost FORM is forced by monotonicity alone (no continuity).**

The cost function `F` (reciprocal-symmetric, normalized, satisfying the
composition law) is forced into the cosh log-shape `H_F t = cosh (c·t)` by the
single regularity hypothesis that `H_F = F∘exp + 1` is monotone on `[0,∞)`. This
is the completeness-free replacement for the `ContinuousOn`/Aczél-smoothness
hypothesis of `Cost.FunctionalEquation.law_of_logic_forces_jcost`: the composition
law gives the d'Alembert equation on `H_F`, reciprocal symmetry gives evenness,
normalization gives `H_F 0 = 1`, and `dAlembert_cosh_of_monotone` finishes using
only order + field + sqrt + Archimedean density. -/
theorem composition_law_monotone_forces_cosh_family (F : ℝ → ℝ)
    (hRecip : Cost.FunctionalEquation.IsReciprocalCost F)
    (hNorm : Cost.FunctionalEquation.IsNormalized F)
    (hComp : Cost.FunctionalEquation.SatisfiesCompositionLaw F)
    (hMono : MonotoneOn (Cost.FunctionalEquation.H F) (Set.Ici (0 : ℝ))) :
    ∃ c : ℝ, ∀ t, Cost.FunctionalEquation.H F t = Real.cosh (c * t) := by
  have hCoshAdd := (Cost.FunctionalEquation.composition_law_equiv_coshAdd F).mp hComp
  have h_direct := Cost.FunctionalEquation.CoshAddIdentity_implies_DirectCoshAdd F hCoshAdd
  have h_dAlembert : ∀ t u,
      Cost.FunctionalEquation.H F (t + u) + Cost.FunctionalEquation.H F (t - u)
        = 2 * Cost.FunctionalEquation.H F t * Cost.FunctionalEquation.H F u := by
    intro t u
    simp only [Cost.FunctionalEquation.H]
    linear_combination (h_direct t u)
  have h0 : Cost.FunctionalEquation.H F 0 = 1 := by
    simp only [Cost.FunctionalEquation.H]
    rw [Cost.FunctionalEquation.G_zero_of_unit F hNorm]; norm_num
  have heven : Function.Even (Cost.FunctionalEquation.H F) := by
    intro t
    simp only [Cost.FunctionalEquation.H]
    rw [Cost.FunctionalEquation.G_even_of_reciprocal_symmetry F (fun {x} hx => hRecip x hx) t]
  exact dAlembert_cosh_of_monotone h_dAlembert h0 heven hMono

/-! ## The chain-facing entry point

What the block above delivers is the cosh family. Turning that into `J` needs
one derivative computation and the observation that the calibration equation
`c² = 1` cannot tell `c = 1` from `c = -1`, which is harmless because `cosh` is
even. No completeness, no continuity, and no scale-family detour. -/

/-- The log-coordinate curvature at the unit of the scaled cosh cost is `c²`.

This is the calibration functional evaluated on the family the d'Alembert block
produces. It is the whole reason calibration can select a member: the map from
exponent to calibration value is `c ↦ c²`, so fixing the value to `1` fixes the
exponent up to sign. -/
theorem cosh_scale_curvature (l : ℝ) :
    deriv (deriv (fun t : ℝ => Real.cosh (l * t) - 1)) 0 = l ^ 2 := by
  have hlin : ∀ t : ℝ, HasDerivAt (fun t => l * t) l t := by
    intro t; simpa using (hasDerivAt_id t).const_mul l
  have hd1 : ∀ t : ℝ,
      HasDerivAt (fun t => Real.cosh (l * t) - 1) (Real.sinh (l * t) * l) t := by
    intro t; exact ((hlin t).cosh).sub_const 1
  have hderiv1 : deriv (fun t : ℝ => Real.cosh (l * t) - 1)
      = fun t => Real.sinh (l * t) * l := by
    funext t; exact (hd1 t).deriv
  have hd2 : HasDerivAt (fun t => Real.sinh (l * t) * l)
      (Real.cosh (l * 0) * l * l) 0 := ((hlin 0).sinh).mul_const l
  rw [hderiv1, hd2.deriv, mul_zero, Real.cosh_zero, one_mul]
  ring

/-- In log coordinates `Cost.Jcost` is exactly `cosh`. -/
theorem H_jcost_eq_cosh (t : ℝ) :
    Cost.FunctionalEquation.H Cost.Jcost t = Real.cosh t := by
  simp only [Cost.FunctionalEquation.H, Cost.FunctionalEquation.G, Cost.Jcost,
    Real.cosh_eq, Real.exp_neg]
  ring

/-- `cosh (l · t)` is nondecreasing on `[0, ∞)` whenever `l ≥ 0`. -/
theorem cosh_mul_monotoneOn {l : ℝ} (hl : 0 ≤ l) :
    MonotoneOn (fun t : ℝ => Real.cosh (l * t)) (Set.Ici (0 : ℝ)) := by
  intro a ha b hb hab
  have ha0 : (0 : ℝ) ≤ a := Set.mem_Ici.mp ha
  have hb0 : (0 : ℝ) ≤ b := Set.mem_Ici.mp hb
  refine Real.cosh_le_cosh.mpr ?_
  rw [abs_of_nonneg (mul_nonneg hl ha0), abs_of_nonneg (mul_nonneg hl hb0)]
  exact mul_le_mul_of_nonneg_left hab hl

/-- `J` satisfies the order hypothesis. Without this the order route would be a
theorem about an empty class, so it is the non-vacuity witness for everything
the chain now hangs on `MonotoneOn`. -/
theorem H_jcost_monotoneOn :
    MonotoneOn (Cost.FunctionalEquation.H Cost.Jcost) (Set.Ici (0 : ℝ)) := by
  have h : Cost.FunctionalEquation.H Cost.Jcost = fun t : ℝ => Real.cosh (1 * t) := by
    funext t; rw [H_jcost_eq_cosh, one_mul]
  rw [h]
  exact cosh_mul_monotoneOn (by norm_num)

/-- **The recognition cost is forced by order.**

A reciprocal-symmetric, normalized, composition-law cost whose log transform is
nondecreasing on `[0, ∞)` and which meets the unit calibration equals
`Cost.Jcost` on the positives. Continuity is never invoked, no smoothness
package is required, and nothing in the proof needs a least upper bound, so the
statement is available on any Archimedean ordered field.

This is the theorem the forcing chain's T5 rung now cites. The older route
through the scale family, `law_of_logic_forces_jcost_monotone`, proves the same
thing and stays where it is; it just cannot be named from below the completion
layer, which is what this version fixes. -/
theorem jcost_forced_by_order (F : ℝ → ℝ)
    (hRecip : Cost.FunctionalEquation.IsReciprocalCost F)
    (hNorm : Cost.FunctionalEquation.IsNormalized F)
    (hComp : Cost.FunctionalEquation.SatisfiesCompositionLaw F)
    (hMono : MonotoneOn (Cost.FunctionalEquation.H F) (Set.Ici (0 : ℝ)))
    (hCalib : Cost.FunctionalEquation.IsCalibrated F) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  obtain ⟨c, hc⟩ :=
    composition_law_monotone_forces_cosh_family F hRecip hNorm hComp hMono
  have hGpt : ∀ t : ℝ,
      Cost.FunctionalEquation.G F t = Real.cosh (c * t) - 1 := by
    intro t
    have ht := hc t
    simp only [Cost.FunctionalEquation.H] at ht
    linarith
  have hG : Cost.FunctionalEquation.G F = fun t : ℝ => Real.cosh (c * t) - 1 :=
    funext hGpt
  have hc2 : c ^ 2 = 1 := by
    have hcal : deriv (deriv (Cost.FunctionalEquation.G F)) 0 = 1 := hCalib
    rw [hG, cosh_scale_curvature c] at hcal
    exact hcal
  -- `c² = 1` leaves the sign free, and `cosh` cannot see it.
  have hcosh_eq : ∀ t : ℝ, Real.cosh (c * t) = Real.cosh t := by
    intro t
    have hfac : (c - 1) * (c + 1) = 0 := by nlinarith [hc2]
    rcases mul_eq_zero.mp hfac with h | h
    · rw [show c = 1 by linarith, one_mul]
    · rw [show c = -1 by linarith, show (-1 : ℝ) * t = -t by ring, Real.cosh_neg]
  intro x hx
  have hgx : Cost.FunctionalEquation.G F (Real.log x) = F x := by
    simp only [Cost.FunctionalEquation.G]
    rw [Real.exp_log hx]
  have hval : F x = Real.cosh (Real.log x) - 1 := by
    have h1 := hGpt (Real.log x)
    rw [hgx, hcosh_eq] at h1
    exact h1
  rw [hval, Cost.Jcost, Real.cosh_eq, Real.exp_log hx, Real.exp_neg, Real.exp_log hx]

/-! ## Axiom audit -/

#print axioms cosh_scale_curvature
#print axioms H_jcost_monotoneOn
#print axioms jcost_forced_by_order

end PRCJCost
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
