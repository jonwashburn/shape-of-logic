import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.Convexity

/-!
# Path Space and the J-Action Functional

This module sets up the variational stage for the principle of least action
derived from the d'Alembert cost functional `J`. It defines:

* `AdmissiblePath a b`: continuous, strictly positive paths on `[a, b]`,
* `actionJ γ`: the J-action `∫ J(γ(t)) dt`,
* `fixedEndpoints γ₁ γ₂`: the boundary-condition relation,
* `interp γ₁ γ₂ s`: the straight-line interpolation in path space.

Paper companion: `papers/RS_Least_Action.tex`.

The crucial structural fact, recorded here, is that admissible paths are
closed under convex interpolation: if `γ₁` and `γ₂` are positive on `[a,b]`,
so is any `(1-s) γ₁ + s γ₂` with `s ∈ [0,1]`. This is what enables the
strict-convexity argument of `Action.FunctionalConvexity` to work without
any extra positivity hypothesis.
-/

namespace IndisputableMonolith
namespace Action

open Real Set MeasureTheory IndisputableMonolith.Cost

/-! ## Admissible paths -/

/-- An admissible path on `[a, b]` is a continuous, strictly positive function. -/
structure AdmissiblePath (a b : ℝ) where
  /-- The underlying function. -/
  toFun : ℝ → ℝ
  /-- Continuity on the closed interval. -/
  cont : ContinuousOn toFun (Icc a b)
  /-- Strict positivity on the closed interval. -/
  pos : ∀ t ∈ Icc a b, 0 < toFun t

namespace AdmissiblePath

variable {a b : ℝ}

instance : CoeFun (AdmissiblePath a b) (fun _ => ℝ → ℝ) := ⟨AdmissiblePath.toFun⟩

@[simp] lemma coe_mk (f : ℝ → ℝ) (hc : ContinuousOn f (Icc a b))
    (hp : ∀ t ∈ Icc a b, 0 < f t) :
    (⟨f, hc, hp⟩ : AdmissiblePath a b).toFun = f := rfl

/-- The constant path at value `c > 0`. -/
def const (a b c : ℝ) (hc : 0 < c) : AdmissiblePath a b where
  toFun := fun _ => c
  cont := continuousOn_const
  pos := fun _ _ => hc

@[simp] lemma const_apply {a b c : ℝ} (hc : 0 < c) (t : ℝ) :
    (const a b c hc).toFun t = c := rfl

end AdmissiblePath

/-! ## The J-action functional -/

/-- The J-action functional `S[γ] = ∫_a^b J(γ(t)) dt`.

    This is the central object of the variational principle. Geodesics of
    the Hessian metric `g(x) = J''(x) = 1/x³` minimize this functional
    among admissible paths with fixed endpoints. -/
noncomputable def actionJ {a b : ℝ} (γ : AdmissiblePath a b) : ℝ :=
  ∫ t in a..b, Jcost (γ.toFun t)

@[simp] lemma actionJ_def {a b : ℝ} (γ : AdmissiblePath a b) :
    actionJ γ = ∫ t in a..b, Jcost (γ.toFun t) := rfl

/-- The action of any admissible path is non-negative. -/
lemma actionJ_nonneg {a b : ℝ} (hab : a ≤ b) (γ : AdmissiblePath a b) :
    0 ≤ actionJ γ := by
  unfold actionJ
  exact intervalIntegral.integral_nonneg hab
    (fun t ht => Jcost_nonneg (γ.pos t ht))

/-- The action of the constant path at `1` (the cost-minimum) vanishes. -/
lemma actionJ_const_one {a b : ℝ} :
    actionJ (AdmissiblePath.const a b 1 one_pos) = 0 := by
  unfold actionJ
  simp [AdmissiblePath.const_apply, Jcost_unit0]

/-! ## Fixed endpoints -/

/-- Two admissible paths share endpoints. -/
def fixedEndpoints {a b : ℝ} (γ₁ γ₂ : AdmissiblePath a b) : Prop :=
  γ₁.toFun a = γ₂.toFun a ∧ γ₁.toFun b = γ₂.toFun b

lemma fixedEndpoints_refl {a b : ℝ} (γ : AdmissiblePath a b) :
    fixedEndpoints γ γ := And.intro rfl rfl

lemma fixedEndpoints_symm {a b : ℝ} {γ₁ γ₂ : AdmissiblePath a b}
    (h : fixedEndpoints γ₁ γ₂) : fixedEndpoints γ₂ γ₁ :=
  ⟨h.1.symm, h.2.symm⟩

lemma fixedEndpoints_trans {a b : ℝ} {γ₁ γ₂ γ₃ : AdmissiblePath a b}
    (h₁ : fixedEndpoints γ₁ γ₂) (h₂ : fixedEndpoints γ₂ γ₃) :
    fixedEndpoints γ₁ γ₃ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-! ## Convex interpolation in path space -/

/-- The straight-line interpolation between two admissible paths.

    `interp γ₁ γ₂ s = (1 - s) · γ₁ + s · γ₂`.

    The key structural fact is that for `s ∈ [0,1]`, this convex combination
    is again strictly positive and continuous, hence again admissible. -/
def interp {a b : ℝ} (γ₁ γ₂ : AdmissiblePath a b) (s : ℝ)
    (hs : s ∈ Icc (0:ℝ) 1) : AdmissiblePath a b where
  toFun := fun t => (1 - s) * γ₁.toFun t + s * γ₂.toFun t
  cont := by
    have h1 : ContinuousOn (fun t => (1 - s) * γ₁.toFun t) (Icc a b) :=
      γ₁.cont.const_smul (1 - s) |>.congr (fun _ _ => by simp [smul_eq_mul])
    have h2 : ContinuousOn (fun t => s * γ₂.toFun t) (Icc a b) :=
      γ₂.cont.const_smul s |>.congr (fun _ _ => by simp [smul_eq_mul])
    exact h1.add h2
  pos := by
    intro t ht
    have h1s : 0 ≤ 1 - s := by linarith [hs.2]
    have hs' : 0 ≤ s := hs.1
    have hp1 : 0 < γ₁.toFun t := γ₁.pos t ht
    have hp2 : 0 < γ₂.toFun t := γ₂.pos t ht
    -- Either s = 0 (LHS pure γ₁), or s > 0 (RHS strictly positive). Either way > 0.
    rcases lt_or_eq_of_le hs' with hs_pos | hs_zero
    · have := mul_pos hs_pos hp2
      have hnn : 0 ≤ (1 - s) * γ₁.toFun t := mul_nonneg h1s hp1.le
      linarith
    · -- s = 0: the combination is 1 · γ₁ + 0 · γ₂ = γ₁
      simp [← hs_zero, hp1]

@[simp] lemma interp_apply {a b : ℝ} (γ₁ γ₂ : AdmissiblePath a b) (s : ℝ)
    (hs : s ∈ Icc (0:ℝ) 1) (t : ℝ) :
    (interp γ₁ γ₂ s hs).toFun t = (1 - s) * γ₁.toFun t + s * γ₂.toFun t := rfl

/-- Interpolation at `s = 0` is the first path. -/
lemma interp_zero {a b : ℝ} (γ₁ γ₂ : AdmissiblePath a b) :
    ∀ t, (interp γ₁ γ₂ 0 ⟨le_refl 0, by norm_num⟩).toFun t = γ₁.toFun t := by
  intro t; simp [interp_apply]

/-- Interpolation at `s = 1` is the second path. -/
lemma interp_one {a b : ℝ} (γ₁ γ₂ : AdmissiblePath a b) :
    ∀ t, (interp γ₁ γ₂ 1 ⟨by norm_num, le_refl 1⟩).toFun t = γ₂.toFun t := by
  intro t; simp [interp_apply]

/-- Interpolation preserves shared endpoints. -/
lemma interp_fixedEndpoints {a b : ℝ} {γ₁ γ₂ : AdmissiblePath a b}
    (h : fixedEndpoints γ₁ γ₂) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    fixedEndpoints γ₁ (interp γ₁ γ₂ s hs) := by
  refine ⟨?_, ?_⟩
  · simp [interp_apply, h.1]; ring
  · simp [interp_apply, h.2]; ring

/-! ## Status report -/

/-- Status string for the path-space module. -/
def pathSpace_status : String :=
  "Action.PathSpace: AdmissiblePath, actionJ, interp, fixedEndpoints (0 sorry, 0 axiom)"

end Action
end IndisputableMonolith
