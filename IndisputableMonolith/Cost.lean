import Mathlib

namespace IndisputableMonolith
namespace Cost

noncomputable def Jcost (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

structure CostRequirements (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

lemma Jcost_unit0 : Jcost 1 = 0 := by
  simp [Jcost]

/-- J(x) expressed as a squared ratio: J(x) = (x-1)²/(2x). -/
lemma Jcost_eq_sq {x : ℝ} (hx : x ≠ 0) :
    Jcost x = (x - 1) ^ 2 / (2 * x) := by
  unfold Jcost
  field_simp [hx]
  ring

lemma Jcost_symm {x : ℝ} (hx : 0 < x) : Jcost x = Jcost x⁻¹ := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [Jcost_eq_sq hx0, Jcost_eq_sq (inv_ne_zero hx0)]
  field_simp [hx0]
  ring

/-- J(x) ≥ 0 for positive x (AM-GM inequality) -/
lemma Jcost_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ Jcost x := by
  have hx0 : x ≠ 0 := hx.ne'
  rw [Jcost_eq_sq hx0]
  positivity

def AgreesOnExp (F : ℝ → ℝ) : Prop := ∀ t : ℝ, F (Real.exp t) = Jcost (Real.exp t)

@[simp] lemma Jcost_exp (t : ℝ) :
  Jcost (Real.exp t) = ((Real.exp t) + (Real.exp (-t))) / 2 - 1 := by
  have h : (Real.exp t)⁻¹ = Real.exp (-t) := by
    symm; simp [Real.exp_neg t]
  simp [Jcost, h]

class SymmUnit (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

class AveragingAgree (F : ℝ → ℝ) : Prop where
  agrees : AgreesOnExp F

class AveragingDerivation (F : ℝ → ℝ) : Prop extends SymmUnit F where
  agrees : AgreesOnExp F

lemma even_on_log_of_symm {F : ℝ → ℝ} [SymmUnit F] (t : ℝ) :
    F (Real.exp t) = F (Real.exp (-t)) := by
  have hx : 0 < Real.exp t := Real.exp_pos t
  simpa [Real.exp_neg] using (SymmUnit.symmetric (F:=F) hx)

class AveragingBounds (F : ℝ → ℝ) : Prop extends SymmUnit F where
  upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

theorem agrees_on_exp_of_bounds {F : ℝ → ℝ} [AveragingBounds F] :
    AgreesOnExp F := by
  intro t
  have h₁ := AveragingBounds.upper (F:=F) t
  have h₂ := AveragingBounds.lower (F:=F) t
  have : F (Real.exp t) = Jcost (Real.exp t) := le_antisymm h₁ h₂
  simpa using this

theorem F_eq_J_on_pos_alt (F : ℝ → ℝ)
  (hAgree : AgreesOnExp F) : ∀ {x : ℝ}, 0 < x → F x = Jcost x := by
  intro x hx
  have : ∃ t, Real.exp t = x := ⟨Real.log x, by simpa using Real.exp_log hx⟩
  rcases this with ⟨t, rfl⟩
  simpa using hAgree t

instance (priority := 90) averagingDerivation_of_bounds {F : ℝ → ℝ} [AveragingBounds F] :
    AveragingDerivation F :=
  { toSymmUnit := (inferInstance : SymmUnit F)
  , agrees := agrees_on_exp_of_bounds (F:=F) }

def mkAveragingBounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t))
  (lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)) :
  AveragingBounds F :=
{ toSymmUnit := symm, upper := upper, lower := lower }

class JensenSketch (F : ℝ → ℝ) : Prop extends SymmUnit F where
  axis_upper : ∀ t : ℝ, F (Real.exp t) ≤ Jcost (Real.exp t)
  axis_lower : ∀ t : ℝ, Jcost (Real.exp t) ≤ F (Real.exp t)

instance (priority := 95) averagingBounds_of_jensen {F : ℝ → ℝ} [JensenSketch F] :
    AveragingBounds F :=
  mkAveragingBounds F (symm := (inferInstance : SymmUnit F))
    (upper := JensenSketch.axis_upper (F:=F))
    (lower := JensenSketch.axis_lower (F:=F))

noncomputable def JensenSketch.of_log_bounds (F : ℝ → ℝ)
  (symm : SymmUnit F)
  (upper_log : ∀ t : ℝ, F (Real.exp t) ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1))
  (lower_log : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ F (Real.exp t)) :
  JensenSketch F :=
{ toSymmUnit := symm
, axis_upper := by intro t; simpa [Jcost_exp] using upper_log t
, axis_lower := by intro t; simpa [Jcost_exp] using lower_log t }

noncomputable def F_ofLog (G : ℝ → ℝ) : ℝ → ℝ := fun x => G (Real.log x)

class LogModel (G : ℝ → ℝ) where
  even_log : ∀ t : ℝ, G (-t) = G t
  base0 : G 0 = 0
  upper_cosh : ∀ t : ℝ, G t ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1)
  lower_cosh : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ G t

instance (G : ℝ → ℝ) [LogModel G] : SymmUnit (F_ofLog G) :=
  { symmetric := by
      intro x hx
      have hlog : Real.log (x⁻¹) = - Real.log x := by
        simp
      dsimp [F_ofLog]
      have he : G (Real.log x) = G (- Real.log x) := by
        simpa using (LogModel.even_log (G:=G) (Real.log x)).symm
      simpa [hlog]
        using he
    , unit0 := by
      dsimp [F_ofLog]
      simpa [Real.log_one] using (LogModel.base0 (G:=G)) }

instance (priority := 90) (G : ℝ → ℝ) [LogModel G] : JensenSketch (F_ofLog G) :=
  JensenSketch.of_log_bounds (F:=F_ofLog G)
    (symm := (inferInstance : SymmUnit (F_ofLog G)))
    (upper_log := by
      intro t
      dsimp [F_ofLog]
      simpa using (LogModel.upper_cosh (G:=G) t))
    (lower_log := by
      intro t
      dsimp [F_ofLog]
      simpa using (LogModel.lower_cosh (G:=G) t))

theorem agree_on_exp_extends {F : ℝ → ℝ}
  (hAgree : AgreesOnExp F) : ∀ {x : ℝ}, 0 < x → F x = Jcost x := by
  intro x hx
  have : F (Real.exp (Real.log x)) = Jcost (Real.exp (Real.log x)) := hAgree (Real.log x)
  simp [Real.exp_log hx] at this
  exact this

theorem F_eq_J_on_pos {F : ℝ → ℝ}
  (hAgree : AgreesOnExp F) :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  agree_on_exp_extends (F:=F) hAgree

theorem F_eq_J_on_pos_of_averaging {F : ℝ → ℝ} [AveragingAgree F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos (hAgree := AveragingAgree.agrees (F:=F))

theorem agrees_on_exp_of_symm_unit (F : ℝ → ℝ) [AveragingDerivation F] :
  AgreesOnExp F := AveragingDerivation.agrees (F:=F)

theorem F_eq_J_on_pos_of_derivation (F : ℝ → ℝ) [AveragingDerivation F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
  F_eq_J_on_pos (hAgree := agrees_on_exp_of_symm_unit F)

theorem T5_cost_uniqueness_on_pos {F : ℝ → ℝ} [JensenSketch F] :
  ∀ {x : ℝ}, 0 < x → F x = Jcost x :=
by
  intro x hx
  have hAgree : AgreesOnExp F := by
    intro t
    exact le_antisymm (JensenSketch.axis_upper (F:=F) t) (JensenSketch.axis_lower (F:=F) t)
  exact (agree_on_exp_extends (F:=F) hAgree) hx

noncomputable def Jlog (t : ℝ) : ℝ := Jcost (Real.exp t)

lemma Jlog_as_cosh (t : ℝ) : Jlog t = Real.cosh t - 1 := by
  unfold Jlog Jcost
  rw [Real.cosh_eq, inv_eq_one_div, Real.exp_neg]
  ring

lemma hasDerivAt_Jlog (t : ℝ) : HasDerivAt Jlog (Real.sinh t) t := by
  have h1 : Jlog = fun t => Real.cosh t - 1 := by
    ext t
    exact Jlog_as_cosh t
  rw [h1]
  have h_cosh : HasDerivAt Real.cosh (Real.sinh t) t := Real.hasDerivAt_cosh t
  have h_const : HasDerivAt (fun _ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  have h_sub := h_cosh.sub h_const
  simp at h_sub
  exact h_sub

@[simp] lemma hasDerivAt_Jlog_zero : HasDerivAt Jlog 0 0 := by
  simpa using (hasDerivAt_Jlog 0)

@[simp] lemma deriv_Jlog_zero : deriv Jlog 0 = 0 := by
  classical
  simpa using (hasDerivAt_Jlog_zero).deriv

theorem hasDerivAt_Jcost (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt Jcost ((1 - x⁻¹ ^ 2) / 2) x := by
  unfold Jcost
  -- The derivative of f(x) = (x + 1/x)/2 - 1 is f'(x) = (1 - 1/x²)/2
  have h1 : HasDerivAt (fun y => y + y⁻¹) (1 + (-(x^2)⁻¹ : ℝ)) x := by
    apply HasDerivAt.add
    · exact hasDerivAt_id x
    · exact hasDerivAt_inv hx
  have h2 : HasDerivAt (fun y => (y + y⁻¹) / 2) ((1 + (-(x^2)⁻¹)) / 2) x :=
    h1.div_const 2
  have h3 : HasDerivAt (fun y => (y + y⁻¹) / 2 - 1) ((1 + (-(x^2)⁻¹)) / 2 - 0) x :=
    h2.sub (hasDerivAt_const x (1 : ℝ))
  have h_eq : (1 + (-(x^2)⁻¹)) / 2 - 0 = (1 - x⁻¹ ^ 2) / 2 := by
    have : (x^2)⁻¹ = x⁻¹ ^ 2 := by rw [inv_pow]
    linarith [this]
  rw [← h_eq]
  exact h3

theorem deriv_Jcost_one : deriv Jcost 1 = 0 := by
  have h : HasDerivAt Jcost ((1 - 1⁻¹ ^ 2) / 2) 1 := hasDerivAt_Jcost 1 (by norm_num)
  simp at h
  exact h.deriv

/-!
## Strict Convexity of Jcost

The theorem `Jcost_strictConvexOn_pos : StrictConvexOn ℝ (Set.Ioi 0) Jcost`
is proven in `Cost/Convexity.lean` using the second derivative approach:
J''(x) = x⁻³ > 0 for x > 0.

Import `IndisputableMonolith.Cost.Convexity` to access this theorem.
-/

@[simp] lemma Jlog_zero : Jlog 0 = 0 := by
  simp [Jlog, Jcost]

lemma Jlog_nonneg (t : ℝ) : 0 ≤ Jlog t :=
  Jcost_nonneg (Real.exp_pos t)

/-- J(x) > 0 for x ≠ 1 and x > 0. -/
lemma Jcost_pos_of_ne_one (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) : 0 < Jcost x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [Jcost_eq_sq hx0]
  apply div_pos
  · have hne : (x - 1) ≠ 0 := sub_ne_zero.mpr hx1
    exact sq_pos_of_ne_zero hne
  · have h2 : (0 : ℝ) < 2 := by norm_num
    exact mul_pos h2 hx

/-- J(x) = 0 iff x = 1, for positive x. -/
lemma Jcost_eq_zero_iff (x : ℝ) (hx : 0 < x) : Jcost x = 0 ↔ x = 1 := by
  constructor
  · intro h
    by_contra h1
    exact absurd h (ne_of_gt (Jcost_pos_of_ne_one x hx h1))
  · intro h
    rw [h]
    exact Jcost_unit0

/-- **THEOREM**: Jcost is surjective onto [0, ∞). -/
theorem Jcost_surjective_on_nonneg : ∀ y : ℝ, 0 ≤ y → ∃ x : ℝ, 1 ≤ x ∧ Jcost x = y := by
  intro y hy
  -- J(x) = (x + 1/x)/2 - 1
  -- Solve (x + 1/x)/2 - 1 = y => x + 1/x = 2(y+1)
  -- x^2 - 2(y+1)x + 1 = 0
  -- x = [(2(y+1)) + sqrt(4(y+1)^2 - 4)] / 2 = (y+1) + sqrt((y+1)^2 - 1)
  let x := (y + 1) + Real.sqrt ((y + 1) ^ 2 - 1)
  use x
  have h_y1_ge_1 : 1 ≤ y + 1 := by linarith
  have h_sq_ge_0 : 0 ≤ (y + 1) ^ 2 - 1 := by nlinarith
  constructor
  · have : 0 ≤ Real.sqrt ((y + 1) ^ 2 - 1) := Real.sqrt_nonneg _
    linarith
  · unfold Jcost
    have hx_pos : 0 < x := by
      have : 0 ≤ Real.sqrt ((y + 1) ^ 2 - 1) := Real.sqrt_nonneg _
      linarith
    field_simp [hx_pos.ne']
    -- Goal after field_simp: x^2 + 1 - x*2 = x*2*y
    -- Since x = y+1 + sqrt((y+1)^2 - 1), we have x^2 - 2(y+1)x + 1 = 0
    -- Thus x^2 + 1 = 2(y+1)x = 2x + 2xy, so x^2 + 1 - 2x = 2xy
    let s := Real.sqrt ((y + 1) ^ 2 - 1)
    have hs_sq : s ^ 2 = (y + 1) ^ 2 - 1 := Real.sq_sqrt h_sq_ge_0
    have hx_eq : x = y + 1 + s := rfl
    -- Key equation: x^2 - 2(y+1)x + 1 = 0
    have h_quad : x ^ 2 - 2 * (y + 1) * x + 1 = 0 := by
      have h1 : x ^ 2 = (y + 1 + s) ^ 2 := by rw [hx_eq]
      have h2 : (y + 1 + s) ^ 2 = (y + 1) ^ 2 + 2 * (y + 1) * s + s ^ 2 := by ring
      have h3 : s ^ 2 = (y + 1) ^ 2 - 1 := hs_sq
      calc x ^ 2 - 2 * (y + 1) * x + 1
          = (y + 1 + s) ^ 2 - 2 * (y + 1) * (y + 1 + s) + 1 := by simp only [hx_eq]
        _ = ((y + 1) ^ 2 + 2 * (y + 1) * s + s ^ 2) - 2 * (y + 1) * (y + 1 + s) + 1 := by rw [h2]
        _ = ((y + 1) ^ 2 + 2 * (y + 1) * s + ((y + 1) ^ 2 - 1)) - 2 * (y + 1) * (y + 1 + s) + 1 := by rw [h3]
        _ = 0 := by ring
    -- From h_quad: x^2 + 1 = 2(y+1)x = 2x(y+1) = 2x + 2xy
    -- So: x^2 + 1 - 2x = 2xy
    linarith [h_quad]

lemma Jlog_eq_zero_iff (t : ℝ) : Jlog t = 0 ↔ t = 0 := by
  constructor
  · intro h
    have hxpos : 0 < Real.exp t := Real.exp_pos t
    have hxne : Real.exp t ≠ 0 := ne_of_gt hxpos
    have hrepr := Jcost_eq_sq hxne
    rw [Jlog, hrepr] at h
    have hden_pos : 0 < 2 * Real.exp t := by
      apply mul_pos
      · norm_num
      · exact hxpos
    have hden_ne : 2 * Real.exp t ≠ 0 := ne_of_gt hden_pos
    rw [div_eq_zero_iff] at h
    cases h with
    | inl h_num =>
      have hexp1 : Real.exp t - 1 = 0 := by nlinarith [sq_nonneg (Real.exp t - 1)]
      have hexp_eq : Real.exp t = 1 := by linarith
      rw [Real.exp_eq_one_iff] at hexp_eq
      exact hexp_eq
    | inr h_den =>
      exact absurd h_den hden_ne
  · intro h
    rw [h]
    exact Jlog_zero


theorem EL_stationary_at_zero : deriv Jlog 0 = 0 := by
  simp

theorem EL_global_min (t : ℝ) : Jlog 0 ≤ Jlog t := by
  simpa [Jlog_zero] using Jlog_nonneg t

/-- From J(x) = 0 and x > 0, conclude x = 1. -/
lemma Jcost_zero_iff_one {x : ℝ} (hx : 0 < x) (h : Jcost x = 0) : x = 1 :=
  (Jcost_eq_zero_iff x hx).mp h

/-! ## Triangle Inequality for J -/

/-- J in terms of cosh: J(exp(t)) = cosh(t) - 1 -/
lemma Jcost_exp_cosh (t : ℝ) : Jcost (Real.exp t) = Real.cosh t - 1 :=
  Jlog_as_cosh t

/-- The sqrt of 2*J gives |log|, which IS a metric. -/
noncomputable def Jmetric (x : ℝ) : ℝ := Real.sqrt (2 * Jcost x)

/-- Jmetric(1) = 0 -/
lemma Jmetric_one : Jmetric 1 = 0 := by
  simp [Jmetric, Jcost_unit0]

/-- Jmetric is symmetric: Jmetric(x) = Jmetric(1/x) -/
lemma Jmetric_symm {x : ℝ} (hx : 0 < x) : Jmetric x = Jmetric x⁻¹ := by
  simp only [Jmetric, Jcost_symm hx]

/-- Jmetric is non-negative -/
lemma Jmetric_nonneg {x : ℝ} (_ : 0 < x) : 0 ≤ Jmetric x :=
  Real.sqrt_nonneg _

/-- Key identity: 2(cosh(t) - 1) = 4sinh²(t/2)

    Proof: cosh(2u) = cosh²(u) + sinh²(u), and cosh²(u) = 1 + sinh²(u).
    So cosh(2u) = 1 + 2sinh²(u), hence cosh(2u) - 1 = 2sinh²(u). -/
lemma cosh_minus_one_eq (t : ℝ) : 2 * (Real.cosh t - 1) = 4 * Real.sinh (t / 2) ^ 2 := by
  -- Use the double-angle formula: cosh(2u) = cosh²(u) + sinh²(u)
  have h := Real.cosh_two_mul (t / 2)
  -- h : cosh(2*(t/2)) = cosh²(t/2) + sinh²(t/2)
  simp only [two_mul, add_halves] at h
  -- So h : cosh(t) = cosh²(t/2) + sinh²(t/2)
  -- From cosh²(t/2) - sinh²(t/2) = 1, we get cosh²(t/2) = 1 + sinh²(t/2)
  have h2 := Real.cosh_sq_sub_sinh_sq (t / 2)
  have h3 : Real.cosh (t / 2) ^ 2 = 1 + Real.sinh (t / 2) ^ 2 := by linarith
  -- Substitute: cosh(t) = (1 + sinh²(t/2)) + sinh²(t/2) = 1 + 2sinh²(t/2)
  -- So cosh(t) - 1 = 2sinh²(t/2)
  calc 2 * (Real.cosh t - 1)
      = 2 * ((Real.cosh (t / 2) ^ 2 + Real.sinh (t / 2) ^ 2) - 1) := by rw [h]
    _ = 2 * (((1 + Real.sinh (t / 2) ^ 2) + Real.sinh (t / 2) ^ 2) - 1) := by rw [h3]
    _ = 2 * (2 * Real.sinh (t / 2) ^ 2) := by ring
    _ = 4 * Real.sinh (t / 2) ^ 2 := by ring

/-- **THEOREM: Quadratic Lower Bound for cosh**
    cosh x ≥ 1 + x²/2 for all x.

    Proof: From the definition cosh x = (e^x + e^(-x)) / 2 and the Taylor series,
    we have cosh x = 1 + x²/2 + x⁴/24 + ... where all terms are non-negative.

    Alternative proof via convexity: cosh is convex (cosh'' = cosh > 0), and
    the tangent line at 0 gives cosh x ≥ cosh 0 + cosh'(0) * x = 1 + 0 = 1.
    The quadratic bound follows from cosh'' = cosh ≥ 1. -/
theorem cosh_quadratic_lower_bound (x : ℝ) : Real.cosh x ≥ 1 + x^2 / 2 := by
  -- Use the Taylor series expansion
  -- cosh x = ∑' n, x ^ (2 * n) / (2 * n)!
  -- The first two partial sums are: n=0 → 1, n=1 → 1 + x²/2
  -- Since all terms are non-negative, cosh x ≥ 1 + x²/2
  have h := Real.hasSum_cosh x
  -- Extract first two terms and show tail is non-negative
  have h_term0 : (fun n => x ^ (2 * n) / ↑(2 * n).factorial) 0 = 1 := by simp
  have h_term1 : (fun n => x ^ (2 * n) / ↑(2 * n).factorial) 1 = x^2 / 2 := by simp
  -- Each term x^(2n)/(2n)! is non-negative because even powers are non-negative
  have h_nn : ∀ n, 0 ≤ x ^ (2 * n) / ↑(2 * n).factorial := fun n => by
    apply div_nonneg
    · -- x^(2n) = (x^2)^n ≥ 0
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg x) n
    · exact Nat.cast_nonneg _
  -- The sum is at least the sum of the first two terms
  have h_ge : Real.cosh x ≥ 1 + x^2 / 2 := by
    rw [← h.tsum_eq]
    calc ∑' n, x ^ (2 * n) / ↑(2 * n).factorial
        ≥ (x ^ (2 * 0) / ↑(2 * 0).factorial) + (x ^ (2 * 1) / ↑(2 * 1).factorial) := by
          have hs := h.summable
          have h01 : ({0, 1} : Finset ℕ).sum (fun n => x ^ (2 * n) / ↑(2 * n).factorial) ≤
                     ∑' n, x ^ (2 * n) / ↑(2 * n).factorial :=
            hs.sum_le_tsum _ (fun i _ => h_nn i)
          simp only [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)] at h01
          exact h01
      _ = 1 + x^2 / 2 := by simp
  exact h_ge

/-- Jmetric in terms of sinh: Jmetric(exp(t)) = 2|sinh(t/2)| -/
lemma Jmetric_exp_sinh (t : ℝ) : Jmetric (Real.exp t) = 2 * |Real.sinh (t / 2)| := by
  unfold Jmetric
  rw [Jcost_exp_cosh, cosh_minus_one_eq]
  -- sqrt(4 * sinh²(t/2)) = sqrt(4) * |sinh(t/2)| = 2 * |sinh(t/2)|
  rw [show (4 : ℝ) * Real.sinh (t / 2) ^ 2 = (2 * Real.sinh (t / 2)) ^ 2 by ring]
  rw [Real.sqrt_sq_eq_abs]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-! ### Note on Triangle Inequality

The function `Jmetric(x) = sqrt(2 * Jcost(x))` does NOT satisfy the triangle inequality
under multiplication. Numerical counterexample:
- Jmetric(6) ≈ 2.04 > Jmetric(2) + Jmetric(3) ≈ 1.86

This is expected: J-cost measures the "recognition strain" of a ratio, and strain
compounds superlinearly when multiplying far-from-unity ratios.

The key inequality that DOES hold is the d'Alembert identity, which gives
`Jcost_submult`: J(xy) ≤ 2J(x) + 2J(y) + 2J(x)J(y). -/

/-- **Standard Analysis**: Evaluation of Jmetric at specific points. -/
theorem Jmetric_val_6 : Jmetric 6 = Real.sqrt (25 / 6) := by
  unfold Jmetric Jcost
  norm_num

theorem Jmetric_val_2 : Jmetric 2 = Real.sqrt (1 / 2) := by
  unfold Jmetric Jcost
  norm_num

theorem Jmetric_val_3 : Jmetric 3 = Real.sqrt (4 / 3) := by
  unfold Jmetric Jcost
  norm_num

theorem sqrt_triangle_violation : Real.sqrt (25 / 6) > Real.sqrt (1 / 2) + Real.sqrt (4 / 3) := by
  have h1 : 0 ≤ Real.sqrt (1 / 2) + Real.sqrt (4 / 3) := by positivity
  change Real.sqrt (1 / 2) + Real.sqrt (4 / 3) < Real.sqrt (25 / 6)
  rw [← Real.sqrt_sq h1]
  rw [Real.sqrt_lt_sqrt_iff (by positivity)]
  rw [add_sq, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
  rw [mul_assoc, ← Real.sqrt_mul (by norm_num)]
  norm_num
  -- Goal: 1 / 2 + 2 * (√2 / √3) + 4 / 3 < 25 / 6
  suffices 2 * (Real.sqrt 2 / Real.sqrt 3) < 7 / 3 by linarith
  have h_lhs : 2 * (Real.sqrt 2 / Real.sqrt 3) = Real.sqrt (8 / 3) := by
    rw [← Real.sqrt_div (by norm_num) 3]
    rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  have h_rhs : (7 / 3 : ℝ) = Real.sqrt (49 / 9) := by
    rw [Real.sqrt_div (by norm_num) 9]
    norm_num
  rw [h_lhs, h_rhs]
  rw [Real.sqrt_lt_sqrt_iff (by positivity)]
  norm_num

/-- **DEPRECATED**: The naive triangle inequality does NOT hold for Jmetric.
    Use `Jcost_submult` instead, which gives a valid submultiplicativity bound. -/
theorem Jmetric_triangle_FALSE {x y : ℝ} (_hx : 0 < x) (_hy : 0 < y) :
    ¬ (∀ a b : ℝ, 0 < a → 0 < b → Jmetric (a * b) ≤ Jmetric a + Jmetric b) := by
  intro h
  -- Counterexample: a = 2, b = 3
  let a : ℝ := 2
  let b : ℝ := 3
  have ha : 0 < a := by norm_num
  have hb : 0 < b := by norm_num
  have h_tri := h a b ha hb
  rw [show a * b = 6 by norm_num, Jmetric_val_6, Jmetric_val_2, Jmetric_val_3] at h_tri
  have h_viol := sqrt_triangle_violation
  linarith

/-- **DEPRECATED**: The "weak triangle" J(xy) ≤ 2(J(x)+J(y)) + 2√(J(x)J(y)) is FALSE.

    Counterexample: x = y = 10
    - J(100) ≈ 49.005
    - 2(J(10) + J(10)) + 2√(J(10)·J(10)) = 2(4.05 + 4.05) + 2·4.05 ≈ 24.3
    - 49.005 > 24.3

    Use `Jcost_submult` instead: J(xy) ≤ 2J(x) + 2J(y) + 2J(x)J(y), which IS proved. -/
theorem Jcost_weak_triangle_FALSE :
    ¬ (∀ x y : ℝ, 0 < x → 0 < y →
      Jcost (x * y) ≤ 2 * (Jcost x + Jcost y) + 2 * Real.sqrt (Jcost x * Jcost y)) := by
  intro h
  -- Counterexample: x = y = 10, J(100) > 2(J(10)+J(10)) + 2*sqrt(J(10)*J(10))
  -- J(100) = (100 + 1/100)/2 - 1 = 49.005
  -- J(10) = (10 + 0.1)/2 - 1 = 4.05
  -- RHS = 2*(4.05 + 4.05) + 2*sqrt(4.05*4.05) = 16.2 + 8.1 = 24.3
  -- 49.005 > 24.3 is TRUE, not ≤, so the inequality fails
  have hc := h 10 10 (by norm_num) (by norm_num)
  -- The claim asserts ≤ but the counterexample shows >
  -- J(100) = 49.005, RHS = 24.3, so 49.005 > 24.3
  simp only [Jcost] at hc
  nlinarith [sq_nonneg (10 : ℝ), Real.sqrt_nonneg (Jcost 10 * Jcost 10)]

/-- The d'Alembert identity: J(xy) + J(x/y) = 2J(x) + 2J(y) + 2J(x)J(y) -/
theorem dalembert_identity {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Jcost (x * y) + Jcost (x / y) = 2 * Jcost x + 2 * Jcost y + 2 * Jcost x * Jcost y := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hxy : x * y ≠ 0 := mul_ne_zero hx0 hy0
  have hxdy : x / y ≠ 0 := div_ne_zero hx0 hy0
  simp only [Jcost_eq_sq hxy, Jcost_eq_sq hxdy, Jcost_eq_sq hx0, Jcost_eq_sq hy0]
  field_simp
  ring

/-- From d'Alembert: J(xy) ≤ 2J(x) + 2J(y) + 2J(x)J(y) since J(x/y) ≥ 0 -/
lemma Jcost_submult {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Jcost (x * y) ≤ 2 * Jcost x + 2 * Jcost y + 2 * Jcost x * Jcost y := by
  have h := dalembert_identity hx hy
  have hnonneg : 0 ≤ Jcost (x / y) := Jcost_nonneg (div_pos hx hy)
  linarith

/-- Bound on J product: J(xy) ≤ 2*(1 + J(x))*(1 + J(y)) - 2
    This follows from d'Alembert since (1+J(x))(1+J(y)) = 1 + J(x) + J(y) + J(x)J(y) -/
lemma Jcost_prod_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Jcost (x * y) ≤ 2 * (1 + Jcost x) * (1 + Jcost y) - 2 := by
  have h := Jcost_submult hx hy
  -- 2*(1+J(x))*(1+J(y)) - 2 = 2*(1 + J(x) + J(y) + J(x)*J(y)) - 2
  --                        = 2 + 2*J(x) + 2*J(y) + 2*J(x)*J(y) - 2
  --                        = 2*J(x) + 2*J(y) + 2*J(x)*J(y)
  calc Jcost (x * y) ≤ 2 * Jcost x + 2 * Jcost y + 2 * Jcost x * Jcost y := h
    _ = 2 * (1 + Jcost x) * (1 + Jcost y) - 2 := by ring

/-! ## Small-strain Taylor expansion -/

lemma Jcost_one_plus_eps_quadratic (ε : ℝ) (hε : |ε| ≤ (1 : ℝ) / 2) :
    ∃ (c : ℝ), Jcost (1 + ε) = ε ^ 2 / 2 + c * ε ^ 3 ∧ |c| ≤ 2 := by
  classical
  have hbounds := abs_le.mp hε
  have hpos : 0 < 1 + ε := by
    have : -(1 : ℝ) / 2 ≤ ε := by simpa [neg_div] using hbounds.1
    linarith
  have hne : 1 + ε ≠ 0 := ne_of_gt hpos
  have hcalc : Jcost (1 + ε) = ε ^ 2 / (2 * (1 + ε)) := by
    simpa [pow_two, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
      using (Jcost_eq_sq hne)
  let c : ℝ := -1 / (2 * (1 + ε))
  have h_eq :
      Jcost (1 + ε) = ε ^ 2 / 2 + c * ε ^ 3 := by
    have : ε ^ 2 / (2 * (1 + ε)) = ε ^ 2 / 2 + (-1 / (2 * (1 + ε))) * ε ^ 3 := by
      field_simp [hne]
      ring
    simpa [hcalc, c] using this
  have hden_pos : 0 < 2 * (1 + ε) := by nlinarith [hpos]
  have habs : |c| = 1 / (2 * (1 + ε)) := by
    simp [c, div_eq_mul_inv, abs_mul, abs_inv, abs_of_pos hpos]
  -- Use 1/(2(1+ε)) ≤ 1 from (1+ε) ≥ 1/2
  have hone_le : (1 : ℝ) ≤ 2 * (1 + ε) := by
    have : (1 / 2 : ℝ) ≤ 1 + ε := by linarith
    simpa [two_mul] using mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2)
  have hdiv_le_one : 1 / (2 * (1 + ε)) ≤ 1 := by
    have hpos1 : 0 < (1 : ℝ) := by norm_num
    simpa [one_div] using one_div_le_one_div_of_le hpos1 hone_le
  have hbound : |c| ≤ 2 := by
    have h1 : |c| ≤ 1 := by simpa [habs] using hdiv_le_one
    have h12 : (1 : ℝ) ≤ 2 := by norm_num
    exact le_trans h1 h12
  exact ⟨c, h_eq, hbound⟩

lemma Jcost_small_strain_bound (ε : ℝ) (hε : |ε| ≤ (1 : ℝ) / 10) :
    |Jcost (1 + ε) - ε ^ 2 / 2| ≤ ε ^ 2 / 10 := by
  classical
  have hbounds := abs_le.mp hε
  have hpos : 0 < 1 + ε := by
    have : -(1 : ℝ) / 10 ≤ ε := by simpa [neg_div] using hbounds.1
    linarith
  have hne : 1 + ε ≠ 0 := ne_of_gt hpos
  have hform : Jcost (1 + ε) = ε ^ 2 / (2 * (1 + ε)) := by
    simpa [pow_two, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
      using (Jcost_eq_sq hne)
  have hden_pos : 0 < 2 * (1 + ε) := by nlinarith [hpos]
  -- Exact difference and absolute value
  have h1 : Jcost (1 + ε) - ε ^ 2 / 2
      = ε ^ 2 / (2 * (1 + ε)) - ε ^ 2 / 2 := by
    simp [hform]
  have hx : (2 : ℝ) * (1 + ε) ≠ 0 := mul_ne_zero two_ne_zero hne
  have h2 : ε ^ 2 / (2 * (1 + ε)) - ε ^ 2 / 2 = -ε ^ 3 / (2 * (1 + ε)) := by
    field_simp [hx]
    ring
  have hdiff : Jcost (1 + ε) - ε ^ 2 / 2 = -ε ^ 3 / (2 * (1 + ε)) := h1.trans h2
  have habs : |Jcost (1 + ε) - ε ^ 2 / 2| = |ε| ^ 3 / (2 * (1 + ε)) := by
    have hposden : 0 < 2 * (1 + ε) := hden_pos
    simpa [abs_div, abs_neg, abs_pow, abs_of_pos hposden] using
      congrArg (fun z => |z|) hdiff
  -- Now bound using |ε|/(2(1+ε)) ≤ 1/18 from below
  have hx_lower : (9 : ℝ) / 10 ≤ 1 + ε := by linarith [show -(1 : ℝ) / 10 ≤ ε from by simpa [neg_div] using hbounds.1]
  have hx_pos : 0 < (9 : ℝ) / 10 := by norm_num
  have hx_inv : 1 / (1 + ε) ≤ (10 : ℝ) / 9 := by
    have := one_div_le_one_div_of_le hx_pos hx_lower
    simpa using this
  have hrec_bound : 1 / (2 * (1 + ε)) ≤ (5 : ℝ) / 9 := by
    have hmul : (1 / 2 : ℝ) * (1 / (1 + ε)) ≤ (1 / 2) * ((10 : ℝ) / 9) :=
      mul_le_mul_of_nonneg_left hx_inv (by norm_num)
    have hleft : 1 / (2 * (1 + ε)) = (1 / 2) * (1 / (1 + ε)) := by
      simp [div_eq_mul_inv, mul_comm]
    have hright : (5 : ℝ) / 9 = (1 / 2) * ((10 : ℝ) / 9) := by norm_num
    simpa [hleft, hright] using hmul
  have hrec_nonneg : 0 ≤ 1 / (2 * (1 + ε)) := by
    have : 0 ≤ 2 * (1 + ε) := le_of_lt (by nlinarith [hpos])
    exact one_div_nonneg.mpr this
  have hA : |ε| / (2 * (1 + ε)) ≤ (1 : ℝ) / 10 * (1 / (2 * (1 + ε))) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using mul_le_mul_of_nonneg_right hε hrec_nonneg
  have hB : (1 : ℝ) / 10 * (1 / (2 * (1 + ε))) ≤ (1 : ℝ) / 18 := by
    have hmul := mul_le_mul_of_nonneg_left hrec_bound (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 10)
    have hright : (1 : ℝ) / 18 = (1 : ℝ) / 10 * ((5 : ℝ) / 9) := by norm_num
    simpa [hright] using hmul
  have hfrac : |ε| / (2 * (1 + ε)) ≤ (1 : ℝ) / 18 := hA.trans hB
  -- Conclude
  have hineq : |Jcost (1 + ε) - ε ^ 2 / 2| ≤ |ε| ^ 2 / 18 := by
    have hnn : 0 ≤ |ε| ^ 2 := by
      have := sq_nonneg (|ε|); simpa [pow_two] using this
    have hmul := mul_le_mul_of_nonneg_left hfrac hnn
    calc
      |Jcost (1 + ε) - ε ^ 2 / 2| = |ε| ^ 3 / (2 * (1 + ε)) := by simp [habs]
      _ ≤ |ε| ^ 2 * (1 / 18) := by
        simpa [pow_succ, pow_two, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hmul
      _ = |ε| ^ 2 / 18 := by simp [div_eq_mul_inv]
  have hratio : (1 : ℝ) / 18 ≤ 1 / 10 := by norm_num
  have hsq : |ε| ^ 2 = ε ^ 2 := by
    have h1 : |ε| * |ε| = |ε * ε| := by simp [abs_mul]
    calc
      |ε| ^ 2 = |ε| * |ε| := by simp [pow_two]
      _ = |ε * ε| := h1
      _ = |ε ^ 2| := by simp [pow_two]
      _ = ε ^ 2 := by simp [abs_of_nonneg (sq_nonneg ε)]
  have hcompare : |ε| ^ 2 / 18 ≤ ε ^ 2 / 10 := by
    have := mul_le_mul_of_nonneg_left hratio (by exact sq_nonneg ε)
    simpa [hsq, pow_two] using this
  exact (hineq.trans hcompare)

/-- Alias: Jcost_reciprocal = Jcost_symm (for parallel-work compat). -/
lemma Jcost_reciprocal {x : ℝ} (hx : 0 < x) : Jcost x = Jcost x⁻¹ := Jcost_symm hx

/-- J-cost is strictly increasing on `[1, ∞)`.

This root-module copy keeps downstream files from importing both
`IndisputableMonolith.Cost` and `IndisputableMonolith.Cost.JcostCore`, which
define overlapping names in the same namespace. -/
lemma Jcost_strict_mono_on_one_infty (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hx1 : 1 ≤ x) (hxy : x < y) :
    Jcost x < Jcost y := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  rw [Jcost_eq_sq hx0, Jcost_eq_sq hy0]
  have h2x : 0 < 2 * x := by linarith
  have h2y : 0 < 2 * y := by linarith
  rw [div_lt_div_iff₀ h2x h2y]
  have hmain : (x - 1) ^ 2 * (2 * y) < (y - 1) ^ 2 * (2 * x) := by
    let f : ℝ → ℝ := fun t => (t - 1) ^ 2 / t
    have hf_mono : ∀ a b : ℝ, 1 ≤ a → a < b → f a < f b := by
      intro a b ha hab
      simp only [f]
      have ha0 : (0 : ℝ) < a := by linarith
      have hb0 : (0 : ℝ) < b := by linarith
      rw [div_lt_div_iff₀ ha0 hb0]
      have : (a - 1) ^ 2 * b - (b - 1) ^ 2 * a < 0 := by
        have hcalc : (a - 1) ^ 2 * b - (b - 1) ^ 2 * a = (a - b) * (a * b - 1) := by
          ring
        rw [hcalc]
        have h1 : a - b < 0 := by linarith
        have h2 : a * b - 1 > 0 := by nlinarith
        nlinarith
      linarith
    have := hf_mono x y hx1 hxy
    simp only [f] at this
    rw [div_lt_div_iff₀ hx hy] at this
    calc
      (x - 1) ^ 2 * (2 * y) = 2 * ((x - 1) ^ 2 * y) := by ring
      _ < 2 * ((y - 1) ^ 2 * x) := by nlinarith
      _ = (y - 1) ^ 2 * (2 * x) := by ring
  exact hmain

end Cost
end IndisputableMonolith
