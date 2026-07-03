import Mathlib
import Mathlib.Analysis.Calculus.MeanValue
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Foundation.DAlembert.CurvatureGate
import IndisputableMonolith.Foundation.DAlembert.Counterexamples

/-!
# The Fourth Gate: d'Alembert Structure

This module formalizes the **Fourth Gate**: the d'Alembert structure condition.

## Relation to Gate 3 (Curvature)

In the Option~A formulation used in the paper, Gate~3 is a \emph{normalized} closure:
the hyperbolic branch is assumed directly as the ODE `G''(t) = G(t) + 1`.
Together with symmetry (evenness) and calibration, that already forces
`G(t) = cosh(t) - 1`. Consequently the shifted log-lift `H = G + 1 = cosh`
automatically satisfies the d'Alembert functional equation.

So, in that formulation, ``Gate 4'' is not an additional restriction beyond Gate~3;
it is a derived structure and a convenient cross-check.

We keep this module explicit because it packages the classical functional-equation
viewpoint (Aczél's classification theorem) as a compact certificate path in Lean.

## Historical Note

The d'Alembert functional equation `f(x+y) + f(x-y) = 2f(x)f(y)` was studied by
Jean le Rond d'Alembert in the 18th century. Its continuous solutions are exactly
`cosh(λx)` for λ ∈ ℝ. This is a classical result in functional equation theory.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DAlembert
namespace FourthGate

open Real Cost CurvatureGate

/-! ## Definition of the Fourth Gate -/

/-- **d'Alembert Structure**: A function H satisfies the d'Alembert functional equation. -/
def SatisfiesDAlembert (H : ℝ → ℝ) : Prop :=
  (H 0 = 1) ∧ (∀ t u : ℝ, H (t + u) + H (t - u) = 2 * H t * H u)

/-- The d'Alembert structure gate for a cost function F:
    The shifted log-lift H(t) = F(eᵗ) + 1 satisfies d'Alembert. -/
def HasDAlembert (F : ℝ → ℝ) : Prop :=
  SatisfiesDAlembert (fun t => F (Real.exp t) + 1)

/-! ## Canonical Solutions -/

/-- cosh satisfies the d'Alembert equation. -/
theorem cosh_satisfies_dAlembert : SatisfiesDAlembert Real.cosh := by
  constructor
  · exact Real.cosh_zero
  · intro t u
    have h1 := Real.cosh_add t u
    have h2 := Real.cosh_sub t u
    linarith

/-- Jcost has d'Alembert structure. -/
theorem Jcost_has_dAlembert_structure : HasDAlembert Cost.Jcost := by
  unfold HasDAlembert SatisfiesDAlembert
  constructor
  · simp [Cost.Jcost, Real.exp_zero]
  · intro t u
    have hH : ∀ s, Cost.Jcost (Real.exp s) + 1 = Real.cosh s := by
      intro s
      simp only [Cost.Jcost]
      have hcosh : Real.cosh s = (Real.exp s + Real.exp (-s)) / 2 := Real.cosh_eq s
      have hneg : Real.exp (-s) = (Real.exp s)⁻¹ := Real.exp_neg s
      linarith
    simp only [hH]
    have hcosh := cosh_satisfies_dAlembert.2 t u
    exact hcosh

/-! ## d'Alembert Classification Theorem -/

/-- Differentiating the d'Alembert functional equation twice:
if `f(x+y) + f(x-y) = 2 f(x) f(y)`, then `f''(x) = f''(0) * f(x)`. -/
theorem dalembert_deriv_ode (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hDA : ∀ x y, f (x + y) + f (x - y) = 2 * f x * f y) :
    ∀ x, deriv (deriv f) x = deriv (deriv f) 0 * f x := by
  -- Proof: fix t. The functions u ↦ f(t+u)+f(t-u) and u ↦ 2·f(t)·f(u) agree pointwise
  -- (by hDA), so their second derivatives at u=0 agree.
  -- LHS: d²/du²[f(t+u)+f(t-u)]|_{u=0} = 2·f''(t)
  -- RHS: d²/du²[2·f(t)·f(u)]|_{u=0}   = 2·f(t)·f''(0)
  -- Therefore f''(t) = f''(0)·f(t).
  have hDiff : Differentiable ℝ f :=
    hf.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have hCDiff1_f' : ContDiff ℝ 1 (deriv f) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at hf
    rw [contDiff_succ_iff_deriv] at hf
    exact hf.2.2
  have hDiffDeriv : Differentiable ℝ (deriv f) :=
    hCDiff1_f'.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)
  -- Shift helpers: HasDerivAt for affine shifts of u
  have hsh_add : ∀ (s v : ℝ), HasDerivAt (fun u => s + u) (1 : ℝ) v := fun s v => by
    have h := (hasDerivAt_id v).add_const s; simp only [id] at h
    rwa [show (fun u : ℝ => u + s) = fun u => s + u from funext fun u => add_comm u s] at h
  have hsh_sub : ∀ (s v : ℝ), HasDerivAt (fun u => s - u) (-1 : ℝ) v := fun s v => by
    have h1 : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) v := by
      have := (hasDerivAt_id v).neg; simp only [id] at this; exact this
    have h2 := h1.const_add s
    rwa [show (fun u : ℝ => s + -u) = fun u => s - u from funext fun u => by ring] at h2
  intro t
  -- Pointwise equality of the two sides of hDA, lifted to functions of u
  have h_feq : (fun u => f (t + u) + f (t - u)) = (fun u => 2 * f t * f u) :=
    funext (hDA t)
  have key : deriv (deriv (fun u => f (t + u) + f (t - u))) 0 =
             deriv (deriv (fun u => 2 * f t * f u)) 0 :=
    congr_arg (fun fn => deriv (deriv fn) 0) h_feq
  -- Compute LHS = 2 * f''(t)
  have lhs_eq : deriv (deriv (fun u => f (t + u) + f (t - u))) 0 = 2 * deriv (deriv f) t := by
    have h_plus : ∀ v, HasDerivAt (fun u => f (t + u)) (deriv f (t + v)) v := fun v => by
      have hcomp := (hDiff (t + v)).hasDerivAt.comp v (hsh_add t v)
      simp only [mul_one, Function.comp_apply] at hcomp; exact hcomp
    have h_minus : ∀ v, HasDerivAt (fun u => f (t - u)) (-deriv f (t - v)) v := fun v => by
      have hcomp := (hDiff (t - v)).hasDerivAt.comp v (hsh_sub t v)
      simp only [mul_neg, mul_one, Function.comp_apply] at hcomp; exact hcomp
    have hfirst_fun : deriv (fun u => f (t + u) + f (t - u)) =
        fun v => deriv f (t + v) - deriv f (t - v) := funext fun v => by
      have heq : (fun u => f (t + u)) + (fun u => f (t - u)) =
          fun u => f (t + u) + f (t - u) := by ext u; rfl
      have h12 : deriv (fun u => f (t + u) + f (t - u)) v =
          deriv f (t + v) + -deriv f (t - v) := by
        rw [← heq]; exact ((h_plus v).add (h_minus v)).deriv
      linarith [show deriv f (t + v) + -deriv f (t - v) =
          deriv f (t + v) - deriv f (t - v) from by ring]
    have hd2_plus : HasDerivAt (fun v => deriv f (t + v)) (deriv (deriv f) t) 0 := by
      have hDH : HasDerivAt (deriv f) (deriv (deriv f) (t + 0)) (t + 0) :=
        (hDiffDeriv (t + 0)).hasDerivAt
      have hcomp := hDH.comp 0 (hsh_add t 0)
      simp only [mul_one, add_zero, Function.comp_apply] at hcomp; exact hcomp
    have hd2_minus : HasDerivAt (fun v => deriv f (t - v)) (-deriv (deriv f) t) 0 := by
      have hDH : HasDerivAt (deriv f) (deriv (deriv f) (t - 0)) (t - 0) :=
        (hDiffDeriv (t - 0)).hasDerivAt
      have hcomp := hDH.comp 0 (hsh_sub t 0)
      simp only [mul_neg, mul_one, sub_zero, Function.comp_apply] at hcomp; exact hcomp
    rw [congr_fun (congr_arg deriv hfirst_fun) 0]
    have heq2 : (fun v => deriv f (t + v)) - (fun v => deriv f (t - v)) =
        fun v => deriv f (t + v) - deriv f (t - v) := by ext v; rfl
    have h : deriv (fun v => deriv f (t + v) - deriv f (t - v)) 0 =
        deriv (deriv f) t - -deriv (deriv f) t := by
      rw [← heq2]; exact (hd2_plus.sub hd2_minus).deriv
    linarith [show deriv (deriv f) t - -deriv (deriv f) t = 2 * deriv (deriv f) t from by ring]
  -- Compute RHS = 2 * f(t) * f''(0)
  have rhs_eq : deriv (deriv (fun u => 2 * f t * f u)) 0 = 2 * f t * deriv (deriv f) 0 := by
    have hfirst_fun : deriv (fun u => 2 * f t * f u) = fun v => 2 * f t * deriv f v :=
      funext fun v => ((hDiff v).hasDerivAt.const_mul (2 * f t)).deriv
    have hsecond := (hDiffDeriv 0).hasDerivAt.const_mul (2 * f t)
    rw [congr_fun (congr_arg deriv hfirst_fun) 0, hsecond.deriv]
  -- Conclude: f''(t) = f''(0) * f(t)
  rw [lhs_eq, rhs_eq] at key
  -- key : 2 * deriv (deriv f) t = 2 * f t * deriv (deriv f) 0
  calc deriv (deriv f) t
      = (2 * deriv (deriv f) t) / 2 := by ring
    _ = (2 * f t * deriv (deriv f) 0) / 2 := by rw [key]
    _ = deriv (deriv f) 0 * f t := by ring

/-- **Theorem (d'Alembert Classification)**: If H is C², satisfies d'Alembert,
    H(0) = 1, H'(0) = 0, and H''(0) = λ², then H(t) = cosh(λt).

    **Note**: This general λ version is not used in the main forcing chain.
    The framework only requires the λ = 1 case, which is proved in
    `dAlembert_with_unit_calibration`. The general case reduces to it by scaling:
    For λ ≠ 0, define K(s) = H(s/λ); then K'' = K, K(0)=1, K'(0)=0, so K = cosh,
    hence H(t) = cosh(λt). For λ = 0, H'' = 0 gives H = 1 = cosh(0).
    Formalizing the scaling argument requires careful chain-rule handling. -/
theorem dAlembert_classification :
    ∀ H : ℝ → ℝ, ∀ lam : ℝ,
    SatisfiesDAlembert H →
    ContDiff ℝ 2 H →
    deriv H 0 = 0 →
    deriv (deriv H) 0 = lam ^ 2 →
    ∀ t, H t = Real.cosh (lam * t) := by
  intro H lam hDA hSmooth hDeriv0 hCalib t
  have h_ode : ∀ x, deriv (deriv H) x = deriv (deriv H) 0 * H x :=
    dalembert_deriv_ode H hSmooth hDA.2
  by_cases hlam : lam = 0
  · -- λ = 0: H'' = 0, so H is constant; H(0)=1, H'(0)=0 ⇒ H = 1 = cosh(0)
    subst hlam
    have hode0 : ∀ x, deriv (deriv H) x = 0 := fun x => by
      rw [h_ode x, hCalib, zero_pow two_ne_zero]; exact zero_mul (H x)
    -- H''=0 ⇒ deriv H constant; deriv H 0 = 0 ⇒ deriv H = 0 ⇒ H constant; H 0 = 1 ⇒ H = 1
    have hd_deriv : Differentiable ℝ (deriv H) := hSmooth.differentiable_deriv_two
    have hH'0 : ∀ x, deriv H x = 0 := fun x => (is_const_of_deriv_eq_zero hd_deriv hode0 x 0).trans hDeriv0
    have hH_const : ∀ x, H x = 1 := fun x => (is_const_of_deriv_eq_zero (hSmooth.differentiable (by decide)) hH'0 x 0).trans hDA.1
    simp only [hH_const t, zero_mul, Real.cosh_zero]
  · -- λ ≠ 0: K(s) = H(s/λ) satisfies K'' = K, K(0)=1, K'(0)=0, K''(0)=1; apply unit calibration.
    let K := fun s => H (s / lam)
    have hK0 : K 0 = 1 := by simp [K, hDA.1]
    have hK_DA : SatisfiesDAlembert K := by
      constructor; exact hK0
      intro t u
      simp only [K]
      have ht : (t + u) / lam = t / lam + u / lam := by field_simp [hlam]
      have ht' : (t - u) / lam = t / lam - u / lam := by field_simp [hlam]
      rw [ht, ht']
      exact hDA.2 (t / lam) (u / lam)
    have hK_smooth : ContDiff ℝ 2 K :=
      ContDiff.comp hSmooth ((contDiff_id.div_const lam).of_le le_top)
    have hK'_0 : deriv K 0 = 0 := by
      have K_eq : K = fun s => H ((1/lam) * s) := by ext s; simp [K]; congr 1; field_simp [hlam]
      rw [K_eq, deriv_comp_mul_left (1/lam) H 0]
      rw [show (1/lam) * 0 = 0 from by ring, hDeriv0]; simp
    have hK''_0 : deriv (deriv K) 0 = 1 := by
      have K_eq : K = fun s => H ((1/lam) * s) := by ext s; simp [K]; congr 1; field_simp [hlam]
      have dK : deriv K = fun s => (1/lam) * deriv H (s/lam) := by
        ext s
        rw [K_eq, deriv_comp_mul_left (1/lam) H s, smul_eq_mul]
        rw [show (1/lam) * s = s / lam from by field_simp [hlam]]
      rw [dK, deriv_const_mul_field (1/lam)]
      rw [show (fun s => deriv H (s/lam)) = fun s => (deriv H) ((1/lam) * s) from by ext s; congr 1; field_simp [hlam]]
      rw [deriv_comp_mul_left (1/lam) (deriv H) 0, smul_eq_mul]
      rw [show (1/lam) * 0 = 0 from by ring, h_ode 0, hCalib, hDA.1]
      field_simp [hlam]
    have hK_ode : ∀ s, deriv (deriv K) s = K s := by
      intro s
      have K_eq : K = fun z => H ((1/lam) * z) := by ext z; simp [K]; congr 1; field_simp [hlam]
      have dK : deriv K = fun x => (1/lam) * deriv H (x/lam) := by
        ext x
        rw [K_eq, deriv_comp_mul_left (1/lam) H x, smul_eq_mul]
        rw [show (1/lam) * x = x / lam from by field_simp [hlam]]
      rw [dK, deriv_const_mul_field (1/lam)]
      rw [show (fun x => deriv H (x/lam)) = fun x => (deriv H) ((1/lam) * x) from by ext x; congr 1; field_simp [hlam]]
      rw [deriv_comp_mul_left (1/lam) (deriv H) s, smul_eq_mul]
      rw [show (1/lam) * s = s / lam from by field_simp [hlam], h_ode (s/lam)]
      simp only [K, hCalib]; field_simp [hlam]
    have hK_eq_cosh : ∀ s, K s = Real.cosh s :=
      Cost.FunctionalEquation.ode_cosh_uniqueness_contdiff K hK_smooth hK_ode hK0 hK'_0
    have h_eq : K (lam * t) = H t := by simp [K]; field_simp [hlam]
    rw [← h_eq, hK_eq_cosh (lam * t)]

/-- **Corollary**: With calibration H''(0) = 1, we get H = cosh.
    Proof: dalembert_deriv_ode gives H''(t) = H''(0)·H(t); substituting H''(0) = 1
    gives H'' = H; ODE uniqueness (H(0)=1, H'(0)=0) then forces H = cosh. -/
theorem dAlembert_with_unit_calibration (H : ℝ → ℝ)
    (hDA : SatisfiesDAlembert H)
    (hSmooth : ContDiff ℝ 2 H)
    (hDeriv0 : deriv H 0 = 0)
    (hCalib : deriv (deriv H) 0 = 1) :
    ∀ t, H t = Real.cosh t := by
  -- Step 1: H''(t) = H''(0) · H(t) from d'Alembert + C²
  have hode_gen : ∀ x, deriv (deriv H) x = deriv (deriv H) 0 * H x :=
    dalembert_deriv_ode H hSmooth hDA.2
  -- Step 2: Substitute H''(0) = 1 to get the canonical ODE H'' = H
  have hode : ∀ t, deriv (deriv H) t = H t := fun t => by
    rw [hode_gen t, hCalib, one_mul]
  -- Step 3: H(0) = 1 (from SatisfiesDAlembert)
  have hH0 : H 0 = 1 := hDA.1
  -- Step 4: ODE uniqueness — the unique C² solution to H'' = H, H(0) = 1, H'(0) = 0 is cosh
  exact Cost.FunctionalEquation.ode_cosh_uniqueness_contdiff H hSmooth hode hH0 hDeriv0

/-! ## d'Alembert Forces Canonical G -/

/-- d'Alembert structure + calibration forces G = cosh - 1. -/
theorem dAlembert_forces_Gcosh (G : ℝ → ℝ)
    (hDA : SatisfiesDAlembert (fun t => G t + 1))
    (hSmooth : ContDiff ℝ 2 G)
    (_ : G 0 = 0)
    (hEven : ∀ t, G (-t) = G t)
    (hCalib : deriv (deriv G) 0 = 1) :
    ∀ t, G t = Real.cosh t - 1 := by
  let H := fun t => G t + 1
  have hHsmooth : ContDiff ℝ 2 H := hSmooth.add contDiff_const
  have hHderiv0 : deriv H 0 = 0 := by
    have hderivH : deriv H = deriv G := by ext t; simp [H, deriv_add_const]
    rw [hderivH]
    have hGeven : (fun t => G (-t)) = G := funext hEven
    have hcomp : deriv (fun t => G (-t)) 0 = deriv G 0 := by simp only [hGeven]
    have hchain : deriv (fun t => G (-t)) 0 = -(deriv G 0) := by
      have heq : (fun t => G (-t)) = G ∘ (fun t => -t) := rfl
      rw [heq]
      have hGdiff : DifferentiableAt ℝ G 0 := hSmooth.differentiable (by norm_num) |>.differentiableAt
      rw [deriv_comp (0 : ℝ) (by simp only [neg_zero]; exact hGdiff) differentiable_neg.differentiableAt]
      simp only [neg_zero, deriv_neg', mul_neg_one]
    rw [hchain] at hcomp
    linarith
  have hHcalib : deriv (deriv H) 0 = 1 := by
    have h1 : deriv H = deriv G := by ext t; simp [H, deriv_add_const]
    have h2 : deriv (deriv H) = deriv (deriv G) := by simp [h1]
    rw [h2, hCalib]
  have hHcosh := dAlembert_with_unit_calibration H hDA hHsmooth hHderiv0 hHcalib
  intro t
  have := hHcosh t
  simp only [H] at this
  linarith

/-! ## The Counterexample Fails Gate 4 -/

/-- The quadratic log-lift H(t) = t²/2 + 1 does NOT satisfy d'Alembert. -/
theorem Hquad_not_dAlembert : ¬ SatisfiesDAlembert (fun t => t^2/2 + 1) := by
  intro ⟨_, hda⟩
  have h11 := hda 1 1
  norm_num at h11

/-- Fquad does NOT have d'Alembert structure. -/
theorem Fquad_not_dAlembert_structure : ¬ HasDAlembert Counterexamples.Fquad := by
  intro h
  unfold HasDAlembert at h
  have hH : (fun t => Counterexamples.Fquad (Real.exp t) + 1) = (fun t => t^2/2 + 1) := by
    ext t
    simp [Counterexamples.Fquad, Cost.F_ofLog, Counterexamples.Gquad, Real.log_exp]
  rw [hH] at h
  exact Hquad_not_dAlembert h

/-! ## Fourth Gate Summary -/

/-- **Fourth Gate Theorem**: Jcost satisfies d'Alembert structure; Fquad does not. -/
theorem fourth_gate_summary :
    HasDAlembert Cost.Jcost ∧
    ¬ HasDAlembert Counterexamples.Fquad :=
  ⟨Jcost_has_dAlembert_structure, Fquad_not_dAlembert_structure⟩

/-! ## Full Inevitability with Four Gates -/

/-- **Full Inevitability**: d'Alembert structure + structural axioms forces F = Jcost. -/
theorem dAlembert_forces_Jcost (F : ℝ → ℝ)
    (hNorm : F 1 = 0)
    (hSymm : ∀ x : ℝ, 0 < x → F x = F x⁻¹)
    (hSmooth : ContDiff ℝ 2 F)
    (hCalib : deriv (deriv (fun t => F (Real.exp t))) 0 = 1)
    (hDA : HasDAlembert F) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  intro x hx
  let G := fun t => F (Real.exp t)
  have hGsmooth : ContDiff ℝ 2 G := hSmooth.comp Real.contDiff_exp
  have hGnorm : G 0 = 0 := by simp [G, hNorm]
  have hGeven : ∀ t, G (-t) = G t := by
    intro t
    simp only [G, Real.exp_neg]
    exact (hSymm (Real.exp t) (Real.exp_pos t)).symm
  have hGcosh := dAlembert_forces_Gcosh G hDA hGsmooth hGnorm hGeven hCalib
  have hFx : F x = G (Real.log x) := by simp [G, Real.exp_log hx]
  rw [hFx, hGcosh (Real.log x)]
  simp only [Cost.Jcost]
  have hcosh : Real.cosh (Real.log x) = (x + x⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_log hx, Real.exp_neg, Real.exp_log hx]
  linarith [hcosh]

end FourthGate
end DAlembert
end Foundation
end IndisputableMonolith
