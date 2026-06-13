import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.GapWeight
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Foundation.MeasureForcing

/-!
# Alpha Genesis M1: Resummation Forcing

**THE THEOREM.** The exponential dressing of the α seed is not a "resummation
convention." It is forced: any dressing response that factorizes over
independent gap loads and has unit linear response at zero load is exactly
`ε ↦ exp(−ε)`. The additive display `ε ↦ 1 − ε` is not a factorizing
response at all (witness: ε₁ = ε₂ = 1).

This discharges discrete choice (i) of the no-fit proposition (resummation
form (E) vs (A)): form (E) is the unique admissible response; form (A) is its
first-order truncation, a display, not a structural alternative.

## Why factorization is the right premise (not a new choice)

The premise is inherited, not invented for α. It is the same factorization
premise that forces the T9 measure:

* `Foundation.MeasureForcing.RecognitionWeightRule.factorizes` — independent
  composition multiplies weights (lattice layer).
* `Foundation.MeasureForcing.Factorizes` — the continuum layer premise of
  `continuum_weight_forced`.

The surviving coupling fraction after paying gap cost ε IS a recognition
weight at cost ε. Independent gap loads on independent channels compose
additively in cost; an unpaid correlation between independent loads is
forbidden by ledger additivity (same argument as MeasureForcing §1). So the
response must factorize: `g(ε₁ + ε₂) = g(ε₁) · g(ε₂)`.

The calibration `g′(0) = −1` is the unit-linear-response normalization, the
dressing analog of T5's `IsCalibrated` (unit log-curvature at the identity).

## The unification corollary

`alphaInv_eq_seed_mul_forced_weight`: the α dressing factor IS the T9 forced
measure `contWeight` evaluated at the spectral gap load per channel
(`w₈ / (44π)` in rung units). The fine-structure constant is the channel
budget of ∂Q₃ attenuated by the unique recognition weight — the same measure
that fixes ℏ = φ⁻⁵, θ = φ⁻⁴, and the rung-44 scale.

STATUS: THEOREM (0 sorry target). No CODATA reference anywhere in this file.
-/

namespace IndisputableMonolith
namespace Constants
namespace AlphaGenesis

noncomputable section

/-- A **dressing response**: the fraction of coupling budget surviving a gap
load ε. The two fields are the inherited ledger premises:

* `factorizes` — independent gap loads multiply survival fractions (the same
  premise that forces the T9 measure);
* `unit_response` — unit linear response at zero load (calibration, the
  dressing analog of T5's unit log-curvature). -/
structure DressingResponse where
  /-- Survival fraction as a function of gap load. -/
  g : ℝ → ℝ
  /-- Factorization over independent gap loads (ledger additivity shadow). -/
  factorizes : ∀ x y : ℝ, g (x + y) = g x * g y
  /-- Unit linear response at zero load (calibration). -/
  unit_response : HasDerivAt g (-1) 0

namespace DressingResponse

variable (R : DressingResponse)

/-- Zero load means no dressing: `g(0) = 1`. (The alternative `g(0) = 0`
forces `g ≡ 0`, contradicting the unit response.) -/
theorem g_zero : R.g 0 = 1 := by
  have h : R.g 0 = R.g 0 * R.g 0 := by
    have h0 := R.factorizes 0 0
    simpa using h0
  have hz : R.g 0 * (R.g 0 - 1) = 0 := by
    rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp hz with h0 | h1
  · exfalso
    have hall : ∀ x, R.g x = 0 := by
      intro x
      have hx := R.factorizes x 0
      simpa [h0] using hx
    have hconst : R.g = fun _ => (0 : ℝ) := funext hall
    have hd : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (-1) 0 := by
      have hur := R.unit_response
      rw [hconst] at hur
      exact hur
    have hzero : ((-1 : ℝ)) = 0 := hd.unique (hasDerivAt_const 0 0)
    norm_num at hzero
  · linarith [sub_eq_zero.mp h1]

/-- The response is differentiable everywhere with `g′(x) = −g(x)`:
factorization propagates the calibrated derivative from 0 to every point. -/
theorem hasDerivAt_neg_self (x : ℝ) : HasDerivAt R.g (-(R.g x)) x := by
  have hshift : HasDerivAt (fun y : ℝ => y - x) 1 x := (hasDerivAt_id x).sub_const x
  have hcomp0 : HasDerivAt (R.g ∘ fun y : ℝ => y - x) (-1 * 1) x := by
    apply HasDerivAt.comp
    · show HasDerivAt R.g (-1) ((fun y : ℝ => y - x) x)
      simpa [sub_self] using R.unit_response
    · exact hshift
  have hcomp : HasDerivAt (fun y : ℝ => R.g (y - x)) (-1 * 1) x := by
    simpa [Function.comp] using hcomp0
  have hmul : HasDerivAt (fun y : ℝ => R.g x * R.g (y - x)) (R.g x * (-1 * 1)) x :=
    hcomp.const_mul (R.g x)
  have hfun : (fun y : ℝ => R.g x * R.g (y - x)) = R.g := by
    funext y
    rw [← R.factorizes x (y - x)]
    congr 1
    ring
  rw [hfun] at hmul
  convert hmul using 1
  ring

/-- **RESUMMATION FORCING.** Any factorizing dressing response with unit
linear response is exactly the exponential: `g(ε) = exp(−ε)`. There is no
resummation freedom. -/
theorem response_forced : ∀ ε : ℝ, R.g ε = Real.exp (-ε) := by
  -- h(x) = g(x)·exp(x) has zero derivative everywhere, hence is constant 1.
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => R.g y * Real.exp y) 0 x := by
    intro x
    have hmul := (R.hasDerivAt_neg_self x).mul (Real.hasDerivAt_exp x)
    convert hmul using 1
    ring
  have hdiff : Differentiable ℝ (fun y : ℝ => R.g y * Real.exp y) :=
    fun x => (hd x).differentiableAt
  have hderiv : ∀ x : ℝ, deriv (fun y : ℝ => R.g y * Real.exp y) x = 0 :=
    fun x => (hd x).deriv
  have hconst : ∀ x : ℝ, R.g x * Real.exp x = R.g 0 * Real.exp 0 := by
    intro x
    exact is_const_of_deriv_eq_zero hdiff hderiv x 0
  intro ε
  have hε : R.g ε * Real.exp ε = 1 := by
    have hx := hconst ε
    simpa [R.g_zero] using hx
  have hexp : Real.exp ε ≠ 0 := (Real.exp_pos ε).ne'
  have hgε : R.g ε = (Real.exp ε)⁻¹ := by
    have h2 := congrArg (· * (Real.exp ε)⁻¹) hε
    simpa [mul_assoc, mul_inv_cancel₀ hexp] using h2
  rw [hgε, ← Real.exp_neg]

/-- **ADDITIVE FORM EXCLUDED.** No dressing response is the additive display
`ε ↦ 1 − ε`: it fails factorization (witness ε₁ = ε₂ = 1). Form (A) is a
truncation of form (E), not a structural alternative. -/
theorem no_additive_response : R.g ≠ fun ε => 1 - ε := by
  intro hcontra
  have h := R.factorizes 1 1
  rw [hcontra] at h
  norm_num at h

end DressingResponse

/-- The additive map fails the factorization law outright (independent of any
response structure). -/
theorem additive_map_not_factorizing :
    ¬ (∀ x y : ℝ, (1 - (x + y)) = (1 - x) * (1 - y)) := by
  intro h
  have h11 := h 1 1
  norm_num at h11

/-- The dressed coupling: seed times forced response at normalized load. -/
def dressedCoupling (S δ : ℝ) : ℝ := S * Real.exp (-(δ / S))

/-- Any dressing response yields exactly the form-(E) dressed coupling. -/
theorem dressedCoupling_forced (R : DressingResponse) (S δ : ℝ) :
    S * R.g (δ / S) = dressedCoupling S δ := by
  rw [R.response_forced (δ / S)]
  rfl

/-- **THE UNIFICATION COROLLARY.** The certified `alphaInv` is the channel
budget multiplied by the **T9 forced measure** at the spectral gap load per
channel (in rung units):

`α⁻¹ = (4π·11) · contWeight(w₈ / (4π·11))`.

The α dressing factor is not α-specific structure. It is the unique
recognition weight `φ⁻ᵗ` forced by factorization + self-similar calibration
(`Foundation.MeasureForcing.continuum_weight_forced`), evaluated at
`t = w₈/(44π)` rungs. -/
theorem alphaInv_eq_seed_mul_forced_weight :
    Constants.alphaInv =
      Constants.alpha_seed *
        Foundation.MeasureForcing.contWeight
          (Constants.w8_from_eight_tick / Constants.alpha_seed) := by
  rw [Foundation.MeasureForcing.contWeight_gibbs]
  simp only [Constants.alphaInv]
  have hgap : Constants.f_gap = Constants.w8_from_eight_tick * Real.log Constants.phi := rfl
  rw [hgap]
  congr 1
  congr 1
  ring

/-- The response that dresses α and the weight that forces the measure are
one function: `g(lnφ · t) = contWeight(t)` for every dressing response. -/
theorem response_is_forced_measure (R : DressingResponse) (t : ℝ) :
    R.g (Real.log Constants.phi * t) = Foundation.MeasureForcing.contWeight t := by
  rw [R.response_forced, Foundation.MeasureForcing.contWeight_gibbs]
  congr 1
  ring

end

end AlphaGenesis
end Constants
end IndisputableMonolith
