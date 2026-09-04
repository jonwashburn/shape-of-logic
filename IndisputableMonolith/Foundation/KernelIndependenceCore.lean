import Mathlib
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Foundation.MeasureForcing
import IndisputableMonolith.PhiSupport.Lemmas

/-!
# Recognition Kernel: independence core (Phase 3 mathematics)

The shrinks and countermodels for the kernel members, stated over **unknown**
carriers per `L-kernel-state-premises-over-variables`. This module is
deliberately slim: it imports only the functional-equation surface, the measure
forcing surface, and the φ lemmas, so it can be iterated without pulling the
`Cost` aggregate. The certificate that names verdicts per kernel field lives in
`Foundation/RecognitionKernelIndependence.lean`.

## Shrinks proved here

* `composition_calibration_forces_normalized`: normalization is REDUNDANT. The
  composition law at `y = 1` gives `F 1 * (F x + 1) = 0`, so either `F 1 = 0` or
  `F` is the constant `-1` on the positives, and the constant is not calibrated.
  This supersedes the Phase 1 "wash" verdict, which derived normalization from
  the composition law plus *nonnegativity* and had to count nonnegativity as a
  fresh premise. Calibration is already a kernel member, so the trade is free.

## The combiner, answered on both halves

`N-ufc-kernel-combiner-pin-open` asked whether the pinned combiner
`2ab + 2a + 2b` is forced or chosen. It is one of each.

* `linear_coefficient_forced`: the coefficient on the **linear** terms is FORCED
  to `2`. A wrong linear coefficient collapses the unit diagonal to `F ≡ 0`, and
  the zero cost has no log-curvature, so calibration kills it.

* `product_coefficient_is_a_choice`: the coefficient on the **product** term is
  a CHOICE. It is the scale of `F`, and calibration does not spend it, because
  rescaling the cost and rescaling the log-frequency compensate along the family
  `c = 2k²`. The witness at `c = 8` is `quarterCoshTwoCost`, which is normalized,
  calibrated and continuous, satisfies the family law, and is not `Jcost`.

  This is the honest verdict and it cost the first draft of this module, which
  asserted FORCED on the strength of the `k = 1` ray alone. The `k ≠ 1` rays are
  the whole content: they are why calibration cannot recover the pin.

* `compositionGen_scaled`, `compositionGen_of_scaled`, `calibration_scaled`: the
  orbit structure behind both verdicts. Solutions of the family law at
  coefficient `2s` are exactly `s`-rescalings of solutions of the pinned law.

## Countermodels proved here

One per remaining kernel member, each satisfying every other member in its
sector and failing a named `KernelSpine` conclusion.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelIndependence

open Cost.FunctionalEquation

noncomputable section

/-! ## Section A: normalization is redundant -/

/-- The composition law at `y = 1` forces `F 1 * (F x + 1) = 0` pointwise. -/
theorem unit_diagonal_dichotomy
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (x : ℝ) (hx : 0 < x) :
    F 1 * (F x + 1) = 0 := by
  have h := hComp x 1 hx one_pos
  rw [mul_one, div_one] at h
  nlinarith [h]

/-- **Shrink.** The composition law plus calibration force normalization, so
`IsNormalized` is redundant as a kernel member.

The dichotomy above leaves only `F 1 = 0` or `F ≡ -1` on the positives, and the
constant function has vanishing log-curvature, so it cannot be calibrated. -/
theorem composition_calibration_forces_normalized
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (hCalib : IsCalibrated F) :
    IsNormalized F := by
  by_contra hne
  have hconst : ∀ x : ℝ, 0 < x → F x = -1 := by
    intro x hx
    rcases mul_eq_zero.mp (unit_diagonal_dichotomy F hComp x hx) with h1 | h2
    · exact absurd h1 hne
    · linarith
  have hG : G F = fun _ : ℝ => (-1 : ℝ) := by
    funext t
    simpa [G] using hconst (Real.exp t) (Real.exp_pos t)
  have hzero : deriv (deriv (G F)) 0 = 0 := by
    rw [hG]
    simp
  have hcal : deriv (deriv (G F)) 0 = 1 := hCalib
  rw [hzero] at hcal
  exact absurd hcal (by norm_num)

/-! ## Section B: the combiner coefficient is a scale, not a law -/

/-- The composition law with **unknown** coefficients: `c` on the product term
and `d` on each linear term. The kernel's pinned member is
`SatisfiesCompositionLawFamily 2 2`, and the program's headline question is which
of the two coefficients is forced. Answer: `d` is forced, `c` is a choice. -/
def SatisfiesCompositionLawFamily (c d : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y →
    F (x * y) + F (x / y) = c * F x * F y + d * F x + d * F y

/-- The composition law with an unknown product coefficient and the forced
linear coefficient. -/
abbrev SatisfiesCompositionLawGen (c : ℝ) (F : ℝ → ℝ) : Prop :=
  SatisfiesCompositionLawFamily c 2 F

theorem compositionLawGen_two_iff (F : ℝ → ℝ) :
    SatisfiesCompositionLawGen 2 F ↔ SatisfiesCompositionLaw F := by
  constructor <;> intro h x y hx hy <;>
    simpa [SatisfiesCompositionLawFamily] using h x y hx hy

/-- **The linear coefficient is FORCED.** For any nontrivial calibrated cost, the
coefficient on the linear terms of the combiner must be exactly `2`.

At `y = 1` the family equation collapses to `(2 - d) * F x = 0` once `F` is
normalized, so a wrong `d` forces `F ≡ 0` on the positives, and the zero cost has
vanishing log-curvature. Nothing about recognition enters: this half of the
combiner is arithmetic. -/
theorem linear_coefficient_forced
    (c d : ℝ) (F : ℝ → ℝ)
    (hFam : SatisfiesCompositionLawFamily c d F)
    (hNorm : IsNormalized F) (hCalib : IsCalibrated F) :
    d = 2 := by
  by_contra hd
  have hzeroF : ∀ x : ℝ, 0 < x → F x = 0 := by
    intro x hx
    have h := hFam x 1 hx one_pos
    rw [mul_one, div_one] at h
    have hF1 : F 1 = 0 := hNorm
    rw [hF1] at h
    have h2 : (2 - d) * F x = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp h2 with hleft | hright
    · exact absurd (by linarith [hleft] : d = 2) hd
    · exact hright
  have hG : G F = fun _ : ℝ => (0 : ℝ) := by
    funext t
    simpa [G] using hzeroF (Real.exp t) (Real.exp_pos t)
  have hcal : deriv (deriv (G F)) 0 = 1 := hCalib
  rw [hG] at hcal
  simp at hcal

/-- **Rescaling.** A solution of the unknown-coefficient law becomes a solution
of the pinned law after multiplying by `c/2`. The linear coefficients are fixed
at `2` by normalization, so this scale is the *entire* freedom in the combiner. -/
theorem compositionGen_scaled
    (c : ℝ) (F : ℝ → ℝ) (hGen : SatisfiesCompositionLawGen c F) :
    SatisfiesCompositionLaw (fun x => (c / 2) * F x) := by
  intro x y hx hy
  have h := hGen x y hx hy
  have : (c / 2) * F (x * y) + (c / 2) * F (x / y)
      = 2 * ((c / 2) * F x) * ((c / 2) * F y)
        + 2 * ((c / 2) * F x) + 2 * ((c / 2) * F y) := by
    have hexpand : (c / 2) * (F (x * y) + F (x / y))
        = (c / 2) * (c * F x * F y + 2 * F x + 2 * F y) := by
      rw [h]
    nlinarith [hexpand]
  simpa using this

/-- The reverse transport: if `s • F` satisfies the pinned law then `F` satisfies
the family law with product coefficient `2 * s`. This is the statement that the
solution sets of the family are a single scaling orbit. -/
theorem compositionGen_of_scaled
    (s : ℝ) (F : ℝ → ℝ) (hs : s ≠ 0)
    (hScaled : SatisfiesCompositionLaw (fun x => s * F x)) :
    SatisfiesCompositionLawGen (2 * s) F := by
  intro x y hx hy
  have h := hScaled x y hx hy
  simp only at h
  have hmul : s * (F (x * y) + F (x / y))
      = s * ((2 * s) * F x * F y + 2 * F x + 2 * F y) := by
    nlinarith [h]
  have := mul_left_cancel₀ hs hmul
  linarith [this]

/-- Calibration is linear in the scale: rescaling `F` by `s` rescales the
log-curvature by `s`. Unconditional, via `deriv_const_mul_field`. -/
theorem calibration_scaled (s : ℝ) (F : ℝ → ℝ) (hCalib : IsCalibrated F) :
    deriv (deriv (G (fun x => s * F x))) 0 = s := by
  have hG : G (fun x => s * F x) = fun t => s * G F t := by
    funext t; simp [G]
  rw [hG]
  have h1 : deriv (fun t : ℝ => s * G F t) = fun t : ℝ => s * deriv (G F) t := by
    funext t
    exact deriv_const_mul_field s
  rw [h1]
  have h2 : deriv (fun t : ℝ => s * deriv (G F) t) 0 = s * deriv (deriv (G F)) 0 :=
    deriv_const_mul_field s
  rw [h2, hCalib, mul_one]

/-! `Jcost` in log coordinates is `cosh t - 1`, so its log-curvature is `1`.
Proved locally so this module stays slim. -/

theorem G_jcost : G Cost.Jcost = fun t : ℝ => Real.cosh t - 1 := by
  funext t
  simp [G, Cost.Jcost, Real.cosh_eq, Real.exp_neg]

theorem jcost_calibrated : IsCalibrated Cost.Jcost := by
  change deriv (deriv (G Cost.Jcost)) 0 = 1
  rw [G_jcost]
  have h1 : deriv (fun t : ℝ => Real.cosh t - 1) = Real.sinh := by
    funext t
    simpa using (Real.hasDerivAt_cosh t).sub_const 1 |>.deriv
  rw [h1, Real.deriv_sinh]
  simp

/-- **The pin is forced, given that the rescaled solution is the recognition
cost.** The scale freedom in the combiner is exactly the scale freedom of `F`,
and calibration has already spent it: if `(c/2) • F` is `Jcost` on the positives
while `F` itself is calibrated, then `c = 2`.

The hypothesis `hJ` is what the composition law buys downstream, via
`compositionGen_scaled` and `law_of_logic_forces_jcost`. Keeping it explicit here
is deliberate: this module cannot import the Aczél smoothness instance without
pulling the `Cost` aggregate, and stating the theorem with an unused
`SatisfiesCompositionLawGen` hypothesis would be exactly the vacuity that
`L-kernel-state-premises-over-variables` forbids. -/
theorem combiner_forced_of_scaled_eq_jcost
    (c : ℝ) (F : ℝ → ℝ)
    (hCalib : IsCalibrated F)
    (hJ : ∀ x : ℝ, 0 < x → (c / 2) * F x = Cost.Jcost x) :
    c = 2 := by
  have hGeq : G (fun x => (c / 2) * F x) = G Cost.Jcost := by
    funext t
    simpa [G] using hJ (Real.exp t) (Real.exp_pos t)
  have hscale := calibration_scaled (c / 2) F hCalib
  rw [hGeq] at hscale
  have hone : deriv (deriv (G Cost.Jcost)) 0 = 1 := jcost_calibrated
  rw [hone] at hscale
  -- `hscale : 1 = c / 2`
  linarith [hscale]

/-! ## Section C: countermodels, cost sector -/

/-- Half the squared logarithm: the `c = 0` member of the bilinear family. -/
def logSqCost : ℝ → ℝ := fun x => (Real.log x) ^ 2 / 2

theorem logSqCost_G : G logSqCost = fun t : ℝ => t ^ 2 / 2 := by
  funext t
  simp [G, logSqCost, Real.log_exp]

theorem logSqCost_normalized : IsNormalized logSqCost := by
  simp [IsNormalized, logSqCost]

theorem logSqCost_continuous : ContinuousOn logSqCost (Set.Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  exact ((Real.continuousAt_log hx0).pow 2).div_const 2 |>.continuousWithinAt

theorem logSqCost_calibrated : IsCalibrated logSqCost := by
  have hd : deriv (fun t : ℝ => t ^ 2 / 2) = fun t : ℝ => t := by
    funext t
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) ((2 * t ^ (2 - 1)) / 2) t :=
      (hasDerivAt_pow 2 t).div_const 2
    rw [h1.deriv]
    norm_num
  change deriv (deriv (G logSqCost)) 0 = 1
  rw [logSqCost_G, hd]
  simp

/-- `logSqCost` satisfies the additive `c = 0` law: it is a genuine member of the
bilinear family, not a random function. -/
theorem logSqCost_compositionGen_zero : SatisfiesCompositionLawGen 0 logSqCost := by
  intro x y hx hy
  have hlog : Real.log (x * y) = Real.log x + Real.log y := Real.log_mul (ne_of_gt hx) (ne_of_gt hy)
  have hlogdiv : Real.log (x / y) = Real.log x - Real.log y := Real.log_div (ne_of_gt hx) (ne_of_gt hy)
  simp only [logSqCost, hlog, hlogdiv]
  ring

/-- **Countermodel: the composition law is independent.** `logSqCost` is
normalized, calibrated and continuous on the positives, and it fails the pinned
composition law, witnessed at `x = y = e`. -/
theorem logSqCost_not_composition : ¬ SatisfiesCompositionLaw logSqCost := by
  intro h
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hcalc := h (Real.exp 1) (Real.exp 1) he he
  rw [show Real.exp 1 * Real.exp 1 = Real.exp 2 by
        rw [← Real.exp_add]; norm_num,
      div_self (ne_of_gt he)] at hcalc
  simp only [logSqCost, Real.log_exp, Real.log_one] at hcalc
  norm_num at hcalc

/-- Constant zero: satisfies the composition law and normalization, fails
calibration. -/
theorem zeroCost_composition : SatisfiesCompositionLaw (fun _ : ℝ => (0 : ℝ)) := by
  intro x y _ _
  norm_num

theorem zeroCost_normalized : IsNormalized (fun _ : ℝ => (0 : ℝ)) := rfl

theorem zeroCost_continuous : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioi 0) :=
  continuousOn_const

/-- **Countermodel: calibration is independent.** -/
theorem zeroCost_not_calibrated : ¬ IsCalibrated (fun _ : ℝ => (0 : ℝ)) := by
  intro h
  have hzero : deriv (deriv (G (fun _ : ℝ => (0 : ℝ)))) 0 = 0 := by
    have hG : G (fun _ : ℝ => (0 : ℝ)) = fun _ : ℝ => (0 : ℝ) := by
      funext t; simp [G]
    rw [hG]; simp
  have hcal : deriv (deriv (G (fun _ : ℝ => (0 : ℝ)))) 0 = 1 := h
  rw [hzero] at hcal
  exact absurd hcal (by norm_num)

/-! ### The product coefficient is a choice

`coshTwoCost x = cosh (2 log x) - 1` is the `k = 2` member of the cosh family. It
solves the *pinned* law, and its calibrated rescaling `quarterCoshTwoCost` solves
the family law at product coefficient `8`. Since that rescaling is normalized,
calibrated and continuous while differing from `Jcost`, the product coefficient
cannot be derived: it is a unit convention, exactly one place where the
parameter-free telling spends a choice. -/

/-- `cosh (2 log x) - 1`, the `k = 2` member of the cosh family. -/
def coshTwoCost : ℝ → ℝ := fun x => (x ^ 2 + (x ^ 2)⁻¹) / 2 - 1

theorem coshTwoCost_normalized : IsNormalized coshTwoCost := by
  simp [IsNormalized, coshTwoCost]

theorem coshTwoCost_composition : SatisfiesCompositionLaw coshTwoCost := by
  intro x y hx hy
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  simp only [coshTwoCost]
  field_simp
  ring

/-- The calibrated member of the `k = 2` ray. -/
def quarterCoshTwoCost : ℝ → ℝ := fun x => ((x ^ 2 + (x ^ 2)⁻¹) / 2 - 1) / 4

theorem quarterCoshTwoCost_scaled :
    (fun x => (4 : ℝ) * quarterCoshTwoCost x) = coshTwoCost := by
  funext x
  simp only [quarterCoshTwoCost, coshTwoCost]
  ring

/-- The `k = 2` ray solves the family law at product coefficient `8`, not `2`. -/
theorem quarterCoshTwoCost_compositionGen :
    SatisfiesCompositionLawGen 8 quarterCoshTwoCost := by
  have h : SatisfiesCompositionLaw (fun x => (4 : ℝ) * quarterCoshTwoCost x) := by
    rw [quarterCoshTwoCost_scaled]
    exact coshTwoCost_composition
  have h8 : (8 : ℝ) = 2 * 4 := by norm_num
  rw [h8]
  exact compositionGen_of_scaled 4 quarterCoshTwoCost (by norm_num) h

theorem quarterCoshTwoCost_normalized : IsNormalized quarterCoshTwoCost := by
  simp [IsNormalized, quarterCoshTwoCost]

theorem quarterCoshTwoCost_continuous :
    ContinuousOn quarterCoshTwoCost (Set.Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hsq : (x ^ 2) ≠ 0 := pow_ne_zero 2 hx0
  have hc : ContinuousAt (fun x : ℝ => ((x ^ 2 + (x ^ 2)⁻¹) / 2 - 1) / 4) x := by
    fun_prop (disch := assumption)
  exact hc.continuousWithinAt

theorem quarterCoshTwoCost_G :
    G quarterCoshTwoCost = fun t : ℝ => (Real.cosh (2 * t) - 1) / 4 := by
  funext t
  have hexp : (Real.exp t) ^ 2 = Real.exp (2 * t) := by
    rw [← Real.exp_nat_mul]
    norm_num [two_mul]
  simp only [G, quarterCoshTwoCost, hexp, Real.cosh_eq]
  rw [← Real.exp_neg]

theorem quarterCoshTwoCost_calibrated : IsCalibrated quarterCoshTwoCost := by
  have hstep1 : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => (Real.cosh (2 * t) - 1) / 4)
        (Real.sinh (2 * t) * 2 / 4) t := by
    intro t
    have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    exact (((Real.hasDerivAt_cosh (2 * t)).comp t hlin).sub_const 1).div_const 4
  have hd1 : deriv (fun t : ℝ => (Real.cosh (2 * t) - 1) / 4)
      = fun t : ℝ => Real.sinh (2 * t) * 2 / 4 := by
    funext t
    exact (hstep1 t).deriv
  have hstep2 : HasDerivAt (fun t : ℝ => Real.sinh (2 * t) * 2 / 4)
      (Real.cosh (2 * (0 : ℝ)) * 2 * 2 / 4) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 (0 : ℝ) := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
    exact (((Real.hasDerivAt_sinh (2 * (0 : ℝ))).comp 0 hlin).mul_const 2).div_const 4
  change deriv (deriv (G quarterCoshTwoCost)) 0 = 1
  rw [quarterCoshTwoCost_G, hd1, hstep2.deriv]
  norm_num

/-- `quarterCoshTwoCost` is not the recognition cost: they differ at `x = 2`. -/
theorem quarterCoshTwoCost_ne_jcost :
    ¬ (∀ x : ℝ, 0 < x → quarterCoshTwoCost x = Cost.Jcost x) := by
  intro h
  have h2 := h 2 (by norm_num)
  simp only [quarterCoshTwoCost, Cost.Jcost] at h2
  norm_num at h2

/-- **Headline answer.** The product coefficient of the combiner is a CHOICE, not
a consequence. At coefficient `8` there is a normalized, calibrated, continuous
solution of the family law that is not the recognition cost, so no argument from
the remaining kernel members can recover the pinned `2`.

The honest reading: the combiner's linear coefficient is forced
(`linear_coefficient_forced`), its product coefficient is a unit convention, and
calibration does not spend it because rescaling the cost and rescaling the
log-frequency compensate each other along the family `c = 2 * k ^ 2`. This closes
`N-ufc-kernel-combiner-pin-open` on the "choice" branch and it means the kernel
keeps a calibration-shaped entry, stated plainly rather than laundered. -/
theorem product_coefficient_is_a_choice :
    ∃ (c : ℝ) (F : ℝ → ℝ),
      c ≠ 2 ∧
      SatisfiesCompositionLawGen c F ∧
      IsNormalized F ∧
      IsCalibrated F ∧
      ContinuousOn F (Set.Ioi 0) ∧
      ¬ (∀ x : ℝ, 0 < x → F x = Cost.Jcost x) :=
  ⟨8, quarterCoshTwoCost, by norm_num, quarterCoshTwoCost_compositionGen,
    quarterCoshTwoCost_normalized, quarterCoshTwoCost_calibrated,
    quarterCoshTwoCost_continuous, quarterCoshTwoCost_ne_jcost⟩

/-! ## Section D: countermodels, weight sector

`latticeWeight n = (1/φ)^n`. The weight members are factorization, positivity
and the self-similar step. -/

open MeasureForcing

/-- The **negative root** of the self-similar step equation. `x = 1/(1+x)` has
two solutions, `1/φ` and `-φ`, and only one of them is positive. -/
def negPhiWeight : ℕ → ℝ := fun n => (-Constants.phi) ^ n

theorem negPhiWeight_factorizes (m n : ℕ) :
    negPhiWeight (m + n) = negPhiWeight m * negPhiWeight n :=
  pow_add (-Constants.phi) m n

theorem negPhiWeight_step : negPhiWeight 1 = 1 / (1 + negPhiWeight 1) := by
  have hsq : Constants.phi ^ 2 = Constants.phi + 1 := Constants.phi_sq_eq
  have hone : (1 : ℝ) < Constants.phi := PhiSupport.one_lt_phi
  have hne : (1 : ℝ) + (-Constants.phi) ≠ 0 := by
    intro hcontra
    have : Constants.phi = 1 := by linarith
    linarith [hone, this]
  simp only [negPhiWeight, pow_one]
  field_simp
  nlinarith [hsq]

/-- **Countermodel: weight positivity is independent.** The negative root
satisfies factorization and the self-similar step, so neither of those members
forces positivity, and the forced measure fails at `n = 1`. -/
theorem negPhiWeight_not_pos : ¬ (∀ n : ℕ, 0 < negPhiWeight n) := by
  intro h
  have h1 := h 1
  have hone : (1 : ℝ) < Constants.phi := PhiSupport.one_lt_phi
  simp only [negPhiWeight, pow_one] at h1
  linarith

theorem negPhiWeight_ne_latticeWeight : negPhiWeight 1 ≠ latticeWeight 1 := by
  have hone : (1 : ℝ) < Constants.phi := PhiSupport.one_lt_phi
  have hpos : (0 : ℝ) < Constants.phi := lt_trans one_pos hone
  have hlat : latticeWeight 1 = 1 / Constants.phi := by
    simp [latticeWeight]
  rw [hlat]
  simp only [negPhiWeight, pow_one]
  intro hcontra
  have hinv : (0 : ℝ) < 1 / Constants.phi := by positivity
  linarith

/-- The constant weight at the fixed point: positive and self-similar, but not
multiplicative. -/
def constPhiWeight : ℕ → ℝ := fun _ => 1 / Constants.phi

theorem constPhiWeight_pos (n : ℕ) : 0 < constPhiWeight n := by
  have hone : (1 : ℝ) < Constants.phi := PhiSupport.one_lt_phi
  have : (0 : ℝ) < Constants.phi := lt_trans one_pos hone
  simp only [constPhiWeight]
  positivity

theorem constPhiWeight_step : constPhiWeight 1 = 1 / (1 + constPhiWeight 1) := by
  have hfp : Constants.phi = 1 + 1 / Constants.phi := PhiSupport.phi_fixed_point
  simp only [constPhiWeight]
  rw [← hfp]

/-- **Countermodel: factorization is independent.** -/
theorem constPhiWeight_not_factorizes :
    ¬ (∀ m n : ℕ, constPhiWeight (m + n) = constPhiWeight m * constPhiWeight n) := by
  intro h
  have h11 := h 1 1
  have hone : (1 : ℝ) < Constants.phi := PhiSupport.one_lt_phi
  have hpos : (0 : ℝ) < Constants.phi := lt_trans one_pos hone
  have hne : Constants.phi ≠ 0 := ne_of_gt hpos
  simp only [constPhiWeight] at h11
  field_simp at h11
  linarith

theorem constPhiWeight_ne_latticeWeight : constPhiWeight 0 ≠ latticeWeight 0 := by
  have hone : (1 : ℝ) < Constants.phi := PhiSupport.one_lt_phi
  have hpos : (0 : ℝ) < Constants.phi := lt_trans one_pos hone
  have hlat : latticeWeight 0 = 1 := by simp [latticeWeight]
  rw [hlat]
  simp only [constPhiWeight]
  intro hcontra
  rw [div_eq_one_iff_eq (ne_of_gt hpos)] at hcontra
  linarith

/-- The unit weight: positive and multiplicative, but not self-similar. -/
def unitWeight : ℕ → ℝ := fun _ => 1

theorem unitWeight_pos (n : ℕ) : 0 < unitWeight n := by
  simp [unitWeight]

theorem unitWeight_factorizes (m n : ℕ) :
    unitWeight (m + n) = unitWeight m * unitWeight n := by
  simp [unitWeight]

/-- **Countermodel: the self-similar step is independent.** -/
theorem unitWeight_not_step : unitWeight 1 ≠ 1 / (1 + unitWeight 1) := by
  simp only [unitWeight]
  norm_num

theorem unitWeight_ne_latticeWeight : unitWeight 1 ≠ latticeWeight 1 := by
  have hone : (1 : ℝ) < Constants.phi := PhiSupport.one_lt_phi
  have hpos : (0 : ℝ) < Constants.phi := lt_trans one_pos hone
  have hlat : latticeWeight 1 = 1 / Constants.phi := by simp [latticeWeight]
  rw [hlat]
  simp only [unitWeight]
  intro hcontra
  rw [eq_div_iff (ne_of_gt hpos)] at hcontra
  linarith

end

end KernelIndependence
end Foundation
end IndisputableMonolith
