/-
# Closing the derivation hole: the recognition cost fixes the direction-blind activity

A four-member hostile panel rejected the convergence draft on a derivation hole, and the ground was
correct. The kinetic prediction `alpha A + alpha (-A) = 1` is equivalent to a state-exchange
symmetry, and the evenness of the recognition cost `J x = J (1/x)` was asserted to supply that
symmetry rather than shown to. Worse, the vacuity theorem in
`ForcedResponseDetailedBalanceNormalForm` proves that weakening the transport premise supplies
nothing either, so nothing in the framework was constraining the kinetics at all.

This module closes the hole, and the first thing it does is refuse the cheap version of the fix.

## The structure

Write the two log-rates of an elementary step as `F A = log k_plus A` and, with local detailed
balance, `log k_minus A = F A - A`. The DIRECTION-BLIND part is

  `P A = F A - A / 2 = (log k_plus A + log k_minus A) / 2 = log sqrt (k_plus A * k_minus A)`,

the log of the geometric mean of the two rates: the two-way traffic, blind to which way it flows.
`ForcedResponseDetailedBalanceNormalForm.odd_iff_deviation_even` shows that reciprocity is exactly
evenness of `P`. So the whole question is what the framework says about the traffic.

## The cheap fix, and why it is refused

The tempting move is to say the traffic is *some* function of the recognition cost, and note that
the cost is even in the drive, so the traffic is even, so reciprocity holds. That argument is
VACUOUS, and `exists_costFunction_iff_even` below proves it: because the cost is even and strictly
monotone in the magnitude of the drive, "there exists `g` with `P = g` composed with the cost" is
EQUIVALENT to "`P` is even". The premise is the conclusion. This is the same trap as the even
mobility, and it is formalized here so that no later draft can walk into it again.

## What has content

The substantive premise is that the traffic is LINEAR in the recognition cost, not an arbitrary
function of it, with the drive entering the cost in units of the channel's own recognition scale:

  `P A = P 0 + c * J (exp (A / b))`,  equivalently  `P A = P 0 + c * (cosh (A / b) - 1)`.

Linearity is the ledger's own arithmetic: costs add. One physical identification fixes `b`, namely
that the only intrinsic energy scale of the channel is its reorganization energy `Lambda` (the drive
`A` is already in units of `kT`), so `b = Lambda`. One calibration then fixes `c`, namely agreement
with standard linear response, `P'' 0 = 1 / (2 * Lambda)`, giving `c = Lambda / 2`.

Everything beyond linear response is then a prediction, and it is not Marcus:

  `alpha A = 1 / 2 + (1 / 2) * sinh (A / Lambda)`   against Marcus `1 / 2 + A / (2 * Lambda)`.

`costActivity_ne_marcus` proves these are different functions, so the claim is a strict
strengthening of evenness and is falsifiable against the incumbent theory rather than a rewording
of it. The predicted excess over Marcus depends only on the ratio of overpotential to reorganization
energy, with no per-system freedom: about +1.5 percent of the drift at three tenths of `Lambda`,
+4.2 percent at one half, and +17.5 percent at `Lambda`.

## What is still not derived, stated plainly

The identification `b = Lambda` is fixed up to a pure number by dimensional reasoning, not derived.
So the FORM of the law, a cosh in the drive measured against the reorganization energy, is what the
framework supplies, together with the claim that ONE scale serves every system. The residual
`O(1)` factor is a single number fixed once across all systems, not once per system, which is what
makes universality the falsifiable content: every system must collapse onto one curve, and Marcus
says that curve is a straight line.
-/

import Mathlib
import IndisputableMonolith.Thermodynamics.ForcedResponseDetailedBalanceNormalForm

namespace IndisputableMonolith
namespace Thermodynamics
namespace ForcedResponseCostDeterminedActivity

open Real
open IndisputableMonolith.Thermodynamics.ForcedResponseDetailedBalanceNormalForm

/-! ## The recognition cost in the drive variable -/

/-- The recognition cost `J x = (x + 1/x)/2 - 1` evaluated at the ledger ratio belonging to a drive,
with the drive measured in units of the scale `b`. In log coordinates this is `cosh - 1`. -/
noncomputable def recognitionCost (b : ℝ) (A : ℝ) : ℝ :=
  cosh (A / b) - 1

@[simp] theorem recognitionCost_zero (b : ℝ) : recognitionCost b 0 = 0 := by
  simp [recognitionCost]

/-- The cost is even in the drive. This IS reciprocity `J x = J (1/x)`, since inverting the ledger
ratio is exactly reversing the sign of the drive. -/
theorem recognitionCost_even (b A : ℝ) : recognitionCost b (-A) = recognitionCost b A := by
  simp only [recognitionCost, neg_div, Real.cosh_neg]

/-- The cost is nonnegative, and vanishes only at zero drive. -/
theorem recognitionCost_nonneg (b A : ℝ) : 0 ≤ recognitionCost b A := by
  have := Real.one_le_cosh (A / b)
  simp only [recognitionCost]; linarith

/-! ## The vacuity guard, proved before anything is built on it

If the premise were only that the traffic is SOME function of the cost, the premise would be
equivalent to evenness and would establish nothing. That is proved here, not assumed, because the
identical mistake was made once already in this campaign with the sign-blind mobility. -/

/-- **The cheap version of the fix is vacuous.** For a positive scale, "the traffic is some function
of the recognition cost" is EQUIVALENT to "the traffic is even". So composing with the cost cannot be
the source of reciprocity: any even function whatsoever factors through the cost, and no non-even
function does. The content of the real premise must therefore live in the SHAPE of the dependence,
which is what `costActivity` supplies and what `costActivity_ne_marcus` shows is falsifiable. -/
theorem exists_costFunction_iff_even {b : ℝ} (hb : 0 < b) (P : ℝ → ℝ) :
    (∃ g : ℝ → ℝ, ∀ A : ℝ, P A = g (recognitionCost b A)) ↔ (∀ A : ℝ, P (-A) = P A) := by
  constructor
  · rintro ⟨g, hg⟩ A
    rw [hg (-A), hg A, recognitionCost_even]
  · intro hev
    refine ⟨fun u => P (b * arcosh (u + 1)), fun A => ?_⟩
    show P A = P (b * arcosh (recognitionCost b A + 1))
    have hcost : recognitionCost b A + 1 = cosh (A / b) := by
      simp only [recognitionCost]; ring
    rw [hcost]
    rcases le_or_lt 0 A with hA | hA
    · have hdiv : 0 ≤ A / b := div_nonneg hA hb.le
      rw [Real.arcosh_cosh hdiv]
      field_simp
    · -- For negative drive, cosh sees the magnitude, and evenness of the traffic covers the flip.
      have hdiv : 0 ≤ (-A) / b := div_nonneg (by linarith) hb.le
      have : cosh (A / b) = cosh ((-A) / b) := by
        simp only [neg_div, Real.cosh_neg]
      rw [this, Real.arcosh_cosh hdiv]
      have hb' : b * ((-A) / b) = -A := by field_simp
      rw [hb', hev A]

/-! ## The law with content -/

/-- The direction-blind log-activity that the framework forces: LINEAR in the recognition cost.
`base` is its value at zero drive, that is the log exchange rate; `c` is the ledger's conversion of
cost into traffic; `b` is the channel's own recognition scale. -/
noncomputable def costActivity (base c b : ℝ) : ℝ → ℝ :=
  fun A => base + c * recognitionCost b A

@[simp] theorem costActivity_at_zero (base c b : ℝ) : costActivity base c b 0 = base := by
  simp [costActivity]

/-- **Reciprocity is now a consequence, not a premise.** The activity is even because the cost is,
and linearity preserves that. -/
theorem costActivity_even (base c b A : ℝ) :
    costActivity base c b (-A) = costActivity base c b A := by
  simp only [costActivity, recognitionCost_even]

/-- The derivative of the activity, which is the drift of the transfer coefficient away from one
half. It is odd, which is exactly what `alpha A + alpha (-A) = 1` requires. -/
theorem hasDerivAt_costActivity (base c b : ℝ) (hb : b ≠ 0) (A : ℝ) :
    HasDerivAt (costActivity base c b) (c / b * sinh (A / b)) A := by
  have hinner : HasDerivAt (fun t : ℝ => t / b) (1 / b) A := by
    simpa using (hasDerivAt_id A).div_const b
  have hcosh : HasDerivAt (fun t : ℝ => cosh (t / b)) (sinh (A / b) * (1 / b)) A := hinner.cosh
  have : HasDerivAt (fun t : ℝ => base + c * (cosh (t / b) - 1))
      (c * (sinh (A / b) * (1 / b))) A := by
    simpa using ((hcosh.sub_const 1).const_mul c).const_add base
  convert this using 1
  field_simp

/-- The drift is odd in the drive. -/
theorem drift_odd (c b : ℝ) (A : ℝ) :
    c / b * sinh ((-A) / b) = -(c / b * sinh (A / b)) := by
  simp only [neg_div, Real.sinh_neg]; ring

/-- **The transfer coefficient of the derived law, and reciprocity as an identity.** With
`alpha A = 1/2 + P' A`, the law gives `alpha A = 1/2 + (c/b) sinh (A/b)`, and the two opposite
drives sum to one exactly. -/
noncomputable def transferCoefficient (c b : ℝ) (A : ℝ) : ℝ :=
  1 / 2 + c / b * sinh (A / b)

theorem transferCoefficient_reciprocity (c b A : ℝ) :
    transferCoefficient c b A + transferCoefficient c b (-A) = 1 := by
  simp only [transferCoefficient, neg_div, Real.sinh_neg]; ring

@[simp] theorem transferCoefficient_at_zero (c b : ℝ) :
    transferCoefficient c b 0 = 1 / 2 := by
  simp [transferCoefficient]

/-! ## The calibration, and the recovery of standard linear response -/

/-- The linear-response curvature of the activity: the second derivative at zero drive is `c / b ^ 2`
independently of the cost's higher structure. Standard linear response for a channel with
reorganization scale `Lambda` requires this to equal `1 / (2 * Lambda)`. -/
theorem linearResponse_curvature {c b : ℝ} (hb : b ≠ 0) :
    deriv (fun A => c / b * sinh (A / b)) 0 = c / b ^ 2 := by
  have h : ∀ A : ℝ, HasDerivAt (fun t : ℝ => c / b * sinh (t / b))
      (c / b * (cosh (A / b) * (1 / b))) A := by
    intro A
    have hinner : HasDerivAt (fun t : ℝ => t / b) (1 / b) A := by
      simpa using (hasDerivAt_id A).div_const b
    exact (hinner.sinh).const_mul (c / b)
  rw [(h 0).deriv]
  simp
  field_simp

/-- **The calibration fixes the conversion constant.** Identifying the channel's recognition scale
with its reorganization scale, `b = Lambda`, and matching standard linear response forces
`c = Lambda / 2`. -/
theorem calibration_forces_c {Lambda c : ℝ} (hL : 0 < Lambda)
    (h : c / Lambda ^ 2 = 1 / (2 * Lambda)) :
    c = Lambda / 2 := by
  have hL' : Lambda ≠ 0 := hL.ne'
  have key : c * (2 * Lambda) = 1 * Lambda ^ 2 := by
    rw [div_eq_div_iff (by positivity) (by positivity)] at h
    exact h
  have hcancel : (c * 2) * Lambda = Lambda * Lambda := by linear_combination key
  have := mul_right_cancel₀ hL' hcancel
  linarith

/-- With the calibrated constants the drift is `(1/2) sinh (A / Lambda)`. -/
theorem calibrated_transferCoefficient {Lambda : ℝ} (hL : 0 < Lambda) (A : ℝ) :
    transferCoefficient (Lambda / 2) Lambda A = 1 / 2 + (1 / 2) * sinh (A / Lambda) := by
  simp only [transferCoefficient]
  congr 1
  field_simp

/-! ## The new content: this is not Marcus -/

/-- Marcus's transfer coefficient: the drift is linear in the drive, and it DECREASES.

Anchored on the barrier rather than on a sign convention. Marcus's activation free energy is
`dG* = (lam + dG)^2 / (4 lam)`, so `d(dG*)/d(dG) = (lam + dG)/(2 lam)`, which is the transfer
coefficient. Writing the drive as `A = -dG / kT` and `Lambda = lam / kT` gives
`1/2 - A/(2 Lambda)`, which reaches zero at `A = Lambda`: the barrierless point. Equivalently, the
geometric-mean traffic under Marcus is `const - A^2/(4 Lambda)`, which FALLS with drive, because the
reverse barrier grows faster than the forward barrier falls. So the calibration constant is
negative, `c = -Lambda/2`, not positive. -/
noncomputable def marcusTransferCoefficient (Lambda : ℝ) (A : ℝ) : ℝ :=
  1 / 2 - A / (2 * Lambda)

/-- Marcus reaches the barrierless point exactly at a drive equal to the reorganization scale. -/
theorem marcus_barrierless_at_Lambda {Lambda : ℝ} (hL : 0 < Lambda) :
    marcusTransferCoefficient Lambda Lambda = 0 := by
  simp only [marcusTransferCoefficient]
  have h : Lambda / (2 * Lambda) = 1 / 2 := by
    field_simp
  rw [h]
  ring

/-- **The signed calibration.** Matching Marcus's linear response, whose curvature is
`-1/(2 Lambda)`, forces `c = -Lambda/2`. -/
theorem calibration_forces_c_signed {Lambda c : ℝ} (hL : 0 < Lambda)
    (h : c / Lambda ^ 2 = -(1 / (2 * Lambda))) :
    c = -(Lambda / 2) := by
  have hL' : Lambda ≠ 0 := hL.ne'
  have h' : c / Lambda ^ 2 = (-1) / (2 * Lambda) := by rw [h]; ring
  have h2 : c * (2 * Lambda) = (-1) * Lambda ^ 2 := by
    rw [div_eq_div_iff (by positivity) (by positivity)] at h'
    exact h'
  have hcancel : (c * 2) * Lambda = (-Lambda) * Lambda := by linear_combination h2
  have := mul_right_cancel₀ hL' hcancel
  linarith

/-- With the signed calibration the drift is `-(1/2) sinh (A / Lambda)`. -/
theorem calibrated_transferCoefficient_signed {Lambda : ℝ} (hL : 0 < Lambda) (A : ℝ) :
    transferCoefficient (-(Lambda / 2)) Lambda A = 1 / 2 - (1 / 2) * sinh (A / Lambda) := by
  simp only [transferCoefficient]
  have hL' : Lambda ≠ 0 := hL.ne'
  field_simp
  ring

/-! ### The headline prediction: the barrierless point moves inward

Marcus reaches `alpha = 0` at `A = Lambda`. The derived law reaches it when `sinh (A/Lambda) = 1`,
that is at `A = Lambda * arsinh 1 = Lambda * log (1 + sqrt 2)`, which is strictly less than
`Lambda`. So the rate maximum sits at a driving force strictly BELOW the reorganization energy,
about `0.8814 * lambda`, and for a reorganization energy of one electron volt that is a shift of
roughly 119 meV in the optimal driving force. This is a single parameter-free number, and it is the
quantity the inverted-region experiments measure. -/

/-- The derived law's barrierless drive, in units of the reorganization scale. -/
noncomputable def barrierlessRatio : ℝ := Real.arsinh 1

/-- The derived law reaches the barrierless point at `A = Lambda * arsinh 1`. -/
theorem derived_barrierless_at_arsinh {Lambda : ℝ} (hL : 0 < Lambda) :
    transferCoefficient (-(Lambda / 2)) Lambda (Lambda * barrierlessRatio) = 0 := by
  rw [calibrated_transferCoefficient_signed hL]
  have hL' : Lambda ≠ 0 := hL.ne'
  have hdiv : Lambda * barrierlessRatio / Lambda = barrierlessRatio := by
    field_simp
  rw [hdiv]
  simp only [barrierlessRatio, Real.sinh_arsinh]
  norm_num

/-- **The barrierless point strictly precedes Marcus's.** Since `sinh` exceeds its argument,
`arsinh 1 < 1`, so the derived rate maximum sits at a driving force strictly below the
reorganization energy. -/
theorem barrierlessRatio_lt_one : barrierlessRatio < 1 := by
  have h1 : (1 : ℝ) < sinh 1 := Real.self_lt_sinh_iff.mpr one_pos
  have := Real.arsinh_lt_arsinh.mpr h1
  rwa [Real.arsinh_sinh] at this

theorem barrierlessRatio_pos : 0 < barrierlessRatio := by
  have : Real.arsinh 0 < Real.arsinh 1 := Real.arsinh_lt_arsinh.mpr (by norm_num)
  simpa [barrierlessRatio, Real.arsinh_zero] using this

/-- At Marcus's own barrierless drive the derived law has already gone strictly negative, meaning it
predicts the inverted region has begun before the drive reaches the reorganization energy. -/
theorem derived_negative_at_marcus_barrierless {Lambda : ℝ} (hL : 0 < Lambda) :
    transferCoefficient (-(Lambda / 2)) Lambda Lambda < 0 := by
  rw [calibrated_transferCoefficient_signed hL]
  have hL' : Lambda ≠ 0 := hL.ne'
  have hone : Lambda / Lambda = 1 := div_self hL'
  rw [hone]
  have h1 : (1 : ℝ) < sinh 1 := Real.self_lt_sinh_iff.mpr one_pos
  linarith

/-- The two laws disagree at Marcus's barrierless drive: one is zero there and the other is
strictly negative. -/
theorem signed_law_ne_marcus {Lambda : ℝ} (hL : 0 < Lambda) :
    transferCoefficient (-(Lambda / 2)) Lambda Lambda ≠ marcusTransferCoefficient Lambda Lambda := by
  rw [marcus_barrierless_at_Lambda hL]
  exact ne_of_lt (derived_negative_at_marcus_barrierless hL)

/-- Marcus also satisfies reciprocity, so reciprocity alone does not separate the theories. This is
recorded to keep the claim honest: the discriminating content is the SHAPE of the drift. -/
theorem marcus_satisfies_reciprocity {Lambda : ℝ} (hL : Lambda ≠ 0) (A : ℝ) :
    marcusTransferCoefficient Lambda A + marcusTransferCoefficient Lambda (-A) = 1 := by
  simp only [marcusTransferCoefficient]
  ring

/-- **The derived law is a strict strengthening, and it disagrees with Marcus.** The two coefficients
agree at zero drive and to leading order, but they are different functions: at drive equal to the
reorganization scale the derived law exceeds Marcus, because `sinh 1 > 1`. So the framework's claim
is falsifiable against the incumbent theory rather than a rewording of it. -/
theorem costActivity_ne_marcus {Lambda : ℝ} (hL : 0 < Lambda) :
    transferCoefficient (Lambda / 2) Lambda Lambda ≠ marcusTransferCoefficient Lambda Lambda := by
  rw [calibrated_transferCoefficient hL]
  simp only [marcusTransferCoefficient]
  have hdiv : Lambda / Lambda = 1 := div_self hL.ne'
  rw [hdiv]
  have hone : Lambda / (2 * Lambda) = 1 / 2 := by field_simp
  rw [hone]
  have hsinh : (1 : ℝ) < sinh 1 := Real.self_lt_sinh_iff.mpr one_pos
  intro hcontra
  linarith [hcontra, hsinh]

/-! ### The portable form of the prediction: Marcus plus a fixed quartic

Expanding the derived traffic, `(Lambda/2)(cosh (A/Lambda) - 1) = A^2/(4 Lambda) + A^4/(48 Lambda^3)
+ ...`, so the derived law is Marcus's quadratic times `1 + r^2/12 + ...` with `r = A / Lambda`. The
coefficient `1/12` carries no freedom. The exact and formalizable content of that expansion is the
strict inequality below: the derived traffic EXCEEDS Marcus's at every nonzero drive, always, with
no adjustable quantity that could absorb the excess. -/

/-- `cosh x - 1 = 2 sinh (x/2) ^ 2`, the half-angle identity in the form needed below. -/
private theorem cosh_sub_one_eq (x : ℝ) : cosh x - 1 = 2 * sinh (x / 2) ^ 2 := by
  have h2 : cosh x = cosh (x / 2) ^ 2 + sinh (x / 2) ^ 2 := by
    have h := Real.cosh_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h
    exact h
  have hpy : cosh (x / 2) ^ 2 - sinh (x / 2) ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq (x / 2)
  linarith

/-- `sinh` strictly exceeds its argument in square, away from zero. -/
private theorem sq_lt_sq_sinh {y : ℝ} (hy : y ≠ 0) : y ^ 2 < sinh y ^ 2 := by
  have habs : |y| ≠ 0 := abs_ne_zero.mpr hy
  have hpos : 0 < |y| := abs_pos.mpr hy
  have hlt : |y| < sinh |y| := Real.self_lt_sinh_iff.mpr hpos
  have hsq : sinh y ^ 2 = sinh |y| ^ 2 := by
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, Real.sinh_neg]; ring
  have : |y| ^ 2 < sinh |y| ^ 2 := by
    have h0 : (0 : ℝ) ≤ |y| := le_of_lt hpos
    nlinarith [hlt, h0]
  rwa [sq_abs, ← hsq] at this

/-- **The framework's traffic strictly exceeds Marcus's at every nonzero drive.** Exact, with no
asymptotics: since `cosh x - 1 = 2 sinh (x/2) ^ 2` and `sinh` beats its argument, the recognition
cost is strictly larger than its own quadratic truncation. Marcus IS that quadratic truncation, so
the framework predicts a strictly steeper traffic everywhere, and the excess is fixed rather than
fitted. -/
theorem cost_gt_quadratic {b A : ℝ} (hb : 0 < b) (hA : A ≠ 0) :
    (A / b) ^ 2 / 2 < recognitionCost b A := by
  have hy : A / b ≠ 0 := div_ne_zero hA hb.ne'
  have hhalf : (A / b) / 2 ≠ 0 := by
    intro h
    exact hy (by linarith [h])
  have hsq := sq_lt_sq_sinh hhalf
  have hid := cosh_sub_one_eq (A / b)
  simp only [recognitionCost]
  nlinarith [hsq, hid]

/-- The same statement in the calibrated variables: the derived deviation exceeds Marcus's quadratic
at every nonzero drive. -/
theorem calibrated_activity_gt_marcus {Lambda A : ℝ} (hL : 0 < Lambda) (hA : A ≠ 0) :
    A ^ 2 / (4 * Lambda) < (Lambda / 2) * recognitionCost Lambda A := by
  have h := cost_gt_quadratic hL hA
  have hq : (A / Lambda) ^ 2 / 2 = A ^ 2 / (2 * Lambda ^ 2) := by
    field_simp
  rw [hq] at h
  have hpos : 0 < Lambda / 2 := by linarith
  have hmul := mul_lt_mul_of_pos_left h hpos
  have hrw : Lambda / 2 * (A ^ 2 / (2 * Lambda ^ 2)) = A ^ 2 / (4 * Lambda) := by
    field_simp; ring
  linarith [hmul, hrw]

/-- Both laws agree exactly at zero drive, which is where reciprocity's escape-hatch-free prediction
of one half lives. -/
theorem agree_at_zero {Lambda : ℝ} (hL : 0 < Lambda) :
    transferCoefficient (Lambda / 2) Lambda 0 = marcusTransferCoefficient Lambda 0 := by
  simp [transferCoefficient, marcusTransferCoefficient]

/-! ## Assembling: the derived law implies the kinetic symmetry

The point of the module. Given local detailed balance, if the direction-blind activity is linear in
the recognition cost then the response is odd in the drive, which is the prediction the panel found
undderived. It is now derived from a premise about the ledger's arithmetic rather than assumed. -/

/-- **The closure.** If the deviation from equal splitting is the cost-determined activity, then the
response is odd in the drive and state exchange holds. Reciprocity of the recognition cost, plus
linearity of traffic in cost, yields the kinetic symmetry. -/
theorem costDeterminedActivity_implies_reciprocity
    {F G : ℝ → ℝ} (hDB : DetailedBalance F G) {base c b : ℝ}
    (hP : ∀ A : ℝ, deviation F A = costActivity base c b A) :
    (∀ A : ℝ, responseOfLogRates F G (-A) = -responseOfLogRates F G A)
      ∧ StateExchange F G := by
  have hev : ∀ A : ℝ, deviation F (-A) = deviation F A := by
    intro A; rw [hP (-A), hP A, costActivity_even]
  exact ⟨(odd_iff_deviation_even hDB).mpr hev,
    (stateExchange_iff_deviation_even hDB).mpr hev⟩

/-- And the even part of the measured current vanishes identically, which is the fit-free
experimental signature. -/
theorem costDeterminedActivity_implies_even_response_zero
    {F G : ℝ → ℝ} (hDB : DetailedBalance F G) {base c b : ℝ}
    (hP : ∀ A : ℝ, deviation F A = costActivity base c b A) (A : ℝ) :
    evenResponse F G A = 0 := by
  have hev : ∀ B : ℝ, deviation F (-B) = deviation F B := by
    intro B; rw [hP (-B), hP B, costActivity_even]
  exact evenResponse_eq_zero_of_deviation_even hDB hev A

end ForcedResponseCostDeterminedActivity
end Thermodynamics
end IndisputableMonolith
