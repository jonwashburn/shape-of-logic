import Mathlib
import IndisputableMonolith.Thermodynamics.ForcedResponseLargeDeviationBridge

/-!
# Reciprocity needs a sign-blind mobility, not a drive-free one

`ForcedResponseOddness` proved that reciprocity plus a mobility independent of the drive forces
the Butler-Volmer symmetry factor to one half. That premise is stronger than the argument needs,
and the excess strength produced a false empirical conclusion, recorded and now retracted.

The argument runs: reciprocity `J x = J (1/x)` makes the cost even in the log-ratio, so the
conjugate force is odd, so the flux is odd, so the response is symmetric. The only thing the
mobility has to do is not destroy oddness. A constant cannot destroy it, but neither can any
**even** function of the drive, since even times odd is odd. So the premise is not that the
medium ignores the drive; it is that the medium cannot tell which way the drive points.

That distinction decides an empirical question. Measured Tafel plots curve, and the transfer
coefficient drifts with overpotential roughly as Marcus predicts, `alpha = 1/2 + A/(2*Lambda)`
in dimensionless drive `A` and reorganization energy `Lambda`. Reading the required mobility off
`butlerVolmer_factorization` gives `M A = 4 * exp ((alpha - 1/2) * A)`, so the Marcus drift needs

    M A = 4 * exp (A^2 / (2*Lambda)),

which is **even**. Measured curvature therefore does not touch reciprocity at all.
`marcus_drift_preserves_oddness` is that statement. An earlier audit in this campaign concluded
from the observed curvature that a drive-free mobility fails above roughly `0.3*Lambda` and
recorded it as a wall on the recognition response law. The conclusion was wrong: it tested
drive-freedom, which the framework does not need, rather than sign-blindness, which it does.

What reciprocity does forbid is an odd component in the mobility, and that has an observable
signature. Writing the response with independent anodic and cathodic coefficients,
`exp (a*A) - exp (-(b*A))`, oddness holds exactly when `a = b`
(`eq_of_twoCoefficientShape_odd`). So the prediction is that the two branches have Tafel slopes
of equal magnitude at every overpotential. Note this is weaker than, and should not be confused
with, the Butler-Volmer bookkeeping convention `a + b = 1`: at `a = b = 2/5` the response
`2*sinh (2*A/5)` is perfectly odd while summing to `4/5`. Combining `a = b` with the pinned
bridge scale of `ForcedResponseLargeDeviationBridge` is what returns one half.

Honest tier. Everything here is THEOREM: real analysis, no empirical input. The two premises are
hypotheses of the statements, not claims about any electrode.

## Superseded, 2026-07-25, by a hostile referee read this program agrees with

Read `ForcedResponseDetailedBalanceNormalForm` before relying on anything below. Two corrections
land there, both of which this module got wrong:

1. **The sign-blind framing is empty.** For any odd `j`, setting `M A = j A / (k * sinh (k*A))`
 gives an even `M`, since a quotient of odd functions is even. So "there exists an even mobility
 reproducing `j`" is *equivalent* to `j` being odd and constrains nothing
 (`exists_even_mobility_iff_odd`). The theorems below are true and their mobility language is
 decoration; the content is oddness alone.
2. **`a = b` is not the prediction, and cannot be.** Local detailed balance already forces
 `a + b = 1`, because `k_plus / k_minus = exp ((a+b) * A)` must equal `exp A`. So `a + b = 1` is
 not a bookkeeping convention as claimed below, and the illustration `a = b = 2/5` is a rescaled
 drive rather than a physical alternative. With constant coefficients, `a = b` plus detailed
 balance gives exactly `alpha = 1/2`, which is Marcus 1965, so there is no daylight. The real
 prediction needs drive-dependent coefficients: `alpha A + alpha (-A) = 1`, relating one
 direction at two drives, where detailed balance relates two directions at one drive. See
 `odd_iff_deviation_even`.
-/

namespace IndisputableMonolith
namespace Thermodynamics
namespace ForcedResponseSignBlindMobility

open Real
open ForcedResponseLaw
open ForcedResponseOddness

noncomputable section

/-! ## A drive-dependent mobility, and the weakest premise that keeps the flux odd -/

/-- Gradient flux with a mobility allowed to depend on the drive, at linear bridge scale `k`. -/
def generalFlux (M : ℝ → ℝ) (k A : ℝ) : ℝ :=
  M A * (k * sinh (k * A))

/-- The drive-free case of `ForcedResponseOddness` is the constant-mobility specialization. -/
theorem generalFlux_const (M k A : ℝ) :
    generalFlux (fun _ => M) k A = constantMobilityFlux M k A := by
  rw [generalFlux, constantMobilityFlux]

/-- **A sign-blind mobility keeps the flux odd.** This is the premise the reciprocity argument
actually requires: the medium may respond to the strength of the drive, but not to its sign. -/
theorem generalFlux_odd_of_even_mobility
    {M : ℝ → ℝ} (hM : ∀ A : ℝ, M (-A) = M A) (k A : ℝ) :
    generalFlux M k (-A) = -generalFlux M k A := by
  rw [generalFlux, generalFlux, hM A]
  rw [show k * -A = -(k * A) by ring, Real.sinh_neg]
  ring

/-! ## The Marcus drift is even, so measured curvature does not touch reciprocity -/

/-- The mobility that reproduces the Marcus drift `alpha = 1/2 + A/(2*Lambda)`.

Corrected 2026-07-25: the exponent is `A^2/(4*Lambda)`, not `A^2/(2*Lambda)`. A measured transfer
coefficient is a *differential* slope, `alpha = dF/dA` for `F` the log forward rate, so
`alpha A = 1/2 + A/(2*Lambda)` integrates to `F A = A/2 + A^2/(4*Lambda)`. Reading
`M A = 4 * exp ((alpha - 1/2) * A)` off `butlerVolmer_factorization` treats `alpha` as sitting
directly in the exponent and doubles the quadratic term. See
`ForcedResponseDetailedBalanceNormalForm.marcusDeviation`. -/
def marcusMobility (Lambda : ℝ) : ℝ → ℝ :=
  fun A => 4 * exp (A ^ 2 / (4 * Lambda))

/-- The Marcus mobility is even in the drive. -/
theorem marcusMobility_even (Lambda A : ℝ) :
    marcusMobility Lambda (-A) = marcusMobility Lambda A := by
  simp only [marcusMobility, neg_sq]

/-- At zero drive the Marcus mobility is the pinned value four, so the drive-free result of
`ForcedResponseLargeDeviationBridge` is its zero-drive limit rather than a competitor. -/
theorem marcusMobility_at_zero (Lambda : ℝ) : marcusMobility Lambda 0 = 4 := by
  simp [marcusMobility]

/-- **The Marcus drift preserves oddness.** A transfer coefficient drifting with overpotential
exactly as Marcus theory says is fully consistent with reciprocity. Observed Tafel curvature is
therefore not evidence against the recognition response law, and the earlier audit conclusion
that it bounded the law above `0.3*Lambda` is retracted by this theorem. -/
theorem marcus_drift_preserves_oddness (Lambda k A : ℝ) :
    generalFlux (marcusMobility Lambda) k (-A) = -generalFlux (marcusMobility Lambda) k A :=
  generalFlux_odd_of_even_mobility (marcusMobility_even Lambda) k A

/-! ## What reciprocity does forbid: unequal anodic and cathodic coefficients -/

/-- The response written with independent anodic and cathodic coefficients. Butler-Volmer is the
special case `b = 1 - a`; nothing here imposes that convention. -/
def twoCoefficientShape (a b A : ℝ) : ℝ :=
  exp (a * A) - exp (-(b * A))

/-- Butler-Volmer is the `b = 1 - a` slice. -/
theorem butlerVolmerShape_eq_twoCoefficientShape (alpha A : ℝ) :
    butlerVolmerShape alpha A = twoCoefficientShape alpha (1 - alpha) A := by
  rw [butlerVolmerShape, twoCoefficientShape,
    show -(1 - alpha) * A = -((1 - alpha) * A) by ring]

/-- Equal coefficients give an odd response. -/
theorem twoCoefficientShape_odd_of_eq (a A : ℝ) :
    twoCoefficientShape a a (-A) = -twoCoefficientShape a a A := by
  simp only [twoCoefficientShape, mul_neg, neg_neg]
  ring

/-- `cosh` agreeing at a point forces the arguments to agree in absolute value. -/
private theorem abs_eq_of_cosh_eq {x y : ℝ} (h : cosh x = cosh y) : |x| = |y| := by
  rcases lt_trichotomy |x| |y| with hlt | heq | hgt
  · exact absurd h (by have := Real.cosh_lt_cosh.mpr hlt; linarith)
  · exact heq
  · exact absurd h (by have := Real.cosh_lt_cosh.mpr hgt; linarith)

/-- **An odd response forces equal anodic and cathodic coefficients.** The observable content of
reciprocity: the two branches must have Tafel slopes of equal magnitude, at every drive. -/
theorem eq_of_twoCoefficientShape_odd
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hodd : ∀ A : ℝ, twoCoefficientShape a b (-A) = -twoCoefficientShape a b A) :
    a = b := by
  -- Oddness at drive one turns into equality of two hyperbolic cosines.
  have h1 := hodd 1
  simp only [twoCoefficientShape, mul_one, mul_neg, neg_neg] at h1
  have hcosh : cosh a = cosh b := by
    rw [Real.cosh_eq, Real.cosh_eq]
    linarith [h1]
  have habs : |a| = |b| := abs_eq_of_cosh_eq hcosh
  rwa [abs_of_pos ha, abs_of_pos hb] at habs

/-- The converse packaging: a sign-blind mobility realizing a two-coefficient response forces
the coefficients equal. This is the falsifiable statement, and the laboratory aims at its
contrapositive. -/
theorem even_mobility_match_forces_equal_coefficients
    {M : ℝ → ℝ} {a b k : ℝ}
    (hM : ∀ A : ℝ, M (-A) = M A) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ A : ℝ, twoCoefficientShape a b A = generalFlux M k A) :
    a = b := by
  refine eq_of_twoCoefficientShape_odd ha hb (fun A => ?_)
  rw [h (-A), h A, generalFlux_odd_of_even_mobility hM]

/-- Unequal measured coefficients exclude every sign-blind mobility at every bridge scale. A
system with genuinely asymmetric anodic and cathodic Tafel slopes is not one channel driven both
ways. -/
theorem unequal_coefficients_exclude_sign_blind_mobility
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    ¬ ∃ (M : ℝ → ℝ) (k : ℝ), (∀ A : ℝ, M (-A) = M A) ∧
        ∀ A : ℝ, twoCoefficientShape a b A = generalFlux M k A := by
  rintro ⟨M, k, hM, h⟩
  exact hne (even_mobility_match_forces_equal_coefficients hM ha hb h)

/-- Equal coefficients plus the Butler-Volmer bookkeeping convention `a + b = 1` return one half.
Stated to keep the two conditions distinct: oddness alone gives `a = b`, and `a = b = 2/5` is
odd while violating the convention. -/
theorem eq_and_sum_one_forces_half {a b : ℝ} (heq : a = b) (hsum : a + b = 1) :
    a = 1 / 2 := by
  rw [heq] at hsum
  linarith

end

end ForcedResponseSignBlindMobility
end Thermodynamics
end IndisputableMonolith
