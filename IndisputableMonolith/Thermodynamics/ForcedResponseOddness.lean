import Mathlib
import IndisputableMonolith.Thermodynamics.ForcedResponseLaw

/-!
# Reciprocity forces a symmetric transfer coefficient, once the mobility is drive-free

`ForcedResponseLaw` establishes that the gradient-flow reading of J-cost does not by
itself select the Butler-Volmer symmetry factor: `every_butlerVolmer_alpha_is_gradientFlux`
exhibits, for each `alpha`, a positive mobility reproducing that `alpha` exactly. That is
correct, and it was read as killing the prediction.

It does not, and the reason is visible in the witness. The absorbing mobility is
`butlerVolmerMobility alpha affinity = 4 * exp ((alpha - 1/2) * affinity)`, which depends
**exponentially on the drive**. A quantity that grows exponentially with the affinity it
is supposed to be responding to is not a mobility in the sense transport theory uses the
word: a mobility is a property of the medium, measured independently of the drive. So the
freedom the previous module found is real freedom in the formalism and illegitimate
freedom in the physics.

Impose the physical meaning and the prediction returns, by a route that needs no
calculus at all:

* `J x = J (1/x)` means the cost is **even** in the log-ratio coordinate;
* therefore the conjugate force `sinh` is **odd**;
* a mobility that does not depend on the drive cannot destroy that oddness, so the flux
  is odd;
* and Butler-Volmer is odd for exactly one value of its symmetry factor, one half.

`butlerVolmer_eq_constantMobilityFlux_forces_half` is that chain. Reciprocity plus a
drive-free mobility forces `alpha = 1/2`; nothing else is assumed, and no linearization
is used, so the conclusion holds at arbitrarily large overpotential.

What this buys empirically is stronger than the original claim, because it is harder to
satisfy by accident. It is a **joint** constraint on two independently measurable
quantities: a system with a measured `alpha` away from one half must exhibit a
drive-dependent mobility, and not merely any drive dependence but the specific profile
`exp ((alpha - 1/2) * affinity)` fixed by `butlerVolmer_factorization`. A reported
asymmetric `alpha` with a drive-free mobility refutes the framework outright.

Honest tier. Everything below is THEOREM: pure mathematics, no empirical input. The
identification of the physical flux with a J-cost gradient, and of the medium's mobility
with a drive-free factor, are the two named premises, and they are hypotheses of the
statements rather than claims about any real electrode.
-/

namespace IndisputableMonolith
namespace Thermodynamics
namespace ForcedResponseOddness

open Real
open ForcedResponseLaw

noncomputable section

/-! ## Reciprocity is evenness, and the conjugate force is odd -/

/-- Reciprocity `J x = J (1/x)` in the log-ratio coordinate: the cost is even. -/
theorem canonicalLogCost_even (s : ℝ) :
    canonicalLogCost (-s) = canonicalLogCost s := by
  rw [canonicalLogCost_eq_cosh_sub_one, canonicalLogCost_eq_cosh_sub_one, Real.cosh_neg]

/-- The force conjugate to an even cost is odd. -/
theorem conjugateForce_odd (s : ℝ) :
    deriv canonicalLogCost (-s) = -deriv canonicalLogCost s := by
  rw [canonicalLogCost_deriv, canonicalLogCost_deriv, Real.sinh_neg]

/-! ## A drive-free mobility preserves oddness -/

/-- Gradient flux with a mobility that does not depend on the drive, and a linear bridge
of scale `k`. This is `gradientFlux` with `mobility` a constant function. -/
def constantMobilityFlux (M k affinity : ℝ) : ℝ :=
  M * (k * sinh (k * affinity))

/-- The drive-free case is the specialization of the general gradient flux. -/
theorem constantMobilityFlux_eq_gradientFlux (M k affinity : ℝ) :
    constantMobilityFlux M k affinity =
      gradientFlux (fun _ => M) (linearBridge k) affinity := by
  rw [constantMobilityFlux, gradientFlux, linearBridge_cost_deriv]

/-- With a drive-free mobility the flux is an odd function of the drive. This is the
whole physical content: reciprocity makes the force odd, and a constant cannot break
oddness. -/
theorem constantMobilityFlux_odd (M k affinity : ℝ) :
    constantMobilityFlux M k (-affinity) = -constantMobilityFlux M k affinity := by
  rw [constantMobilityFlux, constantMobilityFlux]
  rw [show k * -affinity = -(k * affinity) by ring, Real.sinh_neg]
  ring

/-! ## Butler-Volmer is odd at exactly one symmetry factor -/

/-- The obstruction to oddness, in closed form: adding the Butler-Volmer shape at
opposite drives leaves a difference of two hyperbolic cosines, which vanishes for all
drives only when the symmetry factor is one half. -/
theorem butlerVolmer_add_reflected (alpha affinity : ℝ) :
    butlerVolmerShape alpha affinity + butlerVolmerShape alpha (-affinity) =
      2 * cosh (alpha * affinity) - 2 * cosh ((1 - alpha) * affinity) := by
  rw [butlerVolmerShape, butlerVolmerShape, Real.cosh_eq, Real.cosh_eq]
  have h1 : alpha * -affinity = -(alpha * affinity) := by ring
  have h2 : -(1 - alpha) * -affinity = (1 - alpha) * affinity := by ring
  have h3 : -(1 - alpha) * affinity = -((1 - alpha) * affinity) := by ring
  rw [h1, h2, h3]
  ring

/-- `cosh` agreeing at a point forces the arguments to agree in absolute value. -/
private theorem abs_eq_of_cosh_eq {x y : ℝ} (h : cosh x = cosh y) : |x| = |y| := by
  rcases lt_trichotomy |x| |y| with hlt | heq | hgt
  · exact absurd h (by have := Real.cosh_lt_cosh.mpr hlt; linarith)
  · exact heq
  · exact absurd h (by have := Real.cosh_lt_cosh.mpr hgt; linarith)

/-- **Butler-Volmer is odd if and only if its symmetry factor is one half.** -/
theorem butlerVolmer_odd_iff_half (alpha : ℝ) :
    (∀ affinity : ℝ, butlerVolmerShape alpha (-affinity) =
      -butlerVolmerShape alpha affinity) ↔ alpha = 1 / 2 := by
  constructor
  · intro hodd
    -- Oddness at drive 1 makes the reflected sum vanish, so the two cosines agree.
    have hsum : butlerVolmerShape alpha 1 + butlerVolmerShape alpha (-1) = 0 := by
      rw [hodd 1]; ring
    have hcosh : cosh (alpha * 1) = cosh ((1 - alpha) * 1) := by
      have := butlerVolmer_add_reflected alpha 1
      rw [hsum] at this
      linarith
    have habs : |alpha| = |1 - alpha| := by
      simpa using abs_eq_of_cosh_eq (by simpa using hcosh)
    -- Squaring removes the absolute values: alpha^2 = (1 - alpha)^2 gives 2*alpha = 1.
    have hsq : alpha ^ 2 = (1 - alpha) ^ 2 := by
      have := congrArg (fun t : ℝ => t ^ 2) habs
      simpa [sq_abs] using this
    nlinarith [hsq]
  · intro hhalf affinity
    subst hhalf
    rw [butlerVolmer_half_eq_two_sinh, butlerVolmer_half_eq_two_sinh,
      show -affinity / 2 = -(affinity / 2) by ring, Real.sinh_neg]
    ring

/-! ## The forcing theorem -/

/-- **Reciprocity plus a drive-free mobility forces the symmetry factor to one half.**

If the Butler-Volmer response of a process coincides with a J-cost gradient flow whose
mobility does not depend on the drive, then `alpha = 1/2`. No linearization is used, so
this holds at arbitrary overpotential, and no property of the medium is assumed beyond
the mobility being a property of the medium rather than of the drive. -/
theorem butlerVolmer_eq_constantMobilityFlux_forces_half
    {alpha M k : ℝ}
    (h : ∀ affinity : ℝ, butlerVolmerShape alpha affinity = constantMobilityFlux M k affinity) :
    alpha = 1 / 2 := by
  refine (butlerVolmer_odd_iff_half alpha).mp (fun affinity => ?_)
  rw [h (-affinity), h affinity, constantMobilityFlux_odd]

/-- The contrapositive, which is the falsifier a laboratory can aim at: a process whose
measured symmetry factor is not one half cannot be a J-cost gradient flow with any
drive-free mobility, at any bridge scale. -/
theorem alpha_ne_half_excludes_drive_free_mobility
    {alpha : ℝ} (halpha : alpha ≠ 1 / 2) :
    ¬ ∃ M k : ℝ, ∀ affinity : ℝ,
        butlerVolmerShape alpha affinity = constantMobilityFlux M k affinity := by
  rintro ⟨M, k, h⟩
  exact halpha (butlerVolmer_eq_constantMobilityFlux_forces_half h)

/-- And the positive companion: at one half the drive-free realization exists, with the
bridge scale and mobility both pinned. So the symmetric case is not merely permitted, it
is realized by a mobility of exactly 4 at bridge scale one half. -/
theorem half_is_realized_drive_free (affinity : ℝ) :
    butlerVolmerShape (1 / 2) affinity = constantMobilityFlux 4 (1 / 2) affinity := by
  rw [butlerVolmer_half_eq_two_sinh, constantMobilityFlux]
  ring_nf

end

end ForcedResponseOddness
end Thermodynamics
end IndisputableMonolith
