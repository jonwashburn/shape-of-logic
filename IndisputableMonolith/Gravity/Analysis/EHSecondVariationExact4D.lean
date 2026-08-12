import IndisputableMonolith.Gravity.Analysis.ContinuumTTSecondVariation4D

/-!
# The exact second variation of `∫ √g R`, and what it says about step 7's A3

Step 7 derived the continuum Einstein-Hilbert face `-(1/4)·|k|²·‖H‖²_F` from four
inputs.  Three of them (A1 the linearized Levi-Civita connection, A2 the linearized
Ricci tensor, and Regge's own normalization) are formalized.  The fourth, **A3**,
that `d²/dt² ∫√g R = -∫ h_{μν} G⁽¹⁾^{μν}`, is *stated and used* in
`ContinuumTTSecondVariation4D` and never derived there.  It is the one place in
arc 2's coefficient chain where a factor could still hide, because it is the step
that fixes the overall normalization of the density.

## What is now known, and how

A3 has been tested exactly, off Lean, by
`scripts/qg/eh_second_variation_exact_20260727.py`: for the metric family
`g_{μν}(t) = δ_{μν} + t H_{μν} cos(κ z)` in four Euclidean dimensions with the wave
along `z`, that script builds the **full** inverse metric, the **full** Christoffel
symbols, the **full** Ricci tensor and the **full** scalar curvature with no
expansion in `t` anywhere, then takes `d²/dt²` of `√(det g)·R` at `t = 0` and
averages over one wavelength.  It compares the result against `-∫h·G⁽¹⁾` built the
way `ContinuumTTSecondVariation4D` builds it.  Findings:

* On the plus polarization the exact density is `κ²·(7 sin²(κz) - 4)`, whose
  wavelength average is `-κ²/2`, which is exactly `-(1/4)·κ²·2` and so exactly the
  derived face.  Same on the cross polarization.  Same, scaled by four, on twice the
  plus polarization.
* A3's own right-hand side agrees with the exact left-hand side at **every** witness
  tried, including two that are not transverse-traceless (a transverse pure trace
  and a longitudinal perturbation).  So A3 is not an artefact of the TT reduction.
* The face formula is specific to TT, as it must be: the transverse pure trace has
  the same Frobenius square 2 and the same wave, and its exact average is `+κ²/2`,
  the opposite sign from the face.  A formula that fit that too would be fitting
  nothing.

That is a symbolic-algebra receipt, not a kernel one, so the exact curvature is
tagged **DERIVED-UNFORMALIZED** and this module does not assert it.

## What this module proves

Everything downstream of the closed form, in Lean, at the base triple: that the
exact density's wavelength average **is** the derived Einstein-Hilbert face, that it
therefore agrees with A3's right-hand side at the witness, that the two non-TT
decoys do **not** land on the face, and that no rescaling of the density survives.

## What remains open

One named goal: derive `d²/dt²(√(det g)·R)|_{t=0} = κ²(7 sin²(κz) - 4)` inside Lean
from `pd`, the Christoffel formula and the Ricci contraction, rather than from the
symbolic receipt.  `ContinuumTTSecondVariation4D.pd` is already the right
primitive (a one-dimensional `deriv` through `Function.update`, so no `fderiv`
machinery is needed), and for the plus polarization the perturbed metric is
diagonal, `diag(1, 1 + t cos κz, 1 - t cos κz, 1)`, so its inverse can be written
down explicitly and *proved* to be the inverse rather than obtained from
`Matrix.inv`.  The exact intermediate the script prints, for whoever formalizes it:

  `det g = 1 - t² cos²(κz)`
  `R = κ²t²(3t² sin⁴ - 7t² sin² + 4t² + 7 sin² - 4) / (2(1 - t² cos²)²)`

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace EHSecondVariationExact4D

open BigOperators
open EdgeTTDecomposition4D (Mat4 momentumSq)
open ContinuumTTSecondVariation4D (Pt phaseAverage densityOfPhase ehFace frobSq
  phaseAverage_const_mul ehFace_eq_phaseAverage)

noncomputable section

/-! ## §1. Two phase averages

`ContinuumTTSecondVariation4D` proves the cosine-squared mean.  The exact density
is a sine-squared plus a constant, so those are the two averages needed here.
-/

theorem phaseAverage_const (c : ℝ) : phaseAverage (fun _ => c) = c := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold phaseAverage
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  field_simp

theorem phaseAverage_sin_sq : phaseAverage (fun θ => Real.sin θ ^ 2) = 1 / 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold phaseAverage
  rw [integral_sin_sq]
  simp only [Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero, Real.cos_zero,
    zero_mul, sub_zero, sub_self]
  field_simp
  ring

/-- Average of `a·sin²θ + b`, which is the shape of every exact density below. -/
theorem phaseAverage_sin_sq_affine (a b : ℝ) :
    phaseAverage (fun θ => a * Real.sin θ ^ 2 + b) = a / 2 + b := by
  have hsin : IntervalIntegrable (fun θ : ℝ => a * Real.sin θ ^ 2)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (continuous_const.mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _ : ℝ => b)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    continuous_const.intervalIntegrable _ _
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold phaseAverage
  rw [intervalIntegral.integral_add hsin hconst,
    intervalIntegral.integral_const_mul, integral_sin_sq,
    intervalIntegral.integral_const]
  simp only [Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero, Real.cos_zero,
    zero_mul, sub_zero, sub_self, smul_eq_mul]
  field_simp
  ring

/-! ## §2. The exact densities

Each is `d²/dt²(√(det g)·R)` at `t = 0` on the named perturbation, written as a
function of the phase, as computed from the Christoffel definition by
`scripts/qg/eh_second_variation_exact_20260727.py`.  `m` is `|k|²`.
-/

/-- Exact second variation density on a transverse-traceless wave of Frobenius
square 2 (the plus and cross polarizations both give this). -/
def exactDensityTT (m : ℝ) (θ : ℝ) : ℝ := m * (7 * Real.sin θ ^ 2 - 4)

/-- Exact second variation density on a transverse **pure trace** of Frobenius
square 2.  Same mass, same wave, different physics. -/
def exactDensityTrace (m : ℝ) (θ : ℝ) : ℝ := m * Real.sin θ ^ 2

/-- Exact second variation density on a longitudinal perturbation, Frobenius
square 1.  It vanishes identically. -/
def exactDensityLongitudinal (_m : ℝ) (_θ : ℝ) : ℝ := 0

theorem exactDensityTT_average (m : ℝ) :
    phaseAverage (exactDensityTT m) = -(m / 2) := by
  have hrw : exactDensityTT m
      = fun θ => (7 * m) * Real.sin θ ^ 2 + (-(4 * m)) := by
    funext θ; unfold exactDensityTT; ring
  rw [hrw, phaseAverage_sin_sq_affine]
  ring

theorem exactDensityTrace_average (m : ℝ) :
    phaseAverage (exactDensityTrace m) = m / 2 := by
  have hrw : exactDensityTrace m = fun θ => m * Real.sin θ ^ 2 + 0 := by
    funext θ; unfold exactDensityTrace; ring
  rw [hrw, phaseAverage_sin_sq_affine]
  ring

theorem exactDensityLongitudinal_average (m : ℝ) :
    phaseAverage (exactDensityLongitudinal m) = 0 := by
  unfold exactDensityLongitudinal
  simpa using phaseAverage_const (0 : ℝ)

/-! ## §3. The exact computation lands on the derived face

Stated for any polarization of Frobenius square 2 and any wave covector, because
`ehFace` depends on `H` only through `frobSq H`.  The script's witness is a
relabeling of the banked plus and cross polarizations, both of which have
Frobenius square 2.
-/

/-- **The result.**  The wavelength average of the exact second variation equals
step 7's derived Einstein-Hilbert face.  No linearization was used to obtain the
left-hand side; A1 and A2 were used to obtain the right-hand side. -/
theorem exact_average_eq_ehFace (H : Mat4) (k : Pt) (hF : frobSq H = 2) :
    phaseAverage (exactDensityTT (momentumSq k)) = ehFace H k := by
  rw [exactDensityTT_average]
  unfold ContinuumTTSecondVariation4D.ehFace
  rw [hF]
  ring

/-- **A3 at the witness.**  Step 7's assumed right-hand side and the exact
left-hand side have the same wavelength average, so the assumption did not move
the coefficient. -/
theorem a3_agrees_with_exact (H : Mat4) (k : Pt) (hF : frobSq H = 2) :
    phaseAverage (exactDensityTT (momentumSq k)) = phaseAverage (densityOfPhase H k) := by
  rw [exact_average_eq_ehFace H k hF, ehFace_eq_phaseAverage]

/-! ## §4. Discrimination: the face formula is not fitting everything

A gate that never fires has not been tested.  These two perturbations are exactly
what a fit-anything face formula would also capture, and it does not capture them.
-/

/-- The transverse pure trace carries the same Frobenius square 2 and the same
wave, and its exact average has the **opposite sign** from the face.  So
`exact_average_eq_ehFace` is a statement about transverse-traceless data and not
about perturbations of mass 2. -/
theorem trace_decoy_misses_the_face (H : Mat4) (k : Pt) (hF : frobSq H = 2)
    (hm : momentumSq k ≠ 0) :
    phaseAverage (exactDensityTrace (momentumSq k)) ≠ ehFace H k := by
  rw [exactDensityTrace_average]
  unfold ContinuumTTSecondVariation4D.ehFace
  rw [hF]
  intro h
  apply hm
  have : momentumSq k / 2 + (1 / 4 : ℝ) * momentumSq k * 2 = 0 := by
    rw [h]; ring
  linarith [this]

/-- The longitudinal perturbation has vanishing exact second variation, which the
face formula does not report for a nonzero polarization. -/
theorem longitudinal_decoy_misses_the_face (H : Mat4) (k : Pt) (hF : frobSq H = 1)
    (hm : momentumSq k ≠ 0) :
    phaseAverage (exactDensityLongitudinal (momentumSq k)) ≠ ehFace H k := by
  rw [exactDensityLongitudinal_average]
  unfold ContinuumTTSecondVariation4D.ehFace
  rw [hF]
  intro h
  apply hm
  linarith [h]

/-- **Rigidity.**  Rescaling the exact density by any `c ≠ 1` breaks the agreement,
so the match is not a normalization that was free to be chosen. -/
theorem exact_density_rigid (m c : ℝ) (hm : m ≠ 0)
    (h : phaseAverage (fun θ => c * exactDensityTT m θ) = -(m / 2)) : c = 1 := by
  rw [phaseAverage_const_mul, exactDensityTT_average] at h
  have hm2 : -(m / 2) ≠ 0 := by
    intro hz; exact hm (by linarith)
  have hone : c * -(m / 2) = 1 * -(m / 2) := by rw [one_mul]; exact h
  exact mul_right_cancel₀ hm2 hone

/-! ## §5. Provenance, in one string -/

/-- What is derived here and what is not, in the words a referee needs. -/
def provenance : String :=
  "DERIVED IN LEAN: the wavelength averages, the identification of the exact TT \
density's average with step 7's derived face -(1/4)|k|^2||H||_F^2, the agreement \
of that average with A3's own right-hand side, the failure of a transverse pure \
trace of the same Frobenius mass and of a longitudinal perturbation to land on \
the face, and the rigidity of the coefficient under rescaling. \
DERIVED BUT NOT IN LEAN (symbolic algebra, scripts/qg/eh_second_variation_exact_20260727.py): \
that d^2/dt^2 of sqrt(det g) R at t=0 on the plus polarization is kappa^2(7 sin^2 - 4), \
computed from the full inverse metric, full Christoffels and full Ricci with no \
expansion in t, and the agreement of A3's two sides at five witnesses including two \
that are not transverse-traceless. NOT USED ANYWHERE HERE: the Regge tree, the \
coupling table, the Bloch symbol, the norm gate, or any banked coefficient."

end

end EHSecondVariationExact4D
end Analysis
end Gravity
end IndisputableMonolith
