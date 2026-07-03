import Mathlib
import IndisputableMonolith.Masses.L1bChamberVolume
import IndisputableMonolith.Masses.L1bDensityCertificate
import IndisputableMonolith.Masses.LeptonTorsionKernel

/-!
# L1b chamber density bridge: `1/48 ↔ 1/(4π)` in one theorem

This module wires the geometric solid-angle bridge
(`L1bChamberVolume.solidAngleCone`, `solidAngle cone = 4π/48`) into the scalar
density certificate (`L1bDensityCertificate.density_arithmetic_certificate`),
so the finite carrier's uniform weight `1/48` and the boundary density
`1/(4π)` are connected inside a single statement.

Two forms, per the headline-theorem panel:

* **Structural (primary), `ENNReal`-valued.**
  `density_solidAngle_structural`:
  `((1 : ENNReal)/48) / solidAngle cone = (solidAngle Set.univ)⁻¹`.
  The uniform weight `1/48` over the chamber's solid angle equals the inverse
  of the total solid angle. This is normalization-independent: the `3 •`
  factor in the definition of `solidAngle` cancels, so the statement holds
  whatever the chosen solid-angle normalization, and reads off the chamber
  count `48` and the total `4π` together.

* **Explicit endpoint (corollary), `Real`-valued.**
  `density_solidAngle_real`:
  `(1/48 : ℝ) / (solidAngle cone).toReal = 1 / (4 * Real.pi)`.
  Substituting the endpoint `solidAngle Set.univ = 4π` gives the physical
  boundary density `1/(4π)` directly.

Honesty note. `solidAngle S := 3 • vol(ball ∩ S)` is a faithful solid angle
only for cones / radial sets (sets that are unions of rays through the origin),
where `vol(ball ∩ S)` is proportional to the spherical measure of `S ∩ S²`.
`cone` is such a set. The theorems below are stated for `cone` and
`Set.univ`; they should not be read as a general spherical-area calculus.
-/

namespace IndisputableMonolith
namespace Masses
namespace L1bChamberDensityBridge

open MeasureTheory
open IndisputableMonolith.Masses.L1bChamberVolume
open IndisputableMonolith.Masses.L1bChamberFundamentalDomain

noncomputable section

/-- The uniform-density cancellation in `ENNReal`: for a finite nonzero total
`U`, splitting it into 48 equal parts and weighting one part by `1/48` returns
`U⁻¹`. -/
theorem ennreal_uniform_density {U : ENNReal} (hU0 : U ≠ 0) (hUtop : U ≠ ⊤) :
    ((1 : ENNReal) / 48) / (U / 48) = U⁻¹ := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
      ENNReal.mul_inv (Or.inr hUtop) (Or.inr hU0)]
  rw [show ((1 : ENNReal) / 48) = (48 : ENNReal)⁻¹ * 1 by rw [mul_one, one_div]]
  rw [inv_inv, mul_one]
  rw [show (48 : ENNReal) * U⁻¹ * 48⁻¹ = (48 : ENNReal) * 48⁻¹ * U⁻¹ by ring]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- The total solid angle of the ambient ball is positive, hence nonzero. -/
theorem solidAngle_univ_ne_zero : solidAngle Set.univ ≠ 0 := by
  rw [solidAngle_univ]
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

/-- The total solid angle of the ambient ball is finite. -/
theorem solidAngle_univ_ne_top : solidAngle Set.univ ≠ ⊤ := by
  rw [solidAngle_univ]; exact ENNReal.ofReal_ne_top

/-- **Headline (structural).** The finite uniform weight `1/48` over the
chamber's solid angle equals the inverse of the total solid angle. This is the
`1/48 ↔ 1/(total)` identification, free of the `solidAngle` normalization
constant. -/
theorem density_solidAngle_structural :
    ((1 : ENNReal) / 48) / solidAngle cone = (solidAngle Set.univ)⁻¹ := by
  rw [solidAngleCone_eq_total_div]
  exact ennreal_uniform_density solidAngle_univ_ne_zero solidAngle_univ_ne_top

/-- **Headline (explicit endpoint).** With the total solid angle equal to `4π`,
the finite uniform weight `1/48` over the chamber's solid angle has boundary
density `1/(4π)`. -/
theorem density_solidAngle_real :
    (1 / 48 : ℝ) / (solidAngle cone).toReal = 1 / (4 * Real.pi) := by
  rw [solidAngleCone, ENNReal.toReal_ofReal (by positivity)]
  exact L1bDensityCertificate.density_arithmetic_certificate Real.pi Real.pi_ne_zero

/-! ## Independent witness for the kernel's leading boundary extraction target

`LeptonTorsionKernel.leadingBoundaryExtractionTarget` is an OPEN check shape: it
asks for an *independently computed* angular functional that equals the kernel's
leading boundary quantum `leadingBoundaryQuantum = 1/solid_angle_Q3 = 1/(4π)`.
The kernel's own value comes from the **discrete Gauss-Bonnet** route
(`solid_angle_Q3`, the `4π` assembled from the eight vertex angular deficits of
`∂Q₃`).

The finite-carrier program supplies a structurally *different* witness. The
order-48 hyperoctahedral carrier tiles the ball into 48 congruent chambers; one
chamber carries solid angle `solidAngle cone` computed by **continuous Lebesgue
measure** (`EuclideanSpace.volume_ball` etc.), and the carrier's uniform weight
`1/48` over that chamber has density `(1/48)/(solidAngle cone).toReal`. This
quantity never references `solid_angle_Q3`. The theorem below shows it equals the
kernel's leading boundary quantum, discharging the extraction target with a
witness from a genuinely independent geometric construction.

Honest scope (unchanged): this proves the two geometric routes (vertex-deficit
Gauss-Bonnet, and finite-carrier Lebesgue chamber density) agree on the extracted
value `1/(4π)`. It does **not** prove the *physics* identification that the
charged-lepton torsion correction the kernel sees IS this angular functional;
that adjacent-generation-correction claim stays MODEL (`LeptonTorsionKernel`
docstring). What is closed is the named, code-cited extraction shape, with an
independent witness rather than the circular `∃ k, k = 1/(4π)`. -/

/-- The finite carrier's own leading angular functional: the uniform weight
`1/48` spread over one chamber's (Lebesgue) solid angle. Built from the carrier
count `48` and the chamber geometry alone; it does **not** reference
`solid_angle_Q3` (the discrete Gauss-Bonnet route the kernel uses). -/
def chamberAngularFunctional : ℝ :=
  (1 / 48 : ℝ) / (solidAngle cone).toReal

/-- The finite-carrier angular functional is exactly `1/(4π)`. -/
theorem chamberAngularFunctional_eq :
    chamberAngularFunctional = 1 / (4 * Real.pi) :=
  density_solidAngle_real

/-- **Headline (extraction).** The finite-carrier chamber-density functional
discharges the kernel's leading boundary extraction target: it equals the kernel's
leading boundary quantum `1/(4π)`. The witness is the order-48 carrier's
uniform-weight-over-chamber density, computed by continuous Lebesgue measure and
independent of the discrete Gauss-Bonnet `solid_angle_Q3` the kernel uses. So the
two geometric routes meet at the extracted value. (This does not establish the
physics identification of the lepton torsion correction with this functional; see
the section docstring.) -/
theorem chamber_discharges_leading_extraction :
    LeptonTorsionKernel.leadingBoundaryExtractionTarget chamberAngularFunctional := by
  unfold LeptonTorsionKernel.leadingBoundaryExtractionTarget
  rw [LeptonTorsionKernel.leadingBoundaryQuantum_eq]
  exact chamberAngularFunctional_eq

end

end L1bChamberDensityBridge
end Masses
end IndisputableMonolith
