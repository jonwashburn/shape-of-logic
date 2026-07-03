import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Spectral.DFT8
import IndisputableMonolith.Masses.TrailingFoldBridge

/-!
# T1-B1: DFT-8 Phase → Recognition Cost Bridge (the Golden Gap package)

This module implements the panel-greenlit "Golden Gap / trace-norm bridge" for lift
`T1_B1_dft_phase_cost` (panel verdict `state/panel/t1b1_bridge_20260702_033446.json`).
It bridges the discrete DFT-8 half-period phase index (mode 4, the antipode `ω⁴ = -1`
of the 8-tick recognition clock) to the continuous recognition cost `J` that sets the
trailing fold functional in `TrailingFoldBridge`.

## What is proved (THEOREM layer, all lake-gated, no `sorry`)

The octave half-cost `1/2` of premise B1 is not an unstructured number: it decomposes
exactly as **antipode base cost plus golden trace-norm gap**,

  `J(x²) = J(-1) + (x + x⁻¹)² / 2`   (the *gap identity*, any `x ≠ 0`),

where `-1 = ω⁴` is the DFT-8 half-period involution. Hence

  `J(φ²) = J((ω⁴).re) + (φ + φ⁻¹)² / 2 = -2 + 5/2 = 1/2`.

The DFT-8 antipode supplies the base cost `J(-1) = -2` (the unique cost of the
half-period involution), and the golden section supplies the gap `5/2` through the
trace certificate `(φ + φ⁻¹)² = 5`. The decomposition is *discriminating*, not
decorative: the certificate

  `J(x²) = 1/2  ↔  (x + x⁻¹)² = 5`

excludes every non-golden base. In particular the **silver ratio** `1 + √2` (trace
square `8`, not `5`) fails octave closure — the concrete non-vacuity witness the
panel demanded. The antipode's real part is itself the golden field norm:
`(ω⁴).re = φ(1 − φ) = −1` (the norm of `φ` in `ℤ[φ]`).

## Honest residuals (NOT closed here; recorded per the panel's honesty checks)

1. **The `.re` projection is unforced.** `J` is a real-argument functional and the
   complex extension of the cost is phase-invariant (depends only on modulus), so
   evaluating the antipode through its real part `(ω⁴).re = -1` rather than through a
   canonical complex-cost extension is a modeling choice. A forced complex cost
   functional on the DFT-8 modes is OPEN.
2. **The golden instantiation is unforced.** The discriminant `(x + x⁻¹)² = 5` has
   root set `{φ, φ⁻¹, −φ, −φ⁻¹}`; selecting the positive expanding root `x = φ` is
   the standard positivity/scale convention, not a theorem. Equivalently, B1 forces
   `ρ ∈ {φ², φ⁻²}` (`jCost_eq_half_iff`), never `ρ = φ²` alone.

So B1 itself (`J = 1/2` as the *physical* cost of the generation-closing fold) remains
a MODEL premise; what this module upgrades is its *structure*: the `1/2` is now the
lake-checked arithmetic shadow of the DFT-8 antipode plus the golden trace gap, and it
provably rejects non-golden ratios. Tier: THEOREM (arithmetic bridge) conditional on
nothing; B1's physical reading stays MODEL.

Lean status: no `sorry`; no new axioms beyond Mathlib base.
-/

namespace IndisputableMonolith
namespace Masses
namespace T1DftPhaseCostBridge

open Constants
open LeptonTorsionKernel

noncomputable section

/-! ## The DFT-8 antipode and its cost -/

/-- The real part of the DFT-8 half-period mode: `(ω⁴).re = -1`. This is the unique
self-conjugate non-DC point of the 8-tick clock (mode 4 of 8, the Nyquist antipode),
projected to the real cost axis. -/
theorem omega8_pow4_re : (Spectral.omega8 ^ 4).re = -1 := by
  rw [Spectral.omega8_pow_4]
  simp

/-- The recognition cost of the half-period involution: `J(-1) = -2`. This is the
antipode base cost that anchors the golden-gap decomposition. -/
theorem jcost_neg_one : Cost.Jcost (-1) = -2 := by
  unfold Cost.Jcost
  norm_num

/-! ## Golden trace certificate -/

/-- The golden inverse in trace form: `φ⁻¹ = φ - 1` (from `φ² = φ + 1`). -/
theorem phi_inv_eq_phi_sub_one : phi⁻¹ = phi - 1 := by
  have key : phi * (phi - 1) = 1 := by linear_combination phi_sq_eq
  exact (eq_inv_of_mul_eq_one_right key).symm

/-- **Golden trace certificate.** `(φ + φ⁻¹)² = 5`: the golden base is exactly a
square root of the discriminant `5`. This is the "gap" side of the decomposition. -/
theorem golden_trace_sq_eq_five : (phi + phi⁻¹) ^ 2 = 5 := by
  rw [phi_inv_eq_phi_sub_one]
  linear_combination (4 : ℝ) * phi_sq_eq

/-! ## The gap identity (greenlit theorem 1) -/

/-- **Gap identity.** For any nonzero real `x`, the cost of the square decomposes as
the antipode base cost plus half the squared trace:

  `J(x²) = J(-1) + (x + x⁻¹)² / 2`.

This is the structural bridge: squaring (one full traversal of the half-period pair)
always pays the involution's base cost `J(-1) = -2`, plus a nonnegative trace-norm
gap. It is an identity of the cost functional, independent of any golden input. -/
theorem jcost_sq_gap (x : ℝ) (hx : x ≠ 0) :
    Cost.Jcost (x ^ 2) = Cost.Jcost (-1) + (x + x⁻¹) ^ 2 / 2 := by
  rw [jcost_neg_one]
  unfold Cost.Jcost
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  field_simp [hx, hx2]
  ring

/-! ## The antipode golden gap (greenlit theorems 2-4) -/

/-- **Antipode golden gap.** The octave cost of the golden square decomposes through
the DFT-8 half-period mode:

  `J(φ²) = J((ω⁴).re) + (φ + φ⁻¹)² / 2`.

The `1/2` of premise B1 is the sum of the antipode base cost `-2` and the golden
trace gap `5/2`. (Residual 1: the `.re` projection is an unforced modeling choice;
see module docstring.) -/
theorem dft8_antipode_golden_gap :
    Cost.Jcost (phi ^ 2) =
      Cost.Jcost ((Spectral.omega8 ^ 4).re) + (phi + phi⁻¹) ^ 2 / 2 := by
  rw [omega8_pow4_re]
  exact jcost_sq_gap phi phi_ne_zero

/-- The octave half-cost written directly through the DFT-8 involution:
`J(φ²) = (1 - 2·(ω⁴).re)/2 - 1`. Substituting `(ω⁴).re = -1` gives `3/2 - 1 = 1/2`:
the phase index 4 of 8 enters the cost only through the involution's real part. -/
theorem jcost_golden_square_via_dft8_involution :
    Cost.Jcost (phi ^ 2) = (1 - 2 * (Spectral.omega8 ^ 4).re) / 2 - 1 := by
  rw [omega8_pow4_re, jCost_phi_sq_eq_half]
  norm_num

/-- **The antipode is the golden norm.** The real part of the DFT-8 half-period mode
equals the field norm of `φ` in `ℤ[φ]`: `(ω⁴).re = φ(1 - φ) = -1`. The same `-1`
that closes the 8-tick clock's half period is the norm certificate of the golden
section — the two sides of the bridge name one number. -/
theorem dft8_involution_is_golden_norm :
    (Spectral.omega8 ^ 4).re = phi * (1 - phi) := by
  rw [omega8_pow4_re]
  linear_combination phi_sq_eq

/-! ## The discriminant certificate and non-vacuity witness -/

/-- **Discriminant certificate.** The octave half-cost on a square is *equivalent* to
the trace discriminant: for `x ≠ 0`,

  `J(x²) = 1/2  ↔  (x + x⁻¹)² = 5`.

The forward direction is what makes the bridge discriminating: the octave cost does
not merely evaluate at `φ`, it *forces* the trace square to `5` (root set
`{±φ, ±φ⁻¹}`; residual 2: the positive-root selection `x = φ` is a convention). -/
theorem jcost_sq_eq_half_iff_trace_sq_eq_five {x : ℝ} (hx : x ≠ 0) :
    Cost.Jcost (x ^ 2) = 1 / 2 ↔ (x + x⁻¹) ^ 2 = 5 := by
  rw [jcost_sq_gap x hx, jcost_neg_one]
  constructor
  · intro h; linarith
  · intro h; rw [h]; norm_num

/-- The silver ratio's trace square is `8`, not `5`: `((1+√2) + (1+√2)⁻¹)² = 8`. -/
theorem silver_trace_sq_eq_eight :
    ((1 + Real.sqrt 2) + (1 + Real.sqrt 2)⁻¹) ^ 2 = 8 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hmul : (1 + Real.sqrt 2) * (Real.sqrt 2 - 1) = 1 := by linear_combination h2
  have hinv : (1 + Real.sqrt 2)⁻¹ = Real.sqrt 2 - 1 :=
    (eq_inv_of_mul_eq_one_right hmul).symm
  rw [hinv]
  linear_combination (4 : ℝ) * h2

/-- **Non-vacuity witness (silver exclusion).** The silver ratio `1 + √2` — the
next metallic mean, satisfying `x² = 2x + 1` instead of `x² = x + 1` — does NOT
satisfy octave closure: `J((1+√2)²) ≠ 1/2`. The octave half-cost genuinely selects
the golden discriminant `5` and rejects the silver discriminant `8`; the bridge is
not a relabeling that any self-similar base would pass. -/
theorem silver_square_not_octave :
    ¬ TrailingFoldBridge.OctaveClosurePremise ((1 + Real.sqrt 2) ^ 2) := by
  intro h
  have hpos : (0 : ℝ) < 1 + Real.sqrt 2 := by positivity
  have hne : (1 + Real.sqrt 2) ≠ 0 := ne_of_gt hpos
  have h' : Cost.Jcost ((1 + Real.sqrt 2) ^ 2) = 1 / 2 := h
  have h5 : ((1 + Real.sqrt 2) + (1 + Real.sqrt 2)⁻¹) ^ 2 = 5 :=
    (jcost_sq_eq_half_iff_trace_sq_eq_five hne).mp h'
  rw [silver_trace_sq_eq_eight] at h5
  norm_num at h5

/-! ## Connection to premise B1 -/

/-- B1's canonical witness, DERIVED through the DFT-8 gap decomposition: the octave
closure of `φ²` is exactly antipode base cost plus golden trace gap,
`-2 + 5/2 = 1/2`. This re-derives `jCost_phi_sq_eq_half` along the phase-structured
route instead of by direct arithmetic, exhibiting *where* the `1/2` comes from. -/
theorem octaveClosure_at_golden_square_via_gap :
    TrailingFoldBridge.OctaveClosurePremise (phi ^ 2) := by
  unfold TrailingFoldBridge.OctaveClosurePremise
  rw [dft8_antipode_golden_gap, omega8_pow4_re, jcost_neg_one, golden_trace_sq_eq_five]
  norm_num

/-- The B1 premise on a squared base is equivalent to the golden discriminant: for
`x ≠ 0`, `OctaveClosurePremise (x²) ↔ (x + x⁻¹)² = 5`. This is the sharpest honest
form of the phase→cost bridge: the octave cost constrains the *base trace*, and the
golden section is the unique positive expanding solution (residual 2). -/
theorem octaveClosure_square_iff_discriminant {x : ℝ} (hx : x ≠ 0) :
    TrailingFoldBridge.OctaveClosurePremise (x ^ 2) ↔ (x + x⁻¹) ^ 2 = 5 :=
  jcost_sq_eq_half_iff_trace_sq_eq_five hx

end

end T1DftPhaseCostBridge
end Masses
end IndisputableMonolith
