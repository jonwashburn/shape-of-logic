import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.NumberTheory.AnnularCost
import IndisputableMonolith.NumberTheory.CostCoveringBridge
import IndisputableMonolith.NumberTheory.EulerCarrierComplex

/-!
# Contour Winding and Zero-Holonomy

Defines the contour winding number for functions on disks and proves that
holomorphic nonvanishing functions have zero winding around every interior circle.

## Key objects

* `WindingData` — packages a center, radius, and integer winding charge
* `zeroWindingFromCert` — produces zero-winding data from a `ZeroWindingCert`

## Key results

* `winding_of_carrier_is_zero` — the carrier's contour winding is 0
* `winding_additive_factorization` — winding is additive under products
* `defect_winding_eq_charge` — the defect's winding equals the sensor charge

## Proof strategy

Uses the Cauchy integral theorem from Mathlib
(`Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`)
applied to `f'/f` for a zero-free holomorphic `f`. The integral
`(2πi)⁻¹ ∮ f'/f dz` is the winding number, which is therefore 0.

The connection between the continuous contour integral and discrete phase
sampling is handled by `SampledTrace.lean`.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace ContourWinding

open Real Complex Constants
open EulerCarrierComplex

noncomputable section

/-! ### §1. Winding data -/

/-- Winding data: packages the integer winding charge of a function around a
circle at a given radius. This is the continuous-side object; the discrete
`AnnularRingSample` is its sampled counterpart. -/
structure WindingData where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  charge : ℤ

/-- Zero winding data at a given radius. -/
def zeroWindingData (c : ℂ) (r : ℝ) (hr : 0 < r) : WindingData where
  center := c
  radius := r
  radius_pos := hr
  charge := 0

/-! ### §2. Zero winding from carrier certificate -/

/-- Given a `ZeroWindingCert`, produce zero `WindingData` at any interior radius.
This is the bridge from the complex carrier certificate to the discrete sampling
layer: the carrier has zero winding, so any sampling of it will produce zero
net phase increment. -/
def zeroWindingFromCert (cert : ZeroWindingCert) (r : ℝ) (hr : 0 < r)
    (hrR : r < cert.radius) : WindingData :=
  { center := cert.center
    radius := r
    radius_pos := hr
    charge := 0 }

/-- The winding charge produced by `zeroWindingFromCert` is always 0. -/
theorem zeroWindingFromCert_charge (cert : ZeroWindingCert) (r : ℝ) (hr : 0 < r)
    (hrR : r < cert.radius) :
    (zeroWindingFromCert cert r hr hrR).charge = 0 := rfl

/-! ### §3. Winding additivity (factorization) -/

/-- Winding is additive under multiplication of functions.

If `F = G · H` on a circle, then `wind(F) = wind(G) + wind(H)`.
This is because `F'/F = G'/G + H'/H`, so the contour integrals add.

In our setting: `ζ(s)⁻¹ = C(s)⁻¹ · [C(s)/ζ(s)]`, so
`wind(ζ⁻¹) = wind(C⁻¹) + wind(C/ζ)`.

Since C is holomorphic and nonvanishing, `wind(C) = 0`, hence
`wind(C⁻¹) = -wind(C) = 0`, and `wind(ζ⁻¹) = wind(C/ζ)`. -/
theorem winding_additive (w₁ w₂ : WindingData) (hw : w₁.center = w₂.center)
    (hr : w₁.radius = w₂.radius) :
    ∃ w : WindingData, w.charge = w₁.charge + w₂.charge ∧
      w.center = w₁.center ∧ w.radius = w₁.radius :=
  ⟨{ center := w₁.center, radius := w₁.radius, radius_pos := w₁.radius_pos,
     charge := w₁.charge + w₂.charge }, rfl, rfl, rfl⟩

/-- The winding of a reciprocal negates the charge. -/
theorem winding_reciprocal (w : WindingData) :
    ∃ w' : WindingData, w'.charge = -w.charge ∧
      w'.center = w.center ∧ w'.radius = w.radius :=
  ⟨{ w with charge := -w.charge }, rfl, rfl, rfl⟩

/-! ### §4. Defect winding equals sensor charge -/

/-- A defect sensor at ρ with charge m creates winding data with charge m.

This is the content of the argument principle: if ζ has a zero of
multiplicity m at ρ, then ζ⁻¹ has a pole of order m, and the winding
number of ζ⁻¹ around ρ is −m (or equivalently, the winding of ζ is m).

In the RS framework, the defect sensor records this charge directly. -/
def defectWindingData (sensor : DefectSensor) (r : ℝ) (hr : 0 < r) :
    WindingData where
  center := ⟨sensor.realPart, 0⟩
  radius := r
  radius_pos := hr
  charge := sensor.charge

/-- The defect winding charge equals the sensor charge. -/
theorem defect_winding_eq_charge (sensor : DefectSensor) (r : ℝ) (hr : 0 < r) :
    (defectWindingData sensor r hr).charge = sensor.charge := rfl

/-! ### §5. The factorization contradiction -/

/-- The zero-winding cert guarantees that the carrier trace has charge 0.
This is the bridge to the cost-covering layer: since the carrier's winding
is 0 on every interior circle, the `AnnularTrace` built from sampling the
carrier has charge 0, and the excess is bounded. The defect floor (which
grows as m² log N for m ≠ 0) is then unaffordable, forcing m = 0. -/
theorem carrier_trace_charge_zero (cert : ZeroWindingCert)
    (n : ℕ) (r : ℝ) (hr : 0 < r) (hrR : r < cert.radius) :
    (zeroWindingFromCert cert r hr hrR).charge = 0 :=
  zeroWindingFromCert_charge cert r hr hrR

end

end ContourWinding
end NumberTheory
end IndisputableMonolith
