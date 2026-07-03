import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.RecogSpec.Spec

/-!
# Metric-from-Units Certificate (Minkowski / light-cone)

This module provides a **non-scaffold** first milestone for the “Ledger ⇒ Metric”
bridge checklist:

- define a minimal 4D “metric” interface (symmetric bilinear evaluation),
- instantiate it with the Minkowski metric determined by a speed parameter `c`,
- and prove the **light-cone/null** condition for the anchor vector `(τ₀, ℓ₀, 0, 0)`
  using the RS cone-bound identity `c · τ₀ = ℓ₀`.

No imports from `Relativity/Geometry/*` are used.
-/

namespace IndisputableMonolith
namespace Verification
namespace MetricFromUnits

open IndisputableMonolith.Constants

/-! ### Minimal 4-vector and metric interface -/

structure Vec4 where
  t : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

/-- Minimal symmetric “metric” interface: an evaluation pairing plus symmetry. -/
structure Metric4 where
  eval : Vec4 → Vec4 → ℝ
  symm : ∀ v w : Vec4, eval v w = eval w v

/-! ### Minkowski metric determined by speed `c` -/

/-- Minkowski bilinear evaluation with signature `(-c^2, +1, +1, +1)` in coordinates
`(t, x, y, z)`. -/
def minkowskiEval (c : ℝ) (v w : Vec4) : ℝ :=
  -(c ^ 2) * v.t * w.t + v.x * w.x + v.y * w.y + v.z * w.z

lemma minkowskiEval_symm (c : ℝ) (v w : Vec4) : minkowskiEval c v w = minkowskiEval c w v := by
  unfold minkowskiEval
  ring

/-- The Minkowski `Metric4` instance at speed `c`. -/
def minkowskiMetric (c : ℝ) : Metric4 :=
  { eval := minkowskiEval c, symm := minkowskiEval_symm c }

/-- Quadratic form induced by a metric. -/
def normSq (g : Metric4) (v : Vec4) : ℝ :=
  g.eval v v

/-! ### Light-cone/null anchor vector -/

/-- Anchor vector `(τ, ℓ, 0, 0)` extracted from RS units. -/
def anchorsVec (U : RSUnits) : Vec4 :=
  { t := U.tau0, x := U.ell0, y := 0, z := 0 }

lemma anchorsVec_null_of_cone (c τ ℓ : ℝ) (h : c * τ = ℓ) :
    normSq (minkowskiMetric c) { t := τ, x := ℓ, y := 0, z := 0 } = 0 := by
  unfold normSq minkowskiMetric minkowskiEval
  -- reduce to `-(c^2)*τ^2 + ℓ^2 = 0` and rewrite `ℓ = c*τ`
  simp [pow_two, h.symm]
  ring

/-- The anchor vector is null for every RSUnits pack (by the built-in cone bound). -/
lemma anchorsVec_null (U : RSUnits) :
    normSq (minkowskiMetric U.c) (anchorsVec U) = 0 := by
  -- RSUnits contains the cone bound `c * τ0 = ℓ0` as a field.
  simpa [anchorsVec] using anchorsVec_null_of_cone U.c U.tau0 U.ell0 U.c_ell0_tau0

/-! ### Certificate -/

structure MetricFromUnitsCert where
  deriving Repr

/-- Verification predicate: Minkowski metric built from RS units has a null anchor vector. -/
@[simp] def MetricFromUnitsCert.verified (_c : MetricFromUnitsCert) : Prop :=
  ∀ U : RSUnits, normSq (minkowskiMetric U.c) (anchorsVec U) = 0

@[simp] theorem MetricFromUnitsCert.verified_any (c : MetricFromUnitsCert) :
    MetricFromUnitsCert.verified c := by
  intro U
  exact anchorsVec_null U

end MetricFromUnits
end Verification
end IndisputableMonolith
