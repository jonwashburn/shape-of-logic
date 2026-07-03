import Mathlib
import IndisputableMonolith.Cost

/-!
# Snell's Law from RS — B14 Optics Depth

Snell's law: n₁ sin θ₁ = n₂ sin θ₂.
In RS: refraction ratio r = n₂/n₁ ↔ J(r) cost.

At r = 1 (same medium): J = 0, no bending.
At r ≠ 1 (different media): J > 0, light bends.

Five canonical optical phenomena (reflection, refraction, diffraction,
interference, polarisation) = configDim D = 5.

Lean: 5 phenomena, J = 0 at equal media.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.OpticsSnellsLawFromRS
open Cost

inductive OpticalPhenomenon where
  | reflection | refraction | diffraction | interference | polarisation
  deriving DecidableEq, Repr, BEq, Fintype

theorem opticalPhenomenonCount : Fintype.card OpticalPhenomenon = 5 := by decide

/-- Same medium: J = 0 (no bending). -/
theorem same_medium : Jcost 1 = 0 := Jcost_unit0

/-- Different media: J > 0 (bending occurs). -/
theorem different_media {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < Jcost r := Jcost_pos_of_ne_one r hr hne

/-- Refraction is symmetric: J(n₂/n₁) = J(n₁/n₂). -/
theorem refraction_symmetric {r : ℝ} (hr : 0 < r) :
    Jcost r = Jcost r⁻¹ := Jcost_symm hr

structure OpticsCert where
  five_phenomena : Fintype.card OpticalPhenomenon = 5
  same_medium_zero : Jcost 1 = 0
  bending_positive : ∀ {r : ℝ}, 0 < r → r ≠ 1 → 0 < Jcost r

def opticsCert : OpticsCert where
  five_phenomena := opticalPhenomenonCount
  same_medium_zero := same_medium
  bending_positive := different_media

end IndisputableMonolith.Physics.OpticsSnellsLawFromRS
