import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import IndisputableMonolith.Geometry.CayleyMengerN

/-!
# Dimension-Parametric Schläfli Interface

This module states the n-dimensional Schläfli identity in a finite-index
form.  The 3D tetrahedral theorem can later be shown to instantiate this
interface at `n = 3`.
-/

namespace IndisputableMonolith
namespace Geometry
namespace SchlaefliN

noncomputable section

/-- Abstract hinge data for an n-simplex: a hinge is codimension two, so
its measure is an `(n-2)`-volume. -/
structure HingeDataN where
  measure : ℝ
  measure_nonneg : 0 ≤ measure

/-- Schläfli derivative data in dimension `n`, over finitely many hinges and
edge-length coordinates. -/
structure SchlaefliDataN (nH nE : ℕ) where
  hinge : Fin nH → HingeDataN
  dTheta_dL : Fin nH → Fin nE → ℝ

/-- The n-dimensional Schläfli identity:
`Σ_h V_{n-2}(h) · ∂θ_h/∂L_e = 0` for every edge coordinate `e`. -/
def SchlaefliIdentityN {nH nE : ℕ} (D : SchlaefliDataN nH nE) : Prop :=
  ∀ e : Fin nE, ∑ h : Fin nH, (D.hinge h).measure * D.dTheta_dL h e = 0

/-- Direct eliminator for the n-dimensional identity. -/
theorem schlaefliN_kills_angle_term {nH nE : ℕ}
    (D : SchlaefliDataN nH nE) (hS : SchlaefliIdentityN D) (e : Fin nE) :
    ∑ h : Fin nH, (D.hinge h).measure * D.dTheta_dL h e = 0 :=
  hS e

end

end SchlaefliN
end Geometry
end IndisputableMonolith
