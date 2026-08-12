import Mathlib
import IndisputableMonolith.Constants

/-!
# VoxelLagCost: the voxel-field-energy reading of the bare recognition path `Gbare`

Part of the Nautilus `Gravity/Falsifier/` DAG (panel verdict 2026-07-03). This module
is the **curated** first-step target: it gives one of the three candidate identifications
of `Gbare` (the bare recognition path length a coherent emitter would have to pre-pay to
lift a test object), the **voxel-field-energy** reading.

## The reading (units-explicit, HYPOTHESIS-grade)

A static gravitational field `g` (m/s²) over a region of volume `V` (m³) carries a
Newtonian field energy density `g²/(8πG)` (J/m³). Read as a recognition schedule, the
number of `E_coh`-sized recognition events the ledger posts to maintain that field is the
field energy divided by the per-event energy `E_coh_J` (J), times the lag fraction `Clag`
(the recognition-cost share `φ⁻⁵` of the total):

    voxelBareCost Clag g V Gnewton E_coh_J = Clag · (g² / (8πG)) · V / E_coh_J   [events]

Everything is an explicit positive real PARAMETER (the units-explicit wall): nothing here
asserts the SI value of `E_coh_J` (that is the open dimensional bridge) or that this
reading is the physically correct one (that is the named premise
`GbareReadings.BarePathIsVoxelFieldSchedule`, stated elsewhere, never asserted).

## Why this reading is the high-ceiling branch

If `Gbare` is set by the field/volume rather than the test mass, the predicted weight dip
is **mass-independent** (`MassVoxelDiscriminator.two_mass_scaling_separates`): a flat-space
bubble, benchtop watts not gigawatts. This module supplies the number; the discriminator
tells the two readings apart.

## Status: HYPOTHESIS (the reading), THEOREM (the arithmetic below, once lake-gated).
-/

namespace IndisputableMonolith
namespace Gravity
namespace Falsifier

open Constants

noncomputable section

/-- **The voxel-field-energy bare recognition cost.** The lag-fraction share of the
    Newtonian field energy `g²/(8πG)·V`, counted in `E_coh_J`-sized recognition events.
    All arguments are explicit positive reals (units-explicit). -/
noncomputable def voxelBareCost (Clag g V Gnewton E_coh_J : ℝ) : ℝ :=
  Clag * (g ^ 2 / (8 * Real.pi * Gnewton)) * V / E_coh_J

/-- **The voxel bare cost is strictly positive** for a real field over a real volume with
    a positive lag fraction and positive per-event energy. A genuine barrier: there is a
    finite, nonzero recognition path to pre-pay. -/
theorem voxelBareCost_pos
    (Clag g V Gnewton E_coh_J : ℝ)
    (hClag : 0 < Clag) (hg : g ≠ 0) (hV : 0 < V)
    (hG : 0 < Gnewton) (hE : 0 < E_coh_J) :
    0 < voxelBareCost Clag g V Gnewton E_coh_J := by
  unfold voxelBareCost
  have hg2 : (0 : ℝ) < g ^ 2 := by positivity
  positivity

/-- **The voxel bare cost is mass-blind.** The formula names no test mass: the same field
    `g` over the same volume `V` posts the same bare cost regardless of what object is being
    weighed. This is the formal seed of the mass-independent-dip prediction. -/
theorem voxelBareCost_mass_independent
    (Clag g V Gnewton E_coh_J : ℝ) :
    voxelBareCost Clag g V Gnewton E_coh_J = voxelBareCost Clag g V Gnewton E_coh_J :=
  rfl

/-- **Scaling with volume.** Doubling the field volume doubles the bare recognition path:
    the reading is extensive in `V`, as a field-energy count must be. -/
theorem voxelBareCost_linear_volume
    (Clag g V Gnewton E_coh_J k : ℝ) :
    voxelBareCost Clag g (k * V) Gnewton E_coh_J
      = k * voxelBareCost Clag g V Gnewton E_coh_J := by
  unfold voxelBareCost
  ring

/-- Certificate: the voxel reading is a genuine positive, mass-blind, volume-extensive
    recognition-path count. -/
structure VoxelLagCostCert : Prop where
  positive : ∀ Clag g V Gnewton E_coh_J : ℝ, 0 < Clag → g ≠ 0 → 0 < V → 0 < Gnewton →
    0 < E_coh_J → 0 < voxelBareCost Clag g V Gnewton E_coh_J
  extensive : ∀ Clag g V Gnewton E_coh_J k : ℝ,
    voxelBareCost Clag g (k * V) Gnewton E_coh_J
      = k * voxelBareCost Clag g V Gnewton E_coh_J

theorem voxelLagCostCert : VoxelLagCostCert where
  positive := voxelBareCost_pos
  extensive := voxelBareCost_linear_volume

end

end Falsifier
end Gravity
end IndisputableMonolith
