import IndisputableMonolith.Cosmology.DomainCoarsening2D

/-!
# The coarsening cost in three dimensions: the cost lives on a surface, not in the volume

## Status: THEOREM (0 sorry, 0 axiom beyond Mathlib's standard three).

This module backs `scripts/cosmogenesis/domain_coarsen_3d.py`, which takes the locked-domain coarsening into
the dimension the forcing chain actually selects (T8: D = 3, `Foundation.UnifiedForcingChain`). A locked domain
is now a maximal 6-connected component of equal charge, carried as one coarse super-region; the
recognition-active interface between domains is a 2D surface, so the engine cost localizes to a surface and a
single growing domain of volume `V` is carried at cost set by its surface `~ V^(2/3)`: the sharpest
sub-extensive scaling, and the honest endpoint of "carry each region at the coarsest phi-rung its recognition
allows" in the dimension reality has.

As in 2D, the exact analogue of the 1D identity `runs = boundaries + 1` is the inequality
`components <= bichromatic + 1` (a 3D interface can be multiply connected), a connected-graph fact
(component-counting-under-edge-deletion). That fact is now a Lean THEOREM, dimension-free, in
`Cosmology.InterfaceComponentBound.mono_components_le_bichromatic_succ`: on any connected finite world the
monochromatic-component count is at most the bichromatic-edge count plus one. The 3D octahedral lattice is one
instance of its connected-ambient hypothesis (wiring the specific 6-neighbour lattice graph and identifying the
flood-fill components with the graph components is the routine remaining step; the hard content, the
edge-deletion merge bound Mathlib lacked, is discharged there).

What IS a clean theorem, and what this module proves, is the SEPARABLE (per-axis fiber) coarsening cost, and
the new 3D content is that it is INDEPENDENT OF THE DEPTH. Model the 3D field as a list of planes, each a list
of 1D fibers (`List (List (List α))`, indexed `[x][y][z]`). The list of all z-fibers is `grid.flatten` (flatten
the x and y levels). Coarsening along z carries `rowCost (grid.flatten)` super-regions (the sum of `runs` over
all z-fibers), and `zFiber_cost_eq` proves, for any grid whose fibers are all nonempty,

  `rowCost (grid.flatten) = rowInterface (grid.flatten) + (grid.flatten).length`,

i.e. the separable coarsening carries exactly (the total z-interface) plus (the number of z-fibers = the x-y
cross-sectional cell count) super-regions. The right side has NO dependence on the fiber lengths: deepening the
world in z does not increase the carried cost, only adding distinctions does. This is the per-axis backbone of
the 3D surface law. The true 3D component coarsening merges across fibers as well, so it is never worse:
`components_3D <= rowCost`, bracketed below by the cross-section and above by the volume
(`zFiber_cost_le_volume`), and pinned to the interface. Composed with `Cosmology.RecognitionWorkBound` (the
resolution cost per cadence cycle is bounded by the cadence INDEPENDENT of the index type, so it covers 3D
cells verbatim), the 3D engine's state and work are both bounded by the interface, not the volume.

The strict companion `foam_cost_tracks_interface` makes the Phase-15 multi-domain ("recognition foam") claim
formal: at a fixed cross-section, strictly more z-interface costs strictly more, so a finely recognized foam is
carried at strictly higher cost than a coarse split of the same extent, while changing only the depth costs
nothing. The engine pays for recognition activity, not volume. (The numeric foam driver
`scripts/cosmogenesis/domain_coarsen_foam_3d.py` measures the true 6-connected component count, which this
separable cost upper-bounds.)
-/

namespace IndisputableMonolith
namespace Cosmology
namespace DomainCoarsening3D

open IndisputableMonolith.Cosmology.DomainCoarsening
open IndisputableMonolith.Cosmology.DomainCoarsening2D

variable {α : Type*} [DecidableEq α]

/-- The list of all 1D z-fibers of a 3D grid indexed `[x][y][z]`: flatten the x and y levels. Each z-fiber is
the charge column at a fixed `(x, y)`; the engine coarsens each fiber into its maximal equal-charge runs. -/
def zFibers (grid : List (List (List α))) : List (List α) := grid.flatten

omit [DecidableEq α] in
@[simp] theorem zFibers_nil : zFibers ([] : List (List (List α))) = [] := rfl

omit [DecidableEq α] in
/-- Every z-fiber is nonempty when every fiber in every plane is nonempty. -/
theorem zFibers_nonempty (grid : List (List (List α)))
    (h : ∀ plane ∈ grid, ∀ fiber ∈ plane, fiber ≠ []) :
    ∀ f ∈ zFibers grid, f ≠ [] := by
  intro f hf
  rw [zFibers, List.mem_flatten] at hf
  obtain ⟨plane, hplane, hfplane⟩ := hf
  exact h plane hplane f hfplane

/-- **The 3D separable coarsening cost = z-interface + number of z-fibers, independent of the depth.**
For any 3D grid whose z-fibers are all nonempty, coarsening along the z-axis carries exactly (the total
z-interface) plus (the number of z-fibers = the x-y cross-sectional cell count) super-regions. The right side
depends only on the interface and the cross-section, never on the fiber lengths: making the world deeper in z
does not increase the carried cost. This is the exact per-axis generalization of the 1D law
`runs = boundaries + 1`, summed over every fiber of the 3D grid, and the per-axis backbone of the surface law.
The true 3D component coarsening also merges across fibers, so it carries at most this many super-regions. -/
theorem zFiber_cost_eq (grid : List (List (List α)))
    (h : ∀ plane ∈ grid, ∀ fiber ∈ plane, fiber ≠ []) :
    rowCost (zFibers grid) = rowInterface (zFibers grid) + (zFibers grid).length :=
  rowwise_cost_eq (zFibers grid) (zFibers_nonempty grid h)

/-- The carried separable cost never exceeds the volume: the number of coarse super-regions along z is at most
the total number of cells (each fiber coarsens into at most as many runs as it has cells, `runs_le_length`).
Together with `zFiber_cost_eq`, the carried cost is bracketed `(#z-fibers) <= rowCost <= (volume)` and pinned
to the z-interface, so when the interface grows as a surface while the volume grows as `t^3`, the carried cost
is sub-extensive in the volume. -/
theorem zFiber_cost_le_volume (grid : List (List (List α))) :
    rowCost (zFibers grid) ≤ ((zFibers grid).map List.length).sum := by
  show ((zFibers grid).map runs).sum ≤ ((zFibers grid).map List.length).sum
  exact List.sum_le_sum (fun fiber _ => runs_le_length fiber)

/-- **Depth independence, stated directly.** Two 3D grids with the same total z-interface and the same number
of z-fibers carry the same separable cost, regardless of how their fibers differ in length (depth). This is the
formal sense in which the 3D cost lives on the interface surface and the cross-section, not in the volume. -/
theorem zFiber_cost_depth_independent (g₁ g₂ : List (List (List α)))
    (h₁ : ∀ plane ∈ g₁, ∀ fiber ∈ plane, fiber ≠ [])
    (h₂ : ∀ plane ∈ g₂, ∀ fiber ∈ plane, fiber ≠ [])
    (hiface : rowInterface (zFibers g₁) = rowInterface (zFibers g₂))
    (hcross : (zFibers g₁).length = (zFibers g₂).length) :
    rowCost (zFibers g₁) = rowCost (zFibers g₂) := by
  rw [zFiber_cost_eq g₁ h₁, zFiber_cost_eq g₂ h₂, hiface, hcross]

/-- **The cost tracks the recognition interface, not the depth (the Phase-15 foam law, formalized).** Two 3D
grids with the same number of z-fibers (the same x-y cross-section): the one whose field carries strictly more
z-interface carries strictly more separable cost. This is the exact sense in which a finer, more recognized
structure (a foam with more domain walls) costs strictly more to carry than a coarser one at the same extent,
while deepening the world in z (changing fiber lengths, with the interface fixed) changes nothing
(`zFiber_cost_depth_independent`). The engine pays for recognition activity, not volume. -/
theorem foam_cost_tracks_interface (g₁ g₂ : List (List (List α)))
    (h₁ : ∀ plane ∈ g₁, ∀ fiber ∈ plane, fiber ≠ [])
    (h₂ : ∀ plane ∈ g₂, ∀ fiber ∈ plane, fiber ≠ [])
    (hcross : (zFibers g₁).length = (zFibers g₂).length)
    (hmore : rowInterface (zFibers g₁) < rowInterface (zFibers g₂)) :
    rowCost (zFibers g₁) < rowCost (zFibers g₂) := by
  rw [zFiber_cost_eq g₁ h₁, zFiber_cost_eq g₂ h₂, hcross]
  omega

end DomainCoarsening3D
end Cosmology
end IndisputableMonolith
