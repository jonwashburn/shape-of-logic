import Mathlib

/-!
# Finite recognition cell boundary commitments (engineering scaffold)

Python exact cells in `scripts/cosmogenesis/cell{1d,2d,3d,voxel}.py` mirror these boundary tags.
No new axioms; certificate targets for periodic ring and open patch serialization.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace FiniteCellBoundary

/-- Periodic 1D ring: sites `Fin n` with wrap posting. -/
structure PeriodicRing (n : Nat) where
  n_pos : 0 < n

/-- Open 2D patch: finite grid without wrap. -/
structure OpenPatch (nx ny : Nat) where
  nx_pos : 0 < nx
  ny_pos : 0 < ny

/-- Bounded 3D voxel without wrap. -/
structure BoundedVoxel (nx ny nz : Nat) where
  nx_pos : 0 < nx
  ny_pos : 0 < ny
  nz_pos : 0 < nz

theorem periodic_ring_n_pos {n : Nat} (c : PeriodicRing n) : 0 < n := c.n_pos

end FiniteCellBoundary
end Cosmology
end IndisputableMonolith
