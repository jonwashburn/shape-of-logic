import Mathlib
import IndisputableMonolith.Cosmology.InterfaceComponentBound
import IndisputableMonolith.Cosmology.LatticeBallVolume
import IndisputableMonolith.Cosmology.PolarizedBirthDomains

/-!
# The recognition-active interface of the birth field lives on the spine

## Status: THEOREM (0 sorry, 0 axiom beyond Mathlib's standard three).

Phase 50 (`PolarizedBirthDomains`) proved the *carried* side of the forced conjugate-birth field: the
field `+1` on `x > 0`, `-1` on `x < 0`, `0` on the `x = 0` spine is held as exactly 3 locked domains
for every radius, so the carried state is `O(1)` while the world is `Θ(t^d)`. This module proves the
complementary *interface* side: where the recognition activity (the bichromatic edges, the forced
distinctions) actually sits.

The result is sharp and structural. Every bichromatic edge of the polarized field has an endpoint on
the spine `x = 0` (`bichromatic_endpoint_on_spine`): the charge `sign(x)` changes only across the
spine, so a same-row step that flips the charge must touch the column `x = 0`. Hence the entire
recognition-active interface is confined to the spine (`interface_on_spine`). The spine itself is a
ball one dimension lower: the 2D spine is the segment `|y| ≤ t` (`spine_card = 2t + 1`), the 3D spine
is the 2D diamond `|y| + |z| ≤ t` (`spine_card = 2t² + 2t + 1`). So the interface lives on a
codimension-1 set whose size is `Θ(t^{d-1})`, and `interface / volume → 0`: the cost localizes to a
surface, as a THEOREM, not numeric.

Together with Phase 50 this closes both halves of the sub-extensivity picture for the birth field:
the carried domains are `O(1)` and the active interface is confined to a `Θ(t^{d-1})` spine, both
vanishing as a fraction of the `Θ(t^d)` world.

HONEST SCOPE. This proves the interface is *confined to* the spine and that the spine is a
codimension-1 ball; it does not separately Lean-count the exact number of interface edges (numerically
`8t - 4` ordered edges in 2D), which would need an enumeration of the `toList` edge set. The
sub-extensivity content ("the cost lives on a lower-dimensional surface") is exactly
spine-confinement plus the spine cardinality, and both are theorems here.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace PolarizedBirthInterface

open InterfaceComponentBound

/-! ### The 2-D diamond: the interface is confined to the spine `x = 0`. -/

namespace Diamond

open InterfaceComponentBound.Diamond
open PolarizedBirthDomains.Diamond

/-- **Every active edge touches the spine.** For the polarized diamond field, any two adjacent cells
of different charge have an endpoint on the spine `x = 0`. The charge `sign(x)` flips only between
columns `x = -1, 0, 1`, and a charge-flipping adjacency must step the `x`-coordinate across `0`, so
one endpoint sits on the spine. Pure case analysis: split the `sign` on each endpoint, then the
unit-distance adjacency forces the spine. -/
theorem bichromatic_endpoint_on_spine (t : ℕ) (a b : Vtx t)
    (hadj : adj a.val b.val) (hc : polarized t a ≠ polarized t b) :
    a.val.1 = 0 ∨ b.val.1 = 0 := by
  unfold adj at hadj
  simp only [polarized] at hc
  split_ifs at hc <;> omega

/-- **The whole recognition-active interface is on the spine.** Every bichromatic edge in the
interface list (the forced distinctions the engine posts on the birth field) has an endpoint on the
spine `x = 0`. This is the exact list `InterfaceComponentBound.Diamond.mono_le_interface_succ` bounds,
now shown to be spine-confined. -/
theorem interface_on_spine (t : ℕ) :
    ∀ p ∈ (edges t).filter (fun q => decide (polarized t q.1 ≠ polarized t q.2)),
      p.1.val.1 = 0 ∨ p.2.val.1 = 0 := by
  intro p hp
  rw [List.mem_filter] at hp
  obtain ⟨hpe, hpc⟩ := hp
  rw [mem_edges] at hpe
  rw [decide_eq_true_eq] at hpc
  exact bichromatic_endpoint_on_spine t p.1 p.2 hpe hpc

/-- The spine of the 2-D diamond: the cells on the column `x = 0`. -/
def spine (t : ℕ) : Finset (ℤ × ℤ) :=
  (InterfaceComponentBound.Diamond.ball t).filter (fun p => p.1 = 0)

/-- The spine is the image of the segment `[-t, t]` under `y ↦ (0, y)`: it is a 1-D ball. -/
theorem spine_eq_image (t : ℕ) :
    spine t = (Finset.Icc (-(t : ℤ)) t).image (fun y => ((0 : ℤ), y)) := by
  apply Finset.ext
  rintro ⟨x, y⟩
  simp only [spine, Finset.mem_filter, Finset.mem_image, Finset.mem_Icc,
    InterfaceComponentBound.Diamond.mem_ball_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hb, rfl⟩
    exact ⟨y, by omega, rfl, rfl⟩
  · rintro ⟨z, hz, rfl, rfl⟩
    exact ⟨by omega, rfl⟩

/-- **The 2-D spine is `2t + 1` cells.** The interface of the birth field is confined to this
codimension-1 set (a 1-D ball), which is `Θ(t)` while the world is `Θ(t²)`. -/
theorem spine_card (t : ℕ) : (spine t).card = 2 * t + 1 := by
  rw [spine_eq_image, Finset.card_image_of_injective _ (by
    intro u v h; simpa using h)]
  rw [Int.card_Icc]
  omega

/-- **Interface sub-extensivity (2-D).** The recognition-active interface of the birth field is
confined to the spine, a set of `2t + 1` cells, so `spine · t ≤ area`: the interface fraction falls
as `~ 1/t`. The cost lives on a 1-D curve while the world is the 2-D area `2t² + 2t + 1`. -/
theorem interface_subextensive (t : ℕ) (ht : 1 ≤ t) :
    (spine t).card = 2 * t + 1 ∧
      (spine t).card * t ≤ (InterfaceComponentBound.Diamond.ball t).card := by
  refine ⟨spine_card t, ?_⟩
  rw [spine_card t, LatticeBallVolume.Diamond.card_ball]
  nlinarith [ht]

/-- **Birth-field sub-extensivity, both halves (2-D).** The single capstone tying Phase 50 to Phase 51
for the forced conjugate-birth field: (1) it is carried as exactly 3 locked domains for every radius
(`O(1)` carried state, Phase 50), (2) its entire recognition-active interface is spine-incident, and
(3) the spine times the radius fits in the area, so the interface is confined to a codimension-1 set.
Both the carried-domain fraction and the interface support vanish as a fraction of the `Θ(t²)` world:
the North-Star "carry each region at the coarsest φ-rung its recognition allows" made exact for the
birth field, as a THEOREM. -/
theorem birth_field_subextensive (t : ℕ) (ht : 1 ≤ t) :
    comp (PolarizedBirthDomains.Diamond.Fmono t) = 3
    ∧ (∀ p ∈ (edges t).filter (fun q => decide (polarized t q.1 ≠ polarized t q.2)),
         p.1.val.1 = 0 ∨ p.2.val.1 = 0)
    ∧ (spine t).card * t ≤ (InterfaceComponentBound.Diamond.ball t).card :=
  ⟨PolarizedBirthDomains.Diamond.polarized_components_eq_three t ht,
   interface_on_spine t, (interface_subextensive t ht).2⟩

end Diamond

/-! ### The 3-D octahedron: the interface is confined to the spine disk `x = 0`.

The dimension D = 3 is the one the forcing chain selects. The spine is now a 2-D diamond. -/

namespace Octahedron

open InterfaceComponentBound.Octahedron
open PolarizedBirthDomains.Octahedron

/-- **Every active edge touches the spine disk.** For the polarized octahedron field, any two
adjacent cells of different charge have an endpoint on the spine `x = 0`. Same mechanism as the
diamond: `sign(x)` flips only across `x = 0`, and a charge-flipping 6-neighbour step crosses it. -/
theorem bichromatic_endpoint_on_spine (t : ℕ) (a b : Vtx t)
    (hadj : adj a.val b.val) (hc : polarized t a ≠ polarized t b) :
    a.val.1 = 0 ∨ b.val.1 = 0 := by
  unfold adj at hadj
  simp only [polarized] at hc
  split_ifs at hc <;> omega

/-- **The whole recognition-active interface is on the spine disk.** Every bichromatic edge in the
interface list has an endpoint on the spine `x = 0`. -/
theorem interface_on_spine (t : ℕ) :
    ∀ p ∈ (edges t).filter (fun q => decide (polarized t q.1 ≠ polarized t q.2)),
      p.1.val.1 = 0 ∨ p.2.val.1 = 0 := by
  intro p hp
  rw [List.mem_filter] at hp
  obtain ⟨hpe, hpc⟩ := hp
  rw [mem_edges] at hpe
  rw [decide_eq_true_eq] at hpc
  exact bichromatic_endpoint_on_spine t p.1 p.2 hpe hpc

/-- The spine of the 3-D octahedron: the cells on the disk `x = 0`. -/
def spine (t : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (InterfaceComponentBound.Octahedron.ball t).filter (fun p => p.1 = 0)

/-- The spine is the image of the 2-D diamond under `(y, z) ↦ (0, y, z)`: it is a 2-D ball, one
dimension below the octahedron. -/
theorem spine_eq_image (t : ℕ) :
    spine t = (InterfaceComponentBound.Diamond.ball t).image (fun q => ((0 : ℤ), q.1, q.2)) := by
  apply Finset.ext
  rintro ⟨x, y, z⟩
  rw [spine, Finset.mem_filter, InterfaceComponentBound.Octahedron.mem_ball_iff, Finset.mem_image]
  constructor
  · rintro ⟨hb, hx⟩
    subst hx
    refine ⟨(y, z), ?_, rfl⟩
    rw [InterfaceComponentBound.Diamond.mem_ball_iff]; omega
  · rintro ⟨⟨u, w⟩, huw, heq⟩
    rw [InterfaceComponentBound.Diamond.mem_ball_iff] at huw
    rw [Prod.mk.injEq, Prod.mk.injEq] at heq
    obtain ⟨h0, hu, hw⟩ := heq
    exact ⟨by omega, by omega⟩

/-- **The 3-D spine is `2t² + 2t + 1` cells** (a 2-D diamond, Phase 49 area law). The interface of
the birth field is confined to this codimension-1 disk, which is `Θ(t²)` while the world is `Θ(t³)`. -/
theorem spine_card (t : ℕ) : (spine t).card = 2 * t ^ 2 + 2 * t + 1 := by
  rw [spine_eq_image, Finset.card_image_of_injective _ (by
    intro u v h
    rw [Prod.mk.injEq, Prod.mk.injEq] at h
    exact Prod.ext h.2.1 h.2.2)]
  rw [LatticeBallVolume.Diamond.card_ball]

/-- **Interface sub-extensivity (3-D).** The recognition-active interface of the birth field is
confined to the spine disk, a set of `2t² + 2t + 1` cells, so `spine · t ≤ 3 · volume`: the interface
fraction falls as `~ 1/t`. The cost lives on a 2-D surface while the world is the 3-D volume (the
centered-octahedral number, `Θ(t³)`), in the dimension D = 3 the forcing chain selects. -/
theorem interface_subextensive (t : ℕ) (ht : 1 ≤ t) :
    (spine t).card = 2 * t ^ 2 + 2 * t + 1 ∧
      (spine t).card * t ≤ 3 * (InterfaceComponentBound.Octahedron.ball t).card := by
  refine ⟨spine_card t, ?_⟩
  rw [spine_card t, LatticeBallVolume.Octahedron.three_mul_card_ball t]
  nlinarith [ht, Nat.zero_le t]

/-- **Birth-field sub-extensivity, both halves (3-D).** The capstone tying Phase 50 to Phase 51 in the
dimension D = 3 the forcing chain selects: (1) the forced birth field is carried as exactly 3 locked
domains for every radius (Phase 50), (2) its entire interface is spine-incident, and (3) the spine
disk times the radius fits in `3 ·` the volume, confining the interface to a codimension-1 disk. Both
the carried-domain fraction and the interface support vanish as a fraction of the `Θ(t³)` world. -/
theorem birth_field_subextensive (t : ℕ) (ht : 1 ≤ t) :
    comp (PolarizedBirthDomains.Octahedron.Fmono t) = 3
    ∧ (∀ p ∈ (edges t).filter (fun q => decide (polarized t q.1 ≠ polarized t q.2)),
         p.1.val.1 = 0 ∨ p.2.val.1 = 0)
    ∧ (spine t).card * t ≤ 3 * (InterfaceComponentBound.Octahedron.ball t).card :=
  ⟨PolarizedBirthDomains.Octahedron.polarized_components_eq_three t ht,
   interface_on_spine t, (interface_subextensive t ht).2⟩

end Octahedron

end PolarizedBirthInterface
end Cosmology
end IndisputableMonolith
