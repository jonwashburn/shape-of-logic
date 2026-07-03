import Mathlib
import IndisputableMonolith.Cosmology.InterfaceComponentBound
import IndisputableMonolith.Cosmology.LatticeBallVolume
import IndisputableMonolith.Cosmology.PolarizedBirthDomains
import IndisputableMonolith.Cosmology.PolarizedBirthInterface
import IndisputableMonolith.Cosmology.PolarizedBirthInterfaceCount

/-!
# Total adjacency count of the coarsening world, and the exact carried-versus-interface split

`PolarizedBirthInterfaceCount` counts the *interface* exactly: the bichromatic (forced-distinction)
edges of the polarized birth field number `8t - 4` in 2D and `8t² - 8t + 4` in 3D. That is the cost
the engine pays. This module counts the *other* side of the ledger: the total number of adjacencies,
and hence the *monochromatic* (carried-internal) edges the engine carries for free.

The total ordered adjacency count of the L1 ball is a closed form, a THEOREM over `ℕ` with no `sorry`
and no new axioms:

* `Diamond.total_edge_card t = 8 t²` (the 2D diamond, 4-neighbour adjacency).
* `Octahedron.three_mul_total_edge_card t : 3 · card = 24 t³ + 12 t`, i.e. `8 t³ + 4 t` (the 3D
  octahedron, 6-neighbour adjacency).

The proof is a clean "volume minus boundary" count. The ordered edges biject onto pairs `(cell, dir)`
with `cell` and `cell + dir` both in the ball, summed over the unit directions. For a fixed direction
`d`, the cells whose `d`-neighbour leaves the ball form a codimension-1 boundary: in 2D one cell per
row (`2t + 1` of them, the silhouette `Icc (-t) t`), in 3D one cell per `(y,z)` of the transverse
diamond (`card (Diamond.ball t) = 2t² + 2t + 1` of them). So each direction contributes
`card (ball) - card (boundary)` edges, and summing over the `2d` directions gives the total. Both
counts reuse the Phase-49 area/volume laws (`LatticeBallVolume`) for the bulk and the boundary.

The payoff (in `PolarizedBirthInterface`, `carried_edge_card`): every adjacency is either a carried
monochromatic edge or a forced bichromatic interface edge, so the monochromatic carried edges number
exactly `total - interface = 8t² - (8t - 4) = 8t² - 8t + 4` in 2D. The carried fraction
`mono / total = 1 - (8t - 4)/(8t²) → 1`: almost every adjacency is carried for free, and the engine
pays only the vanishing interface fraction. This is the exact, closed-form statement of "carry the
bulk coarse, pay only for the interface" that the coarsening north star asserts.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace LatticeBallEdges

open Finset
open scoped BigOperators

namespace Diamond

open InterfaceComponentBound.Diamond

/-- The four unit directions of the 4-neighbour lattice. -/
def dirs : Finset (ℤ × ℤ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

theorem dirs_card : dirs.card = 4 := by decide

/-- The total ordered adjacency set of the diamond, as a `Finset` of vertex pairs. This is exactly
the `edges` set of `InterfaceComponentBound`, whose `toList` is the engine's edge list. -/
noncomputable def E (t : ℕ) : Finset (Vtx t × Vtx t) :=
  Finset.univ.filter (fun p => adj p.1.val p.2.val)

/-- The `(cell, direction)` index set: a cell of the ball together with a unit direction whose step
stays in the ball. The ordered edges biject onto this set. -/
def Dset (t : ℕ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (ball t ×ˢ dirs).filter (fun p => (p.1.1 + p.2.1, p.1.2 + p.2.2) ∈ ball t)

/-- **Right boundary count.** The cells whose `+x` neighbour leaves the ball are exactly the
rightmost cell of each row, one per `y ∈ [-t, t]`, so there are `2t + 1` of them. -/
theorem boundary_xpos (t : ℕ) :
    ((ball t).filter (fun p => (p.1 + 1, p.2) ∉ ball t)).card = 2 * t + 1 := by
  rw [show 2 * t + 1 = (Finset.Icc (-(t : ℤ)) t).card from by rw [Int.card_Icc]; omega]
  refine Finset.card_bij' (fun p _ => p.2) (fun y _ => (((t : ℤ) - y.natAbs), y)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Finset.mem_Icc]; omega
  · intro y hy
    simp only [Finset.mem_Icc] at hy
    simp only [Finset.mem_filter, mem_ball_iff]
    refine ⟨by omega, by omega⟩
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · intro y _; rfl

/-- **Left boundary count.** Symmetric to `boundary_xpos`: `2t + 1` leftmost cells. -/
theorem boundary_xneg (t : ℕ) :
    ((ball t).filter (fun p => (p.1 + -1, p.2) ∉ ball t)).card = 2 * t + 1 := by
  rw [show 2 * t + 1 = (Finset.Icc (-(t : ℤ)) t).card from by rw [Int.card_Icc]; omega]
  refine Finset.card_bij' (fun p _ => p.2) (fun y _ => ((-((t : ℤ) - y.natAbs)), y)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Finset.mem_Icc]; omega
  · intro y hy
    simp only [Finset.mem_Icc] at hy
    simp only [Finset.mem_filter, mem_ball_iff]
    refine ⟨by omega, by omega⟩
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · intro y _; rfl

/-- **Top boundary count.** The cells whose `+y` neighbour leaves the ball: one per column. -/
theorem boundary_ypos (t : ℕ) :
    ((ball t).filter (fun p => (p.1, p.2 + 1) ∉ ball t)).card = 2 * t + 1 := by
  rw [show 2 * t + 1 = (Finset.Icc (-(t : ℤ)) t).card from by rw [Int.card_Icc]; omega]
  refine Finset.card_bij' (fun p _ => p.1) (fun x _ => (x, ((t : ℤ) - x.natAbs))) ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Finset.mem_Icc]; omega
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_filter, mem_ball_iff]
    refine ⟨by omega, by omega⟩
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · intro x _; rfl

/-- **Bottom boundary count.** The cells whose `-y` neighbour leaves the ball: one per column. -/
theorem boundary_yneg (t : ℕ) :
    ((ball t).filter (fun p => (p.1, p.2 + -1) ∉ ball t)).card = 2 * t + 1 := by
  rw [show 2 * t + 1 = (Finset.Icc (-(t : ℤ)) t).card from by rw [Int.card_Icc]; omega]
  refine Finset.card_bij' (fun p _ => p.1) (fun x _ => (x, (-((t : ℤ) - x.natAbs)))) ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Finset.mem_Icc]; omega
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_filter, mem_ball_iff]
    refine ⟨by omega, by omega⟩
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · intro x _; rfl

/-- For each unit direction, the cells whose `d`-neighbour stays in the ball number `2t²`: the bulk
`card (ball) = 2t² + 2t + 1` minus the `2t + 1` boundary cells. -/
theorem step_card (t : ℕ) (d : ℤ × ℤ) (hd : d ∈ dirs) :
    ((ball t).filter (fun p => (p.1 + d.1, p.2 + d.2) ∈ ball t)).card = 2 * t ^ 2 := by
  have hvol : (ball t).card = 2 * t ^ 2 + 2 * t + 1 := LatticeBallVolume.Diamond.card_ball t
  simp only [dirs, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · have hbd := boundary_xpos t
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := ball t) (p := fun p : ℤ × ℤ => (p.1 + 1, p.2) ∈ ball t)
    simp only [add_zero] at *
    omega
  · have hbd := boundary_xneg t
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := ball t) (p := fun p : ℤ × ℤ => (p.1 + -1, p.2) ∈ ball t)
    simp only [add_zero] at *
    omega
  · have hbd := boundary_ypos t
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := ball t) (p := fun p : ℤ × ℤ => (p.1, p.2 + 1) ∈ ball t)
    simp only [add_zero] at *
    omega
  · have hbd := boundary_yneg t
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := ball t) (p := fun p : ℤ × ℤ => (p.1, p.2 + -1) ∈ ball t)
    simp only [add_zero] at *
    omega

/-- The `(cell, direction)` index set has `8t²` elements: four directions, each contributing `2t²`
in-ball steps. -/
theorem Dset_card (t : ℕ) : (Dset t).card = 8 * t ^ 2 := by
  have hsum : (Dset t).card
      = ∑ d ∈ dirs, ((ball t).filter (fun p => (p.1 + d.1, p.2 + d.2) ∈ ball t)).card := by
    rw [Dset, Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.card_filter]
  rw [hsum]
  rw [Finset.sum_congr rfl (fun d hd => step_card t d hd)]
  rw [Finset.sum_const, dirs_card]
  ring

/-- **The 2-D total adjacency law.** The diamond `|x| + |y| ≤ t` has exactly `8t²` ordered
4-neighbour adjacencies (each undirected edge counted in both orientations). THEOREM over `ℕ`. The
ordered edges biject onto `(cell, direction)` steps that stay in the ball. -/
theorem total_edge_card (t : ℕ) : (E t).card = 8 * t ^ 2 := by
  rw [← Dset_card t]
  refine Finset.card_bij'
    (fun p _ => (p.1.val, (p.2.val.1 - p.1.val.1, p.2.val.2 - p.1.val.2)))
    (fun cd hcd => (⟨cd.1, ?_⟩, ⟨(cd.1.1 + cd.2.1, cd.1.2 + cd.2.2), ?_⟩)) ?_ ?_ ?_ ?_
  · -- cd.1 ∈ ball (for the inverse's first vertex)
    simp only [Dset, Finset.mem_filter, Finset.mem_product] at hcd
    exact hcd.1.1
  · -- cd.1 + cd.2 ∈ ball (for the inverse's second vertex)
    simp only [Dset, Finset.mem_filter, Finset.mem_product] at hcd
    exact hcd.2
  · -- hi : forward maps E into Dset
    rintro ⟨a, b⟩ hp
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Dset, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨a.property, ?_⟩, ?_⟩
    · -- the difference is a unit direction
      unfold adj at hp
      simp only [dirs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      omega
    · -- stepping by the difference lands on b ∈ ball
      have hb : (a.val.1 + (b.val.1 - a.val.1), a.val.2 + (b.val.2 - a.val.2)) = b.val := by
        rw [Prod.ext_iff]; refine ⟨?_, ?_⟩ <;> · dsimp only; ring
      rw [hb]; exact b.property
  · -- hj : inverse maps Dset into E
    rintro ⟨c, d⟩ hcd
    simp only [Dset, Finset.mem_filter, Finset.mem_product] at hcd
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold adj
    have hdir : d ∈ dirs := hcd.1.2
    simp only [dirs, Finset.mem_insert, Finset.mem_singleton] at hdir
    rcases hdir with rfl | rfl | rfl | rfl <;> · dsimp only; omega
  · -- left inverse
    rintro ⟨a, b⟩ hp
    dsimp only
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · apply Subtype.ext; rfl
    · apply Subtype.ext
      rw [Prod.ext_iff]
      refine ⟨?_, ?_⟩ <;> · dsimp only; ring
  · -- right inverse
    rintro ⟨c, d⟩ hcd
    dsimp only
    rw [Prod.ext_iff]
    refine ⟨rfl, ?_⟩
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩ <;> · dsimp only; ring

/-- The engine's edge list has `8t²` entries: the same total adjacency count, as a list length. -/
theorem edges_length (t : ℕ) : (InterfaceComponentBound.Diamond.edges t).length = 8 * t ^ 2 := by
  rw [InterfaceComponentBound.Diamond.edges, Finset.length_toList]
  exact total_edge_card t

open PolarizedBirthDomains.Diamond (polarized)
open PolarizedBirthInterface.Diamond (B)

/-- The carried (monochromatic) adjacencies of the polarized birth field: the equal-charge edges,
internal to a locked domain, which the engine carries coarse for free. -/
noncomputable def carried (t : ℕ) : Finset (Vtx t × Vtx t) :=
  (E t).filter (fun p => polarized t p.1 = polarized t p.2)

/-- **The exact carried (monochromatic) edge count.** Every adjacency is either a forced bichromatic
interface edge (`B`, counted as `8t - 4`) or a carried monochromatic edge. Since the total is `8t²`,
the carried edges number exactly `8t² - (8t - 4) = 8t² - 8t + 4`: the bulk the engine carries for
free, complementing the `8t - 4` it must post. THEOREM over `ℕ` (`t ≥ 1`). -/
theorem carried_edge_card (t : ℕ) (ht : 1 ≤ t) :
    (carried t).card = 8 * t ^ 2 - 8 * t + 4 := by
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := E t) (p := fun p : Vtx t × Vtx t => polarized t p.1 ≠ polarized t p.2)
  have hBeq : (E t).filter (fun p => polarized t p.1 ≠ polarized t p.2) = B t := by
    rw [E, B, Finset.filter_filter]
  have hMeq : (E t).filter (fun p => ¬ (polarized t p.1 ≠ polarized t p.2)) = carried t := by
    rw [carried]
    apply Finset.filter_congr
    intro p _
    simp
  rw [hBeq, hMeq] at hsplit
  have hB : (B t).card = 8 * t - 4 := PolarizedBirthInterface.Diamond.interface_card_eq t ht
  have hE : (E t).card = 8 * t ^ 2 := total_edge_card t
  rw [hB, hE] at hsplit
  have hge : 8 * t ≤ 8 * t ^ 2 := by nlinarith [ht]
  omega

/-- **Discrete isoperimetric / surface law.** The forced interface satisfies
`(interface)² ≤ 8 · (total adjacency)`, so the interface grows only as the *square root* of the bulk:
it is a codimension-1 surface, not a bulk quantity. Sharp form of "the cost is sub-extensive,
localized to a perimeter." THEOREM over `ℕ`. -/
theorem interface_sq_le_total (t : ℕ) (ht : 1 ≤ t) :
    (B t).card ^ 2 ≤ 8 * (E t).card := by
  rw [PolarizedBirthInterface.Diamond.interface_card_eq t ht, total_edge_card t]
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hL : 8 * (n + 1) - 4 = 8 * n + 4 := by omega
  rw [hL]
  nlinarith [Nat.zero_le n]

/-- **Carried dominates interface.** For a world of radius `t ≥ 1`, the engine carries at least as
many edges coarse as it posts (`8t² - 8t + 4 ≥ 8t - 4`, with equality only at `t = 1`): the carried
bulk overtakes the interface as soon as the world is larger than a single shell. -/
theorem carried_ge_interface (t : ℕ) (ht : 1 ≤ t) :
    (B t).card ≤ (carried t).card := by
  rw [PolarizedBirthInterface.Diamond.interface_card_eq t ht, carried_edge_card t ht]
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hsq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  rw [hsq]
  omega

end Diamond

namespace Octahedron

open InterfaceComponentBound.Octahedron

/-- The six unit directions of the 6-neighbour lattice. -/
def dirs : Finset (ℤ × ℤ × ℤ) :=
  {(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)}

theorem dirs_card : dirs.card = 6 := by decide

/-- The total ordered adjacency set of the octahedron, as a `Finset` of vertex pairs. -/
noncomputable def E (t : ℕ) : Finset (Vtx t × Vtx t) :=
  Finset.univ.filter (fun p => adj p.1.val p.2.val)

/-- The `(cell, direction)` index set: a cell of the ball together with a unit direction whose step
stays in the ball. The ordered edges biject onto this set. -/
def Dset (t : ℕ) : Finset ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) :=
  (ball t ×ˢ dirs).filter
    (fun p => (p.1.1 + p.2.1, p.1.2.1 + p.2.2.1, p.1.2.2 + p.2.2.2) ∈ ball t)

/-- **+x boundary count.** The octahedron cells whose `+x` neighbour leaves the ball are exactly the
maximal-`x` cell of each `(y, z)` transverse diamond, one per point of `Diamond.ball t`, so there are
`2t² + 2t + 1` of them. The boundary is a codimension-1 diamond. -/
theorem boundary_xpos (t : ℕ) :
    ((ball t).filter (fun p => (p.1 + 1, p.2.1, p.2.2) ∉ ball t)).card
      = 2 * t ^ 2 + 2 * t + 1 := by
  rw [← LatticeBallVolume.Diamond.card_ball t]
  refine Finset.card_bij' (fun p _ => (p.2.1, p.2.2))
    (fun q _ => (((t : ℤ) - q.1.natAbs - q.2.natAbs), q.1, q.2)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [InterfaceComponentBound.Diamond.mem_ball_iff]; omega
  · intro q hq
    rw [InterfaceComponentBound.Diamond.mem_ball_iff] at hq
    simp only [Finset.mem_filter, mem_ball_iff]
    refine ⟨by omega, by omega⟩
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · intro q _; rfl

/-- **-x boundary count.** Symmetric: `2t² + 2t + 1` minimal-`x` cells. -/
theorem boundary_xneg (t : ℕ) :
    ((ball t).filter (fun p => (p.1 + -1, p.2.1, p.2.2) ∉ ball t)).card
      = 2 * t ^ 2 + 2 * t + 1 := by
  rw [← LatticeBallVolume.Diamond.card_ball t]
  refine Finset.card_bij' (fun p _ => (p.2.1, p.2.2))
    (fun q _ => ((-((t : ℤ) - q.1.natAbs - q.2.natAbs)), q.1, q.2)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [InterfaceComponentBound.Diamond.mem_ball_iff]; omega
  · intro q hq
    rw [InterfaceComponentBound.Diamond.mem_ball_iff] at hq
    simp only [Finset.mem_filter, mem_ball_iff]
    refine ⟨by omega, by omega⟩
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · intro q _; rfl

/-- **+y boundary count.** `2t² + 2t + 1` maximal-`y` cells, one per `(x, z)` transverse diamond. -/
theorem boundary_ypos (t : ℕ) :
    ((ball t).filter (fun p => (p.1, p.2.1 + 1, p.2.2) ∉ ball t)).card
      = 2 * t ^ 2 + 2 * t + 1 := by
  rw [← LatticeBallVolume.Diamond.card_ball t]
  refine Finset.card_bij' (fun p _ => (p.1, p.2.2))
    (fun q _ => (q.1, ((t : ℤ) - q.1.natAbs - q.2.natAbs), q.2)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [InterfaceComponentBound.Diamond.mem_ball_iff]; omega
  · intro q hq
    rw [InterfaceComponentBound.Diamond.mem_ball_iff] at hq
    simp only [Finset.mem_filter, mem_ball_iff]
    refine ⟨by omega, by omega⟩
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · intro q _; rfl

/-- **-y boundary count.** `2t² + 2t + 1` minimal-`y` cells. -/
theorem boundary_yneg (t : ℕ) :
    ((ball t).filter (fun p => (p.1, p.2.1 + -1, p.2.2) ∉ ball t)).card
      = 2 * t ^ 2 + 2 * t + 1 := by
  rw [← LatticeBallVolume.Diamond.card_ball t]
  refine Finset.card_bij' (fun p _ => (p.1, p.2.2))
    (fun q _ => (q.1, (-((t : ℤ) - q.1.natAbs - q.2.natAbs)), q.2)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [InterfaceComponentBound.Diamond.mem_ball_iff]; omega
  · intro q hq
    rw [InterfaceComponentBound.Diamond.mem_ball_iff] at hq
    simp only [Finset.mem_filter, mem_ball_iff]
    refine ⟨by omega, by omega⟩
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · intro q _; rfl

/-- **+z boundary count.** `2t² + 2t + 1` maximal-`z` cells, one per `(x, y)` transverse diamond. -/
theorem boundary_zpos (t : ℕ) :
    ((ball t).filter (fun p => (p.1, p.2.1, p.2.2 + 1) ∉ ball t)).card
      = 2 * t ^ 2 + 2 * t + 1 := by
  rw [← LatticeBallVolume.Diamond.card_ball t]
  refine Finset.card_bij' (fun p _ => (p.1, p.2.1))
    (fun q _ => (q.1, q.2, ((t : ℤ) - q.1.natAbs - q.2.natAbs))) ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [InterfaceComponentBound.Diamond.mem_ball_iff]; omega
  · intro q hq
    rw [InterfaceComponentBound.Diamond.mem_ball_iff] at hq
    simp only [Finset.mem_filter, mem_ball_iff]
    refine ⟨by omega, by omega⟩
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · intro q _; rfl

/-- **-z boundary count.** `2t² + 2t + 1` minimal-`z` cells. -/
theorem boundary_zneg (t : ℕ) :
    ((ball t).filter (fun p => (p.1, p.2.1, p.2.2 + -1) ∉ ball t)).card
      = 2 * t ^ 2 + 2 * t + 1 := by
  rw [← LatticeBallVolume.Diamond.card_ball t]
  refine Finset.card_bij' (fun p _ => (p.1, p.2.1))
    (fun q _ => (q.1, q.2, (-((t : ℤ) - q.1.natAbs - q.2.natAbs)))) ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [InterfaceComponentBound.Diamond.mem_ball_iff]; omega
  · intro q hq
    rw [InterfaceComponentBound.Diamond.mem_ball_iff] at hq
    simp only [Finset.mem_filter, mem_ball_iff]
    refine ⟨by omega, by omega⟩
  · rintro ⟨x, y, z⟩ hp
    simp only [Finset.mem_filter, mem_ball_iff] at hp
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · intro q _; rfl

/-- For each unit direction, `3 ·` the count of in-ball steps is `4t³ + 2t`: the bulk
`3 · card (ball) = 4t³ + 6t² + 8t + 3` minus `3 ·` the `2t² + 2t + 1` codimension-1 boundary. -/
theorem three_mul_step_card (t : ℕ) (d : ℤ × ℤ × ℤ) (hd : d ∈ dirs) :
    3 * ((ball t).filter (fun p => (p.1 + d.1, p.2.1 + d.2.1, p.2.2 + d.2.2) ∈ ball t)).card
      = 4 * t ^ 3 + 2 * t := by
  have hvol : 3 * (ball t).card = 4 * t ^ 3 + 6 * t ^ 2 + 8 * t + 3 :=
    LatticeBallVolume.Octahedron.three_mul_card_ball t
  simp only [dirs, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · have hbd := boundary_xpos t
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := ball t) (p := fun p : ℤ × ℤ × ℤ => (p.1 + 1, p.2.1, p.2.2) ∈ ball t)
    simp only [add_zero] at *
    omega
  · have hbd := boundary_xneg t
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := ball t) (p := fun p : ℤ × ℤ × ℤ => (p.1 + -1, p.2.1, p.2.2) ∈ ball t)
    simp only [add_zero] at *
    omega
  · have hbd := boundary_ypos t
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := ball t) (p := fun p : ℤ × ℤ × ℤ => (p.1, p.2.1 + 1, p.2.2) ∈ ball t)
    simp only [add_zero] at *
    omega
  · have hbd := boundary_yneg t
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := ball t) (p := fun p : ℤ × ℤ × ℤ => (p.1, p.2.1 + -1, p.2.2) ∈ ball t)
    simp only [add_zero] at *
    omega
  · have hbd := boundary_zpos t
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := ball t) (p := fun p : ℤ × ℤ × ℤ => (p.1, p.2.1, p.2.2 + 1) ∈ ball t)
    simp only [add_zero] at *
    omega
  · have hbd := boundary_zneg t
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := ball t) (p := fun p : ℤ × ℤ × ℤ => (p.1, p.2.1, p.2.2 + -1) ∈ ball t)
    simp only [add_zero] at *
    omega

/-- `3 ·` the `(cell, direction)` index count is `24t³ + 12t`: six directions, each `4t³ + 2t`. -/
theorem three_mul_Dset_card (t : ℕ) : 3 * (Dset t).card = 24 * t ^ 3 + 12 * t := by
  have hsum : (Dset t).card
      = ∑ d ∈ dirs,
          ((ball t).filter (fun p => (p.1 + d.1, p.2.1 + d.2.1, p.2.2 + d.2.2) ∈ ball t)).card := by
    rw [Dset, Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.card_filter]
  rw [hsum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun d hd => three_mul_step_card t d hd)]
  rw [Finset.sum_const, dirs_card]
  ring

set_option maxHeartbeats 1000000 in
/-- **The 3-D total adjacency law, division-free.** The octahedron `|x| + |y| + |z| ≤ t` has exactly
`8t³ + 4t` ordered 6-neighbour adjacencies (stated as `3 · card = 24t³ + 12t`). THEOREM over `ℕ`. -/
theorem three_mul_total_edge_card (t : ℕ) : 3 * (E t).card = 24 * t ^ 3 + 12 * t := by
  rw [show (E t).card = (Dset t).card from ?_, three_mul_Dset_card t]
  refine Finset.card_bij'
    (fun p _ => (p.1.val, (p.2.val.1 - p.1.val.1, p.2.val.2.1 - p.1.val.2.1,
                  p.2.val.2.2 - p.1.val.2.2)))
    (fun cd hcd => (⟨cd.1, ?_⟩,
      ⟨(cd.1.1 + cd.2.1, cd.1.2.1 + cd.2.2.1, cd.1.2.2 + cd.2.2.2), ?_⟩)) ?_ ?_ ?_ ?_
  · simp only [Dset, Finset.mem_filter, Finset.mem_product] at hcd
    exact hcd.1.1
  · simp only [Dset, Finset.mem_filter, Finset.mem_product] at hcd
    exact hcd.2
  · rintro ⟨a, b⟩ hp
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Dset, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨a.property, ?_⟩, ?_⟩
    · unfold adj at hp
      simp only [dirs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      omega
    · have hb : (a.val.1 + (b.val.1 - a.val.1), a.val.2.1 + (b.val.2.1 - a.val.2.1),
          a.val.2.2 + (b.val.2.2 - a.val.2.2)) = b.val := by
        rw [Prod.ext_iff, Prod.ext_iff]
        refine ⟨?_, ?_, ?_⟩ <;> · dsimp only; ring
      rw [hb]; exact b.property
  · rintro ⟨c, d⟩ hcd
    simp only [Dset, Finset.mem_filter, Finset.mem_product] at hcd
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold adj
    have hdir : d ∈ dirs := hcd.1.2
    simp only [dirs, Finset.mem_insert, Finset.mem_singleton] at hdir
    rcases hdir with rfl | rfl | rfl | rfl | rfl | rfl <;> · dsimp only; omega
  · rintro ⟨a, b⟩ hp
    dsimp only
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · apply Subtype.ext; rfl
    · apply Subtype.ext
      rw [Prod.ext_iff, Prod.ext_iff]
      refine ⟨?_, ?_, ?_⟩ <;> · dsimp only; ring
  · rintro ⟨c, d⟩ hcd
    dsimp only
    rw [Prod.ext_iff]
    refine ⟨rfl, ?_⟩
    rw [Prod.ext_iff, Prod.ext_iff]
    refine ⟨?_, ?_, ?_⟩ <;> · dsimp only; ring

/-- **The 3-D total adjacency count.** Dividing the division-free law, the octahedron has exactly
`8t³ + 4t` ordered 6-neighbour adjacencies. -/
theorem total_edge_card (t : ℕ) : (E t).card = 8 * t ^ 3 + 4 * t := by
  have h := three_mul_total_edge_card t
  omega

/-- The engine's octahedron edge list has `8t³ + 4t` entries. -/
theorem edges_length (t : ℕ) :
    (InterfaceComponentBound.Octahedron.edges t).length = 8 * t ^ 3 + 4 * t := by
  rw [InterfaceComponentBound.Octahedron.edges, Finset.length_toList]
  exact total_edge_card t

open PolarizedBirthDomains.Octahedron (polarized)
open PolarizedBirthInterface.Octahedron (B)

/-- The carried (monochromatic) adjacencies of the polarized octahedron birth field. -/
noncomputable def carried (t : ℕ) : Finset (Vtx t × Vtx t) :=
  (E t).filter (fun p => polarized t p.1 = polarized t p.2)

/-- **The exact carried (monochromatic) edge count in 3-D.** Total `8t³ + 4t` minus the interface
`8t² - 8t + 4` gives carried `8t³ - 8t² + 12t - 4`: the bulk the octahedron coarsening carries free,
complementing the `Θ(t²)` interface it must post. THEOREM over `ℕ` (`t ≥ 1`). -/
theorem carried_edge_card (t : ℕ) (ht : 1 ≤ t) :
    (carried t).card = 8 * t ^ 3 - 8 * t ^ 2 + 12 * t - 4 := by
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := E t) (p := fun p : Vtx t × Vtx t => polarized t p.1 ≠ polarized t p.2)
  have hBeq : (E t).filter (fun p => polarized t p.1 ≠ polarized t p.2) = B t := by
    rw [E, B, Finset.filter_filter]
  have hMeq : (E t).filter (fun p => ¬ (polarized t p.1 ≠ polarized t p.2)) = carried t := by
    rw [carried]
    apply Finset.filter_congr
    intro p _
    simp
  rw [hBeq, hMeq] at hsplit
  have hB : (B t).card = 8 * t ^ 2 - 8 * t + 4 := PolarizedBirthInterface.Octahedron.interface_card_eq t ht
  have hE : (E t).card = 8 * t ^ 3 + 4 * t := total_edge_card t
  rw [hB, hE] at hsplit
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have h2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  have h3 : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring
  rw [h2, h3] at hsplit ⊢
  omega

/-- **Discrete isoperimetric / surface law (3-D).** The forced interface satisfies
`(interface)³ ≤ 8 · (total adjacency)²`, the codimension-1 scaling in three dimensions: the interface
is `Θ(t²)` while the total adjacency is `Θ(t³)`, so the interface grows only as the `2/3` power of the
bulk. It is a surface, not a volume. THEOREM over `ℕ`. -/
theorem interface_cube_le_total_sq (t : ℕ) (ht : 1 ≤ t) :
    (B t).card ^ 3 ≤ 8 * (E t).card ^ 2 := by
  rw [PolarizedBirthInterface.Octahedron.interface_card_eq t ht, total_edge_card t]
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hL : 8 * (n + 1) ^ 2 - 8 * (n + 1) + 4 = 8 * n ^ 2 + 8 * n + 4 := by
    have e1 : 8 * (n + 1) ^ 2 = 8 * n ^ 2 + 16 * n + 8 := by ring
    omega
  rw [hL]
  have hB : 8 * n ^ 2 + 8 * n + 4 ≤ 8 * (n + 1) ^ 2 := by nlinarith [Nat.zero_le n]
  have hE : 8 * (n + 1) ^ 3 ≤ 8 * (n + 1) ^ 3 + 4 * (n + 1) := Nat.le_add_right _ _
  calc (8 * n ^ 2 + 8 * n + 4) ^ 3
      ≤ (8 * (n + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hB 3
    _ = 8 * (8 * (n + 1) ^ 3) ^ 2 := by ring
    _ ≤ 8 * (8 * (n + 1) ^ 3 + 4 * (n + 1)) ^ 2 :=
        Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hE 2)

/-- **Carried dominates interface (3-D).** For a world of radius `t ≥ 1`, the octahedron coarsening
carries strictly more edges free than it posts (`8t³ - 8t² + 12t - 4 ≥ 8t² - 8t + 4`): the carried
bulk overtakes the `Θ(t²)` interface for every world larger than a single shell. -/
theorem carried_ge_interface (t : ℕ) (ht : 1 ≤ t) :
    (B t).card ≤ (carried t).card := by
  rw [PolarizedBirthInterface.Octahedron.interface_card_eq t ht, carried_edge_card t ht]
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have e2 : 8 * (n + 1) ^ 2 = 8 * n ^ 2 + 16 * n + 8 := by ring
  have e3 : 8 * (n + 1) ^ 3 = 8 * n ^ 3 + 24 * n ^ 2 + 24 * n + 8 := by ring
  omega

end Octahedron

end LatticeBallEdges
end Cosmology
end IndisputableMonolith
