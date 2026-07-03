import Mathlib
import IndisputableMonolith.Cosmology.InterfaceComponentBound
import IndisputableMonolith.Cosmology.LatticeBallVolume
import IndisputableMonolith.Cosmology.PolarizedBirthDomains
import IndisputableMonolith.Cosmology.PolarizedBirthInterface

/-!
# The exact interface edge count of the birth field, and constant recognition activity per cycle

## Status: THEOREM (0 sorry, 0 axiom beyond Mathlib's standard three).

Phase 51 (`PolarizedBirthInterface`) proved the recognition-active interface of the forced
conjugate-birth field is confined to the codimension-1 spine and that the spine is sub-extensive,
but it bounded only the spine *cells*, leaving the exact number of interface *edges* numeric. This
module closes that: it counts the bichromatic ordered-edge list exactly.

For the 2-D diamond the interface edge count is `8t - 4` (`interface_card_eq`), the ordered-edge
count the engine's `comp`/`mono_le_interface_succ` machinery actually uses (twice the `4t - 2`
undirected perimeter, since `edges` lists each adjacency in both orientations). The proof bridges
the `toList` edge filter to a `Finset.card` (`interface_length_eq_card`), then counts that Finset by
an explicit bijection (`Finset.card_bij'`) onto `{interior spine y} × {side, orientation}`: every
bichromatic edge has exactly one spine endpoint `(0, y)` and one neighbour `(±1, y)`, so the data of
the edge is exactly `(y, side, orientation)` with `|y| ≤ t - 1`.

The headline corollary is `interface_increment_const`: the interface grows by exactly `8` ordered
edges per cadence cycle (`t → t + 1`), a constant **independent of the world size**. The polarized
birth posts a constant number of forced distinctions per cycle even as the world grows as `Θ(t²)`.
This is the literal Lean statement of the compute-watch principle the simulation runs on: cost
scales with recognition activity (the interface increment, `O(1)` per cycle), not with volume.

The `Octahedron` namespace lifts the same count to the dimension the forcing chain selects (D = 3).
There the interface is a 2-D surface: the bichromatic edges sit on the spine disk `x = 0`, in
bijection with `{interior spine (y,z)} × {side, orientation}` where the interior spine is a 2-D
diamond of radius `t - 1`, so the exact ordered count is `8t² - 8t + 4` (`Octahedron.interface_card_eq`,
four times the Phase-49 area law `2(t-1)² + 2(t-1) + 1`). The per-cycle increment is then `16t`
(`Octahedron.interface_increment_linear`), `Θ(t)` rather than `O(1)`. That is the honest 3-D statement:
in three dimensions the forced recognition activity per cadence cycle grows linearly with the radius,
because the recognition-active interface is a growing codimension-1 disk, not a fixed-size band. Cost
still tracks recognition activity; in D = 3 that activity is `Θ(t)` per cycle, sub-extensive in the
`Θ(t³)` volume but not constant.

Both namespaces also carry `interface_total_growth`, the net interface edges introduced over a full
forward run from radius `1` to `T`: `8T - 8 = 8(T-1)` in 2D and `8T² - 8T = 8T(T-1)` in 3D, the
difference of the start and end interface sizes. This is `Θ(T^(D-1))`, strictly sub-extensive against
the brute-force `Θ(T^(D+1))` spacetime cost (volume times cycles), the closed-form compute-watch
run-total: a full run posts `Θ(T^(D-1))` net forced distinctions, not `Θ(T^(D+1))`.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace PolarizedBirthInterface

open InterfaceComponentBound

namespace Diamond

open InterfaceComponentBound.Diamond
open PolarizedBirthDomains.Diamond

/-- The bichromatic ordered-edge set of the polarized diamond field, as a `Finset`. This is the
interface: the forced distinctions the engine posts. -/
noncomputable def B (t : ℕ) : Finset (Vtx t × Vtx t) :=
  Finset.univ.filter (fun p => adj p.1.val p.2.val ∧ polarized t p.1 ≠ polarized t p.2)

/-- **Bridge: the interface edge-list length equals the Finset cardinality.** The `toList` edge set
filtered to bichromatic pairs has length equal to the cardinality of the bichromatic edge `Finset`,
because the edge list is `Nodup` (a `Finset.toList`) and filtering preserves `Nodup`. -/
theorem interface_length_eq_card (t : ℕ) :
    ((edges t).filter (fun p => decide (polarized t p.1 ≠ polarized t p.2))).length = (B t).card := by
  have hnd : ((edges t).filter (fun p => decide (polarized t p.1 ≠ polarized t p.2))).Nodup := by
    apply List.Nodup.filter
    exact Finset.nodup_toList _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext q
  obtain ⟨a, b⟩ := q
  simp only [List.mem_toFinset, List.mem_filter, mem_edges, decide_eq_true_eq, B,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Structure of a bichromatic edge.** Any adjacent pair of different polarized charge has exactly
one endpoint on the spine `x = 0` and the other at `x = ±1`, and they share the `y`-coordinate. Pure
case analysis on the two `sign(x)` values plus the unit-distance adjacency. This is the workhorse
that pins the edge data to `(y, side, orientation)`. -/
theorem edge_structure (t : ℕ) (a b : Vtx t) (hadj : adj a.val b.val)
    (hpol : polarized t a ≠ polarized t b) :
    (a.val.1 = 0 ∧ (b.val.1 = 1 ∨ b.val.1 = -1) ∧ a.val.2 = b.val.2) ∨
    (b.val.1 = 0 ∧ (a.val.1 = 1 ∨ a.val.1 = -1) ∧ a.val.2 = b.val.2) := by
  unfold adj at hadj
  simp only [polarized] at hpol
  split_ifs at hpol <;> omega

/-- The index set parameterising the interface edges: the interior spine `y`-coordinate
(`|y| ≤ t - 1`, the cells that actually have an `x = ±1` neighbour) times `(side, orientation)`. -/
def idx (t : ℕ) : Finset (ℤ × Bool × Bool) :=
  (Finset.Icc (-(t : ℤ) + 1) ((t : ℤ) - 1)) ×ˢ (Finset.univ : Finset (Bool × Bool))

/-- The index set has `8t - 4` elements: `(2t - 1)` interior spine cells times `4` (side, orient). -/
theorem idx_card (t : ℕ) (ht : 1 ≤ t) : (idx t).card = 8 * t - 4 := by
  rw [idx, Finset.card_product, Int.card_Icc]
  have h4 : (Finset.univ : Finset (Bool × Bool)).card = 4 := by decide
  rw [h4]
  omega

/-- The spine cell `(0, y)` of an index lies in the ball. -/
theorem memSpine (t : ℕ) (a : ℤ × Bool × Bool) (ha : a ∈ idx t) :
    ((0 : ℤ), a.1) ∈ ball t := by
  rw [idx, Finset.mem_product, Finset.mem_Icc] at ha
  obtain ⟨⟨hlo, hhi⟩, -⟩ := ha
  rw [InterfaceComponentBound.Diamond.mem_ball_iff]
  omega

/-- The neighbour cell `(±1, y)` of an index lies in the ball (since `|y| ≤ t - 1`). -/
theorem memNbr (t : ℕ) (a : ℤ × Bool × Bool) (ha : a ∈ idx t) :
    (((if a.2.1 then (1 : ℤ) else -1)), a.1) ∈ ball t := by
  rw [idx, Finset.mem_product, Finset.mem_Icc] at ha
  obtain ⟨⟨hlo, hhi⟩, -⟩ := ha
  rw [InterfaceComponentBound.Diamond.mem_ball_iff]
  split <;> · simp only [Int.natAbs_one, Int.natAbs_neg]; omega

/-- The index data of a bichromatic edge: `(spine y, side of the ±1 neighbour, orientation)`. -/
def edgeIndex (t : ℕ) (p : Vtx t × Vtx t) : ℤ × Bool × Bool :=
  if p.1.val.1 = 0 then (p.1.val.2, decide (0 < p.2.val.1), true)
  else (p.2.val.2, decide (0 < p.1.val.1), false)

/-- The bichromatic edge reconstructed from its index data. -/
def edgeFromIndex (t : ℕ) (a : ℤ × Bool × Bool) (ha : a ∈ idx t) : Vtx t × Vtx t :=
  if a.2.2 then
    (⟨((0 : ℤ), a.1), memSpine t a ha⟩, ⟨((if a.2.1 then (1 : ℤ) else -1), a.1), memNbr t a ha⟩)
  else
    (⟨((if a.2.1 then (1 : ℤ) else -1), a.1), memNbr t a ha⟩, ⟨((0 : ℤ), a.1), memSpine t a ha⟩)

/-- **The exact 2-D interface edge count is `8t - 4`** (ordered edges). The bichromatic edge set is in
bijection with `{interior spine y} × {side, orientation}`: every bichromatic edge has exactly one
spine endpoint `(0, y)` and one neighbour `(±1, y)` sharing the `y`-coordinate, so the edge is fully
determined by `(y, side, orientation)` with `|y| ≤ t - 1`. -/
theorem interface_card_eq (t : ℕ) (ht : 1 ≤ t) : (B t).card = 8 * t - 4 := by
  rw [← idx_card t ht]
  refine Finset.card_bij' (fun p _ => edgeIndex t p) (fun a ha => edgeFromIndex t a ha) ?_ ?_ ?_ ?_
  · -- hi : edgeIndex maps B into idx
    rintro ⟨a, b⟩ hp
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hadj, hpol⟩ := hp
    have hbm := b.property
    have ham := a.property
    rw [InterfaceComponentBound.Diamond.mem_ball_iff] at ham hbm
    show edgeIndex t (a, b) ∈ idx t
    rcases edge_structure t a b hadj hpol with ⟨h0, hbpm, hyeq⟩ | ⟨h0, hapm, hyeq⟩
    · dsimp only [edgeIndex]
      rw [if_pos h0, idx]
      have key : b.val.2.natAbs ≤ t - 1 := by
        have hb : b.val.1.natAbs + b.val.2.natAbs ≤ t := by
          have hmem := b.property
          rwa [InterfaceComponentBound.Diamond.mem_ball_iff] at hmem
        have h1 : b.val.1.natAbs = 1 := by rcases hbpm with hb1 | hb1 <;> rw [hb1] <;> decide
        omega
      have hbnd : a.val.2 ∈ Finset.Icc (-(t : ℤ) + 1) ((t : ℤ) - 1) := by
        rw [Finset.mem_Icc, hyeq]
        omega
      exact Finset.mem_product.mpr ⟨hbnd, Finset.mem_univ _⟩
    · have hne : ¬ (a.val.1 = 0) := by rcases hapm with h | h <;> omega
      dsimp only [edgeIndex]
      rw [if_neg hne, idx]
      have key : a.val.2.natAbs ≤ t - 1 := by
        have ha : a.val.1.natAbs + a.val.2.natAbs ≤ t := by
          have hmem := a.property
          rwa [InterfaceComponentBound.Diamond.mem_ball_iff] at hmem
        have h1 : a.val.1.natAbs = 1 := by rcases hapm with ha1 | ha1 <;> rw [ha1] <;> decide
        omega
      have hbnd : b.val.2 ∈ Finset.Icc (-(t : ℤ) + 1) ((t : ℤ) - 1) := by
        rw [Finset.mem_Icc, ← hyeq]
        omega
      exact Finset.mem_product.mpr ⟨hbnd, Finset.mem_univ _⟩
  · -- hj : edgeFromIndex maps idx into B
    rintro a ha
    show edgeFromIndex t a ha ∈ B t
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold edgeFromIndex
    split
    · refine ⟨?_, ?_⟩
      · unfold adj; dsimp only; split <;> omega
      · simp only [polarized]; dsimp only; split_ifs <;> omega
    · refine ⟨?_, ?_⟩
      · unfold adj; dsimp only; split <;> omega
      · simp only [polarized]; dsimp only; split_ifs <;> omega
  · -- left_inv : edgeFromIndex (edgeIndex p) = p
    rintro ⟨a, b⟩ hp
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hadj, hpol⟩ := hp
    rcases edge_structure t a b hadj hpol with ⟨h0, hbpm, hyeq⟩ | ⟨h0, hapm, hyeq⟩
    · apply Prod.ext
      · apply Subtype.ext
        simp only [edgeIndex, edgeFromIndex, h0]
        rw [Prod.ext_iff]
        exact ⟨h0.symm, rfl⟩
      · apply Subtype.ext
        simp only [edgeIndex, edgeFromIndex, h0]
        rw [Prod.ext_iff]
        refine ⟨?_, hyeq⟩
        rcases hbpm with hb1 | hb1 <;> simp [hb1]
    · have hne : ¬ (a.val.1 = 0) := by rcases hapm with h | h <;> omega
      apply Prod.ext
      · apply Subtype.ext
        simp only [edgeIndex, edgeFromIndex, if_neg hne]
        rw [Prod.ext_iff]
        refine ⟨?_, hyeq.symm⟩
        rcases hapm with ha1 | ha1 <;> simp [ha1]
      · apply Subtype.ext
        simp only [edgeIndex, edgeFromIndex, if_neg hne]
        rw [Prod.ext_iff]
        rcases edge_structure t a b hadj hpol with ⟨h0', _, _⟩ | ⟨h0', _, _⟩
        · exact absurd h0' hne
        · exact ⟨h0'.symm, rfl⟩
  · -- right_inv : edgeIndex (edgeFromIndex a) = a
    rintro a ha
    obtain ⟨y, side, orient⟩ := a
    show edgeIndex t (edgeFromIndex t (y, side, orient) ha) = (y, side, orient)
    cases orient <;> cases side <;>
      simp [edgeFromIndex, edgeIndex]

/-- **The concrete interface edge-list length is `8t - 4`.** Bridging the exact `Finset` count
`interface_card_eq` through `interface_length_eq_card`, the actual bichromatic edge list the engine
filters out of `edges t` has length exactly `8t - 4`. This is the form the numeric layer sees. -/
theorem interface_length_eq (t : ℕ) (ht : 1 ≤ t) :
    ((edges t).filter (fun p => decide (polarized t p.1 ≠ polarized t p.2))).length = 8 * t - 4 := by
  rw [interface_length_eq_card, interface_card_eq t ht]

/-- **Constant per-cycle recognition activity (the compute-watch law, in Lean).** Advancing the
diamond birth field by one cadence cycle (`t → t + 1`) adds exactly `8` ordered interface edges,
*independent of `t`* and hence independent of the world volume (which grows as `Θ(t²)`). The forced
distinctions the engine must post per cycle are `O(1)`, so the simulation's cost scales with
recognition activity, never with volume. -/
theorem interface_increment_const (t : ℕ) (ht : 1 ≤ t) :
    (B (t + 1)).card - (B t).card = 8 := by
  rw [interface_card_eq (t + 1) (by omega), interface_card_eq t ht]
  omega

/-- **Total interface growth over a forward run (2-D).** The net number of interface edges the
polarized birth introduces over a full run from radius `1` to radius `T` is exactly `8T - 8 = 8(T-1)`,
the difference of the start and end interface sizes. This is `Θ(T)`, sub-extensive against the
brute-force spacetime cost `Θ(T³)` (volume `Θ(T²)` times `T` cycles): the compute-watch total. -/
theorem interface_total_growth (T : ℕ) (hT : 1 ≤ T) :
    (B T).card - (B 1).card = 8 * T - 8 := by
  rw [interface_card_eq T hT, interface_card_eq 1 (le_refl 1)]
  omega

end Diamond

namespace Octahedron

open InterfaceComponentBound.Octahedron
open PolarizedBirthDomains.Octahedron

/-- The bichromatic ordered-edge set of the polarized octahedron field, as a `Finset`. -/
noncomputable def B (t : ℕ) : Finset (Vtx t × Vtx t) :=
  Finset.univ.filter (fun p => adj p.1.val p.2.val ∧ polarized t p.1 ≠ polarized t p.2)

/-- **Bridge: the interface edge-list length equals the Finset cardinality.** Same `Nodup`-filter
argument as the 2-D case. -/
theorem interface_length_eq_card (t : ℕ) :
    ((edges t).filter (fun p => decide (polarized t p.1 ≠ polarized t p.2))).length = (B t).card := by
  have hnd : ((edges t).filter (fun p => decide (polarized t p.1 ≠ polarized t p.2))).Nodup := by
    apply List.Nodup.filter
    exact Finset.nodup_toList _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext q
  obtain ⟨a, b⟩ := q
  simp only [List.mem_toFinset, List.mem_filter, mem_edges, decide_eq_true_eq, B,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Structure of a bichromatic edge (3-D).** Any adjacent pair of different polarized charge has
exactly one endpoint on the spine disk `x = 0` and the other at `x = ±1`, sharing both transverse
coordinates `(y, z)`. Pure case analysis on the two `sign(x)` values plus unit-distance adjacency. -/
theorem edge_structure (t : ℕ) (a b : Vtx t) (hadj : adj a.val b.val)
    (hpol : polarized t a ≠ polarized t b) :
    (a.val.1 = 0 ∧ (b.val.1 = 1 ∨ b.val.1 = -1) ∧ a.val.2.1 = b.val.2.1 ∧ a.val.2.2 = b.val.2.2) ∨
    (b.val.1 = 0 ∧ (a.val.1 = 1 ∨ a.val.1 = -1) ∧ a.val.2.1 = b.val.2.1 ∧ a.val.2.2 = b.val.2.2) := by
  unfold adj at hadj
  simp only [polarized] at hpol
  split_ifs at hpol <;> omega

/-- The index set parameterising the 3-D interface edges: the interior spine disk
`{(y, z) : |y| + |z| ≤ t - 1}` (a 2-D diamond, the cells that actually have an `x = ±1` neighbour)
times `(side, orientation)`. -/
def idx (t : ℕ) : Finset ((ℤ × ℤ) × Bool × Bool) :=
  (InterfaceComponentBound.Diamond.ball (t - 1)) ×ˢ (Finset.univ : Finset (Bool × Bool))

/-- The index set has `8t² - 8t + 4` elements: the interior spine disk is a 2-D diamond of radius
`t - 1` with `2(t-1)² + 2(t-1) + 1` cells (the Phase-49 area law), times `4` (side, orient). -/
theorem idx_card (t : ℕ) (ht : 1 ≤ t) : (idx t).card = 8 * t ^ 2 - 8 * t + 4 := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  rw [idx, Finset.card_product]
  have h4 : (Finset.univ : Finset (Bool × Bool)).card = 4 := by decide
  have e1 : n + 1 - 1 = n := by omega
  rw [e1, h4, LatticeBallVolume.Diamond.card_ball n]
  have e2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  rw [e2]
  omega

/-- The spine cell `(0, y, z)` of an index lies in the ball. -/
theorem memSpine (t : ℕ) (a : (ℤ × ℤ) × Bool × Bool) (ha : a ∈ idx t) :
    ((0 : ℤ), a.1) ∈ ball t := by
  rw [idx, Finset.mem_product] at ha
  obtain ⟨hy, -⟩ := ha
  rw [InterfaceComponentBound.Diamond.mem_ball_iff] at hy
  rw [InterfaceComponentBound.Octahedron.mem_ball_iff]
  omega

/-- The neighbour cell `(±1, y, z)` of an index lies in the ball (since `|y| + |z| ≤ t - 1`). -/
theorem memNbr (t : ℕ) (ht : 1 ≤ t) (a : (ℤ × ℤ) × Bool × Bool) (ha : a ∈ idx t) :
    (((if a.2.1 then (1 : ℤ) else -1)), a.1) ∈ ball t := by
  rw [idx, Finset.mem_product] at ha
  obtain ⟨hy, -⟩ := ha
  rw [InterfaceComponentBound.Diamond.mem_ball_iff] at hy
  rw [InterfaceComponentBound.Octahedron.mem_ball_iff]
  split <;> · simp only [Int.natAbs_one, Int.natAbs_neg]; omega

/-- The index data of a bichromatic 3-D edge: `(spine (y,z), side of the ±1 neighbour, orientation)`. -/
def edgeIndex (t : ℕ) (p : Vtx t × Vtx t) : (ℤ × ℤ) × Bool × Bool :=
  if p.1.val.1 = 0 then (p.1.val.2, decide (0 < p.2.val.1), true)
  else (p.2.val.2, decide (0 < p.1.val.1), false)

/-- The bichromatic 3-D edge reconstructed from its index data. -/
def edgeFromIndex (t : ℕ) (ht : 1 ≤ t) (a : (ℤ × ℤ) × Bool × Bool) (ha : a ∈ idx t) :
    Vtx t × Vtx t :=
  if a.2.2 then
    (⟨((0 : ℤ), a.1), memSpine t a ha⟩, ⟨((if a.2.1 then (1 : ℤ) else -1), a.1), memNbr t ht a ha⟩)
  else
    (⟨((if a.2.1 then (1 : ℤ) else -1), a.1), memNbr t ht a ha⟩, ⟨((0 : ℤ), a.1), memSpine t a ha⟩)

/-- **The exact 3-D interface edge count is `8t² - 8t + 4`** (ordered edges). The bichromatic edge set
is in bijection with `{interior spine (y,z)} × {side, orientation}`: every bichromatic edge has one
spine endpoint `(0, y, z)` and one neighbour `(±1, y, z)` sharing `(y, z)`, so the edge is fully
determined by `(y, z, side, orientation)` with `|y| + |z| ≤ t - 1`. The interior spine is a 2-D
diamond, so the count is `4 ·` its area law `2(t-1)² + 2(t-1) + 1 = 2t² - 2t + 1`. -/
theorem interface_card_eq (t : ℕ) (ht : 1 ≤ t) : (B t).card = 8 * t ^ 2 - 8 * t + 4 := by
  rw [← idx_card t ht]
  refine Finset.card_bij' (fun p _ => edgeIndex t p) (fun a ha => edgeFromIndex t ht a ha) ?_ ?_ ?_ ?_
  · -- hi : edgeIndex maps B into idx
    rintro ⟨a, b⟩ hp
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hadj, hpol⟩ := hp
    show edgeIndex t (a, b) ∈ idx t
    rcases edge_structure t a b hadj hpol with ⟨h0, hbpm, hy1, hy2⟩ | ⟨h0, hapm, hy1, hy2⟩
    · dsimp only [edgeIndex]
      rw [if_pos h0, idx]
      have key : b.val.2.1.natAbs + b.val.2.2.natAbs ≤ t - 1 := by
        have hb : b.val.1.natAbs + b.val.2.1.natAbs + b.val.2.2.natAbs ≤ t := by
          have hmem := b.property
          rwa [InterfaceComponentBound.Octahedron.mem_ball_iff] at hmem
        have h1 : b.val.1.natAbs = 1 := by rcases hbpm with hb1 | hb1 <;> rw [hb1] <;> decide
        omega
      have hbnd : a.val.2 ∈ InterfaceComponentBound.Diamond.ball (t - 1) := by
        rw [InterfaceComponentBound.Diamond.mem_ball_iff, hy1, hy2]
        omega
      exact Finset.mem_product.mpr ⟨hbnd, Finset.mem_univ _⟩
    · have hne : ¬ (a.val.1 = 0) := by rcases hapm with h | h <;> omega
      dsimp only [edgeIndex]
      rw [if_neg hne, idx]
      have key : a.val.2.1.natAbs + a.val.2.2.natAbs ≤ t - 1 := by
        have ha : a.val.1.natAbs + a.val.2.1.natAbs + a.val.2.2.natAbs ≤ t := by
          have hmem := a.property
          rwa [InterfaceComponentBound.Octahedron.mem_ball_iff] at hmem
        have h1 : a.val.1.natAbs = 1 := by rcases hapm with ha1 | ha1 <;> rw [ha1] <;> decide
        omega
      have hbnd : b.val.2 ∈ InterfaceComponentBound.Diamond.ball (t - 1) := by
        rw [InterfaceComponentBound.Diamond.mem_ball_iff, ← hy1, ← hy2]
        omega
      exact Finset.mem_product.mpr ⟨hbnd, Finset.mem_univ _⟩
  · -- hj : edgeFromIndex maps idx into B
    rintro a ha
    show edgeFromIndex t ht a ha ∈ B t
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold edgeFromIndex
    split
    · refine ⟨?_, ?_⟩
      · unfold adj; dsimp only; split <;> omega
      · simp only [polarized]; dsimp only; split_ifs <;> omega
    · refine ⟨?_, ?_⟩
      · unfold adj; dsimp only; split <;> omega
      · simp only [polarized]; dsimp only; split_ifs <;> omega
  · -- left_inv : edgeFromIndex (edgeIndex p) = p
    rintro ⟨a, b⟩ hp
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hadj, hpol⟩ := hp
    rcases edge_structure t a b hadj hpol with ⟨h0, hbpm, hy1, hy2⟩ | ⟨h0, hapm, hy1, hy2⟩
    · apply Prod.ext
      · apply Subtype.ext
        simp only [edgeIndex, edgeFromIndex, h0, if_true]
        rw [Prod.ext_iff]
        exact ⟨h0.symm, rfl⟩
      · apply Subtype.ext
        simp only [edgeIndex, edgeFromIndex, h0, if_true]
        rw [Prod.ext_iff]
        refine ⟨?_, Prod.ext_iff.mpr ⟨hy1, hy2⟩⟩
        rcases hbpm with hb1 | hb1 <;> simp [hb1]
    · have hne : ¬ (a.val.1 = 0) := by rcases hapm with h | h <;> omega
      apply Prod.ext
      · apply Subtype.ext
        simp only [edgeIndex, edgeFromIndex, if_neg hne]
        rw [Prod.ext_iff]
        refine ⟨?_, Prod.ext_iff.mpr ⟨hy1.symm, hy2.symm⟩⟩
        rcases hapm with ha1 | ha1 <;> simp [ha1]
      · apply Subtype.ext
        simp only [edgeIndex, edgeFromIndex, if_neg hne]
        rw [Prod.ext_iff]
        exact ⟨h0.symm, rfl⟩
  · -- right_inv : edgeIndex (edgeFromIndex a) = a
    rintro a ha
    obtain ⟨yz, side, orient⟩ := a
    show edgeIndex t (edgeFromIndex t ht (yz, side, orient) ha) = (yz, side, orient)
    cases orient <;> cases side <;>
      simp [edgeFromIndex, edgeIndex]

/-- **The concrete 3-D interface edge-list length is `8t² - 8t + 4`.** -/
theorem interface_length_eq (t : ℕ) (ht : 1 ≤ t) :
    ((edges t).filter (fun p => decide (polarized t p.1 ≠ polarized t p.2))).length
      = 8 * t ^ 2 - 8 * t + 4 := by
  rw [interface_length_eq_card, interface_card_eq t ht]

/-- **Linear per-cycle recognition activity (3-D).** Advancing the octahedron birth field by one
cadence cycle (`t → t + 1`) adds exactly `16t` ordered interface edges. Unlike the 2-D case (where the
increment is the constant `8`), in three dimensions the forced recognition activity per cycle grows
`Θ(t)`: the interface is a 2-D surface whose area grows linearly per shell. This is the honest 3-D
form of the compute-watch law: cost per cycle still tracks recognition activity, but in D = 3 that
activity is `Θ(t)`, not `O(1)`, because the recognition-active interface is a growing codim-1 disk. -/
theorem interface_increment_linear (t : ℕ) (ht : 1 ≤ t) :
    (B (t + 1)).card - (B t).card = 16 * t := by
  rw [interface_card_eq (t + 1) (by omega), interface_card_eq t ht]
  have e : (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 := by ring
  have hsq : t ≤ t ^ 2 := by nlinarith [ht]
  rw [e]
  omega

/-- **Total interface growth over a forward run (3-D).** The net number of interface edges the
polarized octahedron birth introduces over a full run from radius `1` to radius `T` is exactly
`8T² - 8T = 8T(T-1)`, the difference of the start and end interface sizes. This is `Θ(T²)`,
sub-extensive against the brute-force spacetime cost `Θ(T⁴)` (volume `Θ(T³)` times `T` cycles): the
3-D compute-watch total. A full forward run to radius `T` posts `Θ(T²)` net forced distinctions, not
the `Θ(T⁴)` a volume-times-ticks accounting would charge. -/
theorem interface_total_growth (T : ℕ) (hT : 1 ≤ T) :
    (B T).card - (B 1).card = 8 * T ^ 2 - 8 * T := by
  rw [interface_card_eq T hT, interface_card_eq 1 (le_refl 1)]
  simp only [one_pow, mul_one]
  have hsq : T ≤ T ^ 2 := by nlinarith [hT]
  omega

end Octahedron

end PolarizedBirthInterface
end Cosmology
end IndisputableMonolith
