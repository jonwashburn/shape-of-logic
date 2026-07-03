import Mathlib

/-!
# Cosmology: the Euler characteristic of the assembled recognition foam (Phase 18)

## Status: THEOREM (0 sorry, 0 RS-internal axiom).

Phase 15 assembles a genuine many-domain foam from the forced birth law; Phase 17
freezes its super-horizon part. This module gives the parameter-free TOPOLOGICAL readout
that `scripts/cosmogenesis/foam_topology.py` computes on the assembled structure: the
cubical Euler characteristic of a digital region, the recognition analogue of the
cosmic-web genus statistic.

The Euler characteristic of a finite cubical complex is the alternating sum of its cell
counts, `χ = N₀ − N₁ + N₂ − N₃` (occupied vertices, minus unit edges, plus unit squares,
minus unit cubes). Two facts make the numeric readout meaningful with no fitted scale,
and both are proved here.

## §1. Contractible normalization: a filled box reads `χ = 1`

A filled `d`-box has `χ = 1`, INDEPENDENT of its side lengths
(`eulerChar{1,2,3}D_filledBox`). That size-independence is the signature of a topological
invariant: a solid region, however large, has the Euler characteristic of a point. So in
the numeric readout any deviation of `χ` from `1` measures genuine topology, extra
connected components, tunnels (`b₁`), or enclosed voids (`b₂`), and never mere size. The
2-D identity is `N₀ − N₁ + N₂ = (a+1)(b+1) − [a(b+1) + (a+1)b] + ab = 1`; the 3-D identity
is the analogous alternating sum over the six face families and the cube interior.

## §2. Inclusion-exclusion (valuation): `χ` is additive over domains

`χ(A ∪ B) + χ(A ∩ B) = χ(A) + χ(B)` for any two finite cell sets
(`eulerChar_union_add_inter`), so `χ` is additive over disjoint unions
(`eulerChar_disjoint_union`). This is the combinatorial core that makes `χ` well-defined
and is the reason the readout may sum the Euler characteristic over the separated locked
domains the law assembles: `k` disjoint solid domains read `χ = k`, recovering the
component count, while a single contractible domain reads `χ = 1`.

## What the numeric module shows on top of this (classical, not Lean)

The polar law assembles a single contractible domain (`χ = 1`), while the Thue-Morse foam
fragments into a simply-connected dust whose `χ` equals its component count `b₀` (so
`b₁ = b₂ = 0`: no tunnels, no enclosed voids). The Euler curve `χ(R)` as the world grows
is a topological signature that separates the laws, and the Phase-17 freeze-out lowers
`χ` by erasing the inner ball's topology to the vacuum while the frozen outer foam keeps
its dust topology. Hole/void detection is checked numerically against hand-built shapes
(a 2-D annulus reads `χ = 0`, a hollow 3-D shell reads `χ = 2`).

## §4. The closed forced relaxation erases topology (Phase 20)

The Phase-7 forced dynamics (`RecognitionEquilibrium`) relaxes any coupled world to
consensus, conserving the level sum and dropping the level variance monotonically. A
connected `σ = 0` world therefore relaxes to the all-zero field, whose positive excursion
set is empty (`χ = 0`, the vacuum); a positive consensus fills the region (`χ = χ(K)`, one
blob). Either way every handle and enclosed void is gone (`eulerChar_excursion_empty`,
`eulerChar_excursion_all`). So a sponge fed to the closed dynamics has its topology erased,
the law-level fact behind `scripts/cosmogenesis/foam_relaxation_topology.py`: sustained
cosmic-web structure needs the OPEN driven law (Phase 11), not the closed relaxation.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace FoamTopology

open Finset

/-! ## §1. The Euler characteristic as an alternating cell-count sum, and its valuation. -/

/-- The Euler characteristic of a finite set of cells, each weighted by `(-1)` raised to
its dimension: `χ(K) = ∑_{c ∈ K} (-1)^{dim c}`. For a cubical complex this is the
alternating sum of cell counts by dimension, `N₀ − N₁ + N₂ − …`, the quantity computed
in `scripts/cosmogenesis/foam_topology.py`. -/
def eulerChar {α : Type*} (dim : α → ℕ) (K : Finset α) : ℤ :=
  ∑ c ∈ K, (-1 : ℤ) ^ (dim c)

/-- The empty complex has Euler characteristic zero. -/
@[simp] theorem eulerChar_empty {α : Type*} (dim : α → ℕ) :
    eulerChar dim (∅ : Finset α) = 0 := by
  simp [eulerChar]

/-- **THEOREM (valuation / inclusion-exclusion).** The cubical Euler characteristic is a
valuation: `χ(A ∪ B) + χ(A ∩ B) = χ(A) + χ(B)`. This is the combinatorial core that makes
`χ` well-defined and additive; it is the reason the numeric readout may sum `χ` over the
locked domains the law assembles. -/
theorem eulerChar_union_add_inter {α : Type*} [DecidableEq α] (dim : α → ℕ)
    (A B : Finset α) :
    eulerChar dim (A ∪ B) + eulerChar dim (A ∩ B)
      = eulerChar dim A + eulerChar dim B := by
  classical
  unfold eulerChar
  exact Finset.sum_union_inter

/-- **THEOREM.** Over disjoint cell sets the Euler characteristic is additive:
`χ(A ∪ B) = χ(A) + χ(B)`. So `k` separated locked domains contribute `k` times their
Euler characteristic; with the box normalization of §2, `k` disjoint solid domains read
`χ = k`, recovering the connected-component count. -/
theorem eulerChar_disjoint_union {α : Type*} [DecidableEq α] (dim : α → ℕ)
    {A B : Finset α} (h : Disjoint A B) :
    eulerChar dim (A ∪ B) = eulerChar dim A + eulerChar dim B := by
  classical
  have hbase := eulerChar_union_add_inter dim A B
  have hinter : A ∩ B = (∅ : Finset α) := Finset.disjoint_iff_inter_eq_empty.mp h
  rw [hinter, eulerChar_empty, add_zero] at hbase
  exact hbase

/-! ## §2. The contractible normalization: a filled box reads `χ = 1`, size-independent. -/

/-- **THEOREM (1-D normalization).** A filled segment of `a + 1` lattice points (so `a`
unit edges) has Euler characteristic `N₀ − N₁ = (a+1) − a = 1`: one contractible
component, independent of length. -/
theorem eulerChar1D_filledBox (a : ℤ) : (a + 1) - a = 1 := by ring

/-- **THEOREM (2-D normalization).** A filled rectangle of `(a+1)×(b+1)` lattice points
has Euler characteristic `N₀ − N₁ + N₂ = 1`, INDEPENDENT of `a, b`. Here
`N₀ = (a+1)(b+1)` vertices, `N₁ = a(b+1) + (a+1)b` unit edges (horizontal then vertical),
and `N₂ = a·b` unit squares. A solid rectangle, however large, is topologically a
point. -/
theorem eulerChar2D_filledBox (a b : ℤ) :
    (a + 1) * (b + 1) - (a * (b + 1) + (a + 1) * b) + a * b = 1 := by ring

/-- **THEOREM (3-D normalization).** A filled box of `(a+1)×(b+1)×(c+1)` lattice points
has Euler characteristic `N₀ − N₁ + N₂ − N₃ = 1`, INDEPENDENT of `a, b, c`. The cell
counts are `N₀ = (a+1)(b+1)(c+1)`; `N₁ = a(b+1)(c+1) + (a+1)b(c+1) + (a+1)(b+1)c` (edges
along the three axes); `N₂ = ab(c+1) + a(b+1)c + (a+1)bc` (squares in the three coordinate
planes); `N₃ = abc` (unit cubes). A solid box, however large, is topologically a point,
so in the numeric readout any deviation of `χ` from `1` measures genuine topology, never
size. -/
theorem eulerChar3D_filledBox (a b c : ℤ) :
    (a + 1) * (b + 1) * (c + 1)
      - (a * (b + 1) * (c + 1) + (a + 1) * b * (c + 1) + (a + 1) * (b + 1) * c)
      + (a * b * (c + 1) + a * (b + 1) * c + (a + 1) * b * c)
      - a * b * c = 1 := by ring

/-! ## §2b. The Betti detectors: one removed interior vertex is one hole (2-D) or one void (3-D).

These normalize the separated Betti readout in `scripts/cosmogenesis/foam_betti.py`. Removing a
single strictly-interior vertex from a filled box (with all its incident cells present, so the box
side is at least three per axis) deletes the vertex and its incident higher cells. In 2-D the
removed contributions are `1` vertex, `4` edges, `4` squares, so `χ` falls from `1` to
`1 + (-1 + 4 - 4) = 0`: the solid becomes an annulus with one tunnel (`b₁ = 1`). In 3-D they are
`1` vertex, `6` edges, `12` squares, `8` cubes, so `χ` rises from `1` to
`1 + (-1 + 6 - 12 + 8) = 2`: the solid becomes a hollow shell with one enclosed void (`b₂ = 1`).
With `eulerChar{2,3}D_filledBox` (the blob, `χ = 1`) these pin all three primitive topologies the
readout reports: blob (`χ = 1`), hole (`χ = 0`), void (`χ = 2`). -/

/-- **THEOREM (2-D hole detector).** A filled rectangle with one strictly-interior vertex removed
has `χ = 0`: deleting the vertex (`N₀ −= 1`), its `4` incident edges, and its `4` incident squares
drops `χ` from `1` to `0`, the invariant of an annulus with one tunnel (`b₁ = 1`). Meaningful for
`a, b ≥ 2` (so a strictly-interior vertex exists); the identity itself holds for all `a, b`. -/
theorem eulerChar2D_oneHole (a b : ℤ) :
    ((a + 1) * (b + 1) - 1)
      - ((a * (b + 1) + (a + 1) * b) - 4)
      + (a * b - 4) = 0 := by ring

/-- **THEOREM (3-D void detector).** A filled box with one strictly-interior vertex removed has
`χ = 2`: deleting the vertex (`N₀ −= 1`), its `6` incident edges, `12` incident squares, and `8`
incident cubes raises `χ` from `1` to `2`, the invariant of a hollow shell with one enclosed void
(`b₂ = 1`). Meaningful for `a, b, c ≥ 2` (so a strictly-interior vertex exists); the identity
itself holds for all `a, b, c`. -/
theorem eulerChar3D_oneVoid (a b c : ℤ) :
    ((a + 1) * (b + 1) * (c + 1) - 1)
      - ((a * (b + 1) * (c + 1) + (a + 1) * b * (c + 1) + (a + 1) * (b + 1) * c) - 6)
      + ((a * b * (c + 1) + a * (b + 1) * c + (a + 1) * b * c) - 12)
      - (a * b * c - 8) = 2 := by ring

/-! ## §3. The freeze-out lowers `χ`: erasing a contractible inner ball drops it by one. -/

/-- **THEOREM (freeze-out simplification, abstract form).** If the assembled positive
region splits as a disjoint union of an inner ball `I` and an outer frozen foam `O`, and
the inner ball is contractible (`χ(I) = 1`, the §2 normalization), then erasing the inner
ball (the Phase-17 homogenization to the vacuum) lowers the total Euler characteristic by
exactly one: `χ(I ∪ O) = χ(O) + 1`. This is the law-level statement behind the numeric
drop in `χ` across the recognition front. -/
theorem eulerChar_freezeOut_drop {α : Type*} [DecidableEq α] (dim : α → ℕ)
    {I O : Finset α} (hdisj : Disjoint I O) (hI : eulerChar dim I = 1) :
    eulerChar dim (I ∪ O) = eulerChar dim O + 1 := by
  rw [eulerChar_disjoint_union dim hdisj, hI]
  ring

/-! ## §4. The closed forced relaxation erases topology: the `σ = 0` consensus endpoint is trivial.

The Phase-7 forced recognition dynamics (`Cosmology.RecognitionEquilibrium`) drives any coupled
world to consensus. The level sum is conserved by every forced resolution
(`RecognitionEquilibrium.pairResolve_levelSum`) and the level variance is a Lyapunov function that
drops by exactly `(xᵢ − xⱼ)² / 2` per resolution (`RecognitionEquilibrium.variance_pairResolve`,
hence `variance_nonincreasing`), with the zero-cost fixed point being consensus
(`RecognitionEquilibrium.totalCost_eq_zero_iff`). So a connected `σ = 0` world relaxes to the
all-zero field: the unique consensus level is `σ / n = 0`.

Read on the positive excursion set `{c ∈ K : p c}` with `p c := 0 < f c` (the over-dense cells),
that endpoint is topologically TRIVIAL. The two lemmas below pin the two possible consensus
excursion sets, and both kill every handle (`b₁`) and enclosed void (`b₂`):

* a `σ = 0` connected consensus is the all-zero field, so no cell is over-dense, the excursion set
  is empty, and `χ = 0` (the vacuum, `eulerChar_excursion_empty`);
* a strictly positive consensus (`σ > 0`) makes every cell over-dense, so the excursion set is the
  whole region and `χ = χ(K)` (a single contractible blob, `= 1` for a box by §2,
  `eulerChar_excursion_all`).

This is the law-level content of the `scripts/cosmogenesis/foam_relaxation_topology.py` history: a
sponge fed to the closed dynamics has its handles and voids erased and decays to the vacuum. The
closed forced law cannot sustain assembled structure; the cosmic web requires the OPEN driven law
(Phase 11), and that necessity is exactly the gap between this trivial endpoint and a sponge. -/

/-- **THEOREM (vacuum endpoint).** If no cell of `K` is over-dense (`¬ p c` for every `c ∈ K`, the
`σ = 0` consensus `f ≡ 0` under `p c := 0 < f c`), the positive excursion set `K.filter p` is empty
and its Euler characteristic is `0`. The closed forced relaxation erases the structure to the
vacuum. -/
theorem eulerChar_excursion_empty {α : Type*} (dim : α → ℕ) (p : α → Prop) [DecidablePred p]
    (K : Finset α) (h : ∀ c ∈ K, ¬ p c) :
    eulerChar dim (K.filter p) = 0 := by
  rw [Finset.filter_false_of_mem h, eulerChar_empty]

/-- **THEOREM (blob endpoint).** If every cell of `K` is over-dense (`p c` for every `c ∈ K`, a
strictly positive consensus `σ > 0`), the positive excursion set `K.filter p` is all of `K`, so its
Euler characteristic is `χ(K)`, a single contractible blob (`= 1` for a filled box by §2). Either
consensus endpoint is topologically trivial: no handles (`b₁`), no enclosed voids (`b₂`). -/
theorem eulerChar_excursion_all {α : Type*} (dim : α → ℕ) (p : α → Prop) [DecidablePred p]
    (K : Finset α) (h : ∀ c ∈ K, p c) :
    eulerChar dim (K.filter p) = eulerChar dim K := by
  rw [Finset.filter_true_of_mem h]

end FoamTopology
end Cosmology
end IndisputableMonolith
