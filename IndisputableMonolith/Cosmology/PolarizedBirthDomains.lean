import Mathlib
import IndisputableMonolith.Cosmology.InterfaceComponentBound
import IndisputableMonolith.Cosmology.LatticeBallVolume

/-!
# The forced birth field is carried at O(1) cost: carried-state sub-extensivity

## Status: THEOREM (0 sorry, 0 axiom beyond Mathlib's standard three).

Phase 48 (`InterfaceComponentBound`) proved the locked-domain count is at most the interface plus
one on the diamond and octahedron, for any charge field. Phase 49 (`LatticeBallVolume`) proved the
world's size in closed form (`2t² + 2t + 1` cells in 2D, the centered-octahedral number in 3D). This
module pins down the carried state for the *forced conjugate-birth (polarized) field* itself: the
field the 2D/3D shell birth installs, namely `+1` on the fine half `x > 0`, `-1` on the coarse half
`x < 0`, and `0` on the `x = 0` spine.

For that field the number of locked domains is **at most 3, independent of the radius** (the fine
half, the coarse half, and the spine are each one 4-connected / 6-connected monochromatic region).
So a world of `Θ(t^d)` cells is carried as O(1) super-regions: the carried-state fraction
`components / volume → 0`. This is the sharpest possible sub-extensivity, and it is the North-Star
claim "carry each region at the coarsest φ-rung its recognition allows" made exact for the birth
configuration, as a THEOREM (not numeric).

The proof reuses the Phase-48 descent idea, generalized to descent toward a *finite set* of roots:
`clos_someRoot_of_descent` says that if a height vanishes only on a list of roots and every other
cell steps down a monochromatic edge, then every cell connects to one of the roots;
`comp_le_of_roots` turns "every class is represented among `roots`" into `components ≤ roots.length`.
The polarized height `(|x| - [x ≠ 0]) + |y| (+ |z|)` descends within each charge level to its own
root (`(1,0)`, `(-1,0)`, `(0,0)` in 2D), so the three roots cover every cell and `components ≤ 3`.

HONEST SCOPE. This is the carried state of the *birth* field. The live engine then diffuses the
spine by forced resolution, creating additional small interface components; those are bounded above
by the Phase-48 interface bound, not counted here. The "carried at O(1)" statement is exact for the
forced conjugate birth, which is the configuration the shell creation installs each cadence cycle.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace PolarizedBirthDomains

open InterfaceComponentBound

variable {V : Type*}

/-! ### General: descent toward a finite set of roots bounds the component count. -/

/-- **Descent toward a finite set of roots.** If a height `h : V → ℕ` vanishes only on the cells in
`roots`, and every cell of positive height has an edge (in either orientation) to a strictly-lower
cell, then every cell is connected to some root in `roots`. Strong induction on `h v`, exactly as
`InterfaceComponentBound.clos_root_of_descent` but with several roots instead of one. -/
theorem clos_someRoot_of_descent [Finite V] (E : List (V × V)) (h : V → ℕ) (roots : List V)
    (hzero : ∀ v, h v = 0 → v ∈ roots)
    (hdesc : ∀ v, h v ≠ 0 → ∃ u, ((v, u) ∈ E ∨ (u, v) ∈ E) ∧ h u < h v) :
    ∀ v, ∃ r ∈ roots, clos E v r := by
  have e := clos_equiv E
  have H : ∀ n, ∀ v, h v = n → ∃ r ∈ roots, clos E v r := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv
      rcases Nat.eq_zero_or_pos (h v) with h0 | hpos
      · exact ⟨v, hzero v h0, e.refl v⟩
      · have hvne : h v ≠ 0 := by omega
        obtain ⟨u, hedge, hlt⟩ := hdesc v hvne
        have hvu : clos E v u := by
          rcases hedge with he | he
          · exact Relation.EqvGen.rel v u he
          · exact e.symm (Relation.EqvGen.rel u v he)
        obtain ⟨r, hr, hur⟩ := ih (h u) (by omega) u rfl
        exact ⟨r, hr, e.trans hvu hur⟩
  intro v
  exact H (h v) v rfl

/-- **Few roots bound the component count.** If every cell's component is represented by some root in
`roots`, the number of components is at most `roots.length`. (The quotient map, restricted to the
roots, hits every class.) -/
theorem comp_le_of_roots [Finite V] (E : List (V × V)) (roots : List V)
    (hcov : ∀ v : V, ∃ r ∈ roots, clos E v r) : comp E ≤ roots.length := by
  classical
  haveI : Fintype (Quotient (cs E)) := Fintype.ofFinite _
  have himg : (Finset.univ : Finset (Quotient (cs E)))
      ⊆ roots.toFinset.image (Quotient.mk (cs E)) := by
    intro q _
    obtain ⟨v, rfl⟩ := Quotient.exists_rep q
    obtain ⟨r, hr, hvr⟩ := hcov v
    rw [Finset.mem_image]
    exact ⟨r, List.mem_toFinset.2 hr, Quotient.sound ((clos_equiv E).symm hvr)⟩
  calc comp E = Fintype.card (Quotient (cs E)) := by
            rw [comp, Nat.card_eq_fintype_card]
    _ = (Finset.univ : Finset (Quotient (cs E))).card := by rw [Finset.card_univ]
    _ ≤ (roots.toFinset.image (Quotient.mk (cs E))).card := Finset.card_le_card himg
    _ ≤ roots.toFinset.card := Finset.card_image_le
    _ ≤ roots.length := List.toFinset_card_le roots

/-- **Charge is a monochromatic-closure invariant.** Two cells connected through monochromatic edges
carry the same charge. Induction on the equivalence-closure derivation: the generating (monochromatic)
edges are equal-charge by construction; reflexivity, symmetry, and transitivity preserve equality. -/
theorem clos_mono_charge {β : Type*} [DecidableEq β] (E : List (V × V)) (c : V → β) {u v : V}
    (h : clos (E.filter (fun p => decide (c p.1 = c p.2))) u v) : c u = c v := by
  induction h with
  | rel x y hxy =>
      simp only [gen, List.mem_filter, decide_eq_true_eq] at hxy
      exact hxy.2
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Three distinct charges force at least three components.** If three cells carry pairwise-distinct
charges, they lie in three distinct monochromatic components (charge is a closure invariant), so the
induced charge map on the quotient hits three values and the component count is at least 3. -/
theorem three_le_comp_of_three_charges {β : Type*} [Finite V] [DecidableEq β] (E : List (V × V))
    (c : V → β) (a b d : V) (hab : c a ≠ c b) (had : c a ≠ c d) (hbd : c b ≠ c d) :
    3 ≤ comp (E.filter (fun p => decide (c p.1 = c p.2))) := by
  classical
  set F := E.filter (fun p => decide (c p.1 = c p.2)) with hF
  haveI : Fintype (Quotient (cs F)) := Fintype.ofFinite _
  set q : Quotient (cs F) → β :=
    Quotient.lift c (fun x y h => clos_mono_charge E c (hF ▸ h)) with hq
  have hqa : q (Quotient.mk (cs F) a) = c a := rfl
  have hqb : q (Quotient.mk (cs F) b) = c b := rfl
  have hqd : q (Quotient.mk (cs F) d) = c d := rfl
  have hsub : ({c a, c b, c d} : Finset β) ⊆ Finset.image q Finset.univ := by
    intro w hw
    rw [Finset.mem_image]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨Quotient.mk (cs F) a, Finset.mem_univ _, hqa⟩
    · exact ⟨Quotient.mk (cs F) b, Finset.mem_univ _, hqb⟩
    · exact ⟨Quotient.mk (cs F) d, Finset.mem_univ _, hqd⟩
  have hcard : ({c a, c b, c d} : Finset β).card = 3 := by
    rw [Finset.card_insert_of_not_mem (by simp [hab, had]),
        Finset.card_insert_of_not_mem (by simp [hbd]), Finset.card_singleton]
  calc 3 = ({c a, c b, c d} : Finset β).card := hcard.symm
    _ ≤ (Finset.image q Finset.univ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Quotient (cs F))).card := Finset.card_image_le
    _ = Fintype.card (Quotient (cs F)) := Finset.card_univ
    _ = comp F := by rw [comp, Nat.card_eq_fintype_card]

/-! ### The 2-D diamond: the polarized birth field has at most 3 locked domains. -/

namespace Diamond

open InterfaceComponentBound.Diamond

/-- The forced conjugate-birth charge on the diamond: `+1` on the fine half `x > 0`, `-1` on the
coarse half `x < 0`, `0` on the `x = 0` spine. -/
def polarized (t : ℕ) (v : Vtx t) : ℤ :=
  if 0 < v.val.1 then 1 else if v.val.1 < 0 then -1 else 0

/-- The monochromatic edge list of the polarized diamond: adjacent same-charge cell pairs. -/
noncomputable def Fmono (t : ℕ) : List (Vtx t × Vtx t) :=
  (edges t).filter (fun p => decide (polarized t p.1 = polarized t p.2))

/-- The descent height toward the three roots: `(|x| - [x ≠ 0]) + |y|`, which vanishes exactly at
`(1,0)`, `(-1,0)`, `(0,0)` and decreases along a same-charge step toward the relevant root. -/
def hgt (t : ℕ) (v : Vtx t) : ℕ :=
  (v.val.1.natAbs - (if v.val.1 = 0 then 0 else 1)) + v.val.2.natAbs

/-- A monochromatic edge between two diamond cells: adjacency plus equal polarized charge. -/
theorem mem_Fmono (t : ℕ) (a b : Vtx t)
    (hadj : adj a.val b.val) (hc : polarized t a = polarized t b) : (a, b) ∈ Fmono t := by
  rw [Fmono, List.mem_filter]
  exact ⟨(mem_edges t a b).2 hadj, by simpa using hc⟩

/-- The three roots of the polarized diamond (need `t ≥ 1` for the `±1` halves to be present). -/
def roots (t : ℕ) (ht : 1 ≤ t) : List (Vtx t) :=
  [ ⟨(1, 0), by rw [mem_ball_iff]; omega⟩
  , ⟨(-1, 0), by rw [mem_ball_iff]; omega⟩
  , ⟨(0, 0), by rw [mem_ball_iff]; omega⟩ ]

/-- A zero-height cell is one of the three roots. -/
theorem hzero (t : ℕ) (ht : 1 ≤ t) :
    ∀ v : Vtx t, hgt t v = 0 → v ∈ roots t ht := by
  rintro ⟨⟨x, y⟩, hmem⟩ h0
  simp only [hgt] at h0
  rw [roots]
  by_cases hx : x = 0
  · subst hx
    have hy : y = 0 := by simp only [Int.natAbs_zero] at h0; omega
    subst hy
    simp [List.mem_cons]
  · have hx1 : x.natAbs = 1 := by
      rw [if_neg hx] at h0; omega
    have hy : y = 0 := by
      rw [if_neg hx] at h0; omega
    subst hy
    rcases Int.natAbs_eq_iff.1 hx1 with hxp | hxn
    · subst hxp; simp [List.mem_cons]
    · have : x = -1 := by simpa using hxn
      subst this; simp [List.mem_cons]

/-- From any off-root diamond cell there is a monochromatic edge to a strictly-lower cell: move the
non-zero coordinate toward the root of the cell's own charge level. -/
theorem hdesc (t : ℕ) :
    ∀ v : Vtx t, hgt t v ≠ 0 →
      ∃ u, ((v, u) ∈ Fmono t ∨ (u, v) ∈ Fmono t) ∧ hgt t u < hgt t v := by
  rintro ⟨⟨x, y⟩, hmem⟩ hv
  rw [mem_ball_iff] at hmem
  simp only [hgt] at hv ⊢
  rcases lt_trichotomy y 0 with hy | hy | hy
  · -- y < 0: step to (x, y+1), same x so same charge
    refine ⟨⟨(x, y + 1), by rw [mem_ball_iff]; omega⟩, Or.inl (mem_Fmono t _ _ ?_ ?_), ?_⟩
    · unfold adj; dsimp only; omega
    · simp only [polarized]
    · dsimp only; split_ifs <;> omega
  · -- y = 0: step the x-coordinate toward ±1 (only possible when |x| ≥ 2)
    subst hy
    rcases lt_trichotomy x 0 with hx | hx | hx
    · -- x < 0; root is (-1,0); descend needs x ≤ -2
      have hx2 : x ≤ -2 := by
        rcases lt_or_ge x (-1) with h | h
        · omega
        · exfalso; have : x = -1 := by omega
          subst this; simp at hv
      refine ⟨⟨(x + 1, 0), by rw [mem_ball_iff]; omega⟩, Or.inl (mem_Fmono t _ _ ?_ ?_), ?_⟩
      · unfold adj; dsimp only; omega
      · simp only [polarized]; dsimp only; split_ifs <;> omega
      · dsimp only; split_ifs <;> omega
    · exfalso; subst hx; simp at hv
    · -- x > 0; root is (1,0); descend needs x ≥ 2
      have hx2 : 2 ≤ x := by
        rcases lt_or_ge 1 x with h | h
        · omega
        · exfalso; have : x = 1 := by omega
          subst this; simp at hv
      refine ⟨⟨(x - 1, 0), by rw [mem_ball_iff]; omega⟩, Or.inl (mem_Fmono t _ _ ?_ ?_), ?_⟩
      · unfold adj; dsimp only; omega
      · simp only [polarized]; dsimp only; split_ifs <;> omega
      · dsimp only; split_ifs <;> omega
  · -- y > 0: step to (x, y-1), same x so same charge
    refine ⟨⟨(x, y - 1), by rw [mem_ball_iff]; omega⟩, Or.inl (mem_Fmono t _ _ ?_ ?_), ?_⟩
    · unfold adj; dsimp only; omega
    · simp only [polarized]
    · dsimp only; split_ifs <;> omega

/-- **The polarized birth field is carried as at most 3 super-regions, every radius.** For the forced
conjugate-birth charge on the diamond of radius `t ≥ 1`, the number of locked (monochromatic
4-connected) domains is at most 3: the fine half, the coarse half, and the spine. THEOREM for all
radii. -/
theorem polarized_components_le_three (t : ℕ) (ht : 1 ≤ t) :
    comp (Fmono t) ≤ 3 := by
  have hcov := clos_someRoot_of_descent (Fmono t) (hgt t) (roots t ht) (hzero t ht)
    (by
      intro v hv
      obtain ⟨u, hedge, hlt⟩ := hdesc t v hv
      exact ⟨u, hedge, hlt⟩)
  have := comp_le_of_roots (Fmono t) (roots t ht) hcov
  simpa [roots] using this

/-- **The polarized birth field has exactly 3 locked domains, every radius (2-D).** The upper bound
`≤ 3` (descent toward the three roots) meets the lower bound `≥ 3` (the three roots carry the three
distinct charges `+1`, `-1`, `0`, and charge is a closure invariant). So the carried state is exactly
3 for all `t ≥ 1`: the fine half, the coarse half, and the spine. -/
theorem polarized_components_eq_three (t : ℕ) (ht : 1 ≤ t) : comp (Fmono t) = 3 := by
  refine le_antisymm (polarized_components_le_three t ht) ?_
  exact three_le_comp_of_three_charges (edges t) (polarized t)
    ⟨(1, 0), by rw [mem_ball_iff]; omega⟩
    ⟨(-1, 0), by rw [mem_ball_iff]; omega⟩
    ⟨(0, 0), by rw [mem_ball_iff]; omega⟩
    (by simp only [polarized]; dsimp only; decide)
    (by simp only [polarized]; dsimp only; decide)
    (by simp only [polarized]; dsimp only; decide)

/-- **Carried-state sub-extensivity for the birth field (2-D).** The polarized diamond fills
`2t² + 2t + 1` cells (Phase 49) but is carried as exactly 3 super-regions, so the carried state times
the radius is at most the area for every `t ≥ 1`: `3 t ≤ card (ball t)`, the carried cost is `O(1)`
while the world is `Θ(t²)`. -/
theorem polarized_carried_subextensive (t : ℕ) (ht : 1 ≤ t) :
    comp (Fmono t) = 3 ∧ 3 * t ≤ (InterfaceComponentBound.Diamond.ball t).card := by
  refine ⟨polarized_components_eq_three t ht, ?_⟩
  rw [LatticeBallVolume.Diamond.card_ball]
  nlinarith [ht]

end Diamond

/-! ### The 3-D octahedron: the polarized birth field has at most 3 locked domains.

Identical structure to the diamond, with the spine now a 2-D disk (`x = 0`) and the two halves 3-D.
The dimension D = 3 is the one the forcing chain selects. -/

namespace Octahedron

open InterfaceComponentBound.Octahedron

/-- The forced conjugate-birth charge on the octahedron: `+1` on the fine half `x > 0`, `-1` on the
coarse half `x < 0`, `0` on the `x = 0` spine disk. -/
def polarized (t : ℕ) (v : Vtx t) : ℤ :=
  if 0 < v.val.1 then 1 else if v.val.1 < 0 then -1 else 0

/-- The monochromatic edge list of the polarized octahedron. -/
noncomputable def Fmono (t : ℕ) : List (Vtx t × Vtx t) :=
  (edges t).filter (fun p => decide (polarized t p.1 = polarized t p.2))

/-- The descent height toward the three roots: `(|x| - [x ≠ 0]) + |y| + |z|`. -/
def hgt (t : ℕ) (v : Vtx t) : ℕ :=
  (v.val.1.natAbs - (if v.val.1 = 0 then 0 else 1)) + v.val.2.1.natAbs + v.val.2.2.natAbs

theorem mem_Fmono (t : ℕ) (a b : Vtx t)
    (hadj : adj a.val b.val) (hc : polarized t a = polarized t b) : (a, b) ∈ Fmono t := by
  rw [Fmono, List.mem_filter]
  exact ⟨(mem_edges t a b).2 hadj, by simpa using hc⟩

/-- The three roots of the polarized octahedron (need `t ≥ 1`). -/
def roots (t : ℕ) (ht : 1 ≤ t) : List (Vtx t) :=
  [ ⟨(1, 0, 0), by rw [mem_ball_iff]; omega⟩
  , ⟨(-1, 0, 0), by rw [mem_ball_iff]; omega⟩
  , ⟨(0, 0, 0), by rw [mem_ball_iff]; omega⟩ ]

theorem hzero (t : ℕ) (ht : 1 ≤ t) :
    ∀ v : Vtx t, hgt t v = 0 → v ∈ roots t ht := by
  rintro ⟨⟨x, y, z⟩, hmem⟩ h0
  simp only [hgt] at h0
  rw [roots]
  by_cases hx : x = 0
  · subst hx
    have hy : y = 0 := by simp only [Int.natAbs_zero] at h0; omega
    have hz : z = 0 := by simp only [Int.natAbs_zero] at h0; omega
    subst hy; subst hz
    simp [List.mem_cons]
  · have hx1 : x.natAbs = 1 := by rw [if_neg hx] at h0; omega
    have hy : y = 0 := by rw [if_neg hx] at h0; omega
    have hz : z = 0 := by rw [if_neg hx] at h0; omega
    subst hy; subst hz
    rcases Int.natAbs_eq_iff.1 hx1 with hxp | hxn
    · subst hxp; simp [List.mem_cons]
    · have : x = -1 := by simpa using hxn
      subst this; simp [List.mem_cons]

theorem hdesc (t : ℕ) :
    ∀ v : Vtx t, hgt t v ≠ 0 →
      ∃ u, ((v, u) ∈ Fmono t ∨ (u, v) ∈ Fmono t) ∧ hgt t u < hgt t v := by
  rintro ⟨⟨x, y, z⟩, hmem⟩ hv
  rw [mem_ball_iff] at hmem
  simp only [hgt] at hv ⊢
  rcases lt_trichotomy z 0 with hz | hz | hz
  · refine ⟨⟨(x, y, z + 1), by rw [mem_ball_iff]; omega⟩, Or.inl (mem_Fmono t _ _ ?_ ?_), ?_⟩
    · unfold adj; dsimp only; omega
    · simp only [polarized]
    · dsimp only; split_ifs <;> omega
  · subst hz
    rcases lt_trichotomy y 0 with hy | hy | hy
    · refine ⟨⟨(x, y + 1, 0), by rw [mem_ball_iff]; omega⟩, Or.inl (mem_Fmono t _ _ ?_ ?_), ?_⟩
      · unfold adj; dsimp only; omega
      · simp only [polarized]
      · dsimp only; split_ifs <;> omega
    · subst hy
      rcases lt_trichotomy x 0 with hx | hx | hx
      · have hx2 : x ≤ -2 := by
          rcases lt_or_ge x (-1) with h | h
          · omega
          · exfalso; have : x = -1 := by omega
            subst this; simp at hv
        refine ⟨⟨(x + 1, 0, 0), by rw [mem_ball_iff]; omega⟩, Or.inl (mem_Fmono t _ _ ?_ ?_), ?_⟩
        · unfold adj; dsimp only; omega
        · simp only [polarized]; dsimp only; split_ifs <;> omega
        · dsimp only; split_ifs <;> omega
      · exfalso; subst hx; simp at hv
      · have hx2 : 2 ≤ x := by
          rcases lt_or_ge 1 x with h | h
          · omega
          · exfalso; have : x = 1 := by omega
            subst this; simp at hv
        refine ⟨⟨(x - 1, 0, 0), by rw [mem_ball_iff]; omega⟩, Or.inl (mem_Fmono t _ _ ?_ ?_), ?_⟩
        · unfold adj; dsimp only; omega
        · simp only [polarized]; dsimp only; split_ifs <;> omega
        · dsimp only; split_ifs <;> omega
    · refine ⟨⟨(x, y - 1, 0), by rw [mem_ball_iff]; omega⟩, Or.inl (mem_Fmono t _ _ ?_ ?_), ?_⟩
      · unfold adj; dsimp only; omega
      · simp only [polarized]
      · dsimp only; split_ifs <;> omega
  · refine ⟨⟨(x, y, z - 1), by rw [mem_ball_iff]; omega⟩, Or.inl (mem_Fmono t _ _ ?_ ?_), ?_⟩
    · unfold adj; dsimp only; omega
    · simp only [polarized]
    · dsimp only; split_ifs <;> omega

/-- **The polarized birth field is carried as at most 3 super-regions, every radius (3-D).** For the
forced conjugate-birth charge on the octahedron of radius `t ≥ 1`, the number of locked
(monochromatic 6-connected) domains is at most 3: the fine half, the coarse half, and the spine disk.
THEOREM for all radii, in the dimension D = 3 the forcing chain selects. -/
theorem polarized_components_le_three (t : ℕ) (ht : 1 ≤ t) :
    comp (Fmono t) ≤ 3 := by
  have hcov := clos_someRoot_of_descent (Fmono t) (hgt t) (roots t ht) (hzero t ht)
    (by
      intro v hv
      obtain ⟨u, hedge, hlt⟩ := hdesc t v hv
      exact ⟨u, hedge, hlt⟩)
  have := comp_le_of_roots (Fmono t) (roots t ht) hcov
  simpa [roots] using this

/-- **The polarized birth field has exactly 3 locked domains, every radius (3-D).** Upper bound `≤ 3`
(descent toward the three roots) meets lower bound `≥ 3` (the three roots carry charges `+1`, `-1`,
`0`). The carried state is exactly 3 for all `t ≥ 1`, in the dimension D = 3 the forcing chain
selects: the fine half, the coarse half, and the spine disk. -/
theorem polarized_components_eq_three (t : ℕ) (ht : 1 ≤ t) : comp (Fmono t) = 3 := by
  refine le_antisymm (polarized_components_le_three t ht) ?_
  exact three_le_comp_of_three_charges (edges t) (polarized t)
    ⟨(1, 0, 0), by rw [mem_ball_iff]; omega⟩
    ⟨(-1, 0, 0), by rw [mem_ball_iff]; omega⟩
    ⟨(0, 0, 0), by rw [mem_ball_iff]; omega⟩
    (by simp only [polarized]; dsimp only; decide)
    (by simp only [polarized]; dsimp only; decide)
    (by simp only [polarized]; dsimp only; decide)

/-- **Carried-state sub-extensivity for the birth field (3-D).** The polarized octahedron fills the
centered-octahedral number of cells (Phase 49: `3 · card = 4t³ + 6t² + 8t + 3`, i.e. `Θ(t³)`) but is
carried as exactly 3 super-regions, so `3 t² ≤ card (ball t)` for every `t`: the carried cost is
`O(1)` while the world is `Θ(t³)`. -/
theorem polarized_carried_subextensive (t : ℕ) (ht : 1 ≤ t) :
    comp (Fmono t) = 3 ∧ 3 * t ^ 2 ≤ (InterfaceComponentBound.Octahedron.ball t).card := by
  refine ⟨polarized_components_eq_three t ht, ?_⟩
  have h := LatticeBallVolume.Octahedron.three_mul_card_ball t
  nlinarith [h, Nat.zero_le t]

end Octahedron

end PolarizedBirthDomains
end Cosmology
end IndisputableMonolith
