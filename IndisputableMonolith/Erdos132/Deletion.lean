/-
Copyright (c) 2026 Recognition Physics Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Erdos-132 `d=1` deletion core: a feasible `d=1` branch at `n ≥ 7` has a deletable vertex.

This module is the load-bearing combinatorial step of the `d=1` *extinction* theorem
("no feasible planar `d=1` set has `≥ 6` points"). It is pure finite combinatorics:
no geometry, only `Finset`.

## The object

A `d=1` branch is a `{0,1,2}`-coloring of the off-diagonal pairs of an `n`-point set
with EXACTLY one pair colored `0` (the unique diameter `{p,q}`) and both colors `1`
and `2` nonempty. Here a color class is recorded as its edge set `E : Finset (Finset
(Fin n))`, each edge a `2`-element vertex set.

## The deletion core (`deletion_exists`)

For `n ≥ 7`, there is a vertex `w ∉ {p,q}` whose removal keeps BOTH non-diameter
colors nonempty (each class still has an edge avoiding `w`). Removing such a `w` also
preserves the unique diameter (it is not an endpoint, and there are no other `0`-edges),
so the induced coloring on `Fin n` minus `w` is again a `d=1` branch. Feasibility
transfers down for free (a subset of a planar realization is realizable). Hence every
feasible `d=1` branch at `n ≥ 7` restricts to one at `n − 1`, and downward induction
reduces all `n ≥ 6` to the (computationally empty) `n = 6` base.

## The pigeonhole

A vertex `w` "kills" color `c` iff every `c`-edge contains `w`. Such a `w` lies in any
single chosen `c`-edge `e_c`, so the kill-set is `⊆ e_c`, hence has `card ≤ 2`. With
two colors that is `≤ 4` killers; together with the two diameter endpoints, the set to
avoid has `card ≤ 6 < 7 ≤ n`, so a good vertex always remains. This is the edge-free
form (no star/triangle case split).
-/
import Mathlib.Tactic

namespace Erdos132.Deletion

open Finset

variable {n : ℕ}

/-- The vertices that lie in **every** edge of `E`: deleting any one of them empties
the color class `E`. -/
def killers (E : Finset (Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter (fun w => ∀ e ∈ E, w ∈ e)

/-- A killer of `E` lies in any single edge `e₀ ∈ E`. -/
lemma killers_subset_edge {E : Finset (Finset (Fin n))} {e0 : Finset (Fin n)}
    (he0 : e0 ∈ E) : killers E ⊆ e0 := by
  intro w hw
  rw [killers, mem_filter] at hw
  exact hw.2 e0 he0

/-- Since every edge has exactly two endpoints, a color class has at most two killers. -/
lemma killers_card_le_two {E : Finset (Finset (Fin n))} {e0 : Finset (Fin n)}
    (he0 : e0 ∈ E) (he0card : e0.card = 2) : (killers E).card ≤ 2 := by
  calc (killers E).card ≤ e0.card := Finset.card_le_card (killers_subset_edge he0)
    _ = 2 := he0card

/-- `w` is **not** a killer of `E` iff some edge of `E` avoids `w`. -/
lemma not_killer_iff {E : Finset (Finset (Fin n))} {w : Fin n} :
    w ∉ killers E ↔ ∃ e ∈ E, w ∉ e := by
  rw [killers, mem_filter]
  push_neg
  constructor
  · intro h; exact h (Finset.mem_univ w)
  · intro h _; exact h

/-- **Deletion core.** Let `{p, q}` be the (unique) diameter pair and let `E1, E2` be
the two non-diameter color classes, each a nonempty set of `2`-element edges. If
`n ≥ 7` then there is a vertex `w ∉ {p, q}` such that each of `E1`, `E2` still has an
edge avoiding `w`. Removing `w` therefore yields a `d=1` branch on `n − 1` vertices. -/
theorem deletion_exists
    (hn : 7 ≤ n) (p q : Fin n)
    (E1 E2 : Finset (Finset (Fin n)))
    (e1 : Finset (Fin n)) (he1 : e1 ∈ E1) (he1card : e1.card = 2)
    (e2 : Finset (Fin n)) (he2 : e2 ∈ E2) (he2card : e2.card = 2) :
    ∃ w : Fin n, w ≠ p ∧ w ≠ q ∧
      (∃ e ∈ E1, w ∉ e) ∧ (∃ e ∈ E2, w ∉ e) := by
  -- The vertices to avoid: the two diameter endpoints, plus the killers of each color.
  set S : Finset (Fin n) := ({p, q} ∪ killers E1) ∪ killers E2 with hS
  -- `card S ≤ 2 + 2 + 2 = 6`.
  have hpq : ({p, q} : Finset (Fin n)).card ≤ 2 := by
    calc ({p, q} : Finset (Fin n)).card ≤ ({q} : Finset (Fin n)).card + 1 :=
          Finset.card_insert_le _ _
      _ = 2 := by simp
  have hk1 : (killers E1).card ≤ 2 := killers_card_le_two he1 he1card
  have hk2 : (killers E2).card ≤ 2 := killers_card_le_two he2 he2card
  have hcard : S.card ≤ 6 := by
    have h12 : ({p, q} ∪ killers E1 : Finset (Fin n)).card ≤ 4 :=
      (Finset.card_union_le _ _).trans (by omega)
    calc S.card ≤ ({p, q} ∪ killers E1 : Finset (Fin n)).card + (killers E2).card :=
          Finset.card_union_le _ _
      _ ≤ 6 := by omega
  -- Hence `S` is a proper subset of `univ`, so it misses some vertex.
  have hlt : S.card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]; omega
  have hss : S ⊂ (Finset.univ : Finset (Fin n)) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ S, ?_⟩
    intro hc; rw [hc] at hlt; exact lt_irrefl _ hlt
  obtain ⟨w, -, hwS⟩ := Finset.exists_of_ssubset hss
  -- Unpack the three avoidances.
  rw [hS] at hwS
  have hw_pq : w ∉ ({p, q} : Finset (Fin n)) := by
    intro hc; exact hwS (Finset.mem_union_left _ (Finset.mem_union_left _ hc))
  have hw_k1 : w ∉ killers E1 := by
    intro hc; exact hwS (Finset.mem_union_left _ (Finset.mem_union_right _ hc))
  have hw_k2 : w ∉ killers E2 := fun hc => hwS (Finset.mem_union_right _ hc)
  have hwp : w ≠ p := by
    intro hc; exact hw_pq (by rw [hc]; exact Finset.mem_insert_self p {q})
  have hwq : w ≠ q := by
    intro hc; exact hw_pq (by rw [hc]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q))
  exact ⟨w, hwp, hwq, not_killer_iff.mp hw_k1, not_killer_iff.mp hw_k2⟩

end Erdos132.Deletion
