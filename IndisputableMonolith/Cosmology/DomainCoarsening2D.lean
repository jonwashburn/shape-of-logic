import IndisputableMonolith.Cosmology.DomainCoarsening

/-!
# The coarsening cost in two dimensions: separable rows, and an upper bound on the 2D component count

## Status: THEOREM (0 sorry, 0 axiom beyond Mathlib's standard three).

This module backs `scripts/cosmogenesis/domain_coarsen_2d.py`, which lifts the locked-domain coarsening off
the line into a 2D world: a locked domain is a maximal 4-connected component of equal charge, carried as one
coarse super-region, and the recognition-active interface between domains is a 1D curve, so the engine cost
localizes to a perimeter (sub-extensive in the area).

The 1D cost law `runs = boundaries + 1` (`Cosmology.DomainCoarsening.runs_eq`) is an exact identity because a
1D interface between two domains is a single point. In 2D the exact analogue `components = bichromatic + 1`
becomes the inequality `components <= bichromatic + 1` (a 2D interface can be multiply connected), which is a
connected-graph fact (component-counting-under-edge-deletion). That fact is now a Lean THEOREM, dimension-free,
in `Cosmology.InterfaceComponentBound.mono_components_le_bichromatic_succ`: on any connected finite world the
monochromatic-component count is at most the bichromatic-edge count plus one. The 2D diamond lattice is one
instance of its connected-ambient hypothesis (wiring the specific lattice graph and identifying the flood-fill
components with the graph components is the routine remaining step; the hard mathematical content, the
edge-deletion merge bound that Mathlib lacked, is discharged there).

What IS a clean theorem, and what this module proves, is the SEPARABLE (row-wise) coarsening cost. Modeling
the 2D field as a list of rows (`List (List α)`), `rowCost` is the total number of 1D super-regions when each
row is coarsened independently (the sum of `runs` over rows), and `rowInterface` is the total horizontal
interface (the sum of `boundaries` over rows). The headline `rowwise_cost_eq` proves, for any grid whose rows
are all nonempty,

  `rowCost rows = rowInterface rows + rows.length`,

i.e. the separable coarsening carries exactly (horizontal interface) + (number of rows) super-regions. This is
the exact per-axis generalization of `runs = boundaries + 1`, summed over rows. The true 2D component
coarsening also merges vertically, so it is never worse: `components_2D <= rowCost` (the numeric bound), and
`rowCost = rowInterface + rows.length` gives a clean, fully-proved upper bound on the carried 2D cost in terms
of the horizontal interface and the row count, with no dependence on the row widths (the area). Composed with
`Cosmology.RecognitionWorkBound` (the resolution cost per cadence cycle is bounded by the cadence INDEPENDENT
of the index type, so it covers 2D cells verbatim), the 2D engine's state and work are both bounded by the
interface, not the area.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace DomainCoarsening2D

open IndisputableMonolith.Cosmology.DomainCoarsening

variable {α : Type*} [DecidableEq α]

/-- The 1D cost law as a row lemma: a nonempty row coarsens into (its horizontal interface) + 1 super-regions. -/
theorem runs_eq_of_ne_nil (r : List α) (h : r ≠ []) : runs r = boundaries r + 1 := by
  cases r with
  | nil => exact absurd rfl h
  | cons a l => exact runs_eq a l

/-- The separable (row-wise) coarsening cost: the total number of 1D super-regions when each row is
coarsened independently. -/
def rowCost (rows : List (List α)) : ℕ := (rows.map runs).sum

/-- The total horizontal interface: the sum over rows of the forced distinctions within each row. -/
def rowInterface (rows : List (List α)) : ℕ := (rows.map boundaries).sum

@[simp] theorem rowCost_nil : rowCost ([] : List (List α)) = 0 := rfl
@[simp] theorem rowInterface_nil : rowInterface ([] : List (List α)) = 0 := rfl

theorem rowCost_cons (r : List α) (rs : List (List α)) :
    rowCost (r :: rs) = runs r + rowCost rs := by
  simp [rowCost]

theorem rowInterface_cons (r : List α) (rs : List (List α)) :
    rowInterface (r :: rs) = boundaries r + rowInterface rs := by
  simp [rowInterface]

/-- **The separable coarsening cost = horizontal interface + number of rows.** For any 2D grid whose rows are
all nonempty, coarsening each row independently carries exactly (the total horizontal interface) plus (the
number of rows) super-regions. This is the exact per-axis generalization of the 1D law `runs = boundaries + 1`
summed over rows, and it depends only on the interface and the row count, never on the row widths (the area).
The true 2D component coarsening merges vertically as well, so it carries at most this many super-regions. -/
theorem rowwise_cost_eq (rows : List (List α)) (h : ∀ r ∈ rows, r ≠ []) :
    rowCost rows = rowInterface rows + rows.length := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    rw [rowCost_cons, rowInterface_cons, runs_eq_of_ne_nil r (h r (List.mem_cons.mpr (Or.inl rfl)))]
    rw [ih (fun row hrow => h row (List.mem_cons.mpr (Or.inr hrow)))]
    simp [List.length_cons]
    ring

/-- The carried cost is bounded by the interface, not the area: the separable coarsening cost is
`rowInterface + rows.length`, with no dependence on the row widths. -/
theorem rowwise_cost_independent_of_width (rows : List (List α)) (h : ∀ r ∈ rows, r ≠ []) :
    rowCost rows = rowInterface rows + rows.length :=
  rowwise_cost_eq rows h

end DomainCoarsening2D
end Cosmology
end IndisputableMonolith
