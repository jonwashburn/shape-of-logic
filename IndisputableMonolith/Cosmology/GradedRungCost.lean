import Mathlib
import IndisputableMonolith.Cosmology.PolarizedBirthInterfaceCost

/-!
# The graded-rung cost ledger: any unit-step phi-rung field pays J(phi) per forced distinction

Phase 55 (`PolarizedBirthInterfaceCost`) proved the recognition-cost ledger for the *binary* birth
field, whose charge is `sign(x) in {+1, 0, -1}`: carried bulk costs zero, the interface costs
`(count) * J(phi)`. But the live engine carries a *graded* phi-rung profile, not a single sign flip:
the north star is to "carry each region at the coarsest phi-rung its recognition allows," which is a
multi-valued rung field. This module proves the cost law at that level of generality.

The only property the cost law needs is the **forced minimal-distinction property**: across every
adjacency the rung changes by at most one (`UnitStep`). A unit recognition step resolves at most one
phi-rung, so `k p - k q in {0, +1, -1}` for every edge `(p, q)`. This is exactly what the lattice
plus the single-rung-step law forces (it is the `level_diff` mechanism of Phase 55), and it is the
invariant the live engine maintains because the T-3 refiner descends one rung at a time.

For **any** finite ordered edge set `E : Finset (V x V)` and **any** integer rung field `k : V -> Z`
satisfying `UnitStep k E`, this module proves, over the reals with 0 `sorry` and only the three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

* a carried (equal-rung) adjacency costs exactly `0` (`edgeCost_carried`): `J(phi^0) = J(1) = 0`;
* an interface (different-rung) adjacency costs exactly `J(phi)` (`edgeCost_interface`): the gap is
  forced to `±1` rung, so `J(phi^(±1)) = J(phi)` by reciprocal symmetry;
* `carriedCost = 0` (`carriedCost_eq_zero`), `totalCost = interfaceCost`
  (`totalCost_eq_interfaceCost`), and the closed form `totalCost = (interface edge count) * J(phi)`
  (`totalCost_eq_card`), with `J(phi) > 0` (`Jcost_phi_pos`).

So the engine pays exactly `J(phi)` per forced unit-rung distinction and carries the entire same-rung
bulk for free, for *any* rung profile, not just the binary birth field. The polarized birth field of
Phase 55 is recovered as the `k = polarized` special case (`Diamond.polarized_totalCost_card`,
`Octahedron.polarized_totalCost_card`), with `UnitStep` discharged by the Phase-55 `level_diff`
(`Diamond.polarized_unitStep`, `Octahedron.polarized_unitStep`).

THEOREM (0 `sorry`, standard three axioms only). The `UnitStep` hypothesis is the forced
minimal-distinction property, proved here for the birth field and maintained by the engine's T-3
single-rung refinement; it is not a fitted parameter.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace GradedRungCost

open Finset
open scoped BigOperators
open PolarizedBirthInterfaceCost (Jpow Jpow_zero Jpow_of_abs_one Jcost_phi_pos)

variable {V : Type*}

/-! ## §1. The per-edge cost and the forced minimal-distinction property -/

/-- The recognition cost of one ordered adjacency `(p.1, p.2)` under a phi-rung field `k`:
`J(phi^(k p.1 - k p.2))`, the forced cost `J` evaluated at the rung gap. -/
noncomputable def edgeCost (k : V → ℤ) (p : V × V) : ℝ := Jpow (k p.1 - k p.2)

/-- **The forced minimal-distinction property.** A rung field `k` posts only single-rung distinctions
across the edge set `E`: every adjacency changes the rung by at most one, `k p.1 - k p.2 in {0,+1,-1}`.
A unit recognition step resolves at most one phi-rung; the live engine maintains this because T-3
descends one rung at a time. -/
def UnitStep (k : V → ℤ) (E : Finset (V × V)) : Prop :=
  ∀ p ∈ E, k p.1 - k p.2 = 0 ∨ k p.1 - k p.2 = 1 ∨ k p.1 - k p.2 = -1

/-- A carried (equal-rung) adjacency costs exactly zero: `J(phi^0) = J(1) = 0`. -/
theorem edgeCost_carried (k : V → ℤ) {p : V × V} (h : k p.1 = k p.2) :
    edgeCost k p = 0 := by
  have hz : k p.1 - k p.2 = 0 := sub_eq_zero.mpr h
  rw [edgeCost, hz, Jpow_zero]

/-- Under the unit-step law, an interface (different-rung) adjacency costs exactly `J(phi)`: the gap
is forced to `±1` rung, and `J(phi^(±1)) = J(phi)` by reciprocal symmetry. -/
theorem edgeCost_interface (k : V → ℤ) {E : Finset (V × V)} (hk : UnitStep k E)
    {p : V × V} (hp : p ∈ E) (hne : k p.1 ≠ k p.2) :
    edgeCost k p = Cost.Jcost Constants.phi := by
  have hd : k p.1 - k p.2 = 1 ∨ k p.1 - k p.2 = -1 := by
    rcases hk p hp with h0 | h1 | hm1
    · exact absurd (sub_eq_zero.mp h0) hne
    · exact Or.inl h1
    · exact Or.inr hm1
  rw [edgeCost]
  exact Jpow_of_abs_one hd

/-! ## §2. The three ledger sums and the closed form -/

/-- The total interface recognition cost: the sum of `edgeCost` over the different-rung edges. -/
noncomputable def interfaceCost (k : V → ℤ) (E : Finset (V × V)) : ℝ :=
  ∑ p ∈ E.filter (fun p => k p.1 ≠ k p.2), edgeCost k p

/-- The total carried recognition cost: the sum of `edgeCost` over the equal-rung edges. -/
noncomputable def carriedCost (k : V → ℤ) (E : Finset (V × V)) : ℝ :=
  ∑ p ∈ E.filter (fun p => k p.1 = k p.2), edgeCost k p

/-- The total recognition cost of the field: the sum of `edgeCost` over every adjacency. -/
noncomputable def totalCost (k : V → ℤ) (E : Finset (V × V)) : ℝ :=
  ∑ p ∈ E, edgeCost k p

/-- **Carried cost is exactly zero.** The whole same-rung bulk the engine carries coarse is free. -/
theorem carriedCost_eq_zero (k : V → ℤ) (E : Finset (V × V)) :
    carriedCost k E = 0 := by
  simp only [carriedCost]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_filter] at hp
  exact edgeCost_carried k hp.2

/-- **The total cost equals the interface cost**, because the carried bulk contributes nothing. -/
theorem totalCost_eq_interfaceCost (k : V → ℤ) (E : Finset (V × V)) :
    totalCost k E = interfaceCost k E := by
  have hsplit := Finset.sum_filter_add_sum_filter_not E (fun p => k p.1 ≠ k p.2) (edgeCost k)
  have hzero : ∑ p ∈ E.filter (fun p => ¬ (k p.1 ≠ k p.2)), edgeCost k p = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter] at hp
    exact edgeCost_carried k (not_not.mp hp.2)
  rw [hzero, add_zero] at hsplit
  simp only [totalCost, interfaceCost]
  exact hsplit.symm

/-- The interface cost is the interface edge count times `J(phi)` (`UnitStep` makes every
different-rung edge cost exactly one `J(phi)`). -/
theorem interfaceCost_eq_card (k : V → ℤ) (E : Finset (V × V)) (hk : UnitStep k E) :
    interfaceCost k E = (E.filter (fun p => k p.1 ≠ k p.2)).card • Cost.Jcost Constants.phi := by
  have hpt : ∀ p ∈ E.filter (fun p => k p.1 ≠ k p.2),
      edgeCost k p = Cost.Jcost Constants.phi := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact edgeCost_interface k hk hp.1 hp.2
  simp only [interfaceCost]
  rw [Finset.sum_congr rfl hpt, Finset.sum_const]

/-- **The total recognition cost of any unit-step rung field is `(interface edge count) * J(phi)`.**
Carried bulk is free; the whole cost sits on the forced unit-rung distinctions. -/
theorem totalCost_eq_card (k : V → ℤ) (E : Finset (V × V)) (hk : UnitStep k E) :
    totalCost k E = (E.filter (fun p => k p.1 ≠ k p.2)).card • Cost.Jcost Constants.phi := by
  rw [totalCost_eq_interfaceCost, interfaceCost_eq_card k E hk]

/-- **Graded-rung cost ledger headline (Phase 56).** For any finite ordered edge set `E` and any
integer rung field `k` with the forced minimal-distinction property `UnitStep k E`: the carried
same-rung bulk costs exactly zero, the total cost equals the interface cost, the total cost is the
interface edge count times the one-rung cost `J(phi)`, and `J(phi) > 0` is a genuine positive cost.
The cost of carrying any rung profile is `J(phi)` per forced unit-rung distinction, bulk free. -/
theorem t56_graded_cost_ledger (k : V → ℤ) (E : Finset (V × V)) (hk : UnitStep k E) :
    carriedCost k E = 0
    ∧ totalCost k E = interfaceCost k E
    ∧ totalCost k E = (E.filter (fun p => k p.1 ≠ k p.2)).card • Cost.Jcost Constants.phi
    ∧ 0 < Cost.Jcost Constants.phi :=
  ⟨carriedCost_eq_zero k E, totalCost_eq_interfaceCost k E,
   totalCost_eq_card k E hk, Jcost_phi_pos⟩

/-! ## §3. The polarized birth field is the `k = sign(x)` special case (2D) -/

namespace Diamond

open InterfaceComponentBound.Diamond
open PolarizedBirthDomains.Diamond (polarized)
open LatticeBallEdges.Diamond (E)

/-- **The polarized birth field satisfies the forced minimal-distinction property.** Every adjacency
of the diamond either keeps the charge (carried, gap `0`) or flips it across the spine, and the
Phase-55 `level_diff` shows a flip is exactly `±1` rung. So `UnitStep (polarized t) (E t)`. -/
theorem polarized_unitStep (t : ℕ) : UnitStep (polarized t) (E t) := by
  intro p hp
  rw [E, Finset.mem_filter] at hp
  by_cases h : polarized t p.1 = polarized t p.2
  · exact Or.inl (sub_eq_zero.mpr h)
  · rcases PolarizedBirthInterfaceCost.Diamond.level_diff t p.1 p.2 hp.2 h with h1 | hm1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr hm1)

/-- The general graded-rung `totalCost` at `k = polarized t` is definitionally the Phase-55
`PolarizedBirthInterfaceCost.Diamond.totalCost t`. -/
theorem polarized_totalCost (t : ℕ) :
    totalCost (polarized t) (E t) = PolarizedBirthInterfaceCost.Diamond.totalCost t := rfl

/-- **The general law recovers the Phase-55 2D closed form.** Instantiating the graded-rung ledger at
the polarized birth field gives `totalCost = (8t - 4) * J(phi)` (`t >= 1`): Phase 55 is the binary
special case of the graded-rung cost law. -/
theorem polarized_totalCost_card (t : ℕ) (ht : 1 ≤ t) :
    totalCost (polarized t) (E t) = (8 * t - 4) • Cost.Jcost Constants.phi := by
  rw [polarized_totalCost, PolarizedBirthInterfaceCost.Diamond.totalCost_card t ht]

end Diamond

/-! ## §4. The polarized birth field is the `k = sign(x)` special case (3D) -/

namespace Octahedron

open InterfaceComponentBound.Octahedron
open PolarizedBirthDomains.Octahedron (polarized)
open LatticeBallEdges.Octahedron (E)

/-- **The 3D polarized birth field satisfies the forced minimal-distinction property.** Same argument
as 2D via the octahedron `level_diff`: every 6-neighbour adjacency keeps the charge or flips it by
exactly one rung. So `UnitStep (polarized t) (E t)`. -/
theorem polarized_unitStep (t : ℕ) : UnitStep (polarized t) (E t) := by
  intro p hp
  rw [E, Finset.mem_filter] at hp
  by_cases h : polarized t p.1 = polarized t p.2
  · exact Or.inl (sub_eq_zero.mpr h)
  · rcases PolarizedBirthInterfaceCost.Octahedron.level_diff t p.1 p.2 hp.2 h with h1 | hm1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr hm1)

/-- The general graded-rung `totalCost` at `k = polarized t` is definitionally the Phase-55
`PolarizedBirthInterfaceCost.Octahedron.totalCost t` (3D). -/
theorem polarized_totalCost (t : ℕ) :
    totalCost (polarized t) (E t) = PolarizedBirthInterfaceCost.Octahedron.totalCost t := rfl

/-- **The general law recovers the Phase-55 3D closed form.** Instantiating the graded-rung ledger at
the polarized octahedron field gives `totalCost = (8t^2 - 8t + 4) * J(phi)` (`t >= 1`): the dimension
`T8` forces (D=3) version of the binary special case of the graded-rung cost law. -/
theorem polarized_totalCost_card (t : ℕ) (ht : 1 ≤ t) :
    totalCost (polarized t) (E t) = (8 * t ^ 2 - 8 * t + 4) • Cost.Jcost Constants.phi := by
  rw [polarized_totalCost, PolarizedBirthInterfaceCost.Octahedron.totalCost_card t ht]

end Octahedron

end GradedRungCost
end Cosmology
end IndisputableMonolith
