import Mathlib
import IndisputableMonolith.Cosmology.LatticeBallEdges
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# The recognition COST of the coarsening ledger: carried bulk is free, the interface is paid

`LatticeBallEdges` (Phase 54) closed the edge-*count* ledger: every adjacency of the polarized birth
field is either a carried monochromatic edge or a forced bichromatic interface edge, and it counted
each side exactly (`total = interface + carried`). This module weights that ledger by the actual
recognition cost the engine posts, the forced cost `J(x) = (x + x⁻¹)/2 - 1` (`Cost.Jcost`, unique by
`Cost.FunctionalEquation`) evaluated at the phi-rung gap between two cells' charges.

The charge of the polarized field is `sign(x) ∈ {+1, 0, -1}` (`PolarizedBirthDomains.polarized`), and
the cost of one ordered adjacency is `J(φ^(charge p - charge q))`. Two facts pin it down:

* a **carried** (monochromatic) edge has equal charges, so it spans `0` phi-rungs and costs
  `J(φ^0) = J(1) = 0` exactly (`Cost.Jcost_unit0`). The bulk is carried for *literally zero*
  recognition cost.
* an **interface** (bichromatic) edge has one endpoint on the `x = 0` spine and the other at
  `x = ±1` (`edge_structure`), so the charges differ by exactly `±1`: it spans one phi-rung and costs
  `J(φ^(±1)) = J(φ)` exactly (`Cost.Jcost_symm`, reciprocal symmetry).

So the entire recognition cost of the field is the interface count times `J(φ)`:

* 2D diamond: `totalCost t = (8t - 4) • J(φ)`, `carriedCost t = 0` (`Diamond`).
* 3D octahedron: `totalCost t = (8t² - 8t + 4) • J(φ)`, `carriedCost t = 0` (`Octahedron`).

with `J(φ) = (√5 - 2)/2 > 0` (`Jcost_phi_pos`), a genuine positive cost. This is the literal,
cost-unit statement of the north star's compute-watch law: cost scales with the recognition activity
(the codimension-1 interface), not with the bulk volume the engine carries coarse for free.

THEOREM over `ℝ` and `ℕ` with 0 `sorry` and only the three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).
-/

namespace IndisputableMonolith
namespace Cosmology
namespace PolarizedBirthInterfaceCost

open Finset
open scoped BigOperators

/-! ## §0. The phi-rung cost, shared by both dimensions -/

/-- The recognition cost of an ordered adjacency whose two cells' charges differ by `d` phi-rungs:
`J(φ^d)`. The forced cost `J` is `Cost.Jcost`; `φ` is the forced golden ratio `Constants.phi`. -/
noncomputable def Jpow (d : ℤ) : ℝ := Cost.Jcost (Constants.phi ^ d)

/-- A zero-rung gap (a carried, monochromatic edge) costs nothing: `J(φ^0) = J(1) = 0`. -/
lemma Jpow_zero : Jpow 0 = 0 := by
  rw [Jpow, zpow_zero, Cost.Jcost_unit0]

/-- A one-rung-up gap costs `J(φ)`. -/
lemma Jpow_one : Jpow 1 = Cost.Jcost Constants.phi := by
  rw [Jpow, zpow_one]

/-- A one-rung-down gap costs `J(φ)` too, by reciprocal symmetry `J(φ⁻¹) = J(φ)`. -/
lemma Jpow_neg_one : Jpow (-1) = Cost.Jcost Constants.phi := by
  have h : Constants.phi ^ (-1 : ℤ) = Constants.phi⁻¹ := by
    rw [zpow_neg, zpow_one]
  rw [Jpow, h, ← Cost.Jcost_symm Constants.phi_pos]

/-- Either a single rung up or a single rung down costs exactly `J(φ)`: the recognition cost of a
forced interface distinction. -/
lemma Jpow_of_abs_one {d : ℤ} (h : d = 1 ∨ d = -1) : Jpow d = Cost.Jcost Constants.phi := by
  rcases h with h | h <;> subst h
  · exact Jpow_one
  · exact Jpow_neg_one

/-- `J(φ) > 0`: a forced interface distinction has a genuine, strictly positive recognition cost.
`J(φ) = (φ - 1)²/(2φ) = (√5 - 2)/2`. -/
lemma Jcost_phi_pos : 0 < Cost.Jcost Constants.phi := by
  rw [Cost.Jcost_eq_sq Constants.phi_ne_zero]
  apply div_pos
  · have hne : Constants.phi - 1 ≠ 0 := sub_ne_zero.mpr Constants.phi_ne_one
    positivity
  · have := Constants.phi_pos; linarith

/-! ## §1. The 2D diamond cost ledger -/

namespace Diamond

open InterfaceComponentBound.Diamond
open PolarizedBirthDomains.Diamond (polarized)
open PolarizedBirthInterface.Diamond (B interface_card_eq)
open LatticeBallEdges.Diamond (E carried)

/-- **The level gap across a bichromatic edge is exactly `±1`.** Adjacent cells of different charge
have one endpoint on the `x = 0` spine (charge `0`) and the other at `x = ±1` (charge `±1`), because
a unit step changes `x` by at most one and so cannot cross from `+1` to `-1`. Hence the charge
difference is `+1` or `-1`. -/
theorem level_diff (t : ℕ) (a b : Vtx t) (hadj : adj a.val b.val)
    (hpol : polarized t a ≠ polarized t b) :
    polarized t a - polarized t b = 1 ∨ polarized t a - polarized t b = -1 := by
  unfold adj at hadj
  simp only [polarized] at hpol ⊢
  split_ifs at hpol ⊢ <;> omega

/-- The recognition cost the engine posts across one ordered adjacency of the polarized diamond:
`J` at the phi-rung gap between the two cells' charges. -/
noncomputable def edgeCost (t : ℕ) (p : Vtx t × Vtx t) : ℝ :=
  Jpow (polarized t p.1 - polarized t p.2)

/-- A carried (monochromatic) edge costs exactly `0`: equal charges span no phi-rung. -/
theorem edgeCost_carried_zero (t : ℕ) (p : Vtx t × Vtx t) (hp : p ∈ carried t) :
    edgeCost t p = 0 := by
  rw [carried, Finset.mem_filter] at hp
  have hd : polarized t p.1 - polarized t p.2 = 0 := sub_eq_zero.mpr hp.2
  rw [edgeCost, hd, Jpow_zero]

/-- A forced interface (bichromatic) edge costs exactly `J(φ)`: its charges differ by one phi-rung. -/
theorem edgeCost_interface (t : ℕ) (p : Vtx t × Vtx t) (hp : p ∈ B t) :
    edgeCost t p = Cost.Jcost Constants.phi := by
  simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨hadj, hpol⟩ := hp
  simp only [edgeCost]
  exact Jpow_of_abs_one (level_diff t p.1 p.2 hadj hpol)

/-- The total interface recognition cost: the sum of `edgeCost` over the bichromatic edges. -/
noncomputable def interfaceCost (t : ℕ) : ℝ := ∑ p ∈ B t, edgeCost t p

/-- The total carried recognition cost: the sum of `edgeCost` over the monochromatic edges. -/
noncomputable def carriedCost (t : ℕ) : ℝ := ∑ p ∈ carried t, edgeCost t p

/-- The total recognition cost of the field: the sum of `edgeCost` over every adjacency. -/
noncomputable def totalCost (t : ℕ) : ℝ := ∑ p ∈ E t, edgeCost t p

/-- **Carried cost is exactly zero.** The whole bulk the engine carries coarse costs no recognition. -/
theorem carriedCost_eq_zero (t : ℕ) : carriedCost t = 0 := by
  simp only [carriedCost]
  apply Finset.sum_eq_zero
  intro p hp
  exact edgeCost_carried_zero t p hp

/-- The interface cost is the interface edge count times `J(φ)`. -/
theorem interfaceCost_eq_card (t : ℕ) :
    interfaceCost t = (B t).card • Cost.Jcost Constants.phi := by
  simp only [interfaceCost]
  rw [Finset.sum_congr rfl (fun p hp => edgeCost_interface t p hp), Finset.sum_const]

/-- **The total cost equals the interface cost**, because the carried bulk contributes nothing. -/
theorem totalCost_eq_interfaceCost (t : ℕ) : totalCost t = interfaceCost t := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (E t)
    (fun p => polarized t p.1 ≠ polarized t p.2) (edgeCost t)
  have hBeq : (E t).filter (fun p => polarized t p.1 ≠ polarized t p.2) = B t := by
    rw [E, B, Finset.filter_filter]
  have hMeq : (E t).filter (fun p => ¬ (polarized t p.1 ≠ polarized t p.2)) = carried t := by
    rw [carried]
    apply Finset.filter_congr
    intro p _
    simp
  rw [hBeq, hMeq] at hsplit
  have hzero : ∑ p ∈ carried t, edgeCost t p = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    exact edgeCost_carried_zero t p hp
  rw [hzero, add_zero] at hsplit
  simp only [totalCost, interfaceCost]
  exact hsplit.symm

/-- **The exact interface recognition cost is `(8t - 4) • J(φ)`** (`t ≥ 1`). -/
theorem interfaceCost_card (t : ℕ) (ht : 1 ≤ t) :
    interfaceCost t = (8 * t - 4) • Cost.Jcost Constants.phi := by
  rw [interfaceCost_eq_card, interface_card_eq t ht]

/-- **The total recognition cost of the polarized diamond field is `(8t - 4) • J(φ)`** (`t ≥ 1`):
the carried bulk is free, and the whole cost sits on the `8t - 4` interface edges. -/
theorem totalCost_card (t : ℕ) (ht : 1 ≤ t) :
    totalCost t = (8 * t - 4) • Cost.Jcost Constants.phi := by
  rw [totalCost_eq_interfaceCost, interfaceCost_card t ht]

/-- The total cost in real-multiplication form, `(8t - 4) * J(φ)` (`t ≥ 1`). -/
theorem totalCost_mul (t : ℕ) (ht : 1 ≤ t) :
    totalCost t = ((8 * t - 4 : ℕ) : ℝ) * Cost.Jcost Constants.phi := by
  rw [totalCost_card t ht, nsmul_eq_mul]

/-- **The run-total recognition cost over a full forward run** from radius `1` to `T` is exactly
`8(T - 1) • J(φ)`. The cost the engine posts to grow the whole world is `Θ(T)`, strictly
sub-extensive against the brute-force volume-times-ticks `Θ(T³)`: the compute-watch law in cost
units, integrated over the run. -/
theorem runCost_growth (T : ℕ) (hT : 1 ≤ T) :
    totalCost T - totalCost 1 = ((8 * T - 8 : ℕ) : ℝ) * Cost.Jcost Constants.phi := by
  rw [totalCost_mul T hT, totalCost_mul 1 le_rfl]
  have h4 : 4 ≤ 8 * T := by omega
  have h8 : 8 ≤ 8 * T := by omega
  have e1 : ((8 * T - 4 : ℕ) : ℝ) = 8 * (T : ℝ) - 4 := by
    rw [Nat.cast_sub h4]; push_cast; ring
  have e2 : ((8 * 1 - 4 : ℕ) : ℝ) = 4 := by norm_num
  have e3 : ((8 * T - 8 : ℕ) : ℝ) = 8 * (T : ℝ) - 8 := by
    rw [Nat.cast_sub h8]; push_cast; ring
  rw [e1, e2, e3]; ring

/-- **The per-cycle recognition cost increment** of advancing the diamond by one cadence cycle
(`t → t+1`) is the constant `8 • J(φ)` (`t ≥ 1`): the differential form of the compute-watch law.
In 2D the recognition-active interface is a `1`-dimensional curve whose length gains a constant `8`
ordered edges per shell, so the cost the engine posts each cycle is constant, `O(1)`, independent of
how large the world already is. -/
theorem costIncrement (t : ℕ) (ht : 1 ≤ t) :
    totalCost (t + 1) - totalCost t = 8 * Cost.Jcost Constants.phi := by
  rw [totalCost_mul (t + 1) (by omega), totalCost_mul t ht]
  have e1 : ((8 * (t + 1) - 4 : ℕ) : ℝ) = 8 * (t : ℝ) + 4 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : ((8 * t - 4 : ℕ) : ℝ) = 8 * (t : ℝ) - 4 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e1, e2]; ring

/-- **2D headline (Phase 55).** For a polarized diamond of radius `t ≥ 1`: the carried bulk costs
exactly zero recognition, the total cost is `(8t - 4) • J(φ)` (the interface count times the
one-rung cost), and `J(φ) > 0` is a genuine positive cost. "Carry the bulk free, pay only for the
interface," in exact cost units. -/
theorem t55_cost_ledger (t : ℕ) (ht : 1 ≤ t) :
    carriedCost t = 0
    ∧ totalCost t = (8 * t - 4) • Cost.Jcost Constants.phi
    ∧ totalCost t = interfaceCost t
    ∧ 0 < Cost.Jcost Constants.phi :=
  ⟨carriedCost_eq_zero t, totalCost_card t ht, totalCost_eq_interfaceCost t, Jcost_phi_pos⟩

end Diamond

/-! ## §2. The 3D octahedron cost ledger -/

namespace Octahedron

open InterfaceComponentBound.Octahedron
open PolarizedBirthDomains.Octahedron (polarized)
open PolarizedBirthInterface.Octahedron (B interface_card_eq)
open LatticeBallEdges.Octahedron (E carried)

/-- **The level gap across a bichromatic edge is exactly `±1`** (3D). Same argument as 2D: a unit
6-neighbour step changes `x` by at most one, so the only way two adjacent cells differ in charge is
one on the spine `x = 0` and one at `x = ±1`. -/
theorem level_diff (t : ℕ) (a b : Vtx t) (hadj : adj a.val b.val)
    (hpol : polarized t a ≠ polarized t b) :
    polarized t a - polarized t b = 1 ∨ polarized t a - polarized t b = -1 := by
  unfold adj at hadj
  simp only [polarized] at hpol ⊢
  split_ifs at hpol ⊢ <;> omega

/-- The recognition cost of one ordered adjacency of the polarized octahedron. -/
noncomputable def edgeCost (t : ℕ) (p : Vtx t × Vtx t) : ℝ :=
  Jpow (polarized t p.1 - polarized t p.2)

/-- A carried (monochromatic) octahedron edge costs exactly `0`. -/
theorem edgeCost_carried_zero (t : ℕ) (p : Vtx t × Vtx t) (hp : p ∈ carried t) :
    edgeCost t p = 0 := by
  rw [carried, Finset.mem_filter] at hp
  have hd : polarized t p.1 - polarized t p.2 = 0 := sub_eq_zero.mpr hp.2
  rw [edgeCost, hd, Jpow_zero]

/-- A forced interface (bichromatic) octahedron edge costs exactly `J(φ)`. -/
theorem edgeCost_interface (t : ℕ) (p : Vtx t × Vtx t) (hp : p ∈ B t) :
    edgeCost t p = Cost.Jcost Constants.phi := by
  simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨hadj, hpol⟩ := hp
  simp only [edgeCost]
  exact Jpow_of_abs_one (level_diff t p.1 p.2 hadj hpol)

/-- The total interface recognition cost (3D). -/
noncomputable def interfaceCost (t : ℕ) : ℝ := ∑ p ∈ B t, edgeCost t p

/-- The total carried recognition cost (3D). -/
noncomputable def carriedCost (t : ℕ) : ℝ := ∑ p ∈ carried t, edgeCost t p

/-- The total recognition cost of the octahedron field (3D). -/
noncomputable def totalCost (t : ℕ) : ℝ := ∑ p ∈ E t, edgeCost t p

/-- **Carried cost is exactly zero** (3D). -/
theorem carriedCost_eq_zero (t : ℕ) : carriedCost t = 0 := by
  simp only [carriedCost]
  apply Finset.sum_eq_zero
  intro p hp
  exact edgeCost_carried_zero t p hp

/-- The interface cost is the interface edge count times `J(φ)` (3D). -/
theorem interfaceCost_eq_card (t : ℕ) :
    interfaceCost t = (B t).card • Cost.Jcost Constants.phi := by
  simp only [interfaceCost]
  rw [Finset.sum_congr rfl (fun p hp => edgeCost_interface t p hp), Finset.sum_const]

/-- **The total cost equals the interface cost** (3D). -/
theorem totalCost_eq_interfaceCost (t : ℕ) : totalCost t = interfaceCost t := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (E t)
    (fun p => polarized t p.1 ≠ polarized t p.2) (edgeCost t)
  have hBeq : (E t).filter (fun p => polarized t p.1 ≠ polarized t p.2) = B t := by
    rw [E, B, Finset.filter_filter]
  have hMeq : (E t).filter (fun p => ¬ (polarized t p.1 ≠ polarized t p.2)) = carried t := by
    rw [carried]
    apply Finset.filter_congr
    intro p _
    simp
  rw [hBeq, hMeq] at hsplit
  have hzero : ∑ p ∈ carried t, edgeCost t p = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    exact edgeCost_carried_zero t p hp
  rw [hzero, add_zero] at hsplit
  simp only [totalCost, interfaceCost]
  exact hsplit.symm

/-- **The exact interface recognition cost is `(8t² - 8t + 4) • J(φ)`** (`t ≥ 1`). -/
theorem interfaceCost_card (t : ℕ) (ht : 1 ≤ t) :
    interfaceCost t = (8 * t ^ 2 - 8 * t + 4) • Cost.Jcost Constants.phi := by
  rw [interfaceCost_eq_card, interface_card_eq t ht]

/-- **The total recognition cost of the polarized octahedron field is `(8t² - 8t + 4) • J(φ)`**
(`t ≥ 1`): the 3D bulk is carried free, the cost sits on the `8t² - 8t + 4` interface edges. -/
theorem totalCost_card (t : ℕ) (ht : 1 ≤ t) :
    totalCost t = (8 * t ^ 2 - 8 * t + 4) • Cost.Jcost Constants.phi := by
  rw [totalCost_eq_interfaceCost, interfaceCost_card t ht]

/-- The total cost in real-multiplication form, `(8t² - 8t + 4) * J(φ)` (`t ≥ 1`). -/
theorem totalCost_mul (t : ℕ) (ht : 1 ≤ t) :
    totalCost t = ((8 * t ^ 2 - 8 * t + 4 : ℕ) : ℝ) * Cost.Jcost Constants.phi := by
  rw [totalCost_card t ht, nsmul_eq_mul]

/-- **The run-total recognition cost over a full forward run** from radius `1` to `T` is exactly
`8T(T - 1) • J(φ)`. In the dimension `T8` forces (D=3) the cost the engine posts to grow the whole
world is `Θ(T²)`, strictly sub-extensive against the brute-force `Θ(T⁴)`: the compute-watch law in
cost units, integrated over the run. -/
theorem runCost_growth (T : ℕ) (hT : 1 ≤ T) :
    totalCost T - totalCost 1 = ((8 * T ^ 2 - 8 * T : ℕ) : ℝ) * Cost.Jcost Constants.phi := by
  rw [totalCost_mul T hT, totalCost_mul 1 le_rfl]
  have hTT : 8 * T ≤ 8 * T ^ 2 := by nlinarith [hT]
  have e1 : ((8 * T ^ 2 - 8 * T + 4 : ℕ) : ℝ) = 8 * (T : ℝ) ^ 2 - 8 * (T : ℝ) + 4 := by
    rw [Nat.cast_add, Nat.cast_sub hTT]; push_cast; ring
  have e2 : ((8 * 1 ^ 2 - 8 * 1 + 4 : ℕ) : ℝ) = 4 := by norm_num
  have e3 : ((8 * T ^ 2 - 8 * T : ℕ) : ℝ) = 8 * (T : ℝ) ^ 2 - 8 * (T : ℝ) := by
    rw [Nat.cast_sub hTT]; push_cast; ring
  rw [e1, e2, e3]; ring

/-- **The per-cycle recognition cost increment** of advancing the octahedron by one cadence cycle
(`t → t+1`) is `16t • J(φ)` (`t ≥ 1`): the differential form of the compute-watch law in the
dimension `T8` forces (D=3). The recognition-active interface is now a `2`-dimensional surface whose
area gains `16t` ordered edges per shell, so the cost the engine posts each cycle grows `Θ(t)`, the
honest 3D statement (not the constant `O(1)` of 2D), still strictly sub-extensive in the `Θ(t³)`
bulk. -/
theorem costIncrement (t : ℕ) (ht : 1 ≤ t) :
    totalCost (t + 1) - totalCost t = (16 * t : ℝ) * Cost.Jcost Constants.phi := by
  rw [totalCost_mul (t + 1) (by omega), totalCost_mul t ht]
  have hle1 : 8 * (t + 1) ≤ 8 * (t + 1) ^ 2 := by nlinarith [Nat.le_add_left 1 t]
  have hle2 : 8 * t ≤ 8 * t ^ 2 := by nlinarith [ht]
  have e1 : ((8 * (t + 1) ^ 2 - 8 * (t + 1) + 4 : ℕ) : ℝ)
      = 8 * (t : ℝ) ^ 2 + 8 * (t : ℝ) + 4 := by
    rw [Nat.cast_add, Nat.cast_sub hle1]; push_cast; ring
  have e2 : ((8 * t ^ 2 - 8 * t + 4 : ℕ) : ℝ) = 8 * (t : ℝ) ^ 2 - 8 * (t : ℝ) + 4 := by
    rw [Nat.cast_add, Nat.cast_sub hle2]; push_cast; ring
  rw [e1, e2]; ring

/-- **3D headline (Phase 55).** For a polarized octahedron of radius `t ≥ 1`: the carried bulk costs
exactly zero recognition, the total cost is `(8t² - 8t + 4) • J(φ)` (the interface count times the
one-rung cost), and `J(φ) > 0`. The dimension `T8` forces (D=3) version of "carry the bulk free, pay
only for the interface." -/
theorem t55_cost_ledger (t : ℕ) (ht : 1 ≤ t) :
    carriedCost t = 0
    ∧ totalCost t = (8 * t ^ 2 - 8 * t + 4) • Cost.Jcost Constants.phi
    ∧ totalCost t = interfaceCost t
    ∧ 0 < Cost.Jcost Constants.phi :=
  ⟨carriedCost_eq_zero t, totalCost_card t ht, totalCost_eq_interfaceCost t, Jcost_phi_pos⟩

end Octahedron

end PolarizedBirthInterfaceCost
end Cosmology
end IndisputableMonolith
