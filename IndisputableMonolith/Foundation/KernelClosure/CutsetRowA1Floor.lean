import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.ClockFromCompletion

/-!
# Cutset A1: completion is one item of the floor above, and the floor above halves

## The sentence

Row 6 closed "one post per tick" by losslessness (`CutsetRow6Lossless`) and kept
one clause as a definition: a completed recognition is one the floor above reads
as one item (`PassOccupiesItem`), where "item" is the address `x ↦ x / 2` per
cell (`OctaveFloorStep.addressD`). Nothing said why the factor is two.

## The blade

T1: a distinction is a two-state cell. The floor above is a ledger of the same
kind: `d` cells, each two-sided, each reading one cell below by a coarsening of
that cell's coordinate (one rule at every floor, row 4a). A per-cell coarsening
with factors `m : Fin d → ℕ` has, over each item, a fiber whose cell `i` carries
`m i` states (`fiberEquiv`). Then

* cellwise: every cell of the floor above is two-sided iff every `m i = 2`
  (`cell_twoSided_iff`);
* by count: if every cell is read (`2 ≤ m i`) and the item's fiber is one floor
  of states (a pattern space), then every `m i = 2` (`fiber_pattern_iff`);

and at `m = 2` the coarsening is `addressD` (`coarseAddress_two`). So "occupies
an item" has no free factor: the halving is what a same-kind floor above means.

## Decoys

* `m = 1` (no floor above; the bounce and the face live here): the fiber is a
  point, not a pattern space (`one_not_pattern`).
* `m = 3` (three-sided cells): `3^d ≠ 2^d` (`three_not_pattern`).
* mixed `(4, 2, 1)` at `d = 3`: passes the count (`mixed_count_passes`, eight
  states) and fails cellwise (`mixed_cellwise_fails`): cell `0` has four states
  and cell `2` has one. The count gate needs "every cell is read"; the cellwise
  gate does not.

## The gate reaches the code

Coverage is re-derived through the general coarsening: occupying an item of any
per-cell floor above is surjection onto that floor's residues
(`occupiesCoarseItem_iff_surjective`), and `PassOccupiesItem` is the `m = 2`
case (`passOccupiesItem_iff_occupiesCoarseItem`), so
`passOccupiesItem_iff_surjective` is recovered (`coverage_reached`).

## What remains

That there is a floor above at all: the existence half of row 4's realized
hierarchy (`boolFramework` has none). Under existence and T1 on the floor above,
completion is occupying an item and the item is the halving.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace RowA1Floor

open Patterns OctaveFloorStep ClockFromCompletion

variable {d : ℕ}

/-! ## A per-cell coarsening -/

/-- Cell `i` of the floor above reads cell `i` below with factor `m i`. -/
def coarseAddress (m : Fin d → ℕ) (x : Fin d → ℤ) : Fin d → ℤ :=
  fun i => x i / (m i : ℤ)

/-- The states of one item's cells: cell `i` has `m i` of them. -/
abbrev Residue (m : Fin d → ℕ) : Type := (i : Fin d) → Fin (m i)

/-- The residue of a position: what the item's cells read of it. -/
def coarseResidue (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) (x : Fin d → ℤ) : Residue m :=
  fun i => ⟨(x i % (m i : ℤ)).toNat, by
    have h0 : (0 : ℤ) < m i := by exact_mod_cast hm i
    have hlt := Int.emod_lt_of_pos (x i) h0
    have hnn := Int.emod_nonneg (x i) h0.ne'
    have hcast := Int.toNat_of_nonneg hnn
    rw [← hcast] at hlt
    exact_mod_cast hlt⟩

/-- Assemble a position from a residue and an address. -/
def assembleM (m : Fin d → ℕ) (r : Residue m) (a : Fin d → ℤ) : Fin d → ℤ :=
  fun i => (m i : ℤ) * a i + ((r i).val : ℤ)

theorem coarseAddress_assembleM (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) (r : Residue m)
    (a : Fin d → ℤ) : coarseAddress m (assembleM m r a) = a := by
  funext i
  show ((m i : ℤ) * a i + ((r i).val : ℤ)) / (m i : ℤ) = a i
  have h0 : (0 : ℤ) < m i := by exact_mod_cast hm i
  have hr : ((r i).val : ℤ) < m i := by exact_mod_cast (r i).isLt
  rw [add_comm, Int.add_mul_ediv_left _ _ h0.ne',
    Int.ediv_eq_zero_of_lt (by positivity) hr, zero_add]

theorem coarseResidue_assembleM (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) (r : Residue m)
    (a : Fin d → ℤ) : coarseResidue m hm (assembleM m r a) = r := by
  funext i
  apply Fin.ext
  show (((m i : ℤ) * a i + ((r i).val : ℤ)) % (m i : ℤ)).toNat = (r i).val
  have h0 : (0 : ℤ) < m i := by exact_mod_cast hm i
  have hr : ((r i).val : ℤ) < m i := by exact_mod_cast (r i).isLt
  rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) hr]
  exact Int.toNat_natCast _

theorem assembleM_residue_address (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) (x : Fin d → ℤ) :
    assembleM m (coarseResidue m hm x) (coarseAddress m x) = x := by
  funext i
  show (m i : ℤ) * (x i / (m i : ℤ)) + (((x i % (m i : ℤ)).toNat : ℕ) : ℤ) = x i
  have h0 : (0 : ℤ) < m i := by exact_mod_cast hm i
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ h0.ne')]
  exact Int.ediv_add_emod _ _

/-- **The fiber over an item is the item's cells.** -/
def fiberEquiv (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) (a : Fin d → ℤ) :
    {x : Fin d → ℤ // coarseAddress m x = a} ≃ Residue m where
  toFun x := coarseResidue m hm x.1
  invFun r := ⟨assembleM m r a, coarseAddress_assembleM m hm r a⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    apply Subtype.ext
    show assembleM m (coarseResidue m hm x) a = x
    subst hx
    exact assembleM_residue_address m hm x
  right_inv r := coarseResidue_assembleM m hm r a

theorem card_residue (m : Fin d → ℕ) : Fintype.card (Residue m) = ∏ i, m i := by
  simp [Residue, Fintype.card_pi, Fintype.card_fin]

/-! ## The blade, cellwise: a two-sided cell has factor two -/

/-- **T1 on the floor above.** A cell with `n` states is two-sided iff `n = 2`. -/
theorem cell_twoSided_iff (n : ℕ) : Nonempty (Fin n ≃ Bool) ↔ n = 2 := by
  constructor
  · rintro ⟨e⟩
    have h := Fintype.card_congr e
    simpa [Fintype.card_fin, Fintype.card_bool] using h
  · rintro rfl
    exact ⟨finTwoEquiv⟩

/-- Every cell of the floor above two-sided iff every factor is two. -/
theorem cellwise_iff (m : Fin d → ℕ) :
    (∀ i, Nonempty (Fin (m i) ≃ Bool)) ↔ ∀ i, m i = 2 :=
  forall_congr' fun i => cell_twoSided_iff (m i)

/-! ## The blade, by count: one floor of states over every item -/

theorem two_pow_le_prod (m : Fin d → ℕ) (hm : ∀ i, 2 ≤ m i) : 2 ^ d ≤ ∏ i, m i := by
  have h := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin d => (2 : ℕ)) (g := m)
    (fun _ _ => by norm_num) (fun i _ => hm i)
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

/-- If every cell is read and the fiber has exactly one floor of states, every
factor is two. -/
theorem prod_eq_two_pow (m : Fin d → ℕ) (hm : ∀ i, 2 ≤ m i) (hp : ∏ i, m i = 2 ^ d) :
    ∀ i, m i = 2 := by
  intro j
  by_contra hne
  have hj : 3 ≤ m j := by have := hm j; omega
  have hsplit := Finset.mul_prod_erase Finset.univ m (Finset.mem_univ j)
  have hrest : 2 ^ (d - 1) ≤ ∏ i ∈ Finset.univ.erase j, m i := by
    have h := Finset.prod_le_prod (s := Finset.univ.erase j) (f := fun _ : Fin d => (2 : ℕ))
      (g := m) (fun _ _ => by norm_num) (fun i _ => hm i)
    have hc : (Finset.univ.erase j).card = d - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    simpa [Finset.prod_const, hc] using h
  have hd : 1 ≤ d := Fin.pos j
  have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hP : 0 < 2 ^ (d - 1) := by positivity
  have : 3 * 2 ^ (d - 1) ≤ m j * ∏ i ∈ Finset.univ.erase j, m i :=
    Nat.mul_le_mul hj hrest
  rw [hsplit, hp, hpow] at this
  omega

/-- **The count blade.** With every cell read, the fiber is a pattern space iff
every factor is two. -/
theorem fiber_pattern_iff (m : Fin d → ℕ) (hm : ∀ i, 2 ≤ m i) (a : Fin d → ℤ) :
    Nonempty ({x : Fin d → ℤ // coarseAddress m x = a} ≃ Pattern d) ↔ ∀ i, m i = 2 := by
  have hm0 : ∀ i, 0 < m i := fun i => by have := hm i; omega
  constructor
  · rintro ⟨e⟩
    have e' : Residue m ≃ Pattern d := (fiberEquiv m hm0 a).symm.trans e
    have h := Fintype.card_congr e'
    rw [card_residue, card_pattern] at h
    exact prod_eq_two_pow m hm h
  · intro h2
    refine ⟨(fiberEquiv m hm0 a).trans ?_⟩
    refine Equiv.piCongrRight fun i => ?_
    rw [h2 i]
    exact finTwoEquiv

/-! ## Decoys -/

/-- `m = 1`: no floor above. The fiber is a point. -/
theorem one_not_pattern (d : ℕ) (hd : 1 ≤ d) :
    ¬ Nonempty (Residue (fun _ : Fin d => 1) ≃ Pattern d) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  rw [card_residue, card_pattern] at h
  simp only [Finset.prod_const_one] at h
  have : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  omega

/-- `m = 3`: three-sided cells. `3^d ≠ 2^d`. -/
theorem three_not_pattern (d : ℕ) (hd : 1 ≤ d) :
    ¬ Nonempty (Residue (fun _ : Fin d => 3) ≃ Pattern d) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  rw [card_residue, card_pattern] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have : 2 ^ d < 3 ^ d := Nat.pow_lt_pow_left (by norm_num) (by omega)
  omega

/-- The mixed floor `(4, 2, 1)`: cell `0` read with factor four, cell `1`
halved, cell `2` not read. -/
def mixed : Fin 3 → ℕ := ![4, 2, 1]

theorem card_mixed : Fintype.card (Residue mixed) = 8 := by
  rw [card_residue]
  simp [mixed, Fin.prod_univ_three]

/-- The mixed floor passes the count: eight states over every item. -/
theorem mixed_count_passes : Nonempty (Residue mixed ≃ Pattern 3) :=
  ⟨Fintype.equivOfCardEq (by rw [card_mixed, card_pattern]; norm_num)⟩

/-- The mixed floor fails cellwise: its cell `0` is not two-sided. -/
theorem mixed_cellwise_fails : ¬ ∀ i, Nonempty (Fin (mixed i) ≃ Bool) := by
  intro h
  have h0 := (cell_twoSided_iff _).1 (h 0)
  simp [mixed] at h0

/-- The mixed floor does not read every cell. -/
theorem mixed_not_all_read : ¬ ∀ i, 2 ≤ mixed i := by
  intro h
  have h2 := h 2
  simp [mixed] at h2

/-! ## At factor two the coarsening is the address -/

theorem coarseAddress_two : coarseAddress (fun _ : Fin d => 2) = addressD := by
  funext x i
  show x i / ((2 : ℕ) : ℤ) = x i / 2
  norm_num

theorem coarseResidue_two (x : Fin d → ℤ) (i : Fin d) :
    coarseResidue (fun _ : Fin d => 2) (fun _ => by norm_num) x i =
      finTwoEquiv.symm (parityD x i) := by
  apply Fin.ext
  show (x i % ((2 : ℕ) : ℤ)).toNat = (finTwoEquiv.symm (decide (x i % 2 = 1))).val
  rcases Int.emod_two_eq (x i) with h | h
  · have hd : ¬ (x i % 2 = 1) := by omega
    rw [decide_eq_false hd]
    simp [h, finTwoEquiv]
  · rw [decide_eq_true h]
    simp [h, finTwoEquiv]

/-! ## Coverage through the general coarsening -/

/-- A pass on the floor above's residues occupies item `a`: every position with
that address has its residue reached. -/
def OccupiesCoarseItem (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) {T : ℕ}
    (pass : Fin T → Residue m) (a : Fin d → ℤ) : Prop :=
  ∀ x : Fin d → ℤ, coarseAddress m x = a → ∃ t : Fin T, pass t = coarseResidue m hm x

/-- **Coverage is derived for every per-cell floor above.** -/
theorem occupiesCoarseItem_iff_surjective (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) {T : ℕ}
    (pass : Fin T → Residue m) (a : Fin d → ℤ) :
    OccupiesCoarseItem m hm pass a ↔ Function.Surjective pass := by
  constructor
  · intro h r
    obtain ⟨t, ht⟩ := h (assembleM m r a) (coarseAddress_assembleM m hm r a)
    exact ⟨t, by rw [ht, coarseResidue_assembleM]⟩
  · intro h x _
    exact h _

/-- `PassOccupiesItem` is the `m = 2` case. -/
theorem passOccupiesItem_iff_occupiesCoarseItem {T : ℕ} (pass : Fin T → Pattern d)
    (a : Fin d → ℤ) :
    PassOccupiesItem pass a ↔
      OccupiesCoarseItem (fun _ : Fin d => 2) (fun _ => by norm_num)
        (fun t i => finTwoEquiv.symm (pass t i)) a := by
  unfold PassOccupiesItem OccupiesCoarseItem
  rw [coarseAddress_two]
  refine forall_congr' fun x => imp_congr_right fun _ => exists_congr fun t => ?_
  constructor
  · intro h
    funext i
    rw [coarseResidue_two]
    show finTwoEquiv.symm (pass t i) = finTwoEquiv.symm (parityD x i)
    rw [h]
  · intro h
    funext i
    have hi := congrFun h i
    rw [coarseResidue_two] at hi
    exact finTwoEquiv.symm.injective hi

/-- **The gate reaches the code.** Coverage for `PassOccupiesItem`, through the
general coarsening. -/
theorem coverage_reached {T : ℕ} (pass : Fin T → Pattern d) (a : Fin d → ℤ) :
    PassOccupiesItem pass a ↔ Function.Surjective pass := by
  rw [passOccupiesItem_iff_occupiesCoarseItem, occupiesCoarseItem_iff_surjective]
  constructor
  · intro h p
    obtain ⟨t, ht⟩ := h (fun i => finTwoEquiv.symm (p i))
    refine ⟨t, funext fun i => finTwoEquiv.symm.injective (congrFun ht i)⟩
  · intro h r
    obtain ⟨t, ht⟩ := h (fun i => finTwoEquiv (r i))
    refine ⟨t, funext fun i => ?_⟩
    show finTwoEquiv.symm (pass t i) = r i
    rw [ht]
    exact finTwoEquiv.symm_apply_apply _

/-! ## Certificate -/

structure Cert : Prop where
  /-- T1 on the floor above: a two-sided cell has factor two. -/
  cell_twoSided : ∀ n : ℕ, Nonempty (Fin n ≃ Bool) ↔ n = 2
  /-- Every cell two-sided iff every factor two. -/
  cellwise : ∀ {d : ℕ} (m : Fin d → ℕ), (∀ i, Nonempty (Fin (m i) ≃ Bool)) ↔ ∀ i, m i = 2
  /-- Count: every cell read and one floor of states over an item forces factor two. -/
  fiber_pattern : ∀ {d : ℕ} (m : Fin d → ℕ), (∀ i, 2 ≤ m i) → ∀ a : Fin d → ℤ,
    Nonempty ({x : Fin d → ℤ // coarseAddress m x = a} ≃ Pattern d) ↔ ∀ i, m i = 2
  /-- `m = 1` rejected. -/
  one_rejected : ∀ d : ℕ, 1 ≤ d → ¬ Nonempty (Residue (fun _ : Fin d => 1) ≃ Pattern d)
  /-- `m = 3` rejected. -/
  three_rejected : ∀ d : ℕ, 1 ≤ d → ¬ Nonempty (Residue (fun _ : Fin d => 3) ≃ Pattern d)
  /-- Mixed passes the count and fails cellwise and "every cell read". -/
  mixed : Nonempty (Residue RowA1Floor.mixed ≃ Pattern 3) ∧
    ¬ (∀ i, Nonempty (Fin (RowA1Floor.mixed i) ≃ Bool)) ∧ ¬ (∀ i, 2 ≤ RowA1Floor.mixed i)
  /-- At factor two the coarsening is the address. -/
  halving_is_address : ∀ d : ℕ, coarseAddress (fun _ : Fin d => 2) = addressD
  /-- Coverage for every per-cell floor above. -/
  coverage_general : ∀ {d : ℕ} (m : Fin d → ℕ) (hm : ∀ i, 0 < m i) {T : ℕ}
    (pass : Fin T → Residue m) (a : Fin d → ℤ),
    OccupiesCoarseItem m hm pass a ↔ Function.Surjective pass
  /-- Coverage for `PassOccupiesItem`, reached through the general case. -/
  coverage_reached : ∀ {d T : ℕ} (pass : Fin T → Pattern d) (a : Fin d → ℤ),
    PassOccupiesItem pass a ↔ Function.Surjective pass

theorem cert : Cert where
  cell_twoSided := cell_twoSided_iff
  cellwise := cellwise_iff
  fiber_pattern := fiber_pattern_iff
  one_rejected := one_not_pattern
  three_rejected := three_not_pattern
  mixed := ⟨mixed_count_passes, mixed_cellwise_fails, mixed_not_all_read⟩
  halving_is_address := fun _ => coarseAddress_two
  coverage_general := occupiesCoarseItem_iff_surjective
  coverage_reached := coverage_reached

end RowA1Floor
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
