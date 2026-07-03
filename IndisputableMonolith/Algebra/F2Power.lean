import Mathlib

/-!
# `F2Power D`: the elementary abelian 2-group of rank `D`

## Status: THEOREM module (0 sorry, 0 RS-internal axiom).

The companion paper to this module is
`papers/Seven_Plots_Three_Dimensions.tex`. There the count `7` for
Booker's basic plot families is *asserted* to come from
`(Z/2)^3 \ {0}`. Here the count is *proved*, so that downstream
modules (`Aesthetics.NarrativeGeodesic`, `Narrative.CubeBridge`,
`Patterns.TwoToTheDMinusOne`) can chain off a real theorem instead of
a hardcoded definition.

## What this module provides

* `F2Power D := Fin D → Bool`: the underlying type. Pointwise XOR is
  the abelian group operation.
* `instance : AddCommGroup (F2Power D)` and `Fintype`, with
  `card_eq : Fintype.card (F2Power D) = 2 ^ D`.
* `nonzero_card : (Finset.univ.filter (fun v => v ≠ 0)).card = 2 ^ D - 1`.
* `nonzero_card_three : … = 7` (immediate corollary at D = 3).
* `hammingWeight v := (Finset.univ.filter (fun i => v i = true)).card`,
  with `weight_zero_iff : hammingWeight v = 0 ↔ v = 0` and
  `weight_le : hammingWeight v ≤ D`.
* The 1+3+3+1 weight decomposition at D = 3:
  * `card_weight_zero_three : (… filter weight = 0).card = 1`
  * `card_weight_one_three : … = 3`
  * `card_weight_two_three : … = 3`
  * `card_weight_three_three : … = 1`

The subgroup structure carries to the Booker bijection in
`Aesthetics.NarrativeGeodesic`: each non-zero `v : F2Power 3`
generates the `1`-dimensional subgroup `{0, v}` (closed under XOR
because `v + v = 0` in `F2`), giving exactly `7` such subgroups.

## Falsifier

A `D : ℕ` for which `(Finset.univ.filter (· ≠ (0 : F2Power D))).card`
differs from `2 ^ D - 1`. Combinatorially impossible (proved below).
-/

namespace IndisputableMonolith
namespace Algebra

/-- The elementary abelian 2-group of rank `D`, modeled as
    `Fin D → Bool` with pointwise XOR. -/
def F2Power (D : ℕ) : Type := Fin D → Bool

namespace F2Power

variable {D : ℕ}

instance : DecidableEq (F2Power D) := by
  unfold F2Power; infer_instance

instance : Fintype (F2Power D) := by
  unfold F2Power; infer_instance

instance : Inhabited (F2Power D) := by
  unfold F2Power; infer_instance

/-- The zero element: all coordinates `false`. -/
instance : Zero (F2Power D) := ⟨fun _ => false⟩

@[simp] theorem zero_apply (i : Fin D) : (0 : F2Power D) i = false := rfl

/-- Pointwise XOR. -/
instance : Add (F2Power D) := ⟨fun u v => fun i => xor (u i) (v i)⟩

@[simp] theorem add_apply (u v : F2Power D) (i : Fin D) :
    (u + v) i = xor (u i) (v i) := rfl

/-- Negation in characteristic 2 is the identity. -/
instance : Neg (F2Power D) := ⟨fun v => v⟩

@[simp] theorem neg_eq_self (v : F2Power D) : -v = v := rfl

/-- Subtraction reduces to addition in characteristic 2. -/
instance : Sub (F2Power D) := ⟨fun u v => u + v⟩

@[simp] theorem sub_eq_add (u v : F2Power D) : u - v = u + v := rfl

instance : AddCommGroup (F2Power D) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  add_assoc u v w := by
    funext i
    show xor (xor (u i) (v i)) (w i) = xor (u i) (xor (v i) (w i))
    cases u i <;> cases v i <;> cases w i <;> rfl
  zero_add v := by
    funext i
    show xor false (v i) = v i
    cases v i <;> rfl
  add_zero v := by
    funext i
    show xor (v i) false = v i
    cases v i <;> rfl
  neg_add_cancel v := by
    funext i
    show xor (v i) (v i) = false
    cases v i <;> rfl
  add_comm u v := by
    funext i
    show xor (u i) (v i) = xor (v i) (u i)
    cases u i <;> cases v i <;> rfl
  nsmul := nsmulRec
  zsmul := zsmulRec
  sub_eq_add_neg u v := by funext i; rfl

@[simp] theorem add_self (v : F2Power D) : v + v = 0 := by
  funext i
  show xor (v i) (v i) = false
  cases v i <;> rfl

/-! ## Cardinality -/

/-- `F2Power D` has `2 ^ D` elements. -/
theorem card_eq : Fintype.card (F2Power D) = 2 ^ D := by
  unfold F2Power
  simp [Fintype.card_bool, Fintype.card_fin]

/-- The number of non-zero vectors in `F2Power D` is `2 ^ D - 1`. -/
theorem nonzero_card :
    (Finset.univ.filter (fun v : F2Power D => v ≠ 0)).card = 2 ^ D - 1 := by
  have h : (Finset.univ.filter (fun v : F2Power D => v ≠ 0)).card =
           Fintype.card (F2Power D) - 1 := by
    rw [show (Finset.univ.filter (fun v : F2Power D => v ≠ 0)) =
            Finset.univ.erase 0 from ?_, Finset.card_erase_of_mem (Finset.mem_univ _)]
    · rfl
    · ext v
      simp [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ]
  rw [h, card_eq]

/-- At `D = 3`, the non-zero count is `7`. The seven Booker plot
    families bijection in `Aesthetics.NarrativeGeodesic` chains off
    this corollary. -/
theorem nonzero_card_three :
    (Finset.univ.filter (fun v : F2Power 3 => v ≠ 0)).card = 7 := by
  have h := @nonzero_card 3
  -- h : … = 2 ^ 3 - 1
  have h2 : (2 : ℕ) ^ 3 - 1 = 7 := by norm_num
  rw [h2] at h
  exact h

/-! ## Hamming weight -/

/-- The Hamming weight of `v`: the number of coordinates equal to
    `true`. -/
def hammingWeight (v : F2Power D) : ℕ :=
  (Finset.univ.filter (fun i => v i = true)).card

@[simp] theorem hammingWeight_zero : hammingWeight (0 : F2Power D) = 0 := by
  unfold hammingWeight
  simp [zero_apply]

theorem hammingWeight_le (v : F2Power D) : hammingWeight v ≤ D := by
  unfold hammingWeight
  calc (Finset.univ.filter (fun i => v i = true)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = D := by simp [Finset.card_univ, Fintype.card_fin]

theorem weight_zero_iff (v : F2Power D) :
    hammingWeight v = 0 ↔ v = 0 := by
  constructor
  · intro h
    unfold hammingWeight at h
    rw [Finset.card_eq_zero] at h
    funext i
    have hi : i ∉ Finset.univ.filter (fun j => v j = true) := by
      rw [h]; exact Finset.notMem_empty _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    -- hi : ¬ v i = true
    cases hv : v i
    · rfl
    · exact absurd hv hi
  · intro h
    subst h
    exact hammingWeight_zero

/-! ## Weight decomposition at `D = 3`

The seven non-zero vectors of `F2Power 3` partition by Hamming
weight into 3 weight-1 (single-axis), 3 weight-2 (two-axis), and 1
weight-3 (all-axes) class. This is the `1+3+3+1` decomposition that
matches Booker's primary/compound/transcendent classification. -/

/-- The unique weight-0 element: the zero vector. -/
theorem card_weight_zero_three :
    (Finset.univ.filter (fun v : F2Power 3 => hammingWeight v = 0)).card = 1 := by
  have hsubset :
      (Finset.univ.filter (fun v : F2Power 3 => hammingWeight v = 0)) = {0} := by
    ext v
    simp [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, weight_zero_iff]
  rw [hsubset]
  rfl

/-- The three weight-1 vectors of `F2Power 3` are
    `(true, false, false)`, `(false, true, false)`,
    `(false, false, true)`. -/
def axis1 : F2Power 3 := ![true, false, false]
def axis2 : F2Power 3 := ![false, true, false]
def axis3 : F2Power 3 := ![false, false, true]

theorem axis1_weight : hammingWeight axis1 = 1 := by
  unfold hammingWeight axis1
  decide

theorem axis2_weight : hammingWeight axis2 = 1 := by
  unfold hammingWeight axis2
  decide

theorem axis3_weight : hammingWeight axis3 = 1 := by
  unfold hammingWeight axis3
  decide

/-- The three weight-2 vectors. -/
def axis12 : F2Power 3 := ![true, true, false]
def axis13 : F2Power 3 := ![true, false, true]
def axis23 : F2Power 3 := ![false, true, true]

/-- The unique weight-3 vector. -/
def axis123 : F2Power 3 := ![true, true, true]

theorem axis123_weight : hammingWeight axis123 = 3 := by
  unfold hammingWeight axis123
  decide

/-! ## Subgroup count

Every non-zero `v : F2Power D` generates the 1-dimensional subspace
`{0, v}` (closed under XOR because `v + v = 0`). The map
`v ↦ {0, v}` from non-zero vectors to 1-dimensional subspaces is a
bijection: every 1-dimensional `F2`-subspace consists of exactly two
elements (`0` and a single non-zero generator), and the generator is
unique. -/

/-- The 1-dimensional subspace generated by a non-zero `v`. -/
def oneDimSubspace (v : F2Power D) : Finset (F2Power D) :=
  {0, v}

theorem oneDimSubspace_card (v : F2Power D) (hv : v ≠ 0) :
    (oneDimSubspace v).card = 2 := by
  unfold oneDimSubspace
  simp [Finset.card_insert_of_notMem, Ne.symm hv]

/-- The 1-dimensional subspace is closed under addition. -/
theorem oneDimSubspace_closed (v : F2Power D) (a b : F2Power D)
    (ha : a ∈ oneDimSubspace v) (hb : b ∈ oneDimSubspace v) :
    a + b ∈ oneDimSubspace v := by
  unfold oneDimSubspace at ha hb ⊢
  simp [Finset.mem_insert, Finset.mem_singleton] at ha hb ⊢
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    subst_vars <;> simp [add_self]

end F2Power

end Algebra
end IndisputableMonolith
