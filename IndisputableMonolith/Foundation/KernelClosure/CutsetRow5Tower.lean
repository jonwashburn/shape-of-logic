import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow5RecogGeom
import IndisputableMonolith.Foundation.OctaveFloorStep

/-!
# Cutset row 5, the tower: a record that survives motion is not a record of where

## The question

Row 5's one remaining sentence is that the placements of the act's two traces
form a recognition geometry (`CutsetRow5RecogGeom.RecognitionGeometry`): some
recognizer that reads the same event along every recognition-free motion tells
two placements apart. This module asks whether the octave floor tower
(`OctaveFloorStep`), which is the theory's own account of position, supplies
that recognizer.

## Step 0: position is a ledger fact

A lattice position is exactly its floor patterns plus a residual address
(`towerEquiv`); the item at floor `F+1` is division by `2^(F+1)`
(`addressD_iterate_apply`). So a unit step of a trace flips bits, and a motion
is recognition-free *for a floor* when it stays inside one item of that floor.

## What the tower reads

The floor readers read where a trace is, and every one of them is moved by a
carry: for every floor `F` and every axis `i` there is a position whose unit
step along `i` changes its floor-`F+1` item (`floorReader_moves`). More than
that: any reader of positions that no unit step changes is constant
(`invariant_reader_constant`). So no recognizer built from position, at any
floor or across floors, is both invariant under motion and nontrivial
(`no_invariant_positional_recognizer`), and a pair kinematics whose
configurations are positions with unit steps among its motions is not a
recognition geometry (`no_positional_geometry`), in every dimension.

## What this settles

The tower cannot supply the row 5 recognizer. A record the placement keeps
through motion is not a record of *where* the traces are; it is a record of
*how they sit*, an invariant of the motion class. On placements of two loops the
motion classes are the linking classes, which exist in exactly one dimension
(`recognitionGeometry_forces_D3`, `recognitionGeometry_at_three`). The one
sentence that remains for row 5 is therefore sharper than before: the ledger
reads the act's placement through a motion invariant. That the ledger's traces
have a space in this sense (RG2, `RecogGeom.Recognizer.nontrivial`) is the
identification the row rests on; the tower neither supplies nor contradicts it.

The cells-only ledger (record kept as a "done" bit, placement not read) is not
excluded here: its "done" bit is the floor-above reading of A1
(`CutsetRowA1Floor`), so it is a ledger with a floor above that reads the act
and does not read the placement. It is the world with a ledger and no space.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row5Tower

open LinkingNecessity OctaveFloorStep Row5RecogGeom

variable {D : ℕ}

/-! ## Step 0: the item at floor `k` is division by `2^k` -/

theorem addressD_iterate_apply (k : ℕ) (x : Fin D → ℤ) (i : Fin D) :
    (addressD^[k] x) i = x i / 2 ^ k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih]
      show x i / 2 / 2 ^ k = x i / 2 ^ (k + 1)
      rw [Int.ediv_ediv_eq_ediv_mul]
      · rw [pow_succ, mul_comm]
      · norm_num

/-! ## The floor readers are moved by a carry -/

/-- **Every floor reader is moved by some unit step.** At the position
`2^(F+1) - 1` on every axis, one step along axis `i` carries into floor `F+1`. -/
theorem floorReader_moves (F : ℕ) (i : Fin D) :
    ∃ x : Fin D → ℤ,
      addressD^[F + 1] (x + Pi.single i 1) ≠ addressD^[F + 1] x := by
  refine ⟨fun _ => 2 ^ (F + 1) - 1, ?_⟩
  intro heq
  have h := congrFun heq i
  rw [addressD_iterate_apply, addressD_iterate_apply] at h
  simp only [Pi.add_apply, Pi.single_eq_same] at h
  have hp : (0 : ℤ) < 2 ^ (F + 1) := by positivity
  have h1 : ((2 : ℤ) ^ (F + 1) - 1 + 1) / 2 ^ (F + 1) = 1 := by
    rw [sub_add_cancel]
    exact Int.ediv_self hp.ne'
  have h0 : ((2 : ℤ) ^ (F + 1) - 1) / 2 ^ (F + 1) = 0 :=
    Int.ediv_eq_zero_of_lt (by omega) (by omega)
  rw [h1, h0] at h
  exact one_ne_zero h

/-! ## A reader no step changes reads nothing -/

/-- Invariance under one step in each direction gives invariance under any
number of steps. -/
theorem invariant_steps {E : Type} (R : (Fin D → ℤ) → E)
    (h : ∀ x (i : Fin D), R (x + Pi.single i 1) = R x) (x : Fin D → ℤ) (i : Fin D) (n : ℤ) :
    R (x + Pi.single i n) = R x := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [Pi.single_add, ← add_assoc, h, ih]
  | pred n ih =>
      have := h (x + Pi.single i (-(n : ℤ) - 1)) i
      rw [add_assoc, ← Pi.single_add, sub_add_cancel] at this
      rw [← this, ih]

/-- **A reader of positions that no unit step changes is constant.** -/
theorem invariant_reader_constant {E : Type} (R : (Fin D → ℤ) → E)
    (h : ∀ x (i : Fin D), R (x + Pi.single i 1) = R x) : ∀ x y, R x = R y := by
  have hzero : ∀ x : Fin D → ℤ, R x = R 0 := by
    intro x
    have key : ∀ s : Finset (Fin D), R (∑ i ∈ s, Pi.single i (x i)) = R 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert j s hj ih =>
          rw [Finset.sum_insert hj, add_comm, invariant_steps R h, ih]
    have := key Finset.univ
    rwa [Finset.univ_sum_single] at this
  intro x y
  rw [hzero x, hzero y]

/-! ## No positional recognizer survives motion -/

/-- **No recognizer of positions is both step-invariant and nontrivial.** -/
theorem no_invariant_positional_recognizer :
    ¬ ∃ (E : Type) (R : RecogGeom.Recognizer (Fin D → ℤ) E),
      ∀ x (i : Fin D), R.R (x + Pi.single i 1) = R.R x := by
  rintro ⟨E, R, hinv⟩
  obtain ⟨a, b, hab⟩ := R.nontrivial
  exact hab (invariant_reader_constant R.R hinv a b)

/-- **Placements read as positions form no recognition geometry.** Any pair
kinematics whose configurations are lattice positions, with the unit steps
among its recognition-free motions, admits no invariant nontrivial recognizer. -/
theorem no_positional_geometry (X : PairKinematics) (e : X.Config ≃ (Fin D → ℤ))
    (hstep : ∀ c (i : Fin D), X.deform c (e.symm (e c + Pi.single i 1))) :
    ¬ RecognitionGeometry X := by
  rintro ⟨E, ⟨R⟩⟩
  apply no_invariant_positional_recognizer (D := D)
  refine ⟨E, { R := fun x => R.R (e.symm x), nontrivial := ?_ }, ?_⟩
  · obtain ⟨a, b, hab⟩ := R.nontrivial
    exact ⟨e a, e b, by simpa using hab⟩
  · intro x i
    show R.R (e.symm (x + Pi.single i 1)) = R.R (e.symm x)
    have := R.invariant _ _ (hstep (e.symm x) i)
    rw [e.apply_symm_apply] at this
    exact this.symm

/-! ## The floor reader is a recognizer, and it is not invariant -/

/-- The floor-`F+1` reader as a recognizer on positions (nontrivial for `D ≥ 1`). -/
def floorReader (F : ℕ) (i : Fin D) : RecogGeom.Recognizer (Fin D → ℤ) (Fin D → ℤ) where
  R := addressD^[F + 1]
  nontrivial := by
    obtain ⟨x, hx⟩ := floorReader_moves F i
    exact ⟨x + Pi.single i 1, x, hx⟩

/-- The floor reader reads where, and motion changes where. -/
theorem floorReader_not_invariant (F : ℕ) (i : Fin D) :
    ¬ ∀ x (j : Fin D), (floorReader F i).R (x + Pi.single j 1) = (floorReader F i).R x := by
  intro h
  exact no_invariant_positional_recognizer ⟨_, floorReader F i, h⟩

/-! ## Certificate -/

structure Cert : Prop where
  /-- Step 0: the item at floor `k` is division by `2^k`. -/
  item_is_division : ∀ (D k : ℕ) (x : Fin D → ℤ) (i : Fin D), (addressD^[k] x) i = x i / 2 ^ k
  /-- Every floor reader is moved by some unit step. -/
  floor_reader_moves : ∀ (D F : ℕ) (i : Fin D), ∃ x : Fin D → ℤ,
    addressD^[F + 1] (x + Pi.single i 1) ≠ addressD^[F + 1] x
  /-- A reader no step changes is constant. -/
  invariant_is_constant : ∀ (D : ℕ) {E : Type} (R : (Fin D → ℤ) → E),
    (∀ x (i : Fin D), R (x + Pi.single i 1) = R x) → ∀ x y, R x = R y
  /-- No step-invariant nontrivial recognizer of positions. -/
  no_positional_recognizer : ∀ D : ℕ, ¬ ∃ (E : Type) (R : RecogGeom.Recognizer (Fin D → ℤ) E),
    ∀ x (i : Fin D), R.R (x + Pi.single i 1) = R.R x
  /-- Placements read as positions are no recognition geometry, in any dimension. -/
  no_positional_geometry : ∀ (D : ℕ) (X : PairKinematics) (e : X.Config ≃ (Fin D → ℤ)),
    (∀ c (i : Fin D), X.deform c (e.symm (e c + Pi.single i 1))) → ¬ RecognitionGeometry X
  /-- The positive side, unchanged: a recognition geometry on loop placements is `D = 3`. -/
  forces_D3 : ∀ (D : DimensionForcing.Dimension) (S : SpatialLoopSpace D),
    RecognitionGeometry S.kin → D = 3
  at_three : ∀ S : SpatialLoopSpace 3, RecognitionGeometry S.kin
  decoy : ¬ RecognitionGeometry unlinkedKinematics

theorem cert : Cert where
  item_is_division := fun _ k x i => addressD_iterate_apply k x i
  floor_reader_moves := fun _ F i => floorReader_moves F i
  invariant_is_constant := fun _ _ R h => invariant_reader_constant R h
  no_positional_recognizer := fun _ => no_invariant_positional_recognizer
  no_positional_geometry := fun _ X e h => no_positional_geometry X e h
  forces_D3 := recognitionGeometry_forces_D3
  at_three := recognitionGeometry_at_three
  decoy := d4_not_recognitionGeometry

end Row5Tower
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
