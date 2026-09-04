import Mathlib
import IndisputableMonolith.Foundation.EmbodimentFactorization

/-!
# The floor-to-floor step: the same eight at every scale, by construction

## The question

The library carries the octave at three floors, each citing the eight-tick
on its own: the nuclear closures 2 and 8, the atomic shells on the
composite sphere, and the genetic code's `64 = 8²`. Three separate
invocations of one structure is an observation. This module asks whether
there is a step from a floor to the next that makes the recurrence a
consequence rather than a coincidence.

## The answer

There is, and it was already in the tree under another name.
`EmbodimentFactorization` proves that a voxel factors as a pattern times an
address, `VoxelSpace ≃ Q3 × (Fin 3 → ℤ)`. The address is again a voxel: the
type `Fin 3 → ℤ` *is* `VoxelSpace`. So the factorization can be applied to
the address, and again to its address, without end. Each application peels
off one more layer of three binary distinctions. The floor-`F` pattern of a
position is the `F`-th binary digit of each of its three coordinates
(`floorPat`), and the floors are independent: any sequence of patterns and
any residual address assemble into exactly one position (`towerEquiv`).

The step from floor `F` to floor `F+1` is `addressD`: an item of floor
`F+1` is the address left when floor `F`'s pattern is divided out. The
fiber over one such item is a complete octave of floor-`F` patterns, and
every item's fiber is (`item_fiber_full_octave`): closure at one floor,
the whole set of eight patterns sharing an address, *is* one item of the
next. That sentence was the floors conjecture; here it is a theorem about
the lattice.

## What is honestly shown, and what is not

* The step is **dimension-generic**. `stepEquivD` is proved for `Fin D → ℤ`
  at every `D`, with `2^D` patterns per floor (`card_floor`). The number
  eight is not produced by the step; it is produced by `D = 3`, which is
  forced elsewhere (`PublicSpineLinkingClosure.forces_D3`) and is also the
  one dimension where the `2^D` states coincide with the `2(D+1)` frame
  roles (`StateQuaternions.card_evenClass_eq_dim`). The step explains why
  the count *recurs*; it does not explain the count.
* The step needs infinite addresses. A floor whose addresses form a finite
  group does not step (`finite_address_does_not_step`): the tower has no
  top, and a bounded carrier would be its top floor.
* The floors of this tower are binary scales of one lattice. That the
  physical floors (nuclear, atomic, genetic, molecular) *are* these scales
  is a reading and stays MODEL. One check is recorded: two consecutive
  floors carry exactly `64` patterns (`two_floors_card`), which is the
  codon count `4³ = 64 = 8²`, with each
  nucleotide's two bits read as one bit on each of two floors. That is a
  count agreeing, not a derivation of the code.
* The role names of `plans/Octave_Floors_Slot_Map_20260830.html` (closed,
  1-over, half, 1-short, and their mirrors) are the `2(D+1)` frame slots,
  which at `D = 3` are in bijection with the eight floor patterns. Which
  physical occupant sits in which slot at which floor is not decided here.

Status: 0 sorry; axiom audits printed at the end.
-/

namespace IndisputableMonolith
namespace Foundation
namespace OctaveFloorStep

open Q3PhysicalCovering EmbodimentFactorization

variable {D : ℕ}

/-! ## §1. The step, in every dimension -/

/-- The parity of each coordinate: the pattern a lattice point carries. -/
def parityD (x : Fin D → ℤ) : Fin D → Bool := fun i => decide (x i % 2 = 1)

/-- The address: each coordinate with its parity bit divided out. It is a
lattice point of the same type, which is what makes the step iterable. -/
def addressD (x : Fin D → ℤ) : Fin D → ℤ := fun i => x i / 2

/-- Assemble a lattice point from a pattern and an address. -/
def assembleD (p : Fin D → Bool) (a : Fin D → ℤ) : Fin D → ℤ :=
  fun i => 2 * a i + (if p i then 1 else 0)

theorem parityD_assembleD (p : Fin D → Bool) (a : Fin D → ℤ) :
    parityD (assembleD p a) = p := by
  funext i
  show decide ((2 * a i + (if p i then 1 else 0)) % 2 = 1) = p i
  cases hp : p i
  · have h : ¬ (2 * a i + (0 : ℤ)) % 2 = 1 := by omega
    simpa using decide_eq_false h
  · have h : (2 * a i + (1 : ℤ)) % 2 = 1 := by omega
    simpa using decide_eq_true h

theorem addressD_assembleD (p : Fin D → Bool) (a : Fin D → ℤ) :
    addressD (assembleD p a) = a := by
  funext i
  show (2 * a i + (if p i then 1 else 0)) / 2 = a i
  cases p i <;> simp <;> omega

theorem assembleD_parity_address (x : Fin D → ℤ) :
    assembleD (parityD x) (addressD x) = x := by
  funext i
  show 2 * (x i / 2) + (if decide (x i % 2 = 1) then 1 else 0) = x i
  rcases Int.emod_two_eq (x i) with h | h
  · have hd : ¬ (x i % 2 = 1) := by omega
    simp [hd]
    omega
  · simp [h]
    omega

/-- **The step.** In every dimension, a lattice point is a pattern times a
lattice point. -/
def stepEquivD : (Fin D → ℤ) ≃ (Fin D → Bool) × (Fin D → ℤ) where
  toFun x := (parityD x, addressD x)
  invFun q := assembleD q.1 q.2
  left_inv x := assembleD_parity_address x
  right_inv q := by
    cases q with
    | mk p a => simp [parityD_assembleD, addressD_assembleD]

/-- Patterns per floor: `2^D`. Eight exactly when `D = 3`. -/
theorem card_floor : Fintype.card (Fin D → Bool) = 2 ^ D := by
  simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-! ## §2. The tower: floors are independent binary digits -/

/-- The floor-`F` pattern of a lattice point: the parity after `F`
halvings, which is the `F`-th binary digit of each coordinate. -/
def floorPat (F : ℕ) (x : Fin D → ℤ) : Fin D → Bool :=
  parityD (addressD^[F] x)

theorem floorPat_zero (x : Fin D → ℤ) : floorPat 0 x = parityD x := rfl

theorem addressD_iterate_assembleD (F : ℕ) (p : Fin D → Bool) (a : Fin D → ℤ) :
    addressD^[F + 1] (assembleD p a) = addressD^[F] a := by
  rw [Function.iterate_succ_apply, addressD_assembleD]

/-- Assembling a pattern at the bottom pushes every floor up by one. -/
theorem floorPat_succ_assembleD (F : ℕ) (p : Fin D → Bool) (a : Fin D → ℤ) :
    floorPat (F + 1) (assembleD p a) = floorPat F a := by
  unfold floorPat
  rw [addressD_iterate_assembleD]

theorem floorPat_zero_assembleD (p : Fin D → Bool) (a : Fin D → ℤ) :
    floorPat 0 (assembleD p a) = p := by
  rw [floorPat_zero, parityD_assembleD]

/-- Build a lattice point from `F` floor patterns and a residual address. -/
def build : (F : ℕ) → (Fin F → (Fin D → Bool)) → (Fin D → ℤ) → (Fin D → ℤ)
  | 0, _, a => a
  | F + 1, ps, a => assembleD (ps 0) (build F (Fin.tail ps) a)

theorem addressD_iterate_build (F : ℕ) (ps : Fin F → (Fin D → Bool))
    (a : Fin D → ℤ) : addressD^[F] (build F ps a) = a := by
  induction F with
  | zero => rfl
  | succ F ih =>
      show addressD^[F + 1] (assembleD (ps 0) (build F (Fin.tail ps) a)) = a
      rw [addressD_iterate_assembleD, ih]

theorem floorPat_build (F : ℕ) (ps : Fin F → (Fin D → Bool)) (a : Fin D → ℤ)
    (i : Fin F) : floorPat i (build F ps a) = ps i := by
  induction F with
  | zero => exact i.elim0
  | succ F ih =>
      show floorPat i (assembleD (ps 0) (build F (Fin.tail ps) a)) = ps i
      refine Fin.cases ?_ ?_ i
      · exact floorPat_zero_assembleD _ _
      · intro j
        show floorPat (j.1 + 1) (assembleD (ps 0) (build F (Fin.tail ps) a))
          = ps j.succ
        rw [floorPat_succ_assembleD]
        exact ih (Fin.tail ps) j

theorem build_floorPat_address (F : ℕ) (x : Fin D → ℤ) :
    build F (fun i => floorPat i x) (addressD^[F] x) = x := by
  induction F generalizing x with
  | zero => rfl
  | succ F ih =>
      show assembleD (floorPat 0 x)
        (build F (Fin.tail fun i : Fin (F + 1) => floorPat i x)
          (addressD^[F + 1] x)) = x
      have htail : (Fin.tail fun i : Fin (F + 1) => floorPat i x)
          = fun i : Fin F => floorPat i (addressD x) := by
        funext i
        show floorPat (i.1 + 1) x = floorPat i (addressD x)
        unfold floorPat
        rw [Function.iterate_succ_apply]
      rw [htail, Function.iterate_succ_apply, ih (addressD x), floorPat_zero,
        assembleD_parity_address]

/-- **The tower.** A lattice point is exactly `F` independent floor
patterns together with a residual address, for every `F`. -/
def towerEquiv (F : ℕ) :
    (Fin D → ℤ) ≃ (Fin F → (Fin D → Bool)) × (Fin D → ℤ) where
  toFun x := (fun i => floorPat i x, addressD^[F] x)
  invFun q := build F q.1 q.2
  left_inv x := build_floorPat_address F x
  right_inv q := by
    cases q with
    | mk ps a =>
        simp only [Prod.mk.injEq]
        exact ⟨funext fun i => floorPat_build F ps a i,
          addressD_iterate_build F ps a⟩

/-! ## §3. Closure at one floor is an item of the next -/

/-- **Every floor is a full recognizer.** At every floor, every pattern
occurs. -/
theorem floorPat_surjective (F : ℕ) :
    Function.Surjective (floorPat (D := D) F) := by
  intro p
  refine ⟨build (F + 1) (fun _ => p) 0, ?_⟩
  exact floorPat_build (F + 1) (fun _ => p) 0 ⟨F, Nat.lt_succ_self F⟩

/-- **Closure is an item.** The item of floor `F+1` is the address after
`F+1` halvings. Over any item and any choice of the lower floors, the
floor-`F` pattern ranges over the whole octave: the set of positions sharing
an item is a complete floor-`F` octave. -/
theorem item_fiber_full_octave (F : ℕ) (a : Fin D → ℤ)
    (lower : Fin F → (Fin D → Bool)) (p : Fin D → Bool) :
    ∃ x : Fin D → ℤ, addressD^[F + 1] x = a
      ∧ floorPat F x = p
      ∧ ∀ i : Fin F, floorPat i x = lower i := by
  refine ⟨build (F + 1) (Fin.snoc lower p) a, ?_, ?_, ?_⟩
  · exact addressD_iterate_build (F + 1) _ a
  · have h := floorPat_build (F + 1) (Fin.snoc lower p) a (Fin.last F)
    rwa [Fin.snoc_last] at h
  · intro i
    have h := floorPat_build (F + 1) (Fin.snoc lower p) a i.castSucc
    rwa [Fin.snoc_castSucc] at h

/-- The position with given floors and item is unique: the fiber over an
item, with the lower floors fixed, has exactly one position per top-floor
pattern. -/
theorem item_fiber_unique (F : ℕ) (x y : Fin D → ℤ)
    (ha : addressD^[F + 1] x = addressD^[F + 1] y)
    (hp : ∀ i : Fin (F + 1), floorPat i x = floorPat i y) : x = y := by
  have hx := build_floorPat_address (F + 1) x
  have hy := build_floorPat_address (F + 1) y
  rw [← hx, ← hy]
  congr 1
  funext i
  exact hp i

/-- **The fiber over an item is `2^D` positions per lower configuration**:
one complete octave at `D = 3`. Stated as a bijection with the top floor. -/
def itemFiberEquiv (F : ℕ) (a : Fin D → ℤ) (lower : Fin F → (Fin D → Bool)) :
    {x : Fin D → ℤ // addressD^[F + 1] x = a ∧ ∀ i : Fin F, floorPat i x = lower i}
      ≃ (Fin D → Bool) where
  toFun x := floorPat F x.1
  invFun p := ⟨build (F + 1) (Fin.snoc lower p) a,
    addressD_iterate_build (F + 1) _ a,
    fun i => by
      have h := floorPat_build (F + 1) (Fin.snoc lower p) a i.castSucc
      rwa [Fin.snoc_castSucc] at h⟩
  left_inv x := by
    apply Subtype.ext
    apply item_fiber_unique F
    · rw [addressD_iterate_build, x.2.1]
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · have h := floorPat_build (F + 1) (Fin.snoc lower (floorPat F x.1)) a (Fin.last F)
        rw [Fin.snoc_last] at h
        exact h
      · intro j
        have h := floorPat_build (F + 1) (Fin.snoc lower (floorPat F x.1)) a j.castSucc
        rw [Fin.snoc_castSucc] at h
        rw [h]
        exact (x.2.2 j).symm
  right_inv p := by
    show floorPat F (build (F + 1) (Fin.snoc lower p) a) = p
    have h := floorPat_build (F + 1) (Fin.snoc lower p) a (Fin.last F)
    rwa [Fin.snoc_last] at h

/-! ## §4. The decoy: finite addresses do not step -/

/-- A floor whose addresses form a finite group cannot factor as pattern
times itself: the step needs the address to be free. A bounded carrier is
a top floor. -/
theorem finite_address_does_not_step :
    ¬ ∃ _ : (Fin 3 → ZMod 2) ≃ (Fin 3 → Bool) × (Fin 3 → ZMod 2), True := by
  rintro ⟨e, _⟩
  have h := Fintype.card_congr e
  simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ZMod.card] at h

/-! ## §5. The three-dimensional instance is the atomic map's own objects -/

theorem parityD_three_eq_cellParity : parityD (D := 3) = cellParity := rfl

theorem addressD_three_eq_address : addressD (D := 3) = address := rfl

theorem assembleD_three_eq_assemble (p : Q3) (a : Fin 3 → ℤ) :
    assembleD (D := 3) p a = assemble p a := by
  funext i
  show 2 * a i + (if p i then 1 else 0) = 2 * a i + bitZ (p i)
  cases p i <;> rfl

/-- At `D = 3` the step is `EmbodimentFactorization.positionEquiv`: the
same map, now recognized as iterable. -/
theorem stepEquivD_three_apply (x : VoxelSpace) :
    stepEquivD (D := 3) x = positionEquiv x := rfl

/-- Eight patterns per floor at `D = 3`. -/
theorem card_floor_three : Fintype.card (Fin 3 → Bool) = 8 := by
  rw [card_floor]
  norm_num

/-- **Two consecutive floors carry `64` patterns**, the codon count
(`4³ = 64 = 8²`). A check, not a derivation:
it says the genetic floor has the pattern count of two adjacent floors of
this tower, with each nucleotide's two bits read as one bit per floor. -/
theorem two_floors_card : Fintype.card (Fin 2 → (Fin 3 → Bool)) = 64 := by
  simp [Fintype.card_bool, Fintype.card_fin]

/-! ## §6. The census -/

structure ReasonStatus where
  id : String
  title : String
  status : String

def floorStepCensus : List ReasonStatus :=
  [ ⟨"S1", "a lattice point is a pattern times a lattice point, in every dimension (stepEquivD)", "THEOREM"⟩
  , ⟨"S2", "the step iterates: F floors of independent patterns plus a residual address (towerEquiv)", "THEOREM"⟩
  , ⟨"S3", "every floor is a full recognizer; every pattern occurs at every floor (floorPat_surjective)", "THEOREM"⟩
  , ⟨"S4", "closure is an item: the positions sharing a next-floor item form a complete octave, one per top pattern (item_fiber_full_octave, itemFiberEquiv)", "THEOREM"⟩
  , ⟨"S5", "finite addresses do not step; the tower has no top (finite_address_does_not_step)", "THEOREM"⟩
  , ⟨"S6", "the step is dimension-generic with 2^D patterns per floor; eight is D = 3, forced elsewhere (card_floor, forces_D3)", "THEOREM; the count is not produced by the step"⟩
  , ⟨"S7", "at D = 3 the step is positionEquiv, the atomic map's own factorization (stepEquivD_three_apply)", "THEOREM"⟩
  , ⟨"S8", "two consecutive floors carry 64 patterns, the codon count (two_floors_card)", "THEOREM as a count; the reading of nucleotide bits as floors is MODEL"⟩
  , ⟨"S9", "the physical floors (nuclear, atomic, genetic, molecular) are binary scales of this lattice", "MODEL"⟩
  , ⟨"S10", "which physical occupant sits in which of the eight slots at each floor", "OPEN (the floors map's three role claims, unchecked here)"⟩
  ]

#print axioms stepEquivD
#print axioms towerEquiv
#print axioms floorPat_surjective
#print axioms item_fiber_full_octave
#print axioms item_fiber_unique
#print axioms itemFiberEquiv
#print axioms finite_address_does_not_step
#print axioms stepEquivD_three_apply
#print axioms two_floors_card

end OctaveFloorStep
end Foundation
end IndisputableMonolith
