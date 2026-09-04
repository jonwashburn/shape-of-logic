import Mathlib
import IndisputableMonolith.Foundation.Q3PhysicalCovering

/-!
# Embodiment factorization: position = pattern × address

Assumed required, then scored:

  A map carrying the pattern layer into physical embodiment.

`Q3PhysicalCovering` settled the direction of that map: there is no
placement of the eight patterns onto the voxel lattice (C05, C10), and the
forced object runs the other way, `cellParity : Z^3 → Q3`, every voxel
carrying the phase of its coordinate parities (C03). This module proves
what that covering makes of the embodiment question: **physical position
factorizes, exactly and constructively, as pattern times address**,

  `VoxelSpace ≃ Q3 × (Fin 3 → ℤ)`,

with `cellParity` the first projection. Under that equivalence:

* the D = 3 distinctions of the recognizer are physical degrees of
  freedom, namely the parities of the three spatial coordinates (E01);
* a posting (one-bit flip in pattern space) is realized by a unit
  translation of physical position along the corresponding axis (E03);
* two embodiments of the same pattern differ by an even translation, and
  the even translations (the deck action of the covering) are exactly the
  motions the pattern layer cannot see (E04, E05);
* the observables invariant under the deck action are exactly the pattern
  functionals (E06). Every functional of the pattern — the Z charge among
  them — is therefore blind to the address, and the address is what
  embodiment adds.

Decoys scored before any implication:

* the factorization needs a choice of section (no: `address` is floor
  division, and the induced section is `patternToCell`, the unique
  positive isometric section of C06);
* the pattern determines the position up to a bounded set (no: fibers are
  infinite, E02);
* deck invariance is weaker than being a pattern functional (no: E06 is
  an equivalence).

Honesty:

* THEOREM: E01–E06 below, on the lattice carrier `Fin 3 → ℤ`. That
  carrier is itself the MODEL layer this module inherits from
  `Q3PhysicalCovering`.
* MODEL: the reading of `address`-forgetting as boundary dissolution
  (light-memory), and of the pattern factor as the persistent content.
  The mathematics is E06; the identification with consciousness is not
  made here.
* OPEN: the remaining closures of the atomic map are not touched: the
  group action relating recognizer states to the atomic Hilbert space,
  occupancy of a composite as occupancy of an orbital, and the modelling
  assumptions (M1)–(M3) of the capacity count. The price of an address
  (an absolute scale for embodiment cost) is the standing scale wall and
  is not priced here.

Status: 0 sorry; axioms audited to the base triple below.
-/

namespace IndisputableMonolith
namespace Foundation
namespace EmbodimentFactorization

open Q3PhysicalCovering

/-! ## The two halves of a position -/

/-- The address of a voxel: its position with the parity bit divided out,
    coordinate by coordinate (floor division by two). -/
def address (x : VoxelSpace) : Fin 3 → ℤ :=
  fun i => x i / 2

/-- Assemble a position from a pattern and an address. -/
def assemble (p : Q3) (a : Fin 3 → ℤ) : VoxelSpace :=
  fun i => 2 * a i + bitZ (p i)

@[simp] theorem bitZ_false : bitZ false = 0 := rfl
@[simp] theorem bitZ_true : bitZ true = 1 := rfl

theorem bitZ_emod_two (x : ℤ) : bitZ (decide (x % 2 = 1)) = x % 2 := by
  rcases Int.emod_two_eq x with h | h <;> simp [h]

/-- E01a. The pattern of an assembled position is the pattern it was
    assembled from. -/
theorem cellParity_assemble (p : Q3) (a : Fin 3 → ℤ) :
    cellParity (assemble p a) = p := by
  funext i
  show decide ((2 * a i + bitZ (p i)) % 2 = 1) = p i
  cases hp : p i
  · have h : ¬ (2 * a i + (0 : ℤ)) % 2 = 1 := by omega
    simpa using decide_eq_false h
  · have h : (2 * a i + (1 : ℤ)) % 2 = 1 := by omega
    simpa using decide_eq_true h

/-- E01b. The address of an assembled position is the address it was
    assembled from. -/
theorem address_assemble (p : Q3) (a : Fin 3 → ℤ) :
    address (assemble p a) = a := by
  funext i
  show (2 * a i + bitZ (p i)) / 2 = a i
  cases p i <;> simp <;> omega

/-- E01c. Every position is the assembly of its pattern and its address. -/
theorem assemble_parity_address (x : VoxelSpace) :
    assemble (cellParity x) (address x) = x := by
  funext i
  show 2 * (x i / 2) + bitZ (decide (x i % 2 = 1)) = x i
  rw [bitZ_emod_two]
  omega

/-- **E01. Position factorizes as pattern times address.** The recognizer's
    three distinctions are the parities of the three physical coordinates,
    and what a position carries beyond its pattern is exactly one integer
    address per axis. -/
def positionEquiv : VoxelSpace ≃ Q3 × (Fin 3 → ℤ) where
  toFun x := (cellParity x, address x)
  invFun q := assemble q.1 q.2
  left_inv x := assemble_parity_address x
  right_inv q := by
    cases q with
    | mk p a => simp [cellParity_assemble, address_assemble]

theorem positionEquiv_fst (x : VoxelSpace) :
    (positionEquiv x).1 = cellParity x := rfl

/-! ## E02. Fibers are infinite: a pattern never determines its embodiment -/

theorem assemble_injective_address (p : Q3) :
    Function.Injective (assemble p) := by
  intro a b h
  have := congrArg address h
  rwa [address_assemble, address_assemble] at this

/-- E02. Every pattern has infinitely many embodiments. -/
theorem fiber_infinite (p : Q3) :
    {x : VoxelSpace | cellParity x = p}.Infinite := by
  have hinj : Function.Injective (assemble p) := assemble_injective_address p
  have hmem : ∀ a, assemble p a ∈ {x : VoxelSpace | cellParity x = p} :=
    fun a => cellParity_assemble p a
  have : Infinite (Fin 3 → ℤ) :=
    Infinite.of_injective (fun n : ℤ => (fun _ => n : Fin 3 → ℤ))
      (fun m n h => congrFun h 0)
  exact Set.infinite_of_injective_forall_mem hinj hmem

/-! ## E03. A posting is a unit physical step -/

/-- Flip one distinction of a pattern. -/
def flipPat (k : Fin 3) (p : Q3) : Q3 :=
  fun j => if j = k then !(p j) else p j

/-- Translate a position one unit along axis `k`. -/
def unitStep (k : Fin 3) (x : VoxelSpace) : VoxelSpace :=
  fun i => x i + axisUnit k i

/-- E03. A one-bit flip in pattern space is realized by a unit translation
    in physical space: the posting is the step. -/
theorem posting_is_unit_step (k : Fin 3) (x : VoxelSpace) :
    cellParity (unitStep k x) = flipPat k (cellParity x) := by
  funext i
  simp only [cellParity, unitStep, flipPat, axisUnit]
  by_cases h : i = k
  · subst h
    simp only [if_pos rfl]
    rcases Int.emod_two_eq (x i) with h0 | h1
    · have h2 : (x i + 1) % 2 = 1 := by omega
      simp [h2, h0]
    · have h2 : ¬ (x i + 1) % 2 = 1 := by omega
      simp [h2, h1]
  · simp [if_neg h]

/-- The unit step moves the position by Manhattan distance one. -/
theorem unitStep_manhattan (k : Fin 3) (x : VoxelSpace) :
    manhattan (unitStep k x) x = 1 := by
  unfold manhattan unitStep axisUnit
  fin_cases k <;> simp

/-! ## E04–E05. The deck action: what the pattern cannot see -/

/-- The deck action of the covering: translation by a doubled vector. -/
def deck (v : Fin 3 → ℤ) (x : VoxelSpace) : VoxelSpace :=
  fun i => x i + 2 * v i

/-- E04. The pattern is blind to the deck action. -/
theorem cellParity_deck (v : Fin 3 → ℤ) (x : VoxelSpace) :
    cellParity (deck v x) = cellParity x := by
  funext i
  show decide ((x i + 2 * v i) % 2 = 1) = decide (x i % 2 = 1)
  have h : (x i + 2 * v i) % 2 = x i % 2 := by omega
  rw [h]

/-- E05. Two positions carry the same pattern exactly when they differ by
    an even translation: the fiber is one deck orbit. -/
theorem same_pattern_iff_deck (x y : VoxelSpace) :
    cellParity x = cellParity y ↔ ∃ v, y = deck v x := by
  constructor
  · intro h
    refine ⟨fun i => (y i - x i) / 2, ?_⟩
    funext i
    have hi := congrFun h i
    have hiff : x i % 2 = 1 ↔ y i % 2 = 1 := by
      simpa [cellParity, decide_eq_decide] using hi
    show y i = x i + 2 * ((y i - x i) / 2)
    rcases Int.emod_two_eq (x i) with h0 | h1 <;>
      rcases Int.emod_two_eq (y i) with g0 | g1 <;> omega
  · rintro ⟨v, rfl⟩
    exact (cellParity_deck v x).symm

/-! ## E06. Deck-invariant observables are exactly the pattern functionals -/

/-- E06. A functional of position is invariant under the deck action if and
    only if it factors through the pattern. The pattern layer holds exactly
    the deck-invariant content of a position; the address is the rest. -/
theorem deck_invariant_iff_pattern_functional {α : Type _}
    (f : VoxelSpace → α) :
    (∀ v x, f (deck v x) = f x) ↔
      ∃ g : Q3 → α, ∀ x, f x = g (cellParity x) := by
  constructor
  · intro h
    refine ⟨fun p => f (patternToCell p), fun x => ?_⟩
    have hx : deck (address x) (patternToCell (cellParity x)) = x := by
      funext i
      show bitZ (cellParity x i) + 2 * (x i / 2) = x i
      unfold cellParity
      rw [bitZ_emod_two]
      omega
    calc f x = f (deck (address x) (patternToCell (cellParity x))) := by
                rw [hx]
      _ = f (patternToCell (cellParity x)) := h _ _
  · rintro ⟨g, hg⟩ v x
    rw [hg, hg, cellParity_deck]

/-- Corollary: every pattern functional takes the same value on every
    embodiment of a pattern. Content survives any change of address. -/
theorem pattern_functional_constant_on_fiber {α : Type _} (g : Q3 → α)
    (x y : VoxelSpace) (h : cellParity x = cellParity y) :
    g (cellParity x) = g (cellParity y) := by rw [h]

/-! ## The census -/

def reasonTable : List ReasonStatus :=
  [ ⟨"E01", "position factorizes as pattern times address", "THEOREM"⟩
  , ⟨"E02", "every pattern has infinitely many embodiments", "THEOREM"⟩
  , ⟨"E03", "a posting is a unit physical step", "THEOREM"⟩
  , ⟨"E04", "the pattern is blind to even translations", "THEOREM"⟩
  , ⟨"E05", "a fiber is exactly one deck orbit", "THEOREM"⟩
  , ⟨"E06", "deck-invariant observables are the pattern functionals", "THEOREM"⟩
  , ⟨"E07", "the lattice carrier is physical space", "MODEL"⟩
  , ⟨"E08", "address-forgetting is boundary dissolution", "MODEL"⟩
  , ⟨"E09", "group action from recognizer states to the atomic Hilbert space", "OPEN"⟩
  , ⟨"E10", "occupancy of a composite is occupancy of an orbital", "OPEN"⟩
  , ⟨"E11", "the price of an address (absolute embodiment cost)", "OPEN"⟩
  ]

/-- The factorization, packaged: the covering splits position into the
    pattern the recognizer holds and the address embodiment adds, postings
    are unit steps, and the pattern layer is exactly the deck-invariant
    content of physical position. -/
theorem embodiment_factorization_forced :
    (∀ x, assemble (cellParity x) (address x) = x) ∧
      (∀ p a, cellParity (assemble p a) = p) ∧
      (∀ p a, address (assemble p a) = a) ∧
      (∀ p, {x : VoxelSpace | cellParity x = p}.Infinite) ∧
      (∀ k x, cellParity (unitStep k x) = flipPat k (cellParity x)) ∧
      (∀ x y, cellParity x = cellParity y ↔ ∃ v, y = deck v x) :=
  ⟨assemble_parity_address, cellParity_assemble, address_assemble,
   fiber_infinite, posting_is_unit_step, same_pattern_iff_deck⟩

#print axioms positionEquiv
#print axioms fiber_infinite
#print axioms posting_is_unit_step
#print axioms same_pattern_iff_deck
#print axioms deck_invariant_iff_pattern_functional
#print axioms embodiment_factorization_forced

end EmbodimentFactorization
end Foundation
end IndisputableMonolith
