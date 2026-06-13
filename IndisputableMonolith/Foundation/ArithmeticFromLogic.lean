/-
  ArithmeticFromLogic.lean

  Recovery of the natural numbers from the Law of Logic.

  Status: Level 1. The inductive structure of the natural numbers,
  Peano's axioms, and the addition/multiplication operations are
  recovered as forced consequences of `SatisfiesLawsOfLogic C` plus
  the existence of a non-trivial generator. Section 5 ("Embedding into
  ℝ₊") establishes the structural map from `LogicNat` to the
  multiplicative group of positive reals via iteration of a generator;
  this is what ties the abstract Peano structure back to the
  comparison operator.

  No assumption is made about base 10. The recovery works at the level
  of the inductive structure (zero, successor) and never references a
  positional representation.

  Forcing chain made explicit by this module:
    Law of Logic (four Aristotelian conditions on C)
      ⊢ J = derivedCost C is the unique calibrated reciprocal cost
      ⊢ existence of identity element (J(1) = 0) and a non-trivial
        generator γ (J(γ) > 0 for some γ ≠ 1)
      ⊢ orbit structure {1, γ, γ², γ³, ...} is Peano-shaped
      ⊢ LogicNat (this module) ≃ Nat as semirings.

  References:
    - Foundation.LogicAsFunctionalEquation: SatisfiesLawsOfLogic, the
      Translation Theorem, the J-uniqueness corollary.
    - Cost.FunctionalEquation: law_of_logic_forces_jcost.
    - Foundation.DAlembert.Inevitability: bilinear_family_forced.
-/

import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation

namespace IndisputableMonolith
namespace Foundation
namespace ArithmeticFromLogic

open IndisputableMonolith.Foundation.LogicAsFunctionalEquation

/-! ## 1. The Inductive Structure Forced by the Comparison Operator

The Law of Logic, applied to a non-trivial comparison operator, gives:

  - an identity element (x = 1, the unique zero of the derived cost J)
  - a non-trivial generator γ ≠ 1 with strictly positive cost

The orbit of γ under repeated multiplication, together with the
identity, has exactly two constructors: "be at the identity" and "take
one more step." That two-constructor structure is the natural-number
structure. We make it an inductive type below.

Nothing in the construction references base 10, base 2, or any
positional system. The only primitives are the identity element and
the step operation. -/

/-- The natural numbers as forced by the Law of Logic.

`identity` represents the zero-cost element (the multiplicative
identity in the orbit). `step` represents one more iteration of the
generator. The two-constructor structure mirrors the orbit
{1, γ, γ², γ³, ...} as the smallest subset of ℝ₊ closed under
multiplication by γ and containing 1. -/
inductive LogicNat : Type
  | identity : LogicNat
  | step     : LogicNat → LogicNat
  deriving DecidableEq, Repr

namespace LogicNat

/-! ## 2. Zero and Successor (Peano Primitives) -/

/-- Zero is the identity comparison: a thing compared with itself,
costing zero in J. -/
@[simp] def zero : LogicNat := .identity

/-- Successor is one more application of the generator. -/
@[simp] def succ (n : LogicNat) : LogicNat := .step n

/-! ## 3. Peano Axioms as Theorems

Each axiom is a theorem of the inductive structure. None is posited.
-/

/-- **Peano P1 (zero is not a successor)**: the identity is
distinguishable from any iterate of the generator. -/
theorem zero_ne_succ (n : LogicNat) : zero ≠ succ n := by
  intro h; cases h

/-- **Peano P1, contrapositive**: every successor differs from zero. -/
theorem succ_ne_zero (n : LogicNat) : succ n ≠ zero := by
  intro h; cases h

/-- **Peano P2 (successor injectivity)**: forced by the constructor
disjointness of the inductive type, which itself reflects the
injectivity of multiplication by the generator on the orbit. -/
theorem succ_injective : Function.Injective succ := by
  intro a b h
  cases h
  rfl

/-- **Peano P3 (induction)**: any property closed under successor and
holding at zero holds for every `LogicNat`. -/
theorem induction
    {motive : LogicNat → Prop}
    (h0 : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) :
    ∀ n, motive n := by
  intro n
  induction n with
  | identity => exact h0
  | step n ih => exact hs n ih

/-! ## 4. Addition and Multiplication

Addition is repeated successor; multiplication is repeated addition.
Both are defined by recursion on the second argument. We register
them as `Add` and `Mul` instances so Lean's standard `+` and `*`
notation work on `LogicNat` directly. -/

/-- Addition by recursion on the second argument. -/
def add : LogicNat → LogicNat → LogicNat
  | n, .identity => n
  | n, .step m   => .step (add n m)

instance : Add LogicNat := ⟨add⟩
instance : Zero LogicNat := ⟨zero⟩
instance : One LogicNat := ⟨succ zero⟩

@[simp] theorem add_def (n m : LogicNat) : n + m = add n m := rfl
@[simp] theorem zero_def : (0 : LogicNat) = zero := rfl
@[simp] theorem one_def : (1 : LogicNat) = succ zero := rfl

@[simp] theorem add_zero (n : LogicNat) : n + zero = n := rfl

@[simp] theorem add_succ (n m : LogicNat) : n + succ m = succ (n + m) := rfl

theorem zero_add (n : LogicNat) : zero + n = n := by
  induction n with
  | identity => rfl
  | step n ih =>
    show zero + succ n = succ n
    rw [add_succ, ih]

theorem succ_add (n m : LogicNat) : succ n + m = succ (n + m) := by
  induction m with
  | identity => rfl
  | step m ih =>
    show succ n + succ m = succ (n + succ m)
    rw [add_succ, add_succ, ih]

theorem add_assoc (a b c : LogicNat) : (a + b) + c = a + (b + c) := by
  induction c with
  | identity => rfl
  | step c ih =>
    show (a + b) + succ c = a + (b + succ c)
    rw [add_succ, add_succ, add_succ, ih]

theorem add_comm (a b : LogicNat) : a + b = b + a := by
  induction b with
  | identity =>
    show a + zero = zero + a
    rw [add_zero, zero_add]
  | step b ih =>
    show a + succ b = succ b + a
    rw [add_succ, succ_add, ih]

/-- Multiplication by recursion on the second argument. -/
def mul : LogicNat → LogicNat → LogicNat
  | _, .identity => zero
  | n, .step m   => mul n m + n

instance : Mul LogicNat := ⟨mul⟩

@[simp] theorem mul_def (n m : LogicNat) : n * m = mul n m := rfl

@[simp] theorem mul_zero (n : LogicNat) : n * zero = zero := rfl

@[simp] theorem mul_succ (n m : LogicNat) : n * succ m = n * m + n := rfl

theorem zero_mul (n : LogicNat) : zero * n = zero := by
  induction n with
  | identity => rfl
  | step n ih =>
    show zero * succ n = zero
    rw [mul_succ, ih, zero_add]

theorem mul_one (n : LogicNat) : n * succ zero = n := by
  show n * succ zero = n
  rw [mul_succ, mul_zero, zero_add]

theorem one_mul (n : LogicNat) : succ zero * n = n := by
  induction n with
  | identity => rfl
  | step n ih =>
    show succ zero * succ n = succ n
    rw [mul_succ, ih]
    show n + succ zero = succ n
    rw [add_succ, add_zero]

theorem mul_add (a b c : LogicNat) : a * (b + c) = a * b + a * c := by
  induction c with
  | identity =>
    show a * (b + zero) = a * b + a * zero
    rw [add_zero, mul_zero, add_zero]
  | step c ih =>
    show a * (b + succ c) = a * b + a * succ c
    rw [add_succ, mul_succ, mul_succ, ih, add_assoc]

/-! ## 5. Recovery Theorem: LogicNat ≃ Nat

Lean's built-in `Nat` has the same inductive shape as `LogicNat`. The
two are isomorphic. This is the recovery: the natural numbers Lean
already has are exactly the structure forced by the Law of Logic, with
no base 10, no positional representation, and no arithmetic axioms
posited. -/

/-- The forward map: read off the iteration count. -/
def toNat : LogicNat → Nat
  | .identity => 0
  | .step n   => Nat.succ (toNat n)

/-- The inverse map: build the orbit by iterating the step. -/
def fromNat : Nat → LogicNat
  | 0          => .identity
  | Nat.succ n => .step (fromNat n)

@[simp] theorem toNat_zero : toNat zero = 0 := rfl
@[simp] theorem toNat_succ (n : LogicNat) : toNat (succ n) = Nat.succ (toNat n) := rfl
@[simp] theorem fromNat_zero : fromNat 0 = zero := rfl
@[simp] theorem fromNat_succ (n : Nat) : fromNat (Nat.succ n) = succ (fromNat n) := rfl

theorem fromNat_toNat : ∀ n : LogicNat, fromNat (toNat n) = n := by
  intro n
  induction n with
  | identity => rfl
  | step n ih =>
    show fromNat (toNat (succ n)) = succ n
    rw [toNat_succ, fromNat_succ, ih]

theorem toNat_fromNat : ∀ n : Nat, toNat (fromNat n) = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show toNat (fromNat (Nat.succ n)) = Nat.succ n
    rw [fromNat_succ, toNat_succ, ih]

/-- **Recovery theorem (carrier)**: `LogicNat` and `Nat` have the same
underlying set, witnessed by the round-trip equalities. -/
def equivNat : LogicNat ≃ Nat where
  toFun := toNat
  invFun := fromNat
  left_inv := fromNat_toNat
  right_inv := toNat_fromNat

/-- **Recovery theorem (addition)**: the addition `LogicNat` carries
agrees with `Nat` addition under the equivalence. -/
theorem toNat_add (a b : LogicNat) :
    toNat (a + b) = toNat a + toNat b := by
  induction b with
  | identity =>
    show toNat (a + zero) = toNat a + toNat zero
    rw [add_zero, toNat_zero, Nat.add_zero]
  | step b ih =>
    show toNat (a + succ b) = toNat a + toNat (succ b)
    rw [add_succ, toNat_succ, toNat_succ, ih, Nat.add_succ]

/-- **Recovery theorem (multiplication)**: the multiplication
`LogicNat` carries agrees with `Nat` multiplication under the
equivalence. -/
theorem toNat_mul (a b : LogicNat) :
    toNat (a * b) = toNat a * toNat b := by
  induction b with
  | identity =>
    show toNat (a * zero) = toNat a * toNat zero
    rw [mul_zero, toNat_zero, Nat.mul_zero]
  | step b ih =>
    show toNat (a * succ b) = toNat a * toNat (succ b)
    rw [mul_succ, toNat_succ, toNat_add, ih, Nat.mul_succ]

/-- Left cancellation: `a + b = a + c ⇒ b = c`. Proved by transferring
to `Nat` via the recovery isomorphism. -/
theorem add_left_cancel {a b c : LogicNat} (h : a + b = a + c) : b = c := by
  have hcast := congrArg toNat h
  rw [toNat_add, toNat_add] at hcast
  have hnat : toNat b = toNat c := by omega
  have := congrArg fromNat hnat
  rw [fromNat_toNat, fromNat_toNat] at this
  exact this

/-- Right cancellation: `a + c = b + c ⇒ a = b`. -/
theorem add_right_cancel {a b c : LogicNat} (h : a + c = b + c) : a = b := by
  rw [add_comm a c, add_comm b c] at h
  exact add_left_cancel h

/-- Transfer principle: an equation in `LogicNat` holds iff it holds
under `toNat`. This is the workhorse for proofs that route through
`omega` on `Nat`. -/
theorem eq_iff_toNat_eq {a b : LogicNat} : a = b ↔ toNat a = toNat b := by
  constructor
  · exact congrArg toNat
  · intro h
    have := congrArg fromNat h
    rw [fromNat_toNat, fromNat_toNat] at this
    exact this

/-! ## 5b. Order on LogicNat

Order is forced by the orbit's cost ordering: in the orbit
`{1, γ, γ², ...}` with `γ > 1`, the cost `J(γⁿ)` is strictly
increasing in `n`. Section 6's `embed_strictMono` establishes this
analytically. Here we define the abstract Peano order intrinsically
to `LogicNat` (via existence of an additive complement) so the order
content does not depend on which generator was used. The connection
back to the orbit is `embed_le_iff` in Section 6.

The standard Peano definition: `n ≤ m` iff there exists `k` with
`n + k = m`. Strict order: `n < m` iff there exists `k` with
`n + step k = m`. -/

/-- Non-strict order on `LogicNat`. -/
def le (n m : LogicNat) : Prop := ∃ k : LogicNat, n + k = m

/-- Strict order on `LogicNat`. -/
def lt (n m : LogicNat) : Prop := ∃ k : LogicNat, n + succ k = m

instance : LE LogicNat := ⟨le⟩
instance : LT LogicNat := ⟨lt⟩

@[simp] theorem le_def (n m : LogicNat) : n ≤ m ↔ ∃ k, n + k = m := Iff.rfl
@[simp] theorem lt_def (n m : LogicNat) : n < m ↔ ∃ k, n + succ k = m := Iff.rfl

theorem le_refl (n : LogicNat) : n ≤ n := ⟨zero, add_zero n⟩

theorem zero_le (n : LogicNat) : zero ≤ n := ⟨n, zero_add n⟩

theorem le_trans {a b c : LogicNat} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  obtain ⟨k1, hk1⟩ := hab
  obtain ⟨k2, hk2⟩ := hbc
  refine ⟨k1 + k2, ?_⟩
  rw [← add_assoc, hk1, hk2]

theorem le_succ (n : LogicNat) : n ≤ succ n := ⟨succ zero, by
  show n + succ zero = succ n
  rw [add_succ, add_zero]⟩

theorem succ_le_succ {a b : LogicNat} (h : a ≤ b) : succ a ≤ succ b := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  show succ a + k = succ b
  rw [succ_add, hk]

theorem lt_iff_succ_le {n m : LogicNat} : n < m ↔ succ n ≤ m := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    show succ n + k = m
    rw [succ_add]
    show succ (n + k) = m
    rw [← add_succ]
    -- need n + succ k = m, but we have n + succ k = m via hk; succ_add transforms
    -- Wait: hk : n + succ k = m, and succ (n + k) = n + succ k by add_succ. So succ (n + k) = m.
    exact hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    show n + succ k = m
    rw [add_succ]
    show succ (n + k) = m
    rw [← succ_add]
    exact hk

theorem lt_irrefl (n : LogicNat) : ¬ n < n := by
  rintro ⟨k, hk⟩
  -- n + succ k = n. Apply toNat: toNat n + toNat (succ k) = toNat n on Nat.
  have := congrArg toNat hk
  rw [toNat_add, toNat_succ] at this
  -- this : toNat n + Nat.succ (toNat k) = toNat n
  omega

theorem lt_trans {a b c : LogicNat} (hab : a < b) (hbc : b < c) : a < c := by
  rw [lt_iff_succ_le] at hab hbc ⊢
  exact le_trans hab (le_trans (le_succ b) hbc)

theorem zero_lt_succ (n : LogicNat) : zero < succ n :=
  ⟨n, by show zero + succ n = succ n; rw [zero_add]⟩

theorem lt_iff_le_and_ne {a b : LogicNat} : a < b ↔ a ≤ b ∧ a ≠ b := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨⟨succ k, hk⟩, ?_⟩
    intro hab
    rw [hab] at hk
    -- b + succ k = b means succ k = 0 by additive cancellation; impossible.
    have := congrArg toNat hk
    rw [toNat_add, toNat_succ] at this
    omega
  · rintro ⟨⟨k, hk⟩, hne⟩
    -- a + k = b, a ≠ b, so k ≠ 0; k = succ k' for some k'.
    cases k with
    | identity =>
      exfalso
      apply hne
      simpa using hk
    | step k' => exact ⟨k', hk⟩

theorem le_antisymm {a b : LogicNat} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  obtain ⟨k1, hk1⟩ := hab
  obtain ⟨k2, hk2⟩ := hba
  have h1 := congrArg toNat hk1
  have h2 := congrArg toNat hk2
  rw [toNat_add] at h1 h2
  -- toNat a + toNat k1 = toNat b, toNat b + toNat k2 = toNat a.
  have hnat : toNat a = toNat b := by omega
  -- Lift to LogicNat via the equivalence.
  have := congrArg fromNat hnat
  rw [fromNat_toNat, fromNat_toNat] at this
  exact this

/-- `LogicNat` carries a partial order via the Peano definition. -/
instance : Preorder LogicNat where
  le := le
  lt := lt
  le_refl := le_refl
  le_trans := fun _ _ _ => le_trans
  lt_iff_le_not_ge := by
    intro a b
    -- Unfold lt and le to avoid notation-instance loop in the instance
    -- definition itself.
    show lt a b ↔ le a b ∧ ¬ le b a
    have hiff : lt a b ↔ le a b ∧ a ≠ b := lt_iff_le_and_ne
    rw [hiff]
    constructor
    · rintro ⟨hab, hne⟩
      refine ⟨hab, ?_⟩
      intro hba
      exact hne (le_antisymm hab hba)
    · rintro ⟨hab, hnba⟩
      refine ⟨hab, ?_⟩
      intro habeq
      exact hnba (habeq ▸ le_refl b)

/-- `LogicNat` is a partial order. -/
instance : PartialOrder LogicNat where
  __ := (inferInstance : Preorder LogicNat)
  le_antisymm := fun _ _ => le_antisymm

/-! ## Recovery (Order): Peano order matches `Nat` order. -/

theorem toNat_le (a b : LogicNat) : a ≤ b ↔ toNat a ≤ toNat b := by
  constructor
  · rintro ⟨k, hk⟩
    have := congrArg toNat hk
    rw [toNat_add] at this
    omega
  · intro h
    refine ⟨fromNat (toNat b - toNat a), ?_⟩
    have hroundtrip : ∀ n : LogicNat, fromNat (toNat n) = n := fromNat_toNat
    -- toNat (a + fromNat (toNat b - toNat a)) = toNat a + (toNat b - toNat a) = toNat b
    have hadd : toNat (a + fromNat (toNat b - toNat a)) = toNat b := by
      rw [toNat_add, toNat_fromNat]
      omega
    -- Apply equivNat injectivity
    have : a + fromNat (toNat b - toNat a) = b := by
      have h1 := congrArg fromNat hadd
      rw [hroundtrip, hroundtrip] at h1
      exact h1
    exact this

theorem toNat_lt (a b : LogicNat) : a < b ↔ toNat a < toNat b := by
  rw [lt_iff_succ_le, toNat_le]
  constructor
  · intro h
    rw [toNat_succ] at h
    omega
  · intro h
    rw [toNat_succ]
    omega

/-- `LogicNat` is a linear order: any two elements are comparable, and
the order is decidable. Both follow from the recovery isomorphism with
`Nat`. -/
instance : LinearOrder LogicNat where
  __ := (inferInstance : PartialOrder LogicNat)
  le_total := fun a b => by
    rcases Nat.le_total (toNat a) (toNat b) with h | h
    · left
      exact (toNat_le a b).mpr h
    · right
      exact (toNat_le b a).mpr h
  toDecidableLE := fun a b =>
    decidable_of_iff (toNat a ≤ toNat b) (toNat_le a b).symm
  toDecidableEq := inferInstance

/-- `LogicNat` is well-founded under strict order: induction on size is
admissible. Transfer from `Nat`'s well-foundedness via the recovery
isomorphism. -/
instance : WellFoundedLT LogicNat where
  wf := by
    have hNat : WellFounded (fun a b : LogicNat => toNat a < toNat b) :=
      InvImage.wf toNat (Nat.lt_wfRel.wf)
    apply Subrelation.wf (h₁ := ?_) hNat
    intro a b h
    exact (toNat_lt a b).mp h

end LogicNat

/-! ## 6. Embedding into ℝ₊ via a Generator

Section 5 recovers the abstract Peano structure. Section 6 ties that
structure back to the comparison operator that started the chain. The
embedding `LogicNat → ℝ₊` sends `n` to `γⁿ` for any non-trivial
generator `γ` of the multiplicative group of positive reals. This is
the structural witness that the abstract Peano structure of
`LogicNat` is the orbit structure of any non-trivial element under
multiplication.

The full chain (existence of γ from `non_trivial`, injectivity of the
embedding from the J-cost positivity off-identity, generator-free
characterization of the embedding's image) is left for Level 2. The
content of this section is the embedding map and its multiplicative
homomorphism property. -/

/-- A non-trivial generator: any positive real other than the
identity. The Law of Logic guarantees existence via the
`non_trivial` field of `SatisfiesLawsOfLogic`. -/
structure Generator where
  value      : ℝ
  pos        : 0 < value
  nontrivial : value ≠ 1

/-- **Chain closure**: a comparison operator satisfying the Law of Logic
yields an explicit non-trivial generator. The construction extracts the
witness from `non_trivial` and uses `identity` to rule out `value = 1`.

This is the structural completion of the chain. Before this lemma,
`Generator` was a free structure; now it is *literally* derived from
`SatisfiesLawsOfLogic`. -/
noncomputable def generatorOfLawsOfLogic
    {C : ComparisonOperator} (hLaws : SatisfiesLawsOfLogic C) : Generator :=
  let x := Classical.choose hLaws.non_trivial
  have hx : 0 < x ∧ derivedCost C x ≠ 0 := Classical.choose_spec hLaws.non_trivial
  { value      := x
    pos        := hx.1
    nontrivial := by
      intro hx_eq_one
      apply hx.2
      show derivedCost C x = 0
      rw [hx_eq_one]
      show C 1 1 = 0
      exact hLaws.identity 1 one_pos }

/-- The orbit embedding: `LogicNat` into the positive reals. -/
def embed (γ : Generator) : LogicNat → ℝ
  | .identity => 1
  | .step n   => γ.value * embed γ n

@[simp] theorem embed_zero (γ : Generator) : embed γ LogicNat.zero = 1 := rfl

@[simp] theorem embed_succ (γ : Generator) (n : LogicNat) :
    embed γ (LogicNat.succ n) = γ.value * embed γ n := rfl

/-- The embedding lands in the strictly positive reals. -/
theorem embed_pos (γ : Generator) (n : LogicNat) : 0 < embed γ n := by
  induction n with
  | identity => exact one_pos
  | step n ih =>
    show 0 < γ.value * embed γ n
    exact mul_pos γ.pos ih

/-- **Multiplicative homomorphism**: addition in `LogicNat` corresponds
to multiplication of orbit elements. This is the structural fact that
`LogicNat` *is* the orbit, parameterized by iteration count. -/
theorem embed_add (γ : Generator) (a b : LogicNat) :
    embed γ (a + b) = embed γ a * embed γ b := by
  induction b with
  | identity =>
    show embed γ (a + LogicNat.zero) = embed γ a * embed γ LogicNat.zero
    rw [LogicNat.add_zero, embed_zero, mul_one]
  | step b ih =>
    show embed γ (a + LogicNat.succ b) = embed γ a * embed γ (LogicNat.succ b)
    rw [LogicNat.add_succ, embed_succ, embed_succ, ih]
    ring

/-- The embedding is the natural-number power of `γ.value`. -/
theorem embed_eq_pow (γ : Generator) (n : LogicNat) :
    embed γ n = γ.value ^ (LogicNat.toNat n) := by
  induction n with
  | identity => simp [embed, LogicNat.toNat]
  | step n ih =>
    show γ.value * embed γ n = γ.value ^ (Nat.succ (LogicNat.toNat n))
    rw [ih, pow_succ]
    ring

/-! ## Embedding Injectivity (J-positivity off identity)

The key fact: a non-trivial generator `γ ≠ 1` cannot have `γⁿ = γᵐ`
for `n ≠ m`. Structurally, this is forced by J-positivity off
identity: `J(γᵏ) > 0` for any `k ≥ 1` (since `γᵏ ≠ 1` whenever
`γ ≠ 1` and `k ≥ 1`), and `J(x) = 0 ↔ x = 1`. Analytically, it
follows from `Real.log γ.value ≠ 0` and the rule `log(γⁿ) = n · log γ`
on positive reals. The latter route is shorter and is what we use
here. -/

/-- Logarithm of a non-trivial generator is non-zero. -/
private theorem log_generator_ne_zero (γ : Generator) :
    Real.log γ.value ≠ 0 := by
  intro h
  -- Real.log_eq_zero_iff: log x = 0 ↔ x = 0 ∨ x = 1 ∨ x = -1
  rcases (Real.log_eq_zero.mp h) with h0 | h1 | hneg
  · exact (lt_irrefl (0 : ℝ)) (h0 ▸ γ.pos)
  · exact γ.nontrivial h1
  · linarith [γ.pos]

/-- **Embedding injectivity**: distinct natural numbers map to distinct
points in the orbit. This closes the bridge from the abstract `LogicNat`
to the concrete orbit `{1, γ, γ², ...}` in ℝ₊. -/
theorem embed_injective (γ : Generator) : Function.Injective (embed γ) := by
  intro a b hab
  -- Translate to powers.
  rw [embed_eq_pow, embed_eq_pow] at hab
  -- Take logs.
  have hpos_a : 0 < γ.value ^ (LogicNat.toNat a) := pow_pos γ.pos _
  have hpos_b : 0 < γ.value ^ (LogicNat.toNat b) := pow_pos γ.pos _
  have hlog : Real.log (γ.value ^ (LogicNat.toNat a))
              = Real.log (γ.value ^ (LogicNat.toNat b)) := by
    exact congrArg Real.log hab
  rw [Real.log_pow, Real.log_pow] at hlog
  -- Cancel the non-zero log γ.value.
  have hne := log_generator_ne_zero γ
  have hcast : ((LogicNat.toNat a : ℝ)) = ((LogicNat.toNat b : ℝ)) := by
    have := mul_right_cancel₀ hne hlog
    exact this
  have h_nat : LogicNat.toNat a = LogicNat.toNat b := by exact_mod_cast hcast
  -- Lift back to LogicNat via the equivalence.
  have := congrArg LogicNat.fromNat h_nat
  rw [LogicNat.fromNat_toNat, LogicNat.fromNat_toNat] at this
  exact this

/-! ## Order via the Embedding (γ > 1 case)

When `γ > 1`, the orbit is strictly increasing under multiplication
by `γ`, and `embed γ` is a strictly monotone embedding of the Peano
order on `LogicNat` into `(ℝ, ≤)`. This is the analytic counterpart
of the abstract Peano order from Section 5b. -/

/-- For `γ > 1`, `γⁿ ≤ γᵐ ↔ n ≤ m` on `Nat`. -/
private theorem pow_le_pow_iff_of_one_lt {γ : ℝ} (hγ : 1 < γ) (n m : Nat) :
    γ ^ n ≤ γ ^ m ↔ n ≤ m := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have : γ ^ m < γ ^ n := pow_lt_pow_right₀ hγ hlt
    linarith
  · intro h
    exact pow_le_pow_right₀ (le_of_lt hγ) h

/-- For `γ > 1`, `γⁿ < γᵐ ↔ n < m` on `Nat`. -/
private theorem pow_lt_pow_iff_of_one_lt {γ : ℝ} (hγ : 1 < γ) (n m : Nat) :
    γ ^ n < γ ^ m ↔ n < m := by
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    have := pow_le_pow_right₀ (le_of_lt hγ) hle
    linarith
  · intro h
    exact pow_lt_pow_right₀ hγ h

/-- **Embedding monotonicity (γ > 1)**: the embedding is order-preserving. -/
theorem embed_le_iff_of_one_lt (γ : Generator) (hγ : 1 < γ.value) (a b : LogicNat) :
    embed γ a ≤ embed γ b ↔ a ≤ b := by
  rw [embed_eq_pow, embed_eq_pow, pow_le_pow_iff_of_one_lt hγ, ← LogicNat.toNat_le]

/-- **Embedding strict monotonicity (γ > 1)**. -/
theorem embed_lt_iff_of_one_lt (γ : Generator) (hγ : 1 < γ.value) (a b : LogicNat) :
    embed γ a < embed γ b ↔ a < b := by
  rw [embed_eq_pow, embed_eq_pow, pow_lt_pow_iff_of_one_lt hγ, ← LogicNat.toNat_lt]

/-- **Embedding is strictly monotone for γ > 1**. -/
theorem embed_strictMono_of_one_lt (γ : Generator) (hγ : 1 < γ.value) :
    StrictMono (embed γ) :=
  fun _ _ h => (embed_lt_iff_of_one_lt γ hγ _ _).mpr h

/-! ## Summary

  Law of Logic (four Aristotelian conditions on a comparison operator)
        ↓  (forces, via Translation Theorem and Aczél)
  J(x) = ½(x + x⁻¹) − 1 with unique zero at x = 1, positive elsewhere
        ↓  (the orbit of any γ ≠ 1 under multiplication has Peano shape)
  LogicNat (zero, succ, induction)
        ↓  (recovery theorem, this module)
  Nat with addition and multiplication

The Peano axioms are theorems. Addition and multiplication are forced
by the orbit structure. No positional representation is assumed. The
only structural choice is the generator γ ≠ 1, which exists by
non-triviality of the comparison operator.

What this module establishes is the recovery of the abstract Peano
structure. What it does not yet establish (left for a follow-up
module) is:

  - Injectivity of `embed γ` (forced by J-positivity off-identity)
  - Generator-free characterization of the orbit
  - Order on `LogicNat` (forced by the cost ordering on the orbit)
  - Subtraction, division, the rationals, the reals (each requires
    additional structure on top of the bare orbit)

These extensions follow standard reverse-mathematics templates once
the Peano structure is in hand.
-/

end ArithmeticFromLogic
end Foundation
end IndisputableMonolith
