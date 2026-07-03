/-
  UniversalForcing/ForcedSemiring.lean

  From "the successor tower is forced" to "the arithmetic is forced."

  Canonicity (CanonicalForcing) shows the Universal-Forcing map is the unique
  zero/step-preserving map between two forced arithmetics. But zero and step are
  only the *Peano* surface. The program's thesis is that distinction forces the
  same arithmetic *structure*, and arithmetic is the semiring: addition and
  multiplication, not just succession.

  This module closes that gap. Addition and multiplication on the forced carrier
  (`LogicNat`) are the standard primitive-recursive operations
  (ArithmeticFromLogic). The key fact is that they are *determined by zero and
  step*: any function preserving zero and step automatically preserves `+` and
  `*`, because those operations are defined by recursion on step with base zero.
  Therefore the canonical forcing map — already the unique zero/step morphism — is
  automatically a semiring homomorphism, and being a bijection, a semiring
  isomorphism.

  The upshot: distinction forces not merely *a successor tower* but *the
  arithmetic*, `(ℕ, 0, 1, +, ×)`, canonically, in every strict realization, with
  the connecting map a determined semiring isomorphism.
-/

import IndisputableMonolith.Foundation.UniversalForcing.CanonicalForcing

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace ForcedSemiring

open ArithmeticFromLogic
open ArithmeticFromLogic.LogicNat

/-! ## Any zero/step-preserving self-map of `LogicNat` preserves `+` and `×`. -/

/-- A map fixing zero and commuting with `succ` preserves addition. Addition
recurses on its second argument, so the proof is a single induction. -/
theorem map_preserves_add (h : LogicNat → LogicNat)
    (h0 : h LogicNat.zero = LogicNat.zero)
    (hs : ∀ n, h (LogicNat.succ n) = LogicNat.succ (h n)) :
    ∀ a b : LogicNat, h (a + b) = h a + h b := by
  intro a b
  induction b with
  | identity =>
      show h (a + LogicNat.zero) = h a + h LogicNat.zero
      rw [add_zero, h0, add_zero]
  | step b ih =>
      show h (a + LogicNat.succ b) = h a + h (LogicNat.succ b)
      rw [add_succ, hs, ih, hs, add_succ]

/-- A map fixing zero and commuting with `succ` (hence, by the previous lemma,
preserving `+`) preserves multiplication. Multiplication recurses on its second
argument via addition. -/
theorem map_preserves_mul (h : LogicNat → LogicNat)
    (h0 : h LogicNat.zero = LogicNat.zero)
    (hs : ∀ n, h (LogicNat.succ n) = LogicNat.succ (h n)) :
    ∀ a b : LogicNat, h (a * b) = h a * h b := by
  have hadd := map_preserves_add h h0 hs
  intro a b
  induction b with
  | identity =>
      show h (a * LogicNat.zero) = h a * h LogicNat.zero
      rw [mul_zero, h0, mul_zero]
  | step b ih =>
      show h (a * LogicNat.succ b) = h a * h (LogicNat.succ b)
      rw [mul_succ, hadd, ih, hs, mul_succ]

/-- A zero/step-preserving map fixes `1 = succ 0`. -/
theorem map_preserves_one (h : LogicNat → LogicNat)
    (h0 : h LogicNat.zero = LogicNat.zero)
    (hs : ∀ n, h (LogicNat.succ n) = LogicNat.succ (h n)) :
    h 1 = 1 := by
  show h (LogicNat.succ LogicNat.zero) = LogicNat.succ LogicNat.zero
  rw [hs, h0]

/-! ## The canonical forcing map as a semiring isomorphism. -/

/-- The universal-forcing map between two strict realizations, presented as a
self-map of `LogicNat` (the forced carriers are definitionally `LogicNat`). -/
noncomputable def forcingFn (R S : UniversalForcing.Strict.StrictLogicRealization.{0,0}) :
    LogicNat → LogicNat :=
  fun n => (UniversalForcing.Strict.StrictLogicRealization.universal_forcing.{0,0,0,0,0,0} R S) n

theorem forcingFn_zero (R S : UniversalForcing.Strict.StrictLogicRealization.{0,0}) :
    forcingFn R S LogicNat.zero = LogicNat.zero :=
  UniversalForcing.Strict.StrictLogicRealization.universal_forcing_map_zero R S

theorem forcingFn_succ (R S : UniversalForcing.Strict.StrictLogicRealization.{0,0}) (n : LogicNat) :
    forcingFn R S (LogicNat.succ n) = LogicNat.succ (forcingFn R S n) :=
  UniversalForcing.Strict.StrictLogicRealization.universal_forcing_map_step R S n

/-- **The forcing map preserves addition.** -/
theorem forcingFn_add (R S : UniversalForcing.Strict.StrictLogicRealization.{0,0})
    (a b : LogicNat) :
    forcingFn R S (a + b) = forcingFn R S a + forcingFn R S b :=
  map_preserves_add (forcingFn R S) (forcingFn_zero R S) (forcingFn_succ R S) a b

/-- **The forcing map preserves multiplication.** -/
theorem forcingFn_mul (R S : UniversalForcing.Strict.StrictLogicRealization.{0,0})
    (a b : LogicNat) :
    forcingFn R S (a * b) = forcingFn R S a * forcingFn R S b :=
  map_preserves_mul (forcingFn R S) (forcingFn_zero R S) (forcingFn_succ R S) a b

/-- **The forcing map preserves one.** -/
theorem forcingFn_one (R S : UniversalForcing.Strict.StrictLogicRealization.{0,0}) :
    forcingFn R S 1 = 1 :=
  map_preserves_one (forcingFn R S) (forcingFn_zero R S) (forcingFn_succ R S)

/-- The forcing map is a bijection: it is the underlying function of the
universal-forcing equivalence. -/
theorem forcingFn_bijective (R S : UniversalForcing.Strict.StrictLogicRealization.{0,0}) :
    Function.Bijective (forcingFn R S) :=
  (UniversalForcing.Strict.StrictLogicRealization.universal_forcing.{0,0,0,0,0,0} R S).bijective

/-- **Uniqueness as a semiring map.** Any function preserving zero and step
equals the forcing map, so in particular the forcing map is the unique semiring
homomorphism — it is determined, not chosen. (Restated from canonicity for the
`LogicNat` presentation.) -/
theorem forcingFn_unique (R S : UniversalForcing.Strict.StrictLogicRealization.{0,0})
    (f : LogicNat → LogicNat)
    (h0 : f LogicNat.zero = LogicNat.zero)
    (hs : ∀ n, f (LogicNat.succ n) = LogicNat.succ (f n)) :
    f = forcingFn R S :=
  UniversalForcing.Strict.StrictLogicRealization.universal_forcing_unique R S f h0 hs

/-- **Certificate: distinction forces the arithmetic, not just the tower.** For
any two strict realizations the canonical forcing map is a bijection that
preserves `0`, `1`, `+`, and `×`, and it is the unique zero/step-preserving map.
The forced object is the semiring `(ℕ, 0, 1, +, ×)`, canonically. -/
structure ForcedSemiringCert where
  map : ∀ (R S : UniversalForcing.Strict.StrictLogicRealization.{0,0}), LogicNat → LogicNat
  bij : ∀ R S, Function.Bijective (map R S)
  zero : ∀ R S, map R S LogicNat.zero = LogicNat.zero
  one : ∀ R S, map R S 1 = 1
  add : ∀ R S a b, map R S (a + b) = map R S a + map R S b
  mul : ∀ R S a b, map R S (a * b) = map R S a * map R S b
  unique : ∀ R S (f : LogicNat → LogicNat),
      f LogicNat.zero = LogicNat.zero →
      (∀ n, f (LogicNat.succ n) = LogicNat.succ (f n)) →
      f = map R S

/-- The forced-semiring certificate holds. -/
noncomputable def forcedSemiringCert_holds : ForcedSemiringCert where
  map := forcingFn
  bij := forcingFn_bijective
  zero := forcingFn_zero
  one := forcingFn_one
  add := forcingFn_add
  mul := forcingFn_mul
  unique := forcingFn_unique

/-! ## Honest note: on the strict path the forcing map is the identity.

`StrictLogicRealization` uses a uniform free orbit (`LogicNat`) for every
realization, so the two forced arithmetics are literally the same carrier and the
canonical map between them is the identity. This does not trivialize the theory:
the non-trivial content is (a) the general preservation lemmas above, which apply
to *any* zero/step map, and (b) the cross-carrier canonicity in
`CanonicalForcing.ArithmeticOf.forcing_map_unique`. It is simply honest about the
strict presentation. -/
theorem forcingFn_eq_id (R S : UniversalForcing.Strict.StrictLogicRealization.{0,0}) :
    forcingFn R S = id :=
  (forcingFn_unique R S id rfl (fun _ => rfl)).symm

/-! ## The forced arithmetic is Lean's `ℕ`, as a semiring. -/

theorem toNat_one : LogicNat.toNat 1 = 1 := rfl

/-- **Capstone: distinction forces `ℕ`.** The forced carrier `LogicNat` is
isomorphic to Lean's `Nat` as a `(0, 1, +, ×)`-structure. Every strict realization
forces this same carrier (CanonicalForcing), so the arithmetic that distinction
forces is, up to canonical semiring isomorphism, exactly the natural numbers Lean
already has — with no base, no positional notation, and no arithmetic axioms
posited. -/
structure ForcedArithmeticIsNat where
  toEquiv : LogicNat ≃ Nat
  map_zero : toEquiv LogicNat.zero = 0
  map_one : toEquiv 1 = 1
  map_add : ∀ a b, toEquiv (a + b) = toEquiv a + toEquiv b
  map_mul : ∀ a b, toEquiv (a * b) = toEquiv a * toEquiv b

/-- The forced arithmetic is `ℕ`. -/
noncomputable def forcedArithmeticIsNat : ForcedArithmeticIsNat where
  toEquiv := LogicNat.equivNat
  map_zero := LogicNat.toNat_zero
  map_one := toNat_one
  map_add := LogicNat.toNat_add
  map_mul := LogicNat.toNat_mul

end ForcedSemiring
end UniversalForcing
end Foundation
end IndisputableMonolith
