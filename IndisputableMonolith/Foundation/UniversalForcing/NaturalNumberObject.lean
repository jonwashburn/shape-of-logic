import IndisputableMonolith.Foundation.UniversalForcing
import IndisputableMonolith.Foundation.UniversalForcing.Strict.DiscreteBoolean

/-!
  NaturalNumberObject.lean

  Lawvere natural-number object characterization of the forced arithmetic.

  This module makes precise the categorical sense in which the Law of Logic
  forces the natural numbers. The Lawvere characterization is:
  a triple `(N, z, s)` is a *natural-number object* if for every triple
  `(X, x, f)` with `x : X` and `f : X → X` there exists a unique map
  `h : N → X` satisfying `h z = x` and `h ∘ s = f ∘ h`.

  This is the statement "ℕ is the initial pointed endomap algebra" and it is
  what "ℕ" means in any categorical foundation that does not presuppose ℕ.

  We prove:

  * `LogicNat` with `identity`/`step` is a natural-number object.
  * Every realization's forced arithmetic is a natural-number object.
  * Any two natural-number objects are canonically isomorphic.
  * The strict Boolean realization carrier collapses to the parity image
    `Nat.bodd ∘ toNat`, but the iteration object is unchanged.

  The last point is the formal answer to the critic's worry: "you did not
  derive ℕ; you smuggled in iteration-counting." The iteration object is
  the natural-number object in the Lawvere sense, and it is the same in
  every realization, including the discrete Boolean one whose carrier
  contains only two elements.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing

open ArithmeticFromLogic

universe u

/-! ## Lawvere natural-number object property -/

/-- A triple `(N, z, s)` is a Lawvere natural-number object: for every
target pointed endomap `(X, x, f)`, primitive recursion exists and is unique.

This characterization makes no reference to `Nat`. It is the universal
property that any Peano structure must satisfy. The field name `recursor`
avoids the reserved `rec` symbol used for auto-generated structure recursors. -/
structure IsNaturalNumberObject {N : Type u} (z : N) (s : N → N) where
  recursor : ∀ {X : Type u}, X → (X → X) → N → X
  recursor_zero : ∀ {X : Type u} (x : X) (f : X → X), recursor x f z = x
  recursor_step : ∀ {X : Type u} (x : X) (f : X → X) (n : N),
    recursor x f (s n) = f (recursor x f n)
  recursor_unique : ∀ {X : Type u} (x : X) (f : X → X) (h : N → X),
    h z = x → (∀ n, h (s n) = f (h n)) → ∀ n, h n = recursor x f n

namespace IsNaturalNumberObject

variable {N : Type u} {z : N} {s : N → N}

/-- The Peano object carried by a natural-number object. -/
def toPeano (_h : IsNaturalNumberObject z s) : PeanoObject where
  carrier := N
  zero := z
  step := s

/-- Initiality of an NNO in the category of pointed endomap algebras. -/
def isInitial (h : IsNaturalNumberObject z s) :
    PeanoObject.IsInitial (toPeano h) where
  lift := fun B =>
    { toFun := h.recursor B.zero B.step
      map_zero := h.recursor_zero B.zero B.step
      map_step := fun n => h.recursor_step B.zero B.step n }
  uniq := by
    intro B f g
    funext n
    have hf := h.recursor_unique B.zero B.step f.toFun f.map_zero f.map_step n
    have hg := h.recursor_unique B.zero B.step g.toFun g.map_zero g.map_step n
    rw [hf, hg]

end IsNaturalNumberObject

/-! ## `LogicNat` is a natural-number object -/

/-- `LogicNat` with `identity` and `step` is a Lawvere natural-number object. -/
def logicNat_isNNO :
    IsNaturalNumberObject (N := LogicNat) LogicNat.identity LogicNat.step where
  recursor := fun {X} x f => ArithmeticOf.logicNatFold ⟨X, x, f⟩
  recursor_zero := fun _ _ => rfl
  recursor_step := fun _ _ _ => rfl
  recursor_unique := by
    intro X x f h hz hs n
    induction n with
    | identity => exact hz
    | step n ih =>
        calc
          h (LogicNat.step n) = f (h n) := hs n
          _ = f (ArithmeticOf.logicNatFold ⟨X, x, f⟩ n) := by rw [ih]
          _ = ArithmeticOf.logicNatFold ⟨X, x, f⟩ (LogicNat.step n) := rfl

/-! ## Forced arithmetic of every realization is a natural-number object -/

/-- The natural-number object structure on a realization's iteration orbit.
Provided by transport from `LogicNat` through the realization's certified
orbit equivalence. The universe of the NNO is the carrier universe of the
realization. -/
noncomputable def realizationOrbit_isNNO.{u₁, v₁} (R : LogicRealization.{u₁, v₁}) :
    IsNaturalNumberObject (N := R.Orbit) R.orbitZero R.orbitStep where
  recursor := fun {X} x f n =>
    @ArithmeticOf.logicNatFold.{u₁} ⟨X, x, f⟩ (R.orbitEquivLogicNat n)
  recursor_zero := fun {X} x f => by
    show @ArithmeticOf.logicNatFold.{u₁} ⟨X, x, f⟩ (R.orbitEquivLogicNat R.orbitZero) = x
    rw [R.orbitEquiv_zero]
    rfl
  recursor_step := fun {X} x f n => by
    show @ArithmeticOf.logicNatFold.{u₁} ⟨X, x, f⟩ (R.orbitEquivLogicNat (R.orbitStep n)) =
      f (@ArithmeticOf.logicNatFold.{u₁} ⟨X, x, f⟩ (R.orbitEquivLogicNat n))
    rw [R.orbitEquiv_step]
    rfl
  recursor_unique := by
    intro X x f h hz hs n
    have hlogic_zero :
        (h ∘ R.orbitEquivLogicNat.symm) LogicNat.zero = x := by
      simp only [Function.comp_apply]
      have hsymm0 : R.orbitEquivLogicNat.symm LogicNat.zero = R.orbitZero := by
        apply R.orbitEquivLogicNat.injective
        simp [R.orbitEquiv_zero]
      rw [hsymm0]
      exact hz
    have hlogic_step : ∀ k,
        (h ∘ R.orbitEquivLogicNat.symm) (LogicNat.step k) =
          f ((h ∘ R.orbitEquivLogicNat.symm) k) := by
      intro k
      simp only [Function.comp_apply]
      have hsymm_step :
          R.orbitEquivLogicNat.symm (LogicNat.step k) =
            R.orbitStep (R.orbitEquivLogicNat.symm k) := by
        apply R.orbitEquivLogicNat.injective
        rw [R.orbitEquiv_step]
        simp
      rw [hsymm_step]
      exact hs (R.orbitEquivLogicNat.symm k)
    have huniq :
        ∀ k, (h ∘ R.orbitEquivLogicNat.symm) k =
          @ArithmeticOf.logicNatFold.{u₁} ⟨X, x, f⟩ k := by
      intro k
      induction k with
      | identity => exact hlogic_zero
      | step k ih =>
          calc
            (h ∘ R.orbitEquivLogicNat.symm) (LogicNat.step k)
                = f ((h ∘ R.orbitEquivLogicNat.symm) k) := hlogic_step k
            _ = f (@ArithmeticOf.logicNatFold.{u₁} ⟨X, x, f⟩ k) := by rw [ih]
            _ = @ArithmeticOf.logicNatFold.{u₁} ⟨X, x, f⟩ (LogicNat.step k) := rfl
    have hh : h n = (h ∘ R.orbitEquivLogicNat.symm) (R.orbitEquivLogicNat n) := by
      simp [Function.comp_apply]
    rw [hh, huniq]

/-- Convenience alias: the forced arithmetic of every realization is a Lawvere
natural-number object. The forced arithmetic is by definition the realization
orbit, so this is the same statement as `realizationOrbit_isNNO`. -/
noncomputable def forcedArithmetic_isNNO.{u₁, v₁} (R : LogicRealization.{u₁, v₁}) :
    IsNaturalNumberObject
      (N := (arithmeticOf R).peano.carrier)
      (arithmeticOf R).peano.zero
      (arithmeticOf R).peano.step :=
  realizationOrbit_isNNO R

/-! ## Uniqueness up to canonical isomorphism -/

/-- Any two natural-number objects are canonically equivalent. This is the
Lawvere statement that the natural-number object is unique up to unique
isomorphism. -/
def IsNaturalNumberObject.equiv
    {N₁ N₂ : Type u} {z₁ : N₁} {s₁ : N₁ → N₁} {z₂ : N₂} {s₂ : N₂ → N₂}
    (h₁ : IsNaturalNumberObject z₁ s₁) (h₂ : IsNaturalNumberObject z₂ s₂) :
    N₁ ≃ N₂ where
  toFun := h₁.recursor z₂ s₂
  invFun := h₂.recursor z₁ s₁
  left_inv := by
    intro n
    have hcomp_zero : (h₂.recursor z₁ s₁) ((h₁.recursor z₂ s₂) z₁) = z₁ := by
      rw [h₁.recursor_zero, h₂.recursor_zero]
    have hcomp_step : ∀ k,
        (h₂.recursor z₁ s₁) ((h₁.recursor z₂ s₂) (s₁ k)) =
          s₁ ((h₂.recursor z₁ s₁) ((h₁.recursor z₂ s₂) k)) := by
      intro k
      rw [h₁.recursor_step, h₂.recursor_step]
    have hid_zero : (id : N₁ → N₁) z₁ = z₁ := rfl
    have hid_step : ∀ k, (id : N₁ → N₁) (s₁ k) = s₁ ((id : N₁ → N₁) k) := by
      intro k; rfl
    have huniq_id := h₁.recursor_unique z₁ s₁ id hid_zero hid_step n
    have huniq_comp := h₁.recursor_unique z₁ s₁
      (fun k => (h₂.recursor z₁ s₁) ((h₁.recursor z₂ s₂) k))
      hcomp_zero hcomp_step n
    rw [huniq_comp]
    exact huniq_id.symm
  right_inv := by
    intro n
    have hcomp_zero : (h₁.recursor z₂ s₂) ((h₂.recursor z₁ s₁) z₂) = z₂ := by
      rw [h₂.recursor_zero, h₁.recursor_zero]
    have hcomp_step : ∀ k,
        (h₁.recursor z₂ s₂) ((h₂.recursor z₁ s₁) (s₂ k)) =
          s₂ ((h₁.recursor z₂ s₂) ((h₂.recursor z₁ s₁) k)) := by
      intro k
      rw [h₂.recursor_step, h₁.recursor_step]
    have hid_zero : (id : N₂ → N₂) z₂ = z₂ := rfl
    have hid_step : ∀ k, (id : N₂ → N₂) (s₂ k) = s₂ ((id : N₂ → N₂) k) := by
      intro k; rfl
    have huniq_id := h₂.recursor_unique z₂ s₂ id hid_zero hid_step n
    have huniq_comp := h₂.recursor_unique z₂ s₂
      (fun k => (h₁.recursor z₂ s₂) ((h₂.recursor z₁ s₁) k))
      hcomp_zero hcomp_step n
    rw [huniq_comp]
    exact huniq_id.symm

/-- The forced arithmetic of every realization is canonically equivalent to
`LogicNat`. This is the Universal Forcing statement at the natural-number
object level: every Law-of-Logic realization carries the same NNO. -/
noncomputable def realizationOrbit_equiv_logicNat (R : LogicRealization.{0, 0}) :
    R.Orbit ≃ LogicNat :=
  IsNaturalNumberObject.equiv (realizationOrbit_isNNO R) logicNat_isNNO

/-- The Lawvere universality statement: any two realizations have iteration
orbits that satisfy the natural-number-object property, hence are
canonically equivalent. -/
noncomputable def universal_forcing_via_NNO
    (R S : LogicRealization.{0, 0}) : R.Orbit ≃ S.Orbit :=
  IsNaturalNumberObject.equiv (realizationOrbit_isNNO R) (realizationOrbit_isNNO S)

/-! ## The Boolean parity-collapse theorem

The discrete Boolean realization is the sharpest test of the iteration-object
versus orbit-as-set distinction. The carrier `Bool` has only two elements,
and the strict realization's `interpret : LogicNat → Bool` collapses
infinitely many iteration steps onto two values. The iteration object
itself never collapses; it is `LogicNat`, the natural-number object.

The theorem below makes the collapse explicit: the Boolean interpretation
is exactly the parity map `Nat.bodd ∘ toNat`. -/

namespace Strict.DiscreteBoolean

open IndisputableMonolith.Foundation.UniversalForcing.Strict

/-- One step of the Boolean strict realization is `xor true _`, which is
boolean negation. -/
private theorem xorBool_true (b : Bool) : xorBool true b = !b := by
  cases b <;> rfl

/-- The Boolean strict-realization interpretation is the parity map.

This is the formal statement that the iteration count survives even when
the orbit-as-set collapses to `{false, true}`. -/
theorem interpret_eq_parity (n : LogicNat) :
    StrictLogicRealization.interpret strictBooleanRealization n =
      Nat.bodd (LogicNat.toNat n) := by
  induction n with
  | identity => rfl
  | step n ih =>
      show xorBool true (StrictLogicRealization.interpret strictBooleanRealization n) =
        Nat.bodd (Nat.succ (LogicNat.toNat n))
      rw [xorBool_true, ih, Nat.bodd_succ]

/-- Even though the carrier image collapses, the iteration object is the
full `LogicNat`. Concretely: the interpretation map is not injective. -/
theorem interpret_collapses :
    ¬ Function.Injective
      (StrictLogicRealization.interpret strictBooleanRealization) := by
  intro hinj
  have h0 :
      StrictLogicRealization.interpret strictBooleanRealization LogicNat.identity =
        Nat.bodd 0 := interpret_eq_parity _
  have h2 :
      StrictLogicRealization.interpret strictBooleanRealization
        (LogicNat.step (LogicNat.step LogicNat.identity)) =
          Nat.bodd 2 := interpret_eq_parity _
  have hbodd : (Nat.bodd 0 : Bool) = Nat.bodd 2 := by decide
  have hboth :
      StrictLogicRealization.interpret strictBooleanRealization LogicNat.identity =
        StrictLogicRealization.interpret strictBooleanRealization
          (LogicNat.step (LogicNat.step LogicNat.identity)) := by
    rw [h0, h2, hbodd]
  have hne : LogicNat.identity ≠ LogicNat.step (LogicNat.step LogicNat.identity) :=
    LogicNat.zero_ne_succ _
  exact hne (hinj hboth)

/-- Despite the carrier collapse, the iteration object is itself a
natural-number object — the same one as in the continuous positive-ratio
realization. -/
def boolean_freeOrbit_isNNO :
    IsNaturalNumberObject
      (N := StrictLogicRealization.FreeOrbit strictBooleanRealization)
      LogicNat.identity LogicNat.step :=
  logicNat_isNNO

end Strict.DiscreteBoolean

end UniversalForcing
end Foundation
end IndisputableMonolith
