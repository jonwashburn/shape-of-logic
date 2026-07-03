/-
  UniversalForcing/CanonicalForcing.lean

  Closing the representation-claim weakness.

  The Universal Forcing thesis must not be demoted to "there exists *some*
  isomorphism between the two forced ℕ-towers." Any two countable Peano objects
  are abstractly isomorphic, so bare existence carries no content. The actual
  content is **canonicity**: the forcing map is the *unique* structure-preserving
  function, fully determined by initiality. There is no choice, no representation
  ambiguity — the zero/step data pins exactly one map.

  This module proves it for strict realizations (the main Universal-Forcing
  theorem path), where every forced arithmetic carrier is concretely `LogicNat`:

  * `universal_forcing_map_zero` / `universal_forcing_map_step`: the forcing
    equivalence is itself a Peano homomorphism (preserves zero and step).
  * `universal_forcing_unique`: *any* function preserving zero and step equals
    the forcing map. This is the canonicity statement — the map is forced, not
    chosen.
  * `universal_forcing_iff`: a complete characterization (preservation ↔ being
    the forcing map).
  * `universal_forcing_equiv_unique`: two equivalences that both preserve zero
    and step are equal as functions. Uniqueness up to *nothing*, not merely up to
    iso.
  * `CanonicalForcingCert` / `canonicalForcingCert_holds`: the certificate.

  With this, the program's headline ("two realizations force the same arithmetic")
  is a statement about a canonical, determined morphism, not a representation
  artifact.

  The general (non-strict, cross-universe) case is `ArithmeticOf.universal_objective`:
  for any two Law-of-Logic realizations and any forced arithmetics over them
  (sharing a carrier universe), the structure-preserving equivalence exists and
  is the unique zero/step-preserving map. That theorem is the precise statement
  of `universal-forcing-program.mdc`'s "canonical equivalence of `ArithmeticOf R`
  and `ArithmeticOf S` across admissible realizations".
-/

import IndisputableMonolith.Foundation.ArithmeticOf
import IndisputableMonolith.Foundation.UniversalForcing.StrictRealization

namespace IndisputableMonolith
namespace Foundation

/-! ## General canonicity (any two realizations, shared carrier universe)

The strict, universe-0 statements below are the main-path case. These general
lemmas cover *any* two Law-of-Logic realizations whose forced arithmetics share a
carrier universe `w` — which is always arrangeable, since the carrier universe is
a free parameter of `ArithmeticOf`. The same-universe condition is not a
restriction on the mathematics; it is the only setting in which "the unique
structure morphism" is even a well-formed comparison (`IsInitial.uniq` quantifies
over Peano objects in one universe). `equivOfInitial` itself is cross-universe in
its slots, so the pinning `ArithmeticOf.{u,v,w,w,w}` is what makes the uniqueness
argument type-check. -/

namespace ArithmeticOf

open ArithmeticFromLogic

universe u v u' v' w

variable {R : LogicRealization.{u, v}} {S : LogicRealization.{u', v'}}

/-- The forcing equivalence preserves zero (general realizations). -/
@[simp] theorem equivOfInitial_map_zero
    (A : ArithmeticOf.{u, v, w, w, w} R) (B : ArithmeticOf.{u', v', w, w, w} S) :
    (equivOfInitial A B) A.peano.zero = B.peano.zero :=
  (A.initial.lift B.peano).map_zero

/-- The forcing equivalence intertwines step (general realizations). -/
@[simp] theorem equivOfInitial_map_step
    (A : ArithmeticOf.{u, v, w, w, w} R) (B : ArithmeticOf.{u', v', w, w, w} S)
    (x : A.peano.carrier) :
    (equivOfInitial A B) (A.peano.step x) = B.peano.step ((equivOfInitial A B) x) :=
  (A.initial.lift B.peano).map_step x

/-- **General canonicity.** Any function preserving zero and step between two
forced arithmetics (sharing a carrier universe) *is* the forcing map. The map is
determined by the zero/step data alone — no representational freedom. -/
theorem forcing_map_unique
    (A : ArithmeticOf.{u, v, w, w, w} R) (B : ArithmeticOf.{u', v', w, w, w} S)
    (f : A.peano.carrier → B.peano.carrier)
    (hz : f A.peano.zero = B.peano.zero)
    (hs : ∀ x, f (A.peano.step x) = B.peano.step (f x)) :
    f = (equivOfInitial A B).toFun := by
  have h := A.initial.uniq B.peano
      (⟨f, hz, hs⟩ : PeanoObject.Hom A.peano B.peano) (A.initial.lift B.peano)
  simpa [equivOfInitial] using h

/-- Complete characterization (general realizations). -/
theorem forcing_map_iff
    (A : ArithmeticOf.{u, v, w, w, w} R) (B : ArithmeticOf.{u', v', w, w, w} S)
    (f : A.peano.carrier → B.peano.carrier) :
    (f A.peano.zero = B.peano.zero ∧ ∀ x, f (A.peano.step x) = B.peano.step (f x))
      ↔ f = (equivOfInitial A B).toFun := by
  constructor
  · rintro ⟨hz, hs⟩
    exact forcing_map_unique A B f hz hs
  · rintro rfl
    exact ⟨equivOfInitial_map_zero A B, equivOfInitial_map_step A B⟩

/-- **Uniqueness up to nothing** (general realizations): two equivalences that
both preserve zero and step are equal as functions. -/
theorem forcing_equiv_unique
    (A : ArithmeticOf.{u, v, w, w, w} R) (B : ArithmeticOf.{u', v', w, w, w} S)
    (e₁ e₂ : A.peano.carrier ≃ B.peano.carrier)
    (hz₁ : e₁ A.peano.zero = B.peano.zero)
    (hs₁ : ∀ x, e₁ (A.peano.step x) = B.peano.step (e₁ x))
    (hz₂ : e₂ A.peano.zero = B.peano.zero)
    (hs₂ : ∀ x, e₂ (A.peano.step x) = B.peano.step (e₂ x)) :
    (e₁ : A.peano.carrier → B.peano.carrier) = e₂ := by
  have h1 := forcing_map_unique A B (e₁ : A.peano.carrier → B.peano.carrier) hz₁ hs₁
  have h2 := forcing_map_unique A B (e₂ : A.peano.carrier → B.peano.carrier) hz₂ hs₂
  rw [h1, h2]

/-- **The Universal-Forcing objective at full generality.** For *any* two
Law-of-Logic realizations `R`, `S` (in arbitrary universes) and any forced
arithmetics `A` over `R`, `B` over `S` sharing a carrier universe, there is a
structure-preserving equivalence between the carriers that is *the unique*
zero/step-preserving map. This is the precise content of
`universal-forcing-program.mdc`'s "canonical equivalence of `ArithmeticOf R` and
`ArithmeticOf S` across admissible realizations": not bare existence of some
iso, but a canonical, determined morphism.

Unlike the strict-realization certificate below (where the carrier is concretely
`LogicNat` and the map is the identity), here `A.peano.carrier` and
`B.peano.carrier` may be genuinely different Peano objects, so the equivalence is
a nontrivial iso — yet still the only structure morphism between them. -/
theorem universal_objective
    (A : ArithmeticOf.{u, v, w, w, w} R) (B : ArithmeticOf.{u', v', w, w, w} S) :
    ∃ e : A.peano.carrier ≃ B.peano.carrier,
      e A.peano.zero = B.peano.zero
      ∧ (∀ x, e (A.peano.step x) = B.peano.step (e x))
      ∧ (∀ f : A.peano.carrier → B.peano.carrier,
            f A.peano.zero = B.peano.zero →
            (∀ x, f (A.peano.step x) = B.peano.step (f x)) →
            f = e.toFun) :=
  ⟨equivOfInitial A B,
   equivOfInitial_map_zero A B,
   equivOfInitial_map_step A B,
   fun f hz hs => forcing_map_unique A B f hz hs⟩

end ArithmeticOf

namespace UniversalForcing
namespace Strict
namespace StrictLogicRealization

open ArithmeticFromLogic

/-- The strict universal-forcing equivalence preserves zero: it sends `R`'s
forced zero to `S`'s forced zero. -/
@[simp] theorem universal_forcing_map_zero (R S : StrictLogicRealization.{0,0}) :
    (universal_forcing.{0,0,0,0,0,0} R S) (arith.{0,0,0} R).peano.zero
      = (arith.{0,0,0} S).peano.zero :=
  ((arith.{0,0,0} R).initial.lift (arith.{0,0,0} S).peano).map_zero

/-- The strict universal-forcing equivalence intertwines `R`'s step with `S`'s
step. -/
@[simp] theorem universal_forcing_map_step (R S : StrictLogicRealization.{0,0})
    (x : (arith.{0,0,0} R).peano.carrier) :
    (universal_forcing.{0,0,0,0,0,0} R S) ((arith.{0,0,0} R).peano.step x)
      = (arith.{0,0,0} S).peano.step ((universal_forcing.{0,0,0,0,0,0} R S) x) :=
  ((arith.{0,0,0} R).initial.lift (arith.{0,0,0} S).peano).map_step x

/-- **Canonicity.** Any function that preserves zero and step *is* the strict
universal-forcing map. The structure-preserving map between two forced
arithmetics is unique, so the equivalence is determined by the zero/step data
alone — there is no representational freedom. -/
theorem universal_forcing_unique (R S : StrictLogicRealization.{0,0})
    (f : (arith.{0,0,0} R).peano.carrier → (arith.{0,0,0} S).peano.carrier)
    (hz : f (arith.{0,0,0} R).peano.zero = (arith.{0,0,0} S).peano.zero)
    (hs : ∀ x, f ((arith.{0,0,0} R).peano.step x) = (arith.{0,0,0} S).peano.step (f x)) :
    f = (universal_forcing.{0,0,0,0,0,0} R S).toFun := by
  have h := (arith.{0,0,0} R).initial.uniq (arith.{0,0,0} S).peano
      (⟨f, hz, hs⟩ : PeanoObject.Hom (arith.{0,0,0} R).peano (arith.{0,0,0} S).peano)
      ((arith.{0,0,0} R).initial.lift (arith.{0,0,0} S).peano)
  simpa [universal_forcing, ArithmeticOf.equivOfInitial] using h

/-- Complete characterization: a map is the forcing map iff it preserves zero and
step. -/
theorem universal_forcing_iff (R S : StrictLogicRealization.{0,0})
    (f : (arith.{0,0,0} R).peano.carrier → (arith.{0,0,0} S).peano.carrier) :
    (f (arith.{0,0,0} R).peano.zero = (arith.{0,0,0} S).peano.zero
        ∧ ∀ x, f ((arith.{0,0,0} R).peano.step x) = (arith.{0,0,0} S).peano.step (f x))
      ↔ f = (universal_forcing.{0,0,0,0,0,0} R S).toFun := by
  constructor
  · rintro ⟨hz, hs⟩
    exact universal_forcing_unique R S f hz hs
  · rintro rfl
    exact ⟨universal_forcing_map_zero R S, universal_forcing_map_step R S⟩

/-- **Uniqueness up to nothing.** Two equivalences that both preserve zero and
step are equal as functions. The forcing isomorphism is not "an" iso among many;
it is the only structure morphism, hence canonical. -/
theorem universal_forcing_equiv_unique (R S : StrictLogicRealization.{0,0})
    (e₁ e₂ : (arith.{0,0,0} R).peano.carrier ≃ (arith.{0,0,0} S).peano.carrier)
    (hz₁ : e₁ (arith.{0,0,0} R).peano.zero = (arith.{0,0,0} S).peano.zero)
    (hs₁ : ∀ x, e₁ ((arith.{0,0,0} R).peano.step x) = (arith.{0,0,0} S).peano.step (e₁ x))
    (hz₂ : e₂ (arith.{0,0,0} R).peano.zero = (arith.{0,0,0} S).peano.zero)
    (hs₂ : ∀ x, e₂ ((arith.{0,0,0} R).peano.step x) = (arith.{0,0,0} S).peano.step (e₂ x)) :
    (e₁ : (arith.{0,0,0} R).peano.carrier → (arith.{0,0,0} S).peano.carrier) = e₂ := by
  have h1 := universal_forcing_unique R S
      (e₁ : (arith.{0,0,0} R).peano.carrier → (arith.{0,0,0} S).peano.carrier) hz₁ hs₁
  have h2 := universal_forcing_unique R S
      (e₂ : (arith.{0,0,0} R).peano.carrier → (arith.{0,0,0} S).peano.carrier) hz₂ hs₂
  rw [h1, h2]

end StrictLogicRealization
end Strict

/-- **Certificate: forcing is canonical, not representational.** The forced
arithmetic equivalence between any two strict realizations exists, preserves the
full Peano structure, and is the unique such map. -/
structure CanonicalForcingCert where
  /-- The forcing map exists for every pair of strict realizations. -/
  exists_map : ∀ (R S : Strict.StrictLogicRealization.{0,0}),
      (Strict.StrictLogicRealization.arith.{0,0,0} R).peano.carrier ≃
        (Strict.StrictLogicRealization.arith.{0,0,0} S).peano.carrier
  /-- It preserves zero. -/
  preserves_zero : ∀ (R S : Strict.StrictLogicRealization.{0,0}),
      (exists_map R S) (Strict.StrictLogicRealization.arith.{0,0,0} R).peano.zero
        = (Strict.StrictLogicRealization.arith.{0,0,0} S).peano.zero
  /-- It preserves step. -/
  preserves_step : ∀ (R S : Strict.StrictLogicRealization.{0,0})
      (x : (Strict.StrictLogicRealization.arith.{0,0,0} R).peano.carrier),
      (exists_map R S) ((Strict.StrictLogicRealization.arith.{0,0,0} R).peano.step x)
        = (Strict.StrictLogicRealization.arith.{0,0,0} S).peano.step ((exists_map R S) x)
  /-- It is the unique zero/step-preserving function. -/
  unique : ∀ (R S : Strict.StrictLogicRealization.{0,0})
      (f : (Strict.StrictLogicRealization.arith.{0,0,0} R).peano.carrier →
            (Strict.StrictLogicRealization.arith.{0,0,0} S).peano.carrier),
      f (Strict.StrictLogicRealization.arith.{0,0,0} R).peano.zero
          = (Strict.StrictLogicRealization.arith.{0,0,0} S).peano.zero →
      (∀ x, f ((Strict.StrictLogicRealization.arith.{0,0,0} R).peano.step x)
            = (Strict.StrictLogicRealization.arith.{0,0,0} S).peano.step (f x)) →
      f = (exists_map R S).toFun

/-- The canonicity certificate holds. -/
noncomputable def canonicalForcingCert_holds : CanonicalForcingCert where
  exists_map := fun R S => Strict.StrictLogicRealization.universal_forcing.{0,0,0,0,0,0} R S
  preserves_zero := fun R S => Strict.StrictLogicRealization.universal_forcing_map_zero R S
  preserves_step := fun R S x => Strict.StrictLogicRealization.universal_forcing_map_step R S x
  unique := fun R S f hz hs => Strict.StrictLogicRealization.universal_forcing_unique R S f hz hs

end UniversalForcing
end Foundation
end IndisputableMonolith
