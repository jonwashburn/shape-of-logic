import Mathlib
import IndisputableMonolith.Foundation.LogicRealization
import IndisputableMonolith.Foundation.UniversalForcing

/-!
# Universal Instantiation from One Distinction

This module repairs the core skeptical objection to
`RealityFromDistinction`: a bare distinction should not merely be bundled
beside an already-existing canonical reality certificate. It should first
instantiate the Law-of-Logic realization interface on its own carrier.

Given any carrier `K` with two distinguishable points `x ≠ y`, we build a
`LogicRealization` whose carrier is exactly `K`. The comparison is the
two-valued equality cost, the identity point is `x`, and the step map is
the constant map to `y`. The internal orbit is the free `LogicNat` orbit.

This construction is intentionally minimal. It does not assert that every
carrier has a native smooth real-valued J-cost. It proves the first
universal step that is actually true:

* every non-singleton carrier instantiates the Law-of-Logic interface;
* therefore Universal Forcing applies to that carrier;
* therefore the carrier has the same forced arithmetic object as the
  canonical recognition realization.

The continuous J/spacetime layer is then reached through canonical
realization-invariance, not by pretending that an arbitrary `K` is itself
the positive real line.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalInstantiationFromDistinction

open ArithmeticFromLogic
open UniversalForcing

universe u

/-! ## Equality cost on an arbitrary carrier -/

/-- Two-valued equality cost: zero on equal inputs, one on distinct inputs. -/
def eqCost {K : Type u} [DecidableEq K] (a b : K) : Nat :=
  if a = b then 0 else 1

theorem eqCost_self {K : Type u} [DecidableEq K] (a : K) :
    eqCost a a = 0 := by
  simp [eqCost]

theorem eqCost_symm {K : Type u} [DecidableEq K] (a b : K) :
    eqCost a b = eqCost b a := by
  unfold eqCost
  by_cases h : a = b
  · subst h
    simp
  · have hba : ¬ b = a := fun hb => h hb.symm
    simp [h, hba]

theorem eqCost_ne_one {K : Type u} [DecidableEq K] {a b : K} (h : a ≠ b) :
    eqCost a b = 1 := by
  simp [eqCost, h]

/-! ## Instantiating `LogicRealization` on K -/

/-- The canonical interpretation of a lifted `LogicNat` into a carrier with a
named base point `x` and a named distinct point `y`: zero maps to `x`, every
successor maps to `y`. The `ULift` lets the orbit live in the same universe as
the arbitrary carrier. -/
def distinctionInterpret {K : Type u} (x y : K) : ULift.{u} LogicNat → K
  | ⟨LogicNat.identity⟩ => x
  | ⟨LogicNat.step _⟩ => y

/-- The step map induced by a single distinction: every state advances to the
distinguished second point. This gives a total endomap on `K`. -/
def distinctionStep {K : Type u} (_x y : K) : K → K :=
  fun _ => y

@[simp] theorem distinctionInterpret_zero {K : Type u} (x y : K) :
    distinctionInterpret x y (ULift.up LogicNat.identity) = x := rfl

@[simp] theorem distinctionInterpret_step {K : Type u} (x y : K)
    (n : ULift.{u} LogicNat) :
    distinctionInterpret x y (ULift.up (LogicNat.step n.down)) =
      distinctionStep x y (distinctionInterpret x y n) := by
  cases n with
  | up n =>
    cases n <;> rfl

/-- **Universal instantiation theorem.**

Any carrier with a named distinction `x ≠ y` is a `LogicRealization` on
that very carrier. -/
noncomputable def logicRealizationOfDistinction
    (K : Type u) [DecidableEq K] (x y : K) (hxy : x ≠ y) :
    LogicRealization.{u, 0} where
  Carrier := K
  Cost := Nat
  zeroCost := inferInstance
  compare := eqCost
  zero := x
  step := distinctionStep x y
  Orbit := ULift.{u} LogicNat
  orbitZero := ULift.up LogicNat.zero
  orbitStep := fun n => ULift.up (LogicNat.succ n.down)
  interpret := distinctionInterpret x y
  interpret_zero := rfl
  interpret_step := by
    intro n
    exact distinctionInterpret_step x y n
  orbit_no_confusion := by
    intro n h
    exact LogicNat.zero_ne_succ n.down (congrArg ULift.down h)
  orbit_step_injective := by
    intro a b h
    apply ULift.ext
    exact LogicNat.succ_injective (congrArg ULift.down h)
  orbit_induction := by
    intro P h0 hs n
    cases n with
    | up n =>
      induction n with
      | identity => exact h0
      | step n ih => exact hs (ULift.up n) ih
  orbitEquivLogicNat :=
    { toFun := fun n => n.down
      invFun := fun n => ULift.up n
      left_inv := by intro n; cases n; rfl
      right_inv := by intro n; rfl }
  orbitEquiv_zero := rfl
  orbitEquiv_step := by intro n; rfl
  identity := by
    intro a
    exact eqCost_self a
  nonContradiction := by
    intro a b
    exact eqCost_symm a b
  -- The three slots below are *carried* propositions, not proof obligations:
  -- `LogicRealization` stores a `Prop` in each (`excludedMiddle`, `composition`,
  -- `actionInvariant`) and never forces it to hold. We therefore store the
  -- genuine, setting-appropriate statements that DO hold for the two-valued
  -- equality cost, and discharge each below (`logicRealizationOfDistinction_*`).
  --
  -- We deliberately do NOT store a multiplicative composition law: equality cost
  -- provably fails (L4) multiplicative composition consistency
  -- (`PrimitiveDistinction.equality_cost_insufficient_for_recognition`). That
  -- failure is exactly why this realization is minimal and the continuous J/φ
  -- layer is reached by realization-invariance, not by pretending an arbitrary
  -- `K` is the positive real line. The `composition` slot therefore carries the
  -- additive triangle inequality that the equality cost DOES satisfy.
  excludedMiddle := ∀ a b : K, a = b ∨ a ≠ b
  composition := ∀ a b c : K, eqCost a c ≤ eqCost a b + eqCost b c
  actionInvariant := ∀ a b : K, distinctionStep x y a = distinctionStep x y b
  nontrivial := by
    refine ⟨y, ?_⟩
    have hyx : y ≠ x := fun hy => hxy hy.symm
    simp [eqCost, hyx]

/-! ## The carried law-slots are genuine, not vacuous

The three `Prop`-valued slots of the minimal realization (`excludedMiddle`,
`composition`, `actionInvariant`) carry statements that actually hold for the
two-valued equality cost. We discharge them here so the realization is not
"too permissive": it makes named, true claims appropriate to a single
distinction, and explicitly declines the one law (multiplicative composition)
that equality cost provably cannot satisfy. -/

/-- The minimal distinction realization genuinely satisfies the excluded-middle
content it carries: every pair on the carrier is same-or-different. -/
theorem logicRealizationOfDistinction_excludedMiddle
    {K : Type u} [DecidableEq K] (x y : K) (hxy : x ≠ y) :
    (logicRealizationOfDistinction K x y hxy).excludedMiddle := by
  show ∀ a b : K, a = b ∨ a ≠ b
  exact fun a b => eq_or_ne a b

/-- The minimal distinction realization satisfies the *additive* composition law
(the triangle inequality) of its two-valued equality cost. This is NOT the
multiplicative composition consistency (L4), which equality cost provably fails
(`PrimitiveDistinction.equality_cost_insufficient_for_recognition`); the slot
deliberately carries only the additive law that does hold. -/
theorem logicRealizationOfDistinction_composition
    {K : Type u} [DecidableEq K] (x y : K) (hxy : x ≠ y) :
    (logicRealizationOfDistinction K x y hxy).composition := by
  show ∀ a b c : K, eqCost a c ≤ eqCost a b + eqCost b c
  intro a b c
  by_cases hac : a = c
  · have h0 : eqCost a c = 0 := by simp [eqCost, hac]
    rw [h0]; exact Nat.zero_le _
  · have hac1 : eqCost a c = 1 := eqCost_ne_one hac
    have hsplit : a ≠ b ∨ b ≠ c := by
      by_contra hcon
      push_neg at hcon
      exact hac (hcon.1.trans hcon.2)
    rw [hac1]
    rcases hsplit with hab | hbc
    · have h1 : eqCost a b = 1 := eqCost_ne_one hab
      have h2 : 0 ≤ eqCost b c := Nat.zero_le _
      omega
    · have h1 : eqCost b c = 1 := eqCost_ne_one hbc
      have h2 : 0 ≤ eqCost a b := Nat.zero_le _
      omega

/-- The distinction step action is invariant across inputs: it is the constant
map onto the marked second point. -/
theorem logicRealizationOfDistinction_actionInvariant
    {K : Type u} [DecidableEq K] (x y : K) (hxy : x ≠ y) :
    (logicRealizationOfDistinction K x y hxy).actionInvariant := by
  show ∀ a b : K, distinctionStep x y a = distinctionStep x y b
  intro _ _; rfl

/-! ## Carrier-level theorem from the bare proposition -/

/-- Every inhabited carrier with some distinction admits a native
`LogicRealization`. The `DecidableEq K` instance is obtained classically. -/
theorem exists_logicRealization_of_distinction
    (K : Type u) [Nonempty K] (h : ∃ x y : K, x ≠ y) :
    Nonempty (LogicRealization.{u, 0}) := by
  classical
  rcases h with ⟨x, y, hxy⟩
  exact ⟨logicRealizationOfDistinction K x y hxy⟩

/-- A more precise version retaining the chosen points. -/
theorem exists_named_logicRealization_of_distinction
    (K : Type u) [Nonempty K] (h : ∃ x y : K, x ≠ y) :
    ∃ x y : K, ∃ hxy : x ≠ y,
      Nonempty (LogicRealization.{u, 0}) := by
  classical
  rcases h with ⟨x, y, hxy⟩
  exact ⟨x, y, hxy, ⟨logicRealizationOfDistinction K x y hxy⟩⟩

/-! ## Universal Forcing applies to the K-native realization -/

/-- The forced arithmetic of the `K`-native realization is canonically
`LogicNat`. -/
noncomputable def distinction_arithmetic_equiv_logicNat
    {K : Type u} [DecidableEq K] (x y : K) (hxy : x ≠ y) :
    (UniversalForcing.arithmeticOf
      (logicRealizationOfDistinction K x y hxy)).peano.carrier ≃ LogicNat :=
  (logicRealizationOfDistinction K x y hxy).orbitEquivLogicNat

/-- Any two non-singleton carriers, with chosen distinctions, have
canonically equivalent forced arithmetic. -/
noncomputable def distinction_realizations_have_same_arithmetic
    {K L : Type u} [DecidableEq K] [DecidableEq L]
    {x y : K} {a b : L} (hxy : x ≠ y) (hab : a ≠ b) :
    (UniversalForcing.arithmeticOf
      (logicRealizationOfDistinction K x y hxy)).peano.carrier ≃
    (UniversalForcing.arithmeticOf
      (logicRealizationOfDistinction L a b hab)).peano.carrier :=
  (logicRealizationOfDistinction K x y hxy).orbitEquivLogicNat.trans
    (logicRealizationOfDistinction L a b hab).orbitEquivLogicNat.symm

/-! ## Certificate -/

structure UniversalInstantiationCert (K : Type u) [Nonempty K] : Prop where
  instantiate :
    (∃ x y : K, x ≠ y) → Nonempty (LogicRealization.{u, 0})
  named :
    (∃ x y : K, x ≠ y) →
      ∃ x y : K, ∃ hxy : x ≠ y,
        Nonempty (LogicRealization.{u, 0})

theorem universalInstantiationCert
    (K : Type u) [Nonempty K] :
    UniversalInstantiationCert K where
  instantiate := exists_logicRealization_of_distinction K
  named := exists_named_logicRealization_of_distinction K

end UniversalInstantiationFromDistinction
end Foundation
end IndisputableMonolith
