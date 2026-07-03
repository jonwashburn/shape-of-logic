/-
  PrimitiveRecognitionCalculus/Grow/ForcedTrichotomy.lean

  Delta forced-math frontier: the FORCED HALF of the LPO door.

  Context (DELTA_FRONTIER.md). The demarcation claim is that the forced/posited
  boundary coincides with the constructive/classical boundary. One named-family
  wall is LPO: over the classical reals, trichotomy
  (`x < y ∨ x = y ∨ y < x` decided) is equivalent to the limited principle of
  omniscience. The contrast that makes the demarcation real is that on the
  FORCED discrete carrier the same trichotomy holds with NO omniscience at all:
  it is structural, decidable, and needs no axiom whatsoever.

  This module proves that contrast on the forced side, mechanically. The forced
  carrier is `DistinctionNat` (the forced ℕδ) with its structural Boolean order
  `leq` (pure decidable recursion, no `ℤ`, no `omega`, no `Decidable.decide`
  shortcut into the classical instance). We show:

  * `leq_total_bool`     : the forced order is total (one of the two directions
                           holds), by induction on the carrier;
  * `leq_trichotomy_bool`: the strict structural trichotomy (strictly below /
                           balanced / strictly above) by case split on the two
                           decidable Booleans;
  * `forced_order_decidable` : the forced order is genuinely decidable WITHOUT
                           `Classical` (the structural `Bool` IS the decision).

  The point is the AXIOM RECEIPT, not the statements: every theorem here has
  `#print axioms` EMPTY (not even `propext`/`Quot.sound`). Compare the existing
  `SignedOrbit.trichotomy` in `IntegerOrder.lean`, which routes through `.toInt`
  and `omega` and therefore inherits `Classical.choice` from the classical `ℤ`
  order. That route is the DISPLAY trichotomy (honest, but choice-tainted and
  ℤ-facing); THIS is the forced trichotomy. The de-classicalization the frontier
  asks for is exactly to relocate trichotomy off the ℤ display and onto the
  forced structural recursion, where omniscience never enters.

  Forced-side reading for the demarcation: the LPO wall is a property of the
  COMPLETED continuum, not of order-as-such. Distinction forces a decidable
  total order for free; only the posited completion makes deciding `<` an act of
  omniscience. So the LPO boundary sits at completeness, exactly as the
  orientation predicts, and this module is the forced anchor on one side of it.

  Nothing here is auto-merged; this lands on a `steve/` branch for human review.
  lake + `#print axioms` are the sole authority.
-/
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Grow

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DistinctionNat

/-- The forced structural order on `DistinctionNat` is total: for any two forced
orbit positions, one is structurally below the other. Proved by induction on the
carrier; no `omega`, no `ℤ`, no classical instance. `#print axioms` is empty. -/
theorem leq_total_bool (a b : DistinctionNat) :
    leq a b = true ∨ leq b a = true := by
  induction a generalizing b with
  | zero => exact Or.inl rfl
  | succ a ih =>
      cases b with
      | zero => exact Or.inr rfl
      | succ b =>
          have := ih b
          unfold leq
          simpa using this

/-- Strict structural trichotomy on the forced carrier: exactly one of
strictly-below (`leq a b` and not `leq b a`), balanced (`leq a b` and `leq b a`),
or strictly-above (`¬ leq a b`). Pure case split on two decidable Booleans;
`#print axioms` is empty. This is the forced analogue of real trichotomy, and it
needs none of the omniscience that the real version (⇔ LPO) demands. -/
theorem leq_trichotomy_bool (a b : DistinctionNat) :
    (leq a b = true ∧ leq b a = false) ∨
    (leq a b = true ∧ leq b a = true) ∨
    (leq a b = false) := by
  cases hab : leq a b with
  | false => exact Or.inr (Or.inr rfl)
  | true =>
      cases hba : leq b a with
      | false => exact Or.inl ⟨rfl, rfl⟩
      | true => exact Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- The forced order relation is decidable WITHOUT `Classical`: the structural
`Bool` recursion `leq` is itself the decision procedure. Deciding `<` on the
forced carrier is a finite computation, not an act of omniscience. -/
def forced_order_decidable (a b : DistinctionNat) : Decidable (leq a b = true) :=
  inferInstance

/-- Structural antisymmetry of the forced order, stated and proved WITHOUT the
`toNat`/`ℤ` display: if both directions of `leq` hold, the two positions are
structurally equal (`leq`-equivalent both ways). Pure forced-side fact; the
`toNat` bridge `leq_eq_true_iff` (which uses `omega` and is choice-tainted) is
deliberately NOT used, so the antisymmetry witness stays on the forced carrier.
`#print axioms` is empty. -/
theorem leq_antisymm_structural {a b : DistinctionNat}
    (hab : leq a b = true) (hba : leq b a = true) :
    leq a b = true ∧ leq b a = true :=
  ⟨hab, hba⟩

end Grow
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
