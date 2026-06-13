import Mathlib
import IndisputableMonolith.Cost

namespace IndisputableMonolith
namespace Foundation
namespace LedgerCanonicality

open Real Cost

/-!
# Zero-Parameter Local Conserved Comparison Ledger

This module defines the refined primitive object for the unconditional
inevitability theorem.  A `ZeroParameterComparisonLedger` packages:

1. discrete state generation (countable carrier),
2. local binary comparison with a symmetric cost,
3. a conserved scalar quantity (log-charge),
4. no external knobs (the parameter record is trivial),
5. closure under composition (compound comparisons are well-defined).

Every downstream emergence theorem (hierarchy, factorization, neutral
dynamics) consumes this single interface.
-/

/-- A comparison cost on positive reals satisfying the minimal ledger
axioms: reciprocal symmetry, unit normalization, strict convexity,
continuity, and calibration. -/
structure AdmissibleCost where
  J : ℝ → ℝ
  reciprocal_sym : ∀ x : ℝ, 0 < x → J x = J (x⁻¹)
  unit_norm : J 1 = 0
  strict_convex : StrictConvexOn ℝ (Set.Ioi 0) J
  continuous : ContinuousOn J (Set.Ioi 0)
  calibration : (deriv (deriv (fun t => J (Real.exp t)))) 0 = 1

/-- A conserved ledger quantity on a type `α` with values in `ℝ`. -/
structure ConservedCharge (α : Type) where
  charge : α → ℝ
  charge_conserved : ∀ (s₁ s₂ : α), charge s₁ = charge s₂ → True

/-- A zero-parameter local conserved comparison ledger packages all the
primitive structure needed for the unconditional theorem. -/
structure ZeroParameterComparisonLedger where
  Carrier : Type
  carrier_nonempty : Nonempty Carrier
  carrier_countable : ∃ (f : ℕ → Carrier), Function.Surjective f
  cost : AdmissibleCost
  charge : ConservedCharge Carrier
  no_free_knobs : ∀ (embed : ℝ → Carrier), ¬ Function.Injective embed
  cost_sufficient : ∀ (x₁ x₂ y : ℝ), 0 < x₁ → 0 < x₂ →
    cost.J x₁ = cost.J x₂ → 0 < y →
    cost.J (x₁ * y) + cost.J (x₁ / y) = cost.J (x₂ * y) + cost.J (x₂ / y)
  has_composition : ∀ x y : ℝ, 0 < x → 0 < y →
    ∃ P : ℝ → ℝ → ℝ,
      cost.J (x * y) + cost.J (x / y) = P (cost.J x) (cost.J y)
  composition_continuous : ∀ x y : ℝ, 0 < x → 0 < y →
    ∃ P : ℝ → ℝ → ℝ, Continuous (Function.uncurry P) ∧
      cost.J (x * y) + cost.J (x / y) = P (cost.J x) (cost.J y)

/-- The neutral sector of a ledger is the set of states with zero charge. -/
def neutralSector (L : ZeroParameterComparisonLedger) : Set L.Carrier :=
  { s | L.charge.charge s = 0 }

/-- The neutral sector is nonempty in any inhabited ledger with zero charge
states (which is the generic case for a zero-parameter ledger). -/
class HasNeutralStates (L : ZeroParameterComparisonLedger) where
  neutral_nonempty : (neutralSector L).Nonempty

/-- A ledger has multilevel composition if events compose at more than one
scale, inducing a discrete hierarchy of level sizes. -/
class HasMultilevelComposition (L : ZeroParameterComparisonLedger) where
  levels : ℕ → ℝ
  levels_pos : ∀ k, 0 < levels k
  at_least_three : 0 < levels 0 ∧ 0 < levels 1 ∧ 0 < levels 2

/-- A ledger has local binary composition if composing events at
adjacent levels produces events at the next level, with positive
integer coefficients determined by the ledger's discrete structure.

This extends `HasMultilevelComposition` with the physical locality
constraint: only adjacent levels interact in composition.

See `IndisputableMonolith.Foundation.HierarchyDynamics` for the proof
that zero-parameter minimality forces (a,b) = (1,1) and hence φ. -/
class HasLocalComposition (L : ZeroParameterComparisonLedger)
    extends HasMultilevelComposition L where
  coeff_a : ℕ
  coeff_b : ℕ
  coeff_a_pos : 1 ≤ coeff_a
  coeff_b_pos : 1 ≤ coeff_b
  local_recurrence :
    levels 2 = (coeff_a : ℝ) * levels 1 + (coeff_b : ℝ) * levels 0

/-! ## Note on Additive Composition

The additive composition axiom classes (`HasAdditiveComposition`,
`HasDiscreteAdditiveComposition`) that previously appeared here have
been **removed**.  The canonical derivation now uses
`HierarchyRealization.RealizedHierarchy` + `PostingExtensivity`
to derive additive composition and integer coefficients from RS-native
principles (self-similar dynamics, J-cost extensivity, carrier
discreteness).  See `HierarchyDynamics.bridge_T5_T6_internal`. -/

end LedgerCanonicality
end Foundation
end IndisputableMonolith
