import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Foundation.ClosedObservableFramework
import IndisputableMonolith.Foundation.LedgerCompositionToJCost
import IndisputableMonolith.Foundation.DAlembert.Ultimate

/-!
# Positive-ratio comparison and factorization existence from the ledger (Phase 3)

Two Phase 3 checklist items remained after `LedgerCompositionToJCost` discharged
the "apply `law_of_logic_forces_jcost`" step:

* **Derive positive-ratio comparison from ledger**: the object the recognition
  cost `J` is applied to (the comparison between two observable states) is a
  *positive ratio*, with reciprocal symmetry under state swap.
* **Derive factorization/composition from ledger**: the existence of a binary
  combiner `P` with `F(x·y) + F(x/y) = P(F x, F y)` (the d'Alembert factorization
  input, `HasMultiplicativeConsistency`) was *assumed*, not derived.

This module closes both honestly.

## Positive-ratio comparison

A `ClosedObservableFramework` carries a strictly positive observable `r : S → ℝ`.
The comparison between two states is the ratio `r s₁ / r s₂`, which is

* strictly positive (`compRatio_pos`), so the *domain* of `J` is exactly the
  positive ray, not assumed but read off `r_pos`;
* inverted by the state swap (`compRatio_swap`), so a reciprocal-symmetric cost
  is swap-invariant (`comparison_cost_swap_invariant`): this is `IsReciprocalCost`
  realized on the ledger;
* unital at self-comparison (`compRatio_self`), so a normalized cost vanishes on
  self-comparison (`comparison_cost_self_zero`): this is `IsNormalized`.

## Factorization existence is a well-definedness condition

`HasMultiplicativeConsistency F` is, by definition, `∃ P, CostComposesThrough F P`.
We prove it is *equivalent* to the combination being **cost-determined**: the value
`F(x·y) + F(x/y)` depends only on the pair of single-point costs `(F x, F y)`
(`hasMultiplicativeConsistency_iff_costDetermined`).  So the factorization combiner
is not an arbitrary analytic input; it exists exactly when the symmetric
combination is a function of the costs alone, which is the ledger-native
well-definedness condition already appearing as the `hJ_suff` field of
`ClosedFramework.ledger_reconstruction`.  Combined with
`LedgerCompositionToJCost`, a comparison cost whose combination is cost-determined
*through a ledger-posting combiner* is forced to be `J`.

Non-vacuity: `J`'s own combination is cost-determined
(`jcost_combinationCostDetermined`), since `J` composes through `rclCombiner`.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LedgerComparisonToComposition

open ClosedFramework
open Cost.FunctionalEquation
open DAlembert.FactorizationForcing
open LedgerCompositionToJCost

/-! ## Positive-ratio comparison from the ledger -/

/-- The comparison ratio between two observable states of a closed framework. -/
noncomputable def compRatio (F : ClosedObservableFramework) (s₁ s₂ : F.S) : ℝ :=
  F.r s₁ / F.r s₂

/-- **The comparison object is a positive ratio.**  Read off the framework's
strictly positive observable `r`: the domain of the recognition cost is the
positive ray, derived rather than assumed. -/
theorem compRatio_pos (F : ClosedObservableFramework) (s₁ s₂ : F.S) :
    0 < compRatio F s₁ s₂ :=
  div_pos (F.r_pos s₁) (F.r_pos s₂)

/-- **State swap inverts the comparison ratio.**  Swapping the two states sends the
ratio to its reciprocal, the geometric origin of reciprocal symmetry. -/
theorem compRatio_swap (F : ClosedObservableFramework) (s₁ s₂ : F.S) :
    compRatio F s₂ s₁ = (compRatio F s₁ s₂)⁻¹ := by
  unfold compRatio
  rw [inv_div]

/-- **Self-comparison is the unit ratio.** -/
theorem compRatio_self (F : ClosedObservableFramework) (s : F.S) :
    compRatio F s s = 1 :=
  div_self (ne_of_gt (F.r_pos s))

/-- **Reciprocal symmetry realized on the ledger.**  A reciprocal-symmetric cost
assigns equal cost to a comparison and its state-swap, because the swap inverts the
positive ratio. -/
theorem comparison_cost_swap_invariant (F : ClosedObservableFramework)
    (J : ℝ → ℝ) (hJ : IsReciprocalCost J) (s₁ s₂ : F.S) :
    J (compRatio F s₁ s₂) = J (compRatio F s₂ s₁) := by
  rw [compRatio_swap F s₁ s₂]
  exact hJ (compRatio F s₁ s₂) (compRatio_pos F s₁ s₂)

/-- **Normalization realized on the ledger.**  A normalized cost vanishes on
self-comparison, since self-comparison is the unit ratio. -/
theorem comparison_cost_self_zero (F : ClosedObservableFramework)
    (J : ℝ → ℝ) (hJ : IsNormalized J) (s : F.S) :
    J (compRatio F s s) = 0 := by
  rw [compRatio_self]
  exact hJ

/-! ## Factorization existence is the cost-determined-combination condition -/

/-- The symmetric combination of a cost `F` is **cost-determined** if its value
`F(x·y) + F(x/y)` depends only on the pair of single-point costs `(F x, F y)`.
This is the ledger-native well-definedness condition (the `hJ_suff` field of
`ledger_reconstruction`, in its joint form). -/
def CombinationCostDetermined (F : ℝ → ℝ) : Prop :=
  ∀ x₁ y₁ x₂ y₂ : ℝ, 0 < x₁ → 0 < y₁ → 0 < x₂ → 0 < y₂ →
    F x₁ = F x₂ → F y₁ = F y₂ →
    F (x₁ * y₁) + F (x₁ / y₁) = F (x₂ * y₂) + F (x₂ / y₂)

/-- **Factorization existence ⇔ cost-determined combination.**  A comparison cost
admits a binary combiner `P` with `F(x·y) + F(x/y) = P(F x, F y)` (the d'Alembert
`HasMultiplicativeConsistency` factorization input) **iff** its symmetric
combination is cost-determined.  So the combiner is not an arbitrary analytic
assumption: it exists exactly when the combination is a function of the costs
alone.  The reverse direction builds `P` by choosing, for each cost pair in the
image, a witnessing ratio pair; cost-determinedness makes the choice irrelevant. -/
theorem hasMultiplicativeConsistency_iff_costDetermined (F : ℝ → ℝ) :
    DAlembert.Ultimate.HasMultiplicativeConsistency F ↔ CombinationCostDetermined F := by
  constructor
  · rintro ⟨P, hP⟩ x₁ y₁ x₂ y₂ hx₁ hy₁ hx₂ hy₂ hFx hFy
    rw [hP x₁ y₁ hx₁ hy₁, hP x₂ y₂ hx₂ hy₂, hFx, hFy]
  · intro hdet
    classical
    refine ⟨fun u v =>
      if h : ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ F p.1 = u ∧ F p.2 = v
      then F (h.choose.1 * h.choose.2) + F (h.choose.1 / h.choose.2)
      else 0, ?_⟩
    intro x y hx hy
    have hex : ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ F p.1 = F x ∧ F p.2 = F y :=
      ⟨(x, y), hx, hy, rfl, rfl⟩
    show F (x * y) + F (x / y) =
      (if h : ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ F p.1 = F x ∧ F p.2 = F y
        then F (h.choose.1 * h.choose.2) + F (h.choose.1 / h.choose.2)
        else 0)
    rw [dif_pos hex]
    obtain ⟨hp1, hp2, hpx, hpy⟩ := hex.choose_spec
    exact (hdet hex.choose.1 hex.choose.2 x y hp1 hp2 hx hy hpx hpy).symm

/-- `HasMultiplicativeConsistency F` is definitionally `∃ P, CostComposesThrough F P`:
the factorization input is exactly "the cost composes through some combiner". -/
theorem hasMultiplicativeConsistency_iff_exists_composesThrough (F : ℝ → ℝ) :
    DAlembert.Ultimate.HasMultiplicativeConsistency F ↔
      ∃ P : ℝ → ℝ → ℝ, CostComposesThrough F P :=
  Iff.rfl

/-! ## Non-vacuity: `J`'s combination is cost-determined -/

/-- **`J`'s combination is cost-determined.**  Since `J` composes through
`rclCombiner`, its symmetric combination is a function of the single-point costs,
so the factorization-existence condition is non-vacuous. -/
theorem jcost_combinationCostDetermined :
    CombinationCostDetermined Cost.Jcost :=
  (hasMultiplicativeConsistency_iff_costDetermined Cost.Jcost).mp
    ⟨rclCombiner, jcost_composesThrough_rclCombiner⟩

/-! ## Phase 3 composite: cost-determined through a ledger combiner forces `J` -/

/-- **Phase 3 composite.**  A comparison cost that is reciprocal, normalized,
calibrated, and continuous, whose symmetric combination is realized through a
primitive ledger-posting combiner with per-slice directional regularity, is forced
to be `J`.  The factorization combiner is supplied through the ledger (so it is
forced to `rclCombiner`), the composition law follows, and
`law_of_logic_forces_jcost` finishes, with no analytic composition-law hypothesis
assumed. -/
theorem ledgerComparison_forces_jcost
    (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (hRecip : IsReciprocalCost F) (hNorm : IsNormalized F)
    (hCalib : IsCalibrated F) (hCont : ContinuousOn F (Set.Ioi 0))
    (hP : LedgerToFactorization.PrimitiveLedgerPostingSemantics P)
    (hdir : ∀ u, Monotone (fun v => P u v) ∨ Antitone (fun v => P u v))
    (hCompose : CostComposesThrough F P) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x :=
  ledgerComposition_forces_jcost F P hRecip hNorm hCalib hCont hP hdir hCompose

/-! ## Certificate -/

/-- The Phase 3 comparison/factorization closure certificate. -/
structure LedgerComparisonCertificate : Prop where
  /-- The comparison object is a strictly positive ratio of observables. -/
  comparison_is_positive_ratio :
    ∀ (F : ClosedObservableFramework) (s₁ s₂ : F.S), 0 < compRatio F s₁ s₂
  /-- State swap inverts the comparison ratio (reciprocal symmetry origin). -/
  comparison_swap_inverts :
    ∀ (F : ClosedObservableFramework) (s₁ s₂ : F.S),
      compRatio F s₂ s₁ = (compRatio F s₁ s₂)⁻¹
  /-- Self-comparison is the unit ratio (normalization origin). -/
  comparison_self_unit :
    ∀ (F : ClosedObservableFramework) (s : F.S), compRatio F s s = 1
  /-- Factorization existence is equivalent to the combination being
  cost-determined. -/
  factorization_iff_cost_determined :
    ∀ F : ℝ → ℝ,
      DAlembert.Ultimate.HasMultiplicativeConsistency F ↔ CombinationCostDetermined F
  /-- `J`'s combination is cost-determined (non-vacuity). -/
  jcost_cost_determined : CombinationCostDetermined Cost.Jcost

/-- The Phase 3 comparison/factorization certificate holds. -/
theorem ledgerComparisonCertificate : LedgerComparisonCertificate where
  comparison_is_positive_ratio := compRatio_pos
  comparison_swap_inverts := compRatio_swap
  comparison_self_unit := compRatio_self
  factorization_iff_cost_determined := hasMultiplicativeConsistency_iff_costDetermined
  jcost_cost_determined := jcost_combinationCostDetermined

end LedgerComparisonToComposition
end Foundation
end IndisputableMonolith
