import IndisputableMonolith.Gravity.SevenGaps.WickActionCertAssembly
import IndisputableMonolith.Gravity.SevenGaps.WickActionCutLimitFamily

/-!
# Wave C4 F2: family `WickActionContinuationCertV2` assembly

Binding design: `D-gap6-v2-succession-family-design-20260723`.

Assembles every banked family ingredient into
`wickActionContinuationCertV2_of_causal` under `7/12 < α`, then lands the
succession terminal

`wick_action_continuation_4d_v2 :=
  (∀ α, 7/12 < α → CertV2 α) ∧ CertV2 1`

and retires the frozen V1 terminal via `not_wick_action_continuation_4d`
(from `contAction_not_satisfiable_at_one`).

## Honesty (disclosed)

* **V1 retirement.** The frozen closed-interval `contAction` field is
  unsatisfiable at the cut (`contAction_not_satisfiable_at_one`); hence
  `¬ wick_action_continuation_4d`. Succession is choice (a): the v2
  terminal replaces V1 as the ledger target.
* **`euclidSchlaefli`.** Differentiability of the Euclidean-endpoint
  action on the collapsed one-hinge geometry, **not** classical
  multi-hinge Schläfli cancellation `Σ A θ' = 0`.
* **One-hinge MODEL scoping.** Charts collapse to a single angle path
  (`induced_pent*_eq`); the certificate is the three-pent one-hinge
  model, not a full multi-hinge complex.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace WickActionInteriorHinge

open Complex
open Filter Topology
open CausalSimplex4D
open ThreePentCausalConsistency

noncomputable section

/-! ## §F2. Family certificate assembly -/

theorem chartsAgree_of_causal (α : ℝ) :
    inducedSqEdges pentAVert 1 α =
        CausalSimplex4D.lorentzianSqEdges CausalPentType.threeTwo 1 α ∧
      inducedSqEdges pentBVert 1 α =
        CausalSimplex4D.lorentzianSqEdges CausalPentType.threeTwo 1 α ∧
      inducedSqEdges pentCVert 1 α =
        CausalSimplex4D.lorentzianSqEdges CausalPentType.threeTwo 1 α :=
  ⟨induced_pentA_eq 1 α, induced_pentB_eq 1 α, induced_pentC_eq 1 α⟩

theorem euclidCosReal_of_causal {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    pentHingeCosPath α 1 = ((euclidCos α : ℝ) : ℂ) ∧
      (α = 1 → euclidCos α = -(1 / 4)) :=
  ⟨pentHingeCosPath_eq_euclidCos hα, fun h => by
    subst h
    exact euclidCos_one⟩

theorem euclidAnchor_of_causal {α : ℝ} (hα : (7 / 12 : ℝ) < α) :
    wickActionPath α 1 =
      ((hingeArea * (2 * Real.pi - 3 * Real.arccos (euclidCos α)) : ℝ) : ℂ) := by
  simpa [euclidAngle] using wickActionPath_eq_euclidRegge hα

/-- Family-wide repaired V2 certificate on the causal range `7/12 < α`. -/
theorem wickActionContinuationCertV2_of_causal {α : ℝ}
    (hα : (7 / 12 : ℝ) < α) : WickActionContinuationCertV2 α where
  causalRange := hα
  chartsAgree := chartsAgree_of_causal α
  branchRegularSum := branchRegularSum_of_causal hα
  contActionInterior := continuousOn_wickActionPath_Ioc_of_causal hα
  cutLimit := lorentzAnchor_of_causal hα
  euclidCosReal := euclidCosReal_of_causal hα
  euclidAnchor := euclidAnchor_of_causal hα
  lorentzAnchor := lorentzAnchor_of_causal hα
  rapidityPinned := rapidityPinned_of_causal hα
  euclidSchlaefli := euclidSchlaefli_field_inhabited hα

/-! ## §F3a. Succession terminal (V2) + V1 retirement -/

/-- Ledger-named V2 terminal. Family conjunct plus the physical coupling
`α = 1`. Succeeds the frozen V1 terminal `wick_action_continuation_4d`,
which is provably unsatisfiable (`not_wick_action_continuation_4d`).

Honesty: `euclidSchlaefli` is differentiability-only on the one-hinge
MODEL; classical multi-hinge Schläfli cancellation is not claimed. -/
def wick_action_continuation_4d_v2 : Prop :=
  (∀ α : ℝ, (7 / 12 : ℝ) < α → WickActionContinuationCertV2 α) ∧
    WickActionContinuationCertV2 1

theorem wick_action_continuation_4d_v2_holds :
    wick_action_continuation_4d_v2 :=
  ⟨fun _α hα => wickActionContinuationCertV2_of_causal hα,
    wickActionContinuationCertV2_one⟩

/-- V1 terminal retirement: frozen `contAction` is unsatisfiable at α = 1. -/
theorem not_wick_action_continuation_4d : ¬ wick_action_continuation_4d := by
  intro h
  exact contAction_not_satisfiable_at_one h.2.contAction

/-- Family Prop alias inhabited by the V2 terminal's first conjunct. -/
theorem wick_action_continuation_v2_family_holds :
    wick_action_continuation_v2_family :=
  fun _α hα => wickActionContinuationCertV2_of_causal hα

end

end WickActionInteriorHinge
end SevenGaps
end Gravity
end IndisputableMonolith
