import Mathlib
import IndisputableMonolith.Cost

/-!
# C16: J-Cost Positivity Universality — Wave 63 Cross-Domain

Structural claim extending C7: the same single lemma `Jcost_pos_of_ne_one`
is the source of non-equilibrium cost in every RS domain where J-cost
applies. This is the off-equilibrium analogue of C7 (which covered
equilibrium Jcost(1) = 0).

Universal lemma: for any r ∈ (0, ∞) with r ≠ 1, J(r) > 0.

Specialisations (all the same theorem with domain labels):
  • Turbulent flow cost in hydrodynamics
  • Disease cost in medicine (deviation from homeostasis)
  • Off-target cost in CRISPR (imperfect guide match)
  • Off-equilibrium game theory
  • Market arbitrage gap
  • Biased reasoning (cognitive biases)
  • Recognition deficit (neurodevelopmental)

All are definitionally the same proposition: `∀ r, 0 < r → r ≠ 1 → 0 < J r`.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.CrossDomain.JPositivityUniversality

open IndisputableMonolith.Cost

/-- The universal non-equilibrium cost claim (definitional specialisation
    of `Jcost_pos_of_ne_one`). -/
def TurbulentCost : Prop := ∀ r : ℝ, 0 < r → r ≠ 1 → 0 < Jcost r
def DiseaseCost : Prop := ∀ r : ℝ, 0 < r → r ≠ 1 → 0 < Jcost r
def OffTargetCost : Prop := ∀ r : ℝ, 0 < r → r ≠ 1 → 0 < Jcost r
def OffEquilibriumGameCost : Prop := ∀ r : ℝ, 0 < r → r ≠ 1 → 0 < Jcost r
def MarketArbitrageGap : Prop := ∀ r : ℝ, 0 < r → r ≠ 1 → 0 < Jcost r
def BiasedReasoningCost : Prop := ∀ r : ℝ, 0 < r → r ≠ 1 → 0 < Jcost r
def RecognitionDeficit : Prop := ∀ r : ℝ, 0 < r → r ≠ 1 → 0 < Jcost r

theorem turbulent_cost : TurbulentCost := fun r hr hne => Jcost_pos_of_ne_one r hr hne
theorem disease_cost : DiseaseCost := fun r hr hne => Jcost_pos_of_ne_one r hr hne
theorem off_target_cost : OffTargetCost := fun r hr hne => Jcost_pos_of_ne_one r hr hne
theorem off_equilibrium_game_cost : OffEquilibriumGameCost :=
  fun r hr hne => Jcost_pos_of_ne_one r hr hne
theorem market_arbitrage_gap : MarketArbitrageGap :=
  fun r hr hne => Jcost_pos_of_ne_one r hr hne
theorem biased_reasoning_cost : BiasedReasoningCost :=
  fun r hr hne => Jcost_pos_of_ne_one r hr hne
theorem recognition_deficit : RecognitionDeficit :=
  fun r hr hne => Jcost_pos_of_ne_one r hr hne

/-! ## Universality: all seven are definitionally the same proposition. -/

theorem all_seven_are_one :
    TurbulentCost = DiseaseCost ∧
    DiseaseCost = OffTargetCost ∧
    OffTargetCost = OffEquilibriumGameCost ∧
    OffEquilibriumGameCost = MarketArbitrageGap ∧
    MarketArbitrageGap = BiasedReasoningCost ∧
    BiasedReasoningCost = RecognitionDeficit :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- J-cost is symmetric around r = 1: J(r) = J(r⁻¹). -/
theorem symmetry_at_equilibrium (r : ℝ) (hr : 0 < r) : Jcost r = Jcost r⁻¹ :=
  Jcost_symm hr

/-- The minimum of J on (0, ∞) is at r = 1, value 0. -/
theorem minimum_at_one : ∀ r : ℝ, 0 < r → Jcost 1 ≤ Jcost r := by
  intro r hr
  rw [Jcost_unit0]
  rcases eq_or_ne r 1 with heq | hne
  · rw [heq, Jcost_unit0]
  · exact le_of_lt (Jcost_pos_of_ne_one r hr hne)

structure JPositivityUniversalityCert where
  turbulent : TurbulentCost
  disease : DiseaseCost
  off_target : OffTargetCost
  off_game : OffEquilibriumGameCost
  arbitrage : MarketArbitrageGap
  biased : BiasedReasoningCost
  deficit : RecognitionDeficit
  all_same : TurbulentCost = DiseaseCost ∧
             DiseaseCost = OffTargetCost ∧
             OffTargetCost = OffEquilibriumGameCost ∧
             OffEquilibriumGameCost = MarketArbitrageGap ∧
             MarketArbitrageGap = BiasedReasoningCost ∧
             BiasedReasoningCost = RecognitionDeficit
  minimum_at_1 : ∀ r : ℝ, 0 < r → Jcost 1 ≤ Jcost r
  symmetry : ∀ r : ℝ, 0 < r → Jcost r = Jcost r⁻¹

def jPositivityUniversalityCert : JPositivityUniversalityCert where
  turbulent := turbulent_cost
  disease := disease_cost
  off_target := off_target_cost
  off_game := off_equilibrium_game_cost
  arbitrage := market_arbitrage_gap
  biased := biased_reasoning_cost
  deficit := recognition_deficit
  all_same := all_seven_are_one
  minimum_at_1 := minimum_at_one
  symmetry := symmetry_at_equilibrium

end IndisputableMonolith.CrossDomain.JPositivityUniversality
