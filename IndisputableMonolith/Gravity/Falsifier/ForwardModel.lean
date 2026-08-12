import Mathlib
import IndisputableMonolith.Gravity.Falsifier.GbareReadings

/-!
# ForwardModel: the predicted weight dip as a function of drive parameters

Part of the Nautilus `Gravity/Falsifier/` DAG (panel verdict 2026-07-03).

`GravitationalPrepaidChannel.lift_priced` gives `(1 - w_g)·Gbare = prepaid`, so the
fractional weight dip is `1 - w_g = prepaid/Gbare`. The emitter budget bounds the posted
recognition cost by `prepaid ≤ η·P·τ` (`EmitterWindow.BudgetedWindowChannel`: efficiency
`η ∈ [0,1]`, drive power `P` watts, window `τ` seconds, converted to events). Composing the
two gives the forward model: an UPPER BOUND on the observable dip in terms of quantities an
experimenter sets (`η, P, τ`) and the disputed denominator `Gbare`.

    dip = prepaid / Gbare ≤ (η·P·τ) / Gbare =: dip_forward_model

This is the experiment's design equation. Its numeric value is decided by which `Gbare`
reading holds (`GbareReadings`); the discriminator (`MassVoxelDiscriminator`) tells them
apart from the mass-scaling of the measured dip.

## Status: THEOREM (the bound), conditional on the emitter budget hypothesis.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Falsifier

noncomputable section

/-- The observable fractional weight dip `1 - w_g = prepaid / Gbare`. -/
noncomputable def dip (prepaid Gbare : ℝ) : ℝ := prepaid / Gbare

/-- The forward-model dip ceiling: the maximal dip the emitter budget `η·P·τ` can buy on
    a bare path `Gbare`. -/
noncomputable def dip_forward_model (eta P tau Gbare : ℝ) : ℝ :=
  eta * P * tau / Gbare

/-- **The forward model bounds the observable dip.** Given the emitter budget cap
    `prepaid ≤ η·P·τ` and a positive bare path, the measured dip cannot exceed the
    model ceiling. This is the design inequality: to see a dip of `d`, the drive must
    supply `η·P·τ ≥ d·Gbare`. -/
theorem dip_le_forward_model
    (prepaid eta P tau Gbare : ℝ)
    (hGbare : 0 < Gbare) (hbudget : prepaid ≤ eta * P * tau) :
    dip prepaid Gbare ≤ dip_forward_model eta P tau Gbare := by
  unfold dip dip_forward_model
  exact div_le_div_of_nonneg_right hbudget hGbare.le

/-- The dip is nonnegative for a nonnegative posted cost. -/
theorem dip_nonneg (prepaid Gbare : ℝ) (hp : 0 ≤ prepaid) (hG : 0 < Gbare) :
    0 ≤ dip prepaid Gbare := by
  unfold dip
  exact div_nonneg hp hG.le

/-- **The dip is strictly anti-monotone in the bare path.** A larger `Gbare` (e.g. the
    rest-energy reading vs the voxel reading) gives a strictly smaller dip at fixed posted
    cost: the same drive buys less lift on a heavier recognition schedule. This is what
    makes the three `Gbare` readings observationally distinct. -/
theorem dip_strict_anti_Gbare
    (prepaid G₁ G₂ : ℝ) (hp : 0 < prepaid) (hG₁ : 0 < G₁) (hlt : G₁ < G₂) :
    dip prepaid G₂ < dip prepaid G₁ := by
  unfold dip
  exact div_lt_div_of_pos_left hp hG₁ hlt

/-- Certificate: the forward model is a genuine dip ceiling — it bounds the observable
    dip under the emitter budget, is nonnegative, and is strictly decreasing in the bare
    path (so the three `Gbare` readings are observationally distinct). -/
structure ForwardModelCert : Prop where
  bound : ∀ prepaid eta P tau Gbare : ℝ, 0 < Gbare → prepaid ≤ eta * P * tau →
    dip prepaid Gbare ≤ dip_forward_model eta P tau Gbare
  nonneg : ∀ prepaid Gbare : ℝ, 0 ≤ prepaid → 0 < Gbare → 0 ≤ dip prepaid Gbare
  anti : ∀ prepaid G₁ G₂ : ℝ, 0 < prepaid → 0 < G₁ → G₁ < G₂ →
    dip prepaid G₂ < dip prepaid G₁

theorem forwardModelCert : ForwardModelCert where
  bound := dip_le_forward_model
  nonneg := dip_nonneg
  anti := dip_strict_anti_Gbare

end

end Falsifier
end Gravity
end IndisputableMonolith
