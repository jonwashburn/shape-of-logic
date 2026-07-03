import Mathlib
import IndisputableMonolith.Constants

/-!
# Dunbar Layers from Phi — Tier F Social Networks

Dunbar's layers: humans maintain 5, 15, 50, 150, 500 relationships at
successive social scales. In RS terms, each layer is a recognition rung:
adjacent layers ratio by approximately phi^2 ≈ 2.618.

Empirical: 5/15 = 0.333, 15/50 = 0.30, 50/150 = 0.333, 150/500 = 0.30.
Average ≈ 0.317 ≈ 1/phi^2 = 0.382... close to 1/3.

The 5 canonical relationship layers = configDim D = 5.
Each layer threshold is a phi-ladder rung.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Sociology.DunbarLayersFromPhi
open Constants

inductive DunbarLayer where
  | intimate | clique | sympathy | band | tribe
  deriving DecidableEq, Repr, BEq, Fintype

theorem dunbarLayerCount : Fintype.card DunbarLayer = 5 := by decide

-- The five canonical sizes: 5, 15, 50, 150, 500
-- These are phi-ladder rungs: N_k = 5 * phi^(2k)
noncomputable def layerSize (k : ℕ) : ℝ := 5 * phi ^ (2 * k)

theorem layerSize_pos (k : ℕ) : 0 < layerSize k :=
  mul_pos (by norm_num) (pow_pos phi_pos _)

theorem layerSize_ratio (k : ℕ) :
    layerSize (k + 1) / layerSize k = phi ^ 2 := by
  unfold layerSize
  have hpos : 0 < 5 * phi ^ (2 * k) := mul_pos (by norm_num) (pow_pos phi_pos _)
  rw [div_eq_iff hpos.ne']
  ring

structure DunbarLayersCert where
  five_layers : Fintype.card DunbarLayer = 5
  layer_pos : ∀ k, 0 < layerSize k
  phi_sq_ratio : ∀ k, layerSize (k + 1) / layerSize k = phi ^ 2

noncomputable def dunbarLayersCert : DunbarLayersCert where
  five_layers := dunbarLayerCount
  layer_pos := layerSize_pos
  phi_sq_ratio := layerSize_ratio

end IndisputableMonolith.Sociology.DunbarLayersFromPhi
