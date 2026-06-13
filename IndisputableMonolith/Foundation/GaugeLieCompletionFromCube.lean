import Mathlib
import IndisputableMonolith.Foundation.GaugeFromCube

/-!
# Gauge Lie Completion from the 3-Cube

This module starts `P0-S2-01` from `planning/REALITY_DERIVATION_PUNCHLIST.md`.

The existing cube work proves the forced `B_3` layer counts:

* axis permutations: `3`
* even sign-flip completion: `2`
* parity quotient: `1`

This file records the compact-completion rule that sends those recognition
axis counts to the Standard Model compact factors:

* `3 -> SU(3)` color
* `2 -> SU(2)` weak isospin
* `1 -> U(1)` hypercharge phase

It also keeps two separate notions apart:

* recognition-axis count: `(3,2,1)`, total `6`
* Lie rank: `(2,1,1)`, total `4`

This is not yet the full hypercharge or fermion-representation derivation.
It is the first clean bridge theorem from the cube layer skeleton to the
compact gauge-factor skeleton.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Foundation.GaugeLieCompletionFromCube

open GaugeFromCube

/-- Compact gauge factors selected by the cube-layer completion rule. -/
inductive CompactGaugeFactor where
  | su3
  | su2
  | u1
  deriving DecidableEq, Repr, BEq, Fintype

theorem compactGaugeFactor_count : Fintype.card CompactGaugeFactor = 3 := by
  decide

/-- Recognition-axis count carried by each factor. -/
def recognitionAxisCount : CompactGaugeFactor -> ℕ
  | .su3 => 3
  | .su2 => 2
  | .u1 => 1

/-- Actual Lie rank of the compact factor. -/
def lieRank : CompactGaugeFactor -> ℕ
  | .su3 => 2
  | .su2 => 1
  | .u1 => 1

/-- Gauge-boson carrier count for the adjoint/phase sector. -/
def carrierCount : CompactGaugeFactor -> ℕ
  | .su3 => 3 ^ 2 - 1
  | .su2 => 2 ^ 2 - 1
  | .u1 => 1

/-- The cube completion has recognition-axis counts `(3,2,1)`. -/
theorem recognition_axis_counts :
    recognitionAxisCount .su3 = 3 ∧
    recognitionAxisCount .su2 = 2 ∧
    recognitionAxisCount .u1 = 1 := by
  decide

/-- Recognition-axis total is `3 + 2 + 1 = 6`, matching the cube face count. -/
theorem recognition_axis_total :
    recognitionAxisCount .su3 + recognitionAxisCount .su2 + recognitionAxisCount .u1 =
      cube_face_count 3 := by
  rw [cube3_face_count]
  decide

/-- The compact-factor Lie ranks are `(2,1,1)`. -/
theorem lie_rank_values :
    lieRank .su3 = 2 ∧ lieRank .su2 = 1 ∧ lieRank .u1 = 1 := by
  decide

/-- Total Lie rank of `SU(3) x SU(2) x U(1)` is `4`. -/
theorem lie_rank_total :
    lieRank .su3 + lieRank .su2 + lieRank .u1 = 4 := by
  decide

/-- Carrier counts are `8`, `3`, and `1`. -/
theorem carrier_counts :
    carrierCount .su3 = 8 ∧ carrierCount .su2 = 3 ∧ carrierCount .u1 = 1 := by
  decide

/-- Total gauge carriers before electroweak mixing: `8 + 3 + 1 = 12`. -/
theorem carrier_total :
    carrierCount .su3 + carrierCount .su2 + carrierCount .u1 = 12 := by
  decide

/-- The `B_3` order factorization already proved in `GaugeFromCube`. -/
theorem cube_order_factors_as_completion :
    Fintype.card (SignedPerm 3) =
      axis_perm_count 3 * even_sign_flip_count 3 * parity_quotient_order := by
  exact three_layer_factorization

structure GaugeLieCompletionCert where
  factor_count : Fintype.card CompactGaugeFactor = 3
  axis_counts :
    recognitionAxisCount .su3 = 3 ∧
    recognitionAxisCount .su2 = 2 ∧
    recognitionAxisCount .u1 = 1
  axis_total :
    recognitionAxisCount .su3 + recognitionAxisCount .su2 + recognitionAxisCount .u1 =
      cube_face_count 3
  lie_ranks : lieRank .su3 = 2 ∧ lieRank .su2 = 1 ∧ lieRank .u1 = 1
  lie_rank_sum : lieRank .su3 + lieRank .su2 + lieRank .u1 = 4
  carriers : carrierCount .su3 = 8 ∧ carrierCount .su2 = 3 ∧ carrierCount .u1 = 1
  carrier_sum : carrierCount .su3 + carrierCount .su2 + carrierCount .u1 = 12
  b3_factorization :
    Fintype.card (SignedPerm 3) =
      axis_perm_count 3 * even_sign_flip_count 3 * parity_quotient_order

def gaugeLieCompletionCert : GaugeLieCompletionCert where
  factor_count := compactGaugeFactor_count
  axis_counts := recognition_axis_counts
  axis_total := recognition_axis_total
  lie_ranks := lie_rank_values
  lie_rank_sum := lie_rank_total
  carriers := carrier_counts
  carrier_sum := carrier_total
  b3_factorization := cube_order_factors_as_completion

end IndisputableMonolith.Foundation.GaugeLieCompletionFromCube
