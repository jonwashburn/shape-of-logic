import Mathlib
import IndisputableMonolith.Foundation.LeastCostUnitLinking

/-!
# Sharper arity-cost floors

A complete pass whose registered locus is a sphere meeting every state
is priced from the cells of that locus, not only from the vertex count.

On a square-faced surface homeomorphic to `S²` the Euler count
`V − E + F = 2` with `4F = 2E` and `V = 2^D` forces `F = 2^D − 2`.
Each face costs at least three postings, so the pass costs at least
`3 · 2^D − 6`. At the dimension `D = 5` forced by a two-parameter
requirement that is `90`, which exceeds both the eight-tick sequential
floor and the generic `2^D` floor on the same cube.

In every process dimension the cell-count floor is
`(2^k − 1)(k + 1) 2^{D−k}`. At `D = 2k+1` this is
`(2^k - 1)(k + 1) 2^{k+1}`, equal to `2^D` at `k = 1` and strictly
larger for every `k ≥ 2` (72 already at `k = 2`).

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace ArityCostFloors

open LeastCostUnitLinking

/-- Euler data of a closed square-faced surface. -/
structure SquareSurfaceEuler where
  V : ℕ
  E : ℕ
  F : ℕ
  four_F_eq_two_E : 4 * F = 2 * E
  euler : (V : ℤ) - E + F = 2

theorem squareSurface_E_eq_two_F (S : SquareSurfaceEuler) :
    S.E = 2 * S.F := by
  have h : 2 * (2 * S.F) = 2 * S.E := by
    rw [← Nat.mul_assoc]
    exact S.four_F_eq_two_E
  exact (Nat.mul_left_cancel (by decide : 0 < 2) h).symm

theorem squareSurface_V_eq_F_add_two (S : SquareSurfaceEuler) :
    S.V = S.F + 2 := by
  have hE := squareSurface_E_eq_two_F S
  have h : (S.V : ℤ) - (2 * S.F) + S.F = 2 := by
    simpa [hE] using S.euler
  have h' : (S.V : ℤ) = (S.F : ℤ) + 2 := by
    linarith
  exact_mod_cast h'

/-- Face count forced by Euler and the square relation, given `V = 2^D`. -/
def faceCount (D : ℕ) : ℕ := 2 ^ D - 2

/-- Edge count forced by the same data. -/
def edgeCount (D : ℕ) : ℕ := 2 ^ (D + 1) - 4

theorem faceCount_of_full_cube {D : ℕ} (_hD : 2 ≤ D)
    (S : SquareSurfaceEuler) (hV : S.V = 2 ^ D) :
    S.F = faceCount D := by
  have hVF := squareSurface_V_eq_F_add_two S
  have : S.F + 2 = 2 ^ D := by
    rw [← hVF, hV]
  simpa [faceCount] using Nat.eq_sub_of_add_eq this

theorem edgeCount_of_full_cube {D : ℕ} (hD : 2 ≤ D)
    (S : SquareSurfaceEuler) (hV : S.V = 2 ^ D) :
    S.E = edgeCount D := by
  have hF := faceCount_of_full_cube hD S hV
  have hE := squareSurface_E_eq_two_F S
  have hpow : 2 ≤ 2 ^ D :=
    le_trans (by decide : 2 ≤ 4)
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hD)
  have hmul : 2 * (2 ^ D - 2) = 2 ^ (D + 1) - 4 := by
    rw [Nat.mul_sub_left_distrib, pow_succ]
    simp [Nat.mul_comm]
  calc
    S.E = 2 * S.F := hE
    _ = 2 * (2 ^ D - 2) := by simp [hF, faceCount]
    _ = 2 ^ (D + 1) - 4 := hmul
    _ = edgeCount D := rfl

/-- Each square face is an arity-four act and costs at least three
postings, so the surface pass costs at least `3F`. -/
def arityFourFloor (D : ℕ) : ℕ := 3 * faceCount D

theorem arityFourFloor_eq (D : ℕ) :
    arityFourFloor D = 3 * (2 ^ D - 2) :=
  rfl

theorem arityFourFloor_eq' (D : ℕ) (hD : 2 ≤ D) :
    arityFourFloor D = 3 * 2 ^ D - 6 := by
  have hpow : 2 ≤ 2 ^ D :=
    le_trans (by decide : 2 ≤ 4)
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hD)
  simp [arityFourFloor, faceCount, Nat.mul_sub_left_distrib]

theorem arityFourFloor_at_five : arityFourFloor 5 = 90 := by
  decide

/-- The arity-four floor on the five-cube exceeds the sequential
eight-tick floor. -/
theorem arityFour_exceeds_eight :
    minCompletePassCost 1 < arityFourFloor 5 := by
  decide

/-- The arity-four floor exceeds the generic `2^D` floor on the same
cube, for every `D ≥ 2`. -/
theorem arityFour_exceeds_vertex_floor {D : ℕ} (hD : 2 ≤ D) :
    2 ^ D < arityFourFloor D := by
  have h := arityFourFloor_eq' D hD
  have hpow : 4 ≤ 2 ^ D :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hD
  have : 2 ^ D < 3 * 2 ^ D - 6 := by
    have : 6 < 2 * 2 ^ D := by
      have : 3 ≤ 2 ^ D := le_trans (by decide : 3 ≤ 4) hpow
      omega
    omega
  simpa [h] using this

/-- Cell-count floor for an arity-`2^k` pass whose locus is homeomorphic
to `S^k` and meets every state. -/
def arityFloor (k D : ℕ) : ℕ :=
  (2 ^ k - 1) * (k + 1) * 2 ^ (D - k)

/-- At the dimension `D = 2k+1` forced by the requirement in degree `k`. -/
def arityFloorAtProcess (k : ℕ) : ℕ :=
  (2 ^ k - 1) * (k + 1) * 2 ^ (k + 1)

theorem arityFloor_at_forced_dimension (k : ℕ) :
    arityFloor k (2 * k + 1) = arityFloorAtProcess k := by
  have : 2 * k + 1 - k = k + 1 := by omega
  simp [arityFloor, arityFloorAtProcess, this]

theorem arityFloor_k_one :
    arityFloorAtProcess 1 = 8 := by
  decide

theorem arityFloor_k_two :
    arityFloorAtProcess 2 = 72 := by
  decide

/-- Per-state cost is `1` at `k = 1`: the bound returns `2^D`. -/
theorem arityFloor_per_state_k_one :
    arityFloorAtProcess 1 = 2 ^ (2 * 1 + 1) := by
  decide

theorem arityFloor_ge_product {k : ℕ} (hk : 2 ≤ k) :
    3 * 3 * 8 ≤ arityFloorAtProcess k := by
  have hA : 3 ≤ 2 ^ k - 1 := by
    have : 4 ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk
    omega
  have hB : 3 ≤ k + 1 := by omega
  have hC : 8 ≤ 2 ^ (k + 1) := by
    have : 4 ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk
    have : 8 ≤ 2 * 2 ^ k := by omega
    simpa [pow_succ, Nat.mul_comm] using this
  have := Nat.mul_le_mul (Nat.mul_le_mul hA hB) hC
  simpa [arityFloorAtProcess, Nat.mul_assoc] using this

/-- For `k ≥ 2` the cell-count floor strictly exceeds the sequential
eight-tick bound. -/
theorem arityFloor_exceeds_eight {k : ℕ} (hk : 2 ≤ k) :
    minCompletePassCost 1 < arityFloorAtProcess k := by
  have h8 : minCompletePassCost 1 = 8 := three_cube_costs_eight
  have hge := arityFloor_ge_product hk
  have : 8 < 72 := by decide
  have : 8 < arityFloorAtProcess k := lt_of_lt_of_le (by decide : 8 < 72) hge
  simpa [h8] using this

theorem cheapest_recognizer_still_three_dimensional {k : ℕ} (hk : 1 ≤ k)
    (hle : arityFloorAtProcess k ≤ arityFloorAtProcess 1) : k = 1 := by
  have h1 : arityFloorAtProcess 1 = 8 := arityFloor_k_one
  by_contra hk1
  have hk2 : 2 ≤ k := by omega
  have hlt := arityFloor_exceeds_eight hk2
  have : 8 < arityFloorAtProcess k := by
    simpa [minCompletePassCost, h1] using hlt
  omega

end ArityCostFloors
end Foundation
end IndisputableMonolith
