import Mathlib
import IndisputableMonolith.Patterns

/-!
# Grid expansion from the D=3 Boolean lattice

Physical voxels are `ℤ³`. Generation n of the dyadic grid is
`Fin 3 → Fin (2^n)`, with `8^n` cells. Linear scale doubles each
generation; volume octuples. Each cell has eight Boolean children.

A map from Q3 onto all voxels remains impossible
(`Q3PhysicalCovering.C05`). Expansion is refinement of the lattice,
not a covering by eight ticks.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace GridExpansion

open Patterns

/-- Physical voxel lattice. Definitionally `Fin 3 → ℤ`. -/
abbrev VoxelSpace := Fin 3 → ℤ

/-- Q3 configuration space. -/
abbrev Q3 := Pattern 3

/-- Generation-n dyadic grid: one `Fin (2^n)` coordinate per axis. -/
abbrev Grid (n : ℕ) := Fin 3 → Fin (2 ^ n)

theorem grid_card (n : ℕ) : Fintype.card (Grid n) = 8 ^ n := by
  have hfun : Fintype.card (Fin 3 → Fin (2 ^ n)) = (2 ^ n) ^ 3 := by
    simp [Fintype.card_fun, Fintype.card_fin]
  have hpow : (2 ^ n) ^ 3 = 8 ^ n := by
    calc
      (2 ^ n) ^ 3 = 2 ^ (n * 3) := by rw [← pow_mul]
      _ = 2 ^ (3 * n) := by rw [Nat.mul_comm]
      _ = (2 ^ 3) ^ n := by rw [pow_mul]
      _ = 8 ^ n := by norm_num
  simpa [Grid] using hfun.trans hpow

theorem generation_linear_scale (n : ℕ) :
    2 ^ (n + 1) = 2 ^ n * 2 :=
  pow_succ 2 n

theorem generation_volume_octuples (n : ℕ) :
    Fintype.card (Grid (n + 1)) = 8 * Fintype.card (Grid n) := by
  rw [grid_card, grid_card, pow_succ, Nat.mul_comm]

/-- Child of a generation-n cell along a Boolean offset. -/
def child {n : ℕ} (x : Grid n) (σ : Pattern 3) : Grid (n + 1) :=
  fun i =>
    let b : ℕ := bif σ i then 1 else 0
    have hlt : 2 * (x i).val + b < 2 ^ (n + 1) := by
      have hx : (x i).val < 2 ^ n := (x i).isLt
      have hb : b ≤ 1 := by
        cases hσ : σ i <;> simp [b, hσ]
      have : 2 * (x i).val + b ≤ 2 * (x i).val + 1 := Nat.add_le_add_left hb _
      have hbound : 2 * (x i).val + 1 < 2 ^ n * 2 := by
        have : 2 * (x i).val + 1 < 2 * 2 ^ n := by omega
        simpa [Nat.mul_comm] using this
      have hpow : 2 ^ n * 2 = 2 ^ (n + 1) := (pow_succ 2 n).symm
      omega
    ⟨2 * (x i).val + b, hlt⟩

theorem child_val {n : ℕ} (x : Grid n) (σ : Pattern 3) (i : Fin 3) :
    (child x σ i).val = 2 * (x i).val + bif σ i then 1 else 0 :=
  rfl

/-- The eight children of a cell are distinct. -/
theorem child_injective_in_offset {n : ℕ} (x : Grid n) :
    Function.Injective (child x) := by
  intro σ τ h
  funext i
  have hi := congrArg Fin.val (congrFun h i)
  simp [child_val] at hi
  cases hσ : σ i <;> cases hτ : τ i <;> simp [hσ, hτ] at hi ⊢

/-- The unique Boolean refinement doubles linear scale and octuples volume. -/
theorem dyadic_expansion (n : ℕ) :
    2 ^ (n + 1) = 2 ^ n * 2 ∧
      Fintype.card (Grid (n + 1)) = 8 * Fintype.card (Grid n) :=
  ⟨generation_linear_scale n, generation_volume_octuples n⟩

theorem voxelSpace_infinite : Infinite VoxelSpace :=
  Infinite.of_injective (fun n : ℤ => fun i : Fin 3 => if i = 0 then n else 0)
    (fun a b h => by
      have := congrFun h 0
      simpa using this)

/-- Eight ticks still cannot occupy the infinite lattice. -/
theorem ticks_do_not_cover_voxels (f : Q3 → VoxelSpace) :
    ¬ Function.Surjective f := by
  haveI : Infinite VoxelSpace := voxelSpace_infinite
  exact not_surjective_finite_infinite f

end GridExpansion
end Foundation
end IndisputableMonolith
