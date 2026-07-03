import IndisputableMonolith.Cost.Ndim.Hessian

/-!
# Radical distribution for the rank-one log-coordinate metric

The log-coordinate Hessian only detects the single active direction `α`.
Its radical distribution is therefore the constant hyperplane `dot α v = 0`.

We formalize this distribution and its integrability via affine leaves
`{ t | dot α t = c }`.
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

open scoped BigOperators

/-- The radical distribution of the rank-one Hessian metric. -/
def Radical {n : ℕ} (α : Vec n) : Set (Vec n) :=
  { v | dot α v = 0 }

/-- The affine leaves orthogonal to the active direction. -/
def LevelSet {n : ℕ} (α : Vec n) (c : ℝ) : Set (Vec n) :=
  { t | dot α t = c }

/-- Affine translation along a constant direction. -/
def affineShift {n : ℕ} (t v : Vec n) (s : ℝ) : Vec n :=
  fun i => t i + s * v i

@[simp] theorem mem_Radical_iff {n : ℕ} (α : Vec n) (v : Vec n) :
    v ∈ Radical α ↔ dot α v = 0 := Iff.rfl

@[simp] theorem mem_LevelSet_iff {n : ℕ} (α : Vec n) (c : ℝ) (t : Vec n) :
    t ∈ LevelSet α c ↔ dot α t = c := Iff.rfl

@[simp] theorem zero_mem_Radical {n : ℕ} (α : Vec n) :
    (fun _ => 0 : Vec n) ∈ Radical α := by
  unfold Radical dot
  simp

theorem add_mem_Radical {n : ℕ} (α : Vec n) {v w : Vec n}
    (hv : v ∈ Radical α) (hw : w ∈ Radical α) :
    v + w ∈ Radical α := by
  unfold Radical dot at hv hw ⊢
  have hv0 : ∑ i : Fin n, α i * v i = 0 := hv
  have hw0 : ∑ i : Fin n, α i * w i = 0 := hw
  calc
    ∑ i : Fin n, α i * (v i + w i)
        = (∑ i : Fin n, α i * v i) + ∑ i : Fin n, α i * w i := by
            simp [mul_add, Finset.sum_add_distrib]
    _ = 0 := by rw [hv0, hw0]; ring

theorem smul_mem_Radical {n : ℕ} (α : Vec n) {v : Vec n} (s : ℝ)
    (hv : v ∈ Radical α) :
    s • v ∈ Radical α := by
  unfold Radical dot at hv ⊢
  calc
    ∑ i : Fin n, α i * (s * v i)
        = s * ∑ i : Fin n, α i * v i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = 0 := by rw [hv]; ring

theorem sub_mem_Radical {n : ℕ} (α : Vec n) {v w : Vec n}
    (hv : v ∈ Radical α) (hw : w ∈ Radical α) :
    v - w ∈ Radical α := by
  simpa [sub_eq_add_neg] using
    add_mem_Radical α hv (smul_mem_Radical α (-1) hw)

/-- The Hessian quadratic form vanishes exactly on the radical distribution. -/
theorem quadraticHessian_eq_zero_iff {n : ℕ} (α t v : Vec n) :
    quadraticHessian α t v = 0 ↔ v ∈ Radical α := by
  rw [quadraticHessian_eq]
  constructor
  · intro hq
    unfold Radical
    have hcosh : 0 < Real.cosh (dot α t) := by positivity
    have hsq : (dot α v) ^ 2 = 0 := by
      exact (mul_eq_zero.mp (by simpa using hq)).resolve_left hcosh.ne'
    have hdot : dot α v = 0 := sq_eq_zero_iff.mp hsq
    exact hdot
  · intro hv
    rw [mem_Radical_iff] at hv
    simp [hv]

/-- Weighted dot product along an affine shift. -/
theorem dot_affineShift {n : ℕ} (α t v : Vec n) (s : ℝ) :
    dot α (affineShift t v s) = dot α t + s * dot α v := by
  unfold dot affineShift
  calc
    ∑ i : Fin n, α i * (t i + s * v i)
        = ∑ i : Fin n, (α i * t i + s * (α i * v i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = (∑ i : Fin n, α i * t i) + s * ∑ i : Fin n, α i * v i := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Directions in the radical stay inside the affine leaves `dot α = c`. -/
theorem affineShift_mem_LevelSet {n : ℕ} (α : Vec n) {c s : ℝ} {t v : Vec n}
    (ht : t ∈ LevelSet α c) (hv : v ∈ Radical α) :
    affineShift t v s ∈ LevelSet α c := by
  rw [mem_LevelSet_iff] at ht ⊢
  have hv' : dot α v = 0 := hv
  rw [dot_affineShift, ht, hv']
  ring

/-- The radical distribution is integrable: its integral leaves are the affine
hyperplanes `dot α = c`. -/
theorem radical_integrable_by_affine_leaves {n : ℕ} (α : Vec n) (c : ℝ) :
    ∀ ⦃t v : Vec n⦄, t ∈ LevelSet α c → v ∈ Radical α →
      ∀ s : ℝ, affineShift t v s ∈ LevelSet α c := by
  intro t v ht hv s
  exact affineShift_mem_LevelSet α ht hv

/-- A constant direction preserves the affine leaf through `t` exactly when it
lies in the radical distribution. -/
theorem preserves_own_leaf_iff_mem_Radical {n : ℕ} (α t v : Vec n) :
    (∀ s : ℝ, affineShift t v s ∈ LevelSet α (dot α t)) ↔ v ∈ Radical α := by
  constructor
  · intro h
    have h1 := h 1
    rw [mem_LevelSet_iff, dot_affineShift] at h1
    unfold Radical
    have : dot α v = 0 := by linarith
    exact this
  · intro hv s
    exact affineShift_mem_LevelSet α (by simp [LevelSet]) hv

end Ndim
end Cost
end IndisputableMonolith
