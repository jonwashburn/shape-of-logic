import IndisputableMonolith.Cost.Ndim.Core

/-!
# Affine connections in `x`- and `t`-coordinates

The `t = log x` coordinates are affine-flat by construction. When pulled back
to `x`-coordinates, the same flat connection acquires the familiar diagonal
Christoffel term `Γⁱ_{ii} = -1 / xᵢ`.

This module records those coefficient formulas and proves the basic projective
equivalence dichotomy: the one-dimensional case is projectively equivalent to
the zero connection, while in dimensions `n ≥ 2` this fails.
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

/-- The Kronecker delta on `Fin n`. -/
def delta {n : ℕ} (i j : Fin n) : ℝ :=
  if i = j then 1 else 0

/-- The flat affine connection in `x`-coordinates. -/
def xFlatConnection {n : ℕ} (_x : Vec n) (_i _j _k : Fin n) : ℝ := 0

/-- The flat `t`-connection pulled back through `tᵢ = log xᵢ`. -/
noncomputable def tPulledConnection {n : ℕ} (x : Vec n) (i j k : Fin n) : ℝ :=
  if i = j ∧ j = k then -(x i)⁻¹ else 0

/-- Projective equivalence to the zero connection. -/
def ProjectivelyEquivalentToZeroAt {n : ℕ}
    (Γ : Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∃ ψ : Vec n, ∀ i j k : Fin n,
    Γ i j k = delta i j * ψ k + delta i k * ψ j

@[simp] theorem xFlatConnection_apply {n : ℕ} (x : Vec n) (i j k : Fin n) :
    xFlatConnection x i j k = 0 := rfl

theorem tPulledConnection_diag {n : ℕ} (x : Vec n) (i : Fin n) :
    tPulledConnection x i i i = -(x i)⁻¹ := by
  unfold tPulledConnection
  simp

theorem tPulledConnection_offDiag {n : ℕ} (x : Vec n) {i j k : Fin n}
    (hijk : ¬ (i = j ∧ j = k)) :
    tPulledConnection x i j k = 0 := by
  unfold tPulledConnection
  simp [hijk]

theorem projectivelyEquivalent_one_dim {x : Vec 1} :
    ProjectivelyEquivalentToZeroAt (tPulledConnection x) := by
  refine ⟨fun _ => -((x 0)⁻¹) / 2, ?_⟩
  intro i j k
  fin_cases i
  fin_cases j
  fin_cases k
  simp [delta, tPulledConnection]

theorem not_projectivelyEquivalentToZeroAt_tPulledConnection {n : ℕ}
    (hn : 2 ≤ n) (x : Vec n) (hx : ∀ i : Fin n, x i ≠ 0) :
    ¬ ProjectivelyEquivalentToZeroAt (tPulledConnection x) := by
  let i0 : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩
  let i1 : Fin n := ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hn⟩
  have hi01 : i0 ≠ i1 := by
    simp [i0, i1]
  intro hproj
  rcases hproj with ⟨ψ, hψ⟩
  have hpsi1 : ψ i1 = 0 := by
    have h := hψ i0 i0 i1
    simpa [eq_comm, delta, tPulledConnection, hi01] using h
  have hdiag : tPulledConnection x i1 i1 i1 = delta i1 i1 * ψ i1 + delta i1 i1 * ψ i1 := by
    simpa using hψ i1 i1 i1
  have hxinv_zero : (x i1)⁻¹ = 0 := by
    have h' : -(x i1)⁻¹ = 0 := by
      simpa [delta, tPulledConnection, hpsi1] using hdiag
    exact neg_eq_zero.mp h'
  exact (inv_ne_zero (hx i1)) hxinv_zero

end Ndim
end Cost
end IndisputableMonolith
