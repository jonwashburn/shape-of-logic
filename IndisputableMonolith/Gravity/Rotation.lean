import Mathlib

namespace IndisputableMonolith
namespace Gravity
namespace Rotation

/-- Rotation system with gravitational constant G and enclosed mass function `Menc`. -/
structure RotSys where
  G : ℝ
  posG : 0 < G
  Menc : ℝ → ℝ
  nonnegM : ∀ r, 0 ≤ Menc r

/-- Rotation velocity as a function of radius. -/
noncomputable def vrot (S : RotSys) (r : ℝ) : ℝ :=
  Real.sqrt (S.G * S.Menc r / r)

/-- Centripetal acceleration as a function of radius. -/
noncomputable def g (S : RotSys) (r : ℝ) : ℝ :=
  (vrot S r) ^ 2 / r

/-- Algebraic identity: `vrot^2 = G Menc / r` for `r > 0`. -/
lemma vrot_sq (S : RotSys) {r : ℝ} (hr : 0 < r) :
  (vrot S r) ^ 2 = S.G * S.Menc r / r := by
  dsimp [vrot]
  have hnum_nonneg : 0 ≤ S.G * S.Menc r := by
    have hM : 0 ≤ S.Menc r := S.nonnegM r
    exact mul_nonneg (le_of_lt S.posG) hM
  have hfrac_nonneg : 0 ≤ S.G * S.Menc r / r := by
    exact div_nonneg hnum_nonneg (le_of_lt hr)
  calc
    (Real.sqrt (S.G * S.Menc r / r)) ^ 2 = S.G * S.Menc r / r := by
      rw [Real.sq_sqrt hfrac_nonneg]

/-- If the enclosed mass grows linearly, `Menc(r) = α r` with `α ≥ 0`, then the rotation curve is flat:
    `vrot(r) = √(G α)` for all `r > 0`. -/
lemma vrot_flat_of_linear_Menc (S : RotSys) (α : ℝ)
  (hlin : ∀ {r : ℝ}, 0 < r → S.Menc r = α * r) :
  ∀ {r : ℝ}, 0 < r → vrot S r = Real.sqrt (S.G * α) := by
  intro r hr
  have hM : S.Menc r = α * r := hlin hr
  have hrne : r ≠ 0 := ne_of_gt hr
  have hfrac : S.G * S.Menc r / r = S.G * α := by
    calc
      S.G * S.Menc r / r = S.G * (α * r) / r := by rw [hM]
      _ = S.G * α * r / r := by ring
      _ = S.G * α := by field_simp [hrne]
  dsimp [vrot]
  rw [hfrac]

/-- Under linear mass growth `Menc(r) = α r`, the centripetal acceleration scales as `g(r) = (G α)/r`. -/
lemma g_of_linear_Menc (S : RotSys) (α : ℝ)
  (hlin : ∀ {r : ℝ}, 0 < r → S.Menc r = α * r) :
  ∀ {r : ℝ}, 0 < r → g S r = (S.G * α) / r := by
  intro r hr
  have hM : S.Menc r = α * r := hlin hr
  have hrne : r ≠ 0 := ne_of_gt hr
  dsimp [g]
  have hvrot_sq : (vrot S r) ^ 2 = S.G * α := by
    have hfrac : S.G * S.Menc r / r = S.G * α := by
      calc
        S.G * S.Menc r / r = S.G * (α * r) / r := by rw [hM]
        _ = S.G * α * r / r := by ring
        _ = S.G * α := by field_simp [hrne]
    dsimp [vrot]
    have hnonneg : 0 ≤ S.G * S.Menc r / r := by
      have hnum_nonneg : 0 ≤ S.G * S.Menc r := by
        have hM : 0 ≤ S.Menc r := S.nonnegM r
        exact mul_nonneg (le_of_lt S.posG) hM
      exact div_nonneg hnum_nonneg (le_of_lt hr)
    calc
      Real.sqrt (S.G * S.Menc r / r) ^ 2 = S.G * S.Menc r / r := by
        rw [Real.sq_sqrt hnonneg]
      _ = S.G * α := by rw [hfrac]
  calc
    g S r = (vrot S r) ^ 2 / r := by dsimp [g]
    _ = (S.G * α) / r := by rw [hvrot_sq]

/-- Newtonian rotation curve is flat when the enclosed mass grows linearly:
    if `Menc(r) = γ r` (γ ≥ 0) then `vrot(r) = √(G γ)` for all r > 0. -/
lemma vrot_flat_of_linear_Menc_Newtonian (S : RotSys) (γ : ℝ)
  (hγ : 0 ≤ γ) (hlin : ∀ {r : ℝ}, 0 < r → S.Menc r = γ * r) :
  ∀ {r : ℝ}, 0 < r → vrot S r = Real.sqrt (S.G * γ) := by
  intro r hr
  have hrne : r ≠ 0 := ne_of_gt hr
  have hM : S.Menc r = γ * r := hlin hr
  -- vrot = sqrt(G * Menc / r) = sqrt(G * γ)
  have hnonneg : 0 ≤ S.G * γ := mul_nonneg (le_of_lt S.posG) hγ
  have hfrac : S.G * S.Menc r / r = S.G * γ := by
    calc
      S.G * S.Menc r / r = S.G * (γ * r) / r := by rw [hM]
      _ = S.G * γ * r / r := by ring
      _ = S.G * γ := by field_simp [hrne]
  dsimp [vrot]
  rw [hfrac]

end Rotation
end Gravity
end IndisputableMonolith