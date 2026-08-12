import IndisputableMonolith.Gravity.ILGRealEnhancementMeshGap

namespace IndisputableMonolith
namespace Gravity
namespace ILGRealEnhancementMeshThreshold

open ILGRealExponentEnhancement
open ILGRealEnhancementMeshGap

/-- First-step enhancement gap on the geometric mesh. -/
noncomputable def firstStepGap (R0 r0 α ρ : ℝ) : ℝ :=
  w_real (R0 * ρ) r0 α - w_real R0 r0 α

/-- Explicit block count forcing the mesh climb past target `M`:
    `Nat.ceil (M / firstStepGap) + 1`. -/
noncomputable def meshThresholdBlocks (R0 r0 α ρ M : ℝ) : ℕ :=
  Nat.ceil (M / firstStepGap R0 r0 α ρ) + 1

private lemma firstStepGap_pos
    (R0 r0 α ρ : ℝ)
    (hR0 : 0 < R0) (hr0 : 0 < r0) (hα : 0 < α) (hρ : 1 < ρ) :
    0 < firstStepGap R0 r0 α ρ := by
  have hRlt : R0 < R0 * ρ := by nlinarith [hR0, hρ]
  have hmono :=
    enhancement_real_strict_mono R0 (R0 * ρ) r0 α hR0 hRlt hr0 hα
  simpa [firstStepGap] using sub_pos.mpr hmono

/-- Geometric-mesh enhancement threshold crossing.

For every positive base radius `R0`, scale `r0`, exponent `α > 0`, growth
factor `ρ > 1`, and nonnegative target `M`, the explicit block count
`n = Nat.ceil (M / δ) + 1` (with `δ` the first-step gap) forces the
geometric-mesh enhancement climb past `M`. Load-bearing parent supplies
the linear floor `n · δ ≤ climb`; the second mechanism is the Archimedean
block-selection formula converting that floor into an explicit crossing
index. -/
theorem enhancement_real_geometric_mesh_threshold_crossing
    (R0 r0 α ρ M : ℝ)
    (hR0 : 0 < R0) (hr0 : 0 < r0) (hα : 0 < α) (hρ : 1 < ρ) (_hM : 0 ≤ M) :
    M <
      w_real (R0 * ρ ^ meshThresholdBlocks R0 r0 α ρ M) r0 α -
        w_real R0 r0 α := by
  let δ : ℝ := firstStepGap R0 r0 α ρ
  let n : ℕ := meshThresholdBlocks R0 r0 α ρ M
  have hδpos : 0 < δ := firstStepGap_pos R0 r0 α ρ hR0 hr0 hα hρ
  have hδeq : δ = w_real (R0 * ρ) r0 α - w_real R0 r0 α := rfl
  -- Load-bearing parent: n-fold linear gap floor on the geometric mesh.
  have hfloor :=
    enhancement_real_geometric_mesh_gap_floor R0 r0 α ρ n hR0 hr0 hα hρ
  have hclimb :
      (n : ℝ) * δ ≤
        w_real (R0 * ρ ^ n) r0 α - w_real R0 r0 α := by
    simpa [hδeq] using hfloor
  -- Second mechanism: Archimedean selection n = Nat.ceil (M/δ) + 1.
  have hn_def : n = Nat.ceil (M / δ) + 1 := rfl
  have hδne : δ ≠ 0 := ne_of_gt hδpos
  have hceil : M / δ ≤ (Nat.ceil (M / δ) : ℝ) := Nat.le_ceil (M / δ)
  have hM_le : M ≤ (Nat.ceil (M / δ) : ℝ) * δ := by
    have hmul : (M / δ) * δ ≤ (Nat.ceil (M / δ) : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hceil (le_of_lt hδpos)
    have hre : (M / δ) * δ = M := div_mul_cancel₀ M hδne
    rw [hre] at hmul
    exact hmul
  have hn_cast : (n : ℝ) = (Nat.ceil (M / δ) : ℝ) + 1 := by
    rw [hn_def]
    norm_cast
  have hnδ : M + δ ≤ (n : ℝ) * δ := by
    have htmp : M + δ ≤ ((Nat.ceil (M / δ) : ℝ) + 1) * δ := by
      nlinarith [hM_le, hδpos]
    rwa [← hn_cast] at htmp
  have hn_gt : M < (n : ℝ) * δ := by nlinarith [hnδ, hδpos]
  show M < w_real (R0 * ρ ^ n) r0 α - w_real R0 r0 α
  linarith [hclimb, hn_gt]

end ILGRealEnhancementMeshThreshold
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.ILGRealEnhancementMeshThreshold.enhancement_real_geometric_mesh_threshold_crossing
