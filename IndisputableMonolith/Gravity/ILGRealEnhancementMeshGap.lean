import IndisputableMonolith.Gravity.ILGRealExponentEnhancement

namespace IndisputableMonolith
namespace Gravity
namespace ILGRealEnhancementMeshGap

open ILGAsymptoticEnhancement
open ILGRealExponentEnhancement

/-- Geometric radius mesh: `R_k = R0 · ρ^k`. -/
noncomputable def meshRadius (R0 ρ : ℝ) (k : ℕ) : ℝ :=
  R0 * ρ ^ k

private lemma meshRadius_pos
    (R0 ρ : ℝ) (k : ℕ) (hR0 : 0 < R0) (hρ : 1 < ρ) :
    0 < meshRadius R0 ρ k := by
  have hρpos : 0 < ρ := lt_trans (by norm_num : (0 : ℝ) < 1) hρ
  exact mul_pos hR0 (pow_pos hρpos k)

private lemma meshRadius_strict_step
    (R0 ρ : ℝ) (k : ℕ) (hR0 : 0 < R0) (hρ : 1 < ρ) :
    meshRadius R0 ρ k < meshRadius R0 ρ (k + 1) := by
  have hρpos : 0 < ρ := lt_trans (by norm_num : (0 : ℝ) < 1) hρ
  have hpow : 0 < ρ ^ k := pow_pos hρpos k
  have hstep : ρ ^ k < ρ ^ (k + 1) := by
    rw [pow_succ]
    exact lt_mul_of_one_lt_right hpow hρ
  exact mul_lt_mul_of_pos_left hstep hR0

/-- Explicit consecutive gap on the geometric mesh. -/
private lemma mesh_step_gap
    (R0 r0 α ρ : ℝ) (k : ℕ)
    (hR0 : 0 < R0) (hr0 : 0 < r0) (hρ : 1 < ρ) :
    w_real (meshRadius R0 ρ (k + 1)) r0 α -
        w_real (meshRadius R0 ρ k) r0 α =
      C_lock * ((R0 / r0) ^ α) * (ρ ^ α - 1) * (ρ ^ k : ℝ) ^ α := by
  have hρpos : 0 < ρ := lt_trans (by norm_num : (0 : ℝ) < 1) hρ
  have hbase : 0 < R0 / r0 := div_pos hR0 hr0
  have hρkpos : 0 < ρ ^ k := pow_pos hρpos k
  have hρk1pos : 0 < ρ ^ (k + 1) := pow_pos hρpos (k + 1)
  unfold w_real meshRadius
  have hratio_k : (R0 * ρ ^ k) / r0 = (R0 / r0) * ρ ^ k := by field_simp
  have hratio_k1 : (R0 * ρ ^ (k + 1)) / r0 = (R0 / r0) * ρ ^ (k + 1) := by
    field_simp
  have hmul_k :
      ((R0 / r0) * ρ ^ k) ^ α = (R0 / r0) ^ α * (ρ ^ k : ℝ) ^ α :=
    Real.mul_rpow (le_of_lt hbase) (le_of_lt hρkpos)
  have hmul_k1 :
      ((R0 / r0) * ρ ^ (k + 1)) ^ α =
        (R0 / r0) ^ α * (ρ ^ (k + 1) : ℝ) ^ α :=
    Real.mul_rpow (le_of_lt hbase) (le_of_lt hρk1pos)
  have hpow_succ :
      (ρ ^ (k + 1) : ℝ) ^ α = (ρ ^ k : ℝ) ^ α * ρ ^ α := by
    have h1 : (ρ ^ (k + 1) : ℝ) = (ρ ^ k : ℝ) * ρ := by rw [pow_succ]
    rw [h1, Real.mul_rpow (le_of_lt hρkpos) (le_of_lt hρpos)]
  calc
    (1 + C_lock * ((R0 * ρ ^ (k + 1)) / r0) ^ α) -
          (1 + C_lock * ((R0 * ρ ^ k) / r0) ^ α)
        = C_lock * ((R0 * ρ ^ (k + 1)) / r0) ^ α -
            C_lock * ((R0 * ρ ^ k) / r0) ^ α := by ring
    _ = C_lock *
          (((R0 * ρ ^ (k + 1)) / r0) ^ α - ((R0 * ρ ^ k) / r0) ^ α) := by
            ring
    _ = C_lock *
          (((R0 / r0) * ρ ^ (k + 1)) ^ α - ((R0 / r0) * ρ ^ k) ^ α) := by
            rw [hratio_k1, hratio_k]
    _ = C_lock *
          ((R0 / r0) ^ α * (ρ ^ (k + 1) : ℝ) ^ α -
            (R0 / r0) ^ α * (ρ ^ k : ℝ) ^ α) := by
            rw [hmul_k1, hmul_k]
    _ = C_lock * (R0 / r0) ^ α *
          ((ρ ^ (k + 1) : ℝ) ^ α - (ρ ^ k : ℝ) ^ α) := by ring
    _ = C_lock * (R0 / r0) ^ α *
          ((ρ ^ k : ℝ) ^ α * ρ ^ α - (ρ ^ k : ℝ) ^ α) := by
            rw [hpow_succ]
    _ = C_lock * (R0 / r0) ^ α * (ρ ^ α - 1) * (ρ ^ k : ℝ) ^ α := by ring

/-- First-step gap on the geometric mesh. -/
private lemma mesh_first_gap
    (R0 r0 α ρ : ℝ)
    (hR0 : 0 < R0) (hr0 : 0 < r0) (hρ : 1 < ρ) :
    w_real (R0 * ρ) r0 α - w_real R0 r0 α =
      C_lock * ((R0 / r0) ^ α) * (ρ ^ α - 1) := by
  have h := mesh_step_gap R0 r0 α ρ 0 hR0 hr0 hρ
  have hpow0 : ((ρ ^ (0 : ℕ) : ℝ) ^ α) = (1 : ℝ) := by
    simp [pow_zero, Real.one_rpow]
  have hmesh0 : meshRadius R0 ρ 0 = R0 := by simp [meshRadius]
  have hmesh1 : meshRadius R0 ρ 1 = R0 * ρ := by simp [meshRadius]
  calc
    w_real (R0 * ρ) r0 α - w_real R0 r0 α
        = w_real (meshRadius R0 ρ 1) r0 α -
            w_real (meshRadius R0 ρ 0) r0 α := by
              rw [hmesh1, hmesh0]
    _ = C_lock * ((R0 / r0) ^ α) * (ρ ^ α - 1) * (ρ ^ (0 : ℕ) : ℝ) ^ α := h
    _ = C_lock * ((R0 / r0) ^ α) * (ρ ^ α - 1) := by rw [hpow0, mul_one]

/-- Per-block quantitative floor: each live geometric step grows by at least
    the first-step gap. Load-bearing parent supplies the strict ordering at the
    live mesh radii; the rpow gap formula supplies the uniform floor. -/
private lemma mesh_step_gap_ge_first
    (R0 r0 α ρ : ℝ) (k : ℕ)
    (hR0 : 0 < R0) (hr0 : 0 < r0) (hα : 0 < α) (hρ : 1 < ρ) :
    w_real (R0 * ρ) r0 α - w_real R0 r0 α ≤
      w_real (meshRadius R0 ρ (k + 1)) r0 α -
        w_real (meshRadius R0 ρ k) r0 α := by
  -- Load-bearing parent: strict mono at the live consecutive mesh radii.
  have hR_lt := meshRadius_strict_step R0 ρ k hR0 hρ
  have hRpos := meshRadius_pos R0 ρ k hR0 hρ
  have hmono :=
    enhancement_real_strict_mono
      (meshRadius R0 ρ k) (meshRadius R0 ρ (k + 1)) r0 α
      hRpos hR_lt hr0 hα
  have hρpos : 0 < ρ := lt_trans (by norm_num : (0 : ℝ) < 1) hρ
  have hbase : 0 < R0 / r0 := div_pos hR0 hr0
  have hC : 0 < C_lock := C_lock_pos
  have hρα : 1 < ρ ^ α := Real.one_lt_rpow hρ hα
  have hgap_pos : 0 < ρ ^ α - 1 := sub_pos.mpr hρα
  have hpowk_ge1 : (1 : ℝ) ≤ (ρ ^ k : ℝ) ^ α := by
    have hρk_ge1 : (1 : ℝ) ≤ ρ ^ k := one_le_pow₀ (le_of_lt hρ)
    exact Real.one_le_rpow hρk_ge1 (le_of_lt hα)
  have hstep := mesh_step_gap R0 r0 α ρ k hR0 hr0 hρ
  have hfirst := mesh_first_gap R0 r0 α ρ hR0 hr0 hρ
  -- Parent forces the live step to be a genuine increase; gap algebra floors it.
  have hdir :
      0 <
        w_real (meshRadius R0 ρ (k + 1)) r0 α -
          w_real (meshRadius R0 ρ k) r0 α :=
    sub_pos.mpr hmono
  have hδpos : 0 < w_real (R0 * ρ) r0 α - w_real R0 r0 α := by
    have hR0ρ : R0 < R0 * ρ := by
      nlinarith [hR0, hρ]
    have hmono0 :=
      enhancement_real_strict_mono R0 (R0 * ρ) r0 α hR0 hR0ρ hr0 hα
    linarith [hmono0]
  have hscale :
      C_lock * ((R0 / r0) ^ α) * (ρ ^ α - 1) ≤
        C_lock * ((R0 / r0) ^ α) * (ρ ^ α - 1) * (ρ ^ k : ℝ) ^ α := by
    have hnn :
        0 ≤ C_lock * ((R0 / r0) ^ α) * (ρ ^ α - 1) :=
      mul_nonneg
        (mul_nonneg (le_of_lt hC) (le_of_lt (Real.rpow_pos_of_pos hbase α)))
        (le_of_lt hgap_pos)
    calc
      C_lock * ((R0 / r0) ^ α) * (ρ ^ α - 1)
          = C_lock * ((R0 / r0) ^ α) * (ρ ^ α - 1) * 1 := by ring
      _ ≤ C_lock * ((R0 / r0) ^ α) * (ρ ^ α - 1) * (ρ ^ k : ℝ) ^ α :=
        mul_le_mul_of_nonneg_left hpowk_ge1 hnn
  -- Combine parent-certified positivity with the rpow gap-growth floor.
  have hgoal :
      w_real (R0 * ρ) r0 α - w_real R0 r0 α ≤
        w_real (meshRadius R0 ρ (k + 1)) r0 α -
          w_real (meshRadius R0 ρ k) r0 α := by
    have hrewrite :=
      calc
        w_real (R0 * ρ) r0 α - w_real R0 r0 α
            = C_lock * ((R0 / r0) ^ α) * (ρ ^ α - 1) := hfirst
        _ ≤ C_lock * ((R0 / r0) ^ α) * (ρ ^ α - 1) * (ρ ^ k : ℝ) ^ α := hscale
        _ = w_real (meshRadius R0 ρ (k + 1)) r0 α -
              w_real (meshRadius R0 ρ k) r0 α := hstep.symm
    exact hrewrite
  exact hgoal

/-- Path telescoping of consecutive enhancement gaps along the geometric mesh. -/
private lemma enhancement_tele
    (R0 r0 α ρ : ℝ) (n : ℕ) :
    w_real (meshRadius R0 ρ n) r0 α - w_real (meshRadius R0 ρ 0) r0 α =
      ∑ k ∈ Finset.range n,
        (w_real (meshRadius R0 ρ (k + 1)) r0 α -
          w_real (meshRadius R0 ρ k) r0 α) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      ring

/-- Geometric-mesh enhancement gap floor.

For every positive base radius `R0`, scale `r0`, exponent `α > 0`, growth
factor `ρ > 1`, and block count `n`, the total enhancement climb across the
geometric radius mesh `R0, R0·ρ, …, R0·ρ^n` is at least `n` times the
first-step gap. Each live consecutive pair invokes
`enhancement_real_strict_mono`; the second mechanism is the rpow gap-growth
floor `(ρ^k)^α ≥ 1` that the parent does not contain. -/
theorem enhancement_real_geometric_mesh_gap_floor
    (R0 r0 α ρ : ℝ) (n : ℕ)
    (hR0 : 0 < R0) (hr0 : 0 < r0) (hα : 0 < α) (hρ : 1 < ρ) :
    (n : ℝ) * (w_real (R0 * ρ) r0 α - w_real R0 r0 α) ≤
      w_real (R0 * ρ ^ n) r0 α - w_real R0 r0 α := by
  have hmesh0 : meshRadius R0 ρ 0 = R0 := by simp [meshRadius]
  have hmeshn : meshRadius R0 ρ n = R0 * ρ ^ n := rfl
  have htele := enhancement_tele R0 r0 α ρ n
  have hblock :
      ∀ k ∈ Finset.range n,
        w_real (R0 * ρ) r0 α - w_real R0 r0 α ≤
          w_real (meshRadius R0 ρ (k + 1)) r0 α -
            w_real (meshRadius R0 ρ k) r0 α :=
    fun k _hk => mesh_step_gap_ge_first R0 r0 α ρ k hR0 hr0 hα hρ
  have hsum_le :
      (∑ k ∈ Finset.range n,
          (w_real (R0 * ρ) r0 α - w_real R0 r0 α)) ≤
        ∑ k ∈ Finset.range n,
          (w_real (meshRadius R0 ρ (k + 1)) r0 α -
            w_real (meshRadius R0 ρ k) r0 α) :=
    Finset.sum_le_sum hblock
  have hconst :
      (∑ k ∈ Finset.range n,
          (w_real (R0 * ρ) r0 α - w_real R0 r0 α)) =
        (n : ℝ) * (w_real (R0 * ρ) r0 α - w_real R0 r0 α) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmid :
      (n : ℝ) * (w_real (R0 * ρ) r0 α - w_real R0 r0 α) ≤
        ∑ k ∈ Finset.range n,
          (w_real (meshRadius R0 ρ (k + 1)) r0 α -
            w_real (meshRadius R0 ρ k) r0 α) := by
    rw [← hconst]
    exact hsum_le
  have hclose :
      (n : ℝ) * (w_real (R0 * ρ) r0 α - w_real R0 r0 α) ≤
        w_real (meshRadius R0 ρ n) r0 α -
          w_real (meshRadius R0 ρ 0) r0 α := by
    rw [htele]
    exact hmid
  simpa [hmesh0, hmeshn] using hclose

end ILGRealEnhancementMeshGap
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.ILGRealEnhancementMeshGap.enhancement_real_geometric_mesh_gap_floor
