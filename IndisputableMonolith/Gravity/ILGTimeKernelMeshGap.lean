import IndisputableMonolith.Gravity.ILGDerivation

namespace IndisputableMonolith
namespace Gravity
namespace ILGTimeKernelMeshGap

open ILG

/-- Geometric dynamical-time mesh: `T_k = T0 · ρ^k`. -/
noncomputable def meshTime (T0 ρ : ℝ) (k : ℕ) : ℝ :=
  T0 * ρ ^ k

private lemma meshTime_strict_step
    (T0 ρ : ℝ) (k : ℕ) (hT0 : 0 < T0) (hρ : 1 < ρ) :
    meshTime T0 ρ k < meshTime T0 ρ (k + 1) := by
  have hρpos : 0 < ρ := lt_trans (by norm_num : (0 : ℝ) < 1) hρ
  have hpow : 0 < ρ ^ k := pow_pos hρpos k
  have hstep : ρ ^ k < ρ ^ (k + 1) := by
    rw [pow_succ]
    exact lt_mul_of_one_lt_right hpow hρ
  exact mul_lt_mul_of_pos_left hstep hT0

private lemma T0_pos_of_unclamped
    (T0 τ0 : ℝ) (hτ : 0 < τ0)
    (hunc : defaultConfig.eps_t ≤ T0 / τ0) :
    0 < T0 := by
  have heps : (0 : ℝ) < defaultConfig.eps_t := by norm_num [defaultConfig]
  have hquot : 0 < T0 / τ0 := lt_of_lt_of_le heps hunc
  have h : (0 : ℝ) * τ0 < T0 := (lt_div_iff₀ hτ).mp hquot
  simpa using h

private lemma mesh_unclamped
    (T0 τ0 ρ : ℝ) (k : ℕ)
    (hτ : 0 < τ0) (hρ : 1 < ρ)
    (hunc : defaultConfig.eps_t ≤ T0 / τ0) :
    defaultConfig.eps_t ≤ meshTime T0 ρ k / τ0 := by
  have hT0 : 0 < T0 := T0_pos_of_unclamped T0 τ0 hτ hunc
  have hρpos : 0 < ρ := lt_trans (by norm_num : (0 : ℝ) < 1) hρ
  have hpow : (1 : ℝ) ≤ ρ ^ k := one_le_pow₀ (le_of_lt hρ)
  have hratio :
      meshTime T0 ρ k / τ0 = (T0 / τ0) * ρ ^ k := by
    unfold meshTime
    field_simp
  have hscale : T0 / τ0 ≤ (T0 / τ0) * ρ ^ k := by
    have hnn : 0 ≤ T0 / τ0 := le_of_lt (lt_of_lt_of_le
      (by norm_num [defaultConfig] : (0 : ℝ) < defaultConfig.eps_t) hunc)
    calc
      T0 / τ0 = (T0 / τ0) * 1 := by ring
      _ ≤ (T0 / τ0) * ρ ^ k := mul_le_mul_of_nonneg_left hpow hnn
  have : defaultConfig.eps_t ≤ (T0 / τ0) * ρ ^ k := le_trans hunc hscale
  simpa [hratio] using this

/-- Explicit consecutive gap on the unclamped geometric time mesh. -/
private lemma mesh_step_gap
    (P : Params) (τ0 T0 ρ : ℝ) (k : ℕ)
    (hτ : 0 < τ0) (hρ : 1 < ρ)
    (hunc : defaultConfig.eps_t ≤ T0 / τ0) :
    w_t P (meshTime T0 ρ (k + 1)) τ0 -
        w_t P (meshTime T0 ρ k) τ0 =
      P.Clag * ((T0 / τ0) ^ P.alpha) * (ρ ^ P.alpha - 1) *
        (ρ ^ k : ℝ) ^ P.alpha := by
  have hT0 : 0 < T0 := T0_pos_of_unclamped T0 τ0 hτ hunc
  have hρpos : 0 < ρ := lt_trans (by norm_num : (0 : ℝ) < 1) hρ
  have hbase : 0 < T0 / τ0 := by
    have heps : (0 : ℝ) < defaultConfig.eps_t := by norm_num [defaultConfig]
    exact lt_of_lt_of_le heps hunc
  have hρkpos : 0 < ρ ^ k := pow_pos hρpos k
  have hρk1pos : 0 < ρ ^ (k + 1) := pow_pos hρpos (k + 1)
  have hunc_k := mesh_unclamped T0 τ0 ρ k hτ hρ hunc
  have hunc_k1 := mesh_unclamped T0 τ0 ρ (k + 1) hτ hρ hunc
  have hm_k :
      max defaultConfig.eps_t (meshTime T0 ρ k / τ0) =
        meshTime T0 ρ k / τ0 := max_eq_right hunc_k
  have hm_k1 :
      max defaultConfig.eps_t (meshTime T0 ρ (k + 1) / τ0) =
        meshTime T0 ρ (k + 1) / τ0 := max_eq_right hunc_k1
  have hratio_k :
      meshTime T0 ρ k / τ0 = (T0 / τ0) * ρ ^ k := by
    unfold meshTime; field_simp
  have hratio_k1 :
      meshTime T0 ρ (k + 1) / τ0 = (T0 / τ0) * ρ ^ (k + 1) := by
    unfold meshTime; field_simp
  have hmul_k :
      ((T0 / τ0) * ρ ^ k) ^ P.alpha =
        (T0 / τ0) ^ P.alpha * (ρ ^ k : ℝ) ^ P.alpha :=
    Real.mul_rpow (le_of_lt hbase) (le_of_lt hρkpos)
  have hmul_k1 :
      ((T0 / τ0) * ρ ^ (k + 1)) ^ P.alpha =
        (T0 / τ0) ^ P.alpha * (ρ ^ (k + 1) : ℝ) ^ P.alpha :=
    Real.mul_rpow (le_of_lt hbase) (le_of_lt hρk1pos)
  have hpow_succ :
      (ρ ^ (k + 1) : ℝ) ^ P.alpha =
        (ρ ^ k : ℝ) ^ P.alpha * ρ ^ P.alpha := by
    have h1 : (ρ ^ (k + 1) : ℝ) = (ρ ^ k : ℝ) * ρ := by rw [pow_succ]
    rw [h1, Real.mul_rpow (le_of_lt hρkpos) (le_of_lt hρpos)]
  simp only [w_t, w_t_with, hm_k, hm_k1]
  calc
    (1 + P.Clag * ((meshTime T0 ρ (k + 1) / τ0) ^ P.alpha - 1)) -
          (1 + P.Clag * ((meshTime T0 ρ k / τ0) ^ P.alpha - 1))
        = P.Clag * ((meshTime T0 ρ (k + 1) / τ0) ^ P.alpha -
            (meshTime T0 ρ k / τ0) ^ P.alpha) := by ring
    _ = P.Clag *
          (((T0 / τ0) * ρ ^ (k + 1)) ^ P.alpha -
            ((T0 / τ0) * ρ ^ k) ^ P.alpha) := by
            rw [hratio_k1, hratio_k]
    _ = P.Clag *
          ((T0 / τ0) ^ P.alpha * (ρ ^ (k + 1) : ℝ) ^ P.alpha -
            (T0 / τ0) ^ P.alpha * (ρ ^ k : ℝ) ^ P.alpha) := by
            rw [hmul_k1, hmul_k]
    _ = P.Clag * (T0 / τ0) ^ P.alpha *
          ((ρ ^ (k + 1) : ℝ) ^ P.alpha - (ρ ^ k : ℝ) ^ P.alpha) := by ring
    _ = P.Clag * (T0 / τ0) ^ P.alpha *
          ((ρ ^ k : ℝ) ^ P.alpha * ρ ^ P.alpha - (ρ ^ k : ℝ) ^ P.alpha) := by
            rw [hpow_succ]
    _ = P.Clag * ((T0 / τ0) ^ P.alpha) * (ρ ^ P.alpha - 1) *
          (ρ ^ k : ℝ) ^ P.alpha := by ring

private lemma mesh_first_gap
    (P : Params) (τ0 T0 ρ : ℝ)
    (hτ : 0 < τ0) (hρ : 1 < ρ)
    (hunc : defaultConfig.eps_t ≤ T0 / τ0) :
    w_t P (T0 * ρ) τ0 - w_t P T0 τ0 =
      P.Clag * ((T0 / τ0) ^ P.alpha) * (ρ ^ P.alpha - 1) := by
  have h := mesh_step_gap P τ0 T0 ρ 0 hτ hρ hunc
  have hpow0 : ((ρ ^ (0 : ℕ) : ℝ) ^ P.alpha) = (1 : ℝ) := by
    simp [pow_zero, Real.one_rpow]
  have hmesh0 : meshTime T0 ρ 0 = T0 := by simp [meshTime]
  have hmesh1 : meshTime T0 ρ 1 = T0 * ρ := by simp [meshTime]
  calc
    w_t P (T0 * ρ) τ0 - w_t P T0 τ0
        = w_t P (meshTime T0 ρ 1) τ0 - w_t P (meshTime T0 ρ 0) τ0 := by
              rw [hmesh1, hmesh0]
    _ = P.Clag * ((T0 / τ0) ^ P.alpha) * (ρ ^ P.alpha - 1) *
          (ρ ^ (0 : ℕ) : ℝ) ^ P.alpha := h
    _ = P.Clag * ((T0 / τ0) ^ P.alpha) * (ρ ^ P.alpha - 1) := by
          rw [hpow0, mul_one]

private lemma mesh_step_gap_ge_first
    (P : Params) (τ0 T0 ρ : ℝ) (k : ℕ)
    (hτ : 0 < τ0) (hα : 0 < P.alpha) (hC : 0 < P.Clag)
    (hρ : 1 < ρ) (hunc : defaultConfig.eps_t ≤ T0 / τ0) :
    w_t P (T0 * ρ) τ0 - w_t P T0 τ0 ≤
      w_t P (meshTime T0 ρ (k + 1)) τ0 -
        w_t P (meshTime T0 ρ k) τ0 := by
  have hT0 : 0 < T0 := T0_pos_of_unclamped T0 τ0 hτ hunc
  have hR_lt := meshTime_strict_step T0 ρ k hT0 hρ
  have hunc_k := mesh_unclamped T0 τ0 ρ k hτ hρ hunc
  -- Load-bearing parent: strict mono at the live consecutive mesh times.
  have hmono :=
    w_t_strictMono_unclamped P τ0 hτ hα hC
      (meshTime T0 ρ k) (meshTime T0 ρ (k + 1)) hunc_k hR_lt
  have hρpos : 0 < ρ := lt_trans (by norm_num : (0 : ℝ) < 1) hρ
  have hbase : 0 < T0 / τ0 := by
    have heps : (0 : ℝ) < defaultConfig.eps_t := by norm_num [defaultConfig]
    exact lt_of_lt_of_le heps hunc
  have hρα : 1 < ρ ^ P.alpha := Real.one_lt_rpow hρ hα
  have hgap_pos : 0 < ρ ^ P.alpha - 1 := sub_pos.mpr hρα
  have hpowk_ge1 : (1 : ℝ) ≤ (ρ ^ k : ℝ) ^ P.alpha := by
    have hρk_ge1 : (1 : ℝ) ≤ ρ ^ k := one_le_pow₀ (le_of_lt hρ)
    exact Real.one_le_rpow hρk_ge1 (le_of_lt hα)
  have hstep := mesh_step_gap P τ0 T0 ρ k hτ hρ hunc
  have hfirst := mesh_first_gap P τ0 T0 ρ hτ hρ hunc
  have hdir :
      0 <
        w_t P (meshTime T0 ρ (k + 1)) τ0 -
          w_t P (meshTime T0 ρ k) τ0 :=
    sub_pos.mpr hmono
  have hδpos : 0 < w_t P (T0 * ρ) τ0 - w_t P T0 τ0 := by
    have hT0ρ : T0 < T0 * ρ := by nlinarith [hT0, hρ]
    have hmono0 :=
      w_t_strictMono_unclamped P τ0 hτ hα hC T0 (T0 * ρ) hunc hT0ρ
    linarith [hmono0]
  have hscale :
      P.Clag * ((T0 / τ0) ^ P.alpha) * (ρ ^ P.alpha - 1) ≤
        P.Clag * ((T0 / τ0) ^ P.alpha) * (ρ ^ P.alpha - 1) *
          (ρ ^ k : ℝ) ^ P.alpha := by
    have hnn :
        0 ≤ P.Clag * ((T0 / τ0) ^ P.alpha) * (ρ ^ P.alpha - 1) :=
      mul_nonneg
        (mul_nonneg (le_of_lt hC) (le_of_lt (Real.rpow_pos_of_pos hbase P.alpha)))
        (le_of_lt hgap_pos)
    calc
      P.Clag * ((T0 / τ0) ^ P.alpha) * (ρ ^ P.alpha - 1)
          = P.Clag * ((T0 / τ0) ^ P.alpha) * (ρ ^ P.alpha - 1) * 1 := by ring
      _ ≤ P.Clag * ((T0 / τ0) ^ P.alpha) * (ρ ^ P.alpha - 1) *
            (ρ ^ k : ℝ) ^ P.alpha :=
        mul_le_mul_of_nonneg_left hpowk_ge1 hnn
  have hrewrite :=
    calc
      w_t P (T0 * ρ) τ0 - w_t P T0 τ0
          = P.Clag * ((T0 / τ0) ^ P.alpha) * (ρ ^ P.alpha - 1) := hfirst
      _ ≤ P.Clag * ((T0 / τ0) ^ P.alpha) * (ρ ^ P.alpha - 1) *
            (ρ ^ k : ℝ) ^ P.alpha := hscale
      _ = w_t P (meshTime T0 ρ (k + 1)) τ0 -
            w_t P (meshTime T0 ρ k) τ0 := hstep.symm
  exact hrewrite

private lemma enhancement_tele
    (P : Params) (τ0 T0 ρ : ℝ) (n : ℕ) :
    w_t P (meshTime T0 ρ n) τ0 - w_t P (meshTime T0 ρ 0) τ0 =
      ∑ k ∈ Finset.range n,
        (w_t P (meshTime T0 ρ (k + 1)) τ0 -
          w_t P (meshTime T0 ρ k) τ0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      ring

/-- Geometric-mesh ILG time-kernel gap floor.

For every ILG parameter pack with `α > 0` and `Clag > 0`, every positive tick
`τ0`, every unclamped base dynamical time `T0` (`eps_t ≤ T0/τ0`), growth factor
`ρ > 1`, and block count `n`, the total time-kernel climb across the geometric
mesh `T0, T0·ρ, …, T0·ρ^n` is at least `n` times the first-step gap. Each live
consecutive pair invokes `w_t_strictMono_unclamped`; the second mechanism is the
rpow gap-growth floor `(ρ^k)^α ≥ 1` that the parent does not contain. -/
theorem w_t_geometric_mesh_gap_floor
    (P : Params) (τ0 T0 ρ : ℝ) (n : ℕ)
    (hτ : 0 < τ0) (hα : 0 < P.alpha) (hC : 0 < P.Clag)
    (hunc : defaultConfig.eps_t ≤ T0 / τ0) (hρ : 1 < ρ) :
    (n : ℝ) * (w_t P (T0 * ρ) τ0 - w_t P T0 τ0) ≤
      w_t P (T0 * ρ ^ n) τ0 - w_t P T0 τ0 := by
  have hmesh0 : meshTime T0 ρ 0 = T0 := by simp [meshTime]
  have hmeshn : meshTime T0 ρ n = T0 * ρ ^ n := rfl
  have htele := enhancement_tele P τ0 T0 ρ n
  have hblock :
      ∀ k ∈ Finset.range n,
        w_t P (T0 * ρ) τ0 - w_t P T0 τ0 ≤
          w_t P (meshTime T0 ρ (k + 1)) τ0 -
            w_t P (meshTime T0 ρ k) τ0 :=
    fun k _hk => mesh_step_gap_ge_first P τ0 T0 ρ k hτ hα hC hρ hunc
  have hsum_le :
      (∑ k ∈ Finset.range n,
          (w_t P (T0 * ρ) τ0 - w_t P T0 τ0)) ≤
        ∑ k ∈ Finset.range n,
          (w_t P (meshTime T0 ρ (k + 1)) τ0 -
            w_t P (meshTime T0 ρ k) τ0) :=
    Finset.sum_le_sum hblock
  have hconst :
      (∑ k ∈ Finset.range n,
          (w_t P (T0 * ρ) τ0 - w_t P T0 τ0)) =
        (n : ℝ) * (w_t P (T0 * ρ) τ0 - w_t P T0 τ0) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmid :
      (n : ℝ) * (w_t P (T0 * ρ) τ0 - w_t P T0 τ0) ≤
        ∑ k ∈ Finset.range n,
          (w_t P (meshTime T0 ρ (k + 1)) τ0 -
            w_t P (meshTime T0 ρ k) τ0) := by
    rw [← hconst]
    exact hsum_le
  have hclose :
      (n : ℝ) * (w_t P (T0 * ρ) τ0 - w_t P T0 τ0) ≤
        w_t P (meshTime T0 ρ n) τ0 -
          w_t P (meshTime T0 ρ 0) τ0 := by
    rw [htele]
    exact hmid
  simpa [hmesh0, hmeshn] using hclose

end ILGTimeKernelMeshGap
end Gravity
end IndisputableMonolith
