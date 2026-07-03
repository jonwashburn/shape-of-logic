import Mathlib
import IndisputableMonolith.Constants

/-!
# Born Rule Route B: No-Signaling Uniqueness (Proposition 3.7)

Formalizes the central theorem of the Born rule paper (Simons, Washburn,
Allahyarov): the premises (SA)+(NC)+(CS)+(PA)+(P5)₂ force f(r) = r².

## Status: Zero sorry
-/

namespace IndisputableMonolith.Verification.BornRuleRouteB

open Real

noncomputable section

/-- Route B hypothesis bundle (Proposition 3.7(a)–(d), pre-processed). -/
structure RouteBHyp (f : ℝ → ℝ) : Prop where
  cont : Continuous f
  f_zero : f 0 = 0
  f_one : f 1 = 1
  no_sig : ∀ r s : ℝ, 0 < r → 0 < s → s < 1 →
    f (r * s) + f (r * Real.sqrt (1 - s ^ 2)) = f r

/-! ## Steps 1–2: No-Signaling → Additive Cauchy Equation -/

def hSub (f : ℝ → ℝ) (x : ℝ) : ℝ := f (Real.sqrt x)

theorem hSub_zero {f : ℝ → ℝ} (H : RouteBHyp f) : hSub f 0 = 0 := by
  simp only [hSub, Real.sqrt_zero, H.f_zero]

theorem hSub_one {f : ℝ → ℝ} (H : RouteBHyp f) : hSub f 1 = 1 := by
  simp only [hSub, Real.sqrt_one, H.f_one]

theorem hSub_cont {f : ℝ → ℝ} (H : RouteBHyp f) : Continuous (hSub f) :=
  H.cont.comp continuous_sqrt

theorem hSub_split {f : ℝ → ℝ} (H : RouteBHyp f)
    {R p : ℝ} (hR : 0 < R) (hp0 : 0 < p) (hp1 : p < 1) :
    hSub f (R * p) + hSub f (R * (1 - p)) = hSub f R := by
  unfold hSub
  set r := Real.sqrt R with hr_def
  set s := Real.sqrt p with hs_def
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hR
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hp0
  have hs_sq : s ^ 2 = p := Real.sq_sqrt (le_of_lt hp0)
  have hs_lt1 : s < 1 := by
    nlinarith [hs_sq]
  have : Real.sqrt (R * p) = r * s :=
    (Real.sqrt_mul (le_of_lt hR) p).symm ▸ by rw [hr_def, hs_def]
  rw [this]
  have h_1ms : 1 - s ^ 2 = 1 - p := by rw [hs_sq]
  have : Real.sqrt (R * (1 - p)) = r * Real.sqrt (1 - s ^ 2) := by
    rw [h_1ms, hr_def, ← Real.sqrt_mul (le_of_lt hR)]
  rw [this]
  exact H.no_sig r s hr_pos hs_pos hs_lt1

theorem hSub_additive {f : ℝ → ℝ} (H : RouteBHyp f)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hSub f (x + y) = hSub f x + hSub f y := by
  have hS : 0 < x + y := add_pos hx hy
  have hS_ne : x + y ≠ 0 := ne_of_gt hS
  have hp : 0 < x / (x + y) := div_pos hx hS
  have hp1 : x / (x + y) < 1 := by rwa [div_lt_one hS, add_comm, lt_add_iff_pos_left]
  have h1 : (x + y) * (x / (x + y)) = x := mul_div_cancel₀ x hS_ne
  have h2 : (x + y) * (1 - x / (x + y)) = y := by field_simp; linarith
  have := hSub_split H hS hp hp1
  rw [h1, h2] at this; linarith

/-! ## Step 3: Cauchy Equation Solution (Bounded-Deviation Argument) -/

private theorem additive_nat_mul
    {g : ℝ → ℝ} (g_add : ∀ x y : ℝ, 0 < x → 0 < y → g (x + y) = g x + g y)
    (g0 : g 0 = 0) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    g (↑n * x) = ↑n * g x := by
  induction n with
  | zero => simp [g0]
  | succ k ih =>
    cases k with
    | zero => simp
    | succ m =>
      have hk : (0 : ℝ) < ↑(m + 1) * x := by positivity
      have : (↑(m + 2) : ℝ) * x = ↑(m + 1) * x + x := by push_cast; ring
      rw [this, g_add _ _ hk hx, ih]
      push_cast; ring

private theorem additive_nat_zero
    {g : ℝ → ℝ} (g_add : ∀ x y : ℝ, 0 < x → 0 < y → g (x + y) = g x + g y)
    (g0 : g 0 = 0) (g1 : g 1 = 0) (n : ℕ) :
    g (↑n : ℝ) = 0 := by
  have := additive_nat_mul g_add g0 n one_pos
  simp only [mul_one] at this; rw [this, g1, mul_zero]

private theorem additive_zero_on_unit
    {g : ℝ → ℝ} (gcont : Continuous g)
    (g_add : ∀ x y : ℝ, 0 < x → 0 < y → g (x + y) = g x + g y)
    (g0 : g 0 = 0) (g1 : g 1 = 0)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : g x = 0 := by
  rcases eq_or_lt_of_le hx0 with rfl | hx_pos; · exact g0
  rcases eq_or_lt_of_le hx1 with rfl | _; · exact g1
  obtain ⟨z, _, hz_max⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (show (0 : ℝ) ≤ 2 by norm_num))
    ((continuous_abs.comp gcont).continuousOn)
  set M := |g z| + 1
  have hM_pos : (0 : ℝ) < M := by positivity
  have hM_bd : ∀ t ∈ Set.Icc (0 : ℝ) 2, |g t| ≤ M :=
    fun t ht => le_trans (hz_max ht) (le_of_lt (lt_add_one _))
  by_contra h_ne
  have h_gx_pos : 0 < |g x| := abs_pos.mpr h_ne
  obtain ⟨N, hN⟩ := exists_nat_gt (M / |g x|)
  have hN_pos : (0 : ℝ) < ↑N := lt_trans (div_pos hM_pos h_gx_pos) hN
  have hN_nat : 0 < N := Nat.pos_of_ne_zero (by exact_mod_cast ne_of_gt hN_pos)
  have h_scale := additive_nat_mul g_add g0 N hx_pos
  have h_Nx_nn : (0 : ℝ) ≤ ↑N * x := by positivity
  set frac := ↑N * x - ↑⌊↑N * x⌋₊ with frac_def
  have h_frac_nn : 0 ≤ frac := sub_nonneg.mpr (Nat.floor_le h_Nx_nn)
  have h_frac_lt : frac < 1 := by
    simp only [frac_def]
    have := Nat.lt_floor_add_one (↑N * x); push_cast at this ⊢; linarith
  have h_frac_le2 : frac ≤ 2 := by linarith
  have h_key : g (↑⌊↑N * x⌋₊ : ℝ) = 0 := additive_nat_zero g_add g0 g1 _
  have h_gNx : g (↑N * x) = g frac := by
    rcases eq_or_lt_of_le h_frac_nn with heq | h_frac_pos
    · have hfrac0 : frac = 0 := by linarith
      rw [show ↑N * x = (↑⌊↑N * x⌋₊ : ℝ) from by linarith [frac_def],
          h_key, hfrac0, g0]
    · rcases Nat.eq_zero_or_pos ⌊↑N * x⌋₊ with h0 | hpos
      · simp only [h0, Nat.cast_zero] at frac_def ⊢; simp [frac_def]
      · have h_fl_pos : (0 : ℝ) < (↑⌊↑N * x⌋₊ : ℝ) := by exact_mod_cast hpos
        have h_decomp : ↑N * x = frac + (↑⌊↑N * x⌋₊ : ℝ) := by
          simp only [frac_def]; ring
        rw [h_decomp, g_add _ _ h_frac_pos h_fl_pos, h_key, add_zero]
  rw [h_scale] at h_gNx
  have h_bd := hM_bd frac ⟨h_frac_nn, h_frac_le2⟩
  rw [← h_gNx] at h_bd
  rw [abs_mul, abs_of_pos hN_pos] at h_bd
  nlinarith [mul_lt_mul_of_pos_right hN h_gx_pos,
             div_mul_cancel₀ M (ne_of_gt h_gx_pos)]

private theorem additive_zero_on_nonneg
    {g : ℝ → ℝ} (gcont : Continuous g)
    (g_add : ∀ x y : ℝ, 0 < x → 0 < y → g (x + y) = g x + g y)
    (g0 : g 0 = 0) (g1 : g 1 = 0)
    {x : ℝ} (hx : 0 ≤ x) : g x = 0 := by
  rcases le_or_gt x 1 with h | h
  · exact additive_zero_on_unit gcont g_add g0 g1 hx h
  · set frac := x - ↑⌊x⌋₊ with frac_def
    have h_frac_nn : 0 ≤ frac := sub_nonneg.mpr (Nat.floor_le hx)
    have h_frac_lt : frac < 1 := by
      simp only [frac_def]
      have := Nat.lt_floor_add_one x; push_cast at this ⊢; linarith
    have h_key : g (↑⌊x⌋₊ : ℝ) = 0 := additive_nat_zero g_add g0 g1 _
    rcases eq_or_lt_of_le h_frac_nn with heq | h_frac_pos
    · rw [show x = (↑⌊x⌋₊ : ℝ) from by linarith [frac_def]]; exact h_key
    · have hfl_pos : (0 : ℝ) < (↑⌊x⌋₊ : ℝ) := by
        rcases Nat.eq_zero_or_pos ⌊x⌋₊ with h0 | hp
        · simp only [h0, Nat.cast_zero] at frac_def; linarith
        · exact_mod_cast hp
      have h_decomp : x = frac + (↑⌊x⌋₊ : ℝ) := by simp only [frac_def]; ring
      rw [h_decomp, g_add _ _ h_frac_pos hfl_pos, h_key, add_zero]
      exact additive_zero_on_unit gcont g_add g0 g1 h_frac_nn (le_of_lt h_frac_lt)

/-! ## Step 3 applied: h = id -/

private def gDev (f : ℝ → ℝ) (x : ℝ) : ℝ := hSub f x - x

theorem hSub_eq_id {f : ℝ → ℝ} (H : RouteBHyp f) {x : ℝ} (hx : 0 ≤ x) :
    hSub f x = x := by
  have h0 : gDev f x = 0 := additive_zero_on_nonneg
    ((hSub_cont H).sub continuous_id)
    (fun a b ha hb => show hSub f (a + b) - (a + b) = (hSub f a - a) + (hSub f b - b) by
      rw [hSub_additive H ha hb]; ring)
    (show hSub f 0 - 0 = 0 by rw [hSub_zero H]; ring)
    (show hSub f 1 - 1 = 0 by rw [hSub_one H]; ring)
    hx
  unfold gDev at h0; linarith

/-! ## Step 4: f(r) = r² -/

/-- **Proposition 3.7 (Route B)**: f(r) = r² for all r ≥ 0. -/
theorem born_rule_route_B {f : ℝ → ℝ} (H : RouteBHyp f)
    {r : ℝ} (hr : 0 ≤ r) : f r = r ^ 2 := by
  have : hSub f (r ^ 2) = r ^ 2 := hSub_eq_id H (sq_nonneg r)
  simp only [hSub, Real.sqrt_sq hr] at this; exact this

/-- (MA) is a COROLLARY, not an axiom (Remark 3.6 of the paper). -/
theorem modulus_multiplicativity {f : ℝ → ℝ} (H : RouteBHyp f)
    {r₁ r₂ : ℝ} (h1 : 0 ≤ r₁) (h2 : 0 ≤ r₂) :
    f (r₁ * r₂) = f r₁ * f r₂ := by
  simp only [born_rule_route_B H (mul_nonneg h1 h2),
    born_rule_route_B H h1, born_rule_route_B H h2]; ring

/-! ## Certificate -/

/-- Route B Born Rule Certificate. -/
structure RouteBCert (f : ℝ → ℝ) : Prop where
  quadratic : ∀ r, 0 ≤ r → f r = r ^ 2
  mult : ∀ r₁ r₂, 0 ≤ r₁ → 0 ≤ r₂ → f (r₁ * r₂) = f r₁ * f r₂

theorem route_B_certified {f : ℝ → ℝ} (H : RouteBHyp f) : RouteBCert f where
  quadratic := fun _r hr => born_rule_route_B H hr
  mult := fun _r₁ _r₂ h1 h2 => modulus_multiplicativity H h1 h2

end

end IndisputableMonolith.Verification.BornRuleRouteB
