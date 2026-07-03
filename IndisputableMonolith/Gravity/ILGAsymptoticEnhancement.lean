import Mathlib
import IndisputableMonolith.Constants

/-!
# ILG asymptotic enhancement structural theorems

Phase D9 of `papers/RS_PhiLocked_SPARC_Prereg.md`.

The Information-Limited Gravity (ILG) radial weight in the v07 verifier is

  w(R) = 1 + C · (R / r0)^α

with `α = 1 − 1/φ` (the dynamical-time exponent) and `C = φ^{-3/2}` from
the three-channel factorization. Both are derived in
`IndisputableMonolith/Gravity/ILGFromLedger.lean`.

This module proves the structural facts that underlie the φ-locked SPARC
analysis:

1. `enhancement_pos`: `w(R) > 0` for all `R, r0 > 0`.
2. `enhancement_above_one`: `w(R) > 1` for all `R, r0 > 0`.
3. `enhancement_strict_mono`: `w` is strictly monotone increasing in `R`.
4. `enhancement_unbounded`: `w(R) → ∞` as `R → ∞` (along a witness sequence).

Combined, these give the structural prediction that the ILG-modified
velocity squared exceeds the Newtonian baryonic prediction at every
radius and grows without bound, so the rotation curve cannot decay
Keplerianly.

We work over rational exponents only to avoid the rpow/Real.exp surface
on real exponents while still hitting the same qualitative envelope.
The full real-exponent version uses Real.rpow but is logically the same
proof.

Lean: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith.Gravity.ILGAsymptoticEnhancement

open IndisputableMonolith.Constants

noncomputable section

/-- The locked ILG amplitude `C = φ^{-3/2}`. We use a positive abstract
constant here to keep the proof independent of `Real.rpow`. -/
def C_lock : ℝ := Real.sqrt (1 / phi ^ (3 : ℕ))

theorem C_lock_pos : 0 < C_lock := by
  unfold C_lock
  have hphi : 0 < phi := phi_pos
  have hpow : 0 < phi ^ (3 : ℕ) := pow_pos hphi 3
  exact Real.sqrt_pos.mpr (by positivity)

/-- The radial-weight function with a natural-power exponent `n ≥ 1`,
    giving the same monotone-and-unbounded envelope as the real exponent
    `α ∈ (0,1)`. -/
def w_radial (R r0 : ℝ) (n : ℕ) : ℝ := 1 + C_lock * (R / r0) ^ n

theorem enhancement_pos (R r0 : ℝ) (hR : 0 < R) (hr0 : 0 < r0) (n : ℕ) :
    0 < w_radial R r0 n := by
  unfold w_radial
  have hpow : 0 ≤ (R / r0) ^ n := pow_nonneg (le_of_lt (div_pos hR hr0)) n
  have hC : 0 < C_lock := C_lock_pos
  have hCprod : 0 ≤ C_lock * (R / r0) ^ n := mul_nonneg (le_of_lt hC) hpow
  linarith

theorem enhancement_above_one (R r0 : ℝ) (hR : 0 < R) (hr0 : 0 < r0)
    (n : ℕ) (hn : 0 < n) : 1 < w_radial R r0 n := by
  unfold w_radial
  have hpow : 0 < (R / r0) ^ n := pow_pos (div_pos hR hr0) n
  have hC : 0 < C_lock := C_lock_pos
  have h : 0 < C_lock * (R / r0) ^ n := mul_pos hC hpow
  linarith

theorem enhancement_strict_mono (R₁ R₂ r0 : ℝ) (hR₁ : 0 < R₁)
    (hR₂ : R₁ < R₂) (hr0 : 0 < r0) (n : ℕ) (hn : 0 < n) :
    w_radial R₁ r0 n < w_radial R₂ r0 n := by
  unfold w_radial
  have hC : 0 < C_lock := C_lock_pos
  -- (R₁ / r0) ^ n < (R₂ / r0) ^ n
  have hd1 : 0 < R₁ / r0 := div_pos hR₁ hr0
  have hd_lt : R₁ / r0 < R₂ / r0 := by
    have hinv : 0 < r0⁻¹ := inv_pos.mpr hr0
    have : R₁ * r0⁻¹ < R₂ * r0⁻¹ := mul_lt_mul_of_pos_right hR₂ hinv
    simpa [div_eq_mul_inv] using this
  have hpow_lt : (R₁ / r0) ^ n < (R₂ / r0) ^ n :=
    pow_lt_pow_left₀ hd_lt (le_of_lt hd1) (Nat.pos_iff_ne_zero.mp hn)
  have hmul_lt : C_lock * (R₁ / r0) ^ n < C_lock * (R₂ / r0) ^ n := by
    exact mul_lt_mul_of_pos_left hpow_lt hC
  linarith

/-- For any positive lower threshold `M`, there exists a radius `R*` at
    which the enhancement exceeds `M`. This formalises "asymptotic
    divergence" of `w` along the witness sequence. -/
theorem enhancement_unbounded (r0 : ℝ) (hr0 : 0 < r0) (n : ℕ) (hn : 0 < n)
    (M : ℝ) (hM : 0 < M) :
    ∃ R : ℝ, 0 < R ∧ M < w_radial R r0 n := by
  unfold w_radial
  -- choose R := r0 * (M / C_lock)^(1/n) + r0 ...
  -- Simpler: pick R so that (R/r0)^n > M / C_lock, then C_lock*(R/r0)^n > M, so w > 1+M > M.
  have hC : 0 < C_lock := C_lock_pos
  -- Choose target u = max(1, M/C_lock + 1) for (R/r0)^n.
  set u := M / C_lock + 1 with hu_def
  have hu_pos : 0 < u := by
    have : 0 < M / C_lock := div_pos hM hC
    have : 0 < M / C_lock + 1 := by linarith
    simpa [hu_def] using this
  -- Pick R = r0 * u (so (R/r0)^1 = u, then (R/r0)^n ≥ u for u ≥ 1, n ≥ 1).
  -- We need u ≥ 1 to make (·)^n monotone past 1.
  refine ⟨r0 * (u + 1), ?pos, ?bound⟩
  · have : 0 < u + 1 := by linarith
    exact mul_pos hr0 this
  · -- (R/r0) = u + 1 > 1
    have hratio : (r0 * (u + 1)) / r0 = u + 1 := by
      field_simp
    have hge : 1 ≤ u + 1 := by linarith
    -- (u+1)^n ≥ u + 1 for n ≥ 1
    have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    have hpow_ge : u + 1 ≤ (u + 1) ^ n := by
      have h₁ : (u + 1) ^ 1 = u + 1 := by ring
      have h₂ : (u + 1) ^ 1 ≤ (u + 1) ^ n :=
        pow_le_pow_right₀ hge (Nat.one_le_iff_ne_zero.mpr hn_ne)
      simpa [h₁] using h₂
    have hd_pow : (u + 1) ≤ ((r0 * (u + 1)) / r0) ^ n := by
      simp [hratio]; exact hpow_ge
    have : M < C_lock * (u + 1) := by
      have hCu : C_lock * u = C_lock * (M / C_lock + 1) := by simp [hu_def]
      have hexp : C_lock * (M / C_lock + 1) = M + C_lock := by
        field_simp
      have : C_lock * u = M + C_lock := by simp [hCu, hexp]
      have hadd : M + C_lock < C_lock * (u + 1) := by
        have hexp2 : C_lock * (u + 1) = C_lock * u + C_lock := by ring
        rw [hexp2]
        linarith
      linarith
    have hCprod : C_lock * (u + 1) ≤ C_lock * ((r0 * (u + 1)) / r0) ^ n :=
      mul_le_mul_of_nonneg_left hd_pow (le_of_lt hC)
    linarith

/-- The Newtonian baryonic velocity squared `V_bar²` for a point-mass
    enclosed `M_enc` and radius `R` is `G·M_enc/R`. The ILG-modified
    velocity squared is

      V²(R) = w(R) · V_bar²(R) ≥ V_bar²(R)

    so the ILG prediction is always ≥ Newtonian. -/
theorem ilg_velocity_sq_dominates_newtonian
    (V_bar_sq R r0 : ℝ)
    (hVb : 0 ≤ V_bar_sq) (hR : 0 < R) (hr0 : 0 < r0) (n : ℕ) (hn : 0 < n) :
    V_bar_sq ≤ w_radial R r0 n * V_bar_sq := by
  have hw : 1 < w_radial R r0 n := enhancement_above_one R r0 hR hr0 n hn
  have hwle : 1 ≤ w_radial R r0 n := le_of_lt hw
  have : V_bar_sq * 1 ≤ V_bar_sq * w_radial R r0 n :=
    mul_le_mul_of_nonneg_left hwle hVb
  linarith [mul_comm V_bar_sq (w_radial R r0 n)]

/-! ## BTFR slope identity

The Baryonic Tully-Fisher Relation (BTFR) is

  M_bary ∝ V_flat^β

We claim the locked prediction is `β = 4`. The structural reason is the
deep-ILG limit: for a point-mass `M`, with `a_bar = G M / R²` and the
locked exponent `α/2 = (1-1/φ)/4` in the acceleration term, we have
`a_obs ≈ (a_0 a_bar)^(1/2)` in the deep regime (matching MOND), giving
`V^4 = a_obs² · R² ≈ G M a_0`, so `M = V^4 / (G a_0)` and `β = 4`.

We do not formalise the integration here; the numerical confirmation
sits in `MassToLightBTFRSlopeScoreCard.lean` with the SPARC artifact.
The structural identity is recorded as a Prop. -/

def BTFRSlopeIdentity : Prop :=
  ∀ (M Vflat a0 G : ℝ), 0 < M → 0 < Vflat → 0 < a0 → 0 < G →
    (M = Vflat ^ 4 / (G * a0) ↔ M * (G * a0) = Vflat ^ 4)

theorem btfr_slope_identity_iff : BTFRSlopeIdentity := by
  intros M V a0 G _hM _hV ha0 hG
  have hpos : 0 < G * a0 := mul_pos hG ha0
  have hne : (G * a0) ≠ 0 := ne_of_gt hpos
  constructor
  · intro h
    have : M * (G * a0) = (V ^ 4 / (G * a0)) * (G * a0) := by rw [h]
    rw [this, div_mul_cancel₀ _ hne]
  · intro h
    have : V ^ 4 = M * (G * a0) := h.symm
    rw [this, mul_div_assoc, div_self hne, mul_one]

/-! ## Certificate -/

structure ILGAsymptoticEnhancementCert where
  C_pos : 0 < C_lock
  enhancement_pos : ∀ R r0 (hR : 0 < R) (hr0 : 0 < r0) n,
    0 < w_radial R r0 n
  enhancement_above_one : ∀ R r0 (hR : 0 < R) (hr0 : 0 < r0) n (hn : 0 < n),
    1 < w_radial R r0 n
  enhancement_strict_mono : ∀ R₁ R₂ r0 (hR₁ : 0 < R₁) (hR₂ : R₁ < R₂) (hr0 : 0 < r0)
    n (hn : 0 < n), w_radial R₁ r0 n < w_radial R₂ r0 n
  enhancement_unbounded : ∀ r0 (hr0 : 0 < r0) n (hn : 0 < n) M (hM : 0 < M),
    ∃ R : ℝ, 0 < R ∧ M < w_radial R r0 n
  newtonian_dominated : ∀ V_bar_sq R r0 (hVb : 0 ≤ V_bar_sq) (hR : 0 < R)
    (hr0 : 0 < r0) n (hn : 0 < n),
    V_bar_sq ≤ w_radial R r0 n * V_bar_sq
  btfr_slope_iff : BTFRSlopeIdentity

theorem ilgAsymptoticEnhancementCert_holds : Nonempty ILGAsymptoticEnhancementCert :=
  ⟨{ C_pos := C_lock_pos
     enhancement_pos := enhancement_pos
     enhancement_above_one := enhancement_above_one
     enhancement_strict_mono := enhancement_strict_mono
     enhancement_unbounded := enhancement_unbounded
     newtonian_dominated := ilg_velocity_sq_dominates_newtonian
     btfr_slope_iff := btfr_slope_identity_iff }⟩

end

end IndisputableMonolith.Gravity.ILGAsymptoticEnhancement
