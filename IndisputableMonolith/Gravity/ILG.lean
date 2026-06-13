import Mathlib

namespace IndisputableMonolith
namespace Gravity
namespace ILG

noncomputable section
open Real

/-! Minimal extracted time-kernel basics with parametric interfaces. -/

structure BridgeData where
  tau0 : ℝ

structure BaryonCurves where
  vgas  : ℝ → ℝ
  vdisk : ℝ → ℝ
  vbul  : ℝ → ℝ

/-! Configurable numeric regularization parameters. -/
structure Config where
  upsilonStar : ℝ
  eps_r : ℝ
  eps_v : ℝ
  eps_t : ℝ
  eps_a : ℝ

@[simp] def defaultConfig : Config :=
  { upsilonStar := 1.0
  , eps_r := 1e-12
  , eps_v := 1e-12
  , eps_t := 0.01
  , eps_a := 1e-12 }

structure ConfigProps (cfg : Config) : Prop where
  eps_t_nonneg : 0 ≤ cfg.eps_t
  eps_t_le_one : cfg.eps_t ≤ 1

@[simp] lemma defaultConfig_props : ConfigProps defaultConfig := by
  refine ⟨?h0, ?h1⟩ <;> norm_num

def vbarSq_with (cfg : Config) (C : BaryonCurves) (r : ℝ) : ℝ :=
  max 0 ((C.vgas r) ^ 2 + ((Real.sqrt cfg.upsilonStar) * (C.vdisk r)) ^ 2 + (C.vbul r) ^ 2)

def vbar_with (cfg : Config) (C : BaryonCurves) (r : ℝ) : ℝ :=
  Real.sqrt (max cfg.eps_v (vbarSq_with cfg C r))

def gbar_with (cfg : Config) (C : BaryonCurves) (r : ℝ) : ℝ :=
  (vbar_with cfg C r) ^ 2 / max cfg.eps_r r

structure Params where
  alpha      : ℝ
  Clag       : ℝ
  A          : ℝ
  r0         : ℝ
  p          : ℝ
  hz_over_Rd : ℝ

structure ParamProps (P : Params) : Prop where
  alpha_nonneg : 0 ≤ P.alpha
  Clag_nonneg  : 0 ≤ P.Clag
  Clag_le_one  : P.Clag ≤ 1
  A_nonneg     : 0 ≤ P.A
  r0_pos       : 0 < P.r0
  p_pos        : 0 < P.p

def w_t_with (cfg : Config) (P : Params) (Tdyn τ0 : ℝ) : ℝ :=
  let t := max cfg.eps_t (Tdyn / τ0)
  1 + P.Clag * (Real.rpow t P.alpha - 1)

@[simp] def w_t (P : Params) (Tdyn τ0 : ℝ) : ℝ := w_t_with defaultConfig P Tdyn τ0

@[simp] def w_t_display (P : Params) (B : BridgeData) (Tdyn : ℝ) : ℝ :=
  w_t_with defaultConfig P Tdyn B.tau0

lemma eps_t_le_one_default : defaultConfig.eps_t ≤ (1 : ℝ) := by
  norm_num

/-- Reference identity under nonzero tick: w_t(τ0, τ0) = 1. -/
lemma w_t_ref_with (cfg : Config) (hcfg : ConfigProps cfg)
  (P : Params) (τ0 : ℝ) (hτ : τ0 ≠ 0) : w_t_with cfg P τ0 τ0 = 1 := by
  dsimp [w_t_with]
  have hdiv : τ0 / τ0 = (1 : ℝ) := by
    field_simp [hτ]
  have hmax : max cfg.eps_t (τ0 / τ0) = (1 : ℝ) := by
    simpa [hdiv, max_eq_right hcfg.eps_t_le_one]
  simp [hmax]

lemma w_t_ref (P : Params) (τ0 : ℝ) (hτ : τ0 ≠ 0) : w_t P τ0 τ0 = 1 :=
  w_t_ref_with defaultConfig defaultConfig_props P τ0 hτ

lemma w_t_rescale_with (cfg : Config) (P : Params) (c Tdyn τ0 : ℝ) (hc : 0 < c) :
  w_t_with cfg P (c * Tdyn) (c * τ0) = w_t_with cfg P Tdyn τ0 := by
  dsimp [w_t_with]
  have hc0 : (c : ℝ) ≠ 0 := ne_of_gt hc
  have : (c * Tdyn) / (c * τ0) = Tdyn / τ0 := by field_simp [hc0]
  simp [this]

lemma w_t_rescale (P : Params) (c Tdyn τ0 : ℝ) (hc : 0 < c) :
  w_t P (c * Tdyn) (c * τ0) = w_t P Tdyn τ0 :=
  w_t_rescale_with defaultConfig P c Tdyn τ0 hc

/-- Nonnegativity of time-kernel under ParamProps. -/
lemma w_t_nonneg_with (cfg : Config) (hcfg : ConfigProps cfg)
  (P : Params) (H : ParamProps P) (Tdyn τ0 : ℝ) :
  0 ≤ w_t_with cfg P Tdyn τ0 := by
  dsimp [w_t_with]
  set t := max cfg.eps_t (Tdyn / τ0) with ht
  have ht_nonneg : 0 ≤ t := by
    have hle : cfg.eps_t ≤ t := by
      simpa [ht] using le_max_left cfg.eps_t (Tdyn / τ0)
    exact le_trans hcfg.eps_t_nonneg hle
  have hrpow_nonneg : 0 ≤ Real.rpow t P.alpha := by
    simpa using Real.rpow_nonneg ht_nonneg P.alpha
  have h_rpow_minus_one : (-1 : ℝ) ≤ Real.rpow t P.alpha - 1 := by
    linarith
  have h_mul : (-P.Clag : ℝ) ≤ P.Clag * (Real.rpow t P.alpha - 1) := by
    have h := mul_le_mul_of_nonneg_left h_rpow_minus_one H.Clag_nonneg
    -- h : P.Clag * (-1) ≤ P.Clag * (Real.rpow t P.alpha - 1)
    simpa using h
  have h_base : 0 ≤ (1 : ℝ) - P.Clag := sub_nonneg.mpr H.Clag_le_one
  have h_lower : (1 : ℝ) - P.Clag ≤ 1 + P.Clag * (Real.rpow t P.alpha - 1) := by
    linarith
  exact le_trans h_base h_lower

lemma w_t_nonneg (P : Params) (H : ParamProps P) (Tdyn τ0 : ℝ) :
    0 ≤ w_t P Tdyn τ0 := by
  -- For defaultConfig, eps_t = 0.01 > 0.
  -- Thus t = max(0.01, Tdyn/τ0) > 0.
  -- rpow t alpha is non-negative for t > 0.
  -- Result follows from Clag <= 1.
  unfold w_t
  exact w_t_nonneg_with defaultConfig defaultConfig_props P H Tdyn τ0

/-- Time-kernel is at least 1 when alpha >= 0, Clag >= 0 and Tdyn >= tau0. -/
lemma w_t_ge_one (P : Params) (H : ParamProps P) (Tdyn τ0 : ℝ) (hτ : 0 < τ0) (hT : τ0 ≤ Tdyn) :
    1 ≤ w_t P Tdyn τ0 := by
  unfold w_t w_t_with
  let t := max defaultConfig.eps_t (Tdyn / τ0)
  have h_ratio : 1 ≤ Tdyn / τ0 := (one_le_div hτ).mpr hT
  have h_base : 1 ≤ t := le_max_of_le_right h_ratio
  -- Since base >= 1 and alpha >= 0, base^alpha >= 1
  have h_pow : 1 ≤ t ^ P.alpha := Real.one_le_rpow h_base H.alpha_nonneg
  have h_diff : 0 ≤ t ^ P.alpha - 1 := sub_nonneg.mpr h_pow
  have h_mul : 0 ≤ P.Clag * (t ^ P.alpha - 1) :=
    mul_nonneg H.Clag_nonneg h_diff
  -- Goal: 1 ≤ 1 + P.Clag * (t ^ P.alpha - 1)
  -- This follows from h_mul: 0 ≤ P.Clag * (t ^ P.alpha - 1)
  simp only [ge_iff_le, le_add_iff_nonneg_right]
  exact h_mul

end
end ILG
end Gravity
end IndisputableMonolith
