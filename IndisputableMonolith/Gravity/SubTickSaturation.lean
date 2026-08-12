import Mathlib
import IndisputableMonolith.Gravity.ILG

/-!
# Sub-Tick Saturation: No Negative Lag, No Sub-Tick Lift

This module discharges item A2 of `plans/RS_Nautilus_Honest_Envelope_Plan_20260701.html`:
what does the ILG weight kernel do below the recognition tick (`Tdyn < τ0`)?

## The problem

The kernel `w = 1 + Clag * ((Tdyn/τ0)^α - 1)` was derived and validated for
galactic timescales (`Tdyn >> τ0`). The Lean implementation (`ILG.w_t_with`)
floors the ratio at a *numerical* regularizer `eps_t = 0.01`, which is a
config parameter, not physics. Extrapolating the raw formula below the tick
gives `w < 1` (down to `w -> 1 - Clag ≈ 0.91` as the ratio -> 0), which was
the source of the "~9% weight-reduction ceiling" claim for optical-band
coherent driving. That extrapolation was never derived.

## The resolution (ledger conservation, gravity side)

The lag term `Clag * (t^α - 1)` is a **recognition cost**: the penalty a
system pays for being recognized across more ledger ticks than its own
dynamics span. Two premises, both from the spine:

1. **Costs are nonnegative** (J ≥ 0 with equality only at balance; the
   T5 cost uniqueness `law_of_logic_forces_jcost` gives `J ≥ 0`).
2. **Nothing pre-pays gravitational recognition.** This is the same
   ledger-conservation principle as `Fusion/PrepaidScreening` ("no unpaid
   discounts"): a discount on a recognition cost requires an environment
   that has already posted part of the path. Fusion has such an environment
   (the screening cloud pays the channel energy). The weight kernel does
   not: there is no channel by which a coherent drive posts the *source
   mass's* recognition events in advance.

Together: an admissible extension of the kernel below the tick must satisfy
`w ≥ 1` everywhere (no negative lag), and must agree with the derived kernel
in its validated regime (`Tdyn ≥ τ0`). We prove the **saturated kernel**
(ratio floored at 1, not at `eps_t`) is the pointwise-LEAST such extension,
and that every admissible extension gives `w = ` (at least) `1` sub-tick.

## Consequences (the honest envelope)

- `w_sat ≥ 1` unconditionally: **there is no sub-tick weight reduction in
  the ILG channel.** The ~9% ceiling is RETRACTED as an artifact of
  extrapolating the raw formula across `t = 1`; the "optical-band
  inversion" strategy with it.
- `w_sat = w_t` for `Tdyn ≥ τ0`: nothing changes where the kernel is
  validated (galactic phenomenology untouched).
- `w_sat = 1` for `Tdyn ≤ τ0`: driving a system faster than the tick makes
  it weight-*neutral*, never light. The floor is exact and attained.
- The raw eps-floored kernel provably dips below 1 sub-tick
  (`w_t_lt_one_subtick`), i.e. it VIOLATES the no-negative-lag premise
  there. This localizes the earlier overstatement precisely: wrong branch
  of a config-regularized formula, not wrong physics.

## Status

Everything in this file is THEOREM (lake-gated, axiom-clean) *given* the
`NoNegativeLag` premise structure, which is stated explicitly as the
hypothesis of the extension theorems, honestly tagged: the premise itself is
DERIVED-UNFORMALIZED from J ≥ 0 + no-prepayment-channel (see the companion
derivation artifact `plans/RS_Prepaid_Screening_Derivation_20260702.html`).

Companion (same conservation law, opposite sign of opportunity):
`Fusion/PrepaidScreening.lean` - where the environment CAN pre-pay, the
discount is exactly the pre-payment; where it cannot, there is no discount.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SubTickSaturation

open ILG

noncomputable section

/-! ## The saturated kernel -/

/-- The raw (un-floored) kernel as a function of the timescale ratio `t = Tdyn/τ0`. -/
def w_raw_ratio (P : Params) (t : ℝ) : ℝ :=
  1 + P.Clag * (Real.rpow t P.alpha - 1)

/-- The saturated kernel: the ratio is floored at 1 (the tick), not at a
    numerical regularizer. Below the tick the kernel saturates to exactly 1. -/
def w_sat_ratio (P : Params) (t : ℝ) : ℝ :=
  w_raw_ratio P (max 1 t)

/-- Saturated kernel on physical arguments. -/
def w_sat (P : Params) (Tdyn τ0 : ℝ) : ℝ :=
  w_sat_ratio P (Tdyn / τ0)

/-! ## The headline: no sub-tick lift -/

/-- **No negative lag.** The saturated kernel is at least 1 for every ratio,
    including the entire sub-tick regime. There is no weight reduction in
    the ILG channel, at any drive frequency. -/
theorem w_sat_ratio_ge_one (P : Params) (H : ParamProps P) (t : ℝ) :
    1 ≤ w_sat_ratio P t := by
  unfold w_sat_ratio w_raw_ratio
  have h_base : (1 : ℝ) ≤ max 1 t := le_max_left 1 t
  have h_pow : (1 : ℝ) ≤ Real.rpow (max 1 t) P.alpha :=
    Real.one_le_rpow h_base H.alpha_nonneg
  have h_mul : 0 ≤ P.Clag * (Real.rpow (max 1 t) P.alpha - 1) :=
    mul_nonneg H.Clag_nonneg (by linarith)
  linarith

theorem w_sat_ge_one (P : Params) (H : ParamProps P) (Tdyn τ0 : ℝ) :
    1 ≤ w_sat P Tdyn τ0 :=
  w_sat_ratio_ge_one P H (Tdyn / τ0)

/-- **Sub-tick saturation is exact.** At or below the tick the kernel is
    exactly 1: a super-tick coherent drive makes the system weight-neutral,
    never light. -/
theorem w_sat_eq_one_subtick (P : Params) (Tdyn τ0 : ℝ)
    (hτ : 0 < τ0) (hT : Tdyn ≤ τ0) : w_sat P Tdyn τ0 = 1 := by
  unfold w_sat w_sat_ratio w_raw_ratio
  have hratio : Tdyn / τ0 ≤ 1 := (div_le_one hτ).mpr hT
  have hmax : max 1 (Tdyn / τ0) = 1 := max_eq_left hratio
  have h1 : Real.rpow (1 : ℝ) P.alpha = 1 := Real.one_rpow P.alpha
  rw [hmax, h1]
  ring

/-- The floor `w = 1` is attained (at `Tdyn = τ0`), so the greatest lower
    bound of the saturated kernel is exactly 1: the retraction of the
    `1 - Clag ≈ 0.91` ceiling is sharp. -/
theorem w_sat_floor_attained (P : Params) (τ0 : ℝ) (hτ : 0 < τ0) :
    w_sat P τ0 τ0 = 1 :=
  w_sat_eq_one_subtick P τ0 τ0 hτ le_rfl

/-! ## Agreement with the derived kernel in its validated regime -/

/-- Above the tick the saturated kernel coincides with the implemented
    `ILG.w_t_with` kernel (for any config with `eps_t ≤ 1`): the saturation
    changes nothing where the kernel was derived and validated. Galactic
    phenomenology is untouched. -/
theorem w_sat_eq_w_t_with_supertick (cfg : Config) (hcfg : ConfigProps cfg)
    (P : Params) (Tdyn τ0 : ℝ) (hτ : 0 < τ0) (hT : τ0 ≤ Tdyn) :
    w_sat P Tdyn τ0 = w_t_with cfg P Tdyn τ0 := by
  unfold w_sat w_sat_ratio w_raw_ratio w_t_with
  have hratio : (1 : ℝ) ≤ Tdyn / τ0 := (one_le_div hτ).mpr hT
  have hmax1 : max 1 (Tdyn / τ0) = Tdyn / τ0 := max_eq_right hratio
  have hmaxe : max cfg.eps_t (Tdyn / τ0) = Tdyn / τ0 :=
    max_eq_right (le_trans hcfg.eps_t_le_one hratio)
  rw [hmax1]
  simp only [hmaxe]

theorem w_sat_eq_w_t_supertick (P : Params) (Tdyn τ0 : ℝ)
    (hτ : 0 < τ0) (hT : τ0 ≤ Tdyn) :
    w_sat P Tdyn τ0 = w_t P Tdyn τ0 :=
  w_sat_eq_w_t_with_supertick defaultConfig defaultConfig_props P Tdyn τ0 hτ hT

/-! ## The raw kernel violates the premise sub-tick (the localized error) -/

/-- **The raw eps-floored kernel dips below 1 sub-tick.** With the default
    config (`eps_t = 0.01 < 1`), a strictly sub-tick ratio, and genuinely
    active parameters (`α > 0`, `Clag > 0`), the implemented kernel gives
    `w < 1`. This is the branch the "~9% weight reduction / optical-band
    inversion" claims were read off. Under the no-negative-lag premise this
    branch is unphysical: the dip is an artifact of the numerical floor
    `eps_t`, not a derived prediction. -/
theorem w_t_lt_one_subtick (P : Params)
    (halpha : 0 < P.alpha) (hClag : 0 < P.Clag)
    (Tdyn τ0 : ℝ) (hτ : 0 < τ0) (hT : 0 ≤ Tdyn) (hsub : Tdyn < τ0) :
    w_t P Tdyn τ0 < 1 := by
  unfold w_t w_t_with
  have hratio_lt : Tdyn / τ0 < 1 := (div_lt_one hτ).mpr hsub
  have hratio_nonneg : 0 ≤ Tdyn / τ0 := div_nonneg hT (le_of_lt hτ)
  set t := max defaultConfig.eps_t (Tdyn / τ0) with ht
  have ht_lt_one : t < 1 := by
    apply max_lt _ hratio_lt
    show defaultConfig.eps_t < 1
    norm_num [defaultConfig]
  have ht_nonneg : 0 ≤ t := le_trans hratio_nonneg (le_max_right _ _)
  have h_pow : Real.rpow t P.alpha < 1 := Real.rpow_lt_one ht_nonneg ht_lt_one halpha
  have h_mul : P.Clag * (Real.rpow t P.alpha - 1) < 0 :=
    mul_neg_of_pos_of_neg hClag (by linarith)
  simp only []
  linarith

/-! ## Minimality: the saturated kernel is the least admissible extension -/

/-- An admissible sub-tick extension of the ILG kernel (as a function of the
    timescale ratio): it must respect no-negative-lag everywhere (costs are
    nonnegative and nothing pre-pays gravitational recognition), and it must
    agree with the derived kernel in the validated regime `t ≥ 1`. -/
structure AdmissibleExtension (P : Params) (g : ℝ → ℝ) : Prop where
  /-- No negative lag: recognition lag is a cost, and gravity has no
      pre-payment channel, so no extension may dip below 1. -/
  no_negative_lag : ∀ t : ℝ, 1 ≤ g t
  /-- Agreement with the derived kernel where it was derived (`t ≥ 1`). -/
  agrees_supertick : ∀ t : ℝ, 1 ≤ t → g t = w_raw_ratio P t

/-- The saturated kernel is itself admissible. -/
theorem w_sat_admissible (P : Params) (H : ParamProps P) :
    AdmissibleExtension P (w_sat_ratio P) where
  no_negative_lag := w_sat_ratio_ge_one P H
  agrees_supertick := by
    intro t ht
    unfold w_sat_ratio
    rw [max_eq_right ht]

/-- **Least-extension theorem.** Every admissible extension dominates the
    saturated kernel pointwise: `w_sat` is the unique minimal completion of
    the ILG kernel below the tick. Any physical sub-tick behavior consistent
    with the ledger premises gives weight ≥ the saturated value, i.e.
    `w ≥ 1`: the no-lift conclusion is forced for the whole admissible
    class, not just for one chosen extension. -/
theorem w_sat_least (P : Params) (g : ℝ → ℝ)
    (hg : AdmissibleExtension P g) (t : ℝ) :
    w_sat_ratio P t ≤ g t := by
  rcases le_or_gt 1 t with ht | ht
  · -- validated regime: both equal the raw kernel
    rw [hg.agrees_supertick t ht]
    unfold w_sat_ratio
    rw [max_eq_right ht]
  · -- sub-tick: w_sat = 1 ≤ g
    have hsat : w_sat_ratio P t = 1 := by
      unfold w_sat_ratio w_raw_ratio
      have h1 : Real.rpow (1 : ℝ) P.alpha = 1 := Real.one_rpow P.alpha
      rw [max_eq_left (le_of_lt ht), h1]
      ring
    rw [hsat]
    exact hg.no_negative_lag t

/-- Uniqueness of the minimal admissible extension: any admissible extension
    that is pointwise-least equals `w_sat_ratio` everywhere. -/
theorem w_sat_unique_least (P : Params) (H : ParamProps P) (g : ℝ → ℝ)
    (hg : AdmissibleExtension P g)
    (hleast : ∀ (h : ℝ → ℝ), AdmissibleExtension P h → ∀ t, g t ≤ h t) :
    ∀ t, g t = w_sat_ratio P t := by
  intro t
  have h1 : g t ≤ w_sat_ratio P t := hleast _ (w_sat_admissible P H) t
  have h2 : w_sat_ratio P t ≤ g t := w_sat_least P g hg t
  linarith

end

end SubTickSaturation
end Gravity
end IndisputableMonolith
