import IndisputableMonolith.Foundation.DeltaSpine.LadderRatioBounds

/-!
# MassRatioBinding: the muon/electron mass ratio pinned to the φ-ladder (sigma0)

**The first empirical bite of the forced-ratio thread: a measured particle-mass
ratio bound against φ-ladder rungs by choice-free integer arithmetic alone.**

CODATA 2022 gives the muon-electron mass ratio as

  `m_μ / m_e = 206.768 2827 (46)`.

We take the deliberately generous ±10σ window

  `R ∈ [206.7682367, 206.7683287]`,

encoded exactly as the integer interval `[muE_lo, muE_hi] / muE_scale` with
`muE_scale = 10^7`. Everything proved here is a sigma0 arithmetic fact about
those integer endpoints against `phiPow` on ℤ[φ]; the (MEASURED) claim that the
physical ratio lies in the window is CODATA's, quoted in
`MassRatioBindingReal` (sigma1) as an explicit hypothesis, never as a theorem.

Three levels of binding, each a pair of kernel-`decide` facts:

1. **Window** (`muE_window_*`): `φ¹¹ < R_lo` and `R_hi < φ¹²`. The whole
   measured window lies strictly between consecutive ladder rungs 11 and 12.
   The RS mass law (`RSBridge.Anchor`) assigns the muon and electron equal
   charge index `Z = 1332` and rungs 13 and 2, predicting the pure φ-power
   ratio `φ^(13−2) = φ¹¹` — the rung gap this window brackets.

2. **Nearest rung** (`muE_nearest_rung_*`): `φ²¹ < R_lo²` and `R_hi² < φ²³`,
   i.e. `10.5 < log_φ R < 11.5`. Among ALL integers, 11 is the unique nearest
   rung gap to the measured ratio: the RS assignment is not merely consistent
   with the window, it is forced as the closest ladder point.

3. **Deviation bracket** (`muE_deviation_*`): with `ε := log_φ R − 11` the
   deviation of the measured ratio from the exact rung,
   `φ⁶⁹⁸ < R_lo⁶³` and `R_hi⁸⁸ < φ⁹⁷⁵` give the tight rational bracket

     `5/63 < ε < 7/88`   (`0.0793651 < ε < 0.0795455`; ε ≈ 0.0795256).

   Since `7/88 < 1/(4π)` (equivalent to `π < 22/7`; proved at sigma1), the
   bracket REFUTES the naive identification `ε = 1/(4π)` at ≥10σ: the measured
   deviation sits strictly below `1/(4π) ≈ 0.0795775`. Any finer closed form
   for ε is OPEN; this module claims only the bracket.

The mechanism is the sigma0 sign machinery of `DeltaSpine.GoldenInt`
(`IsPos`/`RatLt`/`RatGt`): `p/q < φⁿ` reduces to the sign of an element of
ℤ[φ], decided by comparing `s²` with `5t²` (√5-irrationality,
`int_sq_eq_five_sq`). Integer powers like `muE_lo⁶³` (a 587-digit numerator)
reduce in the kernel via GMP-backed `Int` arithmetic. No `Real`, no `Float`,
no `native_decide`.

**Verdict target: sigma0 DELTA_FORCED** — every theorem here closes within
`{propext, Quot.sound}`. Audit with `scripts/sigma_audit.py`.

Real-side reading and the link to the RS mass law: `MassRatioBindingReal`
(sigma1 CHOICE). Numeric pre-verification:
`scripts/_probe_mass_ratio_binding.py`.

Delta Forcing Spectrum program: `Delta_Forcing_Spectrum_20260626.tex`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DeltaSpine
namespace GoldenInt

/- `phiPow 975` unfolds through 975 nested applications; the kernel needs the
   recursion-depth headroom (measured: the default 512 fails, 100000 passes
   with a wide margin). -/
set_option maxRecDepth 100000

/-! ## The CODATA 2022 window (exact integer encoding)

`m_μ/m_e = 206.7682827(46)`; window = central value ± 10σ, over `10^7`. -/

/-- Lower endpoint of the CODATA 2022 ±10σ window: `206.7682367 · 10⁷`. -/
def muE_lo : ℤ := 2067682367

/-- Upper endpoint of the CODATA 2022 ±10σ window: `206.7683287 · 10⁷`. -/
def muE_hi : ℤ := 2067683287

/-- Common denominator of the window endpoints: `10⁷`. -/
def muE_scale : ℤ := 10000000

/-! ## Level 1: the window lies strictly between rungs 11 and 12 -/

/-- **Window, lower**: `φ¹¹ < R_lo` — the eleventh rung lies strictly below
    the entire measured window (`φ¹¹ ≈ 199.005`). -/
theorem muE_window_lower : RatGt muE_lo muE_scale (phiPow 11) := by decide

/-- **Window, upper**: `R_hi < φ¹²` — the twelfth rung lies strictly above
    the entire measured window (`φ¹² ≈ 321.997`). -/
theorem muE_window_upper : RatLt muE_hi muE_scale (phiPow 12) := by decide

/-! ## Level 2: 11 is the unique nearest rung (`10.5 < log_φ R < 11.5`) -/

/-- **Nearest rung, lower**: `φ²¹ < R_lo²`, i.e. `φ^10.5 < R_lo`. -/
theorem muE_nearest_rung_lower :
    RatGt (muE_lo ^ 2) (muE_scale ^ 2) (phiPow 21) := by decide

/-- **Nearest rung, upper**: `R_hi² < φ²³`, i.e. `R_hi < φ^11.5`. -/
theorem muE_nearest_rung_upper :
    RatLt (muE_hi ^ 2) (muE_scale ^ 2) (phiPow 23) := by decide

/-! ## Level 3: the deviation bracket `5/63 < ε < 7/88`

`ε := log_φ R − 11`. The exponents encode `11 + 5/63 = 698/63` and
`11 + 7/88 = 975/88`. -/

/-- **Deviation, lower**: `φ⁶⁹⁸ < R_lo⁶³`, i.e. `φ^(11 + 5/63) < R_lo`,
    hence `ε > 5/63` across the window. -/
theorem muE_deviation_lower :
    RatGt (muE_lo ^ 63) (muE_scale ^ 63) (phiPow 698) := by decide

/-- **Deviation, upper**: `R_hi⁸⁸ < φ⁹⁷⁵`, i.e. `R_hi < φ^(11 + 7/88)`,
    hence `ε < 7/88` across the window. -/
theorem muE_deviation_upper :
    RatLt (muE_hi ^ 88) (muE_scale ^ 88) (phiPow 975) := by decide

/-- **Mass-ratio binding, delta-forced (sigma0)**: the full bundle. The CODATA
    2022 ±10σ window for `m_μ/m_e` lies strictly inside `(φ¹¹, φ¹²)`, has 11 as
    its unique nearest rung gap (`φ²¹ < R² < φ²³`), and its deviation exponent
    from the exact rung is bracketed by `5/63 < ε < 7/88`. Every conjunct is a
    choice-free integer computation on ℤ[φ], closed by kernel `decide` inside
    `{propext, Quot.sound}`. -/
theorem mass_ratio_binding :
    (RatGt muE_lo muE_scale (phiPow 11) ∧ RatLt muE_hi muE_scale (phiPow 12)) ∧
    (RatGt (muE_lo ^ 2) (muE_scale ^ 2) (phiPow 21) ∧
     RatLt (muE_hi ^ 2) (muE_scale ^ 2) (phiPow 23)) ∧
    (RatGt (muE_lo ^ 63) (muE_scale ^ 63) (phiPow 698) ∧
     RatLt (muE_hi ^ 88) (muE_scale ^ 88) (phiPow 975)) :=
  ⟨⟨muE_window_lower, muE_window_upper⟩,
   ⟨muE_nearest_rung_lower, muE_nearest_rung_upper⟩,
   ⟨muE_deviation_lower, muE_deviation_upper⟩⟩

/-! ## Runtime certificates (`#eval`)

The same decidable predicates evaluated through the compiler, so each bound is
confirmed by two independent engines (kernel + runtime). -/

/-- info: true -/
#guard_msgs in
#eval decide (RatGt muE_lo muE_scale (phiPow 11))

/-- info: true -/
#guard_msgs in
#eval decide (RatLt muE_hi muE_scale (phiPow 12))

/-- info: true -/
#guard_msgs in
#eval decide (RatGt (muE_lo ^ 2) (muE_scale ^ 2) (phiPow 21))

/-- info: true -/
#guard_msgs in
#eval decide (RatLt (muE_hi ^ 2) (muE_scale ^ 2) (phiPow 23))

/-- info: true -/
#guard_msgs in
#eval decide (RatGt (muE_lo ^ 63) (muE_scale ^ 63) (phiPow 698))

/-- info: true -/
#guard_msgs in
#eval decide (RatLt (muE_hi ^ 88) (muE_scale ^ 88) (phiPow 975))

end GoldenInt
end DeltaSpine
end Foundation
end IndisputableMonolith
