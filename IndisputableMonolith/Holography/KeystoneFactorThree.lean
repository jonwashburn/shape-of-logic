import IndisputableMonolith.Holography.RecordCostAsymmetry
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Factor-3 Keystone: a conditional exclusion of the microstate reading

**Status: CONDITIONAL theorem (panel-greenlit Live Bet 2, 2026-07-01). Nothing here is
unconditional physics; the value of this module is the exclusion STRUCTURE.**

## The claim, in one paragraph

The rank/nullity selector (`RecordCostAsymmetry`) leaves ONE explicit physical premise for
the Bekenstein-Hawking `1/4`: `HorizonEntropyIsRecordCost`. The counterfactual premise
`HorizonEntropyIsMicrostateCost` yields `3/4`, i.e. `S = 3·(A/4)` — a factor EXACTLY 3, at
every horizon radius, machine-checked from the ledger floor (`microstateCost = 3 =
3 · recordCost`). The keystone: IF the Bekenstein bound `S ≤ 2πER` holds for TOTAL
thermodynamic horizon entropy (LEG-B, an OPEN hypothesis stated here as a typed premise,
never proved), and IF the record reading saturates it at the horizon (`A/4 = 2πER`,
Schwarzschild saturation), THEN the microstate reading VIOLATES the bound by the fixed
factor 3 — no volume scaling, no bulk map, no large-`R` limit needed. Conditional on those
two named inputs plus per-pixel additivity (LEG-A), `HorizonEntropyIsRecordCost` is
discharged by exclusion within the proved two-reading dichotomy.

## The typing audit (the panel's explicit question)

The panel asked whether LEG-B's statement "can be total-entropy-typed." Answer, enforced
here by construction: the bound hypothesis `TotalEntropyBekensteinBound` is typed on a
STATIC entropy `S : ℝ` in the same units as the area term — the per-pixel-summed count of
`EntropyCandidateAudit` (candidates C3/C6 scale, bits, or their `ln 2`-converted nats).
It must NOT be typed on `HawkingTemperature.accessibleInfo`, which is a RATE
(nats·tick⁻¹); `EntropyCandidateAudit.accessibleInfo_unfold` exhibits the type mismatch.
The exclusion is invariant under the bits→nats conversion
(`violation_survives_unit_conversion`) because it is a strict ratio-3 statement, so the
unit choice cannot rescue the microstate reading.

## Honest scope (per `soul.mdc`)

- LEG-B (the Casini-form bound as a theorem about RS total entropy): **OPEN.** Stated as
  the explicit `Prop` `TotalEntropyBekensteinBound`, consumed as a hypothesis, never
  asserted.
- Horizon saturation `A/4 = 2πER`: **MODEL input** (Schwarzschild `R = 2GE` in RS units);
  consumed as a hypothesis.
- LEG-A (per-pixel additivity, the spectrometer's `PerPixelRecordAdditivity`): **MODEL
  premise**, measured to hold for private/unshared pixels under GLOBAL closure
  (`SharedCutMarginal`, spectrometer 2026-07-01); consumed as the hypothesis `hAdd`.
- The factor 3 itself: **THEOREM, axiom-clean** (`factor_three_is_ledger_forced`), from
  `decide` on the ledger floor.
- The exclusion given the above: **THEOREM** (`microstate_chain_contradicts_bound`).

The weakest link (LEG-B) sets the tag: this module is a CONDITIONAL discharge, not an
unconditional derivation of `1/4`. What it buys: the selector premise is no longer a bare
identification — inside the holographic program (bound + saturation + additivity) the
kernel reading is INCONSISTENT, not merely disfavored.
-/

namespace IndisputableMonolith
namespace Holography
namespace KeystoneFactorThree

open RecordCostAsymmetry

/-! ## The machine-checked factor 3 -/

/-- **The factor 3 is ledger-forced, not hand-typed.** The kernel-side (microstate) cost of
the one-face closure map is exactly three times its image-side (record) cost: `3 = 3 · 1`.
Both sides are computed by `decide` on the actual map; the `3` in "the microstate reading
assigns `3·(A/4)`" is THIS `3`. -/
theorem factor_three_is_ledger_forced :
    microstateCost (fun c : PixelLocal.FaceCfg => PixelLocal.closed c) true
      = 3 * recordCost (fun c : PixelLocal.FaceCfg => PixelLocal.closed c) := by
  decide

/-- The same factor at the density level: the nullity density `3/4` is three times the rank
density `1/4` (`CoefficientBridge.freeBits = 3 · closureRank`). -/
theorem density_ratio_is_three :
    (CoefficientBridge.freeBits : ℚ) / (CoefficientBridge.rawBits : ℚ)
      = 3 * ((CoefficientBridge.closureRank : ℚ) / (CoefficientBridge.rawBits : ℚ)) := by
  rw [CoefficientBridge.freeBits_eq_three, CoefficientBridge.closureRank_eq_one,
    CoefficientBridge.rawBits_eq_four]
  norm_num

/-! ## LEG-B as an explicit typed premise -/

/-- **LEG-B, total-entropy-typed (OPEN; a premise, never proved here).** The Casini-form
Bekenstein bound on the TOTAL static thermodynamic horizon entropy `S` (same units as the
area term; bits or nats, fixed consistently on both sides). This is the reading the panel
demanded: `S` is a static count (candidates C3/C6 of `EntropyCandidateAudit`), NOT the
posted-information RATE `accessibleInfo` (nats·tick⁻¹), which has the wrong type to appear
here. -/
def TotalEntropyBekensteinBound (S E R : ℝ) : Prop :=
  S ≤ 2 * Real.pi * E * R

/-! ## The keystone at the area level -/

/-- **Record reading saturates the bound.** Given horizon saturation `A/4 = 2πER`, the
record-reading entropy `A/4` satisfies the bound with equality. -/
theorem record_reading_saturates (A E R : ℝ)
    (hSat : A / 4 = 2 * Real.pi * E * R) :
    TotalEntropyBekensteinBound (A / 4) E R :=
  le_of_eq hSat

/-- **Microstate reading violates the saturated bound — at every radius.** Given the same
saturation and a nondegenerate horizon (`0 < A`), the microstate-reading entropy `3·(A/4)`
strictly exceeds the bound. The violation is the fixed factor 3: no volume scaling, no
bulk-to-boundary map, no asymptotics. -/
theorem microstate_reading_violates (A E R : ℝ) (hA : 0 < A)
    (hSat : A / 4 = 2 * Real.pi * E * R) :
    ¬ TotalEntropyBekensteinBound (3 * (A / 4)) E R := by
  unfold TotalEntropyBekensteinBound
  rw [← hSat]
  intro h
  linarith

/-- **The keystone package.** Under saturation, the two readings are separated by the
bound itself: record passes (with equality), microstate fails (strictly). Conditional on
LEG-B this is the selector discharge. -/
theorem keystone_selects_record_reading (A E R : ℝ) (hA : 0 < A)
    (hSat : A / 4 = 2 * Real.pi * E * R) :
    TotalEntropyBekensteinBound (A / 4) E R
      ∧ ¬ TotalEntropyBekensteinBound (3 * (A / 4)) E R :=
  ⟨record_reading_saturates A E R hSat, microstate_reading_violates A E R hA hSat⟩

/-- **Scale-freeness of the violation.** The excess is exactly the constant 3 at every
saturated horizon: `3·(A/4) = 3·(2πER)` whenever `A/4 = 2πER`. This is what distinguishes
the keystone from a `δ`-shell or large-`R` correction argument. -/
theorem violation_is_scale_free (A E R : ℝ)
    (hSat : A / 4 = 2 * Real.pi * E * R) :
    3 * (A / 4) = 3 * (2 * Real.pi * E * R) := by
  rw [hSat]

/-- **The unit choice cannot rescue the microstate reading.** A strict violation in bits
stays a strict violation in nats (multiplying both sides by `ln 2 > 0`), so the exclusion
is invariant under the `EntropyCandidateAudit.bitsToNats` conversion. -/
theorem violation_survives_unit_conversion (S bound : ℝ) (h : bound < S) :
    bound * Real.log 2 < S * Real.log 2 :=
  mul_lt_mul_of_pos_right h (Real.log_pos (by norm_num))

/-! ## The full conditional chain, from the named ℕ-level premises -/

/-- **The microstate chain is inconsistent (the keystone, fully typed).** Assemble the
named premises: the horizon carries per-pixel multiplicity `m` under the MICROSTATE
reading (`HorizonEntropyIsMicrostateCost`, so `m = 3` by `decide`); total entropy is
per-pixel additive over `N ≥ 1` private pixels (LEG-A, `hAdd`); the horizon area in pixel
units is `rawBits · N = 4N` and saturates `A/4 = 2πER` (`hSat`); and the total-entropy
Bekenstein bound holds (LEG-B, `hBound`). CONTRADICTION: `S = 3N > N = 2πER`. So within
the dichotomy, conditional on LEG-A + LEG-B + saturation, the microstate reading is
excluded and `HorizonEntropyIsRecordCost` is forced. -/
theorem microstate_chain_contradicts_bound
    (m N : ℕ) (S E R : ℝ) (hN : 0 < N)
    (hMicro : HorizonEntropyIsMicrostateCost m)
    (hAdd : S = (m : ℝ) * N)
    (hSat : ((CoefficientBridge.rawBits * N : ℕ) : ℝ) / 4 = 2 * Real.pi * E * R)
    (hBound : TotalEntropyBekensteinBound S E R) :
    False := by
  have hm : m = 3 := by
    unfold HorizonEntropyIsMicrostateCost at hMicro
    rw [hMicro]; decide
  have hA : ((CoefficientBridge.rawBits * N : ℕ) : ℝ) = 4 * N := by
    rw [CoefficientBridge.rawBits_eq_four]; push_cast; ring
  rw [hA] at hSat
  unfold TotalEntropyBekensteinBound at hBound
  rw [hAdd, hm, ← hSat] at hBound
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  push_cast at hBound
  linarith

/-- **The record chain is consistent (saturation).** The same assembly under the RECORD
reading (`m = 1`) yields `S = N = 2πER`: the bound is saturated, not violated. Together
with `microstate_chain_contradicts_bound` this is the conditional discharge of
`HorizonEntropyIsRecordCost`: within the proved dichotomy, it is the unique reading
consistent with the (hypothesized) total-entropy Bekenstein bound at a saturated
horizon. -/
theorem record_chain_saturates_bound
    (m N : ℕ) (S E R : ℝ)
    (hRec : HorizonEntropyIsRecordCost m)
    (hAdd : S = (m : ℝ) * N)
    (hSat : ((CoefficientBridge.rawBits * N : ℕ) : ℝ) / 4 = 2 * Real.pi * E * R) :
    TotalEntropyBekensteinBound S E R := by
  have hm : m = 1 := by
    unfold HorizonEntropyIsRecordCost at hRec
    rw [hRec]; exact recordCost_closed
  have hA : ((CoefficientBridge.rawBits * N : ℕ) : ℝ) = 4 * N := by
    rw [CoefficientBridge.rawBits_eq_four]; push_cast; ring
  rw [hA] at hSat
  unfold TotalEntropyBekensteinBound
  rw [hAdd, hm]
  push_cast
  linarith [le_of_eq hSat]

/-- **Certificate.** The keystone in one statement: conditional on LEG-A (per-pixel
additivity), LEG-B (total-entropy Bekenstein bound), and horizon saturation, the
microstate reading is inconsistent and the record reading saturates. The `1/4` premise
`HorizonEntropyIsRecordCost` is thereby discharged BY EXCLUSION within the dichotomy —
modulo exactly the named open legs, nothing else. -/
theorem keystone_certificate :
    (∀ (m N : ℕ) (S E R : ℝ), 0 < N →
        HorizonEntropyIsMicrostateCost m →
        S = (m : ℝ) * N →
        ((CoefficientBridge.rawBits * N : ℕ) : ℝ) / 4 = 2 * Real.pi * E * R →
        TotalEntropyBekensteinBound S E R → False)
    ∧ (∀ (m N : ℕ) (S E R : ℝ),
        HorizonEntropyIsRecordCost m →
        S = (m : ℝ) * N →
        ((CoefficientBridge.rawBits * N : ℕ) : ℝ) / 4 = 2 * Real.pi * E * R →
        TotalEntropyBekensteinBound S E R) :=
  ⟨fun m N S E R hN hMicro hAdd hSat hBound =>
      microstate_chain_contradicts_bound m N S E R hN hMicro hAdd hSat hBound,
    fun m N S E R hRec hAdd hSat =>
      record_chain_saturates_bound m N S E R hRec hAdd hSat⟩

end KeystoneFactorThree
end Holography
end IndisputableMonolith
