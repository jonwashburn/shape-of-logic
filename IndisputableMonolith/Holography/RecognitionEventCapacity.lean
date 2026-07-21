import IndisputableMonolith.Foundation.MeasureForcing

/-!
# RecognitionEventCapacity: the access bound as forced-measure entropy per event

The deflation test (`ThetaAccessDeflation`) killed the naive "eight states per site"
quotient: the physical per-carrier content is a continuum, so the orbit count is not the
physical access bound. The hypothesis this module executes (Jon, 2026-06-26): the right
PHYSICAL access bound is FORCED-MEASUREMENT OUTCOME QUANTIZATION. A single recognition
event resolves into discrete `φ^{-n}`-weighted outcomes (the T9 forced measure, proved in
`Foundation.MeasureForcing`: `probMass n = (1-φ^{-1})·φ^{-n}`, normalized, mean depth `φ`,
partition `φ^2`). The access law is then NOT an orbit count but the INFORMATION CONTENT of
one recognition event, the Shannon entropy of the forced measure, additive over events.

The central number is forced, with no free parameter and no arbitrary alphabet:

* `forcedEntropy = (φ + 2)·log φ` nats (≈ 1.741): information per recognition event.
* `effectiveOutcomes = exp(forcedEntropy) = φ^{φ+2}` (≈ 5.70): the EFFECTIVE outcome count
  (perplexity) per event. Replaces the spurious `8`, and is genuinely different from 8.
* `bitsPerEvent = (φ+2)·log₂ φ` (≈ 2.51 bits) (`bitsPerEvent_eq`).
* `eventAccess k = k·forcedEntropy`: the rebuilt access rate, scaled over `k` events. The
  old `|R|·log₂|α|` bound is the special case where each event is a uniform `α`-symbol.

CRITICAL FRAMING (panel, 2026-06-26), do not overclaim: entropy bounds AVERAGE INFORMATION
/ CHANNEL CAPACITY, NOT zero-error distinguishability. `ThetaAccessDeflation.sumSig_surjective`
proves a forced readout can hard-distinguish INFINITELY many states, so `effectiveOutcomes`
is an EFFECTIVE (perplexity) count, NOT a hard cardinality ceiling, and the rebuilt access
law is a mutual-information / channel-capacity statement, not an injection bound. That is
why it supersedes the deflated orbit count: the orbit count was a false hard ceiling; this
is the true average rate.

Status. THEOREM (axiom-clean), grounded in proved `MeasureForcing` decls: the per-term
log-weight law (`neglog_probMass`), the closed form `probMass n = (φ^{n+2})⁻¹`, the
effective outcome count `φ^{φ+2}`, the bit-rate identity, and additivity. The keystone
`forcedEntropy_eq` (the Shannon-tsum value) is now PROVED (closed 2026-06-26, axiom-clean:
`[propext, Classical.choice, Quot.sound]`): the standard entropy-of-geometric computation,
done from `meanRung_eq_phi` and `probMass_tsum_one` via the additive-tsum split. MODEL: identifying
"information per recognition event" with the entropy of the forced instance-weighting
(cost-sufficiency: the forced measure is the only intrinsic weighting). OPEN, documented
(NOT a faked Prop): the Born bridge, that this entropy is literally the entropy of a
forced-MEASUREMENT outcome distribution (the bridge from the sub-Gaussian L² seed in
`MeasureForcing` to recognition Hilbert space). The elliptic `U(1)` phase sector
(`Recognition_Cost_As_Symplectic_Action`) is where the residual outcome phase lives. Do
NOT assert the Born rule as an identity (a prior panel killed "phase projection = Born").

Anti-vacuity: `forcedEntropy` is the genuine Shannon tsum `-∑ P(n) log P(n)` of the proved
forced measure, not a chosen constant; its value `(φ+2)log φ` is to be computed from
`meanRung_eq_phi` and normalization, never posited. Every consequence below is proved
modulo that one keystone.
-/

namespace IndisputableMonolith
namespace Holography
namespace RecognitionEventCapacity

open IndisputableMonolith.Foundation.MeasureForcing
open scoped BigOperators

noncomputable section

/-- The Shannon entropy (nats) of the forced measure `P(n) = (1-ρ)ρⁿ`: information per
recognition event. -/
noncomputable def forcedEntropy : ℝ := ∑' n : ℕ, probMass n * (-(Real.log (probMass n)))

/-- `1 - ρ = ρ²` (the golden identity `1 - φ⁻¹ = φ⁻²`). -/
theorem one_sub_rho_eq_sq : 1 - rho = rho ^ 2 := by
  rw [one_sub_rho]; unfold rho; rw [div_pow, one_pow]

/-- Closed form: `P(n) = (φ^{n+2})⁻¹`. The forced measure is a pure inverse power of φ. -/
theorem probMass_eq_inv_pow (n : ℕ) : probMass n = (Constants.phi ^ (n + 2))⁻¹ := by
  unfold probMass
  rw [one_sub_rho]
  unfold rho
  rw [div_pow, one_pow, pow_add]
  have hphi : Constants.phi ≠ 0 := ne_of_gt Constants.phi_pos
  field_simp

/-- Per-term log-weight law: `-log P(n) = (n+2)·log φ`, linear in recognition depth. -/
theorem neglog_probMass (n : ℕ) :
    -(Real.log (probMass n)) = ((n : ℝ) + 2) * Real.log Constants.phi := by
  rw [probMass_eq_inv_pow, Real.log_inv, Real.log_pow]
  push_cast
  ring

/-- **The per-event entropy (keystone).** A single recognition event carries `(φ+2)·log φ`
nats, the Shannon entropy of the forced measure, computed from its mean depth `φ`
(`meanRung_eq_phi`) and normalization (`probMass_tsum_one`).

PROVED (2026-06-26, axiom-clean). Strategy realized below:
rewrite each summand by `neglog_probMass` to `probMass n * (((n:ℝ)+2) * log φ)`, then via
`tsum_congr` to `log φ * ((n:ℝ) * probMass n) + (2 * log φ) * probMass n`; split with the
additive tsum lemma using `Summable (fun n => (n:ℝ) * probMass n)` (from
`summable_pow_mul_geometric_of_norm_lt_one 1` times `(1-ρ)`) and `Summable probMass` (from
`summable_geometric_of_lt_one` times `(1-ρ)`); pull constants with `tsum_mul_left`; close
with `meanRung_eq_phi` (`∑ n·P(n) = φ`) and `probMass_tsum_one` (`∑ P(n) = 1`), then `ring`
gives `(φ+2)·log φ`. -/
theorem forcedEntropy_eq :
    forcedEntropy = (Constants.phi + 2) * Real.log Constants.phi := by
  have hnorm : ‖rho‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos rho_pos]; exact rho_lt_one
  have hsP : Summable probMass := by
    have hg : Summable (fun n : ℕ => rho ^ n) :=
      summable_geometric_of_lt_one rho_nonneg rho_lt_one
    have := hg.mul_left (1 - rho)
    simpa [probMass] using this
  have hsNP : Summable (fun n : ℕ => (n : ℝ) * probMass n) := by
    have h0 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * rho ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
    have h1 := h0.mul_left (1 - rho)
    have heq : (fun n : ℕ => (n : ℝ) * probMass n)
        = fun n : ℕ => (1 - rho) * ((n : ℝ) ^ 1 * rho ^ n) := by
      funext n; unfold probMass; ring
    rw [heq]; exact h1
  have hsum2P : Summable (fun n : ℕ => (2 : ℝ) * probMass n) := hsP.mul_left 2
  have hmean : (∑' n : ℕ, (n : ℝ) * probMass n) = Constants.phi := by
    have h := meanRung_eq_phi; unfold meanRung at h; exact h
  have h2sum : (∑' n : ℕ, (2 : ℝ) * probMass n) = 2 := by
    rw [tsum_mul_left, probMass_tsum_one]; ring
  unfold forcedEntropy
  have hstep : (∑' n : ℕ, probMass n * (-(Real.log (probMass n))))
      = Real.log Constants.phi
          * ((∑' n : ℕ, (n : ℝ) * probMass n) + (∑' n : ℕ, (2 : ℝ) * probMass n)) := by
    rw [← hsNP.tsum_add hsum2P, ← tsum_mul_left]
    exact tsum_congr (fun n => by rw [neglog_probMass]; ring)
  rw [hstep, hmean, h2sum]; ring

/-- The effective outcome count per recognition event: the perplexity `exp H` of the
forced measure. EFFECTIVE (average), not a hard distinguishability ceiling (the hard count
is infinite, `ThetaAccessDeflation.sumSig_surjective`). -/
noncomputable def effectiveOutcomes : ℝ := Real.exp forcedEntropy

/-- **The forced effective outcome count is `φ^{φ+2}`** (≈ 5.70), replacing the spurious
`8` of the orbit count. A perplexity / channel-capacity quantity, not a hard ceiling.
Proved modulo the entropy keystone. -/
theorem effectiveOutcomes_eq :
    effectiveOutcomes = Constants.phi ^ (Constants.phi + 2) := by
  unfold effectiveOutcomes
  rw [forcedEntropy_eq,
      show (Constants.phi + 2) * Real.log Constants.phi
        = Real.log Constants.phi * (Constants.phi + 2) from mul_comm _ _,
      ← Real.rpow_def_of_pos Constants.phi_pos]

/-- Bits of information per recognition event. -/
noncomputable def bitsPerEvent : ℝ := forcedEntropy / Real.log 2

/-- **The forced per-event bit rate is `(φ+2)·log₂ φ`** (≈ 2.51 bits), the physically
forced access rate replacing the artifact `3 = log₂ 8`. Proved modulo the entropy
keystone. -/
theorem bitsPerEvent_eq :
    bitsPerEvent = (Constants.phi + 2) * Real.logb 2 Constants.phi := by
  unfold bitsPerEvent Real.logb
  rw [forcedEntropy_eq]
  ring

/-- The information accessible across `k` recognition events, at the forced per-event
rate. MODEL definition: this is `k·H` by construction. The SUBSTANTIVE additivity (that
the entropy of `k` INDEPENDENT events equals `k·H`, via the product measure and the
forced-measure factorization `Factorizes`) is the open next target, NOT this definitional
linearity. -/
noncomputable def eventAccess (k : ℕ) : ℝ := (k : ℝ) * forcedEntropy

/-- Definitional linearity of `eventAccess` (MODEL). This is true by the definition
`eventAccess k = k·H`; it is NOT the substantive product-measure additivity theorem (which
is open). Kept only to record the scaling shape. -/
theorem eventAccess_additive (j k : ℕ) :
    eventAccess (j + k) = eventAccess j + eventAccess k := by
  unfold eventAccess; push_cast; ring

/-- **Recognition-event capacity certificate.** The per-event information is the forced
measure's entropy `(φ+2)log φ`; the effective outcome count is `φ^{φ+2}`; the bit rate is
`(φ+2)log₂φ`; access is additive over events. -/
structure EventCapacityCert : Prop where
  entropy_value : forcedEntropy = (Constants.phi + 2) * Real.log Constants.phi
  outcomes_value : effectiveOutcomes = Constants.phi ^ (Constants.phi + 2)
  bits_value : bitsPerEvent = (Constants.phi + 2) * Real.logb 2 Constants.phi
  additive : ∀ j k : ℕ, eventAccess (j + k) = eventAccess j + eventAccess k

theorem eventCapacityCert : EventCapacityCert where
  entropy_value := forcedEntropy_eq
  outcomes_value := effectiveOutcomes_eq
  bits_value := bitsPerEvent_eq
  additive := eventAccess_additive

end

end RecognitionEventCapacity
end Holography
end IndisputableMonolith
