import IndisputableMonolith.Holography.SeamTransferCore

/-!
# SeamLedgerDischarge: typing the R1–R4 residue and pushing B2 below the anomaly reading

**Derivation-captain acceptance 2026-07-05** (residues `derive_20260705_135226` [R1],
`derive_20260705_155804` [R2], `derive_20260705_171355` [R3], `derive_20260705_184734`
[R4], Opus-critic passed): the four conjuncts of `ConservingSeamPricing` are grounded
in ledger language. This module TYPES that residue in its WEAKEST honest form and
proves that B2 (the deficit-free period `β = 2π/κ` is the UNIQUE zero of the
per-cycle seam cost) survives a strict weakening of the fourth conjunct: the exact
character-anomaly reading `Tr(W)/2 − 1` is NOT load-bearing for the B2 zero set.

## What is THEOREM here (all Lean, no sorry, no axioms)

1. **The trace bound (THEOREM, the key new lemma).** A pairing-CONSERVING transfer
   with real eigenvalue `x > 0` has `Tr W = x + x⁻¹ ≥ 2`, with equality iff `x = 1`
   (`conserving_trace_bound`). Route: `preserves_pairForm_iff_det_one` (R2's ledger
   conservation IS unimodularity) + `balanced_trace` (Cayley–Hamilton) + AM–GM.
2. **B2 from the weak premise (THEOREM, FORCED-CONDITIONAL).** For ANY trace
   reading `f` with `f 2 = 0` (calibration) and `f t ≠ 0` for `t > 2`
   (faithfulness), `LedgerClosurePricing` forces `C κ T = 0 ↔ T = 2π/κ`
   (`b2_unique_zero_of_ledgerClosure`). No `J`, no `cosh`, no anomaly normalization
   enters the zero-set argument.
3. **The bridge (THEOREM).** At the anomaly reading `f = (·/2 − 1)`, the weak
   premise is EQUIVALENT to `ConservingSeamPricing` (`anomalyLedger_iff_conserving`);
   the existing chain `seamTransferPricing_of_conserving` →
   `censusPricing_of_seamTransfer` → `b2_unique_zero_of_conserving` is then CITED,
   never re-proved, to recover `C = J(turnRatio)` and B2.
4. **Non-vacuity (THEOREM).** `turnRatioCost` satisfies the weak premise via the
   `hyperbolicWitness` family (`ledgerClosurePricing_turnRatioCost`), and every
   reading `R` is realized by its own induced cost
   (`ledgerClosurePricing_readingCost`).
5. **Tightness (THEOREM).** Dropping faithfulness or calibration KILLS the
   discharge (`faithfulness_is_load_bearing`, `calibration_is_load_bearing`): the
   weakening is honest — nothing weaker closes B2.

## What stays OPEN (do not overclaim)

- **B3**: the identification of `κ` with the horizon's continued clock rate is
  typed elsewhere and remains OPEN; R3's `turnRatio` delivery is conditional on it.
- **Physical instantiation**: that the ACTUAL seam cost functional satisfies
  `LedgerClosurePricing` for some `TraceReading` — i.e., that the physical seam's
  closure action, cost report, and audit discipline realize R1–R4 — is the residue.
  The prose R1–R4 ground each conjunct in T2 double-entry language; the Lean premise
  is tagged **MODEL-until-derived**. Every consumer below is **FORCED-CONDITIONAL**;
  the weakest link sets the tag (`soul.mdc`).
-/

namespace IndisputableMonolith
namespace Holography
namespace SeamLedgerDischarge

open SeamTransferCore TurnRatioCarrier

/-! ## Scalar AM–GM half: `x + x⁻¹ ≥ 2` on positives, tight exactly at 1 -/

/-- AM–GM for a positive real and its reciprocal: `2 ≤ x + x⁻¹`. This is the
scalar engine of the discharge: it converts "delivered eigenvalue exists and is
positive" into a one-sided bound on the ONLY audit invariant (the trace). -/
theorem two_le_add_inv {x : ℝ} (hx : 0 < x) : 2 ≤ x + x⁻¹ := by
  have h1 : x * x⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hx)
  nlinarith [sq_nonneg (x - 1), hx, h1]

/-- The AM–GM bound is tight EXACTLY at `x = 1`: `x + x⁻¹ = 2 ↔ x = 1` on
positives. The unique-zero structure of B2 lives entirely in this equivalence. -/
theorem add_inv_eq_two_iff {x : ℝ} (hx : 0 < x) : x + x⁻¹ = 2 ↔ x = 1 := by
  constructor
  · intro h
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h1 : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
    have hsq : (x - 1) * (x - 1) = 0 := by nlinarith [h, h1, hx]
    have h0 : x - 1 = 0 := by
      rcases mul_eq_zero.mp hsq with h' | h' <;> exact h'
    linarith
  · rintro rfl
    norm_num

/-! ## The key new lemma (B): conservation + positive delivery bound the trace -/

/-- **R2 + R3 force the trace (THEOREM).** A transfer conserving the double-entry
pairing form (R2, the ledger conservation sentence — converted to `det = 1` by
`preserves_pairForm_iff_det_one`, CITED) with a real eigenvalue `x ≠ 0` (R3, the
delivered leg) has `Tr W = x + x⁻¹`, by `balanced_trace` (CITED, Cayley–Hamilton).
The reciprocal leg is derived, never posited (the circularity fence). -/
theorem conserving_trace_eq {W : Matrix (Fin 2) (Fin 2) ℝ} {x : ℝ}
    (hcons : ∀ u v, pairForm (W.mulVec u) (W.mulVec v) = pairForm u v)
    (hx : 0 < x) (h : HasRealEigen W x) :
    W.trace = x + x⁻¹ :=
  balanced_trace ((preserves_pairForm_iff_det_one W).mp hcons) (ne_of_gt hx) h

/-- **The conserving trace is bounded below by 2 (THEOREM).** Any pairing-conserving
transfer with positive delivered eigenvalue has trace at least the identity's. -/
theorem conserving_trace_ge_two {W : Matrix (Fin 2) (Fin 2) ℝ} {x : ℝ}
    (hcons : ∀ u v, pairForm (W.mulVec u) (W.mulVec v) = pairForm u v)
    (hx : 0 < x) (h : HasRealEigen W x) :
    2 ≤ W.trace := by
  rw [conserving_trace_eq hcons hx h]
  exact two_le_add_inv hx

/-- **The trace hits 2 exactly at unit delivery (THEOREM).** `Tr W = 2 ↔ x = 1`:
the entire zero-set content of B2, expressed on the audit invariant alone. -/
theorem conserving_trace_eq_two_iff {W : Matrix (Fin 2) (Fin 2) ℝ} {x : ℝ}
    (hcons : ∀ u v, pairForm (W.mulVec u) (W.mulVec v) = pairForm u v)
    (hx : 0 < x) (h : HasRealEigen W x) :
    W.trace = 2 ↔ x = 1 := by
  rw [conserving_trace_eq hcons hx h]
  exact add_inv_eq_two_iff hx

/-- **The key new lemma, bundled (THEOREM):** for pairing-conserving `W` with real
eigenvalue `x > 0`, `Tr W = x + x⁻¹ ≥ 2`, with equality iff `x = 1`. This is what
lets the discharge below run on ANY calibrated faithful trace reading, not just the
character anomaly: the trace separates "deficit-free" from "mismatched" all by
itself. -/
theorem conserving_trace_bound {W : Matrix (Fin 2) (Fin 2) ℝ} {x : ℝ}
    (hcons : ∀ u v, pairForm (W.mulVec u) (W.mulVec v) = pairForm u v)
    (hx : 0 < x) (h : HasRealEigen W x) :
    W.trace = x + x⁻¹ ∧ 2 ≤ W.trace ∧ (W.trace = 2 ↔ x = 1) :=
  ⟨conserving_trace_eq hcons hx h, conserving_trace_ge_two hcons hx h,
    conserving_trace_eq_two_iff hcons hx h⟩

/-! ## The typed residue premise (R1–R4, weakest honest form) -/

/-- **The R4 residue, weakened to its zero-set content.** R4 (audit invariance: the
reported cost is a conjugation class function, because debit/credit are roles and any
invertible recombination of the pair fiber is an audit-equivalent relabeling) plus
`sl2_add_inv` (CITED from `SeamTransferCore`: the trace is the unique conjugation
invariant of a unimodular 2×2 transfer) says the cost reads `W` only through
`Tr W`. We type the CONCLUSION of that argument — a single reading function of the
trace — plus the two minimal audit normalizations a zero-set theorem needs:

* `calibrated`: the identity closure (trace 2, unit delivery) is free. This is a
  point condition at ONE trace value, the weakest calibration usable.
* `faithful`: a genuine mismatch is not free. Weakened from strict monotonicity on
  `[2, ∞)`: nonvanishing on `(2, ∞)` is strictly weaker (strict mono + `f 2 = 0`
  implies it), and `(2, ∞)` is EXACTLY the trace range of conserving transfers with
  positive non-unit delivery (`conserving_trace_bound`), so nothing weaker can close
  B2 — `faithfulness_is_load_bearing` below proves the necessity.

Crucially, `f = fun t => t/2 − 1` (the character anomaly) is NOT baked in: the exact
anomaly reading is not load-bearing for B2's zero set. -/
structure TraceReading where
  /-- The reading function: R4's class-function property, factored through the trace
  (the unique conjugation invariant at `det = 1`, per `sl2_add_inv`, CITED). -/
  f : ℝ → ℝ
  /-- Calibration (R4, ledger normalization): the identity closure — no mismatch,
  trace 2 — posts zero cost. -/
  calibrated : f 2 = 0
  /-- Faithfulness (R4, audit discipline): a strictly imbalanced closure — trace
  strictly above the identity's — cannot read as free. Stated only on `(2, ∞)`, the
  exact realizable range; the weakest condition that closes B2. -/
  faithful : ∀ t : ℝ, 2 < t → f t ≠ 0

/-- **The typed R1–R4 premise (MODEL until derived).** For each `(κ, T)` the seam's
closure action is:

* **R1 (linearity, carried by the type):** a matrix `W : Matrix (Fin 2) (Fin 2) ℝ`
  on the 2d pair fiber — the additive composition of double-entry postings, banked
  from T2, is the linearity; no spectral form is posited.
* **R2 (conservation):** `W` conserves the double-entry pairing form `pairForm`
  (the oriented debit/credit cross-exposure); a closure that changed it would post
  a debit without matching credit, violating T2. No determinant is NAMED here;
  `preserves_pairForm_iff_det_one` (CITED) converts.
* **R3 (delivery):** the delivered leg scales by the turn ratio `x = κT/(2π)`
  (`HasRealEigen W (turnRatio κ T)`); the `2π` is B1's exponential-lattice closure
  geometry, `κ` is B3's clock rate (typed, OPEN). No other eigenvalue is posited.
* **R4 (weakened reading):** the reported cost is `R.f (Tr W)` for the fixed
  calibrated, faithful reading `R` — NOT necessarily the character anomaly.

STATUS: **MODEL-until-derived** from the seam ledger. Consumers below are
**FORCED-CONDITIONAL** on this premise; the weakest link sets the tag. -/
def LedgerClosurePricing (R : TraceReading) (C : ℝ → ℝ → ℝ) : Prop :=
  ∀ kappa T : ℝ, 0 < kappa → 0 < T →
    ∃ W : Matrix (Fin 2) (Fin 2) ℝ,
      (∀ u v, pairForm (W.mulVec u) (W.mulVec v) = pairForm u v) ∧
      HasRealEigen W (turnRatio kappa T) ∧
      C kappa T = R.f W.trace

/-! ## (C) The B2 discharge from the weak premise -/

/-- **B2 from the weak residue (THEOREM, FORCED-CONDITIONAL on
`LedgerClosurePricing`).** For ANY calibrated faithful trace reading, the
deficit-free period `β = 2π/κ` is the UNIQUE zero of the per-cycle cost:

* off the period, `turnRatio ≠ 1` (`turnRatio_eq_one_iff`, CITED), so the trace is
  strictly above 2 (`conserving_trace_bound`) and faithfulness forbids a zero;
* at the period, `turnRatio = 1`, the trace is exactly 2, and calibration fires.

The character anomaly appears NOWHERE: the B2 zero set is forced by conservation,
delivery, calibration, and faithfulness alone. -/
theorem b2_unique_zero_of_ledgerClosure (R : TraceReading) (C : ℝ → ℝ → ℝ)
    (h : LedgerClosurePricing R C) (kappa T : ℝ) (hk : 0 < kappa) (hT : 0 < T) :
    C kappa T = 0 ↔ T = DeficitFreePeriod.euclideanPeriod kappa := by
  obtain ⟨W, hcons, heig, hC⟩ := h kappa T hk hT
  have hx : 0 < turnRatio kappa T := turnRatio_pos hk hT
  rw [hC]
  constructor
  · intro h0
    by_contra hne
    have hx1 : turnRatio kappa T ≠ 1 := fun h1 =>
      hne ((turnRatio_eq_one_iff kappa T hk).mp h1)
    have htr2 : W.trace ≠ 2 := fun heq =>
      hx1 ((conserving_trace_eq_two_iff hcons hx heig).mp heq)
    have hgt : 2 < W.trace :=
      lt_of_le_of_ne (conserving_trace_ge_two hcons hx heig) (Ne.symm htr2)
    exact R.faithful W.trace hgt h0
  · intro hTeq
    have hx1 : turnRatio kappa T = 1 := (turnRatio_eq_one_iff kappa T hk).mpr hTeq
    have htr : W.trace = 2 := by
      rw [conserving_trace_eq hcons hx heig, hx1]
      norm_num
    rw [htr]
    exact R.calibrated

/-! ## (D) The bridge to the existing chain at the anomaly reading -/

/-- The character-anomaly reading: `f t = t/2 − 1`, calibrated (`f 2 = 0`) and
faithful (`f t > 0` for `t > 2`). This is ONE admissible reading among many; the
discharge above never needs it. It exists to connect to the landed chain. -/
noncomputable def anomalyReading : TraceReading where
  f := fun t => t / 2 - 1
  calibrated := by norm_num
  faithful := by
    intro t ht
    have hpos : 0 < t / 2 - 1 := by linarith
    exact ne_of_gt hpos

@[simp] theorem anomalyReading_apply (t : ℝ) :
    anomalyReading.f t = t / 2 - 1 := rfl

/-- **The bridge (THEOREM).** If the reading IS the character anomaly, the weak
premise implies `ConservingSeamPricing` (CITED from `SeamTransferCore`): the pieces
are literally the same conjuncts, with `R.f (Tr W)` definitionally `charAnomaly W`. -/
theorem conservingSeamPricing_of_anomalyLedger (C : ℝ → ℝ → ℝ)
    (h : LedgerClosurePricing anomalyReading C) :
    SeamTransferCore.ConservingSeamPricing C := by
  intro kappa T hk hT
  obtain ⟨W, hcons, heig, hC⟩ := h kappa T hk hT
  refine ⟨W, hcons, heig, ?_⟩
  rw [hC]
  exact anomalyReading_apply W.trace

/-- **The anomaly instance is exactly the landed premise (THEOREM).** At the
character-anomaly reading, `LedgerClosurePricing` and `ConservingSeamPricing` are
equivalent: the weak premise strictly GENERALIZES the landed one (any other
calibrated faithful reading is also admitted), losing nothing at the anomaly point. -/
theorem anomalyLedger_iff_conserving (C : ℝ → ℝ → ℝ) :
    LedgerClosurePricing anomalyReading C ↔
      SeamTransferCore.ConservingSeamPricing C := by
  constructor
  · exact conservingSeamPricing_of_anomalyLedger C
  · intro h kappa T hk hT
    obtain ⟨W, hcons, heig, hC⟩ := h kappa T hk hT
    exact ⟨W, hcons, heig, hC.trans rfl⟩

/-- **CensusPricing through the chain (THEOREM, CITED).** Anomaly-read ledger
pricing yields `CensusPricing` via `seamTransferPricing_of_conserving` and
`censusPricing_of_seamTransfer` — cited, never re-proved. -/
theorem censusPricing_of_anomalyLedger (C : ℝ → ℝ → ℝ)
    (h : LedgerClosurePricing anomalyReading C) :
    TurnRatioCarrier.CensusPricing C :=
  censusPricing_of_seamTransfer C
    (seamTransferPricing_of_conserving C
      (conservingSeamPricing_of_anomalyLedger C h))

/-- **The cost is J of the turn ratio (THEOREM, FORCED-CONDITIONAL).** At the
anomaly reading, the weak premise forces `C κ T = J(κT/2π)` — the full T5 pricing,
recovered by citation of the landed chain. -/
theorem cost_eq_J_of_anomalyLedger (C : ℝ → ℝ → ℝ)
    (h : LedgerClosurePricing anomalyReading C)
    (kappa T : ℝ) (hk : 0 < kappa) (hT : 0 < T) :
    C kappa T = Cost.Jcost (turnRatio kappa T) :=
  censusPricing_of_anomalyLedger C h kappa T hk hT

/-- **B2 through the landed chain (THEOREM, CITED).** At the anomaly reading the B2
discharge also follows from `b2_unique_zero_of_conserving` — consistency check that
the weak route and the landed route agree on the zero set. -/
theorem b2_unique_zero_of_anomalyLedger (C : ℝ → ℝ → ℝ)
    (h : LedgerClosurePricing anomalyReading C)
    (kappa T : ℝ) (hk : 0 < kappa) (hT : 0 < T) :
    C kappa T = 0 ↔ T = DeficitFreePeriod.euclideanPeriod kappa :=
  b2_unique_zero_of_conserving C
    (conservingSeamPricing_of_anomalyLedger C h) kappa T hk hT

/-! ## (E) Non-vacuity witnesses -/

/-- **Non-vacuity (THEOREM).** The turn-ratio cost satisfies the weak premise at
the anomaly reading, witnessed by the `hyperbolicWitness` family (CITED, witness
only — never the construction, per the circularity fence). -/
theorem ledgerClosurePricing_turnRatioCost :
    LedgerClosurePricing anomalyReading TurnRatioCarrier.turnRatioCost := by
  intro kappa T hk hT
  have hx : 0 < turnRatio kappa T := turnRatio_pos hk hT
  have hdet : (hyperbolicWitness (turnRatio kappa T)).det = 1 :=
    hyperbolicWitness_det _ (ne_of_gt hx)
  refine ⟨hyperbolicWitness (turnRatio kappa T),
    (preserves_pairForm_iff_det_one _).mpr hdet,
    hyperbolicWitness_eigen _, ?_⟩
  have hJ : SeamTransferCore.charAnomaly (hyperbolicWitness (turnRatio kappa T))
      = Cost.Jcost (turnRatio kappa T) :=
    charAnomaly_eq_J hdet hx (hyperbolicWitness_eigen _)
  calc TurnRatioCarrier.turnRatioCost kappa T
      = Cost.Jcost (turnRatio kappa T) := rfl
    _ = SeamTransferCore.charAnomaly (hyperbolicWitness (turnRatio kappa T)) :=
        hJ.symm
    _ = anomalyReading.f (hyperbolicWitness (turnRatio kappa T)).trace := rfl

/-- **Non-vacuity for EVERY reading (THEOREM).** Each `TraceReading` is realized by
its own induced cost `R.f (x + x⁻¹)` via the hyperbolic witness family: the weak
premise is inhabited at every admissible reading, so its generality is not vacuous. -/
theorem ledgerClosurePricing_readingCost (R : TraceReading) :
    LedgerClosurePricing R
      (fun kappa T => R.f (turnRatio kappa T + (turnRatio kappa T)⁻¹)) := by
  intro kappa T hk hT
  have hx : 0 < turnRatio kappa T := turnRatio_pos hk hT
  have hdet : (hyperbolicWitness (turnRatio kappa T)).det = 1 :=
    hyperbolicWitness_det _ (ne_of_gt hx)
  have hcons : ∀ u v, pairForm ((hyperbolicWitness (turnRatio kappa T)).mulVec u)
      ((hyperbolicWitness (turnRatio kappa T)).mulVec v) = pairForm u v :=
    (preserves_pairForm_iff_det_one _).mpr hdet
  refine ⟨hyperbolicWitness (turnRatio kappa T), hcons,
    hyperbolicWitness_eigen _, ?_⟩
  have htr := conserving_trace_eq hcons hx (hyperbolicWitness_eigen _)
  exact congrArg R.f htr.symm

/-! ## Tightness: the weakening is exactly as weak as B2 allows -/

/-- **Faithfulness is load-bearing (THEOREM).** Dropping `faithful` (keeping the
calibrated reading `f ≡ 0`) admits the identically-zero cost, whose zero set
contains periods OFF the deficit-free period: B2's uniqueness fails. So the
faithfulness clause of `TraceReading` is necessary, not decorative. -/
theorem faithfulness_is_load_bearing :
    ∃ C : ℝ → ℝ → ℝ,
      (∀ kappa T : ℝ, 0 < kappa → 0 < T →
        ∃ W : Matrix (Fin 2) (Fin 2) ℝ,
          (∀ u v, pairForm (W.mulVec u) (W.mulVec v) = pairForm u v) ∧
          HasRealEigen W (turnRatio kappa T) ∧
          C kappa T = (fun _ : ℝ => (0 : ℝ)) W.trace) ∧
      ∃ kappa T : ℝ, 0 < kappa ∧ 0 < T ∧ C kappa T = 0 ∧
        T ≠ DeficitFreePeriod.euclideanPeriod kappa := by
  refine ⟨fun _ _ => 0, ?_, 1, 1, one_pos, one_pos, rfl, ?_⟩
  · intro kappa T hk hT
    have hx : 0 < turnRatio kappa T := turnRatio_pos hk hT
    exact ⟨hyperbolicWitness (turnRatio kappa T),
      (preserves_pairForm_iff_det_one _).mpr
        (hyperbolicWitness_det _ (ne_of_gt hx)),
      hyperbolicWitness_eigen _, rfl⟩
  · intro hTeq
    have h1 : turnRatio 1 1 = 1 := (turnRatio_eq_one_iff 1 1 one_pos).mpr hTeq
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h2pi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    unfold TurnRatioCarrier.turnRatio at h1
    rw [div_eq_one_iff_eq h2pi] at h1
    linarith

/-- **Calibration is load-bearing (THEOREM).** Dropping `calibrated` (keeping the
faithful reading `f ≡ 1`) admits the constant cost `1`, which has NO zero at all:
the deficit-free period would not be a zero, and B2's existence half fails. -/
theorem calibration_is_load_bearing :
    ∃ C : ℝ → ℝ → ℝ,
      (∀ kappa T : ℝ, 0 < kappa → 0 < T →
        ∃ W : Matrix (Fin 2) (Fin 2) ℝ,
          (∀ u v, pairForm (W.mulVec u) (W.mulVec v) = pairForm u v) ∧
          HasRealEigen W (turnRatio kappa T) ∧
          C kappa T = (fun _ : ℝ => (1 : ℝ)) W.trace) ∧
      ∀ kappa T : ℝ, C kappa T ≠ 0 := by
  refine ⟨fun _ _ => 1, ?_, fun _ _ => one_ne_zero⟩
  intro kappa T hk hT
  have hx : 0 < turnRatio kappa T := turnRatio_pos hk hT
  exact ⟨hyperbolicWitness (turnRatio kappa T),
    (preserves_pairForm_iff_det_one _).mpr
      (hyperbolicWitness_det _ (ne_of_gt hx)),
    hyperbolicWitness_eigen _, rfl⟩

/-! ## Certificate -/

/-- Bundled certificate for the R1–R4 discharge: the trace bound is forced by
conservation and positive delivery; B2 holds under EVERY calibrated faithful
reading (the character anomaly is not load-bearing for the zero set); the anomaly
instance is exactly the landed `ConservingSeamPricing`; and the premise is
inhabited. All fields unconditional THEOREMs; the physical instantiation of
`LedgerClosurePricing` for the actual seam stays the named MODEL premise, consumed
only by the FORCED-CONDITIONAL discharge theorems, stated separately. -/
structure SeamLedgerDischargeCert : Prop where
  trace_forced : ∀ (W : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ),
    (∀ u v, pairForm (W.mulVec u) (W.mulVec v) = pairForm u v) →
    0 < x → HasRealEigen W x →
    W.trace = x + x⁻¹ ∧ 2 ≤ W.trace ∧ (W.trace = 2 ↔ x = 1)
  b2_any_reading : ∀ (R : TraceReading) (C : ℝ → ℝ → ℝ),
    LedgerClosurePricing R C → ∀ kappa T : ℝ, 0 < kappa → 0 < T →
      (C kappa T = 0 ↔ T = DeficitFreePeriod.euclideanPeriod kappa)
  anomaly_bridge : ∀ C : ℝ → ℝ → ℝ,
    LedgerClosurePricing anomalyReading C ↔
      SeamTransferCore.ConservingSeamPricing C
  nonvacuous : LedgerClosurePricing anomalyReading TurnRatioCarrier.turnRatioCost

/-- The certificate holds. -/
theorem seamLedgerDischargeCert : SeamLedgerDischargeCert where
  trace_forced := fun _ _ hcons hx h => conserving_trace_bound hcons hx h
  b2_any_reading := fun R C h kappa T hk hT =>
    b2_unique_zero_of_ledgerClosure R C h kappa T hk hT
  anomaly_bridge := anomalyLedger_iff_conserving
  nonvacuous := ledgerClosurePricing_turnRatioCost

end SeamLedgerDischarge
end Holography
end IndisputableMonolith
