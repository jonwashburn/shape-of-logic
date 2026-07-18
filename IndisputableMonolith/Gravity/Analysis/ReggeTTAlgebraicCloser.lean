import IndisputableMonolith.Gravity.Analysis.ReggeTTContinuumLimit
import IndisputableMonolith.Gravity.Analysis.ReggeTTGateBBridge

/-!
# Regge TT algebraic closer: the C8 closed form `(1/2)·xᵀ·adj(E)·x` and the
# TT isotropy value `-(1/4)`

QG full-theory campaign, Paper C / Pillar 1, production stage C-DAG3 of the
panel-locked D-dag order (`ReggeTTBlochAssembly → ReggeTTContinuumLimit →
ReggeTTAlgebraicCloser → ReggeTTContinuumCloser`).  This is the SOLE
production importer of the committed algebraic certificate spike (through
the Gate B bridge chain); no other production stage may import it.

## What this module proves (all THEOREM)

* `continuumMoment_eq_half_adjugate` — **the C8 closed form as a kernel
  equation**: for every SYMMETRIC polarization matrix `E` and every real
  direction `x`, the continuum-limit bucket moment fold of the production
  chain (the exact limit object of P1.1a,
  `reggeTTMoment rawCosineSupport (rawPhaseQuadratic x)
  (rawBucketAmplitude E)`) equals `(1/2) · xᵀ · adj(E) · x`, with
  `Matrix.adjugate` the actual Mathlib adjugate.  Route: the kernel
  identification of the production-chain fold with the Gate B bridge fold
  (same geometry-derived tables), the proved bridge equality
  `rawMoment_eq_committedSpikeLHS`, the committed spike block collapses
  `tetBlock*_eq` (block DATA only; the spike's own TT certificate
  `tt_continuum_certificate` is never invoked), and one
  `linear_combination` certificate over the three symmetry generators.
* `adjugateQuadraticForm_tt` — the TT adjugate step: for symmetric,
  traceless, `x`-transverse `E`, `xᵀ·adj(E)·x = -(1/2)·|x|²·⟨E,E⟩`.
  This is the kernel form of the eigenvalue argument (on the TT variety
  `x` is a null eigenvector of `E`, so `adj(E)x = λ₁λ₂x` with
  `λ₁ + λ₂ = 0`), discharged as an explicit cofactor certificate over the
  seven TT generators via `linear_combination`.
* `reggeTTMoment_tt_value` — **P1.1b, the isotropy value**: for every
  nonzero integer mode `m` and every TT polarization
  (`IsTTPolarization`), the P1.1a limit moment at the normalized real
  direction equals exactly `reggeTTContinuumCoefficient = -(1/4)`.
* `canonicalFiniteH_div_momentumNormSq_tendsto_isotropy` — P1.1a + P1.1b
  composed: the normalized finite reduced symbol converges to `-(1/4)`
  for every nonzero mode and TT polarization.

## Disclosures (binding)

* SYMMETRY SCOPE.  The closed form `(1/2)·xᵀ·adj(E)·x` holds under the
  three matrix-symmetry hypotheses and NOT identically in all nine free
  entries: the free-entry difference is the exact rotational square
  `-(1/8)·(E₀₁x₂ − E₀₂x₁ − E₁₀x₂ + E₁₂x₀ + E₂₀x₁ − E₂₁x₀)²`, which
  vanishes on symmetric `E`.  This matches the C8 certificate's own
  statement ("identically for every symmetric E").
* ALIASING NON-REPAIR.  The finite assembly identity feeding P1.1a holds
  only at non-aliased side lengths (`∃ i, ¬ N ∣ 2·mᵢ`); at the finitely
  many aliased small `N` the finite reduced symbol is NOT identified with
  the bucket fold and no repair is attempted.  The production chain
  consumes the identity through the eventual-filter form, which is all
  the continuum limit needs.  Unrepaired and disclosed.
* ANSWER KEY.  The exact C8 contraction
  (`state/qg_full_theory/isotropy_contraction/isotropy_certificate.py`)
  is the convention anchor for both `linear_combination` certificates;
  the Lean proofs stand independently of it (the kernel re-verifies every
  identity from the committed block data and Mathlib's adjugate).

No `sorry`, no `admit`, no new axioms, no `native_decide`, no `: True` or
`Nonempty`-only headline in this file.  Everything here is finite algebra;
expected axiom footprint of every theorem is the standard trio
`[propext, Classical.choice, Quot.sound]`.  Receipts at end of file.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTAlgebraicCloser

open ReggeTTSymbolPreflight
open ReggeTTBlochInterfaceAudit

noncomputable section

/-! ## §1. Kernel identification of the production fold with the bridge fold

The production chain (`ReggeTTBlochAssembly` / `ReggeTTContinuumLimit`)
derives its bucket tables from the periodic geometry; the Gate B bridge
(`ReggeTTGateBBridge`) uses the literal core tables, grounded there against
the same geometry.  These lemmas identify the two folds object by object,
so the bridge equality can be consumed by the production limit.

PROVENANCE (critic-requested disclosure): the two table families are NOT
co-seeded from one transcription.  The assembly side is DERIVED
(`slotBaseBit`/`slotDispBit` through `cubeVertexBit ∘ cubeEdgeBase ∘
localEdgeOf` on the actual Freudenthal cube triangulation); the core side
is a literal table that the bridge independently GROUNDS against the same
geometric objects (`edgeMidpointPhase_grounded`, `coreWeight_eq_raw`,
`corePolEdgeCoeff_eq`, `slotDispCore_eq`).  The 216-case kernel equality
below is therefore a genuine cross-check of derivation against grounded
transcription, not a comparison of one source with itself. -/

/-- The geometry-derived doubled-midpoint table of the production assembly
equals the literal core table of the Gate B bridge, entry by entry. -/
theorem slotMidTwice_eq_core (t f : Fin 6) (i : Fin 3) :
    ReggeTTBlochAssembly.slotMidTwice t f i =
      ReggeTTGateBBridgeCore.slotMidTwice t f i := by
  fin_cases t <;> fin_cases f <;> fin_cases i <;> rfl

/-- The production bucket key map equals the bridge bucket key map. -/
theorem bucketKeyOf_eq :
    ReggeTTBlochAssembly.bucketKeyOf = ReggeTTGateBBridge.bucketKeyOf := by
  funext p
  unfold ReggeTTBlochAssembly.bucketKeyOf ReggeTTGateBBridge.bucketKeyOf
  congr 1
  funext i
  rw [slotMidTwice_eq_core, slotMidTwice_eq_core]

/-- The production cosine support is the bridge moment support. -/
theorem rawCosineSupport_eq_rawMomentSupport :
    ReggeTTBlochAssembly.rawCosineSupport =
      ReggeTTGateBBridge.rawMomentSupport := by
  unfold ReggeTTBlochAssembly.rawCosineSupport
    ReggeTTGateBBridge.rawMomentSupport
  rw [bucketKeyOf_eq]

/-- The signed raw triple weights coincide (both are
`-(J_fg/(2√a*_f))·c_{d(t,f)}·c_{d(t,g)}` over the same kernel objects). -/
theorem rawTripleWeight_eq :
    ReggeTTBlochAssembly.rawTripleWeight =
      ReggeTTGateBBridge.rawTripleWeight := rfl

/-- The bucket-fiber-aggregated amplitudes coincide. -/
theorem rawBucketAmplitude_eq (E : Fin 3 → Fin 3 → ℝ) :
    ReggeTTBlochAssembly.rawBucketAmplitude E =
      ReggeTTGateBBridge.rawBucketAmplitude E := by
  funext b
  unfold ReggeTTBlochAssembly.rawBucketAmplitude
    ReggeTTGateBBridge.rawBucketAmplitude
  rw [bucketKeyOf_eq, rawTripleWeight_eq]

/-- The midpoint phase quadratics coincide. -/
theorem rawPhaseQuadratic_eq (x : Fin 3 → ℝ) :
    ReggeTTContinuumLimit.rawPhaseQuadratic x =
      ReggeTTGateBBridge.rawPhaseQuadratic x := rfl

/-- The production continuum moment fold IS the Gate B bridge moment fold. -/
theorem continuumMoment_eq_bridgeMoment (E : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) :
    reggeTTMoment ReggeTTBlochAssembly.rawCosineSupport
        (ReggeTTContinuumLimit.rawPhaseQuadratic x)
        (ReggeTTBlochAssembly.rawBucketAmplitude E) =
      reggeTTMoment ReggeTTGateBBridge.rawMomentSupport
        (ReggeTTGateBBridge.rawPhaseQuadratic x)
        (ReggeTTGateBBridge.rawBucketAmplitude E) := by
  rw [rawCosineSupport_eq_rawMomentSupport, rawBucketAmplitude_eq,
    rawPhaseQuadratic_eq]

/-! ## §2. The adjugate quadratic form and its explicit entries -/

/-- The C8 closed-form object: `xᵀ · adj(E) · x` with `Matrix.adjugate`
the actual Mathlib adjugate of the polarization matrix. -/
def adjugateQuadraticForm (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    x i * Matrix.adjugate (Matrix.of E) i j * x j

private theorem adjugate00 (E : Fin 3 → Fin 3 → ℝ) :
    Matrix.adjugate (Matrix.of E) 0 0 = E 1 1 * E 2 2 - E 1 2 * E 2 1 := by
  rw [Matrix.adjugate_fin_three]; rfl

private theorem adjugate01 (E : Fin 3 → Fin 3 → ℝ) :
    Matrix.adjugate (Matrix.of E) 0 1 = -(E 0 1 * E 2 2) + E 0 2 * E 2 1 := by
  rw [Matrix.adjugate_fin_three]; rfl

private theorem adjugate02 (E : Fin 3 → Fin 3 → ℝ) :
    Matrix.adjugate (Matrix.of E) 0 2 = E 0 1 * E 1 2 - E 0 2 * E 1 1 := by
  rw [Matrix.adjugate_fin_three]; rfl

private theorem adjugate10 (E : Fin 3 → Fin 3 → ℝ) :
    Matrix.adjugate (Matrix.of E) 1 0 = -(E 1 0 * E 2 2) + E 1 2 * E 2 0 := by
  rw [Matrix.adjugate_fin_three]; rfl

private theorem adjugate11 (E : Fin 3 → Fin 3 → ℝ) :
    Matrix.adjugate (Matrix.of E) 1 1 = E 0 0 * E 2 2 - E 0 2 * E 2 0 := by
  rw [Matrix.adjugate_fin_three]; rfl

private theorem adjugate12 (E : Fin 3 → Fin 3 → ℝ) :
    Matrix.adjugate (Matrix.of E) 1 2 = -(E 0 0 * E 1 2) + E 0 2 * E 1 0 := by
  rw [Matrix.adjugate_fin_three]; rfl

private theorem adjugate20 (E : Fin 3 → Fin 3 → ℝ) :
    Matrix.adjugate (Matrix.of E) 2 0 = E 1 0 * E 2 1 - E 1 1 * E 2 0 := by
  rw [Matrix.adjugate_fin_three]; rfl

private theorem adjugate21 (E : Fin 3 → Fin 3 → ℝ) :
    Matrix.adjugate (Matrix.of E) 2 1 = -(E 0 0 * E 2 1) + E 0 1 * E 2 0 := by
  rw [Matrix.adjugate_fin_three]; rfl

private theorem adjugate22 (E : Fin 3 → Fin 3 → ℝ) :
    Matrix.adjugate (Matrix.of E) 2 2 = E 0 0 * E 1 1 - E 0 1 * E 1 0 := by
  rw [Matrix.adjugate_fin_three]; rfl

/-- Fully explicit scalar form of the adjugate quadratic form. -/
theorem adjugateQuadraticForm_explicit (E : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) :
    adjugateQuadraticForm E x =
      x 0 * (E 1 1 * E 2 2 - E 1 2 * E 2 1) * x 0 +
        x 0 * (-(E 0 1 * E 2 2) + E 0 2 * E 2 1) * x 1 +
        x 0 * (E 0 1 * E 1 2 - E 0 2 * E 1 1) * x 2 +
        (x 1 * (-(E 1 0 * E 2 2) + E 1 2 * E 2 0) * x 0 +
          x 1 * (E 0 0 * E 2 2 - E 0 2 * E 2 0) * x 1 +
          x 1 * (-(E 0 0 * E 1 2) + E 0 2 * E 1 0) * x 2) +
        (x 2 * (E 1 0 * E 2 1 - E 1 1 * E 2 0) * x 0 +
          x 2 * (-(E 0 0 * E 2 1) + E 0 1 * E 2 0) * x 1 +
          x 2 * (E 0 0 * E 1 1 - E 0 1 * E 1 0) * x 2) := by
  unfold adjugateQuadraticForm
  simp only [Fin.sum_univ_three]
  rw [adjugate00, adjugate01, adjugate02, adjugate10, adjugate11,
    adjugate12, adjugate20, adjugate21, adjugate22]

/-! ## §3. Step (i): the committed spike block sum is the closed form -/

/-- Definitional expansion of the committed spike LHS at a marshalled
matrix/direction pair (structure-projection reduction only). -/
theorem committedSpikeLHS_spikeInput_expand (E : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) :
    ReggeTTBlochConventionAudit.committedSpikeLHS
        (ReggeTTBlochConventionAudit.spikeInput E x) =
      ReggeTTContinuumCertificateSpike.tetBlock0 (E 0 0) (E 0 1) (E 0 2)
          (E 1 0) (E 1 1) (E 1 2) (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2)
          (Real.sqrt 2) (Real.sqrt 3) Real.pi +
        ReggeTTContinuumCertificateSpike.tetBlock1 (E 0 0) (E 0 1) (E 0 2)
          (E 1 0) (E 1 1) (E 1 2) (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2)
          (Real.sqrt 2) (Real.sqrt 3) Real.pi +
        ReggeTTContinuumCertificateSpike.tetBlock2 (E 0 0) (E 0 1) (E 0 2)
          (E 1 0) (E 1 1) (E 1 2) (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2)
          (Real.sqrt 2) (Real.sqrt 3) Real.pi +
        ReggeTTContinuumCertificateSpike.tetBlock3 (E 0 0) (E 0 1) (E 0 2)
          (E 1 0) (E 1 1) (E 1 2) (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2)
          (Real.sqrt 2) (Real.sqrt 3) Real.pi +
        ReggeTTContinuumCertificateSpike.tetBlock4 (E 0 0) (E 0 1) (E 0 2)
          (E 1 0) (E 1 1) (E 1 2) (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2)
          (Real.sqrt 2) (Real.sqrt 3) Real.pi +
        ReggeTTContinuumCertificateSpike.tetBlock5 (E 0 0) (E 0 1) (E 0 2)
          (E 1 0) (E 1 1) (E 1 2) (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2)
          (Real.sqrt 2) (Real.sqrt 3) Real.pi := rfl

set_option maxHeartbeats 3200000 in
/-- **STEP (i) OF THE C8 CLOSED FORM (THEOREM): the committed spike block
sum equals `(1/2)·xᵀ·adj(E)·x` for every symmetric `E` and every `x`.**
The three symmetry hypotheses are consumed through an explicit rotational
cofactor certificate (the free-entry difference is
`-(1/8)·(E₀₁x₂ − E₀₂x₁ − E₁₀x₂ + E₁₂x₀ + E₂₀x₁ − E₂₁x₀)²`, disclosed in
the module docstring).  Only the spike block DATA (`tetBlock*_eq`) is
used; the spike's own TT certificate is never invoked. -/
theorem committedSpikeLHS_eq_half_adjugate (E : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ)
    (hsym01 : E 0 1 = E 1 0) (hsym02 : E 0 2 = E 2 0)
    (hsym12 : E 1 2 = E 2 1) :
    ReggeTTBlochConventionAudit.committedSpikeLHS
        (ReggeTTBlochConventionAudit.spikeInput E x) =
      (1 / 2) * adjugateQuadraticForm E x := by
  rw [committedSpikeLHS_spikeInput_expand, adjugateQuadraticForm_explicit]
  rw [ReggeTTContinuumCertificateSpike.tetBlock0_eq,
    ReggeTTContinuumCertificateSpike.tetBlock1_eq,
    ReggeTTContinuumCertificateSpike.tetBlock2_eq,
    ReggeTTContinuumCertificateSpike.tetBlock3_eq,
    ReggeTTContinuumCertificateSpike.tetBlock4_eq,
    ReggeTTContinuumCertificateSpike.tetBlock5_eq]
  linear_combination
    (-(1 / 8) * (E 0 1 * x 2 - E 0 2 * x 1 - E 1 0 * x 2 + E 1 2 * x 0 +
        E 2 0 * x 1 - E 2 1 * x 0) * x 2) * hsym01 +
      ((1 / 8) * (E 0 1 * x 2 - E 0 2 * x 1 - E 1 0 * x 2 + E 1 2 * x 0 +
        E 2 0 * x 1 - E 2 1 * x 0) * x 1) * hsym02 +
      (-(1 / 8) * (E 0 1 * x 2 - E 0 2 * x 1 - E 1 0 * x 2 + E 1 2 * x 0 +
        E 2 0 * x 1 - E 2 1 * x 0) * x 0) * hsym12

/-- The Gate B bridge moment fold equals the closed form for symmetric
polarizations. -/
theorem bridgeMoment_eq_half_adjugate (E : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ)
    (hsym01 : E 0 1 = E 1 0) (hsym02 : E 0 2 = E 2 0)
    (hsym12 : E 1 2 = E 2 1) :
    reggeTTMoment ReggeTTGateBBridge.rawMomentSupport
        (ReggeTTGateBBridge.rawPhaseQuadratic x)
        (ReggeTTGateBBridge.rawBucketAmplitude E) =
      (1 / 2) * adjugateQuadraticForm E x := by
  rw [ReggeTTGateBBridge.rawMoment_eq_committedSpikeLHS,
    committedSpikeLHS_eq_half_adjugate E x hsym01 hsym02 hsym12]

/-- **THE C8 CLOSED FORM, PRODUCTION HEADLINE (THEOREM): the continuum
bucket moment fold of the P1.1a limit equals `(1/2)·xᵀ·adj(E)·x` for every
symmetric polarization matrix and every real direction.** -/
theorem continuumMoment_eq_half_adjugate (E : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ)
    (hsym01 : E 0 1 = E 1 0) (hsym02 : E 0 2 = E 2 0)
    (hsym12 : E 1 2 = E 2 1) :
    reggeTTMoment ReggeTTBlochAssembly.rawCosineSupport
        (ReggeTTContinuumLimit.rawPhaseQuadratic x)
        (ReggeTTBlochAssembly.rawBucketAmplitude E) =
      (1 / 2) * adjugateQuadraticForm E x := by
  rw [continuumMoment_eq_bridgeMoment]
  exact bridgeMoment_eq_half_adjugate E x hsym01 hsym02 hsym12

/-! ## §4. Step (ii): the adjugate step on the TT variety -/

set_option maxHeartbeats 1600000 in
/-- **STEP (ii) OF THE C8 CLOSED FORM (THEOREM): on the TT variety the
adjugate quadratic form collapses to `-(1/2)·|x|²·⟨E,E⟩`.**  Kernel form
of the eigenvalue argument (`x` is a null eigenvector of `E`, so
`adj(E)x = λ₁λ₂x` with `λ₁ + λ₂ = 0`), discharged as an explicit cofactor
certificate over the seven TT generators. -/
theorem adjugateQuadraticForm_tt (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (hsym01 : E 0 1 = E 1 0) (hsym02 : E 0 2 = E 2 0)
    (hsym12 : E 1 2 = E 2 1)
    (htr : E 0 0 + E 1 1 + E 2 2 = 0)
    (htrans0 : x 0 * E 0 0 + x 1 * E 1 0 + x 2 * E 2 0 = 0)
    (htrans1 : x 0 * E 0 1 + x 1 * E 1 1 + x 2 * E 2 1 = 0)
    (htrans2 : x 0 * E 0 2 + x 1 * E 1 2 + x 2 * E 2 2 = 0) :
    adjugateQuadraticForm E x =
      -(1 / 2) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) *
        (E 0 0 * E 0 0 + E 0 1 * E 0 1 + E 0 2 * E 0 2 + E 1 0 * E 1 0 +
          E 1 1 * E 1 1 + E 1 2 * E 1 2 + E 2 0 * E 2 0 + E 2 1 * E 2 1 +
          E 2 2 * E 2 2) := by
  rw [adjugateQuadraticForm_explicit]
  linear_combination
    (E 0 0 * x 0 * x 1 - E 0 1 * x 0 ^ 2 / 2 + E 0 1 * x 1 ^ 2 / 2 +
        E 0 1 * x 2 ^ 2 / 2 - E 1 0 * x 0 ^ 2 / 2 - E 1 0 * x 1 ^ 2 / 2 -
        E 1 0 * x 2 ^ 2 / 2 - E 2 1 * x 0 * x 2 + E 2 2 * x 0 * x 1) *
      hsym01 +
    (E 0 0 * x 0 * x 2 - E 0 2 * x 0 ^ 2 / 2 + E 0 2 * x 1 ^ 2 / 2 +
        E 0 2 * x 2 ^ 2 / 2 + E 1 1 * x 0 * x 2 - E 1 2 * x 0 * x 1 -
        E 2 0 * x 0 ^ 2 / 2 - E 2 0 * x 1 ^ 2 / 2 - E 2 0 * x 2 ^ 2 / 2) *
      hsym02 +
    (E 0 0 * x 1 * x 2 - E 0 2 * x 0 * x 1 + E 1 1 * x 1 * x 2 +
        E 1 2 * x 0 ^ 2 / 2 - E 1 2 * x 1 ^ 2 / 2 + E 1 2 * x 2 ^ 2 / 2 -
        E 2 1 * x 0 ^ 2 / 2 - E 2 1 * x 1 ^ 2 / 2 - E 2 1 * x 2 ^ 2 / 2) *
      hsym12 +
    (-(E 0 0 * x 0 ^ 2) / 2 + E 0 0 * x 1 ^ 2 / 2 + E 0 0 * x 2 ^ 2 / 2 -
        2 * E 0 1 * x 0 * x 1 - E 0 2 * x 0 * x 2 + E 1 1 * x 0 ^ 2 / 2 -
        E 1 1 * x 1 ^ 2 / 2 + E 1 1 * x 2 ^ 2 / 2 - E 1 2 * x 1 * x 2 +
        E 2 2 * x 0 ^ 2 / 2 + E 2 2 * x 1 ^ 2 / 2 + E 2 2 * x 2 ^ 2 / 2) *
      htr +
    (E 0 0 * x 0 + E 0 1 * x 1 + E 0 2 * x 2) * htrans0 +
    (E 0 1 * x 0 + E 1 1 * x 1 + E 1 2 * x 2) * htrans1 +
    (-(E 0 0 * x 2) + E 0 2 * x 0 - E 1 1 * x 2 + E 1 2 * x 1) * htrans2

/-! ## §5. P1.1b: the isotropy value `-(1/4)` -/

/-- The moment value at unit-normalized real TT data: the fold equals
exactly `reggeTTContinuumCoefficient = -(1/4)`. -/
theorem reggeTTMoment_tt_real (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (hsym01 : E 0 1 = E 1 0) (hsym02 : E 0 2 = E 2 0)
    (hsym12 : E 1 2 = E 2 1)
    (htr : E 0 0 + E 1 1 + E 2 2 = 0)
    (htrans0 : x 0 * E 0 0 + x 1 * E 1 0 + x 2 * E 2 0 = 0)
    (htrans1 : x 0 * E 0 1 + x 1 * E 1 1 + x 2 * E 2 1 = 0)
    (htrans2 : x 0 * E 0 2 + x 1 * E 1 2 + x 2 * E 2 2 = 0)
    (hxnorm : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1)
    (hEnorm : (∑ i : Fin 3, ∑ j : Fin 3, E i j * E i j) = 1) :
    reggeTTMoment ReggeTTBlochAssembly.rawCosineSupport
        (ReggeTTContinuumLimit.rawPhaseQuadratic x)
        (ReggeTTBlochAssembly.rawBucketAmplitude E) =
      reggeTTContinuumCoefficient := by
  have hEnorm' := hEnorm
  simp only [Fin.sum_univ_three] at hEnorm'
  have hcoeff : reggeTTContinuumCoefficient = -(1 / 4 : ℝ) := rfl
  rw [continuumMoment_eq_half_adjugate E x hsym01 hsym02 hsym12,
    adjugateQuadraticForm_tt E x hsym01 hsym02 hsym12 htr htrans0 htrans1
      htrans2, hcoeff]
  linear_combination
    (-(1 / 4 : ℝ) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)) * hEnorm' +
      (-(1 / 4 : ℝ)) * hxnorm

/-- **P1.1b HEADLINE (THEOREM): for every nonzero integer mode and every
TT polarization, the P1.1a continuum moment at the normalized real
direction equals exactly `reggeTTContinuumCoefficient = -(1/4)`.** -/
theorem reggeTTMoment_tt_value (m : Fin 3 → ℤ) (E : Fin 3 → Fin 3 → ℝ)
    (hm : ∃ i : Fin 3, m i ≠ 0) (hTT : IsTTPolarization m E) :
    reggeTTMoment ReggeTTBlochAssembly.rawCosineSupport
        (ReggeTTContinuumLimit.rawPhaseQuadratic
          (ReggeTTContinuumLimit.normalizedRealMode m))
        (ReggeTTBlochAssembly.rawBucketAmplitude E) =
      reggeTTContinuumCoefficient := by
  obtain ⟨hsymm, htrace, htrans, hnorm⟩ := hTT
  have hs : 0 < ReggeTTContinuumLimit.realModeNormSq (fun i => (m i : ℝ)) :=
    ReggeTTContinuumLimit.realModeNormSq_intCast_pos m hm
  have hxval : ∀ i : Fin 3,
      ReggeTTContinuumLimit.normalizedRealMode m i =
        (m i : ℝ) /
          Real.sqrt (ReggeTTContinuumLimit.realModeNormSq
            (fun j => (m j : ℝ))) := fun i => rfl
  have htr : E 0 0 + E 1 1 + E 2 2 = 0 := by
    have h := htrace
    rwa [Fin.sum_univ_three] at h
  have hxtrans : ∀ j : Fin 3,
      ReggeTTContinuumLimit.normalizedRealMode m 0 * E 0 j +
          ReggeTTContinuumLimit.normalizedRealMode m 1 * E 1 j +
          ReggeTTContinuumLimit.normalizedRealMode m 2 * E 2 j = 0 := by
    intro j
    have h := htrans j
    rw [Fin.sum_univ_three] at h
    rw [hxval 0, hxval 1, hxval 2, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_mul_eq_mul_div, div_add_div_same, div_add_div_same, h, zero_div]
  have hxnorm :
      ReggeTTContinuumLimit.normalizedRealMode m 0 ^ 2 +
          ReggeTTContinuumLimit.normalizedRealMode m 1 ^ 2 +
          ReggeTTContinuumLimit.normalizedRealMode m 2 ^ 2 = 1 := by
    have hsum : (m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2 + (m 2 : ℝ) ^ 2 =
        ReggeTTContinuumLimit.realModeNormSq (fun j => (m j : ℝ)) := by
      simp only [ReggeTTContinuumLimit.realModeNormSq, Fin.sum_univ_three]
    rw [hxval 0, hxval 1, hxval 2, div_pow, div_pow, div_pow,
      div_add_div_same, div_add_div_same, Real.sq_sqrt hs.le, hsum,
      div_self hs.ne']
  exact reggeTTMoment_tt_real E (ReggeTTContinuumLimit.normalizedRealMode m)
    (hsymm 0 1) (hsymm 0 2) (hsymm 1 2) htr (hxtrans 0) (hxtrans 1)
    (hxtrans 2) hxnorm hnorm

/-- **P1.1a + P1.1b COMPOSED (THEOREM): the normalized finite reduced
Regge TT symbol converges to exactly `-(1/4)` for every nonzero integer
mode and every TT polarization.** -/
theorem canonicalFiniteH_div_momentumNormSq_tendsto_isotropy
    (m : Fin 3 → ℤ) (E : Fin 3 → Fin 3 → ℝ)
    (hm : ∃ i : Fin 3, m i ≠ 0) (hTT : IsTTPolarization m E) :
    Filter.Tendsto
      (fun j : ℕ =>
        @canonicalFiniteH (j + 3) (instNeZeroAddThree j) E m /
          momentumNormSq (j + 3) m)
      Filter.atTop (nhds reggeTTContinuumCoefficient) := by
  have h :=
    ReggeTTContinuumLimit.canonicalFiniteH_div_momentumNormSq_tendsto E m hm
  rwa [reggeTTMoment_tt_value m E hm hTT] at h

end

end ReggeTTAlgebraicCloser
end Analysis
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTAlgebraicCloser.continuumMoment_eq_bridgeMoment
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTAlgebraicCloser.committedSpikeLHS_eq_half_adjugate
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTAlgebraicCloser.continuumMoment_eq_half_adjugate
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTAlgebraicCloser.adjugateQuadraticForm_tt
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTAlgebraicCloser.reggeTTMoment_tt_value
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTAlgebraicCloser.canonicalFiniteH_div_momentumNormSq_tendsto_isotropy
