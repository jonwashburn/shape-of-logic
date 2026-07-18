import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Gravity.RecognitionLedger
import IndisputableMonolith.Numerics.Interval.Log

/-!
# Seven Gaps, Pillar 3 fallback: φ-horizon absorption comb PREFLIGHT

## Status: FALSIFIER-GATED PREFLIGHT of a MODEL mechanism. Pillar 3 stays OPEN.

NOTHING in this module is a prediction. The candidate mechanism (horizon area
quantization with gap ΔA = 4·ln(φ)·ℓ_P², converting via black-hole
thermodynamics into a repeated absorption comb at GMω* = ln(φ)/(8π) ≈ 0.019147
for Schwarzschild) is a MODEL whose load-bearing hypotheses are NOT derived
from RS capital. This module measures exactly how much of the mechanism the
existing capital forces. Answer: the kinematic algebra and one asymptotic
entropy-gap theorem are real; the quantization itself is NOT forced, and the
P1 scaling falsifier FAILS the mechanism at the current formalization level
(see `scaling_family_blocks_ledger_gap`, `ledger_boundary_cost_no_uniform_gap`).

THE DEAD 0.618 ECHO IS NOT BEING REVIVED. `Gravity.BlackHoleEchoesSI` records
the φ-rung ECHO-TRAIN route (damping ratio 1/φ ≈ 0.618); that discriminator
was killed against O3/O4 bounds and stays dead. The present preflight concerns
an ABSORPTION/LEVEL-STRUCTURE claim (a comb of transition frequencies from a
quantized area spectrum), a categorically different observable from an
echo-train time series. Every docstring below keeps that distinction.

## Capital map (what exists, file:line, verified 2026-07-15)

* `IndisputableMonolith/Relativity/Compact/BlackHoleEntropy.lean`
  (SEALED subtree; the ci_guard sealed-import rule forbids importing it here,
  so the area function is definitionally MIRRORED below):
  - :19 `HorizonArea (Rs : ℝ) : ℝ := 4·π·Rs²` — area is a CONTINUOUS REAL of a
    continuous real radius. No discretization anywhere.
  - :32 `LedgerCapacityLimit (A ell0 : ℝ) : ℝ := A / ell0²` — a capacity BOUND
    as a real number, not a state count; scale-covariant, imposes no spectrum.
  - :41 `bh_entropy_from_ledger` — definitional identity S = N/4; :54
    `max_recognition_flux` — existential shell. Neither quantizes area.
* `IndisputableMonolith/Relativity/Compact/BlackHoleDerivation.lean` — the
  BH-001..006 sections are `True := trivial` placeholders; NOT capital.
* `IndisputableMonolith/Gravity/RecognitionLedger.lean` (ACTIVE, imported):
  - :74 `RecognitionLedger` — REAL-valued cost function on a finite lattice
    with symmetry, diagonal-zero, nonnegativity, RCL subadditivity.
  - :175 `SubstrateBipartition` — the horizon analogue (interior/exterior).
  - :184 `boundaryCost` — real-valued horizon cost. No quantization.
* `IndisputableMonolith/Gravity/BlackHoleEchoesSI.lean` — the DEAD echo route
  (rung radius φ^N, delay 2·t_P·φ^N·ln φ, damping 1/φ). Killed as an
  observable; quarantined; understood; not touched here.
* `IndisputableMonolith/Holography/BekensteinReduction.lean` — the closest
  prior area-quantization capital. Its single named postulate
  `SectorAreaQuantization` (:169) is REFUTED (2026-07-01, lossy-quotient
  construction). Its live edge-based successors (κ = 4 vs κ = 3, OPEN) would
  give an area quantum κ·H·ℓ_P² with H = (φ+2)·ln φ, i.e.
  ΔA = κ·(φ+2)·ln(φ)·ℓ_P² — NOT the comb's 4·ln(φ)·ℓ_P²; the ratio is exactly
  (κ/4)·(φ+2) ≈ 3.62 at κ = 4. So even the nearest OPEN quantization line does
  not produce this mechanism's gap. (Scratch receipt:
  `state/qg_full_theory/horizon_comb_preflight/comb_values.txt`.)
* Foundation 8-tick / voxel capital (`Patterns`, T7): TEMPORAL discreteness
  (period 2³ = 8). No module discretizes HORIZON AREA in φ-tied units.

KEY ANSWER to the preflight's central question: horizon area is a continuous
real everywhere in the capital, with a capacity bound only. Nothing
discretizes it.

## Panel-locked gate verdicts

* **P1 (λ-scaling-modulus falsifier): the scaling family EXISTS; the area gap
  is NOT forced at the current formalization level; the mechanism FAILS P1 at
  that level.** Kernel-checked in two independent forms. Continuum form:
  admissibility in the capital is exactly `0 < Rs`; scaling `Rs ↦ λ·Rs`
  preserves it and scales area by λ² (`horizonAreaMirror_scaling`), the area
  map achieves EVERY positive real (`horizonArea_achieves_every_positive`),
  hence no positive gap separates achievable areas
  (`scaling_family_blocks_ledger_gap`). Ledger form: for every λ ≥ 1 the
  scaled ledger λ·ℒ satisfies ALL FOUR RecognitionLedger axioms including RCL
  subadditivity (`scaleLedger`), boundary cost scales linearly
  (`scaleLedger_boundaryCost`), hence the achievable horizon boundary-cost
  spectrum has no uniform gap either
  (`ledger_boundary_cost_no_uniform_gap`).
* **P2 (canonical horizon patch class + Fibonacci counts): NO discrete horizon
  state class exists in the capital.** The named missing ingredient is
  recorded as the Prop-level target `HorizonPatchClassTarget` with the exact
  Fibonacci recurrence as a field. `fibPatchWitness` shows the target is
  SATISFIABLE (by `Nat.fib` by fiat) — it is a consistency witness, NOT a
  derivation; no physics is invented. OPEN, flag false.
* **P3 (area-gap theorem shape): the asymptotic entropy-gap fragment is a REAL
  THEOREM landed here** (`fib_ratio_tendsto_phi`,
  `log_fib_gap_tendsto_log_phi`: ln F_{n+1} − ln F_n → ln φ, kernel-checked
  against `Constants.phi` via Mathlib's `tendsto_fib_succ_div_fib_atTop`).
  The IF-THEN chain (IF a discrete patch class exists AND its counts are
  Fibonacci AND S = ln(count) AND S = A/(4ℓ_P²), THEN the entropy gap tends to
  ln φ and the area gap tends to 4·ln(φ)·ℓ_P²) is kernel-checked with the IFs
  as named structure fields (`HorizonCombModel`, honestly MODEL). The EXACT
  per-level gap (`AreaGapTarget`) and the derivation of the IFs from RS
  capital remain OPEN, flag false.
* **P4 (nonzero adjacent-sector transition): named target only**
  (`AdjacentSectorTransitionNonzero`). There is NO capital for a horizon
  transition operator; none is pretended. OPEN, flag false.

## Comb observable (MODEL-tier consequences, recorded with kernel bounds)

* `combFrequencyGM = ln(φ)/(8π)` exactly; numerically 0.01914681…
  (scratch receipt above); kernel interval (0.0191, 0.0193) proved in
  `combFrequencyGM_bounds` from `Numerics.log_phi_gt_0481/lt_0483` and
  `Real.pi_gt_d6/pi_lt_d6`.
* Kerr locked shape: ω − mΩ_H = κ·ln(φ)/(2π) (`kerrCombOffset`), related to
  the Schwarzschild value by `kerrCombOffset_eq` (= 4κ·combFrequencyGM), and
  derived from the MODEL area gap by `model_area_gap_gives_kerr_comb` and
  `schwarzschild_comb_frequency` (GM·ω* = ln(φ)/(8π)).

## Honest fraction forced

Existing capital forces: the kinematic φ-algebra, the asymptotic Fibonacci
entropy-gap limit, and the exact-value/interval lemmas — and it POSITIVELY
REFUTES the quantization at the current formalization level (P1). The
load-bearing physical content (discrete horizon states, Fibonacci counting,
entropy = log-count at the horizon, the first-law conversion) is 0% forced.
`mechanism_forced := false`.

Zero `sorry`, zero `admit`, zero new axioms. No vacuous `True` shells: every
theorem below has real mathematical content or is an `rfl`-forced status
record explicitly labeled as documentation.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace HorizonLedgerPreflight

open Constants

noncomputable section

/-! ## §P1a. Continuum form: the λ-scaling modulus on the horizon-area capital

The sealed `Relativity.Compact.BlackHoleEntropy.HorizonArea` (BlackHoleEntropy
.lean:19) is `4·π·Rs²` on a continuous real radius with sole admissibility
condition `0 < Rs`. We mirror it definitionally (the sealed-import guard in
`scripts/ci_guard.sh` forbids importing the Relativity subtree here) and prove
the scaling family survives, so no area gap is forced. -/

/-- Definitional MIRROR of the sealed capital's horizon area
(`Relativity/Compact/BlackHoleEntropy.lean:19`): `A(Rs) = 4·π·Rs²`.
Same formula, restated here because the Relativity subtree is sealed.

CAVEAT (critic 2026-07-15): the identity between this mirror and the
sealed definition is INSPECTION-VERIFIED only, not kernel-checked (the
sealed-import guard forbids stating the equality in Lean). Any edit to
the sealed `HorizonArea` formula silently invalidates the P1 no-go
below; keep the two textually in sync. -/
def schwarzschildHorizonAreaMirror (Rs : ℝ) : ℝ := 4 * Real.pi * Rs ^ 2

/-- **P1 (scaling family exists, area law).** The capital's horizon area is
exactly quadratically covariant under the radial scaling `Rs ↦ λ·Rs`:
`A(λ·Rs) = λ²·A(Rs)`. This is the continuous scaling modulus the falsifier
asks about. -/
theorem horizonAreaMirror_scaling (lam Rs : ℝ) :
    schwarzschildHorizonAreaMirror (lam * Rs)
      = lam ^ 2 * schwarzschildHorizonAreaMirror Rs := by
  simp only [schwarzschildHorizonAreaMirror]
  ring

/-- **P1 (scaling family exists, admissibility).** The capital's ONLY
admissibility condition on a Schwarzschild horizon configuration is `0 < Rs`
(every theorem in `BlackHoleEntropy.lean` quantifies over exactly this), and
it is preserved by every positive scaling. So the family
`Rs ↦ λ·Rs (λ > 0)` stays inside the admissible class. -/
theorem horizonAreaMirror_scaling_admissible (lam Rs : ℝ)
    (hlam : 0 < lam) (hRs : 0 < Rs) : 0 < lam * Rs :=
  mul_pos hlam hRs

/-- The capital's capacity bound (`LedgerCapacityLimit A ell0 = A/ell0²`,
BlackHoleEntropy.lean:32) is itself scale-covariant: capacity of a λ²-scaled
area is λ² times the capacity. A real-valued bound cannot quantize the
spectrum. -/
theorem ledgerCapacityMirror_scaling (lam A ell0 : ℝ) :
    (lam ^ 2 * A) / ell0 ^ 2 = lam ^ 2 * (A / ell0 ^ 2) := by
  ring

/-- Every positive real is an achieved horizon area of an admissible
configuration: take `Rs = √(A/(4π))`. The achievable area spectrum is the
full ray `(0, ∞)`. -/
theorem horizonArea_achieves_every_positive (A : ℝ) (hA : 0 < A) :
    ∃ Rs : ℝ, 0 < Rs ∧ schwarzschildHorizonAreaMirror Rs = A := by
  have h4pi : (0 : ℝ) < 4 * Real.pi := by positivity
  refine ⟨Real.sqrt (A / (4 * Real.pi)),
    Real.sqrt_pos.mpr (div_pos hA h4pi), ?_⟩
  simp only [schwarzschildHorizonAreaMirror]
  rw [Real.sq_sqrt (le_of_lt (div_pos hA h4pi))]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **P1 VERDICT (continuum form): the scaling family blocks the ledger area
gap.** For every claimed gap `g > 0` and every achieved area `A > 0` there is
an ADMISSIBLE configuration whose area differs from `A` but by less than `g`.
Hence the existing capital forces NO quantized area spectrum — in particular
not `ΔA = 4·ln(φ)·ℓ_P²` — and the comb mechanism FAILS gate P1 at the current
formalization level. This is the kernel-checked no-go the preflight was gated
on. -/
theorem scaling_family_blocks_ledger_gap (g A : ℝ) (hg : 0 < g) (hA : 0 < A) :
    ∃ Rs : ℝ, 0 < Rs ∧
      schwarzschildHorizonAreaMirror Rs ≠ A ∧
      |schwarzschildHorizonAreaMirror Rs - A| < g := by
  obtain ⟨Rs, hRs, hArea⟩ :=
    horizonArea_achieves_every_positive (A + g / 2) (by linarith)
  refine ⟨Rs, hRs, ?_, ?_⟩
  · rw [hArea]
    intro h
    linarith
  · rw [hArea, show A + g / 2 - A = g / 2 from by ring,
      abs_of_pos (half_pos hg)]
    linarith

/-! ## §P1b. Ledger form: the λ-scaling modulus on the RecognitionLedger capital

The active horizon capital is `Gravity.RecognitionLedger`: real-valued costs,
a bipartition as the horizon, `boundaryCost` as the horizon ledger content.
We exhibit the scaling family ON THE ACTUAL STRUCTURE: for every λ ≥ 1 the
pointwise-scaled ledger satisfies all four ledger axioms (RCL subadditivity
survives because `λ·R(u,v) ≤ R(λu, λv)` for λ ≥ 1), and the boundary cost
scales linearly. So the discrete-lattice layer does not quantize horizon cost
either. -/

/-- The λ-scaled recognition ledger (λ ≥ 1): every cost multiplied by `lam`.
All four `RecognitionLedger` axioms are re-proved for the scaled object; RCL
subadditivity uses `lam·(2uv+2u+2v) ≤ 2(lam·u)(lam·v)+2(lam·u)+2(lam·v)`,
which holds because `lam² ≥ lam` for `lam ≥ 1` and costs are nonnegative. -/
def scaleLedger {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger.RecognitionLedger Λ) (lam : ℝ) (hlam : 1 ≤ lam) :
    RecognitionLedger.RecognitionLedger Λ where
  cost i j := lam * L.cost i j
  symmetric i j := by rw [L.symmetric i j]
  diagonal_zero i := by rw [L.diagonal_zero i, mul_zero]
  nonneg i j := mul_nonneg (le_trans zero_le_one hlam) (L.nonneg i j)
  rcl_subadditive i j k := by
    have h := L.rcl_subadditive i j k
    have hu := L.nonneg i j
    have hv := L.nonneg j k
    have hlam0 : (0 : ℝ) ≤ lam := le_trans zero_le_one hlam
    simp only [RecognitionLedger.rclGate] at h ⊢
    nlinarith [mul_le_mul_of_nonneg_left h hlam0,
      mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hlam) hlam0) hu) hv,
      mul_nonneg hu hv]

/-- Boundary (horizon) cost of the scaled ledger is exactly `lam` times the
original: the scaling family acts CONTINUOUSLY on the horizon ledger content
while preserving every ledger axiom. -/
theorem scaleLedger_boundaryCost {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger.RecognitionLedger Λ) (lam : ℝ) (hlam : 1 ≤ lam)
    (P : RecognitionLedger.SubstrateBipartition Λ) :
    RecognitionLedger.boundaryCost (scaleLedger L lam hlam) P
      = lam * RecognitionLedger.boundaryCost L P := by
  simp only [RecognitionLedger.boundaryCost, scaleLedger, Finset.mul_sum]

/-- **P1 VERDICT (ledger form): no uniform gap in the horizon boundary-cost
spectrum.** For every claimed gap `g > 0`, every recognition ledger with
positive horizon boundary cost admits an axiom-preserving scaling whose
boundary cost is distinct but within `g`. The discrete-lattice capital does
not quantize horizon cost. -/
theorem ledger_boundary_cost_no_uniform_gap
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger.RecognitionLedger Λ)
    (P : RecognitionLedger.SubstrateBipartition Λ)
    (hB : 0 < RecognitionLedger.boundaryCost L P)
    (g : ℝ) (hg : 0 < g) :
    ∃ (lam : ℝ) (hlam : 1 ≤ lam),
      RecognitionLedger.boundaryCost (scaleLedger L lam hlam) P
        ≠ RecognitionLedger.boundaryCost L P ∧
      |RecognitionLedger.boundaryCost (scaleLedger L lam hlam) P
        - RecognitionLedger.boundaryCost L P| < g := by
  set B := RecognitionLedger.boundaryCost L P with hBdef
  have hBne : B ≠ 0 := ne_of_gt hB
  have hlam : 1 ≤ 1 + g / (2 * B) := by
    have hpos : 0 < g / (2 * B) := div_pos hg (by linarith)
    linarith
  have hexp : (1 + g / (2 * B)) * B = B + g / 2 := by
    field_simp
  refine ⟨1 + g / (2 * B), hlam, ?_, ?_⟩
  · rw [scaleLedger_boundaryCost, ← hBdef, hexp]
    intro h
    linarith
  · rw [scaleLedger_boundaryCost, ← hBdef, hexp,
      show B + g / 2 - B = g / 2 from by ring, abs_of_pos (half_pos hg)]
    linarith

/-! ## §P2. The named missing ingredient: a discrete horizon patch class

The capital offers NO discrete horizon state structure: `RecognitionLedger`
costs are reals, `SubstrateBipartition` carries no per-patch state type, the
sealed `LedgerCapacityLimit` is a real bound, and the pixel-area line's only
quantization postulate is refuted (`Holography.BekensteinReduction`,
docstring). Per the preflight rules we therefore DO NOT invent physics; we
record the target as a Prop-level definition with the exact Fibonacci
recurrence as a named field, and leave existence-from-capital OPEN
(flag false in `horizonCombPreflightStatus`). -/

/-- **P2 TARGET (OPEN; no RS capital constructs this).** A canonical horizon
patch class: a level-indexed microstate count that is positive and satisfies
the EXACT Fibonacci recurrence `count(n+2) = count(n+1) + count(n)`. What a
real derivation would require: a horizon patch state type forced by the
ledger/voxel capital, an automorphism quotient, and a counting theorem — none
of which exist yet. -/
structure HorizonPatchClassTarget where
  /-- Microstate count at area level `n` (mod horizon automorphisms). -/
  microstates : ℕ → ℕ
  /-- Every level has at least one state. -/
  microstates_pos : ∀ n, 0 < microstates n
  /-- The exact Fibonacci recurrence the φ-comb mechanism needs. -/
  fibonacci_recurrence :
    ∀ n, microstates (n + 2) = microstates (n + 1) + microstates n

/-- CONSISTENCY WITNESS ONLY (NOT a derivation): `Nat.fib (· + 1)` satisfies
the target, so `HorizonPatchClassTarget` is a satisfiable specification, not
a vacuous one. The witness inserts Fibonacci BY FIAT; nothing in RS capital
selects it. The OPEN problem is existence FROM CAPITAL, which this witness
does not touch. -/
def fibPatchWitness : HorizonPatchClassTarget where
  microstates n := Nat.fib (n + 1)
  microstates_pos n := Nat.fib_pos.mpr (Nat.succ_pos n)
  fibonacci_recurrence n := by
    show Nat.fib (n + 1 + 2) = Nat.fib (n + 1 + 1) + Nat.fib (n + 1)
    rw [Nat.fib_add_two]
    exact Nat.add_comm _ _

/-! ## §P3a. The REAL theorem fragment: Fibonacci log-gap tends to ln φ

Kernel-checked against `Constants.phi` (definitionally `Real.goldenRatio`),
via Mathlib's `tendsto_fib_succ_div_fib_atTop`. Entropy interpretation: IF a
horizon microstate count is Fibonacci and entropy is the log-count, the
per-level entropy gap converges to ln φ. The interpretation is MODEL; the
limit itself is THEOREM. This fragment stands regardless of the comb's fate. -/

/-- **THEOREM.** `F(n+1)/F(n) → φ` with `φ = Constants.phi` (definitionally
`Real.goldenRatio`). Re-export of Mathlib's `tendsto_fib_succ_div_fib_atTop`
against the RS constant. -/
theorem fib_ratio_tendsto_phi :
    Filter.Tendsto (fun n => (Nat.fib (n + 1) : ℝ) / (Nat.fib n : ℝ))
      Filter.atTop (nhds Constants.phi) :=
  tendsto_fib_succ_div_fib_atTop

/-- **THEOREM (the entropy-gap fragment).** `ln F(n+1) − ln F(n) → ln φ`.
With `S(n) = ln(count(n))` and Fibonacci counts, the per-level entropy gap
converges to `ln φ`; with `S = A/(4ℓ_P²)` (MODEL) the area gap converges to
`4·ln(φ)·ℓ_P²`. The limit here is unconditional. -/
theorem log_fib_gap_tendsto_log_phi :
    Filter.Tendsto
      (fun n => Real.log (Nat.fib (n + 1) : ℝ) - Real.log (Nat.fib n : ℝ))
      Filter.atTop (nhds (Real.log Constants.phi)) := by
  have hratio : Filter.Tendsto
      (fun n => Real.log ((Nat.fib (n + 1) : ℝ) / (Nat.fib n : ℝ)))
      Filter.atTop (nhds (Real.log Constants.phi)) :=
    ((Real.continuousAt_log (ne_of_gt Constants.phi_pos)).tendsto).comp
      fib_ratio_tendsto_phi
  refine Filter.Tendsto.congr' ?_ hratio
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnum : ((Nat.fib (n + 1) : ℝ)) ≠ 0 := by
    have h : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (Nat.succ_pos n)
    exact_mod_cast ne_of_gt h
  have hden : ((Nat.fib n : ℝ)) ≠ 0 := by
    have h : 0 < Nat.fib n := Nat.fib_pos.mpr hn
    exact_mod_cast ne_of_gt h
  exact Real.log_div hnum hden

/-! ## §P3b. The MODEL chain, with the IFs as named hypothesis fields

`HorizonCombModel` bundles the UNPROVED hypotheses the mechanism needs. Every
field is an IF; the theorems below are the kernel-checked THENs. Tier: MODEL.
None of the fields is derived from RS capital (that is precisely what P1/P2
report as missing). -/

/-- **MODEL (hypothesis bundle, NOT derived).** The IF-side of the comb chain:
* IF a discrete horizon patch class exists (`patchClass` — P2, OPEN),
* IF its counts are Fibonacci (`counts_are_fib` — inserted, not forced),
* IF the Planck area `lP2` is positive (`lP2_pos` — bookkeeping),
with horizon entropy READ as log-count (`entropy` below) and area READ as
`4·lP2·S` i.e. `S = A/(4ℓ_P²)` (`area` below; the sealed capital's
`bh_entropy_from_ledger` is definitional, so this reading is also MODEL). -/
structure HorizonCombModel where
  /-- IF: a discrete horizon patch class exists (P2 target). -/
  patchClass : HorizonPatchClassTarget
  /-- IF: its microstate counts are exactly Fibonacci. -/
  counts_are_fib : ∀ n, patchClass.microstates n = Nat.fib (n + 1)
  /-- Planck area (positive bookkeeping constant, units ℓ_P²). -/
  lP2 : ℝ
  /-- IF: positivity of the area unit. -/
  lP2_pos : 0 < lP2

namespace HorizonCombModel

/-- MODEL reading: horizon entropy at level `n` is the log of the microstate
count (Boltzmann reading of the patch class; NOT derived from capital). -/
def entropy (M : HorizonCombModel) (n : ℕ) : ℝ :=
  Real.log (M.patchClass.microstates n : ℝ)

/-- MODEL reading: horizon area at level `n` via `S = A/(4ℓ_P²)`, i.e.
`A = 4·ℓ_P²·S` (Bekenstein-Hawking reading; the sealed capital states it only
definitionally). -/
def area (M : HorizonCombModel) (n : ℕ) : ℝ :=
  4 * M.lP2 * M.entropy n

/-- **THEN (kernel-checked).** Under the model hypotheses the per-level
entropy gap converges to `ln φ`. -/
theorem entropy_gap_tendsto (M : HorizonCombModel) :
    Filter.Tendsto (fun n => M.entropy (n + 1) - M.entropy n)
      Filter.atTop (nhds (Real.log Constants.phi)) := by
  have hshift : Filter.Tendsto
      (fun n =>
        Real.log (Nat.fib (n + 1 + 1) : ℝ) - Real.log (Nat.fib (n + 1) : ℝ))
      Filter.atTop (nhds (Real.log Constants.phi)) :=
    log_fib_gap_tendsto_log_phi.comp (Filter.tendsto_add_atTop_nat 1)
  refine hshift.congr fun n => ?_
  simp only [entropy, M.counts_are_fib]

/-- **THEN (kernel-checked).** Under the model hypotheses the per-level AREA
gap converges to `4·ln(φ)·ℓ_P²` — the comb mechanism's target gap, reached
here ONLY as the asymptotic consequence of the inserted hypotheses. -/
theorem area_gap_tendsto (M : HorizonCombModel) :
    Filter.Tendsto (fun n => M.area (n + 1) - M.area n)
      Filter.atTop (nhds (4 * M.lP2 * Real.log Constants.phi)) := by
  have h := (M.entropy_gap_tendsto).const_mul (4 * M.lP2)
  refine h.congr fun n => ?_
  simp only [area]
  ring

end HorizonCombModel

/-- Model inhabitation witness (consistency of the hypothesis bundle; carries
no physics: `lP2 = 1` is a placeholder unit). -/
def horizonCombModelWitness : HorizonCombModel where
  patchClass := fibPatchWitness
  counts_are_fib _ := rfl
  lP2 := 1
  lP2_pos := zero_lt_one

/-- **P3 TARGET (OPEN).** The EXACT per-level area gap
`A(n+1) − A(n) = 4·ln(φ)·ℓ_P²` for all `n` (not just asymptotically). No RS
capital forces this; what a real derivation would require is P2's patch class
FROM CAPITAL plus an exact (not asymptotic) counting theorem, or a different
exact mechanism entirely. -/
def AreaGapTarget (lP2 : ℝ) (A : ℕ → ℝ) : Prop :=
  ∀ n, A (n + 1) - A n = 4 * Real.log Constants.phi * lP2

/-! ## §Comb observable (MODEL-tier consequences, exact values + kernel bounds)

ABSORPTION/LEVEL-STRUCTURE claim, NOT an echo train. Numeric receipt:
GMω* = ln(φ)/(8π) = 0.01914681015812707
(`state/qg_full_theory/horizon_comb_preflight/comb_values.txt`). -/

/-- The Schwarzschild comb observable, exact: `GM·ω* = ln(φ)/(8π)`.
Tier: MODEL (a consequence of the underived chain above, via the first law
`ΔM = κ·ΔA/(8π)` with `ω = ΔM` in ℏ = c = 1 units; see
`schwarzschild_comb_frequency`). NOT a prediction until the area quantization
is DERIVED. -/
def combFrequencyGM : ℝ := Real.log Constants.phi / (8 * Real.pi)

theorem combFrequencyGM_pos : 0 < combFrequencyGM :=
  div_pos (Real.log_pos Constants.one_lt_phi) (by positivity)

/-- Kernel interval for the comb observable: `0.0191 < ln(φ)/(8π) < 0.0193`.
Grounded in `Numerics.log_phi_gt_0481`/`log_phi_lt_0483` (Taylor-certified)
and `Real.pi_gt_d6`/`pi_lt_d6`. True value 0.019147 (receipt in scratch).

TRUST-BASE CAVEAT (critic 2026-07-15): the upstream log-φ interval lemmas
in `Numerics/Interval/Log.lean` use `native_decide`, so this bound
transitively inherits the `Lean.ofReduceBool` trust base; it is NOT on
the bare standard-trio axiom footing of the rest of this module. -/
theorem combFrequencyGM_bounds :
    (0.0191 : ℝ) < combFrequencyGM ∧ combFrequencyGM < (0.0193 : ℝ) := by
  have hphi : Constants.phi = Real.goldenRatio := rfl
  have hlog_lo : (0.481 : ℝ) < Real.log Constants.phi := by
    rw [hphi]
    exact Numerics.log_phi_gt_0481
  have hlog_hi : Real.log Constants.phi < (0.483 : ℝ) := by
    rw [hphi]
    exact Numerics.log_phi_lt_0483
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have h8pi : (0 : ℝ) < 8 * Real.pi := by positivity
  constructor
  · rw [combFrequencyGM, lt_div_iff₀ h8pi]
    nlinarith
  · rw [combFrequencyGM, div_lt_iff₀ h8pi]
    nlinarith

/-- The Kerr locked comb shape: the offset of the absorption lines from the
superradiant bound, `ω − m·Ω_H = κ·ln(φ)/(2π)` at surface gravity `κ`.
Tier: MODEL (same underived chain). -/
def kerrCombOffset (kappa : ℝ) : ℝ :=
  kappa * Real.log Constants.phi / (2 * Real.pi)

/-- Consistency: the Kerr offset is `4κ` times the Schwarzschild observable
(`κ_Schw = 1/(4GM)` reproduces `GM·ω* = ln(φ)/(8π)`). -/
theorem kerrCombOffset_eq (kappa : ℝ) :
    kerrCombOffset kappa = (4 * kappa) * combFrequencyGM := by
  rw [kerrCombOffset, combFrequencyGM]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- MODEL conversion step (the first-law input, stated as a definition so its
hypothesis status is explicit): a transition between adjacent area sectors
with gap `deltaA` at surface gravity `kappa` has frequency
`ω = κ·ΔA/(8π·ℓ_P²)` (from `ΔM = κ·ΔA/(8πG)`, `ω = ΔM`, `ℓ_P² = G` in
ℏ = c = 1 units). -/
def modelTransitionFrequency (kappa lP2 deltaA : ℝ) : ℝ :=
  kappa * deltaA / (8 * Real.pi * lP2)

/-- **THEN (kernel-checked algebra).** Feeding the MODEL area gap
`ΔA = 4·ln(φ)·ℓ_P²` through the first-law conversion yields exactly the Kerr
comb offset `κ·ln(φ)/(2π)`. -/
theorem model_area_gap_gives_kerr_comb (kappa lP2 : ℝ) (hlP2 : lP2 ≠ 0) :
    modelTransitionFrequency kappa lP2 (4 * Real.log Constants.phi * lP2)
      = kerrCombOffset kappa := by
  rw [modelTransitionFrequency, kerrCombOffset]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **THEN (kernel-checked algebra).** For Schwarzschild
(`κ = 1/(4GM)`) the comb sits at `GM·ω* = ln(φ)/(8π)` exactly — the
mechanism's headline observable, derived HERE only from the inserted MODEL
hypotheses. -/
theorem schwarzschild_comb_frequency (G M lP2 : ℝ)
    (hG : G ≠ 0) (hM : M ≠ 0) (hlP2 : lP2 ≠ 0) :
    (G * M) * modelTransitionFrequency (1 / (4 * G * M)) lP2
        (4 * Real.log Constants.phi * lP2)
      = combFrequencyGM := by
  rw [modelTransitionFrequency, combFrequencyGM]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ## §P4. Adjacent-sector transition: named target, no capital -/

/-- **P4 TARGET (OPEN; there is NO capital for this and none is pretended).**
For a horizon transition kernel `T` between area sectors, the comb is
observable only if adjacent-sector matrix elements are nonzero. No RS module
constructs any horizon transition operator; building one would require
horizon dynamics (absorption amplitudes between ledger sectors), which does
not exist in the formalization. Flag false. -/
def AdjacentSectorTransitionNonzero (T : ℕ → ℕ → ℝ) : Prop :=
  ∀ n, T n (n + 1) ≠ 0

/-! ## §Status flags (documentation record; the mathematics is above) -/

/-- Status flags for the horizon comb preflight. The mechanism is NOT forced:
P1's scaling family survives (kernel-checked), P2's discrete state class is
absent from capital, P3 landed only the asymptotic fragment plus the MODEL
chain, P4 has no capital. The honest forced fraction is the kinematics and
the Fibonacci limit; the physical quantization content is 0% forced. -/
structure HorizonCombPreflightStatus where
  /-- P1: a continuous scaling family of admissible configurations with
  `A(λe) = λ²A(e)` EXISTS at the current formalization level (proved). -/
  p1_scaling_family_exists_at_current_formalization : Bool
  /-- P1 consequence: the area gap `ΔA = 4·ln(φ)·ℓ_P²` is forced. FALSE. -/
  p1_area_gap_forced : Bool
  /-- P2: a discrete horizon state class exists in RS capital. FALSE. -/
  p2_discrete_horizon_state_class_in_capital : Bool
  /-- P3: the asymptotic entropy-gap theorem (`ln F ratio → ln φ`) landed. -/
  p3_asymptotic_entropy_gap_theorem_landed : Bool
  /-- P3: the exact per-level area gap is derived from capital. FALSE. -/
  p3_exact_area_gap_derived : Bool
  /-- P4: capital for an adjacent-sector transition operator exists. FALSE. -/
  p4_transition_capital_exists : Bool
  /-- The absorption-comb mechanism is forced by existing capital. FALSE. -/
  mechanism_forced : Bool
  /-- The dead 0.618 echo-train discriminator is being revived here. FALSE. -/
  echo_discriminator_revived : Bool

/-- The canonical preflight status (rfl-forced documentation record). -/
def horizonCombPreflightStatus : HorizonCombPreflightStatus where
  p1_scaling_family_exists_at_current_formalization := true
  p1_area_gap_forced := false
  p2_discrete_horizon_state_class_in_capital := false
  p3_asymptotic_entropy_gap_theorem_landed := true
  p3_exact_area_gap_derived := false
  p4_transition_capital_exists := false
  mechanism_forced := false
  echo_discriminator_revived := false

/-- Status record (rfl-forced; documentation, not new mathematics). -/
theorem horizonCombPreflightStatus_flags :
    HorizonCombPreflightStatus.p1_scaling_family_exists_at_current_formalization
        horizonCombPreflightStatus = true ∧
    horizonCombPreflightStatus.p1_area_gap_forced = false ∧
    HorizonCombPreflightStatus.p2_discrete_horizon_state_class_in_capital
        horizonCombPreflightStatus = false ∧
    HorizonCombPreflightStatus.p3_asymptotic_entropy_gap_theorem_landed
        horizonCombPreflightStatus = true ∧
    horizonCombPreflightStatus.p3_exact_area_gap_derived = false ∧
    horizonCombPreflightStatus.p4_transition_capital_exists = false ∧
    horizonCombPreflightStatus.mechanism_forced = false ∧
    horizonCombPreflightStatus.echo_discriminator_revived = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

end HorizonLedgerPreflight
end SevenGaps
end Gravity
end IndisputableMonolith
