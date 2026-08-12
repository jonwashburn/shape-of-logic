import Mathlib
import IndisputableMonolith.Foundation.PairKernelOnsiteExclusion

/-!
# Door 2 / L0: the finite-range (locality) hypothesis on the ledger weight graph

Pair-kernel provenance lane (`glm/fold_derivation_logs/pairwise_kernel_derive.md`).

## Why L0 is needed regardless of L1 / the bridge

`PairKernelOnsiteExclusion` proved on-site-mass exclusion conditional on `ShiftInvariant`
(difference-only cost), and the bridge (`PairKernelRatioBridge`) closed the last route to
making `ShiftInvariant` a THEOREM (it is MODEL-forced, definitional). But even a
THEOREM-grade `ShiftInvariant` does NOT exclude a screened (Yukawa-like) kernel: the
panel's mean-field counterexample, formalized as `meanFieldLedgerCost`, is difference-only
and shift-invariant yet all-to-all coupled, and an all-to-all coupling produces a mass gap
away from `k = 0` (the `+μ` screening symbol; the dispersion analysis is MEASURED /
numerical in the L2 harness, not re-proved here). Excluding that route needs a SEPARATE
locality hypothesis: the weights must vanish beyond a fixed range.

A canon scan (2026-07-07) found NO range/locality principle on `WeightedLedgerGraph`
anywhere in the Lean surface. `LocalityFromLedger.lean` proves a different locality (the
T5→T6 binary-recurrence adjacency between scale *levels*), not a range cutoff on the pair
weight kernel. So `L0` is genuinely un-formalized, and the honest move is to name it as an
explicit, discriminating **HYPOTHESIS** rather than rest silently on the `4³` lattice's
nearest-neighbor adjacency that the L2 harness happened to use.

## What this module supplies (honest scope)

- `FiniteRange G R`: the named locality hypothesis — the weight between two sites at
  index-distance `> R` is zero. This is the postulate; it is NOT derived here.
- **Teeth (`meanFieldLedgerCost_not_finiteRange`):** the mean-field graph that carries the
  built screening honest-negative violates `FiniteRange` at every fixed radius once the
  carrier is large enough. So `FiniteRange` is genuinely load-bearing — it rejects exactly
  the counterexample that survives L1.
- **Non-vacuity (`bandWeight_finiteRange` + admissibility):** a nearest-neighbor band graph
  is an admissible `WeightedLedgerGraph` that satisfies `FiniteRange 1`. So the hypothesis
  is not empty; some real cost satisfies it.

This module does NOT prove "L0 ⇒ no screening" (that is the dispersion/Fourier step, MEASURED
in L2). It formalizes the hypothesis, proves it discriminates, and tags it HYPOTHESIS.

## Scoped verdict (`inference-discipline.mdc` form)

- CLAIM: `FiniteRange` is a non-vacuous, discriminating locality hypothesis on the ledger
  weight graph — satisfiable by a band graph, violated by the mean-field graph that carries
  the screening honest-negative.
- DOMAIN: `WeightedLedgerGraph` over `Fin n`; index-distance `Nat.dist i.val j.val`.
- PREMISES: none beyond the definitions (all statements proved).
- REACH: max licensed → "L0 is a real, load-bearing hypothesis, currently HYPOTHESIS-tier
  (postulated, not derived from a more primitive RS principle), that rejects the mean-field
  screening carrier and is satisfiable." Does NOT license → "L0 excludes screening" (that is
  the un-formalized dispersion step), nor "L0 is forced by RS" (its provenance — deriving a
  range cutoff from atomic-tick / recognition adjacency — is OPEN, expected-closure), nor any
  claim about `1/r` vs. Yukawa from primitives, nor any use of `5/8`, `5/16`, `27/16`,
  `Z_eff`, or hydrogenic `F(r)` (none appear here).

Zero `sorry`. Zero new `axiom`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PairKernelLocality

open SimplicialLedger.ContinuumBridge
open PairKernelOnsiteExclusion

noncomputable section

/-! ## §1. Index distance and the finite-range hypothesis -/

/-- The index distance between two sites of a `Fin n` carrier: `|i − j|` via `Nat.dist`.
    This is a placeholder geometry for the abstract carrier; the point is only that it
    separates far-apart indices, which is all a range cutoff needs. -/
def cellDist {n : ℕ} (i j : Fin n) : ℕ := Nat.dist i.val j.val

theorem cellDist_comm {n : ℕ} (i j : Fin n) : cellDist i j = cellDist j i := by
  simp only [cellDist, Nat.dist_comm]

/-- **L0 (finite-range / locality hypothesis).** The weight between two sites more than `R`
    index-cells apart is zero: no coupling beyond a fixed range. This is the separate
    postulate `L1` / the bridge do not supply; it is stated as a named hypothesis, NOT
    derived from anything more primitive in the Lean surface today (its provenance is OPEN,
    expected-closure via the atomic-tick / recognition adjacency being nearest-neighbor). -/
def FiniteRange {n : ℕ} (G : WeightedLedgerGraph n) (R : ℕ) : Prop :=
  ∀ i j : Fin n, R < cellDist i j → G.weight i j = 0

/-! ## §2. Teeth: the mean-field screening carrier is NOT finite-range

`meanFieldWeight` (uniform all-to-all coupling `1`, the carrier of the built screening
honest-negative `meanFieldLedgerCost_shift_invariant`) violates `FiniteRange` at every
fixed radius `R` once `n ≥ R + 2`: sites `0` and `R+1` are `R+1 > R` cells apart yet still
coupled with weight `1`. So `FiniteRange` genuinely rejects the counterexample L1 could not
touch — it is load-bearing, not a null hypothesis. -/

theorem meanFieldWeight_not_finiteRange (R n : ℕ) (hn : R + 2 ≤ n) :
    ¬ FiniteRange (meanFieldWeight n) R := by
  intro hFR
  have hi : (0 : ℕ) < n := by omega
  have hj : R + 1 < n := by omega
  have hrange : R < cellDist (⟨0, hi⟩ : Fin n) (⟨R + 1, hj⟩ : Fin n) := by
    show R < Nat.dist 0 (R + 1)
    unfold Nat.dist
    omega
  have h1 := hFR ⟨0, hi⟩ ⟨R + 1, hj⟩ hrange
  simp only [meanFieldWeight] at h1
  exact one_ne_zero h1

/-- The same teeth, stated on the built honest-negative cost `meanFieldLedgerCost`: its
    weight graph (`meanFieldWeight`) is not finite-range. This is the direct link — L0 is
    exactly the hypothesis that rejects the screening carrier that survives L1. -/
theorem meanFieldLedgerCost_not_finiteRange (R n : ℕ) (hn : R + 2 ≤ n) :
    ¬ FiniteRange (meanFieldLedgerCost n).G R :=
  meanFieldWeight_not_finiteRange R n hn

/-! ## §3. Non-vacuity: a nearest-neighbor band graph is admissible and finite-range -/

/-- The nearest-neighbor **band** weight graph: coupling `1` between sites at most one cell
    apart, `0` otherwise. An admissible `WeightedLedgerGraph` (nonnegative, symmetric). -/
def bandWeight (n : ℕ) : WeightedLedgerGraph n where
  weight := fun i j => if cellDist i j ≤ 1 then 1 else 0
  weight_nonneg := fun i j => by
    show (0 : ℝ) ≤ if cellDist i j ≤ 1 then (1 : ℝ) else 0
    split <;> norm_num
  weight_symm := fun i j => by
    show (if cellDist i j ≤ 1 then (1 : ℝ) else 0) = if cellDist j i ≤ 1 then (1 : ℝ) else 0
    rw [cellDist_comm i j]

/-- The band graph satisfies the locality hypothesis at radius `1`: nothing couples beyond
    one cell. So `FiniteRange` is not empty — a real admissible cost lives inside it. -/
theorem bandWeight_finiteRange (n : ℕ) : FiniteRange (bandWeight n) 1 := by
  intro i j hR
  simp only [bandWeight]
  exact if_neg (not_le.mpr hR)

/-- Sanity: the band graph does couple adjacent sites (weight `1` on the nearest-neighbor
    pair `0,1`), so it is not the trivial diagonal graph — the witness carries real content. -/
theorem bandWeight_adjacent_coupled (n : ℕ) (hn : 2 ≤ n) :
    (bandWeight n).weight ⟨0, by omega⟩ ⟨1, by omega⟩ = 1 := by
  have hd : cellDist (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) ≤ 1 := by
    show Nat.dist 0 1 ≤ 1
    unfold Nat.dist
    omega
  simp only [bandWeight]
  exact if_pos hd

/-! ## §4. Bundle: `FiniteRange` is a genuine, discriminating hypothesis -/

/-- **L0 status bundle.** `FiniteRange` is (a) satisfiable by an admissible non-trivial
    graph (the band graph, radius `1`), and (b) violated by the mean-field graph that
    carries the built screening honest-negative (at every fixed radius, for large enough
    carriers). A hypothesis with both properties is neither vacuous nor trivially true: it
    does real work. It remains HYPOTHESIS-tier — its RS provenance (a forced range cutoff)
    is OPEN. -/
theorem finiteRange_is_discriminating :
    (∀ n, FiniteRange (bandWeight n) 1) ∧
      (∀ R n, R + 2 ≤ n → ¬ FiniteRange (meanFieldWeight n) R) :=
  ⟨bandWeight_finiteRange, meanFieldWeight_not_finiteRange⟩

end

end PairKernelLocality
end Foundation
end IndisputableMonolith
