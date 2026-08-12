import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.SimplicialLedger.ContinuumBridge
import IndisputableMonolith.Foundation.SimplicialLedger.EdgeLengthFromPsi
import IndisputableMonolith.Foundation.SimplicialLedger.NonlinearBridge

/-!
# Door 2 / L1-hard: onsite-term exclusion from shift invariance

Pair-kernel provenance lane (`glm/fold_derivation_logs/pairwise_kernel_derive.md`).
L2 (`recognition_fold/screening_law/l2_hessian_dispersion.py`) measured the exact-`J`
Hessian's dispersion on a `4³ × 8` lattice and found it gapless and second-order, but
that test **assumed** the cost is a pure function of link/posting differences (no
on-site term). `exactJCostAction` is *defined* difference-only, so proving its shift
invariance is a null test (a one-line tautology; it provides zero evidence RS forbids
an on-site term, since we simply chose not to write one).

This module supplies the genuine, non-vacuous obligation: quantify over a class of
candidate ledger costs wide enough to *express* an on-site term, and prove that term is
forced constant by a genuine hypothesis (`ShiftInvariant`), not by construction.

## Panel verdict (2026-07-07, `door2_L1_provenance` panel, judge Fable xhigh)

The panel's decisive finding (Director 3's mean-field counterexample, kept as
`meanFieldLedgerCost` below) is that **shift invariance alone is necessary but NOT
sufficient** to exclude a screened (Yukawa-like) kernel: an admissible, shift-invariant,
purely difference-only cost can still carry an *all-to-all* (spatially non-local)
weight structure that produces a mass gap away from `k = 0`. Excluding that requires a
**separate** locality hypothesis (`L0`, finite-range weights), which is not addressed
here and is not yet anywhere in the Lean surface. `l1_onsite_forced_constant` below is
exactly the `L1` half of the panel's package (on-site exclusion); it does **not** by
itself decide `1/r` vs. Yukawa screening, only the on-site-mass branch of that question.

## Scoped verdict (`inference-discipline.mdc` form)

- CLAIM: for a `GeneralLedgerCost` (onsite term FREE, link term a pure function of
  posting differences, over any admissible weighted graph), global shift invariance of
  the total cost forces the onsite term to be a constant function of its argument.
- DOMAIN: any finite carrier `Fin n`, `n ≥ 1`; any nonneg-symmetric weight graph; any
  `link : ℝ → ℝ`.
- PREMISES: `ShiftInvariant C` (R1) [**HYPOTHESIS**. The 2026-07-07 `MP ⇒ Axiom R` canon audit
  resolved its provenance: it is NOT forced by the Meta-Principle. Canonical MP is
  `Recognition.MP := ¬∃ _ : Recognize Nothing Nothing, True` (`Empty` is uninhabited); it rejects only
  the uninhabited `Nothing`, so it cannot reject an inhabited frozen anchor (the value-0 vacuum an
  on-site mass term prices against). The `MP ⇒ Axiom R` live bet is CLOSED NEGATIVE. What the canon
  actually has is ratio-only cost primitives with no on-site slot: `LedgerForcing.event_cost e =
  J e.ratio` (`reciprocity`, `conservation_from_balance` proved) and
  `ConstraintForcing.RecognitionLogCost A B = (log A − log B)²` (`recognition_exchange_invariance_axiom`,
  `recognition_identity_axiom` proved). So `ShiftInvariant` holds definitionally on that ratio-carrier;
  on the `Recognition.Ledger` debit/credit carrier mirrored here (where an on-site slot IS expressible)
  its honest tier is MODEL-forced (definitional: a recognition is a two-party ratio), not MP-THEOREM.
  It stays a named, load-bearing assumption of this theorem]; `0 < n` [trivial].
- REACH: max licensed → "IF the ledger cost is admissible-shift-invariant, THEN no
  on-site mass term is writable, which is exactly what the L2 decoy `+m² Σ φᵢ²` violates
  and what the numeric harness correctly flagged Yukawa." Does NOT license → exclusion of
  *non-local* (all-to-all / mean-field) screening (`meanFieldLedgerCost` below is an
  explicit admissible counterexample to that stronger claim), nor any claim about
  `5/8`, `5/16`, `27/16`, `Z_eff`, or the hydrogenic `F(r)` carrier (none appear here).

Zero `sorry`. Zero new `axiom`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PairKernelOnsiteExclusion

open SimplicialLedger.ContinuumBridge
open SimplicialLedger.EdgeLengthFromPsi
open SimplicialLedger.NonlinearBridge

noncomputable section

/-! ## §1. The candidate class: onsite term is FREE

This is the anti-cheat. `exactJCostAction` has no on-site slot at all, so no proof about
it can typecheck against the theorem below. `GeneralLedgerCost.onsite` is an arbitrary
`ℝ → ℝ`; the theorem must rule out its non-constant instances by hypothesis, not by the
shape of the definition. -/

/-- A general ledger cost on `n` log-potential carriers: a (possibly nonzero) absolute
    per-site term `onsite`, plus a per-link term `link` evaluated on posting differences
    over an admissible weighted graph. `onsite` is a genuinely free parameter — nothing
    in this structure forces it to vanish or to be constant; that is exactly the content
    the forcing theorem below must supply from an extra hypothesis. -/
structure GeneralLedgerCost (n : ℕ) where
  /-- The underlying admissible (nonneg, symmetric) weighted ledger graph. -/
  G : WeightedLedgerGraph n
  /-- The absolute per-site cost term (the thing whose admissibility is in question). -/
  onsite : ℝ → ℝ
  /-- The per-link (posting-difference) cost term. -/
  link : ℝ → ℝ

/-- The total cost of a log-potential assignment under a general ledger cost:
    `Σᵢ onsite(εᵢ) + Σᵢⱼ wᵢⱼ · link(εᵢ − εⱼ)`. -/
def GeneralLedgerCost.eval {n : ℕ} (C : GeneralLedgerCost n) (ε : LogPotential n) : ℝ :=
  (∑ i : Fin n, C.onsite (ε i)) +
    ∑ i : Fin n, ∑ j : Fin n, C.G.weight i j * C.link (ε i - ε j)

/-- **R1 (global shift invariance).** Adding an arbitrary constant to every log-potential
    leaves the total ledger cost unchanged. This is the candidate double-entry gauge
    symmetry under investigation: absolute account *levels* carry no cost, only the
    *relations* between them do. It is stated here as a named hypothesis, not derived. -/
def ShiftInvariant {n : ℕ} (C : GeneralLedgerCost n) : Prop :=
  ∀ (ε : LogPotential n) (c : ℝ), C.eval (fun i => ε i + c) = C.eval ε

/-! ## §2. The link term is automatically shift-invariant (this is the null test to reject
    as a standalone deliverable — it carries zero content about the onsite term). -/

/-- The link (difference-only) part of `eval` never changes under a global shift, for
    *any* `link` function and *any* weight graph — a pure consequence of the fact that
    `(εᵢ + c) − (εⱼ + c) = εᵢ − εⱼ`. This is the tautological half of `ShiftInvariant`;
    it is exactly what makes `exactJCostAction`'s own shift invariance a null test (it
    has no onsite slot, so it only ever exercises this half). -/
theorem link_part_shift_invariant {n : ℕ} (C : GeneralLedgerCost n)
    (ε : LogPotential n) (c : ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, C.G.weight i j * C.link ((ε i + c) - (ε j + c)))
      = ∑ i : Fin n, ∑ j : Fin n, C.G.weight i j * C.link (ε i - ε j) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have : (ε i + c) - (ε j + c) = ε i - ε j := by ring
  rw [this]

/-- Consequently, `ShiftInvariant C` is *equivalent* to the onsite sum alone being
    shift-invariant. This isolates exactly the non-vacuous content: `ShiftInvariant`
    only has teeth against the onsite term, never against `link`. -/
theorem shiftInvariant_iff_onsite_sum {n : ℕ} (C : GeneralLedgerCost n) :
    ShiftInvariant C ↔
      ∀ (ε : LogPotential n) (c : ℝ),
        (∑ i : Fin n, C.onsite (ε i + c)) = ∑ i : Fin n, C.onsite (ε i) := by
  constructor
  · intro hR1 ε c
    have h := hR1 ε c
    unfold GeneralLedgerCost.eval at h
    rw [link_part_shift_invariant C ε c] at h
    linarith
  · intro honsite ε c
    unfold GeneralLedgerCost.eval
    rw [link_part_shift_invariant C ε c, honsite ε c]

/-! ## §3. L1-FORCE: the non-vacuous target -/

/-- **L1-FORCE (`l1_onsite_forced_constant`).** Under `ShiftInvariant` and `n ≥ 1`, the
    onsite part of an admissible `GeneralLedgerCost` is forced to be a constant
    function of its real argument — i.e. no on-site mass/absolute term is writable.

    Non-vacuity: this is FALSE without `ShiftInvariant`. Take `onsite u = u²` (the exact
    shape of the L2 decoy `+m² Σ φᵢ²`, which the numeric harness correctly flagged
    Yukawa): `yukawaOnsiteDecoy_not_shift_invariant` below shows this instance fails
    the hypothesis, so deleting `hR1` lets it stand as a live counterexample to the
    conclusion. -/
theorem l1_onsite_forced_constant {n : ℕ} (C : GeneralLedgerCost n) (hn : 0 < n)
    (hR1 : ShiftInvariant C) :
    ∃ k : ℝ, ∀ u : ℝ, C.onsite u = k := by
  refine ⟨C.onsite 0, fun u => ?_⟩
  have honsite := (shiftInvariant_iff_onsite_sum C).mp hR1 (fun _ => (0 : ℝ)) u
  simp only [zero_add] at honsite
  have hL : (∑ _i : Fin n, C.onsite u) = (n : ℝ) * C.onsite u := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hR : (∑ _i : Fin n, C.onsite 0) = (n : ℝ) * C.onsite 0 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hL, hR] at honsite
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  exact mul_left_cancel₀ hnr honsite

/-! ## §4. Decoy 1 (R1 fails): the on-site mass term, byte-for-byte the L2 decoy -/

/-- The decoy on-site "mass" cost, `onsite u = u²`, `link ≡ 0` — the exact shape of the
    `+m² Σ φᵢ²` operator the L2 Python harness flagged `DEAD_YUKAWA`. It is a perfectly
    well-formed `GeneralLedgerCost` (the structure does not forbid it), which is the
    point: nothing rules it out except a genuine hypothesis. -/
def yukawaOnsiteDecoy {n : ℕ} (G : WeightedLedgerGraph n) : GeneralLedgerCost n where
  G := G
  onsite := fun u => u ^ 2
  link := fun _ => 0

/-- **Anti-cheat witness.** The on-site mass decoy does NOT satisfy `ShiftInvariant`
    (for `n ≥ 1`): shifting the flat vacuum by `1` changes the total cost from `0` to
    `n`. So `ShiftInvariant` is genuinely load-bearing — the theorem above has teeth,
    and is not a restatement of something already true of every `GeneralLedgerCost`. -/
theorem yukawaOnsiteDecoy_not_shift_invariant {n : ℕ} (G : WeightedLedgerGraph n)
    (hn : 0 < n) :
    ¬ ShiftInvariant (yukawaOnsiteDecoy G) := by
  intro hR1
  have h := (shiftInvariant_iff_onsite_sum (yukawaOnsiteDecoy G)).mp hR1 (fun _ => (0 : ℝ)) 1
  simp only [yukawaOnsiteDecoy, zero_add] at h
  have hL : (∑ _i : Fin n, (1 : ℝ) ^ 2) = (n : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hR : (∑ _i : Fin n, (0 : ℝ) ^ 2) = (0 : ℝ) := by simp
  rw [hL, hR] at h
  exact (Nat.cast_ne_zero.mpr hn.ne') h

/-! ## §5. Witness 2 (the honest negative): admissible + shift-invariant does not imply
    locality. `ShiftInvariant` alone is necessary but NOT sufficient to exclude a
    screened kernel; the panel's mean-field counterexample lands here, formalized as an
    explicit non-local instance that is admissible and trivially shift-invariant. -/

/-- The **mean-field / all-to-all** weight graph: uniform coupling `1` between *every*
    pair of sites, including maximally separated ones. This is a perfectly admissible
    `WeightedLedgerGraph` (nonnegative, symmetric) — nothing in the graph axioms demands
    finite range. -/
def meanFieldWeight (n : ℕ) : WeightedLedgerGraph n where
  weight := fun _ _ => 1
  weight_nonneg := fun _ _ => zero_le_one
  weight_symm := fun _ _ => rfl

/-- The mean-field weight has full support: every pair, including every distinct pair,
    is coupled with nonzero weight. This is the formal shape of "not finite-range" — a
    genuinely local weight graph must vanish outside a bounded neighborhood as `n`
    grows, and this one never does. -/
theorem meanFieldWeight_full_support (n : ℕ) (i j : Fin n) :
    (meanFieldWeight n).weight i j ≠ 0 := by
  simp [meanFieldWeight]

/-- The mean-field ledger cost: NO on-site term at all (`onsite ≡ 0`, so it trivially
    satisfies the conclusion of `l1_onsite_forced_constant` with `k = 0`), link term a
    plain quadratic, and the non-local mean-field weight graph. -/
def meanFieldLedgerCost (n : ℕ) : GeneralLedgerCost n where
  G := meanFieldWeight n
  onsite := fun _ => 0
  link := fun u => u ^ 2

/-- **The honest negative.** The mean-field ledger cost is shift-invariant (it has no
    onsite term, so `ShiftInvariant` holds for the shape reason isolated in
    `shiftInvariant_iff_onsite_sum`, not because locality was ever assumed), yet its
    weight graph is non-local (`meanFieldWeight_full_support`). So `L1`
    (`l1_onsite_forced_constant`), even fully proved and even fully forced from
    first principles, does NOT by itself exclude a screened kernel: excluding the
    mean-field / all-to-all route needs a SEPARATE locality hypothesis `L0`
    (finite-range weights), which is not addressed in this module and, per the panel
    audit, is currently nowhere in the Lean surface. This is the scoped, honest residual
    of Door 2 / L1-hard: on-site exclusion is real and forced (conditional on
    `ShiftInvariant`), but on-site exclusion alone is not the whole story. -/
theorem meanFieldLedgerCost_shift_invariant (n : ℕ) :
    ShiftInvariant (meanFieldLedgerCost n) := by
  rw [shiftInvariant_iff_onsite_sum]
  intro ε c
  simp [meanFieldLedgerCost]

/-! ## §6. Positive control: `exactJCostAction` sits in the `onsite ≡ 0` slice

This connects the abstract exclusion theorem back to the real RS Lean object cited in
the Door 2 log. It is explicitly NOT the forcing result — proving `exactJCostAction`'s
own shift invariance directly (skipping `GeneralLedgerCost` entirely) is exactly the
null test the panel and the Door 2 log both flag and reject; it is recorded here only as
a consistency anchor, and the anti-cheat is that `l1_onsite_forced_constant` never
unfolds `exactJCostAction` at all. -/

/-- `exactJCostAction` re-expressed as a `GeneralLedgerCost` with the onsite slot
    identically the zero function — RS's actual cost primitive has never carried a
    writable onsite term in the first place. -/
def exactJCostAsGeneralLedgerCost {n : ℕ} (G : WeightedLedgerGraph n) : GeneralLedgerCost n where
  G := G
  onsite := fun _ => 0
  link := fun u => Real.cosh u - 1

/-- The re-expression agrees with `exactJCostAction` exactly. -/
theorem exactJCostAsGeneralLedgerCost_eval {n : ℕ} (G : WeightedLedgerGraph n)
    (ε : LogPotential n) :
    (exactJCostAsGeneralLedgerCost G).eval ε = exactJCostAction G ε := by
  unfold GeneralLedgerCost.eval exactJCostAsGeneralLedgerCost exactJCostAction
  simp

/-- Sanity corollary: applying the general forcing theorem to the `exactJCostAction`
    slice recovers `k = 0` (the onsite term was already zero, not merely forced to be
    some unknown constant). Consistency check, not new content. -/
theorem exactJCostAsGeneralLedgerCost_onsite_zero {n : ℕ} (G : WeightedLedgerGraph n)
    (_hn : 0 < n) :
    ∃ k : ℝ, k = 0 ∧ ∀ u : ℝ, (exactJCostAsGeneralLedgerCost G).onsite u = k := by
  refine ⟨0, rfl, fun u => rfl⟩

end

end PairKernelOnsiteExclusion
end Foundation
end IndisputableMonolith
