import Mathlib
import IndisputableMonolith.Recognition
import IndisputableMonolith.RecogSpec.Core
-- Note: LedgerNecessity.lean has pre-existing build issues; we don't need it directly
-- The ledger structure is defined independently here for the T5 forcing argument

/-!
# Ledger-Derived Cost Constraints (Symmetry and Unit) — with a No-Go Certificate

This module derives TWO of the T5 constraints from the ledger structure (T3),
and proves that the remaining constraint CANNOT be so derived.

## Main Results

1. **Symmetry Forced**: The ledger's double-entry structure forces F(x) = F(1/x).
2. **Unit Forced**: The identity posting (no change) has zero cost, forcing F(1) = 0.
3. **NO-GO (`aczel_hypothesis_refuted`)**: symmetry + unit + continuity +
   curvature calibration do NOT force the Cosh-Add (d'Alembert) identity.
   Witness: `G(t) = t²/2`. The composition law C6 is an independent,
   load-bearing hypothesis of the T5 characterization theorem.

## The Honest Chain

```
T3 (Ledger Structure)
  ↓ [Double-entry bookkeeping]
F(x) = F(1/x)  (Reciprocal Symmetry — proved here)
  ↓ [Identity posting = no entry]
F(1) = 0  (Unit Normalization — proved here)

C6 (composition / Cosh-Add)  — INDEPENDENT HYPOTHESIS (not derivable; no-go proved here)
C7 (calibration λ = 1)       — normalization choice
  ↓ [given C1–C7: Aczél-type classification]
T5: J(x) = ½(x + 1/x) - 1 is the unique admissible cost
```

## History

An earlier revision of this file claimed the Cosh-Add identity followed from
the ledger constraints plus continuity, citing Aczél (1966, Thm. 3.1.3), and
concluded T5 was "unconditionally forced" from T1–T4. Both claims were false
(2026 internal audit, Finding 2) and are retracted; the refutation is now a
kernel-checked theorem in this file.

## References

- Aczél, J. "Lectures on Functional Equations and Their Applications" (1966), Ch. 3
  (classification of d'Alembert solutions — used with, not instead of, C6)
- Recognition Science: T3 Ledger Necessity theorems

-/

namespace IndisputableMonolith
namespace Verification
namespace T5
namespace LedgerCost

open Real

/-! ## Part 1: Ledger-Derived Cost Structure

A ledger is a double-entry system where every debit has a matching credit.
The "cost" of a recognition event is the magnitude of the ledger entry required
to record the transition from state A to state B.
-/

/-- A ledger posting records a transition between two positive values.
    The ratio A/B captures the "exchange rate" of the transition. -/
structure LedgerPosting where
  source : ℝ
  target : ℝ
  source_pos : 0 < source
  target_pos : 0 < target

/-- The ratio of a ledger posting. -/
noncomputable def LedgerPosting.ratio (p : LedgerPosting) : ℝ :=
  p.source / p.target

/-- The inverse posting (swapping source and target). -/
def LedgerPosting.inverse (p : LedgerPosting) : LedgerPosting :=
  { source := p.target
  , target := p.source
  , source_pos := p.target_pos
  , target_pos := p.source_pos }

lemma LedgerPosting.inverse_ratio (p : LedgerPosting) :
    p.inverse.ratio = p.ratio⁻¹ := by
  simp only [inverse, ratio]
  have hs : p.source ≠ 0 := p.source_pos.ne'
  have ht : p.target ≠ 0 := p.target_pos.ne'
  field_simp

/-- The identity posting (source = target). -/
noncomputable def LedgerPosting.identity (x : ℝ) (hx : 0 < x) : LedgerPosting :=
  { source := x
  , target := x
  , source_pos := hx
  , target_pos := hx }

lemma LedgerPosting.identity_ratio (x : ℝ) (hx : 0 < x) :
    (LedgerPosting.identity x hx).ratio = 1 := by
  simp only [identity, ratio]
  have hne : x ≠ 0 := hx.ne'
  field_simp

/-! ## Part 2: The Ledger Cost Functional

The cost of a ledger posting measures the "work" required to record the transition.
This is defined in terms of the ratio, capturing the asymmetry between source and target.
-/

/-- A cost functional on ledger postings.

Note: an earlier revision carried a vacuous field `domain : ∀ x, 0 < x → True`
(flagged in external audit as contentless debris). It has been removed; the
positivity of ratios is enforced at the `LedgerPosting` level, not here. -/
structure LedgerCostFunctional where
  /-- The cost function on positive ratios. -/
  cost : ℝ → ℝ

/-- The cost of a ledger posting under a cost functional. -/
noncomputable def LedgerCostFunctional.postingCost
    (F : LedgerCostFunctional) (p : LedgerPosting) : ℝ :=
  F.cost p.ratio

/-! ## Part 3: Symmetry Forced from Double-Entry

**Theorem**: In a double-entry ledger, the cost of posting A→B equals the cost of B→A.

**Proof**: A double-entry ledger records both sides of every transaction:
- Posting A→B creates a debit of A and credit of B
- Posting B→A creates a debit of B and credit of A
- These are the same transaction viewed from opposite sides
- Therefore the cost must be equal

In ratio terms: F(A/B) = F(B/A) = F((A/B)⁻¹)
-/

/-- A cost functional respects double-entry if inverse postings have equal cost. -/
def LedgerCostFunctional.respectsDoubleEntry (F : LedgerCostFunctional) : Prop :=
  ∀ p : LedgerPosting, F.postingCost p = F.postingCost p.inverse

/-- **Theorem (Symmetry Forced)**: Double-entry structure forces reciprocal symmetry.

This is the key theorem connecting T3 (Ledger) to the T5 constraint F(x) = F(1/x).
-/
theorem symmetry_forced_from_double_entry
    (F : LedgerCostFunctional)
    (hDE : F.respectsDoubleEntry) :
    ∀ x, 0 < x → F.cost x = F.cost x⁻¹ := by
  intro x hx
  -- Construct a posting with ratio x
  let p : LedgerPosting := {
    source := x
    target := 1
    source_pos := hx
    target_pos := one_pos
  }
  -- The posting has ratio x
  have hp_ratio : p.ratio = x := by simp [LedgerPosting.ratio, p]
  -- The inverse posting has ratio 1/x
  have hp_inv_ratio : p.inverse.ratio = x⁻¹ := by
    rw [LedgerPosting.inverse_ratio, hp_ratio]
  -- By double-entry, costs are equal
  have h := hDE p
  simp only [LedgerCostFunctional.postingCost] at h
  rw [hp_ratio, hp_inv_ratio] at h
  exact h

/-! ## Part 4: Unit Normalization Forced from Identity

**Theorem**: The identity posting (no change) has zero cost.

**Proof**: An identity posting A→A represents "no transaction" in the ledger.
No debit or credit is recorded. The cost of doing nothing must be zero,
as it's the baseline against which all other costs are measured.

In ratio terms: F(1) = 0
-/

/-- A cost functional has zero identity cost if F(1) = 0. -/
def LedgerCostFunctional.zeroIdentityCost (F : LedgerCostFunctional) : Prop :=
  F.cost 1 = 0

/-- **Theorem (Unit Forced)**: Identity postings have zero cost.

This is the key theorem connecting T3 (Ledger) to the T5 constraint F(1) = 0.

The argument: An identity posting records no change in the ledger.
Since no entry is made, the cost must be zero.
-/
theorem unit_forced_from_identity_posting
    (F : LedgerCostFunctional)
    (hZero : ∀ p : LedgerPosting, p.source = p.target → F.postingCost p = 0) :
    F.zeroIdentityCost := by
  unfold LedgerCostFunctional.zeroIdentityCost
  -- Construct an identity posting
  let p := LedgerPosting.identity 1 one_pos
  have hp_eq : p.source = p.target := rfl
  have hp_ratio : p.ratio = 1 := LedgerPosting.identity_ratio 1 one_pos
  -- Apply the hypothesis
  have h := hZero p hp_eq
  simp only [LedgerCostFunctional.postingCost, hp_ratio] at h
  exact h

/-! ## Part 5: Additivity from Sequential Postings

**Theorem**: Sequential ledger postings have additive costs in log-space.

**Proof**: If we post A→B and then B→C, the total ledger effect is A→C.
The costs should combine: Cost(A→B) + Cost(B→C) relates to Cost(A→C).

In log-space (t = log(ratio)):
- Posting with ratio r₁ followed by ratio r₂ gives total ratio r₁·r₂
- log(r₁·r₂) = log(r₁) + log(r₂)
- This additivity in log-space constrains the functional form

This property, combined with symmetry and continuity, leads to the cosh-add identity.
-/

/-- Sequential postings: if p₁ goes A→B and p₂ goes B→C, the composition goes A→C. -/
def LedgerPosting.compose (p₁ p₂ : LedgerPosting)
    (h : p₁.target = p₂.source) : LedgerPosting :=
  { source := p₁.source
  , target := p₂.target
  , source_pos := p₁.source_pos
  , target_pos := p₂.target_pos }

lemma LedgerPosting.compose_ratio (p₁ p₂ : LedgerPosting) (h : p₁.target = p₂.source) :
    (p₁.compose p₂ h).ratio = p₁.ratio * p₂.ratio := by
  simp only [compose, ratio]
  have ht1 : p₁.target ≠ 0 := p₁.target_pos.ne'
  have ht2 : p₂.target ≠ 0 := p₂.target_pos.ne'
  have hs2 : p₂.source ≠ 0 := p₂.source_pos.ne'
  rw [h]
  field_simp

/-- In log-space, composition corresponds to addition of log-ratios. -/
lemma log_ratio_additive (p₁ p₂ : LedgerPosting) (h : p₁.target = p₂.source) :
    Real.log (p₁.compose p₂ h).ratio = Real.log p₁.ratio + Real.log p₂.ratio := by
  rw [LedgerPosting.compose_ratio p₁ p₂ h]
  have hr1 : 0 < p₁.ratio := by
    simp only [LedgerPosting.ratio]
    exact div_pos p₁.source_pos p₁.target_pos
  have hr2 : 0 < p₂.ratio := by
    simp only [LedgerPosting.ratio]
    exact div_pos p₂.source_pos p₂.target_pos
  exact Real.log_mul hr1.ne' hr2.ne'

/-! ## Part 6: The Complete Forcing Theorem

We now state the complete theorem: the ledger structure forces all T5 constraints
except the Cosh-Add identity, which follows from functional equation theory.
-/

/-- A cost functional is ledger-compatible if it respects double-entry and
    has zero identity cost. -/
structure LedgerCompatible (F : LedgerCostFunctional) : Prop where
  double_entry : F.respectsDoubleEntry
  zero_identity : ∀ p : LedgerPosting, p.source = p.target → F.postingCost p = 0

/-- **Main Theorem**: Ledger compatibility forces the T5 constraints.

From the ledger structure (T3), we derive:
1. Reciprocal symmetry: F(x) = F(1/x)
2. Unit normalization: F(1) = 0

These are the two physical constraints of T5. The remaining constraint
(the Cosh-Add identity, i.e. the composition law C6) is an INDEPENDENT
hypothesis: it does not follow from these constraints plus continuity
(see `aczel_hypothesis_refuted` below).
-/
theorem ledger_forces_t5_constraints
    (F : LedgerCostFunctional)
    (hLC : LedgerCompatible F) :
    (∀ x, 0 < x → F.cost x = F.cost x⁻¹) ∧ F.cost 1 = 0 := by
  constructor
  · exact symmetry_forced_from_double_entry F hLC.double_entry
  · exact unit_forced_from_identity_posting F hLC.zero_identity

/-! ## Part 7: The Cosh-Add Identity Is an Independent Hypothesis (corrected)

An earlier revision of this section claimed the Cosh-Add identity is "a
mathematical consequence of the constraints derived above plus continuity",
citing Aczél (1966, Theorem 3.1.3). **That claim was false** and is
retracted (2026 internal audit, Finding 2). Aczél's theorem classifies the
solutions OF the d'Alembert equation; it does not derive the equation from
evenness, normalization, continuity, and calibration. The counterexample
`G(t) = t²/2` (below) satisfies all four conditions and violates Cosh-Add.

The honest status: Cosh-Add is the log-axis form of the composition law
(closure hypothesis C6 in the RS_v1 paper) and enters as an independent,
load-bearing hypothesis of the T5 characterization theorem.
-/

/-- The Cosh-Add (d'Alembert-type) identity in the form used by T5.

This is the log-axis form of the composition law C6. It is an INDEPENDENT
hypothesis of the T5 characterization: it is NOT implied by symmetry, unit
normalization, continuity, and curvature calibration (see
`aczel_hypothesis_refuted`).
-/
def CoshAddFromLedger (G : ℝ → ℝ) : Prop :=
  ∀ t u : ℝ, G (t+u) + G (t-u) = 2 * (G t * G u) + 2 * (G t + G u)

/-- **REFUTED PROPOSITION** (retained only so its refutation can be stated).

This proposition asserts that evenness + normalization + continuity + unit
log-curvature alone force the Cosh-Add (d'Alembert) identity. **It is FALSE.**
The quadratic cost `G(t) = t²/2` satisfies every hypothesis and violates
Cosh-Add (see `aczel_hypothesis_refuted` below).

An earlier revision of this file misattributed this proposition to Aczél
(1966, Theorem 3.1.3) and presented it as established mathematics. That was
an error, identified in the 2026 internal audit (Thapa, T−2..T5 forcing
report, Finding 2). Aczél's classification runs in the OTHER direction: it
classifies solutions OF the d'Alembert equation; it does not derive the
equation from regularity hypotheses. The composition law (the paper's
closure hypothesis C6) is genuinely load-bearing and cannot be obtained
from symmetry, normalization, continuity, and calibration alone.

Nothing in this repository may assume this proposition. It is kept as a
`def` solely as the subject of the no-go certificate below. -/
def aczel_theorem_3_1_3_hypothesis : Prop :=
  ∀ (G : ℝ → ℝ),
    Function.Even G →
    G 0 = 0 →
    Continuous G →
    deriv (deriv G) 0 = 1 →
    CoshAddFromLedger G

/-- The quadratic-cost witness `G(t) = t²/2`. Even, vanishes at 0, continuous,
with unit second derivative at the origin — yet it does not satisfy Cosh-Add. -/
noncomputable def quadraticWitness : ℝ → ℝ := fun t => t ^ 2 / 2

lemma quadraticWitness_even : Function.Even quadraticWitness := by
  intro t; simp [quadraticWitness]

lemma quadraticWitness_zero : quadraticWitness 0 = 0 := by
  simp [quadraticWitness]

lemma quadraticWitness_continuous : Continuous quadraticWitness := by
  unfold quadraticWitness; fun_prop

lemma quadraticWitness_deriv : deriv quadraticWitness = fun t => t := by
  funext x
  have h : HasDerivAt quadraticWitness x x := by
    have := (hasDerivAt_pow 2 x).div_const 2
    simpa [quadraticWitness, pow_one] using this
  simpa using h.deriv

lemma quadraticWitness_second_deriv : deriv (deriv quadraticWitness) 0 = 1 := by
  rw [quadraticWitness_deriv]
  simp

/-- The witness violates Cosh-Add at t = u = 1: LHS = 2, RHS = 5/2. -/
lemma quadraticWitness_not_coshAdd : ¬ CoshAddFromLedger quadraticWitness := by
  intro h
  have h11 := h 1 1
  norm_num [quadraticWitness] at h11

/-- **NO-GO CERTIFICATE (Finding 2 resolution)**: the proposition
`aczel_theorem_3_1_3_hypothesis` is false. Symmetry, unit normalization,
continuity, and unit log-curvature calibration do NOT force the Cosh-Add
identity; the composition law C6 is an independent, load-bearing hypothesis.

Witness: `G(t) = t²/2`. -/
theorem aczel_hypothesis_refuted : ¬ aczel_theorem_3_1_3_hypothesis := by
  intro h
  exact quadraticWitness_not_coshAdd
    (h quadraticWitness quadraticWitness_even quadraticWitness_zero
      quadraticWitness_continuous quadraticWitness_second_deriv)

/-! ## Summary (corrected 2026-07-06)

What this file actually establishes:

```
T3 (Ledger)  →  Symmetry F(x) = F(1/x)   (from double-entry, proved above)
             →  Unit F(1) = 0            (from identity posting, proved above)
```

What it does NOT establish, and what `aczel_hypothesis_refuted` proves CANNOT
be established from these constraints alone:

```
Symmetry + Unit + Continuity + Calibration  ↛  Cosh-Add  ↛  J
```

The Cosh-Add (d'Alembert) identity is equivalent to the composition law
(the paper's closure hypothesis C6) and must be assumed or motivated
independently. The witness `G(t) = t²/2` satisfies every ledger-derived
constraint plus continuity and calibration, and is not J.

Consequently T5 is a CONDITIONAL characterization theorem: given C1–C7
(including the load-bearing C6 and the calibration C7), J is the unique
cost. It is NOT unconditionally forced from T1–T4. An earlier revision of
this summary claimed otherwise; that claim is retracted, and the refutation
is now a kernel-checked certificate in this file.
-/

end LedgerCost
end T5
end Verification
end IndisputableMonolith
