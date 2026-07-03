import Mathlib
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# NESS Conditional Independence, Measure-Theoretic Factorization

This module replaces the old `True`-predicate theorem surface with an explicit
probability-factorization statement over a `ProbabilityMeasure`.

Mathlib in this checkout exposes `ProbabilityMeasure` and `condExp`, but does
not expose a stable `MeasureTheory.CondIndep` / `IndepFun` API under those
names. We therefore define conditional independence by the standard blanket
factorization:

  P(I=i, B=b, E=e) · P(B=b) = P(I=i, B=b) · P(B=b, E=e).

This is equivalent to `P(I=i, E=e | B=b) = P(I=i | B=b) P(E=e | B=b)` when
`P(B=b) ≠ 0`. It is the finite-valued event-level form of the FEP Markov
blanket condition.
-/

namespace IndisputableMonolith.Information.NESSConditionalIndependenceMeasure

open MeasureTheory

noncomputable section

variable {Ω Internal Blanket External : Type*} [MeasurableSpace Ω]

/-- A measurable projection of a state space into the FEP partition. -/
structure BlanketProjection (Ω Internal Blanket External : Type*) where
  internal : Ω → Internal
  blanket : Ω → Blanket
  external : Ω → External

/-- Event where all three coarse-grained coordinates take specified values. -/
def atomSet (π : BlanketProjection Ω Internal Blanket External)
    (i : Internal) (b : Blanket) (e : External) : Set Ω :=
  {ω | π.internal ω = i ∧ π.blanket ω = b ∧ π.external ω = e}

/-- Event where internal and blanket coordinates take specified values. -/
def internalBlanketSet (π : BlanketProjection Ω Internal Blanket External)
    (i : Internal) (b : Blanket) : Set Ω :=
  {ω | π.internal ω = i ∧ π.blanket ω = b}

/-- Event where blanket and external coordinates take specified values. -/
def blanketExternalSet (π : BlanketProjection Ω Internal Blanket External)
    (b : Blanket) (e : External) : Set Ω :=
  {ω | π.blanket ω = b ∧ π.external ω = e}

/-- Blanket event. -/
def blanketSet (π : BlanketProjection Ω Internal Blanket External)
    (b : Blanket) : Set Ω :=
  {ω | π.blanket ω = b}

/-- Measure-theoretic conditional independence as blanket factorization. -/
def CondIndepGivenBlanket
    (P : ProbabilityMeasure Ω)
    (π : BlanketProjection Ω Internal Blanket External) : Prop :=
  ∀ (i : Internal) (b : Blanket) (e : External),
    (P : Measure Ω) (atomSet π i b e) * (P : Measure Ω) (blanketSet π b) =
    (P : Measure Ω) (internalBlanketSet π i b) *
      (P : Measure Ω) (blanketExternalSet π b e)

/-- Ledger-boundary sparsity on the measure surface: the measure has the
blanket factorization. In later work this can be derived from a concrete
recognition-field generator; here it is the exact hypothesis needed for
conditional independence. -/
def LedgerBoundarySparsity
    (P : ProbabilityMeasure Ω)
    (π : BlanketProjection Ω Internal Blanket External) : Prop :=
  ∀ (i : Internal) (b : Blanket) (e : External),
    (P : Measure Ω) (atomSet π i b e) * (P : Measure Ω) (blanketSet π b) =
    (P : Measure Ω) (internalBlanketSet π i b) *
      (P : Measure Ω) (blanketExternalSet π b e)

theorem ledger_sparsity_implies_measure_condIndep
    (P : ProbabilityMeasure Ω)
    (π : BlanketProjection Ω Internal Blanket External)
    (h : LedgerBoundarySparsity P π) :
    CondIndepGivenBlanket P π := by
  exact h

/-- Product form of conditional independence. This is the event-level
conditional-independence identity, kept in multiplication form to avoid
division side conditions in `ENNReal`. -/
theorem conditional_product_form
    (P : ProbabilityMeasure Ω)
    (π : BlanketProjection Ω Internal Blanket External)
    (h : CondIndepGivenBlanket P π)
    (i : Internal) (b : Blanket) (e : External) :
    (P : Measure Ω) (atomSet π i b e) * (P : Measure Ω) (blanketSet π b) =
    (P : Measure Ω) (internalBlanketSet π i b) *
      (P : Measure Ω) (blanketExternalSet π b e) := by
  exact h i b e

structure NESSMeasureCert where
  conditional_independence :
    ∀ {Ω I B E : Type*} [MeasurableSpace Ω]
      (P : ProbabilityMeasure Ω) (π : BlanketProjection Ω I B E),
      LedgerBoundarySparsity P π → CondIndepGivenBlanket P π
  conditional_product :
    ∀ {Ω I B E : Type*} [MeasurableSpace Ω]
      (P : ProbabilityMeasure Ω) (π : BlanketProjection Ω I B E)
      (h : CondIndepGivenBlanket P π)
      (i : I) (b : B) (e : E),
      (P : Measure Ω) (atomSet π i b e) * (P : Measure Ω) (blanketSet π b) =
      (P : Measure Ω) (internalBlanketSet π i b) *
        (P : Measure Ω) (blanketExternalSet π b e)

theorem nessMeasureCert_holds : NESSMeasureCert :=
{ conditional_independence := @ledger_sparsity_implies_measure_condIndep
  conditional_product := @conditional_product_form }

end

end IndisputableMonolith.Information.NESSConditionalIndependenceMeasure
