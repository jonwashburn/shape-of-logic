import IndisputableMonolith.Mathematics.HodgeDiffuseLocalization

/-!
# The diffuse Hodge obstruction in the algebraic quotient

This module makes the first quotient move in the Hodge calibration program.
It does not prove Hodge, and it does not assume the missing calibration lemma
under another name.

Given an additive group `Coh` of rational `(p,p)` classes and the subgroup `A`
of algebraic classes, the obstruction lives in the quotient `Coh ⧸ A`.  The
previous localization module proved that, after the Siu split, a class is
algebraic iff its diffuse residual is algebraic.  Here that statement is
rewritten as:

    Hodge iff every diffuse residual has zero image in `Coh ⧸ A`.

The final section introduces an abstract amortized calibration defect on this
quotient.  The only analytic input is named explicitly as
`CalibrationCompletionConservative`: the completion-side calibration functional
has zero amortized defect on the diffuse residual classes.  Turning that into a
zero quotient class also needs the hard coercivity statement:
nonzero diffuse quotient classes have positive amortized defect.  Neither
hypothesis is proved here.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDiffuseQuotient

open HodgeDiffuseLocalization

universe u

variable {Coh : Type u} [AddCommGroup Coh]

/-- The algebraic quotient of rational `(p,p)` classes by algebraic classes. -/
abbrev AlgebraicQuotient (A : AddSubgroup Coh) : Type u :=
  Coh ⧸ A

/-- The quotient class of a cohomology class modulo algebraic classes. -/
def quotientClass (A : AddSubgroup Coh) (x : Coh) : AlgebraicQuotient A :=
  QuotientAddGroup.mk x

/-- A class maps to zero in the algebraic quotient exactly when it is algebraic. -/
theorem quotientClass_eq_zero_iff_mem
    (A : AddSubgroup Coh) (x : Coh) :
    quotientClass A x = 0 ↔ x ∈ A := by
  change QuotientAddGroup.mk x = QuotientAddGroup.mk (0 : Coh) ↔ x ∈ A
  rw [QuotientAddGroup.eq]
  constructor
  · intro h
    have hxneg : -x ∈ A := by simpa using h
    simpa using A.neg_mem hxneg
  · intro hx
    have hxneg : -x ∈ A := A.neg_mem hx
    simpa using hxneg

/-- The diffuse residual class, viewed in the quotient by algebraic classes. -/
def diffuseResidualQuotient
    (A : AddSubgroup Coh) (S : SiuData Coh A) (α : Coh) : AlgebraicQuotient A :=
  quotientClass A (S.diffuse α)

/-- Per-class quotient localization: `α` is algebraic iff its diffuse residual is
zero in the quotient by algebraic classes. -/
theorem hodgeClass_iff_diffuseResidualQuotient_zero
    (A : AddSubgroup Coh) (S : SiuData Coh A) (α : Coh) :
    α ∈ A ↔ diffuseResidualQuotient A S α = 0 := by
  rw [hodge_iff_diffuse A (S.sum α) (S.analytic_mem α)]
  exact (quotientClass_eq_zero_iff_mem A (S.diffuse α)).symm

/-- Global quotient localization: rational Hodge for this abstract class group is
equivalent to every diffuse residual vanishing in `Coh ⧸ A`. -/
theorem hodge_iff_all_diffuseResidualQuotient_zero
    (A : AddSubgroup Coh) (S : SiuData Coh A) :
    (∀ α : Coh, α ∈ A) ↔
      (∀ α : Coh, diffuseResidualQuotient A S α = 0) := by
  constructor
  · intro h α
    exact (hodgeClass_iff_diffuseResidualQuotient_zero A S α).mp (h α)
  · intro h α
    exact (hodgeClass_iff_diffuseResidualQuotient_zero A S α).mpr (h α)

/-! ## Calibration defect on the quotient

The next definitions isolate the exact analytic input without proving it.  The
functional below is meant to model the amortized lattice defect
`inf_m defectZ(m*c)/m`, now pushed down to the algebraic quotient.
-/

/-- A quotient-level calibration defect ledger.  In geometry, `amortizedDefect`
is the Kähler calibration defect after analytic completion and division by
positive multiples.

The dangerous field is `positive_on_nonzero_diffuse`: a nonzero diffuse residual
class in `Coh ⧸ A` has strictly positive amortized defect.  Proving this for the
actual Kähler calibration defect is the sharpened missing lemma. -/
structure QuotientCalibrationLedger
    (A : AddSubgroup Coh) (S : SiuData Coh A) where
  amortizedDefect : AlgebraicQuotient A → ℝ
  nonneg : ∀ q, 0 ≤ amortizedDefect q
  positive_on_nonzero_diffuse :
    ∀ α : Coh, diffuseResidualQuotient A S α ≠ 0 →
      0 < amortizedDefect (diffuseResidualQuotient A S α)

namespace QuotientCalibrationLedger

variable {A : AddSubgroup Coh} {S : SiuData Coh A}

/-- The diffuse residual of `α`, as seen by the quotient calibration ledger. -/
def diffuseResidual
    (_L : QuotientCalibrationLedger A S) (α : Coh) : AlgebraicQuotient A :=
  diffuseResidualQuotient A S α

/-- The named missing analytic hypothesis: analytic completion is conservative
for the Kähler calibration functional on the rational `(p,p)` locus, expressed
as zero amortized defect on every diffuse residual quotient class.

This is the formal counterpart of `inf_m defectZ(m*c)/m = 0`.  It is a
hypothesis, not a theorem in this module. -/
def CalibrationCompletionConservative
    (L : QuotientCalibrationLedger A S) : Prop :=
  ∀ α : Coh, L.amortizedDefect (L.diffuseResidual α) = 0

/-- The sharpened coercivity target: nonzero diffuse residual quotient classes
have positive amortized calibration defect.  This is just the dangerous field of
the ledger, exposed as a named proposition so downstream files can cite the real
missing lemma directly. -/
def PositiveDefectOnNonzeroDiffuse
    (L : QuotientCalibrationLedger A S) : Prop :=
  ∀ α : Coh, L.diffuseResidual α ≠ 0 →
    0 < L.amortizedDefect (L.diffuseResidual α)

/-- The ledger's hard field is exactly the sharpened missing lemma. -/
theorem positiveDefectOnNonzeroDiffuse
    (L : QuotientCalibrationLedger A S) :
    L.PositiveDefectOnNonzeroDiffuse := by
  intro α hne
  exact L.positive_on_nonzero_diffuse α hne

/-- On diffuse residual quotient classes, zero amortized defect forces zero
quotient class.  This is not a primitive assumption anymore; it is derived from
the sharper positivity statement. -/
theorem diffuseResidual_zero_of_zero_defect
    (L : QuotientCalibrationLedger A S) {α : Coh}
    (hzero : L.amortizedDefect (L.diffuseResidual α) = 0) :
    L.diffuseResidual α = 0 := by
  by_contra hne
  have hpos : 0 < L.amortizedDefect (L.diffuseResidual α) :=
    L.positiveDefectOnNonzeroDiffuse α hne
  linarith

/-- The missing analytic hypothesis kills each diffuse residual in the algebraic
quotient, provided nonzero diffuse quotient classes have positive defect. -/
theorem diffuseResidual_zero_of_calibrationCompletionConservative
    (L : QuotientCalibrationLedger A S)
    (hcons : L.CalibrationCompletionConservative) :
    ∀ α : Coh, L.diffuseResidual α = 0 := by
  intro α
  exact L.diffuseResidual_zero_of_zero_defect (hcons α)

/-- If the quotient calibration ledger is conservative on diffuse residuals, then
the abstract Hodge statement follows for the class group.  The proof is purely
algebraic after the explicitly named analytic hypothesis is supplied. -/
theorem hodge_of_calibrationCompletionConservative
    (L : QuotientCalibrationLedger A S)
    (hcons : L.CalibrationCompletionConservative) :
    ∀ α : Coh, α ∈ A := by
  exact (hodge_iff_all_diffuseResidualQuotient_zero A S).mpr
    (L.diffuseResidual_zero_of_calibrationCompletionConservative hcons)

/-- Under the positivity hypothesis packaged in the ledger, Hodge is equivalent
to calibration completion conservativity for diffuse residuals.  The reverse
direction is formal: if the residual is already zero in the quotient, its defect
is assumed zero by `zero_defect_at_zero`.  This does not assert that the
geometric defect has that property; it records the exact extra condition needed
for the equivalence. -/
theorem hodge_iff_calibrationCompletionConservative
    (L : QuotientCalibrationLedger A S)
    (zero_defect_at_zero : L.amortizedDefect 0 = 0) :
    (∀ α : Coh, α ∈ A) ↔ L.CalibrationCompletionConservative := by
  constructor
  · intro h α
    have hzero : L.diffuseResidual α = 0 :=
      (hodge_iff_all_diffuseResidualQuotient_zero A S).mp h α
    rw [hzero]
    exact zero_defect_at_zero
  · intro h
    exact L.hodge_of_calibrationCompletionConservative h

end QuotientCalibrationLedger

end HodgeDiffuseQuotient
end Mathematics
end IndisputableMonolith
