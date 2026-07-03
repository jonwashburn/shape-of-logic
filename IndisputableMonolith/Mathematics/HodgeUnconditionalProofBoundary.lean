import IndisputableMonolith.Mathematics.HodgeDiffuseQuotient

/-!
# Honest boundary for an unconditional Hodge proof

This module records the strongest proof that can be constructed from the current
non-vacuous quotient localization.

It does **not** prove Hodge.  It packages the exact remaining inputs:

* `positive_on_nonzero_diffuse`: nonzero diffuse quotient classes have positive
  amortized Kähler calibration defect;
* `CalibrationCompletionConservative`: every rational diffuse residual has zero
  amortized defect, equivalently `inf_m defectZ(m*c)/m = 0`;
* `zero_defect_at_zero`: the zero quotient class has zero defect.

With those inputs, Hodge follows by the algebra already proved in
`HodgeDiffuseQuotient`.  Without them, a file named "unconditional proof" would
only be using a weaker/vacuous statement of Hodge, such as a prover-chosen
cycle-class map.  This file therefore marks the proof boundary rather than
claiming a theorem the geometry has not supplied.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeUnconditionalProofBoundary

open HodgeDiffuseLocalization
open HodgeDiffuseQuotient

universe u

variable {Coh : Type u} [AddCommGroup Coh]

/-- A non-vacuous quotient-calibration interface for rational `(p,p)` classes.
The data are abstract, but the dependency order is the intended geometric one:
first the Siu split and algebraic quotient, then an amortized calibration defect
on the quotient, then the normalization at the zero class. -/
structure DiffuseCalibrationInterface (Coh : Type u) [AddCommGroup Coh] where
  algebraicClasses : AddSubgroup Coh
  siu : SiuData Coh algebraicClasses
  ledger : QuotientCalibrationLedger algebraicClasses siu
  zero_defect_at_zero : ledger.amortizedDefect 0 = 0

namespace DiffuseCalibrationInterface

/-- The abstract rational Hodge statement for this quotient interface. -/
def HodgeStatement (I : DiffuseCalibrationInterface Coh) : Prop :=
  ∀ α : Coh, α ∈ I.algebraicClasses

/-- The sharpened missing lemma in quotient form: analytic completion is
conservative for the Kähler calibration functional on every rational diffuse
residual. -/
def CalibrationConservativityTarget
    (I : DiffuseCalibrationInterface Coh) : Prop :=
  I.ledger.CalibrationCompletionConservative

/-- The coercivity half of the missing lemma, exposed with the interface names.
This is already a field of `I.ledger`; proving it for the actual geometric
defect is Hodge-level work. -/
def PositiveDefectOnNonzeroDiffuseTarget
    (I : DiffuseCalibrationInterface Coh) : Prop :=
  I.ledger.PositiveDefectOnNonzeroDiffuse

/-- The interface carries the sharpened positivity target as a named theorem,
because it is one of the explicit fields required to build the ledger. -/
theorem positiveDefectOnNonzeroDiffuseTarget
    (I : DiffuseCalibrationInterface Coh) :
    I.PositiveDefectOnNonzeroDiffuseTarget :=
  I.ledger.positiveDefectOnNonzeroDiffuse

/-- Exact non-vacuous reduction: for the quotient-calibration interface, rational
Hodge is equivalent to calibration conservativity for all diffuse residuals.
This is algebra plus the explicit positivity/zero-normalization interface, not a
geometric proof of the missing lemma. -/
theorem hodge_iff_calibrationConservativityTarget
    (I : DiffuseCalibrationInterface Coh) :
    I.HodgeStatement ↔ I.CalibrationConservativityTarget :=
  I.ledger.hodge_iff_calibrationCompletionConservative I.zero_defect_at_zero

/-- If the missing calibration conservativity target is supplied, the abstract
Hodge statement follows.  This is the honest conditional "full proof spine." -/
theorem hodge_of_calibrationConservativityTarget
    (I : DiffuseCalibrationInterface Coh)
    (hcons : I.CalibrationConservativityTarget) :
    I.HodgeStatement :=
  (I.hodge_iff_calibrationConservativityTarget).mpr hcons

end DiffuseCalibrationInterface

/-- A bundled set of inputs strong enough to close the quotient-localized Hodge
statement.  The last field is exactly the analytic theorem still missing. -/
structure HonestHodgeClosureInputs (Coh : Type u) [AddCommGroup Coh] where
  interface : DiffuseCalibrationInterface Coh
  calibration_conservative : interface.CalibrationConservativityTarget

/-- Final honest closure theorem for the current non-vacuous interface.  This is
not an unconditional Hodge theorem; it states precisely what remains to be proved
geometrically before the word "unconditional" is justified. -/
theorem hodge_from_honest_closure_inputs
    (H : HonestHodgeClosureInputs Coh) :
    H.interface.HodgeStatement :=
  H.interface.hodge_of_calibrationConservativityTarget H.calibration_conservative

end HodgeUnconditionalProofBoundary
end Mathematics
end IndisputableMonolith
