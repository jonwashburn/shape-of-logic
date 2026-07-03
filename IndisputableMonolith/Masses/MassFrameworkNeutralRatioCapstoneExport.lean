import Mathlib
import IndisputableMonolith.Masses.NeutralObservedRatioClosureCertificate

/-!
# Mass-framework neutral-ratio capstone export

`NeutralObservedRatioClosureCertificate` closes the neutral observed-ratio lane.
This module exports that capstone into the shared mass-framework observable
closure surface.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace MassFrameworkNeutralRatioCapstoneExport

open NeutralObservedRatioClosureCertificate
open NeutralBracketSourcedDressingClosure
open NeutralObservedRatioDressingEquation
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Exported neutral observed-ratio capstone for the mass-framework observable surface. -/
def massFrameworkNeutralRatioCapstoneExport : Prop :=
  neutralObservedRatioLaneClosed

theorem massFrameworkNeutralRatioCapstoneExport_holds :
    massFrameworkNeutralRatioCapstoneExport := by
  unfold massFrameworkNeutralRatioCapstoneExport
  exact neutralObservedRatioLaneClosed_holds

theorem massFrameworkNeutralRatioCapstoneExport_exact :
    dressedDeltaMsqRatio bracketSourcedDressingClosure = observedRatio :=
  dressedRatio_with_bracketSourcedClosure_eq_observed

theorem massFrameworkNeutralRatioCapstoneExport_eq_required :
    bracketSourcedDressingClosure = requiredNeutralDressing :=
  neutralObservedRatioClosure_eq_required

/-- Export certificate for the neutral observed-ratio capstone. -/
structure MassFrameworkNeutralRatioCapstoneExportCert where
  exported : massFrameworkNeutralRatioCapstoneExport
  exact_ratio : dressedDeltaMsqRatio bracketSourcedDressingClosure = observedRatio
  closure_eq_required : bracketSourcedDressingClosure = requiredNeutralDressing

theorem massFrameworkNeutralRatioCapstoneExportCert_holds :
    MassFrameworkNeutralRatioCapstoneExportCert where
  exported := massFrameworkNeutralRatioCapstoneExport_holds
  exact_ratio := massFrameworkNeutralRatioCapstoneExport_exact
  closure_eq_required := massFrameworkNeutralRatioCapstoneExport_eq_required

end

end MassFrameworkNeutralRatioCapstoneExport
end Masses
end IndisputableMonolith
