import IndisputableMonolith.Mathematics.HodgeDeltaBridge.FullTargetStatement

/-!
# δ-Hodge Bridge: full-target equation selector

This module gives the current strongest honest closure criterion.  It is no
longer enough to select a convenient cycle-class target.  A selector must work
for an explicitly supplied full rational Hodge target `H`, and must produce
finite homogeneous equation-cut certificates for every class in `H`.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement

universe u

/-- Full-target equation selector for one `(X,p,H)`: a fixed cycle-class map into
the full target and equation-cut certificates for every class in that target. -/
structure FullTargetEquationSelector
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (H : FullRationalHodgeTarget X p) where
  map : FullTargetCycleClassMap H
  select : H.hodgeClass → EquationFiniteCertificate X p
  displays :
    ∀ α : H.hodgeClass,
      CertificateDisplaysClass
        map.cl
        ((select α).toFiniteCertificate)
        (H.toRationalHodgeClass α)

/-- A full-target equation selector proves the full-target Hodge statement for
that specific `(X,p,H)`. -/
theorem full_target_hodge_from_equation_selector
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {H : FullRationalHodgeTarget X p}
    (S : FullTargetEquationSelector H) :
    ∀ α : H.hodgeClass,
      ∃ Z : AlgebraicCycle.{u, u} X p,
        Nonempty (CycleClassEquals S.map.cl Z (H.toRationalHodgeClass α)) := by
  intro α
  exact certificate_display_has_cycle
    S.map.cl
    (H.toRationalHodgeClass α)
    ((S.select α).toFiniteCertificate)
    (S.displays α)

/-- Global full-target equation selector: every supplied full Hodge target has a
selector. -/
structure GlobalFullTargetEquationSelector where
  selector :
    ∀ (X : SmoothProjectiveComplexVariety.{u})
      (p : ℕ)
      (H : FullRationalHodgeTarget X p),
      FullTargetEquationSelector H

/-- A global full-target equation selector proves the strengthened full-target
rational Hodge statement. -/
theorem full_target_hodge_from_global_equation_selector
    (G : GlobalFullTargetEquationSelector.{u}) :
    hodge_conjecture_unconditional_full_target.{u} := by
  intro X p H
  let S := G.selector X p H
  refine ⟨S.map, ?_⟩
  intro α
  exact full_target_hodge_from_equation_selector S α

/-- Current strongest sufficient criterion: construct a global full-target
equation selector and the strengthened Hodge target follows. -/
theorem global_full_target_equation_selector_is_sufficient :
    Nonempty (GlobalFullTargetEquationSelector.{u}) →
      hodge_conjecture_unconditional_full_target.{u} := by
  intro h
  rcases h with ⟨G⟩
  exact full_target_hodge_from_global_equation_selector G

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

