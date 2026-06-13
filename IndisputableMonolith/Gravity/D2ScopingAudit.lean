import IndisputableMonolith.Gravity.Track1BCPhysicalResidual
import IndisputableMonolith.Gravity.MasterTheoremUnconditional

/-!
# Gravity: Honest D2 (Regge → Einstein-Hilbert) Scoping Audit

## Status: THEOREM (0 sorry, 0 RS-internal axiom) for what is claimed; the
## open frontier is named, not asserted.

## What this module pins down (peer-review findings F2 / Rec 3)

The D2 classical-recovery witness consumed by the master theorem is
`MasterTheoremUnconditional.concretePhysicalRegEHContinuumProp`, namely

```
∀ D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData l, target D
```

and `physicalReggeEHConcreteProductFilterTarget_holds D` is discharged by
`D.fullReggeProduct_tendsto_continuum`.  Reading the structure
(`PhysicalSixTetCubicDirichletInstance`), the datum `D` carries **two
analytic hypothesis fields**:

* `quadrature_tendsto` — the canonical periodic six-tet quadrature rule
  converges to the continuum EH/Dirichlet integral, and
* `uniform_residual` — the (full nonlinear Regge − quadrature) residual is
  uniformly controlled on the product filter.

`fullReggeProduct_tendsto_continuum` is a genuine theorem: it combines those
two hypotheses by a triangle-inequality squeeze.  So the honest status of
D2 is a **reduction**, not a from-primitives closure:

> On the canonical periodic six-tet cubic torus, quadrature convergence plus
> a vanishing Regge-residual envelope imply full nonlinear Regge → continuum
> EH convergence on the product filter.

This module states that reduction cleanly (`d2_reduction`), discloses that
the D2 target is a real `Tendsto` convergence statement (not `True`), and
**names the precise remaining targets** so they are not hidden inside a
data structure.

## What is NOT proved (the actual open frontier)

1. `D2QuadratureConvergenceTarget` discharged from primitive mesh geometry
   for a concrete refinement family (currently a supplied field).
2. `D2ResidualVanishingTarget` discharged from a primitive curvature/spacing
   bound (currently a supplied field; the residual-envelope constructors in
   `PhysicalSixTetCubicDirichletInstance` reduce it to a vanishing envelope,
   but the envelope itself is still supplied).
3. Generalization beyond the canonical periodic, flat, product six-tet torus
   to physically admissible **non-product, non-flat** triangulations, with
   contracted second Bianchi closure on the same family.

Items 1-2 are analytic; item 3 is the load-bearing geometric problem
(F2).  None is asserted here.
-/

namespace IndisputableMonolith
namespace Gravity
namespace D2ScopingAudit

open PhysicalSixTetCubicDirichletInstance

/-! ## §1. Disclosure: the D2 target is a genuine convergence statement -/

/-- The D2 product-filter target is literally a `Filter.Tendsto` convergence
of the full nonlinear Regge aggregate to the continuum integral.  It is not
`True` and it does not mention the master conclusion. -/
theorem d2_target_is_convergence
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    Track1BCPhysicalResidual.PhysicalReggeEHConcreteProductFilterTarget D =
      Filter.Tendsto
        (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
          (α := α) (ρ := ρ) D.family)
        (D.refinementFilter ×ˢ l : Filter (ρ × α))
        (nhds D.continuumIntegral) := rfl

/-! ## §2. The precise remaining analytic targets, named -/

/-- **Remaining target 1 (quadrature convergence).**  The canonical periodic
six-tet quadrature rule converges to the continuum EH/Dirichlet integral on
the cross-cardinality product schedule.  Currently supplied as the
`quadrature_tendsto` field of the product-filter datum. -/
def D2QuadratureConvergenceTarget
    {α ρ : Type*} (l : Filter α)
    (family : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ) : Prop :=
  CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
    family refinementFilter continuumIntegral

/-- **Remaining target 2 (residual vanishing).**  The (full nonlinear Regge −
quadrature) residual is uniformly controlled on the product filter.
Currently supplied as the `uniform_residual` field. -/
def D2ResidualVanishingTarget
    {α ρ : Type*} (l : Filter α)
    (family : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) : Prop :=
  CanonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget
    family refinementFilter

/-! ## §3. The proved reduction -/

/-- **D2 REDUCTION THEOREM (what is actually proved).**  On the canonical
periodic six-tet cubic torus, the two named analytic targets — quadrature
convergence to the continuum integral and a vanishing Regge-residual — imply
that the full nonlinear Regge aggregate converges to the continuum
Einstein-Hilbert/Dirichlet integral on the product filter.

This is the honest content of the D2 master witness: convergence is reduced
to the two analytic inputs, which remain the open targets (§2).  It makes no
claim about non-product or non-flat triangulations. -/
theorem d2_reduction
    {α ρ : Type*} {l : Filter α}
    (family : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ)
    (hquad : D2QuadratureConvergenceTarget l family refinementFilter continuumIntegral)
    (hres : D2ResidualVanishingTarget l family refinementFilter) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) family)
      (refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds continuumIntegral) :=
  (CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData.fullReggeProduct_tendsto_continuum
    (α := α) (ρ := ρ) (l := l)
    { family := family
      refinementFilter := refinementFilter
      continuumIntegral := continuumIntegral
      quadrature_tendsto := hquad
      uniform_residual := hres })

/-- The reduction, packaged as a single implication for citation. -/
theorem d2_reduction_statement
    {α ρ : Type*} {l : Filter α}
    (family : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ) :
    D2QuadratureConvergenceTarget l family refinementFilter continuumIntegral →
    D2ResidualVanishingTarget l family refinementFilter →
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) family)
      (refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds continuumIntegral) :=
  fun hquad hres => d2_reduction family refinementFilter continuumIntegral hquad hres

/-! ## §4. Scope record -/

/-- Honest D2 scope: the reduction is proved; the two analytic inputs and the
general-triangulation extension are open. -/
structure D2ScopeStatus where
  reduction_proved : Bool
  quadrature_target_open : Bool
  residual_target_open : Bool
  general_triangulation_open : Bool

/-- The current D2 scope on the canonical periodic six-tet torus. -/
def d2ScopeStatus : D2ScopeStatus where
  reduction_proved := true
  quadrature_target_open := true
  residual_target_open := true
  general_triangulation_open := true

end D2ScopingAudit
end Gravity
end IndisputableMonolith
