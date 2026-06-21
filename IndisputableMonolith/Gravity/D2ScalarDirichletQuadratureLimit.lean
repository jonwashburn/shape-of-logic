import IndisputableMonolith.Gravity.D2QuadratureInstances

/-!
# D2 Scalar Dirichlet Quadrature Limit: the Curvature-Bearing Conditional

## Status: THEOREM (0 gaps, 0 RS-internal axiom) for what is claimed; the
## scalar Dirichlet limit for curvature-bearing probes remains the named open
## analytic input.

## What this module adds

This module makes the sharpest honest progress on the remaining open D2
quadrature target: the curvature-bearing scalar graph-Dirichlet quadrature
limit flagged by `D2ScopingAudit` as the sole remaining analytic input after
the damped-schedule residual closure.

**The conditional implication (proved).**  We define
`ScalarDirichletEnergyLimit`, a clearly-named structure packaging the scalar
Dirichlet energy limit hypothesis: a scalar energy function `g : ρ → ℝ`
connected to the quadrature proxies by `proxy_eq` and converging to the
continuum integral by `tendsto`.  We prove that this hypothesis implies the
D2 quadrature convergence target
(`scalar_dirichlet_limit_implies_d2_quadrature_target`), using the
proxy-transport theorem `D2QuadratureInstances.quadrature_target_iff_of_proxy_eq`.

**Combination with the damped-schedule closure (proved).**  Since
`D2DampedScheduleClosure.dampedFamily_fullReggeProduct_tendsto_continuum`
consumes the quadrature target for the original family and discharges the
residual target internally for damped schedules, the scalar Dirichlet energy
limit alone suffices for the full D2 product-filter convergence
(`scalar_limit_and_damped_implies_full_convergence`).

**The flat case as a trivial scalar limit (proved).**  The flat family
(zero probes) satisfies `ScalarDirichletEnergyLimit` at zero trivially
(`flatFamily_scalarDirichletLimit`), recovering the flat-sector quadrature
target and full product-filter convergence via the scalar Dirichlet route
(`flatFamily_quadrature_target_via_scalar_limit`,
`dampedFlat_fullReggeProduct_tendsto_zero_via_scalar_limit`).

## What remains open

The `tendsto` field of `ScalarDirichletEnergyLimit` for curvature-bearing
uniform-probe families — the concrete numerical limit of finite
graph-Dirichlet energies — is the genuine Riemann-sum content of D2 and is
not proved here.  For uniform-probe slices, the `proxy_eq` field is
discharged by `D2QuadratureInstances.quadratureIntegral_of_uniform_probe`,
which collapses the quadrature proxy to
`(card tets) · (V/6) · (½ · DirichletEnergy ξ)`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace D2ScalarDirichletQuadratureLimit

open PhysicalSixTetCubicDirichletInstance
open D2QuadratureInstances
open D2ScopingAudit
open D2DampedScheduleClosure

noncomputable section

/-! ## §1. The scalar Dirichlet energy limit hypothesis -/

/-- The scalar Dirichlet energy limit hypothesis for a quadrature refinement
family.  This packages the explicit numerical limit of finite graph-Dirichlet
energies that the D2 quadrature target reduces to for uniform-probe families.

For uniform-probe families, the `proxy_eq` field is discharged by
`D2QuadratureInstances.quadratureIntegral_of_uniform_probe`, which collapses
the quadrature proxy to `(card tets) · (V/6) · (½ · DirichletEnergy ξ)`.
The `tendsto` field is then the concrete scalar Dirichlet energy limit — the
genuine Riemann-sum content of D2 that remains open for curvature-bearing
probes. -/
structure ScalarDirichletEnergyLimit
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ) where
  /-- The scalar energy function: typically the scaled Dirichlet energy of
  the uniform probe at each refinement. -/
  scalarEnergy : ρ → ℝ
  /-- The scalar energy computes the quadrature proxy at each refinement.
  For uniform-probe slices, this is `quadratureIntegral_of_uniform_probe`. -/
  proxy_eq : ∀ r : ρ, (F.slice r).quadratureIntegral = scalarEnergy r
  /-- The scalar Dirichlet energies converge to the continuum integral.
  This is the open analytic input for curvature-bearing probe families. -/
  tendsto : Filter.Tendsto scalarEnergy refinementFilter (nhds continuumIntegral)

/-! ## §2. The main conditional implication -/

/-- **The scalar Dirichlet energy limit implies the D2 quadrature convergence
target.**  This is the sharpest honest conditional implication for the
curvature-bearing sector: if a scalar sequence of graph-Dirichlet energies
(connected to the quadrature proxies by `proxy_eq`) converges to the
continuum integral, then the D2 quadrature convergence target holds.

Combined with the damped-schedule residual closure
(`D2DampedScheduleClosure`), this reduces the full D2 product-filter
convergence to the scalar Dirichlet energy limit alone (see
`scalar_limit_and_damped_implies_full_convergence`).

The scalar limit itself for curvature-bearing probes remains the open
analytic content of D2. -/
theorem scalar_dirichlet_limit_implies_d2_quadrature_target
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ)
    (H : ScalarDirichletEnergyLimit F refinementFilter continuumIntegral) :
    D2ScopingAudit.D2QuadratureConvergenceTarget l F refinementFilter continuumIntegral :=
  (quadrature_target_iff_of_proxy_eq
    F refinementFilter continuumIntegral H.scalarEnergy H.proxy_eq).mpr H.tendsto

/-! ## §3. Combination with the damped-schedule closure -/

/-- **The scalar Dirichlet energy limit plus the damped schedule implies full
D2 product-filter convergence.**  Since the damped-schedule closure
discharges the uniform residual target unconditionally for damped schedules
(via `dampedFamily_fullReggeProduct_tendsto_continuum`), the scalar
Dirichlet energy limit alone suffices for the full nonlinear Regge aggregate
to converge to the continuum Einstein-Hilbert/Dirichlet integral on the
product filter.

This is the sharpest reduction of D2 to a single analytic input: the scalar
graph-Dirichlet energy limit for curvature-bearing probe families. -/
theorem scalar_limit_and_damped_implies_full_convergence
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ)
    (H : ScalarDirichletEnergyLimit F refinementFilter continuumIntegral) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) (dampedFamily F σ hσ0 hσne))
      (refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds continuumIntegral) :=
  dampedFamily_fullReggeProduct_tendsto_continuum F σ hσ0 hσne
    refinementFilter continuumIntegral
    (scalar_dirichlet_limit_implies_d2_quadrature_target F refinementFilter
      continuumIntegral H)

/-! ## §4. The flat case as a trivial scalar limit -/

/-- The flat family satisfies the scalar Dirichlet energy limit at zero:
the scalar energy is identically zero (the Dirichlet energy of the zero
potential vanishes), and zero converges to zero. -/
noncomputable def flatFamily_scalarDirichletLimit
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) :
    ScalarDirichletEnergyLimit (flatFamily F) refinementFilter 0 where
  scalarEnergy := fun _ => 0
  proxy_eq := by
    intro r
    exact flattenSlice_quadratureIntegral (F.slice r)
  tendsto := tendsto_const_nhds

/-- The flat-sector quadrature target follows from the scalar limit
hypothesis, recovering `D2QuadratureInstances.flatFamily_quadrature_target`
via the scalar Dirichlet route. -/
theorem flatFamily_quadrature_target_via_scalar_limit
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) :
    D2ScopingAudit.D2QuadratureConvergenceTarget l (flatFamily F) refinementFilter 0 :=
  scalar_dirichlet_limit_implies_d2_quadrature_target (flatFamily F) refinementFilter 0
    (flatFamily_scalarDirichletLimit F refinementFilter)

/-- The flat-sector full product-filter convergence follows from the scalar
limit hypothesis, recovering
`D2QuadratureInstances.dampedFlat_fullReggeProduct_tendsto_zero` via the
scalar Dirichlet route. -/
theorem dampedFlat_fullReggeProduct_tendsto_zero_via_scalar_limit
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (refinementFilter : Filter ρ) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) (dampedFamily (flatFamily F) σ hσ0 hσne))
      (refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds 0) :=
  scalar_limit_and_damped_implies_full_convergence (flatFamily F) σ hσ0 hσne
    refinementFilter 0 (flatFamily_scalarDirichletLimit F refinementFilter)

end

end D2ScalarDirichletQuadratureLimit
end Gravity
end IndisputableMonolith