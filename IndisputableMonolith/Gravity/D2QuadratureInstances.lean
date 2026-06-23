import IndisputableMonolith.Gravity.D2DampedScheduleClosure

/-!
# D2 Quadrature Instances: the Flat Sector Closes, the Curved Sector Reduces

## Status: THEOREM (0 sorry, 0 RS-internal axiom)

## What this module adds on top of `D2DampedScheduleClosure`

The damped-schedule closure discharged the uniform-residual input of the D2
reduction.  The remaining analytic input is the cross-cardinality quadrature
limit (`D2QuadratureConvergenceTarget`).  This module does two things to it.

**1. The flat sector closes unconditionally.**  Flattening a family
(replacing every tetrahedron probe by the zero potential) makes every slice
quadrature proxy exactly zero, because the canonical Dirichlet energy of the
zero potential vanishes.  The quadrature target then holds at the flat
continuum integral `0` with no hypothesis, and combining with the damped
residual closure gives `dampedFlat_fullReggeProduct_tendsto_zero`: the full
nonlinear Regge aggregate of the damped flat family converges to the flat
Einstein-Hilbert value on the product filter, with **both** former analytic
fields proved.  `dampedFlatProductFilterData` is the first D2 master datum in
the library whose `quadrature_tendsto` and `uniform_residual` fields are both
theorems, consuming only the Track 1.B local-correspondence data that every
slice carries by definition.

**2. The curved sector reduces to a scalar Dirichlet limit.**  For a slice
whose tetrahedron probes are all equal to one global potential `ξ`, the
quadrature proxy collapses by translation counting to

  `(card tets) · (V/6) · (½ · DirichletEnergy ξ)`,

so the cross-cardinality quadrature target is equivalent, for uniform-probe
families, to convergence of an explicit scalar sequence of scaled Dirichlet
energies (`quadrature_target_iff_of_proxy_eq` +
`quadratureIntegral_of_uniform_probe`).  The open D2 quadrature input is
thereby no longer an abstract `Tendsto` of opaque proxies: it is a concrete
numerical limit of finite graph-Dirichlet energies.

## What remains open

* The scalar Dirichlet limit itself for curvature-bearing probe families
  (the genuine Riemann-sum content of D2).
* The Track 1.B local correspondence at each cardinality (`hLocal`), carried
  by slices as before.
* Non-product, non-flat admissible triangulations.
-/

namespace IndisputableMonolith
namespace Gravity
namespace D2QuadratureInstances

open PhysicalSixTetCubicDirichletInstance
open D2DampedScheduleClosure
open Geometry.ReggeTriangulation3D
open Geometry.ReggeHessian3D
open Geometry.Triangulation3DConsistency
open Geometry.ReggeActionConcrete
open Geometry.PeriodicFreudenthalTorus

noncomputable section

/-! ## §1. The canonical Dirichlet energy of the zero potential vanishes -/

theorem canonicalDirichletEnergy_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    canonicalDirichletEnergy K hK (zeroPotential K) = 0 := by
  unfold canonicalDirichletEnergy zeroPotential
  simp

/-! ## §2. Flattening a slice: zero probes, everything else unchanged -/

/-- The flattened slice: same cardinality, local correspondence, cell-volume
and spacing schedules; every tetrahedron probe replaced by the zero
potential. -/
noncomputable def flattenSlice
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    CanonicalPeriodicTetSixTetVolumeQuadratureSlice l :=
  { Nx := S.Nx
    Ny := S.Ny
    Nz := S.Nz
    instNx := S.instNx
    instNy := S.instNy
    instNz := S.instNz
    hx := S.hx
    hy := S.hy
    hz := S.hz
    hLocal := S.hLocal
    data :=
      letI : NeZero S.Nx := S.instNx
      letI : NeZero S.Ny := S.instNy
      letI : NeZero S.Nz := S.instNz
      { limitCellVolume := S.data.limitCellVolume
        cellVolume := S.data.cellVolume
        cellVolume_tendsto := S.data.cellVolume_tendsto
        tetProbe := fun _ =>
          zeroPotential
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
        spacing := S.data.spacing
        spacing_tendsto_zero := S.data.spacing_tendsto_zero
        spacing_eventually_ne_zero := S.data.spacing_eventually_ne_zero } }

/-- The flattened slice's quadrature proxy is exactly zero. -/
theorem flattenSlice_quadratureIntegral
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    (flattenSlice S).quadratureIntegral = 0 := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  have h : (flattenSlice S).quadratureIntegral =
      ∑ τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)),
        canonicalPeriodicFreudenthalTetVolumeWeight S.Nx S.Ny S.Nz
            S.data.limitCellVolume (tetFinEquiv S.Nx S.Ny S.Nz τ) *
          ((1 / 2) *
            canonicalDirichletEnergy
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
              (zeroPotential
                (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K)) :=
    rfl
  rw [h]
  simp [canonicalDirichletEnergy_zero]

/-! ## §3. The flattened family and its quadrature target at zero -/

/-- Flatten every slice of a family. -/
noncomputable def flatFamily
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ) :
    CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ where
  slice := fun r => flattenSlice (F.slice r)

/-- **The flat-sector quadrature target holds with no hypothesis.**  The
flattened family's quadrature proxies are identically zero, so they converge
to the flat continuum Einstein-Hilbert value `0` along every refinement
filter. -/
theorem flatFamily_quadrature_target
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) :
    CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
      (flatFamily F) refinementFilter 0 := by
  unfold CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
  have h : (fun r : ρ => ((flatFamily F).slice r).quadratureIntegral) =
      fun _ : ρ => (0 : ℝ) := by
    funext r
    exact flattenSlice_quadratureIntegral (F.slice r)
  rw [h]
  exact tendsto_const_nhds

/-- The flat-sector quadrature target in the audit's vocabulary. -/
theorem d2_quadrature_target_flat
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) :
    D2ScopingAudit.D2QuadratureConvergenceTarget l (flatFamily F) refinementFilter 0 :=
  flatFamily_quadrature_target F refinementFilter

/-! ## §4. The unconditional flat-sector closure -/

/-- **FLAT-SECTOR D2 CLOSURE (no supplied analytic inputs).**  For every
slice family and every universal schedule, the full nonlinear Regge aggregate
of the damped flattened family converges to the flat continuum value `0` on
the product filter.  Both former analytic inputs are theorems here: the
quadrature target by §3, the uniform residual by the damped-schedule
closure.  The only data consumed are the slices themselves, including the
Track 1.B local correspondence they carry by definition. -/
theorem dampedFlat_fullReggeProduct_tendsto_zero
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
  dampedFamily_fullReggeProduct_tendsto_continuum (flatFamily F) σ hσ0 hσne
    refinementFilter 0 (flatFamily_quadrature_target F refinementFilter)

/-- The first D2 master datum whose `quadrature_tendsto` and
`uniform_residual` fields are both proved rather than supplied. -/
noncomputable def dampedFlatProductFilterData
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (refinementFilter : Filter ρ) :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l :=
  dampedProductFilterData (flatFamily F) σ hσ0 hσne refinementFilter 0
    (flatFamily_quadrature_target F refinementFilter)

/-- The flat datum satisfies the Track 1.B-PHY concrete product-filter target
consumed by the quantum-gravity master theorem. -/
theorem dampedFlatProductFilterData_satisfies_master_target
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (refinementFilter : Filter ρ) :
    Track1BCPhysicalResidual.PhysicalReggeEHConcreteProductFilterTarget
      (dampedFlatProductFilterData F σ hσ0 hσne refinementFilter) :=
  Track1BCPhysicalResidual.physicalReggeEHConcreteProductFilterTarget_holds
    (dampedFlatProductFilterData F σ hσ0 hσne refinementFilter)

/-! ## §5. Uniform-probe slices: the quadrature proxy is a scaled Dirichlet
energy -/

/-- For a slice whose tetrahedron probes are all the same global potential,
the quadrature proxy collapses to tetrahedron count times limiting cell
weight times the Dirichlet limit action of that potential. -/
theorem quadratureIntegral_of_uniform_probe
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    letI : NeZero S.Nx := S.instNx
    letI : NeZero S.Ny := S.instNy
    letI : NeZero S.Nz := S.instNz
    ∀ ξ : VertexPotential
        (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K,
      (∀ τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)),
        S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ) = ξ) →
      S.quadratureIntegral =
        (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz) : ℝ) *
          (S.data.limitCellVolume / 6) *
          ((1 / 2) *
            canonicalDirichletEnergy
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
              ξ) := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  intro ξ hξ
  have h : S.quadratureIntegral =
      ∑ τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)),
        canonicalPeriodicFreudenthalTetVolumeWeight S.Nx S.Ny S.Nz
            S.data.limitCellVolume (tetFinEquiv S.Nx S.Ny S.Nz τ) *
          ((1 / 2) *
            canonicalDirichletEnergy
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
              (S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ))) := rfl
  rw [h]
  have hterm : ∀ τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)),
      canonicalPeriodicFreudenthalTetVolumeWeight S.Nx S.Ny S.Nz
          S.data.limitCellVolume (tetFinEquiv S.Nx S.Ny S.Nz τ) *
        ((1 / 2) *
          canonicalDirichletEnergy
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
            (S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ))) =
        S.data.limitCellVolume / 6 *
          ((1 / 2) *
            canonicalDirichletEnergy
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
              ξ) := by
    intro τ
    rw [hξ τ]
    simp only [canonicalPeriodicFreudenthalTetVolumeWeight]
  rw [Finset.sum_congr rfl fun τ _ => hterm τ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Transport the cross-cardinality quadrature target along any explicit
formula for the slice proxies.  Together with
`quadratureIntegral_of_uniform_probe`, this turns the open D2 quadrature
input for uniform-probe families into a scalar limit of scaled Dirichlet
energies. -/
theorem quadrature_target_iff_of_proxy_eq
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ)
    (g : ρ → ℝ)
    (hg : ∀ r : ρ, (F.slice r).quadratureIntegral = g r) :
    CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
      F refinementFilter continuumIntegral ↔
      Filter.Tendsto g refinementFilter (nhds continuumIntegral) := by
  unfold CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
  exact Filter.tendsto_congr hg

/-! ## §6. One-statement bundle -/

/-- **D2 status after this module, in one statement.**  For every slice
family `F` and universal schedule `σ`: the flattened family's quadrature
target holds at the flat value `0` with no hypothesis; the damped flattened
family's residual target holds with no hypothesis; and the full nonlinear
Regge aggregate of the damped flattened family converges to `0` on the
product filter.  The flat sector of D2 is closed end to end on the canonical
route, with no supplied analytic field anywhere. -/
theorem d2_flat_sector_one_statement
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (refinementFilter : Filter ρ) :
    D2ScopingAudit.D2QuadratureConvergenceTarget l (flatFamily F) refinementFilter 0 ∧
    D2ScopingAudit.D2ResidualVanishingTarget l (dampedFamily (flatFamily F) σ hσ0 hσne)
      refinementFilter ∧
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) (dampedFamily (flatFamily F) σ hσ0 hσne))
      (refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds 0) :=
  ⟨d2_quadrature_target_flat F refinementFilter,
   d2_residual_vanishing_target_damped (flatFamily F) σ hσ0 hσne refinementFilter,
   dampedFlat_fullReggeProduct_tendsto_zero F σ hσ0 hσne refinementFilter⟩

end

end D2QuadratureInstances
end Gravity
end IndisputableMonolith
