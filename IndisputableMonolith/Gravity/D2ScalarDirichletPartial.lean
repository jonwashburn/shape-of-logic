import IndisputableMonolith.Gravity.D2ScalarDirichletQuadratureLimit

namespace IndisputableMonolith
namespace Gravity
namespace D2ScalarDirichletPartial

open PhysicalSixTetCubicDirichletInstance
open D2QuadratureInstances
open D2ScalarDirichletQuadratureLimit
open D2ScopingAudit
open Geometry.ReggeTriangulation3D
open Geometry.ReggeHessian3D
open Geometry.Triangulation3DConsistency
open Geometry.ReggeActionConcrete
open Geometry.PeriodicFreudenthalTorus

noncomputable section

-- §1. The abstract equivalence
theorem scalar_dirichlet_limit_nonempty_iff_tendsto
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ)
    (g : ρ → ℝ)
    (hg : ∀ r : ρ, (F.slice r).quadratureIntegral = g r) :
    Nonempty (ScalarDirichletEnergyLimit F refinementFilter continuumIntegral) ↔
    Filter.Tendsto g refinementFilter (nhds continuumIntegral) := by
  constructor
  · intro h
    obtain ⟨H⟩ := h
    have heq : g = H.scalarEnergy := by
      funext r
      exact (hg r).symm.trans (H.proxy_eq r)
    rw [heq]
    exact H.tendsto
  · intro h
    refine ⟨?_⟩
    exact { scalarEnergy := g, proxy_eq := hg, tendsto := h }

-- §2. The constructive direction
noncomputable def scalarDirichletLimitOfTendsto
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ)
    (g : ρ → ℝ)
    (hg : ∀ r : ρ, (F.slice r).quadratureIntegral = g r)
    (htendsto : Filter.Tendsto g refinementFilter (nhds continuumIntegral)) :
    ScalarDirichletEnergyLimit F refinementFilter continuumIntegral :=
  { scalarEnergy := g, proxy_eq := hg, tendsto := htendsto }

-- §3. The equivalence for the quadrature integral sequence
theorem scalar_dirichlet_limit_iff_quadrature_tendsto
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ) :
    Nonempty (ScalarDirichletEnergyLimit F refinementFilter continuumIntegral) ↔
    Filter.Tendsto (fun r => (F.slice r).quadratureIntegral) refinementFilter (nhds continuumIntegral) := by
  exact scalar_dirichlet_limit_nonempty_iff_tendsto F refinementFilter continuumIntegral
    (fun r => (F.slice r).quadratureIntegral) (fun r => rfl)

-- §4. The uniform-probe identification
theorem uniform_probe_quadratureIntegral_eq_scaled_dirichlet
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (r : ρ) :
    letI : NeZero (F.slice r).Nx := (F.slice r).instNx
    letI : NeZero (F.slice r).Ny := (F.slice r).instNy
    letI : NeZero (F.slice r).Nz := (F.slice r).instNz
    ∀ ξ : VertexPotential
        (canonicalEncodedPeriodicFreudenthalTorus (F.slice r).Nx (F.slice r).Ny (F.slice r).Nz
          (F.slice r).hx (F.slice r).hy (F.slice r).hz).K,
      (∀ τ : Fin (Fintype.card (PeriodicTet (F.slice r).Nx (F.slice r).Ny (F.slice r).Nz)),
        (F.slice r).data.tetProbe (tetFinEquiv (F.slice r).Nx (F.slice r).Ny (F.slice r).Nz τ) = ξ) →
      (F.slice r).quadratureIntegral =
        (Fintype.card (PeriodicTet (F.slice r).Nx (F.slice r).Ny (F.slice r).Nz) : ℝ) *
          ((F.slice r).data.limitCellVolume / 6) *
          ((1 / 2) *
            canonicalDirichletEnergy
              (canonicalEncodedPeriodicFreudenthalTorus (F.slice r).Nx (F.slice r).Ny (F.slice r).Nz
                (F.slice r).hx (F.slice r).hy (F.slice r).hz).K
              (canonicalEncodedPeriodicFreudenthalTorus (F.slice r).Nx (F.slice r).Ny (F.slice r).Nz
                (F.slice r).hx (F.slice r).hy (F.slice r).hz).hK
              ξ) := by
  exact quadratureIntegral_of_uniform_probe (F.slice r)

-- §5. The combined reduction for uniform-probe families
theorem uniform_probe_scalar_dirichlet_limit_iff_quadrature_tendsto
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ)
    (huniform : ∀ r : ρ,
      letI : NeZero (F.slice r).Nx := (F.slice r).instNx
      letI : NeZero (F.slice r).Ny := (F.slice r).instNy
      letI : NeZero (F.slice r).Nz := (F.slice r).instNz
      ∃ ξ : VertexPotential
          (canonicalEncodedPeriodicFreudenthalTorus (F.slice r).Nx (F.slice r).Ny (F.slice r).Nz
            (F.slice r).hx (F.slice r).hy (F.slice r).hz).K,
        ∀ τ : Fin (Fintype.card (PeriodicTet (F.slice r).Nx (F.slice r).Ny (F.slice r).Nz)),
          (F.slice r).data.tetProbe (tetFinEquiv (F.slice r).Nx (F.slice r).Ny (F.slice r).Nz τ) = ξ) :
    Nonempty (ScalarDirichletEnergyLimit F refinementFilter continuumIntegral) ↔
    Filter.Tendsto (fun r => (F.slice r).quadratureIntegral) refinementFilter (nhds continuumIntegral) := by
  -- For uniform-probe families, quadratureIntegral_of_uniform_probe (via
  -- uniform_probe_quadratureIntegral_eq_scaled_dirichlet) rewrites the proxy
  -- as the scaled Dirichlet energy. The equivalence then follows from
  -- scalar_dirichlet_limit_nonempty_iff_tendsto.
  exact scalar_dirichlet_limit_nonempty_iff_tendsto F refinementFilter continuumIntegral
    (fun r => (F.slice r).quadratureIntegral) (fun r => rfl)

end

end D2ScalarDirichletPartial
end Gravity
end IndisputableMonolith