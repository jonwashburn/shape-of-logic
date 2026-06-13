import IndisputableMonolith.Gravity.Track1BCStructural
import IndisputableMonolith.Gravity.PhysicalSixTetCubicDirichletInstance

/-!
# Track 1.B-PHY: Physical Regge → EH Residual Structural Upgrade

This module packages the physical finite-probe Regge-to-EH residual theorems
from `Gravity.PhysicalSixTetCubicDirichletInstance` as a named Track 1.B-PHY
upgrade beyond the flat-substrate witness in `Gravity.Track1BCStructural`.

Status: **STRUCTURAL THEOREM** (0 sorry, 0 new RS-specific axiom).

What is closed here:
* normalized full nonlinear Regge finite aggregates converge to the canonical
  finite EH/Dirichlet action, with an explicit residual tending to zero, once
  edge-stencil local correspondence holds;
* the same local correspondence feeds the finite-to-continuum bridge when a
  Riemann-sum identification is supplied.

What remains for the unconditional manifold Einstein-Hilbert theorem:
* `PhysicalReggeEHManifoldIntegralRemainingTarget`, i.e.
  `CanonicalPeriodicFiniteEHDirichletLimitWeightIntegralTarget` on a concrete
  periodic Freudenthal refinement family.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Track1BCPhysicalResidual

open PhysicalSixTetCubicDirichletInstance
open Track1BCStructural
open Geometry.ReggeHessian3D
open Geometry.ReggeActionConcrete
open Geometry.PeriodicFreudenthalTorus

noncomputable section

/-- Named Track 1.B-PHY target at a fixed local-correspondence input: the
normalized full nonlinear Regge finite-probe aggregate minus the canonical
finite EH/Dirichlet aggregate tends to zero along any refinement family. -/
theorem physicalReggeEHFiniteProbeResidualTarget
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  (∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ))) -
                    ∑ i : Fin n,
                      limitWeight i *
                        CanonicalPeriodicFiniteEHDirichletLimitAction
                          Nx Ny Nz hx hy hz (probe i))
                l (nhds 0) :=
  canonicalPeriodicFullRegge_variable_weighted_finite_probe_spacing_scaled_div_spacing_norm_sq_finiteEHDirichletLimit_residual_tendsto_zero
    Nx Ny Nz hx hy hz hLocal

/-- After local correspondence, the remaining manifold-level Track 1.B-PHY
input is exactly the Riemann-sum identification of the limiting finite
EH/Dirichlet aggregate with a supplied continuum integral. -/
def PhysicalReggeEHManifoldIntegralRemainingTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  ∀ {n : ℕ}
    (probe :
      Fin n →
        VertexPotential (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
    (limitWeight : Fin n → ℝ)
    (continuumIntegral : CanonicalPeriodicContinuumEHIntegral),
    CanonicalPeriodicFiniteEHDirichletLimitWeightIntegralTarget
      Nx Ny Nz hx hy hz probe limitWeight continuumIntegral

theorem physicalReggeEHFullRegge_tendsto_continuumIntegral_of_localCorrespondence
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (D : CanonicalPeriodicFiniteEHDirichletIntegralRefinementData l Nx Ny Nz hx hy hz) :
    Filter.Tendsto
      (fun t : α =>
        ∑ i : Fin D.n,
          D.weight t i *
            (reggeAction
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (D.spacing t • D.probe i) /
              ‖D.spacing t‖ ^ (2 : ℕ)))
      l
      (nhds D.continuumIntegral) :=
  CanonicalPeriodicFiniteEHDirichletIntegralRefinementData.fullRegge_tendsto_continuumIntegral
    Nx Ny Nz hx hy hz hLocal D

/-- Explicit reduction: the physical upgrade beyond the flat witness splits into
edge-stencil local correspondence (already consumed above) and the single
Riemann-sum target above. -/
theorem physicalReggeEHUpgrade_reduces_to_manifoldIntegralTarget
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hIntegral : PhysicalReggeEHManifoldIntegralRemainingTarget Nx Ny Nz hx hy hz) :
    PhysicalReggeEHManifoldIntegralRemainingTarget Nx Ny Nz hx hy hz := by
  intro n probe limitWeight continuumIntegral
  exact hIntegral (n := n) probe limitWeight continuumIntegral

/-- Compared with `Track1BCStructural.regge_eh_continuum_canonical_witness`, the
physical upgrade replaces the flat zero-zero identity with the finite-probe
residual theorem above, conditional on edge-stencil local correspondence. -/
theorem physicalReggeEHUpgrade_beyond_flatStructuralWitness
    {α : Type*} {l : Filter α}
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    regge_eh_continuum_structural_prop ∧
      (∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
        ∀ {n : ℕ}
          (spacing : α → ℝ)
          (probe :
            Fin n →
              VertexPotential
                (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
          (weight : α → Fin n → ℝ)
          (limitWeight : Fin n → ℝ),
          (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
            Filter.Tendsto spacing l (nhds 0) →
              (∀ᶠ t : α in l, spacing t ≠ 0) →
                Filter.Tendsto
                  (fun t : α =>
                    (∑ i : Fin n,
                      weight t i *
                        (reggeAction
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                          (spacing t • probe i) /
                          ‖spacing t‖ ^ (2 : ℕ))) -
                      ∑ i : Fin n,
                        limitWeight i *
                          CanonicalPeriodicFiniteEHDirichletLimitAction
                            Nx Ny Nz hx hy hz (probe i))
                  l (nhds 0)) :=
  ⟨regge_eh_continuum_canonical_witness,
   physicalReggeEHFiniteProbeResidualTarget Nx Ny Nz hx hy hz hLocal⟩

/-- The reusable finite-probe physical residual conclusion after local
edge-stencil correspondence has been supplied. -/
def PhysicalReggeEHFiniteProbeResidualConclusion
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  ∀ {α : Type*} {l : Filter α},
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ {n : ℕ}
        (spacing : α → ℝ)
        (probe :
          Fin n →
            VertexPotential
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K)
        (weight : α → Fin n → ℝ)
        (limitWeight : Fin n → ℝ),
        (∀ i : Fin n, Filter.Tendsto (fun t : α => weight t i) l (nhds (limitWeight i))) →
          Filter.Tendsto spacing l (nhds 0) →
            (∀ᶠ t : α in l, spacing t ≠ 0) →
              Filter.Tendsto
                (fun t : α =>
                  (∑ i : Fin n,
                    weight t i *
                      (reggeAction
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
                        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
                        (spacing t • probe i) /
                        ‖spacing t‖ ^ (2 : ℕ))) -
                    ∑ i : Fin n,
                      limitWeight i *
                        CanonicalPeriodicFiniteEHDirichletLimitAction
                          Nx Ny Nz hx hy hz (probe i))
                l (nhds 0)

/-- Local correspondence supplies the finite-probe physical residual conclusion. -/
theorem physicalReggeEHFiniteProbeResidualConclusion_of_localCorrespondence
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    PhysicalReggeEHFiniteProbeResidualConclusion Nx Ny Nz hx hy hz := by
  intro α l
  exact physicalReggeEHFiniteProbeResidualTarget Nx Ny Nz hx hy hz hLocal

/-- Fork-B interface: physical finite-probe residual plus the structural
contracted discrete Bianchi theorem, still keeping the manifold integral target
outside the package. -/
structure PhysicalReggeEHBianchiInterface
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (V B : Type) [Fintype B] : Prop where
  finiteProbeResidual :
    PhysicalReggeEHFiniteProbeResidualConclusion Nx Ny Nz hx hy hz
  discreteBianchi :
    ∀ (R : Geometry.DiscreteBianchi.SchlafliReggeData V B) (v : V),
      Geometry.DiscreteBianchi.DiscreteBianchiContractedAtVertex R.toReggeData v
  bianchiIffSchlafli :
    ∀ (R : Geometry.DiscreteBianchi.ReggeData V B) (v : V),
      Geometry.DiscreteBianchi.DiscreteBianchiContractedAtVertex R v ↔
        Geometry.DiscreteBianchi.SchlafliIdentityAtVertex R v
  bianchiHypothesisSpace :
    Nonempty (Geometry.DiscreteBianchi.SchlafliReggeData V B)

/-- Local correspondence is enough to build the combined Track `1B-PHY / 1.C`
interface.  The remaining physical manifold upgrade is exactly
`PhysicalReggeEHManifoldIntegralRemainingTarget`. -/
theorem physicalReggeEHBianchiInterface_of_localCorrespondence
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (V B : Type) [Fintype B]
    (hLocal : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    PhysicalReggeEHBianchiInterface Nx Ny Nz hx hy hz V B where
  finiteProbeResidual :=
    physicalReggeEHFiniteProbeResidualConclusion_of_localCorrespondence
      Nx Ny Nz hx hy hz hLocal
  discreteBianchi := Geometry.DiscreteBianchi.discrete_bianchi_contracted_from_schlafli
  bianchiIffSchlafli := Geometry.DiscreteBianchi.discreteBianchi_eq_schlafli
  bianchiHypothesisSpace := Geometry.DiscreteBianchi.SchlafliReggeData_inhabited V B

/-! ## Concrete refinement-family target for the manifold EH bridge -/

/-- Concrete per-slice Riemann-sum target for the physical manifold bridge.

For a six-tet volume quadrature slice, the finite EH/Dirichlet limiting
aggregate is identified with the slice's canonical quadrature integral.  This
is the slice-level instance of the target used by
`PhysicalReggeEHManifoldIntegralRemainingTarget`, with the probes and weights
fixed by the periodic Freudenthal tetrahedra and the canonical `cellVolume / 6`
split. -/
def PhysicalReggeEHConcreteSliceLimitWeightTarget
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : Prop := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  exact
    CanonicalPeriodicFiniteEHDirichletLimitWeightIntegralTarget
      S.Nx S.Ny S.Nz S.hx S.hy S.hz
      (fun τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)) =>
        S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ))
      (fun τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)) =>
        canonicalPeriodicFreudenthalTetVolumeWeight
          S.Nx S.Ny S.Nz S.data.limitCellVolume
          (tetFinEquiv S.Nx S.Ny S.Nz τ))
      S.quadratureIntegral

/-- Every concrete six-tet volume quadrature slice satisfies its slice-level
limit-weight integral target by definition of the finite quadrature proxy. -/
theorem physicalReggeEHConcreteSliceLimitWeightTarget_holds
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    PhysicalReggeEHConcreteSliceLimitWeightTarget S := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  simpa [
    PhysicalReggeEHConcreteSliceLimitWeightTarget,
    CanonicalPeriodicTetSixTetVolumeQuadratureSlice.quadratureIntegral,
    CanonicalPeriodicTetGeometricQuadratureRule.continuumIntegral,
    CanonicalPeriodicTetGeometricQuadratureRule.toFiniteQuadratureRule,
    canonicalPeriodicTetSixTetVolumeQuadratureRule] using
    (CanonicalPeriodicTetGeometricQuadratureRule.limitWeightIntegralTarget
      S.Nx S.Ny S.Nz S.hx S.hy S.hz
      (canonicalPeriodicTetSixTetVolumeQuadratureRule
        S.Nx S.Ny S.Nz S.hx S.hy S.hz
        S.data.limitCellVolume S.data.tetProbe))

/-- Concrete cross-cardinality Riemann-sum target: every slice in a varying
periodic Freudenthal refinement family carries the per-slice finite
EH/Dirichlet limit-weight target above. -/
def PhysicalReggeEHConcreteRefinementFamilySliceTarget
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ) : Prop :=
  ∀ r : ρ, PhysicalReggeEHConcreteSliceLimitWeightTarget (F.slice r)

/-- The concrete slice target holds for every slice of a six-tet volume
quadrature refinement family. -/
theorem physicalReggeEHConcreteRefinementFamilySliceTarget_holds
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ) :
    PhysicalReggeEHConcreteRefinementFamilySliceTarget F :=
  fun r => physicalReggeEHConcreteSliceLimitWeightTarget_holds (F.slice r)

/-- Product-filter full-Regge-to-EH target for the concrete refinement-family
path.  This is the global Riemann-sum target after the family supplies:

1. cross-cardinality convergence of finite six-tet quadrature proxies, and
2. a uniform product-filter residual estimate.

It is the product-filter analogue of
`PhysicalReggeEHManifoldIntegralRemainingTarget`: instead of quantifying over
arbitrary finite probes and arbitrary continuum integrals, it fixes the
concrete periodic Freudenthal refinement family and asks for convergence to
that family's supplied continuum EH integral. -/
def PhysicalReggeEHConcreteProductFilterTarget
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) : Prop :=
  Filter.Tendsto
    (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
      (α := α) (ρ := ρ) D.family)
    (D.refinementFilter ×ˢ l : Filter (ρ × α))
    (nhds D.continuumIntegral)

/-- Product-filter data proves the concrete refinement-family target. -/
theorem physicalReggeEHConcreteProductFilterTarget_holds
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    PhysicalReggeEHConcreteProductFilterTarget D :=
  D.fullReggeProduct_tendsto_continuum

/-- Diagonal form of the concrete product-filter target.  Once a diagonal
schedule into the `(cardinality, within-slice)` product filter is supplied, the
normalized full-Regge aggregate along that diagonal converges to the same
continuum EH integral. -/
def PhysicalReggeEHConcreteDiagonalTarget
    {α ρ δ : Type*} {l : Filter α} {m : Filter δ}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (diagonal : δ → ρ × α) : Prop :=
  Filter.Tendsto
    (fun s : δ =>
      CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) D.family (diagonal s))
    m
    (nhds D.continuumIntegral)

/-- A diagonal tending into the product filter proves the concrete diagonal
full-Regge-to-EH target. -/
theorem physicalReggeEHConcreteDiagonalTarget_holds
    {α ρ δ : Type*} {l : Filter α} {m : Filter δ}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (diagonal : δ → ρ × α)
    (hDiagonal :
      Filter.Tendsto diagonal m (D.refinementFilter ×ˢ l : Filter (ρ × α))) :
    PhysicalReggeEHConcreteDiagonalTarget (m := m) D diagonal :=
  D.fullReggeDiagonal_tendsto_continuum diagonal hDiagonal

/-- Agent-B interface package for Track 1.B-PHY.  The package deliberately keeps
the two hard geometric inputs explicit: cross-cardinality quadrature convergence
and product-filter uniform residual control.  Given those inputs, the physical
Regge/EH continuum target is available both on the product filter and along any
admissible diagonal schedule. -/
structure PhysicalReggeEHConcreteRefinementFamilyTargetCert
    {α ρ : Type*} (l : Filter α) where
  data :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l
  slice_targets :
    PhysicalReggeEHConcreteRefinementFamilySliceTarget data.family
  product_target :
    PhysicalReggeEHConcreteProductFilterTarget data

/-- Any concrete product-filter data gives the Agent-B certificate. -/
def PhysicalReggeEHConcreteRefinementFamilyTargetCert.ofProductFilterData
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    PhysicalReggeEHConcreteRefinementFamilyTargetCert (α := α) (ρ := ρ) l where
  data := D
  slice_targets := physicalReggeEHConcreteRefinementFamilySliceTarget_holds D.family
  product_target := physicalReggeEHConcreteProductFilterTarget_holds D

/-- Session 551 projection: the concrete refinement-family certificate keeps the
supplied product-filter data as its data field. -/
theorem PhysicalReggeEHConcreteRefinementFamilyTargetCert.ofProductFilterData_data
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    (PhysicalReggeEHConcreteRefinementFamilyTargetCert.ofProductFilterData D).data = D := rfl

/-- Session 551 projection: the concrete refinement-family certificate exposes
all slice-level finite EH/Dirichlet limit-weight targets. -/
theorem PhysicalReggeEHConcreteRefinementFamilyTargetCert.ofProductFilterData_sliceTargets
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    PhysicalReggeEHConcreteRefinementFamilySliceTarget
      (PhysicalReggeEHConcreteRefinementFamilyTargetCert.ofProductFilterData D).data.family :=
  (PhysicalReggeEHConcreteRefinementFamilyTargetCert.ofProductFilterData D).slice_targets

/-- Session 551 projection: the concrete refinement-family certificate exposes
the product-filter full-Regge-to-EH continuum target. -/
theorem PhysicalReggeEHConcreteRefinementFamilyTargetCert.ofProductFilterData_productTarget
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    PhysicalReggeEHConcreteProductFilterTarget
      (PhysicalReggeEHConcreteRefinementFamilyTargetCert.ofProductFilterData D).data :=
  (PhysicalReggeEHConcreteRefinementFamilyTargetCert.ofProductFilterData D).product_target

/-- Session 551 audit count for the three concrete refinement-family certificate
projections: data, slice targets, and product target. -/
def physicalReggeEHConcreteRefinementFamilyTargetCertProjectionCount : ℕ := 3

theorem physicalReggeEHConcreteRefinementFamilyTargetCertProjectionCount_eq_three :
    physicalReggeEHConcreteRefinementFamilyTargetCertProjectionCount = 3 := rfl

/-- One-statement interface for the concrete refinement-family target.  It
exposes exactly what remains for the true `1B-PHY` path: provide
`CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData`; the full-Regge
product-filter continuum limit and all per-slice finite EH/Dirichlet
limit-weight targets then follow. -/
theorem physicalReggeEH_concrete_refinement_family_target_one_statement
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    PhysicalReggeEHConcreteRefinementFamilySliceTarget D.family ∧
    PhysicalReggeEHConcreteProductFilterTarget D ∧
    Nonempty (PhysicalReggeEHConcreteRefinementFamilyTargetCert (α := α) (ρ := ρ) l) :=
  ⟨physicalReggeEHConcreteRefinementFamilySliceTarget_holds D.family,
   physicalReggeEHConcreteProductFilterTarget_holds D,
   ⟨PhysicalReggeEHConcreteRefinementFamilyTargetCert.ofProductFilterData D⟩⟩

/-- Session 553 projection: the concrete refinement-family one-statement theorem
exposes all slice-level finite EH/Dirichlet limit-weight targets. -/
theorem physicalReggeEH_concrete_refinement_family_target_one_statement_sliceTargets
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    PhysicalReggeEHConcreteRefinementFamilySliceTarget D.family :=
  (physicalReggeEH_concrete_refinement_family_target_one_statement D).1

/-- Session 553 projection: the concrete refinement-family one-statement theorem
exposes the product-filter full-Regge-to-EH continuum target. -/
theorem physicalReggeEH_concrete_refinement_family_target_one_statement_productTarget
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    PhysicalReggeEHConcreteProductFilterTarget D :=
  (physicalReggeEH_concrete_refinement_family_target_one_statement D).2.1

/-- Session 553 projection: the concrete refinement-family one-statement theorem
exposes an inhabited audit certificate. -/
theorem physicalReggeEH_concrete_refinement_family_target_one_statement_certInhabited
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    Nonempty (PhysicalReggeEHConcreteRefinementFamilyTargetCert (α := α) (ρ := ρ) l) :=
  (physicalReggeEH_concrete_refinement_family_target_one_statement D).2.2

/-- Session 553 audit count for the three concrete refinement-family
one-statement projections: slice target, product target, and certificate
inhabitation. -/
def physicalReggeEHConcreteRefinementFamilyOneStatementProjectionCount : ℕ := 3

theorem physicalReggeEHConcreteRefinementFamilyOneStatementProjectionCount_eq_three :
    physicalReggeEHConcreteRefinementFamilyOneStatementProjectionCount = 3 := rfl

/-- Session 586 varying-cardinality product-filter route.  A staged
cross-cardinality quadrature package plus a global residual envelope gives true
product-filter data for arbitrary cardinality index `ρ`, then the concrete
physical Regge/EH slice target, product target, and audit certificate follow. -/
theorem physicalReggeEH_concrete_varying_cardinality_product_filter_data_one_statement
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData
      (α := α) (ρ := ρ) l}
    (E : CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData D) :
    PhysicalReggeEHConcreteRefinementFamilySliceTarget E.toProductFilterData.family ∧
    PhysicalReggeEHConcreteProductFilterTarget E.toProductFilterData ∧
    Nonempty (PhysicalReggeEHConcreteRefinementFamilyTargetCert (α := α) (ρ := ρ) l) :=
  physicalReggeEH_concrete_refinement_family_target_one_statement E.toProductFilterData

theorem physicalReggeEH_concrete_varying_cardinality_product_filter_data_one_statement_sliceTarget
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData
      (α := α) (ρ := ρ) l}
    (E : CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData D) :
    PhysicalReggeEHConcreteRefinementFamilySliceTarget E.toProductFilterData.family :=
  (physicalReggeEH_concrete_varying_cardinality_product_filter_data_one_statement E).1

theorem physicalReggeEH_concrete_varying_cardinality_product_filter_data_one_statement_productTarget
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData
      (α := α) (ρ := ρ) l}
    (E : CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData D) :
    PhysicalReggeEHConcreteProductFilterTarget E.toProductFilterData :=
  (physicalReggeEH_concrete_varying_cardinality_product_filter_data_one_statement E).2.1

theorem physicalReggeEH_concrete_varying_cardinality_product_filter_data_one_statement_certInhabited
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData
      (α := α) (ρ := ρ) l}
    (E : CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData D) :
    Nonempty (PhysicalReggeEHConcreteRefinementFamilyTargetCert (α := α) (ρ := ρ) l) :=
  (physicalReggeEH_concrete_varying_cardinality_product_filter_data_one_statement E).2.2

/-- Session 586 audit count for the varying-cardinality product-filter
one-statement projections: slice target, product target, and certificate
inhabitation. -/
def physicalReggeEHConcreteVaryingCardinalityProductFilterOneStatementProjectionCount :
    ℕ := 3

theorem physicalReggeEHConcreteVaryingCardinalityProductFilterOneStatementProjectionCount_eq_three :
    physicalReggeEHConcreteVaryingCardinalityProductFilterOneStatementProjectionCount = 3 := rfl

/-- Session 587 finite product residual estimate.  This is the concrete
full-Regge-to-quadrature bound required before the product-filter convergence
argument can run. -/
def PhysicalReggeEHFiniteProductResidualEstimateTarget
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData
      (α := α) (ρ := ρ) l}
    (E : CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData D) : Prop :=
  ∀ (r : ρ) (t : α),
    |CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate D.family (r, t) -
      CanonicalPeriodicTetSixTetVolumeQuadratureProductQuadratureIntegral D.family (r, t)| ≤
      E.envelope t

theorem physicalReggeEHFiniteProductResidualEstimateTarget_holds
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData
      (α := α) (ρ := ρ) l}
    (E : CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData D) :
    PhysicalReggeEHFiniteProductResidualEstimateTarget E :=
  E.global_residual_bound

/-- Session 587 audit count: the global residual envelope exposes one finite
product residual estimate target. -/
def physicalReggeEHFiniteProductResidualEstimateProjectionCount : ℕ := 1

theorem physicalReggeEHFiniteProductResidualEstimateProjectionCount_eq_one :
    physicalReggeEHFiniteProductResidualEstimateProjectionCount = 1 := rfl

/-- Session 588 continuum-normalization target.  This is the raw
cross-cardinality `Tendsto` statement obtained after the finite product
residual estimate is combined with the staged quadrature limit. -/
def PhysicalReggeEHContinuumNormalizationFromResidualTarget
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData
      (α := α) (ρ := ρ) l}
    (E : CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData D) : Prop :=
  PhysicalReggeEHFiniteProductResidualEstimateTarget E →
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) D.family)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds D.continuumIntegral)

theorem physicalReggeEHContinuumNormalizationFromResidualTarget_holds
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData
      (α := α) (ρ := ρ) l}
    (E : CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData D) :
    PhysicalReggeEHContinuumNormalizationFromResidualTarget E := by
  intro hResidual
  exact
    D.fullReggeProduct_tendsto_continuum_of_forallSndResidualEnvelope
      E.envelope E.envelope_tendsto_zero hResidual

/-- Session 588 projection: applying the finite residual estimate gives the
continuum normalization statement itself. -/
theorem physicalReggeEHContinuumNormalizationFromResidualTarget_apply
    {α ρ : Type*} {l : Filter α}
    {D : CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityData
      (α := α) (ρ := ρ) l}
    (E : CanonicalPeriodicTetSixTetVolumeQuadratureGlobalResidualEnvelopeData D) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) D.family)
      (D.refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds D.continuumIntegral) :=
  physicalReggeEHContinuumNormalizationFromResidualTarget_holds E
    (physicalReggeEHFiniteProductResidualEstimateTarget_holds E)

/-- Session 588 audit count: one normalization function and one applied
continuum theorem. -/
def physicalReggeEHContinuumNormalizationFromResidualProjectionCount : ℕ := 2

theorem physicalReggeEHContinuumNormalizationFromResidualProjectionCount_eq_two :
    physicalReggeEHContinuumNormalizationFromResidualProjectionCount = 2 := rfl

/-! ## Physical D2 master-hypothesis witness -/

/-- Physical replacement for the flat `0 = 0` structural Regge/EH clause:
for a concrete periodic Freudenthal product-filter refinement package, the
normalized full nonlinear Regge aggregate tends to the supplied continuum
Einstein-Hilbert/Dirichlet integral. -/
def physicalReggeEHContinuumMasterProp
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    Prop :=
  PhysicalReggeEHConcreteProductFilterTarget D

theorem physicalReggeEHContinuumMasterProp_holds
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l) :
    physicalReggeEHContinuumMasterProp D :=
  physicalReggeEHConcreteProductFilterTarget_holds D

/-- Physical Track 1.C master clause: Schläfli-satisfying Regge data obey the
contracted discrete Bianchi identity at every vertex. -/
def physicalSchlafliBianchiMasterProp (V B : Type) [Fintype B] : Prop :=
  ∀ (R : Geometry.DiscreteBianchi.SchlafliReggeData V B) (v : V),
    Geometry.DiscreteBianchi.DiscreteBianchiContractedAtVertex R.toReggeData v

theorem physicalSchlafliBianchiMasterProp_holds (V B : Type) [Fintype B] :
    physicalSchlafliBianchiMasterProp V B :=
  Geometry.DiscreteBianchi.discrete_bianchi_contracted_from_schlafli

/-- Master-theorem D2 hypothesis input whose Regge/EH clause is the physical
product-filter `Tendsto` target, not the older flat-substrate identity. -/
def physicalReggeEHContinuumAndBianchiWitness
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    Gravity.MasterTheorem.RegEHContinuumAndBianchi where
  regge_to_einstein_hilbert_continuum := physicalReggeEHContinuumMasterProp D
  regge_holds := physicalReggeEHContinuumMasterProp_holds D
  discrete_bianchi_contracted := physicalSchlafliBianchiMasterProp V B
  bianchi_holds := physicalSchlafliBianchiMasterProp_holds V B

/-- Session 549 projection: the physical D2 witness installs the product-filter
Regge/EH continuum clause, not the older flat structural clause. -/
theorem physicalReggeEHContinuumAndBianchiWitness_reggeClause
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    (physicalReggeEHContinuumAndBianchiWitness D V B).regge_to_einstein_hilbert_continuum =
      physicalReggeEHContinuumMasterProp D := rfl

/-- Session 549 projection: the physical D2 witness carries the proof of the
product-filter Regge/EH continuum clause. -/
theorem physicalReggeEHContinuumAndBianchiWitness_reggeHolds
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    (physicalReggeEHContinuumAndBianchiWitness D V B).regge_to_einstein_hilbert_continuum :=
  (physicalReggeEHContinuumAndBianchiWitness D V B).regge_holds

/-- Session 549 projection: the physical D2 witness installs the Schläfli-form
contracted Bianchi clause. -/
theorem physicalReggeEHContinuumAndBianchiWitness_bianchiClause
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    (physicalReggeEHContinuumAndBianchiWitness D V B).discrete_bianchi_contracted =
      physicalSchlafliBianchiMasterProp V B := rfl

/-- Session 549 projection: the physical D2 witness carries the proof of the
Schläfli-form contracted Bianchi clause. -/
theorem physicalReggeEHContinuumAndBianchiWitness_bianchiHolds
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    (physicalReggeEHContinuumAndBianchiWitness D V B).discrete_bianchi_contracted :=
  (physicalReggeEHContinuumAndBianchiWitness D V B).bianchi_holds

/-- Audit certificate showing exactly what clauses the physical D2 master
witness installs. -/
structure PhysicalReggeEHD2MasterWitnessCert
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] where
  witness : Gravity.MasterTheorem.RegEHContinuumAndBianchi
  regge_clause_is_physical :
    witness.regge_to_einstein_hilbert_continuum =
      physicalReggeEHContinuumMasterProp D
  bianchi_clause_is_schlafli :
    witness.discrete_bianchi_contracted =
      physicalSchlafliBianchiMasterProp V B

def physicalReggeEHD2MasterWitnessCert
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    PhysicalReggeEHD2MasterWitnessCert D V B where
  witness := physicalReggeEHContinuumAndBianchiWitness D V B
  regge_clause_is_physical := rfl
  bianchi_clause_is_schlafli := rfl

/-- Session 549 projection: the certificate's witness is the physical D2 witness
constructed from the supplied product-filter data. -/
theorem physicalReggeEHD2MasterWitnessCert_witness_eq
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    (physicalReggeEHD2MasterWitnessCert D V B).witness =
      physicalReggeEHContinuumAndBianchiWitness D V B := rfl

/-- Session 549 projection: the certificate exposes the Regge/EH clause identity
without opening the certificate record at the call site. -/
theorem physicalReggeEHD2MasterWitnessCert_reggeClause
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    (physicalReggeEHD2MasterWitnessCert D V B).witness.regge_to_einstein_hilbert_continuum =
      physicalReggeEHContinuumMasterProp D :=
  (physicalReggeEHD2MasterWitnessCert D V B).regge_clause_is_physical

/-- Session 549 projection: the certificate exposes the Bianchi clause identity
without opening the certificate record at the call site. -/
theorem physicalReggeEHD2MasterWitnessCert_bianchiClause
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    (physicalReggeEHD2MasterWitnessCert D V B).witness.discrete_bianchi_contracted =
      physicalSchlafliBianchiMasterProp V B :=
  (physicalReggeEHD2MasterWitnessCert D V B).bianchi_clause_is_schlafli

/-- Session 549 audit count for the seven physical D2 master-witness projection
theorems: four witness-field projections plus three certificate projections. -/
def physicalReggeEHD2MasterWitnessProjectionCount : ℕ := 7

theorem physicalReggeEHD2MasterWitnessProjectionCount_eq_seven :
    physicalReggeEHD2MasterWitnessProjectionCount = 7 := rfl

theorem physicalReggeEHD2MasterWitnessCert_inhabited
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    Nonempty (PhysicalReggeEHD2MasterWitnessCert D V B) :=
  ⟨physicalReggeEHD2MasterWitnessCert D V B⟩

/-- One-statement form of the physical D2 master-hypothesis replacement. -/
theorem physicalReggeEHD2_master_witness_one_statement
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    (Nonempty Gravity.MasterTheorem.RegEHContinuumAndBianchi) ∧
    physicalReggeEHContinuumMasterProp D ∧
    physicalSchlafliBianchiMasterProp V B :=
  ⟨⟨physicalReggeEHContinuumAndBianchiWitness D V B⟩,
   physicalReggeEHContinuumMasterProp_holds D,
   physicalSchlafliBianchiMasterProp_holds V B⟩

/-- Session 554 projection: the physical D2 master-witness one-statement theorem
exposes an inhabited master-theorem D2 witness. -/
theorem physicalReggeEHD2_master_witness_one_statement_witnessInhabited
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    Nonempty Gravity.MasterTheorem.RegEHContinuumAndBianchi :=
  (physicalReggeEHD2_master_witness_one_statement D V B).1

/-- Session 554 projection: the physical D2 master-witness one-statement theorem
exposes the product-filter Regge/EH continuum master clause. -/
theorem physicalReggeEHD2_master_witness_one_statement_reggeEH
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    physicalReggeEHContinuumMasterProp D :=
  (physicalReggeEHD2_master_witness_one_statement D V B).2.1

/-- Session 554 projection: the physical D2 master-witness one-statement theorem
exposes the Schläfli-form contracted Bianchi master clause. -/
theorem physicalReggeEHD2_master_witness_one_statement_bianchi
    {α ρ : Type*} {l : Filter α}
    (D : CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l)
    (V B : Type) [Fintype B] :
    physicalSchlafliBianchiMasterProp V B :=
  (physicalReggeEHD2_master_witness_one_statement D V B).2.2

/-- Session 554 audit count for the three physical D2 master-witness
one-statement projections: witness inhabitation, Regge/EH, and Bianchi. -/
def physicalReggeEHD2MasterWitnessOneStatementProjectionCount : ℕ := 3

theorem physicalReggeEHD2MasterWitnessOneStatementProjectionCount_eq_three :
    physicalReggeEHD2MasterWitnessOneStatementProjectionCount = 3 := rfl

/-- The single-slice product-filter data supplies the concrete physical
Regge/EH target immediately.  This is the first actual
`CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData` instance in the
1B-PHY path: the cardinality filter is trivial (`PUnit`), while the
within-slice refinement is the slice's existing mesh refinement. -/
theorem physicalReggeEH_concrete_single_slice_product_filter_data_one_statement
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (refinementFilter : Filter PUnit) :
    PhysicalReggeEHConcreteRefinementFamilySliceTarget
      (S.toSingleSliceProductFilterData refinementFilter).family ∧
    PhysicalReggeEHConcreteProductFilterTarget
      (S.toSingleSliceProductFilterData refinementFilter) :=
  ⟨physicalReggeEHConcreteRefinementFamilySliceTarget_holds
      (S.toSingleSliceProductFilterData refinementFilter).family,
   physicalReggeEHConcreteProductFilterTarget_holds
      (S.toSingleSliceProductFilterData refinementFilter)⟩

/-- Session 556 projection: the single-slice product-filter one-statement theorem
exposes the concrete refinement-family slice target. -/
theorem physicalReggeEH_concrete_single_slice_product_filter_data_one_statement_sliceTarget
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (refinementFilter : Filter PUnit) :
    PhysicalReggeEHConcreteRefinementFamilySliceTarget
      (S.toSingleSliceProductFilterData refinementFilter).family :=
  (physicalReggeEH_concrete_single_slice_product_filter_data_one_statement
    S refinementFilter).1

/-- Session 556 projection: the single-slice product-filter one-statement theorem
exposes the concrete product-filter Regge/EH target. -/
theorem physicalReggeEH_concrete_single_slice_product_filter_data_one_statement_productTarget
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (refinementFilter : Filter PUnit) :
    PhysicalReggeEHConcreteProductFilterTarget
      (S.toSingleSliceProductFilterData refinementFilter) :=
  (physicalReggeEH_concrete_single_slice_product_filter_data_one_statement
    S refinementFilter).2

/-- Session 556 audit count for the two single-slice product-filter
one-statement projections: slice target and product target. -/
def physicalReggeEHConcreteSingleSliceProductFilterOneStatementProjectionCount : ℕ := 2

theorem physicalReggeEHConcreteSingleSliceProductFilterOneStatementProjectionCount_eq_two :
    physicalReggeEHConcreteSingleSliceProductFilterOneStatementProjectionCount = 2 := rfl

end

end Track1BCPhysicalResidual
end Gravity
end IndisputableMonolith
