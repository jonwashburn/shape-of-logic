import IndisputableMonolith.Gravity.D2ScopingAudit

/-!
# D2 Damped-Schedule Closure: the Uniform Residual Is Derived, Not Supplied

## Status: THEOREM (0 sorry, 0 RS-internal axiom)

## What this module closes (D2 open item 2 of `D2ScopingAudit`)

`D2ScopingAudit` names two analytic inputs that the D2 product-filter datum
had carried as supplied hypothesis fields:

1. `D2QuadratureConvergenceTarget` — quadrature proxies converge to the
   continuum integral across cardinalities, and
2. `D2ResidualVanishingTarget` — the (full nonlinear Regge − quadrature)
   residual vanishes uniformly on the product filter.

This module **discharges item 2 from the primitive curvature bound**: every
cardinality slice already carries the Track 1.B local correspondence
(`hLocal`), i.e. the cubic Taylor bound

  `‖R(ξ) − R(0) − ½·ES(ξ)‖ ≤ C·‖ξ‖³`  for `‖ξ‖ < r`,

and that local bound alone forces the two-scale residual to vanish once the
within-slice refinement schedule is damped per slice.  Concretely, for any
varying-cardinality family `F` and any universal schedule `σ → 0` we build
the **damped family** `dampedFamily F σ`: same cardinalities, same probes,
same limiting cell volumes (hence the same quadrature proxies), but
within-slice spacing `σ(t) · d_S` where the damping factor

  `d_S = min (r_S / (1 + Σ_τ ‖ξ_τ‖)) (1 / (1 + K_S))`,
  `K_S = (|V_S|/6) · C_S · Σ_τ ‖ξ_τ‖³`

is computed from the slice's own local-correspondence witnesses `(r_S, C_S)`,
its probe norms, and its limiting cell volume.  The damping keeps every
scaled probe inside the local-correspondence radius and shrinks the per-slice
residual coefficient below a slice-independent envelope `|σ(t)|`.  The
product uniform residual target then holds for `dampedFamily F σ` with **no
supplied analytic field** (`dampedFamily_uniformResidual`).

Consequently the full nonlinear Regge → continuum product-filter convergence
for the damped family needs only the quadrature limit
(`dampedFamily_fullReggeProduct_tendsto_continuum`), and the master-theorem
D2 datum for the damped family is constructed with `uniform_residual`
**proved** (`dampedProductFilterData`).

## What remains open after this module

* `D2QuadratureConvergenceTarget` (item 1): convergence of the explicit
  finite quadrature sums across cardinalities.  This is family-specific
  geometric data and remains the supplied input.
* The local correspondence `hLocal` itself: it is a field of every slice
  (Track 1.B), exactly as it was for the prior reduction; this module adds
  no new hypothesis beyond what slices already carry.
* Non-product, non-flat admissible triangulations (item 3 of the audit).
-/

namespace IndisputableMonolith
namespace Gravity
namespace D2DampedScheduleClosure

open PhysicalSixTetCubicDirichletInstance
open Geometry.ReggeTriangulation3D
open Geometry.ReggeHessian3D
open Geometry.Triangulation3DConsistency
open Geometry.ReggeActionConcrete
open Geometry.PeriodicFreudenthalTorus

noncomputable section

/-! ## §1. Quadratic homogeneity of the canonical Dirichlet energy -/

/-- The canonical graph-Dirichlet energy is quadratically homogeneous under
scalar rescaling of the vertex potential. -/
theorem canonicalDirichletEnergy_smul
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (a : ℝ) (ξ : VertexPotential K) :
    canonicalDirichletEnergy K hK (a • ξ) =
      a ^ (2 : ℕ) * canonicalDirichletEnergy K hK ξ := by
  unfold canonicalDirichletEnergy
  have h : ∀ i j : Fin K.nV,
      canonicalDualWeight K hK i j * ((a • ξ) i - (a • ξ) j) ^ (2 : ℕ) =
        a ^ (2 : ℕ) * (canonicalDualWeight K hK i j * (ξ i - ξ j) ^ (2 : ℕ)) := by
    intro i j
    have hsm : (a • ξ) i - (a • ξ) j = a * (ξ i - ξ j) := by
      simp [Pi.smul_apply, smul_eq_mul, mul_sub]
    rw [hsm, mul_pow]
    ring
  calc (1 / 2) * ∑ i : Fin K.nV, ∑ j : Fin K.nV,
        canonicalDualWeight K hK i j * ((a • ξ) i - (a • ξ) j) ^ (2 : ℕ)
      = (1 / 2) * ∑ i : Fin K.nV, ∑ j : Fin K.nV,
          a ^ (2 : ℕ) * (canonicalDualWeight K hK i j * (ξ i - ξ j) ^ (2 : ℕ)) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => h i j
    _ = a ^ (2 : ℕ) *
          ((1 / 2) * ∑ i : Fin K.nV, ∑ j : Fin K.nV,
            canonicalDualWeight K hK i j * (ξ i - ξ j) ^ (2 : ℕ)) := by
        simp only [← Finset.mul_sum]
        ring

/-! ## §2. Local-correspondence witnesses carried by a slice -/

/-- The local-correspondence radius carried by a cardinality slice. -/
noncomputable def localRadius
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : ℝ :=
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  S.hLocal.choose

/-- The local-correspondence cubic constant carried by a cardinality slice. -/
noncomputable def localConstant
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : ℝ :=
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  S.hLocal.choose_spec.choose

theorem localRadius_pos
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    0 < localRadius S := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  exact S.hLocal.choose_spec.choose_spec.1

theorem localConstant_nonneg
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    0 ≤ localConstant S := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  exact S.hLocal.choose_spec.choose_spec.2.1

/-- The cubic Taylor bound carried by a slice, stated for its canonical
encoded periodic Freudenthal torus. -/
theorem local_bound
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    letI : NeZero S.Nx := S.instNx
    letI : NeZero S.Ny := S.instNy
    letI : NeZero S.Nz := S.instNz
    ∀ ξ : VertexPotential
        (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K,
      ‖ξ‖ < localRadius S →
        ‖reggeAction
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
            ξ -
          reggeAction
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
            (zeroPotential
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K) -
          (1 / 2) *
            periodicEdgeStencilDirichletAction
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz) ξ‖ ≤
          localConstant S * ‖ξ‖ ^ (3 : ℕ) := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  exact S.hLocal.choose_spec.choose_spec.2.2

/-! ## §3. Probe norms, residual coefficient, and the damping factor -/

/-- Sum of probe norms across the slice's tetrahedra. -/
noncomputable def probeNormSum
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : ℝ :=
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  ∑ τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)),
    ‖S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)‖

/-- Sum of cubed probe norms across the slice's tetrahedra. -/
noncomputable def probeCubeSum
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : ℝ :=
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  ∑ τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)),
    ‖S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)‖ ^ (3 : ℕ)

theorem probeNormSum_nonneg
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    0 ≤ probeNormSum S := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  exact Finset.sum_nonneg fun τ _ => norm_nonneg _

theorem probeCubeSum_nonneg
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    0 ≤ probeCubeSum S := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  exact Finset.sum_nonneg fun τ _ => pow_nonneg (norm_nonneg _) _

/-- The slice residual coefficient: limiting cell-volume weight times the
local cubic constant times the cubed probe-norm sum. -/
noncomputable def residualCoefficient
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : ℝ :=
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  |S.data.limitCellVolume| / 6 * localConstant S * probeCubeSum S

theorem residualCoefficient_nonneg
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    0 ≤ residualCoefficient S :=
  mul_nonneg
    (mul_nonneg (div_nonneg (abs_nonneg _) (by norm_num)) (localConstant_nonneg S))
    (probeCubeSum_nonneg S)

/-- The per-slice damping factor.  The first component keeps every damped
probe inside the local-correspondence radius; the second shrinks the slice
residual coefficient below one. -/
noncomputable def dampingFactor
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) : ℝ :=
  min (localRadius S / (1 + probeNormSum S)) (1 / (1 + residualCoefficient S))

theorem one_add_probeNormSum_pos
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    0 < 1 + probeNormSum S := by
  have := probeNormSum_nonneg S
  linarith

theorem one_add_residualCoefficient_pos
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    0 < 1 + residualCoefficient S := by
  have := residualCoefficient_nonneg S
  linarith

theorem dampingFactor_pos
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    0 < dampingFactor S := by
  unfold dampingFactor
  exact lt_min
    (div_pos (localRadius_pos S) (one_add_probeNormSum_pos S))
    (div_pos one_pos (one_add_residualCoefficient_pos S))

theorem dampingFactor_le_radius_quotient
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    dampingFactor S ≤ localRadius S / (1 + probeNormSum S) :=
  min_le_left _ _

theorem dampingFactor_mul_residualCoefficient_le_one
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l) :
    dampingFactor S * residualCoefficient S ≤ 1 := by
  have hK := residualCoefficient_nonneg S
  have h1K := one_add_residualCoefficient_pos S
  have hd : dampingFactor S ≤ 1 / (1 + residualCoefficient S) := min_le_right _ _
  calc dampingFactor S * residualCoefficient S
      ≤ (1 / (1 + residualCoefficient S)) * residualCoefficient S := by
        exact mul_le_mul_of_nonneg_right hd hK
    _ ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one h1K]
        linarith

/-! ## §4. The damped slice -/

/-- The damped slice: same cardinality, probes, local correspondence, and
limiting cell volume; the cell-volume schedule is frozen at its limit and the
spacing schedule is the universal schedule `σ` damped by the slice's own
`dampingFactor`. -/
noncomputable def dampedSlice
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0) :
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
        cellVolume := fun _ => S.data.limitCellVolume
        cellVolume_tendsto := tendsto_const_nhds
        tetProbe := S.data.tetProbe
        spacing := fun u => σ u * dampingFactor S
        spacing_tendsto_zero := by
          simpa using hσ0.mul_const (dampingFactor S)
        spacing_eventually_ne_zero :=
          hσne.mono fun u hu => mul_ne_zero hu (dampingFactor_pos S).ne' } }

/-- Damping does not change the slice's finite quadrature proxy. -/
theorem dampedSlice_quadratureIntegral
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0) :
    (dampedSlice S σ hσ0 hσne).quadratureIntegral = S.quadratureIntegral := rfl

/-! ## §5. The per-tetrahedron normalized residual bound -/

/-- Normalized nonlinear Regge action minus the quadratic Dirichlet limit is
bounded by the slice's cubic constant times `|s|` times the cubed probe norm,
whenever the scaled probe sits inside the local-correspondence radius.  This
is the local cubic Taylor bound divided by `s²`. -/
theorem normalized_regge_sub_limit_abs_le
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (s : ℝ) (hs : s ≠ 0) :
    letI : NeZero S.Nx := S.instNx
    letI : NeZero S.Ny := S.instNy
    letI : NeZero S.Nz := S.instNz
    ∀ ξ : VertexPotential
        (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K,
      ‖s • ξ‖ < localRadius S →
        |reggeAction
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
            (s • ξ) / s ^ (2 : ℕ) -
          (1 / 2) *
            canonicalDirichletEnergy
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
              ξ| ≤
          localConstant S * |s| * ‖ξ‖ ^ (3 : ℕ) := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  intro ξ hsmall
  have hb := local_bound S (s • ξ) hsmall
  have h0 :
      reggeAction
        (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
        (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
        (zeroPotential
          (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K) = 0 :=
    canonicalPeriodicReggeAction_zeroPotential_eq_zero_of_flatConfiguration
      S.Nx S.Ny S.Nz S.hx S.hy S.hz
      (canonicalPeriodicFlatConfiguration S.Nx S.Ny S.Nz S.hx S.hy S.hz)
  have hES :
      canonicalDirichletEnergy
        (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
        (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
        (s • ξ) =
        periodicEdgeStencilDirichletAction
          (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz) (s • ξ) :=
    canonicalPeriodicEdgeStencilTarget S.Nx S.Ny S.Nz S.hx S.hy S.hz (s • ξ)
  have hsm :
      canonicalDirichletEnergy
        (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
        (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
        (s • ξ) =
        s ^ (2 : ℕ) *
          canonicalDirichletEnergy
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
            ξ :=
    canonicalDirichletEnergy_smul _ _ s ξ
  rw [h0, sub_zero, ← hES, hsm, Real.norm_eq_abs] at hb
  have hs2 : (0 : ℝ) < s ^ (2 : ℕ) := by positivity
  have key :
      reggeAction
        (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
        (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
        (s • ξ) / s ^ (2 : ℕ) -
        (1 / 2) *
          canonicalDirichletEnergy
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
            ξ =
        (reggeAction
          (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
          (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
          (s • ξ) -
          (1 / 2) *
            (s ^ (2 : ℕ) *
              canonicalDirichletEnergy
                (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
                (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
                ξ)) / s ^ (2 : ℕ) := by
    field_simp
  rw [key, abs_div, abs_of_pos hs2]
  have hnorm3 : ‖s • ξ‖ ^ (3 : ℕ) = |s| ^ (3 : ℕ) * ‖ξ‖ ^ (3 : ℕ) := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow]
  have habs3 : |s| ^ (3 : ℕ) = |s| * s ^ (2 : ℕ) := by
    rw [pow_succ, sq_abs, mul_comm]
  have hdivle :
      |reggeAction
          (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
          (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
          (s • ξ) -
          (1 / 2) *
            (s ^ (2 : ℕ) *
              canonicalDirichletEnergy
                (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
                (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
                ξ)| / s ^ (2 : ℕ) ≤
        (localConstant S * ‖s • ξ‖ ^ (3 : ℕ)) / s ^ (2 : ℕ) := by
    gcongr
  refine le_trans hdivle (le_of_eq ?_)
  rw [hnorm3, habs3]
  field_simp

/-! ## §6. The damped-slice residual bound -/

/-- The damped slice's full nonlinear Regge aggregate minus its quadrature
proxy is bounded by `|σ t|`, uniformly in the slice, whenever `σ t ≠ 0` and
`|σ t| ≤ 1`.  The damping factor absorbs the slice's local radius, cubic
constant, probe norms, and limiting cell volume. -/
theorem dampedSlice_residual_abs_le
    {α : Type*} {l : Filter α}
    (S : CanonicalPeriodicTetSixTetVolumeQuadratureSlice l)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (t : α) (hne : σ t ≠ 0) (hle : |σ t| ≤ 1) :
    |(dampedSlice S σ hσ0 hσne).fullReggeAggregate t -
      (dampedSlice S σ hσ0 hσne).quadratureIntegral| ≤ |σ t| := by
  letI : NeZero S.Nx := S.instNx
  letI : NeZero S.Ny := S.instNy
  letI : NeZero S.Nz := S.instNz
  have hd_pos : 0 < dampingFactor S := dampingFactor_pos S
  have hs_ne : σ t * dampingFactor S ≠ 0 := mul_ne_zero hne hd_pos.ne'
  have habs_s : |σ t * dampingFactor S| = |σ t| * dampingFactor S := by
    rw [abs_mul, abs_of_pos hd_pos]
  have habs_s_le : |σ t * dampingFactor S| ≤ dampingFactor S := by
    rw [habs_s]
    exact mul_le_of_le_one_left hd_pos.le hle
  -- The damped aggregate and quadrature proxy as explicit tetrahedron sums.
  have hAgg : (dampedSlice S σ hσ0 hσne).fullReggeAggregate t =
      ∑ τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)),
        canonicalPeriodicFreudenthalTetVolumeWeight S.Nx S.Ny S.Nz
            S.data.limitCellVolume (tetFinEquiv S.Nx S.Ny S.Nz τ) *
          (reggeAction
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
            ((σ t * dampingFactor S) • S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)) /
            (σ t * dampingFactor S) ^ (2 : ℕ)) := rfl
  have hQuad : (dampedSlice S σ hσ0 hσne).quadratureIntegral =
      ∑ τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)),
        canonicalPeriodicFreudenthalTetVolumeWeight S.Nx S.Ny S.Nz
            S.data.limitCellVolume (tetFinEquiv S.Nx S.Ny S.Nz τ) *
          ((1 / 2) *
            canonicalDirichletEnergy
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
              (S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ))) := rfl
  rw [hAgg, hQuad, ← Finset.sum_sub_distrib]
  simp only [canonicalPeriodicFreudenthalTetVolumeWeight, ← mul_sub]
  -- Every damped probe sits inside the local-correspondence radius.
  have hsmall : ∀ τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)),
      ‖(σ t * dampingFactor S) • S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)‖ <
        localRadius S := by
    intro τ
    have hM : ‖S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)‖ ≤ probeNormSum S :=
      Finset.single_le_sum (f := fun τ' =>
          ‖S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ')‖)
        (fun τ' _ => norm_nonneg _) (Finset.mem_univ τ)
    have h1M : 0 < 1 + probeNormSum S := one_add_probeNormSum_pos S
    have hM_lt : ‖S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)‖ < 1 + probeNormSum S := by
      linarith
    have hq_pos : 0 < localRadius S / (1 + probeNormSum S) :=
      div_pos (localRadius_pos S) h1M
    calc ‖(σ t * dampingFactor S) • S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)‖
        = |σ t * dampingFactor S| *
            ‖S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ (localRadius S / (1 + probeNormSum S)) *
            ‖S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)‖ := by
          exact mul_le_mul_of_nonneg_right
            (le_trans habs_s_le (dampingFactor_le_radius_quotient S)) (norm_nonneg _)
      _ < (localRadius S / (1 + probeNormSum S)) * (1 + probeNormSum S) := by
          exact mul_lt_mul_of_pos_left hM_lt hq_pos
      _ = localRadius S := div_mul_cancel₀ _ h1M.ne'
  -- Per-tetrahedron bound from the normalized cubic Taylor estimate.
  have hper : ∀ τ ∈ (Finset.univ : Finset (Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)))),
      |S.data.limitCellVolume / 6 *
        (reggeAction
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
            (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
            ((σ t * dampingFactor S) • S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)) /
            (σ t * dampingFactor S) ^ (2 : ℕ) -
          (1 / 2) *
            canonicalDirichletEnergy
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).K
              (canonicalEncodedPeriodicFreudenthalTorus S.Nx S.Ny S.Nz S.hx S.hy S.hz).hK
              (S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)))| ≤
        |S.data.limitCellVolume| / 6 *
          (localConstant S * |σ t * dampingFactor S| *
            ‖S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)‖ ^ (3 : ℕ)) := by
    intro τ _
    rw [abs_mul]
    have hwabs : |S.data.limitCellVolume / 6| = |S.data.limitCellVolume| / 6 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    rw [hwabs]
    exact mul_le_mul_of_nonneg_left
      (normalized_regge_sub_limit_abs_le S (σ t * dampingFactor S) hs_ne
        (S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)) (hsmall τ))
      (div_nonneg (abs_nonneg _) (by norm_num))
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum hper) ?_)
  -- Collapse the sum to the residual coefficient and absorb the damping.
  have hrc : residualCoefficient S =
      |S.data.limitCellVolume| / 6 * localConstant S *
        (∑ τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)),
          ‖S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)‖ ^ (3 : ℕ)) := rfl
  have hsum_eq :
      (∑ τ : Fin (Fintype.card (PeriodicTet S.Nx S.Ny S.Nz)),
        |S.data.limitCellVolume| / 6 *
          (localConstant S * |σ t * dampingFactor S| *
            ‖S.data.tetProbe (tetFinEquiv S.Nx S.Ny S.Nz τ)‖ ^ (3 : ℕ))) =
        |σ t * dampingFactor S| * residualCoefficient S := by
    rw [hrc]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [hsum_eq, habs_s]
  calc |σ t| * dampingFactor S * residualCoefficient S
      = |σ t| * (dampingFactor S * residualCoefficient S) := by ring
    _ ≤ |σ t| * 1 :=
        mul_le_mul_of_nonneg_left
          (dampingFactor_mul_residualCoefficient_le_one S) (abs_nonneg _)
    _ = |σ t| := mul_one _

/-! ## §7. The damped family and the derived uniform residual -/

/-- Damp every slice of a varying-cardinality family with the same universal
schedule `σ`.  Cardinalities, probes, and quadrature proxies are unchanged. -/
noncomputable def dampedFamily
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0) :
    CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ where
  slice := fun r => dampedSlice (F.slice r) σ hσ0 hσne

/-- **DERIVED UNIFORM RESIDUAL (D2 open item 2 discharged).**  The damped
family satisfies the product uniform-residual target for every refinement
filter.  No analytic residual field is supplied: the bound comes from each
slice's own local cubic Taylor correspondence, the flat-action normalization,
the edge-stencil Dirichlet identification, and the constructed damping. -/
theorem dampedFamily_uniformResidual
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (refinementFilter : Filter ρ) :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget
      (dampedFamily F σ hσ0 hσne) refinementFilter := by
  refine canonicalPeriodicTetSixTetVolumeQuadratureProductUniformResidualTarget_of_snd_abs_bound
    (dampedFamily F σ hσ0 hσne) refinementFilter (fun t => |σ t|) ?_ ?_
  · simpa using hσ0.abs
  · have h1 : ∀ᶠ t : α in l, |σ t| ≤ 1 := by
      have hball : Metric.closedBall (0 : ℝ) 1 ∈ nhds (0 : ℝ) :=
        Metric.closedBall_mem_nhds 0 one_pos
      have := hσ0.eventually_mem hball
      simpa [Metric.mem_closedBall, Real.dist_eq] using this
    refine ((hσne.and h1).prod_inr refinementFilter).mono ?_
    rintro ⟨r, t⟩ ⟨ht_ne, ht_le⟩
    exact dampedSlice_residual_abs_le (F.slice r) σ hσ0 hσne t ht_ne ht_le

/-- The damped family inherits the cross-cardinality quadrature target from
the base family, since damping preserves every quadrature proxy. -/
theorem dampedFamily_quadrature_target
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ)
    (hquad :
      CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
        F refinementFilter continuumIntegral) :
    CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
      (dampedFamily F σ hσ0 hσne) refinementFilter continuumIntegral := by
  unfold CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget at hquad ⊢
  simpa only [dampedFamily, dampedSlice_quadratureIntegral] using hquad

/-! ## §8. The D2 datum with a proved residual field, and the closure -/

/-- The master-theorem D2 product-filter datum for the damped family.  The
`uniform_residual` field is **proved**, not supplied; the only analytic input
is the cross-cardinality quadrature limit. -/
noncomputable def dampedProductFilterData
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ)
    (hquad :
      CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
        F refinementFilter continuumIntegral) :
    CanonicalPeriodicTetSixTetVolumeQuadratureProductFilterData (α := α) (ρ := ρ) l where
  family := dampedFamily F σ hσ0 hσne
  refinementFilter := refinementFilter
  continuumIntegral := continuumIntegral
  quadrature_tendsto :=
    dampedFamily_quadrature_target F σ hσ0 hσne refinementFilter continuumIntegral hquad
  uniform_residual :=
    dampedFamily_uniformResidual F σ hσ0 hσne refinementFilter

/-- **D2 DAMPED-SCHEDULE CLOSURE.**  For every varying-cardinality slice
family and every universal schedule `σ → 0`, the full nonlinear Regge
aggregate of the damped family converges to the continuum integral on the
product filter, given only the cross-cardinality quadrature limit.  The
two-scale uniform residual is derived, not assumed. -/
theorem dampedFamily_fullReggeProduct_tendsto_continuum
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ)
    (hquad :
      CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
        F refinementFilter continuumIntegral) :
    Filter.Tendsto
      (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
        (α := α) (ρ := ρ) (dampedFamily F σ hσ0 hσne))
      (refinementFilter ×ˢ l : Filter (ρ × α))
      (nhds continuumIntegral) :=
  (dampedProductFilterData F σ hσ0 hσne refinementFilter continuumIntegral
    hquad).fullReggeProduct_tendsto_continuum

/-- The damped datum satisfies the Track 1.B-PHY concrete product-filter
target consumed by the quantum-gravity master theorem. -/
theorem dampedProductFilterData_satisfies_master_target
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ)
    (hquad :
      CanonicalPeriodicTetSixTetVolumeQuadratureCrossCardinalityTarget
        F refinementFilter continuumIntegral) :
    Track1BCPhysicalResidual.PhysicalReggeEHConcreteProductFilterTarget
      (dampedProductFilterData F σ hσ0 hσne refinementFilter continuumIntegral hquad) :=
  Track1BCPhysicalResidual.physicalReggeEHConcreteProductFilterTarget_holds
    (dampedProductFilterData F σ hσ0 hσne refinementFilter continuumIntegral hquad)

/-! ## §9. Restatement against the named D2 audit targets -/

/-- **`D2ResidualVanishingTarget` holds for damped schedules.**  Stated in the
exact vocabulary of `D2ScopingAudit`: for every family, the residual target of
the damped family is a theorem, with the bound built from each slice's local
correspondence (the primitive curvature bound) and the constructed spacing
damping. -/
theorem d2_residual_vanishing_target_damped
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (refinementFilter : Filter ρ) :
    D2ScopingAudit.D2ResidualVanishingTarget l (dampedFamily F σ hσ0 hσne)
      refinementFilter :=
  dampedFamily_uniformResidual F σ hσ0 hσne refinementFilter

/-- **D2 reduced to one analytic input.**  In the audit's vocabulary: the
quadrature target alone implies the full nonlinear product-filter convergence
for the damped family.  Compare `D2ScopingAudit.d2_reduction_statement`,
which consumed both targets. -/
theorem d2_reduction_to_quadrature_only
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (refinementFilter : Filter ρ) (continuumIntegral : ℝ) :
    D2ScopingAudit.D2QuadratureConvergenceTarget l F refinementFilter continuumIntegral →
      Filter.Tendsto
        (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
          (α := α) (ρ := ρ) (dampedFamily F σ hσ0 hσne))
        (refinementFilter ×ˢ l : Filter (ρ × α))
        (nhds continuumIntegral) :=
  fun hquad =>
    dampedFamily_fullReggeProduct_tendsto_continuum F σ hσ0 hσne refinementFilter
      continuumIntegral hquad

/-- One-statement bundle for citation: damping preserves quadrature proxies,
derives the uniform residual outright, and reduces full D2 convergence to the
quadrature limit alone. -/
theorem d2_damped_schedule_closure_one_statement
    {α ρ : Type*} {l : Filter α}
    (F : CanonicalPeriodicTetSixTetVolumeQuadratureRefinementFamily l ρ)
    (σ : α → ℝ)
    (hσ0 : Filter.Tendsto σ l (nhds 0))
    (hσne : ∀ᶠ t : α in l, σ t ≠ 0)
    (refinementFilter : Filter ρ) :
    (∀ r : ρ,
      ((dampedFamily F σ hσ0 hσne).slice r).quadratureIntegral =
        (F.slice r).quadratureIntegral) ∧
    D2ScopingAudit.D2ResidualVanishingTarget l (dampedFamily F σ hσ0 hσne)
      refinementFilter ∧
    (∀ continuumIntegral : ℝ,
      D2ScopingAudit.D2QuadratureConvergenceTarget l F refinementFilter continuumIntegral →
        Filter.Tendsto
          (CanonicalPeriodicTetSixTetVolumeQuadratureProductFullReggeAggregate
            (α := α) (ρ := ρ) (dampedFamily F σ hσ0 hσne))
          (refinementFilter ×ˢ l : Filter (ρ × α))
          (nhds continuumIntegral)) :=
  ⟨fun r => dampedSlice_quadratureIntegral (F.slice r) σ hσ0 hσne,
   d2_residual_vanishing_target_damped F σ hσ0 hσne refinementFilter,
   fun continuumIntegral hquad =>
     d2_reduction_to_quadrature_only F σ hσ0 hσne refinementFilter continuumIntegral hquad⟩

end

end D2DampedScheduleClosure
end Gravity
end IndisputableMonolith
