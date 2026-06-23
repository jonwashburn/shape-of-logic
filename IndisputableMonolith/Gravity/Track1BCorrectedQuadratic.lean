import IndisputableMonolith.Gravity.D2DampedScheduleClosure
import IndisputableMonolith.Gravity.FreudenthalAxisStencilCoeffCert

/-!
# Track 1.B Corrected Quadratic: the Axis-Stencil Local Correspondence

## Status: THEOREM (0 sorry, 0 RS-internal axiom) for everything stated;
## the corrected gate itself is named OPEN, not asserted.

## Why this module exists (Session 202)

The Track 1.B route to the local Regge/J-cost correspondence factors through
the mixed hinge-deficit quadratic.  The Session 202 exact finite audit showed
the old identification was wrong-weighted: at the `N = 5` single-vertex bump
the mixed quadratic evaluates to `12`, while the seven-class square-root edge
stencil evaluates to `6 + 6√2 + 2√3`, and
`canonicalPeriodicMixedLengthSingleVertexAudit_scalar_mismatch` proves those
scalars differ.  The corrected mixed identification
(`CanonicalPeriodicMixedHingeDeficitAxisStencilTarget`: mixed quadratic =
rational axis stencil) already exists.  What did not exist was the corrected
**endpoint**: the local correspondence with the axis stencil as quadratic,
its algebra, and the theorem explaining why the correction is forced rather
than aesthetic.  This module supplies all three.

## What is proved here

1. `ReggeLocalQuadraticCorrespondence K hK Q`: the local cubic-Taylor
   correspondence with an arbitrary candidate quadratic `Q`, generalizing
   the legacy seven-class definition (which is the instance
   `Q = periodicEdgeStencilDirichletAction P`, proved as an `Iff`).
2. `CanonicalPeriodicAxisStencilLocalCorrespondence`: the corrected endpoint,
   the instance at `Q = canonicalPeriodicMixedAxisStencilAction`.
3. Quadratic algebra for the axis stencil (nonnegativity, exact
   `a²`-homogeneity) and transferred homogeneity for the legacy stencil.
4. **Rigidity** (`reggeLocalQuadraticCorrespondence_quadratic_unique`): two
   homogeneous quadratics satisfying the correspondence on the same complex
   are pointwise equal.  Corollary: the legacy and corrected endpoints are
   jointly satisfiable only if the two stencils coincide identically
   (`not_both_correspondences_of_quadratics_differ`).  Given the Session 202
   mismatch witness, at most one of them can be the true Taylor coefficient;
   the audit selects the axis stencil.
5. **D2 hook** (`normalized_regge_sub_half_quadratic_abs_le` and its axis
   instance): the per-tetrahedron normalized residual bound used by the
   damped-schedule closure, proved parametrically in `Q`, so the entire
   damped D2 pipeline transfers to the corrected quadratic the day the
   corrected gate closes, with quadrature limit action `½ · axis stencil`.
6. The corrected `N = 5` gate, stated exactly: stationarity at `N = 5` is
   already a theorem, so the corrected closure at the certificate scale
   reduces to one finite coefficient identity, the explicit-fiber axis
   target (`CanonicalPeriodicCorrectedTrack1BGateAtN5`).

## What remains open

The `N = 5` gate itself is now CLOSED (2026-06-17): see
`correctedTrack1BGateAtN5_closed`, discharged by the finite coefficient
certificate in `FreudenthalAxisStencilCoeffCert` (with the `native_decide`
axiom caveat noted there). What remains open is only the all-cardinality
generalization (a single explicit-fiber coefficient identity for arbitrary
`N`, not just `N = 5`). Everything else in this module is unconditional.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Track1BCorrectedQuadratic

open PhysicalSixTetCubicDirichletInstance
open D2DampedScheduleClosure
open Geometry.ReggeTriangulation3D
open Geometry.ReggeHessian3D
open Geometry.Triangulation3DConsistency
open Geometry.ReggeActionConcrete
open Geometry.PeriodicFreudenthalTorus

noncomputable section

/-! ## §1. The parametric local quadratic correspondence -/

/-- Local cubic-Taylor correspondence for an arbitrary candidate quadratic
`Q`: near the flat configuration, the full nonlinear Regge action equals its
flat value plus one half of `Q`, up to a controlled cubic remainder.  The
legacy Track 1.B target is the instance `Q = periodicEdgeStencilDirichletAction`;
the Session-202-corrected target is the instance
`Q = canonicalPeriodicMixedAxisStencilAction`. -/
def ReggeLocalQuadraticCorrespondence
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (Q : VertexPotential K → ℝ) : Prop :=
  ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
    ∀ ξ : VertexPotential K, ‖ξ‖ < r →
      ‖reggeAction K hK ξ -
          reggeAction K hK (zeroPotential K) -
          (1 / 2) * Q ξ‖ ≤
        C * ‖ξ‖ ^ (3 : ℕ)

/-- The legacy seven-class endpoint is the parametric correspondence at the
edge-stencil quadratic. -/
theorem edgeStencilLocalCorrespondence_iff
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) :
    CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz ↔
      ReggeLocalQuadraticCorrespondence
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
        (periodicEdgeStencilDirichletAction
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz)) :=
  Iff.rfl

/-- **The corrected Track 1.B endpoint.**  The local correspondence with the
Session-202-corrected quadratic: the rational axis stencil, which the exact
finite audit identifies as the value of the mixed hinge-deficit quadratic. -/
def CanonicalPeriodicAxisStencilLocalCorrespondence
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  ReggeLocalQuadraticCorrespondence
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
    (canonicalPeriodicMixedAxisStencilAction Nx Ny Nz hx hy hz)

/-! ## §2. Quadratic algebra of the two stencils -/

/-- The axis stencil is nonnegative. -/
theorem canonicalPeriodicMixedAxisStencilAction_nonneg
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    0 ≤ canonicalPeriodicMixedAxisStencilAction Nx Ny Nz hx hy hz ξ := by
  unfold canonicalPeriodicMixedAxisStencilAction
  refine Finset.sum_nonneg fun base _ => Finset.sum_nonneg fun d _ => ?_
  dsimp only
  positivity

/-- The axis stencil is exactly quadratically homogeneous. -/
theorem canonicalPeriodicMixedAxisStencilAction_smul
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : ℝ)
    (ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    canonicalPeriodicMixedAxisStencilAction Nx Ny Nz hx hy hz (a • ξ) =
      a ^ (2 : ℕ) * canonicalPeriodicMixedAxisStencilAction Nx Ny Nz hx hy hz ξ := by
  unfold canonicalPeriodicMixedAxisStencilAction
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun base _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  dsimp only
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Quadratic homogeneity transfers to the legacy edge stencil through the
proved identification with the canonical Dirichlet energy. -/
theorem periodicEdgeStencilDirichletAction_smul
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (a : ℝ)
    (ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K) :
    periodicEdgeStencilDirichletAction
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) (a • ξ) =
      a ^ (2 : ℕ) *
        periodicEdgeStencilDirichletAction
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) ξ := by
  rw [← canonicalPeriodicEdgeStencilTarget Nx Ny Nz hx hy hz (a • ξ),
    ← canonicalPeriodicEdgeStencilTarget Nx Ny Nz hx hy hz ξ]
  exact canonicalDirichletEnergy_smul
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK a ξ

/-! ## §3. Rigidity: the Taylor coefficient is unique -/

/-- **RIGIDITY.**  If two quadratically homogeneous candidates both satisfy
the local correspondence on the same complex, they are pointwise equal.  The
quadratic coefficient of a cubic-Taylor expansion is unique, so at most one
stencil can be the true second-order content of the Regge action. -/
theorem reggeLocalQuadraticCorrespondence_quadratic_unique
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (Q₁ Q₂ : VertexPotential K → ℝ)
    (hQ₁ : ∀ (a : ℝ) (ξ : VertexPotential K), Q₁ (a • ξ) = a ^ (2 : ℕ) * Q₁ ξ)
    (hQ₂ : ∀ (a : ℝ) (ξ : VertexPotential K), Q₂ (a • ξ) = a ^ (2 : ℕ) * Q₂ ξ)
    (h₁ : ReggeLocalQuadraticCorrespondence K hK Q₁)
    (h₂ : ReggeLocalQuadraticCorrespondence K hK Q₂) :
    ∀ ξ : VertexPotential K, Q₁ ξ = Q₂ ξ := by
  obtain ⟨r₁, C₁, hr₁, hC₁, hb₁⟩ := h₁
  obtain ⟨r₂, C₂, hr₂, hC₂, hb₂⟩ := h₂
  intro ξ
  by_contra hne
  have hΔpos : 0 < |Q₁ ξ - Q₂ ξ| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set Δ : ℝ := |Q₁ ξ - Q₂ ξ| with hΔdef
  -- Choose the probe scale `t`.
  have hA : (0 : ℝ) < 1 + ‖ξ‖ := by positivity
  have hB : (0 : ℝ) < 1 + 2 * (C₁ + C₂) * ‖ξ‖ ^ (3 : ℕ) := by positivity
  set t : ℝ :=
    min (min r₁ r₂ / (1 + ‖ξ‖)) (Δ / (1 + 2 * (C₁ + C₂) * ‖ξ‖ ^ (3 : ℕ)))
    with ht_def
  have ht_pos : 0 < t := by
    refine lt_min (div_pos (lt_min hr₁ hr₂) hA) (div_pos hΔpos hB)
  -- The scaled probe sits inside both radii.
  have ht_norm : ‖t • ξ‖ = t * ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
  have hsmall : t * ‖ξ‖ < min r₁ r₂ := by
    have h1 : t ≤ min r₁ r₂ / (1 + ‖ξ‖) := min_le_left _ _
    have h2 : ‖ξ‖ < 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
    have hq_pos : 0 < min r₁ r₂ / (1 + ‖ξ‖) := div_pos (lt_min hr₁ hr₂) hA
    calc t * ‖ξ‖ ≤ (min r₁ r₂ / (1 + ‖ξ‖)) * ‖ξ‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg ξ)
      _ < (min r₁ r₂ / (1 + ‖ξ‖)) * (1 + ‖ξ‖) :=
          mul_lt_mul_of_pos_left h2 hq_pos
      _ = min r₁ r₂ := div_mul_cancel₀ _ hA.ne'
  have hsmall₁ : ‖t • ξ‖ < r₁ := by
    rw [ht_norm]; exact lt_of_lt_of_le hsmall (min_le_left _ _)
  have hsmall₂ : ‖t • ξ‖ < r₂ := by
    rw [ht_norm]; exact lt_of_lt_of_le hsmall (min_le_right _ _)
  -- The two cubic bounds at the scaled probe.
  have hb₁' := hb₁ (t • ξ) hsmall₁
  have hb₂' := hb₂ (t • ξ) hsmall₂
  rw [hQ₁ t ξ, Real.norm_eq_abs, ht_norm] at hb₁'
  rw [hQ₂ t ξ, Real.norm_eq_abs, ht_norm] at hb₂'
  -- Triangle inequality forces the quadratic gap below a linear-in-`t` bound.
  have hdiff :
      (reggeAction K hK (t • ξ) - reggeAction K hK (zeroPotential K) -
          (1 / 2) * (t ^ (2 : ℕ) * Q₂ ξ)) -
        (reggeAction K hK (t • ξ) - reggeAction K hK (zeroPotential K) -
          (1 / 2) * (t ^ (2 : ℕ) * Q₁ ξ)) =
        (1 / 2) * t ^ (2 : ℕ) * (Q₁ ξ - Q₂ ξ) := by ring
  have hgap : (1 / 2) * t ^ (2 : ℕ) * Δ ≤ (C₁ + C₂) * (t * ‖ξ‖) ^ (3 : ℕ) := by
    have htri :
        |(1 / 2) * t ^ (2 : ℕ) * (Q₁ ξ - Q₂ ξ)| ≤
          C₂ * (t * ‖ξ‖) ^ (3 : ℕ) + C₁ * (t * ‖ξ‖) ^ (3 : ℕ) := by
      rw [← hdiff]
      exact le_trans (abs_sub _ _) (add_le_add hb₂' hb₁')
    have habs :
        |(1 / 2) * t ^ (2 : ℕ) * (Q₁ ξ - Q₂ ξ)| =
          (1 / 2) * t ^ (2 : ℕ) * Δ := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1/2) * t ^ (2:ℕ))]
    rw [habs] at htri
    linarith
  -- Divide by `t²` and contradict the choice of `t`.
  have ht2_pos : (0 : ℝ) < t ^ (2 : ℕ) := by positivity
  have hΔle : Δ ≤ 2 * (C₁ + C₂) * t * ‖ξ‖ ^ (3 : ℕ) := by
    have hexp : (t * ‖ξ‖) ^ (3 : ℕ) = t ^ (2 : ℕ) * (t * ‖ξ‖ ^ (3 : ℕ)) := by
      ring
    rw [hexp] at hgap
    calc Δ = (1 / 2) * t ^ (2 : ℕ) * Δ * (2 / t ^ (2 : ℕ)) := by
          field_simp
      _ ≤ (C₁ + C₂) * (t ^ (2 : ℕ) * (t * ‖ξ‖ ^ (3 : ℕ))) * (2 / t ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_right hgap (by positivity)
      _ = 2 * (C₁ + C₂) * t * ‖ξ‖ ^ (3 : ℕ) := by
          field_simp
  have ht_le : t ≤ Δ / (1 + 2 * (C₁ + C₂) * ‖ξ‖ ^ (3 : ℕ)) := min_le_right _ _
  have hfinal : Δ < Δ := by
    have hC12 : 0 ≤ C₁ + C₂ := by linarith
    have hfrac :
        2 * (C₁ + C₂) * ‖ξ‖ ^ (3 : ℕ) <
          1 + 2 * (C₁ + C₂) * ‖ξ‖ ^ (3 : ℕ) := by linarith
    calc Δ ≤ 2 * (C₁ + C₂) * t * ‖ξ‖ ^ (3 : ℕ) := hΔle
      _ = t * (2 * (C₁ + C₂) * ‖ξ‖ ^ (3 : ℕ)) := by ring
      _ ≤ (Δ / (1 + 2 * (C₁ + C₂) * ‖ξ‖ ^ (3 : ℕ))) *
            (2 * (C₁ + C₂) * ‖ξ‖ ^ (3 : ℕ)) := by
          refine mul_le_mul_of_nonneg_right ht_le ?_
          positivity
      _ < (Δ / (1 + 2 * (C₁ + C₂) * ‖ξ‖ ^ (3 : ℕ))) *
            (1 + 2 * (C₁ + C₂) * ‖ξ‖ ^ (3 : ℕ)) := by
          refine mul_lt_mul_of_pos_left hfrac ?_
          exact div_pos hΔpos hB
      _ = Δ := div_mul_cancel₀ _ hB.ne'
  exact absurd hfinal (lt_irrefl Δ)

/-- The legacy and corrected endpoints can both hold only if the two stencils
are pointwise equal. -/
theorem both_correspondences_force_equal_quadratics
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hLegacy : CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz)
    (hCorrected : CanonicalPeriodicAxisStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∀ ξ : VertexPotential
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
      periodicEdgeStencilDirichletAction
          (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) ξ =
        canonicalPeriodicMixedAxisStencilAction Nx Ny Nz hx hy hz ξ :=
  reggeLocalQuadraticCorrespondence_quadratic_unique
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
    _ _
    (periodicEdgeStencilDirichletAction_smul Nx Ny Nz hx hy hz)
    (canonicalPeriodicMixedAxisStencilAction_smul Nx Ny Nz hx hy hz)
    ((edgeStencilLocalCorrespondence_iff Nx Ny Nz hx hy hz).mp hLegacy)
    hCorrected

/-- The two stencils differ somewhere (the content of the Session 202 audit
witness, stated as a named proposition). -/
def AxisEdgeStencilQuadraticsDiffer
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz) : Prop :=
  ∃ ξ : VertexPotential
      (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
    periodicEdgeStencilDirichletAction
        (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz) ξ ≠
      canonicalPeriodicMixedAxisStencilAction Nx Ny Nz hx hy hz ξ

/-- **EXCLUSIVITY.**  Given the audit witness, the legacy seven-class endpoint
and the corrected axis endpoint are mutually exclusive: at most one of them is
the true cubic-Taylor statement for the Regge action. -/
theorem not_both_correspondences_of_quadratics_differ
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hdiff : AxisEdgeStencilQuadraticsDiffer Nx Ny Nz hx hy hz) :
    ¬(CanonicalPeriodicEdgeStencilLocalCorrespondence Nx Ny Nz hx hy hz ∧
      CanonicalPeriodicAxisStencilLocalCorrespondence Nx Ny Nz hx hy hz) := by
  rintro ⟨hLegacy, hCorrected⟩
  obtain ⟨ξ, hξ⟩ := hdiff
  exact hξ (both_correspondences_force_equal_quadratics
    Nx Ny Nz hx hy hz hLegacy hCorrected ξ)

/-! ## §4. The D2 hook: the per-tetrahedron bound, parametric in the
quadratic -/

/-- The normalized per-tetrahedron residual bound, proved for an arbitrary
homogeneous quadratic satisfying the cubic bound.  This is the exact bound
the damped-schedule D2 closure consumes, so the whole damped pipeline
transfers to the corrected quadratic the day the corrected gate closes. -/
theorem normalized_regge_sub_half_quadratic_abs_le
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (Q : VertexPotential K → ℝ)
    (hQ : ∀ (a : ℝ) (ξ : VertexPotential K), Q (a • ξ) = a ^ (2 : ℕ) * Q ξ)
    (h0 : reggeAction K hK (zeroPotential K) = 0)
    (r C : ℝ)
    (hb : ∀ ξ : VertexPotential K, ‖ξ‖ < r →
      ‖reggeAction K hK ξ - reggeAction K hK (zeroPotential K) -
        (1 / 2) * Q ξ‖ ≤ C * ‖ξ‖ ^ (3 : ℕ))
    (s : ℝ) (hs : s ≠ 0)
    (ξ : VertexPotential K) (hsmall : ‖s • ξ‖ < r) :
    |reggeAction K hK (s • ξ) / s ^ (2 : ℕ) - (1 / 2) * Q ξ| ≤
      C * |s| * ‖ξ‖ ^ (3 : ℕ) := by
  have hb' := hb (s • ξ) hsmall
  rw [h0, sub_zero, hQ s ξ, Real.norm_eq_abs] at hb'
  have hs2 : (0 : ℝ) < s ^ (2 : ℕ) := by positivity
  have key :
      reggeAction K hK (s • ξ) / s ^ (2 : ℕ) - (1 / 2) * Q ξ =
        (reggeAction K hK (s • ξ) - (1 / 2) * (s ^ (2 : ℕ) * Q ξ)) / s ^ (2 : ℕ) := by
    field_simp
  rw [key, abs_div, abs_of_pos hs2]
  have hnorm3 : ‖s • ξ‖ ^ (3 : ℕ) = |s| ^ (3 : ℕ) * ‖ξ‖ ^ (3 : ℕ) := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow]
  have habs3 : |s| ^ (3 : ℕ) = |s| * s ^ (2 : ℕ) := by
    rw [pow_succ, sq_abs, mul_comm]
  have hdivle :
      |reggeAction K hK (s • ξ) - (1 / 2) * (s ^ (2 : ℕ) * Q ξ)| / s ^ (2 : ℕ) ≤
        (C * ‖s • ξ‖ ^ (3 : ℕ)) / s ^ (2 : ℕ) := by
    gcongr
  refine le_trans hdivle (le_of_eq ?_)
  rw [hnorm3, habs3]
  field_simp

/-- The corrected endpoint feeds the damped D2 pipeline: under the axis
correspondence, the normalized nonlinear Regge action converges to one half
of the axis stencil with the same constructive damping bound used by the
damped-schedule closure. -/
theorem axis_normalized_regge_bound_of_correspondence
    (Nx Ny Nz : ℕ) [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (hx : 2 < Nx) (hy : 2 < Ny) (hz : 2 < Nz)
    (hCorr : CanonicalPeriodicAxisStencilLocalCorrespondence Nx Ny Nz hx hy hz) :
    ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
      ∀ (s : ℝ), s ≠ 0 →
        ∀ ξ : VertexPotential
            (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K,
          ‖s • ξ‖ < r →
          |reggeAction
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
              (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
              (s • ξ) / s ^ (2 : ℕ) -
            (1 / 2) *
              canonicalPeriodicMixedAxisStencilAction Nx Ny Nz hx hy hz ξ| ≤
            C * |s| * ‖ξ‖ ^ (3 : ℕ) := by
  obtain ⟨r, C, hr, hC, hb⟩ := hCorr
  refine ⟨r, C, hr, hC, fun s hs ξ hsmall => ?_⟩
  exact normalized_regge_sub_half_quadratic_abs_le
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).K
    (canonicalEncodedPeriodicFreudenthalTorus Nx Ny Nz hx hy hz).hK
    (canonicalPeriodicMixedAxisStencilAction Nx Ny Nz hx hy hz)
    (canonicalPeriodicMixedAxisStencilAction_smul Nx Ny Nz hx hy hz)
    (canonicalPeriodicReggeAction_zeroPotential_eq_zero_of_flatConfiguration
      Nx Ny Nz hx hy hz
      (canonicalPeriodicFlatConfiguration Nx Ny Nz hx hy hz))
    r C hb s hs ξ hsmall

/-! ## §5. The corrected gate at the certificate scale -/

/-- **The corrected Track 1.B gate at `N = 5`, stated exactly.**  Second-order
Schl\"afli stationarity at `N = 5` is already a theorem, so the corrected
closure at the certificate scale reduces to this single finite coefficient
identity: the explicit-fiber axis-stencil target. -/
abbrev CanonicalPeriodicCorrectedTrack1BGateAtN5 : Prop :=
  CanonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTargetAtN5

/-- **The corrected `N = 5` gate is closed** (2026-06-17). It is discharged by
`FreudenthalAxisStencilCoeffCert.canonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTargetAtN5`,
which proves the explicit-fiber axis-stencil coefficient identity via a finite
`native_decide` certificate over the 125 = 5³ vertex table. Honest caveat: that
certificate's axiom basis includes `Lean.ofReduceBool` and `Lean.trustCompiler`
(compiler trust) on top of `propext / Classical.choice / Quot.sound`. -/
theorem correctedTrack1BGateAtN5_closed : CanonicalPeriodicCorrectedTrack1BGateAtN5 :=
  FreudenthalAxisStencilCoeffCert.canonicalPeriodicMixedHingeDeficitExplicitFiberAxisStencilTargetAtN5

/-- The gate discharges the corrected mixed identification at `N = 5`. -/
theorem correctedMixedTargetAtN5_of_gate
    (hGate : CanonicalPeriodicCorrectedTrack1BGateAtN5) :
    CanonicalPeriodicMixedHingeDeficitAxisStencilTargetAtN5 :=
  canonicalPeriodicMixedHingeDeficitAxisStencilTargetAtN5_of_explicitFiberAxis hGate

/-! ## §6. Status record -/

/-- Corrected Track 1.B scope after this module. -/
structure CorrectedTrack1BStatus where
  corrected_endpoint_formulated : Bool
  axis_stencil_algebra_proved : Bool
  rigidity_proved : Bool
  exclusivity_with_legacy_proved : Bool
  d2_hook_proved : Bool
  stationarity_at_N5_proved : Bool
  gate_open : Bool

/-- The current corrected-quadratic scope: everything formulated and the
supporting theorems proved. The `N = 5` explicit-fiber coefficient gate is now
closed (`gate_open := false`, see `correctedTrack1BGateAtN5_closed`); only the
all-cardinality generalization remains. -/
def correctedTrack1BStatus : CorrectedTrack1BStatus where
  corrected_endpoint_formulated := true
  axis_stencil_algebra_proved := true
  rigidity_proved := true
  exclusivity_with_legacy_proved := true
  d2_hook_proved := true
  stationarity_at_N5_proved := true
  gate_open := false

end

end Track1BCorrectedQuadratic
end Gravity
end IndisputableMonolith
