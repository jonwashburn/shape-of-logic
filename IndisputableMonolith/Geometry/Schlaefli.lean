import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import IndisputableMonolith.Geometry.CayleyMenger
import IndisputableMonolith.Geometry.DihedralAngle

/-!
# Schläfli's Identity

This module formalizes Schläfli's identity for piecewise-flat simplicial
complexes. It is Phase C3 of the program to discharge the Regge deficit
linearization hypothesis on general simplicial complexes.

## Content

For a simplicial `n`-complex `K` with vertex-edge structure fixed, let
`L_e` denote the edge length of edge `e` and `A_h` the area (or
`(n−2)`-volume) of hinge `h`. The dihedral angle of a top simplex `σ`
at a hinge `h ⊂ σ` depends on the edge lengths via Cayley-Menger.

**Schläfli's identity** (Schläfli 1858; see Regge 1961 for the
piecewise-flat version):

  for every edge `e` of `K`,
    `Σ_{σ} Σ_{h ⊂ σ} A_h · (∂θ_σ,h / ∂L_e) = 0`.

Summing only over hinges `h` that meet edge `e`, the classical form is:

  `Σ_h A_h · (∂θ_h / ∂L_e) = 0`

where `θ_h` is the *total* dihedral angle at hinge `h` (sum over the
simplices meeting `h`). This is the identity that makes the Regge
equations reduce from two terms to one:

  δS_Regge / δL_e = Σ_h (∂A_h / ∂L_e) · δ_h + Σ_h A_h · (∂δ_h / ∂L_e)
                  = Σ_h (∂A_h / ∂L_e) · δ_h             ( by Schläfli )
                  = 0                                     ( Regge eqns )

## Status

This identity is *not* trivial; in the Regge literature it is proved
via local integration by parts on each simplex's boundary (see Regge's
original paper or Hartle-Sorkin 1981). Mathlib does not yet have the
ambient geometric-calculus infrastructure to reproduce this proof.

We therefore record Schläfli's identity as a *named hypothesis*, matching
the pattern of `NonlinearConvergence.regge_to_eh_convergence_axiom` and
`CayleyMenger.TetVolumeIdentity`. Downstream consumers (Phase C4 and
Phase C5) thread it explicitly, so that callers can see exactly which
classical fact is being used.

Zero `sorry`, zero new `axiom`.

## References

- Schläfli, L. (1858). *On the multiple integral ∫^n d x d y · · · d z.*
  Quarterly Journal of Pure and Applied Mathematics.
- Regge, T. (1961). *General relativity without coordinates.*
  Nuovo Cimento 19, 558–571.
- Hartle, J. B., Sorkin, R. (1981). *Boundary terms in the action for
  the Regge calculus.* General Relativity and Gravitation 13, 541–549.
- Brewin, L. C. (2000). *The Riemann and extrinsic curvature tensors in
  the Regge calculus.* Class. Quantum Grav. 17, 545.
-/

namespace IndisputableMonolith
namespace Geometry
namespace Schlaefli

open CayleyMenger DihedralAngle

noncomputable section

/-! ## §1. Edge / hinge book-keeping -/

/-- Abstract edge-length data for a simplicial complex with finitely many
    edges indexed by `Fin nE`. -/
structure SimplicialEdgeData (nE : ℕ) where
  len : Fin nE → ℝ
  len_pos : ∀ e, 0 < len e

/-- Abstract hinge data: each hinge knows its area and the collection of
    dihedral angles of the top simplices meeting it. The *total* dihedral
    at the hinge is `Σ θ_σ`; the deficit is `2π − Σ θ_σ`. -/
structure SimplicialHingeData where
  area : ℝ
  area_nonneg : 0 ≤ area
  dihedrals : List DihedralAngleData

namespace SimplicialHingeData

/-- Sum of the dihedral angles at the hinge. -/
def totalTheta (h : SimplicialHingeData) : ℝ :=
  DihedralAngle.sumThetas h.dihedrals

/-- Deficit at the hinge: `2π − Σ θ`. -/
def deficit (h : SimplicialHingeData) : ℝ :=
  DihedralAngle.deficit h.dihedrals

theorem deficit_eq (h : SimplicialHingeData) :
    h.deficit = 2 * Real.pi - h.totalTheta := rfl

end SimplicialHingeData

/-! ## §2. Variational data

For Schläfli's identity we need derivatives of `θ_h` with respect to each
edge length `L_e`. We package these as a matrix of real numbers, one per
(hinge, edge) pair. The identity below constrains this matrix. -/

/-- A matrix of deficit-angle derivatives: `dThetadL h e` is intended
    to be `∂(totalTheta h) / ∂(len e)`. -/
structure DeficitDerivativeMatrix (nH nE : ℕ) where
  dThetadL : Fin nH → Fin nE → ℝ

/-! ## §3. Schläfli's identity as a hypothesis -/

/-- **SCHLÄFLI'S IDENTITY** (piecewise-flat form).

    For a finite collection of hinges (indexed by `Fin nH`) with areas
    `A_h` and a matrix `dThetadL` of dihedral-angle derivatives with
    respect to edge lengths, the weighted sum vanishes:

    `∀ e, Σ_h A_h · (∂θ_h / ∂L_e) = 0`.

    This is the classical local identity; see Regge (1961, eq. 2.8) and
    Brewin (2000). We record it as a hypothesis structure because the
    full proof requires boundary-integration machinery not yet in
    Mathlib. -/
def SchlaefliIdentity {nH nE : ℕ}
    (hinges : Fin nH → SimplicialHingeData)
    (M : DeficitDerivativeMatrix nH nE) : Prop :=
  ∀ e : Fin nE,
    (∑ h : Fin nH, (hinges h).area * M.dThetadL h e) = 0

/-! ## §4. Consequences of Schläfli's identity

Schläfli's identity makes the second term of the Regge variation vanish,
leaving only the `∂A/∂L · δ` piece. This is what the Regge equations of
motion look like. -/

/-- Under Schläfli, the `Σ A · dθ/dL` term in the Regge variation is
    identically zero. -/
theorem schlaefli_kills_dtheta {nH nE : ℕ}
    (hinges : Fin nH → SimplicialHingeData)
    (M : DeficitDerivativeMatrix nH nE)
    (hS : SchlaefliIdentity hinges M) (e : Fin nE) :
    (∑ h : Fin nH, (hinges h).area * M.dThetadL h e) = 0 := hS e

/-- Total deficit functional: `Σ_h A_h · δ_h = Σ_h A_h · (2π − totalTheta h)`. -/
def totalDeficit {nH : ℕ} (hinges : Fin nH → SimplicialHingeData) : ℝ :=
  ∑ h : Fin nH, (hinges h).area * (hinges h).deficit

/-! ## §5. Flat baseline -/

/-- If every hinge satisfies the flat-sum condition, the total deficit
    vanishes. -/
theorem totalDeficit_flat {nH : ℕ}
    (hinges : Fin nH → SimplicialHingeData)
    (hFlat : ∀ h : Fin nH,
      DihedralAngle.FlatSumCondition (hinges h).dihedrals) :
    totalDeficit hinges = 0 := by
  unfold totalDeficit
  apply Finset.sum_eq_zero
  intro h _
  have : (hinges h).deficit = 0 := by
    unfold SimplicialHingeData.deficit
    exact DihedralAngle.deficit_eq_zero_of_flat _ (hFlat h)
  rw [this]; ring

/-! ## §6. Certificate -/

/-- Phase C3 certificate. -/
structure SchlaefliCert where
  flat_total_zero : ∀ {nH : ℕ} (hinges : Fin nH → SimplicialHingeData),
    (∀ h, DihedralAngle.FlatSumCondition (hinges h).dihedrals) →
    totalDeficit hinges = 0
  schlaefli_kills_sum : ∀ {nH nE : ℕ}
    (hinges : Fin nH → SimplicialHingeData)
    (M : DeficitDerivativeMatrix nH nE),
    SchlaefliIdentity hinges M →
    ∀ e : Fin nE,
      (∑ h : Fin nH, (hinges h).area * M.dThetadL h e) = 0

theorem schlaefliCert : SchlaefliCert where
  flat_total_zero := fun hinges hFlat => totalDeficit_flat hinges hFlat
  schlaefli_kills_sum := fun hinges M hS e => schlaefli_kills_dtheta hinges M hS e

end

end Schlaefli
end Geometry
end IndisputableMonolith
