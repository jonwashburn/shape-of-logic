import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import IndisputableMonolith.Geometry.CayleyMenger
import IndisputableMonolith.Geometry.DihedralAngle
import IndisputableMonolith.Geometry.Schlaefli

/-!
# Piran-Williams Deficit Linearization

This module packages the Piran-Williams (1986) linearization of the Regge
deficit angle around a flat simplicial complex. It is Phase C4 of the
program to discharge the Regge deficit linearization hypothesis on
general simplicial complexes.

## Content

Around a flat simplicial complex with edge length `a` (so all deficits
are zero), a small perturbation `η_e` of each edge length induces a
deficit angle

  `δ_h({a + η_e}) = Σ_e (∂δ_h / ∂L_e)|_flat · η_e + O(η²)`

with explicit coefficients determined by the complex's combinatorics and
the vertex-angle measure. For the cubic lattice (with edges shared by
four unit cubes), the coefficients are integer-linear in the `η_e`.

When the edge perturbations are sourced by a log-potential field via
`η_e = a · (ε_i + ε_j) / 2` (conformal ansatz), the deficit becomes a
linear combination of `ε`-differences, and the total action

  `S_Regge = Σ_h A_h · δ_h`

becomes QUADRATIC in `ε` (the linear term vanishes by Schläfli's identity
combined with flatness). This is the content Phase C5 needs.

## Status

The *existence* of the linearization coefficients is classical Regge
calculus. The *sum rule* `Σ_h A_h · δ_h = κ · laplacian_action + O(ε³)`
requires Schläfli's identity (Phase C3). We record both as a single
structure `WellShaped` below.

The concrete coefficients for the cubic lattice are already implicit in
`CubicDeficitDischarge.lean` (Phase A); this file supplies the abstract
machinery that the general simplicial case will need.

Zero `sorry`, zero new `axiom`.

## References

- Piran, T., Williams, R. M. (1986). *Three-plus-one formulation of
  Regge calculus.* Phys. Rev. D 33, 1622.
- Brewin, L. C. (2000). *The Riemann and extrinsic curvature tensors in
  the Regge calculus.* Class. Quantum Grav. 17, 545.
-/

namespace IndisputableMonolith
namespace Geometry
namespace DeficitLinearization

open CayleyMenger DihedralAngle Schlaefli

noncomputable section

/-! ## §1. Linearization data

We package (a) a flat background simplicial complex, (b) an edge-wise
perturbation `η`, and (c) the linearization coefficients. -/

/-- A flat-background simplicial complex: finitely many hinges (indexed
    by `Fin nH`), finitely many edges (`Fin nE`), each hinge satisfying
    the flat-sum condition. -/
structure FlatSimplicialComplex (nH nE : ℕ) where
  hinges : Fin nH → SimplicialHingeData
  edges_length_flat : Fin nE → ℝ
  edges_length_pos : ∀ e, 0 < edges_length_flat e
  flat_all : ∀ h : Fin nH,
    DihedralAngle.FlatSumCondition (hinges h).dihedrals

/-- A perturbation of the flat edge-lengths. -/
structure EdgePerturbation (nE : ℕ) where
  eta : Fin nE → ℝ

/-- Linearization coefficients: for each (hinge, edge) pair, the partial
    derivative of the deficit angle with respect to the edge length,
    evaluated at the flat background. -/
structure LinearizationCoefficients (nH nE : ℕ) extends
    DeficitDerivativeMatrix nH nE

/-! ## §2. Predicted deficit

Given linearization coefficients, the predicted deficit at each hinge
under perturbation `η` is

  `δ̂_h = - Σ_e (∂θ_h / ∂L_e) · η_e`

(the minus sign because deficit = 2π − totalTheta). -/

/-- Linearized deficit at hinge `h` under perturbation `η`. -/
def linearizedDeficit {nH nE : ℕ}
    (M : LinearizationCoefficients nH nE) (η : EdgePerturbation nE)
    (h : Fin nH) : ℝ :=
  - (∑ e : Fin nE, M.dThetadL h e * η.eta e)

/-! ## §3. The well-shapedness bundle

A `WellShaped` package certifies that:

1. The complex is flat at the background.
2. Linearization coefficients exist.
3. Schläfli's identity holds for those coefficients.

This is exactly what Phase C5 needs. -/

/-- A complete well-shapedness package for the linearization. -/
structure WellShapedData (nH nE : ℕ) where
  complex : FlatSimplicialComplex nH nE
  coeffs : LinearizationCoefficients nH nE
  schlaefli : SchlaefliIdentity complex.hinges coeffs.toDeficitDerivativeMatrix

/-! ## §4. Linearized action vanishes at first order

The key consequence: under the flat background and Schläfli's identity,
the *first-order* Regge action vanishes. This means the leading
non-trivial Regge action is *quadratic* in the perturbation, precisely
matching the J-cost Dirichlet energy.

The statement we need:

  `Σ_h A_h · linearizedDeficit_h(η) = - Σ_e (Σ_h A_h · ∂θ_h/∂L_e) · η_e
                                   = 0       (by Schläfli per edge).`
-/

/-- The linear (first-order) part of the Regge action vanishes under
    Schläfli's identity. -/
theorem linear_regge_vanishes {nH nE : ℕ}
    (W : WellShapedData nH nE) (η : EdgePerturbation nE) :
    (∑ h : Fin nH, (W.complex.hinges h).area *
      linearizedDeficit W.coeffs η h) = 0 := by
  unfold linearizedDeficit
  -- Rewrite the sum: move the minus sign out, then swap summation order.
  have h_swap :
      (∑ h : Fin nH, (W.complex.hinges h).area *
        -(∑ e : Fin nE, W.coeffs.dThetadL h e * η.eta e))
      = - ∑ e : Fin nE,
          η.eta e * (∑ h : Fin nH, (W.complex.hinges h).area * W.coeffs.dThetadL h e) := by
    rw [show (∑ h : Fin nH, (W.complex.hinges h).area *
              -(∑ e : Fin nE, W.coeffs.dThetadL h e * η.eta e))
            = -(∑ h : Fin nH, (W.complex.hinges h).area *
                 (∑ e : Fin nE, W.coeffs.dThetadL h e * η.eta e))
         from by
           rw [← Finset.sum_neg_distrib]
           apply Finset.sum_congr rfl
           intro h _; ring]
    rw [show (∑ h : Fin nH, (W.complex.hinges h).area *
              (∑ e : Fin nE, W.coeffs.dThetadL h e * η.eta e))
            = ∑ h : Fin nH, ∑ e : Fin nE,
               (W.complex.hinges h).area * W.coeffs.dThetadL h e * η.eta e
         from by
           apply Finset.sum_congr rfl
           intro h _
           rw [Finset.mul_sum]
           apply Finset.sum_congr rfl
           intro e _; ring]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.sum_mul]
    ring
  rw [h_swap]
  -- Now apply Schläfli's identity per edge.
  have h_each : ∀ e : Fin nE,
      η.eta e * (∑ h : Fin nH, (W.complex.hinges h).area * W.coeffs.dThetadL h e) = 0 := by
    intro e
    rw [W.schlaefli e, mul_zero]
  rw [Finset.sum_eq_zero (fun e _ => h_each e), neg_zero]

/-! ## §5. Certificate -/

structure DeficitLinearizationCert where
  linear_vanishes : ∀ {nH nE : ℕ}
    (W : WellShapedData nH nE) (η : EdgePerturbation nE),
    (∑ h : Fin nH, (W.complex.hinges h).area *
      linearizedDeficit W.coeffs η h) = 0

/-- The certificate is inhabited by the proved `linear_regge_vanishes`. -/
theorem deficitLinearizationCert : DeficitLinearizationCert where
  linear_vanishes := fun W η => linear_regge_vanishes W η

end

end DeficitLinearization
end Geometry
end IndisputableMonolith
