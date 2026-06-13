import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Gravity.Connection

/-!
# Riemann Curvature Tensor in Coordinates

Defines the Riemann curvature tensor from Christoffel symbols and
proves its algebraic symmetries and the algebraic Bianchi identity.

## Key Results

- `riemann_tensor`: R^rho_{sigma mu nu} in terms of Christoffel symbols and their derivatives
- `riemann_antisymmetric_last_two`: R^rho_{sigma mu nu} = -R^rho_{sigma nu mu}
- `algebraic_bianchi`: R^rho_{[sigma mu nu]} = 0
- `riemann_flat_vanishes`: R = 0 for flat (Minkowski) spacetime
-/

namespace IndisputableMonolith
namespace Gravity
namespace RiemannTensor

open Connection

/-! ## Riemann Tensor Definition -/

/-- The Riemann curvature tensor in local coordinates:
    R^rho_{sigma mu nu} = d_mu Gamma^rho_{nu sigma} - d_nu Gamma^rho_{mu sigma}
                         + Gamma^rho_{mu lambda} Gamma^lambda_{nu sigma}
                         - Gamma^rho_{nu lambda} Gamma^lambda_{mu sigma}

    Inputs:
    - gamma: Christoffel symbols Gamma^rho_{mu nu}
    - dgamma: derivatives d_lambda Gamma^rho_{mu nu} -/
noncomputable def riemann_tensor
    (gamma : Idx → Idx → Idx → ℝ)
    (dgamma : Idx → Idx → Idx → Idx → ℝ)
    (rho sigma mu nu : Idx) : ℝ :=
  dgamma mu rho nu sigma - dgamma nu rho mu sigma +
  ∑ lambda : Idx, (gamma rho mu lambda * gamma lambda nu sigma) -
  ∑ lambda : Idx, (gamma rho nu lambda * gamma lambda mu sigma)

/-! ## Algebraic Symmetries -/

/-- R^rho_{sigma mu nu} is antisymmetric in the last two indices:
    R^rho_{sigma mu nu} = -R^rho_{sigma nu mu}.

    Proof: swapping mu <-> nu negates the d_mu Gamma - d_nu Gamma terms
    and swaps the quadratic Gamma terms. -/
theorem riemann_antisymmetric_last_two
    (gamma : Idx → Idx → Idx → ℝ)
    (dgamma : Idx → Idx → Idx → Idx → ℝ)
    (rho sigma mu nu : Idx) :
    riemann_tensor gamma dgamma rho sigma mu nu =
    -(riemann_tensor gamma dgamma rho sigma nu mu) := by
  simp only [riemann_tensor]
  ring

/-- For flat spacetime (all Gamma = 0, all dGamma = 0), the Riemann tensor vanishes. -/
theorem riemann_flat_vanishes (rho sigma mu nu : Idx) :
    riemann_tensor (fun _ _ _ => 0) (fun _ _ _ _ => 0) rho sigma mu nu = 0 := by
  simp [riemann_tensor]

/-! ## Algebraic Bianchi Identity -/

/-- The algebraic (first) Bianchi identity:
    R^rho_{sigma mu nu} + R^rho_{mu nu sigma} + R^rho_{nu sigma mu} = 0

    This is a consequence of the torsion-free condition (symmetric Christoffel). -/
theorem algebraic_bianchi
    (gamma : Idx → Idx → Idx → ℝ)
    (dgamma : Idx → Idx → Idx → Idx → ℝ)
    (h_sym : ∀ rho mu nu, gamma rho mu nu = gamma rho nu mu)
    (h_dsym : ∀ lambda rho mu nu, dgamma lambda rho mu nu = dgamma lambda rho nu mu)
    (rho sigma mu nu : Idx) :
    riemann_tensor gamma dgamma rho sigma mu nu +
    riemann_tensor gamma dgamma rho mu nu sigma +
    riemann_tensor gamma dgamma rho nu sigma mu = 0 := by
  have anti1 := riemann_antisymmetric_last_two gamma dgamma rho sigma mu nu
  have anti2 := riemann_antisymmetric_last_two gamma dgamma rho mu nu sigma
  have anti3 := riemann_antisymmetric_last_two gamma dgamma rho nu sigma mu
  simp only [riemann_tensor] at *
  have quad_cancel : ∀ x : Idx,
    (gamma rho mu x * gamma x nu sigma - gamma rho nu x * gamma x mu sigma) +
    (gamma rho nu x * gamma x sigma mu - gamma rho sigma x * gamma x nu mu) +
    (gamma rho sigma x * gamma x mu nu - gamma rho mu x * gamma x sigma nu) = 0 := by
    intro x
    rw [h_sym x nu sigma, h_sym x mu sigma, h_sym x sigma mu,
        h_sym x nu mu, h_sym x mu nu, h_sym x sigma nu]; ring
  have h_sums : (∑ x : Idx, (gamma rho mu x * gamma x nu sigma - gamma rho nu x * gamma x mu sigma)) +
    (∑ x : Idx, (gamma rho nu x * gamma x sigma mu - gamma rho sigma x * gamma x nu mu)) +
    (∑ x : Idx, (gamma rho sigma x * gamma x mu nu - gamma rho mu x * gamma x sigma nu)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun x _ => quad_cancel x)
  have key : ∀ x : Idx,
    (gamma rho mu x * gamma x nu sigma - gamma rho nu x * gamma x mu sigma) +
    (gamma rho nu x * gamma x sigma mu - gamma rho sigma x * gamma x nu mu) +
    (gamma rho sigma x * gamma x mu nu - gamma rho mu x * gamma x sigma nu) = 0 := by
    intro x; rw [h_sym x nu sigma, h_sym x mu sigma, h_sym x sigma mu,
                  h_sym x nu mu, h_sym x mu nu, h_sym x sigma nu]; ring
  have sum_zero :
    (∑ x : Idx, (gamma rho mu x * gamma x nu sigma - gamma rho nu x * gamma x mu sigma)) +
    (∑ x : Idx, (gamma rho nu x * gamma x sigma mu - gamma rho sigma x * gamma x nu mu)) +
    (∑ x : Idx, (gamma rho sigma x * gamma x mu nu - gamma rho mu x * gamma x sigma nu)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun x _ => key x)
  have neg_flip : ∀ (f g : Idx → ℝ),
    ∑ x : Idx, (f x - g x) = -(∑ x : Idx, (g x - f x)) := by
    intros f g
    have : ∀ x ∈ Finset.univ, f x - g x = -(g x - f x) := by intros; ring
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
  rw [h_dsym mu rho nu sigma, h_dsym nu rho mu sigma, h_dsym nu rho sigma mu,
      h_dsym sigma rho nu mu, h_dsym sigma rho mu nu, h_dsym mu rho sigma nu]
  have full_sum :
    (∑ x : Idx, (gamma rho mu x * gamma x nu sigma)) -
    (∑ x : Idx, (gamma rho nu x * gamma x mu sigma)) +
    ((∑ x : Idx, (gamma rho nu x * gamma x sigma mu)) -
     (∑ x : Idx, (gamma rho sigma x * gamma x nu mu))) +
    ((∑ x : Idx, (gamma rho sigma x * gamma x mu nu)) -
     (∑ x : Idx, (gamma rho mu x * gamma x sigma nu))) = 0 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun x _ => key x)
  linarith

/-! ## Certificate -/

structure RiemannCert where
  antisymmetric : ∀ gamma dgamma rho sigma mu nu,
    riemann_tensor gamma dgamma rho sigma mu nu =
    -(riemann_tensor gamma dgamma rho sigma nu mu)
  flat_vanishes : ∀ rho sigma mu nu,
    riemann_tensor (fun _ _ _ => 0) (fun _ _ _ _ => 0) rho sigma mu nu = 0

theorem riemann_cert : RiemannCert where
  antisymmetric := riemann_antisymmetric_last_two
  flat_vanishes := riemann_flat_vanishes

end RiemannTensor
end Gravity
end IndisputableMonolith
