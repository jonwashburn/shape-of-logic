import Mathlib
import IndisputableMonolith.Gravity.QuantumChannel.AmplitudeLinearForced

/-!
# Gravity quantum channel: mediator universality boundary

The vector-level no-go lives in
`Gravity.QuantumChannel.AmplitudeLinearForced` and
`Gravity.QuantumChannel.NoClassicalMediator`; it is not re-proved here.
That result says a vector response on `Signal8` cannot be simultaneously
amplitude-linear, density-only, and nonzero.

This module proves the exact boundary of the universality premise. For every
fixed update `U`, the density-level map `rho ↦ U * rho * Uᴴ` exists, reproduces
the amplitude dynamics on pure states, is phase-insensitive on pure densities,
and is trace-preserving when `U` is unitary. Thus algebra alone does not
exclude update-dependent mediation.

The new density-level no-go is also formalized: even at density level, no
single fixed map serves all unitary updates. The identity update and the
0-1 swap already disagree on the same input density.

Honesty note on strength: the no-go is a quantifier-order fact (a fixed
`Phi` with `forall U` versus `forall U` each with its own `Phi`), witnessed
by a one-shot clash of two unitaries on one pure density. Its value is that
it makes the strong reading of the universality premise exact and
kernel-checked, not that it is a deep new density-level obstruction. It
formalizes the strongest reading of universality (one fixed map implementing
every unitary update simultaneously); weaker readings (update-parameterized
families, a single CP architecture) are untouched and remain the MODEL
premise. This module does not remove the premise, and it must never be
quoted as "algebra forbids density mediation": the positive half proves the
opposite for every fixed update.

Zero `sorry`. Zero new axioms.
-/

namespace IndisputableMonolith
namespace Gravity
namespace QuantumChannel
namespace MediatorUniversalityBoundary

open AmplitudeLinearForced

noncomputable section

/-! ## Pure densities -/

/-- The pure-state density matrix `|psi><psi|`. -/
def densityOf (psi : Signal8) : Matrix (Fin 8) (Fin 8) Complex :=
  Matrix.of fun i j => psi i * star (psi j)

/-- Pure-state densities are invariant under unit-modulus global phase. -/
theorem densityOf_phase_invariant
    (c : Complex) (hc : ‖c‖ = 1) (psi : Signal8) :
    densityOf (c • psi) = densityOf psi := by
  ext i j
  unfold densityOf
  simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  have hnormSqReal : Complex.normSq c = 1 := by
    rw [Complex.normSq_eq_norm_sq, hc]
    norm_num
  have hmul : c * star c = 1 := by
    calc
      c * star c = (Complex.normSq c : Complex) := by
        rw [Complex.star_def, Complex.mul_conj]
      _ = 1 := by
        exact_mod_cast hnormSqReal
  calc
    (c * psi i) * star (c * psi j)
        = (c * star c) * (psi i * star (psi j)) := by
          rw [star_mul]
          ring
    _ = psi i * star (psi j) := by
      rw [hmul, one_mul]

/-- The trace of a pure density is the sum of squared amplitudes. -/
theorem trace_densityOf (psi : Signal8) :
    (densityOf psi).trace = ∑ k : Fin 8, psi k * star (psi k) := by
  simp [densityOf, Matrix.trace]

/-- The density of the first basis vector is nonzero. -/
theorem densityOf_single_ne_zero :
    densityOf (Pi.single (0 : Fin 8) (1 : Complex)) ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 8)) (0 : Fin 8)
  simp [densityOf] at h00

/-! ## Per-update density mediators -/

/-- The density-level conjugation channel `rho ↦ U * rho * Uᴴ`. -/
def conjugationChannel
    (U : Matrix (Fin 8) (Fin 8) Complex)
    (rho : Matrix (Fin 8) (Fin 8) Complex) :
    Matrix (Fin 8) (Fin 8) Complex :=
  U * rho * U.conjTranspose

/-- Conjugation by `U` reproduces the amplitude update on pure states.
No unitarity hypothesis is needed. -/
theorem conjugationChannel_reproduces
    (U : Matrix (Fin 8) (Fin 8) Complex) (psi : Signal8) :
    conjugationChannel U (densityOf psi) = densityOf (U.mulVec psi) := by
  ext i j
  simp only [conjugationChannel, densityOf, Matrix.mul_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, star_sum, star_mul,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

/-- Conjugation by a unitary matrix is trace-preserving. -/
theorem conjugationChannel_trace_preserving
    (U : Matrix (Fin 8) (Fin 8) Complex)
    (hU : U.conjTranspose * U = 1)
    (rho : Matrix (Fin 8) (Fin 8) Complex) :
    (conjugationChannel U rho).trace = rho.trace := by
  unfold conjugationChannel
  rw [Matrix.trace_mul_cycle U rho U.conjTranspose]
  rw [hU, one_mul]

/-- For every fixed update, an update-dependent density mediator exists. -/
theorem per_update_density_mediator_exists
    (U : Matrix (Fin 8) (Fin 8) Complex) :
    ∃ Phi :
        Matrix (Fin 8) (Fin 8) Complex →
          Matrix (Fin 8) (Fin 8) Complex,
      ∀ psi : Signal8, Phi (densityOf psi) = densityOf (U.mulVec psi) :=
  ⟨conjugationChannel U, conjugationChannel_reproduces U⟩

/-! ## No universal density mediator -/

private def basis0 : Signal8 :=
  Pi.single (0 : Fin 8) (1 : Complex)

private def basis1 : Signal8 :=
  Pi.single (1 : Fin 8) (1 : Complex)

private def swap01 : Equiv.Perm (Fin 8) :=
  Equiv.swap (0 : Fin 8) 1

private def swapMatrix : Matrix (Fin 8) (Fin 8) Complex :=
  Matrix.swap Complex (0 : Fin 8) 1

private theorem swapMatrix_unitary :
    swapMatrix.conjTranspose * swapMatrix = 1 := by
  simp [swapMatrix, Matrix.swap_mul_self]

private theorem swapMatrix_mulVec_basis0 :
    swapMatrix.mulVec basis0 = basis1 := by
  calc
    swapMatrix.mulVec basis0 = basis0 ∘ swap01 := by
      simpa [swapMatrix, swap01] using
        Matrix.swap_mulVec (R := Complex) (i := (0 : Fin 8)) (j := 1) basis0
    _ = basis1 := by
      funext i
      show basis0 (swap01 i) = basis1 i
      fin_cases i <;>
        simp [basis0, basis1, swap01, Equiv.swap_apply_def, Pi.single_apply]

private theorem densityOf_basis0_ne_densityOf_basis1 :
    densityOf basis0 ≠ densityOf basis1 := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 8)) (0 : Fin 8)
  simp [basis0, basis1, densityOf] at h00

/-- No single fixed density-level mediator serves all unitary updates. -/
theorem no_universal_density_mediator :
    ¬ ∃ Phi :
        Matrix (Fin 8) (Fin 8) Complex →
          Matrix (Fin 8) (Fin 8) Complex,
      ∀ U : Matrix (Fin 8) (Fin 8) Complex,
        U.conjTranspose * U = 1 →
          ∀ psi : Signal8,
            Phi (densityOf psi) = densityOf (U.mulVec psi) := by
  rintro ⟨Phi, hPhi⟩
  have hId :
      Phi (densityOf basis0) = densityOf basis0 := by
    have h := hPhi (1 : Matrix (Fin 8) (Fin 8) Complex)
      (by rw [Matrix.conjTranspose_one, one_mul]) basis0
    rwa [Matrix.one_mulVec] at h
  have hSwap :
      Phi (densityOf basis0) = densityOf basis1 := by
    have h := hPhi swapMatrix swapMatrix_unitary basis0
    rwa [swapMatrix_mulVec_basis0] at h
  exact densityOf_basis0_ne_densityOf_basis1 (hId.symm.trans hSwap)

/-! ## Boundary package -/

/-- The exact mediator-universality boundary: every fixed update has a
density-level mediator, but no one mediator works for all unitary updates. -/
theorem mediator_universality_boundary :
    (∀ U : Matrix (Fin 8) (Fin 8) Complex,
      ∃ Phi :
          Matrix (Fin 8) (Fin 8) Complex →
            Matrix (Fin 8) (Fin 8) Complex,
        ∀ psi : Signal8, Phi (densityOf psi) = densityOf (U.mulVec psi)) ∧
    (¬ ∃ Phi :
        Matrix (Fin 8) (Fin 8) Complex →
          Matrix (Fin 8) (Fin 8) Complex,
      ∀ U : Matrix (Fin 8) (Fin 8) Complex,
        U.conjTranspose * U = 1 →
          ∀ psi : Signal8,
            Phi (densityOf psi) = densityOf (U.mulVec psi)) :=
  ⟨fun U => per_update_density_mediator_exists U,
    no_universal_density_mediator⟩

end

end MediatorUniversalityBoundary
end QuantumChannel
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.QuantumChannel.MediatorUniversalityBoundary.conjugationChannel_reproduces
#print axioms IndisputableMonolith.Gravity.QuantumChannel.MediatorUniversalityBoundary.no_universal_density_mediator
#print axioms IndisputableMonolith.Gravity.QuantumChannel.MediatorUniversalityBoundary.mediator_universality_boundary
