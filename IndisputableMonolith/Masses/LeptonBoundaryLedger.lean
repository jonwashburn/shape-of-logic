import Mathlib
import IndisputableMonolith.Masses.LeptonTorsionKernel

/-!
# Lepton Boundary Ledger

This module is the panel-directed `L1a` finite certificate for the leading
charged-lepton torsion constant.

It proves the formalizable part now:

* one primitive Q3 boundary ledger cycle has content `1`;
* CPM push-forward over `Fin n` channels is additive, so the multiplicity is `n`;
* a trace-unital boundary density on total Q3 boundary measure has the unique value
  `n * leadingBoundaryQuantum = n/(4π)`.

Honest boundary: this does not yet prove that the physical charged-lepton channel
must satisfy the trace-unital admissibility predicate. That is the remaining L1
bridge. This file only removes the free scalar once trace-unitality is supplied.
-/

namespace IndisputableMonolith
namespace Masses
namespace LeptonBoundaryLedger

open Constants.AlphaDerivation
open LeptonTorsionKernel

noncomputable section

/-- The primitive Q3 boundary ledger cycle after the CPM quotient has one
undistinguished boundary content carrier. -/
abbrev PrimitiveQ3BoundaryCycle := Unit

/-- Primitive boundary content. This is the integer multiplicity source, not a
solid-angle normalization and not a face count. -/
def primitiveContent (_ : PrimitiveQ3BoundaryCycle) : ℕ :=
  1

/-- The primitive Q3 boundary ledger has content one. -/
theorem primitiveContent_eq_one (c : PrimitiveQ3BoundaryCycle) :
    primitiveContent c = 1 := rfl

/-- CPM channel multiplicity: additive push-forward over `n` independent charged
recognition channels. -/
def cpmChannelMultiplicity (n : ℕ) : ℕ :=
  Fintype.card (Fin n)

/-- The CPM push-forward has integer multiplicity `n`, not parity and not an
average over channels. -/
theorem cpmChannelMultiplicity_eq (n : ℕ) :
    cpmChannelMultiplicity n = n := by
  simp [cpmChannelMultiplicity]

/-- Boundary content after summing the primitive ledger over `n` channels. -/
def additiveBoundaryContent (n : ℕ) : ℝ :=
  ∑ _ : Fin n, (primitiveContent () : ℝ)

/-- Additive boundary content is exactly the channel count. -/
theorem additiveBoundaryContent_eq (n : ℕ) :
    additiveBoundaryContent n = n := by
  simp [additiveBoundaryContent, primitiveContent]

/-- A boundary density is trace-unital for `n` channels when integrating it over
the Q3 boundary measure returns the channel multiplicity. -/
def traceUnitalBoundaryDensity (n : ℕ) (lam : ℝ) : Prop :=
  solid_angle_Q3 * lam = n

/-- The normalized boundary density selected by the Q3 boundary quantum. -/
def normalizedBoundaryDensity (n : ℕ) : ℝ :=
  (n : ℝ) * leadingBoundaryQuantum

private theorem solid_angle_Q3_ne_zero : solid_angle_Q3 ≠ 0 := by
  rw [solid_angle_Q3_eq]
  exact mul_ne_zero (by norm_num) Real.pi_ne_zero

/-- The normalized density is trace-unital. -/
theorem normalizedBoundaryDensity_traceUnital (n : ℕ) :
    traceUnitalBoundaryDensity n (normalizedBoundaryDensity n) := by
  unfold traceUnitalBoundaryDensity normalizedBoundaryDensity leadingBoundaryQuantum
  field_simp [solid_angle_Q3_ne_zero]

/-- Trace-unitality removes the free scalar: any constant Q3 boundary density with
total trace `n` must be `n` copies of the inverse Q3 boundary quantum. -/
theorem boundaryDensityTraceUnital_unique {n : ℕ} {lam : ℝ}
    (h : traceUnitalBoundaryDensity n lam) :
    lam = (n : ℝ) * leadingBoundaryQuantum := by
  unfold traceUnitalBoundaryDensity at h
  unfold leadingBoundaryQuantum
  rw [← h]
  field_simp [solid_angle_Q3_ne_zero]

/-- The normalized density is the advertised `n/(4π)` value. -/
theorem normalizedBoundaryDensity_eq (n : ℕ) :
    normalizedBoundaryDensity n = (n : ℝ) / (4 * Real.pi) := by
  unfold normalizedBoundaryDensity
  rw [leadingBoundaryQuantum_eq]
  ring

/-- The one-channel case gives the leading charged-lepton boundary quantum. -/
theorem normalizedBoundaryDensity_one :
    normalizedBoundaryDensity 1 = 1 / (4 * Real.pi) := by
  rw [normalizedBoundaryDensity_eq]
  norm_num

/-- The three-channel case gives the structural quark-side covariance check. -/
theorem normalizedBoundaryDensity_three :
    normalizedBoundaryDensity 3 = 3 / (4 * Real.pi) := by
  rw [normalizedBoundaryDensity_eq]
  norm_num

/-! ## L1b scalar-killer engine -/

/-- A nonzero idempotent channel projector admits no nonzero scalar rescaling
that remains idempotent except the trivial scalar `1`.

This is the carrier-independent algebraic core named by the panel: once the
charged channel is proved to be a nonzero idempotent, the surviving scalar `s`
from the L1 admissibility bridge is killed before any numerical `1/(4π)` step. -/
theorem scalar_idempotent_forces_one {α : Type*} [Fintype α] [Nonempty α]
    [DecidableEq α] {s : ℝ} (χ : Matrix α α ℝ)
    (hχ : χ * χ = χ) (hχ0 : χ ≠ 0)
    (h : (s • χ) * (s • χ) = s • χ) (hs : s ≠ 0) :
    s = 1 := by
  classical
  have hprod : (s • χ) * (s • χ) = (s ^ 2) • χ := by
    calc
      (s • χ) * (s • χ) = s • (χ * (s • χ)) := by
        rw [Matrix.smul_mul]
      _ = s • (s • (χ * χ)) := by
        rw [Matrix.mul_smul]
      _ = (s * s) • (χ * χ) := by
        rw [smul_smul]
      _ = (s ^ 2) • χ := by
        rw [hχ]
        ext i j
        simp [Matrix.smul_apply, pow_two]
  have hscaled : (s ^ 2) • χ = s • χ := by
    exact hprod.symm.trans h
  have hentry : ∃ i j, χ i j ≠ 0 := by
    by_contra hnone
    apply hχ0
    ext i j
    by_contra hij
    exact hnone ⟨i, j, hij⟩
  rcases hentry with ⟨i, j, hij⟩
  have hcoord := congrArg (fun M : Matrix α α ℝ => M i j) hscaled
  simp only [Matrix.smul_apply, smul_eq_mul] at hcoord
  have hs_factor : s * (s - 1) = 0 := by
    have hmul : (s * (s - 1)) * χ i j = 0 := by
      calc
        (s * (s - 1)) * χ i j = (s ^ 2) * χ i j - s * χ i j := by ring
        _ = 0 := by
          linarith
    exact (mul_eq_zero.mp hmul).resolve_right hij
  exact (mul_eq_zero.mp hs_factor).elim (fun hs0 => (hs hs0).elim) (fun hsm1 => by
    linarith)

/-- The `L1a` partial certificate: multiplicity and trace normalization are
theorem-grade, while the physical admissibility bridge remains open. -/
structure LeptonBoundaryLedgerL1aCert where
  primitive_content :
    ∀ c : PrimitiveQ3BoundaryCycle, primitiveContent c = 1
  multiplicity :
    ∀ n : ℕ, cpmChannelMultiplicity n = n
  additive_content :
    ∀ n : ℕ, additiveBoundaryContent n = n
  trace_unital_unique :
    ∀ {n : ℕ} {lam : ℝ},
      traceUnitalBoundaryDensity n lam →
        lam = (n : ℝ) * leadingBoundaryQuantum
  normalized_value :
    ∀ n : ℕ, normalizedBoundaryDensity n = (n : ℝ) / (4 * Real.pi)
  scalar_killer :
    ∀ {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] {s : ℝ}
      (χ : Matrix α α ℝ),
      χ * χ = χ →
      χ ≠ 0 →
      (s • χ) * (s • χ) = s • χ →
      s ≠ 0 →
      s = 1

theorem leptonBoundaryLedgerL1aCert_holds :
    Nonempty LeptonBoundaryLedgerL1aCert :=
  ⟨{ primitive_content := primitiveContent_eq_one
     multiplicity := cpmChannelMultiplicity_eq
     additive_content := additiveBoundaryContent_eq
     trace_unital_unique := fun h => boundaryDensityTraceUnital_unique h
     normalized_value := normalizedBoundaryDensity_eq
     scalar_killer := fun χ hχ hχ0 h hs =>
       scalar_idempotent_forces_one χ hχ hχ0 h hs }⟩

end

end LeptonBoundaryLedger
end Masses
end IndisputableMonolith
