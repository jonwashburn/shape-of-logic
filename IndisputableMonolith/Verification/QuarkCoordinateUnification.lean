import Mathlib
import IndisputableMonolith.Constants

/-!
# Quark Coordinate Unification (Pass 2)

This module proves a key structural fact:

The two quark mass coordinate conventions are mathematically equivalent
representations of the same positive mass law once a reference mass is fixed.

## Conventions

1. **Core form** (integer-rung architecture):
   `m = A_sector * φ^(r - 8 + gap)`

2. **Quarter/Residue form** (reference-mass coordinates):
   `m = m_ref * φ^R`

The map between them is explicit:
`R = log_φ(A_sector / m_ref) + (r - 8 + gap)`.

So the quarter coordinate is not a second physical law; it is a reparameterization
of the same multiplicative φ-ladder once a reference mass is chosen.
-/

namespace IndisputableMonolith
namespace Verification
namespace QuarkCoordinateUnification

open Constants

noncomputable section

/-- The core exponent in the integer-rung architecture. -/
def coreExponent (r : ℤ) (gap : ℝ) : ℝ :=
  (r : ℝ) - 8 + gap

/-- Core mass law shape (sector yardstick form). -/
def coreMass (A_sector : ℝ) (r : ℤ) (gap : ℝ) : ℝ :=
  A_sector * phi ^ (coreExponent r gap)

/-- Residue/quarter coordinate mass law shape (reference mass form). -/
def residueMass (m_ref : ℝ) (R : ℝ) : ℝ :=
  m_ref * phi ^ R

/-- Coordinate transform from core parameters to residue coordinate. -/
def residueFromCore (A_sector m_ref : ℝ) (r : ℤ) (gap : ℝ) : ℝ :=
  Real.logb phi (A_sector / m_ref) + coreExponent r gap

/-- Coordinate transform from residue coordinate to a core yardstick at fixed `(r,gap)`. -/
def yardstickFromResidue (m_ref : ℝ) (R : ℝ) (r : ℤ) (gap : ℝ) : ℝ :=
  m_ref * phi ^ (R - coreExponent r gap)

/-- Core form equals residue form under the explicit coordinate transform. -/
theorem core_eq_residue_of_positive
    {A_sector m_ref : ℝ} {r : ℤ} {gap : ℝ}
    (hA : 0 < A_sector) (hm : 0 < m_ref) :
    coreMass A_sector r gap = residueMass m_ref (residueFromCore A_sector m_ref r gap) := by
  unfold coreMass residueMass residueFromCore coreExponent
  have hratio : 0 < A_sector / m_ref := div_pos hA hm
  have hpow : A_sector / m_ref = phi ^ (Real.logb phi (A_sector / m_ref)) :=
    (Real.rpow_logb phi_pos phi_ne_one hratio).symm
  calc
    A_sector * phi ^ ((r : ℝ) - 8 + gap)
        = (m_ref * (A_sector / m_ref)) * phi ^ ((r : ℝ) - 8 + gap) := by
            field_simp [hm.ne']
    _ = m_ref * ((A_sector / m_ref) * phi ^ ((r : ℝ) - 8 + gap)) := by ring
    _ = m_ref * (phi ^ (Real.logb phi (A_sector / m_ref)) * phi ^ ((r : ℝ) - 8 + gap)) := by
          congr 1
          exact congrArg (fun t => t * phi ^ ((r : ℝ) - 8 + gap)) hpow
    _ = m_ref * phi ^ (Real.logb phi (A_sector / m_ref) + ((r : ℝ) - 8 + gap)) := by
          rw [← Real.rpow_add phi_pos]

/-- Residue form equals core form under the explicit inverse transform. -/
theorem residue_eq_core
    {m_ref : ℝ} {R : ℝ} {r : ℤ} {gap : ℝ} :
    residueMass m_ref R = coreMass (yardstickFromResidue m_ref R r gap) r gap := by
  unfold residueMass coreMass yardstickFromResidue coreExponent
  let E : ℝ := (r : ℝ) - 8 + gap
  have hpow : phi ^ R = phi ^ (R - E) * phi ^ E := by
    have h := (Real.rpow_add phi_pos (R - E) E)
    have hsum : (R - E) + E = R := by ring
    simpa [hsum] using h
  calc
    m_ref * phi ^ R
        = m_ref * (phi ^ (R - E) * phi ^ E) := by rw [hpow]
    _ = (m_ref * phi ^ (R - E)) * phi ^ E := by ring
    _ = (m_ref * phi ^ (R - ((r : ℝ) - 8 + gap))) * phi ^ ((r : ℝ) - 8 + gap) := by
          simp [E]

/-- Recover residue coordinate from a residue-form mass exactly. -/
theorem recover_residue_coordinate
    {m_ref : ℝ} {R : ℝ}
    (hm : 0 < m_ref) :
    Real.logb phi (residueMass m_ref R / m_ref) = R := by
  unfold residueMass
  have hdiv : (m_ref * phi ^ R) / m_ref = phi ^ R := by
    field_simp [hm.ne']
  rw [hdiv]
  exact Real.logb_rpow phi_pos phi_ne_one

/-- Structural interpretation: once a positive reference mass is fixed,
the two coordinate systems are equivalent (up to explicit transforms). -/
theorem coordinate_systems_equivalent :
    ∀ {A_sector m_ref : ℝ} {r : ℤ} {gap : ℝ},
      0 < A_sector → 0 < m_ref →
      ∃ R : ℝ,
        coreMass A_sector r gap = residueMass m_ref R := by
  intro A_sector m_ref r gap hA hm
  refine ⟨residueFromCore A_sector m_ref r gap, ?_⟩
  exact core_eq_residue_of_positive hA hm

end

end QuarkCoordinateUnification
end Verification
end IndisputableMonolith
