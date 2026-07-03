import Mathlib
import IndisputableMonolith.Constants

/-!
# φ Non-Degeneracy Certificate

This audit certificate packages two fundamental **non-degeneracy** properties of φ:

> φ ≠ 0 and φ ≠ 1

## Why this matters

1. **Division safety**: φ ≠ 0 ensures we can safely divide by φ in expressions
   like φ⁻¹, the J-cost function, and ratio computations.

2. **Non-trivial optimum**: φ ≠ 1 proves that the golden ratio is NOT at the
   cost minimum (J(1) = 0). This is crucial because φ appears throughout RS
   as a fundamental constant — it's not "accidentally" at the trivial point.

3. **Algebraic consequence**: Both follow from 1 < φ (already certified as
   part of PhiPositivityCert), but it's useful to have explicit ≠ statements.

## Proof approach

Both are direct consequences of `one_lt_phi` (1 < φ), which was previously proven.
-/

namespace IndisputableMonolith
namespace Verification
namespace PhiNonDegenerate

open IndisputableMonolith.Constants

structure PhiNonDegenerateCert where
  deriving Repr

/-- Verification predicate: φ is non-degenerate.

φ ≠ 0 (division safe) and φ ≠ 1 (not at cost minimum). -/
@[simp] def PhiNonDegenerateCert.verified (_c : PhiNonDegenerateCert) : Prop :=
  (phi ≠ 0) ∧ (phi ≠ 1)

@[simp] theorem PhiNonDegenerateCert.verified_any (c : PhiNonDegenerateCert) :
    PhiNonDegenerateCert.verified c := by
  constructor
  · exact phi_ne_zero
  · exact phi_ne_one

end PhiNonDegenerate
end Verification
end IndisputableMonolith
