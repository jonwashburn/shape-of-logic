import Mathlib

/-!
# CPT Epsilon Certification Layer

Claim-honest Lean formalization of the epsilon/noise ranking layer used in the paper:

- perturbation bound `|ĉ - c| ≤ ε`,
- minimizer/argmin transfer from `ĉ` to `c`,
- explicit `2ε`-suboptimality guarantee.
-/

namespace IndisputableMonolith
namespace Verification
namespace CPT
namespace EpsilonCertification

open scoped Classical

variable {O : Type}

/-- `ε`-meaning set for a scalar objective on candidates. -/
def MeanEps (c : O → ℝ) (ε : ℝ) : Set O :=
  {o | ∀ o', c o ≤ c o' + ε}

/-- If `oHat` minimizes perturbed costs `cHat` and `|cHat-c| ≤ ε`, then `oHat`
is `2ε`-optimal for the true cost `c`. -/
theorem approx_argmin_stability
    (c cHat : O → ℝ) (ε : ℝ)
    (hErr : ∀ o, |cHat o - c o| ≤ ε)
    (oHat : O)
    (hMin : ∀ o, cHat oHat ≤ cHat o) :
    ∀ o, c oHat ≤ c o + 2 * ε := by
  intro o
  have hHat_ge_true : c oHat ≤ cHat oHat + ε := by
    have h := (abs_le.mp (hErr oHat)).1
    linarith
  have hMin' : cHat oHat ≤ cHat o := hMin o
  have hHat_le_true : cHat o ≤ c o + ε := by
    have h := (abs_le.mp (hErr o)).2
    linarith
  linarith

/-- Set-level form: the perturbed minimizer belongs to the `2ε`-meaning set of `c`. -/
theorem approx_argmin_mem_meanEps
    (c cHat : O → ℝ) (ε : ℝ)
    (hErr : ∀ o, |cHat o - c o| ≤ ε)
    (oHat : O)
    (hMin : ∀ o, cHat oHat ≤ cHat o) :
    oHat ∈ MeanEps c (2 * ε) := by
  intro o
  exact approx_argmin_stability c cHat ε hErr oHat hMin o

end EpsilonCertification
end CPT
end Verification
end IndisputableMonolith
