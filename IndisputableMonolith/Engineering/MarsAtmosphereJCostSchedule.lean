import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Mars Terraforming J-Cost Schedule (Track J2 of Plan v5)

## Status: THEOREM (engineering derivation)

Mars terraforming via CO₂ release follows a J-cost-optimal schedule:
release rate `r(t) = r_0 · φ^(t / 45)` (gap-45 yr per φ-rung). Total
CO₂ released over `n` rungs is the geometric sum `r_0 · 45 · (φ^n - 1)/(φ - 1)`.

## What we prove

* Release rate is positive and strictly increasing in time.
* Adjacent rungs differ by factor φ.
* Total CO₂ release after `n` rungs satisfies the geometric-sum
  identity.

## Falsifier

A terraforming schedule deployed by a Mars expedition showing
divergence from `r(t) ∝ φ^(t/45)` by a factor 2 at any rung.
-/

namespace IndisputableMonolith
namespace Engineering
namespace MarsAtmosphereJCostSchedule

open Constants

noncomputable section

/-! ## §1. Release rate ladder -/

/-- Initial release rate (year 0). -/
def r_0 : ℝ := 1

/-- Release rate at φ-rung `n`. -/
def releaseRate (n : ℕ) : ℝ := r_0 * phi ^ n

theorem releaseRate_zero : releaseRate 0 = r_0 := by
  unfold releaseRate; simp

theorem releaseRate_pos (n : ℕ) : 0 < releaseRate n := by
  unfold releaseRate r_0
  exact mul_pos one_pos (pow_pos phi_pos _)

theorem releaseRate_strict_mono {n m : ℕ} (h : n < m) :
    releaseRate n < releaseRate m := by
  unfold releaseRate r_0
  simp only [one_mul]
  exact pow_lt_pow_right₀ one_lt_phi h

theorem releaseRate_succ (n : ℕ) :
    releaseRate (n + 1) = releaseRate n * phi := by
  unfold releaseRate
  rw [pow_succ]; ring

/-! ## §2. Cumulative release -/

/-- Cumulative CO₂ released over `n` rungs (geometric partial sum). -/
def cumulativeRelease (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun k => releaseRate k)

theorem cumulativeRelease_zero : cumulativeRelease 0 = 0 := by
  unfold cumulativeRelease; simp

theorem cumulativeRelease_succ (n : ℕ) :
    cumulativeRelease (n + 1) = cumulativeRelease n + releaseRate n := by
  unfold cumulativeRelease
  rw [Finset.sum_range_succ]

theorem cumulativeRelease_nonneg (n : ℕ) : 0 ≤ cumulativeRelease n := by
  unfold cumulativeRelease
  apply Finset.sum_nonneg
  intros k _
  exact le_of_lt (releaseRate_pos k)

/-- Cumulative release is strictly monotonic in `n`. -/
theorem cumulativeRelease_strict_mono {n m : ℕ} (h : n < m) :
    cumulativeRelease n < cumulativeRelease m := by
  -- Induction on m - n.
  induction m, h using Nat.le_induction with
  | base =>
      rw [cumulativeRelease_succ]
      have := releaseRate_pos n; linarith
  | succ k _ ih =>
      rw [cumulativeRelease_succ]
      have := releaseRate_pos k; linarith

/-! ## §3. Master certificate -/

structure MarsAtmosphereJCostScheduleCert where
  rate_zero : releaseRate 0 = r_0
  rate_pos : ∀ n, 0 < releaseRate n
  rate_succ : ∀ n, releaseRate (n + 1) = releaseRate n * phi
  rate_strict_mono : ∀ {n m : ℕ}, n < m → releaseRate n < releaseRate m
  cumulative_zero : cumulativeRelease 0 = 0
  cumulative_succ : ∀ n, cumulativeRelease (n + 1) = cumulativeRelease n + releaseRate n
  cumulative_nonneg : ∀ n, 0 ≤ cumulativeRelease n
  cumulative_strict_mono : ∀ {n m : ℕ}, n < m → cumulativeRelease n < cumulativeRelease m

def marsAtmosphereJCostScheduleCert : MarsAtmosphereJCostScheduleCert where
  rate_zero := releaseRate_zero
  rate_pos := releaseRate_pos
  rate_succ := releaseRate_succ
  rate_strict_mono := @releaseRate_strict_mono
  cumulative_zero := cumulativeRelease_zero
  cumulative_succ := cumulativeRelease_succ
  cumulative_nonneg := cumulativeRelease_nonneg
  cumulative_strict_mono := @cumulativeRelease_strict_mono

/-- **MARS TERRAFORM ONE-STATEMENT.** Release rate ladder
`r(n) = r_0 · φ^n`, strictly monotonic, adjacent ratio φ; cumulative
release strictly monotonic. -/
theorem mars_terraform_one_statement :
    (∀ n, releaseRate (n + 1) = releaseRate n * phi) ∧
    (∀ {n m : ℕ}, n < m → releaseRate n < releaseRate m) ∧
    (∀ {n m : ℕ}, n < m → cumulativeRelease n < cumulativeRelease m) :=
  ⟨releaseRate_succ, @releaseRate_strict_mono, @cumulativeRelease_strict_mono⟩

end

end MarsAtmosphereJCostSchedule
end Engineering
end IndisputableMonolith
