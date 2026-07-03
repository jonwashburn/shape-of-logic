import Mathlib
import IndisputableMonolith.QFT.CasimirPlateModes

/-!
# Casimir-Polder Atom-Surface Force

This module records the atom-surface member of the Casimir family.  The
retarded law scales as `a^{-4}`; the nonretarded law scales as `a^{-3}` and is
normalized to agree with the retarded law at `a = c / ω`.
-/

namespace IndisputableMonolith
namespace QFT
namespace CasimirPolderAtomSurface

open CasimirPlateModes
open Constants

noncomputable section

/-- Retarded Casimir-Polder potential for positive polarizability. -/
noncomputable def casimirPolderRetarded (alpha : ℝ) (a : PlateSeparation) : ℝ :=
  -3 * hbar * c * alpha / (8 * Real.pi * a.value ^ 4)

/-- Nonretarded van der Waals form normalized by an atomic frequency `omega`.
The crossover length is `c / omega`. -/
noncomputable def vanDerWaalsNonretarded
    (alpha omega : ℝ) (a : PlateSeparation) : ℝ :=
  -3 * hbar * c * alpha / (8 * Real.pi * (c / omega) * a.value ^ 3)

/-- Crossover length between nonretarded and retarded atom-surface regimes. -/
noncomputable def crossoverLength (omega : ℝ) : ℝ :=
  c / omega

/-- The retarded potential is attractive for positive polarizability. -/
theorem casimirPolderRetarded_negative
    (alpha : ℝ) (a : PlateSeparation) (halpha : 0 < alpha) :
    casimirPolderRetarded alpha a < 0 := by
  unfold casimirPolderRetarded
  have hnum : 0 < 3 * hbar * c * alpha := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hbar_pos) c_pos) halpha
  have hnum_neg : -3 * hbar * c * alpha < 0 := by
    nlinarith
  have hden : 0 < 8 * Real.pi * a.value ^ 4 := by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos a.pos 4)
  exact div_neg_of_neg_of_pos hnum_neg hden

/-- The nonretarded potential is attractive for positive polarizability and
positive atomic frequency. -/
theorem vanDerWaalsNonretarded_negative
    (alpha omega : ℝ) (a : PlateSeparation)
    (halpha : 0 < alpha) (homega : 0 < omega) :
    vanDerWaalsNonretarded alpha omega a < 0 := by
  unfold vanDerWaalsNonretarded
  have hcrossover : 0 < c / omega := div_pos c_pos homega
  have hnum : 0 < 3 * hbar * c * alpha := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hbar_pos) c_pos) halpha
  have hnum_neg : -3 * hbar * c * alpha < 0 := by
    nlinarith
  have hden : 0 < 8 * Real.pi * (c / omega) * a.value ^ 3 := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hcrossover) (pow_pos a.pos 3)
  exact div_neg_of_neg_of_pos hnum_neg hden

/-- At the crossover length `a = c / omega`, the normalized nonretarded law
matches the retarded law. -/
theorem crossover_retarded_eq_nonretarded
    (alpha omega : ℝ) (homega : 0 < omega) :
    casimirPolderRetarded alpha ⟨c / omega, div_pos c_pos homega⟩ =
      vanDerWaalsNonretarded alpha omega ⟨c / omega, div_pos c_pos homega⟩ := by
  unfold casimirPolderRetarded vanDerWaalsNonretarded
  have hω : omega ≠ 0 := ne_of_gt homega
  have hcω : c / omega ≠ 0 := ne_of_gt (div_pos c_pos homega)
  field_simp [hω, hcω]

/-- Casimir-Polder certificate. -/
structure CasimirPolderCert where
  retarded_attractive :
    ∀ (alpha : ℝ) (a : PlateSeparation), 0 < alpha →
      casimirPolderRetarded alpha a < 0
  nonretarded_attractive :
    ∀ (alpha omega : ℝ) (a : PlateSeparation), 0 < alpha → 0 < omega →
      vanDerWaalsNonretarded alpha omega a < 0
  crossover :
    ∀ (alpha omega : ℝ) (homega : 0 < omega),
      casimirPolderRetarded alpha ⟨c / omega, div_pos c_pos homega⟩ =
        vanDerWaalsNonretarded alpha omega ⟨c / omega, div_pos c_pos homega⟩

/-- Certificate instance. -/
def casimirPolderCert : CasimirPolderCert where
  retarded_attractive := casimirPolderRetarded_negative
  nonretarded_attractive := vanDerWaalsNonretarded_negative
  crossover := crossover_retarded_eq_nonretarded

end

end CasimirPolderAtomSurface
end QFT
end IndisputableMonolith
