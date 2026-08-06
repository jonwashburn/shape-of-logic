import Mathlib
import IndisputableMonolith.Thermodynamics.ForcedResponseOddness

/-!
# The drive-free response law is the large-deviation dissipation potential

`ForcedResponseLaw` showed that a free mobility absorbs any Butler-Volmer symmetry factor, and
`ForcedResponseOddness` recovered `alpha = 1/2` by refusing the absorbing witness on the grounds
that a mobility depending exponentially on its own drive is not a mobility. That module had to
argue the point in prose, and prose is where a referee pushes back.

It need not be argued. The premise has a name and a derivation outside this program.

For a chemical reaction network satisfying detailed balance, the dual dissipation potential is
*derived* from the large deviation principle of the underlying Markov jump process, and the
derived function is

    C*(z) = 4 * cosh (z / 2) - 4,      normalized so that C*(z) = z^2 / 2 + O(z^4),

with an affinity-independent prefactor depending only on the state through a geometric mean of
concentrations. The affinity-independence is called **tilt invariance**, and it is exactly what
selects this structure from the infinitely many other gradient structures generating the same
evolution equation. See Mielke, Peletier and Renger, Potential Analysis 41 (2014) 1293
(doi:10.1007/s11118-014-9418-5), Maas and Mielke, J. Stat. Phys. (2020)
(doi:10.1007/s10955-020-02663-4), and Mielke, Patterson, Peletier and Renger
(doi:10.1137/16M1102240).

This module records that `C*` is the recognition cost, and that the two constants agree.

`ldpPotential_eq_four_bridgedCost` is the identification of the potential.
`ldpFlux_eq_constantMobilityFlux` is the identification of the flux, at exactly the mobility
`M = 4` and bridge scale `k = 1/2` that `half_is_realized_drive_free` pinned from the unrelated
requirement of matching Butler-Volmer.

`drive_free_match_forces_constants` is the content worth having. It shows those constants are
not fitted: matching the symmetric Butler-Volmer response at two drives forces `k = 1/2` and
`M = 4` outright. And `butlerVolmer_match_implies_ldp_normalization` then shows the external
normalization condition `M * k^2 = 1`, which was fixed by matching the quadratic fluctuation
regime and had no reason to know about electrochemistry, comes out satisfied rather than
imposed. Two derivations from disjoint premises, one function, one normalization.

Honest tier. Everything here is THEOREM: pure real analysis. What is *not* claimed is that the
recognition derivation of `J` and the large-deviation derivation of `C*` are the same argument.
They are two arguments reaching the same function, which is evidence and not proof. The
empirical domain of validity is a separate matter recorded in the campaign audit: published
outer-sphere kinetics exclude a drive-free mobility above roughly `0.3` of the reorganization
energy, consistent with `C*` being a small-fluctuation normalization to begin with.
-/

namespace IndisputableMonolith
namespace Thermodynamics
namespace ForcedResponseLargeDeviationBridge

open Real
open ForcedResponseLaw
open ForcedResponseOddness

noncomputable section

/-! ## The externally derived potential -/

/-- The dual dissipation potential that the large deviation principle of a detailed-balance
Markov jump process yields, per reaction and stripped of its state-dependent prefactor. -/
def ldpPotential (z : ℝ) : ℝ :=
  4 * cosh (z / 2) - 4

/-- **The large-deviation potential is the recognition cost.** `C*` is four times the canonical
J-cost read through the half-affinity bridge. The factor four is the external normalization and
the half is the bridge scale; neither is adjusted here. -/
theorem ldpPotential_eq_four_bridgedCost (z : ℝ) :
    ldpPotential z = 4 * bridgedCost (linearBridge (1 / 2)) z := by
  rw [ldpPotential, bridgedCost, canonicalLogCost_eq_cosh_sub_one, linearBridge]
  ring_nf

/-! ## The flux, and the two constants -/

/-- The potential is differentiable with the displayed derivative. -/
theorem hasDerivAt_ldpPotential (z : ℝ) :
    HasDerivAt ldpPotential (2 * sinh (z / 2)) z := by
  have hinner : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) z := by
    simpa using (hasDerivAt_id z).div_const 2
  have hcosh : HasDerivAt (fun t : ℝ => cosh (t / 2)) (sinh (z / 2) * (1 / 2)) z :=
    hinner.cosh
  have hsub := (hcosh.const_mul (4 : ℝ)).sub_const (4 : ℝ)
  have hfun : ldpPotential = fun t : ℝ => 4 * cosh (t / 2) - 4 := rfl
  rw [hfun]
  convert hsub using 1
  ring

/-- The flux conjugate to the drive is the symmetric `sinh` law. -/
theorem ldpFlux (z : ℝ) : deriv ldpPotential z = 2 * sinh (z / 2) :=
  (hasDerivAt_ldpPotential z).deriv

/-- **The large-deviation flux is the drive-free recognition flux**, at mobility four and bridge
scale one half. Those are the constants `half_is_realized_drive_free` pinned from Butler-Volmer,
arrived at here from a large deviation principle instead. -/
theorem ldpFlux_eq_constantMobilityFlux (z : ℝ) :
    deriv ldpPotential z = constantMobilityFlux 4 (1 / 2) z := by
  rw [ldpFlux, constantMobilityFlux]
  ring_nf

/-- And therefore the large-deviation flux is symmetric Butler-Volmer exactly. -/
theorem ldpFlux_eq_butlerVolmer_half (z : ℝ) :
    deriv ldpPotential z = butlerVolmerShape (1 / 2) z := by
  rw [ldpFlux, butlerVolmer_half_eq_two_sinh]

/-! ## The external normalization -/

/-- `deriv ldpPotential` as a function, needed to differentiate a second time. -/
theorem deriv_ldpPotential_eq : deriv ldpPotential = fun z : ℝ => 2 * sinh (z / 2) := by
  funext z
  exact ldpFlux z

/-- **The external normalization `C*''(0) = 1`.** This is the condition fixing the prefactor
four in the large deviation literature, where it comes from matching the quadratic fluctuation
regime `C*(z) = z^2/2 + O(z^4)`. -/
theorem ldp_normalization : deriv (deriv ldpPotential) 0 = 1 := by
  rw [deriv_ldpPotential_eq]
  have hinner : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const 2
  have hsinh : HasDerivAt (fun t : ℝ => sinh (t / 2)) (1 / 2) (0 : ℝ) := by
    have h0 : HasDerivAt (fun t : ℝ => sinh (t / 2)) (cosh ((0 : ℝ) / 2) * (1 / 2)) (0 : ℝ) :=
      hinner.sinh
    convert h0 using 1
    norm_num
  have h := (hsinh.const_mul (2 : ℝ)).deriv
  rw [h]
  norm_num

/-! ## The constants are forced, not fitted -/

/-- `cosh` agreeing at a point forces the arguments to agree in absolute value. -/
private theorem abs_eq_of_cosh_eq {x y : ℝ} (h : cosh x = cosh y) : |x| = |y| := by
  rcases lt_trichotomy |x| |y| with hlt | heq | hgt
  · exact absurd h (by have := Real.cosh_lt_cosh.mpr hlt; linarith)
  · exact heq
  · exact absurd h (by have := Real.cosh_lt_cosh.mpr hgt; linarith)

/-- **The mobility and the bridge scale are forced.**

If a drive-free flux with positive mobility and positive bridge scale reproduces the symmetric
Butler-Volmer response, then the mobility is four and the bridge scale is one half. Nothing is
fitted: two drives suffice, and the hyperbolic double-angle identity does the rest.

This is why the agreement with the large-deviation normalization in
`pinned_constants_satisfy_ldp_normalization` is a real coincidence of two derivations rather
than a choice of units. -/
theorem drive_free_match_forces_constants
    {M k : ℝ} (hk : 0 < k)
    (h : ∀ A : ℝ, constantMobilityFlux M k A = butlerVolmerShape (1 / 2) A) :
    k = 1 / 2 ∧ M = 4 := by
  have hsinh1 : 0 < sinh (1 : ℝ) := by
    have hzero : sinh (0 : ℝ) = 0 := Real.sinh_zero
    have hmono : sinh (0 : ℝ) < sinh 1 := Real.sinh_lt_sinh.mpr (by norm_num)
    linarith [hzero, hmono]
  -- Rewrite the hypothesis at the two drives we need.
  have h2 : M * (k * sinh (k * 2)) = 2 * sinh (2 / 2 : ℝ) := by
    have := h 2
    rwa [constantMobilityFlux, butlerVolmer_half_eq_two_sinh] at this
  have h4 : M * (k * sinh (k * 4)) = 2 * sinh (4 / 2 : ℝ) := by
    have := h 4
    rwa [constantMobilityFlux, butlerVolmer_half_eq_two_sinh] at this
  norm_num at h2 h4
  -- Double-angle on both sides: sinh (4k) = 2 sinh (2k) cosh (2k) and sinh 2 = 2 sinh 1 cosh 1.
  have hk4 : sinh (k * 4) = 2 * sinh (k * 2) * cosh (k * 2) := by
    have : k * 4 = 2 * (k * 2) := by ring
    rw [this, Real.sinh_two_mul]
  have hs2 : sinh (2 : ℝ) = 2 * sinh 1 * cosh 1 := by
    have hd := Real.sinh_two_mul (1 : ℝ)
    norm_num at hd
    exact hd
  rw [hk4] at h4
  rw [hs2] at h4
  -- Substituting the first equation collapses h4 to a statement about cosh alone.
  have hcosh : cosh (k * 2) = cosh 1 := by
    have hexpand : (M * (k * sinh (k * 2))) * (2 * cosh (k * 2))
        = 2 * (2 * sinh 1 * cosh 1) := by
      calc (M * (k * sinh (k * 2))) * (2 * cosh (k * 2))
          = M * (k * (2 * sinh (k * 2) * cosh (k * 2))) := by ring
        _ = 2 * (2 * sinh 1 * cosh 1) := h4
    rw [h2] at hexpand
    have hz : sinh 1 * (cosh (k * 2) - cosh 1) = 0 := by linear_combination hexpand / 4
    rcases mul_eq_zero.mp hz with h | h
    · linarith
    · linarith
  -- Positivity turns |2k| = 1 into k = 1/2, and the first equation then gives M.
  have habs : |k * 2| = |(1 : ℝ)| := abs_eq_of_cosh_eq hcosh
  have hkval : k = 1 / 2 := by
    rw [abs_of_pos (by linarith : (0:ℝ) < k * 2), abs_one] at habs
    linarith
  refine ⟨hkval, ?_⟩
  rw [hkval] at h2
  norm_num at h2
  have hkey : (M - 4) * sinh 1 = 0 := by linear_combination 2 * h2
  rcases mul_eq_zero.mp hkey with h | h
  · linarith
  · linarith

/-- **The two normalizations agree.** Matching symmetric Butler-Volmer with a drive-free
mobility implies the large deviation normalization condition `M * k^2 = 1`, which is what fixes
the prefactor externally from the quadratic fluctuation regime `C*(z) = z^2/2 + O(z^4)`. The
electrochemical premise had no access to the fluctuation requirement, and satisfies it. -/
theorem butlerVolmer_match_implies_ldp_normalization
    {M k : ℝ} (hk : 0 < k)
    (h : ∀ A : ℝ, constantMobilityFlux M k A = butlerVolmerShape (1 / 2) A) :
    M * k ^ 2 = 1 := by
  obtain ⟨hkval, hMval⟩ := drive_free_match_forces_constants hk h
  rw [hkval, hMval]
  norm_num

end

end ForcedResponseLargeDeviationBridge
end Thermodynamics
end IndisputableMonolith
