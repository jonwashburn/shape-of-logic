import IndisputableMonolith.Foundation.PhiForcingDerived
import IndisputableMonolith.Foundation.UniversalForcing.ReciprocalGenerator
import IndisputableMonolith.Foundation.HierarchyRealizationObstruction
import IndisputableMonolith.Constants

/-!
# SelectedScaleClosure — Part I φ residual binder

Named residual for the selected short closure that forces φ:

* under `GeometricScaleSequence.isClosed` (`S0 + S1 = S2`), the ratio is φ
  (`closed_ratio_is_phi` / `phi_forcing_complete`);
* equivalently, the reciprocal-shift fixed point `1 + 1/x = x` on `(1,∞)`
  forces φ (`recipShift_fixed_iff`);
* independence: `ClosedObservableFramework` alone does **not** force
  `additive_posting` (`closedFramework_does_not_force_additive_posting`);
* alternate short closures do not force φ: the plastic / Tribonacci root of
  `r³ = r + 1` exists, is positive, and is not φ.

Do not claim `ClosedObservableFramework` alone forces additive posting or φ.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine

open PhiForcingDerived
open UniversalForcing.ReciprocalGenerator
open HierarchyRealizationObstruction
open Constants
open ClosedFramework

/-- Plastic-style independence witness: some positive `r ≠ φ` satisfies the
alternate cubic short closure `r³ = r + 1`. -/
theorem exists_plastic_root_ne_phi :
    ∃ r : ℝ, 0 < r ∧ r ≠ phi ∧ r ^ 3 = r + 1 := by
  let f : ℝ → ℝ := fun x => x ^ 3 - x - 1
  have hf : Continuous f := by fun_prop
  have hroot : ∃ c ∈ Set.Icc (1 : ℝ) 2, f c = 0 := by
    refine intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hf.continuousOn ?_
    -- 0 ∈ Icc (f 1) (f 2) = Icc (-1) 5
    change (0 : ℝ) ∈ Set.Icc (f 1) (f 2)
    simp only [f]
    constructor <;> norm_num
  obtain ⟨r, hrI, hr0⟩ := hroot
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hrI.1
  have hreq : r ^ 3 = r + 1 := by
    have : r ^ 3 - r - 1 = 0 := hr0
    linarith
  refine ⟨r, hrpos, ?_, hreq⟩
  intro hφ
  have hcubed : phi ^ 3 = 2 * phi + 1 := phi_cubed_eq
  have hcontra : phi ^ 3 = phi + 1 := by
    simpa [hφ] using hreq
  have : (2 : ℝ) * phi + 1 = phi + 1 := by
    rw [← hcubed, hcontra]
  have : phi = 0 := by linarith
  exact (ne_of_gt phi_pos) this

/-- **Selected scale-closure binder.** φ uniqueness under the selected short
closure, plus independence of that closure from weaker frameworks / alternate
index closures. -/
structure SelectedScaleClosure : Prop where
  /-- Geometric `isClosed` (S0+S1=S2) forces the ratio to be φ. -/
  closed_forces_phi :
    ∀ S : GeometricScaleSequence, S.isClosed → S.ratio = phi
  /-- Equivalent fixed-point form: `recipShift x = x` on `(1,∞)` iff `x = φ`. -/
  recipShift_forces_phi :
    ∀ x : ℝ, 1 < x → (recipShift x = x ↔ x = phi)
  /-- Pointwise closure condition `1 + r = r²` with `r > 0`, `r ≠ 1` forces `r = φ`. -/
  phi_forcing :
    ∀ r : ℝ, r > 0 → r ≠ 1 → (1 + r = r ^ 2) → r = phi
  /-- `ClosedObservableFramework` alone does not force additive posting. -/
  framework_does_not_force_additive_posting :
    ∃ (F : ClosedObservableFramework) (base : F.S),
      ¬ (F.r (F.T^[2] base) = F.r (F.T^[1] base) + F.r base)
  /-- Alternate cubic short closure admits a positive root distinct from φ. -/
  plastic_independence :
    ∃ r : ℝ, 0 < r ∧ r ≠ phi ∧ r ^ 3 = r + 1

/-- The selected-scale-closure binder holds. -/
theorem selectedScaleClosure_holds : SelectedScaleClosure where
  closed_forces_phi := fun S h => closed_ratio_is_phi S h
  recipShift_forces_phi := fun _ hx => recipShift_fixed_iff hx
  phi_forcing := phi_forcing_complete
  framework_does_not_force_additive_posting :=
    closedFramework_does_not_force_additive_posting
  plastic_independence := exists_plastic_root_ne_phi

end PublicSpine
end Foundation
end IndisputableMonolith
