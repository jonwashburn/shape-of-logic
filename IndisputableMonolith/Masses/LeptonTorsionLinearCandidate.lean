import Mathlib
import IndisputableMonolith.Masses.LeptonDressingFromRecognition
import IndisputableMonolith.Masses.SectorDependentTorsion

/-!
# Linear Lepton Torsion Candidate

U4 has been reduced to a bounded compensating torsion factor:

```
0.889 < τ_torsion < 0.939
```

for the certified positive lepton-running band. This module tests the simplest recognition
shape for that missing term:

```
τ(k) = 1 - k α_RS
```

where `k` is a cube-combinatorial coefficient. This is not claimed as the final dynamics. The
theorem-grade result is a sharp reduction of the search space:

* any linear coefficient `k ∈ [9,15]` lands in the required torsion window;
* `k ≤ 8` is too weak, leaving torsion above the window;
* `k ≥ 16` is too strong, pushing torsion below the window;
* among existing Q₃ counts, `E_pass=11`, `E=12`, `V+F−C=13`, and `V+F=14` survive;
* `F=6` and `W=17` are excluded for this linear ansatz.

So the next U4 target is no longer an arbitrary torsion source. If the source is linear in
`α_RS`, the coefficient must be one of the middle cube counts, not the face count and not the full
wallpaper span.

Lean status: 0 sorry.
-/

namespace IndisputableMonolith
namespace Masses
namespace LeptonTorsionLinearCandidate

open LeptonicVacuumPolarizationRunning
open SectorDependentTorsion

noncomputable section

/-- A simple linear torsion ansatz with cube coefficient `k`. -/
def linearTorsionCoeff (k : ℝ) : ℝ :=
  1 - k * alphaRS

theorem alphaRS_gt_00072 : (0.0072 : ℝ) < alphaRS := by
  unfold alphaRS
  have hpos : (0 : ℝ) < Constants.alphaInv := by
    linarith [IndisputableMonolith.Numerics.alphaInv_gt]
  rw [lt_div_iff₀ hpos]
  nlinarith [IndisputableMonolith.Numerics.alphaInv_lt]

theorem alphaRS_lt_00073 : alphaRS < (0.0073 : ℝ) := by
  unfold alphaRS
  have hpos : (0 : ℝ) < Constants.alphaInv := by
    linarith [IndisputableMonolith.Numerics.alphaInv_gt]
  rw [div_lt_iff₀ hpos]
  nlinarith [IndisputableMonolith.Numerics.alphaInv_gt]

theorem alphaRS_pos : (0 : ℝ) < alphaRS := by
  linarith [alphaRS_gt_00072]

/-- Any linear coefficient in `[9,15]` lands in the U4 torsion window. -/
theorem linearTorsion_window_of_coeff_band {k : ℝ} (hlo : (9 : ℝ) ≤ k) (hhi : k ≤ 15) :
    (0.889 : ℝ) < linearTorsionCoeff k ∧ linearTorsionCoeff k < (0.939 : ℝ) := by
  unfold linearTorsionCoeff
  constructor
  · nlinarith [alphaRS_lt_00073, alphaRS_pos, hlo, hhi]
  · nlinarith [alphaRS_gt_00072, alphaRS_pos, hlo, hhi]

/-- Coefficients at or below `8` are too weak: the torsion remains above the target window. -/
theorem linearTorsion_too_high_of_coeff_le8 {k : ℝ} (hk : k ≤ 8) :
    (0.939 : ℝ) < linearTorsionCoeff k := by
  unfold linearTorsionCoeff
  nlinarith [alphaRS_lt_00073, alphaRS_pos, hk]

/-- Coefficients at or above `16` are too strong: the torsion falls below the target window. -/
theorem linearTorsion_too_low_of_coeff_ge16 {k : ℝ} (hk : (16 : ℝ) ≤ k) :
    linearTorsionCoeff k < (0.889 : ℝ) := by
  unfold linearTorsionCoeff
  nlinarith [alphaRS_gt_00072, alphaRS_pos, hk]

/-! ## Existing cube-count candidates -/

def coeff_Epass : ℝ := (lepton_step_12 : ℝ)
def coeff_E : ℝ := (cube_edges' 3 : ℝ)
def coeff_VFminusC : ℝ := (vertex_face_excess 3 : ℝ)
def coeff_VF : ℝ := (cube_vertices' 3 + cube_faces' 3 : ℝ)
def coeff_F : ℝ := (cube_faces' 3 : ℝ)
def coeff_W : ℝ := (lepton_step_12 + lepton_step_23 : ℝ)

theorem coeff_Epass_eq : coeff_Epass = 11 := by
  unfold coeff_Epass
  exact_mod_cast lepton_step_12_eq

theorem coeff_E_eq : coeff_E = 12 := by
  unfold coeff_E
  exact_mod_cast edges_at_D3

theorem coeff_VFminusC_eq : coeff_VFminusC = 13 := by
  unfold coeff_VFminusC
  exact_mod_cast vertex_face_excess_at_D3

theorem coeff_VF_eq : coeff_VF = 14 := by
  unfold coeff_VF
  rw [vertices_at_D3, faces_at_D3]
  norm_num

theorem coeff_F_eq : coeff_F = 6 := by
  unfold coeff_F
  exact_mod_cast faces_at_D3

theorem coeff_W_eq : coeff_W = 17 := by
  unfold coeff_W
  rw [lepton_step_12_eq, lepton_step_23_eq]
  norm_num

theorem Epass_linear_torsion_in_window :
    (0.889 : ℝ) < linearTorsionCoeff coeff_Epass ∧
    linearTorsionCoeff coeff_Epass < (0.939 : ℝ) := by
  rw [coeff_Epass_eq]
  exact linearTorsion_window_of_coeff_band (by norm_num) (by norm_num)

theorem E_linear_torsion_in_window :
    (0.889 : ℝ) < linearTorsionCoeff coeff_E ∧
    linearTorsionCoeff coeff_E < (0.939 : ℝ) := by
  rw [coeff_E_eq]
  exact linearTorsion_window_of_coeff_band (by norm_num) (by norm_num)

theorem VFminusC_linear_torsion_in_window :
    (0.889 : ℝ) < linearTorsionCoeff coeff_VFminusC ∧
    linearTorsionCoeff coeff_VFminusC < (0.939 : ℝ) := by
  rw [coeff_VFminusC_eq]
  exact linearTorsion_window_of_coeff_band (by norm_num) (by norm_num)

theorem VF_linear_torsion_in_window :
    (0.889 : ℝ) < linearTorsionCoeff coeff_VF ∧
    linearTorsionCoeff coeff_VF < (0.939 : ℝ) := by
  rw [coeff_VF_eq]
  exact linearTorsion_window_of_coeff_band (by norm_num) (by norm_num)

theorem F_linear_torsion_too_high :
    (0.939 : ℝ) < linearTorsionCoeff coeff_F := by
  rw [coeff_F_eq]
  exact linearTorsion_too_high_of_coeff_le8 (by norm_num)

theorem W_linear_torsion_too_low :
    linearTorsionCoeff coeff_W < (0.889 : ℝ) := by
  rw [coeff_W_eq]
  exact linearTorsion_too_low_of_coeff_ge16 (by norm_num)

/-- Certificate: the linear `1-kα` torsion ansatz is not free. The U4 window forces the
middle cube-count band and rejects low/high cube counts. -/
structure LeptonTorsionLinearCandidateCert where
  coeff_band_window :
    ∀ {k : ℝ}, (9 : ℝ) ≤ k → k ≤ 15 →
      (0.889 : ℝ) < linearTorsionCoeff k ∧ linearTorsionCoeff k < 0.939
  low_coeff_excluded :
    ∀ {k : ℝ}, k ≤ 8 → (0.939 : ℝ) < linearTorsionCoeff k
  high_coeff_excluded :
    ∀ {k : ℝ}, (16 : ℝ) ≤ k → linearTorsionCoeff k < 0.889
  Epass_allowed :
    (0.889 : ℝ) < linearTorsionCoeff coeff_Epass ∧
      linearTorsionCoeff coeff_Epass < 0.939
  E_allowed :
    (0.889 : ℝ) < linearTorsionCoeff coeff_E ∧
      linearTorsionCoeff coeff_E < 0.939
  VFminusC_allowed :
    (0.889 : ℝ) < linearTorsionCoeff coeff_VFminusC ∧
      linearTorsionCoeff coeff_VFminusC < 0.939
  VF_allowed :
    (0.889 : ℝ) < linearTorsionCoeff coeff_VF ∧
      linearTorsionCoeff coeff_VF < 0.939
  F_rejected : (0.939 : ℝ) < linearTorsionCoeff coeff_F
  W_rejected : linearTorsionCoeff coeff_W < 0.889

theorem leptonTorsionLinearCandidateCert_holds :
    Nonempty LeptonTorsionLinearCandidateCert :=
  ⟨{ coeff_band_window := fun hlo hhi => linearTorsion_window_of_coeff_band hlo hhi
     low_coeff_excluded := fun hk => linearTorsion_too_high_of_coeff_le8 hk
     high_coeff_excluded := fun hk => linearTorsion_too_low_of_coeff_ge16 hk
     Epass_allowed := Epass_linear_torsion_in_window
     E_allowed := E_linear_torsion_in_window
     VFminusC_allowed := VFminusC_linear_torsion_in_window
     VF_allowed := VF_linear_torsion_in_window
     F_rejected := F_linear_torsion_too_high
     W_rejected := W_linear_torsion_too_low }⟩

end

end LeptonTorsionLinearCandidate
end Masses
end IndisputableMonolith
