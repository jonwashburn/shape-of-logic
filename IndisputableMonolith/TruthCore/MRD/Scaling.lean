import Mathlib

namespace IndisputableMonolith
namespace TruthCore
namespace MRD

structure ScalingModel where
  gamma : ℝ
  f     : ℝ → ℝ → ℝ
  f_hom0 : ∀ {c t1 t2}, 0 < c → f (c * t1) (c * t2) = f t1 t2

noncomputable section

@[simp] noncomputable def predicted_ratio (M : ScalingModel) (tau_m1 tau_m2 tau_f : ℝ) : ℝ :=
  ((tau_m1 / tau_m2) ^ M.gamma) * M.f (tau_m1 / tau_f) (tau_m2 / tau_f)

lemma predicted_ratio_rescale (M : ScalingModel)
  (c tau_m1 tau_m2 tau_f : ℝ) (hc : 0 < c) :
  predicted_ratio M (c * tau_m1) (c * tau_m2) (c * tau_f)
    = predicted_ratio M tau_m1 tau_m2 tau_f := by
  dsimp [predicted_ratio]
  have h12 : (c * tau_m1) / (c * tau_m2) = tau_m1 / tau_m2 := by
    have hc0 : (c:ℝ) ≠ 0 := ne_of_gt hc
    field_simp [hc0]
  have h1f : (c * tau_m1) / (c * tau_f) = tau_m1 / tau_f := by
    have hc0 : (c:ℝ) ≠ 0 := ne_of_gt hc
    field_simp [hc0]
  have h2f : (c * tau_m2) / (c * tau_f) = tau_m2 / tau_f := by
    have hc0 : (c:ℝ) ≠ 0 := ne_of_gt hc
    field_simp [hc0]
  have hf : M.f ((c * tau_m1) / (c * tau_f)) ((c * tau_m2) / (c * tau_f))
            = M.f (tau_m1 / tau_f) (tau_m2 / tau_f) := by
    simpa [h1f, h2f, one_mul] using
      (M.f_hom0 (c:=1) (t1:=tau_m1 / tau_f) (t2:=tau_m2 / tau_f) (by norm_num))
  simp [h12, hf]

end

end MRD
end TruthCore
end IndisputableMonolith
