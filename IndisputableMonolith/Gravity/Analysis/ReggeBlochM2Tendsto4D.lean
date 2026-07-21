import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeBlochM2Symbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeTTContinuumLimit

/-!
# Close `FoldAlongM2Tendsto` for axis TT and pure gauge

Uses the proved cosine two-jet
`ReggeTTContinuumLimit.cos_sub_one_div_sq_tendsto` and the already-proved
zero-momentum vanishing of the deficit kernel on `axisTTPlus` /
`decoyGauge`.

Honest scope: closes the punctured Tendsto along `symbolDir` for those
two polarizations.  General `H` remains the named Prop from the symbol
module.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeBlochM2Tendsto4D

open BigOperators Filter Topology
open ReggeEdgeStencil4D
open ReggeBlochFold4D
open ReggeBlochM2Symbol4D
open ReggeFlat4DHessianAssembly
open ReggeTTContinuumLimit
open EdgeTTDecomposition4D

noncomputable section

def areaAlong (H : Mat4) (s : Fin 24) (t : Fin 10) (μ : ℝ) : ℝ :=
  phasedClassDot (slotAreaCov s t) H (fun i => μ * symbolDir i) (hingeBase s t)

def kerAlong (H : Mat4) (s : Fin 24) (t : Fin 10) (μ : ℝ) : ℝ :=
  phasedClassDot (slotDeficitKer s t) H (fun i => μ * symbolDir i) (hingeBase s t)

theorem areaAlong_eq (H : Mat4) (s : Fin 24) (t : Fin 10) (μ : ℝ) :
    areaAlong H s t μ =
      ∑ d : Fin 15,
        slotAreaCov s t d * classCoeff H d *
          Real.cos (μ * phaseScale (hingeBase s t) d) := by
  simpa [areaAlong] using phasedClassDot_symbolDir (slotAreaCov s t) H μ (hingeBase s t)

theorem kerAlong_eq (H : Mat4) (s : Fin 24) (t : Fin 10) (μ : ℝ) :
    kerAlong H s t μ =
      ∑ d : Fin 15,
        slotDeficitKer s t d * classCoeff H d *
          Real.cos (μ * phaseScale (hingeBase s t) d) := by
  simpa [kerAlong] using
    phasedClassDot_symbolDir (slotDeficitKer s t) H μ (hingeBase s t)

theorem areaAlong_zero (H : Mat4) (s : Fin 24) (t : Fin 10) :
    areaAlong H s t 0 =
      ∑ d : Fin 15, slotAreaCov s t d * classCoeff H d := by
  simp [areaAlong_eq, Real.cos_zero]

theorem kerAlong_zero (H : Mat4) (s : Fin 24) (t : Fin 10) :
    kerAlong H s t 0 =
      ∑ d : Fin 15, slotDeficitKer s t d * classCoeff H d := by
  simp [kerAlong_eq, Real.cos_zero]

theorem kerAlong_axis_zero (s : Fin 24) (t : Fin 10) :
    kerAlong axisTTPlus s t 0 = 0 := by
  rw [kerAlong_zero]
  simpa [classDot] using classDot_slotDeficitKer_axis s t

theorem kerAlong_gauge_zero (s : Fin 24) (t : Fin 10) :
    kerAlong decoyGauge s t 0 = 0 := by
  rw [kerAlong_zero]
  simpa [classDot] using classDot_slotDeficitKer_gauge s t

/-- Formal second-jet coefficient of `kerAlong` after using `K(0)=0`. -/
def kerM2Coeff (H : Mat4) (s : Fin 24) (t : Fin 10) : ℝ :=
  -(1 / 2 : ℝ) *
    ∑ d : Fin 15,
      slotDeficitKer s t d * classCoeff H d *
        (phaseScale (hingeBase s t) d) ^ 2

theorem tendsto_kerAlong_div_sq (H : Mat4) (s : Fin 24) (t : Fin 10)
    (h0 : kerAlong H s t 0 = 0) :
    Tendsto (fun μ : ℝ => kerAlong H s t μ / μ ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (kerM2Coeff H s t)) := by
  have hcongr :
      (fun μ : ℝ => kerAlong H s t μ / μ ^ 2) =ᶠ[𝓝[≠] (0 : ℝ)]
        fun μ : ℝ =>
          ∑ d : Fin 15,
            (slotDeficitKer s t d * classCoeff H d) *
              ((Real.cos (μ * phaseScale (hingeBase s t) d) - 1) / μ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with μ hμ
    have hne : μ ≠ 0 := hμ
    have hK := kerAlong_eq H s t μ
    have hsum0 : kerAlong H s t 0 = 0 := h0
    rw [kerAlong_zero] at hsum0
    have hrewrite :
        kerAlong H s t μ / μ ^ 2 =
          (∑ d : Fin 15,
              slotDeficitKer s t d * classCoeff H d *
                (Real.cos (μ * phaseScale (hingeBase s t) d) - 1)) / μ ^ 2 := by
      rw [hK]
      have hsub :
          (∑ d : Fin 15,
              slotDeficitKer s t d * classCoeff H d *
                Real.cos (μ * phaseScale (hingeBase s t) d)) -
            (∑ d : Fin 15, slotDeficitKer s t d * classCoeff H d) =
          ∑ d : Fin 15,
            slotDeficitKer s t d * classCoeff H d *
              (Real.cos (μ * phaseScale (hingeBase s t) d) - 1) := by
        simp [Finset.sum_sub_distrib, mul_sub]
      calc
        (∑ d : Fin 15,
              slotDeficitKer s t d * classCoeff H d *
                Real.cos (μ * phaseScale (hingeBase s t) d)) / μ ^ 2
            =
          ((∑ d : Fin 15,
                slotDeficitKer s t d * classCoeff H d *
                  Real.cos (μ * phaseScale (hingeBase s t) d)) -
              (∑ d : Fin 15, slotDeficitKer s t d * classCoeff H d)) /
            μ ^ 2 := by rw [hsum0, sub_zero]
        _ = (∑ d : Fin 15,
                slotDeficitKer s t d * classCoeff H d *
                  (Real.cos (μ * phaseScale (hingeBase s t) d) - 1)) /
            μ ^ 2 := by rw [hsub]
    rw [hrewrite, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    field_simp [hne]
  have hsum :
      Tendsto
        (fun μ : ℝ =>
          ∑ d : Fin 15,
            (slotDeficitKer s t d * classCoeff H d) *
              ((Real.cos (μ * phaseScale (hingeBase s t) d) - 1) / μ ^ 2))
        (𝓝[≠] (0 : ℝ))
        (𝓝
          (∑ d : Fin 15,
            (slotDeficitKer s t d * classCoeff H d) *
              (-(phaseScale (hingeBase s t) d) ^ 2 / 2))) := by
    apply tendsto_finset_sum
    intro d _
    exact
      (cos_sub_one_div_sq_tendsto (phaseScale (hingeBase s t) d)).const_mul _
  have htarget :
      (∑ d : Fin 15,
          (slotDeficitKer s t d * classCoeff H d) *
            (-(phaseScale (hingeBase s t) d) ^ 2 / 2)) =
        kerM2Coeff H s t := by
    unfold kerM2Coeff
    simp [div_eq_mul_inv, Finset.mul_sum, mul_left_comm, mul_assoc, mul_comm]
  rw [← htarget]
  exact (tendsto_congr' hcongr).mpr hsum

theorem continuous_areaAlong (H : Mat4) (s : Fin 24) (t : Fin 10) :
    Continuous (areaAlong H s t) := by
  have hfun :
      areaAlong H s t =
        fun μ : ℝ =>
          ∑ d : Fin 15,
            slotAreaCov s t d * classCoeff H d *
              Real.cos (μ * phaseScale (hingeBase s t) d) := by
    funext μ; exact areaAlong_eq H s t μ
  rw [hfun]
  refine continuous_finset_sum _ fun d _ => ?_
  continuity

theorem tendsto_slot_product (H : Mat4) (s : Fin 24) (t : Fin 10)
    (h0 : kerAlong H s t 0 = 0) :
    Tendsto
      (fun μ : ℝ => areaAlong H s t μ * kerAlong H s t μ / μ ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (areaAlong H s t 0 * kerM2Coeff H s t)) := by
  have hK := tendsto_kerAlong_div_sq H s t h0
  have hA :
      Tendsto (areaAlong H s t) (𝓝[≠] (0 : ℝ)) (𝓝 (areaAlong H s t 0)) :=
    ((continuous_areaAlong H s t).tendsto 0).mono_left nhdsWithin_le_nhds
  have hprod := Tendsto.mul hA hK
  have hcongr :
      (fun μ : ℝ => areaAlong H s t μ * (kerAlong H s t μ / μ ^ 2)) =ᶠ[
        𝓝[≠] (0 : ℝ)]
        fun μ : ℝ => areaAlong H s t μ * kerAlong H s t μ / μ ^ 2 := by
    filter_upwards with μ
    ring
  exact (tendsto_congr' hcongr).mp hprod

theorem m2SlotCoeff_eq_area_kerM2 (H : Mat4) (s : Fin 24) (t : Fin 10) :
    m2SlotCoeff H s t =
      (if isT11 s t then areaAlong H s t 0 * kerM2Coeff H s t else 0) := by
  unfold m2SlotCoeff kerM2Coeff
  by_cases ht : isT11 s t
  · simp [ht, areaAlong_zero]
  · simp [ht]

theorem tendsto_transportedSlotTerm_div_sq (H : Mat4) (s : Fin 24) (t : Fin 10)
    (h0 : kerAlong H s t 0 = 0) :
    Tendsto
      (fun μ : ℝ =>
        transportedSlotTerm H (fun i => μ * symbolDir i) s t / μ ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (m2SlotCoeff H s t)) := by
  by_cases ht : isT11 s t
  · have hterm :
        (fun μ : ℝ =>
            transportedSlotTerm H (fun i => μ * symbolDir i) s t / μ ^ 2) =
          fun μ : ℝ => areaAlong H s t μ * kerAlong H s t μ / μ ^ 2 := by
      funext μ
      simp [transportedSlotTerm, ht, areaAlong, kerAlong]
    rw [hterm, m2SlotCoeff_eq_area_kerM2 H s t, if_pos ht]
    exact tendsto_slot_product H s t h0
  · have hterm :
        (fun μ : ℝ =>
            transportedSlotTerm H (fun i => μ * symbolDir i) s t / μ ^ 2) =
          fun _ : ℝ => (0 : ℝ) := by
      funext μ
      simp [transportedSlotTerm, ht]
    rw [hterm, m2SlotCoeff_eq_area_kerM2 H s t, if_neg ht]
    exact tendsto_const_nhds

theorem tendsto_foldAlong_div_sq (H : Mat4)
    (h0 : ∀ s t, kerAlong H s t 0 = 0) :
    Tendsto (fun μ : ℝ => foldAlong H μ / μ ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (m2Symbol H)) := by
  have hsum :
      Tendsto
        (fun μ : ℝ =>
          ∑ s : Fin 24, ∑ t : Fin 10,
            transportedSlotTerm H (fun i => μ * symbolDir i) s t / μ ^ 2)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (∑ s : Fin 24, ∑ t : Fin 10, m2SlotCoeff H s t)) := by
    apply tendsto_finset_sum
    intro s _
    apply tendsto_finset_sum
    intro t _
    exact tendsto_transportedSlotTerm_div_sq H s t (h0 s t)
  have hcongr :
      (fun μ : ℝ => foldAlong H μ / μ ^ 2) =ᶠ[𝓝[≠] (0 : ℝ)]
        fun μ : ℝ =>
          ∑ s : Fin 24, ∑ t : Fin 10,
            transportedSlotTerm H (fun i => μ * symbolDir i) s t / μ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with μ hμ
    have hne : μ ≠ 0 := hμ
    unfold foldAlong blochFold11
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_div]
  exact (tendsto_congr' hcongr).mpr (by simpa [m2Symbol] using hsum)

theorem FoldAlongM2Tendsto_of_axisTTPlus :
    FoldAlongM2Tendsto axisTTPlus := by
  unfold FoldAlongM2Tendsto
  exact tendsto_foldAlong_div_sq axisTTPlus fun s t => kerAlong_axis_zero s t

theorem FoldAlongM2Tendsto_of_decoyGauge :
    FoldAlongM2Tendsto decoyGauge := by
  unfold FoldAlongM2Tendsto
  exact tendsto_foldAlong_div_sq decoyGauge fun s t => kerAlong_gauge_zero s t

theorem FoldAlongM2Tendsto_axisTTPlus_holds :
    FoldAlongM2Tendsto_axisTTPlus :=
  (FoldAlongM2Tendsto_axis_iff).mp FoldAlongM2Tendsto_of_axisTTPlus

theorem FoldAlongM2Tendsto_decoyGauge_holds :
    FoldAlongM2Tendsto_decoyGauge :=
  (FoldAlongM2Tendsto_gauge_iff).mp FoldAlongM2Tendsto_of_decoyGauge

end

end ReggeBlochM2Tendsto4D
end Analysis
end Gravity
end IndisputableMonolith
