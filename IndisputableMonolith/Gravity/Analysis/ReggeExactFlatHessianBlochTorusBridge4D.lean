import Mathlib
import IndisputableMonolith.Gravity.Analysis.Regge4DContinuumPreflight
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochSymbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochSymbolZero4D

/-!
# Discrete torus family glued into midpoint Bloch Tendsto

Composes the banked continuous-scale Tendsto
`tendsto_exactMidpointBloch_m2_div` along the mesh scale
`t(j) = 2π / torusSide j → 𝓝[≠] 0`.

The centered bridge is unconditional.  The uncentered form matching
`TypedResidual_discrete_torus_family_bridge` uses R2
(`ReggeExactFlatHessianBlochSymbolZero4D.exactMidpointBlochSymbolZero_eq_zero`).
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeExactFlatHessianBlochTorusBridge4D

open Regge4DContinuumPreflight
open ReggeExactFlatHessianBlochSymbol4D
open ReggeExactFlatHessianBlochSymbolZero4D
open BigOperators Filter Topology

noncomputable section

abbrev Mat4 := Regge4DContinuumPreflight.Mat4
abbrev Wave4 := Regge4DContinuumPreflight.Wave4

/-! ## §1. Mesh scale and mode identities -/

/-- Continuum scale for continuum index `j`: `2π / (j+3)`. -/
def torusScale (j : ℕ) : ℝ :=
  (2 * Real.pi) / (torusSide j : ℝ)

theorem torusScale_eq (j : ℕ) :
    torusScale j = (2 * Real.pi) / ((j + 3 : ℕ) : ℝ) := by
  unfold torusScale torusSide
  rfl

theorem realMode_eq_scale (j : ℕ) (m : IntMode4) :
    realMode (torusSide j) m = fun i => torusScale j * (m i : ℝ) := by
  funext i
  unfold realMode torusScale
  ring

theorem waveNormSq_intMode_eq (m : IntMode4) :
    waveNormSq (fun i => (m i : ℝ)) = ∑ i : Fin 4, (m i : ℝ) ^ 2 := by
  unfold waveNormSq
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem waveNormSq_intMode_ne_zero (m : IntMode4) (hm : m ≠ 0) :
    waveNormSq (fun i => (m i : ℝ)) ≠ 0 := by
  rw [waveNormSq_intMode_eq]
  intro hzero
  have hmi : ∀ i : Fin 4, (m i : ℝ) = 0 := by
    intro i
    have :=
      (Finset.sum_eq_zero_iff_of_nonneg
          (fun i (_ : i ∈ Finset.univ) => sq_nonneg (m i : ℝ))).1
        hzero i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp this
  apply hm
  funext i
  exact Int.cast_eq_zero.mp (hmi i)

theorem momentumNormSq_eq_scale_sq (j : ℕ) (m : IntMode4) :
    momentumNormSq (torusSide j) m =
      torusScale j ^ 2 * waveNormSq (fun i => (m i : ℝ)) := by
  simp [momentumNormSq_eq, waveNormSq_intMode_eq, torusScale]

/-! ## §2. Scale Tendsto into the punctured neighborhood of 0 -/

theorem tendsto_torusScale_nhds_zero :
    Tendsto torusScale atTop (nhds (0 : ℝ)) := by
  have h :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi)).comp
      (tendsto_add_atTop_nat 3)
  refine h.congr fun j => ?_
  simp [torusScale, torusSide]

theorem eventually_torusScale_ne_zero :
    ∀ᶠ j : ℕ in atTop, torusScale j ≠ 0 := by
  filter_upwards with j
  have hden : ((torusSide j : ℕ) : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (ne_of_gt (by unfold torusSide; omega))
  have hnum : (2 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  exact div_ne_zero hnum hden

theorem tendsto_torusScale_nhdsWithin_ne_zero :
    Tendsto torusScale atTop (𝓝[≠] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_torusScale_nhds_zero ?_
  filter_upwards [eventually_torusScale_ne_zero] with j hj
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact hj

/-! ## §3. Torus-family Tendsto (centered, then uncentered under R2) -/

/-- Centered discrete torus family: banked continuous Tendsto along `t(j)`. -/
theorem tendsto_exactMidpointBloch_torus_family_centered
    (m : IntMode4) (E : Mat4) (hm : m ≠ 0) :
    Tendsto
      (fun j : ℕ =>
        (exactMidpointBlochSymbol E (realMode (torusSide j) m) -
            exactMidpointBlochSymbolZero E) /
          momentumNormSq (torusSide j) m)
      atTop
      (nhds
        (exactMidpointBlochM2 E (fun i => (m i : ℝ)) /
          waveNormSq (fun i => (m i : ℝ)))) := by
  let dir : Wave4 := fun i => (m i : ℝ)
  let n : ℝ := waveNormSq dir
  have hn : n ≠ 0 := waveNormSq_intMode_ne_zero m hm
  have hcont := tendsto_exactMidpointBloch_m2_div E dir n hn
  have hcomp := hcont.comp tendsto_torusScale_nhdsWithin_ne_zero
  refine hcomp.congr' ?_
  filter_upwards with j
  dsimp only [Function.comp_apply]
  rw [realMode_eq_scale, momentumNormSq_eq_scale_sq]

/-- Uncentered form matching `TypedResidual_discrete_torus_family_bridge`.
Requires the R2 hypothesis `exactMidpointBlochSymbolZero E = 0`. -/
theorem tendsto_exactMidpointBloch_torus_family
    (m : IntMode4) (E : Mat4) (hm : m ≠ 0)
    (h0 : exactMidpointBlochSymbolZero E = 0) :
    Tendsto
      (fun j : ℕ =>
        exactMidpointBlochSymbol E (realMode (torusSide j) m) /
          momentumNormSq (torusSide j) m)
      atTop
      (nhds
        (exactMidpointBlochM2 E (fun i => (m i : ℝ)) /
          waveNormSq (fun i => (m i : ℝ)))) := by
  have h := tendsto_exactMidpointBloch_torus_family_centered m E hm
  refine h.congr' ?_
  filter_upwards with j
  rw [h0, sub_zero]

/-- Package: R2 for all polarizations inhabits the discrete torus bridge Prop
shape (same binders as `TypedResidual_discrete_torus_family_bridge`). -/
theorem discrete_torus_family_bridge_of_symbolZero
    (hZ : ∀ H : Mat4, exactMidpointBlochSymbolZero H = 0) :
    ∀ (m : IntMode4) (E : Mat4),
      m ≠ 0 →
        Tendsto
          (fun j : ℕ =>
            exactMidpointBlochSymbol E (realMode (torusSide j) m) /
              momentumNormSq (torusSide j) m)
          atTop
          (nhds
            (exactMidpointBlochM2 E (fun i => (m i : ℝ)) /
              waveNormSq (fun i => (m i : ℝ)))) :=
  fun m E hm => tendsto_exactMidpointBloch_torus_family m E hm (hZ E)

/-- **THEOREM (R4):** discrete torus family bridge, uncentered, for all
nonzero modes and all polarizations.  Composes banked continuous Tendsto
with R2 (`typedResidual_midpointBloch_symbolZero`). -/
theorem discrete_torus_family_bridge :
    ∀ (m : IntMode4) (E : Mat4),
      m ≠ 0 →
        Tendsto
          (fun j : ℕ =>
            exactMidpointBlochSymbol E (realMode (torusSide j) m) /
              momentumNormSq (torusSide j) m)
          atTop
          (nhds
            (exactMidpointBlochM2 E (fun i => (m i : ℝ)) /
              waveNormSq (fun i => (m i : ℝ)))) :=
  discrete_torus_family_bridge_of_symbolZero
    ReggeExactFlatHessianBlochSymbolZero4D.typedResidual_midpointBloch_symbolZero

/-- Mesh ContinuumSymbolIs binder is definitionally the torus-family
midpoint sequence; bridge therefore inhabits ContinuumSymbolIs at the
m² Rayleigh value (still geometric / j-dependent; not a constant face). -/
theorem continuumSymbolIs_midpoint_rayleigh
    (m : IntMode4) (E : Mat4) (hm : m ≠ 0) :
    Regge4DContinuumSymbolIs m E
      (exactMidpointBlochM2 E (fun i => (m i : ℝ)) /
        waveNormSq (fun i => (m i : ℝ))) :=
  discrete_torus_family_bridge m E hm

end

end ReggeExactFlatHessianBlochTorusBridge4D
end Analysis
end Gravity
end IndisputableMonolith
