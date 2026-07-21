import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochData4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochTendsto4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianNormGate4D

/-!
# Exact midpoint Bloch trig-polynomial symbol (named)

Names the Stage-1 unit-cell exact flat Hessian as a finite trig polynomial
over `ReggeExactFlatHessianBlochData4D.couplingTable` (1208 couplings).

Centered Tendsto to the cosine two-jet is proved by specializing
`ReggeExactFlatHessianBlochTendsto4D.tendsto_centeredTrigPoly_div_sq`
through irreducible weight/phase/univ wrappers (avoids Fin-1208 array
whnf blowup during elaboration).

Algebraic normalization identity: discrete bookkeeping ×2 recovers
frozen `-1/4` (`ReggeExactFlatHessianNormGate4D`).  Ledger
`S_RS_converges_EH_4d` / `gap_action_recovery` remain open/false;
mesh ContinuumSymbolIs geometric Tendsto is the ledger gate.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeExactFlatHessianBlochSymbol4D

open ReggeExactFlatHessianBlochData4D
open ReggeExactFlatHessianBlochTendsto4D
open ReggeExactFlatHessianNormGate4D
open BigOperators Filter Topology

noncomputable section

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev Wave4 := Fin 4 → ℝ
abbrev CouplingIdx := Fin couplingTable.size

/-! ## §1. Trig-polynomial symbol (MODEL) -/

def edgeStrain (H : Mat4) (D : Fin 4 → ℤ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, H i j * (D i : ℝ) * (D j : ℝ)

def couplingPhase (c : Coupling) (k : Wave4) : ℝ :=
  ∑ i : Fin 4, k i * c.delta i

def couplingWeight (H : Mat4) (c : Coupling) : ℝ :=
  (1 / 2 : ℝ) * (c.s : ℝ) * edgeStrain H c.De * edgeStrain H c.Dep

def couplingWeightIdx (H : Mat4) (i : CouplingIdx) : ℝ :=
  couplingWeight H couplingTable[i]

def couplingPhaseIdx (k : Wave4) (i : CouplingIdx) : ℝ :=
  couplingPhase couplingTable[i] k

/-- Exact midpoint Bloch symbol: finite trig polynomial over the unit-cell
coupling table. -/
def exactMidpointBlochSymbol (H : Mat4) (k : Wave4) : ℝ :=
  ∑ i : CouplingIdx,
    couplingWeightIdx H i * Real.cos (couplingPhaseIdx k i)

/-- Cosine two-jet m² coefficient of the centered symbol. -/
def exactMidpointBlochM2 (H : Mat4) (k : Wave4) : ℝ :=
  ∑ i : CouplingIdx,
    couplingWeightIdx H i * (-(couplingPhaseIdx k i) ^ 2 / 2)

/-- Zero-momentum value of the trig polynomial. -/
def exactMidpointBlochSymbolZero (H : Mat4) : ℝ :=
  ∑ i : CouplingIdx, couplingWeightIdx H i

/-! ## §2. Irreducible specialization surface (Fin-1208 hygiene) -/

/-- Opaque univ: keeps `Finset.univ : Finset (Fin 1208)` from exploding
during Tendsto specialization. -/
irreducible_def couplingUniv : Finset CouplingIdx := Finset.univ

irreducible_def weightFn (H : Mat4) : CouplingIdx → ℝ := couplingWeightIdx H

irreducible_def phaseFn (dir : Wave4) : CouplingIdx → ℝ := couplingPhaseIdx dir

theorem couplingPhase_smul (t : ℝ) (dir : Wave4) (c : Coupling) :
    couplingPhase c (fun j => t * dir j) = t * couplingPhase c dir := by
  unfold couplingPhase
  simp_rw [mul_assoc]
  exact Eq.symm (Finset.mul_sum _ (fun i => dir i * c.delta i) t)

theorem couplingPhaseIdx_smul (t : ℝ) (dir : Wave4) (i : CouplingIdx) :
    couplingPhaseIdx (fun j => t * dir j) i =
      t * couplingPhaseIdx dir i := by
  unfold couplingPhaseIdx
  exact couplingPhase_smul t dir _

theorem couplingPhase_zero (c : Coupling) :
    couplingPhase c (fun _ => (0 : ℝ)) = 0 := by
  unfold couplingPhase
  simp only [zero_mul, Finset.sum_const_zero]

theorem couplingPhaseIdx_zero (i : CouplingIdx) :
    couplingPhaseIdx (fun _ => (0 : ℝ)) i = 0 := by
  unfold couplingPhaseIdx
  exact couplingPhase_zero _

theorem exactMidpointBlochSymbol_zero_eq (H : Mat4) :
    exactMidpointBlochSymbol H (fun _ => 0) = exactMidpointBlochSymbolZero H := by
  unfold exactMidpointBlochSymbol exactMidpointBlochSymbolZero
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [couplingPhaseIdx_zero, Real.cos_zero, mul_one]

private theorem sum_w_cos_sub_sum_w (H : Mat4) (dir : Wave4) (t : ℝ) :
    (∑ i : CouplingIdx,
        couplingWeightIdx H i *
          Real.cos (couplingPhaseIdx (fun j => t * dir j) i)) -
        ∑ i : CouplingIdx, couplingWeightIdx H i =
      ∑ i : CouplingIdx,
        couplingWeightIdx H i *
          (Real.cos (couplingPhaseIdx (fun j => t * dir j) i) - 1) := by
  simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]

private theorem centered_eq_irred (H : Mat4) (dir : Wave4) (t : ℝ) :
    exactMidpointBlochSymbol H (fun j => t * dir j) -
        exactMidpointBlochSymbolZero H =
      centeredTrigPoly (weightFn H) (phaseFn dir) couplingUniv t := by
  rw [weightFn_def, phaseFn_def, couplingUniv_def]
  unfold exactMidpointBlochSymbol exactMidpointBlochSymbolZero centeredTrigPoly
  rw [sum_w_cos_sub_sum_w]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [couplingPhaseIdx_smul]

private theorem m2_eq_irred (H : Mat4) (dir : Wave4) :
    exactMidpointBlochM2 H dir =
      centeredTrigPolyM2 (weightFn H) (phaseFn dir) couplingUniv := by
  rw [weightFn_def, phaseFn_def, couplingUniv_def]
  rfl

/-- **THEOREM:** centered exact midpoint Bloch `/ t²` tends to its cosine
two-jet.  Specialized through irreducible wrappers (no Fin-1208 whnf). -/
theorem tendsto_exactMidpointBloch_centered_div_sq
    (H : Mat4) (dir : Wave4) :
    Tendsto
      (fun t : ℝ =>
        (exactMidpointBlochSymbol H (fun j => t * dir j) -
            exactMidpointBlochSymbolZero H) / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (nhds (exactMidpointBlochM2 H dir)) := by
  have habs :=
    tendsto_centeredTrigPoly_div_sq (weightFn H) (phaseFn dir) couplingUniv
  have htarget :
      centeredTrigPolyM2 (weightFn H) (phaseFn dir) couplingUniv =
        exactMidpointBlochM2 H dir := (m2_eq_irred H dir).symm
  rw [← htarget]
  refine (tendsto_congr' ?_).mpr habs
  filter_upwards with t
  rw [centered_eq_irred]

/-- Division form: centered `/ (t² n)` tends to `m2 / n` when `n ≠ 0`. -/
theorem tendsto_exactMidpointBloch_m2_div
    (H : Mat4) (dir : Wave4) (n : ℝ) (hn : n ≠ 0) :
    Tendsto
      (fun t : ℝ =>
        (exactMidpointBlochSymbol H (fun j => t * dir j) -
            exactMidpointBlochSymbolZero H) / (t ^ 2 * n))
      (𝓝[≠] (0 : ℝ)) (nhds (exactMidpointBlochM2 H dir / n)) := by
  have h := tendsto_exactMidpointBloch_centered_div_sq H dir
  have hdiv := h.div_const n
  refine (tendsto_congr' ?_).mpr hdiv
  filter_upwards [self_mem_nhdsWithin] with t ht
  field_simp [ht, hn]

/-! ## §3. Status -/

structure ExactBlochSymbolStatus where
  trigPolyNamed : Bool
  abstractTendstoProved : Bool
  specializedTendstoProved : Bool
  normalizationGatePass : Bool
  srsInhabited : Bool
  gapActionRecovery : Bool

def exactBlochSymbolStatus : ExactBlochSymbolStatus where
  trigPolyNamed := true
  abstractTendstoProved := true
  specializedTendstoProved := true
  normalizationGatePass := true
  srsInhabited := false
  gapActionRecovery := false

theorem exactBlochSymbolStatus_flags :
    exactBlochSymbolStatus.trigPolyNamed = true ∧
      exactBlochSymbolStatus.abstractTendstoProved = true ∧
        exactBlochSymbolStatus.specializedTendstoProved = true ∧
          exactBlochSymbolStatus.normalizationGatePass = true ∧
            exactBlochSymbolStatus.srsInhabited = false ∧
              exactBlochSymbolStatus.gapActionRecovery = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gate_passes_with_discrete_bookkeeping :
    NormalizationGatePass = true ∧
      discreteBookkeepingFactor * exactUnitFrobeniusTTCoefficient =
        frozenPreflightEHCoefficient ∧
          continuumEHDiscreteFace (1 : ℝ) = frozenPreflightEHCoefficient :=
  ⟨normalizationGatePass_true, frozen_EH_is_discrete_bookkeeping_times_unitF.symm,
    continuumEHDiscreteFace_on_unitF⟩

/-- Compat alias: former option-C gate name. -/
theorem gate_passes_under_restatement_C :
    NormalizationGatePass = true ∧
      einsteinHilbertTTCoefficient4D_unitFrobenius =
        exactUnitFrobeniusTTCoefficient :=
  ⟨normalizationGatePass_true, unitFrobenius_EH_eq_exact⟩

/-- Re-export: abstract centered Tendsto is available for any weight/phase. -/
theorem abstract_centered_tendsto_available
    {ι : Type*} (w θ : ι → ℝ) (s : Finset ι) :
    Filter.Tendsto (fun t : ℝ => centeredTrigPoly w θ s t / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (centeredTrigPolyM2 w θ s)) :=
  tendsto_centeredTrigPoly_div_sq w θ s

/-- Historical residual string (closed by irreducible specialization). -/
def typedResidual_exact_bloch_fin1208_specialize : String :=
  "CLOSED: tendsto_exactMidpointBloch_centered_div_sq via irreducible couplingUniv/weightFn/phaseFn; abstract Tendsto specialized without Fin-1208 array whnf."

end

end ReggeExactFlatHessianBlochSymbol4D
end Analysis
end Gravity
end IndisputableMonolith
