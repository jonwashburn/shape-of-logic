import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochData4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochSymbol4D

/-!
# Exact midpoint Bloch symbol vanishes at zero momentum

Proves `∀ H, exactMidpointBlochSymbolZero H = 0` by expanding the
zero-momentum trig polynomial as a quartic form
`∑_{a,b,c,d} Q_abcd H_ab H_cd` with rational coefficients `Q_abcd`
read from `couplingTable`, then discharging `Q_abcd = 0` for all
index quadruples by `native_decide` over `ℚ`.

Inhabits `TypedResidual_midpointBloch_symbolZero` (same forall).
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeExactFlatHessianBlochSymbolZero4D

open ReggeExactFlatHessianBlochData4D
open ReggeExactFlatHessianBlochSymbol4D
open BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-! ## §1. Rational quartic coefficients (computable) -/

/-- Computable rational coupling weight (Data.`Coupling.s` is marked
noncomputable by section). -/
def couplingS (coup : Coupling) : ℚ :=
  (coup.num : ℚ) / (coup.den : ℚ)

theorem couplingS_eq_s (coup : Coupling) : couplingS coup = coup.s := rfl

/-- Quartic coefficient of the zero-momentum symbol:
`Q_abcd = ∑_i (1/2) s_i (De_i)_a (De_i)_b (Dep_i)_c (Dep_i)_d`. -/
def qCoeff (a b c d : Fin 4) : ℚ :=
  ∑ i : CouplingIdx,
    (1 / 2 : ℚ) * couplingS couplingTable[i] *
      (couplingTable[i].De a : ℚ) * (couplingTable[i].De b : ℚ) *
      (couplingTable[i].Dep c : ℚ) * (couplingTable[i].Dep d : ℚ)

/-- **THEOREM:** every rational quartic coefficient vanishes. -/
theorem qCoeff_eq_zero : ∀ (a b c d : Fin 4), qCoeff a b c d = 0 := by
  native_decide

noncomputable section

/-! ## §2. Expand symbolZero through the quartic form -/

/-- One coupling's real monomial coefficient before summing over the table. -/
def couplingMonomial (coup : Coupling) (a b c d : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * (couplingS coup : ℝ) *
    (coup.De a : ℝ) * (coup.De b : ℝ) * (coup.Dep c : ℝ) * (coup.Dep d : ℝ)

private theorem edgeStrain_mul_edgeStrain (H : Mat4) (De Dep : Fin 4 → ℤ) :
    edgeStrain H De * edgeStrain H Dep =
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        H a b * H c d * (De a : ℝ) * (De b : ℝ) * (Dep c : ℝ) * (Dep d : ℝ) := by
  unfold edgeStrain
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

private theorem couplingWeight_eq_quartic (H : Mat4) (coup : Coupling) :
    couplingWeight H coup =
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        couplingMonomial coup a b c d * H a b * H c d := by
  unfold couplingWeight couplingMonomial
  rw [← couplingS_eq_s]
  have hre :
      (1 / 2 : ℝ) * (couplingS coup : ℝ) * edgeStrain H coup.De * edgeStrain H coup.Dep =
        ((1 / 2 : ℝ) * (couplingS coup : ℝ)) *
          (edgeStrain H coup.De * edgeStrain H coup.Dep) := by
    ring
  rw [hre, edgeStrain_mul_edgeStrain]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

private theorem qCoeff_cast_eq_sum (a b c d : Fin 4) :
    (qCoeff a b c d : ℝ) =
      ∑ i : CouplingIdx, couplingMonomial couplingTable[i] a b c d := by
  unfold qCoeff couplingMonomial
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  push_cast
  ring

private theorem sum_comm_idx_fin4
    {α : Type*} [AddCommMonoid α]
    (f : CouplingIdx → Fin 4 → Fin 4 → Fin 4 → Fin 4 → α) :
    (∑ i : CouplingIdx, ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        f i a b c d) =
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        ∑ i : CouplingIdx, f i a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

private theorem factor_HabHcd (H : Mat4) (a b c d : Fin 4) :
    (∑ i : CouplingIdx,
        couplingMonomial couplingTable[i] a b c d * H a b * H c d) =
      (qCoeff a b c d : ℝ) * H a b * H c d := by
  have hα :
      ∀ i : CouplingIdx,
        couplingMonomial couplingTable[i] a b c d * H a b * H c d =
          couplingMonomial couplingTable[i] a b c d * (H a b * H c d) := by
    intro i; ring
  simp_rw [hα]
  rw [← Finset.sum_mul, ← qCoeff_cast_eq_sum]
  ring

private theorem sum_weight_eq_sum_quartic_terms (H : Mat4) :
    (∑ i : CouplingIdx, couplingWeight H couplingTable[i]) =
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        (qCoeff a b c d : ℝ) * H a b * H c d := by
  refine (Finset.sum_congr rfl fun i _ =>
    couplingWeight_eq_quartic H couplingTable[i]).trans ?_
  refine (sum_comm_idx_fin4
      (fun (i : CouplingIdx) (a b c d : Fin 4) =>
        couplingMonomial (couplingTable[i]) a b c d * H a b * H c d)).trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
      factor_HabHcd H a b c d

/-- Zero-momentum symbol equals the quartic form with coefficients `qCoeff`. -/
theorem exactMidpointBlochSymbolZero_eq_quartic (H : Mat4) :
    exactMidpointBlochSymbolZero H =
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        (qCoeff a b c d : ℝ) * H a b * H c d := by
  unfold exactMidpointBlochSymbolZero couplingWeightIdx
  exact sum_weight_eq_sum_quartic_terms H

/-! ## §3. Main theorem -/

/-- **THEOREM:** the exact midpoint Bloch symbol vanishes at zero momentum. -/
theorem exactMidpointBlochSymbolZero_eq_zero (H : Mat4) :
    exactMidpointBlochSymbolZero H = 0 := by
  rw [exactMidpointBlochSymbolZero_eq_quartic]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
    Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
  simp [qCoeff_eq_zero a b c d]

/-- Inhabits `TypedResidual_midpointBloch_symbolZero`
(`∀ H, exactMidpointBlochSymbolZero H = 0`). -/
theorem typedResidual_midpointBloch_symbolZero :
    ∀ H : Mat4, exactMidpointBlochSymbolZero H = 0 :=
  exactMidpointBlochSymbolZero_eq_zero

end

end ReggeExactFlatHessianBlochSymbolZero4D
end Analysis
end Gravity
end IndisputableMonolith
