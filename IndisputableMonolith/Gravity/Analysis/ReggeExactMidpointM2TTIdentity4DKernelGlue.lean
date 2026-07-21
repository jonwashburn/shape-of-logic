import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochData4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochSymbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactMidpointM2TTIdentity4DKernelCert
import IndisputableMonolith.Gravity.Analysis.ReggeExactMidpointM2TTIdentity4DM2NumAssemble

/-!
# Algebraic glue: Array-sum m^2 coeffs <-> Int fold <-> scale-32 tables

Lifts the kernel `decide` Int certificates to the Q coefficient tables used by
`ReggeExactMidpointM2TTIdentity4D`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeExactMidpointM2TTIdentity4D
namespace KernelGlue

open ReggeExactFlatHessianBlochData4D
open ReggeExactFlatHessianBlochSymbol4D (CouplingIdx)
open KernelCert
open BigOperators

set_option maxHeartbeats 80000000

/-- Old Array/Finset definition of the bi-quadratic coefficient. -/
def m2CoeffSum (a b c d i j : Fin 4) : ℚ :=
  Finset.sum (Finset.univ : Finset CouplingIdx) fun idx =>
    (-(1 / 4) : ℚ) * ((couplingTable[idx].num : ℚ) / (couplingTable[idx].den : ℚ)) *
      (couplingTable[idx].De a : ℚ) * (couplingTable[idx].De b : ℚ) *
      (couplingTable[idx].Dep c : ℚ) * (couplingTable[idx].Dep d : ℚ) *
      ((couplingTable[idx].delta2 i : ℚ) / 2) *
      ((couplingTable[idx].delta2 j : ℚ) / 2)

/-- Explicit table as scale-32 Int cast (replaces the giant match). -/
def explicitM2CoeffZ (a b c d i j : Fin 4) : ℚ :=
  (explicitZ a b c d i j : ℚ) / 32

/-- Closed table as scale-32 Int cast. -/
def closedCoeffZ (a b c d i j : Fin 4) : ℚ :=
  (closedZ a b c d i j : ℚ) / 32

private theorem toCZ_De (c : Coupling) (a : Fin 4) : De (toCZ c) a = c.De a := by
  fin_cases a <;> rfl

private theorem toCZ_Dep (c : Coupling) (a : Fin 4) : Dep (toCZ c) a = c.Dep a := by
  fin_cases a <;> rfl

private theorem toCZ_D2 (c : Coupling) (a : Fin 4) : D2 (toCZ c) a = c.delta2 a := by
  fin_cases a <;> rfl

/-- Per-coupling rational term equals Int contrib / 256, assuming `den | 16`. -/
theorem termQ_eq_contrib_div (c : Coupling) (a b cd d i j : Fin 4)
    (hd : c.den ∣ 16) (hden : c.den ≠ 0) :
    (-(1 / 4) : ℚ) * ((c.num : ℚ) / (c.den : ℚ)) *
        (c.De a : ℚ) * (c.De b : ℚ) * (c.Dep cd : ℚ) * (c.Dep d : ℚ) *
        ((c.delta2 i : ℚ) / 2) * ((c.delta2 j : ℚ) / 2) =
      (contrib (toCZ c) a b cd d i j : ℚ) / 256 := by
  have hdenQ : (c.den : ℚ) ≠ 0 := by exact_mod_cast hden
  have hNat : ((16 / c.den : Nat) : ℚ) = (16 : ℚ) / (c.den : ℚ) := by
    simpa using (Nat.cast_div (m := 16) (n := c.den) hd hdenQ).symm
  unfold contrib
  simp only [toCZ_De, toCZ_Dep, toCZ_D2, hNat]
  push_cast
  field_simp [hdenQ]
  ring

/-- Every den on the generated CZ list divides 16 and is nonzero. -/
theorem cz_den_dvd_sixteen (t : CZ) (ht : t ∈ couplingZList) :
    t.den ∣ 16 ∧ t.den ≠ 0 := by
  revert t ht
  decide

theorem coupling_den_dvd_sixteen (c : Coupling) (hc : c ∈ couplingTable.toList) :
    c.den ∣ 16 ∧ c.den ≠ 0 := by
  have hb := couplingZList_bridge
  have : toCZ c ∈ couplingZList := by
    have := List.mem_map_of_mem (f := toCZ) hc
    simpa [hb] using this
  simpa [toCZ] using cz_den_dvd_sixteen (toCZ c) this

private theorem sum_map_contrib_eq_m2Num (a b c d i j : Fin 4) :
    (couplingZList.map (fun t => contrib t a b c d i j)).sum =
      m2Num a b c d i j := by
  unfold m2Num
  induction couplingZList with
  | nil => simp
  | cons t ts ih =>
    simp [List.sum_cons, List.foldl, ih]
    abel

private theorem toList_sum_eq_finset_sum (a b c d i j : Fin 4) :
    (couplingTable.toList.map fun coup =>
        (-(1 / 4) : ℚ) * ((coup.num : ℚ) / (coup.den : ℚ)) *
          (coup.De a : ℚ) * (coup.De b : ℚ) *
          (coup.Dep c : ℚ) * (coup.Dep d : ℚ) *
          ((coup.delta2 i : ℚ) / 2) * ((coup.delta2 j : ℚ) / 2)).sum =
      m2CoeffSum a b c d i j := by
  unfold m2CoeffSum
  have hArr :
      couplingTable.toList =
        List.ofFn fun idx : CouplingIdx => couplingTable[idx] := by
    simpa using (Array.toList_eq_ofFn (xs := couplingTable)).symm
  simp [hArr, List.map_ofFn, List.sum_ofFn]

/-- Finset Array sum equals the bridged Int fold / 256. -/
theorem m2CoeffSum_eq_m2Num_div (a b c d i j : Fin 4) :
    m2CoeffSum a b c d i j = (m2Num a b c d i j : ℚ) / 256 := by
  rw [← toList_sum_eq_finset_sum]
  have hmap :
      (couplingTable.toList.map fun coup =>
          (-(1 / 4) : ℚ) * ((coup.num : ℚ) / (coup.den : ℚ)) *
            (coup.De a : ℚ) * (coup.De b : ℚ) *
            (coup.Dep c : ℚ) * (coup.Dep d : ℚ) *
            ((coup.delta2 i : ℚ) / 2) * ((coup.delta2 j : ℚ) / 2)) =
        couplingZList.map fun t => (contrib t a b c d i j : ℚ) / 256 := by
    have hb := couplingZList_bridge
    have h1 :
        (couplingTable.toList.map fun coup =>
            (-(1 / 4) : ℚ) * ((coup.num : ℚ) / (coup.den : ℚ)) *
              (coup.De a : ℚ) * (coup.De b : ℚ) *
              (coup.Dep c : ℚ) * (coup.Dep d : ℚ) *
              ((coup.delta2 i : ℚ) / 2) * ((coup.delta2 j : ℚ) / 2)) =
          couplingTable.toList.map fun coup =>
            (contrib (toCZ coup) a b c d i j : ℚ) / 256 := by
      refine List.map_congr_left.mpr fun coup hc => ?_
      obtain ⟨hdvd, hne⟩ := coupling_den_dvd_sixteen coup hc
      exact termQ_eq_contrib_div coup a b c d i j hdvd hne
    have h2 :
        (couplingTable.toList.map fun coup =>
            (contrib (toCZ coup) a b c d i j : ℚ) / 256) =
          (couplingTable.toList.map toCZ).map fun t =>
            (contrib t a b c d i j : ℚ) / 256 := by
      simp [List.map_map, Function.comp]
    rw [h1, h2, hb]
  rw [hmap]
  have hdiv :
      (couplingZList.map fun t => (contrib t a b c d i j : ℚ) / 256).sum =
        ((couplingZList.map fun t => contrib t a b c d i j).sum : ℚ) / 256 := by
    simp [List.sum_map_div]
  rw [hdiv, sum_map_contrib_eq_m2Num]

/-- m2CoeffSum equals the scale-32 explicit table. -/
theorem m2CoeffSum_eq_explicitM2CoeffZ :
    ∀ (a b c d i j : Fin 4),
      m2CoeffSum a b c d i j = explicitM2CoeffZ a b c d i j := by
  intro a b c d i j
  rw [m2CoeffSum_eq_m2Num_div, explicitM2CoeffZ, m2Num_eq_eight_explicitZ]
  push_cast
  ring

/-- ite closedCoeff equals scale-32 closedZ. -/
theorem closedCoeff_eq_closedCoeffZ :
    ∀ (a b c d i j : Fin 4),
      ((if a = c ∧ b = d ∧ i = j then -(1 / 8) else 0) +
          (if a = c ∧ b = i ∧ d = j then (1 / 4) else 0) +
          (if a = b ∧ c = d ∧ i = j then (1 / 8) else 0) +
          (if a = b ∧ c = i ∧ d = j then -(1 / 4) else 0) : ℚ) =
        closedCoeffZ a b c d i j := by
  intro a b c d i j
  unfold closedCoeffZ closedZ
  split_ifs <;> norm_num

/-- Scaling lemma for the order-4 flip average. -/
theorem sym4_scale
    (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Int)
    (a b c d i j : Fin 4) :
    ((C a b c d i j : ℚ) / 32 + (C b a c d i j : ℚ) / 32 +
        (C a b d c i j : ℚ) / 32 + (C b a d c i j : ℚ) / 32) / 4 =
      (sym4Z C a b c d i j : ℚ) / 32 := by
  unfold sym4Z
  push_cast
  ring

/-- Scaling lemma for the full order-8 symmetrization. -/
theorem symFull_scale
    (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Int)
    (a b c d i j : Fin 4) :
    (((C a b c d i j : ℚ) / 32 + (C b a c d i j : ℚ) / 32 +
            (C a b d c i j : ℚ) / 32 + (C b a d c i j : ℚ) / 32) / 4 +
        ((C c d a b i j : ℚ) / 32 + (C d c a b i j : ℚ) / 32 +
            (C c d b a i j : ℚ) / 32 + (C d c b a i j : ℚ) / 32) / 4) / 2 =
      (symFullZ C a b c d i j : ℚ) / 32 := by
  unfold symFullZ sym4Z
  push_cast
  ring

/-- Pointwise symFull equality on the scale-32 tables. -/
theorem symFullZ_rat_explicit_eq_closed :
    ∀ (a b c d i j : Fin 4),
      (symFullZ explicitZ a b c d i j : ℚ) / 32 =
        (symFullZ closedZ a b c d i j : ℚ) / 32 := by
  intro a b c d i j
  rw [symFullZ_explicit_eq_closed]

end KernelGlue
end ReggeExactMidpointM2TTIdentity4D
end Analysis
end Gravity
end IndisputableMonolith
