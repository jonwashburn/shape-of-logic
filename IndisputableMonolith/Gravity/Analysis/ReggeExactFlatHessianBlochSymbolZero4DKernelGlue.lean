import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochData4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochSymbolZero4DKernelCert

/-!
# Q-lift: Int `qNum` → rational `qCoeff` for midpoint Bloch symbolZero

Closes the SymbolZero native_decide residual by transporting the kernel
`qNum_eq_zero` certificate to `qCoeff a b c d = 0` over `ℚ`.

Does **not** import the m2 Assemble/KernelGlue stack (avoids rebuilding
16 m2Num chunks when only SymbolZero hygiene is needed).
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeExactFlatHessianBlochSymbolZero4D
namespace KernelGlue

open ReggeExactFlatHessianBlochData4D
open ReggeExactMidpointM2TTIdentity4D.KernelCert
  (CZ toCZ De Dep couplingZList couplingZList_bridge)
open ReggeExactFlatHessianBlochSymbolZero4D.KernelCert
  (qContrib qNum qNum_eq_zero couplingZ_den_dvd_16)
open BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

abbrev CouplingIdx := Fin couplingTable.size

/-- Rational quartic coefficient (same formula as SymbolZero.`qCoeff`). -/
def qCoeff (a b c d : Fin 4) : ℚ :=
  ∑ i : CouplingIdx,
    (1 / 2 : ℚ) * ((couplingTable[i].num : ℚ) / (couplingTable[i].den : ℚ)) *
      (couplingTable[i].De a : ℚ) * (couplingTable[i].De b : ℚ) *
      (couplingTable[i].Dep c : ℚ) * (couplingTable[i].Dep d : ℚ)

private theorem couplingTable_toList_eq_ofFn :
    couplingTable.toList =
      List.ofFn (fun i : Fin couplingTable.size => couplingTable[i]) := by
  apply List.ext_getElem
  · rw [Array.length_toList, List.length_ofFn]
  · intro i h1 h2
    simp only [Array.getElem_toList, List.getElem_ofFn]
    rfl

theorem sum_couplingTable_eq_toList_sum (f : Coupling → ℚ) :
    (∑ idx : CouplingIdx, f couplingTable[idx]) =
      (couplingTable.toList.map f).sum := by
  have h2 :
      List.ofFn (fun i : Fin couplingTable.size => f couplingTable[i]) =
        couplingTable.toList.map f := by
    rw [couplingTable_toList_eq_ofFn]
    exact (List.map_ofFn (fun i : Fin couplingTable.size => couplingTable[i]) f).symm
  refine
    ((List.sum_ofFn
        (f := fun i : Fin couplingTable.size => f couplingTable[i])).symm).trans ?_
  rw [h2]

private theorem den_ne_zero {d : Nat} (hd : d ∣ 16) : d ≠ 0 := by
  intro h; subst h; exact (by decide : ¬(0 ∣ 16)) hd

private theorem nat_div_eq_of_dvd {n d : Nat} (hd : d ∣ n) (hd0 : d ≠ 0) :
    ((n / d : Nat) : ℚ) = (n : ℚ) / (d : ℚ) := by
  obtain ⟨k, rfl⟩ := hd
  have hk : (d * k / d : Nat) = k := Nat.mul_div_right k (Nat.pos_of_ne_zero hd0)
  have hdQ : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  rw [hk]
  field_simp [hdQ]
  norm_cast
  ring

private theorem De_toCZ (coup : Coupling) (x : Fin 4) :
    De (toCZ coup) x = coup.De x := by
  fin_cases x <;> rfl

private theorem Dep_toCZ (coup : Coupling) (x : Fin 4) :
    Dep (toCZ coup) x = coup.Dep x := by
  fin_cases x <;> rfl

private theorem qContrib_toCZ_eq (coup : Coupling) (a b c d : Fin 4) :
    qContrib (toCZ coup) a b c d =
      coup.num * coup.De a * coup.De b * coup.Dep c * coup.Dep d *
        ↑(16 / coup.den) := by
  simp only [qContrib]
  rw [De_toCZ, De_toCZ, Dep_toCZ, Dep_toCZ]
  simp only [toCZ]

theorem term_eq_qContrib_div32
    (coup : Coupling) (hd : coup.den ∣ 16) (a b c d : Fin 4) :
    (1 / 2 : ℚ) * ((coup.num : ℚ) / (coup.den : ℚ)) *
        (coup.De a : ℚ) * (coup.De b : ℚ) *
        (coup.Dep c : ℚ) * (coup.Dep d : ℚ) =
      (qContrib (toCZ coup) a b c d : ℚ) / 32 := by
  have hd0 : coup.den ≠ 0 := den_ne_zero hd
  have hdQ : (coup.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have hdiv : ((16 / coup.den : Nat) : ℚ) = (16 : ℚ) / (coup.den : ℚ) :=
    nat_div_eq_of_dvd hd hd0
  rw [qContrib_toCZ_eq]
  have hrhs :
      (((coup.num) * coup.De a * coup.De b * coup.Dep c * coup.Dep d *
          (↑(16 / coup.den) : Int) : Int) : ℚ) / 32 =
        ((coup.num : ℚ) * (coup.De a : ℚ) * (coup.De b : ℚ) * (coup.Dep c : ℚ) *
          (coup.Dep d : ℚ) * ((16 / coup.den : Nat) : ℚ)) / 32 := by
    simp only [Int.cast_mul, Int.cast_natCast]
  rw [hrhs, hdiv]
  field_simp [hdQ]
  ring

private theorem toCZ_mem_couplingZList_of_mem_toList
    {coup : Coupling} (hc : coup ∈ couplingTable.toList) :
    toCZ coup ∈ couplingZList := by
  rw [← couplingZList_bridge]
  exact List.mem_map_of_mem hc

theorem term_eq_qContrib_div32_of_mem
    {coup : Coupling} (hc : coup ∈ couplingTable.toList)
    (a b c d : Fin 4) :
    (1 / 2 : ℚ) * ((coup.num : ℚ) / (coup.den : ℚ)) *
        (coup.De a : ℚ) * (coup.De b : ℚ) *
        (coup.Dep c : ℚ) * (coup.Dep d : ℚ) =
      (qContrib (toCZ coup) a b c d : ℚ) / 32 := by
  have hz : toCZ coup ∈ couplingZList := toCZ_mem_couplingZList_of_mem_toList hc
  have hd : (toCZ coup).den ∣ 16 := couplingZ_den_dvd_16 _ hz
  have hd' : coup.den ∣ 16 := by simpa [toCZ] using hd
  exact term_eq_qContrib_div32 coup hd' a b c d

private theorem foldl_add_eq_add_sum
    (xs : List CZ) (acc : Int) (a b c d : Fin 4) :
    xs.foldl (fun s z => s + qContrib z a b c d) acc =
      acc + (xs.map (fun z => qContrib z a b c d)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons z zs ih =>
    simp [List.foldl_cons, List.map_cons, List.sum_cons, ih, add_assoc]

private theorem foldl_qContrib_eq_sum_map
    (xs : List CZ) (a b c d : Fin 4) :
    xs.foldl (fun acc z => acc + qContrib z a b c d) 0 =
      (xs.map (fun z => qContrib z a b c d)).sum := by
  simpa using foldl_add_eq_add_sum xs 0 a b c d

private theorem map_qContrib_div_sum
    (xs : List CZ) (a b c d : Fin 4) :
    (xs.map (fun z => (qContrib z a b c d : ℚ) / 32)).sum =
      ((xs.foldl (fun acc z => acc + qContrib z a b c d) 0 : Int) : ℚ) / 32 := by
  rw [foldl_qContrib_eq_sum_map]
  induction xs with
  | nil => simp
  | cons z zs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    push_cast
    ring

theorem qCoeff_eq_qNum_div32 (a b c d : Fin 4) :
    qCoeff a b c d = (qNum a b c d : ℚ) / 32 := by
  unfold qCoeff
  rw [sum_couplingTable_eq_toList_sum
      (fun coup =>
        (1 / 2 : ℚ) * ((coup.num : ℚ) / (coup.den : ℚ)) *
          (coup.De a : ℚ) * (coup.De b : ℚ) *
          (coup.Dep c : ℚ) * (coup.Dep d : ℚ))]
  have hpoint :
      couplingTable.toList.map
          (fun coup =>
            (1 / 2 : ℚ) * ((coup.num : ℚ) / (coup.den : ℚ)) *
              (coup.De a : ℚ) * (coup.De b : ℚ) *
              (coup.Dep c : ℚ) * (coup.Dep d : ℚ)) =
        couplingTable.toList.map
          (fun coup => (qContrib (toCZ coup) a b c d : ℚ) / 32) := by
    refine List.map_congr_left fun coup hc =>
      term_eq_qContrib_div32_of_mem hc a b c d
  rw [hpoint]
  have hmap :
      couplingTable.toList.map
          (fun coup => (qContrib (toCZ coup) a b c d : ℚ) / 32) =
        (couplingTable.toList.map toCZ).map
          (fun z => (qContrib z a b c d : ℚ) / 32) := by
    rw [List.map_map]
    rfl
  rw [hmap, couplingZList_bridge, map_qContrib_div_sum]
  rfl

/-- **THEOREM:** every rational quartic coefficient vanishes (kernel-lifted). -/
theorem qCoeff_eq_zero : ∀ (a b c d : Fin 4), qCoeff a b c d = 0 := by
  intro a b c d
  rw [qCoeff_eq_qNum_div32, qNum_eq_zero]
  simp

end KernelGlue
end ReggeExactFlatHessianBlochSymbolZero4D
end Analysis
end Gravity
end IndisputableMonolith
