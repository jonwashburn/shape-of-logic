import Mathlib
import IndisputableMonolith.Patterns
import IndisputableMonolith.Patterns.GrayCycle
import IndisputableMonolith.Patterns.GrayCode
import IndisputableMonolith.Patterns.GrayCodeAxioms
import IndisputableMonolith.Patterns.GrayCycleBRGC

/-!
# GrayCycle (general D) via BRGC (bounded) assumptions

This module is the **Workstream A generalization**: it constructs an adjacent Gray cover/cycle
for general dimension `d` using the standard BRGC formula

  `gray(n) = n XOR (n >>> 1)`

and exposes it as a `Patterns.GrayCover d (2^d)` / `Patterns.GrayCycle d`.

Status / hygiene:
- The construction is definitional.
- This file is intentionally a **bounded / bitwise-formula** development:
  the *successor adjacency* and the 64-bit inverse are routed through
  `Patterns/GrayCodeAxioms.lean`, so the packaged objects here require
  `[GrayCodeAxioms.GrayCodeFacts]` and a bound `d ≤ 64`.
- **Canonical axiom-free general-D certificate**: use
  `IndisputableMonolith/Patterns/GrayCycleBRGC.lean`, which constructs a recursive BRGC
  path via `append` + `rev` and proves injectivity + one-bit adjacency (including wrap)
  for all `d > 0` with **no axioms** and no `d ≤ 64` bound.
- The D=3 case remains fully axiom-free in `Patterns/GrayCycle.lean`.
-/

namespace IndisputableMonolith
namespace Patterns

open Classical

namespace GrayCycleGeneral

open GrayCodeAxioms

/-! ## The BRGC path as a Pattern-valued map -/

/-- The BRGC path as a `Fin (2^d) → Pattern d`. -/
def brgcPath (d : Nat) : Fin (2 ^ d) → Pattern d :=
  fun i => binaryReflectedGray d i

/-! ## One-bit adjacency of BRGC (bounded) -/

/-! ### Wrap-around step (last → 0) is one-bit adjacent (axiom-free) -/

private def allOnes (d : Nat) : Nat := 2 ^ d - 1

private lemma allOnes_succ_eq_bit (t : Nat) :
    allOnes (t + 1) = Nat.bit true (allOnes t) := by
  have hpos1 : 1 ≤ 2 ^ (t + 1) := Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2 : Nat)) (t + 1))
  have hpos0 : 1 ≤ 2 ^ t := Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2 : Nat)) t)
  -- LHS + 1
  have hL : allOnes (t + 1) + 1 = 2 ^ (t + 1) := by
    simp [allOnes, Nat.sub_add_cancel hpos1]
  -- RHS + 1
  have hR : Nat.bit true (allOnes t) + 1 = 2 ^ (t + 1) := by
    have hge : 2 ≤ 2 * (2 ^ t) := by
      have h1 : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by decide : 0 < (2 : Nat))
      -- multiply the inequality by 2
      simpa using (Nat.mul_le_mul_left 2 h1)
    calc
      Nat.bit true (allOnes t) + 1
          = (2 * (allOnes t) + 1) + 1 := by simp [Nat.bit_val, Nat.add_assoc]
      _ = 2 * (allOnes t) + 2 := by
          simp [Nat.add_assoc]
      _ = 2 * (2 ^ t - 1) + 2 := by
          simp [allOnes]
      _ = (2 * (2 ^ t) - 2) + 2 := by
          -- distribute `2 * (a - 1)` and simplify
          simp [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = 2 * (2 ^ t) := Nat.sub_add_cancel hge
      _ = 2 ^ (t + 1) := by
          -- `2^(t+1) = 2^t * 2`
          simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have h : allOnes (t + 1) + 1 = Nat.bit true (allOnes t) + 1 := by
    calc
      allOnes (t + 1) + 1 = 2 ^ (t + 1) := hL
      _ = Nat.bit true (allOnes t) + 1 := by
          simpa using hR.symm
  exact Nat.add_right_cancel h

private lemma allOnes_testBit_lt : ∀ {t k : Nat}, k < t → (allOnes t).testBit k = true
  | 0, _, hk => (Nat.not_lt_zero _ hk).elim
  | (t + 1), 0, _ => by
      -- `allOnes (t+1) = bit true (allOnes t)`
      have hrepr : allOnes (t + 1) = Nat.bit true (allOnes t) := allOnes_succ_eq_bit t
      simpa [hrepr] using (Nat.testBit_bit_zero true (allOnes t))
  | (t + 1), (k + 1), hk => by
      have hk' : k < t := Nat.lt_of_succ_lt_succ hk
      have hrepr : allOnes (t + 1) = Nat.bit true (allOnes t) := allOnes_succ_eq_bit t
      -- shift the bit index down one using `testBit_bit_succ`
      have hshift :
          (allOnes (t + 1)).testBit (k + 1) = (allOnes t).testBit k := by
        simpa [hrepr] using (Nat.testBit_bit_succ (b := true) (n := allOnes t) (m := k))
      -- now finish by IH
      simpa [hshift] using (allOnes_testBit_lt (t := t) (k := k) hk')

private lemma allOnes_testBit_eq_false_at (t : Nat) : (allOnes t).testBit t = false := by
  -- `allOnes t < 2^t`
  have hlt : allOnes t < 2 ^ t := by
    -- `2^t - 1 < 2^t` since `2^t > 0`
    simpa [allOnes] using Nat.sub_lt (pow_pos (by decide : 0 < (2 : Nat)) t) (by decide : 0 < 1)
  exact Nat.testBit_eq_false_of_lt hlt

theorem brgc_wrap_oneBitDiff {d : Nat} (hdpos : 0 < d) :
    OneBitDiff (brgcPath d ⟨2 ^ d - 1, by
      exact Nat.sub_lt (pow_pos (by decide : 0 < (2 : Nat)) d) (by decide)⟩) (brgcPath d 0) := by
  classical
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos) with ⟨t, rfl⟩
  -- d = t+1, unique differing bit is the last one (value t)
  let iLast : Fin (2 ^ (t + 1)) :=
    ⟨2 ^ (t + 1) - 1, by
      exact Nat.sub_lt (pow_pos (by decide : 0 < (2 : Nat)) (t + 1)) (by decide)⟩
  have hw : OneBitDiff (brgcPath (t + 1) iLast) (brgcPath (t + 1) 0) := by
    refine ⟨Fin.last t, ?_, ?_⟩
    · -- show the last bit differs (it is true at iLast, false at 0)
      have ht_true : (natToGray iLast.val).testBit t = true := by
        -- compute `natToGray (allOnes (t+1))` at bit t: true XOR false = true
        have hn : iLast.val = allOnes (t + 1) := rfl
        have hshift : (iLast.val >>> 1) = allOnes t := by
          -- `allOnes (t+1) = bit true (allOnes t)` ⇒ shiftRight 1 yields `allOnes t`
          have hrepr : allOnes (t + 1) = Nat.bit true (allOnes t) := allOnes_succ_eq_bit t
          -- use `bit_shiftRight_one`
          have : (Nat.bit true (allOnes t) >>> 1) = allOnes t := Nat.bit_shiftRight_one true (allOnes t)
          simpa [hn, hrepr] using this
        -- now compute testBit of xor
        -- n.testBit t = true (all ones), (n>>>1).testBit t = false
        have hnbit : (iLast.val).testBit t = true := by
          -- t < t+1
          have : t < t + 1 := Nat.lt_succ_self t
          simpa [hn, allOnes] using allOnes_testBit_lt (t := t + 1) (k := t) this
        have hmbit : (iLast.val >>> 1).testBit t = false := by
          -- iLast>>>1 = allOnes t, and that has bit t = false
          simpa [hshift] using allOnes_testBit_eq_false_at t
        -- combine via xor
        simp [natToGray, hnbit, hmbit]
      -- translate to the Pattern statement
      have : brgcPath (t + 1) iLast (Fin.last t) ≠ brgcPath (t + 1) 0 (Fin.last t) := by
        -- right side is false, left side is true
        have h0 : brgcPath (t + 1) 0 (Fin.last t) = false := by
          simp [brgcPath, binaryReflectedGray, natToGray]
        have h1 : brgcPath (t + 1) iLast (Fin.last t) = true := by
          simpa [brgcPath, binaryReflectedGray] using ht_true
        simpa [h0, h1]
      simpa using this
    · intro j hj
      -- any differing index must be the last one (all other bits are equal/false)
      induction j using Fin.lastCases with
      | last => rfl
      | cast j =>
          -- show contradiction: at castSucc j, both patterns are false
          have hjlt : (j.val : Nat) < t := j.isLt
          -- compute natToGray at bit j.val: true XOR true = false (since both allOnes have ones there)
          have hfalse : brgcPath (t + 1) iLast j.castSucc = false := by
            -- n = allOnes(t+1), m = n>>>1 = allOnes t
            have hn : iLast.val = allOnes (t + 1) := rfl
            have hnbit : (iLast.val).testBit j.val = true := by
              have : j.val < t + 1 := Nat.lt_succ_of_lt hjlt
              simpa [hn, allOnes] using allOnes_testBit_lt (t := t + 1) (k := j.val) this
            have hshift : (iLast.val >>> 1) = allOnes t := by
              have hrepr : allOnes (t + 1) = Nat.bit true (allOnes t) := allOnes_succ_eq_bit t
              have : (Nat.bit true (allOnes t) >>> 1) = allOnes t := Nat.bit_shiftRight_one true (allOnes t)
              simpa [hn, hrepr] using this
            have hmbit : (iLast.val >>> 1).testBit j.val = true := by
              simpa [hshift, allOnes] using allOnes_testBit_lt (t := t) (k := j.val) hjlt
            have : (natToGray iLast.val).testBit j.val = false := by
              simp [natToGray, hnbit, hmbit]
            simpa [brgcPath, binaryReflectedGray] using this
          have h0 : brgcPath (t + 1) 0 j.castSucc = false := by
            simp [brgcPath, binaryReflectedGray, natToGray]
          have : False := by
            -- hj says they differ, but both patterns are false
            simpa [hfalse, h0] using hj
          exact this.elim
  simpa [iLast] using hw

/-! ## Injectivity of the BRGC path (no extra axioms) -/

private lemma natToGray_testBit_false_of_ge {d n k : Nat} (hn : n < 2 ^ d) (hk : d ≤ k) :
    (natToGray n).testBit k = false := by
  -- natToGray n = n XOR (n >>> 1)
  have hn_lt : n < 2 ^ k := by
    have hpow : 2 ^ d ≤ 2 ^ k := by
      rcases lt_or_eq_of_le hk with hlt | rfl
      · exact le_of_lt (Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hlt)
      · rfl
    exact lt_of_lt_of_le hn hpow
  have hn_bit : n.testBit k = false := Nat.testBit_eq_false_of_lt hn_lt
  have hdiv_le : (n >>> 1) ≤ n := by
    -- shiftRight_eq_div_pow: n >>> 1 = n / 2
    simp [Nat.shiftRight_eq_div_pow, Nat.div_le_self]
  have hdiv_lt : (n >>> 1) < 2 ^ k := lt_of_le_of_lt hdiv_le hn_lt
  have hdiv_bit : (n >>> 1).testBit k = false := Nat.testBit_eq_false_of_lt hdiv_lt
  -- combine
  simp [natToGray, hn_bit, hdiv_bit]

variable [GrayCodeFacts]

theorem brgcPath_injective {d : Nat} (hdpos : 0 < d) (hd : d ≤ 64) : Function.Injective (brgcPath d) := by
  intro i j hij
  -- reduce to equality of the Nat Gray codes, then invert using `GrayCodeFacts.grayToNat_inverts_natToGray`.
  have hbits : ∀ k : Nat, (natToGray i.val).testBit k = (natToGray j.val).testBit k := by
    intro k
    by_cases hk : k < d
    · have := congrArg (fun p : Pattern d => p ⟨k, hk⟩) hij
      simpa [brgcPath, binaryReflectedGray, natToGray] using this
    · have hkge : d ≤ k := le_of_not_gt hk
      have hi0 : (natToGray i.val).testBit k = false :=
        natToGray_testBit_false_of_ge (d := d) (n := i.val) (k := k) i.isLt hkge
      have hj0 : (natToGray j.val).testBit k = false :=
        natToGray_testBit_false_of_ge (d := d) (n := j.val) (k := k) j.isLt hkge
      simp [hi0, hj0]
  have hgray : natToGray i.val = natToGray j.val := by
    exact Nat.eq_of_testBit_eq hbits
  -- show both indices are < 2^64
  have hpow : 2 ^ d ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hd
  have hi64 : i.val < 2 ^ 64 := lt_of_lt_of_le i.isLt hpow
  have hj64 : j.val < 2 ^ 64 := lt_of_lt_of_le j.isLt hpow
  have hi_inv : GrayCodeAxioms.grayInverse (natToGray i.val) = i.val :=
    GrayCodeFacts.grayToNat_inverts_natToGray (n := i.val) hi64
  have hj_inv : GrayCodeAxioms.grayInverse (natToGray j.val) = j.val :=
    GrayCodeFacts.grayToNat_inverts_natToGray (n := j.val) hj64
  have : i.val = j.val := by
    have := congrArg GrayCodeAxioms.grayInverse hgray
    simpa [hi_inv, hj_inv] using this
  exact Fin.ext this

lemma brgc_oneBit_step {d : Nat} (hdpos : 0 < d) (hd : d ≤ 64) :
    ∀ i : Fin (2 ^ d), OneBitDiff (brgcPath d i) (brgcPath d (i + 1)) := by
  intro i
  classical
  -- split on whether `i.val + 1 < 2^d` (no wrap) or wrap case
  by_cases hstep : i.val + 1 < 2 ^ d
  · -- Use the Gray-code one-bit property at the Nat level.
    rcases GrayCodeAxioms.gray_code_one_bit_property (d := d) (n := i.val) hstep with
      ⟨k, hk, hkuniq⟩
    have hklt : k < d := hk.1
    let kk : Fin d := ⟨k, hklt⟩
    refine ⟨kk, ?diff, ?uniq⟩
    · -- Show the bit differs at coordinate kk.
      haveI : NeZero (2 ^ d) := ⟨pow_ne_zero d (by decide : (2 : Nat) ≠ 0)⟩
      have hval : (i + 1).val = i.val + 1 :=
        Fin.val_add_one_of_lt' (n := 2 ^ d) (i := i) hstep
      dsimp [brgcPath, binaryReflectedGray, natToGray, kk]
      simpa [hval] using hk.2
    · intro j hj
      -- Uniqueness: any differing coordinate must be kk.
      haveI : NeZero (2 ^ d) := ⟨pow_ne_zero d (by decide : (2 : Nat) ≠ 0)⟩
      have hval : (i + 1).val = i.val + 1 :=
        Fin.val_add_one_of_lt' (n := 2 ^ d) (i := i) hstep
      have hjnat :
          ((i.val ^^^ (i.val >>> 1)).testBit j.val) ≠
            (((i.val + 1) ^^^ ((i.val + 1) >>> 1)).testBit j.val) := by
        dsimp [brgcPath, binaryReflectedGray, natToGray] at hj
        simpa [hval] using hj
      have : (j.val : Nat) = k := by
        exact hkuniq j.val ⟨j.isLt, hjnat⟩
      apply Fin.ext
      simpa [kk] using this
  · -- Wrap case: i is the last index and (i+1)=0 in `Fin (2^d)`.
    -- In the wrap branch, `i` must be the last element: `i.val = 2^d - 1`.
    have hi_eq : i.val = 2 ^ d - 1 := by
      have hle : i.val ≤ 2 ^ d - 1 := Nat.le_pred_of_lt i.isLt
      have hge : 2 ^ d - 1 ≤ i.val := by
        -- not (i+1 < 2^d) ⇒ 2^d ≤ i+1 ⇒ 2^d - 1 ≤ i
        have : 2 ^ d ≤ i.val + 1 := Nat.le_of_not_gt hstep
        have hpos : 0 < 2 ^ d := pow_pos (by decide : 0 < (2 : Nat)) d
        have : Nat.succ (2 ^ d - 1) ≤ Nat.succ i.val := by
          simpa [Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos hpos] using this
        exact Nat.succ_le_succ_iff.mp this
      exact Nat.le_antisymm hle hge
    let iLast : Fin (2 ^ d) :=
      ⟨2 ^ d - 1, by
        exact Nat.sub_lt (pow_pos (by decide : 0 < (2 : Nat)) d) (by decide)⟩
    have hi_def : i = iLast := by
      apply Fin.ext
      simp [iLast, hi_eq]
    have hsucc0_last : iLast + 1 = 0 := by
      apply Fin.ext
      -- compute val_add modulo 2^d at the last index
      have hle : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide : 0 < (2 : Nat))
      -- (2^d - 1 + 1) % 2^d = 0
      simp [Fin.val_add, iLast, Nat.sub_add_cancel hle]
    -- reduce to the wrap-around axiom statement (last index → 0)
    simpa [hi_def, hsucc0_last] using (brgc_wrap_oneBitDiff (d := d) hdpos)

/-! ## General GrayCycle/GrayCover existence under explicit assumptions -/

/-- A packaged Gray cycle for general `d` under the bounded BRGC assumptions. -/
noncomputable def brgcGrayCycle (d : Nat) (hdpos : 0 < d) (hd : d ≤ 64) : GrayCycle d :=
{ path := brgcPath d
  inj := brgcPath_injective (d := d) hdpos hd
  oneBit_step := brgc_oneBit_step (d := d) hdpos hd
}

/-- A packaged Gray cover (surjective + one-bit steps) derived from `brgcGrayCycle`. -/
noncomputable def brgcGrayCover (d : Nat) (hdpos : 0 < d) (hd : d ≤ 64) : GrayCover d (2 ^ d) :=
{ path := brgcPath d
  complete := by
    classical
    have h_inj : Function.Injective (brgcPath d) := brgcPath_injective (d := d) hdpos hd
    have h_card : Fintype.card (Fin (2 ^ d)) = Fintype.card (Pattern d) := by
      simp [Patterns.card_pattern]
    have h_bij : Function.Bijective (brgcPath d) := by
      -- Use the `Fintype` lemma: injective + equal card ⇒ bijective.
      exact (Fintype.bijective_iff_injective_and_card (brgcPath d)).2 ⟨h_inj, h_card⟩
    exact h_bij.2
  oneBit_step := brgc_oneBit_step (d := d) hdpos hd
}

/-- **THEOREM (GENERAL)**: There exists a Gray cycle for any dimension `d > 0`.

    This theorem provides the unconditional existence witness by delegating to
    the recursive BRGC construction in `GrayCycleBRGC.lean`. -/
theorem exists_grayCycle {d : Nat} (hdpos : 0 < d) : ∃ w : GrayCycle d, w.path 0 = GrayCycleBRGC.brgcPath d 0 :=
  ⟨GrayCycleBRGC.brgcGrayCycle d hdpos, rfl⟩

/-- **THEOREM (GENERAL)**: There exists a Gray cover for any dimension `d > 0`. -/
theorem exists_grayCover {d : Nat} (hdpos : 0 < d) : ∃ w : GrayCover d (2 ^ d), w.path 0 = GrayCycleBRGC.brgcPath d 0 :=
  ⟨GrayCycleBRGC.brgcGrayCover d hdpos, rfl⟩

theorem exists_grayCycle_of_le64 {d : Nat} (hdpos : 0 < d) (hd : d ≤ 64) :
    ∃ w : GrayCycle d, w.path = brgcPath d :=
  ⟨brgcGrayCycle d hdpos hd, rfl⟩

theorem exists_grayCover_of_le64 {d : Nat} (hdpos : 0 < d) (hd : d ≤ 64) :
    ∃ w : GrayCover d (2 ^ d), w.path = brgcPath d :=
  ⟨brgcGrayCover d hdpos hd, rfl⟩

end GrayCycleGeneral

end Patterns
end IndisputableMonolith
