import Mathlib
import IndisputableMonolith.Patterns
import IndisputableMonolith.Patterns.GrayCycle

/-!
# GrayCycle (general D) via BRGC recursion (axiom-free)

This module provides an **axiom-free** general-\(D\) Gray cycle construction using the
standard *recursive* BRGC definition:

- BRGC(0) = [0]
- BRGC(d+1) = [0·BRGC(d), 1·(BRGC(d))ʳ]

We implement this as a `Fin (2^d) → Pattern d` path, and prove:
- injectivity (no repeats),
- one-bit adjacency (including wrap-around) for all `d > 0`,
- packaged `GrayCycle d` / `GrayCover d (2^d)`.

This construction is independent of `Patterns/GrayCodeAxioms.lean` and does **not**
use the bitwise formula `gray(n) = n XOR (n >> 1)`.
-/

namespace IndisputableMonolith
namespace Patterns

open Classical

namespace GrayCycleBRGC

/-! ## Utilities: extend a pattern with a trailing bit -/

/-- Append a fresh *last* coordinate `b` to a pattern `p : Pattern d`, yielding a pattern in
dimension `d+1`. -/
def snocBit {d : Nat} (p : Pattern d) (b : Bool) : Pattern (d + 1) :=
  fun j => Fin.lastCases b (fun k => p k) j

@[simp] lemma snocBit_castSucc {d : Nat} (p : Pattern d) (b : Bool) (k : Fin d) :
    snocBit p b k.castSucc = p k := by
  simp [snocBit]

@[simp] lemma snocBit_last {d : Nat} (p : Pattern d) (b : Bool) :
    snocBit p b (Fin.last d) = b := by
  simp [snocBit]

/-! ## The recursive BRGC path -/

private lemma twoPow_succ_eq_add (d : Nat) : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by
  -- `2^(d+1) = 2^d * 2 = 2 * 2^d = 2^d + 2^d`
  simpa [pow_succ, Nat.mul_comm, Nat.two_mul]

/-- The recursive BRGC path as a `Fin (2^d) → Pattern d`. -/
def brgcPath : (d : Nat) → Fin (2 ^ d) → Pattern d
  | 0, _ =>
      -- unique 0-bit pattern
      fun _ => False
  | (d + 1), i =>
      let T : Nat := 2 ^ d
      let hTT : 2 ^ (d + 1) = T + T := by
        simpa [T, twoPow_succ_eq_add d]
      let i' : Fin (T + T) := i.cast hTT
      let left : Fin T → Pattern (d + 1) := fun k => snocBit (brgcPath d k) false
      let right : Fin T → Pattern (d + 1) := fun k => snocBit (brgcPath d (Fin.rev k)) true
      Fin.append left right i'

/-! ## Injectivity (no repeats) -/

private lemma cast_add_one {n m : Nat} [NeZero n] [NeZero m] (h : n = m) (i : Fin n) :
    (i + 1).cast h = (i.cast h) + 1 := by
  subst h
  simp

theorem brgcPath_injective : ∀ d : Nat, Function.Injective (brgcPath d)
  | 0 => by
      intro i j _
      -- `Fin 1` is a subsingleton (only `0`)
      simpa [Fin.eq_zero i, Fin.eq_zero j]
  | (d + 1) => by
      intro i j hij
      -- unfold the `d+1` definition and reduce to injectivity of the appended halves
      classical
      let T : Nat := 2 ^ d
      have hTT : 2 ^ (d + 1) = T + T := by
        simpa [T, twoPow_succ_eq_add d]
      let left : Fin T → Pattern (d + 1) := fun k => snocBit (brgcPath d k) false
      let right : Fin T → Pattern (d + 1) := fun k => snocBit (brgcPath d (Fin.rev k)) true
      have hij' :
          Fin.append left right (i.cast hTT) = Fin.append left right (j.cast hTT) := by
        simpa [brgcPath, T, hTT, left, right] using hij

      have hleft_inj : Function.Injective left := by
        intro a b hab
        have hab' : brgcPath d a = brgcPath d b := by
          funext k
          have := congrArg (fun p : Pattern (d + 1) => p k.castSucc) hab
          simpa [left, snocBit] using this
        exact (brgcPath_injective d) hab'

      have hright_inj : Function.Injective right := by
        intro a b hab
        have hab' : brgcPath d (Fin.rev a) = brgcPath d (Fin.rev b) := by
          funext k
          have := congrArg (fun p : Pattern (d + 1) => p k.castSucc) hab
          simpa [right, snocBit] using this
        have : Fin.rev a = Fin.rev b := (brgcPath_injective d) hab'
        exact Fin.rev_injective this

      have hdis : ∀ a b : Fin T, left a ≠ right b := by
        intro a b hab
        have := congrArg (fun p : Pattern (d + 1) => p (Fin.last d)) hab
        -- last coordinate is the appended bit: false on left, true on right
        simpa [left, right] using this

      have happ_inj : Function.Injective (Fin.append left right) :=
        (Fin.append_injective_iff (xs := left) (ys := right)).2 ⟨hleft_inj, hright_inj, hdis⟩

      have hcast : i.cast hTT = j.cast hTT := happ_inj hij'
      -- cast back along the inverse equality
      have := congrArg (Fin.cast hTT.symm) hcast
      simpa [hTT] using this

/-! ## One-bit adjacency -/

private theorem oneBitDiff_snocBit_same {d : Nat} {p q : Pattern d} (b : Bool) :
    OneBitDiff p q → OneBitDiff (snocBit p b) (snocBit q b) := by
  intro h
  classical
  rcases h with ⟨k, hk, hkuniq⟩
  refine ⟨k.castSucc, ?_, ?_⟩
  · simpa using hk
  · intro j hj
    -- any differing coordinate cannot be the new last coordinate (since it is fixed to `b`)
    induction j using Fin.lastCases with
    | last =>
        have : False := by
          simpa [snocBit] using hj
        exact this.elim
    | cast j =>
        have hj' : p j ≠ q j := by
          simpa [snocBit] using hj
        have : j = k := hkuniq j hj'
        simpa [this]

private theorem oneBitDiff_snocBit_flip {d : Nat} (p : Pattern d) :
    OneBitDiff (snocBit p false) (snocBit p true) := by
  classical
  refine ⟨Fin.last d, ?_, ?_⟩
  · simp
  · intro j hj
    induction j using Fin.lastCases with
    | last => rfl
    | cast j =>
        have : False := by
          -- on old coordinates the patterns are equal
          simpa [snocBit] using hj
        exact this.elim

/-! ### Relating `natAdd` vs `addNat` when the sizes match -/

private lemma natAdd_eq_addNat {T : Nat} (k : Fin T) :
    (Fin.natAdd T k : Fin (T + T)) = k.addNat T := by
  apply Fin.ext
  -- both sides represent the same natural number `T + k`
  simp [Fin.natAdd, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private lemma rev_add_one_eq {n : Nat} [NeZero n] {i : Fin n} (hi : i.val + 1 < n) :
    Fin.rev (i + 1) + 1 = Fin.rev i := by
  classical
  apply Fin.ext
  have hival : (i + 1).val = i.val + 1 :=
    Fin.val_add_one_of_lt' (n := n) (i := i) hi
  have hle1 : i.val + 1 ≤ n := Nat.le_of_lt hi
  have hle2 : i.val + 2 ≤ n := Nat.succ_le_of_lt hi
  have hnat : (n - (i.val + 2)) + 1 = n - (i.val + 1) := by
    have h :
        ((n - (i.val + 2)) + 1) + (i.val + 1) = (n - (i.val + 1)) + (i.val + 1) := by
      calc
        ((n - (i.val + 2)) + 1) + (i.val + 1)
            = (n - (i.val + 2)) + (1 + (i.val + 1)) := by
                simp [Nat.add_assoc]
        _ = (n - (i.val + 2)) + (i.val + 2) := by
                simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = n := Nat.sub_add_cancel hle2
        _ = (n - (i.val + 1)) + (i.val + 1) := (Nat.sub_add_cancel hle1).symm
    exact Nat.add_right_cancel h
  have hrev_succ : (Fin.rev (i + 1)).val = n - (i.val + 2) := by
    simp [Fin.val_rev, hival, Nat.add_assoc]
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hpos1 : 0 < i.val + 1 := Nat.succ_pos _
  have hlt : n - (i.val + 1) < n := Nat.sub_lt hnpos hpos1
  have hrev_add_lt : (Fin.rev (i + 1)).val + 1 < n := by
    calc
      (Fin.rev (i + 1)).val + 1
          = n - (i.val + 1) := by
              calc
                (Fin.rev (i + 1)).val + 1 = (n - (i.val + 2)) + 1 := by
                  simpa [hrev_succ]
                _ = n - (i.val + 1) := hnat
      _ < n := hlt
  have hL : (Fin.rev (i + 1) + 1).val = (Fin.rev (i + 1)).val + 1 :=
    Fin.val_add_one_of_lt' (n := n) (i := Fin.rev (i + 1)) hrev_add_lt
  have hR : (Fin.rev i).val = n - (i.val + 1) := by
    simp [Fin.val_rev]
  calc
    (Fin.rev (i + 1) + 1).val = (Fin.rev (i + 1)).val + 1 := hL
    _ = (n - (i.val + 2)) + 1 := by simpa [hrev_succ]
    _ = n - (i.val + 1) := hnat
    _ = (Fin.rev i).val := by simpa [hR]

theorem brgc_oneBit_step : ∀ {d : Nat}, 0 < d →
    ∀ i : Fin (2 ^ d), OneBitDiff (brgcPath d i) (brgcPath d (i + 1))
  | 0, hdpos => (Nat.not_lt_zero _ hdpos).elim
  | 1, _ => by
      intro i
      -- dimension 1: the cycle is `0 → 1 → 0`, so the only bit flips each step
      fin_cases i
      · -- 0 → 1
        have : OneBitDiff (snocBit (brgcPath 0 0) false) (snocBit (brgcPath 0 0) true) :=
          oneBitDiff_snocBit_flip (p := brgcPath 0 0)
        simpa [brgcPath] using this
      · -- 1 → 0 (wrap), use symmetry
        have h : OneBitDiff (snocBit (brgcPath 0 0) false) (snocBit (brgcPath 0 0) true) :=
          oneBitDiff_snocBit_flip (p := brgcPath 0 0)
        have : OneBitDiff (snocBit (brgcPath 0 0) true) (snocBit (brgcPath 0 0) false) :=
          OneBitDiff_symm h
        simpa [brgcPath] using this
  | (d + 2), _ => by
      -- Inductive step: assume one-bit stepping for dimension `d+1`, prove for `d+2`.
      have ih :
          ∀ i : Fin (2 ^ (d + 1)), OneBitDiff (brgcPath (d + 1) i) (brgcPath (d + 1) (i + 1)) :=
        brgc_oneBit_step (d := d + 1) (Nat.succ_pos _)
      intro i
      classical
      let T : Nat := 2 ^ (d + 1)
      have hTT : 2 ^ (d + 2) = T + T := by
        simpa [T] using twoPow_succ_eq_add (d := d + 1)
      let left : Fin T → Pattern (d + 2) := fun k => snocBit (brgcPath (d + 1) k) false
      let right : Fin T → Pattern (d + 2) := fun k => snocBit (brgcPath (d + 1) (Fin.rev k)) true
      let i' : Fin (T + T) := i.cast hTT

      have hTpos : 0 < T := pow_pos (by decide : 0 < (2 : Nat)) (d + 1)
      letI : NeZero T := ⟨Nat.ne_zero_of_lt hTpos⟩
      letI : NeZero (T + T) := ⟨Nat.ne_zero_of_lt (Nat.add_pos_left hTpos T)⟩

      have hcast_succ : (i + 1).cast hTT = i' + 1 := by
        -- `cast` commutes with `+1` along definitional equalities
        simpa [i'] using (cast_add_one (n := 2 ^ (d + 2)) (m := T + T) (h := hTT) i)

      -- Reduce to the `Fin (T+T)` index space.
      have hTTgoal : OneBitDiff (Fin.append left right i') (Fin.append left right (i' + 1)) := by
        -- case split on whether `i'` lies in the left or right half, and whether we cross a boundary
        induction i' using Fin.addCases with
        | left k =>
            -- i' = castAdd T k
            by_cases hk : k.val + 1 < T
            · -- successor stays in the left half
              have hk_big : (Fin.castAdd T k : Fin (T + T)).val + 1 < T + T := by
                -- k.val + 1 < T ≤ T+T
                exact lt_of_lt_of_le hk (Nat.le_add_right T T)
              have hnext : (Fin.castAdd T k : Fin (T + T)) + 1 = Fin.castAdd T (k + 1) := by
                apply Fin.ext
                have hk1 : (k + 1).val = k.val + 1 :=
                  Fin.val_add_one_of_lt' (n := T) (i := k) hk
                have hk'1 : ((Fin.castAdd T k : Fin (T + T)) + 1).val =
                    (Fin.castAdd T k : Fin (T + T)).val + 1 :=
                  Fin.val_add_one_of_lt' (n := T + T) (i := Fin.castAdd T k) hk_big
                simpa [hk1] using hk'1
              -- adjacency comes from IH in dimension d+1, lifted through `snocBit`
              have hstep : OneBitDiff (brgcPath (d + 1) k) (brgcPath (d + 1) (k + 1)) := ih k
              have hstep' : OneBitDiff (left k) (left (k + 1)) :=
                oneBitDiff_snocBit_same false hstep
              -- rewrite the `append` evaluations
              simpa [Fin.append_left, hnext, left, right] using hstep'
            · -- boundary: last element of left half steps into the first element of right half
              have hkval : k.val = T - 1 := by
                have hle : k.val + 1 ≤ T := Nat.succ_le_of_lt k.isLt
                have hge : T ≤ k.val + 1 := Nat.le_of_not_gt hk
                have : k.val + 1 = T := Nat.le_antisymm hle hge
                exact Nat.eq_sub_of_add_eq this
              have hnext : (Fin.castAdd T k : Fin (T + T)) + 1 = Fin.natAdd T 0 := by
                apply Fin.ext
                -- both have value `T`
                have hT1 : 1 ≤ T := Nat.succ_le_of_lt hTpos
                have hkplus : (Fin.castAdd T k : Fin (T + T)).val + 1 = T := by
                  -- `(castAdd T k).val = k.val = T-1`
                  simpa [hkval, Nat.sub_add_cancel hT1]
                have hk_big : (Fin.castAdd T k : Fin (T + T)).val + 1 < T + T := by
                  -- `T < T+T` since `T>0`
                  have hT1 : 1 ≤ T := Nat.succ_le_of_lt hTpos
                  have hTlt : T < T + T := by
                    have hle : T + 1 ≤ T + T := Nat.add_le_add_left hT1 T
                    exact lt_of_lt_of_le (Nat.lt_succ_self T) hle
                  -- rewrite the LHS using `hkplus : (castAdd ...).val + 1 = T`
                  exact hkplus.symm ▸ hTlt
                have hk'1 : ((Fin.castAdd T k : Fin (T + T)) + 1).val =
                    (Fin.castAdd T k : Fin (T + T)).val + 1 :=
                  Fin.val_add_one_of_lt' (n := T + T) (i := Fin.castAdd T k) hk_big
                have hval : ((Fin.castAdd T k : Fin (T + T)) + 1).val = T := by
                  exact hk'1.trans hkplus
                -- `natAdd T 0` has val `T`
                simpa [hval]
              -- show underlying index on the right is also `k` (since `rev 0` is last)
              have hrev0 : Fin.rev (0 : Fin T) = k := by
                apply Fin.ext
                -- `rev 0` has value `T-1`
                simpa [hkval] using (Fin.val_rev_zero (n := T))
              have hstep' : OneBitDiff (left k) (right 0) := by
                -- same underlying pattern, last bit flips
                simpa [left, right, hrev0] using (oneBitDiff_snocBit_flip (p := brgcPath (d + 1) k))
              -- rewrite `append` at the boundary indices explicitly (avoid `natAdd`/`addNat` mismatch issues)
              have happL : Fin.append left right (Fin.castAdd T k) = left k := by
                simpa using (Fin.append_left (u := left) (v := right) k)
              have happNext : Fin.append left right ((Fin.castAdd T k : Fin (T + T)) + 1) = right 0 := by
                have : Fin.append left right (Fin.natAdd T (0 : Fin T)) = right 0 := by
                  simpa using (Fin.append_right (u := left) (v := right) (i := (0 : Fin T)))
                simpa [hnext] using this
              have hstep0 : OneBitDiff (Fin.append left right (Fin.castAdd T k)) (right 0) := by
                simpa [happL] using hstep'
              -- replace `right 0` with the `append` at the successor index
              simpa [happNext.symm] using hstep0
        | right k =>
            -- i' = natAdd T k
            by_cases hk : k.val + 1 < T
            · -- successor stays in the right half
              have hk_big : (Fin.natAdd T k : Fin (T + T)).val + 1 < T + T := by
                -- (T + k.val) + 1 < T + T since k.val + 1 < T
                have : T + (k.val + 1) < T + T := Nat.add_lt_add_left hk T
                simpa [Fin.natAdd, Nat.add_assoc] using this
              have hnext : (Fin.natAdd T k : Fin (T + T)) + 1 = Fin.natAdd T (k + 1) := by
                apply Fin.ext
                have hk1 : (k + 1).val = k.val + 1 :=
                  Fin.val_add_one_of_lt' (n := T) (i := k) hk
                have hk'1 : ((Fin.natAdd T k : Fin (T + T)) + 1).val =
                    (Fin.natAdd T k : Fin (T + T)).val + 1 :=
                  Fin.val_add_one_of_lt' (n := T + T) (i := Fin.natAdd T k) hk_big
                simpa [hk1, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk'1
              -- adjacency comes from IH in dimension d+1, but the right half is reversed
              have hrevStep : OneBitDiff
                  (brgcPath (d + 1) (Fin.rev (k + 1))) (brgcPath (d + 1) ((Fin.rev (k + 1)) + 1)) := ih (Fin.rev (k + 1))
              have hrevRel : (Fin.rev (k + 1) : Fin T) + 1 = Fin.rev k := by
                -- rev(k+1) + 1 = rev(k) when k.val+1 < T
                -- use the helper lemma on `Fin T`
                simpa [Nat.add_assoc] using (rev_add_one_eq (n := T) (i := k) hk)
              have hstep0 : OneBitDiff (brgcPath (d + 1) (Fin.rev (k + 1))) (brgcPath (d + 1) (Fin.rev k)) := by
                simpa [hrevRel] using hrevStep
              have hstep1 : OneBitDiff (brgcPath (d + 1) (Fin.rev k)) (brgcPath (d + 1) (Fin.rev (k + 1))) :=
                OneBitDiff_symm hstep0
              have hstep' : OneBitDiff (right k) (right (k + 1)) :=
                oneBitDiff_snocBit_same true hstep1
              -- rewrite `append` on the right half via a successor-index evaluation
              have happK : Fin.append left right (Fin.natAdd T k) = right k := by
                simpa using (Fin.append_right (u := left) (v := right) (i := k))
              -- switch to the `addNat` presentation used by the simplifier in this file
              have hnextAdd : (k.addNat T : Fin (T + T)) + 1 = (k + 1).addNat T := by
                -- rewrite both `natAdd` endpoints into `addNat`
                simpa [natAdd_eq_addNat (T := T) (k := k), natAdd_eq_addNat (T := T) (k := (k + 1))] using hnext
              have happK' : Fin.append left right (k.addNat T) = right k := by
                have : Fin.append left right (Fin.natAdd T k) = right k := by
                  simpa using (Fin.append_right (u := left) (v := right) (i := k))
                simpa [natAdd_eq_addNat (T := T) (k := k)] using this
              have happNext : Fin.append left right (k.addNat T + 1) = right (k + 1) := by
                have : Fin.append left right (Fin.natAdd T (k + 1)) = right (k + 1) := by
                  simpa using (Fin.append_right (u := left) (v := right) (i := (k + 1)))
                have : Fin.append left right ((k + 1).addNat T) = right (k + 1) := by
                  simpa [natAdd_eq_addNat (T := T) (k := (k + 1))] using this
                simpa [hnextAdd.symm] using this
              have hstep0 : OneBitDiff (Fin.append left right (k.addNat T)) (right (k + 1)) := by
                simpa [happK'] using hstep'
              simpa [happNext.symm] using hstep0
            · -- boundary: last element of right half wraps back to the first element of left half
              have hkval : k.val = T - 1 := by
                have hle : k.val + 1 ≤ T := Nat.succ_le_of_lt k.isLt
                have hge : T ≤ k.val + 1 := Nat.le_of_not_gt hk
                have : k.val + 1 = T := Nat.le_antisymm hle hge
                exact Nat.eq_sub_of_add_eq this
              have hnext : (Fin.natAdd T k : Fin (T + T)) + 1 = Fin.castAdd T 0 := by
                apply Fin.ext
                -- last element in `Fin (T+T)` wraps to `0`
                have hT1 : 1 ≤ T := Nat.succ_le_of_lt hTpos
                have hsum : k.val + T + 1 = T + T := by
                  calc
                    k.val + T + 1 = (T - 1) + T + 1 := by simp [hkval]
                    _ = (T - 1) + 1 + T := by
                        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                    _ = T + T := by
                        simp [Nat.sub_add_cancel hT1, Nat.add_assoc]
                -- `((natAdd T k) + 1).val = ((k.val + T) + 1) % (T+T) = 0`
                -- (the RHS `castAdd T 0` has value 0)
                have : ((k.val + T + 1) % (T + T)) = 0 := by
                  simpa [hsum, Nat.mod_self]
                simpa [Fin.val_add] using this
              have hrev_last : Fin.rev k = (0 : Fin T) := by
                apply Fin.ext
                -- rev(last) has value 0
                have hT1 : 1 ≤ T := Nat.succ_le_of_lt hTpos
                have : (T - 1 + 1) = T := Nat.sub_add_cancel hT1
                simp [Fin.val_rev, hkval, this]
              have hstep' : OneBitDiff (right k) (left 0) := by
                -- last bit flips from `true` to `false`
                have hflip : OneBitDiff (snocBit (brgcPath (d + 1) 0) false) (snocBit (brgcPath (d + 1) 0) true) :=
                  oneBitDiff_snocBit_flip (p := brgcPath (d + 1) 0)
                have hflip' : OneBitDiff (snocBit (brgcPath (d + 1) 0) true) (snocBit (brgcPath (d + 1) 0) false) :=
                  OneBitDiff_symm hflip
                simpa [left, right, hrev_last] using hflip'
              -- rewrite `append` on the first index, and replace `left 0` with the successor-index append via `hnext`
              -- also rewrite the starting index to `addNat` to match the goal presentation
              have happK : Fin.append left right (k.addNat T) = right k := by
                have : Fin.append left right (Fin.natAdd T k) = right k := by
                  simpa using (Fin.append_right (u := left) (v := right) (i := k))
                simpa [natAdd_eq_addNat (T := T) (k := k)] using this
              have happNext : Fin.append left right ((Fin.natAdd T k : Fin (T + T)) + 1) = left 0 := by
                have : Fin.append left right (Fin.castAdd T (0 : Fin T)) = left 0 := by
                  simpa using (Fin.append_left (u := left) (v := right) (i := (0 : Fin T)))
                -- `(natAdd T k) + 1 = castAdd T 0`
                simpa [hnext.symm] using this
              have hstep0 : OneBitDiff (Fin.append left right (k.addNat T)) (left 0) := by
                simpa [happK] using hstep'
              -- replace `left 0` with the successor-index append
              simpa [happNext.symm] using hstep0

      -- lift back to the `Fin (2^(d+2))` index space
      simpa [brgcPath, T, hTT, left, right, i', hcast_succ] using hTTgoal

/-! ## Packaged GrayCycle/GrayCover -/

noncomputable def brgcGrayCycle (d : Nat) (hdpos : 0 < d) : GrayCycle d :=
{ path := brgcPath d
  inj := brgcPath_injective d
  oneBit_step := brgc_oneBit_step (d := d) hdpos
}

noncomputable def brgcGrayCover (d : Nat) (hdpos : 0 < d) : GrayCover d (2 ^ d) :=
{ path := brgcPath d
  complete := by
    classical
    have h_inj : Function.Injective (brgcPath d) := brgcPath_injective d
    have h_card : Fintype.card (Fin (2 ^ d)) = Fintype.card (Pattern d) := by
      simp [Patterns.card_pattern]
    have h_bij : Function.Bijective (brgcPath d) :=
      (Fintype.bijective_iff_injective_and_card (brgcPath d)).2 ⟨h_inj, h_card⟩
    exact h_bij.2
  oneBit_step := brgc_oneBit_step (d := d) hdpos
}

end GrayCycleBRGC

end Patterns
end IndisputableMonolith
