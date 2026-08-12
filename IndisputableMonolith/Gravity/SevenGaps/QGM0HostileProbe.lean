import IndisputableMonolith.Gravity.SevenGaps.Gap2M0Asymptotics
import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusProductForm

/-!
# Hostile probe: Gap2M0Asymptotics (A45 / C11 M0 saddle campaign)

Outside-module axiom audits and load-bearing identity checks. Does not import
`FullTheoryLedger` (concurrent flip worker). No edits to the campaign module.
-/

namespace QGM0HostileProbe

open Gap2M0Asymptotics Gap2CensusProductForm

/-! ## Outside-module axiom audits (report claims base triple) -/

#print axioms Gap2M0Asymptotics.sum_choose_sq_weighted
#print axioms Gap2M0Asymptotics.loopSqSum_eq
#print axioms Gap2M0Asymptotics.properSqSum_eq
#print axioms Gap2M0Asymptotics.conditional_loop_sq_mean
#print axioms Gap2M0Asymptotics.conditional_proper_sq_mean
#print axioms Gap2M0Asymptotics.loopSqSum_le_properSqSum
#print axioms Gap2M0Asymptotics.wrow_le_exp
#print axioms Gap2M0Asymptotics.wrow_le_two_wterm
#print axioms Gap2M0Asymptotics.factorial_upper
#print axioms Gap2M0Asymptotics.factorial_lower
#print axioms Gap2M0Asymptotics.m0_lower
#print axioms Gap2M0Asymptotics.smallMass_le

/-! ## Identity checks against the census module -/

theorem conditional_loop_uses_margin (n k : Nat) :
    (∑ j ∈ Finset.range (k + 1), cellCount n k j) = n ^ (2 * k) :=
  margin_count n k

theorem conditional_loop_matches_binomial (n k : Nat) (hn : n ≠ 0) :
    (loopSqSum n k : Real) / (n : Real) ^ (2 * k)
      = (k / (n : Real)) ^ 2 + (k / (n : Real)) * (1 - 1 / (n : Real)) :=
  conditional_loop_sq_mean n k hn

theorem conditional_proper_matches_binomial (n k : Nat) (hn : n ≠ 0) :
    (properSqSum n k : Real) / (n : Real) ^ (2 * k)
      = ((k : Real) * (1 - 1 / (n : Real))) ^ 2
        + (k / (n : Real)) * (1 - 1 / (n : Real)) :=
  conditional_proper_sq_mean n k hn

theorem proper_vanishes_at_n_one (k : Nat) : properSqSum 1 k = 0 := by
  rw [properSqSum_eq]
  simp

theorem mechanism_ratio_bound (n k : Nat) (hn : 2 ≤ n) :
    (loopSqSum n k : Real) * ((n : Real) - 1) ≤ (properSqSum n k : Real) :=
  loopSqSum_le_properSqSum n k hn

theorem mechanism_sharp_at_k_one (n : Nat) (hn : 2 ≤ n) :
    (loopSqSum n 1 : Real) * ((n : Real) - 1) = (properSqSum n 1 : Real) := by
  have hL : loopSqSum n 1 = n := by rw [loopSqSum_eq]; simp
  have hP : properSqSum n 1 = n ^ 2 - n := by rw [properSqSum_eq]; simp
  have hn2 : n ≤ n ^ 2 :=
    le_self_pow (by omega : (1 : Nat) ≤ n) (by decide : (2 : Nat) ≠ 0)
  rw [hL, hP]
  push_cast [Nat.cast_sub hn2]
  ring

theorem wrow_zero_pos (c : Nat) : (0 : Real) < wrow c 0 :=
  wrow_pos c 0

theorem loopSqSum_zero_left_statement (k : Nat) : loopSqSum 0 k = 0 :=
  loopSqSum_zero_left k

#print axioms conditional_loop_uses_margin
#print axioms conditional_loop_matches_binomial
#print axioms proper_vanishes_at_n_one
#print axioms mechanism_ratio_bound
#print axioms mechanism_sharp_at_k_one

end QGM0HostileProbe
