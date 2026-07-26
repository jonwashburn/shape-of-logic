/-
# The anchor-free gauge classification, on one named import

`GaugeOrbitIsSignedPowerFamily` said: every inhabitant of the anchor-free structural cost
ledger is either the sign cost or the sign-extended power cost of some nonnegative integer
exponent, and nothing else. It was OPEN, resting on two unformalized imports plus prose
glue. This module proves it, conditional on ONE hypothesis, the six exponentials input
already named in `Cost.TraceRationalExponent`.

What changed is that the second import is gone. Erdős's theorem, that a monotone completely
multiplicative function on the positive integers is a power, is now proved from nothing in
`Cost.MonotoneMultiplicativePower` by Howe's argument, so it enters as a theorem and not as
a hypothesis.

The chain, in the order the file builds it:

1. Above one the trace order and the value order agree (`le_of_trace_le`), so the ledger's
   monotonicity of costs on positive integer orbits becomes monotonicity of the extracted
   character. That plus complete multiplicativity is exactly Howe's hypothesis pack.
2. Howe gives `χ(n) = n^c` for one real `c ≥ 0`, and the nondegenerate branch forces
   `c > 0` because `χ(2)` is the anchor root, which exceeds one.
3. The traces of the cost are displays of carrier elements, hence rational, so the six
   exponentials input applies and `c` is a positive integer `k`
   (`exponent_is_positive_integer`).
4. Multiplicativity carries `χ` from the integers to every positive rational, orientation
   reversal carries it across zero, and the cost is `J ∘ χ` throughout, which is the
   sign-extended power cost of exponent `k`.

The degenerate branch, where the trace at two is exactly two, is the sign cost, and it is
handled first because the extraction that produces `χ` divides by `r² - 1`.

Nothing here is conditional on the ledger being nonempty or on the exponent being odd. Both
parities occur; that was settled in `GaugeOrbitFromRealCharacter` by construction.
-/

import IndisputableMonolith.Cost.GaugeOrbitFromRealCharacter
import IndisputableMonolith.Cost.MonotoneMultiplicativePower

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace PRCJCost

open IndisputableMonolith.Cost.RealCharacterFactorization
  (SansAnchorHypotheses traceDisplay rationalTrace rationalTrace_eq_traceDisplay
    rationalTrace_pos_eq_two_of_two_eq_two nontrivialCharacterValue
    nontrivialCharacterValue_one nontrivialCharacterValue_mul
    nontrivialCharacterValue_recip nontrivialCharacterValue_trace
    nontrivialCharacterValue_two nontrivialCharacterValue_principal_on_nat
    nontrivialCharacterValue_nat_trace_mono anchorRoot anchorRoot_gt_one)

open IndisputableMonolith.Cost.MonotonePower (MonotoneMultiplicative exists_exponent)

open IndisputableMonolith.Cost.TraceRationalExponent
  (SixExponentialsTraceInput exponent_is_positive_integer)

/-! ## The trace order is the value order, above one -/

/-- `v ↦ v + v⁻¹` is strictly increasing on `[1,∞)`, so an inequality between traces of
principal values is an inequality between the values. This is what turns the ledger's
monotonicity condition, which constrains costs, into monotonicity of the character. -/
private theorem le_of_trace_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a + a⁻¹ ≤ b + b⁻¹) : a ≤ b := by
  by_contra hcon
  push_neg at hcon
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have hkey : (a + a⁻¹) - (b + b⁻¹) = (a - b) * (a * b - 1) / (a * b) := by
    field_simp
    ring
  have h1 : (0 : ℝ) < a - b := by linarith
  have h2 : (0 : ℝ) < a * b - 1 := by nlinarith [mul_le_mul_of_nonneg_left hb ha0.le]
  have hpos : 0 < (a - b) * (a * b - 1) / (a * b) :=
    div_pos (mul_pos h1 h2) (mul_pos ha0 hb0)
  rw [← hkey] at hpos
  linarith

/-! ## Reading the cost off the trace -/

variable {F : RatioOrbit → RatioOrbit}

/-- The cost display is the trace display, halved and shifted. -/
private theorem cost_display (hS : SansAnchorHypotheses F) (q : RatioOrbit) :
    ((F q).toRat : ℝ) = rationalTrace F q.toRat / 2 - 1 := by
  rw [rationalTrace_eq_traceDisplay hS q]
  simp only [traceDisplay, nativeCostDoubledTrace, doubledTraceValue,
    RatioOrbit.mul_toRat, RatioOrbit.add_toRat, two_toRat, RatioOrbit.one_toRat]
  push_cast
  ring

/-- At a zero display orientation reversal alone pins the cost, with no character and no
appeal to the zero calibration field. -/
private theorem cost_at_zero (hS : SansAnchorHypotheses F) {q : RatioOrbit}
    (hq : q.toRat = 0) : (F q).toRat = -1 := by
  have h := hS.sign_reversing q q (by rw [hq]; norm_num)
  linarith

/-- Negative displays are determined by the positive ones. -/
private theorem cost_at_neg (hS : SansAnchorHypotheses F) (q : RatioOrbit) :
    (F q).toRat = -(F (ratioOrbitOfRat (-q.toRat))).toRat - 2 :=
  hS.sign_reversing (ratioOrbitOfRat (-q.toRat)) q
    (by rw [ratioOrbitOfRat_toRat]; ring)

/-! ## The degenerate branch is the sign cost -/

/-- **The degenerate anchor is exactly the sign cost.** If the trace at two is two then the
trace is two at every positive display, the cost vanishes there, and orientation reversal
fills in the rest. -/
theorem degenerate_is_signGauge (hS : SansAnchorHypotheses F)
    (htwo : rationalTrace F 2 = 2) (q : RatioOrbit) :
    RatioOrbit.crossEq (F q) (signGaugeNativeCost q) := by
  refine dispCross ?_
  rw [signGaugeNativeCost_toRat]
  rcases lt_trichotomy q.toRat 0 with hneg | hzero | hpos
  · have hpospart : (0 : ℚ) < -q.toRat := by linarith
    have hp : (F (ratioOrbitOfRat (-q.toRat))).toRat = 0 := by
      have h := cost_display hS (ratioOrbitOfRat (-q.toRat))
      rw [ratioOrbitOfRat_toRat,
        rationalTrace_pos_eq_two_of_two_eq_two hS htwo hpospart] at h
      norm_num at h
      exact_mod_cast h
    rw [cost_at_neg hS q, hp, signGaugeCostDisplay, if_neg (not_lt.mpr hneg.le),
      if_neg (ne_of_lt hneg)]
    norm_num
  · rw [cost_at_zero hS hzero, signGaugeCostDisplay,
      if_neg (by rw [hzero]; exact lt_irrefl 0), if_pos hzero]
  · have h := cost_display hS q
    rw [rationalTrace_pos_eq_two_of_two_eq_two hS htwo hpos] at h
    norm_num at h
    rw [signGaugeCostDisplay, if_pos hpos]
    exact_mod_cast h

/-! ## The nondegenerate branch: Howe, then six exponentials -/

/-- The extracted character, restricted to the positive integers, satisfies exactly the
hypotheses of Erdős's theorem. Complete multiplicativity is the extraction's own
multiplicativity; monotonicity is the ledger's, read through `le_of_trace_le`. -/
private theorem natChar_monotoneMultiplicative (hS : SansAnchorHypotheses F)
    (hnt : rationalTrace F 2 ≠ 2) :
    MonotoneMultiplicative (fun n : ℕ => nontrivialCharacterValue F (n : ℚ)) where
  unit := by simpa using nontrivialCharacterValue_one hS hnt
  mul := by
    intro m n hm hn
    have hmq : ((m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hnq : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simpa using nontrivialCharacterValue_mul hS hnt hmq hnq
  mono := by
    intro m n hm hmn
    exact le_of_trace_le (nontrivialCharacterValue_principal_on_nat hS hnt m hm)
      (nontrivialCharacterValue_principal_on_nat hS hnt n (le_trans hm hmn))
      (nontrivialCharacterValue_nat_trace_mono hS hnt hm hmn)

/-- **The exponent is a positive integer.** Howe supplies the real exponent, the anchor root
makes it positive, and the six exponentials input makes it an integer. This is the only
place the import is used. -/
theorem exists_nat_exponent (hsix : SixExponentialsTraceInput)
    (hS : SansAnchorHypotheses F) (hnt : rationalTrace F 2 ≠ 2) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ n : ℕ, 1 ≤ n →
      nontrivialCharacterValue F (n : ℚ) = ((n : ℝ)) ^ k := by
  obtain ⟨c, _, hc⟩ := exists_exponent (natChar_monotoneMultiplicative hS hnt)
  have h2 : nontrivialCharacterValue F ((2 : ℕ) : ℚ) = anchorRoot F := by
    simpa using nontrivialCharacterValue_two hS hnt
  have hroot : 1 < anchorRoot F := anchorRoot_gt_one hS hnt
  have hc2 : (((2 : ℕ) : ℝ)) ^ c = anchorRoot F := by
    rw [← hc 2 (by norm_num), h2]
  have hcpos : 0 < c := by
    by_contra hle
    push_neg at hle
    have hmono : (((2 : ℕ) : ℝ)) ^ c ≤ (((2 : ℕ) : ℝ)) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
    rw [Real.rpow_zero, hc2] at hmono
    linarith
  have htrace : ∀ n : ℕ, 2 ≤ n → n ≤ 5 →
      ∃ t : ℚ, ((n : ℝ)) ^ c + (((n : ℝ)) ^ c)⁻¹ = (t : ℝ) := by
    intro n hn _
    have hnq : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    refine ⟨(nativeCostDoubledTrace F (ratioOrbitOfRat ((n : ℕ) : ℚ))).toRat, ?_⟩
    rw [← hc n (by omega), nontrivialCharacterValue_trace hS hnt hnq]
    rfl
  obtain ⟨k, hk1, hck⟩ := exponent_is_positive_integer hsix hcpos htrace
  refine ⟨k, hk1, fun n hn => ?_⟩
  rw [hc n hn, hck]
  exact Real.rpow_natCast _ _

/-- Multiplicativity carries the power law from the integers to every positive rational. -/
theorem char_at_pos (hS : SansAnchorHypotheses F) (hnt : rationalTrace F 2 ≠ 2)
    {k : ℕ} (hk : ∀ n : ℕ, 1 ≤ n → nontrivialCharacterValue F (n : ℚ) = ((n : ℝ)) ^ k)
    {x : ℚ} (hx : 0 < x) :
    nontrivialCharacterValue F x = ((x ^ k : ℚ) : ℝ) := by
  have hnumpos : 0 < x.num := Rat.num_pos.mpr hx
  have hapos : 0 < x.num.toNat := by omega
  have hbpos : 0 < x.den := x.pos
  have haa : ((x.num.toNat : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hapos.ne'
  have hbb : ((x.den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hbpos.ne'
  have hxrep : ((x.num.toNat : ℕ) : ℚ) / ((x.den : ℕ) : ℚ) = x := by
    have hnum : ((x.num.toNat : ℕ) : ℚ) = ((x.num : ℤ) : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (le_of_lt hnumpos)
    rw [hnum]
    exact Rat.num_div_den x
  have hmul := nontrivialCharacterValue_mul hS hnt haa (inv_ne_zero hbb)
  rw [← div_eq_mul_inv, hxrep, nontrivialCharacterValue_recip hS hnt hbb,
    hk _ hapos, hk _ hbpos] at hmul
  have hqk : x ^ k = ((x.num.toNat : ℕ) : ℚ) ^ k / ((x.den : ℕ) : ℚ) ^ k := by
    conv_lhs => rw [← hxrep]
    rw [div_pow]
  rw [hmul, hqk]
  push_cast
  ring

/-- On a positive display the cost is `J` of the `k`-th power. -/
theorem cost_at_pos (hS : SansAnchorHypotheses F) (hnt : rationalTrace F 2 ≠ 2)
    {k : ℕ} (hk : ∀ n : ℕ, 1 ≤ n → nontrivialCharacterValue F (n : ℚ) = ((n : ℝ)) ^ k)
    {q : RatioOrbit} (hq : 0 < q.toRat) :
    (F q).toRat = jq (q.toRat ^ k) := by
  have hv := char_at_pos hS hnt hk hq
  have hd := cost_display hS q
  have htr := nontrivialCharacterValue_trace hS hnt (ne_of_gt hq)
  have hcast : ((F q).toRat : ℝ) = ((jq (q.toRat ^ k) : ℚ) : ℝ) := by
    rw [hd, ← htr, hv]
    push_cast [jq]
    ring
  exact_mod_cast hcast

/-- **The nondegenerate branch is a sign-extended power cost.** -/
theorem nontrivial_is_signedPower (hS : SansAnchorHypotheses F)
    (hnt : rationalTrace F 2 ≠ 2) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ n : ℕ, 1 ≤ n → nontrivialCharacterValue F (n : ℚ) = ((n : ℝ)) ^ k) :
    ∀ q : RatioOrbit, RatioOrbit.crossEq (F q) (signedPowerNativeCost (k - 1) q) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  intro q
  refine dispCross ?_
  rw [signedPowerNativeCost_toRat]
  simp only [Nat.add_sub_cancel]
  rcases lt_trichotomy q.toRat 0 with hneg | hzero | hpos
  · have hpospart : (0 : ℚ) < -q.toRat := by linarith
    have hp : (F (ratioOrbitOfRat (-q.toRat))).toRat = jq ((-q.toRat) ^ (m + 1)) := by
      have h := cost_at_pos hS hnt hk (q := ratioOrbitOfRat (-q.toRat))
        (by rw [ratioOrbitOfRat_toRat]; exact hpospart)
      rwa [ratioOrbitOfRat_toRat] at h
    rw [cost_at_neg hS q, hp, signedPow, abs_of_neg hneg,
      show q.toRat * (-q.toRat) ^ m = -((-q.toRat) ^ (m + 1)) by ring, jq_neg]
  · rw [cost_at_zero hS hzero, hzero, signedPow_zero_arg]
    norm_num [jq]
  · rw [cost_at_pos hS hnt hk hpos, signedPow, abs_of_pos hpos]
    congr 1
    ring

/-! ## The classification -/

/-- **The anchor-free gauge classification, on one named import.** Every inhabitant of the
anchor-free structural cost ledger is the sign cost or the sign-extended power cost of a
nonnegative integer exponent. The only hypothesis is the six exponentials input; the Erdős
step is now the theorem `Cost.MonotonePower.exists_exponent`.

Two things this does NOT say. It does not say the exponent is odd: both parities are
inhabited, by construction in `GaugeOrbitFromRealCharacter`. And it does not select `J`:
selection is leastness, which lives in `Cost.UnitFromMinimality`. -/
theorem GaugeOrbitIsSignedPowerFamily_of_sixExponentials
    (hsix : SixExponentialsTraceInput) : GaugeOrbitIsSignedPowerFamily := by
  intro G hG
  have hS := realCharacterFactorizationHypotheses_of_structural hG
  by_cases htwo : rationalTrace G 2 = 2
  · exact Or.inl (degenerate_is_signGauge hS htwo)
  · obtain ⟨k, hk1, hk⟩ := exists_nat_exponent hsix hS htwo
    exact Or.inr ⟨k - 1, nontrivial_is_signedPower hS htwo hk1 hk⟩

/-! ### Axiom audit -/

#print axioms degenerate_is_signGauge
#print axioms exists_nat_exponent
#print axioms nontrivial_is_signedPower
#print axioms GaugeOrbitIsSignedPowerFamily_of_sixExponentials

end PRCJCost
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
