/-
# The exponent is an integer, and why the character was never rational

This module supplies the arithmetic core of the anchor-free gauge classification, and
corrects a structural mistake in how that classification has been attacked.

## The mistake

The program has been trying to prove that every inhabitant of the anchor-free cost
ledger factors through a character valued **in the carrier**, that is, a rational-valued
completely multiplicative function. That target is stronger than the mathematics
supports, which is why it has resisted and why its unrestricted form is refuted.

Solving the composition law by the d'Alembert route gives `F = J ∘ χ`, and the quantity
a cost actually exposes is the trace `χ(x) + χ(x)⁻¹`. A cost is carrier-valued exactly
when its **traces** are rational. It does not follow that `χ` is rational.
`no_rational_character_at_trace_three` makes the gap concrete: the trace equation with
value `3` has no rational solution at all, so a cost charging `1/2` at the ratio two is
perfectly carrier-valued while having no rational character behind it.

## What replaces it

Work with the trace. Writing `χ(n) = n^c`, carrier-valuedness says `n^c + n^(-c)` is
rational for every `n`, which is strictly weaker than `n^c` rational. The classification
then needs only that `c` is an odd positive integer, and the arithmetic of that is here:

* `rat_of_trace_rat_of_pow_rat`: a real above one with rational trace that has **some**
  rational power is itself rational. The proof writes `u^k = a + b·(u - u⁻¹)` with `a`
  and `b` positive rationals, so the irrational part can never cancel.
* `int_of_rat_exponent_of_trace_rat`: a positive rational exponent whose trace at base
  two is rational is an integer.

One input stays outside Lean and is named rather than hidden, since Mathlib does not carry
it: the six exponentials theorem, which rules out irrational exponents.
`exponent_is_positive_integer` packages the chain so that what is imported is visible in
the statement.

There used to be a second import, the Erdős power-function step for monotone completely
multiplicative functions. It is now a theorem, `Cost.MonotonePower.exists_exponent`, proved
by Howe's elementary argument, and the classification that consumes both
(`Cost.GaugeOrbitClassification.GaugeOrbitIsSignedPowerFamily_of_sixExponentials`) now runs
on the six exponentials input alone.
-/

import Mathlib

namespace IndisputableMonolith
namespace Cost
namespace TraceRationalExponent

/-! ## A rational trace need not come from a rational character -/

/-- No rational number squares to five. Proved by counting the five-adic valuation:
a square has even valuation and five has valuation one. -/
theorem no_rational_sqrt_five : ¬ ∃ s : ℚ, s ^ 2 = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rintro ⟨s, hs⟩
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have h1 : padicValRat 5 (s ^ 2) = (2 : ℕ) * padicValRat 5 s :=
    padicValRat.pow hs0
  have h2 : padicValRat 5 ((5 : ℕ) : ℚ) = 1 := padicValRat.self (by norm_num)
  rw [hs] at h1
  norm_num at h2
  rw [h2] at h1
  omega

/-- **The demand for a carrier-valued character is too strong.** The trace equation
`r + r⁻¹ = 3` has no rational solution. So a cost whose value at the ratio two is the
perfectly rational `1/2` has no rational character at that ratio, and asking the
factorization to produce one asks for something that does not exist. -/
theorem no_rational_character_at_trace_three : ¬ ∃ r : ℚ, r + r⁻¹ = 3 := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr
    norm_num at hr
  have hquad : r ^ 2 - 3 * r + 1 = 0 := by
    field_simp at hr
    linarith [hr]
  exact no_rational_sqrt_five ⟨2 * r - 3, by nlinarith [hquad]⟩

/-- The real witness behind the previous theorem, recorded so the object is on the page:
the square of the golden ratio has trace exactly three. -/
theorem golden_square_has_trace_three :
    ((3 + Real.sqrt 5) / 2) + ((3 + Real.sqrt 5) / 2)⁻¹ = 3 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hne : (3 + Real.sqrt 5) / 2 ≠ 0 := by positivity
  field_simp
  nlinarith [hsq, hnn]

/-! ## The arithmetic core

A real above one with a rational trace generates a quadratic object. If any power of it
lands back in the rationals, the irrational part has to cancel, and it cannot, because
its coefficient is a strictly positive rational at every step. -/

/-- Powers of `u` on the basis `{1, d}` with `d = u - u⁻¹`, both coordinates strictly
positive rationals. The positivity of the second coordinate is the whole point: it is
what forbids the irrational part from cancelling. -/
private theorem pow_eq_coords {u : ℝ} (hu : 1 < u) {t : ℚ}
    (ht : u + u⁻¹ = (t : ℝ)) :
    ∀ k : ℕ, 1 ≤ k → ∃ a b : ℚ, 0 < a ∧ 0 < b ∧
      u ^ k = (a : ℝ) + (b : ℝ) * (u - u⁻¹) := by
  have hupos : (0 : ℝ) < u := lt_trans zero_lt_one hu
  have hu0 : u ≠ 0 := ne_of_gt hupos
  have htgt : (2 : ℝ) < (t : ℝ) := by
    rw [← ht]
    have hsq : (0 : ℝ) < (u - 1) ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < (u - 1) ^ 2 / u := div_pos hsq hupos
    have hid : u + u⁻¹ - 2 = (u - 1) ^ 2 / u := by field_simp; ring
    linarith
  have htq : (2 : ℚ) < t := by exact_mod_cast htgt
  obtain ⟨d, hddef⟩ : ∃ d : ℝ, d = u - u⁻¹ := ⟨_, rfl⟩
  have hbase : u = (t : ℝ) / 2 + d / 2 := by
    rw [hddef, ← ht]; ring
  have hd2 : d ^ 2 = (t : ℝ) ^ 2 - 4 := by
    rw [hddef, ← ht]
    field_simp
    ring
  intro k hk
  rw [← hddef]
  induction k with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hk with h1 | h1
      · refine ⟨t / 2, 1 / 2, by linarith, by norm_num, ?_⟩
        have hn0 : n = 0 := by omega
        subst hn0
        rw [pow_one]
        push_cast
        linarith [hbase]
      · have hn : 1 ≤ n := by omega
        obtain ⟨a, b, ha, hb, hab⟩ := ih hn
        have h4 : (0 : ℚ) < t ^ 2 - 4 := by nlinarith
        refine ⟨a * (t / 2) + b * (1 / 2) * (t ^ 2 - 4),
                a * (1 / 2) + b * (t / 2), by positivity, by positivity, ?_⟩
        rw [pow_succ, hab]
        push_cast
        linear_combination ((a : ℝ) + (b : ℝ) * d) * hbase + ((b : ℝ) / 2) * hd2

/-- **A rational trace plus any rational power forces rationality.** If `u > 1` has a
rational trace and some positive power of `u` is rational, then `u` is rational.

This is what makes the trace formulation tractable: a genuinely quadratic unit can never
have a rational power. -/
theorem rat_of_trace_rat_of_pow_rat {u : ℝ} (hu : 1 < u) {t : ℚ}
    (ht : u + u⁻¹ = (t : ℝ)) {q : ℕ} (hq : 1 ≤ q) {A : ℚ}
    (hA : u ^ q = (A : ℝ)) :
    ∃ r : ℚ, u = (r : ℝ) := by
  obtain ⟨a, b, ha, hb, hab⟩ := pow_eq_coords hu ht q hq
  have hbne' : ((b : ℝ)) ≠ 0 := by
    simpa using (ne_of_gt hb : b ≠ 0)
  have hval : (A : ℝ) = (a : ℝ) + (b : ℝ) * (u - u⁻¹) := by rw [← hA, hab]
  have hd : u - u⁻¹ = ((A : ℝ) - (a : ℝ)) / (b : ℝ) := by
    rw [eq_div_iff hbne']
    linear_combination -hval
  refine ⟨(t + (A - a) / b) / 2, ?_⟩
  push_cast
  rw [← hd, ← ht]
  ring

/-! ## The exponent is an integer -/

/-- **A positive rational exponent with a rational trace is an integer.** If `c` is a
positive rational and `2^c + 2^(-c)` is rational, then `c` has denominator one.

Together with the six exponentials theorem, which rules out irrational `c`, this is the
whole exponent step of the gauge classification. Note what it never assumes: `2^c` is
not required to be rational, only its trace, which is exactly the weakening that
`no_rational_character_at_trace_three` shows to be necessary. -/
theorem int_of_rat_exponent_of_trace_rat {c : ℚ} (hc : 0 < c) {t : ℚ}
    (ht : (2 : ℝ) ^ (c : ℝ) + ((2 : ℝ) ^ (c : ℝ))⁻¹ = (t : ℝ)) :
    c.den = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu1 : 1 < (2 : ℝ) ^ (c : ℝ) := by
    have h0 : (2 : ℝ) ^ (0 : ℝ) < (2 : ℝ) ^ (c : ℝ) := by
      apply (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr
      exact_mod_cast hc
    rwa [Real.rpow_zero] at h0
  have hnum : 0 < c.num := Rat.num_pos.mpr hc
  have hpR : ((c.num.toNat : ℕ) : ℝ) = ((c.num : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg (le_of_lt hnum))
  have hcq : (c : ℝ) * ((c.den : ℕ) : ℝ) = ((c.num.toNat : ℕ) : ℝ) := by
    rw [hpR]
    exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) (Rat.mul_den_eq_num c)
  have hpow : ((2 : ℝ) ^ (c : ℝ)) ^ (c.den) = (((2 : ℚ) ^ (c.num.toNat) : ℚ) : ℝ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (c : ℝ)) c.den, ← Real.rpow_mul (by norm_num), hcq,
      Real.rpow_natCast]
    push_cast
    ring
  obtain ⟨r, hr⟩ := rat_of_trace_rat_of_pow_rat hu1 ht c.pos hpow
  have hrq : r ^ (c.den) = (2 : ℚ) ^ (c.num.toNat) := by
    have h : ((r ^ (c.den) : ℚ) : ℝ) = (((2 : ℚ) ^ (c.num.toNat) : ℚ) : ℝ) := by
      rw [← hpow, hr]; push_cast; ring
    exact_mod_cast h
  have hrne : r ≠ 0 := by
    intro h
    rw [h, zero_pow (by have := c.pos; omega : c.den ≠ 0)] at hrq
    have hp : (0 : ℚ) < (2 : ℚ) ^ (c.num.toNat) := by positivity
    rw [← hrq] at hp
    exact lt_irrefl _ hp
  have hv1 : padicValRat 2 (r ^ (c.den)) = (c.den : ℕ) * padicValRat 2 r :=
    padicValRat.pow hrne
  have hself : padicValRat 2 ((2 : ℚ)) = 1 := by
    have h := padicValRat.self (p := 2) (by norm_num)
    norm_num at h
    exact h
  have hv2 : padicValRat 2 ((2 : ℚ) ^ (c.num.toNat)) = (c.num.toNat : ℕ) * 1 := by
    rw [padicValRat.pow (by norm_num : (2 : ℚ) ≠ 0), hself]
  rw [hrq, hv2] at hv1
  have hdvd : c.den ∣ c.num.toNat := by
    have hz : ((c.den : ℕ) : ℤ) ∣ ((c.num.toNat : ℕ) : ℤ) :=
      ⟨padicValRat 2 r, by push_cast at hv1 ⊢; linarith⟩
    exact_mod_cast hz
  have hpabs : c.num.toNat = c.num.natAbs := by
    have h1 : ((c.num.toNat : ℕ) : ℤ) = c.num := Int.toNat_of_nonneg (le_of_lt hnum)
    have h2 : ((c.num.natAbs : ℕ) : ℤ) = c.num := Int.natAbs_of_nonneg (le_of_lt hnum)
    omega
  have hcop : Nat.gcd c.num.toNat c.den = 1 := by
    rw [hpabs]; exact c.reduced
  exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd dvd_rfl)

/-! ## The chain, with the imported inputs named

Neither the six exponentials theorem nor the Erdős power-function step is in Mathlib, so
they enter as explicit hypotheses. A reader can see precisely what is imported. -/

/-- The six exponentials input, in exactly the form the classification uses: if the trace
of `n^c` is rational at the three bases two, three and five, the exponent is rational.
This is a published corollary of the six exponentials theorem (Lang, Ramachandra) and is
stated as a hypothesis because the ambient library carries neither it nor
Gelfond--Schneider. -/
def SixExponentialsTraceInput : Prop :=
  ∀ c : ℝ, (∀ n : ℕ, 2 ≤ n → n ≤ 5 →
      ∃ t : ℚ, ((n : ℝ)) ^ c + (((n : ℝ)) ^ c)⁻¹ = (t : ℝ)) →
    ∃ r : ℚ, c = (r : ℝ)

/-- **The exponent is a positive integer.** Given the imported six exponentials input, a
positive real exponent whose traces at the small bases are rational is a positive integer.
It is not further restricted to the odd integers: both parities are inhabited, by
`Cost.GaugeOrbitFromRealCharacter.signedPowerNativeCost_sansAnchor`. This is the arithmetic
half of `GaugeOrbitIsSignedPowerFamily_of_sixExponentials`; the analytic half is Howe. -/
theorem exponent_is_positive_integer (hsix : SixExponentialsTraceInput)
    {c : ℝ} (hc : 0 < c)
    (htrace : ∀ n : ℕ, 2 ≤ n → n ≤ 5 →
      ∃ t : ℚ, ((n : ℝ)) ^ c + (((n : ℝ)) ^ c)⁻¹ = (t : ℝ)) :
    ∃ k : ℕ, 1 ≤ k ∧ c = (k : ℝ) := by
  obtain ⟨r, hr⟩ := hsix c htrace
  have hrpos : 0 < r := by
    have h : (0 : ℝ) < (r : ℝ) := hr ▸ hc
    exact_mod_cast h
  obtain ⟨t, ht⟩ := htrace 2 (by norm_num) (by norm_num)
  have ht' : (2 : ℝ) ^ ((r : ℚ) : ℝ) + ((2 : ℝ) ^ ((r : ℚ) : ℝ))⁻¹ = (t : ℝ) := by
    rw [← hr]
    norm_num at ht ⊢
    exact ht
  have hden : r.den = 1 := int_of_rat_exponent_of_trace_rat hrpos ht'
  have hnum : 0 < r.num := Rat.num_pos.mpr hrpos
  refine ⟨r.num.toNat, by omega, ?_⟩
  have hrn : ((r.num : ℤ) : ℚ) = r := by
    conv_rhs => rw [← Rat.num_div_den r]
    rw [hden]
    norm_num
  have hfin : ((r.num.toNat : ℕ) : ℚ) = r := by
    rw [show ((r.num.toNat : ℕ) : ℚ) = ((r.num.toNat : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_of_nonneg (le_of_lt hnum)]
    exact hrn
  rw [hr]
  exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) hfin.symm

/-! ### Axiom audit -/

#print axioms no_rational_character_at_trace_three
#print axioms rat_of_trace_rat_of_pow_rat
#print axioms int_of_rat_exponent_of_trace_rat
#print axioms exponent_is_positive_integer

end TraceRationalExponent
end Cost
end IndisputableMonolith
