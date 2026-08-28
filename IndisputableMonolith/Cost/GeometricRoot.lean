import Mathlib
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Foundation.PhiForcingDerived

/-!
# Geometric Root of the J-Cost Law

Origin: the 2026-07-30 naming panel's judge named one headline live bet with
the power to reopen the naming slate: *if the discrete ledger and the golden
ratio fall out of the chaining inequality rather than out of minimality, then
every candidate name names a corollary.* Jon's instruction the same day: prove
it. This module is the proof attempt on the mechanical legs of that bet.

## What is proved here (THEOREM, kernel-checked, axioms printed below)

1. **The identity is exact.** `Jcost x = cosh (log x) - 1 = (x-1)^2/(2x)`.
   The cosh form is banked (`Cost.FunctionalEquation.Jcost_G_eq_cosh_sub_one`);
   the chordal form `(x-1)^2/(2x)` is the hyperbolic-distance reading
   (on the imaginary geodesic, `cosh d - 1 = |z-w|^2/(2 Im z Im w)`).
2. **The chaining inequality is an exact identity with positive excess.**
   `J(e^{a+b}) = J(e^a) + J(e^b) + J(e^a)·J(e^b) + sinh a·sinh b`.
   For same-sign `a, b` the excess is nonnegative (superadditivity) and
   strictly positive when both are nonzero. Chaining two distinctions always
   costs strictly more than the sum of its parts.
3. **Subdivision trivializes, so the tick is forced.**
   `n · J(e^{ε/n}) → 0`: splitting a fixed distinction into arbitrarily fine
   micro-steps makes its total J-cost arbitrarily small. A ledger that is
   infinitely refinable cannot sustain a positive cost floor for any chain;
   contrapositively, a ledger with an irreducible cost floor `c > 0` is forced
   to forbid refinement past `n ≤ ε²·cosh ε/(2c)`. Ledger discreteness as a
   regularizer, not an assumption.
4. **Assembly.** Tick (3) + closure on the ladder (banked,
   `PhiForcingDerived.closed_ratio_is_phi`) gives `r = φ`.

## What is NOT proved here (honest status)

The closure hypothesis in leg 4 is still assumed (`GeometricScaleSequence.isClosed`),
exactly as in `PhiForcingDerived`. Deriving the closure condition itself
(`levels 2 = levels 1 + levels 0`) from the superadditivity excess of leg 2,
rather than assuming a geometric ladder, is the remaining research leg. The
ledger falsifier for it stands (`C-im-phi-forced`): a derivation of the closure
condition from the recognition kernel without assuming a geometric ladder would
promote T6 from conditional to forced and fire the panel's reversal condition.
-/

namespace IndisputableMonolith
namespace Cost
namespace GeometricRoot

open Real Filter Topology

/-! ## Leg 0: the identity is exact (banked + chordal corollary) -/

/-- In the additive coordinate `x = e^t`, `J = cosh t - 1` exactly.
This is the banked theorem restated through `log`. -/
theorem jcost_eq_cosh_log_sub_one {x : ℝ} (hx : 0 < x) :
    Jcost x = Real.cosh (Real.log x) - 1 := by
  have h := FunctionalEquation.Jcost_G_eq_cosh_sub_one (Real.log x)
  simpa [FunctionalEquation.G, Real.exp_log hx] using h

/-- The chordal form: `J(x) = (x-1)^2/(2x)`. On the upper half-plane this is
`cosh d(i, ix) - 1` with `d` the hyperbolic distance, via
`cosh d(z,w) - 1 = |z-w|^2/(2 Im z Im w)`. The geometric reading is the
docstring; the arithmetic content is this identity. -/
theorem jcost_eq_chordal {x : ℝ} (hx : 0 < x) :
    Jcost x = (x - 1) ^ 2 / (2 * x) := by
  unfold Jcost
  field_simp [hx.ne']
  ring

/-! ## Hyperbolic trigonometry infrastructure -/

/-- Difference identity: `cosh y - cosh x = 2 sinh((y+x)/2) sinh((y-x)/2)`. -/
theorem cosh_sub_cosh (x y : ℝ) :
    Real.cosh y - Real.cosh x
      = 2 * Real.sinh ((y + x) / 2) * Real.sinh ((y - x) / 2) := by
  have hcore : ∀ A B : ℝ,
      Real.cosh (A + B) - Real.cosh (A - B) = 2 * Real.sinh A * Real.sinh B := by
    intro A B
    have hsub : Real.cosh (A - B)
        = Real.cosh A * Real.cosh B - Real.sinh A * Real.sinh B := by
      have h := Real.cosh_add A (-B)
      rw [Real.cosh_neg, Real.sinh_neg] at h
      rw [sub_eq_add_neg]
      linarith [h]
    rw [Real.cosh_add, hsub]
    ring
  have h := hcore ((y + x) / 2) ((y - x) / 2)
  have hy : (y + x) / 2 + (y - x) / 2 = y := by ring
  have hx : (y + x) / 2 - (y - x) / 2 = x := by ring
  rwa [hy, hx] at h

/-- Half-angle: `cosh t - 1 = 2 sinh²(t/2)`. -/
theorem cosh_sub_one_eq_two_sinh_sq_half (t : ℝ) :
    Real.cosh t - 1 = 2 * Real.sinh (t / 2) ^ 2 := by
  have h := cosh_sub_cosh 0 t
  rw [Real.cosh_zero, add_zero, sub_zero] at h
  rw [h]
  ring

/-- Double-angle: `cosh(2t) = 2 cosh²t - 1`. -/
theorem cosh_two_mul' (t : ℝ) : Real.cosh (2 * t) = 2 * Real.cosh t ^ 2 - 1 := by
  rw [show (2 : ℝ) * t = t + t from by ring, Real.cosh_add]
  have h2 : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq t
  have h3 : Real.sinh t ^ 2 = Real.cosh t ^ 2 - 1 := by linarith
  nlinarith [h3]

/-- `sinh` is nonnegative on nonnegative arguments (elementary, from `exp`). -/
theorem sinh_nonneg_of_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.sinh t := by
  rcases ht.eq_or_lt with h | h
  · rw [← h]
    simp [Real.sinh_zero]
  · rw [Real.sinh_eq]
    have h1 : 1 < Real.exp t := Real.one_lt_exp_iff.mpr h
    have h2 : Real.exp (-t) ≤ 1 := by
      rw [Real.exp_neg]
      exact inv_le_one_of_one_le₀ (le_of_lt h1)
    linarith [Real.exp_pos t, Real.exp_pos (-t)]

/-- `sinh` is positive on positive arguments. -/
theorem sinh_pos_of_pos {t : ℝ} (ht : 0 < t) : 0 < Real.sinh t := by
  rw [Real.sinh_eq]
  have h1 : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have h2 : Real.exp (-t) < 1 := by
    rw [Real.exp_neg]
    exact inv_lt_one_of_one_lt₀ h1
  linarith [Real.exp_pos t, Real.exp_pos (-t)]

/-- `cosh` is monotone on `[0, ∞)`. -/
theorem cosh_mono_on_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.cosh x ≤ Real.cosh y := by
  have h := cosh_sub_cosh x y
  have hA : 0 ≤ Real.sinh ((y + x) / 2) := sinh_nonneg_of_nonneg (by linarith)
  have hB : 0 ≤ Real.sinh ((y - x) / 2) := sinh_nonneg_of_nonneg (by linarith)
  have hnn : 0 ≤ 2 * Real.sinh ((y + x) / 2) * Real.sinh ((y - x) / 2) := by
    positivity
  linarith

/-- The mean-value bound: `sinh u ≤ u·cosh u` for `u > 0`. -/
theorem sinh_le_mul_cosh {u : ℝ} (hu : 0 < u) : Real.sinh u ≤ u * Real.cosh u := by
  obtain ⟨ξ, hξ, hderiv⟩ := exists_deriv_eq_slope Real.sinh hu
    Real.continuous_sinh.continuousOn Real.differentiable_sinh.differentiableOn
  simp only [Real.deriv_sinh, Real.sinh_zero, sub_zero] at hderiv
  have hξ0 : 0 ≤ ξ := le_of_lt hξ.1
  have hξu : ξ ≤ u := le_of_lt hξ.2
  have hcosh := cosh_mono_on_nonneg hξ0 hξu
  have hu' : u ≠ 0 := ne_of_gt hu
  have hs : Real.sinh u = u * Real.cosh ξ := by
    rw [eq_div_iff hu'] at hderiv
    rw [← hderiv]
    ring
  rw [hs]
  exact mul_le_mul_of_nonneg_left hcosh (le_of_lt hu)

/-- Absolute form: `|sinh u| ≤ |u|·cosh u` for all `u`. -/
theorem abs_sinh_le_abs_mul_cosh (u : ℝ) : |Real.sinh u| ≤ |u| * Real.cosh u := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg (sinh_nonneg_of_nonneg hu), abs_of_nonneg hu]
    rcases eq_or_lt_of_le hu with rfl | h
    · simp
    · exact sinh_le_mul_cosh h
  · have hsinh : Real.sinh u < 0 := by
      have h := sinh_pos_of_pos (neg_pos.mpr hu)
      rw [Real.sinh_neg] at h
      linarith
    rw [abs_of_neg hsinh, abs_of_neg hu]
    have hb := sinh_le_mul_cosh (neg_pos.mpr hu)
    rw [Real.sinh_neg, Real.cosh_neg] at hb
    exact hb

/-- `cosh²(t/2) ≤ cosh t`, from the double-angle identity and `cosh ≥ 1`. -/
theorem cosh_sq_half_le (t : ℝ) : Real.cosh (t / 2) ^ 2 ≤ Real.cosh t := by
  have hdouble : Real.cosh t = 2 * Real.cosh (t / 2) ^ 2 - 1 := by
    have h := cosh_two_mul' (t / 2)
    rwa [show (2 : ℝ) * (t / 2) = t from by ring] at h
  have hc : 1 ≤ Real.cosh t := Real.one_le_cosh t
  nlinarith [hdouble, hc, sq_nonneg (Real.cosh (t / 2))]

/-- The global quadratic bound: `cosh t - 1 ≤ (t²/2)·cosh t`. This is the
entire analytic content of the subdivision-triviality theorem. -/
theorem cosh_sub_one_le (t : ℝ) :
    Real.cosh t - 1 ≤ t ^ 2 / 2 * Real.cosh t := by
  rw [cosh_sub_one_eq_two_sinh_sq_half]
  have habs := abs_sinh_le_abs_mul_cosh (t / 2)
  have hsq : Real.sinh (t / 2) ^ 2 ≤ (|t / 2| * Real.cosh (t / 2)) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rwa [sq_abs] at h
  have hc2 := cosh_sq_half_le t
  calc 2 * Real.sinh (t / 2) ^ 2
      ≤ 2 * (|t / 2| * Real.cosh (t / 2)) ^ 2 := by linarith [hsq]
    _ = t ^ 2 / 2 * Real.cosh (t / 2) ^ 2 := by
        rw [mul_pow, sq_abs]
        ring
    _ ≤ t ^ 2 / 2 * Real.cosh t := by
        apply mul_le_mul_of_nonneg_left hc2
        positivity

/-! ## Leg 1: the chaining inequality is an exact identity -/

/-- **The chaining identity.** The cost of a chained distinction exceeds the
sum of its parts by an exactly computable excess:
`J(e^{a+b}) = J(e^a) + J(e^b) + J(e^a)·J(e^b) + sinh a·sinh b`. -/
theorem jcost_chain_excess_identity (a b : ℝ) :
    Jcost (Real.exp (a + b))
      = Jcost (Real.exp a) + Jcost (Real.exp b)
        + Jcost (Real.exp a) * Jcost (Real.exp b) + Real.sinh a * Real.sinh b := by
  have h1 : Jcost (Real.exp (a + b)) = Real.cosh (a + b) - 1 := by
    have h := FunctionalEquation.Jcost_G_eq_cosh_sub_one (a + b)
    simpa [FunctionalEquation.G] using h
  have h2 : Jcost (Real.exp a) = Real.cosh a - 1 := by
    have h := FunctionalEquation.Jcost_G_eq_cosh_sub_one a
    simpa [FunctionalEquation.G] using h
  have h3 : Jcost (Real.exp b) = Real.cosh b - 1 := by
    have h := FunctionalEquation.Jcost_G_eq_cosh_sub_one b
    simpa [FunctionalEquation.G] using h
  rw [h1, h2, h3, Real.cosh_add]
  ring

/-- `J ≥ 0` on the positive reals, in exponential coordinates. -/
theorem jcost_exp_nonneg (a : ℝ) : 0 ≤ Jcost (Real.exp a) := by
  have ht : Jcost (Real.exp a) = Real.cosh a - 1 := by
    have h := FunctionalEquation.Jcost_G_eq_cosh_sub_one a
    simpa [FunctionalEquation.G] using h
  rw [ht]
  exact sub_nonneg.mpr (Real.one_le_cosh a)

/-- `J > 0` away from the identity distinction, in exponential coordinates. -/
theorem jcost_exp_pos {a : ℝ} (ha : a ≠ 0) : 0 < Jcost (Real.exp a) := by
  have ht : Jcost (Real.exp a) = Real.cosh a - 1 := by
    have h := FunctionalEquation.Jcost_G_eq_cosh_sub_one a
    simpa [FunctionalEquation.G] using h
  rw [ht, cosh_sub_one_eq_two_sinh_sq_half]
  have hne : Real.sinh (a / 2) ≠ 0 := by
    intro hz
    rw [Real.sinh_eq] at hz
    have h2 : Real.exp (a / 2) - Real.exp (-(a / 2)) = 0 := by linarith [hz]
    have he : Real.exp (a / 2) = Real.exp (-(a / 2)) := sub_eq_zero.mp h2
    have hinj := Real.exp_injective he
    apply ha
    linarith [hinj]
  exact mul_pos two_pos (sq_pos_of_ne_zero hne)

/-- **Superadditivity (the chaining inequality).** For same-sign `a, b`,
chaining two distinctions costs at least the sum of the parts. -/
theorem jcost_superadd_same_sign {a b : ℝ} (h : 0 ≤ a * b) :
    Jcost (Real.exp a) + Jcost (Real.exp b) ≤ Jcost (Real.exp (a + b)) := by
  rw [jcost_chain_excess_identity]
  have hJa : 0 ≤ Jcost (Real.exp a) := jcost_exp_nonneg a
  have hJb : 0 ≤ Jcost (Real.exp b) := jcost_exp_nonneg b
  have hsinh : 0 ≤ Real.sinh a * Real.sinh b := by
    rcases mul_nonneg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact mul_nonneg (sinh_nonneg_of_nonneg ha) (sinh_nonneg_of_nonneg hb)
    · have h1 : Real.sinh a = - Real.sinh (-a) := by
        rw [Real.sinh_neg a]
        ring
      have h2 : Real.sinh b = - Real.sinh (-b) := by
        rw [Real.sinh_neg b]
        ring
      rw [h1, h2, neg_mul_neg]
      exact mul_nonneg (sinh_nonneg_of_nonneg (neg_nonneg.mpr ha))
        (sinh_nonneg_of_nonneg (neg_nonneg.mpr hb))
  linarith [mul_nonneg hJa hJb, hsinh]

/-- **Strict superadditivity.** For same-sign nonzero `a, b`, chaining two
distinctions costs strictly more than the sum of the parts: the excess
`J(e^a)J(e^b) + sinh a sinh b` is positive. -/
theorem jcost_superadd_strict_same_sign {a b : ℝ} (h : 0 < a * b) :
    Jcost (Real.exp a) + Jcost (Real.exp b) < Jcost (Real.exp (a + b)) := by
  rw [jcost_chain_excess_identity]
  have hJa : 0 < Jcost (Real.exp a) := jcost_exp_pos (fun ha => by
    rw [ha] at h
    simp at h)
  have hJb : 0 < Jcost (Real.exp b) := jcost_exp_pos (fun hb => by
    rw [hb] at h
    simp at h)
  have hsinh : 0 < Real.sinh a * Real.sinh b := by
    rcases mul_pos_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact mul_pos (sinh_pos_of_pos ha) (sinh_pos_of_pos hb)
    · have h1 : Real.sinh a = - Real.sinh (-a) := by
        rw [Real.sinh_neg a]
        ring
      have h2 : Real.sinh b = - Real.sinh (-b) := by
        rw [Real.sinh_neg b]
        ring
      rw [h1, h2, neg_mul_neg]
      exact mul_pos (sinh_pos_of_pos (neg_pos.mpr ha)) (sinh_pos_of_pos (neg_pos.mpr hb))
  have h3 : 0 < Jcost (Real.exp a) * Jcost (Real.exp b) := mul_pos hJa hJb
  linarith [h3, hsinh]

/-- The chaining inequality in ratio form: for distinctions `x, y ≥ 1`,
`J(x) + J(y) ≤ J(x·y)`. -/
theorem jcost_superadd_ratio {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Jcost x + Jcost y ≤ Jcost (x * y) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have h := jcost_superadd_same_sign (mul_nonneg (Real.log_nonneg hx) (Real.log_nonneg hy))
  have e1 : Real.exp (Real.log x) = x := Real.exp_log hx0
  have e2 : Real.exp (Real.log y) = y := Real.exp_log hy0
  have e3 : Real.exp (Real.log x + Real.log y) = x * y := by
    rw [Real.exp_add, e1, e2]
  rwa [e1, e2, e3] at h

/-! ## Leg 2: subdivision trivializes, so the tick is forced -/

/-- Per-refinement cost bound: splitting a distinction of log-size `ε` into
`n` equal micro-steps costs at most `ε²·cosh ε/(2n)`. -/
theorem subdivision_cost_bound (ε : ℝ) (n : ℕ) :
    (n : ℝ) * Jcost (Real.exp (ε / n))
      ≤ ε ^ 2 * Real.cosh ε / (2 * (n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Jcost, Real.exp_zero, div_zero]
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have ht : Jcost (Real.exp (ε / n)) = Real.cosh (ε / n) - 1 := by
      have h := FunctionalEquation.Jcost_G_eq_cosh_sub_one (ε / (n : ℝ))
      simpa [FunctionalEquation.G] using h
    rw [ht]
    have hb := cosh_sub_one_le (ε / (n : ℝ))
    have hcosh_le : Real.cosh (ε / (n : ℝ)) ≤ Real.cosh ε := by
      have h1 : |ε / (n : ℝ)| ≤ |ε| := by
        rw [abs_div, abs_of_pos hn']
        exact div_le_self (abs_nonneg ε) (by exact_mod_cast hn)
      calc Real.cosh (ε / (n : ℝ)) = Real.cosh |ε / (n : ℝ)| := (Real.cosh_abs _).symm
        _ ≤ Real.cosh |ε| := cosh_mono_on_nonneg (abs_nonneg _) h1
        _ = Real.cosh ε := Real.cosh_abs _
    calc (n : ℝ) * (Real.cosh (ε / n) - 1)
        ≤ (n : ℝ) * ((ε / n) ^ 2 / 2 * Real.cosh (ε / n)) :=
          mul_le_mul_of_nonneg_left hb (le_of_lt hn')
      _ = ε ^ 2 / (2 * (n : ℝ)) * Real.cosh (ε / n) := by
          field_simp [hn'.ne']
      _ ≤ ε ^ 2 / (2 * (n : ℝ)) * Real.cosh ε := by
          apply mul_le_mul_of_nonneg_left hcosh_le
          positivity
      _ = ε ^ 2 * Real.cosh ε / (2 * (n : ℝ)) := by ring

/-- Per-refinement cost is nonnegative. -/
theorem subdivision_cost_nonneg (ε : ℝ) (n : ℕ) :
    0 ≤ (n : ℝ) * Jcost (Real.exp (ε / n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.le
    have ht : Jcost (Real.exp (ε / n)) = Real.cosh (ε / n) - 1 := by
      have h := FunctionalEquation.Jcost_G_eq_cosh_sub_one (ε / (n : ℝ))
      simpa [FunctionalEquation.G] using h
    rw [ht]
    exact mul_nonneg hn' (sub_nonneg.mpr (Real.one_le_cosh _))

/-- **Subdivision trivializes.** The total cost of `n` equal micro-steps
spanning a fixed distinction of log-size `ε` tends to zero:
`n · J(e^{ε/n}) → 0`. A continuum (infinitely refinable) ledger prices every
finite chain arbitrarily low. -/
theorem jcost_subdivision_trivializes (ε : ℝ) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * Jcost (Real.exp (ε / n)))
      Filter.atTop (nhds 0) := by
  have hC : Filter.Tendsto (fun n : ℕ => ε ^ 2 * Real.cosh ε / (2 * (n : ℝ)))
      Filter.atTop (nhds 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (ε ^ 2 * Real.cosh ε / 2)
    exact h.congr (fun n => by rw [div_div])
  exact squeeze_zero (subdivision_cost_nonneg ε) (subdivision_cost_bound ε) hC

/-- No positive cost floor survives refinement: for any `c > 0`, some
refinement level prices the `ε`-chain below `c`. -/
theorem no_cost_floor_under_refinement {ε : ℝ} {c : ℝ} (hc : 0 < c) :
    ∃ n : ℕ, (n : ℝ) * Jcost (Real.exp (ε / n)) < c := by
  have ht := jcost_subdivision_trivializes ε
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) * Jcost (Real.exp (ε / n)) < c :=
    ht.eventually (eventually_lt_nhds hc)
  exact hev.exists

/-- **The tick is forced (contrapositive form).** A ledger that permits
arbitrary refinement and still charges at least `c > 0` for the `ε`-chain at
every level does not exist: cost-nontriviality is incompatible with infinite
refinability. -/
theorem cost_floor_forces_tick {ε : ℝ} {c : ℝ} (hc : 0 < c)
    (hfloor : ∀ n : ℕ, c ≤ (n : ℝ) * Jcost (Real.exp (ε / n))) :
    False := by
  obtain ⟨n, hn⟩ := no_cost_floor_under_refinement hc
  exact absurd (hfloor n) (not_le.mpr hn)

/-- Positive reading: a ledger sustaining floor `c > 0` at refinement level
`n` must satisfy `n ≤ ε²·cosh ε/(2c)`; the tick is a regularizer forced by
cost-nontriviality, with an explicit bound. -/
theorem tick_bound {ε : ℝ} {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 0 < n)
    (hfloor : c ≤ (n : ℝ) * Jcost (Real.exp (ε / n))) :
    (n : ℝ) ≤ ε ^ 2 * Real.cosh ε / (2 * c) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : c ≤ ε ^ 2 * Real.cosh ε / (2 * (n : ℝ)) :=
    le_trans hfloor (subdivision_cost_bound ε n)
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))] at h1
  rw [le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hc)]
  have e : c * (2 * (n : ℝ)) = (n : ℝ) * (2 * c) := by ring
  linarith [h1, e]

/-! ## Leg 3 (assembly): tick + closure gives φ; closure itself remains open -/

/-- The geometric-root chain, assembled. Three kernel-checked components:
the tick is forced (subdivision trivializes), chaining is superadditive, and
on a closed geometric ladder the ratio is φ (banked). The closure hypothesis
of the third component is the remaining research leg; see module docstring. -/
theorem geometric_root_assembly :
    (∀ ε : ℝ, Filter.Tendsto (fun n : ℕ => (n : ℝ) * Jcost (Real.exp (ε / n)))
        Filter.atTop (nhds 0))
    ∧ (∀ x y : ℝ, 1 ≤ x → 1 ≤ y → Jcost x + Jcost y ≤ Jcost (x * y))
    ∧ (∀ S : Foundation.PhiForcingDerived.GeometricScaleSequence,
        S.isClosed → S.ratio = Constants.phi) :=
  ⟨jcost_subdivision_trivializes,
   fun x y hx hy => @jcost_superadd_ratio x y hx hy,
   fun S h => Foundation.PhiForcingDerived.closed_ratio_is_phi S h⟩

end GeometricRoot
end Cost
end IndisputableMonolith

#print axioms IndisputableMonolith.Cost.GeometricRoot.jcost_chain_excess_identity
#print axioms IndisputableMonolith.Cost.GeometricRoot.jcost_superadd_strict_same_sign
#print axioms IndisputableMonolith.Cost.GeometricRoot.jcost_subdivision_trivializes
#print axioms IndisputableMonolith.Cost.GeometricRoot.cost_floor_forces_tick
#print axioms IndisputableMonolith.Cost.GeometricRoot.tick_bound
#print axioms IndisputableMonolith.Cost.GeometricRoot.geometric_root_assembly
