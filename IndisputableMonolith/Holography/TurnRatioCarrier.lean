import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Holography.DeficitFreePeriod
import IndisputableMonolith.Holography.EightTickSubperiodExclusion

/-!
# TurnRatioCarrier: the B2 core priced on the real turn ratio (LEG-B)

**Panel decision 2026-07-04** (`state/panel/bekenstein_legb_20260704_20260704_142417.json`,
plan `plans/Bekenstein_LEGB_Loop_And_Derivation_Plan_20260704.html`): price the per-cycle
recognition cost of the continued 8-tick cycle as `J` of the REAL TURN RATIO

  `C(T) = J(κT / 2π)`,   `J(x) = (x + x⁻¹)/2 − 1`  (T5, `Cost.Jcost`),

not as any extension of `J` to the returned U(1) phase. The ratio carrier applies T5 on
`ℝ₊` where it is a THEOREM (`Cost.Jcost_eq_zero_iff`), and in one inequality it sees the
deficit (`x < 1`), the excess (`x > 1`), and every `n`-sheeted cover
(`J(n) = (n−1)²/(2n) > 0` for `n ≥ 2`). Consequences landed here:

1. **Unique zero-cost period (THEOREM).** `C(T) = 0 ↔ T = 2π/κ` for `κ, T > 0`
   (`turnRatioCost_eq_zero_iff`): the deficit-free period is not merely the MINIMAL
   positive closure time (`DeficitFreePeriod.euclideanPeriod_isLeast`) but the UNIQUE
   zero of the per-cycle cost. Strict positivity off the period is
   `turnRatioCost_pos_of_ne_period`.
2. **KMS-window discharge (THEOREM).** Every `n ≥ 2` lattice multiple (the n-sheeted
   Euclidean cover, angle `2πn`) carries strictly positive cost
   (`turnRatioCost_cover_pos`, value `Jcost_cover_value`), so zero-cost closure forces
   `n = 1` (`lattice_period_zero_cost_iff`) with NO window hypothesis. This retires the
   `legb_kms_window_unique` window premise on the cost side.
3. **Phase-branch poison lemma (THEOREM).** The J-FORMULA applied verbatim to the
   returned unit phase gives `cos δ − 1 ≤ 0` (`phaseCost_nonpos`): never strictly
   positive, so it cannot penalize any deficit, and it vanishes on EVERY cover
   (`phaseCost_vanishes_on_covers`), so it can never single out `n = 1`. The phase
   branch is dead in-kernel. (Distinct object from `DeficitFreePeriod.deficitCost
   = 1 − cos δ`, the chord form, which is nonneg but equally lattice-blind at covers.)
4. **U(1)-extension underdetermination (THEOREM).** Two extensions of `J` to `ℂ`
   (`Jprime`, `Jsecond`) that AGREE with `Cost.Jcost` on `ℝ₊` yet differ at `I`, one of
   which vanishes at `I ≠ 1` (`u1_extension_zero_set_not_forced`): the kernel record
   that "extend J off the reals" is a CHOICE, not a forced object, killing the
   extend-J-to-U(1) route to B2.
5. **Flat-space limit (THEOREM).** As `κ → 0⁺` the cost of any fixed period diverges
   (`turnRatioCost_unbounded_near_zero_kappa`) and the forced period itself diverges
   (`euclideanPeriod_unbounded`): no horizon, no finite zero-cost period, no residual
   thermality. Accumulated cost over repeated positive-cost cycles is unbounded
   (`accumulatedCost_unbounded`).
6. **Once-per-closure census record (THEOREM, by `decide`).** On the forced substrate,
   the witness 8-walk posts each admissible sector EXACTLY once per closure, while its
   `n = 2` retrace (a closed 16-walk) is census-complete but DOUBLE-POSTS every sector
   (`eight_tick_multiple_exclusion`). This is the discrete once-per-closure content the
   `CensusPricing` premise prices; it also records that
   `EightTickSubperiodExclusion` alone (proper divisors {1,2,4}) does NOT exclude
   multiples: the multiple side is a posting-discipline fact, not a census-absence fact.

## The honest residual (do not overclaim)

The ONE remaining physics premise is `CensusPricing`: the fixed-point per-cycle cost of
the continued cycle IS `J` of the delivered/required closure ratio, posted once per
closure. Given it, B2 discharges carrier-agnostically
(`b2_unique_zero_of_censusPricing`). Until `CensusPricing` is derived from the seam
ledger, consumers are FORCED-CONDITIONAL on this one named premise (tag per `soul.mdc`:
the weakest link sets the tag). Its under-posting half is the landed
`EightTickSubperiodExclusion`; its over-posting half is the double-posting record here.
-/

namespace IndisputableMonolith
namespace Holography
namespace TurnRatioCarrier

open Complex

/-! ## The carrier: the real turn ratio and its J-cost -/

/-- The turn ratio: the fraction of one full turn the continued clock at rate `κ`
sweeps in Euclidean time `T`. The `2π` is the full-turn angle (kernel of
`Complex.exp`, `DeficitFreePeriod.holonomy_eq_one_iff_lattice`), not a temperature. -/
noncomputable def turnRatio (kappa T : ℝ) : ℝ :=
  kappa * T / (2 * Real.pi)

/-- The per-cycle recognition cost priced on the turn ratio: `C(T) = J(κT/2π)` with
`J` the unique T5 cost (`Cost.Jcost`). -/
noncomputable def turnRatioCost (kappa T : ℝ) : ℝ :=
  Cost.Jcost (turnRatio kappa T)

theorem turnRatio_pos {kappa T : ℝ} (hk : 0 < kappa) (hT : 0 < T) :
    0 < turnRatio kappa T := by
  unfold turnRatio
  positivity

/-- The turn ratio is `1` exactly at the deficit-free period `T = 2π/κ`. -/
theorem turnRatio_eq_one_iff (kappa T : ℝ) (hk : 0 < kappa) :
    turnRatio kappa T = 1 ↔ T = DeficitFreePeriod.euclideanPeriod kappa := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hk0 : kappa ≠ 0 := ne_of_gt hk
  unfold turnRatio DeficitFreePeriod.euclideanPeriod
  rw [div_eq_one_iff_eq (by positivity), eq_div_iff hk0]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- The cost is nonnegative for positive rate and period (T5 AM-GM,
`Cost.Jcost_nonneg`). -/
theorem turnRatioCost_nonneg {kappa T : ℝ} (hk : 0 < kappa) (hT : 0 < T) :
    0 ≤ turnRatioCost kappa T :=
  Cost.Jcost_nonneg (turnRatio_pos hk hT)

/-- **Headline (B2 math half): the deficit-free period is the UNIQUE zero of the
per-cycle cost.** `C(T) = 0 ↔ T = 2π/κ`. Strictly stronger than minimality
(`DeficitFreePeriod.euclideanPeriod_isLeast`): no other positive period, lattice or
not, deficit or excess, has zero cost. Pure T5 (`Cost.Jcost_eq_zero_iff`). -/
theorem turnRatioCost_eq_zero_iff (kappa T : ℝ) (hk : 0 < kappa) (hT : 0 < T) :
    turnRatioCost kappa T = 0 ↔ T = DeficitFreePeriod.euclideanPeriod kappa := by
  unfold turnRatioCost
  rw [Cost.Jcost_eq_zero_iff _ (turnRatio_pos hk hT)]
  exact turnRatio_eq_one_iff kappa T hk

/-- Strict positivity off the deficit-free period: any other positive period, deficit
or excess, costs strictly positive recognition per cycle. -/
theorem turnRatioCost_pos_of_ne_period (kappa T : ℝ) (hk : 0 < kappa) (hT : 0 < T)
    (hne : T ≠ DeficitFreePeriod.euclideanPeriod kappa) :
    0 < turnRatioCost kappa T := by
  rcases lt_or_eq_of_le (turnRatioCost_nonneg hk hT) with hpos | heq
  · exact hpos
  · exact absurd ((turnRatioCost_eq_zero_iff kappa T hk hT).mp heq.symm) hne

/-- T5 reciprocity on the carrier: a deficit (ratio `x`) and its reciprocal excess
(ratio `1/x`) cost the same (`Cost.Jcost_symm`). -/
theorem turnRatioCost_reciprocal (kappa T : ℝ) (hk : 0 < kappa) (hT : 0 < T) :
    Cost.Jcost (turnRatio kappa T) = Cost.Jcost (turnRatio kappa T)⁻¹ :=
  Cost.Jcost_symm (turnRatio_pos hk hT)

/-! ## The n-sheeted covers: positive cost, KMS window discharged -/

/-- The turn ratio of the `n`-fold cover of the deficit-free period is exactly `n`. -/
theorem turnRatio_cover (kappa : ℝ) (hk : 0 < kappa) (n : ℕ) :
    turnRatio kappa (n * DeficitFreePeriod.euclideanPeriod kappa) = n := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hk0 : kappa ≠ 0 := ne_of_gt hk
  unfold turnRatio DeficitFreePeriod.euclideanPeriod
  field_simp

/-- The panel's cover-cost value: `J(n) = (n−1)²/(2n)` (from `Cost.Jcost_eq_sq`). -/
theorem Jcost_cover_value (n : ℕ) (hn : 1 ≤ n) :
    Cost.Jcost (n : ℝ) = ((n : ℝ) - 1) ^ 2 / (2 * n) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact Cost.Jcost_eq_sq hn0

/-- **KMS-window discharge, positivity half:** every `n ≥ 2` sheeted cover (Euclidean
angle `2πn`) carries strictly positive per-cycle cost. The excess-angle branch is
cost-excluded by the same T5 inequality as the deficit branch. -/
theorem turnRatioCost_cover_pos (kappa : ℝ) (hk : 0 < kappa) (n : ℕ) (hn : 2 ≤ n) :
    0 < turnRatioCost kappa (n * DeficitFreePeriod.euclideanPeriod kappa) := by
  unfold turnRatioCost
  rw [turnRatio_cover kappa hk n]
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hn
  have hne : (n : ℝ) ≠ 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hn
    exact ne_of_gt this
  exact Cost.Jcost_pos_of_ne_one _ hpos hne

/-- **KMS-window discharge, uniqueness form:** among ALL lattice periods
`T = n·(2π/κ)` (`n ≥ 1`), zero cost holds exactly at `n = 1`. No window hypothesis
`β < 2·(2π/κ)` is needed: the cost functional itself excludes every multiple. -/
theorem lattice_period_zero_cost_iff (kappa : ℝ) (hk : 0 < kappa) (n : ℕ) (hn : 1 ≤ n) :
    turnRatioCost kappa (n * DeficitFreePeriod.euclideanPeriod kappa) = 0 ↔ n = 1 := by
  have hpos : (0 : ℝ) < n := by
    have hn' : 0 < n := by omega
    exact_mod_cast hn'
  unfold turnRatioCost
  rw [turnRatio_cover kappa hk n, Cost.Jcost_eq_zero_iff _ hpos]
  exact_mod_cast Nat.cast_eq_one (R := ℝ)

/-! ## The phase branch is poison: sign-dead and lattice-blind -/

/-- The J-FORMULA applied verbatim to the returned unit phase `exp(iδ)` (real part
reading). This is the object the derive captain kept reaching for; the next two
theorems record in-kernel why it can never work. -/
noncomputable def phaseCost (δ : ℝ) : ℝ :=
  ((Complex.exp (δ * Complex.I) + (Complex.exp (δ * Complex.I))⁻¹) / 2 - 1).re

/-- The phase-branch cost evaluates to `cos δ − 1`. -/
theorem phaseCost_eq (δ : ℝ) : phaseCost δ = Real.cos δ - 1 := by
  unfold phaseCost
  rw [← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  have h : (Complex.cos δ + Complex.sin δ * Complex.I +
      (Complex.cos δ + -Complex.sin δ * Complex.I)) / 2 - 1 = Complex.cos δ - 1 := by
    ring
  rw [h, Complex.sub_re, Complex.cos_ofReal_re, Complex.one_re]

/-- **Poison lemma (sign death):** the phase-branch cost is NEVER strictly positive,
so it cannot penalize any deficit. The phase branch cannot force the period. -/
theorem phaseCost_nonpos (δ : ℝ) : phaseCost δ ≤ 0 := by
  rw [phaseCost_eq]
  linarith [Real.cos_le_one δ]

/-- **Poison lemma (lattice blindness):** the phase-branch cost vanishes on EVERY
`n`-sheeted cover, so it can never single out `n = 1`. Contrast
`turnRatioCost_cover_pos`. -/
theorem phaseCost_vanishes_on_covers (n : ℤ) : phaseCost ((n : ℝ) * (2 * Real.pi)) = 0 := by
  rw [phaseCost_eq, Real.cos_int_mul_two_pi]
  ring

/-! ## The U(1) extension of J is a choice: two agreeing extensions that disagree -/

/-- The naive real-part extension of the J-formula to `ℂ`. -/
noncomputable def JextRe (z : ℂ) : ℝ := ((z + z⁻¹) / 2 - 1).re

/-- `JextRe` agrees with the T5 cost on the reals. -/
theorem JextRe_agrees (x : ℝ) : JextRe (x : ℂ) = Cost.Jcost x := by
  unfold JextRe Cost.Jcost
  have h : ((x : ℂ) + (x : ℂ)⁻¹) / 2 - 1 = ((x + x⁻¹) / 2 - 1 : ℝ) := by
    push_cast
    ring
  rw [h, Complex.ofReal_re]

/-- First counterexample extension: agrees with `J` on `ℝ` (where `im = 0`), differs
off it. -/
noncomputable def Jprime (z : ℂ) : ℝ := (1 + z.im ^ 2) * JextRe z

/-- Second counterexample extension: also agrees with `J` on `ℝ₊`, also differs off
it, and has a DIFFERENT zero set. -/
noncomputable def Jsecond (z : ℂ) : ℝ := (z.re ^ 2 / Complex.normSq z) * JextRe z

theorem Jprime_agrees (x : ℝ) : Jprime (x : ℂ) = Cost.Jcost x := by
  unfold Jprime
  rw [JextRe_agrees]
  simp

theorem Jsecond_agrees (x : ℝ) (hx : 0 < x) : Jsecond (x : ℂ) = Cost.Jcost x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold Jsecond
  rw [JextRe_agrees]
  rw [Complex.normSq_ofReal, Complex.ofReal_re]
  have h1 : x ^ 2 / (x * x) = 1 := by
    field_simp
  rw [h1, one_mul]

theorem JextRe_I : JextRe Complex.I = -1 := by
  unfold JextRe
  rw [Complex.inv_I]
  simp

theorem Jprime_I : Jprime Complex.I = -2 := by
  unfold Jprime
  rw [JextRe_I]
  norm_num [Complex.I_im]

theorem Jsecond_I : Jsecond Complex.I = 0 := by
  unfold Jsecond
  simp [Complex.I_re]

/-- **Kernel record: the U(1)/ℂ extension of `J` is underdetermined.** Two extensions
agree with `Cost.Jcost` on all of `ℝ₊` yet disagree at `I`. Any argument that "extends
J to the phase and reads off the period" is choosing its conclusion. -/
theorem u1_extension_not_unique :
    ∃ J₁ J₂ : ℂ → ℝ,
      (∀ x : ℝ, 0 < x → J₁ (x : ℂ) = Cost.Jcost x) ∧
      (∀ x : ℝ, 0 < x → J₂ (x : ℂ) = Cost.Jcost x) ∧
      ∃ z : ℂ, J₁ z ≠ J₂ z := by
  refine ⟨Jprime, Jsecond, fun x _ => Jprime_agrees x, fun x hx => Jsecond_agrees x hx,
    Complex.I, ?_⟩
  rw [Jprime_I, Jsecond_I]
  norm_num

/-- **Kernel record: the zero set of an agreeing extension is not forced.** `Jsecond`
agrees with `J` on `ℝ₊` yet vanishes at `I ≠ 1`: imposing "zero iff closure" on an
extension ASSUMES B2's conclusion rather than deriving it. -/
theorem u1_extension_zero_set_not_forced :
    ∃ J' : ℂ → ℝ,
      (∀ x : ℝ, 0 < x → J' (x : ℂ) = Cost.Jcost x) ∧
      J' Complex.I = 0 ∧ (Complex.I : ℂ) ≠ 1 := by
  refine ⟨Jsecond, fun x hx => Jsecond_agrees x hx, Jsecond_I, ?_⟩
  intro h
  have := congrArg Complex.im h
  simp at this

/-! ## Flat-space limit: no horizon, no finite zero-cost period, no bound -/

/-- As `κ → 0⁺` the deficit-free period diverges: below any bound `M` there is a rate
threshold under which the period exceeds `M`. No finite periodicity survives in flat
space. -/
theorem euclideanPeriod_unbounded (M : ℝ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ kappa : ℝ, 0 < kappa → kappa < κ₀ →
      M < DeficitFreePeriod.euclideanPeriod kappa := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hA : (0 : ℝ) < max M 1 := lt_max_of_lt_right one_pos
  refine ⟨2 * Real.pi / max M 1, by positivity, ?_⟩
  intro kappa hk hklt
  unfold DeficitFreePeriod.euclideanPeriod
  have h1 : max M 1 < 2 * Real.pi / kappa := by
    rw [lt_div_iff₀ hk]
    calc max M 1 * kappa < max M 1 * (2 * Real.pi / max M 1) := by
          exact mul_lt_mul_of_pos_left hklt hA
      _ = 2 * Real.pi := by field_simp
  exact lt_of_le_of_lt (le_max_left M 1) h1

/-- As `κ → 0⁺` the per-cycle cost of any FIXED period diverges past every bound: the
turn ratio collapses to `0⁺` and `J` blows up. Flat space admits no finite-cost
closure at any finite period; no residual thermality survives. -/
theorem turnRatioCost_unbounded_near_zero_kappa (T : ℝ) (hT : 0 < T) (M : ℝ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ kappa : ℝ, 0 < kappa → kappa < κ₀ →
      M < turnRatioCost kappa T := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set A : ℝ := max M 0 with hA
  have hA0 : 0 ≤ A := le_max_right M 0
  have hMA : M ≤ A := le_max_left M 0
  have hden : (0 : ℝ) < 2 * A + 4 := by linarith
  refine ⟨2 * Real.pi / (T * (2 * A + 4)), by positivity, ?_⟩
  intro kappa hk hklt
  have hx : 0 < turnRatio kappa T := turnRatio_pos hk hT
  -- the ratio is small: x < 1/(2A+4)
  have hxlt : turnRatio kappa T < 1 / (2 * A + 4) := by
    unfold turnRatio
    rw [div_lt_div_iff₀ (by positivity) hden]
    have h1 : kappa * (T * (2 * A + 4)) < 2 * Real.pi := by
      have := mul_lt_mul_of_pos_right hklt (by positivity : (0:ℝ) < T * (2 * A + 4))
      calc kappa * (T * (2 * A + 4))
          < 2 * Real.pi / (T * (2 * A + 4)) * (T * (2 * A + 4)) := this
        _ = 2 * Real.pi := by field_simp
    calc kappa * T * (2 * A + 4) = kappa * (T * (2 * A + 4)) := by ring
      _ < 2 * Real.pi := h1
      _ = 1 * (2 * Real.pi) := by ring
  -- hence the reciprocal is large: 2A+4 < x⁻¹
  have hinv : 2 * A + 4 < (turnRatio kappa T)⁻¹ := by
    have hprod : turnRatio kappa T * (2 * A + 4) < 1 := (lt_div_iff₀ hden).mp hxlt
    have hxx : turnRatio kappa T * (2 * A + 4) <
        turnRatio kappa T * (turnRatio kappa T)⁻¹ := by
      rw [mul_inv_cancel₀ (ne_of_gt hx)]
      exact hprod
    exact lt_of_mul_lt_mul_left hxx hx.le
  -- and J(x) ≥ x⁻¹/2 − 1 dominates
  have hJ : (turnRatio kappa T)⁻¹ / 2 - 1 ≤ Cost.Jcost (turnRatio kappa T) := by
    unfold Cost.Jcost
    nlinarith [hx.le]
  unfold turnRatioCost
  nlinarith [hJ, hinv, hMA]

/-- Accumulated cost over `N` cycles at per-cycle cost `c`. -/
def accumulatedCost (N : ℕ) (c : ℝ) : ℝ := N * c

/-- Any strictly positive per-cycle cost accumulates past every bound (Archimedean):
a deficit or excess closure cannot persist at the fixed point. -/
theorem accumulatedCost_unbounded (c : ℝ) (hc : 0 < c) (B : ℝ) :
    ∃ N : ℕ, B < accumulatedCost N c := by
  obtain ⟨N, hN⟩ := exists_nat_gt (B / c)
  refine ⟨N, ?_⟩
  unfold accumulatedCost
  rwa [div_lt_iff₀ hc] at hN

/-! ## Once per closure: the single cycle posts each sector once, the double cover
posts each twice (kernel `decide`) -/

open EightTickSubperiodExclusion in
/-- How many times a walk's cycle representatives (visits minus the closing return)
post into a given admissible orbit. -/
def visitCount (s : PixelLocal.FaceCfg) (fs : List (Fin 4)) (orbit : List Nat) : ℕ :=
  ((walkVisits s fs).dropLast.filter (fun c => orbit.contains c.val)).length

/-- The census witness walk of `EightTickSubperiodExclusion`
(`0→1→3→7→15→14→10→8→0`). -/
def witnessWalk : List (Fin 4) := [0, 1, 2, 3, 0, 2, 1, 3]

open EightTickSubperiodExclusion in
/-- **Once-per-closure record (THEOREM, kernel `decide`).** The witness 8-walk closes
and posts each of the four admissible sectors EXACTLY once; its `n = 2` retrace (a
closed 16-walk, the discrete 2-sheeted cover) is census-complete but posts each sector
EXACTLY twice. The multiple branch is not a census-absence fact (the cover still sees
all sectors, so `EightTickSubperiodExclusion` alone cannot exclude it): it is a
DOUBLE-POSTING fact, which is precisely the over-posting half of the `CensusPricing`
premise. -/
theorem eight_tick_multiple_exclusion :
    (walkEnd 0 witnessWalk = 0 ∧
      visitCount 0 witnessWalk [0] = 1 ∧
      visitCount 0 witnessWalk [3, 6, 12, 9] = 1 ∧
      visitCount 0 witnessWalk [5, 10] = 1 ∧
      visitCount 0 witnessWalk [15] = 1) ∧
    (walkEnd 0 (witnessWalk ++ witnessWalk) = 0 ∧
      censusComplete 0 (witnessWalk ++ witnessWalk) = true ∧
      visitCount 0 (witnessWalk ++ witnessWalk) [0] = 2 ∧
      visitCount 0 (witnessWalk ++ witnessWalk) [3, 6, 12, 9] = 2 ∧
      visitCount 0 (witnessWalk ++ witnessWalk) [5, 10] = 2 ∧
      visitCount 0 (witnessWalk ++ witnessWalk) [15] = 2) := by
  decide

/-! ## The named premise and the carrier-agnostic B2 discharge -/

/-- **The one remaining physics premise (`CensusPricing` /
`CensusClosureNormalization`), NAMED and TYPED.** The fixed-point per-cycle
recognition cost of the continued cycle at rate `κ` and Euclidean period `T` is `J` of
the turn ratio (the delivered/required closure fraction), posted once per closure.
Under-posting half: `EightTickSubperiodExclusion` (proper sub-periods destroy the
census). Over-posting half: `eight_tick_multiple_exclusion` (covers double-post).
STATUS: MODEL until derived from the seam ledger; consumers of the discharge below are
FORCED-CONDITIONAL on it. -/
def CensusPricing (C : ℝ → ℝ → ℝ) : Prop :=
  ∀ kappa T : ℝ, 0 < kappa → 0 < T → C kappa T = Cost.Jcost (turnRatio kappa T)

/-- The turn-ratio cost itself satisfies the pricing premise (non-vacuity witness). -/
theorem turnRatioCost_censusPricing : CensusPricing turnRatioCost :=
  fun _ _ _ _ => rfl

/-- **B2, carrier-agnostic, discharged from the named premise.** ANY per-cycle cost
functional satisfying `CensusPricing` has the deficit-free period `2π/κ` as its UNIQUE
zero: deficits, excesses, and every `n ≥ 2` cover all cost strictly positive
recognition, and the cost accumulates without bound (`accumulatedCost_unbounded`).
FORCED-CONDITIONAL: the tag is set by the `CensusPricing` premise. -/
theorem b2_unique_zero_of_censusPricing (C : ℝ → ℝ → ℝ) (hC : CensusPricing C)
    (kappa T : ℝ) (hk : 0 < kappa) (hT : 0 < T) :
    C kappa T = 0 ↔ T = DeficitFreePeriod.euclideanPeriod kappa := by
  rw [hC kappa T hk hT]
  exact turnRatioCost_eq_zero_iff kappa T hk hT

/-! ## Certificate -/

/-- Bundled certificate for the turn-ratio carrier: unique zero at the deficit-free
period, strict positivity off it, positive cost on every `n ≥ 2` cover (KMS window
discharged without a window hypothesis), the phase branch sign-dead and lattice-blind,
the U(1) extension underdetermined, and the flat-space limits correct. All fields are
unconditional THEOREMs; the physics premise (`CensusPricing`) is consumed only by
`b2_unique_zero_of_censusPricing`, which is stated separately. -/
structure TurnRatioCarrierCert : Prop where
  unique_zero : ∀ kappa T : ℝ, 0 < kappa → 0 < T →
    (turnRatioCost kappa T = 0 ↔ T = DeficitFreePeriod.euclideanPeriod kappa)
  pos_off_period : ∀ kappa T : ℝ, 0 < kappa → 0 < T →
    T ≠ DeficitFreePeriod.euclideanPeriod kappa → 0 < turnRatioCost kappa T
  cover_pos : ∀ kappa : ℝ, 0 < kappa → ∀ n : ℕ, 2 ≤ n →
    0 < turnRatioCost kappa (n * DeficitFreePeriod.euclideanPeriod kappa)
  phase_dead : ∀ δ : ℝ, phaseCost δ ≤ 0
  phase_lattice_blind : ∀ n : ℤ, phaseCost ((n : ℝ) * (2 * Real.pi)) = 0
  extension_not_unique : ∃ J₁ J₂ : ℂ → ℝ,
    (∀ x : ℝ, 0 < x → J₁ (x : ℂ) = Cost.Jcost x) ∧
    (∀ x : ℝ, 0 < x → J₂ (x : ℂ) = Cost.Jcost x) ∧
    ∃ z : ℂ, J₁ z ≠ J₂ z
  flat_space_period : ∀ M : ℝ, ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ kappa : ℝ,
    0 < kappa → kappa < κ₀ → M < DeficitFreePeriod.euclideanPeriod kappa

/-- The certificate holds. -/
theorem turnRatioCarrierCert : TurnRatioCarrierCert where
  unique_zero := turnRatioCost_eq_zero_iff
  pos_off_period := turnRatioCost_pos_of_ne_period
  cover_pos := fun kappa hk n hn => turnRatioCost_cover_pos kappa hk n hn
  phase_dead := phaseCost_nonpos
  phase_lattice_blind := phaseCost_vanishes_on_covers
  extension_not_unique := u1_extension_not_unique
  flat_space_period := euclideanPeriod_unbounded

end TurnRatioCarrier
end Holography
end IndisputableMonolith
