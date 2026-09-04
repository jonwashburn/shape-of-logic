/-
  Cost/UnitForcedFromCarrier.lean

  THE UNIT OF COST IS FORCED BY THE CARRIER, NOT CHOSEN.

  The question. `Delta_Cost_Form_Forced_Unit_Gauge` (May 2026) proves a stratification: the
  cost laws force the cost FORM, the gauge orbit `x ↦ J (x ^ c)` for `c > 0`, and leave one
  free positive real, the log-curvature at the unit, which equals `c ^ 2`. Its §"The one open
  question that would upgrade the result" asks whether that curvature is itself derivable from
  distinction, "specifically from the cost of a single distinction act", and conjectures that
  "the minimal recognition cost of telling apart two states that differ by one act, carried
  from the discrete layer to the completion, fixes the second-order coefficient of the cost
  profile at the unit to exactly one".

  This file proves that conjecture, on one named classical import.

  The two conditions. BOTH ARE POSTULATES. Neither names a number, and each is satisfied by a
  nontrivial class, so the trade is a point in the positive reals for two qualitative
  principles. It is not the elimination of an assumption, and this file does not claim that.

  * CARRIER-COMPATIBILITY (`CarrierValued`). The continuous cost restricts, on the carrier, to
    a cost that lands back in the carrier: `F c n` is rational at rational `n`. δ's `def:laws`
    defines a cost form as `F : K_{>0} → K` for an ordered field `K` and says the first three
    laws "make sense on any field of values, in particular on the rational field that
    distinction produces". That is a PERMISSION, that `ℚ`-valued cost forms are admissible
    objects, and reading it as an OBLIGATION on the continuous member would be a modal
    fallacy. The `ℚ`-valued cost on `ℚ_{>0}` and the continuous cost on `ℝ_{>0}` are two
    objects, and the claim that one serves both layers is an assumption. It is the natural one
    if `ℝ_{>0}` is the completion of the carrier and the cost extends continuously, which is
    δ's own picture, but it is a postulate and is labelled as one here. Identified as the
    weakest joint by adversarial review, 2026-07-27.
  * LEAST COST (`LeastAmongCarrierValued`). Among the carrier-compatible members, take the
    cheapest. This is the principle δ's own conjecture names ("the minimal recognition cost"),
    and `Cost.UnitFromMinimality.anchor_is_minimality_over_powers` shows it cuts the gauge
    family at exactly the place the stipulated anchor did. `unit_forced_by_automorphism` below
    offers a structural alternative that does not minimize anything and reaches the same
    conclusion, so the answer is not an artifact of choosing a variational principle.

  SCOPE, so the minimality claim is not over-read. `J` is NOT least among all `ℚ`-valued cost
  forms on `ℚ_{>0}`. By δ's own `thm:negative` those are the character costs of a free abelian
  group with one independent choice per prime, and `χ(2) = 2` with `χ(p) = 1` elsewhere
  undercuts `J` at the ratio three. What excludes those is MONOTONICITY, the ledger's own order
  condition, which with complete multiplicativity forces a power map by Erdős's theorem
  (proved unconditionally from Howe's argument in `Cost.MonotoneMultiplicativePower`, and
  consumed by `Cost.GaugeOrbitClassification`). So the competitor class here is restricted
  three times, by carrier-compatibility, by the continuous gauge shape (equivalently by
  monotonicity on the carrier), and by nondegeneracy, which is what rules out the cost that
  charges nothing. Each restriction is δ's, and all three are named rather than assumed
  silently.

  What this does NOT contradict. `PRCCalibrationTarget.calibration_unit_is_a_gauge` and
  `PRCCalibrationIndependence.calibration_unit_not_forced_by_cost_laws` prove that the cost
  LAWS alone do not force `c = 1`, and remain true. Their scope is the law set with
  real-valued costs, and the accompanying note that "the whole family is admissible on ℚ_δ"
  is correct for real-valued costs. It fails for carrier-valued ones: a gauge member at
  non-integer scale charges an irrational amount at a rational ratio, and the six exponentials
  theorem is what turns that observation into integrality of the exponent.

  The chain.

  1. Carrier-valuedness at the bases two, three and five says the traces are rational, so the
     six exponentials input gives `c = k` for a positive integer `k`
     (`Cost.TraceRationalExponent.exponent_is_positive_integer`).
  2. Least cost over the integer gauges then forces `k = 1`
     (`Cost.UnitFromMinimality.isLeastPower_iff_canonical`).
  3. The log-curvature at the unit is `c ^ 2`
     (`PRCCalibrationTarget.Calibration.logCurvature`), hence exactly one.

  Both hypotheses are load-bearing and this file proves it rather than asserting it.
  `carrierValued_two` exhibits a carrier-valued gauge that is not the unit, so leastness is
  needed; `leastAmongIntegerGauges_half` exhibits a least gauge that is not the unit, so
  carrier-valuedness is needed.

  The one import that is not proved here is the six exponentials input, already named and
  isolated in `Cost.TraceRationalExponent.SixExponentialsTraceInput`. It is a corollary of the
  six exponentials THEOREM of Siegel, Lang and Ramachandra, NOT of the open four exponentials
  conjecture, and the distinction is the number of bases. With `y = (1, c)` independent over
  `ℚ` exactly when `c` is irrational, and `x = (log 2, log 3, log 5)` independent over `ℚ` by
  unique factorization, the six numbers are `2, 3, 5, 2^c, 3^c, 5^c`; a rational trace makes
  `n^c` a root of `X² - tX + 1` hence algebraic of degree at most two, so all six would be
  algebraic, which the theorem forbids. Two bases instead of three would need the four
  exponentials conjecture, which is open, so the three-base form of the hypothesis is
  load-bearing and must not be weakened to a single act of distinction. Confirmed
  independently by two frontier referees, 2026-07-27.

  Note what is NOT imported. The input delivers only `c ∈ ℚ`. The finish from rational to
  integer is proved in Lean, by a 2-adic valuation argument, in
  `Cost.TraceRationalExponent.int_of_rat_exponent_of_trace_rat`, and the base `n = 4` in the
  hypothesis is redundant since `4^c + 4^{-c} = (2^c + 2^{-c})² - 2`.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.TraceRationalExponent
import IndisputableMonolith.Cost.UnitFromMinimality
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCCalibrationTarget

namespace IndisputableMonolith
namespace Cost
namespace UnitForcedFromCarrier

open IndisputableMonolith.Cost.TraceRationalExponent
  (SixExponentialsTraceInput exponent_is_positive_integer)

open IndisputableMonolith.Cost.UnitFromMinimality
  (IsLeastPowerCost isLeastPower_iff_canonical jcost_lt_pow no_least_gauge_member)

/-! ## The gauge family, in multiplicative coordinates -/

/-- The gauge member at scale `c`: the cost that charges `J` of the `c`-th power. The whole
admissible family is exactly `{gaugeCost c : c > 0}`, and `gaugeCost 1 = J`. -/
noncomputable def gaugeCost (c x : ℝ) : ℝ := Jcost (x ^ c)

@[simp] lemma gaugeCost_one (x : ℝ) : gaugeCost 1 x = Jcost x := by
  simp [gaugeCost]

lemma gaugeCost_natCast (m : ℕ) (x : ℝ) : gaugeCost (m : ℝ) x = Jcost (x ^ m) := by
  simp [gaugeCost, Real.rpow_natCast]

/-! ## The two δ-native conditions -/

/-- **Carrier-valuedness.** The cost of a small integer ratio is a rational, that is, the
cost lands back in the carrier `ℚ_δ` that distinction generates. Three bases are enough,
and three is what the six exponentials theorem needs. -/
def CarrierValued (c : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 5 → ∃ q : ℚ, gaugeCost c (n : ℝ) = (q : ℝ)

/-- **Least cost.** The scale `c` charges no more than any integer gauge, at every ratio
other than the unit. The condition never names `J`, so leastness is not smuggled in. -/
def LeastAmongIntegerGauges (c : ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ x : ℝ, 0 < x → x ≠ 1 → gaugeCost c x ≤ gaugeCost (m : ℝ) x

/-- Carrier-valuedness of the cost is rationality of the trace, which is the form the
arithmetic step consumes. The cost is the trace halved and shifted, so the two conditions
are the same condition. -/
lemma trace_rat_of_carrierValued {c : ℝ} (h : CarrierValued c) :
    ∀ n : ℕ, 2 ≤ n → n ≤ 5 →
      ∃ t : ℚ, ((n : ℝ)) ^ c + (((n : ℝ)) ^ c)⁻¹ = (t : ℝ) := by
  intro n h2 h5
  obtain ⟨q, hq⟩ := h n h2 h5
  refine ⟨2 * q + 2, ?_⟩
  have hcost : (((n : ℝ)) ^ c + (((n : ℝ)) ^ c)⁻¹) / 2 - 1 = (q : ℝ) := by
    simpa [gaugeCost, Jcost] using hq
  push_cast
  linarith

/-! ## The unit is forced -/

/-- **The unit of cost is forced.** A positive scale that is carrier-valued and least among
the integer gauges is the unit scale. Carrier-valuedness plus the six exponentials input makes
the scale a positive integer; least cost then makes it one.

This is the conjecture of `Delta_Cost_Form_Forced_Unit_Gauge` §"The one open question", proved
rather than assumed, with the single classical import visible in the statement. -/
theorem unit_forced (hsix : SixExponentialsTraceInput) {c : ℝ} (hc : 0 < c)
    (hcar : CarrierValued c) (hmin : LeastAmongIntegerGauges c) : c = 1 := by
  obtain ⟨k, hk1, hck⟩ :=
    exponent_is_positive_integer hsix hc (trace_rat_of_carrierValued hcar)
  have hleast : IsLeastPowerCost k := by
    intro m hm x hx hx1
    have h := hmin m hm x hx hx1
    rw [hck] at h
    simpa [gaugeCost, Real.rpow_natCast] using h
  have hk : k = 1 := (isLeastPower_iff_canonical k hk1).mp hleast
  rw [hck, hk]
  norm_num

/-- **The log-curvature at the unit is one, forced.** The residual gauge coordinate of the
stratification theorem is `c ^ 2`; under carrier-valuedness and least cost it is exactly one,
so the calibration datum that `Delta_Cost_Form_Forced_Unit_Gauge` supplied from outside is
determined from inside. -/
theorem logCurvature_forced (hsix : SixExponentialsTraceInput) {c : ℝ} (hc : 0 < c)
    (hcar : CarrierValued c) (hmin : LeastAmongIntegerGauges c) :
    deriv (deriv (fun t => Real.cosh (c * t) - 1)) 0 = 1 := by
  rw [Foundation.PrimitiveRecognitionCalculus.Calibration.logCurvature c,
    unit_forced hsix hc hcar hmin]
  norm_num

/-- **And the cost is `J`.** The selected member is the canonical cost on the whole positive
axis, with no calibration and no anchor. -/
theorem cost_is_Jcost (hsix : SixExponentialsTraceInput) {c : ℝ} (hc : 0 < c)
    (hcar : CarrierValued c) (hmin : LeastAmongIntegerGauges c) :
    ∀ x : ℝ, 0 < x → gaugeCost c x = Jcost x := by
  intro x _
  rw [unit_forced hsix hc hcar hmin]
  simp

/-- The cost of the first distinction is then determined, not stipulated: telling one from
two costs a quarter. -/
theorem cost_of_the_first_distinction (hsix : SixExponentialsTraceInput) {c : ℝ} (hc : 0 < c)
    (hcar : CarrierValued c) (hmin : LeastAmongIntegerGauges c) :
    gaugeCost c 2 = 1 / 4 := by
  rw [cost_is_Jcost hsix hc hcar hmin 2 (by norm_num)]
  norm_num [Jcost]

/-! ## The intrinsic form: least among the carrier-valued gauges

`LeastAmongIntegerGauges` names its competitor class by an arithmetic property of the
exponent, which invites the objection that the class was chosen to make the answer come out.
The objection is answerable: take the competitors to be exactly the gauges satisfying the same
condition imposed on the subject, carrier-valuedness. Nothing is then hand-picked, and the
statement reads as what it is, that the unit is the cheapest δ-native cost there is.

Restricting to carrier-valued competitors is not a weakening that rescues leastness either.
Over ALL real scales no least member exists, since halving always undercuts
(`no_least_gauge_member`), and the infimum is the cost that charges nothing. Carrier-valuedness
is what makes least cost a selection principle rather than a descent to zero, which is the
precise sense in which the discrete carrier, and not the completion, is what fixes the unit. -/

/-- Least cost among the carrier-valued gauges: the competitor class is defined by the very
condition imposed on the subject, so no class was chosen to suit the answer. -/
def LeastAmongCarrierValued (c : ℝ) : Prop :=
  ∀ d : ℝ, 0 < d → CarrierValued d → ∀ x : ℝ, 0 < x → x ≠ 1 → gaugeCost c x ≤ gaugeCost d x

/-- The unit scale is carrier-valued: `J` of a rational ratio is a rational. -/
theorem carrierValued_one : CarrierValued 1 := by
  intro n _ _
  refine ⟨((n : ℚ) + ((n : ℚ))⁻¹) / 2 - 1, ?_⟩
  simp only [gaugeCost, Jcost, Real.rpow_one]
  push_cast
  ring

/-- The unit scale is least among the integer gauges. -/
theorem leastAmongIntegerGauges_one : LeastAmongIntegerGauges 1 := by
  intro m hm x hx hx1
  rw [gaugeCost_one, gaugeCost_natCast]
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hm1 : m = 1 := by omega
    subst hm1
    simp
  · exact le_of_lt (jcost_lt_pow x hx hx1 m hm2)

/-- **The unit is forced, intrinsic form.** A positive scale that is carrier-valued and
charges no more than any carrier-valued gauge is the unit scale. Only one competitor is
needed to run the argument, the unit itself, so the conclusion does not depend on knowing
the competitor class in advance. -/
theorem unit_forced_intrinsic (hsix : SixExponentialsTraceInput) {c : ℝ} (hc : 0 < c)
    (hcar : CarrierValued c) (hmin : LeastAmongCarrierValued c) : c = 1 := by
  obtain ⟨k, hk1, hck⟩ :=
    exponent_is_positive_integer hsix hc (trace_rat_of_carrierValued hcar)
  by_contra hne
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · exact absurd (by rw [hck, show k = 1 by omega]; norm_num) hne
    · exact hge
  have hle := hmin 1 one_pos carrierValued_one 2 (by norm_num) (by norm_num)
  rw [hck, gaugeCost_one, gaugeCost_natCast] at hle
  exact absurd hle (not_le.mpr (jcost_lt_pow 2 (by norm_num) (by norm_num) k hk2))

/-- **The hypothesis set is satisfiable, and satisfied at exactly one scale.** Stated as an
equivalence so that no vacuity reading is available: the conditions are not jointly empty,
they hold of the unit, and they hold of nothing else. -/
theorem carrierValued_and_least_iff_unit (hsix : SixExponentialsTraceInput) {c : ℝ}
    (hc : 0 < c) :
    (CarrierValued c ∧ LeastAmongCarrierValued c) ↔ c = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact unit_forced_intrinsic hsix hc h1 h2
  · rintro rfl
    refine ⟨carrierValued_one, ?_⟩
    intro d hd hdcar x hx hx1
    obtain ⟨k, hk1, hdk⟩ :=
      exponent_is_positive_integer hsix hd (trace_rat_of_carrierValued hdcar)
    rw [gaugeCost_one, hdk, gaugeCost_natCast]
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · have hk1' : k = 1 := by omega
      subst hk1'
      simp
    · exact le_of_lt (jcost_lt_pow x hx hx1 k hk2)

/-- **δ's open question, answered.** The log-curvature of the cost at the unit is exactly one,
derived from the carrier rather than stipulated on the completion. The scale that was the one
residual free parameter of the stratification theorem is the cheapest δ-native cost, and there
is only one of those. -/
theorem logCurvature_forced_intrinsic (hsix : SixExponentialsTraceInput) {c : ℝ} (hc : 0 < c)
    (hcar : CarrierValued c) (hmin : LeastAmongCarrierValued c) :
    deriv (deriv (fun t => Real.cosh (c * t) - 1)) 0 = 1 := by
  rw [Foundation.PrimitiveRecognitionCalculus.Calibration.logCurvature c,
    unit_forced_intrinsic hsix hc hcar hmin]
  norm_num

/-! ## A structural alternative to minimality

Least cost invites a fair objection: a cost is a yardstick, and a system does not choose the
smallest yardstick for itself. There is a selection principle that minimizes nothing and gives
the same answer, which is worth having because it shows the answer is a property of the carrier
rather than of the principle used to pick.

Every carrier-compatible member reads a ratio through the character `x ↦ x ^ k`, an
endomorphism of the multiplicative group of positive rationals. For `k = 1` that endomorphism
is the identity, hence an automorphism; for every `k ≥ 2` it is proper, since two is not a
`k`-th power of a rational. So the unit member is the unique one whose character is an
automorphism of the carrier: the only cost that reads the carrier itself rather than a
coarsening of it. Least cost is then a corollary rather than a postulate. -/

/-- The cost's character is an automorphism of the carrier: every positive rational is the
`c`-th power of a positive rational, so the cost reads the whole carrier and not a proper
subgroup of it. -/
def CharacterIsAutomorphism (c : ℝ) : Prop :=
  ∀ q : ℚ, 0 < q → ∃ r : ℚ, 0 < r ∧ ((r : ℝ)) ^ c = (q : ℝ)

/-- The `k`-th power map is onto the positive rationals exactly when `k = 1`. Above one it
misses two, by the 2-adic valuation. -/
theorem powerMap_surjective_iff (k : ℕ) (hk : 1 ≤ k) :
    (∀ q : ℚ, 0 < q → ∃ r : ℚ, 0 < r ∧ r ^ k = q) ↔ k = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    obtain ⟨r, hrpos, hr⟩ := h 2 (by norm_num)
    have hrne : r ≠ 0 := ne_of_gt hrpos
    have hv : padicValRat 2 (r ^ k) = (k : ℕ) * padicValRat 2 r := padicValRat.pow hrne
    have hself : padicValRat 2 ((2 : ℚ)) = 1 := by
      have h2 := padicValRat.self (p := 2) (by norm_num)
      norm_num at h2
      exact h2
    rw [hr, hself] at hv
    have hdvd : (k : ℤ) ∣ 1 := ⟨padicValRat 2 r, hv⟩
    have : (k : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) hdvd
    exact_mod_cast this
  · rintro rfl
    intro q hq
    exact ⟨q, hq, pow_one q⟩

/-- **The unit is forced, with no appeal to least cost.** A carrier-compatible scale whose
character is an automorphism of the carrier is the unit scale. Same conclusion as
`unit_forced_intrinsic`, reached by a structural condition instead of a variational one. -/
theorem unit_forced_by_automorphism (hsix : SixExponentialsTraceInput) {c : ℝ} (hc : 0 < c)
    (hcar : CarrierValued c) (haut : CharacterIsAutomorphism c) : c = 1 := by
  obtain ⟨k, hk1, hck⟩ :=
    exponent_is_positive_integer hsix hc (trace_rat_of_carrierValued hcar)
  have hsurj : ∀ q : ℚ, 0 < q → ∃ r : ℚ, 0 < r ∧ r ^ k = q := by
    intro q hq
    obtain ⟨r, hrpos, hr⟩ := haut q hq
    refine ⟨r, hrpos, ?_⟩
    rw [hck, Real.rpow_natCast] at hr
    exact_mod_cast hr
  have hk : k = 1 := (powerMap_surjective_iff k hk1).mp hsurj
  rw [hck, hk]
  norm_num

/-- **The two selection principles agree.** For a carrier-compatible scale, being least and
having an automorphism character are the same condition, and both hold of exactly the unit.
Two independent principles reaching one answer is evidence the answer belongs to the carrier
and not to the principle. -/
theorem automorphism_iff_least (hsix : SixExponentialsTraceInput) {c : ℝ} (hc : 0 < c)
    (hcar : CarrierValued c) :
    CharacterIsAutomorphism c ↔ LeastAmongCarrierValued c := by
  constructor
  · intro haut
    have h1 : c = 1 := unit_forced_by_automorphism hsix hc hcar haut
    subst h1
    exact ((carrierValued_and_least_iff_unit hsix hc).mpr rfl).2
  · intro hmin
    have h1 : c = 1 := unit_forced_intrinsic hsix hc hcar hmin
    subst h1
    intro q hq
    exact ⟨q, hq, by simp⟩

/-! ## Both hypotheses are load-bearing

A selection theorem whose hypotheses have not been shown to discriminate has not been tested.
The next two results exhibit, for each hypothesis, a scale that satisfies the other one and is
not the unit. So neither condition can be dropped, and neither is doing the whole job alone. -/

/-- **Carrier-valuedness alone does not force the unit.** The exponent-two gauge charges a
rational at every rational ratio, so it passes carrier-valuedness while differing from `J`.
Least cost is therefore load-bearing. -/
theorem carrierValued_two : CarrierValued ((2 : ℕ) : ℝ) := by
  intro n _ _
  refine ⟨((n : ℚ) ^ 2 + ((n : ℚ) ^ 2)⁻¹) / 2 - 1, ?_⟩
  simp only [gaugeCost, Jcost, Real.rpow_natCast]
  push_cast
  ring

/-- **Least cost alone does not force the unit.** The half-scale gauge undercuts every integer
gauge, so it passes least cost while differing from `J`. Carrier-valuedness is therefore
load-bearing. -/
theorem leastAmongIntegerGauges_half : LeastAmongIntegerGauges (1 / 2) := by
  intro m hm x hx hx1
  have hhalf : gaugeCost (1 / 2) x < Jcost x := by
    have h := no_least_gauge_member x hx hx1 1 one_pos
    simpa [gaugeCost] using h
  have hstep : Jcost x ≤ Jcost (x ^ m) := by
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have hm1 : m = 1 := by omega
      subst hm1
      simp
    · exact le_of_lt (jcost_lt_pow x hx hx1 m hm2)
  rw [gaugeCost_natCast]
  exact le_of_lt (lt_of_lt_of_le hhalf hstep)

/-- And the half-scale gauge is not carrier-valued: it charges an irrational amount for the
ratio two. This is the mechanism by which the arithmetic step excludes non-integer scales. -/
theorem half_not_carrierValued : ¬ CarrierValued (1 / 2) := by
  intro h
  obtain ⟨q, hq⟩ := h 2 (le_refl 2) (by norm_num)
  have hsqrt : ((2 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  have hcost : (Real.sqrt 2 + (Real.sqrt 2)⁻¹) / 2 - 1 = (q : ℝ) := by
    have := hq
    simp only [gaugeCost, Jcost] at this
    rw [hsqrt] at this
    exact this
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by
    intro h0
    rw [h0] at h2
    norm_num at h2
  have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    field_simp [hne]
    linarith [h2]
  rw [hinv] at hcost
  have hrat : Real.sqrt 2 = ((4 * q + 4) / 3 : ℚ) := by
    push_cast
    linarith [hcost]
  exact irrational_sqrt_two ⟨(4 * q + 4) / 3, hrat.symm⟩

/-! ## Audits -/

#print axioms trace_rat_of_carrierValued
#print axioms unit_forced
#print axioms unit_forced_intrinsic
#print axioms carrierValued_and_least_iff_unit
#print axioms carrierValued_one
#print axioms leastAmongIntegerGauges_one
#print axioms logCurvature_forced
#print axioms logCurvature_forced_intrinsic
#print axioms powerMap_surjective_iff
#print axioms unit_forced_by_automorphism
#print axioms automorphism_iff_least
#print axioms cost_is_Jcost
#print axioms cost_of_the_first_distinction
#print axioms carrierValued_two
#print axioms leastAmongIntegerGauges_half
#print axioms half_not_carrierValued

end UnitForcedFromCarrier
end Cost
end IndisputableMonolith
