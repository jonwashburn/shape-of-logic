import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.RowZeroReconciliation
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCCalibrationIndependence
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCCalibrationTarget

/-!
# Kernel premise closure census: row 2, calibration

Row zero split the cost unit into two coordinates, an amplitude (row 1, a
gauge) and an exponent. This module is the necessary-reasons census for the
exponent coordinate: the kernel's premise `IsCalibrated F`, which says the
log-curvature of the cost at the unit ratio is exactly one.

## Stratum fact first

On real-valued cost laws alone the exponent is free: every `costLambda c`
with `c > 0` is reciprocal, normalized, continuous, and satisfies the
composition law (`composition_law_admits_full_scale_family`), and its
log-curvature is `c ^ 2` (`calibration_value_costLambda`). That wall stands
and is not re-walked here. The census works on the other side of it, where
the cost lives on the carrier that distinction generates, the positive
rationals, and the continuum is the completion.

## The rows

The target is assumed required: the exponent is one. Reasons it would be
unavoidable, each proved or refuted alone:

1. **Carrier first (generative order inverted).** The cost is a function on
   the carrier `ℚ_{>0}` with values in the carrier; the continuous cost on
   `ℝ_{>0}` is its extension. Row 2.1 proves the extension is unique
   (`unique_continuous_extension`) and that carrier-valuedness at the bases
   `2..5`, the postulate `UnitForcedFromCarrier.CarrierValued`, is a theorem
   about the extension rather than a condition on the continuous member
   (`carrierValued_of_carrierNative`). Decoy: without continuity two
   extensions of the same carrier cost differ
   (`extension_not_unique_without_continuity`).
2. **Integer exponent on the carrier.** If the character is an integer power
   `q ↦ q ^ k`, it is an automorphism of `ℚ_{>0}` exactly for `k = ±1`
   (`zpow_surjective_posRat_iff`), and reciprocity identifies the two signs
   (`gaugeCost_neg_one`). So on the carrier the exponent is forced to one
   with no transcendence input, provided the exponent is already known to be
   an integer (`integer_character_automorphism_forces_unit`).
3. **From a real exponent to an integer one.** Howe's theorem makes a
   monotone character a real power `n ^ c`. Rationality of the traces at
   three bases plus the six exponentials theorem makes `c` rational, and the
   2-adic valuation makes it an integer (`Cost.TraceRationalExponent`). The
   six exponentials input is not in Mathlib (checked 2026-09-01: no
   statement of Six Exponentials, Gelfond--Schneider, or Four Exponentials)
   and stays a named EXTERNAL theorem in the ledger. It cannot be weakened
   to two bases: that form is the four exponentials conjecture, which is open.
   This row is therefore not a Lean theorem; it is the exact location of the
   one classical import, stated so the ledger can price it.
4. **Why the automorphism principle bites at the carrier and nowhere else.**
   On the continuum every power map is an automorphism of `ℝ_{>0}`
   (`continuum_power_is_automorphism`), so the principle selects nothing
   there. It selects on the carrier because the carrier has an indivisible
   element (`indivisible_element_forces_unit_exponent`, over an unknown
   commutative group). This is the census's answer to "why does a
   qualitative principle pin a number": the number is a property of the
   carrier's arithmetic, and the principle only reads it off.
5. **Invertibility versus reachability.** Two candidate reasons for the
   automorphism principle, that posting can be undone (injective) and that
   every carrier ratio is a reading (surjective), collapse to one for power
   characters: injectivity is free (`power_character_injective`), so the
   principle's whole content is reachability.

## Verdict

**DERIVED at `traceClosure`** from two qualitative postulates, carrier-native
cost and automorphism character, plus one named EXTERNAL theorem. Neither
postulate names a number. Both are load-bearing, with countermodels re-exported
from `Cost.UnitForcedFromCarrier` and sharpened here: the exponent-two gauge is
carrier-native and not an automorphism; the half gauge is an automorphism of
the continuum and not carrier-native.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace CalibrationCensus

open Cost
open Cost.FunctionalEquation
open Cost.UnitForcedFromCarrier
open PrimitiveRecognitionCalculus
open PrimitiveRecognitionCalculus.PRCJCost

noncomputable section

/-! ## Stratum fact: the wall on real-valued laws (re-export) -/

/-- **The wall.** Every positive exponent passes every non-calibration cost
law on the reals, and the log-curvature is the square of the exponent. Real-
valued laws do not pin the unit. -/
theorem wall_real_laws_do_not_pin_exponent (c : ℝ) (hc : 0 < c) :
    IsReciprocalCost (costLambda c) ∧ IsNormalized (costLambda c) ∧
      SatisfiesCompositionLaw (costLambda c) ∧
      deriv (deriv (G (costLambda c))) 0 = c ^ 2 :=
  ⟨(composition_law_admits_full_scale_family c hc).1,
    (composition_law_admits_full_scale_family c hc).2.1,
    (composition_law_admits_full_scale_family c hc).2.2.1,
    calibration_value_costLambda c⟩

/-- The gauge member in the carrier file and the gauge member in the
calibration file are the same function on the positive axis. -/
theorem gaugeCost_eq_costLambda (c x : ℝ) (hx : 0 < x) :
    gaugeCost c x = costLambda c x := by
  simp only [gaugeCost, Jcost, costLambda]
  rw [Real.rpow_neg (le_of_lt hx)]

/-- Their log-profiles agree everywhere (the log-profile only reads positive
arguments). -/
theorem G_gaugeCost_eq_G_costLambda (c : ℝ) :
    G (gaugeCost c) = G (costLambda c) := by
  funext t
  simp only [G]
  exact gaugeCost_eq_costLambda c _ (Real.exp_pos t)

/-- **Calibration of a gauge member is the statement `c = 1`.** -/
theorem isCalibrated_gaugeCost_iff {c : ℝ} (hc : 0 < c) :
    IsCalibrated (gaugeCost c) ↔ c = 1 := by
  unfold IsCalibrated
  rw [G_gaugeCost_eq_G_costLambda, calibration_value_costLambda]
  constructor
  · intro h
    nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 1), hc]
  · rintro rfl
    norm_num

/-! ## Row 2.1: carrier first, unique continuous extension -/

/-- The positive rationals, as a subset of the reals. -/
def posRatSet : Set ℝ := {x | ∃ q : ℚ, 0 < q ∧ (q : ℝ) = x}

/-- The positive rationals are dense in the positive reals. -/
theorem Ioi_subset_closure_posRatSet : Set.Ioi (0 : ℝ) ⊆ closure posRatSet := by
  intro x hx
  have hx' : (0 : ℝ) < x := hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (x - ε) (x / 2) < x by
    apply max_lt <;> linarith)
  have hqpos : (0 : ℚ) < q := by
    have : x / 2 < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq1
    have : (0 : ℝ) < (q : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨(q : ℝ), ⟨q, hqpos, rfl⟩, ?_⟩
  rw [Real.dist_eq, abs_sub_lt_iff]
  have : x - ε < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq1
  constructor <;> linarith

theorem posRatSet_subset_Ioi : posRatSet ⊆ Set.Ioi (0 : ℝ) := by
  rintro x ⟨q, hq, rfl⟩
  show (0 : ℝ) < (q : ℝ)
  exact_mod_cast hq

/-- **Unique continuous extension.** Two costs continuous on the positive
axis that agree on every positive rational agree on every positive real. -/
theorem unique_continuous_extension (F G' : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Ioi 0)) (hG : ContinuousOn G' (Set.Ioi 0))
    (h : ∀ q : ℚ, 0 < q → F q = G' q) :
    Set.EqOn F G' (Set.Ioi 0) := by
  have hs : Set.EqOn F G' posRatSet := by
    rintro x ⟨q, hq, rfl⟩
    exact h q hq
  exact hs.of_subset_closure hF hG posRatSet_subset_Ioi Ioi_subset_closure_posRatSet

/-- The native cost on the carrier: a rational-valued function of a rational
ratio, at integer exponent `k`. This is the object δ's cost laws are about;
the continuous cost is downstream of it. -/
def nativeCost (k : ℤ) (q : ℚ) : ℚ := (q ^ k + q ^ (-k)) / 2 - 1

/-- The gauge member at a natural exponent extends the native cost. -/
theorem gaugeCost_extends_nativeCost (k : ℕ) (q : ℚ) (hq : 0 < q) :
    gaugeCost (k : ℝ) (q : ℝ) = (nativeCost (k : ℤ) q : ℝ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  simp only [gaugeCost, Jcost, nativeCost]
  rw [Real.rpow_natCast]
  push_cast
  rw [zpow_neg, zpow_natCast]

/-- **Carrier-first.** Any cost continuous on the positive axis that
restricts to the native cost at exponent `k` on the carrier is the gauge
member at exponent `k`. The continuous cost is determined by the carrier
cost; there is nothing on the continuum left to choose. -/
theorem continuous_extension_of_nativeCost (k : ℕ) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Ioi 0))
    (hnat : ∀ q : ℚ, 0 < q → F q = (nativeCost (k : ℤ) q : ℝ)) :
    Set.EqOn F (gaugeCost (k : ℝ)) (Set.Ioi 0) := by
  apply unique_continuous_extension F (gaugeCost (k : ℝ)) hF
  · -- `gaugeCost k` is continuous on the positive axis.
    have h1 : ContinuousOn (fun x : ℝ => x ^ (k : ℝ)) (Set.Ioi 0) := by
      intro x hx
      exact (Real.continuousAt_rpow_const x (k : ℝ) (Or.inl (ne_of_gt hx))).continuousWithinAt
    have h2 : ContinuousOn Jcost (Set.Ioi 0) := by
      intro x hx
      have hx' : (0 : ℝ) < x := hx
      unfold Jcost
      apply ContinuousAt.continuousWithinAt
      have : ContinuousAt (fun y : ℝ => (y + y⁻¹) / 2 - 1) x := by
        apply ContinuousAt.sub
        · apply ContinuousAt.div_const
          apply ContinuousAt.add continuousAt_id
          exact continuousAt_inv₀ (ne_of_gt hx')
        · exact continuousAt_const
      exact this
    have hmaps : Set.MapsTo (fun x : ℝ => x ^ (k : ℝ)) (Set.Ioi 0) (Set.Ioi 0) :=
      fun y hy => Real.rpow_pos_of_pos hy _
    exact h2.comp h1 hmaps
  · intro q hq
    rw [hnat q hq, gaugeCost_extends_nativeCost k q hq]

/-- A cost is carrier-native when it restricts on the carrier to a
carrier-valued function. This is the qualitative postulate that replaces
`CarrierValued`: no bases, no numerals. -/
def CarrierNative (F : ℝ → ℝ) : Prop :=
  ∃ f : ℚ → ℚ, ∀ q : ℚ, 0 < q → F q = (f q : ℝ)

/-- **Carrier-valuedness at the bases is a theorem about a carrier-native
cost**, not a separate postulate. -/
theorem carrierValued_of_carrierNative {c : ℝ} (h : CarrierNative (gaugeCost c)) :
    CarrierValued c := by
  obtain ⟨f, hf⟩ := h
  intro n hn _
  refine ⟨f n, ?_⟩
  have := hf (n : ℚ) (by exact_mod_cast (show 0 < n by omega))
  simpa using this

/-- The integer gauges are carrier-native. -/
theorem carrierNative_nat (k : ℕ) : CarrierNative (gaugeCost (k : ℝ)) :=
  ⟨nativeCost (k : ℤ), fun q hq => gaugeCost_extends_nativeCost k q hq⟩

/-- **Decoy for row 2.1.** Without continuity the carrier cost has more than
one extension: `J` and `J` shifted by one on the irrationals restrict to the
same carrier cost and differ at `√2`. Continuity is load-bearing. -/
theorem extension_not_unique_without_continuity :
    ∃ F G' : ℝ → ℝ,
      (∀ q : ℚ, 0 < q → F q = (nativeCost 1 q : ℝ)) ∧
      (∀ q : ℚ, 0 < q → G' q = (nativeCost 1 q : ℝ)) ∧
      ¬ Set.EqOn F G' (Set.Ioi 0) := by
  classical
  refine ⟨gaugeCost 1, fun x => if ∃ q : ℚ, (q : ℝ) = x then gaugeCost 1 x else gaugeCost 1 x + 1,
    ?_, ?_, ?_⟩
  · intro q hq
    have := gaugeCost_extends_nativeCost 1 q hq
    simpa using this
  · intro q hq
    have h := gaugeCost_extends_nativeCost 1 q hq
    simp only [Nat.cast_one] at h
    have hex : ∃ r : ℚ, (r : ℝ) = (q : ℝ) := ⟨q, rfl⟩
    show (if ∃ r : ℚ, (r : ℝ) = (q : ℝ) then gaugeCost 1 q else gaugeCost 1 q + 1) =
      (nativeCost 1 q : ℝ)
    rw [if_pos hex]
    simpa using h
  · intro heq
    have h := heq (show Real.sqrt 2 ∈ Set.Ioi (0 : ℝ) from Real.sqrt_pos.mpr (by norm_num))
    have hirr : ¬ ∃ q : ℚ, (q : ℝ) = Real.sqrt 2 := by
      rintro ⟨q, hq⟩
      exact irrational_sqrt_two ⟨q, hq⟩
    have h' : gaugeCost 1 (Real.sqrt 2) =
        (if ∃ r : ℚ, (r : ℝ) = Real.sqrt 2 then gaugeCost 1 (Real.sqrt 2)
          else gaugeCost 1 (Real.sqrt 2) + 1) := h
    rw [if_neg hirr] at h'
    linarith

/-! ## Row 2.2: on the carrier the automorphisms are the exponents `±1` -/

/-- The integer power map on the positive rationals is onto exactly for
`k = 1` and `k = -1`. Every other exponent misses the ratio two (or its
inverse). -/
theorem zpow_surjective_posRat_iff (k : ℤ) (hk : k ≠ 0) :
    (∀ q : ℚ, 0 < q → ∃ r : ℚ, 0 < r ∧ r ^ k = q) ↔ (k = 1 ∨ k = -1) := by
  constructor
  · intro h
    rcases lt_or_gt_of_ne hk with hneg | hpos
    · -- k < 0: reduce to the natural power `-k`.
      obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨k.natAbs, by omega⟩
      have hn1 : 1 ≤ n := by omega
      have hsurj : ∀ q : ℚ, 0 < q → ∃ r : ℚ, 0 < r ∧ r ^ n = q := by
        intro q hq
        obtain ⟨r, hr, hrk⟩ := h q⁻¹ (inv_pos.mpr hq)
        refine ⟨r, hr, ?_⟩
        rw [hn, zpow_neg, zpow_natCast] at hrk
        have := congrArg (·⁻¹) hrk
        simpa using this
      have := (powerMap_surjective_iff n hn1).mp hsurj
      right; omega
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.natAbs, by omega⟩
      have hn1 : 1 ≤ n := by omega
      have hsurj : ∀ q : ℚ, 0 < q → ∃ r : ℚ, 0 < r ∧ r ^ n = q := by
        intro q hq
        obtain ⟨r, hr, hrk⟩ := h q hq
        refine ⟨r, hr, ?_⟩
        rw [hn, zpow_natCast] at hrk
        exact hrk
      have := (powerMap_surjective_iff n hn1).mp hsurj
      left; omega
  · rintro (rfl | rfl)
    · intro q hq; exact ⟨q, hq, zpow_one q⟩
    · intro q hq
      refine ⟨q⁻¹, inv_pos.mpr hq, ?_⟩
      simp

/-- **Reciprocity identifies the two automorphisms.** The exponent `-1`
gauge is the unit gauge: reading a ratio or its inverse costs the same.
This is where the sign freedom of `Aut(ℤ) = {±1}` is spent, by the two-
sidedness of distinction and nothing else. -/
theorem gaugeCost_neg_one (x : ℝ) (_hx : 0 < x) :
    gaugeCost (-1) x = gaugeCost 1 x := by
  simp only [gaugeCost, Jcost, Real.rpow_one, Real.rpow_neg_one]
  rw [inv_inv, add_comm]

/-- **Integer exponent plus automorphism forces the unit, with no
transcendence.** If the character is known to be an integer power and is an
automorphism of the carrier, the cost is `J`. -/
theorem integer_character_automorphism_forces_unit (k : ℤ) (hk : k ≠ 0)
    (haut : ∀ q : ℚ, 0 < q → ∃ r : ℚ, 0 < r ∧ r ^ k = q) :
    ∀ x : ℝ, 0 < x → gaugeCost (k : ℝ) x = Jcost x := by
  intro x hx
  rcases (zpow_surjective_posRat_iff k hk).mp haut with rfl | rfl
  · simp
  · push_cast
    rw [gaugeCost_neg_one x hx]
    simp

/-! ## Row 2.3: the classical import, located

`Cost.TraceRationalExponent.exponent_is_positive_integer` is the bridge from a
real exponent to an integer one. Its single hypothesis is the six exponentials
input. This row re-exports the bridge under its census label so the ledger
prices exactly one EXTERNAL theorem, and records that Mathlib carries no form
of it (grep of `Mathlib/` for Six Exponentials, Gelfond, Schneider, Four
Exponentials on 2026-09-01: no hits). -/

/-- **The one classical import, isolated.** Given the six exponentials input,
a carrier-valued positive exponent is a positive integer. Everything after
this point in the chain is elementary. -/
theorem exponent_integer_given_sixExponentials
    (hsix : TraceRationalExponent.SixExponentialsTraceInput)
    {c : ℝ} (hc : 0 < c) (hcar : CarrierValued c) :
    ∃ k : ℕ, 1 ≤ k ∧ c = (k : ℝ) :=
  TraceRationalExponent.exponent_is_positive_integer hsix hc (trace_rat_of_carrierValued hcar)

/-! ## Row 2.4: why the automorphism principle bites at the carrier -/

/-- **On the continuum every power map is an automorphism.** For every `c > 0`
and every positive real `y` there is a positive real `x` with `x ^ c = y`. So
the automorphism principle, applied to `ℝ_{>0}`, selects nothing: the
principle has content only because the carrier is not the continuum. -/
theorem continuum_power_is_automorphism (c : ℝ) (hc : 0 < c) :
    ∀ y : ℝ, 0 < y → ∃ x : ℝ, 0 < x ∧ x ^ c = y := by
  intro y hy
  refine ⟨y ^ (1 / c), Real.rpow_pos_of_pos hy _, ?_⟩
  rw [← Real.rpow_mul (le_of_lt hy)]
  have : 1 / c * c = 1 := by field_simp
  rw [this, Real.rpow_one]

/-- **Over an unknown commutative carrier.** If some element is not a `k`-th
power for any `k ≥ 2` (an indivisible element), then the `k`-th power map is
onto exactly when `k = 1`. This is the shape of the carrier's arithmetic that
the automorphism principle reads. -/
theorem indivisible_element_forces_unit_exponent {G : Type*} [CommGroup G]
    (g : G) (hg : ∀ k : ℕ, 2 ≤ k → ∀ r : G, r ^ k ≠ g)
    (k : ℕ) (hk : 1 ≤ k) :
    Function.Surjective (fun r : G => r ^ k) ↔ k = 1 := by
  constructor
  · intro hs
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    obtain ⟨r, hr⟩ := hs g
    exact hg k hk2 r hr
  · rintro rfl
    intro y
    exact ⟨y, pow_one y⟩

/-- **Decoy for row 2.4.** In a divisible carrier every power map is onto, so
the row's hypothesis is what does the work. The positive reals are the
witness; the additive rationals would do as well. -/
theorem divisible_carrier_every_power_onto :
    ∀ k : ℕ, 1 ≤ k → ∀ y : ℝ, 0 < y → ∃ x : ℝ, 0 < x ∧ x ^ k = y := by
  intro k hk y hy
  obtain ⟨x, hx, hxk⟩ := continuum_power_is_automorphism (k : ℝ) (by exact_mod_cast hk) y hy
  refine ⟨x, hx, ?_⟩
  rw [← Real.rpow_natCast]
  exact hxk

/-- The carrier `ℚ_{>0}` has an indivisible element: two is no proper power. -/
theorem two_is_indivisible_in_posRat :
    ∀ k : ℕ, 2 ≤ k → ∀ r : ℚ, 0 < r → r ^ k ≠ 2 := by
  intro k hk r hr hrk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrne : r ≠ 0 := ne_of_gt hr
  have hv : padicValRat 2 (r ^ k) = (k : ℕ) * padicValRat 2 r := padicValRat.pow hrne
  have hself : padicValRat 2 ((2 : ℚ)) = 1 := by
    have h2 := padicValRat.self (p := 2) (by norm_num)
    norm_num at h2
    exact h2
  rw [hrk, hself] at hv
  have hdvd : (k : ℤ) ∣ 1 := ⟨padicValRat 2 r, hv⟩
  have : (k : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) hdvd
  omega

/-! ## Row 2.5: invertibility and reachability are one reason -/

/-- Every nonzero power character is injective on the positive reals, so
"posting can be undone" is free and adds nothing to "every ratio is a
reading". -/
theorem power_character_injective (c : ℝ) (hc : c ≠ 0) :
    ∀ x y : ℝ, 0 < x → 0 < y → x ^ c = y ^ c → x = y := by
  intro x y hx hy h
  have := congrArg (fun z : ℝ => z ^ (1 / c)) h
  simp only at this
  rw [← Real.rpow_mul (le_of_lt hx), ← Real.rpow_mul (le_of_lt hy)] at this
  have hcc : c * (1 / c) = 1 := by field_simp
  rw [hcc, Real.rpow_one, Real.rpow_one] at this
  exact this

/-! ## The verdict: DERIVED at `traceClosure` -/

/-- **Row 2 verdict.** A positive exponent whose gauge member is carrier-
native and whose character is an automorphism of the carrier is the unit, and
the cost is calibrated. Two qualitative postulates and one named external
theorem; no numeral is assumed. -/
theorem calibration_derived
    (hsix : TraceRationalExponent.SixExponentialsTraceInput)
    {c : ℝ} (hc : 0 < c)
    (hnat : CarrierNative (gaugeCost c))
    (haut : CharacterIsAutomorphism c) :
    c = 1 ∧ IsCalibrated (gaugeCost c) := by
  have h1 : c = 1 :=
    unit_forced_by_automorphism hsix hc (carrierValued_of_carrierNative hnat) haut
  exact ⟨h1, (isCalibrated_gaugeCost_iff hc).mpr h1⟩

/-- The verdict at its stratum. The continuum enters only as the completion
in which the extension lives; the selection is made on the carrier. -/
theorem calibration_derived_tagged
    (hsix : TraceRationalExponent.SixExponentialsTraceInput) :
    PublicSpine.Tagged StrengthTag.traceClosure
      (∀ c : ℝ, 0 < c → CarrierNative (gaugeCost c) → CharacterIsAutomorphism c →
        IsCalibrated (gaugeCost c)) where
  holds := fun _ hc hnat haut => (calibration_derived hsix hc hnat haut).2

/-! ## Both postulates load-bearing, sharpened -/

/-- **Dropping the automorphism postulate.** The exponent-two gauge is
carrier-native and not calibrated. -/
theorem carrierNative_two_not_calibrated :
    CarrierNative (gaugeCost ((2 : ℕ) : ℝ)) ∧
      ¬ CharacterIsAutomorphism ((2 : ℕ) : ℝ) ∧
      ¬ IsCalibrated (gaugeCost ((2 : ℕ) : ℝ)) := by
  refine ⟨carrierNative_nat 2, ?_, ?_⟩
  · intro h
    obtain ⟨r, hr, hrk⟩ := h 2 (by norm_num)
    rw [Real.rpow_natCast] at hrk
    have hrk' : r ^ 2 = 2 := by exact_mod_cast hrk
    exact two_is_indivisible_in_posRat 2 le_rfl r hr hrk'
  · rw [isCalibrated_gaugeCost_iff (by norm_num)]
    norm_num

/-- **Dropping the carrier-native postulate.** The half gauge has an
automorphism character on the continuum, is not carrier-native, and is not
calibrated. -/
theorem half_automorphism_on_continuum_not_native :
    (∀ y : ℝ, 0 < y → ∃ x : ℝ, 0 < x ∧ x ^ (1 / 2 : ℝ) = y) ∧
      ¬ CarrierNative (gaugeCost (1 / 2)) ∧
      ¬ IsCalibrated (gaugeCost (1 / 2)) := by
  refine ⟨continuum_power_is_automorphism _ (by norm_num), ?_, ?_⟩
  · intro h
    exact half_not_carrierValued (carrierValued_of_carrierNative h)
  · rw [isCalibrated_gaugeCost_iff (by norm_num)]
    norm_num

/-- **The postulate set is inhabited at exactly one exponent.** -/
theorem native_and_automorphism_iff_unit
    (hsix : TraceRationalExponent.SixExponentialsTraceInput) {c : ℝ} (hc : 0 < c) :
    (CarrierNative (gaugeCost c) ∧ CharacterIsAutomorphism c) ↔ c = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact (calibration_derived hsix hc h1 h2).1
  · rintro rfl
    refine ⟨?_, ?_⟩
    · have := carrierNative_nat 1
      simpa using this
    · intro q hq
      exact ⟨q, hq, by simp⟩

/-! ## Certificate -/

structure CalibrationCensusCert : Prop where
  wall : ∀ c : ℝ, 0 < c → deriv (deriv (G (costLambda c))) 0 = c ^ 2
  unique_extension :
    ∀ F G' : ℝ → ℝ, ContinuousOn F (Set.Ioi 0) → ContinuousOn G' (Set.Ioi 0) →
      (∀ q : ℚ, 0 < q → F q = G' q) → Set.EqOn F G' (Set.Ioi 0)
  extension_decoy :
    ∃ F G' : ℝ → ℝ,
      (∀ q : ℚ, 0 < q → F q = (nativeCost 1 q : ℝ)) ∧
      (∀ q : ℚ, 0 < q → G' q = (nativeCost 1 q : ℝ)) ∧
      ¬ Set.EqOn F G' (Set.Ioi 0)
  carrier_automorphisms :
    ∀ k : ℤ, k ≠ 0 →
      ((∀ q : ℚ, 0 < q → ∃ r : ℚ, 0 < r ∧ r ^ k = q) ↔ (k = 1 ∨ k = -1))
  continuum_selects_nothing : ∀ c : ℝ, 0 < c → ∀ y : ℝ, 0 < y → ∃ x : ℝ, 0 < x ∧ x ^ c = y
  verdict :
    TraceRationalExponent.SixExponentialsTraceInput →
      ∀ c : ℝ, 0 < c → CarrierNative (gaugeCost c) → CharacterIsAutomorphism c → c = 1
  automorphism_load_bearing : CarrierNative (gaugeCost ((2 : ℕ) : ℝ)) ∧
    ¬ CharacterIsAutomorphism ((2 : ℕ) : ℝ)
  native_load_bearing : ¬ CarrierNative (gaugeCost (1 / 2))

theorem calibrationCensusCert_holds : CalibrationCensusCert where
  wall := fun c _ => calibration_value_costLambda c
  unique_extension := unique_continuous_extension
  extension_decoy := extension_not_unique_without_continuity
  carrier_automorphisms := zpow_surjective_posRat_iff
  continuum_selects_nothing := continuum_power_is_automorphism
  verdict := fun hsix _ hc hnat haut => (calibration_derived hsix hc hnat haut).1
  automorphism_load_bearing :=
    ⟨carrierNative_two_not_calibrated.1, carrierNative_two_not_calibrated.2.1⟩
  native_load_bearing := half_automorphism_on_continuum_not_native.2.1

/-! ## Audits -/

#print axioms isCalibrated_gaugeCost_iff
#print axioms unique_continuous_extension
#print axioms continuous_extension_of_nativeCost
#print axioms extension_not_unique_without_continuity
#print axioms zpow_surjective_posRat_iff
#print axioms integer_character_automorphism_forces_unit
#print axioms continuum_power_is_automorphism
#print axioms indivisible_element_forces_unit_exponent
#print axioms calibration_derived
#print axioms calibration_derived_tagged
#print axioms native_and_automorphism_iff_unit
#print axioms calibrationCensusCert_holds

end

end CalibrationCensus
end KernelClosure
end Foundation
end IndisputableMonolith
