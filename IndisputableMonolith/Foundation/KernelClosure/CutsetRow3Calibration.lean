import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetHarness
import IndisputableMonolith.Foundation.KernelClosure.CalibrationNecessaryReasons

/-!
# Row 3 by cutset: the exponent as a count

Row 3 of the kernel purchase ledger is calibration. It is DERIVED at
`traceClosure` from two qualitative postulates, carrier-native cost and
automorphism character, plus one named EXTERNAL theorem (six exponentials),
which is used once: to turn a real exponent whose traces are rational into an
integer. This module asks what a cutset can do to the two postulates and to the
import.

## 3a, carrier-native: the blade is the sentence

The only floor word for "the cost lands in the carrier" is "postings are
counts": the cost of comparing two counts is a ratio of counts
(`CountPosted`). `countPosted_iff_carrierNative` proves this is extensionally
the postulate `CarrierNative` for nonnegative costs. So 3a is the harness's
known hole (`Blade := Sentence`) and is **not** a cutset closure. What the
equivalence does show is that `CarrierNative` is not a new sentence: it is the
T2 identification "recognition work is a count" (`BooleanUnitFromGeneratorCount`)
applied to the value of a comparison. The row's honest reading: one
identification, used twice.

## 3b, automorphism: the count route, no import

Read the exponent itself as a count of postings: the character `q ↦ q ^ k`
posts the comparison `k` times. Then the candidate class is `k : ℕ`, and

* the integer gauges are carrier-native automatically (`carrierNative_nat`);
* `k = 0` is the constant cost, excluded by nondegeneracy (row 2a);
* least count (B2) selects `k = 1` outright (`least_route`), and so does
  reachability (`automorphism_route`, via `powerMap_surjective_iff`): the two
  selection principles agree, with no transcendence input.

`countRow` inhabits the harness: floor `0 < k`, sentence "the character is an
automorphism of the carrier", blade "k is the least positive count" (B2, a floor
theorem), real object `1`, violator `2`.

## What this does and does not do to the import

The six exponentials theorem is **not discharged as a theorem**. It is bypassed
by a reading: on the count route the exponent is never a real number, so no
transcendence question arises. The ledger keeps its verdict (DERIVED with the
import) and gains the alternative: MODEL under the count reading, import-free.
Which of the two a paper states is a choice of premise, recorded as such.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row3Calibration

open Cost Cost.UnitForcedFromCarrier CalibrationCensus

noncomputable section

/-! ## 3a: postings are counts -/

/-- The cost of comparing two counts is a ratio of counts. The floor word for
"carrier-native": a posting is a count. -/
def CountPosted (F : ℝ → ℝ) : Prop :=
  ∀ q : ℚ, 0 < q → ∃ a b : ℕ, 0 < b ∧ F q = (a : ℝ) / b

/-- A nonnegative rational is a ratio of counts. -/
theorem rat_nonneg_eq_nat_div (r : ℚ) (hr : 0 ≤ r) :
    ∃ a b : ℕ, 0 < b ∧ (r : ℝ) = (a : ℝ) / b := by
  refine ⟨r.num.toNat, r.den, r.den_pos, ?_⟩
  have hnum : ((r.num.toNat : ℤ)) = r.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hr)
  rw [Rat.cast_def]
  congr 1
  exact_mod_cast hnum.symm

/-- **The blade is the sentence.** For a nonnegative cost, "postings are counts"
is extensionally `CarrierNative`. -/
theorem countPosted_iff_carrierNative (F : ℝ → ℝ) (hF : ∀ x : ℝ, 0 < x → 0 ≤ F x) :
    CountPosted F ↔ CarrierNative F := by
  constructor
  · intro h
    choose a b hb hF' using h
    refine ⟨fun q => if hq : 0 < q then ((a q hq : ℚ) / (b q hq : ℚ)) else 0, ?_⟩
    intro q hq
    simp only [dif_pos hq]
    rw [hF' q hq]
    push_cast
    rfl
  · rintro ⟨f, hf⟩ q hq
    have hpos : (0 : ℝ) < q := by exact_mod_cast hq
    have hnn : (0 : ℝ) ≤ (f q : ℝ) := by rw [← hf q hq]; exact hF q hpos
    obtain ⟨a, b, hb, hab⟩ := rat_nonneg_eq_nat_div (f q) (by exact_mod_cast hnn)
    exact ⟨a, b, hb, by rw [hf q hq, hab]⟩

theorem gaugeCost_nonneg (c x : ℝ) (hx : 0 < x) : 0 ≤ gaugeCost c x :=
  Jcost_nonneg (Real.rpow_pos_of_pos hx c)

/-- On the gauge family the equivalence holds at every exponent. -/
theorem countPosted_gauge_iff (c : ℝ) :
    CountPosted (gaugeCost c) ↔ CarrierNative (gaugeCost c) :=
  countPosted_iff_carrierNative _ (gaugeCost_nonneg c)

/-- The half gauge does not post counts: the census countermodel for 3a. -/
theorem half_not_countPosted : ¬ CountPosted (gaugeCost (1 / 2)) :=
  fun h => half_automorphism_on_continuum_not_native.2.1 ((countPosted_gauge_iff _).1 h)

/-- The integer gauges post counts. -/
theorem nat_countPosted (k : ℕ) : CountPosted (gaugeCost (k : ℝ)) :=
  (countPosted_gauge_iff _).2 (carrierNative_nat k)

/-! ## 3b: the count route -/

/-- The character of a count exponent is an automorphism exactly when the
count is one. -/
theorem characterIsAutomorphism_nat_iff (k : ℕ) (hk : 0 < k) :
    CharacterIsAutomorphism (k : ℝ) ↔ k = 1 := by
  rw [← powerMap_surjective_iff k hk]
  constructor
  · intro h q hq
    obtain ⟨r, hr, hrk⟩ := h q hq
    refine ⟨r, hr, ?_⟩
    rw [Real.rpow_natCast] at hrk
    exact_mod_cast hrk
  · intro h q hq
    obtain ⟨r, hr, hrk⟩ := h q hq
    refine ⟨r, hr, ?_⟩
    rw [Real.rpow_natCast]
    exact_mod_cast hrk

/-- **Reachability route.** A count exponent whose character reaches the whole
carrier is the unit, and the cost is `J`. No transcendence input. -/
theorem automorphism_route (k : ℕ) (hk : 0 < k) (haut : CharacterIsAutomorphism (k : ℝ)) :
    ∀ x : ℝ, 0 < x → gaugeCost (k : ℝ) x = Jcost x := by
  have h1 := (characterIsAutomorphism_nat_iff k hk).1 haut
  subst h1
  intro x _
  simp

/-- **Least-count route.** The least positive count is one, and the cost is `J`.
No transcendence input, and no automorphism postulate either. -/
theorem least_route (k : ℕ) (hleast : IsLeast {n : ℕ | 0 < n} k) :
    ∀ x : ℝ, 0 < x → gaugeCost (k : ℝ) x = Jcost x := by
  have h1 : k = 1 := hleast.unique least_positive_count
  subst h1
  intro x _
  simp

/-- The two selection principles agree on count exponents. -/
theorem least_iff_automorphism (k : ℕ) (hk : 0 < k) :
    IsLeast {n : ℕ | 0 < n} k ↔ CharacterIsAutomorphism (k : ℝ) := by
  rw [characterIsAutomorphism_nat_iff k hk]
  constructor
  · intro h
    exact h.unique least_positive_count
  · rintro rfl
    exact least_positive_count

/-! ## The row -/

/-- Row 3b in harness form, on count exponents. -/
def countRow : CutsetRow ℕ where
  Floor := fun k => 0 < k
  Sentence := fun k => CharacterIsAutomorphism (k : ℝ)
  Blade := fun k => IsLeast {n : ℕ | 0 < n} k
  provenance := .floorTheorem "least count (B2): the least positive count is one"
  real := 1
  real_floor := Nat.one_pos
  blade_real := least_positive_count
  violator := 2
  violator_floor := by norm_num
  violator_violates := by
    have h := carrierNative_two_not_calibrated.2.1
    exact_mod_cast h
  blade_kills_violator := by
    intro h
    have := h.2 (show (1 : ℕ) ∈ {n : ℕ | 0 < n} from Nat.one_pos)
    omega
  exclusion := fun k hk hs hb => hs ((least_iff_automorphism k hk).1 hb)

/-! ## Certificate -/

structure Cert : Prop where
  blade_is_sentence :
    ∀ F : ℝ → ℝ, (∀ x : ℝ, 0 < x → 0 ≤ F x) → (CountPosted F ↔ CarrierNative F)
  half_fails : ¬ CountPosted (gaugeCost (1 / 2))
  nat_passes : ∀ k : ℕ, CountPosted (gaugeCost (k : ℝ))
  automorphism_route :
    ∀ k : ℕ, 0 < k → CharacterIsAutomorphism (k : ℝ) →
      ∀ x : ℝ, 0 < x → gaugeCost (k : ℝ) x = Jcost x
  least_route :
    ∀ k : ℕ, IsLeast {n : ℕ | 0 < n} k → ∀ x : ℝ, 0 < x → gaugeCost (k : ℝ) x = Jcost x
  principles_agree : ∀ k : ℕ, 0 < k → (IsLeast {n : ℕ | 0 < n} k ↔ CharacterIsAutomorphism (k : ℝ))
  row_forces : ∀ k : ℕ, countRow.Floor k → countRow.Blade k → countRow.Sentence k
  row_class_nonempty : ∃ k : ℕ, countRow.Floor k ∧ ¬ countRow.Sentence k

theorem cert : Cert where
  blade_is_sentence := countPosted_iff_carrierNative
  half_fails := half_not_countPosted
  nat_passes := nat_countPosted
  automorphism_route := automorphism_route
  least_route := least_route
  principles_agree := least_iff_automorphism
  row_forces := countRow.forces
  row_class_nonempty := countRow.class_nonempty

end

end Row3Calibration
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
