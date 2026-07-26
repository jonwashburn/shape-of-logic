/-
  Cost/UnitFromMinimality.lean

  THE UNIT OF COST, SELECTED BY COST.

  Background. The composition law forces the FORM of the recognition cost but not its
  scale: the admissible costs come in a gauge family `x ↦ J (x ^ l)`, and picking `l = 1`
  has been done by calibration (`G''(0) = 1` on the continuum, an anchor at orbit two on
  the countable carrier). Calibration is a stipulation, so the standing honest wording has
  been "parameter-free up to a choice of unit", and whether the unit is forced or
  conventional has been open since `Delta_Cost_Form_Forced_Unit_Gauge` (May 2026).

  What this file adds. A selection principle that needs no calibration: among admissible
  costs, take the cheapest. Whether that works turns entirely on whether the gauge is
  discrete or continuous, and the two carriers differ exactly there.

  * On the countable carrier the gauge members proved to inhabit the anchor-free ledger
    form a discrete family indexed by an integer exponent, and `J` is their STRICT
    POINTWISE MINIMUM among the nondegenerate ones (`jcost_lt_pow`, with the earlier
    odd-power-only form `jcost_lt_odd_power`). Least cost therefore selects the unit
    outright, with no anchor: `unit_is_selected_by_minimality_over_powers`.
  * On the continuum the gauge is a continuum, the family is totally ordered with no
    least member (`no_least_gauge_member`), and its pointwise infimum is the zero cost
    (`gauge_tendsto_zero`). So no least-cost principle can fix a unit there; it
    degenerates to charging nothing for everything.

  Reading. The freedom that forces calibration is not a feature of cost. It is introduced
  by completing to the real line, and it destroys the selection principle that would
  otherwise fix the unit for free. Combined with the standing result that the completion
  is a genuine purchase, the unit is a convention on the reals and a theorem on the
  carrier.

  Scope, so this is not over-read. Minimality selects `J` from the power family, every
  member of which is proved to inhabit the anchor-free ledger. Two things are still needed
  for the unqualified reading. The reverse inclusion, that the ledger admits nothing
  outside that family, is OPEN (the Alaoglu-Erdos / six-exponentials wall). And exponent
  zero, the sign cost, does inhabit the ledger and charges nothing, so it undercuts `J`
  and is excluded by nondegeneracy rather than by cost
  (`exponent_zero_undercuts_everything`). So the selection theorems here are
  unconditional about the power family and the full "no anchor is needed" reading is
  conditional on the classification plus nondegeneracy. This file states the conditional
  explicitly rather than blurring it.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.FunctionalEquation

namespace IndisputableMonolith
namespace Cost
namespace UnitFromMinimality

/-! ## Reciprocity lets every statement be proved above one -/

/-- Cost is blind to inversion of the base, so a gauge statement need only be proved for
bases above one. Stated for real exponents since the continuum half needs it. -/
lemma jcost_rpow_inv (x : ℝ) (hx : 0 < x) (l : ℝ) :
    Jcost (x ^ l) = Jcost ((x⁻¹) ^ l) := by
  have hpos : 0 < x ^ l := Real.rpow_pos_of_pos hx l
  rw [Real.inv_rpow hx.le l]
  exact Jcost_symm hpos

/-- The same, for the natural-number powers the discrete gauge uses. -/
lemma jcost_pow_inv (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Jcost (x ^ n) = Jcost ((x⁻¹) ^ n) := by
  have hpos : 0 < x ^ n := pow_pos hx n
  rw [inv_pow]
  exact Jcost_symm hpos

/-! ## The countable carrier: a discrete gauge has a least member, and it is `J` -/

/-- Above one, every higher odd power costs strictly more. -/
lemma jcost_lt_odd_power_of_one_lt (x : ℝ) (hx : 1 < x) (k : ℕ) (hk : 1 ≤ k) :
    Jcost x < Jcost (x ^ (2 * k + 1)) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlt : x < x ^ (2 * k + 1) := by
    have h1 : (1 : ℕ) < 2 * k + 1 := by omega
    calc x = x ^ 1 := (pow_one x).symm
    _ < x ^ (2 * k + 1) := pow_lt_pow_right₀ hx h1
  exact Jcost_strict_mono_on_one_infty x (x ^ (2 * k + 1)) hx0
    (lt_trans hx0 hlt) hx.le hlt

/-- **The unit is the cheapest gauge member.** For any base other than the unit, the
canonical cost `J` charges strictly less than every higher odd power of the gauge. Since
those odd powers are exactly the members proved to inhabit the anchor-free ledger on the
countable carrier, least cost picks out `J` with no calibration and no anchor. -/
theorem jcost_lt_odd_power (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) (k : ℕ) (hk : 1 ≤ k) :
    Jcost x < Jcost (x ^ (2 * k + 1)) := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · -- Below one: invert and reuse the case above one.
    have hinv : 1 < x⁻¹ := one_lt_inv_iff₀.mpr ⟨hx, hlt⟩
    have h := jcost_lt_odd_power_of_one_lt x⁻¹ hinv k hk
    rwa [← Jcost_symm hx, ← jcost_pow_inv x hx (2 * k + 1)] at h
  · exact absurd heq hx1
  · exact jcost_lt_odd_power_of_one_lt x hgt k hk

/-- Packaging: on the discrete gauge, least cost is a selection principle. Every gauge
member other than `J` is strictly more expensive at every base that is not the unit. -/
theorem unit_is_selected_by_minimality :
    ∀ x : ℝ, 0 < x → x ≠ 1 → ∀ k : ℕ, 1 ≤ k → Jcost x < Jcost (x ^ (2 * k + 1)) :=
  fun x hx hx1 k hk => jcost_lt_odd_power x hx hx1 k hk

/-! ### Leastness, quantified over the family and not against a designated member

The condition below makes no reference to the canonical cost. It says only that the
`k`-th member is nowhere more expensive than **any** member of the family, which is what
"least element of the pointwise order" means. Stating it against `J` instead would smuggle
in the answer, so it is stated properly and the characterization is derived. -/

/-- The `k`-th gauge member is a least element of the odd-power family under the pointwise
order: it charges no more than any member, at every ratio other than the unit. -/
def IsLeastOddPowerCost (k : ℕ) : Prop :=
  ∀ j : ℕ, ∀ x : ℝ, 0 < x → x ≠ 1 →
    Jcost (x ^ (2 * k + 1)) ≤ Jcost (x ^ (2 * j + 1))

/-- **The canonical cost is the unique least element of the gauge family.** No reference
to `J` appears in `IsLeastOddPowerCost`; leastness is quantified over the family alone,
and it happens to hold of exactly one member. -/
theorem isLeast_iff_canonical (k : ℕ) : IsLeastOddPowerCost k ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hle := h 0 2 (by norm_num) (by norm_num)
    have hlt := jcost_lt_odd_power (2 : ℝ) (by norm_num) (by norm_num) k hk1
    simp only [Nat.mul_zero, Nat.zero_add, pow_one] at hle
    exact absurd hle (not_le.mpr hlt)
  · rintro rfl
    intro j x hx hx1
    simp only [Nat.mul_zero, Nat.zero_add, pow_one]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · exact le_of_lt (jcost_lt_odd_power x hx hx1 j hj)

/-! ### The family is larger than the odd powers, and leastness survives the enlargement

The classification of anchor-free inhabitants was corrected twice on 2026-07-25. The
inhabited set is not the odd powers. The sign cost inhabits it at exponent zero, and the
sign-extended character `x ↦ x·|x|^m` inhabits it at exponent `m+1` of either parity, so
every nonnegative integer exponent occurs (`Cost/GaugeOrbitFromRealCharacter.lean`:
`signGaugeNativeCost_sansAnchor`, `signedPowerNativeCost_sansAnchor`). Restricted to the
positive ratios, where the pointwise order is decided, that whole family is `x ↦ J (x ^ n)`
for `n : ℕ`. Since 2026-07-26 that is also the complete list: no other inhabitant exists
(`Cost.GaugeOrbitClassification.GaugeOrbitIsSignedPowerFamily_of_sixExponentials`, on the
six exponentials input), so the leastness statements below now range over exactly the
ledger's inhabitants rather than over a family known only to be contained in it.

Leastness therefore has to be re-proved over the enlarged family, or the selection claim
covers less than the ledger contains. It goes through with the parity deleted: nothing in
the argument used it, only that the exponent exceeds one. Exponent zero charges nothing
anywhere and is least for the wrong reason, which is what the nondegeneracy hypothesis in
the companion argument excludes. -/

/-- Above one, every higher power costs strictly more, at either parity of the exponent. -/
lemma jcost_lt_pow_of_one_lt (x : ℝ) (hx : 1 < x) (n : ℕ) (hn : 2 ≤ n) :
    Jcost x < Jcost (x ^ n) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlt : x < x ^ n := by
    have h1 : (1 : ℕ) < n := by omega
    calc x = x ^ 1 := (pow_one x).symm
    _ < x ^ n := pow_lt_pow_right₀ hx h1
  exact Jcost_strict_mono_on_one_infty x (x ^ n) hx0 (lt_trans hx0 hlt) hx.le hlt

/-- **The unit is the cheapest member of the enlarged family.** For any base other than the
unit, `J` charges strictly less than the cost generated by any exponent above one. This is
`jcost_lt_odd_power` with the parity restriction removed, which is what the corrected
classification requires. -/
theorem jcost_lt_pow (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) (n : ℕ) (hn : 2 ≤ n) :
    Jcost x < Jcost (x ^ n) := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · have hinv : 1 < x⁻¹ := one_lt_inv_iff₀.mpr ⟨hx, hlt⟩
    have h := jcost_lt_pow_of_one_lt x⁻¹ hinv n hn
    rwa [← Jcost_symm hx, ← jcost_pow_inv x hx n] at h
  · exact absurd heq hx1
  · exact jcost_lt_pow_of_one_lt x hgt n hn

theorem unit_is_selected_by_minimality_over_powers :
    ∀ x : ℝ, 0 < x → x ≠ 1 → ∀ n : ℕ, 2 ≤ n → Jcost x < Jcost (x ^ n) :=
  fun x hx hx1 n hn => jcost_lt_pow x hx hx1 n hn

/-- The exponent-`n` member is a least element of the nondegenerate power family under the
pointwise order. Nondegeneracy is the restriction `1 ≤ m` on the competitors: exponent zero
is the identically zero cost. -/
def IsLeastPowerCost (n : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ x : ℝ, 0 < x → x ≠ 1 → Jcost (x ^ n) ≤ Jcost (x ^ m)

/-- **The canonical cost is the unique least nondegenerate member, at every exponent and not
merely the odd ones.** As before, the condition never names `J`. -/
theorem isLeastPower_iff_canonical (n : ℕ) (hn : 1 ≤ n) :
    IsLeastPowerCost n ↔ n = 1 := by
  constructor
  · intro h
    by_contra hne
    have hn2 : 2 ≤ n := by omega
    have hle := h 1 (le_refl 1) 2 (by norm_num) (by norm_num)
    have hlt := jcost_lt_pow (2 : ℝ) (by norm_num) (by norm_num) n hn2
    rw [pow_one] at hle
    exact absurd hle (not_le.mpr hlt)
  · rintro rfl
    intro m hm x hx hx1
    rw [pow_one]
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have hm1 : m = 1 := by omega
      subst hm1
      simp
    · exact le_of_lt (jcost_lt_pow x hx hx1 m hm2)

/-- Exponent zero is the degenerate member: it charges nothing at every ratio. It is least in
the enlarged family, and for a reason that has nothing to do with cost, which is exactly why
selection needs nondegeneracy rather than leastness alone. -/
theorem exponent_zero_charges_nothing (x : ℝ) : Jcost (x ^ (0 : ℕ)) = 0 := by
  rw [pow_zero]
  exact Jcost_unit0

theorem exponent_zero_undercuts_everything (n : ℕ) (x : ℝ) (hx : 0 < x) :
    Jcost (x ^ (0 : ℕ)) ≤ Jcost (x ^ n) := by
  rw [exponent_zero_charges_nothing]
  exact Jcost_nonneg (pow_pos hx n)

/-! ### The anchor was minimality all along

The structural ledger's surviving stipulation is the anchor at orbit two: the requirement
that the cost charge `J 2 = 1/4` there. The next two results show that this stipulation
and the minimality condition cut the gauge family at exactly the same place, so the
anchor is not an arbitrary numeric convention. It is the cheapest-cost condition, written
at one point. -/

/-- The anchor selects the canonical member and nothing else, and it does so **at every
base**. The choice of orbit two as the anchor point is therefore immaterial: any single
ratio other than the unit pins the same member. What looked like two arbitrary choices,
where to anchor and what value to give it, is one determination with no freedom in it. -/
theorem anchor_iff_canonical (b : ℝ) (hb : 0 < b) (hb1 : b ≠ 1) (k : ℕ) :
    Jcost (b ^ (2 * k + 1)) = Jcost b ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    exact absurd h (ne_of_gt (jcost_lt_odd_power b hb hb1 k hk1))
  · rintro rfl
    norm_num

/-- **The anchor is the leastness condition.** On the gauge family the stipulated anchor
value and genuine leastness over the family hold of exactly the same member, for any
anchor base. So the one surviving stipulation in the structural ledger is not a convention
about a number; it is least cost, evaluated at a point, and the point may be any point.

Note what is and is not shown. Leastness here is over the odd-power family, which is the
part of the anchor-free ledger proved to be inhabited. Leastness over the whole ledger
needs the classification discussed in the accompanying paper. -/
theorem anchor_is_minimality (b : ℝ) (hb : 0 < b) (hb1 : b ≠ 1) (k : ℕ) :
    (Jcost (b ^ (2 * k + 1)) = Jcost b) ↔ IsLeastOddPowerCost k := by
  rw [anchor_iff_canonical b hb hb1, isLeast_iff_canonical]

/-- The anchor characterization over the enlarged family: any single base other than the unit
pins the exponent to one, at either parity. -/
theorem anchorPower_iff_canonical (b : ℝ) (hb : 0 < b) (hb1 : b ≠ 1) (n : ℕ) (hn : 1 ≤ n) :
    Jcost (b ^ n) = Jcost b ↔ n = 1 := by
  constructor
  · intro h
    by_contra hne
    have hn2 : 2 ≤ n := by omega
    exact absurd h (ne_of_gt (jcost_lt_pow b hb hb1 n hn2))
  · rintro rfl
    rw [pow_one]

/-- **The anchor is the leastness condition, over the whole nondegenerate family.** Same
statement as `anchor_is_minimality` with the parity restriction removed, so it now covers
every exponent the corrected classification admits. -/
theorem anchor_is_minimality_over_powers (b : ℝ) (hb : 0 < b) (hb1 : b ≠ 1) (n : ℕ)
    (hn : 1 ≤ n) :
    (Jcost (b ^ n) = Jcost b) ↔ IsLeastPowerCost n := by
  rw [anchorPower_iff_canonical b hb hb1 n hn, isLeastPower_iff_canonical n hn]

/-- **The cost of the first distinction.** The composition law fixes the output scale of
the cost, since rescaling a solution breaks it. The only freedom left was the input scale,
and minimality has just removed it. So this number is now determined rather than
stipulated: telling one from two costs a quarter. -/
theorem cost_of_the_first_distinction : Jcost 2 = 1 / 4 := by
  norm_num [Jcost]

/-! ## The continuum: a continuous gauge has no least member -/

/-- Above one, halving the exponent is strictly cheaper. -/
lemma gauge_halving_is_cheaper_of_one_lt (x : ℝ) (hx : 1 < x) (l : ℝ) (hl : 0 < l) :
    Jcost (x ^ (l / 2)) < Jcost (x ^ l) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hhalf : 0 < l / 2 := by linarith
  have hone : 1 < x ^ (l / 2) := Real.one_lt_rpow_iff_of_pos hx0 |>.mpr (Or.inl ⟨hx, hhalf⟩)
  have hlt : x ^ (l / 2) < x ^ l := by
    exact Real.rpow_lt_rpow_left_iff hx |>.mpr (by linarith)
  exact Jcost_strict_mono_on_one_infty _ _ (lt_trans zero_lt_one hone)
    (lt_trans (lt_trans zero_lt_one hone) hlt) hone.le hlt

/-- **No cheapest cost exists on the continuum.** For every admissible scale there is a
strictly cheaper one, so the least-cost principle that fixes the unit on the countable
carrier has nothing to select here. -/
theorem no_least_gauge_member (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) (l : ℝ) (hl : 0 < l) :
    Jcost (x ^ (l / 2)) < Jcost (x ^ l) := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · have hinv : 1 < x⁻¹ := one_lt_inv_iff₀.mpr ⟨hx, hlt⟩
    have h := gauge_halving_is_cheaper_of_one_lt x⁻¹ hinv l hl
    rwa [← jcost_rpow_inv x hx (l / 2), ← jcost_rpow_inv x hx l] at h
  · exact absurd heq hx1
  · exact gauge_halving_is_cheaper_of_one_lt x hgt l hl

/-- And the descent runs all the way to nothing: the gauge family's pointwise limit as
the scale vanishes is the zero cost. So the infimum is not merely unattained, it is the
degenerate cost that charges nothing for anything. -/
theorem gauge_tendsto_zero (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto (fun l : ℝ => Jcost (x ^ l)) (nhds 0) (nhds 0) := by
  have hrw : (fun l : ℝ => Jcost (x ^ l))
      = fun l : ℝ => Real.cosh (Real.log x * l) - 1 := by
    funext l
    rw [Real.rpow_def_of_pos hx, Jcost_exp_cosh]
  rw [hrw]
  have hcont : Continuous (fun l : ℝ => Real.cosh (Real.log x * l) - 1) := by
    fun_prop
  have h0 : Real.cosh (Real.log x * (0 : ℝ)) - 1 = 0 := by simp
  simpa [h0] using hcont.tendsto (0 : ℝ)

/-- **The limit of the descent is admissible, not excluded.** The scale zero gives the
identically zero function, and that function satisfies the composition law, reciprocity
and normalization. So the descent of `no_least_gauge_member` does not run off the edge of
the admissible class; it runs to a member of it. Ruling the zero cost out takes a
nondegeneracy condition that the stated hypotheses do not contain, which is a further
reason a bare least-cost principle cannot fix a unit on the line. -/
theorem zero_cost_is_admissible :
    FunctionalEquation.IsReciprocalCost (fun _ => 0)
    ∧ FunctionalEquation.IsNormalized (fun _ => 0)
    ∧ FunctionalEquation.SatisfiesCompositionLaw (fun _ => 0)
    ∧ ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioi 0)
    ∧ (∀ x : ℝ, 0 < x → Jcost (x ^ (0 : ℝ)) = 0) := by
  refine ⟨fun _ _ => rfl, rfl, fun _ _ _ _ => by norm_num,
    continuousOn_const, fun x _ => ?_⟩
  rw [Real.rpow_zero]
  exact Jcost_unit0

/-! ## The contrast, in one statement -/

/-- The two carriers, side by side. Least cost is a selection principle on the discrete
gauge and not on the continuous one, and completion to the real line is what turns the
first into the second.

The first clause is the countable carrier: `J` is strictly cheapest among the odd powers.
The second is the continuum: no scale is cheapest, because halving always undercuts. This
is a conjunction of the two facts, not a characterization of discreteness. -/
theorem discrete_gauge_has_a_floor_and_continuous_gauge_does_not :
    (∀ x : ℝ, 0 < x → x ≠ 1 → ∀ k : ℕ, 1 ≤ k → Jcost x < Jcost (x ^ (2 * k + 1)))
    ∧ (∀ x : ℝ, 0 < x → x ≠ 1 → ∀ l : ℝ, 0 < l → Jcost (x ^ (l / 2)) < Jcost (x ^ l)) :=
  ⟨fun x hx hx1 k hk => jcost_lt_odd_power x hx hx1 k hk,
   fun x hx hx1 l hl => no_least_gauge_member x hx hx1 l hl⟩

/-! ## Audits -/

#print axioms jcost_lt_odd_power
#print axioms isLeast_iff_canonical
#print axioms anchor_is_minimality
#print axioms jcost_lt_pow
#print axioms isLeastPower_iff_canonical
#print axioms anchor_is_minimality_over_powers
#print axioms exponent_zero_undercuts_everything
#print axioms cost_of_the_first_distinction
#print axioms no_least_gauge_member
#print axioms gauge_tendsto_zero
#print axioms zero_cost_is_admissible
#print axioms discrete_gauge_has_a_floor_and_continuous_gauge_does_not

end UnitFromMinimality
end Cost
end IndisputableMonolith
