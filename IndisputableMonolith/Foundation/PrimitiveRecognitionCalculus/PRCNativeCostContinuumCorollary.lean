/-
  PrimitiveRecognitionCalculus/PRCNativeCostContinuumCorollary.lean

  Round-trip source:
    plans/Delta_JCost_FreeSide_Program_Plan_20260724.html  (round 7)

  ROUND 7: invert the bridge.

  `PRCJCost.bridge_to_existing_jcost_uniqueness` runs the wrong way. It takes the
  continuous positive-real uniqueness theorem as a premise and re-exports it, so
  the δ-native surface is downstream of the completed line. That is backwards for
  a program whose own audit says the line is not forced.

  This module reverses the arrow. The native theorem
  (`PRCStructuralNativeCostUniquenessTarget_proved`, round 5) already pins the
  cost at every point of the δ-native carrier, and the carrier displays every
  rational. What the continuum adds is exactly one step, and this module isolates
  it and prices it:

    * `nativeCostOnRationals`  — the native answer, read on ℚ, IS `Cost.Jcost`.
    * `carrier_displays_every_rational` — nothing on ℚ is missed.
    * `completion_step` — a function continuous on `(0, ∞)` that agrees with the
      native answer at every positive rational equals `Cost.Jcost` everywhere on
      `(0, ∞)`. Density, and nothing else.
    * `continuum_uniqueness_from_native` — the continuous conclusion, derived
      from the native theorem plus that one step.
    * `completion_is_a_real_purchase` — and the step is not free: without
      continuity the rational agreement leaves the irrational points wide open
      (`irrationalShiftCost`).

  So the continuum result is now a corollary we can price rather than an input we
  depend on. The price is one word, `ContinuousOn`, and the receipt is here.

  Scope: reads the round-4/5/6 ledger and Mathlib. It edits no upstream module.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCNativeCostStructuralLedger
import IndisputableMonolith.Cost.FunctionalEquation

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace PRCJCost

/-! ## Part 1: the δ-native carrier displays every rational

The native theorem is stated on `RatioOrbit`. To compare it with a statement
about ℝ we need to know that the carrier misses no rational, so that "the native
answer at every carrier point" and "the answer at every rational" are the same
sentence. They are: `toRat` is surjective, by construction. -/

/-- The δ-native carrier displays every rational: nothing on ℚ is out of reach of
the free side. The witness `ratioOrbitOfRat` is the round-1 construction. -/
theorem carrier_displays_every_rational (t : ℚ) :
    ∃ q : RatioOrbit, q.toRat = t :=
  ⟨ratioOrbitOfRat t, ratioOrbitOfRat_toRat t⟩

/-! ## Part 2: read on ℚ, the native answer is the continuum answer

`onRatioOrbit_toReal_jcost` already says the canonical native display transports
to `Cost.Jcost`. Composed with the round-5 uniqueness theorem this says: any
inhabitant of the structural ledger, read at any rational, is `Cost.Jcost` there.
No continuity has been used, and no real number has entered a hypothesis. -/

/-- Any structural native cost, displayed at any rational, agrees with the
continuum cost at that rational. -/
theorem structural_cost_eq_jcost_on_rationals
    {G : RatioOrbit → RatioOrbit} (hG : PRCStructuralNativeCostHypotheses G)
    (t : ℚ) :
    (((G (ratioOrbitOfRat t)).toRat : ℚ) : ℝ) = Cost.Jcost (t : ℝ) := by
  have hnat := crossDisp (PRCStructuralNativeCostUniquenessTarget_proved G hG
    (ratioOrbitOfRat t))
  rw [hnat, onRatioOrbit_toReal_jcost, ratioOrbitOfRat_toRat]

/-! ## Part 3: the completion step, isolated

This is the whole of what the continuum adds. Positive rationals are dense in
`(0, ∞)`, so a continuous function on `(0, ∞)` that agrees with `Cost.Jcost` at
every positive rational agrees with it everywhere on `(0, ∞)`. -/

/-- The positive rationals, seen inside ℝ. -/
def positiveRationalPoints : Set ℝ := {x : ℝ | ∃ t : ℚ, 0 < t ∧ (t : ℝ) = x}

theorem positiveRationalPoints_subset : positiveRationalPoints ⊆ Set.Ioi (0 : ℝ) := by
  rintro x ⟨t, ht, rfl⟩
  have : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  exact this

/-- Density, stated as the only fact about ℝ this module consumes. -/
theorem Ioi_subset_closure_positiveRationalPoints :
    Set.Ioi (0 : ℝ) ⊆ closure positiveRationalPoints := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hlt : max 0 (x - ε / 2) < x := by
    rcases max_cases (0 : ℝ) (x - ε / 2) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact hx0
    · rw [h]; linarith
  obtain ⟨t, ht₁, ht₂⟩ := exists_rat_btwn hlt
  have htpos : (0 : ℝ) < (t : ℝ) := lt_of_le_of_lt (le_max_left _ _) ht₁
  have htq : (0 : ℚ) < t := by exact_mod_cast htpos
  have hmem : (t : ℝ) ∈ positiveRationalPoints := ⟨t, htq, rfl⟩
  refine ⟨(t : ℝ), hmem, ?_⟩
  have hlow : x - ε / 2 < (t : ℝ) := lt_of_le_of_lt (le_max_right _ _) ht₁
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem jcost_continuousOn : ContinuousOn Cost.Jcost (Set.Ioi (0 : ℝ)) := by
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Ioi (0 : ℝ)) :=
    ContinuousOn.inv₀ continuousOn_id (fun x hx => ne_of_gt hx)
  have hsum : ContinuousOn (fun x : ℝ => (x + x⁻¹) / 2) (Set.Ioi (0 : ℝ)) :=
    ContinuousOn.div_const (ContinuousOn.add continuousOn_id hinv) 2
  exact ContinuousOn.sub hsum continuousOn_const

/-- **The completion step.** This is the entire content of the move from the
δ-native carrier to the completed line, for this theorem. -/
theorem completion_step {F : ℝ → ℝ}
    (hcont : ContinuousOn F (Set.Ioi 0))
    (hrat : ∀ t : ℚ, 0 < t → F (t : ℝ) = Cost.Jcost (t : ℝ)) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  have heq : Set.EqOn F Cost.Jcost positiveRationalPoints := by
    rintro x ⟨t, ht, rfl⟩
    exact hrat t ht
  have hall : Set.EqOn F Cost.Jcost (Set.Ioi (0 : ℝ)) :=
    heq.of_subset_closure hcont jcost_continuousOn positiveRationalPoints_subset
      Ioi_subset_closure_positiveRationalPoints
  intro x hx
  exact hall hx

/-! ## Part 4: the continuum theorem, as a corollary

The arrow now points the other way. The native theorem supplies the answer; the
completion step supplies the domain. -/

/-- **The inverted bridge.** A function on the positive reals whose restriction
to the δ-native carrier is a structural native cost, and which is continuous, is
`Cost.Jcost`. The native theorem does the selecting; continuity only carries the
answer off the carrier. -/
theorem continuum_uniqueness_from_native
    {F : ℝ → ℝ} {G : RatioOrbit → RatioOrbit}
    (hG : PRCStructuralNativeCostHypotheses G)
    (hrestrict : ∀ q : RatioOrbit, 0 < q.toRat → F ((q.toRat : ℚ) : ℝ)
      = (((G q).toRat : ℚ) : ℝ))
    (hcont : ContinuousOn F (Set.Ioi 0)) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  refine completion_step hcont ?_
  intro t ht
  have hq : (0 : ℚ) < (ratioOrbitOfRat t).toRat := by
    rw [ratioOrbitOfRat_toRat]; exact ht
  have h₁ := hrestrict (ratioOrbitOfRat t) hq
  rw [ratioOrbitOfRat_toRat] at h₁
  rw [h₁]
  exact structural_cost_eq_jcost_on_rationals hG t

/-! ## Part 5: the completion step is a real purchase

Round 6 showed the surviving anchor is a genuine gauge by inhabiting the
anchor-free ledger with a second cost. The same discipline applies here: the
completion step is not a redundancy. Drop continuity and the rational agreement
says nothing at the irrational points. -/

open Classical in
/-- The native answer on ℚ, shifted by one off ℚ. Agrees with `Cost.Jcost` at
every rational and nowhere else. -/
noncomputable def irrationalShiftCost (x : ℝ) : ℝ :=
  if (∃ t : ℚ, (t : ℝ) = x) then Cost.Jcost x else Cost.Jcost x + 1

theorem irrationalShiftCost_of_rat (t : ℚ) :
    irrationalShiftCost (t : ℝ) = Cost.Jcost (t : ℝ) := by
  classical
  rw [irrationalShiftCost, if_pos ⟨t, rfl⟩]

theorem irrationalShiftCost_ne_at_sqrt_two :
    irrationalShiftCost (Real.sqrt 2) ≠ Cost.Jcost (Real.sqrt 2) := by
  classical
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have hne : ¬ ∃ t : ℚ, (t : ℝ) = Real.sqrt 2 := by
    rintro ⟨t, ht⟩
    exact hirr ⟨t, ht⟩
  rw [irrationalShiftCost, if_neg hne]
  intro h
  linarith [h]

/-- Continuity is doing real work: rational agreement alone does not pin the
function on `(0, ∞)`. -/
theorem completion_is_a_real_purchase :
    ∃ F : ℝ → ℝ, (∀ t : ℚ, 0 < t → F (t : ℝ) = Cost.Jcost (t : ℝ)) ∧
      ∃ x : ℝ, 0 < x ∧ F x ≠ Cost.Jcost x := by
  refine ⟨irrationalShiftCost, fun t _ => irrationalShiftCost_of_rat t,
    Real.sqrt 2, Real.sqrt_pos.mpr (by norm_num), irrationalShiftCost_ne_at_sqrt_two⟩

/-! ## Part 6: the round-7 certificate -/

/-- **Inverted cost bridge.** The free side selects the cost; the completed line
only extends its domain, and the extension has a named, non-redundant price. -/
structure InvertedCostBridge : Prop where
  /-- The carrier misses no rational. -/
  carrier_total : ∀ t : ℚ, ∃ q : RatioOrbit, q.toRat = t
  /-- Every inhabitant of the structural ledger IS the continuum cost, at every
  rational, with no continuity assumed anywhere. -/
  native_answer_is_the_continuum_answer :
    ∀ G : RatioOrbit → RatioOrbit, PRCStructuralNativeCostHypotheses G →
      ∀ t : ℚ, (((G (ratioOrbitOfRat t)).toRat : ℚ) : ℝ) = Cost.Jcost (t : ℝ)
  /-- The completion step, isolated: density and nothing else. -/
  completion :
    ∀ F : ℝ → ℝ, ContinuousOn F (Set.Ioi 0) →
      (∀ t : ℚ, 0 < t → F (t : ℝ) = Cost.Jcost (t : ℝ)) →
        ∀ x : ℝ, 0 < x → F x = Cost.Jcost x
  /-- And so the continuous conclusion is a corollary of the native theorem. -/
  continuum_is_a_corollary :
    ∀ (F : ℝ → ℝ) (G : RatioOrbit → RatioOrbit),
      PRCStructuralNativeCostHypotheses G →
        (∀ q : RatioOrbit, 0 < q.toRat → F ((q.toRat : ℚ) : ℝ)
          = (((G q).toRat : ℚ) : ℝ)) →
          ContinuousOn F (Set.Ioi 0) → ∀ x : ℝ, 0 < x → F x = Cost.Jcost x
  /-- The step is a purchase, not a redundancy. -/
  completion_priced :
    ∃ F : ℝ → ℝ, (∀ t : ℚ, 0 < t → F (t : ℝ) = Cost.Jcost (t : ℝ)) ∧
      ∃ x : ℝ, 0 < x ∧ F x ≠ Cost.Jcost x

theorem invertedCostBridge_holds : InvertedCostBridge where
  carrier_total := carrier_displays_every_rational
  native_answer_is_the_continuum_answer := fun _ hG t =>
    structural_cost_eq_jcost_on_rationals hG t
  completion := fun _ hcont hrat => completion_step hcont hrat
  continuum_is_a_corollary := fun _ _ hG hrestrict hcont =>
    continuum_uniqueness_from_native hG hrestrict hcont
  completion_priced := completion_is_a_real_purchase

end PRCJCost

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
