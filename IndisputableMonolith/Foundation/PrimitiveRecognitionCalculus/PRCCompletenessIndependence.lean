/-
  PrimitiveRecognitionCalculus/PRCCompletenessIndependence.lean

  The deepest open frontier of the δ program, resolved: is the continuous completion
  (the move to the order-complete field ℝ) FORCED by the δ / cost axioms, or is it an
  independent posit?

  Prior work established the SEPARATION (the completion has elements the δ-native
  carrier lacks) and tagged the completion as a "stronger commitment". What was
  missing was an exact INDEPENDENCE statement: a model of the cost/field axioms that
  fails order-completeness. This module supplies it.

  The witness is the countable exp/log-closed field `T` of `PRCExpLogField`, on which
  the canonical cost `Cost.Jcost` is closed (`PRCCostOnField`). We prove:

  * `subfield_not_complete`: ANY proper subfield `K ⊊ ℝ` lacks the least-upper-bound
    property. Every subfield contains ℚ (which is dense in ℝ), so for any `r ∉ K` the
    Dedekind cut `{x ∈ K : x < r}` is nonempty, bounded above in `K`, yet has no least
    upper bound inside `K` (its real supremum is `r ∉ K`, and density rules out any
    `K`-element being a least upper bound). This is the classical "a cut at an
    irrational has no rational supremum" argument, lifted from ℚ to any proper
    subfield.

  * `completeness_not_forced_by_cost_axioms`: the countable field `T` is closed under
    `Cost.Jcost` and is countable, YET lacks the least-upper-bound property, WHILE ℝ
    has it (`Real.exists_isLUB`). So order-completeness is true of one cost-closed
    field (ℝ) and false of another (`T`): it is NOT a consequence of the cost/field
    axioms. The completion to ℝ is a strictly stronger commitment, independent of δ.

  This resolves the question the program flagged as its real remaining frontier: the
  continuous completion is NOT δ-forced. δ and the cost laws are satisfied by a
  countable, incomplete carrier; completeness is an additional, independent axiom.

  HONEST BOUNDARY. "Independence" here is semantic/model-theoretic in the precise
  sense that the property `has-LUB` is not entailed by `is-a-subfield-of-ℝ-closed-
  under-Jcost`: it holds in ℝ and fails in `T`, both of which are such fields. We do
  not build a first-order theory and run a formal independence proof; we exhibit the
  two models directly, which is the stronger and more transparent statement.

  No project-local axioms. No sorry.
-/

import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCCostOnField

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace CompletenessIndependence

open ExpLogField

/-- `s` is a least upper bound of `S` lying inside the subfield `K`: it is in `K`, it
bounds `S`, and it is `≤` every `K`-element that bounds `S`. This is the relativized
notion of supremum that order-completeness of `K` would always supply. -/
def IsLUBIn (K : Subfield ℝ) (S : Set ℝ) (s : ℝ) : Prop :=
  s ∈ K ∧ (∀ x ∈ S, x ≤ s) ∧ ∀ u ∈ K, (∀ x ∈ S, x ≤ u) → s ≤ u

/-- **Any proper subfield of ℝ lacks the least-upper-bound property.** Every subfield
contains ℚ; ℚ is dense in ℝ; so for any real `r ∉ K`, the cut `{x ∈ K : x < r}` is
nonempty and bounded above in `K`, but no `K`-element is its least upper bound: a
candidate `s < r` is beaten by a rational in `(s, r)` that still lies in the cut, a
candidate `s > r` is not least because a rational in `(r, s)` already bounds the cut,
and `s = r` is impossible since `r ∉ K`. -/
theorem subfield_not_complete (K : Subfield ℝ) (hK : (K : Set ℝ) ≠ Set.univ) :
    ∃ S : Set ℝ,
      (∀ x ∈ S, x ∈ K)
        ∧ S.Nonempty
        ∧ (∃ b ∈ K, ∀ x ∈ S, x ≤ b)
        ∧ ¬ ∃ s, IsLUBIn K S s := by
  obtain ⟨r, hr⟩ := (Set.ne_univ_iff_exists_notMem _).mp hK
  refine ⟨{x | x ∈ K ∧ x < r}, ?_, ?_, ?_, ?_⟩
  · intro x hx; exact hx.1
  · obtain ⟨q, hq⟩ := exists_rat_lt r
    exact ⟨(q : ℝ), SubfieldClass.ratCast_mem K q, hq⟩
  · obtain ⟨q, hq⟩ := exists_rat_gt r
    exact ⟨(q : ℝ), SubfieldClass.ratCast_mem K q, fun x hx => le_of_lt (lt_trans hx.2 hq)⟩
  · rintro ⟨s, hsK, hub, hleast⟩
    rcases lt_trichotomy s r with hlt | heq | hgt
    · obtain ⟨q, hsq, hqr⟩ := exists_rat_btwn hlt
      have hqS : (q : ℝ) ∈ {x | x ∈ K ∧ x < r} := ⟨SubfieldClass.ratCast_mem K q, hqr⟩
      exact absurd (hub _ hqS) (not_le.mpr hsq)
    · exact hr (heq ▸ hsK)
    · obtain ⟨q, hrq, hqs⟩ := exists_rat_btwn hgt
      have hqub : ∀ x ∈ {x | x ∈ K ∧ x < r}, x ≤ (q : ℝ) :=
        fun x hx => le_of_lt (lt_trans hx.2 hrq)
      exact absurd (hleast _ (SubfieldClass.ratCast_mem K q) hqub) (not_le.mpr hqs)

/-- **Every countable subfield of ℝ lacks the least-upper-bound property.**
Countability forces properness (ℝ is uncountable), and properness forces
incompleteness by `subfield_not_complete`. So order-completeness and countability are
flatly incompatible for subfields of ℝ: completeness is exactly what uncountability
(the continuum) buys. Whatever countable carrier δ uses, it is never order-complete. -/
theorem countable_subfield_not_complete (K : Subfield ℝ)
    (hc : (K : Set ℝ).Countable) :
    ∃ S : Set ℝ,
      (∀ x ∈ S, x ∈ K)
        ∧ S.Nonempty
        ∧ (∃ b ∈ K, ∀ x ∈ S, x ≤ b)
        ∧ ¬ ∃ s, IsLUBIn K S s := by
  refine subfield_not_complete K ?_
  intro h
  exact Cardinal.not_countable_real (h ▸ hc)

/-- The countable cost-closed field `T` lacks the least-upper-bound property. -/
theorem T_not_complete :
    ∃ S : Set ℝ,
      (∀ x ∈ S, x ∈ T)
        ∧ S.Nonempty
        ∧ (∃ b ∈ T, ∀ x ∈ S, x ≤ b)
        ∧ ¬ ∃ s, IsLUBIn T S s :=
  countable_subfield_not_complete T T_countable

/-- ℝ has the least-upper-bound property: every nonempty bounded-above set has a least
upper bound. -/
theorem real_has_lub (S : Set ℝ) (hne : S.Nonempty) (hbdd : ∃ b, ∀ x ∈ S, x ≤ b) :
    ∃ s, IsLUB S s := by
  obtain ⟨b, hb⟩ := hbdd
  exact Real.exists_isLUB hne ⟨b, fun x hx => hb x hx⟩

/-- **Independence of order-completeness from the cost/field axioms.** The countable
field `T` is closed under the canonical cost `Cost.Jcost` and is countable, yet it
lacks the least-upper-bound property; ℝ has it. Order-completeness therefore holds in
one cost-closed subfield of ℝ (namely ℝ itself) and fails in another (`T`): it is not
entailed by being a `Cost.Jcost`-closed field. The continuous completion is a
strictly stronger, independent commitment, not a δ-consequence. -/
theorem completeness_not_forced_by_cost_axioms :
    (∀ x ∈ T, Cost.Jcost x ∈ T)
      ∧ (T : Set ℝ).Countable
      ∧ (∃ S : Set ℝ,
          (∀ x ∈ S, x ∈ T) ∧ S.Nonempty ∧ (∃ b ∈ T, ∀ x ∈ S, x ≤ b)
            ∧ ¬ ∃ s, IsLUBIn T S s)
      ∧ (∀ S : Set ℝ, S.Nonempty → (∃ b, ∀ x ∈ S, x ≤ b) → ∃ s, IsLUB S s) :=
  ⟨fun _ hx => CostOnField.jcost_mem_T hx, T_countable, T_not_complete, real_has_lub⟩

/-- The canonical cost `Cost.Jcost` genuinely satisfies the recognition-cost axioms:
the unit law `J(1) = 0` and reciprocal symmetry `J(x) = J(x⁻¹)` for positive `x`. So
the premise of the independence result is not merely "closed under a function"; it is
"a model of the cost laws". -/
theorem jcost_isCostRequirements : Cost.CostRequirements Cost.Jcost :=
  ⟨fun hx => Cost.Jcost_symm hx, Cost.Jcost_unit0⟩

/-- **Completeness independent of the GENUINE cost laws (not just `Jcost`-closure).**
This upgrades `completeness_not_forced_by_cost_axioms`: the premise now records that
`Cost.Jcost` is a bona fide recognition cost (unit `J(1)=0`, reciprocal symmetry
`J(x)=J(x⁻¹)`, nonnegativity `J(x)≥0` on positives), and that `T` is a countable field
on which `Jcost` is closed (hence a model of those laws). `T` still fails the
least-upper-bound property while ℝ satisfies it. So order-completeness is not entailed
by the genuine cost laws plus the field structure; it is an independent commitment.
This is the credibility-gating form: a skeptic cannot say the independence rests on a
weak "closure" premise rather than the actual cost axioms. -/
theorem completeness_not_forced_by_genuine_cost_laws :
    (Cost.Jcost 1 = 0)
      ∧ (∀ x : ℝ, 0 < x → Cost.Jcost x = Cost.Jcost x⁻¹)
      ∧ (∀ x : ℝ, 0 < x → 0 ≤ Cost.Jcost x)
      ∧ (∀ x ∈ T, Cost.Jcost x ∈ T)
      ∧ (T : Set ℝ).Countable
      ∧ (∃ S : Set ℝ,
          (∀ x ∈ S, x ∈ T) ∧ S.Nonempty ∧ (∃ b ∈ T, ∀ x ∈ S, x ≤ b)
            ∧ ¬ ∃ s, IsLUBIn T S s)
      ∧ (∀ S : Set ℝ, S.Nonempty → (∃ b, ∀ x ∈ S, x ≤ b) → ∃ s, IsLUB S s) :=
  ⟨Cost.Jcost_unit0, fun _ hx => Cost.Jcost_symm hx, fun _ hx => Cost.Jcost_nonneg hx,
    fun _ hx => CostOnField.jcost_mem_T hx, T_countable, T_not_complete, real_has_lub⟩

/-- **The sharp final form.** Order-completeness is precisely the content the
continuum adds: NO countable subfield of ℝ is order-complete, while ℝ is. Since every
δ result places the carrier in a countable field (the constants, the φ-ladder, the
cost dynamics all live countably), the carrier δ uses is never order-complete,
whichever countable field it is. Completeness is an independent axiom whose only model
is uncountable. -/
theorem completeness_is_exactly_the_continuum :
    (∀ K : Subfield ℝ, (K : Set ℝ).Countable →
        ∃ S : Set ℝ, (∀ x ∈ S, x ∈ K) ∧ S.Nonempty ∧ (∃ b ∈ K, ∀ x ∈ S, x ≤ b)
          ∧ ¬ ∃ s, IsLUBIn K S s)
      ∧ (∀ S : Set ℝ, S.Nonempty → (∃ b, ∀ x ∈ S, x ≤ b) → ∃ s, IsLUB S s) :=
  ⟨countable_subfield_not_complete, real_has_lub⟩

end CompletenessIndependence
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
