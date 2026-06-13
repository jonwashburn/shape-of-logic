import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.LawOfExistence
import IndisputableMonolith.Foundation.DiscretenessForcing
import IndisputableMonolith.Foundation.PhiForcing

/-!
# RS Ontology Predicates: RSExists and RSTrue

This module defines the **operational ontology** of Recognition Science.

## The Core Insight

In RS, existence and truth are not primitive notions - they are **selection outcomes**
determined by cost minimization under the unique J function.

## Definitions

- **RSExists x**: x is a stable configuration under J (defect collapses to 0)
- **RSTrue P**: P is stable under recognition iteration (doesn't drift)
- **RSReal x**: x is both existent and discrete (in the stable configuration space)

## The Selection Rule

```
x exists ⟺ defect(x) → 0 under coercive projection + aggregation
P is true ⟺ P stabilizes under recognition iteration
```

This makes "existence" and "truth" **verifiable** rather than **assumed**.

## Connection to Meta-Principle

The Meta-Principle "Nothing cannot recognize itself" becomes:
- MP_physical: defect(0⁺) = ∞, so "nothing" is not selectable
- This is a **derived consequence** of the cost structure, not a pre-logical axiom

## Key Theorems

1. `rs_exists_iff_defect_zero`: RSExists x ⟺ defect x = 0
2. `rs_exists_unique_at_one`: The only RSExistent value is 1
3. `nothing_not_rs_exists`: 0⁺ is not RSExistent (∀ ε > 0, ¬RSExists ε for small ε)
4. `mp_physical`: The Meta-Principle as a cost theorem
-/

namespace IndisputableMonolith
namespace Foundation
namespace OntologyPredicates

open Real
open LawOfExistence

/-! ## RSExists: Existence as Selection Outcome -/

/-- **RSExists**: A value x exists in the RS sense if:
    1. x > 0 (positive configuration)
    2. defect(x) = 0 (stable under J-cost)

    This is the operational definition of "existence" in RS.
    It's not assumed - it's the result of selection by cost minimization. -/
def RSExists (x : ℝ) : Prop := 0 < x ∧ defect x = 0

/-- RSExists is equivalent to the Law of Existence predicate. -/
theorem rs_exists_iff_law_exists {x : ℝ} :
    RSExists x ↔ LawOfExistence.Exists x := by
  constructor
  · intro ⟨hpos, hdef⟩
    exact ⟨hpos, hdef⟩
  · intro ⟨hpos, hdef⟩
    exact ⟨hpos, hdef⟩

/-- RSExists is equivalent to defect = 0 (for positive values). -/
theorem rs_exists_iff_defect_zero {x : ℝ} (hx : 0 < x) :
    RSExists x ↔ defect x = 0 := by
  constructor
  · intro ⟨_, hdef⟩; exact hdef
  · intro hdef; exact ⟨hx, hdef⟩

/-- The only RSExistent value is 1. -/
theorem rs_exists_unique_one : ∀ x : ℝ, RSExists x ↔ x = 1 := by
  intro x
  constructor
  · intro ⟨hpos, hdef⟩
    exact (defect_zero_iff_one hpos).mp hdef
  · intro hx
    rw [hx]
    exact ⟨by norm_num, defect_at_one⟩

/-- Unity is the unique RSExistent configuration. -/
theorem rs_exists_one : RSExists 1 := ⟨by norm_num, defect_at_one⟩

/-- There exists exactly one RSExistent value. -/
theorem rs_exists_unique : ∃! x : ℝ, RSExists x := by
  use 1
  constructor
  · exact rs_exists_one
  · intro y hy
    exact (rs_exists_unique_one y).mp hy

/-! ## Nothing Cannot RSExist -/

/-- For any threshold, sufficiently small positive values have defect exceeding it.
    This means "approaching nothing" has unbounded cost. -/
theorem nothing_unbounded_defect :
    ∀ C : ℝ, ∃ ε > 0, ∀ x, 0 < x → x < ε → C < defect x :=
  nothing_cannot_exist

/-- No value near zero is RSExistent.
    This is the operational content of "Nothing cannot recognize itself". -/
theorem nothing_not_rs_exists :
    ∃ ε > 0, ∀ x, 0 < x → x < ε → ¬RSExists x := by
  obtain ⟨ε, hε_pos, hε⟩ := nothing_unbounded_defect 1
  use ε, hε_pos
  intro x hx_pos hx_small ⟨_, hdef⟩
  have hC : 1 < defect x := hε x hx_pos hx_small
  rw [hdef] at hC
  linarith

/-! ## RSTrue: Truth as Stabilized Recognition -/

/-- A configuration-to-cost bridge: maps a configuration to the scalar
    cost-input via observable and scale maps relative to a reference. -/
structure CostBridge (C : Type*) where
  χ : C → ℝ
  χ_pos : ∀ c, 0 < χ c

/-- A predicate stabilizes along the orbit of `B` from seed `c₀` to the
    value it takes at `c_star`, meaning the orbit eventually agrees with
    `c_star` on `P`. -/
def Stabilizes {C : Type*} (B : C → C) (P : C → Bool) (c₀ c_star : C) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → P (B^[n] c₀) = P c_star

/-- Configuration-level existence: `c` exists iff its cost-bridge
    image has zero defect, i.e. `χ(c) = 1`. -/
def RSExists_cfg {C : Type*} (bridge : CostBridge C) (c : C) : Prop :=
  RSExists (bridge.χ c)

/-- **RSTrue**: A predicate `P` is RS-true at `c_star` under dynamics `B`
    from seed `c₀` if:
    1. `c_star` exists (its cost-bridge value has zero defect),
    2. `P` holds at `c_star`,
    3. `P` stabilizes along the orbit to the value at `c_star`.

    This replaces the placeholder `def RSTrue (P : Prop) : Prop := P`. -/
def RSTrue {C : Type*}
    (bridge : CostBridge C) (B : C → C) (c₀ c_star : C) (P : C → Bool) : Prop :=
  RSExists_cfg bridge c_star ∧ P c_star = true ∧ Stabilizes B P c₀ c_star

/-! ## RS-Decidability and Boolean Laws -/

/-- A predicate is **RS-decidable** at `(c_star, B, c₀)` when the background
    conditions for Boolean reasoning hold: existence and stabilization. -/
def RSDecidable {C : Type*}
    (bridge : CostBridge C) (B : C → C) (c₀ c_star : C) (P : C → Bool) : Prop :=
  RSExists_cfg bridge c_star ∧ Stabilizes B P c₀ c_star

/-- One direction always holds: RSTrue(¬P) ⟹ ¬RSTrue(P). -/
theorem rs_true_neg_imp_neg_rs_true {C : Type*}
    {bridge : CostBridge C} {B : C → C} {c₀ c_star : C} {P : C → Bool} :
    RSTrue bridge B c₀ c_star (fun c => !P c) → ¬RSTrue bridge B c₀ c_star P := by
  intro ⟨_, hval, _⟩ ⟨_, hval', _⟩
  simp at hval
  rw [hval] at hval'
  exact Bool.false_ne_true hval'

/-- Under RS-decidability the full negation law holds. -/
theorem rs_true_neg_iff_neg_rs_true {C : Type*}
    {bridge : CostBridge C} {B : C → C} {c₀ c_star : C} {P : C → Bool}
    (hdec : RSDecidable bridge B c₀ c_star P) :
    RSTrue bridge B c₀ c_star (fun c => !P c) ↔ ¬RSTrue bridge B c₀ c_star P := by
  constructor
  · exact rs_true_neg_imp_neg_rs_true
  · intro hnotP
    have ⟨hexists, hstab⟩ := hdec
    by_cases hv : P c_star = true
    · exfalso; exact hnotP ⟨hexists, hv, hstab⟩
    · push_neg at hv
      have hv' : P c_star = false := Bool.eq_false_iff.mpr hv
      refine ⟨hexists, ?_, ?_⟩
      · simp [hv']
      · obtain ⟨N, hN⟩ := hstab
        exact ⟨N, fun n hn => by simp [hN n hn, hv']⟩

/-- RSTrue under conjunction: both must be RS-true. -/
theorem rs_true_and {C : Type*}
    {bridge : CostBridge C} {B : C → C} {c₀ c_star : C}
    {P Q : C → Bool} :
    RSTrue bridge B c₀ c_star (fun c => P c && Q c) ↔
    RSTrue bridge B c₀ c_star P ∧ RSTrue bridge B c₀ c_star Q := by
  unfold RSTrue Stabilizes
  constructor
  · intro ⟨hex, hval, N, hN⟩
    have hpv : P c_star = true := by cases hp : P c_star <;> simp_all
    have hqv : Q c_star = true := by cases hq : Q c_star <;> simp_all
    constructor
    · refine ⟨hex, hpv, N, fun n hn => ?_⟩
      have h := hN n hn; simp only at h
      cases hp : P (B^[n] c₀) <;> simp_all
    · refine ⟨hex, hqv, N, fun n hn => ?_⟩
      have h := hN n hn; simp only at h
      cases hq : Q (B^[n] c₀) <;> simp_all
  · intro ⟨⟨hex, hvP, NP, hNP⟩, ⟨_, hvQ, NQ, hNQ⟩⟩
    refine ⟨hex, by simp only; rw [hvP, hvQ]; rfl, max NP NQ, fun n hn => ?_⟩
    simp only
    rw [hNP n ((le_max_left NP NQ).trans hn), hNQ n ((le_max_right NP NQ).trans hn)]

/-! ## Classical wrapper (backward compatibility) -/

/-- Classical RSTrue: for pure propositions without dynamics context.
    Equivalent to the old placeholder `def RSTrue (P : Prop) : Prop := P`. -/
def RSTrue_classical (P : Prop) : Prop := P

theorem rs_true_classical_iff (P : Prop) : RSTrue_classical P ↔ P := Iff.rfl

/-! ## RSReal: Existence in the Discrete Configuration Space -/

/-- **RSReal**: A value x is "real" in the RS sense if:
    1. RSExists x (stable under J)
    2. x is in the discrete configuration space (quantized)

    For now, we model discreteness as being algebraic in φ. -/
def RSReal (x : ℝ) : Prop :=
  RSExists x ∧ ∃ n m : ℤ, x = PhiForcing.φ ^ n * PhiForcing.φ ^ m

/-- Unity is RSReal (trivially, as φ⁰ · φ⁰ = 1). -/
theorem rs_real_one : RSReal 1 := by
  constructor
  · exact rs_exists_one
  · use 0, 0
    simp [PhiForcing.φ]

/-! ## The Meta-Principle as a Physical Theorem -/

/-- **MP_PHYSICAL**: The Meta-Principle "Nothing cannot recognize itself"
    as a theorem about cost.

    In the CPM/cost foundation, this is DERIVED, not assumed:
    - "Nothing" (x → 0⁺) has unbounded defect
    - Therefore "nothing" cannot be selected by cost minimization
    - Therefore "something" must exist (the unique x=1 minimizer)

    This replaces the tautological "Empty has no inhabitants" with
    a physical statement about selection. -/
theorem mp_physical :
    (∀ C : ℝ, ∃ ε > 0, ∀ x, 0 < x → x < ε → C < defect x) ∧  -- Nothing is infinitely expensive
    (∃! x : ℝ, RSExists x) ∧  -- There exists exactly one existent thing
    (∀ x, RSExists x → x = 1)  -- That thing is unity
  := ⟨nothing_cannot_exist, rs_exists_unique, fun x hx => (rs_exists_unique_one x).mp hx⟩

/-- The Meta-Principle forces existence: since nothing is not selectable,
    something must be selected. -/
theorem mp_forces_existence :
    (∀ C : ℝ, ∃ ε > 0, ∀ x, 0 < x → x < ε → C < defect x) →
    ∃ x : ℝ, RSExists x := by
  intro _
  exact ⟨1, rs_exists_one⟩

/-! ## Categorical Distinctness Between RS Closure and Gödel I

The two structures below are **documentation records, not theorems**.
Their fields are `Prop` placeholders; the canonical inhabitants set every
field to `True`. They package the philosophical/categorical claim that
the RS closure question (uniqueness of the cost minimizer) and Gödel I
(incompleteness of recursively axiomatized arithmetic) are about
different objects.

The historical naming (`GodelDissolution`, `godel_dissolution`,
`godel_not_obstruction`) overstated what is recorded here. None of these
declarations is a refutation of Gödel I or a proof that RS escapes
incompleteness. The substantive argument lives in the prose of
`papers/Godel_And_RS_Closure_Honest_Assessment_20260520.html` and is a
meta-level categorical claim, not a Lean theorem.

The companion arithmetic-recovery paper
(`papers/RS_Arithmetic_From_Law_Of_Logic.pdf`) and the functional-equation
paper (`Logic_Functional_Equation.tex`) state the honest position: the
recovered arithmetic inherits incompleteness from Gödel I; RS closure
(uniqueness of the J-minimum and the forcing chain to constants) is a
categorically different question, not affected by incompleteness of the
downstream arithmetic theory.
-/

/-- Documentation record: RS closure and Gödel I target different objects.
Each field is a `Prop` placeholder; the canonical inhabitant has every
field set to `True`. Not a theorem. -/
structure RsAndGodelCategoricalDistinctness where
  /-- RS closure is about selection / uniqueness of cost minimum. -/
  rs_is_selection : Prop
  /-- Gödel I is about provability inside recursively axiomatized arithmetic. -/
  godel_is_about_proof : Prop
  /-- These are categorically different targets; one does not bear on the
  other in the direct sense. -/
  different_targets : rs_is_selection → godel_is_about_proof → True

/-- Canonical inhabitant of `RsAndGodelCategoricalDistinctness` with each
philosophical field set to `True`. Documentation, not a theorem. -/
def rs_and_godel_categorical_distinctness : RsAndGodelCategoricalDistinctness := {
  rs_is_selection := True
  godel_is_about_proof := True
  different_targets := fun _ _ => trivial
}

/-- **Deprecated.** Renamed to `RsAndGodelCategoricalDistinctness`. -/
@[deprecated "Renamed to RsAndGodelCategoricalDistinctness" (since := "2026-05-20")]
abbrev GodelDissolution := RsAndGodelCategoricalDistinctness

/-- **Deprecated.** Renamed to `rs_and_godel_categorical_distinctness`. -/
@[deprecated "Renamed to rs_and_godel_categorical_distinctness" (since := "2026-05-20")]
def godel_dissolution : RsAndGodelCategoricalDistinctness :=
  rs_and_godel_categorical_distinctness

/-- Vacuous statement (`True → True`): given uniqueness of the RS existent,
no obstruction is derived from a trivial Gödel premise. The body is
`fun _ _ => trivial`; there is no theorem content here. The historical
name `godel_not_obstruction` overstated what this records.

The honest version of this claim ("Gödel I does not directly target the
RS forcing chain") is meta-level prose, not a Lean theorem. -/
theorem rs_closure_vacuous_under_godel_premise :
    (∃! x : ℝ, RSExists x) →
    True →
    True := by
  intro _ _; trivial

/-- **Deprecated.** Renamed to `rs_closure_vacuous_under_godel_premise`. -/
@[deprecated "Renamed to rs_closure_vacuous_under_godel_premise" (since := "2026-05-20")]
theorem godel_not_obstruction :
    (∃! x : ℝ, RSExists x) →
    True →
    True := rs_closure_vacuous_under_godel_premise

/-! ## Summary: The Ontology Stack -/

/-- **ONTOLOGY_SUMMARY**: The RS ontology predicates form a coherent stack:

    1. **RSExists**: x exists ⟺ defect(x) = 0 ⟺ x = 1
    2. **RSTrue**: P is RS-true at c_star ⟺ c_star exists ∧ P(c_star) ∧ P stabilizes
       Boolean laws (e.g. RSTrue(¬P) ⟺ ¬RSTrue(P)) hold on the RS-decidable domain.
    3. **RSReal**: x is real ⟺ RSExists x ∧ x is discrete (algebraic in φ)

    The Meta-Principle emerges as:
    - "Nothing" (x → 0⁺) has unbounded defect
    - Therefore only x = 1 is selected
    - Therefore existence is forced -/
theorem ontology_summary :
    (∀ x : ℝ, RSExists x ↔ x = 1) ∧
    (∃! x : ℝ, RSExists x) ∧
    (∃ ε > 0, ∀ x, 0 < x → x < ε → ¬RSExists x) ∧
    (∀ C : ℝ, ∃ ε > 0, ∀ x, 0 < x → x < ε → C < defect x) :=
  ⟨rs_exists_unique_one, rs_exists_unique, nothing_not_rs_exists, nothing_cannot_exist⟩

/-! ## Disjunction Law for RSTrue (Paper Theorem 3.5 / Proposition 3.4)

The paper proves that RSTrue distributes over disjunction:
- One direction (Proposition 3.4): RSTrue(P) ∨ RSTrue(Q) ⟹ RSTrue(P ∨ Q)
- Converse under RS-decidability (Theorem 3.5): RSTrue(P ∨ Q) ⟹ RSTrue(P) ∨ RSTrue(Q)
-/

/-- RSTrue(P) implies RSTrue(P ∨ Q). (Proposition 3.4, left case) -/
theorem rs_true_or_of_left {C : Type*}
    {bridge : CostBridge C} {B : C → C} {c₀ c_star : C}
    {P Q : C → Bool} :
    RSTrue bridge B c₀ c_star P →
    RSTrue bridge B c₀ c_star (fun c => P c || Q c) := by
  intro ⟨hex, hval, N, hN⟩
  refine ⟨hex, by simp [hval], N, fun n hn => ?_⟩
  simp [hN n hn, hval]

/-- RSTrue(Q) implies RSTrue(P ∨ Q). (Proposition 3.4, right case) -/
theorem rs_true_or_of_right {C : Type*}
    {bridge : CostBridge C} {B : C → C} {c₀ c_star : C}
    {P Q : C → Bool} :
    RSTrue bridge B c₀ c_star Q →
    RSTrue bridge B c₀ c_star (fun c => P c || Q c) := by
  intro ⟨hex, hval, N, hN⟩
  refine ⟨hex, by simp [hval], N, fun n hn => ?_⟩
  simp [hN n hn, hval]

/-- RSTrue(P) ∨ RSTrue(Q) ⟹ RSTrue(P ∨ Q). (Proposition 3.4) -/
theorem rs_true_or_intro {C : Type*}
    {bridge : CostBridge C} {B : C → C} {c₀ c_star : C}
    {P Q : C → Bool} :
    RSTrue bridge B c₀ c_star P ∨ RSTrue bridge B c₀ c_star Q →
    RSTrue bridge B c₀ c_star (fun c => P c || Q c) := by
  rintro (hp | hq)
  · exact rs_true_or_of_left hp
  · exact rs_true_or_of_right hq

/-- Under RS-decidability of both P and Q:
    RSTrue(P ∨ Q) ⟺ RSTrue(P) ∨ RSTrue(Q). (Theorem 3.5) -/
theorem rs_true_or_iff {C : Type*}
    {bridge : CostBridge C} {B : C → C} {c₀ c_star : C}
    {P Q : C → Bool}
    (hdecP : RSDecidable bridge B c₀ c_star P)
    (hdecQ : RSDecidable bridge B c₀ c_star Q) :
    RSTrue bridge B c₀ c_star (fun c => P c || Q c) ↔
    RSTrue bridge B c₀ c_star P ∨ RSTrue bridge B c₀ c_star Q := by
  constructor
  · intro ⟨hex, hval, _⟩
    cases hP : P c_star
    · cases hQ : Q c_star
      · simp [hP, hQ] at hval
      · exact Or.inr ⟨hex, hQ, hdecQ.2⟩
    · exact Or.inl ⟨hex, hP, hdecP.2⟩
  · exact rs_true_or_intro

/-! ## Decomposed Recognition Bridge (Paper §1.1, Eq. 5–6)

The paper decomposes the cost bridge χ(c) = ι(R(c))/ι(R(c_ref)) into:
- A recognizer R : C → E (observable map)
- A scale map ι : E → ℝ₊ (positive-definite embedding)
- A reference configuration c_ref

This richer structure supports the identity↔zero-cost chain
(Paper Eq. 15–17) which requires injectivity of ι.
-/

structure RecognitionBridge (C : Type*) (E : Type*) where
  R : C → E
  ι : E → ℝ
  ι_pos : ∀ e, 0 < ι e
  c_ref : C

noncomputable def RecognitionBridge.ratio {C E : Type*}
    (b : RecognitionBridge C E) (c : C) : ℝ :=
  b.ι (b.R c) / b.ι (b.R b.c_ref)

lemma RecognitionBridge.ratio_pos {C E : Type*}
    (b : RecognitionBridge C E) (c : C) : 0 < b.ratio c :=
  div_pos (b.ι_pos _) (b.ι_pos _)

noncomputable def RecognitionBridge.toCostBridge {C E : Type*}
    (b : RecognitionBridge C E) : CostBridge C where
  χ := b.ratio
  χ_pos := b.ratio_pos

/-- Pairwise comparison ratio: x_{ab} = ι(R(a)) / ι(R(c)). -/
noncomputable def RecognitionBridge.pairRatio {C E : Type*}
    (b : RecognitionBridge C E) (a c : C) : ℝ :=
  b.ι (b.R a) / b.ι (b.R c)

lemma RecognitionBridge.pairRatio_pos {C E : Type*}
    (b : RecognitionBridge C E) (a c : C) : 0 < b.pairRatio a c :=
  div_pos (b.ι_pos _) (b.ι_pos _)

/-! ## Event-Space Equivalence Pipeline (Paper §3.1, Eq. 15–17)

The paper derives the chain:
  J(x_{ab}) = 0 ⟺ x_{ab} = 1 ⟺ ι(R(a)) = ι(R(b))
  → (if ι injective) R(a) = R(b) ⟺ a ~_n b
  → (if R injective, i.e. R = R_all) a = b

And the reverse: a = b ⟹ J(x_{ab}) = 0 (no injectivity needed).
-/

theorem RecognitionBridge.zero_cost_iff_ratio_one {C E : Type*}
    (b : RecognitionBridge C E) (a c : C) :
    defect (b.pairRatio a c) = 0 ↔ b.pairRatio a c = 1 :=
  defect_zero_iff_one (b.pairRatio_pos a c)

theorem RecognitionBridge.ratio_one_iff_equal_scale {C E : Type*}
    (b : RecognitionBridge C E) (a c : C) :
    b.pairRatio a c = 1 ↔ b.ι (b.R a) = b.ι (b.R c) := by
  constructor
  · intro h
    have hne := ne_of_gt (b.ι_pos (b.R c))
    unfold pairRatio at h
    rwa [div_eq_iff hne, one_mul] at h
  · intro h
    unfold pairRatio
    rw [h, div_self (ne_of_gt (b.ι_pos _))]

/-- Zero cost + injective ι ⟹ equal events: R(a) = R(c). (Paper Eq. 15) -/
theorem RecognitionBridge.zero_cost_implies_equal_recognition {C E : Type*}
    (b : RecognitionBridge C E) (hInj : Function.Injective b.ι)
    (a c : C) (h : defect (b.pairRatio a c) = 0) :
    b.R a = b.R c :=
  hInj ((b.ratio_one_iff_equal_scale a c).mp ((b.zero_cost_iff_ratio_one a c).mp h))

/-- Zero cost + injective ι + injective R ⟹ state equality: a = c. (Paper Eq. 17) -/
theorem RecognitionBridge.zero_cost_injective_R_implies_eq {C E : Type*}
    (b : RecognitionBridge C E)
    (hι_inj : Function.Injective b.ι)
    (hR_inj : Function.Injective b.R)
    (a c : C) (h : defect (b.pairRatio a c) = 0) :
    a = c :=
  hR_inj (b.zero_cost_implies_equal_recognition hι_inj a c h)

/-- Reverse direction: identity implies zero cost (no injectivity needed).
    (Paper §3.1.2) -/
theorem RecognitionBridge.identity_implies_zero_cost {C E : Type*}
    (b : RecognitionBridge C E) (a : C) :
    defect (b.pairRatio a a) = 0 := by
  have h1 : b.pairRatio a a = 1 := by
    unfold pairRatio
    exact div_self (ne_of_gt (b.ι_pos _))
  exact (b.zero_cost_iff_ratio_one a a).mpr h1

/-! ## General RSReal with Discrete Skeleton (Paper §1.1, Eq. 8–9)

The paper defines RSReal with a general discrete skeleton D ⊆ ℝ
and a synthesis-map variant RSReal_{F,D_U}(x).
-/

/-- RSReal with a general discrete skeleton D ⊆ ℝ. (Paper Eq. 8) -/
def RSReal_gen (D : Set ℝ) (x : ℝ) : Prop :=
  RSExists x ∧ x ∈ D

/-- RSReal with synthesis map F : U → ℝ and discrete skeleton D ⊆ U. (Paper Eq. 9) -/
def RSReal_synth {U : Type*} (D : Set U) (F : U → ℝ) (x : ℝ) : Prop :=
  RSExists x ∧ ∃ u ∈ D, x = F u

theorem RSReal_gen_at_one {D : Set ℝ} (hD : (1 : ℝ) ∈ D) : RSReal_gen D 1 :=
  ⟨rs_exists_one, hD⟩

theorem RSReal_gen_iff {D : Set ℝ} {x : ℝ} :
    RSReal_gen D x ↔ x = 1 ∧ x ∈ D := by
  simp only [RSReal_gen, rs_exists_unique_one]

theorem RSReal_synth_iff {U : Type*} {D : Set U} {F : U → ℝ} {x : ℝ} :
    RSReal_synth D F x ↔ x = 1 ∧ ∃ u ∈ D, x = F u := by
  simp only [RSReal_synth, rs_exists_unique_one]

/-- The φ-ladder as a specific discrete skeleton. -/
noncomputable def phi_ladder : Set ℝ :=
  {x | ∃ n : ℤ, x = PhiForcing.φ ^ n}

theorem one_mem_phi_ladder : (1 : ℝ) ∈ phi_ladder :=
  ⟨0, by simp [PhiForcing.φ]⟩

theorem RSReal_gen_phi_one : RSReal_gen phi_ladder 1 :=
  RSReal_gen_at_one one_mem_phi_ladder

/-! ## Numeric Verification of Paper Examples (Section 4.1)

The paper uses concrete J-cost values in Tables 1–3.
We verify each value used.
-/

theorem Jcost_val_2 : Cost.Jcost 2 = 1 / 4 := by
  unfold Cost.Jcost; norm_num

theorem Jcost_val_4 : Cost.Jcost 4 = 9 / 8 := by
  unfold Cost.Jcost; norm_num

theorem Jcost_val_5 : Cost.Jcost 5 = 8 / 5 := by
  unfold Cost.Jcost; norm_num

theorem Jcost_val_6 : Cost.Jcost 6 = 25 / 12 := by
  unfold Cost.Jcost; norm_num

theorem Jcost_val_8 : Cost.Jcost 8 = 49 / 16 := by
  unfold Cost.Jcost; norm_num

/-- J(1/2) = J(2) by reciprocal symmetry (used in Example 3). -/
theorem Jcost_val_half : Cost.Jcost (1 / 2) = 1 / 4 := by
  unfold Cost.Jcost; norm_num

/-- J(3/2) = 1/12 (used in Example 3, Table 3). -/
theorem Jcost_val_three_halves : Cost.Jcost (3 / 2) = 1 / 12 := by
  unfold Cost.Jcost; norm_num

end OntologyPredicates
end Foundation
end IndisputableMonolith
