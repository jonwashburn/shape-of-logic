/-
  LogicAsFunctionalEquation.lean

  DRAFT for the precursor paper "The Law of Logic as Functional Equation:
  A Logical Formalization of the Recognition Composition Law."

  Intended canonical location:
    reality/IndisputableMonolith/Foundation/LogicAsFunctionalEquation.lean

  Status:
    Level 1 of three (translation theorem; takes the d'Alembert Inevitability
    Theorem and the canonical reciprocal cost uniqueness theorem as published
    citations and invokes them as black boxes).

  Strategy:
    1. Define a ComparisonOperator C : ℝ → ℝ → ℝ.
    2. Encode the four Aristotelian constraints (identity, non-contradiction,
       excluded middle, route-independence) as Lean predicates on C, with
       scale-invariance as the bridge from C-level to F-level statements.
    3. Define the derived cost function F(r) := C(r, 1).
    4. Prove the four constraints imply the hypotheses of
       `bilinear_family_forced` (Inevitability.lean) and
       `law_of_logic_forces_jcost` (FunctionalEquation.lean).
    5. Conclude the Recognition Composition Law and the canonical reciprocal
       cost J(x) = ½(x + 1/x) − 1 are the unique functional form and the
       unique continuous cost compatible with the laws of logic on continuous
       comparisons of positive ratios.

  Honest caveat (carried in the precursor paper's Discussion):
    The polynomial restriction on the route-independence combiner is a
    regularity assumption inherited from the d'Alembert Inevitability Theorem.
    Level 2 (planned in `Foundation/GeneralizedDAlembert.lean`) will replace
    polynomiality with continuity using the classical Aczél–Kannappan–Stetkær
    classification of continuous d'Alembert solutions.

  References:
    - Washburn, Zlatanović, Allahyarov.
      "The d'Alembert Inevitability Theorem."
      Mathematics (MDPI), 2026.
      Lean module: `IndisputableMonolith.Foundation.DAlembert.Inevitability`.
    - Washburn, Zlatanović.
      "Uniqueness of the Canonical Reciprocal Cost."
      Mathematics 14 (2026), 935.
      Lean module: `IndisputableMonolith.Cost.FunctionalEquation`.
-/

import Mathlib
import IndisputableMonolith.Foundation.DAlembert.Inevitability
import IndisputableMonolith.Cost.FunctionalEquation

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

open Real
open IndisputableMonolith.Foundation.DAlembert.Inevitability

/-! ## The Comparison Operator -/

/-- A comparison operator on positive reals takes two positive quantities and
returns a real-valued cost of comparing them. The four Aristotelian
constraints below are the structural content of comparison being a
well-posed operation. -/
abbrev ComparisonOperator := ℝ → ℝ → ℝ

/-- The cost function derived from a comparison operator by fixing the
second argument at the multiplicative identity. Under scale invariance,
this is well-defined on the multiplicative group of positive ratios. -/
@[simp] def derivedCost (C : ComparisonOperator) : ℝ → ℝ :=
  fun r => C r 1

/-! ## The Four Aristotelian Constraints

We encode the classical laws of logic as structural constraints on a
comparison operator. The mapping from Aristotle's propositional
formulations to functional constraints on C is:

  Identity (A = A)             ↦  C(x, x) = 0
                                  comparison of a thing with itself is trivial
  Non-contradiction (¬(A ∧ ¬A))↦  C(x, y) = C(y, x)
                                  the cost is single-valued under reordering
                                  (with scale invariance, this gives reciprocity
                                   F(x) = F(1/x))
  Excluded middle (A ∨ ¬A)     ↦  C is continuous and total on its domain
                                  every comparison returns a definite value
  Composition consistency      ↦  Route-independence (the d'Alembert form)
                                  comparisons assembled forward and backward
                                  must compose by a fixed combining rule
-/

/-- **Identity**: comparing a thing with itself costs zero. The mathematical
counterpart of the Aristotelian law A = A. -/
def Identity (C : ComparisonOperator) : Prop :=
  ∀ x : ℝ, 0 < x → C x x = 0

/-- **Non-contradiction (reciprocal symmetry)**: the cost of comparing x to y
equals the cost of comparing y to x. The mathematical counterpart of the
Aristotelian law ¬(A ∧ ¬A): if comparison were not single-valued under
reordering, the same comparison would simultaneously hold and not hold. -/
def NonContradiction (C : ComparisonOperator) : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y → C x y = C y x

/-- **Excluded middle (totality and continuity)**: every comparison returns a
definite real value and small perturbations of inputs give small
perturbations of cost. The mathematical counterpart of the Aristotelian
law A ∨ ¬A applied to continuous comparisons: there is no "neither" outcome
on the comparison's domain. -/
def ExcludedMiddle (C : ComparisonOperator) : Prop :=
  ContinuousOn (Function.uncurry C) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))

/-- **Scale invariance**: the cost of a comparison depends only on the
ratio of the two quantities. This is the structural bridge from a
two-argument comparison operator to a one-argument cost on positive ratios.
It is what allows the four laws of logic, which make no reference to absolute
scale, to be expressed as constraints on the multiplicative group ℝ₊. -/
def ScaleInvariant (C : ComparisonOperator) : Prop :=
  ∀ x y lam : ℝ, 0 < x → 0 < y → 0 < lam →
    C (lam * x) (lam * y) = C x y

/-- **Route-independence (the d'Alembert form)**: the cost of any composite
comparison, taken in its symmetric forward-and-backward form on positive
ratios, is a polynomial function of the constituent ratio costs.
Concretely: assembling a comparison of ratio xy with a comparison of ratio
x/y (the symmetric forward+backward decomposition) gives a total cost that
is some fixed polynomial in the costs of the individual ratios x and y.
The polynomial restriction is the Level-1 regularity assumption; Level 2
will replace it with continuity. -/
def RouteIndependence (C : ComparisonOperator) : Prop :=
  ∃ P : ℝ → ℝ → ℝ,
    -- P is a polynomial in two variables of degree ≤ 2.
    (∃ a b c d e f : ℝ, ∀ u v, P u v = a + b*u + c*v + d*u*v + e*u^2 + f*v^2) ∧
    -- P is symmetric (consequence of non-contradiction at the combiner level).
    (∀ u v, P u v = P v u) ∧
    -- The d'Alembert composition law on the derived cost function.
    (∀ x y : ℝ, 0 < x → 0 < y →
       derivedCost C (x * y) + derivedCost C (x / y)
       = P (derivedCost C x) (derivedCost C y))

/-- A comparison operator is **non-trivial** if there exists at least one
positive ratio with non-zero cost. (Without this assumption the constant zero
function vacuously satisfies all the constraints.) -/
def NonTrivial (C : ComparisonOperator) : Prop :=
  ∃ x : ℝ, 0 < x ∧ derivedCost C x ≠ 0

/-- A comparison operator **satisfies the laws of logic** if all four
Aristotelian constraints hold, together with scale invariance (the bridge
from two-argument to one-argument form) and non-triviality (so that the
derived cost is not vacuously zero). -/
structure SatisfiesLawsOfLogic (C : ComparisonOperator) : Prop where
  identity            : Identity C
  non_contradiction   : NonContradiction C
  excluded_middle     : ExcludedMiddle C
  scale_invariant     : ScaleInvariant C
  route_independence  : RouteIndependence C
  non_trivial         : NonTrivial C

/-- Public short name for the continuous positive-ratio Law of Logic.

The longer historical name `SatisfiesLawsOfLogic` remains the underlying
structure used by existing proofs.  This alias is the theorem-facing formula:
a comparison operator satisfies the Law of Logic exactly when it satisfies
identity, non-contradiction, excluded middle/continuity, scale invariance,
route independence, and non-triviality. -/
abbrev LawOfLogic (C : ComparisonOperator) : Prop :=
  SatisfiesLawsOfLogic C

/-- Expanded formula for the continuous positive-ratio Law of Logic. -/
theorem lawOfLogic_iff (C : ComparisonOperator) :
    LawOfLogic C ↔
      Identity C ∧
      NonContradiction C ∧
      ExcludedMiddle C ∧
      ScaleInvariant C ∧
      RouteIndependence C ∧
      NonTrivial C := by
  constructor
  · intro h
    exact ⟨h.identity, h.non_contradiction, h.excluded_middle,
      h.scale_invariant, h.route_independence, h.non_trivial⟩
  · rintro ⟨hId, hNC, hEM, hSI, hRI, hNT⟩
    exact
      { identity := hId
        non_contradiction := hNC
        excluded_middle := hEM
        scale_invariant := hSI
        route_independence := hRI
        non_trivial := hNT }

/-! ## Translation Lemmas

The four Aristotelian constraints, applied to the derived cost function
F(r) := C(r, 1), produce the hypotheses of the d'Alembert Inevitability
Theorem.
-/

/-- **Translation lemma 1 (Identity ⇒ Normalization)**: If a comparison
operator satisfies Identity, then the derived cost function takes value
zero at the multiplicative identity. -/
theorem identity_implies_normalized (C : ComparisonOperator)
    (hId : Identity C) :
    IsNormalized (derivedCost C) := by
  unfold IsNormalized derivedCost
  exact hId 1 one_pos

/-- **Translation lemma 2 (Non-contradiction + Scale invariance ⇒ Reciprocity)**:
If a comparison operator is single-valued under argument reordering and
depends only on ratios, then the derived cost function is invariant under
inversion of its argument: F(x) = F(1/x).

The chain of equalities:
  F(x) = C(x, 1)                       definition of derivedCost
       = C(1, x)                       non-contradiction
       = C(x⁻¹·1, x⁻¹·x)               scale invariance (multiply both args by x⁻¹)
       = C(x⁻¹, 1)                     simplify (x⁻¹·1 = x⁻¹, x⁻¹·x = 1)
       = F(x⁻¹)                        definition of derivedCost
-/
theorem non_contradiction_and_scale_imply_reciprocal
    (C : ComparisonOperator)
    (hNC : NonContradiction C)
    (hSI : ScaleInvariant C) :
    IsSymmetric (derivedCost C) := by
  intro x hx
  have hxinv : (0 : ℝ) < x⁻¹ := inv_pos.mpr hx
  have hx_ne : (x : ℝ) ≠ 0 := ne_of_gt hx
  -- Step 1: C(x, 1) = C(1, x) by non-contradiction.
  have h1 : C x 1 = C 1 x := hNC x 1 hx one_pos
  -- Step 2: scale invariance with x' = 1, y' = x, λ = x⁻¹ gives
  --   C(x⁻¹·1, x⁻¹·x) = C(1, x), so C(1, x) = C(x⁻¹·1, x⁻¹·x).
  have h2 : C 1 x = C (x⁻¹ * 1) (x⁻¹ * x) :=
    (hSI 1 x x⁻¹ one_pos hx hxinv).symm
  -- Step 3: simplify x⁻¹·1 = x⁻¹ and x⁻¹·x = 1.
  have h3 : C (x⁻¹ * 1) (x⁻¹ * x) = C x⁻¹ 1 := by
    rw [mul_one, inv_mul_cancel₀ hx_ne]
  show derivedCost C x = derivedCost C x⁻¹
  unfold derivedCost
  exact h1.trans (h2.trans h3)

/-- **Translation lemma 3 (Excluded middle ⇒ Continuity)**: If a comparison
operator is jointly continuous in both arguments on the positive quadrant,
then the derived cost function is continuous on (0, ∞).

The derivedCost C is the composition r ↦ (r, 1) ↦ C(r, 1). The pair-map is
continuous everywhere; the uncurried C is continuous on the positive
quadrant by ExcludedMiddle. The pair-map sends (0, ∞) into the positive
quadrant. Hence the composition is continuous on (0, ∞). -/
theorem excluded_middle_implies_continuous
    (C : ComparisonOperator)
    (hEM : ExcludedMiddle C) :
    ContinuousOn (derivedCost C) (Set.Ioi 0) := by
  -- Pair-map r ↦ (r, 1) is continuous everywhere.
  have h_pair_cont : Continuous (fun s : ℝ => ((s, (1 : ℝ)) : ℝ × ℝ)) :=
    continuous_id.prodMk continuous_const
  have h_pair_on : ContinuousOn (fun s : ℝ => ((s, (1 : ℝ)) : ℝ × ℝ))
      (Set.Ioi (0 : ℝ)) :=
    h_pair_cont.continuousOn
  -- Pair-map sends (0,∞) into the positive quadrant.
  have h_maps : Set.MapsTo (fun s : ℝ => ((s, (1 : ℝ)) : ℝ × ℝ))
      (Set.Ioi (0 : ℝ)) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    intro s hs
    refine ⟨?_, ?_⟩
    · exact hs
    · show (0 : ℝ) < 1
      exact one_pos
  -- Compose to get continuity of (uncurry C) ∘ pair on (0,∞).
  have h_comp : ContinuousOn
      ((Function.uncurry C) ∘ fun s : ℝ => ((s, (1 : ℝ)) : ℝ × ℝ))
      (Set.Ioi (0 : ℝ)) :=
    hEM.comp h_pair_on h_maps
  -- The composition equals derivedCost C definitionally.
  have h_eq : ((Function.uncurry C) ∘ fun s : ℝ => ((s, (1 : ℝ)) : ℝ × ℝ))
              = derivedCost C := by
    funext s
    rfl
  rw [h_eq] at h_comp
  exact h_comp

/-- **Translation lemma 4 (Route-independence ⇒ Multiplicative consistency
with a symmetric polynomial combiner)**: extracted directly from the
definition of `RouteIndependence`. -/
theorem route_independence_implies_multiplicative_consistency
    (C : ComparisonOperator)
    (hRI : RouteIndependence C) :
    ∃ P : ℝ → ℝ → ℝ,
      (∃ a b c d e f : ℝ, ∀ u v, P u v = a + b*u + c*v + d*u*v + e*u^2 + f*v^2) ∧
      (∀ u v, P u v = P v u) ∧
      HasMultiplicativeConsistency (derivedCost C) P := by
  obtain ⟨P, hPoly, hSym, hCons⟩ := hRI
  refine ⟨P, hPoly, hSym, ?_⟩
  intro x y hx hy
  exact hCons x y hx hy

/-! ## The Translation Theorem -/

/-- **Translation Theorem**: A comparison operator satisfying the four
Aristotelian constraints, together with scale invariance and non-triviality,
satisfies the hypotheses of the d'Alembert Inevitability Theorem on its
derived cost function.

This is the core technical content of the precursor paper. Once this is in
hand, the existing peer-reviewed and machine-verified theorems
(`bilinear_family_forced`, `law_of_logic_forces_jcost`) close the chain. -/
theorem laws_of_logic_imply_dalembert_hypotheses
    (C : ComparisonOperator) (hLaws : SatisfiesLawsOfLogic C) :
    IsNormalized (derivedCost C) ∧
    IsSymmetric (derivedCost C) ∧
    (∃ P : ℝ → ℝ → ℝ,
      (∃ a b c d e f : ℝ, ∀ u v, P u v = a + b*u + c*v + d*u*v + e*u^2 + f*v^2) ∧
      (∀ u v, P u v = P v u) ∧
      HasMultiplicativeConsistency (derivedCost C) P) ∧
    ContinuousOn (derivedCost C) (Set.Ioi 0) ∧
    (∃ x : ℝ, 0 < x ∧ derivedCost C x ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact identity_implies_normalized C hLaws.identity
  · exact non_contradiction_and_scale_imply_reciprocal C
      hLaws.non_contradiction hLaws.scale_invariant
  · exact route_independence_implies_multiplicative_consistency C
      hLaws.route_independence
  · exact excluded_middle_implies_continuous C hLaws.excluded_middle
  · exact hLaws.non_trivial

/-! ## Main Theorem: RCL is the Unique Functional Form of the Laws of Logic -/

/-- **Main theorem (Logical Formalization Theorem)**: For a comparison
operator satisfying the four Aristotelian constraints with scale invariance
and non-triviality, the route-independence combiner is necessarily of the
Recognition Composition Law form: `P(u,v) = 2u + 2v + c·uv` for some
constant c ∈ ℝ.

In other words: the unique functional form the laws of logic can take on
continuous comparisons of positive ratios, under the polynomial regularity
assumption, is the Recognition Composition Law.

This is an immediate corollary of `laws_of_logic_imply_dalembert_hypotheses`
combined with `bilinear_family_forced` (Inevitability.lean), which has been
peer-reviewed in:

  Washburn, Zlatanović, Allahyarov.
  "The d'Alembert Inevitability Theorem."
  Mathematics (MDPI), 2026.
-/
theorem RCL_is_unique_functional_form_of_logic
    (C : ComparisonOperator) (hLaws : SatisfiesLawsOfLogic C) :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      HasMultiplicativeConsistency (derivedCost C) P ∧
      (∀ u v, P u v = 2*u + 2*v + c*u*v) := by
  obtain ⟨hNorm, _hSym, ⟨P, hPoly, hSymP, hCons⟩, hCont, hNontriv⟩ :=
    laws_of_logic_imply_dalembert_hypotheses C hLaws
  obtain ⟨c, hP_form, _⟩ :=
    bilinear_family_forced (derivedCost C) P hNorm hCons hPoly hSymP hNontriv hCont
  exact ⟨P, c, hCons, hP_form⟩

/-! ## Cost Corollary: J is the Unique Continuous Cost Function of Logic

The companion uniqueness result for the cost function itself, citing
`law_of_logic_forces_jcost` from FunctionalEquation.lean. Under the four
Aristotelian constraints plus the canonical calibration, the unique
continuous cost on positive ratios is the canonical reciprocal cost
J(x) = ½(x + 1/x) − 1.
-/

open Cost Cost.FunctionalEquation in
/-- **Cost Corollary (J is forced by the laws of logic + calibration)**:
Under the four Aristotelian constraints, the canonical c = 2 normalization,
and the unit log-curvature calibration, the unique continuous cost function
on positive ratios is the canonical reciprocal cost J.

This invokes the peer-reviewed and Lean-verified result:

  Washburn, Zlatanović. "Uniqueness of the Canonical Reciprocal Cost."
  Mathematics 14 (2026), 935.
-/
theorem J_is_unique_cost_under_logic
    (C : ComparisonOperator) (hLaws : SatisfiesLawsOfLogic C)
    [AczelSmoothnessPackage]
    -- The route-independence combiner is the canonical c = 2 RCL.
    (hRCL : SatisfiesCompositionLaw (derivedCost C))
    -- The derived cost satisfies the unit log-curvature calibration.
    (hCalib : IsCalibrated (derivedCost C)) :
    ∀ x : ℝ, 0 < x → derivedCost C x = Cost.Jcost x := by
  obtain ⟨hNorm, hSym, _, hCont, _⟩ :=
    laws_of_logic_imply_dalembert_hypotheses C hLaws
  -- Express IsSymmetric in the form needed by law_of_logic_forces_jcost.
  have hRecip : IsReciprocalCost (derivedCost C) := by
    intro x hx
    exact hSym x hx
  exact law_of_logic_forces_jcost (derivedCost C) hRecip hNorm hRCL hCalib hCont

/-! ## Public Law-of-Logic theorem aliases

These theorem-facing names are the canonical public surface for Pith and
downstream citation pages. The older names above remain in place because they
describe the proof internals. -/

/-- **Law of Logic forces the Recognition Composition Law**:
the continuous positive-ratio Law of Logic forces the route-independence
combiner to have the RCL form `P(u,v) = 2u + 2v + c*u*v`. -/
theorem law_of_logic_forces_recognition_composition_law
    (C : ComparisonOperator) (hLogic : LawOfLogic C) :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      HasMultiplicativeConsistency (derivedCost C) P ∧
      (∀ u v, P u v = 2*u + 2*v + c*u*v) := by
  exact RCL_is_unique_functional_form_of_logic C hLogic

/-- **Law of Logic forces the canonical cost**:
under the canonical RCL normalization and unit log-curvature calibration, the
unique continuous positive-ratio cost satisfying the Law of Logic is
`J(x) = ½(x + x⁻¹) - 1`. -/
theorem law_of_logic_forces_canonical_cost
    (C : ComparisonOperator) (hLogic : LawOfLogic C)
    [Cost.FunctionalEquation.AczelSmoothnessPackage]
    (hRCL : Cost.FunctionalEquation.SatisfiesCompositionLaw (derivedCost C))
    (hCalib : Cost.FunctionalEquation.IsCalibrated (derivedCost C)) :
    ∀ x : ℝ, 0 < x → derivedCost C x = Cost.Jcost x := by
  exact J_is_unique_cost_under_logic C hLogic hRCL hCalib

/-! ## Summary

The chain established by this module:

  Four Aristotelian laws on a comparison operator
        ↓  (Translation Theorem, this module)
  Hypotheses of the d'Alembert Inevitability Theorem
        ↓  (bilinear_family_forced, Inevitability.lean)
  Recognition Composition Law: P(u,v) = 2u + 2v + c·uv
        ↓  (law_of_logic_forces_jcost, FunctionalEquation.lean)
  Canonical reciprocal cost: J(x) = ½(x + 1/x) − 1

The chain is machine-verified end to end. The Aristotelian framing is
the only new content of this module; the underlying uniqueness machinery
is the work of two already-published Mathematics (MDPI) papers.

Polynomiality of the route-independence combiner remains a regularity
assumption at this level. Level 2 (`Foundation/GeneralizedDAlembert.lean`)
will close that gap by formalizing the classical continuous-combiner
classification (Aczél 1966, Kannappan 2009, Stetkær 2013).
-/

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith
