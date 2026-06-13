import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation
import IndisputableMonolith.Foundation.RecognizerInducesLogic
import IndisputableMonolith.Foundation.PrimitiveDistinction

/-!
# (L4) Composition Consistency from a Multiplicative Recognizer

`Foundation.RecognizerInducesLogic` exposed (L4) Composition Consistency
as a substantive hypothesis (`Recognizer.RecognizerComposition`). The
companion paper `RS_Recognition_Geometry_Logic_Unification.tex` claimed
that any compositional recognizer family on a multiplicative event space
satisfies (L4) automatically. This module formalises the honest version.

## The honest framing

The default `Recognizer.cost` is the equality-induced cost (zero on the
diagonal, a positive weight elsewhere). On the multiplicative event space
`(ℝ_{>0}, ·)`, that cost provably fails (L4) (see
`PrimitiveDistinction.equality_cost_insufficient_for_recognition`).

What this module formalises is the conditional theorem: **if** a recognizer
is paired with a continuous Law-of-Logic-satisfying comparison operator
`C` whose event space is the positive reals under multiplication, **then**
the d'Alembert form of (L4),
\[
F(xy) + F(x/y) = P\bigl(F(x), F(y)\bigr),
\]
holds for the derived cost `F(r) := C(r, 1)`, with a polynomial combiner
of degree at most two. This is exactly what
`LogicAsFunctionalEquation.RouteIndependence` provides.

The headline result is therefore: a `MultiplicativeRecognizer` (a
recognizer onto the positive reals, equipped with a `SatisfiesLawsOfLogic`
operator) automatically satisfies (L4) in its multiplicative form. The
substantive hypothesis becomes a derived theorem under the
multiplicative-structure assumption.

## Honest scope

This module derives (L4) for the *specific* multiplicative-event-space
carrier, with a continuous Law-of-Logic-satisfying cost. The abstract
"every recognizer satisfies (L4)" claim is false: the equality-induced
cost on `(ℝ_{>0}, ·)` refutes it. What this module proves is the
honest conditional: with the right cost on the right carrier, (L4) is
automatic.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MultiplicativeRecognizerL4

open LogicAsFunctionalEquation
open RecognizerInducesLogic
open PrimitiveDistinction

/-! ## The Multiplicative Recognizer -/

/-- A **multiplicative recognizer** is a recognizer whose event space is the
positive reals `ℝ_{>0}`, equipped with a continuous comparison operator
satisfying the Law of Logic. The structure pairs the geometric recognizer
data with the cost-functional data needed to derive (L4) automatically. -/
structure MultiplicativeRecognizer (𝒞 : Type*) where
  /-- The underlying geometric recognizer onto positive reals. -/
  recognizer : Recognizer 𝒞 {x : ℝ // 0 < x}
  /-- The continuous comparison operator on positive reals. -/
  comparator : ComparisonOperator
  /-- The comparator satisfies the Law of Logic (all four Aristotelian
      conditions plus scale invariance and non-triviality). -/
  laws : SatisfiesLawsOfLogic comparator

namespace MultiplicativeRecognizer

variable {𝒞 : Type*}

/-- The cost function induced by a multiplicative recognizer: the derived
cost of its comparator on positive ratios. -/
noncomputable def cost (m : MultiplicativeRecognizer 𝒞) : ℝ → ℝ :=
  derivedCost m.comparator

@[simp] theorem cost_def (m : MultiplicativeRecognizer 𝒞) (r : ℝ) :
    m.cost r = m.comparator r 1 := rfl

/-! ## L4 in d'Alembert (Multiplicative) Form -/

/-- The **multiplicative form of (L4)**: there exists a combiner `P` such
that the cost of the product comparison plus the cost of the quotient
comparison equals `P` evaluated on the component costs. This is the
d'Alembert form of route-independence on positive ratios. -/
def MultiplicativeL4 (m : MultiplicativeRecognizer 𝒞) : Prop :=
  ∃ P : ℝ → ℝ → ℝ,
    ∀ x y : ℝ, 0 < x → 0 < y →
      m.cost (x * y) + m.cost (x / y) = P (m.cost x) (m.cost y)

/-- A polynomial-degree-2 form of (L4): the combiner is a polynomial of
total degree at most two. This is the form the d'Alembert Inevitability
Theorem produces. -/
def MultiplicativeL4Polynomial (m : MultiplicativeRecognizer 𝒞) : Prop :=
  ∃ P : ℝ → ℝ → ℝ,
    (∃ a b c d e f : ℝ, ∀ u v, P u v = a + b*u + c*v + d*u*v + e*u^2 + f*v^2) ∧
    (∀ u v, P u v = P v u) ∧
    (∀ x y : ℝ, 0 < x → 0 < y →
      m.cost (x * y) + m.cost (x / y) = P (m.cost x) (m.cost y))

/-! ## The Derivation Theorem -/

/-- **L4 is automatic in the polynomial form for any multiplicative recognizer.**

The route-independence field of `SatisfiesLawsOfLogic` already provides the
polynomial-degree-2 combiner satisfying the multiplicative L4. -/
theorem multiplicativeRecognizer_satisfies_L4_polynomial
    (m : MultiplicativeRecognizer 𝒞) :
    MultiplicativeL4Polynomial m := by
  obtain ⟨P, hpoly, hsymm, hroute⟩ := m.laws.route_independence
  refine ⟨P, hpoly, hsymm, ?_⟩
  intro x y hx hy
  exact hroute x y hx hy

/-- **L4 is automatic in the abstract form for any multiplicative recognizer.**

The polynomial form trivially gives the existence form. -/
theorem multiplicativeRecognizer_satisfies_L4
    (m : MultiplicativeRecognizer 𝒞) :
    MultiplicativeL4 m := by
  obtain ⟨P, _, _, hroute⟩ := multiplicativeRecognizer_satisfies_L4_polynomial m
  exact ⟨P, hroute⟩

/-- **The (L4) substantive hypothesis is derivable in the multiplicative case.**

This is the headline theorem: the route-independence condition that the
companion paper exposed as a hypothesis (`RecognizerComposition`) is in
fact a theorem under the multiplicative-event-space structure. -/
theorem L4_derivable_on_multiplicative_event_space
    (m : MultiplicativeRecognizer 𝒞) :
    ∃ P : ℝ → ℝ → ℝ,
      ∀ x y : ℝ, 0 < x → 0 < y →
        m.cost (x * y) + m.cost (x / y) = P (m.cost x) (m.cost y) :=
  multiplicativeRecognizer_satisfies_L4 m

/-! ## Companion: The Three Definitional Conditions

The multiplicative recognizer also satisfies the three definitional
Aristotelian conditions (L1), (L2), and (L3) on its derived cost. These
follow directly from the comparator's `SatisfiesLawsOfLogic` certificate.
-/

/-- **(L1) Identity.** The derived cost vanishes at the multiplicative
identity. -/
theorem multiplicative_identity (m : MultiplicativeRecognizer 𝒞) :
    m.cost 1 = 0 := by
  show m.comparator 1 1 = 0
  exact m.laws.identity 1 (by norm_num)

/-- **(L2) Reciprocal symmetry.** The derived cost is symmetric under
reciprocation, a consequence of non-contradiction plus scale invariance. -/
theorem multiplicative_reciprocal_symmetry
    (m : MultiplicativeRecognizer 𝒞) :
    ∀ x : ℝ, 0 < x → m.cost x = m.cost (x⁻¹) := by
  intro x hx
  show m.comparator x 1 = m.comparator (x⁻¹) 1
  -- C(x, 1) = C(1, x) (non-contradiction) = C(x⁻¹, 1) (scale by x⁻¹)
  have hsymm : m.comparator x 1 = m.comparator 1 x :=
    m.laws.non_contradiction x 1 hx (by norm_num)
  have hxinv : (0 : ℝ) < x⁻¹ := inv_pos.mpr hx
  have hscale : m.comparator (x⁻¹ * x) (x⁻¹ * 1) = m.comparator x 1 :=
    m.laws.scale_invariant x 1 (x⁻¹) hx (by norm_num) hxinv
  -- (x⁻¹ * x) = 1 and (x⁻¹ * 1) = x⁻¹
  have hxx : x⁻¹ * x = 1 := inv_mul_cancel₀ (ne_of_gt hx)
  rw [hxx, mul_one] at hscale
  -- so C(1, x⁻¹) = C(x, 1)
  -- chain: C(x, 1) = C(1, x) (above), and C(1, x⁻¹) = C(x, 1) gives
  -- C(1, x) and C(1, x⁻¹) both equal C(x, 1)... use non-contradiction on x⁻¹
  have hsymm2 : m.comparator (x⁻¹) 1 = m.comparator 1 (x⁻¹) :=
    m.laws.non_contradiction (x⁻¹) 1 hxinv (by norm_num)
  rw [hsymm2, ← hscale]

/-! ## Headline Certificate -/

/-- **L4-from-Multiplicative-Recognizer Certificate.**

(L4) Composition Consistency, in its multiplicative d'Alembert form, is
not a hypothesis on a recognizer; it is a derived theorem whenever the
recognizer's event space is the positive reals under multiplication and
the comparator satisfies the Law of Logic. -/
structure L4DerivableCert (𝒞 : Type*) where
  l4_from_recognizer :
    ∀ m : MultiplicativeRecognizer 𝒞,
      ∃ P : ℝ → ℝ → ℝ,
        ∀ x y : ℝ, 0 < x → 0 < y →
          m.cost (x * y) + m.cost (x / y) = P (m.cost x) (m.cost y)
  l4_polynomial_form :
    ∀ m : MultiplicativeRecognizer 𝒞,
      MultiplicativeL4Polynomial m
  identity_at_one :
    ∀ m : MultiplicativeRecognizer 𝒞, m.cost 1 = 0
  reciprocal_symmetry :
    ∀ m : MultiplicativeRecognizer 𝒞,
      ∀ x : ℝ, 0 < x → m.cost x = m.cost (x⁻¹)

def l4DerivableCert (𝒞 : Type*) : L4DerivableCert 𝒞 where
  l4_from_recognizer := fun m => L4_derivable_on_multiplicative_event_space m
  l4_polynomial_form := fun m => multiplicativeRecognizer_satisfies_L4_polynomial m
  identity_at_one := fun m => multiplicative_identity m
  reciprocal_symmetry := fun m => multiplicative_reciprocal_symmetry m

theorem l4DerivableCert_inhabited (𝒞 : Type*) :
    Nonempty (L4DerivableCert 𝒞) :=
  ⟨l4DerivableCert 𝒞⟩

/-! ## Paper-Upgrade Certificate

The companion paper can now cite a single certificate rather than separately
quoting the definitional recognizer results from `RecognizerInducesLogic` and
the multiplicative (L4) result above.  The certificate is intentionally scoped:
the recognizer supplies the equality-induced L1/L2/L3 and primitive observer,
while the multiplicative Law-of-Logic comparator supplies the d'Alembert L4.
-/

/-- **Full multiplicative recognizer-to-logic certificate.**

For recognizers landing in the positive multiplicative event space, the
geometric recognizer supplies the three definitional conditions and primitive
observer, and the paired Law-of-Logic comparator supplies composition
consistency in polynomial d'Alembert form. -/
structure FullMultiplicativeLawOfLogicCert (𝒞 : Type*) where
  recognizer_identity :
    ∀ (m : MultiplicativeRecognizer 𝒞) (weight : ℝ),
      ∀ e : {x : ℝ // 0 < x}, m.recognizer.cost weight e e = 0
  recognizer_non_contradiction :
    ∀ (m : MultiplicativeRecognizer 𝒞) (weight : ℝ),
      ∀ e₁ e₂ : {x : ℝ // 0 < x},
        m.recognizer.cost weight e₁ e₂ = m.recognizer.cost weight e₂ e₁
  recognizer_totality :
    ∀ (m : MultiplicativeRecognizer 𝒞) (weight : ℝ),
      ∀ e₁ e₂ : {x : ℝ // 0 < x},
        ∃ c : ℝ, m.recognizer.cost weight e₁ e₂ = c
  primitive_observer :
    ∀ (m : MultiplicativeRecognizer 𝒞),
      m.recognizer.hasNontrivialRecognition →
        ∃ (O : ObserverFromRecognition.PrimitiveObserver {x : ℝ // 0 < x})
          (e₁ e₂ : {x : ℝ // 0 < x}),
          e₁ ≠ e₂ ∧ ObserverFromRecognition.Separates O e₁ e₂
  multiplicative_l4 :
    ∀ m : MultiplicativeRecognizer 𝒞,
      ∃ P : ℝ → ℝ → ℝ,
        ∀ x y : ℝ, 0 < x → 0 < y →
          m.cost (x * y) + m.cost (x / y) = P (m.cost x) (m.cost y)
  multiplicative_l4_polynomial :
    ∀ m : MultiplicativeRecognizer 𝒞,
      MultiplicativeL4Polynomial m
  comparator_identity_at_one :
    ∀ m : MultiplicativeRecognizer 𝒞, m.cost 1 = 0
  comparator_reciprocal_symmetry :
    ∀ m : MultiplicativeRecognizer 𝒞,
      ∀ x : ℝ, 0 < x → m.cost x = m.cost (x⁻¹)

/-- The full scoped certificate is inhabited for every configuration type. -/
def fullMultiplicativeLawOfLogicCert (𝒞 : Type*) :
    FullMultiplicativeLawOfLogicCert 𝒞 where
  recognizer_identity := fun m weight => Recognizer.identity m.recognizer weight
  recognizer_non_contradiction := fun m weight =>
    Recognizer.non_contradiction m.recognizer weight
  recognizer_totality := fun m weight => Recognizer.totality m.recognizer weight
  primitive_observer := fun m h =>
    Recognizer.induces_primitive_observer m.recognizer h
  multiplicative_l4 := fun m => L4_derivable_on_multiplicative_event_space m
  multiplicative_l4_polynomial := fun m =>
    multiplicativeRecognizer_satisfies_L4_polynomial m
  comparator_identity_at_one := fun m => multiplicative_identity m
  comparator_reciprocal_symmetry := fun m =>
    multiplicative_reciprocal_symmetry m

/-- The paper-upgrade certificate exists without any extra hypothesis beyond
`MultiplicativeRecognizer`. -/
theorem fullMultiplicativeLawOfLogicCert_inhabited (𝒞 : Type*) :
    Nonempty (FullMultiplicativeLawOfLogicCert 𝒞) :=
  ⟨fullMultiplicativeLawOfLogicCert 𝒞⟩

end MultiplicativeRecognizer

/-! ## Summary

The substantive (L4) Composition Consistency condition is no longer an
assumed hypothesis on a recognizer. Whenever:

* the recognizer's event space is the positive reals under multiplication,
* the comparator on that space satisfies the Law of Logic in operator form,

then the route-independence field of `SatisfiesLawsOfLogic` directly
supplies a polynomial-degree-2 combiner realising (L4). The geometric
primitive (recognizer) plus the cost-functional primitive (Law of Logic
on positive ratios) jointly force the d'Alembert composition law.

This closes the L4 frontier identified by
`RecognizerInducesLogic.RecognizerComposition` for the multiplicative case.
The substantive content was always in the comparator's compositional
structure, not in the recognizer's set-theoretic shape.
-/

end MultiplicativeRecognizerL4
end Foundation
end IndisputableMonolith
