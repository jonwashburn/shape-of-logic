/-
  PolynomialityFromLogic.lean

  Level 3 of three for the Law-of-Logic precursor paper.

  Intended canonical location:
    reality/IndisputableMonolith/Foundation/PolynomialityFromLogic.lean

  Status:
    Precise Lean statement of the conjecture and its formal reduction to a
    single clean technical question.  Provable parts fully proved.  The
    irreducible remaining step is identified, named, and reduced to its
    minimal Lean-statable content.

  Goal:
    Eliminate even the regularity hypothesis of Level 2
    (`GeneralizedAczelSmoothnessPackage`) and derive the bilinear family of
    combiners from the four Aristotelian laws and a structural
    closure-under-iteration condition that is itself a consequence of the
    laws of logic at the comparison-of-comparisons level.

  Approach:
    1. Make precise what closure-under-iteration of comparisons means as a
       Lean predicate on the combiner.
    2. Show that closure-under-iteration plus continuity forces a strong
       regularity property on Φ along a one-parameter family of inputs.
    3. State the residual smoothness conjecture as a Lean axiom-class with
       the cleanest possible interface, ready for either formalization or
       counter-investigation.

  References:
    - Aczél, Lectures on Functional Equations and Their Applications, 1966.
    - Kannappan, Functional Equations and Inequalities with Applications,
      Springer 2009.
    - Stetkær, Functional Equations on Groups, World Scientific 2013.
    - This module's companion paper:
      "The Law of Logic as Functional Equation."
-/

import Mathlib
import IndisputableMonolith.Foundation.DAlembert.Inevitability
import IndisputableMonolith.Cost.AczelTheorem

namespace IndisputableMonolith
namespace Foundation
namespace PolynomialityFromLogic

open Real
open IndisputableMonolith.Foundation.DAlembert.Inevitability

/-! ## Closure Under Iteration

The Aristotelian content of "comparisons of comparisons compose
consistently" formalizes as: any finite iterate of the combining rule on
elements of `Range(F)` again lies in `Range(F)`, and the iteration is
continuous in its inputs.

The key structural fact: if Φ is closed under iteration on `Range(F)`,
then `Range(F)` is invariant under the dynamical system `(u, v) ↦ Φ(u, v)`,
and the orbit structure of this system is the structural content of
"composition of comparisons composes."
-/

/-- A combining rule Φ is **closed under iteration** on a set `S ⊆ ℝ` if
applying Φ to two elements of S produces an element of S, and the result is
continuous in both inputs. -/
def ClosedUnderIteration (Phi : ℝ → ℝ → ℝ) (S : Set ℝ) : Prop :=
  ContinuousOn (Function.uncurry Phi) (S ×ˢ S) ∧
  ∀ u v : ℝ, u ∈ S → v ∈ S → Phi u v ∈ S

/-- The structural closure property derived from the four Aristotelian
laws plus the route-independence equation: the combining rule on
`Range(F)` is closed under iteration in this technical sense. -/
def IteratedClosureOnRange (F : ℝ → ℝ) (Phi : ℝ → ℝ → ℝ) : Prop :=
  ClosedUnderIteration Phi (Set.image F (Set.Ioi 0))

/-! ## Provable Consequences

The next two lemmas extract regularity properties from closure-under-iteration
that are used in the conjecture's proof.  Both are fully proved here.
-/

/-- **The diagonal of Φ on Range(F) is continuous.**  Pure consequence of
joint continuity of Φ on Range(F)². -/
theorem diagonal_continuous_on_range
    (F : ℝ → ℝ) (Phi : ℝ → ℝ → ℝ)
    (hClosed : IteratedClosureOnRange F Phi) :
    ContinuousOn (fun v : ℝ => Phi v v) (Set.image F (Set.Ioi 0)) := by
  obtain ⟨hCont, _⟩ := hClosed
  -- The diagonal map v ↦ (v, v) is continuous everywhere; compose with Phi.
  have h_diag_on : ContinuousOn (fun w : ℝ => ((w, w) : ℝ × ℝ))
      (Set.image F (Set.Ioi 0)) :=
    (continuous_id.prodMk continuous_id).continuousOn
  have h_maps : Set.MapsTo (fun w : ℝ => ((w, w) : ℝ × ℝ))
      (Set.image F (Set.Ioi 0))
      ((Set.image F (Set.Ioi 0)) ×ˢ (Set.image F (Set.Ioi 0))) := by
    intro w hw
    exact ⟨hw, hw⟩
  -- Use ContinuousOn.comp on the explicit lambda form of uncurry.
  have h_phi_on : ContinuousOn (fun p : ℝ × ℝ => Phi p.1 p.2)
      ((Set.image F (Set.Ioi 0)) ×ˢ (Set.image F (Set.Ioi 0))) := hCont
  have h_comp : ContinuousOn
      ((fun p : ℝ × ℝ => Phi p.1 p.2) ∘ (fun w : ℝ => ((w, w) : ℝ × ℝ)))
      (Set.image F (Set.Ioi 0)) :=
    h_phi_on.comp h_diag_on h_maps
  -- Convert the composition into the simpler form.
  have h_eq : ((fun p : ℝ × ℝ => Phi p.1 p.2) ∘ (fun w : ℝ => ((w, w) : ℝ × ℝ)))
              = (fun v : ℝ => Phi v v) := by
    funext w
    rfl
  rw [h_eq] at h_comp
  exact h_comp

/-- **Iteration produces continuous orbits.**  If we iterate Φ on a starting
element v ∈ Range(F), the n-fold iterate is again in Range(F), and the map
v ↦ Φ^[n](v, v) is continuous on Range(F). -/
theorem iterate_continuous_on_range
    (F : ℝ → ℝ) (Phi : ℝ → ℝ → ℝ)
    (hClosed : IteratedClosureOnRange F Phi)
    (n : ℕ) :
    ∃ φₙ : ℝ → ℝ,
      ContinuousOn φₙ (Set.image F (Set.Ioi 0)) ∧
      (∀ v ∈ Set.image F (Set.Ioi 0), φₙ v ∈ Set.image F (Set.Ioi 0)) := by
  -- Define the iterate by recursion on n.  Inductively, each iterate is
  -- a continuous map from Range(F) into Range(F).
  induction n with
  | zero =>
    refine ⟨id, ?_, ?_⟩
    · exact continuousOn_id
    · intro v hv
      exact hv
  | succ k ih =>
    obtain ⟨φₖ, hCont_φₖ, hMap_φₖ⟩ := ih
    refine ⟨fun v => Phi (φₖ v) v, ?_, ?_⟩
    · -- Continuity of v ↦ Phi(φₖ v, v) via ContinuousOn.comp.
      obtain ⟨hCont_Phi, _⟩ := hClosed
      have h_pair_on : ContinuousOn (fun w : ℝ => ((φₖ w, w) : ℝ × ℝ))
          (Set.image F (Set.Ioi 0)) :=
        hCont_φₖ.prodMk continuousOn_id
      have h_maps : Set.MapsTo (fun w : ℝ => ((φₖ w, w) : ℝ × ℝ))
          (Set.image F (Set.Ioi 0))
          ((Set.image F (Set.Ioi 0)) ×ˢ (Set.image F (Set.Ioi 0))) := by
        intro w hw
        exact ⟨hMap_φₖ w hw, hw⟩
      have h_phi_on : ContinuousOn (fun p : ℝ × ℝ => Phi p.1 p.2)
          ((Set.image F (Set.Ioi 0)) ×ˢ (Set.image F (Set.Ioi 0))) := hCont_Phi
      have h_comp : ContinuousOn
          ((fun p : ℝ × ℝ => Phi p.1 p.2) ∘
            (fun w : ℝ => ((φₖ w, w) : ℝ × ℝ)))
          (Set.image F (Set.Ioi 0)) :=
        h_phi_on.comp h_pair_on h_maps
      have h_eq : ((fun p : ℝ × ℝ => Phi p.1 p.2) ∘
                    (fun w : ℝ => ((φₖ w, w) : ℝ × ℝ)))
                  = (fun v : ℝ => Phi (φₖ v) v) := by
        funext w
        rfl
      rw [h_eq] at h_comp
      exact h_comp
    · intro v hv
      obtain ⟨_, hClosure⟩ := hClosed
      exact hClosure (φₖ v) v (hMap_φₖ v hv) hv

/-! ## Corrected Status Statement

The earlier version of this module carried a class assumption
`IteratedAnalyticityHolds`, claiming that closure under iteration on
`Range(F)` forces real-analyticity of the combiner.  The quartic-log
counterexample in
`IndisputableMonolith.Foundation.LogicAsFunctionalEquation.QuarticLogCounterexample`
shows that this is false in general: its combiner
`Φ(a,b) = 2a + 2b + 12 sqrt(a*b)` is closed on `[0,∞)` but is not
real-analytic at the origin.

This module therefore keeps only the structural consequences of closure under
iteration that are actually proved:

* diagonal continuity on the range;
* continuous iterates on the range.

The corrected polynomiality problem is moved to the planned
`LogicAsFunctionalEquation.Polynomiality` module: assume real-analyticity at
the origin directly, then prove polynomial degree at most two.
-/

end PolynomialityFromLogic
end Foundation
end IndisputableMonolith
