import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.DAlembert.Counterexamples
import IndisputableMonolith.Foundation.DAlembert.NecessityGates
import IndisputableMonolith.Foundation.DAlembert.EntanglementGate
import IndisputableMonolith.Foundation.DAlembert.CurvatureGate
import IndisputableMonolith.Foundation.DAlembert.FourthGate
import IndisputableMonolith.Foundation.DAlembert.Unconditional

/-!
# Triangulated Proof: Four Gates to Full Inevitability

This module combines the four gates into a unified inevitability theorem.

## The Four Gates

1. **Interaction Gate** (NecessityGates): F has interaction ⟺ F(xy) + F(x/y) ≠ 2F(x) + 2F(y) somewhere
2. **Entanglement Gate** (EntanglementGate): P is entangling ⟺ mixed second difference ≠ 0
3. **Curvature Gate** (CurvatureGate): G satisfies hyperbolic ODE ⟺ G'' = G + 1
4. **d'Alembert Gate** (FourthGate): H = G+1 satisfies d'Alembert ⟺ H(t+u) + H(t-u) = 2H(t)H(u)

## Why Four Gates?

In the Option~A formulation used in the paper, Gate~3 is a \emph{normalized} closure:
the hyperbolic branch is stated directly as $G''=G+1$. Once the flat branch is
excluded by interaction/entanglement (and the spherical branch by calibration),
the solution is already forced to be $G=\cosh-1$, and the RCL combiner follows.

In that formulation, the d'Alembert identity is therefore \emph{derived} (a signature
of $H=\cosh$) rather than an additional restriction. We keep it explicit because it
provides a compact classical viewpoint and a convenient certificate path in Lean.

## Main Results

- J has interaction (proved in NecessityGates)
- Interaction + symmetry ⟹ P is entangling (proved in EntanglementGate)
- RCL combiner is entangling (proved in EntanglementGate)
- J's log-lift satisfies hyperbolic ODE (proved in CurvatureGate)
- J has d'Alembert structure (proved in FourthGate)
- d'Alembert + calibration ⟹ G = cosh - 1 (proved in FourthGate)
- G = cosh - 1 ⟹ F = J (definition)
- F = J ⟹ P = RCL (proved unconditionally in Unconditional)

## The Quadrilateral Structure

```
                         F = J, P = RCL
                              ▲
              ┌───────────────┼───────────────┐
              │               │               │
         Interaction     Entangle        d'Alembert
           Gate            Gate            Gate
              │               │               │
              ▼               ▼               ▼
         F ≠ additive    P has cross    H(t+u)+H(t-u)
                           term          =2H(t)H(u)
                              │
                         Curvature
                           Gate
                              │
                              ▼
                         G'' = G+1
```

In the Option~A formulation, the curvature gate is the decisive closure; the
d'Alembert identity is a derived cross-check and alternate characterization.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DAlembert
namespace TriangulatedProof

open Real Cost NecessityGates EntanglementGate CurvatureGate Unconditional

/-! ## The Core Classification -/

/-- The fundamental trichotomy: under structural axioms, exactly one branch holds. -/
inductive CostBranch where
  | flat : CostBranch       -- Fquad: G = t²/2, P additive, no interaction
  | hyperbolic : CostBranch -- Jcost: G = cosh-1, P = RCL, has interaction
  deriving DecidableEq, Repr

/-! ## Gate 1: Interaction Distinguishes the Branches -/

/-- J is in the hyperbolic branch (has interaction). -/
theorem Jcost_is_hyperbolic : HasInteraction Cost.Jcost := Jcost_hasInteraction

/-- Fquad is in the flat branch (no interaction). -/
theorem Fquad_is_flat : ¬ HasInteraction Counterexamples.Fquad := Fquad_noInteraction

/-! ## Gate 2: Entanglement Characterizes the Combiner -/

/-- RCL combiner is entangling. -/
theorem RCL_is_entangling : IsEntangling Prcl := Prcl_entangling

/-- Additive combiner is not entangling. -/
theorem additive_not_entangling : ¬ IsEntangling Padd := Padd_not_entangling

/-- Interaction forces entanglement (under symmetry). -/
theorem interaction_forces_entanglement (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (hCons : ∀ x y : ℝ, 0 < x → 0 < y → F (x * y) + F (x / y) = P (F x) (F y))
    (hNorm : F 1 = 0)
    (hSymm : ∀ x : ℝ, 0 < x → F x = F x⁻¹)
    (hInt : HasInteraction F) :
    IsEntangling P :=
  interaction_implies_entangling F P hCons hNorm hSymm hInt

/-! ## Gate 3: Curvature Characterizes the ODE -/

/-- J's log-lift satisfies the hyperbolic ODE. -/
theorem Jcost_hyperbolic_ODE : SatisfiesHyperbolicODE Gcosh := Gcosh_satisfies_hyperbolic

/-- Fquad's log-lift satisfies the flat ODE. -/
theorem Fquad_flat_ODE : SatisfiesFlatODE Gquad := Gquad_satisfies_flat

/-- The two ODEs are mutually exclusive. -/
theorem flat_not_hyperbolic : ¬ SatisfiesHyperbolicODE Gquad := Gquad_not_hyperbolic

theorem hyperbolic_not_flat : ¬ SatisfiesFlatODE Gcosh := Gcosh_not_flat

/-! ## The Bridge: Connecting the Gates -/

/-- **Key Hypothesis**: Interaction + Structural Axioms forces the hyperbolic ODE.

    This is the central bridge connecting the gates. It says:
    If F has interaction, symmetry, normalization, smoothness, and consistency,
    then the log-lift G satisfies G'' = G + 1.

    This is NOT yet fully proved from first principles, but is strongly motivated by:
    1. The counterexample (no interaction) ⟹ flat ODE
    2. J (has interaction) ⟹ hyperbolic ODE
    3. Entanglement forces a specific functional form

    We state it as an explicit hypothesis to make the logical structure clear.
-/
def InteractionForcesHyperbolicODE : Prop :=
  ∀ (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ),
    F 1 = 0 →
    (∀ x : ℝ, 0 < x → F x = F x⁻¹) →
    ContDiff ℝ 2 F →
    deriv (deriv (fun t => F (Real.exp t))) 0 = 1 →
    (∀ x y : ℝ, 0 < x → 0 < y → F (x * y) + F (x / y) = P (F x) (F y)) →
    HasInteraction F →
    SatisfiesHyperbolicODE (fun t => F (Real.exp t))

/-! ## The Main Inevitability Theorem -/

/-- **Full Inevitability Theorem (Triangulated Form)**

    Under structural axioms + interaction, both F and P are uniquely forced.

    This theorem makes the bridge hypothesis explicit, showing exactly what
    remains to be proved for full unconditional inevitability.
-/
theorem full_inevitability_triangulated
    (bridge : InteractionForcesHyperbolicODE)
    (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (hNorm : F 1 = 0)
    (hSymm : ∀ x : ℝ, 0 < x → F x = F x⁻¹)
    (hSmooth : ContDiff ℝ 2 F)
    (hCalib : deriv (deriv (fun t => F (Real.exp t))) 0 = 1)
    (hCons : ∀ x y : ℝ, 0 < x → 0 < y → F (x * y) + F (x / y) = P (F x) (F y))
    (hInt : HasInteraction F) :
    -- Part 1: P is entangling (unconditional from interaction)
    IsEntangling P ∧
    -- Part 2: G satisfies hyperbolic ODE (from bridge)
    SatisfiesHyperbolicODE (fun t => F (Real.exp t)) := by
  constructor
  -- Part 1: Interaction ⟹ Entanglement
  · exact interaction_forces_entanglement F P hCons hNorm hSymm hInt
  -- Part 2: Bridge hypothesis gives hyperbolic ODE
  · exact bridge F P hNorm hSymm hSmooth hCalib hCons hInt

/-- If F = J, then P = RCL (unconditional, no bridge needed). -/
theorem P_forced_from_FJ (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (hCons : ∀ x y : ℝ, 0 < x → 0 < y → F (x * y) + F (x / y) = P (F x) (F y))
    (hFJ : ∀ x : ℝ, 0 < x → F x = Cost.Jcost x) :
    ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → P u v = 2 * u * v + 2 * u + 2 * v := by
  have hJcons : ∀ x y : ℝ, 0 < x → 0 < y →
      Cost.Jcost (x * y) + Cost.Jcost (x / y) = P (Cost.Jcost x) (Cost.Jcost y) := by
    intro x y hx hy
    have h := hCons x y hx hy
    rw [hFJ x hx, hFJ y hy, hFJ (x * y) (mul_pos hx hy), hFJ (x / y) (div_pos hx hy)] at h
    exact h
  exact rcl_unconditional P hJcons

/-! ## Summary: What Is Proved vs What Is Assumed -/

/-- **Summary Theorem**: All four gates point to the same conclusion.

    - Gate 1 (Interaction): Distinguishes J from Fquad
    - Gate 2 (Entanglement): Characterizes RCL vs additive combiner
    - Gate 3 (Curvature): Characterizes hyperbolic vs flat ODE
    - Gate 4 (d'Alembert): Forces λ = 1 in cosh(λt), completing the chain

    All four gates are consistent: J passes all four, Fquad fails all four.
-/
theorem gates_consistent :
    -- J has all four properties
    HasInteraction Cost.Jcost ∧
    IsEntangling Prcl ∧
    SatisfiesHyperbolicODE Gcosh ∧
    FourthGate.HasDAlembert Cost.Jcost ∧
    -- Fquad/Padd have the opposite properties
    ¬ HasInteraction Counterexamples.Fquad ∧
    ¬ IsEntangling Padd ∧
    SatisfiesFlatODE Gquad ∧
    ¬ FourthGate.HasDAlembert Counterexamples.Fquad := by
  exact ⟨Jcost_hasInteraction, Prcl_entangling, Gcosh_satisfies_hyperbolic,
         FourthGate.Jcost_has_dAlembert_structure,
         Fquad_noInteraction, Padd_not_entangling, Gquad_satisfies_flat,
         FourthGate.Fquad_not_dAlembert_structure⟩

/-! ## Complete Inevitability with Four Gates -/

/-- **Full Inevitability with Four Gates**: d'Alembert structure completes the proof.

    Unlike the three-gate version which required a bridge hypothesis,
    the four-gate version is fully proved:

    d'Alembert structure + structural axioms ⟹ F = J ⟹ P = RCL
-/
theorem full_inevitability_four_gates (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (hNorm : F 1 = 0)
    (hSymm : ∀ x : ℝ, 0 < x → F x = F x⁻¹)
    (hSmooth : ContDiff ℝ 2 F)
    (hCalib : deriv (deriv (fun t => F (Real.exp t))) 0 = 1)
    (hCons : ∀ x y : ℝ, 0 < x → 0 < y → F (x * y) + F (x / y) = P (F x) (F y))
    (hDA : FourthGate.HasDAlembert F) :
    -- Part 1: F = J
    (∀ x : ℝ, 0 < x → F x = Cost.Jcost x) ∧
    -- Part 2: P = RCL on [0,∞)²
    (∀ u v : ℝ, 0 ≤ u → 0 ≤ v → P u v = 2 * u * v + 2 * u + 2 * v) := by
  constructor
  · -- Part 1: F = J from d'Alembert structure
    exact FourthGate.dAlembert_forces_Jcost F hNorm hSymm hSmooth hCalib hDA
  · -- Part 2: P = RCL from F = J
    have hFJ := FourthGate.dAlembert_forces_Jcost F hNorm hSymm hSmooth hCalib hDA
    exact P_forced_from_FJ F P hCons hFJ

/-- The three gates are equivalent for distinguishing J from Fquad. -/
theorem gates_equivalent_for_Jcost :
    HasInteraction Cost.Jcost ↔
    (∃ P, (∀ x y, 0 < x → 0 < y →
      Cost.Jcost (x*y) + Cost.Jcost (x/y) = P (Cost.Jcost x) (Cost.Jcost y)) ∧
      IsEntangling P) := by
  constructor
  · intro _
    use Prcl
    refine ⟨?_, Prcl_entangling⟩
    intro x y hx hy
    -- This follows from the J_computes_P lemma
    have h := J_computes_P x y hx hy
    -- h : J(xy) + J(x/y) = 2 J(x) J(y) + 2 J(x) + 2 J(y)
    -- Prcl u v = 2uv + 2u + 2v
    unfold Prcl
    linarith
  · intro ⟨_, _, _⟩
    exact Jcost_hasInteraction

end TriangulatedProof
end DAlembert
end Foundation
end IndisputableMonolith
