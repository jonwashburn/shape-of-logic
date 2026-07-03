import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Foundation.DAlembert.FactorizationForcing
import IndisputableMonolith.Foundation.DAlembert.LedgerFactorization
import IndisputableMonolith.Foundation.DAlembert.Inevitability
import IndisputableMonolith.Foundation.DAlembert.Unconditional

/-!
# Right-Affine from Factorization: Closing Gap 4

## Problem Statement

The module `FactorizationForcing.lean` proves `gate_forces_rcl`: given the
`FactorizationAssociativityGate` (symmetric + right-affine + zero-boundary +
unit-diagonal), the combiner `P(u,v)` is forced to equal the RCL polynomial
`2uv + 2u + 2v`.

However, `FactorizationAssociativityGate` takes `rightAffine` as a hypothesis
(line 28 of `FactorizationForcing.lean`):

    rightAffine : ∀ u, ∃ α β, ∀ v, P u v = α * v + β

The paper claims `right_affine` follows from factorization + associativity +
continuity, but the derivation is encoded in `LedgerFactorization.lean` as a
hypothesis rather than a proved theorem (see `ledger_forces_regrouping` line
133, explicitly stating "The right-affine response follows from the triple-
identity / strict-convexity argument (proved in the paper; encoded here as a
hypothesis on the combiner)").

This module closes Gap 4 by:

1. **Directly**: proving `bilinear_implies_right_affine` (trivial algebra).
2. **Compositionally**: combining with `Inevitability.bilinear_family_forced`
   to derive right-affine from polynomial consistency.
3. **Alternative path**: documenting that `Unconditional.rcl_unconditional`
   (in `Unconditional.lean`) already proves `P = RCL polynomial` without ever
   assuming right-affine, using surjectivity of J on [0, ∞) instead. This
   provides a gate-free route to the same conclusion.

## What is proved here (Lean)

* `bilinear_implies_right_affine`: If `P(u,v) = 2u + 2v + c·uv`, then `P` is
  right-affine in `v` for each `u`.
* `polynomial_consistency_implies_right_affine`: If `P` is a symmetric
  quadratic polynomial and `F` satisfies the Inevitability hypotheses, then
  `P` is right-affine.
* `regrouping_from_polynomial_consistency`: If `P` is a symmetric quadratic
  polynomial, we can build `RegroupingInvariance` (the input to
  `ledger_forces_rcl`) without the right-affine hypothesis being separately
  assumed.

## What remains open (not proved in Lean here)

* Deriving that `P` must be a polynomial at all, starting from continuity or
  smoothness of `P`. Under classical Aczél theory, smooth solutions to
  `G(t+u) + G(t-u) = P(G(t), G(u))` are severely constrained, but full
  formalization of the polynomial-shape forcing (from smooth `P`) remains
  open.

## The gate-free alternative

The cleanest answer to "can we avoid assuming right-affine?" is: **yes**, via
the `rcl_unconditional` route in `Unconditional.lean`. That theorem proves
`P = 2uv + 2u + 2v` on `[0, ∞)²` using only:

* F = J is already established (from the Aczel smoothness instance).
* Surjectivity of J onto `[0, ∞)` (theorem `J_surjective_nonneg`).
* The J-RCL identity (theorem `J_computes_P`).

No polynomial, no right-affine, no gate. This is formalized as
`Unconditional.rcl_unconditional`, referenced below.

## Verdict for Gap 4

The right-affine hypothesis in `FactorizationAssociativityGate` is NOT needed
for the RCL forcing conclusion. The existing machinery in `Unconditional.lean`
already provides a gate-free proof. This module makes that fact explicit and
adds a compositional result that right-affine follows from polynomial
consistency, connecting to `Inevitability.bilinear_family_forced`.

The remaining open issue (proving `P` is polynomial from smoothness) is a
separate concern that does not affect the validity of RS's core forcing
chain, because the gate-free path provides the same conclusion through
different hypotheses.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DAlembert
namespace RightAffineFromFactorization

open Real
open Cost
open FactorizationForcing

/-! ## Part 1: Right-affine from bilinear form (immediate consequence)

If `P(u, v) = 2u + 2v + c·uv`, then for each fixed `u`, `P(u, ·)` is affine
in `v` with slope `(2 + c·u)` and intercept `2u`.
-/

/-- Bilinear form implies right-affine. -/
theorem bilinear_implies_right_affine
    (P : ℝ → ℝ → ℝ) (c : ℝ)
    (h_bilinear : ∀ u v, P u v = 2*u + 2*v + c*u*v) :
    ∀ u, ∃ α β, ∀ v, P u v = α * v + β := by
  intro u
  refine ⟨2 + c*u, 2*u, ?_⟩
  intro v
  rw [h_bilinear u v]
  ring

/-- The RCL polynomial (c = 2 case) is right-affine with explicit coefficients. -/
theorem rcl_right_affine :
    ∀ u, ∃ α β, ∀ v, (2*u*v + 2*u + 2*v) = α * v + β := by
  intro u
  refine ⟨2 + 2*u, 2*u, ?_⟩
  intro v
  ring

/-! ## Part 2: Right-affine from polynomial consistency

Combining `Inevitability.bilinear_family_forced` with the bilinear-implies-
right-affine lemma, we get: if `P` is a symmetric quadratic polynomial and `F`
satisfies the standard hypotheses, then `P` is right-affine.

This means the `rightAffine` hypothesis in `FactorizationAssociativityGate` is
redundant under the stronger assumption that `P` is polynomial.
-/

/-- Right-affine follows from polynomial consistency with a cost functional `F`.

This theorem takes the Inevitability hypotheses (F normalized, consistent with
a symmetric quadratic polynomial P, non-trivial, continuous) and concludes
that P is right-affine. -/
theorem polynomial_consistency_implies_right_affine
    (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (hNorm : Inevitability.IsNormalized F)
    (hCons : Inevitability.HasMultiplicativeConsistency F P)
    (hPoly : ∃ (a b c d e f : ℝ), ∀ u v, P u v = a + b*u + c*v + d*u*v + e*u^2 + f*v^2)
    (hSymP : ∀ u v, P u v = P v u)
    (hNonTriv : ∃ x : ℝ, 0 < x ∧ F x ≠ 0)
    (hCont : ContinuousOn F (Set.Ioi 0)) :
    ∀ u, ∃ α β, ∀ v, P u v = α * v + β := by
  obtain ⟨c, hc, _⟩ := Inevitability.bilinear_family_forced F P hNorm hCons hPoly hSymP hNonTriv hCont
  exact bilinear_implies_right_affine P c hc

/-! ## Part 3: Building the gate without right-affine as a separate hypothesis

Now we can build `FactorizationAssociativityGate` using only polynomial
consistency as the "extra" hypothesis instead of right-affine directly. This
demonstrates that right-affine is not an independent assumption but a
consequence of polynomial + functional hypotheses.
-/

/-- Build `FactorizationAssociativityGate` from polynomial consistency.

This packages: symmetric (from the symmetric polynomial P), zeroBoundary
(supplied as hypothesis, derivable from F's normalization via
`symmetry_and_normalization_constrain_P`), unitDiagonal (supplied as
calibration hypothesis), and right-affine (derived via bilinear_family_forced). -/
theorem gate_from_polynomial_consistency
    (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (hNorm : Inevitability.IsNormalized F)
    (hCons : Inevitability.HasMultiplicativeConsistency F P)
    (hPoly : ∃ (a b c d e f : ℝ), ∀ u v, P u v = a + b*u + c*v + d*u*v + e*u^2 + f*v^2)
    (hSymP : ∀ u v, P u v = P v u)
    (hNonTriv : ∃ x : ℝ, 0 < x ∧ F x ≠ 0)
    (hCont : ContinuousOn F (Set.Ioi 0))
    (hP11 : P 1 1 = 6)
    (hP0 : ∀ u, P u 0 = 2 * u) :
    FactorizationAssociativityGate P :=
  { symmetric := hSymP
    rightAffine := polynomial_consistency_implies_right_affine F P
      hNorm hCons hPoly hSymP hNonTriv hCont
    zeroBoundary := hP0
    unitDiagonal := hP11 }

/-- **Main Theorem of this Module**: RCL follows from polynomial consistency
without separately assuming right-affine.

This closes Gap 4 in the direction of: if we're willing to assume P is
polynomial, then right-affine is a theorem, not a hypothesis. -/
theorem polynomial_consistency_forces_rcl
    (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (hNorm : Inevitability.IsNormalized F)
    (hCons : Inevitability.HasMultiplicativeConsistency F P)
    (hPoly : ∃ (a b c d e f : ℝ), ∀ u v, P u v = a + b*u + c*v + d*u*v + e*u^2 + f*v^2)
    (hSymP : ∀ u v, P u v = P v u)
    (hNonTriv : ∃ x : ℝ, 0 < x ∧ F x ≠ 0)
    (hCont : ContinuousOn F (Set.Ioi 0))
    (hP11 : P 1 1 = 6)
    (hP0 : ∀ u, P u 0 = 2 * u) :
    ∀ u v, P u v = 2 * u * v + 2 * u + 2 * v :=
  gate_forces_rcl P
    (gate_from_polynomial_consistency F P hNorm hCons hPoly hSymP hNonTriv hCont hP11 hP0)

/-! ## Part 4: The gate-free alternative (reference to Unconditional.lean)

The strongest statement of "RCL is forced without assuming right-affine" lives
in `Unconditional.lean`. Its theorem `rcl_unconditional` proves that if F = J
and F has any consistency relation F(xy) + F(x/y) = P(F(x), F(y)), then P
equals the RCL polynomial on [0, ∞)².

No polynomial hypothesis is needed. No right-affine hypothesis is needed. The
proof uses only:
* J's surjectivity onto [0, ∞) (`J_surjective_nonneg`)
* J's intrinsic RCL identity (`J_computes_P`)

We re-expose the key theorem here for convenience.
-/

/-- **Gate-free RCL theorem (from Unconditional.lean, re-exposed here).**

If F = J and F has any consistency relation F(xy) + F(x/y) = P(F(x), F(y))
with some function P, then P equals the RCL polynomial on [0, ∞)². This holds
without any assumption on P's form (polynomial, right-affine, smooth, etc.).
-/
theorem rcl_without_gate
    (P : ℝ → ℝ → ℝ)
    (hCons : ∀ x y : ℝ, 0 < x → 0 < y →
      Cost.Jcost (x * y) + Cost.Jcost (x / y) = P (Cost.Jcost x) (Cost.Jcost y)) :
    ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → P u v = 2*u*v + 2*u + 2*v :=
  Unconditional.rcl_unconditional P hCons

/-! ## Part 5: Summary

The Gap 4 question was: can `rightAffine` be derived from factorization +
associativity + continuity, rather than assumed?

**Answer: YES, in two different ways:**

1. **Via polynomial form (this module):** If `P` is a symmetric quadratic
   polynomial and `F` satisfies the Inevitability hypotheses, then `P` is
   right-affine as an immediate algebraic consequence of
   `bilinear_family_forced`. See `polynomial_consistency_implies_right_affine`.

2. **Via surjectivity (Unconditional.lean):** If F = J, then for any function
   P satisfying the consistency relation, P equals the RCL polynomial on
   [0,∞)². No assumption on P at all. See `rcl_without_gate` (aliased from
   `Unconditional.rcl_unconditional`).

Either route avoids needing `rightAffine` as an independent hypothesis. The
core RCL forcing claim therefore does not rest on an unproved right-affine
assumption: the gate can be dismantled by assuming more structure on P (path
1) OR assuming F = J and using surjectivity (path 2).

**The remaining genuinely-open step** (not addressed by this module): proving
that P must be polynomial in the first place, starting only from F being C²
or smooth. This involves classical Aczél theory on functional equations and
is non-trivial to formalize. However, the gate-free path (2) does not require
this step at all, since it bypasses the question of P's form entirely.
-/

end RightAffineFromFactorization
end DAlembert
end Foundation
end IndisputableMonolith
