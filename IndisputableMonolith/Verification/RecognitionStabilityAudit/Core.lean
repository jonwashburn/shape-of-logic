import Mathlib

import IndisputableMonolith.Cost
import IndisputableMonolith.Verification.RecognitionStabilityAudit.Cayley

/-!
# Recognition Stability Audit (RSA): core interface (RL-friendly)

This module is the Lean “home” for the **Recognition Stability Audit** described in
`papers/tex/Recognition_Stability_Audit.tex`.

## What this file is (and why it’s structured this way)

RSA is best read as a **compiler**:

- **Front-end**: compile a candidate existence claim into a *boundary hit* condition for a
  bounded Cayley field `Ξ` (morally: candidate ⇒ sensor pole ⇒ `Ξ → 1`).
- **Back-end**: produce a **finite certificate** that `Ξ` stays inside the Schur class on the
  audited region (and therefore cannot hit the forbidden boundary state).
- **Correctness theorem**: if both sides succeed, the candidate is impossible in the audited
  region.

This file is intentionally **RL-friendly**:

- We represent each RSA step as a small `structure` (a checklist of proof obligations).
- The top-level theorem only uses those obligations, so an LLM can “train” by learning to
  fill in the structures (front-end encodings + back-end certificates).

## Relation to the canonical RS cost `J`

RSA uses the canonical reciprocal cost `J(x) = ½(x + x⁻¹) − 1` on `ℝ_{>0}` as its
foundational cost primitive. In this repository that function is already formalized as
`IndisputableMonolith.Cost.Jcost`.

This file doesn’t re-prove cost uniqueness; it only *references* the cost layer and focuses
on the audit pipeline interface.
-/

namespace IndisputableMonolith
namespace Verification
namespace RecognitionStabilityAudit

open scoped Real Topology
open Filter

/-! ## Small reusable predicates -/

/-- Schur bound (disk bound) on a region `Ω`: `‖f z‖ ≤ 1` for all `z ∈ Ω`. -/
def SchurOn (Ω : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ Ω, ‖f z‖ ≤ 1

/-- Boundary hit at a point: along the punctured neighborhood of `z0`, the field tends to `1`.

This is the *compiled* forbidden-event predicate in RSA:
candidate ⇒ boundary hit (usually via `sensor pole ⇒ Ξ → 1`). -/
def BoundaryHitAt (Ξ : ℂ → ℂ) (z0 : ℂ) : Prop :=
  Tendsto Ξ (𝓝[({z0} : Set ℂ)ᶜ] z0) (𝓝 (1 : ℂ))

/-! ## The RSA problem interface -/

/-- An RSA “problem instance”: a region `Ω` to audit, a candidate predicate, and the Cayley
field `Ξ` that the audit will certify as Schur-bounded. -/
structure Problem where
  /-- Audited region (typically a chart domain after normalization to `𝔻`). -/
  Ω : Set ℂ
  /-- Candidate predicate (“the monster”): the existence claim we try to rule out on `Ω`. -/
  Candidate : ℂ → Prop
  /-- Audited Cayley field. In the paper this is `Ξ = (2𝓙-1)/(2𝓙+1)` after pullback. -/
  Xi : ℂ → ℂ

namespace Problem

/-- Convenience: the paper-facing Cayley field `Ξ` arising from a “sensor” `𝓙`. -/
noncomputable def XiFromSensor (𝓙 : ℂ → ℂ) : ℂ → ℂ :=
  fun z => theta (𝓙 z)

end Problem

/-! ## RSA front-end: candidate ⇒ boundary hit -/

/-- Front-end obligations: compile the candidate into a boundary-hit statement for `Ξ`. -/
structure FrontEnd (P : Problem) : Prop where
  /-- If the candidate holds at `z0 ∈ Ω`, then the Cayley field hits the forbidden boundary:
  `Ξ → 1` along the punctured neighborhood. -/
  candidate_implies_boundaryHit :
      ∀ {z0 : ℂ}, z0 ∈ P.Ω → P.Candidate z0 → BoundaryHitAt P.Xi z0

/-! ## RSA back-end: finite certificate ⇒ no boundary hits -/

/-- Back-end obligations: a (finite) certificate that prevents boundary hits.

In the paper, this is realized via Schur / Herglotz theory (bounded-real / Pick-gap-plus-tail)
plus the “pinch” argument. Here we keep the interface explicit: the certificate must supply
both the global Schur bound and the derived “no boundary hit” conclusion.
-/
structure BackEnd (P : Problem) : Prop where
  /-- Global Schur bound for `Ξ` on `Ω`. -/
  schur_bound : SchurOn P.Ω P.Xi
  /-- The “pinch” outcome: `Ξ` cannot hit the forbidden boundary at any interior point of `Ω`.
  (Domain instantiations discharge this from `schur_bound` + analyticity + nontriviality.) -/
  no_boundary_hit : ∀ {z0 : ℂ}, z0 ∈ P.Ω → ¬ BoundaryHitAt P.Xi z0

/-! ## RSA correctness theorem (the training target) -/

/-- **RSA correctness (audit soundness)**:

If the front-end compiles the candidate into a boundary hit, and the back-end certificate
rules out boundary hits on the audited region, then the candidate cannot occur in the region.
-/
theorem correctness (P : Problem) (FE : FrontEnd P) (BE : BackEnd P) :
    ∀ {z0 : ℂ}, z0 ∈ P.Ω → ¬ P.Candidate z0 := by
  intro z0 hz0 hCand
  have hHit : BoundaryHitAt P.Xi z0 :=
    FE.candidate_implies_boundaryHit hz0 hCand
  exact (BE.no_boundary_hit (z0 := z0) hz0) hHit

end RecognitionStabilityAudit
end Verification
end IndisputableMonolith
