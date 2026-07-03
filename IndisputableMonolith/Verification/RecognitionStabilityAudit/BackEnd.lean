import Mathlib

import IndisputableMonolith.Verification.RecognitionStabilityAudit.Core

/-!
# Recognition Stability Audit (RSA): back-end (Schur/Herglotz “pinch” ⇒ no boundary hits)

This file is the RSA “back-end” abstraction from the manuscript:

- we assume a **Schur bound** `‖Ξ z‖ ≤ 1` on an audited region `Ω`,
- plus **analyticity** (holomorphic / complex differentiable on `Ω`),
- plus **nontriviality** (Ξ is not identically constant),

and derive the “pinch” conclusion:

> `¬ BoundaryHitAt Ξ z0` for any `z0 ∈ Ω`.

Implementation note (RL-friendly): we build the proof from small, reusable lemmas:

1. `BoundaryHitAt Ξ z0` plus continuity at `z0` implies `Ξ z0 = 1`;
2. Schur bound + `Ξ z0 = 1` makes `‖Ξ‖` attain a maximum at `z0`;
3. Maximum modulus principle (strictly convex codomain) forces `Ξ` to be constant;
4. Nontriviality contradicts constancy.
-/

namespace IndisputableMonolith
namespace Verification
namespace RecognitionStabilityAudit

open scoped Real Topology
open Filter Set

/-! ## Helper: boundary-hit forces the value at the point -/

theorem boundaryHit_implies_value_eq_one
    {Ξ : ℂ → ℂ} {z0 : ℂ}
    (hCont : ContinuousAt Ξ z0)
    (hHit : BoundaryHitAt Ξ z0) :
    Ξ z0 = (1 : ℂ) := by
  -- Compare two limits along the same (punctured) filter:
  --   (i) continuity gives `Ξ → Ξ z0`,
  --  (ii) boundary hit gives `Ξ → 1`.
  let l : Filter ℂ := (𝓝[({z0} : Set ℂ)ᶜ] z0)
  have hCont' : Tendsto Ξ l (𝓝 (Ξ z0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds (s := ({z0} : Set ℂ)ᶜ) (hCont.tendsto)
  have hHit' : Tendsto Ξ l (𝓝 (1 : ℂ)) := hHit
  haveI : NeBot l := by
    -- `ℂ` has no isolated points, so punctured neighborhoods are nontrivial.
    simpa [l] using (show NeBot (𝓝[≠] z0) from inferInstance)
  exact tendsto_nhds_unique hCont' hHit'

/-! ## Pinch lemma: Schur bound + holomorphic + nontrivial ⇒ no boundary hits -/

/-- Back-end “pinch” lemma: if `Ξ` is holomorphic on a preconnected open region `Ω` and Schur-bounded
there, then any boundary hit forces `Ξ` to be constant `1` on `Ω`. -/
theorem eq_const_one_of_boundaryHit
    {Ω : Set ℂ} (hΩ_open : IsOpen Ω) (hΩ_conn : IsPreconnected Ω)
    {Ξ : ℂ → ℂ} (hHol : DifferentiableOn ℂ Ξ Ω)
    (hSchur : SchurOn Ω Ξ)
    {z0 : ℂ} (hz0 : z0 ∈ Ω) (hHit : BoundaryHitAt Ξ z0) :
    Set.EqOn Ξ (fun _ => (1 : ℂ)) Ω := by
  -- Step 1: continuity gives `Ξ z0 = 1`.
  have hContAt : ContinuousAt Ξ z0 :=
    (hHol.differentiableAt (hΩ_open.mem_nhds hz0)).continuousAt
  have hXi0 : Ξ z0 = (1 : ℂ) :=
    boundaryHit_implies_value_eq_one (Ξ := Ξ) (z0 := z0) hContAt hHit

  -- Step 2: `‖Ξ‖` attains a maximum at `z0` on `Ω`.
  have hMax : IsMaxOn (norm ∘ Ξ) Ω z0 := by
    intro z hz
    have hz_le : ‖Ξ z‖ ≤ 1 := hSchur z hz
    -- rewrite the RHS as `‖Ξ z0‖ = 1`
    simpa [Function.comp, hXi0] using hz_le

  -- Step 3: maximum modulus (strictly convex codomain) ⇒ Ξ is constant on Ω.
  have hConst : Set.EqOn Ξ (Function.const ℂ (Ξ z0)) Ω :=
    Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      (F := ℂ) (hc := hΩ_conn) (ho := hΩ_open) (hd := hHol) (hcU := hz0) (hm := hMax)

  -- Step 4: substitute `Ξ z0 = 1`.
  refine hConst.trans ?_
  intro z hz
  simp [Function.const, hXi0]

/-- Main back-end lemma: under Schur bound + holomorphic + nontriviality, `BoundaryHitAt` is impossible
at any `z0 ∈ Ω`. -/
theorem no_boundaryHit_of_schur_holomorphic_nontrivial
    {Ω : Set ℂ} (hΩ_open : IsOpen Ω) (hΩ_conn : IsPreconnected Ω)
    {Ξ : ℂ → ℂ} (hHol : DifferentiableOn ℂ Ξ Ω)
    (hSchur : SchurOn Ω Ξ)
    (hNontriv : ∃ z ∈ Ω, Ξ z ≠ (1 : ℂ)) :
    ∀ {z0 : ℂ}, z0 ∈ Ω → ¬ BoundaryHitAt Ξ z0 := by
  intro z0 hz0 hHit
  have hEq : Set.EqOn Ξ (fun _ => (1 : ℂ)) Ω :=
    eq_const_one_of_boundaryHit (Ω := Ω) hΩ_open hΩ_conn (Ξ := Ξ) hHol hSchur hz0 hHit
  rcases hNontriv with ⟨z1, hz1, hz1ne⟩
  exact hz1ne (hEq hz1)

/-! ## A `BackEnd` constructor (certificate builder) -/

/-- Build an RSA `BackEnd` from Schur bound + holomorphicity + nontriviality. -/
def backEnd_of_schur_holomorphic_nontrivial (P : Problem)
    (hΩ_open : IsOpen P.Ω) (hΩ_conn : IsPreconnected P.Ω)
    (hHol : DifferentiableOn ℂ P.Xi P.Ω)
    (hSchur : SchurOn P.Ω P.Xi)
    (hNontriv : ∃ z ∈ P.Ω, P.Xi z ≠ (1 : ℂ)) :
    BackEnd P :=
by
  refine ⟨hSchur, ?_⟩
  intro z0 hz0
  exact no_boundaryHit_of_schur_holomorphic_nontrivial
    (Ω := P.Ω) hΩ_open hΩ_conn (Ξ := P.Xi) hHol hSchur hNontriv hz0

end RecognitionStabilityAudit
end Verification
end IndisputableMonolith
