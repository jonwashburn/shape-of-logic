import Mathlib

import IndisputableMonolith.Verification.RecognitionStabilityAudit.Core
import IndisputableMonolith.Verification.RecognitionStabilityAudit.Cayley

/-!
# Recognition Stability Audit (RSA): front-end (obstruction/sensor ⇒ boundary hit)

This file formalizes the RSA “front-end” step from the manuscript:

1. **Obstruction** `G` (holomorphic representative of a defect/claim).
2. **Sensor** `𝓙 := 1/G`.
3. **Cayley field** `Ξ := theta 𝓙 = (2𝓙-1)/(2𝓙+1)`.
4. **Pole ⇒ boundary hit**: if `𝓙` blows up at `z0`, then `Ξ → 1` along the punctured neighborhood.

We intentionally phrase “pole” as a *norm blow-up* condition. This is strong enough for RSA
and avoids dragging in meromorphic machinery at the interface layer (domain instantiations can
later strengthen it to “has a pole” in the analytic sense).
-/

namespace IndisputableMonolith
namespace Verification
namespace RecognitionStabilityAudit

open scoped Real Topology
open Filter Bornology

/-! ## Sensor blow-up and the Cayley boundary hit -/

/-- “Pole”/blow-up condition for a sensor `𝓙` at `z0`: the norm tends to `+∞` on a punctured
neighborhood. -/
def SensorBlowsUpAt (𝓙 : ℂ → ℂ) (z0 : ℂ) : Prop :=
  Tendsto (fun z => ‖𝓙 z‖) (𝓝[({z0} : Set ℂ)ᶜ] z0) atTop

/-- Core lemma: **sensor blow-up ⇒ Cayley field hits 1**.

This is the paper identity `Ξ(J) - 1 = -2/(2J+1)` plus the fact that `‖2J+1‖ → ∞` when `‖J‖ → ∞`. -/
theorem boundaryHit_theta_of_sensorBlowsUp {𝓙 : ℂ → ℂ} {z0 : ℂ}
    (hBlow : SensorBlowsUpAt 𝓙 z0) :
    BoundaryHitAt (fun z => theta (𝓙 z)) z0 := by
  -- Write `l` for the punctured neighborhood filter.
  set l : Filter ℂ := (𝓝[({z0} : Set ℂ)ᶜ] z0)

  have hNorm_atTop : Tendsto (fun z => ‖𝓙 z‖) l atTop := hBlow

  -- First, `‖2*𝓙 z + 1‖ → +∞` by a reverse-triangle lower bound.
  have hDen_atTop : Tendsto (fun z => ‖(2 * 𝓙 z + 1 : ℂ)‖) l atTop := by
    refine (tendsto_atTop.2 ?_)
    intro A
    -- Choose `B := (A+1)/2` and ask that `‖𝓙 z‖ ≥ B`.
    have hB : ∀ᶠ z in l, (A + 1) / 2 ≤ ‖𝓙 z‖ :=
      hNorm_atTop.eventually (eventually_ge_atTop ((A + 1) / 2))
    filter_upwards [hB] with z hz
    -- `‖2J+1‖ ≥ 2‖J‖ - 1`
    have htri : ‖(2 * 𝓙 z : ℂ)‖ ≤ ‖(2 * 𝓙 z + 1 : ℂ)‖ + ‖(1 : ℂ)‖ := by
      -- `2J = (2J+1) - 1`
      have hsub : ‖(2 * 𝓙 z + 1 : ℂ) - (1 : ℂ)‖ ≤ ‖(2 * 𝓙 z + 1 : ℂ)‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le (2 * 𝓙 z + 1) (1 : ℂ)
      -- rewrite `((2J+1)-1) = 2J` in `hsub`
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    have hrev : ‖(2 * 𝓙 z : ℂ)‖ - ‖(1 : ℂ)‖ ≤ ‖(2 * 𝓙 z + 1 : ℂ)‖ := by
      linarith [htri]
    have hLower : (2 : ℝ) * ‖𝓙 z‖ - 1 ≤ ‖(2 * 𝓙 z + 1 : ℂ)‖ := by
      -- `‖2J‖ = 2‖J‖`, `‖1‖ = 1`
      simpa [norm_mul, (by norm_num : ‖(2 : ℂ)‖ = (2 : ℝ))] using hrev
    -- From `hz : (A+1)/2 ≤ ‖J‖` we get `A ≤ 2‖J‖ - 1`.
    have hA : A ≤ (2 : ℝ) * ‖𝓙 z‖ - 1 := by
      nlinarith
    exact le_trans hA hLower

  -- Convert `‖den‖ → ∞` into `den → cobounded`, then invert to get `den⁻¹ → 0`.
  have hDen_cob : Tendsto (fun z => (2 * 𝓙 z + 1 : ℂ)) l (cobounded ℂ) :=
    (tendsto_norm_atTop_iff_cobounded).1 hDen_atTop
  have hInv : Tendsto (fun z => (2 * 𝓙 z + 1 : ℂ)⁻¹) l (𝓝 (0 : ℂ)) :=
    (Filter.tendsto_inv₀_cobounded (α := ℂ)).comp hDen_cob

  -- We will use the identity `theta(J) = 1 + (-2)/(2J+1)` (valid when `2J+1 ≠ 0`).
  have hDen_ne : ∀ᶠ z in l, (2 * 𝓙 z + 1 : ℂ) ≠ 0 := by
    have hpos : ∀ᶠ z in l, (0 : ℝ) < ‖(2 * 𝓙 z + 1 : ℂ)‖ :=
      hDen_atTop.eventually (eventually_gt_atTop (0 : ℝ))
    filter_upwards [hpos] with z hz
    exact (norm_pos_iff.1 hz)

  have hTheta_eq :
      (fun z => theta (𝓙 z)) =ᶠ[l] (fun z => (-2 : ℂ) * (2 * 𝓙 z + 1)⁻¹ + (1 : ℂ)) := by
    filter_upwards [hDen_ne] with z hz
    -- `field_simp` uses `hz` to justify clearing denominators.
    have hz' : (2 * 𝓙 z + 1 : ℂ) ≠ 0 := hz
    -- Expand `theta`, then compute.
    simp [theta_eq_div]
    field_simp [hz']
    ring

  -- The RHS tends to `1` since `(2J+1)⁻¹ → 0`.
  have hRhs :
      Tendsto (fun z => (-2 : ℂ) * (2 * 𝓙 z + 1)⁻¹ + (1 : ℂ)) l (𝓝 (1 : ℂ)) := by
    have hMul : Tendsto (fun z => (-2 : ℂ) * (2 * 𝓙 z + 1)⁻¹) l (𝓝 (0 : ℂ)) := by
      simpa using ((tendsto_const_nhds (x := (-2 : ℂ))).mul hInv)
    -- Add the constant `1`.
    -- Keep the normal form `(-2*inv)+1` to avoid commutativity issues.
    have : Tendsto (fun z => (-2 : ℂ) * (2 * 𝓙 z + 1)⁻¹ + (1 : ℂ)) l (𝓝 ((0 : ℂ) + (1 : ℂ))) :=
      hMul.add_const (1 : ℂ)
    simpa [add_comm, add_left_comm, add_assoc] using this

  -- Transfer along the eventual equality.
  exact hRhs.congr' hTheta_eq.symm

/-! ## From obstruction `G` to sensor blow-up `𝓙 = 1/G` -/

/-- Sensor associated to an obstruction `G`: `𝓙 = 1/G`. -/
noncomputable def sensorOfObstruction (G : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (G z)⁻¹

/-- If `G z → 0` in a punctured neighborhood and is eventually nonzero, then `‖1/G z‖ → ∞`.

This packages the generic filter lemma needed by RSA, and it is exactly what domain instantiations
prove when they show “candidate ⇒ obstruction has a (simple) zero”.
-/
theorem sensorBlowsUpAt_of_tendsto_zero
    {G : ℂ → ℂ} {z0 : ℂ}
    (h0 : Tendsto G (𝓝[({z0} : Set ℂ)ᶜ] z0) (𝓝 (0 : ℂ)))
    (hne : ∀ᶠ z in (𝓝[({z0} : Set ℂ)ᶜ] z0), G z ≠ 0) :
    SensorBlowsUpAt (sensorOfObstruction G) z0 := by
  -- First upgrade `G → 0` to `G → 0` within `≠ 0` (in the codomain).
  have h0' : Tendsto G (𝓝[({z0} : Set ℂ)ᶜ] z0) (𝓝[{(0 : ℂ)}ᶜ] (0 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (f := G) (a := (0 : ℂ)) (s := ({(0 : ℂ)}ᶜ : Set ℂ)) h0 (hne.mono (fun z hz => by
        simpa using hz))
  -- Now apply the Mathlib lemma: `‖x⁻¹‖ → ∞` as `x → 0` punctured.
  -- (`tendsto_norm_inv_nhdsNE_zero_atTop` is the codomain statement at `0`.)
  have hInv :
      Tendsto (fun w : ℂ => ‖w⁻¹‖) (𝓝[{(0 : ℂ)}ᶜ] (0 : ℂ)) atTop :=
    (tendsto_norm_inv_nhdsNE_zero_atTop (α := ℂ))
  -- Compose and simplify.
  simpa [SensorBlowsUpAt, sensorOfObstruction, Function.comp] using (hInv.comp h0')

/-! ## A reusable `FrontEnd` constructor for “obstruction ⇒ boundary hit” -/

/-- A front-end “compiler” instance built from an obstruction `G` and two analytic obligations:

- candidate ⇒ `G → 0` in the punctured neighborhood;
- candidate ⇒ `G ≠ 0` eventually on the punctured neighborhood.

Then the RSA Cayley field `Ξ = theta(1/G)` hits the boundary state `1`.
-/
def frontEnd_of_obstruction (Ω : Set ℂ) (Candidate : ℂ → Prop) (G : ℂ → ℂ)
    (h0 : ∀ {z0}, z0 ∈ Ω → Candidate z0 → Tendsto G (𝓝[({z0} : Set ℂ)ᶜ] z0) (𝓝 (0 : ℂ)))
    (hne : ∀ {z0}, z0 ∈ Ω → Candidate z0 → ∀ᶠ z in (𝓝[({z0} : Set ℂ)ᶜ] z0), G z ≠ 0) :
    FrontEnd
      { Ω := Ω
        Candidate := Candidate
        Xi := fun z => theta ((G z)⁻¹) } :=
by
  refine ⟨?_⟩
  intro z0 hz0 hC
  have hBlow : SensorBlowsUpAt (sensorOfObstruction G) z0 :=
    sensorBlowsUpAt_of_tendsto_zero (G := G) (z0 := z0) (h0 hz0 hC) (hne hz0 hC)
  -- Pole ⇒ boundary hit.
  simpa [sensorOfObstruction] using
    (boundaryHit_theta_of_sensorBlowsUp (𝓙 := sensorOfObstruction G) (z0 := z0) hBlow)

end RecognitionStabilityAudit
end Verification
end IndisputableMonolith
