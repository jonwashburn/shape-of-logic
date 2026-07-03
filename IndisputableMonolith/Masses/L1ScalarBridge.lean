import Mathlib
import IndisputableMonolith.Masses.LeptonBoundaryLedger

/-!
# L1 Scalar Torsion Bridge (two-layer, panel-directed)

This module is the panel-directed refactor of the leading charged-lepton torsion
constant `1/(4π)` into the honest **two-layer** shape:

* **Layer A — arithmetic (THEOREM).** Given a trace-unital boundary density, the
  free scalar is removed and the density is forced to the unique value
  `n · leadingBoundaryQuantum = n/(4π)`. This is
  `LeptonBoundaryLedger.boundaryDensityTraceUnital_unique`, and the specific number
  `4π` enters only through the *proven* discrete Gauss-Bonnet total
  `Constants.AlphaDerivation.solid_angle_Q3_eq : solid_angle_Q3 = 4π`. No physics
  input, no character input; the same `4π` for all three generations
  (character-blind).

* **Layer B — physical premise (MODEL).** `LeadingCorrectionIsBoundaryFlux` states,
  as two *separate* physical claims about an abstract flux integral `I`, that the
  leading adjacent-generation correction is a boundary-supported recognition flux
  whose Q₃ integral equals the posted channel content. Only under this premise is
  the value forced.

## Why the premise stays MODEL (the two cheap tests, both negative)

The panel greenlit trying to lift Layer B to a theorem via two routes; both are
unavailable at the current lake-checked frontier, so the two model inputs are
genuinely irreducible here:

* **Test 1 — σ-balance from Noether: `flux = content` is NOT a Noether corollary.**
  `Foundation.SigmaNoetherCharge` conserves the *total* σ-charge (`net_skew`) on
  admissible states (`r_hat_conserves_sigma_charge`). It is a global-total
  conservation law with no support/locality clause tying the per-bond σ-current to
  the geometric `∂Q₃` vertex measure. So "posted content = boundary flux integral"
  (the field `flux_is_content`) is a physical postulate, not a corollary.

* **Test 2 — constancy from O_h: uniformity is NOT a lake-checked transitivity
  theorem.** `Masses.ChamberSolidAngleBridge` carries only the orbit–stabilizer
  *counting* identity (`vertex_stabilizer_order : 24/8 = 3`, by `decide`) and the
  equal-*deficit* fact (every vertex deficit is `π/2`). Equal deficits do not force
  equal *density*, and no `MulAction`/`IsPretransitive` of the octahedral group on
  the 8 vertices is constructed. So "the leading flux is uniform over the boundary"
  (the field `uniform_reduction`) is a second physical postulate, not a corollary.

Consequently the composite claim "the leading correction is `1/(4π)`" is
**CONDITIONAL**: it is forced *given* `LeadingCorrectionIsBoundaryFlux`, and that
premise is **MODEL** (two irreducible physical inputs). What is unconditional and
THEOREM-grade is the geometry (`4π`), the uniqueness/forcing, and the
character-blindness.

Lean status: no `sorry`; the forcing theorem is a genuine lake-checked implication
whose hypothesis is an explicit `Prop`, not a hidden assumption.
-/

namespace IndisputableMonolith
namespace Masses
namespace L1ScalarBridge

open Constants.AlphaDerivation
open LeptonTorsionKernel
open LeptonBoundaryLedger

noncomputable section

/-- **Layer B (MODEL).** The physical premise for the leading charged-lepton torsion
constant, decomposed into two separate claims about an abstract boundary flux
integral `I` of the leading correction density `lam`.

`I` is the true integral of the leading adjacent-generation correction over the
recognition boundary `∂Q₃`; it is deliberately a free real so that neither field
is definitionally the conclusion.

* `flux_is_content` — MODEL input A (σ-balance / discrete Stokes). The boundary
  flux integral equals the posted channel content `n`. Not derivable from the
  existing σ-Noether charge, which is global-total only (Test 1).
* `uniform_reduction` — MODEL input B (O_h uniformity). For a flux that is uniform
  over the boundary, the integral collapses to `solid_angle_Q3 · lam`. Not derivable
  from a lake-checked octahedral transitivity theorem (Test 2). -/
structure LeadingCorrectionIsBoundaryFlux (n : ℕ) (lam I : ℝ) : Prop where
  /-- MODEL A: the boundary recognition-flux integral equals the posted content `n`. -/
  flux_is_content : I = (n : ℝ)
  /-- MODEL B: a uniform boundary flux integrates to `(total boundary measure) · lam`. -/
  uniform_reduction : I = solid_angle_Q3 * lam

/-- **CONDITIONAL forcing theorem.** Given the MODEL premise, the leading correction
density is forced to `n/(4π)` and to no other value.

The two MODEL fields combine (by substitution) to trace-unitality
`solid_angle_Q3 · lam = n`; Layer A's uniqueness lemma then removes the free scalar,
and the specific `4π` enters through the proven Gauss-Bonnet total. -/
theorem leadingCorrection_forced {n : ℕ} {lam I : ℝ}
    (h : LeadingCorrectionIsBoundaryFlux n lam I) :
    lam = (n : ℝ) / (4 * Real.pi) := by
  have htrace : traceUnitalBoundaryDensity n lam := by
    unfold traceUnitalBoundaryDensity
    rw [← h.uniform_reduction, h.flux_is_content]
  rw [boundaryDensityTraceUnital_unique htrace, leadingBoundaryQuantum_eq]
  ring

/-- The forced value is `leadingBoundaryQuantum` scaled by the channel count, i.e.
`n` copies of the one-channel boundary quantum. Restates
`leadingCorrection_forced` in kernel terms. -/
theorem leadingCorrection_eq_quantum {n : ℕ} {lam I : ℝ}
    (h : LeadingCorrectionIsBoundaryFlux n lam I) :
    lam = (n : ℝ) * leadingBoundaryQuantum := by
  have htrace : traceUnitalBoundaryDensity n lam := by
    unfold traceUnitalBoundaryDensity
    rw [← h.uniform_reduction, h.flux_is_content]
  exact boundaryDensityTraceUnital_unique htrace

/-- **Character-blindness (THEOREM).** The forced one-channel quantum `n = 1` is
`1/(4π)` independent of any generation/character label: the premise carries no
character data, and the geometry `solid_angle_Q3 = 4π` is the same for all three
generations. This is the honest predictive content of Layer A. -/
theorem oneChannel_quantum_characterBlind {lam I : ℝ}
    (h : LeadingCorrectionIsBoundaryFlux 1 lam I) :
    lam = 1 / (4 * Real.pi) := by
  have := leadingCorrection_forced h
  simpa using this

/-! ## Honest status summary (as `Prop`, not as a claim of proof)

The bundle below names, in the type system, exactly what is proved and what is
assumed, so a reader cannot mistake the CONDITIONAL result for an unconditional one.
-/

/-- The proved, unconditional facts: (i) the geometric boundary total is `4π`;
(ii) trace-unitality forces the unique density; (iii) the forcing holds given the
MODEL premise. The MODEL premise itself is NOT part of this bundle. -/
structure L1ScalarBridgeStatus : Prop where
  /-- THEOREM: the recognition boundary total curvature is `4π` (Gauss-Bonnet). -/
  geometric_total : solid_angle_Q3 = 4 * Real.pi
  /-- THEOREM: trace-unitality removes the free scalar (Layer A uniqueness). -/
  layerA_unique :
    ∀ {n : ℕ} {lam : ℝ}, traceUnitalBoundaryDensity n lam →
      lam = (n : ℝ) * leadingBoundaryQuantum
  /-- THEOREM (conditional): the MODEL premise forces `n/(4π)`. -/
  conditional_forcing :
    ∀ {n : ℕ} {lam I : ℝ}, LeadingCorrectionIsBoundaryFlux n lam I →
      lam = (n : ℝ) / (4 * Real.pi)

/-- The status bundle is inhabited: every field is a genuine lake-checked theorem. -/
theorem l1ScalarBridge_status : L1ScalarBridgeStatus where
  geometric_total := solid_angle_Q3_eq
  layerA_unique := fun h => boundaryDensityTraceUnital_unique h
  conditional_forcing := fun h => leadingCorrection_forced h

end

end L1ScalarBridge
end Masses
end IndisputableMonolith
