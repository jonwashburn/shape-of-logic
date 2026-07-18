import IndisputableMonolith.Gravity.Analysis.ReggeTTBlochInterfaceAudit
import IndisputableMonolith.Gravity.Analysis.ReggeTTContinuumCertificateSpike

/-!
# Regge TT Bloch convention sidecar, attempt 2

This sidecar is intentionally not imported by production modules.  It imports
the committed spike transcription only here, as required by the panel
protocol.

Attempt 2 does not prove Gate B.  The interface moment is now a stencil fold,
not a definition wired to the spike blocks, so the equality to
`tetBlock0 + ... + tetBlock5` remains an honest convention bridge target.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTBlochConventionAudit

open ReggeTTBlochInterfaceAudit

noncomputable section

/-- Scalar packet passed to the committed spike transcription. -/
structure SpikeInput where
  E00 : ℝ
  E01 : ℝ
  E02 : ℝ
  E10 : ℝ
  E11 : ℝ
  E12 : ℝ
  E20 : ℝ
  E21 : ℝ
  E22 : ℝ
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ

/-- Matrix/vector marshalling into the scalar language of the spike file. -/
def spikeInput (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ) : SpikeInput where
  E00 := E 0 0
  E01 := E 0 1
  E02 := E 0 2
  E10 := E 1 0
  E11 := E 1 1
  E12 := E 1 2
  E20 := E 2 0
  E21 := E 2 1
  E22 := E 2 2
  x0 := x 0
  x1 := x 1
  x2 := x 2

/-- The literal committed spike LHS, with `s2 = sqrt 2`, `s3 = sqrt 3`, and
`p = pi` as required by attempt 2. -/
def committedSpikeLHS (input : SpikeInput) : ℝ :=
  ReggeTTContinuumCertificateSpike.tetBlock0
      input.E00 input.E01 input.E02 input.E10 input.E11 input.E12
      input.E20 input.E21 input.E22 input.x0 input.x1 input.x2
      (Real.sqrt 2) (Real.sqrt 3) Real.pi
    + ReggeTTContinuumCertificateSpike.tetBlock1
      input.E00 input.E01 input.E02 input.E10 input.E11 input.E12
      input.E20 input.E21 input.E22 input.x0 input.x1 input.x2
      (Real.sqrt 2) (Real.sqrt 3) Real.pi
    + ReggeTTContinuumCertificateSpike.tetBlock2
      input.E00 input.E01 input.E02 input.E10 input.E11 input.E12
      input.E20 input.E21 input.E22 input.x0 input.x1 input.x2
      (Real.sqrt 2) (Real.sqrt 3) Real.pi
    + ReggeTTContinuumCertificateSpike.tetBlock3
      input.E00 input.E01 input.E02 input.E10 input.E11 input.E12
      input.E20 input.E21 input.E22 input.x0 input.x1 input.x2
      (Real.sqrt 2) (Real.sqrt 3) Real.pi
    + ReggeTTContinuumCertificateSpike.tetBlock4
      input.E00 input.E01 input.E02 input.E10 input.E11 input.E12
      input.E20 input.E21 input.E22 input.x0 input.x1 input.x2
      (Real.sqrt 2) (Real.sqrt 3) Real.pi
    + ReggeTTContinuumCertificateSpike.tetBlock5
      input.E00 input.E01 input.E02 input.E10 input.E11 input.E12
      input.E20 input.E21 input.E22 input.x0 input.x1 input.x2
      (Real.sqrt 2) (Real.sqrt 3) Real.pi

/-- Gate B target proposition, left open as a definition rather than stated as
a theorem.  A future proof must instantiate `support`, `phaseQuadratic`, and
`amplitude` from the actual raw stencil and show that the moment fold matches
the committed spike LHS under the seven TT equations, without using
`tt_continuum_certificate`. -/
def GateBConventionTarget (support : Finset Bucket) (phaseQuadratic : Bucket → ℝ)
    (amplitude : Bucket → ℝ) (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ) : Prop :=
  E 0 1 = E 1 0 →
  E 0 2 = E 2 0 →
  E 1 2 = E 2 1 →
  E 0 0 + E 1 1 + E 2 2 = 0 →
  x 0 * E 0 0 + x 1 * E 1 0 + x 2 * E 2 0 = 0 →
  x 0 * E 0 1 + x 1 * E 1 1 + x 2 * E 2 1 = 0 →
  x 0 * E 0 2 + x 1 * E 1 2 + x 2 * E 2 2 = 0 →
  reggeTTMoment support phaseQuadratic amplitude =
    committedSpikeLHS (spikeInput E x)

end

end ReggeTTBlochConventionAudit
end Analysis
end Gravity
end IndisputableMonolith
