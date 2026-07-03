import Mathlib
import IndisputableMonolith.Cost

/-!
# EML from Oriented Recognition Coordinates

This module formalizes the honest RS/EML bridge.

It does not claim that the reciprocal cost `J` alone derives the EML gate.
That would be false: `J x = J x⁻¹` forgets orientation.

The claim proved here is compiler-layer:

* before reciprocal quotienting, an oriented recognition ledger has an
  additive log coordinate;
* the multiplicative-ratio chart maps are `exp` and `log`;
* the oriented ledger combiner is subtraction;
* therefore the induced two-input compiler gate is
  `eml x y = exp x - log y`.

The same exp/log data, after reciprocal symmetrization, gives
`J(exp u) = cosh u - 1`.
-/

namespace IndisputableMonolith
namespace Information
namespace EMLFromRecognition

open Cost

noncomputable section

/-- Odrzywolek's EML operator, read as an oriented exp-log compiler gate. -/
def eml (x y : ℝ) : ℝ :=
  Real.exp x - Real.log y

/-- Oriented additive ledger coordinates lift to positive ratios by exponentiation. -/
def orientedToRatio (u : ℝ) : ℝ :=
  Real.exp u

/-- Positive ratios project back to additive ledger coordinates by logarithm. -/
def orientedFromRatio (x : ℝ) : ℝ :=
  Real.log x

/-- The oriented ledger combiner before reciprocal symmetrization. -/
def orientedSub (a b : ℝ) : ℝ :=
  a - b

/-- The compiler gate induced by the oriented exp/log chart and subtraction. -/
def orientedCompilerGate (x y : ℝ) : ℝ :=
  orientedSub (orientedToRatio x) (orientedFromRatio y)

/-- The induced oriented compiler gate is exactly EML. -/
theorem oriented_compiler_gate_eq_eml (x y : ℝ) :
    orientedCompilerGate x y = eml x y := by
  rfl

/-- The identity terminal kills the logarithmic channel. -/
theorem identity_terminal_kills_log : Real.log 1 = 0 := by
  simp

/-- EML recovers exponentiation by feeding the identity terminal to the
logarithmic channel. -/
theorem eml_recovers_exp (x : ℝ) :
    eml x 1 = Real.exp x := by
  simp [eml]

/-- EML recovers the constant `e` from the terminal `1`. -/
theorem eml_recovers_e :
    eml 1 1 = Real.exp 1 := by
  simp [eml]

/-- The cancellation loop that recovers logarithm from EML.  Over real Lean
this statement uses Lean's total `Real.log`; analytically it is the real
positive branch or the chosen complex branch in the paper. -/
theorem eml_recovers_log (x : ℝ) :
    eml 1 (eml (eml 1 x) 1) = Real.log x := by
  unfold eml
  simp only [Real.log_one, sub_zero]
  rw [Real.log_exp]
  ring

/-- Once `exp` and `log` have been recovered, EML recovers subtraction on
positive ratios. -/
theorem eml_recovers_sub (x y : ℝ) (hx : 0 < x) :
    eml (Real.log x) (Real.exp y) = x - y := by
  unfold eml
  rw [Real.exp_log hx, Real.log_exp]

/-- Reciprocal cost forgets the orientation of the log coordinate. -/
theorem reciprocal_cost_forgets_orientation (u : ℝ) :
    Jlog u = Jlog (-u) := by
  have h := Jcost_symm (Real.exp_pos u)
  simpa [Jlog, Real.exp_neg] using h

/-- EML keeps oriented channel data: the same terminal can be used to expose
the forward exp channel, while the log channel remains separately addressable. -/
theorem eml_keeps_oriented_channels (x : ℝ) :
    eml x 1 = orientedToRatio x ∧
    orientedFromRatio x = Real.log x := by
  constructor
  · simp [eml, orientedToRatio]
  · rfl

/-- A compact certificate for the theorem-grade RS/EML bridge. -/
structure EMLFromRecognitionCert where
  compiler_gate :
    ∀ x y : ℝ, orientedCompilerGate x y = eml x y
  exp_recovery :
    ∀ x : ℝ, eml x 1 = Real.exp x
  log_recovery :
    ∀ x : ℝ, eml 1 (eml (eml 1 x) 1) = Real.log x
  sub_recovery :
    ∀ x y : ℝ, 0 < x → eml (Real.log x) (Real.exp y) = x - y
  reciprocal_cost_quotient :
    ∀ u : ℝ, Jlog u = Jlog (-u)

/-- The EML compiler gate follows from oriented exp/log recognition data. -/
def emlFromRecognitionCert : EMLFromRecognitionCert where
  compiler_gate := oriented_compiler_gate_eq_eml
  exp_recovery := eml_recovers_exp
  log_recovery := eml_recovers_log
  sub_recovery := eml_recovers_sub
  reciprocal_cost_quotient := reciprocal_cost_forgets_orientation

theorem eml_from_recognition_cert_holds : Nonempty EMLFromRecognitionCert :=
  ⟨emlFromRecognitionCert⟩

end
end EMLFromRecognition
end Information
end IndisputableMonolith
