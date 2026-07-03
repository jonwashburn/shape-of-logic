/-
  PrimitiveRecognitionCalculus/FRSCarrier.lean

  Phase 3 of the Delta-Native Analysis frontier: the F_RS carrier as an explicit
  finite-description syntax.

  `PRCMinimalField` proved that every named RS constant value lives in one
  countable subfield `rsField ⊊ ℝ`, generated abstractly by `Subfield.closure`.
  This module gives the carrier a concrete face: an inductive term language whose
  closed terms are exactly the finite expressions over the RS constant inventory
  and the rationals, with an evaluation into ℝ.

  The point is finite description. A term of `FRSExpr` is a literally finite tree.
  Its value is a real. We prove every value lands in the countable `rsField`, so
  the syntax never escapes the carrier; and we exhibit the constant inventory
  (φ, π, e, α⁻¹) and the rationals as terms.

  Honest boundary (inherited from `PRCMinimalField`). The arithmetic operations of
  the syntax are `+, −, ×, ⁻¹`. The genuinely transcendental constants (π, e, α⁻¹)
  enter as PRIMITIVE inventory symbols, not as finite arithmetic of simpler terms,
  because the transcendental functions that produce them are not finite arithmetic.
  The syntax captures finite generation over a fixed inventory; it does not claim
  to generate the transcendental functions themselves.

  What is proved:

  * `eval_mem`        : every term evaluates into `rsField` (soundness);
  * inventory lemmas  : φ, π, e, α⁻¹ and every rational are terms;
  * `value_countable` : the set of term values is countable (a proper subset of ℝ);
  * `has_protocol_display` : every term value is the value of a Delta-real protocol,
                        so the finite-description carrier has a protocol display in
                        the `ℝδ` interface;
  * `frs_carrier`     : the headline conjunction.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCMinimalField
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaReal

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace FRSCarrier

/-- The F_RS carrier expression syntax: a finite term over the rationals and the
RS constant inventory, closed under field operations. -/
inductive FRSExpr where
  | rat : ℚ → FRSExpr
  | phi : FRSExpr
  | pi : FRSExpr
  | e : FRSExpr
  | alphaInv : FRSExpr
  | neg : FRSExpr → FRSExpr
  | add : FRSExpr → FRSExpr → FRSExpr
  | mul : FRSExpr → FRSExpr → FRSExpr
  | inv : FRSExpr → FRSExpr
  deriving DecidableEq, Repr

/-- Evaluation of a carrier term into ℝ. -/
noncomputable def eval : FRSExpr → ℝ
  | .rat q => (q : ℝ)
  | .phi => Real.goldenRatio
  | .pi => Real.pi
  | .e => Real.exp 1
  | .alphaInv => MinimalField.alphaInv
  | .neg a => -(eval a)
  | .add a b => eval a + eval b
  | .mul a b => eval a * eval b
  | .inv a => (eval a)⁻¹

/-- **Soundness.** Every carrier term evaluates into the countable field `rsField`.
The finite-description syntax never escapes the carrier. -/
theorem eval_mem (ex : FRSExpr) : eval ex ∈ MinimalField.rsField := by
  induction ex with
  | rat q => exact SubfieldClass.ratCast_mem MinimalField.rsField q
  | phi => simpa [eval] using MinimalField.rsField_mem_phi
  | pi => simpa [eval] using MinimalField.rsField_mem_pi
  | e => simpa [eval] using MinimalField.rsField_mem_e
  | alphaInv => simpa [eval] using MinimalField.rsField_mem_alphaInv
  | neg a ih => simpa [eval] using neg_mem ih
  | add a b iha ihb => simpa [eval] using add_mem iha ihb
  | mul a b iha ihb => simpa [eval] using mul_mem iha ihb
  | inv a ih => simpa [eval] using inv_mem ih

/-! ### Constant inventory -/

theorem rat_is_term (q : ℚ) : eval (FRSExpr.rat q) = (q : ℝ) := rfl
theorem phi_is_term : eval FRSExpr.phi = Real.goldenRatio := rfl
theorem pi_is_term : eval FRSExpr.pi = Real.pi := rfl
theorem e_is_term : eval FRSExpr.e = Real.exp 1 := rfl
theorem alphaInv_is_term : eval FRSExpr.alphaInv = MinimalField.alphaInv := rfl

/-- The set of all values produced by the carrier syntax. -/
noncomputable def carrierValues : Set ℝ := Set.range eval

/-- The carrier value set sits inside `rsField`. -/
theorem carrierValues_subset : carrierValues ⊆ (MinimalField.rsField : Set ℝ) := by
  rintro x ⟨ex, rfl⟩
  exact eval_mem ex

/-- The carrier value set is countable: only countably many finite terms exist. -/
theorem carrierValues_countable : carrierValues.Countable :=
  (MinimalField.rsField_countable).mono carrierValues_subset

/-- The carrier values are a proper subset of ℝ. -/
theorem carrierValues_proper : carrierValues ≠ Set.univ := by
  intro h
  exact Cardinal.not_countable_real (h ▸ carrierValues_countable)

/-- **Protocol display.** Every carrier term value is the value of a Delta-real
protocol, so the finite-description carrier renders into the `ℝδ` interface. -/
theorem has_protocol_display (ex : FRSExpr) :
    ∃ x : DeltaReal.Protocol, x.value = eval ex :=
  DeltaReal.Protocol.value_surjective (eval ex)

/-- **Phase 3 headline.** The F_RS carrier is an explicit finite-description
syntax: every term evaluates into the countable field `rsField` (soundness), the
constant inventory (φ, π, e, α⁻¹) and the rationals are terms, the term values are
countable and a proper subset of ℝ, and every term value has a protocol display in
the `ℝδ` interface. The carrier the framework actually computes on is finite
generation over a fixed inventory, not the uncountable continuum. -/
theorem frs_carrier :
    (∀ ex : FRSExpr, eval ex ∈ MinimalField.rsField)
      ∧ eval FRSExpr.phi = Real.goldenRatio
      ∧ eval FRSExpr.pi = Real.pi
      ∧ eval FRSExpr.e = Real.exp 1
      ∧ eval FRSExpr.alphaInv = MinimalField.alphaInv
      ∧ carrierValues.Countable
      ∧ carrierValues ≠ Set.univ
      ∧ (∀ ex : FRSExpr, ∃ x : DeltaReal.Protocol, x.value = eval ex) :=
  ⟨eval_mem, phi_is_term, pi_is_term, e_is_term, alphaInv_is_term,
    carrierValues_countable, carrierValues_proper, has_protocol_display⟩

end FRSCarrier
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
