/-
  PrimitiveRecognitionCalculus/ChoicePrinciples.lean

  The NAMED choice principles: the second registry class of the Delta Forcing
  Spectrum audit, alongside the omniscience posits (`Omniscience.lean`).

  The omniscience principles (LPO, WLPO, LLPO, MP) are DECISION principles:
  they decide Sigma-0-1 data that no finite distinction certificate can decide.
  Countable choice is a different kind of commitment: a FUNCTION-EXISTENCE
  principle. From "every index has a witness" it manufactures a single
  simultaneous witness function. The delta base cannot force it (there is no
  finite certificate for an infinite simultaneous selection), but it is far
  weaker than full `Classical.choice`: it neither decides anything (no excluded
  middle) nor chooses over uncountable families.

  Why it gets its own registry class instead of joining the posits: the audit's
  CONDITIONAL verdict means "constructive modulo a named omniscience decision".
  The NAMED verdict means "constructive modulo a named choice principle". The
  constructive-real ladder (M0a: eta : Q_delta -> R_delta over Bishop-regular
  sequences) is expected to cost exactly AC_omega at the completeness rungs, and
  the ledger must be able to say that precisely, not launder it as BRIDGE
  (full classical) or overclaim it as FORCED.

  Everything here except `classical_acomega` is choice-free. `classical_acomega`
  is DELIBERATELY classical (it is the statement that the display layer
  satisfies AC_omega); it is bridge-tier by design and must not be "purified".

  No project-local axioms. No sorry.
-/

import Mathlib

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace ChoicePrinciples

/-- **ACω**, countable choice over `Type`-valued carriers. For every ℕ-indexed
family of inhabited-by-witness relations there is a simultaneous witness
function. This is the exact choice cost expected of the constructive-real
completeness rungs (Bishop/Bridges). As a `Prop` it is choice-free to STATE;
the point is that it is not provable from the δ base, while `Classical.choice`
proves it trivially (`classical_acomega`). Registered in the audit manifest's
`[registry].named` class: a clean-footprint theorem carrying `ACOmega` as a
hypothesis earns the NAMED verdict, strictly between CONDITIONAL and BRIDGE. -/
def ACOmega : Prop :=
  ∀ (X : Type) (R : ℕ → X → Prop), (∀ n, ∃ x, R n x) → ∃ f : ℕ → X, ∀ n, R n (f n)

/-- The classical display layer satisfies ACω: full choice specializes to
countable choice. DELIBERATELY classical (bridge tier); this theorem is the
calibration point "ACω < Classical.choice" and must not be purified. -/
theorem classical_acomega : ACOmega := fun _X _R h =>
  ⟨fun n => Classical.choose (h n), fun n => Classical.choose_spec (h n)⟩

/-- NAMED-class canary: ACω specializes, choice-free, to `Bool`-valued
relations. The proof is pure application, so the measured axiom footprint is
empty while the statement carries `ACOmega` as a hypothesis: the audit must
report exactly the NAMED verdict on this rung. If this rung ever measures
FORCED or BRIDGE, the tag-class plumbing is broken. -/
theorem acomega_bool (h : ACOmega) :
    ∀ R : ℕ → Bool → Prop, (∀ n, ∃ b, R n b) → ∃ f : ℕ → Bool, ∀ n, R n (f n) :=
  fun R hR => h Bool R hR

/-- ACω yields a modulus-of-witness function for rational approximation
families: the exact shape the CRealPre completeness rung consumes (from
"every precision level has a rational witness" to a single approximation
sequence). Choice-free given the hypothesis; pure application. -/
theorem acomega_rat_seq (h : ACOmega) (R : ℕ → ℚ → Prop) (hR : ∀ n, ∃ q, R n q) :
    ∃ f : ℕ → ℚ, ∀ n, R n (f n) :=
  h ℚ R hR

end ChoicePrinciples
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
