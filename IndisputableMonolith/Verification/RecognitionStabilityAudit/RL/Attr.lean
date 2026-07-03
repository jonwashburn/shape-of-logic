import Mathlib.Init

/-!
# RSA RL attributes (whitelists)

This file defines:

- `@[rsa_simp]`: whitelist for the `rsa_simp` tactic (allowed rewrite/unfold lemmas).
- `@[rsa_milestone]`: whitelist for the `rsa_step` tactic (allowed apply targets).

We keep this separate from the tactics/goal suites to avoid initialization-order issues:
modules can safely *use* these attributes after importing this file.
-/

public meta section

namespace IndisputableMonolith
namespace Verification
namespace RecognitionStabilityAudit

open Lean Meta

/-! ## Environment extensions -/

initialize rsaSimpLemmaExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun s n => s.push n
  }

initialize rsaMilestoneExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun s n => s.push n
  }

/-! ## Attributes -/

/-- Attribute: whitelist a lemma/definition for `rsa_simp` (RSA RL simplifier). -/
syntax (name := rsaSimpAttr) "rsa_simp" : attr

/-- Attribute: mark a lemma as an RSA RL milestone (allowed for `rsa_step`). -/
syntax (name := rsaMilestoneAttr) "rsa_milestone" : attr

@[inherit_doc rsaSimpAttr]
initialize registerBuiltinAttribute {
  name := `rsaSimpAttr
  descr := "Whitelist a lemma/definition for `rsa_simp` (RSA RL simplifier)."
  add := fun declName _stx _kind =>
    MetaM.run' do
      rsaSimpLemmaExt.add declName
}

@[inherit_doc rsaMilestoneAttr]
initialize registerBuiltinAttribute {
  name := `rsaMilestoneAttr
  descr := "Mark a lemma as an RSA RL milestone (allowed for `rsa_step`)."
  add := fun declName _stx _kind =>
    MetaM.run' do
      rsaMilestoneExt.add declName
}

end RecognitionStabilityAudit
end Verification
end IndisputableMonolith

end
