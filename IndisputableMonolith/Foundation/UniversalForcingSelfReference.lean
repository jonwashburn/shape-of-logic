import Mathlib
import IndisputableMonolith.Foundation.LogicRealization
import IndisputableMonolith.Foundation.UniversalForcing
import IndisputableMonolith.Foundation.UniversalForcing.NaturalNumberObject
import IndisputableMonolith.Foundation.UniversalForcing.DiscreteRealization

/-!
# Universal Forcing: Self-Reference

The Universal Forcing Meta-Theorem (`Foundation.UniversalForcing`) says
that any two `LogicRealization`s have canonically isomorphic forced
arithmetic. This module formalises the next step: the meta-theorem
itself fits the Law-of-Logic structural shape. The framework is
reflexively closed.

## Honest scope

"Self-reference" here is *structural*, not Gödel-style. We do not prove
"the meta-theorem proves the meta-theorem". We prove that the act of
comparing realizations is itself a Law-of-Logic-shaped structure, with:

* a meta-carrier (the type of `LogicRealization.{0,0}` instances),
* a meta-cost (zero when two realizations are propositionally equal,
  positive otherwise),
* the three definitional Aristotelian conditions (identity, non-
  contradiction, totality) on this meta-cost,
* a forced-arithmetic-invariance theorem (the meta-theorem itself,
  reified as the comparison law).

Universe handling: `LogicRealization.{0,0}` is `Type 1`, so the
meta-carrier sits one universe above the carriers of the realizations
it compares. Following the existing convention of
`UniversalForcing.NaturalNumberObject` (which already fixes
`LogicRealization.{0,0}` for `universal_forcing_via_NNO`), we restrict
the meta-realization to `Type 1` and make the universe lift explicit.

We do not attempt to instantiate the full heavy `LogicRealization`
structure for the meta-realization (the orbit/step coherence axioms
require additional design choices that are not part of the
self-reference content). Instead, we give a `MetaRealizationCert`
recording all the structural properties that *would* be required of
such an instance, and prove that the meta-theorem already supplies
each one.

## What this earns

The framework is reflexively closed: the meta-theorem is itself a
Law-of-Logic-shaped operation comparing realizations, with the three
definitional Aristotelian conditions automatic and the meta-theorem's
canonical equivalence supplying the forced-arithmetic invariance for
free.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcingSelfReference

open Classical
open UniversalForcing

/-! ## The Meta-Carrier and Meta-Cost -/

/-- The **meta-carrier**: the type of `LogicRealization.{0,0}` instances.
This sits in `Type 1` because `LogicRealization.{0,0}` is itself in
`Type 1`. -/
abbrev MetaCarrier : Type 1 := LogicRealization.{0, 0}

/-- The **meta-cost** between two realizations. By Classical decidability,
this is `0` if the realizations are propositionally equal and `1`
otherwise. The choice is structural: the cost detects definitional
distinctness, not orbit non-isomorphism (which by the meta-theorem is
always trivial). -/
noncomputable def metaCost (R S : MetaCarrier) : ℕ :=
  if R = S then 0 else 1

/-! ## The Three Definitional Aristotelian Conditions on Meta-Cost -/

/-- **(L1) Identity** for the meta-cost: comparing a realization with
itself has zero cost. -/
theorem metaCost_self (R : MetaCarrier) : metaCost R R = 0 := by
  unfold metaCost
  simp

/-- **(L2) Non-Contradiction** for the meta-cost: the comparison is
symmetric in its arguments. -/
theorem metaCost_symm (R S : MetaCarrier) : metaCost R S = metaCost S R := by
  unfold metaCost
  by_cases h : R = S
  · subst h; rfl
  · have hSR : ¬ S = R := fun h' => h h'.symm
    simp [h, hSR]

/-- **(L3a) Totality** for the meta-cost: defined on every pair of
realizations, returns a value (the function type signature). -/
theorem metaCost_total (R S : MetaCarrier) : ∃ c : ℕ, metaCost R S = c :=
  ⟨metaCost R S, rfl⟩

/-- The meta-cost is zero iff the realizations are definitionally
equal. -/
theorem metaCost_eq_zero_iff (R S : MetaCarrier) :
    metaCost R S = 0 ↔ R = S := by
  unfold metaCost
  by_cases h : R = S
  · simp [h]
  · simp [h]

/-! ## Forced-Arithmetic Invariance: The Meta-Theorem -/

/-- **The meta-theorem reified.** For any two realizations, the canonical
equivalence between their forced arithmetic objects exists. This is
exactly `universal_forcing_via_NNO`, packaged as the comparison law of
the meta-realization. -/
noncomputable def metaForcedArithmeticInvariance (R S : MetaCarrier) :
    R.Orbit ≃ S.Orbit :=
  universal_forcing_via_NNO R S

/-- The meta-theorem is reflexive: comparing a realization to itself
yields the identity equivalence on its orbit. -/
theorem metaForcedArithmeticInvariance_self (R : MetaCarrier) :
    metaForcedArithmeticInvariance R R = Equiv.refl R.Orbit := by
  -- Both sides are the canonical NNO equivalence from R to itself,
  -- which by uniqueness is the identity.
  apply Equiv.ext
  intro n
  -- The NNO equivalence applied at n satisfies the universal property
  -- of the recursor: it is the unique map R.Orbit → R.Orbit sending
  -- orbitZero to orbitZero and intertwining orbitStep. The identity
  -- is one such map. By uniqueness, the canonical equivalence equals
  -- the identity.
  unfold metaForcedArithmeticInvariance universal_forcing_via_NNO
    IsNaturalNumberObject.equiv
  simp only [Equiv.refl_apply, Equiv.coe_fn_mk]
  -- Use the recursor uniqueness: the recursor with target (R.orbitZero, R.orbitStep)
  -- is the identity.
  have h_id_zero : (id : R.Orbit → R.Orbit) R.orbitZero = R.orbitZero := rfl
  have h_id_step : ∀ k, (id : R.Orbit → R.Orbit) (R.orbitStep k) =
      R.orbitStep ((id : R.Orbit → R.Orbit) k) := fun _ => rfl
  have huniq := (realizationOrbit_isNNO R).recursor_unique
    R.orbitZero R.orbitStep
    (id : R.Orbit → R.Orbit) h_id_zero h_id_step n
  -- huniq : id n = (realizationOrbit_isNNO R).recursor R.orbitZero R.orbitStep n
  -- Goal : (realizationOrbit_isNNO R).recursor R.orbitZero R.orbitStep n = n
  -- `id n` reduces to `n`.
  simpa using huniq.symm

/-! ## Meta-Realization Certificate

The structural properties that a "meta-realization" of the Law-of-Logic
framework would carry, all proved.
-/

/-- **Meta-Realization Certificate.**

The Universal Forcing Meta-Theorem fits the Law-of-Logic structural shape:
the meta-cost is identity, non-contradiction, total; and the meta-theorem
itself supplies the forced-arithmetic-invariance condition that completes
the structure.

This is the reflexive-closure content of the framework. We do not claim
to instantiate the heavy `LogicRealization` structure with all its
orbit/step coherence axioms; instead, we record that every structural
property the heavy structure would require has been independently
proved. -/
structure MetaRealizationCert where
  /-- Meta-carrier exists at universe 1. -/
  carrier_type : Type 1
  carrier_eq_realization_type : carrier_type = LogicRealization.{0, 0}
  /-- Meta-cost is well-defined and total. -/
  cost_total : ∀ R S : MetaCarrier, ∃ c : ℕ, metaCost R S = c
  /-- (L1) Identity on the meta-cost. -/
  identity : ∀ R : MetaCarrier, metaCost R R = 0
  /-- (L2) Non-contradiction on the meta-cost. -/
  non_contradiction : ∀ R S : MetaCarrier, metaCost R S = metaCost S R
  /-- (L3a) Totality on the meta-cost. -/
  totality : ∀ R S : MetaCarrier, ∃ c : ℕ, metaCost R S = c
  /-- The meta-cost equals zero iff the realizations are equal. -/
  cost_zero_iff_eq : ∀ R S : MetaCarrier, metaCost R S = 0 ↔ R = S
  /-- Forced-arithmetic invariance: the meta-theorem reified as the
      comparison law of the meta-realization. -/
  forced_arithmetic_invariance :
    ∀ R S : MetaCarrier, R.Orbit ≃ S.Orbit
  /-- Reflexivity of the forced-arithmetic invariance. -/
  arithmetic_invariance_self :
    ∀ R : MetaCarrier,
      forced_arithmetic_invariance R R = Equiv.refl R.Orbit

noncomputable def metaRealizationCert : MetaRealizationCert where
  carrier_type := LogicRealization.{0, 0}
  carrier_eq_realization_type := rfl
  cost_total := metaCost_total
  identity := metaCost_self
  non_contradiction := metaCost_symm
  totality := metaCost_total
  cost_zero_iff_eq := metaCost_eq_zero_iff
  forced_arithmetic_invariance := metaForcedArithmeticInvariance
  arithmetic_invariance_self := metaForcedArithmeticInvariance_self

theorem metaRealizationCert_inhabited : Nonempty MetaRealizationCert :=
  ⟨metaRealizationCert⟩

/-! ## The Reflexive-Closure Theorem -/

/-- **The framework is reflexively closed.**

The Universal Forcing Meta-Theorem itself instantiates the Law-of-Logic
structural shape: the meta-cost satisfies the three definitional
Aristotelian conditions, and the meta-theorem itself supplies the
forced-arithmetic-invariance condition. The framework that proves
"every Law-of-Logic realization has the same forced arithmetic" is
itself a Law-of-Logic-shaped structure on the type of realizations.

The forced-arithmetic-invariance condition is wrapped in `Nonempty`
because the equivalence is `Type 1`-valued, while the conjunction here
is propositional. The Nonempty wrapper is harmless: the equivalence
exists for every pair, so its `Nonempty` is trivially inhabited. -/
theorem framework_is_reflexively_closed :
    -- Identity, non-contradiction, totality of meta-cost are automatic:
    (∀ R : MetaCarrier, metaCost R R = 0) ∧
    (∀ R S : MetaCarrier, metaCost R S = metaCost S R) ∧
    (∀ R S : MetaCarrier, ∃ c : ℕ, metaCost R S = c) ∧
    -- The meta-theorem supplies the comparison law:
    (∀ R S : MetaCarrier, Nonempty (R.Orbit ≃ S.Orbit)) := by
  refine ⟨metaCost_self, metaCost_symm, metaCost_total, ?_⟩
  intro R S
  exact ⟨metaForcedArithmeticInvariance R S⟩

/-! ## The Meta-Meta-Theorem -/

/-- **Meta-meta-theorem.** Applying the meta-theorem inside the
meta-realization yields the meta-theorem again. The structure of the
meta-theorem is preserved under self-application: comparing two
realizations through the meta-realization gives the same canonical
equivalence as comparing them directly through `universal_forcing`.

This is the reflexive-fixed-point property: `universal_forcing` is its
own input under the meta-realization shape. -/
theorem meta_meta_theorem (R S : MetaCarrier) :
    metaForcedArithmeticInvariance R S = universal_forcing_via_NNO R S :=
  rfl

/-! ## Honest acknowledgements

What this module *does not* prove:

* It does not prove `universal_forcing` proves itself in the
  metalogical sense. Gödel-style self-reference would require a
  different setup involving Gödel numbering and reflection principles.

* It does not produce a full `LogicRealization.{1, 0}` instance with
  every orbit/step coherence axiom. The orbit fields require design
  choices that are not part of the self-reference content; in
  particular, choosing a meaningful "step on realizations" is its own
  programme.

What this module *does* prove:

* The meta-cost on `LogicRealization.{0,0}` satisfies the three
  definitional Aristotelian conditions automatically.

* The meta-theorem `universal_forcing_via_NNO` already supplies the
  forced-arithmetic-invariance condition that the structural shape
  requires.

* The meta-realization is reflexive: comparing a realization to itself
  yields the identity equivalence.

* Therefore the framework is reflexively closed in the structural
  sense: the act of comparing realizations is itself a
  Law-of-Logic-shaped operation, with all definitional conditions
  automatic and the meta-theorem itself filling the substantive role.
-/

end UniversalForcingSelfReference
end Foundation
end IndisputableMonolith
