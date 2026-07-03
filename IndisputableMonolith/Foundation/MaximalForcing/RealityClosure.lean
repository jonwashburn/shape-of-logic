import IndisputableMonolith.Foundation.MaximalForcing.ForcedInvariant

/-!
# Maximal Forcing: Reality Closure Certificate

This is the crown-theorem interface for the Maximal Forcing Closure program.
The final theorem is not asserted here. Instead, this module states the exact
certificate whose construction will be the theorem:

```
forall C in ForcingClosure P U, ClaimClassification U C
```

Once a real classifier is built for the final claim universe, the crown theorem
is a projection from that certificate.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

universe u

/-- A maximal closure certificate for a primitive and claim universe. -/
structure MaximalClosureCert (P : Primitive) (U : ClaimUniverse.{u}) where
  classifies :
    forall C : RealityClaim U.Realization,
      InClosure P U C -> ClaimClassification U C

/-- Conditional crown theorem: once a classifier certificate exists, every claim
in the forcing closure is forced, independent, or selected. This is deliberately
conditional; the program is to build `MaximalClosureCert` for the real universe,
not to postulate it. -/
theorem maximal_forcing_closure
    {P : Primitive} {U : ClaimUniverse.{u}} (cert : MaximalClosureCert P U) :
    forall C : RealityClaim U.Realization,
      InClosure P U C -> ClaimClassification U C :=
  cert.classifies

/-- Crown theorem in the exact disjunction form: given a classifier certificate,
every claim in the forcing closure is `Forced`, `Independent`, or `Selected`.
This is the literal "as forced as possible" statement; it concedes no contingency
lazily, because `Independent` and `Selected` are themselves proof obligations
(an explicit countermodel witness and a named selection principle, respectively).
-/
theorem maximal_forcing_closure_trichotomy
    {P : Primitive} {U : ClaimUniverse.{u}} (cert : MaximalClosureCert P U)
    (C : RealityClaim U.Realization) (hC : InClosure P U C) :
    Forced U.admissibility.admissible C ∨
    Independent U.admissibility.admissible C ∨
    Selected U.admissibility.admissible C := by
  rcases cert.classifies C hC with h | hw | hs
  · exact Or.inl h
  · exact Or.inr (Or.inl (independent_of_witness hw))
  · exact Or.inr (Or.inr hs)

/-- Session protocol: closing a session on this program means either adding a
new forced invariant, adding an independence witness, tightening admissibility,
or updating the execution plan with the exact remaining blocker. -/
structure SessionUpdateProtocol where
  landed_forced_invariant : Prop
  landed_independence_witness : Prop
  tightened_admissibility : Prop
  updated_execution_plan : Prop
  nonempty_progress :
    landed_forced_invariant ∨
    landed_independence_witness ∨
    tightened_admissibility ∨
    updated_execution_plan

end MaximalForcing
end Foundation
end IndisputableMonolith
