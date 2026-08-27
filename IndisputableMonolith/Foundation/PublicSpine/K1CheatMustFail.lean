import IndisputableMonolith.Foundation.PublicSpine

/-!
# K1 cheat witness — DO_NOT_BUILD / must-fail

Panel `public_spine_dual` (2026-07-08): the free-Prop OPEN target was inhabited
in three lines via the arithmetic encoding (K1). The first fix (abstract
`detects : ℕ → Prop` field + `not_encoding` name-firewall) was ALSO broken:
the empty detector `fun _ => False` inhabited it (probe built green,
2026-07-08), and by `funext`+`propext` any honest detector is *equal* to the
encoding predicate, so the firewall excluded exactly the real bridge. Lesson:
in Prop-land you cannot firewall by predicate identity; only content-typing
holds.

Current binder: `AlexanderLinkingBridge` over `DetectsNontrivialLinking`, a
fixed definition on genuine Mathlib singular homology of circle-complement
subspaces (`linkingComplementH1`). The cheats below must fail:

1. `encoding_plugin_must_fail`: `SphereAdmitsCircleLinking 3` unfolds to the
   arithmetic `(3:ℤ) - 2 = 1`; it cannot elaborate as a complement-homology
   nonvanishing. Type mismatch.
2. `empty_detector_must_fail`: the detector is no longer a choosable structure
   field, so the old cheat is not even expressible. Unknown-field error.

Keep this file OUT of any `lake_lib` / import graph. The gate
(`scripts/public_spine_gate.py`) checks it exists and names the cheats; it
does not build it. If this file ever builds green, the binder has been
weakened — treat as a gate failure.
-/

namespace IndisputableMonolith.Foundation.PublicSpine.K1Cheat
open IndisputableMonolith.Foundation.PublicSpine
open IndisputableMonolith.Foundation.AlexanderDuality

/-- DO_NOT_BUILD: encoding plug-in. Must fail with a type mismatch. -/
theorem encoding_plugin_must_fail : DetectsNontrivialLinking 3 :=
  D3_admits_circle_linking

/-- DO_NOT_BUILD: old empty-detector cheat. Must fail: no such field. -/
theorem empty_detector_must_fail : Nonempty AlexanderLinkingBridge :=
  ⟨{ h1 := CircleWindingChain.circleH1ZIsoInt_holds
     detects_nontrivial_linking := fun _ => False
     forces_D3 := fun _ h => h.elim }⟩

end IndisputableMonolith.Foundation.PublicSpine.K1Cheat
