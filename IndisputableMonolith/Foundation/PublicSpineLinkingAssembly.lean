/-
Conditional assembly of the Alexander linking bridge (campaign P-d3link).

This leaf file glues the Mayer-Vietoris reduction of
`LinkingVanishingHighDim` to the binder `PublicSpine`, exhibiting the exact
remaining distance to the unconditional bridge:

* `forces_D3_of_arcAcyclic`: granting the single frontier
  `ArcComplementsAcyclic D` (embedded arcs in `S^D` have `H₁`-acyclic
  complements — Hatcher 2B.1, arc case) for every `D ≥ 2`, `D ≠ 3`, the
  binder's uniqueness half `∀ D, DetectsNontrivialLinking D → D = 3` holds.
* `target_of_arcAcyclic`: under the same hypothesis, the campaign target
  `target_D3_from_nonencoding_linking` (a fully inhabited
  `AlexanderLinkingBridge`) holds, with no appeal to
  `DimensionForcing.linking_requires_D3` or any other axiom.

The hypothesis is a parameter, not an axiom and not a sorry.  When the arc
lemma is proved (compact-support bisection over the banked Mayer-Vietoris
layer), instantiating these theorems closes the bridge unconditionally.
-/
import IndisputableMonolith.Foundation.PublicSpine
import IndisputableMonolith.Foundation.LinkingVanishingHighDim

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpineLinkingAssembly

/-- The binder's uniqueness half, conditional on the arc-complement
frontier.  Dimensions `0`, `1` are unconditional (`LinkingVanishingLowDim`);
dimensions `2` and `≥ 4` are the Mayer-Vietoris reduction of
`LinkingVanishingHighDim`. -/
theorem forces_D3_of_arcAcyclic
    (harc : ∀ D, 2 ≤ D → D ≠ 3 →
      LinkingVanishingHighDim.ArcComplementsAcyclic D) :
    ∀ D, PublicSpine.DetectsNontrivialLinking D → D = 3 :=
  fun D hdet => LinkingVanishingHighDim.forces_D3_of_arcAcyclic harc D hdet

/-- The campaign target, conditional on the arc-complement frontier: a
fully inhabited `AlexanderLinkingBridge`, bypassing the
`DimensionForcing.linking_requires_D3` axiom on the public spine. -/
theorem target_of_arcAcyclic
    (harc : ∀ D, 2 ≤ D → D ≠ 3 →
      LinkingVanishingHighDim.ArcComplementsAcyclic D) :
    PublicSpine.target_D3_from_nonencoding_linking :=
  PublicSpine.bridge_of_forces_D3 (forces_D3_of_arcAcyclic harc)

end PublicSpineLinkingAssembly
end Foundation
end IndisputableMonolith
