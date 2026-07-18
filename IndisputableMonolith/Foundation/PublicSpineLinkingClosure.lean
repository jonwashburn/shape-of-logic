/-
UNCONDITIONAL closure of the Alexander linking bridge (campaign P-d3link).

`ArcComplementAcyclic.arcComplementsAcyclic` discharges the last remaining
hypothesis parameter of the campaign (embedded arcs in `S^D` have
`H₁`-acyclic complements, every `D`; Hatcher 2B.1, arc case, proved by
compact-support bisection over the banked Mayer-Vietoris layer).  This leaf
file instantiates the conditional assembly with it:

* `forces_D3`: the binder's uniqueness half,
  `∀ D, DetectsNontrivialLinking D → D = 3`, unconditionally.
* `target_D3`: the campaign target `target_D3_from_nonencoding_linking`
  (a fully inhabited `AlexanderLinkingBridge`), unconditionally, with no
  appeal to `DimensionForcing.linking_requires_D3` or any other axiom
  beyond the three standard Lean foundations.
-/
import IndisputableMonolith.Foundation.ArcComplementAcyclic
import IndisputableMonolith.Foundation.PublicSpineLinkingAssembly

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpineLinkingClosure

/-- **Unconditional**: nontrivial linking detection forces dimension `3`.
Dimensions `0`, `1` are `LinkingVanishingLowDim`; dimensions `2` and `≥ 4`
are the Mayer-Vietoris reduction of `LinkingVanishingHighDim` instantiated
with the arc-complement acyclicity theorem. -/
theorem forces_D3 :
    ∀ D, PublicSpine.DetectsNontrivialLinking D → D = 3 :=
  PublicSpineLinkingAssembly.forces_D3_of_arcAcyclic
    (fun D _ _ => ArcComplementAcyclic.arcComplementsAcyclic D)

/-- **Unconditional campaign target**: a fully inhabited
`AlexanderLinkingBridge`, bypassing the `DimensionForcing.linking_requires_D3`
axiom on the public spine. -/
theorem target_D3 : PublicSpine.target_D3_from_nonencoding_linking :=
  PublicSpineLinkingAssembly.target_of_arcAcyclic
    (fun D _ _ => ArcComplementAcyclic.arcComplementsAcyclic D)

end PublicSpineLinkingClosure
end Foundation
end IndisputableMonolith
