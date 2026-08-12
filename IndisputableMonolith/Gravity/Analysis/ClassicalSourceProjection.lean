import IndisputableMonolith.Loom.Separation

/-!
# Classical source projection for order-sensitive gravity

Frozen world G0 of
`holography/plans/OrderSensitive_Gravity_Proposition_20260802.html`.

A classical source projection is a typed reading of a Loom `Config` that is
allowed to stand in for the "conventional source" half of the discovery
discriminator. Only readings already proved equal on the gauge-separated
certificate pair may inhabit the interface at THEOREM grade. Identifying any
such reading with continuum stress-energy remains MODEL.

## What is proved

* Depth-one and abelianised projections equalize `cfgA`/`cfgB` (and
  `cfgC`/`cfgD`).
* Depth-two separates both pairs, so the classical-equal / recognition-unequal
  shape is inhabited.
* Additive / occupation-style bag readings (depth one) are blind: decoy D2.

## Honesty

* THEOREM: the equalities and separations below, by reduction to
  `Loom.Certificate.depth_one_is_blind`, `abelianised_is_blind`,
  `depth_two_separates` and their cfgC/cfgD siblings.
* MODEL: any claim that these projections are physical `T_{μν}`.
* Not claimed: a continuum Einstein equation, a seating into Fin 16, or that
  the depth-two residue is gravitational.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ClassicalSourceProjection

open IndisputableMonolith.Loom
open IndisputableMonolith.Loom.Certificate

/-- A typed classical-source interface on Loom configurations.

`source` extracts the classical reading. `Equal` is the equality relation used
by the discovery gate (propositional equality on the carrier is the default).
`factorsThroughAbelian` records whether the reading ignores depth-two content.
Physical stress-energy identification is never a field of this structure. -/
structure SourceProjection (Source : Type) where
  source : Config → Source
  Equal : Source → Source → Prop
  factorsThroughAbelian : Bool
  nontrivial : ∃ c₁ c₂ : Config, ¬ Equal (source c₁) (source c₂)

/-- Depth-one (loop-by-loop / amplitude bag) projection. -/
def depthOneSource (c : Config) : List Nat :=
  (invariant base c).1

/-- Depth-two (commutator / pair-trace) reading. Not a classical source; the
recognition residual the campaign asks about. -/
def depthTwoReading (c : Config) : List Nat :=
  (invariant base c).2

/-- Abelianised bag-of-relations projection. -/
def abelianSource (c : Config) : List (List Int) :=
  abelBag c

/-- Depth-one projection as a classical source interface. -/
def DepthOneProjection : SourceProjection (List Nat) where
  source := depthOneSource
  Equal := (· = ·)
  factorsThroughAbelian := true
  nontrivial := by
    refine ⟨cfgA, [], ?_⟩
    decide

/-- Abelianised projection as a classical source interface. -/
def AbelianProjection : SourceProjection (List (List Int)) where
  source := abelianSource
  Equal := (· = ·)
  factorsThroughAbelian := true
  nontrivial := by
    refine ⟨cfgA, [], ?_⟩
    decide

/-! ## G0 on the discovery pair -/

/-- **G0, depth one.** Classical depth-one sources of `cfgA` and `cfgB` agree. -/
theorem depthOne_equal_cfgAB :
    DepthOneProjection.Equal (DepthOneProjection.source cfgA)
      (DepthOneProjection.source cfgB) :=
  depth_one_is_blind

/-- **G0, abelian.** Classical abelianised sources of `cfgA` and `cfgB` agree. -/
theorem abelian_equal_cfgAB :
    AbelianProjection.Equal (AbelianProjection.source cfgA)
      (AbelianProjection.source cfgB) :=
  abelianised_is_blind

/-- Recognition depth-two reading separates the discovery pair. -/
theorem depthTwo_separates_cfgAB :
    depthTwoReading cfgA ≠ depthTwoReading cfgB :=
  depth_two_separates

/-- Second discovery pair: depth-one equal. -/
theorem depthOne_equal_cfgCD :
    DepthOneProjection.Equal (DepthOneProjection.source cfgC)
      (DepthOneProjection.source cfgD) :=
  depth_one_is_blind2

/-- Second discovery pair: abelian equal. -/
theorem abelian_equal_cfgCD :
    AbelianProjection.Equal (AbelianProjection.source cfgC)
      (AbelianProjection.source cfgD) :=
  abelianised_is_blind2

/-- Second discovery pair: depth-two separates. -/
theorem depthTwo_separates_cfgCD :
    depthTwoReading cfgC ≠ depthTwoReading cfgD :=
  depth_two_separates2

/-- **Decoy D2.** Any reading that factors as the depth-one bag is blind on the
discovery pair. Instantiated at the depth-one projection itself. -/
theorem decoy_depthOne_blind_on_discovery :
    depthOneSource cfgA = depthOneSource cfgB :=
  depth_one_is_blind

/-- **Decoy D2 (abelian).** The unique abelianised bag reading is blind. -/
theorem decoy_abelian_blind_on_discovery :
    abelianSource cfgA = abelianSource cfgB :=
  abelianised_is_blind

/-- Composite certificate: classical equal and recognition unequal. -/
theorem classicalEqual_recognitionUnequal_cfgAB :
    depthOneSource cfgA = depthOneSource cfgB ∧
      abelianSource cfgA = abelianSource cfgB ∧
      depthTwoReading cfgA ≠ depthTwoReading cfgB :=
  ⟨depth_one_is_blind, abelianised_is_blind, depth_two_separates⟩

end ClassicalSourceProjection
end Analysis
end Gravity
end IndisputableMonolith
