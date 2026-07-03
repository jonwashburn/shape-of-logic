import Lean

open Lean

structure VirtueExport where
  name : String
  transformConst : String
  conservesProof : String
  cadenceProof : String
  gaugeProof : String
  deriving Repr, ToJson

structure SoulInvariantExport where
  name : String
  description : String
  proof : String
  deriving Repr, ToJson

def virtueExports : List VirtueExport :=
  [ { name := "Love"
      transformConst := "IndisputableMonolith.Ethics.Virtues.loveVirtue"
      conservesProof := "loveVirtue.conserves_reciprocity"
      cadenceProof := "loveVirtue.respects_cadence"
      gaugeProof := "loveVirtue.gauge_invariant" }
  , { name := "Justice"
      transformConst := "IndisputableMonolith.Ethics.Virtues.canonicalJusticeVirtue"
      conservesProof := "justiceVirtue.conserves_reciprocity"
      cadenceProof := "justiceVirtue.respects_cadence"
      gaugeProof := "justiceVirtue.gauge_invariant" }
  , { name := "Temperance"
      transformConst := "IndisputableMonolith.Ethics.Virtues.temperanceVirtue"
      conservesProof := "temperanceVirtue.conserves_reciprocity"
      cadenceProof := "temperanceVirtue.respects_cadence"
      gaugeProof := "temperanceVirtue.gauge_invariant" }
  , { name := "Patience"
      transformConst := "IndisputableMonolith.Ethics.Virtues.patienceVirtue"
      conservesProof := "patienceVirtue.conserves_reciprocity"
      cadenceProof := "patienceVirtue.respects_cadence"
      gaugeProof := "patienceVirtue.gauge_invariant" }
  , { name := "Gratitude"
      transformConst := "IndisputableMonolith.Ethics.Virtues.gratitudeVirtue"
      conservesProof := "gratitudeVirtue.conserves_reciprocity"
      cadenceProof := "gratitudeVirtue.respects_cadence"
      gaugeProof := "gratitudeVirtue.gauge_invariant" }
  , { name := "Humility"
      transformConst := "IndisputableMonolith.Ethics.Virtues.humilityVirtue"
      conservesProof := "humilityVirtue.conserves_reciprocity"
      cadenceProof := "humilityVirtue.respects_cadence"
      gaugeProof := "humilityVirtue.gauge_invariant" }
  , { name := "Hope"
      transformConst := "IndisputableMonolith.Ethics.Virtues.hopeVirtue"
      conservesProof := "hopeVirtue.conserves_reciprocity"
      cadenceProof := "hopeVirtue.respects_cadence"
      gaugeProof := "hopeVirtue.gauge_invariant" }
  , { name := "Prudence"
      transformConst := "IndisputableMonolith.Ethics.Virtues.prudenceVirtue"
      conservesProof := "prudenceVirtue.conserves_reciprocity"
      cadenceProof := "prudenceVirtue.respects_cadence"
      gaugeProof := "prudenceVirtue.gauge_invariant" }
  , { name := "Compassion"
      transformConst := "IndisputableMonolith.Ethics.Virtues.compassionVirtue"
      conservesProof := "compassionVirtue.conserves_reciprocity"
      cadenceProof := "compassionVirtue.respects_cadence"
      gaugeProof := "compassionVirtue.gauge_invariant" }
  , { name := "Sacrifice"
      transformConst := "IndisputableMonolith.Ethics.Virtues.sacrificeVirtue"
      conservesProof := "sacrificeVirtue.conserves_reciprocity"
      cadenceProof := "sacrificeVirtue.respects_cadence"
      gaugeProof := "sacrificeVirtue.gauge_invariant" }
  , { name := "Creativity"
      transformConst := "IndisputableMonolith.Ethics.Virtues.creativityVirtue"
      conservesProof := "creativityVirtue.conserves_reciprocity"
      cadenceProof := "creativityVirtue.respects_cadence"
      gaugeProof := "creativityVirtue.gauge_invariant" }
  , { name := "Courage"
      transformConst := "IndisputableMonolith.Ethics.Virtues.courageVirtue"
      conservesProof := "courageVirtue.conserves_reciprocity"
      cadenceProof := "courageVirtue.respects_cadence"
      gaugeProof := "courageVirtue.gauge_invariant" }
  ]

def soulExports : List SoulInvariantExport :=
  [ { name := "VirtueSignature.canonical"
      description := "Canonical virtue signature derived from virtue_generators"
      proof := "IndisputableMonolith.Ethics.Soul.Character.VirtueSignature.canonical" }
  , { name := "SoulCharacter.energy_pos"
      description := "All SoulCharacter states maintain strictly positive recognition energy"
      proof := "IndisputableMonolith.Ethics.Soul.Character.energy_pos" }
  ]

def exportPayload : Json :=
  Json.mkObj
    [ ("version", Json.str "1.0.0")
    , ("virtues", toJson virtueExports)
    , ("soul_invariants", toJson soulExports)
    ]

def main : IO Unit := do
  IO.println (exportPayload.pretty 2)
