import Mathlib
import IndisputableMonolith.Masses.RSBridge.Anchor

namespace IndisputableMonolith
namespace Masses
namespace RungConstructor

/-- Canonical species for the mass framework. -/
inductive Species
  | fermion (f : RSBridge.Fermion)
  | W
  | Z
  | H
  deriving DecidableEq, Repr

open RSBridge

/-- Sector identifier (local copy to avoid circular import).
    Note: Neutrino is distinct from Lepton because it has a different baseline (0 vs 2). -/
inductive Sector | Lepton | Neutrino | UpQuark | DownQuark | Electroweak
  deriving DecidableEq, Repr

/-- Sector mapping for the rung constructor. -/
def sectorOf : Species → Sector
  | .fermion f =>
      match RSBridge.sectorOf f with
      | .lepton   => .Lepton
      | .neutrino => .Neutrino
      | .up       => .UpQuark
      | .down     => .DownQuark
  | .W | .Z | .H => .Electroweak

/-- Charge-index q̃ used as input to the constructor motifs. -/
def tildeQ : Species → ℤ
  | .fermion f => RSBridge.tildeQ f
  | .W => 0
  | .Z => 0
  | .H => 0

end RungConstructor
end Masses
end IndisputableMonolith
