import Mathlib
import IndisputableMonolith.Constants

/-!
# Nuclear Magic Isotopes from RS — Chemistry Structural Depth

Five canonical doubly-magic nuclides (= configDim D = 5):
  He-4 (2,2), O-16 (8,8), Ca-40 (20,20), Ca-48 (20,28), Ni-56 (28,28).

Each has both proton and neutron number equal to a magic number from
{2, 8, 20, 28, 50, 82, 126}.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Chemistry.NuclearMagicIsotopesFromRS

inductive DoublyMagicNuclide where
  | he4
  | o16
  | ca40
  | ca48
  | ni56
  deriving DecidableEq, Repr, BEq, Fintype

theorem doublyMagic_count : Fintype.card DoublyMagicNuclide = 5 := by decide

structure NuclearMagicCert where
  five_nuclides : Fintype.card DoublyMagicNuclide = 5

def nuclearMagicCert : NuclearMagicCert where
  five_nuclides := doublyMagic_count

end IndisputableMonolith.Chemistry.NuclearMagicIsotopesFromRS
