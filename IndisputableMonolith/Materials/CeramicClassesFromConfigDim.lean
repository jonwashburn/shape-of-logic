import Mathlib
import IndisputableMonolith.Constants

/-!
# Ceramic Classes from configDim — Materials Depth

Five canonical ceramic families (= configDim D = 5):
  oxides, carbides, nitrides, borides, silicates.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Materials.CeramicClassesFromConfigDim

inductive CeramicClass where
  | oxide
  | carbide
  | nitride
  | boride
  | silicate
  deriving DecidableEq, Repr, BEq, Fintype

theorem ceramicClass_count : Fintype.card CeramicClass = 5 := by decide

structure CeramicClassesCert where
  five_classes : Fintype.card CeramicClass = 5

def ceramicClassesCert : CeramicClassesCert where
  five_classes := ceramicClass_count

end IndisputableMonolith.Materials.CeramicClassesFromConfigDim
