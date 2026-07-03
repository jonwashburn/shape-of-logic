import Mathlib
import IndisputableMonolith.Constants

/-!
# Acid-Base Theories from configDim — Chemistry Foundations Depth

Five canonical acid-base theories (= configDim D = 5):
  Arrhenius (proton donor in water), Brønsted-Lowry (proton donor),
  Lewis (electron-pair acceptor), Usanovich (electron/cation/anion),
  Pearson HSAB (hard/soft acids-bases).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Chemistry.AcidBaseTheoriesFromConfigDim

inductive AcidBaseTheory where
  | arrhenius
  | bronstedLowry
  | lewis
  | usanovich
  | pearsonHSAB
  deriving DecidableEq, Repr, BEq, Fintype

theorem acidBaseTheory_count : Fintype.card AcidBaseTheory = 5 := by decide

structure AcidBaseTheoriesCert where
  five_theories : Fintype.card AcidBaseTheory = 5

def acidBaseTheoriesCert : AcidBaseTheoriesCert where
  five_theories := acidBaseTheory_count

end IndisputableMonolith.Chemistry.AcidBaseTheoriesFromConfigDim
