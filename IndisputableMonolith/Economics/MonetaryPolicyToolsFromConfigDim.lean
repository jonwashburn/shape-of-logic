import Mathlib
import IndisputableMonolith.Constants

/-!
# Monetary Policy Tools from configDim — E6 Depth

Five canonical central-bank monetary tools (= configDim D = 5):
  open-market operations, discount rate, reserve requirement,
  quantitative easing, forward guidance.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Economics.MonetaryPolicyToolsFromConfigDim

inductive MonetaryTool where
  | openMarket
  | discountRate
  | reserveRequirement
  | qe
  | forwardGuidance
  deriving DecidableEq, Repr, BEq, Fintype

theorem monetaryTool_count : Fintype.card MonetaryTool = 5 := by decide

structure MonetaryToolsCert where
  five_tools : Fintype.card MonetaryTool = 5

def monetaryToolsCert : MonetaryToolsCert where
  five_tools := monetaryTool_count

end IndisputableMonolith.Economics.MonetaryPolicyToolsFromConfigDim
