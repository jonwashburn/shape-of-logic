import Mathlib

namespace IndisputableMonolith
namespace Masses
namespace Ribbons

structure Ribbon where
  start : Fin 8
  dir   : Bool
  bit   : Int
  tag   : Nat

/-- A word is a list of ribbon syllables. -/
abbrev Word := List Ribbon

end Ribbons
end Masses
end IndisputableMonolith


