import Mathlib

namespace IndisputableMonolith
namespace Masses

structure ModuleSummary where
  name : String
  description : String
  manuscript : String

@[simp] def modules : List ModuleSummary :=
  [ { name := "Anchor", description := "Canonical constants", manuscript := "Paper1" }
  , { name := "AnchorPolicy", description := "Policy interfaces", manuscript := "Paper1" }
  , { name := "Assumptions", description := "Model assumptions", manuscript := "Paper1" }
  , { name := "Basic", description := "Mass ladder placeholder", manuscript := "Paper1" }
  ]

end Masses
end IndisputableMonolith
