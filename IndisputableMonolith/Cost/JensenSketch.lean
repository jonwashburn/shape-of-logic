import IndisputableMonolith.Cost

/-!
# JensenSketch (compatibility wrapper)

Historically this module duplicated the `JensenSketch`/T5 interface.
The canonical definitions now live in `IndisputableMonolith/Cost.lean`.

Importing `IndisputableMonolith.Cost.JensenSketch` is therefore equivalent to importing
`IndisputableMonolith.Cost`, with one small convenience instance retained below.
-/

namespace IndisputableMonolith
namespace Cost

/-- Convenience: `JensenSketch` bounds immediately give `AveragingAgree`, i.e.\
pointwise exp-axis agreement with `Jcost`. -/
instance (priority := 95) averagingAgree_of_jensen {F : ℝ → ℝ} [JensenSketch F] :
  AveragingAgree F :=
  ⟨by
    intro t
    exact le_antisymm (JensenSketch.axis_upper (F:=F) t) (JensenSketch.axis_lower (F:=F) t)⟩

end Cost
end IndisputableMonolith
