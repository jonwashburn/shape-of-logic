import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DOrbitClassification
import IndisputableMonolith.Gravity.Analysis.ReggeBlochFold4D

/-!
# Orbit covering permutations for 4D Regge Bloch transport

For each hinge slot `(s,t)` of orbit type `ty`, the covering coordinate
permutation is the **first** `p : Fin 24` (in `permAxes` order) such that

  `permDiffPair (coordPermOf p) (orbitRep ty) = (diffMaskA s t, diffMaskB s t)`.

This is the transport used for **all** orbits.  The hand table
`transportPermOfDiff` / `slotTransportPerm` is `(1,1)`-only and must not be
used for non-`(1,1)` slots (MEASURED: factorized vs transported fold lesson).

## Tier tags

* THEOREM: covering existence on every slot; agreement with
  `slotTransportPerm` on `(1,1)`.
* No `sorry` / `admit` / new axioms / `native_decide` / `: True` shells.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeBlochOrbitTransport4D

open ReggeHinge4DOrbitClassification
open ReggeBlochFold4D

noncomputable section

/-- Boolean cover test for a candidate coordinate permutation. -/
def coversOrbitSlot (ty : HingeOrbitType) (s : Fin 24) (t : Fin 10)
    (p : Fin 24) : Bool :=
  decide
    (permDiffPair (coordPermOf p) (orbitRep ty).1 (orbitRep ty).2 =
      (diffMaskA s t, diffMaskB s t))

/-- First covering `S₄` index for slot `(s,t)` relative to `orbitRep ty`.
Falls back to `0` only if no cover exists (never on realizable slots). -/
def orbitCoveringPerm (ty : HingeOrbitType) (s : Fin 24) (t : Fin 10) :
    Fin 24 :=
  match List.find? (coversOrbitSlot ty s t) (List.finRange 24) with
  | some p => p
  | none => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000 in
/-- Every lattice slot is covered by its own orbit representative. -/
theorem orbitCoveringPerm_covers (s : Fin 24) (t : Fin 10) :
    coversOrbitSlot (hingeOrbitType s t) s t
        (orbitCoveringPerm (hingeOrbitType s t) s t) = true := by
  fin_cases s <;> fin_cases t <;> decide

/-- Packaging: when `ty` is the slot's orbit type, the covering equation holds. -/
theorem orbitCoveringPerm_spec (ty : HingeOrbitType) (s : Fin 24) (t : Fin 10)
    (h : hingeOrbitType s t = ty) :
    permDiffPair (coordPermOf (orbitCoveringPerm ty s t))
        (orbitRep ty).1 (orbitRep ty).2 =
      (diffMaskA s t, diffMaskB s t) := by
  have hc := orbitCoveringPerm_covers s t
  subst h
  simpa [coversOrbitSlot, decide_eq_true_iff] using hc

set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000 in
/-- On `(1,1)` slots the covering perm agrees with the legacy table. -/
theorem orbitCoveringPerm_t11_eq_slotTransportPerm (s : Fin 24) (t : Fin 10) :
    orbitCoveringPerm .t11 s t = slotTransportPerm s t := by
  fin_cases s <;> fin_cases t <;> decide

end

end ReggeBlochOrbitTransport4D
end Analysis
end Gravity
end IndisputableMonolith
