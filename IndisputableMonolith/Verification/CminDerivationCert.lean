import Mathlib
import IndisputableMonolith.CPM.LawOfExistence

/-!
# c_min Derivation Certificate

This certificate proves that the coercivity constants c_min are COMPUTED
from the derived CPM constants, not assumed.

## The Formula

c_min = 1 / (K_net · C_proj · C_eng)

## Two Routes, Two Values

1. **Cone route**: c_min = 1/2
   - K_net = 1, C_proj = 2, C_eng = 1
   - c_min = 1/(1 · 2 · 1) = 1/2

2. **Eight-tick route**: c_min = 49/162
   - K_net = 81/49, C_proj = 2, C_eng = 1
   - c_min = 1/((81/49) · 2 · 1) = 49/162

## Why This Matters

c_min is the coercivity constant: energy_gap ≥ c_min · defect.
Larger c_min means stronger control. The cone route has better
coercivity (1/2 > 49/162) but the eight-tick is more explicit.
-/

namespace IndisputableMonolith
namespace Verification
namespace CminDerivation

open IndisputableMonolith.CPM.LawOfExistence

structure CminDerivationCert where
  deriving Repr

/-- Verification predicate: c_min values are computed from derived constants.

Certifies:
1. c_min = 1/2 for cone route
2. c_min = 49/162 for eight-tick route
3. Positivity for coercivity proofs
4. Explicit computation formula
-/
@[simp] def CminDerivationCert.verified (_c : CminDerivationCert) : Prop :=
  -- Cone route: c_min = 1/2
  (cmin RS.coneConstants = 1/2) ∧
  -- Eight-tick route: c_min = 49/162
  (cmin Bridge.eightTickConstants = 49/162) ∧
  -- Positivity
  (0 < cmin RS.coneConstants) ∧
  (0 < cmin Bridge.eightTickConstants) ∧
  -- Cone has better coercivity than eight-tick
  (cmin RS.coneConstants > cmin Bridge.eightTickConstants)

@[simp] theorem CminDerivationCert.verified_any (c : CminDerivationCert) :
    CminDerivationCert.verified c := by
  refine ⟨?cone_cmin, ?eight_cmin, ?cone_pos, ?eight_pos, ?cone_better⟩
  · exact Bridge.c_value_cone
  · exact Bridge.c_value_eight_tick
  · rw [Bridge.c_value_cone]; norm_num
  · rw [Bridge.c_value_eight_tick]; norm_num
  · rw [Bridge.c_value_cone, Bridge.c_value_eight_tick]; norm_num

end CminDerivation
end Verification
end IndisputableMonolith
