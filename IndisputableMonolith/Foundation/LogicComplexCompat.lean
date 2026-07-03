import IndisputableMonolith.Foundation.ComplexFromLogic
import IndisputableMonolith.NumberTheory.EulerProductEqualsZeta
import IndisputableMonolith.NumberTheory.CompletedZetaLedger

/-!
  LogicComplexCompat.lean

  Compatibility layer between recovered complex numbers and Mathlib's analytic
  complex substrate.

  Phase 2 decision: we do not redefine holomorphy, contour integration, or the
  Riemann zeta function on a separate complex analysis stack.  We use Mathlib
  `ℂ` as the analytic substrate, and this module makes that use explicit:
  every recovered-complex statement is transported through
  `LogicComplex.toComplex`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicComplexCompat

open ComplexFromLogic
open ComplexFromLogic.LogicComplex
open Filter Topology

noncomputable section

/-- The Riemann zeta function read on recovered complex inputs. -/
def logicRiemannZeta (s : LogicComplex) : ℂ :=
  riemannZeta (toComplex s)

/-- The completed zeta function read on recovered complex inputs. -/
def logicCompletedRiemannZeta (s : LogicComplex) : ℂ :=
  completedRiemannZeta (toComplex s)

@[simp] theorem logicRiemannZeta_fromComplex (s : ℂ) :
    logicRiemannZeta (fromComplex s) = riemannZeta s := by
  simp [logicRiemannZeta]

@[simp] theorem logicCompletedRiemannZeta_fromComplex (s : ℂ) :
    logicCompletedRiemannZeta (fromComplex s) = completedRiemannZeta s := by
  simp [logicCompletedRiemannZeta]

/-- Recovered-complex real part agrees with the real part after transport. -/
theorem toComplex_re_eq (s : LogicComplex) :
    (toComplex s).re = RealsFromLogic.LogicReal.toReal s.re := rfl

/-- The Euler product theorem, read on recovered complex inputs. -/
theorem logicRiemannZeta_eulerProduct_tendsto
    (s : LogicComplex) (hs : 1 < (toComplex s).re) :
    Tendsto (fun n : ℕ ↦
        NumberTheory.finitePrimeLedgerPartition (toComplex s) (Nat.primesBelow n))
      atTop (𝓝 (logicRiemannZeta s)) := by
  simpa [logicRiemannZeta] using
    NumberTheory.EulerProductEqualsZeta.ledger_partition_equals_zeta
      (toComplex s) hs

/-- Completed zeta satisfies the functional equation on recovered complex
inputs, by transport to Mathlib's `completedRiemannZeta`. -/
theorem logicCompletedRiemannZeta_one_sub (s : LogicComplex) :
    logicCompletedRiemannZeta (fromComplex (1 - toComplex s)) =
      logicCompletedRiemannZeta s := by
  simp [logicCompletedRiemannZeta, completedRiemannZeta_one_sub]

/-- Certificate that all analytic zeta operations are performed in Mathlib `ℂ`
through the recovered-complex equivalence. -/
structure LogicComplexAnalyticSubstrateCert where
  carrier_equiv : LogicComplex ≃ ℂ
  zeta_transport : ∀ s : LogicComplex,
    logicRiemannZeta s = riemannZeta (toComplex s)
  completed_zeta_transport : ∀ s : LogicComplex,
    logicCompletedRiemannZeta s = completedRiemannZeta (toComplex s)
  euler_product :
    ∀ s : LogicComplex, 1 < (toComplex s).re →
      Tendsto (fun n : ℕ ↦
        NumberTheory.finitePrimeLedgerPartition (toComplex s) (Nat.primesBelow n))
        atTop (𝓝 (logicRiemannZeta s))
  completed_functional_equation :
    ∀ s : LogicComplex,
      logicCompletedRiemannZeta (fromComplex (1 - toComplex s)) =
        logicCompletedRiemannZeta s

/-- The analytic substrate compatibility certificate for Phase 2. -/
def logicComplexAnalyticSubstrateCert : LogicComplexAnalyticSubstrateCert where
  carrier_equiv := equivComplex
  zeta_transport := fun _ => rfl
  completed_zeta_transport := fun _ => rfl
  euler_product := logicRiemannZeta_eulerProduct_tendsto
  completed_functional_equation := logicCompletedRiemannZeta_one_sub

end

end LogicComplexCompat
end Foundation
end IndisputableMonolith
