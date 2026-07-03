/-
  PrimitiveRecognitionCalculus/TraceClosure.lean

  Round-trip source:
    PRC_Kernel_Spec_20260526.html

  Spec anchors:
    K1 (`δ + trace-closure`), R9, K4.13

  This module records the first completed-trace boundary. It does not claim
  that completed infinity is δ-only. It explicitly carries the
  `traceClosure` strength tag.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Basic
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Orbit
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Strength

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- K4.13/R9. A completed trace is an infinite ledger of distinction acts.
This is a trace-closure object, not a finite δ-only trace. -/
structure CompletedTrace where
  actAt : Nat → DistinctionAct

namespace CompletedTrace

/-- The finite prefix of length `n` cut out of a completed trace. -/
def finitePrefix (S : CompletedTrace) : Nat → Trace
  | 0 => Trace.empty
  | Nat.succ n => Trace.extend (finitePrefix S n) (S.actAt n)

@[simp] theorem prefix_zero (S : CompletedTrace) :
    S.finitePrefix 0 = Trace.empty := by
  rfl

@[simp] theorem prefix_succ (S : CompletedTrace) (n : Nat) :
    S.finitePrefix (Nat.succ n) = Trace.extend (S.finitePrefix n) (S.actAt n) := by
  rfl

/-- The canonical completed trace repeats the primitive distinction act. -/
def canonical : CompletedTrace where
  actAt := fun _ => DistinctionAct.delta

@[simp] theorem canonical_actAt (n : Nat) :
    canonical.actAt n = DistinctionAct.delta := by
  rfl

/-- Every prefix of the canonical completed trace is a finite trace. -/
theorem canonical_prefix_exists (n : Nat) :
    Nonempty Trace := by
  exact ⟨canonical.finitePrefix n⟩

end CompletedTrace

/-- K4.13. A completed orbit ledger is the infinite sequence of finite
δ-orbit positions. This is the natural-number side of trace closure. -/
structure CompletedOrbitLedger where
  positionAt : Nat → DistinctionNat

namespace CompletedOrbitLedger

/-- The canonical completed orbit sends verifier index `n` to the `n`th
δ-orbit position. -/
def canonical : CompletedOrbitLedger where
  positionAt := DistinctionNat.ofNat

@[simp] theorem canonical_toNat (n : Nat) :
    (canonical.positionAt n).toNat = n := by
  exact DistinctionNat.toNat_ofNat n

theorem canonical_succ (n : Nat) :
    canonical.positionAt (Nat.succ n) =
      DistinctionNat.succ (canonical.positionAt n) := by
  rfl

end CompletedOrbitLedger

/-- K1/R9. Audit record: completed traces require the trace-closure tag. -/
def traceClosureClaim : StrengthClaim where
  label := "K4.13_trace_closure_boundary"
  tag := StrengthTag.traceClosure
  statement := "Completed traces and completed orbit ledgers extend finite PRC by trace closure."

/-- K4.13. First trace-closure certificate. -/
structure TraceClosureCertificate : Prop where
  completed_trace_exists : Nonempty CompletedTrace
  canonical_completed_trace_exists : Nonempty CompletedTrace
  completed_orbit_ledger_exists : Nonempty CompletedOrbitLedger
  canonical_orbit_verifier_faithful :
    ∀ n : Nat, (CompletedOrbitLedger.canonical.positionAt n).toNat = n
  strength_tag : traceClosureClaim.tag = StrengthTag.traceClosure

/-- K4.13. The trace-closure boundary is inhabited and tagged honestly. -/
theorem trace_closure_certificate : TraceClosureCertificate where
  completed_trace_exists := ⟨CompletedTrace.canonical⟩
  canonical_completed_trace_exists := ⟨CompletedTrace.canonical⟩
  completed_orbit_ledger_exists := ⟨CompletedOrbitLedger.canonical⟩
  canonical_orbit_verifier_faithful := CompletedOrbitLedger.canonical_toNat
  strength_tag := rfl

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
