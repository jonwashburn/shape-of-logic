import Mathlib
import IndisputableMonolith.Constants

/-!
# RS-Native Measurement Framework (Core)

This module defines a **Lean-first** measurement scaffold for Recognition Science (RS).

Design goals:
- **Core theory is RS-native**: ticks/voxels/coh/act + ledger observables, with \(τ₀ = 1\).
- **SI/CODATA is optional calibration**: lives outside core (`Constants.RSNativeUnits.ExternalCalibration`).
- **Protocols are explicit**: every measurement carries a protocol + falsifiers, so “arbitrary choices”
  (windowing, coarse-graining, basis choices) cannot be hidden.

This file is intentionally small and dependency-light. Concrete observables live in
`IndisputableMonolith.Measurement.RSNative.Catalog.*`.
-/

namespace IndisputableMonolith
namespace Measurement
namespace RSNative

/-! ## Protocol metadata -/

inductive Status
  | spec
  | derived
  | hypothesis
  | scaffold
  deriving DecidableEq, Repr

/-- A measurement protocol: how an RS observable is extracted from a state/trace. -/
structure Protocol where
  /-- Short protocol identifier (stable, machine-friendly). -/
  name : String
  /-- Human-readable summary. -/
  summary : String := ""
  /-- Claim hygiene for the extraction step. -/
  status : Status := .spec
  /-- Explicit assumptions (kept small and testable). -/
  assumptions : List String := []
  /-- Falsifiers: what would prove this protocol wrong. -/
  falsifiers : List String := []

namespace Protocol

/-- Protocol hygiene predicate (v1/v2).

Rules:
- `name` must be non-empty
- if `status` is `.hypothesis` or `.scaffold`, both `assumptions` and `falsifiers` must be non-empty -/
def hygienic (p : Protocol) : Prop :=
  p.name ≠ "" ∧
    match p.status with
    | .hypothesis | .scaffold => p.assumptions ≠ [] ∧ p.falsifiers ≠ []
    | _ => True

/-- Boolean check version of `Protocol.hygienic` (useful for audits). -/
def hygienicBool (p : Protocol) : Bool :=
  (!p.name.isEmpty) &&
    match p.status with
    | .hypothesis | .scaffold => (!p.assumptions.isEmpty) && (!p.falsifiers.isEmpty)
    | _ => true

end Protocol

/-! ## Time windows (ticks) -/

/-- A discrete measurement window, expressed in ticks. -/
structure Window where
  /-- Start tick. -/
  t0 : Nat
  /-- Window length in ticks (0 = instantaneous). -/
  len : Nat
  deriving DecidableEq

namespace Window

@[simp] def instant (t : Nat) : Window := ⟨t, 0⟩

@[simp] def stop (w : Window) : Nat := w.t0 + w.len

end Window

/-! ## Uncertainty and measurement record -/

/-- Uncertainty semantics for scalar (real-valued) measurements.

v1 used only `sigma`. v2 adds:
- interval bounds
- a finite discrete distribution scaffold

This is intentionally lightweight: it is a *reporting seam* for measurement,
not a full probability theory. -/
inductive Uncertainty where
  /-- Symmetric 1σ uncertainty (standard deviation), in the same units as the value. -/
  | sigma (σ : ℝ) (hσ : 0 ≤ σ)
  /-- Interval uncertainty: the true value lies in `[lo, hi]`. -/
  | interval (lo hi : ℝ) (hlohi : lo ≤ hi)
  /-- Finite discrete distribution scaffold: list of `(value, weight)` pairs.
      We do not require proof obligations (nonneg/sum=1) in v2; protocols must state hygiene. -/
  | discrete (support : List (ℝ × ℝ))

namespace Uncertainty

@[simp] def sigmaVal : Uncertainty → Option ℝ
  | sigma σ _ => some σ
  | _ => none

@[simp] def intervalBounds : Uncertainty → Option (ℝ × ℝ)
  | interval lo hi _ => some (lo, hi)
  | _ => none

end Uncertainty

/-- A measurement value with protocol + (optional) time window + (optional) uncertainty. -/
structure Measurement (α : Type) where
  value : α
  window : Option Window := none
  protocol : Protocol
  uncertainty : Option Uncertainty := none
  notes : List String := []

namespace Measurement

/-- Map the value of a measurement, preserving window/protocol/uncertainty/notes. -/
def map {α β : Type} (f : α → β) (m : Measurement α) : Measurement β :=
  { value := f m.value
    window := m.window
    protocol := m.protocol
    uncertainty := m.uncertainty
    notes := m.notes
  }

/-- Map the value and replace protocol (e.g., when you derive a new observable). -/
def mapWithProtocol {α β : Type} (f : α → β) (p : Protocol) (m : Measurement α) : Measurement β :=
  { value := f m.value
    window := m.window
    protocol := p
    uncertainty := m.uncertainty
    notes := m.notes
  }

/-- Transform the uncertainty record (when present). -/
def mapUncertainty {α : Type} (uMap : Uncertainty → Uncertainty) (m : Measurement α) : Measurement α :=
  { value := m.value
    window := m.window
    protocol := m.protocol
    uncertainty := m.uncertainty.map uMap
    notes := m.notes
  }

def addNote {α : Type} (note : String) (m : Measurement α) : Measurement α :=
  { m with notes := m.notes ++ [note] }

def addNotes {α : Type} (notes : List String) (m : Measurement α) : Measurement α :=
  { m with notes := m.notes ++ notes }

end Measurement

/-- An observable extracts a `Measurement α` from some state type `S`. -/
abbrev Observable (S α : Type) : Type := S → Measurement α

/-! ## Tagged quantities (type-safe units) -/

/-- A real-valued quantity tagged with a unit/semantic label. -/
structure Quantity (U : Type) where
  val : ℝ

instance (U : Type) : CoeTC (Quantity U) ℝ := ⟨Quantity.val⟩

namespace Quantity

instance (U : Type) : Zero (Quantity U) := ⟨⟨0⟩⟩
instance (U : Type) : Add (Quantity U) := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance (U : Type) : Sub (Quantity U) := ⟨fun a b => ⟨a.val - b.val⟩⟩
instance (U : Type) : Neg (Quantity U) := ⟨fun a => ⟨-a.val⟩⟩
instance (U : Type) : SMul ℝ (Quantity U) := ⟨fun r a => ⟨r * a.val⟩⟩

@[simp] theorem val_zero (U : Type) : (0 : Quantity U).val = 0 := rfl
@[simp] theorem val_add {U : Type} (a b : Quantity U) : (a + b).val = a.val + b.val := rfl
@[simp] theorem val_sub {U : Type} (a b : Quantity U) : (a - b).val = a.val - b.val := rfl
@[simp] theorem val_neg {U : Type} (a : Quantity U) : (-a).val = -a.val := rfl
@[simp] theorem val_smul {U : Type} (r : ℝ) (a : Quantity U) : (r • a).val = r * a.val := rfl

end Quantity

/-! ### Unit/semantic tags (empty types) -/

inductive TickUnit : Type
inductive VoxelUnit : Type
inductive CohUnit : Type
inductive ActUnit : Type
inductive CostUnit : Type
inductive SkewUnit : Type
inductive ZUnit : Type

abbrev Tick := Quantity TickUnit
abbrev Voxel := Quantity VoxelUnit
abbrev Coh := Quantity CohUnit
abbrev Act := Quantity ActUnit
abbrev Cost := Quantity CostUnit
abbrev Skew := Quantity SkewUnit
abbrev ZCharge := Quantity ZUnit

end RSNative
end Measurement
end IndisputableMonolith
