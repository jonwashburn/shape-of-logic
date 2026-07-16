import IndisputableMonolith.Measurement.RSNative.Core

namespace IndisputableMonolith
namespace Measurement
namespace RSNative

/-!
# Cross-Observer Calibration (Scaffold)

This module defines the protocol-level seam for comparing measurements across observers.

It:
- makes the alignment explicit data (a map and a protocol),
- records invariants that must be preserved for a comparison to be meaningful,
- requires falsifiers whenever the status is `.hypothesis` or `.scaffold`.
-/

/-- An alignment protocol extends `Protocol` with explicit invariants for cross-agent comparability. -/
structure AlignmentProtocol where
  protocol : Protocol
  /-- Invariants that must be preserved under alignment (e.g., dominant mode, total Z, etc.). -/
  invariants : List String := []

namespace AlignmentProtocol

@[simp] def name (A : AlignmentProtocol) : String := A.protocol.name
@[simp] def status (A : AlignmentProtocol) : Status := A.protocol.status

end AlignmentProtocol

/-- An alignment map from one agent’s coordinate system to another’s. -/
abbrev AlignmentMap (α β : Type) : Type := α → β

/-- A packaged alignment: map + protocol hygiene. -/
structure Alignment (α β : Type) where
  map : AlignmentMap α β
  protocol : AlignmentProtocol

namespace Alignment

/-- Apply an alignment map to a measurement value, keeping window/uncertainty, and appending an audit note. -/
noncomputable def apply {α β : Type} (A : Alignment α β) (m : Measurement α) : Measurement β :=
  { value := A.map m.value
    window := m.window
    protocol := A.protocol.protocol
    uncertainty := m.uncertainty
    notes := m.notes ++ [s!"Aligned via {A.protocol.name}"]
  }

end Alignment

end RSNative
end Measurement
end IndisputableMonolith
