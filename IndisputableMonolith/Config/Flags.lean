import Mathlib

namespace IndisputableMonolith
namespace Config

/-- vNext feature flags (default-safe). Certificates on by default; behavior changes off. -/
structure Flags where
  /-- Enable v2 certificate bundle (report emission). -/
  enableV2Certs    : Bool := true
  /-- Enable Macrocore ISA and macro-expansion path. -/
  enableMacrocore  : Bool := false
  /-- Enable φ‑IR codec and neutral window packer. -/
  enablePhiIR      : Bool := false
  /-- Enable ConsentDerivative static gate. -/
  enableConsentGate : Bool := false
  /-- Enable J‑greedy scheduler (optional). -/
  enableJScheduler : Bool := false
deriving Repr, DecidableEq

/-- Global default flags. Projects may override via their own module. -/
def default : Flags := {}

end Config
end IndisputableMonolith
