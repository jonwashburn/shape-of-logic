import Mathlib
import IndisputableMonolith.Streams
import IndisputableMonolith.Streams.Blocks

/-!
Re-export of the eight-tick stream invariants used throughout the measurement layer,
plus a lightweight continuous-time measurement scaffold (CQ score).
-/
namespace IndisputableMonolith
namespace Measurement

open PatternLayer
open MeasurementLayer
open Classical

/-- Boolean streams as used by the measurement layer. -/
abbrev Stream := PatternLayer.Stream

/-- Finite windows of length `n`. -/
abbrev Pattern (n : Nat) := PatternLayer.Pattern n

/-- Integer functional counting ones in a window. -/
abbrev Z_of_window {n : Nat} (w : Pattern n) : Nat := PatternLayer.Z_of_window w

/-- Cylinder set of streams matching a window. -/
abbrev Cylinder {n : Nat} (w : Pattern n) : Set Stream := PatternLayer.Cylinder w

/-- Periodic extension of an 8-bit window. -/
abbrev extendPeriodic8 := PatternLayer.extendPeriodic8

/-- Sum of the first `m` bits of a stream. -/
abbrev sumFirst (m : Nat) (s : Stream) : Nat := PatternLayer.sumFirst m s

/-- Sum of one 8-tick sub-block starting at index `j * 8`. -/
abbrev subBlockSum8 (s : Stream) (j : Nat) : Nat := MeasurementLayer.subBlockSum8 s j

/-- Aligned block sum over `k` copies of the 8-tick window. -/
abbrev blockSumAligned8 (k : Nat) (s : Stream) : Nat := MeasurementLayer.blockSumAligned8 k s

/-- Averaged (per-window) observation over aligned blocks. -/
abbrev observeAvg8 (k : Nat) (s : Stream) : Nat := MeasurementLayer.observeAvg8 k s

/-- On any stream lying in the cylinder of an 8-bit window, the first block sum equals `Z`. -/
lemma firstBlockSum_eq_Z_on_cylinder (w : Pattern 8) {s : Stream}
    (hs : s ∈ Cylinder w) :
    subBlockSum8 s 0 = Z_of_window w := by
  simpa [subBlockSum8, Cylinder, Z_of_window]
    using MeasurementLayer.firstBlockSum_eq_Z_on_cylinder (w:=w) (s:=s) hs

/-- For periodic extensions of an 8-bit window, each sub-block sums to `Z`. -/
lemma subBlockSum8_periodic_eq_Z (w : Pattern 8) (j : Nat) :
    subBlockSum8 (extendPeriodic8 w) j = Z_of_window w := by
  simpa [subBlockSum8, extendPeriodic8, Z_of_window]
    using MeasurementLayer.subBlockSum8_periodic_eq_Z (w:=w) j

/-- For `s = extendPeriodic8 w`, summing `k` aligned 8-blocks yields `k * Z(w)`. -/
lemma blockSumAligned8_periodic (w : Pattern 8) (k : Nat) :
    blockSumAligned8 k (extendPeriodic8 w) = k * Z_of_window w := by
  simpa [blockSumAligned8, extendPeriodic8, Z_of_window]
    using MeasurementLayer.blockSumAligned8_periodic (w:=w) k

/-- DNARP Eq.: on periodic extensions of an 8-bit window, the averaged observation equals `Z`. -/
lemma observeAvg8_periodic_eq_Z {k : Nat} (hk : k ≠ 0) (w : Pattern 8) :
    observeAvg8 k (extendPeriodic8 w) = Z_of_window w := by
  simpa [observeAvg8, extendPeriodic8, Z_of_window]
    using MeasurementLayer.observeAvg8_periodic_eq_Z (k:=k) (hk:=hk) (w:=w)

/-- Minimal measurement map scaffold. -/
structure Map (State Obs : Type) where
  T : ℝ
  T_pos : 0 < T
  meas : (ℝ → State) → ℝ → Obs

/-- Midpoint sampling average (lightweight helper). -/
@[simp] noncomputable def avg (T : ℝ) (_hT : 0 < T) (x : ℝ → ℝ) (t : ℝ) : ℝ :=
  let tmid := t + T / 2
  x tmid

/-- CQ (coherence quotient) descriptor with bounds witnessed explicitly. -/
structure CQ where
  listensPerSec : ℝ
  opsPerSec : ℝ
  coherence8 : ℝ
  coherence8_bounds :
    0 ≤ coherence8 ∧ 0 ≤ coherence8 ∧ coherence8 ≤ 1 ∧ coherence8 ≤ 1

/-- CQ score; zero when the operations-per-second denominator vanishes. -/
@[simp] noncomputable def score (c : CQ) : ℝ :=
  if c.opsPerSec = 0 then 0 else (c.listensPerSec / c.opsPerSec) * c.coherence8

end Measurement
end IndisputableMonolith
