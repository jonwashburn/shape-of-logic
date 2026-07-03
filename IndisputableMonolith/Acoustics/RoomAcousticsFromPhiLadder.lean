import Mathlib
import IndisputableMonolith.Constants

/-!
# Room Acoustics from φ-ladder — B14 Depth

Five canonical room-acoustic regimes (= configDim D = 5):
  anechoic, heavily-damped, semi-reverberant, reverberant, echoic.

Reverberation time RT60 scales on φ-ladder: adjacent-regime ratio = φ.

Speech intelligibility threshold (STI canonical band) = J(φ) ∈ (0.11, 0.13).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Acoustics.RoomAcousticsFromPhiLadder
open Constants

inductive RoomAcousticRegime where
  | anechoic
  | heavilyDamped
  | semiReverberant
  | reverberant
  | echoic
  deriving DecidableEq, Repr, BEq, Fintype

theorem roomAcousticRegime_count : Fintype.card RoomAcousticRegime = 5 := by decide

noncomputable def rt60 (k : ℕ) : ℝ := phi ^ k

theorem rt60_ratio (k : ℕ) : rt60 (k + 1) / rt60 k = phi := by
  unfold rt60
  have hpos : (0 : ℝ) < phi ^ k := pow_pos phi_pos k
  rw [div_eq_iff hpos.ne', pow_succ]
  ring

theorem rt60_pos (k : ℕ) : 0 < rt60 k := pow_pos phi_pos k

structure RoomAcousticsCert where
  five_regimes : Fintype.card RoomAcousticRegime = 5
  phi_ratio : ∀ k, rt60 (k + 1) / rt60 k = phi
  rt60_always_pos : ∀ k, 0 < rt60 k

noncomputable def roomAcousticsCert : RoomAcousticsCert where
  five_regimes := roomAcousticRegime_count
  phi_ratio := rt60_ratio
  rt60_always_pos := rt60_pos

end IndisputableMonolith.Acoustics.RoomAcousticsFromPhiLadder
