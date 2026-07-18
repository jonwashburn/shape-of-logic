import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Push
import IndisputableMonolith.Gravity.Analysis.ReggeTTContinuumCertificateSpike

/-!
# Regge TT Gate B bridge core (leaf algebra module for Gate C-B)

Support module for `ReggeTTGateBBridge` (Gate C-B of the Lane C
finishing charter).  This file carries the HEAVY polynomial algebra of
the spike convention bridge in a LEAF import context: it imports ONLY
the committed spike transcription (which itself imports only basic real
arithmetic and the `ring`/`linear_combination` tactics), because the
full symbol-program import chain plus a 216-term `ring` normalization
exceeds the laptop build memory guard when combined in one file.

Everything here is defined over literal tables and scalars:

* `coreWeight`: the literal rational raw-coefficient table (the same 36
  values the independent `rationalStencilWeight` table of Gate C-A2f
  carries; the MAIN module kernel-identifies this table with the actual
  `rawJacobianCoefficient` through the Gate C-A2f theorem, so no
  transcription is trusted).
* `slotDispCore`: the literal slot displacement-class table (the main
  module grounds it against the actual periodic geometry).
* `slotMidTwice`: the literal doubled-midpoint table (the main module
  grounds it against the actual `edgeMidpointPhase`).
* `corePolEdgeCoeff`: the literal seven edge-class linear forms (the
  main module kernel-identifies them with the actual `polEdgeCoeff`).
* `coreTripleTerm`: one signed raw moment term
  `-(phase^2)/2 * -(w_fg * c_f * c_g)`.

`coreTripleSum_eq_spikeSum` is the core identity: the 216-term raw
moment sum equals `tetBlock0 + ... + tetBlock5` with COMPLETELY FREE
`s2 s3 p`, identically in `E` and `x`.  The spike blocks enter as data
only; `tt_continuum_certificate` is never used.

Expected axiom footprint: standard trio.  No `sorry`, no `admit`, no
new axioms, no `native_decide`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTGateBBridgeCore

open ReggeTTContinuumCertificateSpike

noncomputable section

set_option maxHeartbeats 3200000

/-- Literal rational raw-coefficient table (see Gate C-A2f for the
kernel identification with `rawJacobianCoefficient`). -/
def coreWeight : Fin 6 → Fin 6 → ℝ
  | 0, 0 => 0        | 0, 1 => 0        | 0, 2 => 0
  | 0, 3 => 0        | 0, 4 => -(1 / 8) | 0, 5 => 1 / 4
  | 1, 0 => 0        | 1, 1 => 1 / 8    | 1, 2 => -(1 / 8)
  | 1, 3 => -(1 / 4) | 1, 4 => 1 / 4    | 1, 5 => -(1 / 8)
  | 2, 0 => 0        | 2, 1 => -(1 / 8) | 2, 2 => 1 / 12
  | 2, 3 => 1 / 4    | 2, 4 => -(1 / 8) | 2, 5 => 0
  | 3, 0 => 0        | 3, 1 => -(1 / 4) | 3, 2 => 1 / 4
  | 3, 3 => 1 / 4    | 3, 4 => -(1 / 4) | 3, 5 => 0
  | 4, 0 => -(1 / 8) | 4, 1 => 1 / 4    | 4, 2 => -(1 / 8)
  | 4, 3 => -(1 / 4) | 4, 4 => 1 / 8    | 4, 5 => 0
  | 5, 0 => 1 / 4    | 5, 1 => -(1 / 8) | 5, 2 => 0
  | 5, 3 => 0        | 5, 4 => 0        | 5, 5 => 0

/-- Literal slot displacement-class table. -/
def slotDispCore : Fin 6 → Fin 6 → Fin 7
  | 0, 0 => 0 | 0, 1 => 3 | 0, 2 => 6 | 0, 3 => 1 | 0, 4 => 5 | 0, 5 => 2
  | 1, 0 => 0 | 1, 1 => 4 | 1, 2 => 6 | 1, 3 => 2 | 1, 4 => 5 | 1, 5 => 1
  | 2, 0 => 1 | 2, 1 => 3 | 2, 2 => 6 | 2, 3 => 0 | 2, 4 => 4 | 2, 5 => 2
  | 3, 0 => 1 | 3, 1 => 5 | 3, 2 => 6 | 3, 3 => 2 | 3, 4 => 4 | 3, 5 => 0
  | 4, 0 => 2 | 4, 1 => 4 | 4, 2 => 6 | 4, 3 => 0 | 4, 4 => 3 | 4, 5 => 1
  | 5, 0 => 2 | 5, 1 => 5 | 5, 2 => 6 | 5, 3 => 1 | 5, 4 => 3 | 5, 5 => 0

/-- Literal doubled-midpoint table (`2 * (base offset + displacement/2)`
per coordinate). -/
def slotMidTwice : Fin 6 → Fin 6 → Fin 3 → ℤ
  | 0, 0, 0 => 1 | 0, 0, 1 => 0 | 0, 0, 2 => 0
  | 0, 1, 0 => 1 | 0, 1, 1 => 1 | 0, 1, 2 => 0
  | 0, 2, 0 => 1 | 0, 2, 1 => 1 | 0, 2, 2 => 1
  | 0, 3, 0 => 2 | 0, 3, 1 => 1 | 0, 3, 2 => 0
  | 0, 4, 0 => 2 | 0, 4, 1 => 1 | 0, 4, 2 => 1
  | 0, 5, 0 => 2 | 0, 5, 1 => 2 | 0, 5, 2 => 1
  | 1, 0, 0 => 1 | 1, 0, 1 => 0 | 1, 0, 2 => 0
  | 1, 1, 0 => 1 | 1, 1, 1 => 0 | 1, 1, 2 => 1
  | 1, 2, 0 => 1 | 1, 2, 1 => 1 | 1, 2, 2 => 1
  | 1, 3, 0 => 2 | 1, 3, 1 => 0 | 1, 3, 2 => 1
  | 1, 4, 0 => 2 | 1, 4, 1 => 1 | 1, 4, 2 => 1
  | 1, 5, 0 => 2 | 1, 5, 1 => 1 | 1, 5, 2 => 2
  | 2, 0, 0 => 0 | 2, 0, 1 => 1 | 2, 0, 2 => 0
  | 2, 1, 0 => 1 | 2, 1, 1 => 1 | 2, 1, 2 => 0
  | 2, 2, 0 => 1 | 2, 2, 1 => 1 | 2, 2, 2 => 1
  | 2, 3, 0 => 1 | 2, 3, 1 => 2 | 2, 3, 2 => 0
  | 2, 4, 0 => 1 | 2, 4, 1 => 2 | 2, 4, 2 => 1
  | 2, 5, 0 => 2 | 2, 5, 1 => 2 | 2, 5, 2 => 1
  | 3, 0, 0 => 0 | 3, 0, 1 => 1 | 3, 0, 2 => 0
  | 3, 1, 0 => 0 | 3, 1, 1 => 1 | 3, 1, 2 => 1
  | 3, 2, 0 => 1 | 3, 2, 1 => 1 | 3, 2, 2 => 1
  | 3, 3, 0 => 0 | 3, 3, 1 => 2 | 3, 3, 2 => 1
  | 3, 4, 0 => 1 | 3, 4, 1 => 2 | 3, 4, 2 => 1
  | 3, 5, 0 => 1 | 3, 5, 1 => 2 | 3, 5, 2 => 2
  | 4, 0, 0 => 0 | 4, 0, 1 => 0 | 4, 0, 2 => 1
  | 4, 1, 0 => 1 | 4, 1, 1 => 0 | 4, 1, 2 => 1
  | 4, 2, 0 => 1 | 4, 2, 1 => 1 | 4, 2, 2 => 1
  | 4, 3, 0 => 1 | 4, 3, 1 => 0 | 4, 3, 2 => 2
  | 4, 4, 0 => 1 | 4, 4, 1 => 1 | 4, 4, 2 => 2
  | 4, 5, 0 => 2 | 4, 5, 1 => 1 | 4, 5, 2 => 2
  | 5, 0, 0 => 0 | 5, 0, 1 => 0 | 5, 0, 2 => 1
  | 5, 1, 0 => 0 | 5, 1, 1 => 1 | 5, 1, 2 => 1
  | 5, 2, 0 => 1 | 5, 2, 1 => 1 | 5, 2, 2 => 1
  | 5, 3, 0 => 0 | 5, 3, 1 => 1 | 5, 3, 2 => 2
  | 5, 4, 0 => 1 | 5, 4, 1 => 1 | 5, 4, 2 => 2
  | 5, 5, 0 => 1 | 5, 5, 1 => 2 | 5, 5, 2 => 2

/-- Literal edge-class linear forms (`c_d = sum_ij E_ij D_d^i D_d^j`). -/
def corePolEdgeCoeff (E : Fin 3 → Fin 3 → ℝ) : Fin 7 → ℝ
  | 0 => E 0 0
  | 1 => E 1 1
  | 2 => E 2 2
  | 3 => E 0 0 + E 0 1 + E 1 0 + E 1 1
  | 4 => E 0 0 + E 0 2 + E 2 0 + E 2 2
  | 5 => E 1 1 + E 1 2 + E 2 1 + E 2 2
  | 6 => E 0 0 + E 0 1 + E 0 2 + E 1 0 + E 1 1 + E 1 2 + E 2 0 + E 2 1 + E 2 2

/-- One signed raw moment term of triple `q = (t, f, g)`:
`-(midpoint phase)^2/2 * -(w_fg * c_{d(t,f)} * c_{d(t,g)})`. -/
def coreTripleTerm (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (q : Fin 6 × Fin 6 × Fin 6) : ℝ :=
  -((∑ i : Fin 3,
      x i * (((slotMidTwice q.1 q.2.2 i - slotMidTwice q.1 q.2.1 i : ℤ) : ℝ) /
        2)) ^ 2) / 2 *
    -(coreWeight q.2.1 q.2.2 *
      corePolEdgeCoeff E (slotDispCore q.1 q.2.1) *
      corePolEdgeCoeff E (slotDispCore q.1 q.2.2))

private theorem coreBlock0_eq (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (s2 s3 p : ℝ) :
    (∑ f : Fin 6, ∑ g : Fin 6, coreTripleTerm E x (0, f, g)) =
      tetBlock0 (E 0 0) (E 0 1) (E 0 2) (E 1 0) (E 1 1) (E 1 2)
        (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2) s2 s3 p := by
  rw [tetBlock0_eq]
  simp only [Fin.sum_univ_six, coreTripleTerm, coreWeight,
    corePolEdgeCoeff, slotDispCore, slotMidTwice, Fin.sum_univ_three]
  push_cast
  ring

private theorem coreBlock1_eq (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (s2 s3 p : ℝ) :
    (∑ f : Fin 6, ∑ g : Fin 6, coreTripleTerm E x (1, f, g)) =
      tetBlock1 (E 0 0) (E 0 1) (E 0 2) (E 1 0) (E 1 1) (E 1 2)
        (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2) s2 s3 p := by
  rw [tetBlock1_eq]
  simp only [Fin.sum_univ_six, coreTripleTerm, coreWeight,
    corePolEdgeCoeff, slotDispCore, slotMidTwice, Fin.sum_univ_three]
  push_cast
  ring

private theorem coreBlock2_eq (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (s2 s3 p : ℝ) :
    (∑ f : Fin 6, ∑ g : Fin 6, coreTripleTerm E x (2, f, g)) =
      tetBlock2 (E 0 0) (E 0 1) (E 0 2) (E 1 0) (E 1 1) (E 1 2)
        (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2) s2 s3 p := by
  rw [tetBlock2_eq]
  simp only [Fin.sum_univ_six, coreTripleTerm, coreWeight,
    corePolEdgeCoeff, slotDispCore, slotMidTwice, Fin.sum_univ_three]
  push_cast
  ring

private theorem coreBlock3_eq (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (s2 s3 p : ℝ) :
    (∑ f : Fin 6, ∑ g : Fin 6, coreTripleTerm E x (3, f, g)) =
      tetBlock3 (E 0 0) (E 0 1) (E 0 2) (E 1 0) (E 1 1) (E 1 2)
        (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2) s2 s3 p := by
  rw [tetBlock3_eq]
  simp only [Fin.sum_univ_six, coreTripleTerm, coreWeight,
    corePolEdgeCoeff, slotDispCore, slotMidTwice, Fin.sum_univ_three]
  push_cast
  ring

private theorem coreBlock4_eq (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (s2 s3 p : ℝ) :
    (∑ f : Fin 6, ∑ g : Fin 6, coreTripleTerm E x (4, f, g)) =
      tetBlock4 (E 0 0) (E 0 1) (E 0 2) (E 1 0) (E 1 1) (E 1 2)
        (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2) s2 s3 p := by
  rw [tetBlock4_eq]
  simp only [Fin.sum_univ_six, coreTripleTerm, coreWeight,
    corePolEdgeCoeff, slotDispCore, slotMidTwice, Fin.sum_univ_three]
  push_cast
  ring

private theorem coreBlock5_eq (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (s2 s3 p : ℝ) :
    (∑ f : Fin 6, ∑ g : Fin 6, coreTripleTerm E x (5, f, g)) =
      tetBlock5 (E 0 0) (E 0 1) (E 0 2) (E 1 0) (E 1 1) (E 1 2)
        (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2) s2 s3 p := by
  rw [tetBlock5_eq]
  simp only [Fin.sum_univ_six, coreTripleTerm, coreWeight,
    corePolEdgeCoeff, slotDispCore, slotMidTwice, Fin.sum_univ_three]
  push_cast
  ring

/-- THE CORE IDENTITY (THEOREM): the 216-term raw moment sum equals the
sum of the six committed spike blocks, for COMPLETELY FREE `s2 s3 p` and
IDENTICALLY in `E` and `x`.  Only the block data is used; the spike's TT
conclusion is never invoked. -/
theorem coreTripleSum_eq_spikeSum (E : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) (s2 s3 p : ℝ) :
    (∑ q : Fin 6 × Fin 6 × Fin 6, coreTripleTerm E x q) =
      tetBlock0 (E 0 0) (E 0 1) (E 0 2) (E 1 0) (E 1 1) (E 1 2)
          (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2) s2 s3 p
        + tetBlock1 (E 0 0) (E 0 1) (E 0 2) (E 1 0) (E 1 1) (E 1 2)
          (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2) s2 s3 p
        + tetBlock2 (E 0 0) (E 0 1) (E 0 2) (E 1 0) (E 1 1) (E 1 2)
          (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2) s2 s3 p
        + tetBlock3 (E 0 0) (E 0 1) (E 0 2) (E 1 0) (E 1 1) (E 1 2)
          (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2) s2 s3 p
        + tetBlock4 (E 0 0) (E 0 1) (E 0 2) (E 1 0) (E 1 1) (E 1 2)
          (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2) s2 s3 p
        + tetBlock5 (E 0 0) (E 0 1) (E 0 2) (E 1 0) (E 1 1) (E 1 2)
          (E 2 0) (E 2 1) (E 2 2) (x 0) (x 1) (x 2) s2 s3 p := by
  simp only [Fintype.sum_prod_type]
  rw [Fin.sum_univ_six]
  rw [coreBlock0_eq E x s2 s3 p, coreBlock1_eq E x s2 s3 p,
    coreBlock2_eq E x s2 s3 p, coreBlock3_eq E x s2 s3 p,
    coreBlock4_eq E x s2 s3 p, coreBlock5_eq E x s2 s3 p]

end

end ReggeTTGateBBridgeCore
end Analysis
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTGateBBridgeCore.coreTripleSum_eq_spikeSum
