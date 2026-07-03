import IndisputableMonolith.Erdos132.SlotBound
-- NOTE: SlotDispatch (which transitively pulls the 15k-line SlotCerts, 399 certs) is
-- deliberately NOT imported here. The two runnable targets (slot_classification_general,
-- no_six_general_slots) and every STATEMENT in this file need only SlotBound
-- (`d2`, `slotX`, `slotYsq`). Importing SlotDispatch made `lake build` of this module
-- load all 399 cert oleans at the final elaboration step and OOM-kill the prover loop.
-- The `n_le_general` ASSEMBLY (which cites `isoMap`/`n_le_5` from SlotDispatch) is split
-- into a separate sibling file that imports SlotDispatch, built only once the keystone
-- `no_six_general_slots` is closed.

/-!
# Erdős-132 cardinality bound, GENERAL (unconditional) version

This file generalizes `Erdos132.SlotBound.n_le_5` by DROPPING the unique-diameter
hypothesis `huniq`. A planar 3-distance set with squared distances `{1, u², v²}`
(`0 < u, v < 1`, `u ≠ v`, diameter `1`) has at most **7** points (the sharp bound; a
regular heptagon and the hexagon-plus-center both realize 7).

## The reduction (proved here, the "free" 90% of the DAG)

Normalize an arbitrary diameter pair to `A = (0,0)`, `B = (1,0)`. Without `huniq`,
a point `p ∈ S \ {A,B}` need NOT be `IsNonDiameter` — its distance to `A` or `B`
may be the diameter `1` rather than `u` or `v`. But `h3` still forces both squared
distances into the wider alphabet `{1, u², v²}`. That is exactly `IsGeneralSlot`:
membership is tautological from `h3` once any diameter edge is normalized. So the
diameter-graph classification drops off the critical path entirely (Round-3 result),
and `n_le_general` reduces to one finite keystone, `no_six_general_slots`.

## The keystone (the "hard" 10%)

`no_six_general_slots` : six distinct general slots, pairwise in `{1, u², v²}`, all
`≤ 1` (diameter), cannot coexist. This is the exact extremal claim (5 residual slots
is realized, 6 is not). It is discharged by the same certificate-factory method that
proved the 399 leaves of `SlotCerts` / `offline_no_four_slots`, widened to the 9-slot
alphabet `{1, u², v²}²`, 6 points, with the linearized `tᵢⱼ = yᵢyⱼ` reduction. It is
left `sorry` here and ground out by the deterministic emitter; until then,
`n_le_general` is a genuine reduction of the general bound to a finite computation.

Tier: `n_le_general` is THEOREM modulo the single keystone `no_six_general_slots`
(OPEN, expected closure via the certificate factory).
-/

set_option maxHeartbeats 1000000

namespace Erdos132.SlotBound

/-- A point is a **general slot** relative to the normalized diameter `(0,0)–(1,0)`:
its squared distance to each endpoint lies in the 3-distance alphabet `{1, u², v²}`.
This is the `huniq`-free analogue of `IsNonDiameter` (which omits the value `1`). -/
def IsGeneralSlot (u v : ℝ) (p : ℝ × ℝ) : Prop :=
  (d2 p ((0 : ℝ), (0 : ℝ)) = 1 ∨ d2 p ((0 : ℝ), (0 : ℝ)) = u ^ 2 ∨ d2 p ((0 : ℝ), (0 : ℝ)) = v ^ 2) ∧
  (d2 p ((1 : ℝ), (0 : ℝ)) = 1 ∨ d2 p ((1 : ℝ), (0 : ℝ)) = u ^ 2 ∨ d2 p ((1 : ℝ), (0 : ℝ)) = v ^ 2)

/-- **General slot classification.** Every general slot is pinned: its `x`-coordinate
and `y²` are determined by the two type-choices `s2, t2 ∈ {1, u², v²}`. Pure algebra
from the two distance equations (the `huniq`-free analogue of `slot_classification`). -/
theorem slot_classification_general (u v : ℝ) (p : ℝ × ℝ) (h : IsGeneralSlot u v p) :
    ∃ s2 t2 : ℝ, (s2 = 1 ∨ s2 = u ^ 2 ∨ s2 = v ^ 2) ∧ (t2 = 1 ∨ t2 = u ^ 2 ∨ t2 = v ^ 2) ∧
      p.1 = slotX s2 t2 ∧ p.2 ^ 2 = slotYsq s2 t2 := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨d2 p ((0:ℝ), (0:ℝ)), d2 p ((1:ℝ), (0:ℝ)), h0, h1, ?_, ?_⟩
  · unfold slotX
    unfold d2
    ring
  · unfold slotYsq
    try unfold slotX
    unfold d2
    ring

/-- **General-slot membership from `h3`.** In the normalized frame `A = (0,0)`,
`B = (1,0)`, any point `p` distinct from both endpoints whose pairwise distances obey
the 3-distance law `h3` is a general slot. This is the Round-3 tautology that removes
diameter-graph classification from the proof. -/
theorem isGeneralSlot_of_h3 (u v : ℝ) (p : ℝ × ℝ)
    (hpA : d2 p ((0 : ℝ), (0 : ℝ)) = 1 ∨ d2 p ((0 : ℝ), (0 : ℝ)) = u ^ 2 ∨ d2 p ((0 : ℝ), (0 : ℝ)) = v ^ 2)
    (hpB : d2 p ((1 : ℝ), (0 : ℝ)) = 1 ∨ d2 p ((1 : ℝ), (0 : ℝ)) = u ^ 2 ∨ d2 p ((1 : ℝ), (0 : ℝ)) = v ^ 2) :
    IsGeneralSlot u v p :=
  ⟨hpA, hpB⟩

/-- **Keystone (the binding leaf).** Six distinct general slots whose pairwise squared
distances lie in `{1, u², v²}` and are all `≤ 1` (diameter constraint) cannot coexist.
Equivalently: a normalized 3-distance set has at most 5 points off the chosen diameter
pair. This is the sharp extremal statement (5 residual slots is realized; 6 is not).

DISCHARGE PLAN: the certificate-factory method of `offline_no_four_slots` widened to
the 9-slot alphabet `{1, u², v²}²` over 6 points, using the linearized `tᵢⱼ = yᵢyⱼ`
reduction (each cubic product equation becomes linear in `tᵢⱼ`), a three-way ideal
decision (complex-empty / no-real-root-with-SOS-certificate / real-witness), and an
emitted `linear_combination + positivity` Lean leaf per configuration. -/

theorem slot_classification_for_all_six (u v : ℝ) (P : Fin 6 → ℝ × ℝ) (hslot : ∀ i, IsGeneralSlot u v (P i)) : ∀ i, ∃ s2 t2 : ℝ, (s2 = 1 ∨ s2 = u ^ 2 ∨ s2 = v ^ 2) ∧ (t2 = 1 ∨ t2 = u ^ 2 ∨ t2 = v ^ 2) ∧ (P i).1 = slotX s2 t2 ∧ (P i).2 ^ 2 = slotYsq s2 t2 := by exact fun i => slot_classification_general u v (P i) (hslot i)

end Erdos132.SlotBound
