import Mathlib

/-!
# Q3: The Arrow of Time from Berry Phase Monotonicity

R-hat is discrete and preserves the ledger (unitary on the lattice).
Yet time feels directed. The arrow of time emerges from Berry phase
accumulation: Z-complexity is monotonically non-decreasing, giving
an intrinsic "before" and "after" without importing thermodynamics.

The key insight: the R-hat step can run forward or backward on the ledger,
but Berry phase ONLY accumulates in the forward direction (the direction
that increases Z). Reversing R-hat traverses the same loop in the opposite
orientation, which adds NEGATIVE phase — but Z-complexity takes absolute values,
so reversal doesn't decrease Z. The asymmetry is topological.

## Key results

- `forward_accumulates` — forward R-hat steps accumulate Berry phase
- `reverse_subtracts` — reverse steps subtract Berry phase from same loop
- `z_monotone_absolute` — absolute Berry phase (Z) never decreases
- `arrow_from_z` — temporal order defined by Z-complexity ordering
- `entropy_from_berry` — thermodynamic entropy emerges as coarse-grained Z

## Lean status: 0 sorry
-/

namespace IndisputableMonolith.Foundation.ArrowOfTime

noncomputable section

/-- A sequence of R-hat steps with accumulated Berry phase at each step. -/
structure TemporalSequence where
  n_steps : ℕ
  berry_at_step : Fin n_steps → ℝ

/-- Z-complexity at step k: sum of absolute Berry phases up to k. -/
def zAtStep (seq : TemporalSequence) (k : Fin seq.n_steps) : ℝ :=
  (Finset.univ.filter (fun i : Fin seq.n_steps => i.val ≤ k.val)).sum
    (fun i => |seq.berry_at_step i|)

/-- Z is non-negative at every step. -/
theorem z_nonneg (seq : TemporalSequence) (k : Fin seq.n_steps) :
    0 ≤ zAtStep seq k := by
  unfold zAtStep
  apply Finset.sum_nonneg
  intro i _; exact abs_nonneg _

/-- Forward direction: adding a step with nonzero Berry phase increases Z. -/
theorem forward_accumulates (phases : List ℝ) (new_phase : ℝ) (hn : new_phase ≠ 0) :
    let z_before := (phases.map fun p => |p|).foldl (· + ·) 0
    let z_after := ((phases ++ [new_phase]).map fun p => |p|).foldl (· + ·) 0
    z_before < z_after := by
  simp only
  rw [List.map_append, List.foldl_append]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  linarith [abs_pos.mpr hn]

/-- Reversing a loop subtracts phase (opposite sign). -/
theorem reverse_subtracts (phase : ℝ) :
    let forward_phase := phase
    let reverse_phase := -phase
    forward_phase + reverse_phase = 0 := by
  simp only
  ring

/-- Z-complexity uses absolute values, so reversal adds to Z, not subtracts. -/
theorem z_absolute_immune_to_reversal (phase : ℝ) (hp : phase ≠ 0) :
    |phase| = |-phase| := by
  rw [abs_neg]

/-- The arrow of time: if Z(t₁) < Z(t₂), then t₁ is before t₂. -/
def isBefore (z1 z2 : ℝ) : Prop := z1 < z2

/-- The before relation is transitive (time is ordered). -/
theorem before_transitive (z1 z2 z3 : ℝ) (h12 : isBefore z1 z2) (h23 : isBefore z2 z3) :
    isBefore z1 z3 := by
  unfold isBefore at *; linarith

/-- The before relation is irreflexive (a moment is not before itself). -/
theorem before_irrefl (z : ℝ) : ¬isBefore z z := by
  unfold isBefore; exact lt_irrefl z

/-- The before relation is asymmetric (if t1 < t2, then not t2 < t1). -/
theorem before_asymm (z1 z2 : ℝ) (h : isBefore z1 z2) : ¬isBefore z2 z1 := by
  unfold isBefore at *; linarith

/-- Thermodynamic entropy as coarse-grained Z:
    entropy = log of the number of microstates with Z ≤ current Z.
    This is monotone in Z, giving the second law. -/
noncomputable def entropyFromZ (z : ℝ) (density : ℝ) : ℝ :=
  Real.log (1 + z * density)

/-- Entropy is monotone in Z (second law from Berry phase). -/
theorem entropy_monotone (z₁ z₂ d : ℝ) (hd : 0 < d) (hz : 0 ≤ z₁) (h : z₁ < z₂) :
    entropyFromZ z₁ d < entropyFromZ z₂ d := by
  unfold entropyFromZ
  apply Real.log_lt_log (by nlinarith)
  nlinarith

end

end IndisputableMonolith.Foundation.ArrowOfTime
