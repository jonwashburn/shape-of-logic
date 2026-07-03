import Mathlib

/-!
# Branch Selection: Coupling Combiner Forces the Bilinear Branch

The Logic_FE rigidity theorem produces the Recognition Composition Law
family
\[
F(xy) + F(x/y) = 2 F(x) + 2 F(y) + c\,F(x)F(y)
\]
with combiner `P(u, v) = 2u + 2v + c·u·v` for some `c ∈ ℝ`. Under
calibration, the family splits into a bilinear branch (`c ≠ 0`, with
`α = 1` representative `J(x) = ½(x + x⁻¹) − 1`) and an additive branch
(`c = 0`, with representative `½(ln x)²`). The translation theorem alone
does not select between them.

The companion paper `RS_Branch_Selection.tex` introduces a structural
strengthening of (L4) Composition Consistency: the combiner must be a
**coupling combiner**, not separately additive in its arguments. Since the
RCL polynomial combiner is `P(u,v) = 2u + 2v + c·u·v`, coupling is
equivalent to `c ≠ 0`. Hence the strengthened (L4*) excludes the additive
branch.

This module formalises that argument:

* `IsCouplingCombiner P`: `P` is not separately additive in its arguments.
* `interactionDefect P`: the canonical witness for non-coupling.
* `RCLCombiner c`: the polynomial combiner attached to RCL parameter `c`.
* `RCLCombiner_isCoupling_iff`: the RCL combiner is coupling iff `c ≠ 0`.
* `branch_selection`: under the strengthened (L4*), the bilinear branch
  is forced.

Together with Logic_FE this isolates `J` modulo the residual α-coordinate
freedom acknowledged in §5 of `RS_Branch_Selection.tex`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace BranchSelection

/-! ## Coupling Combiners -/

/-- A combiner `P : ℝ → ℝ → ℝ` is **separately additive** when there
exist single-argument functions `p, q` with `P(u, v) = p(u) + q(v)` for
all `u, v`. This is the structural shape we exclude from genuine
composition consistency. -/
def SeparatelyAdditive (P : ℝ → ℝ → ℝ) : Prop :=
  ∃ p q : ℝ → ℝ, ∀ u v : ℝ, P u v = p u + q v

/-- A combiner is a **coupling combiner** when it is not separately
additive. Equivalently, the joint structure of the two arguments enters
the output; the cost of a composite genuinely depends on how its
components fit together. -/
def IsCouplingCombiner (P : ℝ → ℝ → ℝ) : Prop :=
  ¬ SeparatelyAdditive P

/-- The **interaction defect** of a combiner at a pair `(u, v)`:
\[
\Delta P(u, v) := P(u, v) - P(u, 0) - P(0, v) + P(0, 0).
\]
For a separately additive combiner this is identically zero. The defect
is the canonical detector of coupling. -/
def interactionDefect (P : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  P u v - P u 0 - P 0 v + P 0 0

/-! ## Equivalent Forms -/

/-- A separately additive combiner has identically vanishing interaction
defect. -/
theorem interactionDefect_eq_zero_of_separatelyAdditive
    {P : ℝ → ℝ → ℝ} (h : SeparatelyAdditive P) :
    ∀ u v : ℝ, interactionDefect P u v = 0 := by
  rcases h with ⟨p, q, hP⟩
  intro u v
  unfold interactionDefect
  rw [hP u v, hP u 0, hP 0 v, hP 0 0]
  ring

/-- Conversely: a combiner whose interaction defect is identically zero is
separately additive. The witness functions are `p(u) := P(u, 0) - P(0, 0)`
and `q(v) := P(0, v)`. -/
theorem separatelyAdditive_of_interactionDefect_zero
    {P : ℝ → ℝ → ℝ} (h : ∀ u v : ℝ, interactionDefect P u v = 0) :
    SeparatelyAdditive P := by
  refine ⟨fun u => P u 0 - P 0 0, fun v => P 0 v, ?_⟩
  intro u v
  have h_uv := h u v
  unfold interactionDefect at h_uv
  linarith

/-- **Equivalence: separate additivity is identical vanishing of the
interaction defect.** -/
theorem separatelyAdditive_iff_interactionDefect_zero
    (P : ℝ → ℝ → ℝ) :
    SeparatelyAdditive P ↔ ∀ u v : ℝ, interactionDefect P u v = 0 :=
  ⟨interactionDefect_eq_zero_of_separatelyAdditive,
   separatelyAdditive_of_interactionDefect_zero⟩

/-- **Equivalence: coupling is non-vanishing interaction defect.** -/
theorem isCouplingCombiner_iff_interactionDefect_nonzero
    (P : ℝ → ℝ → ℝ) :
    IsCouplingCombiner P ↔ ∃ u v : ℝ, interactionDefect P u v ≠ 0 := by
  unfold IsCouplingCombiner
  rw [separatelyAdditive_iff_interactionDefect_zero]
  constructor
  · intro h
    by_contra hno
    push_neg at hno
    exact h hno
  · rintro ⟨u, v, huv⟩ hall
    exact huv (hall u v)

/-! ## The RCL Combiner -/

/-- The polynomial combiner attached to the RCL family with parameter
`c`: `P(u, v) = 2u + 2v + c·u·v`. -/
def RCLCombiner (c : ℝ) : ℝ → ℝ → ℝ :=
  fun u v => 2 * u + 2 * v + c * u * v

/-- The interaction defect of the RCL combiner at `(u, v)` is exactly
`c · u · v`. -/
theorem interactionDefect_RCLCombiner (c u v : ℝ) :
    interactionDefect (RCLCombiner c) u v = c * u * v := by
  unfold interactionDefect RCLCombiner
  ring

/-- For `c = 0`, the RCL combiner is the additive combiner
`P(u, v) = 2u + 2v`, separately additive with `p(u) = 2u` and
`q(v) = 2v`. -/
theorem RCLCombiner_zero_separatelyAdditive :
    SeparatelyAdditive (RCLCombiner 0) := by
  refine ⟨fun u => 2 * u, fun v => 2 * v, ?_⟩
  intro u v
  unfold RCLCombiner
  ring

/-- For `c ≠ 0`, the RCL combiner has nonvanishing interaction defect
at the test point `(1, 1)`. -/
theorem RCLCombiner_nonzero_couples (c : ℝ) (hc : c ≠ 0) :
    interactionDefect (RCLCombiner c) 1 1 ≠ 0 := by
  rw [interactionDefect_RCLCombiner]
  simpa using hc

/-- **The RCL combiner is a coupling combiner iff `c ≠ 0`.** -/
theorem RCLCombiner_isCoupling_iff (c : ℝ) :
    IsCouplingCombiner (RCLCombiner c) ↔ c ≠ 0 := by
  rw [isCouplingCombiner_iff_interactionDefect_nonzero]
  constructor
  · rintro ⟨u, v, huv⟩
    intro hc
    apply huv
    rw [interactionDefect_RCLCombiner, hc]
    ring
  · intro hc
    exact ⟨1, 1, RCLCombiner_nonzero_couples c hc⟩

/-! ## Branch Selection Theorem -/

/-- **Branch selection by non-degeneracy.**

If the RCL polynomial combiner is required to be a coupling combiner
(the strengthened (L4*) of the companion paper), then the parameter
`c` is forced to be nonzero. Equivalently, the additive branch
(`c = 0`, with calibrated representative `½(ln x)²`) is excluded.

This is the branch-selection theorem of `RS_Branch_Selection.tex` in
its Lean form. The bilinear branch is forced; `J` is the
`α = 1` representative of the bilinear `α`-family. The residual
`α`-coordinate freedom is acknowledged in §5 of the paper and is
addressed by separate generator-calibration / higher-derivative /
action-functional conditions, none of which are part of the
operator-level Aristotelian content. -/
theorem branch_selection (c : ℝ)
    (hCoupling : IsCouplingCombiner (RCLCombiner c)) :
    c ≠ 0 :=
  (RCLCombiner_isCoupling_iff c).mp hCoupling

/-- The contrapositive: if `c = 0`, the RCL combiner is not coupling. The
additive branch fails the strengthened (L4*). -/
theorem additive_branch_not_coupling :
    ¬ IsCouplingCombiner (RCLCombiner 0) := by
  intro h
  exact branch_selection 0 h rfl

/-! ## Headline Certificate -/

/-- **Branch Selection Certificate.**

The structural strengthening of (L4) — coupling, that is, non-additivity —
forces the bilinear branch within the polynomial RCL family produced by
the translation theorem of `Logic_Functional_Equation.tex`. -/
structure BranchSelectionCert where
  separately_additive_iff_defect_zero :
    ∀ P : ℝ → ℝ → ℝ,
      SeparatelyAdditive P ↔ ∀ u v : ℝ, interactionDefect P u v = 0
  coupling_iff_defect_nonzero :
    ∀ P : ℝ → ℝ → ℝ,
      IsCouplingCombiner P ↔ ∃ u v : ℝ, interactionDefect P u v ≠ 0
  rcl_coupling_iff :
    ∀ c : ℝ, IsCouplingCombiner (RCLCombiner c) ↔ c ≠ 0
  bilinear_branch_forced :
    ∀ c : ℝ, IsCouplingCombiner (RCLCombiner c) → c ≠ 0
  additive_branch_excluded :
    ¬ IsCouplingCombiner (RCLCombiner 0)

def branchSelectionCert : BranchSelectionCert where
  separately_additive_iff_defect_zero :=
    fun P => separatelyAdditive_iff_interactionDefect_zero P
  coupling_iff_defect_nonzero :=
    fun P => isCouplingCombiner_iff_interactionDefect_nonzero P
  rcl_coupling_iff := RCLCombiner_isCoupling_iff
  bilinear_branch_forced := branch_selection
  additive_branch_excluded := additive_branch_not_coupling

theorem branchSelectionCert_inhabited : Nonempty BranchSelectionCert :=
  ⟨branchSelectionCert⟩

end BranchSelection
end Foundation
end IndisputableMonolith
