import Mathlib

/-!
# L1b Chamber Bridge

Signed-sort chamber coverage for the finite-to-boundary push-forward.

The boundary `∂Q³` is tiled by the `48` signed-permutation images of one
fundamental chamber (the closed ascending nonnegative cone). This file proves the
combinatorial core of that tiling: every real `3`-vector lies in the closure of
some `B3 = Equiv.Perm (Fin 3) × (Fin 3 → Bool)` image of the fundamental cone, and
on regular points (distinct, nonzero coordinates) the carrying signed permutation
is forced to be the signed sort.

It proves only the combinatorial coverage/uniqueness. The spherical-measure step
(`area(cone) = 4π/48`) is a separate geometric bridge and is not closed here.
-/

namespace IndisputableMonolith
namespace Masses
namespace L1bChamberBridge

noncomputable section

/-- `B3 = signed permutations of three coordinates` (the same carrier as
`L1b3Q3FlagCarrier.B3`, here acting geometrically on real vectors). -/
abbrev B3 : Type := Equiv.Perm (Fin 3) × (Fin 3 → Bool)

/--
Geometric action of a signed permutation on a real `3`-vector: read coordinate `i`
from axis `g.1 i`, flipping its sign when `g.2 i` is `true`.
-/
def signedAct (g : B3) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => if g.2 i then -(v (g.1 i)) else v (g.1 i)

/-- The fundamental chamber: the closed ascending nonnegative cone. -/
def cone : Set (Fin 3 → ℝ) :=
  {v | 0 ≤ v 0 ∧ v 0 ≤ v 1 ∧ v 1 ≤ v 2}

/--
The sign-bit choice `decide (v (σ j) < 0)` makes `signedAct (σ, ·) v` equal to the
absolute values read along `σ`.
-/
theorem signedAct_abs (v : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    signedAct (σ, fun j => decide (v (σ j) < 0)) v i = |v (σ i)| := by
  simp only [signedAct]
  by_cases h : v (σ i) < 0
  · simp [h, abs_of_neg h]
  · have hnn : 0 ≤ v (σ i) := le_of_not_gt h
    simp [h, abs_of_nonneg hnn]

/--
**Signed-sort chamber coverage.** Every real `3`-vector is carried into the
fundamental cone by some signed permutation: take absolute values (sign flips)
then sort ascending (`Tuple.sort`).
-/
theorem exists_signedPerm_mem_cone (v : Fin 3 → ℝ) :
    ∃ g : B3, signedAct g v ∈ cone := by
  set w : Fin 3 → ℝ := fun j => |v j| with hw
  set σ : Equiv.Perm (Fin 3) := Tuple.sort w with hσ
  refine ⟨(σ, fun j => decide (v (σ j) < 0)), ?_⟩
  have hact : signedAct (σ, fun j => decide (v (σ j) < 0)) v = fun i => w (σ i) := by
    funext i
    rw [signedAct_abs]
  have hmono : Monotone (w ∘ σ) := Tuple.monotone_sort w
  simp only [cone, Set.mem_setOf_eq, hact]
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ |v (σ 0)|
    exact abs_nonneg _
  · exact hmono (by decide : (0 : Fin 3) ≤ 1)
  · exact hmono (by decide : (1 : Fin 3) ≤ 2)

/--
**Signed-sort permutation uniqueness.** On a regular point (distinct absolute
values, encoded as `w := |v ·|` being injective) the monotone-rearranging
permutation is forced: any two permutations that sort `w` ascending coincide.
This is the uniqueness half of the `48`-fold tiling on regular points.
-/
theorem signedSort_perm_unique (w : Fin 3 → ℝ) (hw : Function.Injective w)
    {σ τ : Equiv.Perm (Fin 3)}
    (hσ : Monotone (w ∘ σ)) (hτ : Monotone (w ∘ τ)) : σ = τ := by
  have h1 : w ∘ σ = w ∘ (Tuple.sort w) :=
    (Tuple.comp_sort_eq_comp_iff_monotone).mpr hσ
  have h2 : w ∘ τ = w ∘ (Tuple.sort w) :=
    (Tuple.comp_sort_eq_comp_iff_monotone).mpr hτ
  have heq : w ∘ σ = w ∘ τ := h1.trans h2.symm
  apply Equiv.ext
  intro i
  exact hw (congrFun heq i)

end

end L1bChamberBridge
end Masses
end IndisputableMonolith
