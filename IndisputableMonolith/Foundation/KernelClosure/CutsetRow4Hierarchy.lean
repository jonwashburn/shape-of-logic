import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetHarness
import IndisputableMonolith.Foundation.KernelClosure.LadderNecessaryReasons

/-!
# Row 4 by cutset: first test, and what it measured

Row 4 of the kernel purchase ledger is the realized hierarchy: a framework whose
orbit levels are positive, grow, have uniform adjacent ratios
(`ratio_self_similar`) and post additively (`additive_posting`). Its countermodel
is `boolFramework`; the two fields are independent (`LadderNecessaryReasons`:
the linear ladder posts additively without uniform ratios, the doubling ladder
has uniform ratios without additive posting).

The plan's first test for this row was: apply blade B1 (the structure steps,
`S ≃ (Fin D → Bool) × S`), and try to read the octave floor tower as the
hierarchy. Both are done here and both results are measured, not argued.

## What B1 does

* `boolFramework_does_not_step`: the countermodel's state space is `Bool`,
  finite, so it has no floor above. B1 kills the census countermodel as a
  ledger. Planted negative: rejected.
* `linearFramework_steps`: the natural numbers step (parity times half), and the
  linear ladder on them violates uniformity. So B1 does **not** kill the class
  of violators of `ratio_self_similar`; it kills only the finite ones.
  `b1_blunt_for_uniformity` is the theorem, and it is the kill condition the
  plan named for this route.

## What the tower reading measures

Reading the octave floor tower as a hierarchy, with the level at floor `k` the
number of positions in the fiber over an item across `k` floors (`itemFiberEquiv`
gives `2^D` per floor, so `8^k` at `D = 3`), the levels have uniform ratio `8`
and do not post additively (`64 ≠ 8 + 1`), and the framework admits no realized
hierarchy at all (`towerCount_no_realized_hierarchy`). The address tower is
self-similar and is not the `φ`-hierarchy: the hierarchy of row 4 is the cost
ladder, whose generation rule (each rung the join of the two below it) is the
whole content of `additive_posting`. The reading of levels as fiber counts is
a MODEL and is named as such.

## Verdict

Row 4 stays `purchase`. What the first test bought: the countermodel is not a
ledger (B1); B1 is too blunt for the uniformity field, which needs a blade that
says what it is for an observable to read a floor; the additive field is the
generation rule of the cost ladder and is not in the address tower. The
residual is named exactly: (4a) a "reads a floor" blade for uniformity; (4b)
the adjacent-join generation rule for additivity.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row4Hierarchy

open ClosedFramework HierarchyRealization LadderCensus HierarchyRealizationObstruction

noncomputable section

/-! ## B1 on the countermodel -/

/-- The census countermodel has no floor above: its state space is finite. -/
theorem boolFramework_does_not_step {D : ℕ} (hD : 0 < D) : ¬ Steps boolFramework.S D := by
  show ¬ Steps Bool D
  exact finite_does_not_step Bool hD

/-! ## B1 on an infinite violator -/

/-- The natural numbers step: parity times half. -/
def natStep : ℕ ≃ (Fin 1 → Bool) × ℕ where
  toFun n := (fun _ => decide (n % 2 = 1), n / 2)
  invFun q := 2 * q.2 + (if q.1 0 then 1 else 0)
  left_inv n := by
    simp only [decide_eq_true_eq]
    split_ifs <;> omega
  right_inv q := by
    rcases q with ⟨p, m⟩
    simp only [Prod.mk.injEq]
    constructor
    · funext i
      rw [Fin.fin_one_eq_zero i]
      rcases Bool.eq_false_or_eq_true (p 0) with hp | hp <;> simp [hp]
    · split_ifs <;> omega

theorem linearFramework_steps : Steps linearFramework.S 1 := by
  show Steps ℕ 1
  exact ⟨natStep⟩

/-- **B1 is blunt for uniformity.** A framework that steps can still violate
`ratio_self_similar`. -/
theorem b1_blunt_for_uniformity :
    ∃ (F : ClosedObservableFramework) (base : F.S), Steps F.S 1 ∧ ¬ OrbitUniform F base :=
  ⟨linearFramework, linearBase, linearFramework_steps, linearFramework_not_uniform⟩

/-! ## The tower reading -/

/-- The octave tower read as a ladder: the level at floor `k` is the number of
positions in the fiber over an item across `k` floors, `8^k` at `D = 3`. A
reading (MODEL), stated so it can be measured. -/
def towerCountFramework : ClosedObservableFramework :=
  natFramework (fun n => (8 : ℝ) ^ n) (fun n => by positivity) ⟨0, 1, by norm_num⟩

def towerCountBase : towerCountFramework.S :=
  natBase (fun n => (8 : ℝ) ^ n) (fun n => by positivity) ⟨0, 1, by norm_num⟩

theorem towerCount_uniform : OrbitUniform towerCountFramework towerCountBase := by
  intro k
  unfold towerCountFramework towerCountBase
  rw [natFramework_levels, natFramework_levels, natFramework_levels]
  have h1 : (8 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  have h2 : (8 : ℝ) ^ k ≠ 0 := by positivity
  rw [div_eq_div_iff h1 h2]
  ring

theorem towerCount_not_additive : ¬ OrbitAdditive towerCountFramework towerCountBase := by
  unfold OrbitAdditive towerCountFramework towerCountBase
  rw [natFramework_levels, natFramework_levels, natFramework_levels]
  norm_num

theorem natFramework_iterate_base (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hnt : ∃ a b, r a ≠ r b)
    (b k : ℕ) : (natFramework r hr hnt).T^[k] b = b + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl

/-- **The tower is not the hierarchy.** From any base, the fiber-count levels
fail additive posting, so no realized hierarchy lives on this reading. -/
theorem towerCount_no_realized_hierarchy : IsEmpty (RealizedHierarchy towerCountFramework) := by
  refine ⟨fun H => ?_⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, H.baseState = b := ⟨H.baseState, rfl⟩
  have h := H.additive_posting
  rw [H.levels_eq, H.levels_eq, H.levels_eq, hb] at h
  have h' : (8 : ℝ) ^ (b + 2) = (8 : ℝ) ^ (b + 1) + (8 : ℝ) ^ (b + 0) := by
    have e := h
    unfold towerCountFramework at e
    rw [natFramework_iterate_base, natFramework_iterate_base, natFramework_iterate_base] at e
    exact e
  have hx : (0 : ℝ) < (8 : ℝ) ^ b := by positivity
  have e2 : (8 : ℝ) ^ (b + 2) = 64 * (8 : ℝ) ^ b := by ring
  have e1 : (8 : ℝ) ^ (b + 1) = 8 * (8 : ℝ) ^ b := by ring
  have e0 : (8 : ℝ) ^ (b + 0) = (8 : ℝ) ^ b := by ring
  rw [e2, e1, e0] at h'
  linarith

end

/-! ## Certificate -/

structure Cert : Prop where
  bool_no_floor_above : ∀ {D : ℕ}, 0 < D → ¬ Steps boolFramework.S D
  linear_steps : Steps linearFramework.S 1
  b1_blunt : ∃ (F : ClosedObservableFramework) (base : F.S), Steps F.S 1 ∧ ¬ OrbitUniform F base
  tower_uniform : OrbitUniform towerCountFramework towerCountBase
  tower_not_additive : ¬ OrbitAdditive towerCountFramework towerCountBase
  tower_not_hierarchy : IsEmpty (RealizedHierarchy towerCountFramework)

theorem cert : Cert where
  bool_no_floor_above := fun hD => boolFramework_does_not_step hD
  linear_steps := linearFramework_steps
  b1_blunt := b1_blunt_for_uniformity
  tower_uniform := towerCount_uniform
  tower_not_additive := towerCount_not_additive
  tower_not_hierarchy := towerCount_no_realized_hierarchy

end Row4Hierarchy
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
