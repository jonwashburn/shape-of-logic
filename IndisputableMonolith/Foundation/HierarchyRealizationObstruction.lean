import Mathlib
import IndisputableMonolith.Foundation.ClosedObservableFramework

namespace IndisputableMonolith
namespace Foundation
namespace HierarchyRealizationObstruction

open ClosedFramework

/-!
# Obstruction: `ClosedObservableFramework` Alone Does Not Force Hierarchy Fields

This module formalizes the key honesty check for the T5→T6 bridge:
the current earlier primitive `ClosedObservableFramework` is too weak
to derive either

* `ratio_self_similar`, or
* `additive_posting`

for the orbit-defined levels `k ↦ r (T^[k] baseState)`.

We exhibit an explicit finite counterexample. This means any honest
derivation must use stronger earlier structure than `ClosedObservableFramework`
alone.
-/

/-- Any map `ℝ → Bool` fails to be injective. -/
theorem no_injective_real_to_bool (embed : ℝ → Bool) :
    ¬ Function.Injective embed := by
  intro h_inj
  by_cases h01 : embed 0 = embed 1
  · exact zero_ne_one (h_inj h01)
  · have hrep : embed 0 = embed 2 ∨ embed 1 = embed 2 := by
      cases h0 : embed 0 <;> cases h1 : embed 1 <;> cases h2 : embed 2 <;> simp_all
    rcases hrep with h02 | h12
    · have : (0 : ℝ) = 2 := h_inj h02
      norm_num at this
    · have : (1 : ℝ) = 2 := h_inj h12
      norm_num at this

/-- A finite closed-observable framework whose orbit alternates between
observable values `1` and `2`. -/
def boolFramework : ClosedObservableFramework where
  S := Bool
  T := not
  r := fun b => if b then 2 else 1
  r_pos := by
    intro b
    cases b <;> norm_num
  nontrivial := by
    refine ⟨false, true, ?_⟩
    norm_num
  S_countable := by
    refine ⟨fun n => if n % 2 = 0 then false else true, ?_⟩
    intro b
    cases b
    · refine ⟨0, ?_⟩
      simp
    · refine ⟨1, ?_⟩
      simp
  no_continuous_moduli := no_injective_real_to_bool
  charge := fun _ => 0
  charge_conserved := by
    intro s
    rfl

/-- The base state used for the obstruction. -/
def baseState : boolFramework.S := false

/-- The orbit-defined levels of the counterexample framework. -/
def orbitLevels (k : ℕ) : ℝ := boolFramework.r (boolFramework.T^[k] baseState)

@[simp] theorem orbitLevels_zero : orbitLevels 0 = 1 := by
  simp [orbitLevels, boolFramework, baseState]

@[simp] theorem orbitLevels_one : orbitLevels 1 = 2 := by
  simp [orbitLevels, boolFramework, baseState]

@[simp] theorem orbitLevels_two : orbitLevels 2 = 1 := by
  simp [orbitLevels, boolFramework, baseState]

/-- The counterexample orbit does not satisfy ratio self-similarity. -/
theorem orbit_not_ratio_self_similar :
    ¬ (∀ k,
      orbitLevels (k + 2) / orbitLevels (k + 1) =
        orbitLevels (k + 1) / orbitLevels k) := by
  intro h
  have h0 := h 0
  simp [orbitLevels, boolFramework, baseState] at h0
  norm_num at h0

/-- The counterexample orbit does not satisfy additive posting. -/
theorem orbit_not_additive_posting :
    ¬ (orbitLevels 2 = orbitLevels 1 + orbitLevels 0) := by
  simp [orbitLevels, boolFramework, baseState]

/-- Therefore `ClosedObservableFramework` alone cannot force
`ratio_self_similar`. -/
theorem closedFramework_does_not_force_ratio_self_similar :
    ∃ (F : ClosedObservableFramework) (base : F.S),
      ¬ (∀ k,
        F.r (F.T^[k + 2] base) / F.r (F.T^[k + 1] base) =
          F.r (F.T^[k + 1] base) / F.r (F.T^[k] base)) := by
  exact ⟨boolFramework, baseState, orbit_not_ratio_self_similar⟩

/-- Therefore `ClosedObservableFramework` alone cannot force
`additive_posting`. -/
theorem closedFramework_does_not_force_additive_posting :
    ∃ (F : ClosedObservableFramework) (base : F.S),
      ¬ (F.r (F.T^[2] base) = F.r (F.T^[1] base) + F.r base) := by
  exact ⟨boolFramework, baseState, orbit_not_additive_posting⟩

/-- Combined obstruction theorem: the earlier primitive layer admits
models where both target fields fail. -/
theorem closedFramework_does_not_force_realizedHierarchy_fields :
    ∃ (F : ClosedObservableFramework) (base : F.S),
      (¬ (∀ k,
        F.r (F.T^[k + 2] base) / F.r (F.T^[k + 1] base) =
          F.r (F.T^[k + 1] base) / F.r (F.T^[k] base))) ∧
      (¬ (F.r (F.T^[2] base) = F.r (F.T^[1] base) + F.r base)) := by
  exact ⟨boolFramework, baseState, orbit_not_ratio_self_similar, orbit_not_additive_posting⟩

end HierarchyRealizationObstruction
end Foundation
end IndisputableMonolith
