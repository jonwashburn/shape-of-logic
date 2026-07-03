import Mathlib

/-!
Shims for countability and equivalence constructions that are convenient
for Lean 4 developments.

Provides:
- `enumOfCountable` to get a surjection `ℕ → α` from `Countable α`.
- `countable_of_surjective` to obtain `Countable α` from a surjection `ℕ → α`.

## Implementation Notes

mathlib's `Countable` API is stable but indirect (works via `Encodable` or injections).
For clarity and to avoid version coupling, we provide clean constructive proofs here.
-/

open Classical
open Function

namespace Shims

universe u

/-! ### Countability from surjection (fully proven) -/

theorem countable_of_surjective {α : Type u} (f : ℕ → α) (hf : Surjective f) : Countable α := by
  -- Build an injection α → ℕ from the surjection
  classical
  let g : α → ℕ := fun a => Nat.find (hf a)
  have hg : ∀ a, f (g a) = a := fun a => Nat.find_spec (hf a)
  -- g is a left inverse, hence injective
  have hinj : Injective g := by
    intro a₁ a₂ heq
    calc a₁ = f (g a₁) := (hg a₁).symm
      _ = f (g a₂) := by rw [heq]
      _ = a₂ := hg a₂
  -- Use mathlib's Countable constructor (exists in Lean 4)
  exact ⟨g, hinj⟩

/-! ### Enumeration from countability -/

/-- From `Countable α` and inhabitedness, produce a surjection `ℕ → α`.

**Proof strategy**: Use `Nonempty.some` to extract the injection witness from `Countable`,
then invert it classically to build a surjection.

The challenge is that `Countable α := ∃ f, Injective f` is in `Prop`, but we need
to use the witness `f` in a `Type`-producing definition. We use `Nonempty` coercion. -/
noncomputable def enumOfCountable {α : Type u} [Inhabited α] (h : Countable α) : ℕ → α :=
  -- Convert existence proof to Nonempty, then extract witness
  let f_witness : Nonempty (∃ f : α → ℕ, Injective f) := ⟨h.exists_injective_nat⟩
  let f_data := Classical.choice f_witness
  let f := f_data.choose
  -- Build surjection by choosing preimages
  fun n => if h : ∃ a, f a = n then Classical.choose h else default

theorem enumOfCountable_surjective {α : Type u} [Inhabited α] (h : Countable α) :
    Function.Surjective (enumOfCountable h) := by
  intro a
  classical
  -- Extract the injection
  let f_witness : Nonempty (∃ f : α → ℕ, Injective f) := ⟨h.exists_injective_nat⟩
  let f_data := Classical.choice f_witness
  let f := f_data.choose
  let hinj := f_data.choose_spec
  -- f a is in the range, so enumOfCountable (f a) = a
  use f a
  simp [enumOfCountable]
  have hex : ∃ a', f a' = f a := ⟨a, rfl⟩
  rw [dif_pos hex]
  have hchoose := Classical.choose_spec hex
  exact hinj hchoose

end Shims
