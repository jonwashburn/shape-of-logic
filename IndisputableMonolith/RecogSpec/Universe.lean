import Mathlib

/-!
Universe helpers and shims for RecogSpec types.

This file provides small bridges for universe alignment and for interfacing
`Sort u` carriers with APIs that expect `Type u`.
-/

namespace RecogSpec

universe u

/-!
`CarrierType` and `carrierEquiv` present a canonical way to use `Type u`
when an external API requires it, starting from an arbitrary `Sort u` carrier.
-/

structure CarrierWrap (α : Sort u) : Type u where
  val : α

abbrev CarrierType (α : Sort u) : Type u := CarrierWrap α

@[simp] def carrierEquiv (α : Sort u) : α ≃ CarrierType α :=
{ toFun := fun a => ⟨a⟩,
  invFun := fun w => w.val,
  left_inv := by intro a; rfl,
  right_inv := by intro w; cases w; rfl }

end RecogSpec
