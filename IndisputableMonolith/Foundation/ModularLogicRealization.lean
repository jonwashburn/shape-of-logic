import IndisputableMonolith.Foundation.DiscreteLogicRealization

/-!
  ModularLogicRealization.lean

  Periodic finite-cyclic realization for Universal Forcing.

  The internal orbit is still free (`LogicNat`), while the carrier
  interpretation is periodic. This demonstrates that Universal Forcing does
  not require every realization to embed arithmetic faithfully into the carrier.
-/

namespace IndisputableMonolith
namespace Foundation
namespace ModularLogicRealization

/-- Equality cost on a finite carrier. -/
def finCost {m : ℕ} (x y : Fin m) : Nat :=
  if x = y then 0 else 1

@[simp] theorem finCost_self {m : ℕ} (x : Fin m) : finCost x x = 0 := by
  simp [finCost]

theorem finCost_symm {m : ℕ} (x y : Fin m) : finCost x y = finCost y x := by
  by_cases h : x = y
  · subst h
    simp [finCost]
  · have h' : y ≠ x := by intro hyx; exact h hyx.symm
    simp [finCost, h, h']

/-- The cyclic carrier size for the `k`th modular realization. -/
def modulus (k : ℕ) : ℕ := k + 2

theorem modulus_pos (k : ℕ) : 0 < modulus k := by
  unfold modulus
  omega

theorem one_lt_modulus (k : ℕ) : 1 < modulus k := by
  unfold modulus
  omega

/-- Successor on the finite cyclic carrier. -/
def cycStep (k : ℕ) (x : Fin (modulus k)) : Fin (modulus k) :=
  ⟨(x.val + 1) % modulus k, Nat.mod_lt _ (modulus_pos k)⟩

/-- Interpret the free orbit periodically in a finite cyclic carrier. -/
def modularInterpret (k : ℕ) (n : ArithmeticFromLogic.LogicNat) : Fin (modulus k) :=
  ⟨ArithmeticFromLogic.LogicNat.toNat n % modulus k, Nat.mod_lt _ (modulus_pos k)⟩

@[simp] theorem modularInterpret_zero (k : ℕ) :
    modularInterpret k ArithmeticFromLogic.LogicNat.zero = ⟨0, modulus_pos k⟩ := by
  apply Fin.ext
  change 0 % modulus k = 0
  exact Nat.zero_mod (modulus k)

theorem modularInterpret_step (k : ℕ) (n : ArithmeticFromLogic.LogicNat) :
    modularInterpret k (ArithmeticFromLogic.LogicNat.succ n)
      = cycStep k (modularInterpret k n) := by
  apply Fin.ext
  change ArithmeticFromLogic.LogicNat.toNat (ArithmeticFromLogic.LogicNat.succ n) % modulus k =
    (ArithmeticFromLogic.LogicNat.toNat n % modulus k + 1) % modulus k
  rw [ArithmeticFromLogic.LogicNat.toNat_succ, Nat.succ_eq_add_one]
  have h := (Nat.add_mod (ArithmeticFromLogic.LogicNat.toNat n) 1 (modulus k)).symm
  simpa [Nat.mod_eq_of_lt (one_lt_modulus k)] using h

/-- Finite cyclic Law-of-Logic realization with periodic interpretation. -/
def modularRealization (k : ℕ) : LogicRealization where
  Carrier := Fin (modulus k)
  Cost := Nat
  zeroCost := inferInstance
  compare := finCost
  zero := ⟨0, modulus_pos k⟩
  step := cycStep k
  Orbit := ArithmeticFromLogic.LogicNat
  orbitZero := ArithmeticFromLogic.LogicNat.zero
  orbitStep := ArithmeticFromLogic.LogicNat.succ
  interpret := modularInterpret k
  interpret_zero := modularInterpret_zero k
  interpret_step := modularInterpret_step k
  orbit_no_confusion := by
    intro n h
    exact ArithmeticFromLogic.LogicNat.zero_ne_succ n h
  orbit_step_injective := ArithmeticFromLogic.LogicNat.succ_injective
  orbit_induction := by
    intro P h0 hs n
    exact ArithmeticFromLogic.LogicNat.induction (motive := P) h0 hs n
  orbitEquivLogicNat := Equiv.refl ArithmeticFromLogic.LogicNat
  orbitEquiv_zero := rfl
  orbitEquiv_step := by intro n; rfl
  identity := finCost_self
  nonContradiction := finCost_symm
  excludedMiddle := True
  composition := True
  actionInvariant := True
  nontrivial := by
    refine ⟨⟨1, one_lt_modulus k⟩, ?_⟩
    simp [finCost]

/-- Modular realization has invariant extracted arithmetic. -/
noncomputable def modular_arithmetic_invariant (k : ℕ) (R : LogicRealization.{0, 0}) :
    (UniversalForcing.arithmeticOf (modularRealization k)).peano.carrier
      ≃ (UniversalForcing.arithmeticOf R).peano.carrier :=
  ArithmeticOf.equivOfInitial
    (UniversalForcing.arithmeticOf (modularRealization k))
    (UniversalForcing.arithmeticOf R)

/-- The modular interpretation is periodic on the carrier. -/
theorem modular_interpret_periodic (k : ℕ) (n : ArithmeticFromLogic.LogicNat) :
    modularInterpret k
        (ArithmeticFromLogic.LogicNat.fromNat
          (ArithmeticFromLogic.LogicNat.toNat n + modulus k))
      = modularInterpret k n := by
  apply Fin.ext
  simp [modularInterpret, ArithmeticFromLogic.LogicNat.toNat_fromNat]

end ModularLogicRealization
end Foundation
end IndisputableMonolith
