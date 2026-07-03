import Mathlib

/-!
# The hyperoctahedral group `B3` of signed permutations of `Fin 3`

This module installs the group structure on signed permutations of `Fin 3`
(the symmetry group of the cube/octahedron, order `48 = 2^3 · 3!`) and its
linear action on `Fin 3 → ℝ` by coordinate permutation together with sign
flips.  This is the symmetry group that tiles `ℝ³` into the `48` Weyl chambers
used in the L1b chamber bridge; the action here is the one whose fundamental
domain is the closed cone `{0 ≤ x₀ ≤ x₁ ≤ x₂}` realising the finite `1/48`.

We deliberately wrap the underlying data in a `structure` rather than using the
product type `Equiv.Perm (Fin 3) × (Fin 3 → Bool)` directly: that product
already carries the componentwise `Mul` instance (via `Bool`'s `and`), which is
*not* the semidirect-product law we need, so reusing it would create an
instance diamond.
-/

namespace IndisputableMonolith.Masses.L1bHyperoctahedralGroup

open scoped Pointwise

/-- A signed permutation of `Fin 3`: a permutation `perm` together with a sign
pattern `sign` (`true` = flip that coordinate).  These are the `48` elements of
the hyperoctahedral group `B3`. -/
structure SignedPerm where
  perm : Equiv.Perm (Fin 3)
  sign : Fin 3 → Bool

namespace SignedPerm

@[ext] theorem ext {g h : SignedPerm}
    (hp : g.perm = h.perm) (hs : g.sign = h.sign) : g = h := by
  cases g; cases h; cases hp; cases hs; rfl

/-- Group multiplication is the semidirect product law forced by demanding that
the linear action below be a *left* action:
`(σ,s) * (τ,t) = (σ.trans τ, fun i => xor (s i) (t (σ i)))`. -/
instance : Mul SignedPerm where
  mul g h := ⟨g.perm.trans h.perm, fun i => xor (g.sign i) (h.sign (g.perm i))⟩

/-- The identity signed permutation. -/
instance : One SignedPerm where
  one := ⟨1, fun _ => false⟩

/-- Inverse: `(σ,s)⁻¹ = (σ⁻¹, s ∘ σ⁻¹)`. -/
instance : Inv SignedPerm where
  inv g := ⟨g.perm⁻¹, fun i => g.sign (g.perm⁻¹ i)⟩

@[simp] theorem mul_perm (g h : SignedPerm) :
    (g * h).perm = g.perm.trans h.perm := rfl

@[simp] theorem mul_sign (g h : SignedPerm) :
    (g * h).sign = fun i => xor (g.sign i) (h.sign (g.perm i)) := rfl

@[simp] theorem one_perm : (1 : SignedPerm).perm = 1 := rfl
@[simp] theorem one_sign : (1 : SignedPerm).sign = fun _ => false := rfl

@[simp] theorem inv_perm (g : SignedPerm) : g⁻¹.perm = g.perm⁻¹ := rfl
@[simp] theorem inv_sign (g : SignedPerm) :
    g⁻¹.sign = fun i => g.sign (g.perm⁻¹ i) := rfl

instance : Group SignedPerm where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc g h k := by
    ext i
    · simp [Equiv.trans_assoc]
    · simp only [mul_sign]
      exact Bool.xor_assoc _ _ _
  one_mul g := by
    ext i
    · simp
    · simp
  mul_one g := by
    ext i
    · simp
    · simp
  inv_mul_cancel g := by
    ext i
    · simp
    · simp only [mul_sign, one_sign, inv_sign]
      simp

/-- `B3` has exactly `48 = 2^3 · 3!` elements. -/
instance : Fintype SignedPerm :=
  Fintype.ofEquiv (Equiv.Perm (Fin 3) × (Fin 3 → Bool))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun g => (g.perm, g.sign)
      left_inv := fun p => rfl
      right_inv := fun g => by cases g; rfl }

instance : DecidableEq SignedPerm := fun g h => by
  rw [SignedPerm.ext_iff]; exact inferInstance

theorem card_eq_48 : Fintype.card SignedPerm = 48 := by
  rw [Fintype.card_congr
    (Equiv.mk (fun g : SignedPerm => (g.perm, g.sign))
      (fun p => ⟨p.1, p.2⟩) (fun g => by cases g; rfl) (fun p => rfl))]
  decide

/-- The linear action of a signed permutation on `Fin 3 → ℝ`:
permute coordinates by `perm`, then flip the sign of coordinate `i` when
`sign i` is `true`. -/
def signedAct (g : SignedPerm) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => if g.sign i then -(v (g.perm i)) else v (g.perm i)

@[simp] theorem signedAct_one (v : Fin 3 → ℝ) : signedAct 1 v = v := by
  funext i; simp [signedAct]

theorem signedAct_mul (g h : SignedPerm) (v : Fin 3 → ℝ) :
    signedAct (g * h) v = signedAct g (signedAct h v) := by
  funext i
  simp only [signedAct, mul_sign, mul_perm, Equiv.trans_apply]
  rcases g.sign i with _ | _ <;>
    rcases h.sign (g.perm i) with _ | _ <;>
      simp

instance : MulAction SignedPerm (Fin 3 → ℝ) where
  smul := signedAct
  one_smul := signedAct_one
  mul_smul := signedAct_mul

@[simp] theorem smul_def (g : SignedPerm) (v : Fin 3 → ℝ) :
    g • v = signedAct g v := rfl

end SignedPerm

end IndisputableMonolith.Masses.L1bHyperoctahedralGroup
