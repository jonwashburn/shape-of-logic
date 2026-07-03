import IndisputableMonolith.Cost.Ndim.Hessian

/-!
# Cost-induced projector, almost-product, golden, and metallic operators

This module packages the finite-dimensional operator algebra behind the
rank-one tensor picture. A covector `β` and an inverse metric kernel
`hInv` determine a sharp vector `β♯`, an operator
`A = h⁻¹ \tilde g`, its quadratic law `A² = μ A`, and the normalized
projector `P`.
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

open scoped BigOperators

/-- Raise a one-form `β` using the inverse metric kernel `hInv`. -/
noncomputable def sharp {n : ℕ}
    (hInv : Fin n → Fin n → ℝ) (β : Vec n) : Vec n :=
  fun i => ∑ j : Fin n, hInv i j * β j

/-- The rank-one operator `A = h^{-1} \tilde g` in coordinates, where
`\tilde g = λ β ⊗ β`. -/
noncomputable def AApply {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n) : Vec n → Vec n :=
  fun v => fun i => lam * sharp hInv β i * dot β v

/-- The scalar coefficient in the quadratic relation `A² = μ A`. -/
noncomputable def mu {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n) : ℝ :=
  lam * dot β (sharp hInv β)

/-- The normalized projector associated to `A`. -/
noncomputable def PApply {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n) : Vec n → Vec n :=
  fun v => (mu lam hInv β)⁻¹ • AApply lam hInv β v

/-- The induced almost-product operator `F = 2P - I`. -/
noncomputable def FApply {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n) : Vec n → Vec n :=
  fun v => 2 • PApply lam hInv β v - v

/-- The induced golden operator. -/
noncomputable def GApply {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n) : Vec n → Vec n :=
  fun v => ((1 : ℝ) / 2) • v + (Real.sqrt 5 / 2) • FApply lam hInv β v

/-- The metallic family derived from the same almost-product operator. -/
noncomputable def MetallicApply {n : ℕ}
    (p q lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n) : Vec n → Vec n :=
  fun v => (p / 2) • v + (Real.sqrt (p ^ 2 + 4 * q) / 2) • FApply lam hInv β v

theorem AApply_smul {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (c : ℝ) (v : Vec n) :
    AApply lam hInv β (c • v) = c • AApply lam hInv β v := by
  funext i
  unfold AApply dot
  calc
    lam * sharp hInv β i * ∑ j : Fin n, β j * (c * v j)
        = lam * sharp hInv β i * (c * ∑ j : Fin n, β j * v j) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = lam * sharp hInv β i * (c * dot β v) := by
          simp [dot]
    _ = c * (lam * sharp hInv β i * dot β v) := by
          ring

theorem AApply_add {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (v w : Vec n) :
    AApply lam hInv β (v + w) = AApply lam hInv β v + AApply lam hInv β w := by
  funext i
  unfold AApply dot
  calc
    lam * sharp hInv β i * ∑ j : Fin n, β j * (v j + w j)
        = lam * sharp hInv β i * ((∑ j : Fin n, β j * v j) + ∑ j : Fin n, β j * w j) := by
            congr 1
            simp [mul_add, Finset.sum_add_distrib]
    _ = lam * sharp hInv β i * dot β v + lam * sharp hInv β i * dot β w := by
          simp [dot]
          ring
    _ = (AApply lam hInv β v + AApply lam hInv β w) i := by
          simp [AApply]

theorem AApply_neg {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β w : Vec n) :
    AApply lam hInv β (-w) = -AApply lam hInv β w := by
  simpa using AApply_smul lam hInv β (-1) w

theorem AApply_sub {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (v w : Vec n) :
    AApply lam hInv β (v - w) = AApply lam hInv β v - AApply lam hInv β w := by
  ext i
  simp [sub_eq_add_neg, AApply_add, AApply_neg]

theorem dot_AApply {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β v : Vec n) :
    dot β (AApply lam hInv β v) = mu lam hInv β * dot β v := by
  unfold dot AApply mu
  calc
    ∑ i : Fin n, β i * (lam * sharp hInv β i * dot β v)
        = (lam * dot β v) * ∑ i : Fin n, β i * sharp hInv β i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = (lam * ∑ i : Fin n, β i * sharp hInv β i) * dot β v := by
          ring
    _ = mu lam hInv β * dot β v := by
          simp [mu, dot]

theorem AApply_sq {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β v : Vec n) :
    AApply lam hInv β (AApply lam hInv β v) = mu lam hInv β • AApply lam hInv β v := by
  funext i
  have hdot :
      dot β (fun k => lam * sharp hInv β k * dot β v) = mu lam hInv β * dot β v := by
    simpa [AApply] using dot_AApply lam hInv β v
  unfold AApply
  rw [hdot]
  simp [mu]
  ring

theorem PApply_smul {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (c : ℝ) (v : Vec n) :
    PApply lam hInv β (c • v) = c • PApply lam hInv β v := by
  ext i
  simp [PApply, AApply_smul, mul_assoc, mul_comm]

theorem PApply_add {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (v w : Vec n) :
    PApply lam hInv β (v + w) = PApply lam hInv β v + PApply lam hInv β w := by
  ext i
  simp [PApply, AApply_add]
  ring

theorem PApply_neg {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β w : Vec n) :
    PApply lam hInv β (-w) = -PApply lam hInv β w := by
  simpa using PApply_smul lam hInv β (-1) w

theorem PApply_sub {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (v w : Vec n) :
    PApply lam hInv β (v - w) = PApply lam hInv β v - PApply lam hInv β w := by
  ext i
  simp [sub_eq_add_neg, PApply_add, PApply_neg]

theorem PApply_idempotent {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (hμ : mu lam hInv β ≠ 0) (v : Vec n) :
    PApply lam hInv β (PApply lam hInv β v) = PApply lam hInv β v := by
  ext i
  simp [PApply, AApply_smul, AApply_sq, hμ, mul_comm]

theorem PApply_FApply {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (hμ : mu lam hInv β ≠ 0) (v : Vec n) :
    PApply lam hInv β (FApply lam hInv β v) = PApply lam hInv β v := by
  ext i
  have hsubi :
      PApply lam hInv β (FApply lam hInv β v) i
        = PApply lam hInv β (2 • PApply lam hInv β v) i - PApply lam hInv β v i := by
    unfold FApply
    rw [PApply_sub]
    rfl
  have hsmuli :
      PApply lam hInv β (2 • PApply lam hInv β v) i
        = (2 • PApply lam hInv β (PApply lam hInv β v)) i := by
    simpa using congrFun (PApply_smul lam hInv β 2 (PApply lam hInv β v)) i
  have hidi : PApply lam hInv β (PApply lam hInv β v) i = PApply lam hInv β v i := by
    simpa using congrFun (PApply_idempotent lam hInv β hμ v) i
  rw [hsubi, hsmuli]
  simp [hidi]
  ring

theorem FApply_smul {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (c : ℝ) (v : Vec n) :
    FApply lam hInv β (c • v) = c • FApply lam hInv β v := by
  ext i
  simp [FApply, PApply_smul, mul_comm]
  ring

theorem FApply_add {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (v w : Vec n) :
    FApply lam hInv β (v + w) = FApply lam hInv β v + FApply lam hInv β w := by
  ext i
  simp [FApply, PApply_add]
  ring

theorem FApply_neg {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β w : Vec n) :
    FApply lam hInv β (-w) = -FApply lam hInv β w := by
  simpa using FApply_smul lam hInv β (-1) w

theorem FApply_sub {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (v w : Vec n) :
    FApply lam hInv β (v - w) = FApply lam hInv β v - FApply lam hInv β w := by
  ext i
  simp [sub_eq_add_neg, FApply_add, FApply_neg]

theorem FApply_square {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (hμ : mu lam hInv β ≠ 0) (v : Vec n) :
    FApply lam hInv β (FApply lam hInv β v) = v := by
  ext i
  have hPFi : PApply lam hInv β (FApply lam hInv β v) i = PApply lam hInv β v i := by
    simpa using congrFun (PApply_FApply lam hInv β hμ v) i
  calc
    FApply lam hInv β (FApply lam hInv β v) i
        = (2 • PApply lam hInv β (FApply lam hInv β v) - FApply lam hInv β v) i := by
            simp [FApply]
    _ = (2 • PApply lam hInv β v - FApply lam hInv β v) i := by
          simp [hPFi]
    _ = v i := by
          simp [FApply]

theorem FApply_GApply {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (hμ : mu lam hInv β ≠ 0) (v : Vec n) :
    FApply lam hInv β (GApply lam hInv β v)
      = ((1 : ℝ) / 2) • FApply lam hInv β v + (Real.sqrt 5 / 2) • v := by
  unfold GApply
  rw [FApply_add, FApply_smul, FApply_smul, FApply_square _ _ _ hμ]

theorem FApply_MetallicApply {n : ℕ}
    (p q lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (hμ : mu lam hInv β ≠ 0) (v : Vec n) :
    FApply lam hInv β (MetallicApply p q lam hInv β v)
      = (p / 2) • FApply lam hInv β v
        + (Real.sqrt (p ^ 2 + 4 * q) / 2) • v := by
  unfold MetallicApply
  rw [FApply_add, FApply_smul, FApply_smul, FApply_square _ _ _ hμ]

theorem GApply_square {n : ℕ}
    (lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (hμ : mu lam hInv β ≠ 0) (v : Vec n) :
    GApply lam hInv β (GApply lam hInv β v) = GApply lam hInv β v + v := by
  ext i
  have hFGi :
      FApply lam hInv β
          (((1 : ℝ) / 2) • v + (Real.sqrt 5 / 2) • FApply lam hInv β v) i
        = (((1 : ℝ) / 2) • FApply lam hInv β v + (Real.sqrt 5 / 2) • v) i := by
    simpa [GApply] using congrFun (FApply_GApply lam hInv β hμ v) i
  have hsqrt : Real.sqrt 5 * Real.sqrt 5 = 5 := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (5 : ℝ))]
  have hsqrtq : (Real.sqrt 5 / 2) * (Real.sqrt 5 / 2) = 5 / 4 := by
    nlinarith [hsqrt]
  have hFGi' :
      FApply lam hInv β (((2 : ℝ)⁻¹) • v + (Real.sqrt 5 / 2) • FApply lam hInv β v) i
        = (((1 : ℝ) / 2) • FApply lam hInv β v + (Real.sqrt 5 / 2) • v) i := by
    simpa using hFGi
  simp [GApply]
  rw [hFGi']
  have hmul : (Real.sqrt 5 / 2) * ((Real.sqrt 5 / 2) * v i) = (5 / 4) * v i := by
    calc
      (Real.sqrt 5 / 2) * ((Real.sqrt 5 / 2) * v i)
          = ((Real.sqrt 5 / 2) * (Real.sqrt 5 / 2)) * v i := by
              ring
      _ = (5 / 4) * v i := by rw [hsqrtq]
  simp
  nlinarith [hmul]

theorem MetallicApply_square {n : ℕ}
    (p q lam : ℝ) (hInv : Fin n → Fin n → ℝ) (β : Vec n)
    (hμ : mu lam hInv β ≠ 0) (hq : 0 ≤ p ^ 2 + 4 * q) (v : Vec n) :
    MetallicApply p q lam hInv β (MetallicApply p q lam hInv β v)
      = p • MetallicApply p q lam hInv β v + q • v := by
  ext i
  have hFMi :
      FApply lam hInv β
          ((p / 2) • v + (Real.sqrt (p ^ 2 + 4 * q) / 2) • FApply lam hInv β v) i
        = ((p / 2) • FApply lam hInv β v
          + (Real.sqrt (p ^ 2 + 4 * q) / 2) • v) i := by
    simpa [MetallicApply] using congrFun (FApply_MetallicApply p q lam hInv β hμ v) i
  have hsqrt : Real.sqrt (p ^ 2 + 4 * q) * Real.sqrt (p ^ 2 + 4 * q) = p ^ 2 + 4 * q := by
    nlinarith [Real.sq_sqrt hq]
  have hsqrtq :
      (Real.sqrt (p ^ 2 + 4 * q) / 2) * (Real.sqrt (p ^ 2 + 4 * q) / 2)
        = (p ^ 2 + 4 * q) / 4 := by
    nlinarith [hsqrt]
  simp [MetallicApply, hFMi]
  have hmul :
      (Real.sqrt (p ^ 2 + 4 * q) / 2) *
          ((Real.sqrt (p ^ 2 + 4 * q) / 2) * v i)
        = ((p ^ 2 + 4 * q) / 4) * v i := by
    calc
      (Real.sqrt (p ^ 2 + 4 * q) / 2) *
          ((Real.sqrt (p ^ 2 + 4 * q) / 2) * v i)
          = ((Real.sqrt (p ^ 2 + 4 * q) / 2) *
              (Real.sqrt (p ^ 2 + 4 * q) / 2)) * v i := by
              ring
      _ = ((p ^ 2 + 4 * q) / 4) * v i := by rw [hsqrtq]
  nlinarith [hmul]

end Ndim
end Cost
end IndisputableMonolith
