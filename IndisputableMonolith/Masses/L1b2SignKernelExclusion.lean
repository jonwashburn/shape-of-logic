import Mathlib
import IndisputableMonolith.Masses.L1b1UniformReynoldsEngine

/-!
# L1b2 Sign Kernel Exclusion

Generic finite sign-kernel lemmas after `L1b1UniformReynoldsEngine`.

This file proves that normalized rank-one plus-or-minus-one sign kernels are idempotent,
trace/content one, positive on the diagonal, and quadratic-form nonnegative.
Those weak gates do not exclude tau-odd / mixed-sign characters.

The decisive gate is entrywise CPM-cone nonnegativity: a mixed-sign kernel has a
negative off-diagonal entry, and conversely entrywise nonnegativity forces all
signs equal, hence collapses the sign kernel to the uniform Reynolds projector.

This is still only L1b2 finite algebra. It does not identify the physical charged
channel and does not close L1b or L1.
-/

namespace IndisputableMonolith
namespace Masses
namespace L1b2SignKernelExclusion

open L1b1UniformReynoldsEngine

noncomputable section

/-- A real sign vector with entries `+1` or `-1`. -/
def signValues {α : Type*} (eps : α → ℝ) : Prop :=
  ∀ i, eps i = 1 ∨ eps i = -1

/-- Rank-one sign kernel, using the L1b1 character-projector engine. -/
def signKernel {α : Type*} [Fintype α] (eps : α → ℝ) : Matrix α α ℝ :=
  characterProjector eps

/-- Positive diagonal, a weak admissibility gate that L1b2 must show is insufficient. -/
def positiveDiagonal {α : Type*} (M : Matrix α α ℝ) : Prop :=
  ∀ i, 0 < M i i

/-- Quadratic-form nonnegativity, a finite PSD surrogate. -/
def quadraticNonneg {α : Type*} [Fintype α] (M : Matrix α α ℝ) : Prop :=
  ∀ z : α → ℝ, 0 ≤ ∑ i, ∑ j, z i * M i j * z j

/-- A sign vector contains both signs. -/
def mixedSigns {α : Type*} (eps : α → ℝ) : Prop :=
  ∃ i j, eps i = 1 ∧ eps j = -1

/-- A sign vector is odd under an involutive/tau permutation. -/
def tauOdd {α : Type*} (tau : Equiv.Perm α) (eps : α → ℝ) : Prop :=
  ∀ i, eps (tau i) = - eps i

private theorem fintype_card_ne_zero_real (α : Type*) [Fintype α] [Nonempty α] :
    (Fintype.card α : ℝ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

private theorem fintype_card_pos_real (α : Type*) [Fintype α] [Nonempty α] :
    0 < (Fintype.card α : ℝ) := by
  exact_mod_cast Fintype.card_pos

/-- A sign entry squares to one. -/
theorem sign_sq {α : Type*} {eps : α → ℝ} (hε : signValues eps) (i : α) :
    eps i ^ 2 = 1 := by
  rcases hε i with hi | hi <;> rw [hi] <;> norm_num

/-- Multiplicative form of `sign_sq`. -/
theorem sign_mul_self {α : Type*} {eps : α → ℝ} (hε : signValues eps) (i : α) :
    eps i * eps i = 1 := by
  simpa [pow_two] using sign_sq hε i

/-- A plus-or-minus-one vector has squared norm equal to the carrier cardinality. -/
theorem sqNorm_sign {α : Type*} [Fintype α] {eps : α → ℝ}
    (hε : signValues eps) :
    sqNorm eps = (Fintype.card α : ℝ) := by
  unfold sqNorm dot
  calc
    (∑ i, eps i * eps i) = ∑ _ : α, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact sign_mul_self hε i
    _ = (Fintype.card α : ℝ) := by
      simp

/-- Closed form for a normalized sign kernel. -/
theorem signKernel_apply {α : Type*} [Fintype α] {eps : α → ℝ}
    (hε : signValues eps) (i j : α) :
    signKernel eps i j = ((Fintype.card α : ℝ)⁻¹) * eps i * eps j := by
  unfold signKernel characterProjector
  rw [sqNorm_sign hε]
  simp [outerProd, mul_assoc]

/-- A normalized sign kernel is idempotent on a nonempty carrier. -/
theorem signKernel_idempotent {α : Type*} [Fintype α] [Nonempty α]
    {eps : α → ℝ} (hε : signValues eps) :
    signKernel eps * signKernel eps = signKernel eps := by
  unfold signKernel
  apply characterProjector_idempotent
  rw [sqNorm_sign hε]
  exact fintype_card_ne_zero_real α

/-- A normalized sign kernel has diagonal content one. -/
theorem signKernel_diagonalContent_one {α : Type*} [Fintype α] [Nonempty α]
    {eps : α → ℝ} (hε : signValues eps) :
    diagonalContent (signKernel eps) = 1 := by
  unfold diagonalContent
  calc
    (∑ i, signKernel eps i i)
        = ∑ _ : α, ((Fintype.card α : ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [signKernel_apply hε i i]
          rw [mul_assoc, sign_mul_self hε i, mul_one]
    _ = (Fintype.card α : ℝ) * ((Fintype.card α : ℝ)⁻¹) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = 1 := by
          field_simp [fintype_card_ne_zero_real α]

/-- A normalized sign kernel is positive on the diagonal. -/
theorem signKernel_positiveDiagonal {α : Type*} [Fintype α] [Nonempty α]
    {eps : α → ℝ} (hε : signValues eps) :
    positiveDiagonal (signKernel eps) := by
  intro i
  rw [signKernel_apply hε i i, mul_assoc, sign_mul_self hε i, mul_one]
  exact inv_pos.mpr (fintype_card_pos_real α)

private theorem sum_pair_mul_eq_square {α : Type*} [Fintype α] (a : α → ℝ) :
    (∑ i, ∑ j, a i * a j) = (∑ i, a i) ^ 2 := by
  rw [pow_two]
  calc
    (∑ i, ∑ j, a i * a j)
        = ∑ i, a i * (∑ j, a j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = (∑ i, a i) * (∑ j, a j) := by
          rw [Finset.sum_mul]

/-- Explicit quadratic-form value of a sign kernel. -/
theorem signKernel_quadratic_form {α : Type*} [Fintype α]
    {eps : α → ℝ} (hε : signValues eps) (z : α → ℝ) :
    (∑ i, ∑ j, z i * signKernel eps i j * z j)
      = ((Fintype.card α : ℝ)⁻¹) * (∑ i, z i * eps i) ^ 2 := by
  calc
    (∑ i, ∑ j, z i * signKernel eps i j * z j)
        = ∑ i, ∑ j,
            z i * (((Fintype.card α : ℝ)⁻¹) * eps i * eps j) * z j := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [signKernel_apply hε i j]
    _ = ((Fintype.card α : ℝ)⁻¹) *
          (∑ i, ∑ j, (z i * eps i) * (z j * eps j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ((Fintype.card α : ℝ)⁻¹) * (∑ i, z i * eps i) ^ 2 := by
          rw [sum_pair_mul_eq_square (fun i => z i * eps i)]

/-- A normalized sign kernel is quadratic-form nonnegative. -/
theorem signKernel_quadraticNonneg {α : Type*} [Fintype α] [Nonempty α]
    {eps : α → ℝ} (hε : signValues eps) :
    quadraticNonneg (signKernel eps) := by
  intro z
  rw [signKernel_quadratic_form hε z]
  exact mul_nonneg
    (le_of_lt (inv_pos.mpr (fintype_card_pos_real α)))
    (sq_nonneg _)

/-- Mixed signs produce a negative off-diagonal entry. -/
theorem signKernel_negative_offDiagonal_of_mixed {α : Type*} [Fintype α] [Nonempty α]
    {eps : α → ℝ} (hε : signValues eps) (hmix : mixedSigns eps) :
    ∃ i j : α, i ≠ j ∧ signKernel eps i j < 0 := by
  rcases hmix with ⟨i, j, hi, hj⟩
  have hij : i ≠ j := by
    intro hij
    have hcontr : (1 : ℝ) = -1 := by
      calc
        (1 : ℝ) = eps i := hi.symm
        _ = eps j := by rw [hij]
        _ = -1 := hj
    norm_num at hcontr
  refine ⟨i, j, hij, ?_⟩
  rw [signKernel_apply hε i j, hi, hj]
  have hpos : 0 < ((Fintype.card α : ℝ)⁻¹) :=
    inv_pos.mpr (fintype_card_pos_real α)
  nlinarith

/-- Therefore a mixed-sign kernel is not entrywise nonnegative. -/
theorem signKernel_not_entrywiseNonneg_of_mixed {α : Type*} [Fintype α] [Nonempty α]
    {eps : α → ℝ} (hε : signValues eps) (hmix : mixedSigns eps) :
    ¬ entrywiseNonneg (signKernel eps) := by
  intro hnonneg
  rcases signKernel_negative_offDiagonal_of_mixed hε hmix with ⟨i, j, _, hneg⟩
  exact (not_le_of_gt hneg) (hnonneg i j)

/-- Weak gates hold for mixed-sign kernels, but the CPM entrywise cone fails. -/
theorem mixedSignKernel_weakGates_hold_not_entrywiseNonneg
    {α : Type*} [Fintype α] [Nonempty α]
    {eps : α → ℝ} (hε : signValues eps) (hmix : mixedSigns eps) :
    positiveDiagonal (signKernel eps) ∧
      quadraticNonneg (signKernel eps) ∧
        ¬ entrywiseNonneg (signKernel eps) := by
  exact ⟨signKernel_positiveDiagonal hε,
    ⟨signKernel_quadraticNonneg hε,
      signKernel_not_entrywiseNonneg_of_mixed hε hmix⟩⟩

/-- Entrywise nonnegativity forces all sign entries to be equal. -/
theorem signKernel_entrywiseNonneg_forces_all_signs_equal
    {α : Type*} [Fintype α] [Nonempty α]
    {eps : α → ℝ} (hε : signValues eps)
    (hnonneg : entrywiseNonneg (signKernel eps)) :
    ∀ i j : α, eps i = eps j := by
  intro i j
  rcases hε i with hi | hi
  · rcases hε j with hj | hj
    · rw [hi, hj]
    · exfalso
      have hbad : signKernel eps i j < 0 := by
        rw [signKernel_apply hε i j, hi, hj]
        have hpos : 0 < ((Fintype.card α : ℝ)⁻¹) :=
          inv_pos.mpr (fintype_card_pos_real α)
        nlinarith
      exact (not_le_of_gt hbad) (hnonneg i j)
  · rcases hε j with hj | hj
    · exfalso
      have hbad : signKernel eps i j < 0 := by
        rw [signKernel_apply hε i j, hi, hj]
        have hpos : 0 < ((Fintype.card α : ℝ)⁻¹) :=
          inv_pos.mpr (fintype_card_pos_real α)
        nlinarith
      exact (not_le_of_gt hbad) (hnonneg i j)
    · rw [hi, hj]

/-- Under entrywise CPM nonnegativity, a sign kernel collapses to uniform Reynolds. -/
theorem signKernel_eq_uniformReynolds_of_entrywiseNonneg
    {α : Type*} [Fintype α] [Nonempty α]
    {eps : α → ℝ} (hε : signValues eps)
    (hnonneg : entrywiseNonneg (signKernel eps)) :
    signKernel eps = uniformReynolds α := by
  ext i j
  rw [signKernel_apply hε i j, uniformReynolds_apply (α := α) i j]
  have hsame : eps i = eps j :=
    signKernel_entrywiseNonneg_forces_all_signs_equal hε hnonneg i j
  have hs : eps i * eps j = 1 := by
    rw [← hsame]
    exact sign_mul_self hε i
  rw [mul_assoc, hs, mul_one]

/-- Tau-oddness on a nonempty carrier forces mixed signs. -/
theorem mixedSigns_of_tauOdd {α : Type*} [Nonempty α]
    {eps : α → ℝ} {tau : Equiv.Perm α}
    (hε : signValues eps) (hτ : tauOdd tau eps) :
    mixedSigns eps := by
  rcases ‹Nonempty α› with ⟨i⟩
  rcases hε i with hi | hi
  · refine ⟨i, tau i, hi, ?_⟩
    simp [hτ i, hi]
  · refine ⟨tau i, i, ?_, hi⟩
    simp [hτ i, hi]

/-- Hence tau-odd sign kernels fail entrywise CPM nonnegativity. -/
theorem signKernel_not_entrywiseNonneg_of_tauOdd
    {α : Type*} [Fintype α] [Nonempty α]
    {eps : α → ℝ} {tau : Equiv.Perm α}
    (hε : signValues eps) (hτ : tauOdd tau eps) :
    ¬ entrywiseNonneg (signKernel eps) := by
  exact signKernel_not_entrywiseNonneg_of_mixed hε
    (mixedSigns_of_tauOdd hε hτ)

/-- L1b2 finite theorem certificate. -/
structure SignKernelExclusionCert where
  sign_square :
    ∀ {α : Type*} {eps : α → ℝ},
      signValues eps → ∀ i : α, eps i * eps i = 1
  sign_kernel_apply :
    ∀ {α : Type*} [Fintype α] {eps : α → ℝ},
      signValues eps → ∀ i j : α,
        signKernel eps i j = ((Fintype.card α : ℝ)⁻¹) * eps i * eps j
  idempotent :
    ∀ {α : Type*} [Fintype α] [Nonempty α] {eps : α → ℝ},
      signValues eps →
        signKernel eps * signKernel eps = signKernel eps
  diagonal_content_one :
    ∀ {α : Type*} [Fintype α] [Nonempty α] {eps : α → ℝ},
      signValues eps →
        diagonalContent (signKernel eps) = 1
  positive_diagonal :
    ∀ {α : Type*} [Fintype α] [Nonempty α] {eps : α → ℝ},
      signValues eps →
        positiveDiagonal (signKernel eps)
  quadratic_nonneg :
    ∀ {α : Type*} [Fintype α] [Nonempty α] {eps : α → ℝ},
      signValues eps →
        quadraticNonneg (signKernel eps)
  mixed_negative_offDiagonal :
    ∀ {α : Type*} [Fintype α] [Nonempty α] {eps : α → ℝ},
      signValues eps → mixedSigns eps →
        ∃ i j : α, i ≠ j ∧ signKernel eps i j < 0
  mixed_not_entrywise_nonneg :
    ∀ {α : Type*} [Fintype α] [Nonempty α] {eps : α → ℝ},
      signValues eps → mixedSigns eps →
        ¬ entrywiseNonneg (signKernel eps)
  weak_gates_insufficient :
    ∀ {α : Type*} [Fintype α] [Nonempty α] {eps : α → ℝ},
      signValues eps → mixedSigns eps →
        positiveDiagonal (signKernel eps) ∧
          quadraticNonneg (signKernel eps) ∧
            ¬ entrywiseNonneg (signKernel eps)
  entrywise_nonneg_forces_equal :
    ∀ {α : Type*} [Fintype α] [Nonempty α] {eps : α → ℝ},
      signValues eps → entrywiseNonneg (signKernel eps) →
        ∀ i j : α, eps i = eps j
  entrywise_nonneg_forces_uniform :
    ∀ {α : Type*} [Fintype α] [Nonempty α] {eps : α → ℝ},
      signValues eps → entrywiseNonneg (signKernel eps) →
        signKernel eps = uniformReynolds α
  tauOdd_mixed :
    ∀ {α : Type*} [Nonempty α] {eps : α → ℝ} {tau : Equiv.Perm α},
      signValues eps → tauOdd tau eps →
        mixedSigns eps
  tauOdd_not_entrywise_nonneg :
    ∀ {α : Type*} [Fintype α] [Nonempty α]
      {eps : α → ℝ} {tau : Equiv.Perm α},
      signValues eps → tauOdd tau eps →
        ¬ entrywiseNonneg (signKernel eps)

theorem signKernelExclusionCert_holds :
    Nonempty SignKernelExclusionCert :=
  ⟨{ sign_square := by
        intro α eps hε i
        exact sign_mul_self hε i
     sign_kernel_apply := by
        intro α _ eps hε i j
        exact signKernel_apply hε i j
     idempotent := by
        intro α _ _ eps hε
        exact signKernel_idempotent hε
     diagonal_content_one := by
        intro α _ _ eps hε
        exact signKernel_diagonalContent_one hε
     positive_diagonal := by
        intro α _ _ eps hε
        exact signKernel_positiveDiagonal hε
     quadratic_nonneg := by
        intro α _ _ eps hε
        exact signKernel_quadraticNonneg hε
     mixed_negative_offDiagonal := by
        intro α _ _ eps hε hmix
        exact signKernel_negative_offDiagonal_of_mixed hε hmix
     mixed_not_entrywise_nonneg := by
        intro α _ _ eps hε hmix
        exact signKernel_not_entrywiseNonneg_of_mixed hε hmix
     weak_gates_insufficient := by
        intro α _ _ eps hε hmix
        exact mixedSignKernel_weakGates_hold_not_entrywiseNonneg hε hmix
     entrywise_nonneg_forces_equal := by
        intro α _ _ eps hε hnonneg i j
        exact signKernel_entrywiseNonneg_forces_all_signs_equal hε hnonneg i j
     entrywise_nonneg_forces_uniform := by
        intro α _ _ eps hε hnonneg
        exact signKernel_eq_uniformReynolds_of_entrywiseNonneg hε hnonneg
     tauOdd_mixed := by
        intro α _ eps tau hε hτ
        exact mixedSigns_of_tauOdd hε hτ
     tauOdd_not_entrywise_nonneg := by
        intro α _ _ eps tau hε hτ
        exact signKernel_not_entrywiseNonneg_of_tauOdd hε hτ }⟩

end

end L1b2SignKernelExclusion
end Masses
end IndisputableMonolith
