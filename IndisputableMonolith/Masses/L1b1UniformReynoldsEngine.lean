import Mathlib
import IndisputableMonolith.Masses.LeptonBoundaryLedger

/-!
# L1b1 Uniform Reynolds Engine

Panel-produced finite algebra for the charged-lepton leading bridge.

This is the generic carrier-independent rank-one projector engine:

* `outerProd x y`;
* `sqNorm x`;
* `characterProjector x = (sqNorm x)⁻¹ • outerProd x x`;
* `uniformReynolds = characterProjector ones`.

It proves idempotency, trace/content one, nonzero, and entrywise positivity for
the uniform Reynolds projector. It does not identify the physical charged channel;
that is the later `L1b3` carrier/admissibility target.
-/

namespace IndisputableMonolith
namespace Masses
namespace L1b1UniformReynoldsEngine

noncomputable section

/-- Rank-one outer product. -/
def outerProd {α : Type*} (x y : α → ℝ) : Matrix α α ℝ :=
  fun i j => x i * y j

/-- Finite dot product. -/
def dot {α : Type*} [Fintype α] (x y : α → ℝ) : ℝ :=
  ∑ i, x i * y i

/-- Squared norm of a finite real vector. -/
def sqNorm {α : Type*} [Fintype α] (x : α → ℝ) : ℝ :=
  dot x x

/-- Rank-one character projector, normalized by its squared norm. -/
def characterProjector {α : Type*} [Fintype α] (x : α → ℝ) : Matrix α α ℝ :=
  (sqNorm x)⁻¹ • outerProd x x

/-- The constant-one vector. -/
def ones (α : Type*) : α → ℝ :=
  fun _ => 1

/-- Uniform Reynolds projector on a finite carrier. -/
def uniformReynolds (α : Type*) [Fintype α] : Matrix α α ℝ :=
  characterProjector (ones α)

/-- Trace fallback that avoids depending on Mathlib's matrix trace API. -/
def diagonalContent {α : Type*} [Fintype α] (M : Matrix α α ℝ) : ℝ :=
  ∑ i, M i i

/-- Entrywise nonnegativity, the finite CPM cone used by later L1b targets. -/
def entrywiseNonneg {α : Type*} (M : Matrix α α ℝ) : Prop :=
  ∀ i j, 0 ≤ M i j

/-- Entrywise positivity. -/
def entrywisePos {α : Type*} (M : Matrix α α ℝ) : Prop :=
  ∀ i j, 0 < M i j

/-- Outer products multiply by the middle dot product. -/
theorem outerProd_mul_outerProd {α : Type*} [Fintype α]
    (x y z w : α → ℝ) :
    outerProd x y * outerProd z w = dot y z • outerProd x w := by
  ext i j
  simp [Matrix.mul_apply, outerProd, dot, Finset.mul_sum, mul_comm, mul_left_comm]

/-- Character projectors are idempotent whenever the normalizing norm is nonzero. -/
theorem characterProjector_idempotent {α : Type*} [Fintype α]
    (x : α → ℝ) (hx : sqNorm x ≠ 0) :
    characterProjector x * characterProjector x = characterProjector x := by
  unfold characterProjector
  rw [Matrix.smul_mul, Matrix.mul_smul, outerProd_mul_outerProd]
  rw [show dot x x = sqNorm x by rfl]
  ext i j
  simp [Matrix.smul_apply, outerProd]
  field_simp [hx]
  ring_nf
  simp [hx]

/-- The one-vector has squared norm equal to the carrier cardinality. -/
theorem sqNorm_ones {α : Type*} [Fintype α] :
    sqNorm (ones α) = (Fintype.card α : ℝ) := by
  simp [sqNorm, dot, ones]

private theorem card_ne_zero_of_nonempty (α : Type*) [Fintype α] [Nonempty α] :
    (Fintype.card α : ℝ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

private theorem card_pos_real (α : Type*) [Fintype α] [Nonempty α] :
    0 < (Fintype.card α : ℝ) := by
  exact_mod_cast Fintype.card_pos

/-- Closed form for the uniform Reynolds projector. -/
theorem uniformReynolds_apply {α : Type*} [Fintype α] [Nonempty α] (i j : α) :
    uniformReynolds α i j = ((Fintype.card α : ℝ)⁻¹) := by
  unfold uniformReynolds characterProjector
  rw [sqNorm_ones]
  simp [outerProd, ones]

/-- Uniform Reynolds is idempotent. -/
theorem uniformReynolds_idempotent {α : Type*} [Fintype α] [Nonempty α] :
    uniformReynolds α * uniformReynolds α = uniformReynolds α := by
  unfold uniformReynolds
  apply characterProjector_idempotent
  rw [sqNorm_ones]
  exact card_ne_zero_of_nonempty α

/-- Uniform Reynolds has diagonal content one. -/
theorem uniformReynolds_diagonalContent_one {α : Type*} [Fintype α] [Nonempty α] :
    diagonalContent (uniformReynolds α) = 1 := by
  unfold diagonalContent
  simp [uniformReynolds_apply, Finset.sum_const, nsmul_eq_mul]

/-- Uniform Reynolds is nonzero. -/
theorem uniformReynolds_ne_zero {α : Type*} [Fintype α] [Nonempty α] :
    uniformReynolds α ≠ 0 := by
  classical
  rcases ‹Nonempty α› with ⟨i⟩
  intro h
  have hentry : uniformReynolds α i i = 0 := by
    simpa using congrArg (fun M : Matrix α α ℝ => M i i) h
  rw [uniformReynolds_apply] at hentry
  exact (card_ne_zero_of_nonempty α) (inv_eq_zero.mp hentry)

/-- Uniform Reynolds is entrywise positive. -/
theorem uniformReynolds_entrywisePos {α : Type*} [Fintype α] [Nonempty α] :
    entrywisePos (uniformReynolds α) := by
  intro i j
  rw [uniformReynolds_apply]
  exact inv_pos.mpr (card_pos_real α)

/-- Uniform Reynolds is entrywise nonnegative. -/
theorem uniformReynolds_entrywiseNonneg {α : Type*} [Fintype α] [Nonempty α] :
    entrywiseNonneg (uniformReynolds α) := by
  intro i j
  exact le_of_lt (uniformReynolds_entrywisePos i j)

/-- L1b1 theorem-grade certificate. -/
structure UniformReynoldsEngineCert where
  idempotent :
    ∀ {α : Type*} [Fintype α] [Nonempty α],
      uniformReynolds α * uniformReynolds α = uniformReynolds α
  diagonal_content_one :
    ∀ {α : Type*} [Fintype α] [Nonempty α],
      diagonalContent (uniformReynolds α) = 1
  nonzero :
    ∀ {α : Type*} [Fintype α] [Nonempty α],
      uniformReynolds α ≠ 0
  entrywise_positive :
    ∀ {α : Type*} [Fintype α] [Nonempty α],
      entrywisePos (uniformReynolds α)
  entrywise_nonnegative :
    ∀ {α : Type*} [Fintype α] [Nonempty α],
      entrywiseNonneg (uniformReynolds α)

theorem uniformReynoldsEngineCert_holds :
    Nonempty UniformReynoldsEngineCert :=
  ⟨{ idempotent := by intro α _ _; exact uniformReynolds_idempotent
     diagonal_content_one := by intro α _ _; exact uniformReynolds_diagonalContent_one
     nonzero := by intro α _ _; exact uniformReynolds_ne_zero
     entrywise_positive := by intro α _ _; exact uniformReynolds_entrywisePos
     entrywise_nonnegative := by intro α _ _; exact uniformReynolds_entrywiseNonneg }⟩

end

end L1b1UniformReynoldsEngine
end Masses
end IndisputableMonolith
