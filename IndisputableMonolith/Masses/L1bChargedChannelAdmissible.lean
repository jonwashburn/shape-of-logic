import Mathlib
import IndisputableMonolith.Masses.L1b3Q3FlagCarrier

/-!
# L1b Charged Channel Admissible: Conditional Finite-Algebra Uniqueness

This module closes the conditional finite-algebra uniqueness target for the
charged-lepton L1b carrier (the `profile_sum -> profile_constant ->
admissibleChannelKernel_unique` chain).

It proves: any kernel on the principal 48-element `Q3Flag` B3 carrier that is
B3-invariant, idempotent, has diagonal content one, and is entrywise
nonnegative (`AdmissibleChannelKernel`) is forced to equal the uniform
Reynolds projector `uniformReynolds Q3Flag`. The argument is the finite
Kawada-Ito route: invariance reduces the kernel to its identity-row profile
`K x y = mu (x^{-1} y)`; idempotence makes the profile convolution-idempotent;
nonnegativity plus the convolution identity forces the profile's mass at the
identity to be its maximum (`profile_at_id`); the sum constraint
(`profile_sum`, mass one) then forces every profile value down to the mean
`1/48` (`profile_constant`), pinning the kernel to `uniformReynolds`.

This is a THEOREM, axiom-clean (`propext`, `Classical.choice`,
`Lean.ofReduceBool`, `Lean.trustCompiler` from the `Fintype`/`Decidable`
machinery on `Q3Flag`, `Quot.sound`).

Honest boundary: this proves only the finite-algebra uniqueness statement
conditional on `AdmissibleChannelKernel`. It does NOT prove that the physical
charged-lepton recognition channel satisfies that predicate. L1b (the bridge
from this finite-algebra result to the physical channel) and L1 (the full
mass-bridge target) remain OPEN.
-/

namespace IndisputableMonolith
namespace Masses
namespace L1bChargedChannelAdmissible

open L1b1UniformReynoldsEngine
open L1b2SignKernelExclusion
open L1b3Q3FlagCarrier

noncomputable section

local instance : Nonempty Q3Flag := ⟨b3Id⟩

/-- Semantic B3 invariance for a kernel on the principal carrier. -/
def b3Invariant (K : Matrix Q3Flag Q3Flag ℝ) : Prop :=
  ∀ g x y, K (b3Act g x) (b3Act g y) = K x y

/--
Conditional finite-algebra admissibility predicate for the next theorem.

This is a predicate, not a proof that the physical charged-lepton channel
satisfies it.
-/
def AdmissibleChannelKernel (K : Matrix Q3Flag Q3Flag ℝ) : Prop :=
  b3Invariant K ∧
    K * K = K ∧
    diagonalContent K = 1 ∧
    entrywiseNonneg K

/-- Action compatibility inherited from the B3 multiplication certificate. -/
theorem b3Act_mul (g h x : B3) :
    b3Act g (b3Act h x) = b3Act (b3Mul g h) x := by
  exact b3Mul_assoc_all g h x

/-- Acting by `x⁻¹` sends `x` back to the identity flag. -/
theorem b3Act_inv_self (x : Q3Flag) :
    b3Act (b3Inv x) x = b3Id := by
  exact b3Inv_left_all x

/-- Acting by `x` sends the identity flag to `x`. -/
theorem b3Act_id_self (x : Q3Flag) :
    b3Act x b3Id = x := by
  exact b3Id_right_all x

/-- The profile of an invariant kernel: `μ(y) = K(e,y)`. -/
def kernelProfile (K : Matrix Q3Flag Q3Flag ℝ) : Q3Flag → ℝ :=
  fun y => K b3Id y

/--
Gateway lemma: an invariant kernel is determined by its identity-row profile.

This is the load-bearing reduction for the later convolution/max-principle
argument.
-/
theorem kernel_eq_profile (K : Matrix Q3Flag Q3Flag ℝ)
    (hInv : b3Invariant K) (x y : Q3Flag) :
    K x y = kernelProfile K (b3Act (b3Inv x) y) := by
  have hx : b3Act x b3Id = x := b3Act_id_self x
  have H := hInv (b3Inv x) x y
  rw [b3Act_inv_self x] at H
  calc
    K x y = K (b3Act x b3Id) y := by rw [hx]
    _ = K x y := rfl
    _ = K b3Id (b3Act (b3Inv x) y) := H.symm
    _ = kernelProfile K (b3Act (b3Inv x) y) := rfl

/-- Entrywise nonnegativity of a kernel makes its profile nonnegative. -/
theorem profile_nonneg (K : Matrix Q3Flag Q3Flag ℝ)
    (hNonneg : entrywiseNonneg K) :
    ∀ y, 0 ≤ kernelProfile K y := by
  intro y
  exact hNonneg b3Id y

/-- Every diagonal entry of an invariant kernel equals the profile at identity. -/
theorem diagonal_eq_profile_id (K : Matrix Q3Flag Q3Flag ℝ)
    (hInv : b3Invariant K) (x : Q3Flag) :
    K x x = kernelProfile K b3Id := by
  rw [kernel_eq_profile K hInv x x]
  have hx : b3Act (b3Inv x) x = b3Id := b3Act_inv_self x
  rw [hx]

/-- Convolution on the B3 principal carrier profile. -/
def conv (μ ν : Q3Flag → ℝ) : Q3Flag → ℝ :=
  fun z => ∑ w, μ w * ν (b3Act (b3Inv w) z)

/-- Idempotence of `K` induces convolution idempotence of its profile. -/
theorem profile_idempotent (K : Matrix Q3Flag Q3Flag ℝ)
    (hInv : b3Invariant K)
    (hIdem : K * K = K) :
    conv (kernelProfile K) (kernelProfile K) = kernelProfile K := by
  ext v
  have h := congrArg (fun M : Matrix Q3Flag Q3Flag ℝ => M b3Id v) hIdem
  simp only [Matrix.mul_apply] at h
  rw [show K b3Id v = kernelProfile K v from rfl] at h
  rw [show (∑ x, K b3Id x * K x v) =
      ∑ x, kernelProfile K x * kernelProfile K (b3Act (b3Inv x) v) by
        apply Finset.sum_congr rfl
        intro x _
        rw [kernel_eq_profile K hInv x v]
        rfl] at h
  change (∑ w, kernelProfile K w * kernelProfile K (b3Act (b3Inv w) v)) =
    kernelProfile K v
  exact h

/-- For fixed `g`, the principal B3 action permutes the finite carrier. -/
def b3ActEquiv (g : B3) : Q3Flag ≃ Q3Flag where
  toFun := b3Act g
  invFun := b3Act (b3Inv g)
  left_inv := by
    intro x
    rw [b3Act_mul, b3Inv_left_all]
    simpa [b3Act] using b3Id_left_all x
  right_inv := by
    intro x
    rw [b3Act_mul, b3Inv_right_all]
    simpa [b3Act] using b3Id_left_all x

/-- Reindexing by a fixed B3 action preserves finite sums. -/
theorem sum_b3Act (μ : Q3Flag → ℝ) (g : B3) :
    (∑ z, μ (b3Act g z)) = ∑ z, μ z := by
  simpa [b3ActEquiv] using (Equiv.sum_comp (b3ActEquiv g) μ)

/-- Total mass of the B3 convolution is the product of total masses. -/
theorem conv_sum (μ ν : Q3Flag → ℝ) :
    (∑ z, conv μ ν z) = (∑ w, μ w) * (∑ z, ν z) := by
  unfold conv
  calc
    (∑ z, ∑ w, μ w * ν (b3Act (b3Inv w) z))
        = ∑ w, ∑ z, μ w * ν (b3Act (b3Inv w) z) := by
          rw [Finset.sum_comm]
    _ = ∑ w, μ w * (∑ z, ν (b3Act (b3Inv w) z)) := by
          apply Finset.sum_congr rfl
          intro w _
          rw [← Finset.mul_sum]
    _ = ∑ w, μ w * (∑ z, ν z) := by
          apply Finset.sum_congr rfl
          intro w _
          rw [sum_b3Act ν (b3Inv w)]
    _ = (∑ w, μ w) * (∑ z, ν z) := by
          rw [Finset.sum_mul]

/-- Diagonal content one fixes the identity-row value of the profile. -/
theorem profile_at_id (K : Matrix Q3Flag Q3Flag ℝ)
    (hInv : b3Invariant K)
    (hDiag : diagonalContent K = 1) :
    kernelProfile K b3Id = (Fintype.card Q3Flag : ℝ)⁻¹ := by
  have hdiag_const : (∑ x : Q3Flag, kernelProfile K b3Id) = 1 := by
    calc
      (∑ x : Q3Flag, kernelProfile K b3Id) = ∑ x : Q3Flag, K x x := by
        apply Finset.sum_congr rfl
        intro x _
        exact (diagonal_eq_profile_id K hInv x).symm
      _ = 1 := by
        simpa [diagonalContent] using hDiag
  have hdiag_card :
      (Fintype.card Q3Flag : ℝ) * kernelProfile K b3Id = 1 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hdiag_const
  have hcard_ne : (Fintype.card Q3Flag : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    kernelProfile K b3Id =
        (Fintype.card Q3Flag : ℝ)⁻¹ *
          ((Fintype.card Q3Flag : ℝ) * kernelProfile K b3Id) := by
          field_simp [hcard_ne]
    _ = (Fintype.card Q3Flag : ℝ)⁻¹ := by
          rw [hdiag_card]
          ring

/-- The invariant idempotent profile has total mass one. -/
theorem profile_sum (K : Matrix Q3Flag Q3Flag ℝ)
    (hInv : b3Invariant K)
    (hIdem : K * K = K)
    (hDiag : diagonalContent K = 1)
    (hNonneg : entrywiseNonneg K) :
    (∑ y, kernelProfile K y) = 1 := by
  let μ : Q3Flag → ℝ := kernelProfile K
  let S : ℝ := ∑ y, μ y
  have hconv := profile_idempotent K hInv hIdem
  have hsum_conv :
      (∑ y, conv μ μ y) = ∑ y, μ y := by
    simpa [μ] using congrArg (fun f : Q3Flag → ℝ => ∑ y, f y) hconv
  have hSS : S * S = S := by
    rw [conv_sum μ μ] at hsum_conv
    simpa [S] using hsum_conv
  have hdiag_const : (∑ x : Q3Flag, kernelProfile K b3Id) = 1 := by
    calc
      (∑ x : Q3Flag, kernelProfile K b3Id) = ∑ x : Q3Flag, K x x := by
        apply Finset.sum_congr rfl
        intro x _
        exact (diagonal_eq_profile_id K hInv x).symm
      _ = 1 := by
        simpa [diagonalContent] using hDiag
  have hdiag_card :
      (Fintype.card Q3Flag : ℝ) * kernelProfile K b3Id = 1 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hdiag_const
  have hcard_pos : 0 < (Fintype.card Q3Flag : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hprofile_pos : 0 < kernelProfile K b3Id := by
    nlinarith
  have hS_ge : kernelProfile K b3Id ≤ S := by
    dsimp [S, μ]
    exact Finset.single_le_sum
      (fun y _ => profile_nonneg K hNonneg y)
      (Finset.mem_univ b3Id)
  have hSpos : 0 < S := lt_of_lt_of_le hprofile_pos hS_ge
  change S = 1
  nlinarith

/-- The finite Kawada-Ito/max-principle step for the B3 principal carrier. -/
theorem profile_constant (K : Matrix Q3Flag Q3Flag ℝ)
    (hInv : b3Invariant K)
    (hIdem : K * K = K)
    (hDiag : diagonalContent K = 1)
    (hNonneg : entrywiseNonneg K) :
    ∀ y, kernelProfile K y = (Fintype.card Q3Flag : ℝ)⁻¹ := by
  let μ : Q3Flag → ℝ := kernelProfile K
  have hμ_nonneg : ∀ y, 0 ≤ μ y := by
    intro y
    exact profile_nonneg K hNonneg y
  have hsum : (∑ y, μ y) = 1 := by
    simpa [μ] using profile_sum K hInv hIdem hDiag hNonneg
  have hid : μ b3Id = (Fintype.card Q3Flag : ℝ)⁻¹ := by
    simpa [μ] using profile_at_id K hInv hDiag
  rcases Finset.exists_max_image (Finset.univ : Finset Q3Flag) μ
      (Finset.univ_nonempty) with ⟨g₀, _, hmax⟩
  let M : ℝ := μ g₀
  have hleM : ∀ y, μ y ≤ M := by
    intro y
    exact hmax y (Finset.mem_univ y)
  have hM_nonneg : 0 ≤ M := hμ_nonneg g₀
  have hconv_fun := congrFun (profile_idempotent K hInv hIdem) g₀
  have hconv_g₀ :
      (∑ w, μ w * μ (b3Act (b3Inv w) g₀)) = M := by
    simpa [μ, conv, M] using hconv_fun
  have hdef_nonneg :
      ∀ w ∈ (Finset.univ : Finset Q3Flag),
        0 ≤ μ w * (M - μ (b3Act (b3Inv w) g₀)) := by
    intro w _
    exact mul_nonneg (hμ_nonneg w) (sub_nonneg.mpr (hleM (b3Act (b3Inv w) g₀)))
  have hdef_sum :
      (∑ w : Q3Flag, μ w * (M - μ (b3Act (b3Inv w) g₀))) = 0 := by
    calc
      (∑ w : Q3Flag, μ w * (M - μ (b3Act (b3Inv w) g₀)))
          = (∑ w : Q3Flag, μ w * M) -
              (∑ w : Q3Flag, μ w * μ (b3Act (b3Inv w) g₀)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro w _
            ring
      _ = (∑ w : Q3Flag, μ w) * M -
              (∑ w : Q3Flag, μ w * μ (b3Act (b3Inv w) g₀)) := by
            rw [Finset.sum_mul]
      _ = 0 := by
            rw [hsum, hconv_g₀]
            ring
  have hsingle_def_le_zero :
      μ g₀ * (M - μ (b3Act (b3Inv g₀) g₀)) ≤ 0 := by
    have hsingle_le := Finset.single_le_sum hdef_nonneg (Finset.mem_univ g₀)
    simpa [hdef_sum] using hsingle_le
  have harg_id : b3Act (b3Inv g₀) g₀ = b3Id := b3Act_inv_self g₀
  have hM_le_id : M ≤ μ b3Id := by
    by_cases hM_zero : M = 0
    · rw [hM_zero]
      exact hμ_nonneg b3Id
    · have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hM_zero)
      have hprod : M * (M - μ b3Id) ≤ 0 := by
        simpa [M, harg_id] using hsingle_def_le_zero
      nlinarith
  have hM_eq_id : M = μ b3Id := le_antisymm hM_le_id (hleM b3Id)
  have hle_id : ∀ y, μ y ≤ μ b3Id := by
    intro y
    rw [← hM_eq_id]
    exact hleM y
  have hdef_id_nonneg :
      ∀ z ∈ (Finset.univ : Finset Q3Flag), 0 ≤ μ b3Id - μ z := by
    intro z _
    exact sub_nonneg.mpr (hle_id z)
  have hdef_id_sum :
      (∑ z : Q3Flag, (μ b3Id - μ z)) = 0 := by
    calc
      (∑ z : Q3Flag, (μ b3Id - μ z))
          = (∑ z : Q3Flag, μ b3Id) - ∑ z : Q3Flag, μ z := by
            rw [← Finset.sum_sub_distrib]
      _ = (Fintype.card Q3Flag : ℝ) * μ b3Id - ∑ z : Q3Flag, μ z := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = 0 := by
            rw [hid, hsum]
            have hcard_ne : (Fintype.card Q3Flag : ℝ) ≠ 0 := by
              exact_mod_cast Fintype.card_ne_zero
            field_simp [hcard_ne]
            ring
  intro y
  have hy_le_zero : μ b3Id - μ y ≤ 0 := by
    have hsingle_le := Finset.single_le_sum hdef_id_nonneg (Finset.mem_univ y)
    simpa [hdef_id_sum] using hsingle_le
  have hy_nonneg : 0 ≤ μ b3Id - μ y := sub_nonneg.mpr (hle_id y)
  have hy_eq : μ y = μ b3Id := by
    nlinarith
  change μ y = (Fintype.card Q3Flag : ℝ)⁻¹
  rw [hy_eq, hid]

/--
Conditional finite-algebra closure of the L1b charged-channel carrier.

This proves only the finite algebra uniqueness statement: if a kernel on the
principal B3 carrier satisfies the admissibility predicate above, then it is the
uniform Reynolds projector. It does not prove the physical charged-lepton
channel satisfies `AdmissibleChannelKernel`.
-/
theorem admissibleChannelKernel_unique (K : Matrix Q3Flag Q3Flag ℝ)
    (hK : AdmissibleChannelKernel K) :
    K = uniformReynolds Q3Flag := by
  rcases hK with ⟨hInv, hIdem, hDiag, hNonneg⟩
  ext x y
  rw [kernel_eq_profile K hInv x y]
  rw [profile_constant K hInv hIdem hDiag hNonneg (b3Act (b3Inv x) y)]
  rw [uniformReynolds_apply (α := Q3Flag) x y]

end

end L1bChargedChannelAdmissible
end Masses
end IndisputableMonolith
