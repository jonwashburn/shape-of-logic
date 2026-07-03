import IndisputableMonolith.Cost.Ndim.Calibration

/-!
# Permutation symmetry of coefficient weights
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

/-- Coefficients are invariant under permutations of indices. -/
def CoeffPermutationInvariant {n : ℕ} (α : Vec n) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), ∀ i : Fin n, α (σ i) = α i

theorem coeff_perm_invariant_of_uniform {n : ℕ} {α : Vec n}
    (hU : UniformWeights α) :
    CoeffPermutationInvariant α := by
  rcases hU with ⟨a, ha⟩
  intro σ i
  simp [ha]

theorem uniform_of_coeff_perm_invariant {n : ℕ} (hn : 0 < n) {α : Vec n}
    (hperm : CoeffPermutationInvariant α) :
    UniformWeights α := by
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨α i0, ?_⟩
  intro i
  have h := hperm (Equiv.swap i0 i) i0
  simpa using h

end Ndim
end Cost
end IndisputableMonolith
