/- Scratch module for the GLM-5.2 verify-loop integrated (with-retrieval) test.
Temporary: delete after validating retrieve -> propose -> build -> verify. -/
namespace IndisputableMonolith
namespace GlmScratch

theorem glm_scratch_mul_comm (a b : Nat) : a * b = b * a := by
  exact Nat.mul_comm a b

end GlmScratch
end IndisputableMonolith
