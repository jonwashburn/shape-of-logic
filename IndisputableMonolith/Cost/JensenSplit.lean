import Mathlib
import IndisputableMonolith.Cost

/-!
# The uniform split is the cheapest

`Cost/GeometricRoot.lean` proves that the uniform `n`-fold subdivision of
a move of logarithmic size `s` costs `n·J(e^{s/n}) → 0`. This module
proves that the uniform split is the *cheapest* split: for any
decomposition `s = t 0 + … + t (n-1)`,

  `n · J(e^{s/n}) ≤ Σ J(e^{t i})`   (`uniform_split_cheapest`),

by Jensen's inequality applied to the convex symmetric exponential
average `u ↦ (e^u + e^{-u})/2` (`convexOn_symmExpAvg`). Consequently a
positive cost floor that fails against uniform refinements fails against
all refinements: the tick needs no assumption about how a refining
ledger slices its acts.
-/

namespace IndisputableMonolith
namespace Cost

/-- The symmetric exponential average `u ↦ (e^u + e^{-u})/2` is convex
on `ℝ`. -/
lemma convexOn_symmExpAvg :
    ConvexOn ℝ Set.univ (fun u : ℝ => (Real.exp u + Real.exp (-u)) / 2) := by
  have h1 : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
  have h2 : ConvexOn ℝ Set.univ (fun u : ℝ => Real.exp (-u)) := by
    have h := h1.comp_linearMap (-(LinearMap.id : ℝ →ₗ[ℝ] ℝ))
    simpa [Function.comp] using h
  have h3 := (h1.add h2).smul (by norm_num : (0:ℝ) ≤ 1/2)
  simpa [smul_eq_mul, div_eq_inv_mul] using h3

/-- **The uniform split is the cheapest.** For any decomposition of a
move of logarithmic size `s = ∑ i, t i` into `n` micro-moves, the total
cost is at least the cost of the uniform execution. -/
theorem uniform_split_cheapest {n : ℕ} (hn : 0 < n) (t : Fin n → ℝ) :
    (n : ℝ) * Jcost (Real.exp ((∑ i, t i) / n)) ≤
      ∑ i, Jcost (Real.exp (t i)) := by
  classical
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  set g : ℝ → ℝ := fun u => (Real.exp u + Real.exp (-u)) / 2 with hg
  have h₀ : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (n : ℝ)⁻¹ :=
    fun _ _ => by positivity
  have h₁ : ∑ _i : Fin n, (n : ℝ)⁻¹ = 1 := by
    simp [Finset.sum_const, Finset.card_univ]
    field_simp
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin n)), t i ∈ Set.univ :=
    fun _ _ => trivial
  have hj := convexOn_symmExpAvg.map_sum_le h₀ h₁ hmem
  have hsmul : ∑ i : Fin n, (n : ℝ)⁻¹ • t i = (∑ i, t i) / n := by
    rw [← Finset.smul_sum]
    simp [smul_eq_mul, div_eq_inv_mul]
  have hrhs : ∑ i : Fin n, (n : ℝ)⁻¹ • g (t i)
      = (n : ℝ)⁻¹ * ∑ i, g (t i) := by
    rw [← Finset.smul_sum]
    simp [smul_eq_mul]
  rw [hsmul, hrhs] at hj
  have hmul : (n : ℝ) * g ((∑ i, t i) / n) ≤ ∑ i, g (t i) := by
    have h := mul_le_mul_of_nonneg_left hj (le_of_lt hnR)
    calc (n : ℝ) * g ((∑ i, t i) / n) ≤ (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i, g (t i)) := h
      _ = ∑ i, g (t i) := by field_simp
  have hsub : ∑ i : Fin n, Jcost (Real.exp (t i))
      = (∑ i, g (t i)) - (n : ℝ) := by
    have : ∀ i : Fin n, Jcost (Real.exp (t i)) = g (t i) - 1 := by
      intro i
      simp [hg, Jcost_exp]
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib]
    simp [Finset.card_univ]
  have hlhs : (n : ℝ) * Jcost (Real.exp ((∑ i, t i) / n))
      = (n : ℝ) * g ((∑ i, t i) / n) - (n : ℝ) := by
    simp [hg, Jcost_exp]
    ring
  rw [hlhs, hsub]
  linarith [hmul]

end Cost
end IndisputableMonolith
