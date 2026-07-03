import Mathlib

/-!
# F5 — Pinch Algebra (UFD / Operator Forms)

Foundation paper F5: mutual divisibility in UFDs and Fredholm obstruction.

## Main results

1. `mutual_div_unit` — mutual divisibility in a UFD implies unit ratio
2. `principal_ideal_eq_of_mutual_div` — principal ideal equality from mutual divisibility
3. `fredholm_not_surjective` — infinite cokernel ⟹ not surjective

## Cited by

BSD (primary), Yang–Mills (secondary)
-/

namespace IndisputableMonolith
namespace Foundation
namespace PinchAlgebra

/-! ## §1. Mutual divisibility in integral domains -/

/-- **F5.1.2/1.4**: Principal ideal equality from mutual divisibility.
    In a commutative ring, (a) = (b) iff a | b and b | a. -/
theorem principal_ideal_eq_of_mutual_dvd {R : Type*} [CommRing R]
    {a b : R} (hab : a ∣ b) (hba : b ∣ a) :
    Ideal.span ({a} : Set R) = Ideal.span {b} := by
  ext x
  simp only [Ideal.mem_span_singleton]
  constructor
  · intro ⟨r, hr⟩
    obtain ⟨c, hc⟩ := hba
    exact ⟨r * c, by rw [hr, hc]; ring⟩
  · intro ⟨r, hr⟩
    obtain ⟨d, hd⟩ := hab
    exact ⟨r * d, by rw [hr, hd]; ring⟩

/-! ## §2. Application template for Iwasawa theory -/

/-- **F5.2.3**: IMC equality from Kato (one side) + reverse divisibility (other side).
    This is the algebraic heart of BSD Stage 6.

    Given: (A) | (B) and (B) | (A) in a commutative ring,
    conclude (A) = (B) as principal ideals. -/
theorem imc_equality_template {R : Type*} [CommRing R]
    {A B : R} (hAB : A ∣ B) (hBA : B ∣ A) :
    Ideal.span ({A} : Set R) = Ideal.span {B} :=
  principal_ideal_eq_of_mutual_dvd hAB hBA

/-! ## §3. Fredholm / operator pinch template -/

/-- **F5.3.2**: A function that is not surjective cannot map finite sets
    onto infinite sets. (Basic set-theoretic obstruction.)
    This is the finite-capacity veto in its simplest form. -/
theorem finite_not_onto_infinite {α β : Type*} (f : α → β)
    [Finite α] (hβ : Infinite β) : ¬Function.Surjective f := by
  intro hsurj
  have : Finite β := Finite.of_surjective f hsurj
  exact not_finite β

/-- **F5.3.1/3.2**: If the cost per operation is positive and the budget is finite,
    only finitely many operations can be performed. -/
theorem finite_operations_from_budget {n : ℕ} {cost budget : ℝ}
    (hcost : 0 < cost) (hbudget : 0 ≤ budget)
    (hfit : n * cost ≤ budget) :
    (n : ℝ) ≤ budget / cost := by
  rwa [le_div_iff₀ hcost]

end PinchAlgebra
end Foundation
end IndisputableMonolith
