import Mathlib
import IndisputableMonolith.Patterns
import IndisputableMonolith.Patterns.GrayCycle
import IndisputableMonolith.Patterns.GrayCycleBRGC

/-!
# Minimal covering walks are Hamiltonian cycles

Any closed walk on the `d`-cube that visits every vertex has length at
least `2^d`. A walk of that length visits every vertex exactly once, so
it is a Hamiltonian cycle. The reflected Gray path attains the bound
for every `d > 0`.

For `d ≥ 2` the `2^d` edges of that cycle are pairwise distinct: a
repeated undirected edge would force `2 ≡ 0 (mod 2^d)`.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace HamiltonianCovering

open Patterns
open Patterns.GrayCycleBRGC

instance instNeZeroTwoPow (d : ℕ) : NeZero (2 ^ d) :=
  ⟨ne_of_gt (pow_pos (by decide : (0 : ℕ) < 2) d)⟩

/-- A covering walk no longer than the vertex count is bijective. -/
theorem covering_of_min_length_bijective {d T : ℕ} [NeZero T]
    (pass : Fin T → Pattern d)
    (hsurj : Function.Surjective pass)
    (hmin : T ≤ 2 ^ d) :
    Function.Bijective pass := by
  have hT : T = 2 ^ d :=
    le_antisymm hmin (min_ticks_cover pass hsurj)
  have hcard : Fintype.card (Fin T) = Fintype.card (Pattern d) := by
    rw [Fintype.card_fin, card_pattern, hT]
  exact (Fintype.bijective_iff_surjective_and_card pass).mpr ⟨hsurj, hcard⟩

/-- A Gray cover of period `2^d` is a Hamiltonian cycle on the vertices. -/
theorem min_covering_walk_is_hamiltonian {d : ℕ}
    (γ : GrayCover d (2 ^ d)) :
    Function.Bijective γ.path :=
  covering_of_min_length_bijective γ.path γ.complete le_rfl

/-- The reflected Gray path is a Hamiltonian cover in every positive
dimension. -/
theorem exists_hamiltonian_gray {d : ℕ} (hd : 0 < d) :
    ∃ γ : GrayCover d (2 ^ d), Function.Bijective γ.path :=
  ⟨brgcGrayCover d hd, min_covering_walk_is_hamiltonian (brgcGrayCover d hd)⟩

theorem grayCycle_bijective {d : ℕ} (γ : GrayCycle d) :
    Function.Bijective γ.path := by
  have hcard : Fintype.card (Fin (2 ^ d)) = Fintype.card (Pattern d) := by
    simp
  exact (Fintype.bijective_iff_injective_and_card γ.path).mpr ⟨γ.inj, hcard⟩

/-- The two endpoints of an undirected Gray-cycle edge. -/
def cycleEdge {d : ℕ} (γ : GrayCycle d) (i : Fin (2 ^ d)) : Set (Pattern d) :=
  {γ.path i, γ.path (i + 1)}

private lemma two_lt_two_pow {d : ℕ} (hd : 2 ≤ d) : 2 < 2 ^ d :=
  lt_of_lt_of_le (by decide : 2 < 4)
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hd)

private lemma two_ne_zero_of_two_le {d : ℕ} (hd : 2 ≤ d) :
    (2 : Fin (2 ^ d)) ≠ 0 := by
  intro h
  have hlt := two_lt_two_pow hd
  have hval := congrArg Fin.val h
  have : (2 : ℕ) = 0 := by
    simpa [Fin.val_natCast, Nat.mod_eq_of_lt hlt] using hval
  exact (by decide : ¬ (2 : ℕ) = 0) this

private lemma one_ne_zero_of_two_le {d : ℕ} (hd : 2 ≤ d) :
    (1 : Fin (2 ^ d)) ≠ 0 := by
  intro h
  have hlt : 1 < 2 ^ d := lt_trans (by decide : 1 < 2) (two_lt_two_pow hd)
  have : (1 : ℕ) = 0 := by
    simpa [Fin.val_natCast, Nat.mod_eq_of_lt hlt] using congrArg Fin.val h
  exact (by decide : ¬ (1 : ℕ) = 0) this

private lemma path_consecutive_ne {d : ℕ} (hd : 2 ≤ d) (γ : GrayCycle d)
    (i : Fin (2 ^ d)) : γ.path i ≠ γ.path (i + 1) := by
  intro h
  have : i = i + 1 := γ.inj h
  have h10 : (1 : Fin (2 ^ d)) = 0 :=
    add_left_cancel (a := i) (by simpa using this.symm)
  exact one_ne_zero_of_two_le hd h10

/-- For `d ≥ 2`, distinct phases determine distinct undirected edges. -/
theorem grayCycle_edges_distinct {d : ℕ} (hd : 2 ≤ d) (γ : GrayCycle d)
    {i j : Fin (2 ^ d)}
    (heq : cycleEdge γ i = cycleEdge γ j) : i = j := by
  have hpair :
      γ.path i = γ.path j ∧ γ.path (i + 1) = γ.path (j + 1) ∨
        γ.path i = γ.path (j + 1) ∧ γ.path (i + 1) = γ.path j := by
    have hi : γ.path i ∈ cycleEdge γ j := by
      rw [← heq]
      simp [cycleEdge]
    have hi1 : γ.path (i + 1) ∈ cycleEdge γ j := by
      rw [← heq]
      simp [cycleEdge]
    simp [cycleEdge] at hi hi1
    rcases hi with hi | hi
    · rcases hi1 with hi1 | hi1
      · exact (path_consecutive_ne hd γ i (hi.trans hi1.symm)).elim
      · exact Or.inl ⟨hi, hi1⟩
    · rcases hi1 with hi1 | hi1
      · exact Or.inr ⟨hi, hi1⟩
      · exact (path_consecutive_ne hd γ i (hi.trans hi1.symm)).elim
  rcases hpair with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact γ.inj h0
  · have hij : i = j + 1 := γ.inj h0
    have hji : i + 1 = j := γ.inj h1
    have h11 : (1 : Fin (2 ^ d)) + 1 = 2 := by
      apply Fin.ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (two_lt_two_pow hd)]
    have hsum : i + 1 = j + 2 := by
      calc
        i + 1 = j + 1 + 1 := by rw [hij]
        _ = j + (1 + 1) := add_assoc j 1 1
        _ = j + 2 := by rw [h11]
    have hj : j = j + 2 := hji.symm.trans hsum
    have hzero : (0 : Fin (2 ^ d)) = 2 :=
      add_left_cancel (a := j) (by simpa using hj)
    exact (two_ne_zero_of_two_le hd hzero.symm).elim

/-- A Hamiltonian Gray cycle of dimension at least 2 has `2^d` distinct
edges as well as `2^d` distinct vertices. -/
theorem grayCycle_is_simple {d : ℕ} (hd : 2 ≤ d) (γ : GrayCycle d) :
    Function.Bijective γ.path ∧
      ∀ {i j : Fin (2 ^ d)}, cycleEdge γ i = cycleEdge γ j → i = j :=
  ⟨grayCycle_bijective γ, fun heq => grayCycle_edges_distinct hd γ heq⟩

theorem grayCycle3_is_simple :
    Function.Bijective grayCycle3Path ∧
      ∀ {i j : Fin 8},
        ({grayCycle3Path i, grayCycle3Path (i + 1)} : Set _) =
            {grayCycle3Path j, grayCycle3Path (j + 1)} →
          i = j := by
  have h := grayCycle_is_simple (d := 3) (by decide) grayCycle3
  refine ⟨h.1, ?_⟩
  intro i j heq
  simpa [cycleEdge, grayCycle3] using h.2 (i := i) (j := j) (by simpa [cycleEdge, grayCycle3] using heq)

end HamiltonianCovering
end Foundation
end IndisputableMonolith
