import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite weighted-graph Dirichlet action

This module isolates the finite weighted-graph action used by the simplicial
ledger continuum bridge. Its imports are Mathlib-only. The action, Laplacian,
and pairing identities below contain no physical normalization or continuum
endpoint assumptions.
-/

namespace IndisputableMonolith
namespace Foundation
namespace SimplicialLedger
namespace ContinuumBridge

noncomputable section

/-! ## Definitions -/

/-- A weighted simplicial graph representing the ledger. -/
structure WeightedLedgerGraph (n : ℕ) where
  weight : Fin n → Fin n → ℝ
  weight_nonneg : ∀ i j, 0 ≤ weight i j
  weight_symm : ∀ i j, weight i j = weight j i

/-- The discrete Laplacian action (= quadratic J-cost) on the graph. -/
def laplacian_action {n : ℕ} (G : WeightedLedgerGraph n) (ε : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ i : Fin n, ∑ j : Fin n, G.weight i j * (ε i - ε j) ^ 2

/-- The discrete Laplacian of ε at vertex i:
    (Δε)_i = Σ_j w_ij · (ε_i − ε_j) -/
def discrete_laplacian {n : ℕ} (G : WeightedLedgerGraph n) (ε : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, G.weight i j * (ε i - ε j)

/-- The finite pairing `⟨η, Δε⟩`. -/
def laplacian_pairing {n : ℕ} (G : WeightedLedgerGraph n)
    (η ε : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, η i * discrete_laplacian G ε i

/-- The symmetric polar form of the discrete Laplacian action. -/
def laplacian_bilinear {n : ℕ} (G : WeightedLedgerGraph n)
    (ε η : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ i : Fin n, ∑ j : Fin n,
    G.weight i j * (ε i - ε j) * (η i - η j)

/-! ## Finite-sum algebra -/

private theorem right_weighted_sum_eq_neg_left {n : ℕ}
    (G : WeightedLedgerGraph n) (ε η : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
        G.weight i j * (ε i - ε j) * η j)
      =
    -∑ i : Fin n, ∑ j : Fin n,
        G.weight i j * (ε i - ε j) * η i := by
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        G.weight i j * (ε i - ε j) * η j)
        =
      ∑ j : Fin n, ∑ i : Fin n,
        G.weight i j * (ε i - ε j) * η j := by
          rw [Finset.sum_comm]
    _ =
      ∑ i : Fin n, ∑ j : Fin n,
        G.weight j i * (ε j - ε i) * η i := by
          rfl
    _ =
      ∑ i : Fin n, ∑ j : Fin n,
        G.weight i j * (ε j - ε i) * η i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [G.weight_symm]
    _ =
      -∑ i : Fin n, ∑ j : Fin n,
        G.weight i j * (ε i - ε j) * η i := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring

private theorem pairing_eq_left_weighted_sum {n : ℕ}
    (G : WeightedLedgerGraph n) (ε η : Fin n → ℝ) :
    laplacian_pairing G η ε
      =
    ∑ i : Fin n, ∑ j : Fin n,
      G.weight i j * (ε i - ε j) * η i := by
  unfold laplacian_pairing discrete_laplacian
  calc
    (∑ i : Fin n, η i * ∑ j : Fin n,
        G.weight i j * (ε i - ε j))
        =
      ∑ i : Fin n, ∑ j : Fin n,
        η i * (G.weight i j * (ε i - ε j)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
    _ =
      ∑ i : Fin n, ∑ j : Fin n,
        G.weight i j * (ε i - ε j) * η i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring

/-! ## Exact Dirichlet identities -/

/-- The edge polar form is exactly the Laplacian pairing `⟨η, Δε⟩`. -/
theorem laplacian_bilinear_eq_pairing {n : ℕ}
    (G : WeightedLedgerGraph n) (ε η : Fin n → ℝ) :
    laplacian_bilinear G ε η = laplacian_pairing G η ε := by
  unfold laplacian_bilinear
  let L : ℝ :=
    ∑ i : Fin n, ∑ j : Fin n,
      G.weight i j * (ε i - ε j) * η i
  let R : ℝ :=
    ∑ i : Fin n, ∑ j : Fin n,
      G.weight i j * (ε i - ε j) * η j
  have hR : R = -L := by
    dsimp [R, L]
    exact right_weighted_sum_eq_neg_left G ε η
  have hdiff :
      (∑ i : Fin n, ∑ j : Fin n,
        G.weight i j * (ε i - ε j) * (η i - η j)) = 2 * L := by
    calc
      (∑ i : Fin n, ∑ j : Fin n,
        G.weight i j * (ε i - ε j) * (η i - η j))
          = L - R := by
              dsimp [L, R]
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              ring
      _ = 2 * L := by
            rw [hR]
            ring
  calc
    (1 / 2) * ∑ i : Fin n, ∑ j : Fin n,
        G.weight i j * (ε i - ε j) * (η i - η j)
        = L := by
            rw [hdiff]
            ring
    _ = laplacian_pairing G η ε := by
          exact (pairing_eq_left_weighted_sum G ε η).symm

/-- The polar form is symmetric in its two fields. -/
theorem laplacian_bilinear_comm {n : ℕ}
    (G : WeightedLedgerGraph n) (ε η : Fin n → ℝ) :
    laplacian_bilinear G ε η = laplacian_bilinear G η ε := by
  unfold laplacian_bilinear
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- The discrete Laplacian is self-adjoint for the finite pairing. -/
theorem laplacian_pairing_comm {n : ℕ}
    (G : WeightedLedgerGraph n) (ε η : Fin n → ℝ) :
    laplacian_pairing G η ε = laplacian_pairing G ε η := by
  rw [← laplacian_bilinear_eq_pairing G ε η,
    laplacian_bilinear_comm,
    laplacian_bilinear_eq_pairing]

/-- The Dirichlet energy is exactly the Laplacian quadratic pairing. -/
theorem laplacian_action_eq_pairing {n : ℕ}
    (G : WeightedLedgerGraph n) (ε : Fin n → ℝ) :
    laplacian_action G ε = laplacian_pairing G ε ε := by
  calc
    laplacian_action G ε = laplacian_bilinear G ε ε := by
      unfold laplacian_action laplacian_bilinear
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    _ = laplacian_pairing G ε ε :=
      laplacian_bilinear_eq_pairing G ε ε

private theorem double_sum_mul_left {n : ℕ}
    (c : ℝ) (f : Fin n → Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, c * f i j)
      = c * ∑ i : Fin n, ∑ j : Fin n, f i j := by
  calc
    (∑ i : Fin n, ∑ j : Fin n, c * f i j)
        = ∑ i : Fin n, c * ∑ j : Fin n, f i j := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.mul_sum]
    _ = c * ∑ i : Fin n, ∑ j : Fin n, f i j := by
          rw [Finset.mul_sum]

/-- Exact polynomial expansion of the action along the line `ε + tη`.
The linear coefficient is forced to be `2 * ⟨η, Δε⟩` by the action's
ordered-edge normalization. -/
theorem laplacian_action_line_expansion {n : ℕ}
    (G : WeightedLedgerGraph n) (ε η : Fin n → ℝ) (t : ℝ) :
    laplacian_action G (fun i => ε i + t * η i)
      =
    laplacian_action G ε
      + 2 * t * laplacian_pairing G η ε
      + t ^ 2 * laplacian_action G η := by
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n,
        G.weight i j *
          ((ε i + t * η i) - (ε j + t * η j)) ^ 2)
        =
      (∑ i : Fin n, ∑ j : Fin n,
        G.weight i j * (ε i - ε j) ^ 2)
        + 2 * t * (∑ i : Fin n, ∑ j : Fin n,
          G.weight i j * (ε i - ε j) * (η i - η j))
        + t ^ 2 * (∑ i : Fin n, ∑ j : Fin n,
          G.weight i j * (η i - η j) ^ 2) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n,
        G.weight i j *
          ((ε i + t * η i) - (ε j + t * η j)) ^ 2)
          =
        ∑ i : Fin n, ∑ j : Fin n,
          (G.weight i j * (ε i - ε j) ^ 2
            + (2 * t) *
                (G.weight i j * (ε i - ε j) * (η i - η j))
            + t ^ 2 * (G.weight i j * (η i - η j) ^ 2)) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              refine Finset.sum_congr rfl (fun j _ => ?_)
              ring
      _ =
        (∑ i : Fin n, ∑ j : Fin n,
          G.weight i j * (ε i - ε j) ^ 2)
          + (∑ i : Fin n, ∑ j : Fin n,
            (2 * t) *
              (G.weight i j * (ε i - ε j) * (η i - η j)))
          + (∑ i : Fin n, ∑ j : Fin n,
            t ^ 2 * (G.weight i j * (η i - η j) ^ 2)) := by
              simp only [Finset.sum_add_distrib]
      _ =
        (∑ i : Fin n, ∑ j : Fin n,
          G.weight i j * (ε i - ε j) ^ 2)
          + 2 * t * (∑ i : Fin n, ∑ j : Fin n,
            G.weight i j * (ε i - ε j) * (η i - η j))
          + t ^ 2 * (∑ i : Fin n, ∑ j : Fin n,
            G.weight i j * (η i - η j) ^ 2) := by
              rw [double_sum_mul_left (n := n) (c := 2 * t)]
              rw [double_sum_mul_left (n := n) (c := t ^ 2)]
  unfold laplacian_action
  rw [hsum]
  rw [← laplacian_bilinear_eq_pairing G ε η]
  unfold laplacian_bilinear
  ring

/-! ## Unit dipole consequences -/

/-- The unit source at `a` paired with the unit sink at `b`. -/
def unitDipole {n : ℕ} (a b : Fin n) (i : Fin n) : ℝ :=
  (if i = a then 1 else 0) - (if i = b then 1 else 0)

/-- Pairing a field with a unit dipole gives its potential drop. -/
theorem sum_mul_unitDipole {n : ℕ} (ε : Fin n → ℝ) (a b : Fin n) :
    (∑ i : Fin n, ε i * unitDipole a b i) = ε a - ε b := by
  unfold unitDipole
  simp [mul_sub, Finset.sum_sub_distrib]

/-- If the Laplacian is a unit dipole, the action is the potential drop. -/
theorem laplacian_action_eq_potential_drop_of_eq_unitDipole {n : ℕ}
    (G : WeightedLedgerGraph n) (ε : Fin n → ℝ) (a b : Fin n)
    (hsource : ∀ i, discrete_laplacian G ε i = unitDipole a b i) :
    laplacian_action G ε = ε a - ε b := by
  rw [laplacian_action_eq_pairing]
  unfold laplacian_pairing
  calc
    (∑ i : Fin n, ε i * discrete_laplacian G ε i)
        = ∑ i : Fin n, ε i * unitDipole a b i := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [hsource i]
    _ = ε a - ε b := sum_mul_unitDipole ε a b

/-- If twice the Laplacian is a unit dipole, the action is half the
potential drop. This is the alternative normalization exposed by the forced
coefficient `2` in the action variation. -/
theorem laplacian_action_eq_half_potential_drop_of_two_eq_unitDipole {n : ℕ}
    (G : WeightedLedgerGraph n) (ε : Fin n → ℝ) (a b : Fin n)
    (hsource : ∀ i, 2 * discrete_laplacian G ε i = unitDipole a b i) :
    laplacian_action G ε = (ε a - ε b) / 2 := by
  rw [laplacian_action_eq_pairing]
  unfold laplacian_pairing
  have hhalf : ∀ i, discrete_laplacian G ε i = (1 / 2 : ℝ) * unitDipole a b i := by
    intro i
    linarith [hsource i]
  calc
    (∑ i : Fin n, ε i * discrete_laplacian G ε i)
        = ∑ i : Fin n, ε i * ((1 / 2 : ℝ) * unitDipole a b i) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [hhalf i]
    _ = (1 / 2 : ℝ) * ∑ i : Fin n, ε i * unitDipole a b i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
    _ = (ε a - ε b) / 2 := by
          rw [sum_mul_unitDipole]
          ring

end

end ContinuumBridge
end SimplicialLedger
end Foundation
end IndisputableMonolith
