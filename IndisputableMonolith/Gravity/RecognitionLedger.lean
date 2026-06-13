import Mathlib
import IndisputableMonolith.Constants

/-!
# Gravity: The Recognition Ledger

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom).

The recognition ledger is the central bookkeeping structure of recognition
gravity.  It is used in three distinct ways:

1. **Gravitational action.**  The continuum limit of the total ledger cost
   restricted to codimension-2 hinges equals the Regge action.
2. **Page curve.**  The radiation entropy at retarded time u is the von
   Neumann entropy of the reduced state obtained by tracing over cells on
   one side of a horizon boundary.
3. **Vacuum energy.**  The vacuum ledger cost is the ground-state value of
   the total ledger cost over the full substrate lattice.

## Definition

Given a finite substrate lattice Λ (modeled as a `Fintype`), the recognition
ledger is a function

  ℒ : Λ × Λ → [0, ∞)

assigning to each pair of substrate cells (i, j) the accumulated recognition
cost J(x_ij) of the comparison between them.

### Properties

1. **Symmetry:** ℒ(i,j) = ℒ(j,i)
2. **Diagonal zero:** ℒ(i,i) = 0
3. **Non-negative:** ℒ(i,j) ≥ 0 (by definition of the codomain)
4. **RCL subadditivity:** ℒ(i,k) ≤ R(ℒ(i,j), ℒ(j,k)) for every
   intermediate cell j, where R(u,v) = 2uv + 2u + 2v is the forced gate.

### Derived quantities

- **Total ledger cost:** Σ_{i,j} ℒ(i,j)
- **Ledger deficit at cell i:** Δ_i = Σ_j ℒ(i,j)
- **Flatness:** A ledger is flat iff ℒ(i,j) = 0 for all i, j.
-/

namespace IndisputableMonolith
namespace Gravity
namespace RecognitionLedger

open Constants

/-! ## §1. The RCL gate function -/

/-- The forced gate R(u,v) = 2uv + 2u + 2v, as proved in
`Foundation.DAlembert.FactorizationForcing.gate_forces_rcl`. -/
noncomputable def rclGate (u v : ℝ) : ℝ := 2 * u * v + 2 * u + 2 * v

theorem rclGate_symmetric (u v : ℝ) : rclGate u v = rclGate v u := by
  unfold rclGate; ring

theorem rclGate_zero_right (u : ℝ) : rclGate u 0 = 2 * u := by
  unfold rclGate; ring

theorem rclGate_zero_left (v : ℝ) : rclGate 0 v = 2 * v := by
  unfold rclGate; ring

theorem rclGate_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ rclGate u v := by
  unfold rclGate
  nlinarith

/-! ## §2. The recognition ledger structure -/

/-- A recognition ledger on a finite substrate lattice `Λ`. -/
structure RecognitionLedger (Λ : Type*) [Fintype Λ] [DecidableEq Λ] where
  /-- The cost function assigning recognition cost to each cell pair. -/
  cost : Λ → Λ → ℝ
  /-- Symmetry: ℒ(i,j) = ℒ(j,i). -/
  symmetric : ∀ i j, cost i j = cost j i
  /-- Diagonal zero: a cell has zero cost of comparison with itself. -/
  diagonal_zero : ∀ i, cost i i = 0
  /-- Non-negativity: all costs are non-negative. -/
  nonneg : ∀ i j, 0 ≤ cost i j
  /-- RCL subadditivity: the cost from i to k is bounded by the RCL gate
  applied to the costs from i to j and j to k, for every intermediate j. -/
  rcl_subadditive : ∀ i j k, cost i k ≤ rclGate (cost i j) (cost j k)

/-! ## §3. The flat ledger -/

/-- The flat (zero) ledger on any finite lattice. -/
def flatLedger (Λ : Type*) [Fintype Λ] [DecidableEq Λ] : RecognitionLedger Λ where
  cost := fun _ _ => 0
  symmetric := fun _ _ => rfl
  diagonal_zero := fun _ => rfl
  nonneg := fun _ _ => le_refl 0
  rcl_subadditive := fun _ _ _ => by unfold rclGate; norm_num

/-- A ledger is flat iff every cost is zero. -/
def isFlat {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (L : RecognitionLedger Λ) : Prop :=
  ∀ i j, L.cost i j = 0

theorem flatLedger_isFlat (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    isFlat (flatLedger Λ) :=
  fun _ _ => rfl

/-! ## §4. Total ledger cost -/

/-- The total ledger cost: sum of all pairwise costs. -/
noncomputable def totalCost {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger Λ) : ℝ :=
  ∑ i, ∑ j, L.cost i j

/-- The total cost is non-negative. -/
theorem totalCost_nonneg {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger Λ) : 0 ≤ totalCost L := by
  unfold totalCost
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact L.nonneg i j

/-- The total cost vanishes iff the ledger is flat. -/
theorem totalCost_eq_zero_iff_flat {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger Λ) : totalCost L = 0 ↔ isFlat L := by
  constructor
  · intro h0
    unfold isFlat
    intro i j
    unfold totalCost at h0
    have hsums : ∀ x ∈ Finset.univ, ∑ y : Λ, L.cost x y = 0 := by
      rwa [Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => Finset.sum_nonneg (fun y _ => L.nonneg x y))] at h0
    have h0i := hsums i (Finset.mem_univ i)
    have hsumj : ∀ y ∈ Finset.univ, L.cost i y = 0 := by
      rwa [Finset.sum_eq_zero_iff_of_nonneg (fun y _ => L.nonneg i y)] at h0i
    exact hsumj j (Finset.mem_univ j)
  · intro hf
    unfold totalCost
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    exact hf i j

/-- The flat ledger has zero total cost. -/
theorem flatLedger_totalCost_zero (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    totalCost (flatLedger Λ) = 0 :=
  (totalCost_eq_zero_iff_flat _).mpr (flatLedger_isFlat Λ)

/-! ## §5. Ledger deficit at a cell -/

/-- The ledger deficit at cell i: total cost of comparison with all cells. -/
noncomputable def deficit {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger Λ) (i : Λ) : ℝ :=
  ∑ j, L.cost i j

/-- The deficit is non-negative. -/
theorem deficit_nonneg {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger Λ) (i : Λ) : 0 ≤ deficit L i := by
  unfold deficit
  apply Finset.sum_nonneg
  intro j _
  exact L.nonneg i j

/-- Total cost is the sum of deficits. -/
theorem totalCost_eq_sum_deficits {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger Λ) : totalCost L = ∑ i, deficit L i :=
  rfl

/-! ## §6. Boundary and ledger entropy -/

/-- A partition of a substrate into two complementary regions.  The
boundary is the interface between them.  In the gravitational context,
this partition represents a horizon. -/
structure SubstrateBipartition (Λ : Type*) [Fintype Λ] [DecidableEq Λ] where
  interior : Finset Λ
  exterior : Finset Λ
  partition_complete : interior ∪ exterior = Finset.univ
  partition_disjoint : Disjoint interior exterior

/-- The boundary cost of a bipartition: sum of costs between interior
and exterior cells.  This is the ledger analogue of the boundary term
in the gravitational action. -/
noncomputable def boundaryCost {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger Λ) (P : SubstrateBipartition Λ) : ℝ :=
  ∑ i ∈ P.interior, ∑ j ∈ P.exterior, L.cost i j

/-- Boundary cost is non-negative. -/
theorem boundaryCost_nonneg {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger Λ) (P : SubstrateBipartition Λ) :
    0 ≤ boundaryCost L P := by
  unfold boundaryCost
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact L.nonneg i j

/-- Boundary cost is symmetric: exchanging interior and exterior gives
the same boundary cost. -/
theorem boundaryCost_symmetric {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger Λ) (P : SubstrateBipartition Λ) :
    boundaryCost L P =
    ∑ j ∈ P.exterior, ∑ i ∈ P.interior, L.cost j i := by
  unfold boundaryCost
  rw [Finset.sum_comm]
  congr 1; ext j
  congr 1; ext i
  exact L.symmetric i j

/-! ## §7. Master cert -/

structure RecognitionLedgerCert where
  flat_exists : ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ],
    Nonempty (RecognitionLedger Λ)
  flat_total_zero : ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ],
    totalCost (flatLedger Λ) = 0
  total_nonneg : ∀ {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger Λ), 0 ≤ totalCost L
  zero_iff_flat : ∀ {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger Λ), totalCost L = 0 ↔ isFlat L

def recognitionLedgerCert : RecognitionLedgerCert where
  flat_exists := fun Λ _ _ => ⟨flatLedger Λ⟩
  flat_total_zero := fun Λ _ _ => flatLedger_totalCost_zero Λ
  total_nonneg := fun L => totalCost_nonneg L
  zero_iff_flat := fun L => totalCost_eq_zero_iff_flat L

theorem recognitionLedgerCert_inhabited :
    Nonempty RecognitionLedgerCert :=
  ⟨recognitionLedgerCert⟩

/-- **RECOGNITION LEDGER ONE-STATEMENT.**  The recognition ledger is a
symmetric, diagonal-zero, non-negative cost function on a finite lattice
satisfying RCL subadditivity.  Its total cost is non-negative and vanishes
iff the lattice is flat (Minkowski).  The flat ledger exists on any lattice.
Bipartition boundary costs are non-negative and symmetric under exchange.  -/
theorem recognition_ledger_one_statement :
    (∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ],
      Nonempty (RecognitionLedger Λ)) ∧
    (∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ],
      totalCost (flatLedger Λ) = 0) ∧
    (∀ {Λ : Type} [Fintype Λ] [DecidableEq Λ]
      (L : RecognitionLedger Λ), 0 ≤ totalCost L) ∧
    (∀ {Λ : Type} [Fintype Λ] [DecidableEq Λ]
      (L : RecognitionLedger Λ), totalCost L = 0 ↔ isFlat L) :=
  ⟨fun Λ _ _ => ⟨flatLedger Λ⟩,
   fun Λ _ _ => flatLedger_totalCost_zero Λ,
   fun L => totalCost_nonneg L,
   fun L => totalCost_eq_zero_iff_flat L⟩

end RecognitionLedger
end Gravity
end IndisputableMonolith
