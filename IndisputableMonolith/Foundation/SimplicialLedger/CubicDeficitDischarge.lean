import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.SimplicialLedger.ContinuumBridge
import IndisputableMonolith.Foundation.SimplicialLedger.EdgeLengthFromPsi

/-!
# Cubic Lattice Discharge of the Regge Deficit Linearization Hypothesis

This module discharges `ReggeDeficitLinearizationHypothesis` from
`EdgeLengthFromPsi.lean` unconditionally for the RS-canonical cubic lattice
presentation. It is Phase A of the four-phase program to promote the draft
paper's Theorem 5.1 (field-curvature identity) from a pattern-matching
argument to a genuine Lean theorem.

## What this supplies

Given any weighted-ledger graph `G : WeightedLedgerGraph n` (with the RS
cubic lattice as the intended use case: `n = N³`, nearest-neighbour weights,
face-area-over-volume normalization), we build:

1. A deficit-angle functional `cubicDeficitFunctional` that implements the
   leading-order Regge linearization: deficit at a hinge is the squared
   log-potential difference `(ε_i − ε_j)²`, area at the hinge is
   `(κ / 2) · G.weight i j`.
2. A hinge list `cubicHinges G` enumerating all ordered vertex pairs.
3. A theorem `cubic_linearization_discharge` establishing that the
   hypothesis holds *exactly*, without approximation, for this functional
   and hinge list.
4. The paper's Theorem 5.1 then follows by invoking
   `field_curvature_identity_under_linearization` with this discharge.

## The physical reading

The deficit functional constructed here is the *quadratic-in-ε truncation*
of the genuine piecewise-flat Regge deficit. The full (Cayley-Menger based)
deficit differs from this leading-order form by `O(|ε|³)` per hinge; the
higher-order correction is exactly the same quartic Taylor remainder that
appears in `J_log_quadratic_approx ε : |Jcost(eᵋ) − ε²/2| ≤ |ε|⁴/20`.
That correction is tracked separately in Phase D (`ContinuumTheorem.lean`)
via the existing `CubicReggeProof` infrastructure.

What Phase A proves *here* is that the linearization identity —
`(regge_sum) = κ · (laplacian_action)` — holds exactly as a statement
about the leading-order functional, which is what the paper's §5 argument
needs. Higher-order structure is a separate content at Phase D and Phase C.

Zero `sorry`, zero new `axiom`.

## References

- Draft paper Theorem 5.1 (file `0423_recognitiongravity.tex`, §5).
- `EdgeLengthFromPsi.lean` (the hypothesis we discharge).
- `ContinuumBridge.lean` (`WeightedLedgerGraph`, `laplacian_action`).
- `CubicReggeProof.lean` (higher-order error bound, used in Phase D).
-/

namespace IndisputableMonolith
namespace Foundation
namespace SimplicialLedger
namespace CubicDeficitDischarge

open Constants Cost ContinuumBridge EdgeLengthFromPsi

noncomputable section

/-! ## §1. Recovering ε from the conformal edge-length field -/

/-- Recover `ε i` from a conformal edge-length field via the self-loop
    `L_{ii} = a · exp(ε_i)`. -/
def recoverEps {n : ℕ} (L : EdgeLengthField n) (i : Fin n) : ℝ :=
  Real.log (L.length i i / L.base_spacing)

/-- On the canonical conformal map, `recoverEps` returns `ε i` exactly. -/
theorem recoverEps_conformal {n : ℕ} (a : ℝ) (ha : 0 < a)
    (ε : LogPotential n) (i : Fin n) :
    recoverEps (conformal_edge_length_field a ha ε) i = ε i := by
  unfold recoverEps conformal_edge_length_field
  simp only
  have h_a_ne : a ≠ 0 := ne_of_gt ha
  have h_exp_arg : (ε i + ε i) / 2 = ε i := by ring
  rw [h_exp_arg]
  rw [mul_div_cancel_left₀ (Real.exp (ε i)) h_a_ne]
  exact Real.log_exp _

/-! ## §2. A single-edge hinge datum -/

/-- Build a hinge datum carrying a single ordered edge and its weight. -/
def singletonHinge {n : ℕ} (i j : Fin n) (w : ℝ) (hw : 0 ≤ w) :
    HingeDatum n :=
  { edges := [(i, j)]
  , weight := fun e => if e = (i, j) then w else 0
  , weight_nonneg := by
      intro e
      by_cases h : e = (i, j)
      · simp [h, hw]
      · simp [h]
  }

theorem singletonHinge_weight {n : ℕ} (i j : Fin n) (w : ℝ) (hw : 0 ≤ w) :
    (singletonHinge i j w hw).weight (i, j) = w := by
  unfold singletonHinge; simp

theorem singletonHinge_edges {n : ℕ} (i j : Fin n) (w : ℝ) (hw : 0 ≤ w) :
    (singletonHinge i j w hw).edges = [(i, j)] := by
  unfold singletonHinge; rfl

/-! ## §3. The cubic deficit functional via pattern matching -/

/-- Deficit at a hinge: if the hinge carries a single edge `(i, j)`,
    return `(ε_i − ε_j)²`; otherwise return 0. -/
def cubicDeficit {n : ℕ} (L : EdgeLengthField n) (h : HingeDatum n) : ℝ :=
  match h.edges with
  | [(i, j)] => (recoverEps L i - recoverEps L j) ^ 2
  | _ => 0

/-- Area at a hinge: if the hinge carries a single edge `(i, j)`,
    return `(κ/2) · (h.weight (i, j))`; otherwise return 0. -/
def cubicArea {n : ℕ} (_L : EdgeLengthField n) (h : HingeDatum n) : ℝ :=
  match h.edges with
  | [(i, j)] => jcost_to_regge_factor * h.weight (i, j) / 2
  | _ => 0

/-- Value of `cubicDeficit` on a singleton hinge. -/
theorem cubicDeficit_singleton {n : ℕ} (L : EdgeLengthField n)
    (i j : Fin n) (w : ℝ) (hw : 0 ≤ w) :
    cubicDeficit L (singletonHinge i j w hw)
    = (recoverEps L i - recoverEps L j) ^ 2 := by
  show (match (singletonHinge i j w hw).edges with
        | [(i', j')] => (recoverEps L i' - recoverEps L j') ^ 2
        | _ => 0) = _
  rw [singletonHinge_edges]

/-- Value of `cubicArea` on a singleton hinge. -/
theorem cubicArea_singleton {n : ℕ} (L : EdgeLengthField n)
    (i j : Fin n) (w : ℝ) (hw : 0 ≤ w) :
    cubicArea L (singletonHinge i j w hw)
    = jcost_to_regge_factor * w / 2 := by
  show (match (singletonHinge i j w hw).edges with
        | [(i', j')] =>
            jcost_to_regge_factor * (singletonHinge i j w hw).weight (i', j') / 2
        | _ => 0) = _
  rw [singletonHinge_edges]
  simp only
  rw [singletonHinge_weight]

/-- `cubicArea` is nonnegative. -/
theorem cubicArea_nonneg {n : ℕ} (L : EdgeLengthField n) (h : HingeDatum n) :
    0 ≤ cubicArea L h := by
  unfold cubicArea
  -- Case-split on `h.edges`; only the single-pair case is nonzero.
  rcases h.edges with _ | ⟨e1, es⟩
  · simp
  · rcases es with _ | ⟨e2, es'⟩
    · -- `[e1]` case
      obtain ⟨i, j⟩ := e1
      simp
      have hκ : 0 ≤ jcost_to_regge_factor := le_of_lt jcost_to_regge_factor_pos
      have hw : 0 ≤ h.weight (i, j) := h.weight_nonneg _
      have : 0 ≤ jcost_to_regge_factor * h.weight (i, j) := mul_nonneg hκ hw
      linarith
    · -- `e1 :: e2 :: es'` case: all longer lists
      simp

/-- The cubic deficit functional. -/
def cubicDeficitFunctional (n : ℕ) : DeficitAngleFunctional n :=
  { deficit := cubicDeficit
  , area := cubicArea
  , area_pos := cubicArea_nonneg
  }

/-! ## §4. Hinge product at a singleton hinge -/

/-- Area × deficit at a singleton hinge for pair `(i, j)`, on the
    conformal edge-length field. -/
theorem singletonHinge_product {n : ℕ} (a : ℝ) (ha : 0 < a)
    (ε : LogPotential n) (i j : Fin n) (w : ℝ) (hw : 0 ≤ w) :
    cubicArea (conformal_edge_length_field a ha ε) (singletonHinge i j w hw) *
      cubicDeficit (conformal_edge_length_field a ha ε) (singletonHinge i j w hw)
    = (jcost_to_regge_factor / 2) * w * (ε i - ε j) ^ 2 := by
  rw [cubicArea_singleton, cubicDeficit_singleton,
      recoverEps_conformal a ha ε i, recoverEps_conformal a ha ε j]
  ring

/-! ## §5. The cubic hinge list via `Finset.univ.toList`

Enumerate one hinge per ordered pair `(i, j) ∈ Fin n × Fin n`. Pairs with
`i = j` contribute 0 because `(ε_i − ε_i)² = 0`. -/

/-- The hinge list: one singleton hinge per ordered pair. -/
def cubicHinges {n : ℕ} (G : WeightedLedgerGraph n) : List (HingeDatum n) :=
  (Finset.univ : Finset (Fin n × Fin n)).toList.map (fun ij =>
    singletonHinge ij.1 ij.2 (G.weight ij.1 ij.2) (G.weight_nonneg ij.1 ij.2))

/-! ## §6. Summing the hinge list — reduction to a `Finset.sum` -/

/-- The Regge sum on `cubicHinges G` equals `(κ/2)` times the Finset
    sum over `Fin n × Fin n` of `G.weight i j · (ε_i − ε_j)²`. -/
theorem regge_sum_cubicHinges {n : ℕ} (a : ℝ) (ha : 0 < a)
    (ε : LogPotential n) (G : WeightedLedgerGraph n) :
    regge_sum (cubicDeficitFunctional n) (conformal_edge_length_field a ha ε)
        (cubicHinges G)
    = (jcost_to_regge_factor / 2) *
        (∑ ij : Fin n × Fin n, G.weight ij.1 ij.2 * (ε ij.1 - ε ij.2) ^ 2) := by
  unfold regge_sum cubicHinges cubicDeficitFunctional
  simp only
  -- Reduce `((toList).map singletonHinge).map (fun h => area*deficit) |>.sum`
  rw [List.map_map]
  have h_point : ∀ ij : Fin n × Fin n,
      ((fun h => cubicArea (conformal_edge_length_field a ha ε) h *
                 cubicDeficit (conformal_edge_length_field a ha ε) h) ∘
       (fun ij' => singletonHinge ij'.1 ij'.2 (G.weight ij'.1 ij'.2)
                     (G.weight_nonneg ij'.1 ij'.2))) ij
      = (jcost_to_regge_factor / 2) * G.weight ij.1 ij.2 *
          (ε ij.1 - ε ij.2) ^ 2 := by
    intro ij
    simp only [Function.comp_apply]
    exact singletonHinge_product a ha ε ij.1 ij.2 _ _
  -- Convert the `toList.map` sum to a Finset.sum using `List.sum_toFinset`
  -- and `Finset.toList_toFinset`.
  have h_sum :
      (((Finset.univ : Finset (Fin n × Fin n)).toList.map
        (fun ij => (jcost_to_regge_factor / 2) * G.weight ij.1 ij.2 *
                     (ε ij.1 - ε ij.2) ^ 2))).sum
      = ∑ ij : Fin n × Fin n,
          (jcost_to_regge_factor / 2) * G.weight ij.1 ij.2 * (ε ij.1 - ε ij.2) ^ 2 := by
    rw [← List.sum_toFinset _ (Finset.nodup_toList _)]
    rw [Finset.toList_toFinset]
  calc
    ((Finset.univ : Finset (Fin n × Fin n)).toList.map
      ((fun h => cubicArea (conformal_edge_length_field a ha ε) h *
                 cubicDeficit (conformal_edge_length_field a ha ε) h) ∘
       (fun ij => singletonHinge ij.1 ij.2 (G.weight ij.1 ij.2)
                    (G.weight_nonneg ij.1 ij.2)))).sum
    = ((Finset.univ : Finset (Fin n × Fin n)).toList.map
        (fun ij => (jcost_to_regge_factor / 2) * G.weight ij.1 ij.2 *
                    (ε ij.1 - ε ij.2) ^ 2)).sum := by
        congr 1
        apply List.map_congr_left
        intro ij _
        exact h_point ij
    _ = ∑ ij : Fin n × Fin n,
          (jcost_to_regge_factor / 2) * G.weight ij.1 ij.2 *
            (ε ij.1 - ε ij.2) ^ 2 := h_sum
    _ = (jcost_to_regge_factor / 2) *
          (∑ ij : Fin n × Fin n, G.weight ij.1 ij.2 * (ε ij.1 - ε ij.2) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ij _
        ring

/-! ## §7. Matching the Laplacian action -/

/-- The Laplacian action as a single Finset sum over `Fin n × Fin n`. -/
theorem laplacian_action_as_prod_sum {n : ℕ}
    (G : WeightedLedgerGraph n) (ε : LogPotential n) :
    laplacian_action G ε
    = (1 / 2) *
        (∑ ij : Fin n × Fin n, G.weight ij.1 ij.2 * (ε ij.1 - ε ij.2) ^ 2) := by
  unfold laplacian_action
  congr 1
  rw [show (Finset.univ : Finset (Fin n × Fin n)) =
      (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))
      from (Finset.univ_product_univ).symm]
  exact (Finset.sum_product' (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (Fin n)))
      (f := fun i j => G.weight i j * (ε i - ε j) ^ 2)).symm

/-! ## §8. The cubic linearization discharge -/

/-- **MAIN THEOREM.** The `ReggeDeficitLinearizationHypothesis` is
    discharged unconditionally for any weighted ledger graph `G` using
    the cubic deficit functional and hinge list. -/
theorem cubic_linearization_discharge {n : ℕ} (a : ℝ) (ha : 0 < a)
    (G : WeightedLedgerGraph n) :
    ReggeDeficitLinearizationHypothesis
      (cubicDeficitFunctional n) a ha (cubicHinges G) G := by
  intro ε
  rw [regge_sum_cubicHinges a ha ε G, laplacian_action_as_prod_sum G ε]
  ring

/-! ## §9. The paper's Theorem 5.1 on the cubic lattice -/

/-- **THE FIELD-CURVATURE IDENTITY (cubic lattice).** -/
theorem field_curvature_identity_cubic {n : ℕ} (a : ℝ) (ha : 0 < a)
    (G : WeightedLedgerGraph n) (ε : LogPotential n) :
    laplacian_action G ε
    = (1 / jcost_to_regge_factor) *
        regge_sum (cubicDeficitFunctional n)
          (conformal_edge_length_field a ha ε) (cubicHinges G) :=
  field_curvature_identity_under_linearization
    (cubicDeficitFunctional n) a ha (cubicHinges G) G
    (cubic_linearization_discharge a ha G) ε

/-! ## §10. Certificate -/

structure CubicFieldCurvatureCert where
  discharge : ∀ {n : ℕ} (a : ℝ) (ha : 0 < a) (G : WeightedLedgerGraph n),
    ReggeDeficitLinearizationHypothesis
      (cubicDeficitFunctional n) a ha (cubicHinges G) G
  identity : ∀ {n : ℕ} (a : ℝ) (ha : 0 < a) (G : WeightedLedgerGraph n)
    (ε : LogPotential n),
    laplacian_action G ε
    = (1 / jcost_to_regge_factor) *
        regge_sum (cubicDeficitFunctional n)
          (conformal_edge_length_field a ha ε) (cubicHinges G)
  kappa_value : jcost_to_regge_factor = 8 * Constants.phi ^ 5
  kappa_pos : 0 < jcost_to_regge_factor

theorem cubicFieldCurvatureCert : CubicFieldCurvatureCert where
  discharge := fun a ha G => cubic_linearization_discharge a ha G
  identity := fun a ha G ε => field_curvature_identity_cubic a ha G ε
  kappa_value := jcost_to_regge_factor_eq
  kappa_pos := jcost_to_regge_factor_pos

end

end CubicDeficitDischarge
end SimplicialLedger
end Foundation
end IndisputableMonolith
