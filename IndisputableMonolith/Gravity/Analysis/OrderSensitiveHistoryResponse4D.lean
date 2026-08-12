import Mathlib
import IndisputableMonolith.Loom.Separation
import IndisputableMonolith.Gravity.Analysis.ClassicalSourceProjection
import IndisputableMonolith.Gravity.Analysis.Q3PatchSeating
import IndisputableMonolith.Gravity.Analysis.MetricEdgeImage4D

/-!
# Order-sensitive history → edge-current response on the Freudenthal patch

Frozen claims G2/G3 of
`holography/plans/OrderSensitive_Gravity_Proposition_20260802.html`.

The response is built from the depth-two commutator reading of a Loom
`Config` (the same second-order content `Core.pairTraces` /
`HolonomyExpansion.pairSum` isolate). The reading is seated as an
antisymmetric Fin 16 edge current on the generator-(0,2) edge at
record-time false via `Q3PatchSeating`. No metric `H`, no `muCoord` table.

## Honesty

* THEOREM: separation, action firing, metric-image exclusion on cfgA/cfgB.
* MODEL: treating the depth-two fingerprint amplitude as a physical current.
* Scope of outside-image: not a linearized flat-patch metric perturbation.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace OrderSensitiveHistoryResponse4D

open IndisputableMonolith.Loom
open IndisputableMonolith.Loom.Certificate
open ClassicalSourceProjection
open Q3PatchSeating
open MetricEdgeImage4D
open BigOperators

noncomputable section

/-- Polynomial fingerprint of a Nat list. -/
def listFingerprint (l : List Nat) : Nat :=
  l.foldl (fun a x => a * 17 + x) 0

def antisymEdge (a b : Fin 16) (amp : ℝ) : Fin 16 → Fin 16 → ℝ :=
  fun i j =>
    if i = a ∧ j = b then amp
    else if i = b ∧ j = a then -amp
    else 0

/-- Generator-1 endpoints `(0,2)` seated at record-time false (`Loom.gen₁`). -/
def seatGen1 : Fin 16 × Fin 16 :=
  (seat (fun _ => false) false, seat (fun i => i = (1 : Fin 3)) false)

/-- History response from depth-two reading. -/
def historyResponse (c : Config) : Fin 16 → Fin 16 → ℝ :=
  antisymEdge seatGen1.1 seatGen1.2 (listFingerprint (depthTwoReading c) : ℝ)

def responseDiff (c₁ c₂ : Config) : Fin 16 → Fin 16 → ℝ :=
  fun i j => historyResponse c₁ i j - historyResponse c₂ i j

/-- Local edge-current first variation (matches FreudenthalCoverEdgeCurrentAction4D). -/
def edgeCurrentFirstVariation (weight F VF : Fin 16 → Fin 16 → ℝ) : ℝ :=
  ∑ i, ∑ j, weight i j * Real.sinh (F i j) * VF i j

def diracProbe (a b : Fin 16) : Fin 16 → Fin 16 → ℝ :=
  fun i j => if i = a ∧ j = b then (1 : ℝ) else 0

def unitWeight : Fin 16 → Fin 16 → ℝ := fun _ _ => 1

theorem seatGen1_ne : seatGen1.1 ≠ seatGen1.2 := by
  change (0 : Fin 16) ≠ 2
  decide

theorem antisymEdge_fwd (a b : Fin 16) (amp : ℝ) (h : a ≠ b) :
    antisymEdge a b amp a b = amp := by
  unfold antisymEdge; simp [h]

theorem antisymEdge_rev (a b : Fin 16) (amp : ℝ) (h : a ≠ b) :
    antisymEdge a b amp b a = -amp := by
  unfold antisymEdge; simp [h, Ne.symm h]

theorem historyResponse_fwd (c : Config) :
    historyResponse c seatGen1.1 seatGen1.2 =
      (listFingerprint (depthTwoReading c) : ℝ) := by
  unfold historyResponse
  exact antisymEdge_fwd _ _ _ seatGen1_ne

theorem historyResponse_rev (c : Config) :
    historyResponse c seatGen1.2 seatGen1.1 =
      -((listFingerprint (depthTwoReading c) : ℝ)) := by
  unfold historyResponse
  exact antisymEdge_rev _ _ _ seatGen1_ne

theorem fingerprint_separates_cfgAB :
    listFingerprint (depthTwoReading cfgA) ≠
      listFingerprint (depthTwoReading cfgB) := by
  decide

theorem historyResponse_separates_cfgAB :
    historyResponse cfgA ≠ historyResponse cfgB := by
  intro h
  have := congrFun (congrFun h seatGen1.1) seatGen1.2
  rw [historyResponse_fwd, historyResponse_fwd] at this
  exact fingerprint_separates_cfgAB (Nat.cast_injective this)

theorem finiteCertificate_cfgAB :
    depthOneSource cfgA = depthOneSource cfgB ∧
      historyResponse cfgA ≠ historyResponse cfgB :=
  ⟨depth_one_is_blind, historyResponse_separates_cfgAB⟩

theorem edgeCurrentFirstVariation_dirac (weight F : Fin 16 → Fin 16 → ℝ)
    (a b : Fin 16) :
    edgeCurrentFirstVariation weight F (diracProbe a b) =
      weight a b * Real.sinh (F a b) := by
  unfold edgeCurrentFirstVariation diracProbe
  have houter : ∀ i ∈ (Finset.univ : Finset (Fin 16)), i ≠ a →
      (∑ j, weight i j * Real.sinh (F i j) *
        (if i = a ∧ j = b then (1 : ℝ) else 0)) = 0 := by
    intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (fun h => hi h.1), mul_zero]
  rw [Finset.sum_eq_single a houter (fun h => absurd (Finset.mem_univ a) h)]
  have hinner : ∀ j ∈ (Finset.univ : Finset (Fin 16)), j ≠ b →
      weight a j * Real.sinh (F a j) *
        (if a = a ∧ j = b then (1 : ℝ) else 0) = 0 := by
    intro j _ hj
    rw [if_neg (fun h => hj h.2), mul_zero]
  rw [Finset.sum_eq_single b hinner (fun h => absurd (Finset.mem_univ b) h)]
  simp

theorem edgeAction_separates_cfgAB :
    edgeCurrentFirstVariation unitWeight (historyResponse cfgA)
        (diracProbe seatGen1.1 seatGen1.2) ≠
      edgeCurrentFirstVariation unitWeight (historyResponse cfgB)
        (diracProbe seatGen1.1 seatGen1.2) := by
  rw [edgeCurrentFirstVariation_dirac, edgeCurrentFirstVariation_dirac,
    historyResponse_fwd, historyResponse_fwd]
  simp only [unitWeight, one_mul]
  intro hEq
  exact fingerprint_separates_cfgAB (Nat.cast_injective (Real.sinh_inj.mp hEq))

theorem responseDiff_fwd :
    responseDiff cfgA cfgB seatGen1.1 seatGen1.2 =
      (listFingerprint (depthTwoReading cfgA) : ℝ) -
        (listFingerprint (depthTwoReading cfgB) : ℝ) := by
  simp [responseDiff, historyResponse_fwd]

theorem responseDiff_rev :
    responseDiff cfgA cfgB seatGen1.2 seatGen1.1 =
      -responseDiff cfgA cfgB seatGen1.1 seatGen1.2 := by
  simp [responseDiff, historyResponse_rev, historyResponse_fwd]
  ring

theorem responseDiff_fwd_ne :
    responseDiff cfgA cfgB seatGen1.1 seatGen1.2 ≠ 0 := by
  rw [responseDiff_fwd]
  have h := fingerprint_separates_cfgAB
  exact sub_ne_zero.mpr (fun hEq => h (Nat.cast_injective hEq))

theorem responseDiff_cfgAB_not_in_MetricEdgeImage :
    ¬ MetricEdgeImage (responseDiff cfgA cfgB) := by
  rintro ⟨H, hF⟩
  have h0 := congrFun (congrFun hF seatGen1.1) seatGen1.2
  have h1 := congrFun (congrFun hF seatGen1.2) seatGen1.1
  have hsym := strainCurrent_symm H seatGen1.1 seatGen1.2
  have hanti := responseDiff_rev
  have hne := responseDiff_fwd_ne
  have : responseDiff cfgA cfgB seatGen1.1 seatGen1.2 =
      responseDiff cfgA cfgB seatGen1.2 seatGen1.1 := by
    calc
      responseDiff cfgA cfgB seatGen1.1 seatGen1.2
          = strainCurrent H seatGen1.1 seatGen1.2 := h0
      _ = strainCurrent H seatGen1.2 seatGen1.1 := hsym
      _ = responseDiff cfgA cfgB seatGen1.2 seatGen1.1 := h1.symm
  rw [hanti] at this
  have : responseDiff cfgA cfgB seatGen1.1 seatGen1.2 = 0 := by linarith
  exact hne this

theorem decoy_depthOne_blind : depthOneSource cfgA = depthOneSource cfgB :=
  depth_one_is_blind

theorem discovery_pair_is_certificate_cfgAB :
    depthTwoReading cfgA ≠ depthTwoReading cfgB :=
  depth_two_separates

theorem orderSensitive_finite_gate_cfgAB :
    depthOneSource cfgA = depthOneSource cfgB ∧
      historyResponse cfgA ≠ historyResponse cfgB ∧
      ¬ MetricEdgeImage (responseDiff cfgA cfgB) :=
  ⟨depth_one_is_blind, historyResponse_separates_cfgAB,
    responseDiff_cfgAB_not_in_MetricEdgeImage⟩

end

end OrderSensitiveHistoryResponse4D
end Analysis
end Gravity
end IndisputableMonolith
