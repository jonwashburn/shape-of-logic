import IndisputableMonolith.Geometry.FreudenthalCubeTriangulation
import IndisputableMonolith.Geometry.SchlaefliTetrahedronProof

/-!
# Freudenthal length-chain Schläfli summand certificates

Full `6 × 6` evaluation of `schlaefliPolySummandNorm` at `freudenthalTetSqEdges`, and the
induced closed-form `dihedralClosedDerivLength` table for
`freudenthalLocalPairClosedFormSchlaefliCoeff`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace FreudenthalLengthChainEndpointCert

open Geometry
open CayleyMengerPolynomial
open FreudenthalCubeTriangulation
open SchlaefliTetrahedronProof

set_option maxHeartbeats 20000000

/-- Evaluated rationalized Schläfli summand table at `freudenthalTetSqEdges`. -/
def freudenthalSchlaefliPolySummandNormTable : Fin 6 → Fin 6 → ℝ
  | e, k =>
      match e, k with
      | 0, 0 => 0
      | 0, 1 => 0
      | 0, 2 => 0
      | 0, 3 => 0
      | 0, 4 => -1
      | 0, 5 => 2
      | 1, 0 => 0
      | 1, 1 => 2
      | 1, 2 => -2
      | 1, 3 => -4
      | 1, 4 => 4
      | 1, 5 => -2
      | 2, 0 => 0
      | 2, 1 => -3
      | 2, 2 => 2
      | 2, 3 => 6
      | 2, 4 => -3
      | 2, 5 => 0
      | 3, 0 => 0
      | 3, 1 => -2
      | 3, 2 => 2
      | 3, 3 => 2
      | 3, 4 => -2
      | 3, 5 => 0
      | 4, 0 => -2
      | 4, 1 => 4
      | 4, 2 => -2
      | 4, 3 => -4
      | 4, 4 => 2
      | 4, 5 => 0
      | 5, 0 => 2
      | 5, 1 => -1
      | 5, 2 => 0
      | 5, 3 => 0
      | 5, 4 => 0
      | 5, 5 => 0

theorem snorm_zero_0_0 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 0 0 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_zero_0_1 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 0 1 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_zero_0_2 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 0 2 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_zero_0_3 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 0 3 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_0_4 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 0 4 = -1 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_0_5 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 0 5 = 2 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_zero_1_0 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 1 0 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_1_1 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 1 1 = 2 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_1_2 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 1 2 = -2 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_1_3 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 1 3 = -4 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_1_4 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 1 4 = 4 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_1_5 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 1 5 = -2 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_zero_2_0 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 2 0 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_2_1 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 2 1 = -3 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_2_2 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 2 2 = 2 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_2_3 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 2 3 = 6 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_2_4 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 2 4 = -3 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_zero_2_5 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 2 5 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_zero_3_0 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 3 0 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_3_1 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 3 1 = -2 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_3_2 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 3 2 = 2 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_3_3 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 3 3 = 2 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_3_4 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 3 4 = -2 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_zero_3_5 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 3 5 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_4_0 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 4 0 = -2 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_4_1 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 4 1 = 4 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_4_2 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 4 2 = -2 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_4_3 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 4 3 = -4 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_4_4 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 4 4 = 2 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_zero_4_5 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 4 5 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_5_0 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 5 0 = 2 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_5_1 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 5 1 = -1 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_zero_5_2 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 5 2 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_zero_5_3 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 5 3 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_zero_5_4 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 5 4 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

theorem snorm_zero_5_5 :
    schlaefliPolySummandNorm freudenthalTetSqEdges 5 5 = 0 := by
  rw [schlaefliPolySummandNorm_eq_num_div_den]
  unfold schlaefliPolySummandNum schlaefliPolySummandDen freudenthalTetSqEdges
    DihedralCayleyMenger.oppositeCMVertices
  simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial]
  norm_num

/-- The lookup table matches the evaluated rationalized Schläfli summands. -/
theorem freudenthalSchlaefliPolySummandNorm_eq_table (e k : Fin 6) :
    schlaefliPolySummandNorm freudenthalTetSqEdges e k =
      freudenthalSchlaefliPolySummandNormTable e k := by
  match e, k with
  | 0, 0 => exact snorm_zero_0_0
  | 0, 1 => exact snorm_zero_0_1
  | 0, 2 => exact snorm_zero_0_2
  | 0, 3 => exact snorm_zero_0_3
  | 0, 4 => exact snorm_0_4
  | 0, 5 => exact snorm_0_5
  | 1, 0 => exact snorm_zero_1_0
  | 1, 1 => exact snorm_1_1
  | 1, 2 => exact snorm_1_2
  | 1, 3 => exact snorm_1_3
  | 1, 4 => exact snorm_1_4
  | 1, 5 => exact snorm_1_5
  | 2, 0 => exact snorm_zero_2_0
  | 2, 1 => exact snorm_2_1
  | 2, 2 => exact snorm_2_2
  | 2, 3 => exact snorm_2_3
  | 2, 4 => exact snorm_2_4
  | 2, 5 => exact snorm_zero_2_5
  | 3, 0 => exact snorm_zero_3_0
  | 3, 1 => exact snorm_3_1
  | 3, 2 => exact snorm_3_2
  | 3, 3 => exact snorm_3_3
  | 3, 4 => exact snorm_3_4
  | 3, 5 => exact snorm_zero_3_5
  | 4, 0 => exact snorm_4_0
  | 4, 1 => exact snorm_4_1
  | 4, 2 => exact snorm_4_2
  | 4, 3 => exact snorm_4_3
  | 4, 4 => exact snorm_4_4
  | 4, 5 => exact snorm_zero_4_5
  | 5, 0 => exact snorm_5_0
  | 5, 1 => exact snorm_5_1
  | 5, 2 => exact snorm_zero_5_2
  | 5, 3 => exact snorm_zero_5_3
  | 5, 4 => exact snorm_zero_5_4
  | 5, 5 => exact snorm_zero_5_5

/-- Closed-form edge-length derivative from the evaluated rationalized summand. -/
theorem freudenthalDihedralClosedDerivLength_snorm (e k : Fin 6) :
    dihedralClosedDerivLength freudenthalTet e k =
      schlaefliPolySummandNorm freudenthalTetSqEdges e k *
        Real.sqrt (freudenthalTetSqEdges k) / (2 * Real.sqrt (freudenthalTetSqEdges e)) := by
  unfold dihedralClosedDerivLength
  rw [dihedralClosedDerivSq_eq_poly]
  have hsq : freudenthalTet.sqEdge = freudenthalTetSqEdges := by
    simp [freudenthalTet]
  have hbridge := schlaefliSummandBridge freudenthalTet e k
  have hcm : Real.sqrt (2 * cm3 freudenthalTetSqEdges) = 4 := by
    rw [cm3_freudenthalTetSqEdges]
    norm_num
  have hse_ne : Real.sqrt (freudenthalTetSqEdges e) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (freudenthalTet.sqEdge_pos e))
  have hinv :
      (1 / Real.sqrt (2 * cm3 freudenthalTetSqEdges)) = 1 / 4 := by
    rw [hcm]
  have hd_sq :
      dihedralClosedDerivSqPoly freudenthalTet e k =
        schlaefliPolySummandNorm freudenthalTetSqEdges e k /
          (4 * Real.sqrt (freudenthalTetSqEdges e)) := by
    simp only [hsq] at hbridge
    rw [hinv] at hbridge
    have hden_ne : 4 * Real.sqrt (freudenthalTetSqEdges e) ≠ 0 :=
      mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hse_ne
    rw [eq_div_iff hden_ne]
    linarith
  calc
    2 * Real.sqrt (freudenthalTet.sqEdge k) * dihedralClosedDerivSqPoly freudenthalTet e k
        = 2 * Real.sqrt (freudenthalTetSqEdges k) * dihedralClosedDerivSqPoly freudenthalTet e k := by
            rw [hsq]
    _ = 2 * Real.sqrt (freudenthalTetSqEdges k) *
            (schlaefliPolySummandNorm freudenthalTetSqEdges e k /
              (4 * Real.sqrt (freudenthalTetSqEdges e))) := by
            rw [hd_sq]
    _ = schlaefliPolySummandNorm freudenthalTetSqEdges e k *
          Real.sqrt (freudenthalTetSqEdges k) / (2 * Real.sqrt (freudenthalTetSqEdges e)) := by
          field_simp [hse_ne]
          ring

end FreudenthalLengthChainEndpointCert
end Gravity
end IndisputableMonolith
