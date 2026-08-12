import Mathlib

/-!
# Rapidity-overlap metric kernel

This file isolates the finite-dimensional mathematics of a possible successor
to the metric-blind exact-J carrier.

For one spatial channel with log-amplitude `ε`, the two reversed orientations
are averaged with their source-one weights.  Their spatial rapidities cancel,
leaving the rest covector `u` and the averaged rapidity covector
`v(ε) = cosh(ε) u`.  The metric leaf is the overlap difference

`-h⁻¹(u, v(ε) - u)`.

At the Minkowski inverse metric this is exactly `cosh ε - 1`.  The subtraction
is not a fitted offset inside the affine overlap ansatz: flat recovery at
`ε = 0` forces its coefficient to be one.  The leaf actually depends on the
inverse metric, has an explicit nonzero Gateaux derivative, and yields a
symmetric finite response tensor.

This is a matrix/local theorem.  It does not identify a Recognition amplitude
with physical rapidity, prove that the coframe is physical, define a continuum
volume density, or license continuum stress or an empirical observable.

No `sorry`; no new `axiom`.
-/

noncomputable section

namespace IndisputableMonolith
namespace Gravity
namespace Pillar3Successor
namespace RapidityOverlapKernel

open scoped BigOperators
open Matrix

abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev Covector4 := Fin 4 → ℝ

/-- The inverse Minkowski matrix in signature `(-,+,+,+)`. -/
def minkowskiInverse : Matrix4 :=
  Matrix.diagonal (fun μ => if μ = (0 : Fin 4) then (-1 : ℝ) else 1)

/-- Canonical time covector. -/
def restCovector : Covector4 :=
  fun μ => if μ = (0 : Fin 4) then 1 else 0

/-- One signed rapidity covector along a Recognition spatial axis. -/
def signedRapidityCovector
    (axis : Fin 3) (forward : Bool) (ε : ℝ) : Covector4 :=
  fun μ =>
    if μ = (0 : Fin 4) then Real.cosh ε
    else if μ = axis.succ then
      (if forward then 1 else -1) * Real.sinh ε
    else 0

/--
Source-one, reversal-invariant average of the two orientations.  The fixed
halves are the unique two-point reversal-invariant probability weights.
-/
def reversalAverageRapidityCovector
    (axis : Fin 3) (ε : ℝ) : Covector4 :=
  fun μ =>
    (signedRapidityCovector axis true ε μ +
      signedRapidityCovector axis false ε μ) / 2

/-- Reversal averaging cancels the spatial rapidity exactly. -/
theorem reversalAverageRapidityCovector_eq
    (axis : Fin 3) (ε : ℝ) :
    reversalAverageRapidityCovector axis ε =
      fun μ => if μ = (0 : Fin 4) then Real.cosh ε else 0 := by
  funext μ
  by_cases h0 : μ = (0 : Fin 4)
  · simp [reversalAverageRapidityCovector, signedRapidityCovector, h0]
  · by_cases ha : μ = axis.succ
    · simp [reversalAverageRapidityCovector, signedRapidityCovector, h0, ha]
    · simp [reversalAverageRapidityCovector, signedRapidityCovector, h0, ha]

/-- Reversal-averaged rapidity increment relative to the rest orbit. -/
def rapidityIncrement (axis : Fin 3) (ε : ℝ) : Covector4 :=
  fun μ => reversalAverageRapidityCovector axis ε μ - restCovector μ

theorem rapidityIncrement_eq
    (axis : Fin 3) (ε : ℝ) :
    rapidityIncrement axis ε =
      fun μ =>
        if μ = (0 : Fin 4) then Real.cosh ε - 1 else 0 := by
  unfold rapidityIncrement
  rw [reversalAverageRapidityCovector_eq]
  funext μ
  by_cases h0 : μ = (0 : Fin 4) <;>
    simp [rapidityIncrement, restCovector, h0]

/-- Bilinear inverse-metric pairing of two covectors. -/
def inverseMetricPairing
    (h : Matrix4) (u v : Covector4) : ℝ :=
  ∑ μ, ∑ ν, h μ ν * u μ * v ν

theorem inverseMetricPairing_eq_vecMul
    (h : Matrix4) (u v : Covector4) :
    inverseMetricPairing h u v = (u ᵥ* h) ⬝ᵥ v := by
  simp only [inverseMetricPairing, Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- An invertible coordinate change, represented by a frame and its left inverse. -/
structure FrameChange4 where
  frame : Matrix4
  inverseFrame : Matrix4
  inverse_mul_frame : inverseFrame * frame = 1

/-- Contravariant inverse-metric transformation law. -/
def FrameChange4.inverseMetric
    (change : FrameChange4) (h : Matrix4) : Matrix4 :=
  change.frame * h * change.frame.transpose

/-- Covector transformation law. -/
def FrameChange4.covector
    (change : FrameChange4) (u : Covector4) : Covector4 :=
  change.inverseFrame.transpose *ᵥ u

theorem FrameChange4.covector_eq_vecMul
    (change : FrameChange4) (u : Covector4) :
    change.covector u = u ᵥ* change.inverseFrame := by
  unfold FrameChange4.covector
  simpa using
    (Matrix.vecMul_transpose change.inverseFrame.transpose u).symm

/--
The metric overlap is a coordinate scalar when both the inverse metric and
substrate covectors obey their standard transformation laws.
-/
theorem inverseMetricPairing_frameChange
    (change : FrameChange4) (h : Matrix4) (u v : Covector4) :
    inverseMetricPairing (change.inverseMetric h)
        (change.covector u) (change.covector v) =
      inverseMetricPairing h u v := by
  have hmatrix :
      change.inverseFrame *
          (change.frame * h * change.frame.transpose) *
          change.inverseFrame.transpose =
        h := by
    calc
      change.inverseFrame *
            (change.frame * h * change.frame.transpose) *
            change.inverseFrame.transpose =
          (change.inverseFrame * change.frame) * h *
            (change.frame.transpose *
              change.inverseFrame.transpose) := by
                simp only [Matrix.mul_assoc]
      _ = (change.inverseFrame * change.frame) * h *
            (change.inverseFrame * change.frame).transpose := by
              rw [Matrix.transpose_mul]
      _ = h := by
        rw [change.inverse_mul_frame]
        simp
  rw [inverseMetricPairing_eq_vecMul, inverseMetricPairing_eq_vecMul,
    change.covector_eq_vecMul, change.covector_eq_vecMul]
  rw [Matrix.vecMul_vecMul]
  rw [← change.covector_eq_vecMul v]
  unfold FrameChange4.covector
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  unfold FrameChange4.inverseMetric
  rw [hmatrix]

/-- Exact one-edge J cost, restated locally for the standalone kernel. -/
def exactJLeaf (ε : ℝ) : ℝ :=
  Real.cosh ε - 1

/--
Metric-dependent rapidity-overlap leaf.  It stores no response or stress
tensor; the response below is obtained by differentiating this constructor.
-/
def rapidityMetricLeaf
    (h : Matrix4) (axis : Fin 3) (ε : ℝ) : ℝ :=
  -inverseMetricPairing h restCovector (rapidityIncrement axis ε)

/-- Closed form: the constructor reads the inverse-metric `00` component. -/
theorem rapidityMetricLeaf_eq
    (h : Matrix4) (axis : Fin 3) (ε : ℝ) :
    rapidityMetricLeaf h axis ε =
      -(h 0 0) * exactJLeaf ε := by
  unfold rapidityMetricLeaf
  rw [rapidityIncrement_eq]
  simp [inverseMetricPairing, restCovector,
    exactJLeaf, Fin.sum_univ_four]

/-- Exact recovery of the landed exact-J leaf at the Minkowski metric. -/
@[simp] theorem rapidityMetricLeaf_minkowski
    (axis : Fin 3) (ε : ℝ) :
    rapidityMetricLeaf minkowskiInverse axis ε = exactJLeaf ε := by
  rw [rapidityMetricLeaf_eq]
  simp [minkowskiInverse]

/-- The zero-amplitude channel is silent for every metric, not just flat. -/
@[simp] theorem rapidityMetricLeaf_zero
    (h : Matrix4) (axis : Fin 3) :
    rapidityMetricLeaf h axis 0 = 0 := by
  rw [rapidityMetricLeaf_eq]
  simp [exactJLeaf]

/-- Affine line through inverse-metric matrix space. -/
def matrixLine (h H : Matrix4) (t : ℝ) : Matrix4 :=
  fun μ ν => h μ ν + t * H μ ν

/-- Explicit Gateaux derivative of one metric leaf. -/
theorem rapidityMetricLeaf_line_hasDerivAt
    (h H : Matrix4) (axis : Fin 3) (ε : ℝ) :
    HasDerivAt
      (fun t => rapidityMetricLeaf (matrixLine h H t) axis ε)
      (-(H 0 0) * exactJLeaf ε)
      0 := by
  have hlinear :
      HasDerivAt
        (fun t : ℝ =>
          -(h 0 0 + t * H 0 0) * exactJLeaf ε)
        (-(H 0 0) * exactJLeaf ε)
        0 := by
    convert
      (((hasDerivAt_const (x := (0 : ℝ)) (h 0 0)).add
        ((hasDerivAt_id (𝕜 := ℝ) (x := (0 : ℝ))).mul_const
          (H 0 0))).neg.mul_const (exactJLeaf ε))
      using 1 <;> ring
  simpa [rapidityMetricLeaf_eq, matrixLine] using hlinear

/-- Channel data used by the finite carrier kernel. -/
structure MetricChannel where
  axis : Fin 3
  amplitude : ℝ

/-- The original exact-J recursion on a finite channel list. -/
def exactCarrierAction : List MetricChannel → ℝ
  | [] => 0
  | channel :: rest =>
      exactJLeaf channel.amplitude + exactCarrierAction rest

/-- The rapidity-overlap metric recursion on the same channel list. -/
def rapidityMetricAction
    (h : Matrix4) : List MetricChannel → ℝ
  | [] => 0
  | channel :: rest =>
      rapidityMetricLeaf h channel.axis channel.amplitude +
        rapidityMetricAction h rest

/-- The whole finite action has a closed metric dependence. -/
theorem rapidityMetricAction_eq
    (h : Matrix4) (channels : List MetricChannel) :
    rapidityMetricAction h channels =
      -(h 0 0) * exactCarrierAction channels := by
  induction channels with
  | nil => simp [rapidityMetricAction, exactCarrierAction]
  | cons channel rest ih =>
      rw [rapidityMetricAction, exactCarrierAction,
        rapidityMetricLeaf_eq, ih]
      ring

/-- Flat recovery holds for every finite carrier, not merely one witness. -/
@[simp] theorem rapidityMetricAction_minkowski
    (channels : List MetricChannel) :
    rapidityMetricAction minkowskiInverse channels =
      exactCarrierAction channels := by
  rw [rapidityMetricAction_eq]
  simp [minkowskiInverse]

/-- Exact Gateaux derivative of the whole finite action. -/
theorem rapidityMetricAction_line_hasDerivAt
    (h H : Matrix4) (channels : List MetricChannel) :
    HasDerivAt
      (fun t => rapidityMetricAction (matrixLine h H t) channels)
      (-(H 0 0) * exactCarrierAction channels)
      0 := by
  have hlinear :
      HasDerivAt
        (fun t : ℝ =>
          -(h 0 0 + t * H 0 0) * exactCarrierAction channels)
        (-(H 0 0) * exactCarrierAction channels)
        0 := by
    convert
      (((hasDerivAt_const (x := (0 : ℝ)) (h 0 0)).add
        ((hasDerivAt_id (𝕜 := ℝ) (x := (0 : ℝ))).mul_const
          (H 0 0))).neg.mul_const (exactCarrierAction channels))
      using 1 <;> ring
  simpa [rapidityMetricAction_eq, matrixLine] using hlinear

/-- Unit `00` inverse-metric variation. -/
def timeTimeVariation : Matrix4 :=
  fun μ ν =>
    if μ = (0 : Fin 4) ∧ ν = (0 : Fin 4) then 1 else 0

/-- A second symmetric nondegenerate Lorentzian-signature inverse metric. -/
def halfTimeInverse : Matrix4 :=
  Matrix.diagonal
    (fun μ => if μ = (0 : Fin 4) then (-1 / 2 : ℝ) else 1)

theorem halfTimeInverse_symmetric :
    halfTimeInverse.transpose = halfTimeInverse := by
  ext μ ν
  by_cases h : μ = ν
  · subst ν
    rfl
  · have h' : ν ≠ μ := fun hrev => h hrev.symm
    simp [halfTimeInverse, Matrix.transpose_apply, Matrix.diagonal, h, h']

theorem halfTimeInverse_det :
    halfTimeInverse.det = (-1 / 2 : ℝ) := by
  simp [halfTimeInverse, Matrix.det_diagonal, Fin.prod_univ_four]

theorem halfTimeInverse_nondegenerate :
    halfTimeInverse.det ≠ 0 := by
  rw [halfTimeInverse_det]
  norm_num

theorem halfTimeInverse_lorentzian_diagonal :
    halfTimeInverse 0 0 < 0 ∧
      ∀ axis : Fin 3, 0 < halfTimeInverse axis.succ axis.succ := by
  constructor
  · norm_num [halfTimeInverse]
  · intro axis
    simp [halfTimeInverse, Fin.succ_ne_zero]

/-- A concrete one-channel unit-amplitude carrier. -/
def unitCarrier : List MetricChannel :=
  [{ axis := 0, amplitude := 1 }]

theorem exactCarrierAction_unit :
    exactCarrierAction unitCarrier = Real.cosh 1 - 1 := by
  simp [unitCarrier, exactCarrierAction, exactJLeaf]

theorem exactCarrierAction_unit_pos :
    0 < exactCarrierAction unitCarrier := by
  rw [exactCarrierAction_unit]
  linarith [Real.one_lt_cosh.mpr (by norm_num : (1 : ℝ) ≠ 0)]

/-- Actual dependence: two explicit inverse metrics give different actions. -/
theorem rapidityMetricAction_actual_dependence :
    rapidityMetricAction halfTimeInverse unitCarrier ≠
      rapidityMetricAction minkowskiInverse unitCarrier := by
  rw [rapidityMetricAction_eq, rapidityMetricAction_minkowski]
  simp [halfTimeInverse]
  intro h
  nlinarith [exactCarrierAction_unit_pos]

/-- The concrete unit carrier has a nonzero metric derivative. -/
theorem unitCarrier_metricDerivative_ne_zero :
    deriv
      (fun t =>
        rapidityMetricAction
          (matrixLine minkowskiInverse timeTimeVariation t) unitCarrier)
      0 ≠ 0 := by
  rw [(rapidityMetricAction_line_hasDerivAt
    minkowskiInverse timeTimeVariation unitCarrier).deriv]
  simp [timeTimeVariation]
  exact exactCarrierAction_unit_pos.ne'

/--
Finite inverse-metric stress response `-2 dS[h+tH]/dt`.  This is a local
matrix response, not a continuum stress-energy tensor.
-/
def finiteInverseMetricStressResponse
    (channels : List MetricChannel) (H : Matrix4) : ℝ :=
  -2 * (-(H 0 0) * exactCarrierAction channels)

/-- Response tensor obtained from the derivative, rather than inserted. -/
def finiteInverseMetricStressTensor
    (channels : List MetricChannel) : Matrix4 :=
  fun μ ν =>
    if μ = (0 : Fin 4) ∧ ν = (0 : Fin 4) then
      2 * exactCarrierAction channels
    else 0

theorem finiteInverseMetricStressTensor_symmetric
    (channels : List MetricChannel) :
    (finiteInverseMetricStressTensor channels).transpose =
      finiteInverseMetricStressTensor channels := by
  ext μ ν
  by_cases hμ : μ = (0 : Fin 4) <;>
    by_cases hν : ν = (0 : Fin 4) <;>
      simp [finiteInverseMetricStressTensor, hμ, hν]

/-- Tensor contraction equals the stress response defined from the derivative. -/
theorem finiteStressTensor_contract
    (channels : List MetricChannel) (H : Matrix4) :
    (∑ μ, ∑ ν,
        finiteInverseMetricStressTensor channels μ ν * H μ ν) =
      finiteInverseMetricStressResponse channels H := by
  simp [finiteInverseMetricStressTensor,
    finiteInverseMetricStressResponse, Fin.sum_univ_four]
  ring

/-- The derivative-generated finite response is nonzero on the unit witness. -/
theorem unitCarrier_finiteStress_nonzero :
    finiteInverseMetricStressResponse unitCarrier timeTimeVariation ≠ 0 := by
  simp [finiteInverseMetricStressResponse, timeTimeVariation]
  exact exactCarrierAction_unit_pos.ne'

/-! ## Wrong shortcuts and the forced subtraction inside the overlap ansatz -/

/-- Metric-blind shortcut: exact flat value but zero metric derivative. -/
def metricBlindLeaf (_h : Matrix4) (_axis : Fin 3) (ε : ℝ) : ℝ :=
  exactJLeaf ε

theorem metricBlindLeaf_line_derivative_zero
    (h H : Matrix4) (axis : Fin 3) (ε : ℝ) :
    HasDerivAt
      (fun t => metricBlindLeaf (matrixLine h H t) axis ε)
      0 0 := by
  simpa [metricBlindLeaf] using
    (hasDerivAt_const (x := (0 : ℝ)) (exactJLeaf ε))

/--
Raw overlap with an arbitrary coefficient on the rest overlap.  The successor
leaf is the case `coefficient = 1`.
-/
def affineRapidityOverlapLeaf
    (coefficient : ℝ) (h : Matrix4) (axis : Fin 3) (ε : ℝ) : ℝ :=
  -inverseMetricPairing h restCovector
      (reversalAverageRapidityCovector axis ε) +
    coefficient * inverseMetricPairing h restCovector restCovector

theorem affineRapidityOverlapLeaf_zero_minkowski
    (coefficient : ℝ) (axis : Fin 3) :
    affineRapidityOverlapLeaf coefficient minkowskiInverse axis 0 =
      1 - coefficient := by
  unfold affineRapidityOverlapLeaf
  rw [reversalAverageRapidityCovector_eq]
  simp [inverseMetricPairing,
    restCovector, minkowskiInverse, Fin.sum_univ_four]
  ring

/--
Within the affine overlap family, flat recovery at the zero-amplitude vacuum
forces the subtraction coefficient to be exactly one.
-/
theorem flatRecovery_forces_subtraction_coefficient_one
    (coefficient : ℝ)
    (flatRecovery :
      ∀ (axis : Fin 3) (ε : ℝ),
        affineRapidityOverlapLeaf coefficient minkowskiInverse axis ε =
          exactJLeaf ε) :
    coefficient = 1 := by
  have h0 := flatRecovery (0 : Fin 3) 0
  rw [affineRapidityOverlapLeaf_zero_minkowski] at h0
  simp [exactJLeaf] at h0
  linarith

/-- The unsubtracted raw-overlap shortcut fails even the flat vacuum. -/
theorem rawOverlap_wrong_at_zero
    (axis : Fin 3) :
    affineRapidityOverlapLeaf 0 minkowskiInverse axis 0 ≠
      exactJLeaf 0 := by
  rw [affineRapidityOverlapLeaf_zero_minkowski]
  simp [exactJLeaf]

end RapidityOverlapKernel
end Pillar3Successor
end Gravity
end IndisputableMonolith
