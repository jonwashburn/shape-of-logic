import IndisputableMonolith.Geometry.ReggeActionNonlinearHessianProof

/-!
# Cubic Taylor Bound for the Nonlinear Regge Remainder

This module isolates the final analytic Taylor theorem needed after the
nonlinear Hessian has been identified.  The heavy analytic content is a local
third-order bound in the finite-dimensional vertex-potential space.
-/

namespace IndisputableMonolith
namespace Geometry
namespace ReggeActionCubicTaylorBound

open ReggeTriangulation3D
open ReggeHessian3D
open Triangulation3DConsistency
open ReggeActionConcrete
open ReggeActionSmoothness
open ReggeActionSecondVariation
open ReggeActionNonlinearHessianProof

noncomputable section

/-- Exact Taylor theorem needed for the nonlinear Regge remainder.  This is
the finite-dimensional third-order Taylor estimate specialized to the canonical
Regge remainder. -/
def NonlinearReggeCubicTaylorTheorem
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  LocalCubicRemainderBound K hK

def reggeActionCubicRemainderInput_of_taylorTheorem
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hTaylor : NonlinearReggeCubicTaylorTheorem K hK) :
    ReggeActionCubicRemainderInput K hK hFlat :=
  reggeActionCubicRemainderInput_of_bound K hK hFlat hTaylor

/-- The Taylor theorem is exactly the local cubic remainder bound.  This
identity lemma makes the audit explicit: no hidden analytic assumption is
buried in the constructor. -/
theorem nonlinearReggeCubicTaylorTheorem_iff_localBound
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    NonlinearReggeCubicTaylorTheorem K hK ↔ LocalCubicRemainderBound K hK :=
  Iff.rfl

/-- If the canonical nonlinear remainder vanishes identically, the cubic Taylor
theorem follows with zero constant.  The real nonlinear theorem will replace
this strong special case by the finite-dimensional third-order estimate. -/
theorem nonlinearReggeCubicTaylorTheorem_of_identically_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hZero :
      ∀ ξ : VertexPotential K,
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ = 0) :
    NonlinearReggeCubicTaylorTheorem K hK := by
  refine ⟨1, 0, by norm_num, le_rfl, ?_⟩
  intro ξ _hξ
  rw [hZero ξ]
  simp

theorem canonicalRemainder_contDiffAt_zero_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun ξ : VertexPotential K =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ)
      (zeroPotential K) := by
  unfold reggeActionRemainder
  have hAction := hFlat.action_contDiff_at_zero
  have hConst : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun _ξ : VertexPotential K => reggeAction K hK (zeroPotential K))
      (zeroPotential K) := contDiffAt_const
  have hQuad : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun ξ : VertexPotential K =>
        (1 / 2) * hessianQuadratic (canonicalReggeHessian K hK) ξ)
      (zeroPotential K) := by
    unfold hessianQuadratic
    fun_prop
  exact (hAction.sub hConst).sub hQuad

/-- The exact remaining finite-dimensional Taylor theorem.

The canonical remainder is already smooth at the flat point and its value is
zero.  To derive the cubic estimate from standard Taylor theory, it remains to
connect the zero first-variation and zero second-variation inputs for the
canonical remainder to a local `O(||ξ||^3)` bound.  This definition isolates
that analytic theorem without adding an axiom. -/
def CanonicalRemainderCubicTaylorFromJetInputsTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (_hFlat : FlatConfiguration K hK) : Prop :=
  ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
      (canonicalReggeHessian K hK) →
    ReggeActionRemainderSecondVariationInput K hK →
      NonlinearReggeCubicTaylorTheorem K hK

theorem nonlinearReggeCubicTaylorTheorem_of_remainderJetInputs
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hTaylorFromJets : CanonicalRemainderCubicTaylorFromJetInputsTarget K hK hFlat)
    (hFirst :
      ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
        (canonicalReggeHessian K hK))
    (hSecond : ReggeActionRemainderSecondVariationInput K hK) :
    NonlinearReggeCubicTaylorTheorem K hK :=
  hTaylorFromJets hFirst hSecond

theorem linePotential_one
    (K : Triangulation3D) (ξ : VertexPotential K) :
    linePotential K ξ 1 = ξ := by
  funext i
  simp [linePotential]

theorem linePotential_eq_smul
    (K : Triangulation3D) (ξ : VertexPotential K) (t : ℝ) :
    linePotential K ξ t = t • ξ := by
  funext i
  simp [linePotential]

theorem norm_linePotential_le_of_mem_Icc_zero_one
    (K : Triangulation3D) (ξ : VertexPotential K) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖linePotential K ξ t‖ ≤ ‖ξ‖ := by
  rw [linePotential_eq_smul K ξ t, norm_smul, Real.norm_eq_abs]
  have habs : |t| ≤ 1 := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  calc
    |t| * ‖ξ‖ ≤ 1 * ‖ξ‖ :=
      mul_le_mul_of_nonneg_right habs (norm_nonneg ξ)
    _ = ‖ξ‖ := one_mul _

/-- One-dimensional line form of the remaining cubic Taylor estimate.

For every conformal direction `ξ`, restrict the canonical remainder to the line
`t ↦ tξ`.  A standard one-variable Taylor theorem with zero value, first
variation, and second variation at `t = 0` should prove this estimate from a
uniform bound on third derivatives along the segment. -/
def CanonicalRemainderLineCubicEstimateTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
    ∀ ξ : VertexPotential K, ‖ξ‖ < r →
      ‖reggeActionRemainder K hK (canonicalReggeHessian K hK)
          (linePotential K ξ 1)‖ ≤
        C * ‖ξ‖ ^ (3 : ℕ)

theorem nonlinearReggeCubicTaylorTheorem_of_lineCubicEstimate
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hLine : CanonicalRemainderLineCubicEstimateTarget K hK) :
    NonlinearReggeCubicTaylorTheorem K hK := by
  rcases hLine with ⟨r, C, hr, hC, hineq⟩
  refine ⟨r, C, hr, hC, ?_⟩
  intro ξ hξ
  simpa [linePotential_one K ξ] using hineq ξ hξ

private theorem abs_value_le_cubic_of_taylor_data
    (f : ℝ → ℝ) (M a : ℝ)
    (hf : ContDiffOn ℝ (3 : ℕ) f (Set.Icc (0 : ℝ) 1))
    (hTaylorZero : taylorWithinEval f 2 (Set.Icc (0 : ℝ) 1) 0 1 = 0)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 3 f t| ≤ M * a) :
    |f 1| ≤ (M / 6) * a := by
  have hrem :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := f) (x₀ := (0 : ℝ)) (x := (1 : ℝ)) (n := 2)
      (by norm_num) (by simpa using hf)
  rcases hrem with ⟨x', hx', hEq⟩
  rw [hTaylorZero] at hEq
  have hxIcc : x' ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩
  have hb := hbound x' hxIcc
  rw [sub_zero] at hEq
  rw [hEq]
  norm_num
  rw [abs_div]
  norm_num
  have hdiv : |iteratedDeriv 3 f x'| / (6 : ℝ) ≤ (M * a) / 6 :=
    div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 6)
  have hrewrite : (M * a) / 6 = (M / 6) * a := by ring
  rwa [hrewrite] at hdiv

/-- Mathlib-shaped one-variable Taylor data along every conformal line.

This is the precise analytic bridge left after all geometric reductions:
for each direction `ξ`, the line-restricted canonical remainder is `C^3` on the
unit segment, its quadratic Taylor polynomial at zero vanishes, and its third
derivative is bounded by `M * ||ξ||^3` on the segment. -/
def CanonicalRemainderLineTaylorDataTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∃ (r M : ℝ), 0 < r ∧ 0 ≤ M ∧
    ∀ ξ : VertexPotential K, ‖ξ‖ < r →
      ContDiffOn ℝ (3 : ℕ)
        (fun t : ℝ =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK)
            (linePotential K ξ t))
        (Set.Icc (0 : ℝ) 1) ∧
      taylorWithinEval
        (fun t : ℝ =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK)
            (linePotential K ξ t))
        2 (Set.Icc (0 : ℝ) 1) 0 1 = 0 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDeriv 3
          (fun s : ℝ =>
            reggeActionRemainder K hK (canonicalReggeHessian K hK)
              (linePotential K ξ s)) t| ≤ M * ‖ξ‖ ^ (3 : ℕ)

def CanonicalRemainderLineContDiffTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    ∀ ξ : VertexPotential K, ‖ξ‖ < r →
      ContDiffOn ℝ (3 : ℕ)
        (fun t : ℝ =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK)
            (linePotential K ξ t))
        (Set.Icc (0 : ℝ) 1)

theorem canonicalRemainderLineContDiff_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    CanonicalRemainderLineContDiffTarget K hK := by
  let R : VertexPotential K → ℝ :=
    fun ξ => reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ
  have hR : ContDiffAt ℝ (⊤ : ℕ∞) R (zeroPotential K) := by
    simpa [R] using canonicalRemainder_contDiffAt_zero_of_flatConfiguration K hK hFlat
  have hle : ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.2 le_top
  rcases hR.contDiffOn (m := (3 : ℕ∞)) hle (by intro h; simp at h) with
    ⟨u, hu, hRu⟩
  rcases Metric.mem_nhds_iff.mp hu with ⟨eps, heps, hball⟩
  refine ⟨eps, heps, ?_⟩
  intro ξ hξ
  have hline : ContDiffOn ℝ (3 : ℕ∞)
      (fun t : ℝ => linePotential K ξ t) (Set.Icc (0 : ℝ) 1) := by
    rw [contDiffOn_pi]
    intro i
    unfold linePotential
    fun_prop
  have hmaps : Set.MapsTo (fun t : ℝ => linePotential K ξ t)
      (Set.Icc (0 : ℝ) 1) u := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : linePotential K ξ t - zeroPotential K = linePotential K ξ t := by
      funext i
      simp [zeroPotential]
    rw [hsub]
    exact lt_of_le_of_lt (norm_linePotential_le_of_mem_Icc_zero_one K ξ ht) hξ
  have hcomp := hRu.comp hline hmaps
  simpa [R, Function.comp_def] using hcomp

def CanonicalRemainderLineQuadraticTaylorZeroTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    ∀ ξ : VertexPotential K, ‖ξ‖ < r →
      taylorWithinEval
        (fun t : ℝ =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK)
            (linePotential K ξ t))
        2 (Set.Icc (0 : ℝ) 1) 0 1 = 0

def CanonicalRemainderLineThirdDerivBoundTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∃ (r M : ℝ), 0 < r ∧ 0 ≤ M ∧
    ∀ ξ : VertexPotential K, ‖ξ‖ < r →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDeriv 3
          (fun s : ℝ =>
            reggeActionRemainder K hK (canonicalReggeHessian K hK)
              (linePotential K ξ s)) t| ≤ M * ‖ξ‖ ^ (3 : ℕ)

private theorem min_pos3 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < min (min a b) c :=
  lt_min (lt_min ha hb) hc

theorem lineTaylorData_of_splitTargets
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hCont : CanonicalRemainderLineContDiffTarget K hK)
    (hTaylorZero : CanonicalRemainderLineQuadraticTaylorZeroTarget K hK)
    (hThird : CanonicalRemainderLineThirdDerivBoundTarget K hK) :
    CanonicalRemainderLineTaylorDataTarget K hK := by
  rcases hCont with ⟨rC, hrC, hC⟩
  rcases hTaylorZero with ⟨rT, hrT, hT⟩
  rcases hThird with ⟨rD, M, hrD, hM, hD⟩
  refine ⟨min (min rC rT) rD, M, min_pos3 hrC hrT hrD, hM, ?_⟩
  intro ξ hξ
  have hξC : ‖ξ‖ < rC := lt_of_lt_of_le hξ (min_le_left (min rC rT) rD |>.trans (min_le_left rC rT))
  have hξT : ‖ξ‖ < rT := by
    have hle : min (min rC rT) rD ≤ rT :=
      le_trans (min_le_left (min rC rT) rD) (min_le_right rC rT)
    exact lt_of_lt_of_le hξ hle
  have hξD : ‖ξ‖ < rD := lt_of_lt_of_le hξ (min_le_right (min rC rT) rD)
  exact ⟨hC ξ hξC, hT ξ hξT, hD ξ hξD⟩

theorem lineCubicEstimate_of_lineTaylorData
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hData : CanonicalRemainderLineTaylorDataTarget K hK) :
    CanonicalRemainderLineCubicEstimateTarget K hK := by
  rcases hData with ⟨r, M, hr, hM, hdata⟩
  refine ⟨r, M / 6, hr, div_nonneg hM (by norm_num), ?_⟩
  intro ξ hξ
  rcases hdata ξ hξ with ⟨hCont, hTaylorZero, hBound⟩
  have h :=
    abs_value_le_cubic_of_taylor_data
      (fun t : ℝ =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK)
          (linePotential K ξ t))
      M (‖ξ‖ ^ (3 : ℕ)) hCont hTaylorZero hBound
  simpa [Real.norm_eq_abs] using h

theorem nonlinearReggeCubicTaylorTheorem_of_lineTaylorData
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hData : CanonicalRemainderLineTaylorDataTarget K hK) :
    NonlinearReggeCubicTaylorTheorem K hK :=
  nonlinearReggeCubicTaylorTheorem_of_lineCubicEstimate K hK
    (lineCubicEstimate_of_lineTaylorData K hK hData)

/-- Once the nonlinear Hessian is identified and the cubic Taylor theorem is
proved, the canonical nonlinear remainder is controlled by `O(||xi||^3)`. -/
def cubicRemainderInput_of_hessian_and_taylor
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (_hHessian : NonlinearReggeDirectionalHessianTheorem K hK)
    (hTaylor : NonlinearReggeCubicTaylorTheorem K hK) :
    ReggeActionCubicRemainderInput K hK hFlat :=
  reggeActionCubicRemainderInput_of_taylorTheorem K hK hFlat hTaylor

/-- Combined local nonlinear inputs after the Hessian branch and the cubic
Taylor branch have both been supplied.  The fields are theorem-valued outputs,
not new assumptions. -/
structure NonlinearReggeLocalHessianTaylorInputs
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) where
  action_secondVariation : ReggeActionSecondVariationInput K hK hFlat
  remainder_secondVariation : ReggeActionRemainderSecondVariationInput K hK
  cubic_remainder : ReggeActionCubicRemainderInput K hK hFlat

def nonlinearReggeLocalHessianTaylorInputs_of_hessian_and_taylor
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hHessian : NonlinearReggeDirectionalHessianTheorem K hK)
    (hTaylor : NonlinearReggeCubicTaylorTheorem K hK) :
    NonlinearReggeLocalHessianTaylorInputs K hK hFlat where
  action_secondVariation :=
    reggeActionSecondVariationInput_of_flat_nonlinearHessian K hK hFlat hHessian
  remainder_secondVariation :=
    reggeActionRemainderSecondVariationInput_of_flat_nonlinearHessian K hK hFlat
      hHessian
  cubic_remainder :=
    cubicRemainderInput_of_hessian_and_taylor K hK hFlat hHessian hTaylor

def nonlinearReggeLocalHessianTaylorInputs_of_eventuallyZero_edgeStencil_and_taylor
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hZero : WeightedDeficitDerivativeEventuallyZeroTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK)
    (hTaylor : NonlinearReggeCubicTaylorTheorem K hK) :
    NonlinearReggeLocalHessianTaylorInputs K hK hFlat where
  action_secondVariation :=
    reggeActionSecondVariationInput_of_eventuallyZero_and_edgeStencil
      K hK hFlat D hZero hEdge hStencil
  remainder_secondVariation :=
    reggeActionRemainderSecondVariationInput_of_eventuallyZero_and_edgeStencil
      K hK hFlat D hZero hEdge hStencil
  cubic_remainder :=
    reggeActionCubicRemainderInput_of_taylorTheorem K hK hFlat hTaylor

def nonlinearReggeLocalHessianTaylorInputs_of_eventuallyZero_edgeStencil_and_remainderJetTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hZero : WeightedDeficitDerivativeEventuallyZeroTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK)
    (hTaylorFromJets : CanonicalRemainderCubicTaylorFromJetInputsTarget K hK hFlat)
    (hFirst :
      ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
        (canonicalReggeHessian K hK)) :
    NonlinearReggeLocalHessianTaylorInputs K hK hFlat :=
  nonlinearReggeLocalHessianTaylorInputs_of_eventuallyZero_edgeStencil_and_taylor
    K hK hFlat D hZero hEdge hStencil
    (hTaylorFromJets hFirst
      (reggeActionRemainderSecondVariationInput_of_eventuallyZero_and_edgeStencil
        K hK hFlat D hZero hEdge hStencil))

/-! ## §6. Closure of `CanonicalRemainderLineQuadraticTaylorZeroTarget`

This section discharges the second of the three sub-targets that compose
`CanonicalRemainderLineTaylorDataTarget`. The first
(`CanonicalRemainderLineContDiffTarget`) was already closed by
`canonicalRemainderLineContDiff_of_flatConfiguration` above. The third
(`CanonicalRemainderLineThirdDerivBoundTarget`) is closed later in this file by
`canonicalRemainderLineThirdDerivBound_of_flatConfiguration`.

The strategy here is direct: the remainder's quadratic Taylor polynomial at
zero, restricted to the conformal line, vanishes because:
* `R(0) = 0` (`reggeActionRemainder_zero`),
* `R'(0) = 0` along every line (`fderiv R 0 = 0` from
  `ReggeActionRemainderFirstVariationInput`),
* `R''(0) = 0` along every line (`HasSecondDerivAt R_line 0 0` from
  `ReggeActionRemainderSecondVariationInput`).
The bridge from `iteratedDerivWithin` to free-space `iteratedDeriv` uses
`uniqueDiffOn_Icc_zero_one` and `ContDiffAt` (the latter inherited from
`canonicalRemainder_contDiffAt_zero_of_flatConfiguration` plus C^∞ of the
linear line map). -/

/-- ContDiffAt of the line-restricted canonical remainder at `t = 0`. -/
theorem canonicalRemainderLine_contDiffAt_zero_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) (ξ : VertexPotential K) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun t : ℝ =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK)
          (linePotential K ξ t)) 0 := by
  have hR : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun ξ' : VertexPotential K =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
      (zeroPotential K) :=
    canonicalRemainder_contDiffAt_zero_of_flatConfiguration K hK hFlat
  have hLine : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun t : ℝ => linePotential K ξ t) 0 := by
    rw [contDiffAt_pi]
    intro i
    show ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => t * ξ i) 0
    fun_prop
  -- Rewrite the target point using `linePotential K ξ 0 = zeroPotential K`.
  have hLine0 : linePotential K ξ 0 = zeroPotential K := linePotential_zero K ξ
  have hR' : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun ξ' : VertexPotential K =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
      (linePotential K ξ 0) := by
    rw [hLine0]; exact hR
  exact hR'.comp 0 hLine

/-- `R(linePotential ξ 0) = 0`. -/
theorem canonicalRemainderLine_value_at_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    reggeActionRemainder K hK (canonicalReggeHessian K hK)
      (linePotential K ξ 0) = 0 := by
  rw [linePotential_zero K ξ]
  exact ReggeActionConcrete.reggeActionRemainder_zero K hK _

/-- The line `t ↦ t • ξ` has derivative `ξ` at every point. -/
private theorem hasDerivAt_linePotential
    (K : Triangulation3D) (ξ : VertexPotential K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => linePotential K ξ s) ξ t := by
  rw [show (fun s : ℝ => linePotential K ξ s) = (fun s : ℝ => s • ξ) by
    funext s; rw [linePotential_eq_smul]]
  -- HasDerivAt (· • ξ) ξ t : derivative of t ↦ t • ξ is ξ.
  have h := (hasDerivAt_id t).smul_const ξ
  simpa using h

/-- The line-restricted remainder has derivative 0 at 0, given the remainder's
free-space gradient vanishes at 0. -/
theorem canonicalRemainderLine_hasDerivAt_zero_of_remainderFirstVar
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hFirst : ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
      (canonicalReggeHessian K hK))
    (ξ : VertexPotential K) :
    HasDerivAt
      (fun t : ℝ =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK)
          (linePotential K ξ t))
      0 0 := by
  -- ContDiffAt (1) at zeroPotential K gives differentiableAt → HasFDerivAt.
  have hContR : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun ξ' : VertexPotential K =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
      (zeroPotential K) :=
    canonicalRemainder_contDiffAt_zero_of_flatConfiguration K hK hFlat
  have hDiffR : DifferentiableAt ℝ
      (fun ξ' : VertexPotential K =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
      (zeroPotential K) :=
    hContR.differentiableAt (by simp)
  have hHasF : HasFDerivAt
      (fun ξ' : VertexPotential K =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
      (fderiv ℝ
        (fun ξ' : VertexPotential K =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
        (zeroPotential K))
      (zeroPotential K) :=
    hDiffR.hasFDerivAt
  -- `fderiv = 0` from the remainder first-variation input.
  have hFderiv0 :
      fderiv ℝ
        (fun ξ' : VertexPotential K =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
        (zeroPotential K) = 0 :=
    hFirst.remainder_firstVariation_zero
  rw [hFderiv0] at hHasF
  -- Rewrite (zeroPotential K) = (linePotential K ξ 0).
  have hLine0 : zeroPotential K = linePotential K ξ 0 := (linePotential_zero K ξ).symm
  rw [hLine0] at hHasF
  -- Inner derivative: linePotential has derivative ξ.
  have hInner : HasDerivAt (fun t : ℝ => linePotential K ξ t) ξ 0 :=
    hasDerivAt_linePotential K ξ 0
  -- Compose: HasDerivAt (R ∘ linePotential) ((fderiv R 0) ξ) 0.
  have hComp := hHasF.comp_hasDerivAt 0 hInner
  -- `(fderiv R 0) ξ = 0` since `fderiv R 0 = 0`.
  -- After the `rw [hFderiv0]`, the outer derivative is the zero linear map; (0 : VP →L ℝ) ξ = 0.
  simpa using hComp

/-- `iteratedDerivWithin 0 R_line [0,1] 0 = 0`. -/
theorem iteratedDerivWithin_zero_canonicalRemainderLine
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    iteratedDerivWithin 0
      (fun t : ℝ =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK)
          (linePotential K ξ t))
      (Set.Icc (0 : ℝ) 1) 0 = 0 := by
  rw [iteratedDerivWithin_zero]
  exact canonicalRemainderLine_value_at_zero K hK ξ

private theorem zero_mem_Icc_zero_one : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_refl 0, by norm_num⟩

/-- `iteratedDerivWithin 1 R_line [0,1] 0 = 0` given the remainder
first-variation input (which forces `fderiv R 0 = 0` and hence
`deriv R_line 0 = 0` via the chain rule). -/
theorem iteratedDerivWithin_one_canonicalRemainderLine_of_jetInputs
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hFirst : ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
      (canonicalReggeHessian K hK))
    (ξ : VertexPotential K) :
    iteratedDerivWithin 1
      (fun t : ℝ =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK)
          (linePotential K ξ t))
      (Set.Icc (0 : ℝ) 1) 0 = 0 := by
  have hContDiff :=
    canonicalRemainderLine_contDiffAt_zero_of_flatConfiguration K hK hFlat ξ
  have h_iw_eq :
      iteratedDerivWithin 1
        (fun t : ℝ =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK)
            (linePotential K ξ t))
        (Set.Icc (0 : ℝ) 1) 0 =
      iteratedDeriv 1
        (fun t : ℝ =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK)
            (linePotential K ξ t)) 0 := by
    apply iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one
      _ zero_mem_Icc_zero_one
    refine hContDiff.of_le ?_
    exact (WithTop.coe_le_coe).mpr le_top
  rw [h_iw_eq, iteratedDeriv_one]
  -- deriv R_line 0 = 0 from HasDerivAt R_line 0 0.
  exact (canonicalRemainderLine_hasDerivAt_zero_of_remainderFirstVar
    K hK hFlat hFirst ξ).deriv

/-- `iteratedDerivWithin 2 R_line [0,1] 0 = 0` given the remainder
second-variation input (`HasSecondDerivAt R_line 0 0`). -/
theorem iteratedDerivWithin_two_canonicalRemainderLine_of_jetInputs
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hSecond : ReggeActionRemainderSecondVariationInput K hK)
    (ξ : VertexPotential K) :
    iteratedDerivWithin 2
      (fun t : ℝ =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK)
          (linePotential K ξ t))
      (Set.Icc (0 : ℝ) 1) 0 = 0 := by
  have hContDiff :=
    canonicalRemainderLine_contDiffAt_zero_of_flatConfiguration K hK hFlat ξ
  have h_iw_eq :
      iteratedDerivWithin 2
        (fun t : ℝ =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK)
            (linePotential K ξ t))
        (Set.Icc (0 : ℝ) 1) 0 =
      iteratedDeriv 2
        (fun t : ℝ =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK)
            (linePotential K ξ t)) 0 := by
    apply iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one
      _ zero_mem_Icc_zero_one
    refine hContDiff.of_le ?_
    exact (WithTop.coe_le_coe).mpr le_top
  rw [h_iw_eq]
  -- iteratedDeriv 2 f x = deriv (deriv f) x.
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  -- HasSecondDerivAt R_line 0 0 unfolds to HasDerivAt (deriv R_line) 0 0,
  -- which gives `deriv (deriv R_line) 0 = 0`.
  have hSecondAt : HasSecondDerivAt
      (fun t : ℝ =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK)
          (linePotential K ξ t))
      0 0 :=
    hSecond.remainder_secondVariation_zero ξ
  unfold HasSecondDerivAt at hSecondAt
  exact hSecondAt.deriv

/-- **CLOSURE: `CanonicalRemainderLineQuadraticTaylorZeroTarget`.**

The degree-2 Taylor polynomial at zero of the line-restricted canonical
remainder evaluates to zero at `t = 1`, given `FlatConfiguration` plus
the remainder's first- and second-variation inputs. The radius `r = 1` is
arbitrary (the property holds for all `ξ`). -/
theorem canonicalRemainderLineQuadraticTaylorZero_of_jetInputs
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hFirst : ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
      (canonicalReggeHessian K hK))
    (hSecond : ReggeActionRemainderSecondVariationInput K hK) :
    CanonicalRemainderLineQuadraticTaylorZeroTarget K hK := by
  refine ⟨1, by norm_num, ?_⟩
  intro ξ _hξ
  -- Expand `taylorWithinEval` of degree 2 as a sum of three iteratedDerivWithin.
  rw [taylor_within_apply]
  -- Sum over k ∈ {0, 1, 2}.
  have h0 := iteratedDerivWithin_zero_canonicalRemainderLine K hK ξ
  have h1 := iteratedDerivWithin_one_canonicalRemainderLine_of_jetInputs
    K hK hFlat hFirst ξ
  have h2 := iteratedDerivWithin_two_canonicalRemainderLine_of_jetInputs
    K hK hFlat hSecond ξ
  -- Each term in the sum vanishes since the iterated derivatives are zero.
  simp [Finset.sum_range_succ, h0, h1, h2]

/-- Constructor obtaining the remainder second-variation input from
`FlatConfiguration` plus the directional Hessian theorem. (Wrapper.) -/
theorem reggeActionRemainderSecondVariationInput_of_flat_directionalHessian
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hHessian : ReggeActionNonlinearHessianProof.NonlinearReggeDirectionalHessianTheorem K hK) :
    ReggeActionRemainderSecondVariationInput K hK :=
  ReggeActionNonlinearHessianProof.reggeActionRemainderSecondVariationInput_of_flat_nonlinearHessian
    K hK hFlat hHessian

/-- `CanonicalRemainderLineQuadraticTaylorZeroTarget` from `FlatConfiguration`,
the remainder first-variation input, and the directional Hessian theorem. -/
theorem canonicalRemainderLineQuadraticTaylorZero_of_flat_first_and_directionalHessian
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hFirst : ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
      (canonicalReggeHessian K hK))
    (hHessian : ReggeActionNonlinearHessianProof.NonlinearReggeDirectionalHessianTheorem K hK) :
    CanonicalRemainderLineQuadraticTaylorZeroTarget K hK :=
  canonicalRemainderLineQuadraticTaylorZero_of_jetInputs K hK hFlat hFirst
    (reggeActionRemainderSecondVariationInput_of_flat_directionalHessian
      K hK hFlat hHessian)

/-! ## §7. Decomposition of `CanonicalRemainderLineThirdDerivBoundTarget`

The third-derivative bound on the line-restricted canonical remainder
factors through two reductions:

(a) the **chain-rule identity** for `iteratedDeriv 3 (R ∘ lineCLM ξ) t`
    in terms of `iteratedFDeriv ℝ 3 R (t • ξ)` evaluated on three copies
    of `ξ`, which yields the `‖ξ‖^3` scaling, and

(b) the **local norm bound** on `‖iteratedFDeriv ℝ 3 R z‖` for `z` in a
    neighborhood of the flat point, which yields the constant `M`.

Both reductions hold by general Mathlib content (`iteratedFDeriv_comp_right`
plus `ContinuousMultilinearMap.le_opNorm` for (a), and
`ContDiffAt.continuousAt_iteratedFDeriv` for (b)). We expose them as named
sub-targets and discharge `CanonicalRemainderLineThirdDerivBoundTarget` from
their conjunction. Both sub-targets are now closed from `FlatConfiguration`
below. -/

/-- The continuous linear map `t ↦ t • ξ : ℝ →L[ℝ] VertexPotential K`. -/
noncomputable def lineCLM (K : Triangulation3D) (ξ : VertexPotential K) :
    ℝ →L[ℝ] VertexPotential K :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) ξ

@[simp] theorem lineCLM_apply
    (K : Triangulation3D) (ξ : VertexPotential K) (t : ℝ) :
    lineCLM K ξ t = t • ξ := by
  simp [lineCLM, ContinuousLinearMap.smulRight_apply]

@[simp] theorem lineCLM_eq_linePotential
    (K : Triangulation3D) (ξ : VertexPotential K) (t : ℝ) :
    lineCLM K ξ t = linePotential K ξ t := by
  rw [lineCLM_apply, ← linePotential_eq_smul]

theorem lineCLM_one (K : Triangulation3D) (ξ : VertexPotential K) :
    lineCLM K ξ 1 = ξ := by simp

/-- The line-restricted canonical remainder equals the composition of `R` with
`lineCLM K ξ`. -/
theorem canonicalRemainder_line_eq_comp
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    (fun t : ℝ =>
      reggeActionRemainder K hK (canonicalReggeHessian K hK)
        (linePotential K ξ t)) =
    (fun ξ' : VertexPotential K =>
      reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ') ∘
      (lineCLM K ξ) := by
  funext t
  show reggeActionRemainder K hK (canonicalReggeHessian K hK)
        (linePotential K ξ t) =
      reggeActionRemainder K hK (canonicalReggeHessian K hK) (lineCLM K ξ t)
  rw [lineCLM_eq_linePotential]

/-- Sub-target (a): the chain-rule pointwise bound, **localized** to a small
ball of radius `ε` around `0` and the unit segment `[0, 1]`.

Localization is necessary because the chain rule
`iteratedFDeriv 3 (R ∘ g) t = (iteratedFDeriv 3 R (g t)).compContinuousLinearMap (fun _ => g)`
holds globally only if `R` is C³ globally (which we don't have); within a
neighborhood of `0` where `R` is C³, the within-set chain rule
(`ContinuousLinearMap.iteratedFDerivWithin_comp_right`) plus
`iteratedFDerivWithin_of_isOpen` upgrade to free-space `iteratedFDeriv`.

The statement: there is some `ε > 0` such that, for all `ξ` with `‖ξ‖ < ε`
and all `t ∈ [0, 1]`, the third iterated derivative of the line-restricted
remainder at `t` is bounded by
`‖iteratedFDeriv ℝ 3 R (t • ξ)‖ · ‖ξ‖³`. -/
def CanonicalRemainderLineChainRuleBoundTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ (ξ : VertexPotential K), ‖ξ‖ < ε →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDeriv 3
            (fun s : ℝ =>
              reggeActionRemainder K hK (canonicalReggeHessian K hK)
                (linePotential K ξ s)) t|
          ≤ ‖iteratedFDeriv ℝ 3
              (fun ξ' : VertexPotential K =>
                reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
              (t • ξ)‖
            * ‖ξ‖ ^ (3 : ℕ)

/-- Sub-target (b): the local norm bound on the third Fréchet derivative of
`R` in a neighborhood of the flat point. This is `ContDiffAt` plus
`ContDiffAt.continuousAt_iteratedFDeriv`; we expose it as a named target so
the third-deriv bound is theorem-grade conditional on it. -/
def CanonicalRemainderIteratedFDerivLocalBoundTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∃ (δ M : ℝ), 0 < δ ∧ 0 ≤ M ∧
    ∀ z : VertexPotential K, ‖z‖ < δ →
      ‖iteratedFDeriv ℝ 3
          (fun ξ' : VertexPotential K =>
            reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
          z‖ ≤ M

/-- **CLOSURE CONDITIONAL ON CHAIN-RULE + LOCAL NORM BOUND.**

Given the chain-rule pointwise bound and the local norm bound on the third
Fréchet derivative of `R`, the line-restricted third-derivative bound holds
with the same `M` and `r := δ`, valid for all `‖ξ‖ < r` and all `t ∈ [0, 1]`.

Proof: for `‖ξ‖ < δ` and `t ∈ [0, 1]`, the point `t • ξ` has norm
`|t| · ‖ξ‖ ≤ ‖ξ‖ < δ`, so the local norm bound applies and yields
`‖iteratedFDeriv ℝ 3 R (t • ξ)‖ ≤ M`. The chain-rule pointwise bound then
gives `|iteratedDeriv 3 R_line t| ≤ M · ‖ξ‖³`. -/
theorem canonicalRemainderLineThirdDerivBound_of_chainRule_and_localNorm
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hChain : CanonicalRemainderLineChainRuleBoundTarget K hK)
    (hLocal : CanonicalRemainderIteratedFDerivLocalBoundTarget K hK) :
    CanonicalRemainderLineThirdDerivBoundTarget K hK := by
  rcases hLocal with ⟨δ, M, hδ, hM, hBound⟩
  rcases hChain with ⟨εC, hεC, hChainBnd⟩
  refine ⟨min δ εC, M, lt_min hδ hεC, hM, ?_⟩
  intro ξ hξ t ht
  have hξC : ‖ξ‖ < εC := lt_of_lt_of_le hξ (min_le_right _ _)
  have hξL : ‖ξ‖ < δ := lt_of_lt_of_le hξ (min_le_left _ _)
  -- Apply the localized chain-rule pointwise bound.
  have hChainPt := hChainBnd ξ hξC t ht
  -- Local norm bound at point `t • ξ`.
  have h_tξ_norm : ‖t • ξ‖ < δ := by
    have h_t_abs : |t| ≤ 1 := by
      rw [abs_of_nonneg ht.1]; exact ht.2
    rw [norm_smul, Real.norm_eq_abs]
    calc |t| * ‖ξ‖ ≤ 1 * ‖ξ‖ := by
            exact mul_le_mul_of_nonneg_right h_t_abs (norm_nonneg ξ)
      _ = ‖ξ‖ := one_mul _
      _ < δ := hξL
  have h_local := hBound (t • ξ) h_tξ_norm
  -- Combine: |iteratedDeriv 3 R_line t| ≤ ‖iteratedFDeriv 3 R (t • ξ)‖ · ‖ξ‖³ ≤ M · ‖ξ‖³.
  calc |iteratedDeriv 3
          (fun s : ℝ =>
            reggeActionRemainder K hK (canonicalReggeHessian K hK)
              (linePotential K ξ s)) t|
        ≤ ‖iteratedFDeriv ℝ 3
            (fun ξ' : VertexPotential K =>
              reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
            (t • ξ)‖
          * ‖ξ‖ ^ (3 : ℕ) := hChainPt
      _ ≤ M * ‖ξ‖ ^ (3 : ℕ) := by
          have hξ3 : 0 ≤ ‖ξ‖ ^ (3 : ℕ) := by positivity
          exact mul_le_mul_of_nonneg_right h_local hξ3

/-- **CLOSURE: `CanonicalRemainderIteratedFDerivLocalBoundTarget`.**

The third Fréchet derivative of the canonical remainder is locally bounded
at the flat point: by `ContDiffAt` and `ContDiffAt.continuousAt_iteratedFDeriv`,
`iteratedFDeriv ℝ 3 R` is continuous at `0`, so `‖iteratedFDeriv ℝ 3 R z‖ < ‖0‖ + 1`
for `z` close to `0`. We take `M := ‖iteratedFDeriv ℝ 3 R 0‖ + 1` and `δ` from
the continuity δ-ε statement. -/
theorem canonicalRemainder_iteratedFDeriv3_local_bound_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    CanonicalRemainderIteratedFDerivLocalBoundTarget K hK := by
  -- ContDiffAt of R at zeroPotential at order ⊤.
  have hContR : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun ξ' : VertexPotential K =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
      (zeroPotential K) :=
    canonicalRemainder_contDiffAt_zero_of_flatConfiguration K hK hFlat
  -- iteratedFDeriv 3 R is continuous at zeroPotential K.
  have hContAt :
      ContinuousAt
        (iteratedFDeriv ℝ 3
          (fun ξ' : VertexPotential K =>
            reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ'))
        (zeroPotential K) := by
    refine hContR.continuousAt_iteratedFDeriv (k := 3) ?_
    exact (WithTop.coe_le_coe).mpr le_top
  -- Set the bound `M := ‖iteratedFDeriv 3 R 0‖ + 1`.
  set M : ℝ := ‖iteratedFDeriv ℝ 3
        (fun ξ' : VertexPotential K =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
        (zeroPotential K)‖ + 1 with hM_def
  have hM_nonneg : 0 ≤ M := by
    have hpos : 0 ≤ ‖iteratedFDeriv ℝ 3
          (fun ξ' : VertexPotential K =>
            reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
          (zeroPotential K)‖ := norm_nonneg _
    linarith
  -- Continuity at zeroPotential K with tolerance 1.
  rw [Metric.continuousAt_iff] at hContAt
  obtain ⟨δ, hδ_pos, hδ⟩ := hContAt 1 (by norm_num : (0 : ℝ) < 1)
  refine ⟨δ, M, hδ_pos, hM_nonneg, ?_⟩
  intro z hz
  -- ‖z - zeroPotential K‖ = ‖z‖ since zeroPotential K is the zero element.
  have hz_dist : dist z (zeroPotential K) < δ := by
    rw [dist_eq_norm]
    have h_zp : (zeroPotential K) = (0 : VertexPotential K) := by
      funext i; simp [zeroPotential]
    rw [h_zp]
    simpa using hz
  -- Apply continuity bound.
  have h_dist := hδ hz_dist
  -- h_dist : dist (iteratedFDeriv 3 R z) (iteratedFDeriv 3 R 0) < 1
  rw [dist_eq_norm] at h_dist
  -- ‖A - B‖ < 1 implies ‖A‖ ≤ ‖B‖ + 1 = M.
  have h_le : ‖iteratedFDeriv ℝ 3
          (fun ξ' : VertexPotential K =>
            reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ') z‖
        ≤ ‖iteratedFDeriv ℝ 3
            (fun ξ' : VertexPotential K =>
              reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
            (zeroPotential K)‖ + 1 := by
    have h_tri := norm_sub_norm_le
      (iteratedFDeriv ℝ 3
        (fun ξ' : VertexPotential K =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ') z)
      (iteratedFDeriv ℝ 3
        (fun ξ' : VertexPotential K =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
        (zeroPotential K))
    linarith
  exact h_le

/-- **CLOSURE: `CanonicalRemainderLineChainRuleBoundTarget` (localized).**

Within a small open ball `ball(0, ε)` around the flat point, the canonical
remainder is `ContDiffOn ℝ 3` (from `canonicalRemainder_contDiffAt_zero_of_flatConfiguration`).
For `ξ` with `‖ξ‖ < ε` and `t ∈ [0, 1]`, the point `t • ξ` lies in this ball,
the within-set chain rule
`ContinuousLinearMap.iteratedFDerivWithin_comp_right` applies, the within-set
iterated Fréchet derivatives equal the free-space ones via
`iteratedFDerivWithin_of_isOpen`, and the resulting expansion of
`iteratedDeriv 3 (R ∘ lineCLM ξ) t` as
`(iteratedFDeriv ℝ 3 R (t • ξ))(fun _ : Fin 3 => ξ)` is bounded by
`‖iteratedFDeriv ℝ 3 R (t • ξ)‖ · ‖ξ‖³` via
`ContinuousMultilinearMap.le_opNorm`. -/
theorem canonicalRemainderLineChainRuleBound_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    CanonicalRemainderLineChainRuleBoundTarget K hK := by
  -- Step 1: extract a smooth nbhd of zeroPotential K.
  have hContR : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun ξ' : VertexPotential K =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
      (zeroPotential K) :=
    canonicalRemainder_contDiffAt_zero_of_flatConfiguration K hK hFlat
  have hContR3 : ContDiffAt ℝ (3 : ℕ∞)
      (fun ξ' : VertexPotential K =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
      (zeroPotential K) := by
    refine hContR.of_le ?_
    exact (WithTop.coe_le_coe).mpr le_top
  -- Get a ContDiffOn nbhd from ContDiffAt.
  rcases hContR3.contDiffOn (m := (3 : ℕ∞)) (le_refl _)
      (by intro h; simp at h) with ⟨u, hu_nhds, hRu⟩
  -- Refine to an open ball.
  rcases Metric.mem_nhds_iff.mp hu_nhds with ⟨ε, hε_pos, hball⟩
  -- ContDiffOn ℝ 3 R on ball(zeroPotential K, ε).
  have hRball : ContDiffOn ℝ (3 : ℕ∞)
      (fun ξ' : VertexPotential K =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
      (Metric.ball (zeroPotential K) ε) :=
    hRu.mono hball
  -- Translate ball center to 0 (since zeroPotential K = 0 in VP K).
  have hZP : (zeroPotential K) = (0 : VertexPotential K) := by
    funext i; simp [zeroPotential]
  -- Use ball at zero.
  have hRball0 : ContDiffOn ℝ (3 : ℕ∞)
      (fun ξ' : VertexPotential K =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
      (Metric.ball (0 : VertexPotential K) ε) := by
    rw [hZP] at hRball
    exact hRball
  refine ⟨ε, hε_pos, ?_⟩
  intro ξ hξ t ht
  -- Step 2: `t • ξ ∈ ball 0 ε`.
  have h_t_abs : |t| ≤ 1 := by
    rw [abs_of_nonneg ht.1]; exact ht.2
  have h_tξ_in_ball : (t • ξ) ∈ Metric.ball (0 : VertexPotential K) ε := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    calc |t| * ‖ξ‖ ≤ 1 * ‖ξ‖ :=
          mul_le_mul_of_nonneg_right h_t_abs (norm_nonneg ξ)
      _ = ‖ξ‖ := one_mul _
      _ < ε := hξ
  -- Step 3: lineCLM ξ ⁻¹' (ball 0 ε) is open in ℝ.
  have h_open_pre : IsOpen (lineCLM K ξ ⁻¹' Metric.ball (0 : VertexPotential K) ε) :=
    Metric.isOpen_ball.preimage (lineCLM K ξ).continuous
  -- t ∈ preimage (since lineCLM K ξ t = t • ξ ∈ ball).
  have h_t_in_pre : t ∈ lineCLM K ξ ⁻¹' Metric.ball (0 : VertexPotential K) ε := by
    rw [Set.mem_preimage, lineCLM_apply]; exact h_tξ_in_ball
  -- UniqueDiffOn on preimage and on ball.
  have h_uniq_ball : UniqueDiffOn ℝ (Metric.ball (0 : VertexPotential K) ε) :=
    Metric.isOpen_ball.uniqueDiffOn
  have h_uniq_pre : UniqueDiffOn ℝ
      (lineCLM K ξ ⁻¹' Metric.ball (0 : VertexPotential K) ε) :=
    h_open_pre.uniqueDiffOn
  -- Step 4: chain rule via `iteratedFDerivWithin_comp_right`.
  have h_chain_within :
      iteratedFDerivWithin ℝ 3
        (fun s : ℝ =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK)
            ((lineCLM K ξ) s))
        (lineCLM K ξ ⁻¹' Metric.ball (0 : VertexPotential K) ε) t =
        (iteratedFDerivWithin ℝ 3
          (fun ξ' : VertexPotential K =>
            reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
          (Metric.ball (0 : VertexPotential K) ε)
          (lineCLM K ξ t)).compContinuousLinearMap (fun _ : Fin 3 => lineCLM K ξ) := by
    have h := (lineCLM K ξ).iteratedFDerivWithin_comp_right
      (f := fun ξ' : VertexPotential K =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
      (n := (3 : ℕ∞)) hRball0 h_uniq_ball h_uniq_pre h_tξ_in_ball
      (i := 3) (le_refl _)
    -- Adjust the LHS to use the function form rather than ∘.
    convert h using 2
  -- Step 5: convert iteratedFDerivWithin to iteratedFDeriv (open sets).
  have ht_in_ball : lineCLM K ξ t ∈ Metric.ball (0 : VertexPotential K) ε := by
    rw [lineCLM_apply]; exact h_tξ_in_ball
  have h_within_eq_R :
      iteratedFDerivWithin ℝ 3
        (fun ξ' : VertexPotential K =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
        (Metric.ball (0 : VertexPotential K) ε)
        (lineCLM K ξ t) =
      iteratedFDeriv ℝ 3
        (fun ξ' : VertexPotential K =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
        (lineCLM K ξ t) :=
    iteratedFDerivWithin_of_isOpen 3 Metric.isOpen_ball ht_in_ball
  have h_within_eq_comp :
      iteratedFDerivWithin ℝ 3
        (fun s : ℝ =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK)
            ((lineCLM K ξ) s))
        (lineCLM K ξ ⁻¹' Metric.ball (0 : VertexPotential K) ε) t =
      iteratedFDeriv ℝ 3
        (fun s : ℝ =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK)
            ((lineCLM K ξ) s)) t :=
    iteratedFDerivWithin_of_isOpen 3 h_open_pre h_t_in_pre
  -- Combine: free-space iteratedFDeriv chain-rule formula.
  have h_chain_free :
      iteratedFDeriv ℝ 3
        (fun s : ℝ =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK)
            ((lineCLM K ξ) s)) t =
      (iteratedFDeriv ℝ 3
        (fun ξ' : VertexPotential K =>
          reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
        (lineCLM K ξ t)).compContinuousLinearMap (fun _ : Fin 3 => lineCLM K ξ) := by
    rw [← h_within_eq_comp, h_chain_within, h_within_eq_R]
  -- Step 6: rewrite the line-restricted remainder via `lineCLM`.
  have h_eq_line :
      (fun s : ℝ =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK)
          (linePotential K ξ s)) =
      (fun s : ℝ =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK)
          ((lineCLM K ξ) s)) := by
    funext s
    rw [lineCLM_eq_linePotential]
  -- Step 7: bound `|iteratedDeriv 3 R_line t|` using the chain-rule formula.
  rw [h_eq_line]
  -- iteratedDeriv 3 f t = (iteratedFDeriv ℝ 3 f t)(fun _ => 1).
  rw [iteratedDeriv]
  rw [h_chain_free]
  -- Now: |((iteratedFDeriv 3 R (lineCLM ξ t)).compCLM (fun _ => lineCLM ξ))(fun _ => 1)|
  -- = |(iteratedFDeriv 3 R (t • ξ))(fun _ => lineCLM ξ 1)|
  -- = |(iteratedFDeriv 3 R (t • ξ))(fun _ => ξ)|
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [lineCLM_apply]
  -- Goal: |(iteratedFDeriv 3 R (t • ξ))(fun _ => lineCLM ξ 1)| ≤ ‖...‖ · ‖ξ‖^3
  -- Use lineCLM_one to simplify (fun _ => lineCLM K ξ 1) = (fun _ => ξ).
  have h_lcm1 : (fun _ : Fin 3 => lineCLM K ξ 1) = (fun _ : Fin 3 => ξ) := by
    funext i; exact lineCLM_one K ξ
  rw [h_lcm1]
  -- Bound by `ContinuousMultilinearMap.le_opNorm`.
  have h_op := ContinuousMultilinearMap.le_opNorm
    (iteratedFDeriv ℝ 3
      (fun ξ' : VertexPotential K =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
      (t • ξ))
    (fun _ : Fin 3 => ξ)
  -- h_op : ‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖
  -- For m = const ξ on Fin 3, ∏ i, ‖ξ‖ = ‖ξ‖^3.
  have h_prod : (∏ _i : Fin 3, ‖ξ‖) = ‖ξ‖ ^ (3 : ℕ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Convert ‖_‖ to |_| for the real-valued LHS via `abs_eq_norm` on ℝ.
  have h_abs_eq : |(iteratedFDeriv ℝ 3
            (fun ξ' : VertexPotential K =>
              reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
            (t • ξ))
          (fun _ : Fin 3 => ξ)| =
        ‖(iteratedFDeriv ℝ 3
            (fun ξ' : VertexPotential K =>
              reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
            (t • ξ))
          (fun _ : Fin 3 => ξ)‖ := by
    rfl
  rw [h_abs_eq]
  calc ‖(iteratedFDeriv ℝ 3
          (fun ξ' : VertexPotential K =>
            reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
          (t • ξ))
        (fun _ : Fin 3 => ξ)‖
      ≤ ‖iteratedFDeriv ℝ 3
          (fun ξ' : VertexPotential K =>
            reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
          (t • ξ)‖ * (∏ _i : Fin 3, ‖ξ‖) := h_op
    _ = ‖iteratedFDeriv ℝ 3
          (fun ξ' : VertexPotential K =>
            reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ')
          (t • ξ)‖ * ‖ξ‖ ^ (3 : ℕ) := by rw [h_prod]

/-- **CLOSURE OF `CanonicalRemainderLineThirdDerivBoundTarget`.**

The third-derivative bound on the line-restricted canonical remainder
follows from `FlatConfiguration` alone, by combining the chain-rule bound
(`canonicalRemainderLineChainRuleBound_of_flatConfiguration`) with the local
norm bound (`canonicalRemainder_iteratedFDeriv3_local_bound_of_flatConfiguration`)
through `canonicalRemainderLineThirdDerivBound_of_chainRule_and_localNorm`. -/
theorem canonicalRemainderLineThirdDerivBound_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    CanonicalRemainderLineThirdDerivBoundTarget K hK :=
  canonicalRemainderLineThirdDerivBound_of_chainRule_and_localNorm K hK
    (canonicalRemainderLineChainRuleBound_of_flatConfiguration K hK hFlat)
    (canonicalRemainder_iteratedFDeriv3_local_bound_of_flatConfiguration K hK hFlat)

/-- Composite: line-Taylor data target from the four sub-targets:
ContDiff, QuadraticTaylorZero, Chain-rule, and Local norm bound. All four are
closed in this module; this theorem remains as the explicit assembly point. -/
theorem canonicalRemainderLineTaylorData_of_jetInputs_chainRule_and_localNorm
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hFirst : ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
      (canonicalReggeHessian K hK))
    (hSecond : ReggeActionRemainderSecondVariationInput K hK)
    (hChain : CanonicalRemainderLineChainRuleBoundTarget K hK)
    (hLocal : CanonicalRemainderIteratedFDerivLocalBoundTarget K hK) :
    CanonicalRemainderLineTaylorDataTarget K hK :=
  lineTaylorData_of_splitTargets K hK
    (canonicalRemainderLineContDiff_of_flatConfiguration K hK hFlat)
    (canonicalRemainderLineQuadraticTaylorZero_of_jetInputs K hK hFlat hFirst hSecond)
    (canonicalRemainderLineThirdDerivBound_of_chainRule_and_localNorm K hK hChain hLocal)

/-- **CASCADE CLOSURE: line-Taylor data from `FlatConfiguration` + jet inputs.**

With the chain-rule bound now closed from `FlatConfiguration` alone
(`canonicalRemainderLineChainRuleBound_of_flatConfiguration`) and the local
norm bound also closed from `FlatConfiguration` alone
(`canonicalRemainder_iteratedFDeriv3_local_bound_of_flatConfiguration`), the
line-Taylor data target closes from `FlatConfiguration` plus the remainder
first- and second-variation inputs. The latter two inputs are themselves
constructible from `FlatConfiguration` plus the directional Hessian theorem
(see `ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput`
and `reggeActionRemainderSecondVariationInput_of_flat_directionalHessian`). -/
theorem canonicalRemainderLineTaylorData_of_flat_and_remainderJets
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hFirst : ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
      (canonicalReggeHessian K hK))
    (hSecond : ReggeActionRemainderSecondVariationInput K hK) :
    CanonicalRemainderLineTaylorDataTarget K hK :=
  canonicalRemainderLineTaylorData_of_jetInputs_chainRule_and_localNorm
    K hK hFlat hFirst hSecond
    (canonicalRemainderLineChainRuleBound_of_flatConfiguration K hK hFlat)
    (canonicalRemainder_iteratedFDeriv3_local_bound_of_flatConfiguration K hK hFlat)

/-- **CASCADE CLOSURE: cubic Taylor theorem from `FlatConfiguration` + jet
inputs.** -/
theorem nonlinearReggeCubicTaylorTheorem_of_flat_and_remainderJets
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hFirst : ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
      (canonicalReggeHessian K hK))
    (hSecond : ReggeActionRemainderSecondVariationInput K hK) :
    NonlinearReggeCubicTaylorTheorem K hK :=
  nonlinearReggeCubicTaylorTheorem_of_lineTaylorData K hK
    (canonicalRemainderLineTaylorData_of_flat_and_remainderJets
      K hK hFlat hFirst hSecond)

/-! ## §8. 1B-REM audit certificate

The local analytic-remainder lane is closed at the generic finite
triangulation level: from `FlatConfiguration` plus the standard remainder
first- and second-variation inputs, Lean has the line-Taylor data target and
the nonlinear cubic Taylor theorem.  This certificate is intentionally
theorem-valued, not a list of stale `Prop` targets. -/

structure CanonicalRemainderAnalyticClosureCert
    (K : Triangulation3D) (hK : IncidenceConsistent K) where
  line_contDiff_from_flat :
    FlatConfiguration K hK →
      CanonicalRemainderLineContDiffTarget K hK
  line_quadratic_zero_from_jets :
    FlatConfiguration K hK →
      ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
        (canonicalReggeHessian K hK) →
      ReggeActionRemainderSecondVariationInput K hK →
        CanonicalRemainderLineQuadraticTaylorZeroTarget K hK
  line_chain_rule_bound_from_flat :
    FlatConfiguration K hK →
      CanonicalRemainderLineChainRuleBoundTarget K hK
  iteratedFDeriv3_local_bound_from_flat :
    FlatConfiguration K hK →
      CanonicalRemainderIteratedFDerivLocalBoundTarget K hK
  line_third_deriv_bound_from_flat :
    FlatConfiguration K hK →
      CanonicalRemainderLineThirdDerivBoundTarget K hK
  line_taylor_data_from_flat_and_jets :
    FlatConfiguration K hK →
      ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
        (canonicalReggeHessian K hK) →
      ReggeActionRemainderSecondVariationInput K hK →
        CanonicalRemainderLineTaylorDataTarget K hK
  cubic_taylor_from_flat_and_jets :
    FlatConfiguration K hK →
      ReggeActionFirstVariation.ReggeActionRemainderFirstVariationInput K hK
        (canonicalReggeHessian K hK) →
      ReggeActionRemainderSecondVariationInput K hK →
        NonlinearReggeCubicTaylorTheorem K hK

def canonicalRemainderAnalyticClosureCert
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    CanonicalRemainderAnalyticClosureCert K hK where
  line_contDiff_from_flat := fun hFlat =>
    canonicalRemainderLineContDiff_of_flatConfiguration K hK hFlat
  line_quadratic_zero_from_jets := fun hFlat hFirst hSecond =>
    canonicalRemainderLineQuadraticTaylorZero_of_jetInputs K hK hFlat hFirst hSecond
  line_chain_rule_bound_from_flat := fun hFlat =>
    canonicalRemainderLineChainRuleBound_of_flatConfiguration K hK hFlat
  iteratedFDeriv3_local_bound_from_flat := fun hFlat =>
    canonicalRemainder_iteratedFDeriv3_local_bound_of_flatConfiguration K hK hFlat
  line_third_deriv_bound_from_flat := fun hFlat =>
    canonicalRemainderLineThirdDerivBound_of_flatConfiguration K hK hFlat
  line_taylor_data_from_flat_and_jets := fun hFlat hFirst hSecond =>
    canonicalRemainderLineTaylorData_of_flat_and_remainderJets K hK hFlat hFirst hSecond
  cubic_taylor_from_flat_and_jets := fun hFlat hFirst hSecond =>
    nonlinearReggeCubicTaylorTheorem_of_flat_and_remainderJets K hK hFlat hFirst hSecond

end

end ReggeActionCubicTaylorBound
end Geometry
end IndisputableMonolith
