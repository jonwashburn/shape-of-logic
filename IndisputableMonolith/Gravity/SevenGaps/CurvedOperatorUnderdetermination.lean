import IndisputableMonolith.Gravity.SevenGaps.DiscreteLichnerowicz
import IndisputableMonolith.Gravity.Analysis.SpectralConvergence

/-!
# Gap 4 blocker: flat spectrum does not determine curvature coupling

The current certified spectrum theorem in `DiscreteLichnerowicz` has an exact
but narrow reach.  It treats axis modes of the componentwise flat lattice
Laplacian, and its continuum Lichnerowicz value is introduced definitionally
from the flat reduction `Delta_L = -Delta`.  It contains no Riemann-curvature
endomorphism and therefore cannot determine a curved-background coupling.

This module turns that reach gap into a theorem rather than a status flag.
On the actual lattice tensor-field type, it constructs two explicit
zeroth-order curvature-coupled operator families.  Both reduce to the same
`-discLap3` operator for every field and every resolution at zero curvature,
but they differ on a concrete nonzero TT polarization at every nonzero
curvature.  Their eigenvalue branches both satisfy the same flat theorem and
both have certified continuum limits, with different curved limits.

The second half isolates the exact missing analytic premise.  Relative to the
existing flat convergence theorem, convergence of an arbitrary curved
eigenvalue family is equivalent to convergence of its curvature correction
(curved value minus the certified flat value).  A quantitative `C / N^2`
correction bound is a sufficient discretization-consistency certificate via
`SpectralConvergence.eigenvalue_limit_of_uniform_bound`.

Nothing here defines the physical curved Lichnerowicz operator.  The scalar
parameter `rho` is a deliberately minimal curvature proxy used to exhibit
non-identifiability.  A closing Gap 4 construction must derive the genuine
curvature endomorphism from curved discrete geometry and prove its correction
consistent with the continuum Riemann coupling.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace CurvedOperatorUnderdetermination

open Filter Topology

noncomputable section

/-! ## Two genuinely distinct curved extensions of the flat operator -/

/-- A one-parameter family of lattice tensor-field operators.  The first term
is the certified positive flat operator `-discLap3`; the second is a
zeroth-order scalar curvature coupling.  This is a countermodel family, not a
definition of the physical curved Lichnerowicz operator. -/
def curvatureCoupledOperator (coupling rho : ℝ) (N : ℕ)
    (H : DiscreteLichnerowicz.LatticeTensorField) : DiscreteLichnerowicz.LatticeTensorField :=
  fun x => (-1 : ℝ) • DiscreteLichnerowicz.discLap3 N H x + (coupling * rho) • H x

/-- The first explicit curved extension, with curvature coefficient one. -/
def singleCurvatureExtension (rho : ℝ) (N : ℕ)
    (H : DiscreteLichnerowicz.LatticeTensorField) : DiscreteLichnerowicz.LatticeTensorField :=
  curvatureCoupledOperator 1 rho N H

/-- The second explicit curved extension, with curvature coefficient two. -/
def doubleCurvatureExtension (rho : ℝ) (N : ℕ)
    (H : DiscreteLichnerowicz.LatticeTensorField) : DiscreteLichnerowicz.LatticeTensorField :=
  curvatureCoupledOperator 2 rho N H

/-- A constant plus-polarized tensor field used to distinguish the two
operator families. -/
def constantPlusField : DiscreteLichnerowicz.LatticeTensorField := fun _ => DiscreteLichnerowicz.epsPlus

/-- The flat lattice Laplacian annihilates the constant plus field. -/
theorem discLap3_constantPlusField_zero (N : ℕ) :
    DiscreteLichnerowicz.discLap3 N constantPlusField = 0 := by
  funext x
  ext i j
  simp only [DiscreteLichnerowicz.discLap3, constantPlusField,
    Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply]
  rw [Fin.sum_univ_three]
  ring

/-- Every member of the countermodel family has exactly the same complete
flat specialization, on every field and at every lattice resolution. -/
theorem curvatureCoupledOperator_flat_specialization
    (coupling : ℝ) (N : ℕ) (H : DiscreteLichnerowicz.LatticeTensorField) :
    curvatureCoupledOperator coupling 0 N H =
      curvatureCoupledOperator 0 0 N H := by
  ext x i j
  simp [curvatureCoupledOperator]

/-- The two named curved extensions agree on the entire flat specialization,
not merely on one mode or one eigenvalue. -/
theorem extensions_agree_on_entire_flat_specialization :
    ∀ (N : ℕ) (H : DiscreteLichnerowicz.LatticeTensorField),
      singleCurvatureExtension 0 N H = doubleCurvatureExtension 0 N H := by
  intro N H
  trans curvatureCoupledOperator 0 0 N H
  · exact curvatureCoupledOperator_flat_specialization 1 N H
  · exact (curvatureCoupledOperator_flat_specialization 2 N H).symm

/-- At every nonzero curvature and every resolution, the two extensions are
different operators.  The witness is the constant plus polarization, on
which the flat Laplacian vanishes while the two curvature coefficients act
by `rho` and `2 * rho`. -/
theorem extensions_distinct_at_nonzero_curvature
    (rho : ℝ) (hrho : rho ≠ 0) (N : ℕ) :
    (singleCurvatureExtension rho N :
        DiscreteLichnerowicz.LatticeTensorField → DiscreteLichnerowicz.LatticeTensorField) ≠
      (doubleCurvatureExtension rho N :
        DiscreteLichnerowicz.LatticeTensorField → DiscreteLichnerowicz.LatticeTensorField) := by
  intro hEq
  have hField := congrFun hEq constantPlusField
  have hSite := congrFun hField ((0, 0, 0) : DiscreteLichnerowicz.Site3)
  have hEntry := congrFun (congrFun hSite (1 : Fin 3)) (1 : Fin 3)
  simp [singleCurvatureExtension, doubleCurvatureExtension,
    curvatureCoupledOperator, DiscreteLichnerowicz.discLap3, constantPlusField, DiscreteLichnerowicz.epsPlus] at hEntry
  have hEntryRe := congrArg Complex.re hEntry
  norm_num at hEntryRe
  exact hrho (by linarith)

/-! ## The corresponding eigenvalue branches -/

/-- Discrete eigenvalue branch associated with the scalar curvature coupling. -/
def curvedDiscreteEigenvalue (coupling rho : ℝ) (N k : ℕ) : ℝ :=
  DiscreteLichnerowicz.discreteEigenvalue N k + coupling * rho

/-- Continuum eigenvalue branch associated with the same scalar curvature
coupling.  The flat part is exactly the MODEL value from
`DiscreteLichnerowicz`; the curvature term is countermodel data. -/
def curvedContinuumEigenvalue (coupling rho : ℝ) (k : ℕ) : ℝ :=
  DiscreteLichnerowicz.lichnerowiczFlatEigenvalue k + coupling * rho

/-- The countermodel operator acts on every certified transverse axis mode
with the corresponding curved eigenvalue. -/
theorem curvatureCoupledOperator_planeH
    (coupling rho : ℝ) (N k : ℕ)
    (eps : Matrix (Fin 3) (Fin 3) ℂ) (hrow : ∀ j, eps 0 j = 0)
    (x : DiscreteLichnerowicz.Site3) :
    curvatureCoupledOperator coupling rho N (DiscreteLichnerowicz.planeH N (k : ℤ) eps) x =
      curvedDiscreteEigenvalue coupling rho N k •
        DiscreteLichnerowicz.planeH N (k : ℤ) eps x := by
  have hFlat :=
    (DiscreteLichnerowicz.discrete_tt_spectrum_converges_to_flat_lichnerowicz k eps hrow).2.1 N x
  unfold curvatureCoupledOperator
  rw [hFlat, smul_smul, ← add_smul]
  congr 1
  simp only [curvedDiscreteEigenvalue]
  ring

/-- Each countermodel branch converges, by adding its constant curvature
correction to the existing certified flat convergence theorem. -/
theorem curvedDiscreteEigenvalue_tendsto
    (coupling rho : ℝ) (k : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => curvedDiscreteEigenvalue coupling rho N k)
      Filter.atTop (nhds (curvedContinuumEigenvalue coupling rho k)) := by
  exact (DiscreteLichnerowicz.discreteEigenvalue_tendsto k).add tendsto_const_nhds

/-- The two curved continuum values differ whenever curvature is nonzero. -/
theorem curvedContinuumEigenvalues_distinct
    (rho : ℝ) (hrho : rho ≠ 0) (k : ℕ) :
    curvedContinuumEigenvalue 1 rho k ≠
      curvedContinuumEigenvalue 2 rho k := by
  intro h
  unfold curvedContinuumEigenvalue at h
  exact hrho (by linarith)

/-- Certified underdetermination package.  The same full flat operator data
admits two operator extensions that separate at every nonzero curvature; both
eigenvalue branches converge, but to distinct curved values. -/
theorem flat_spectrum_underdetermines_curvature_coupling
    (rho : ℝ) (hrho : rho ≠ 0) (k : ℕ) :
    (∀ (N : ℕ) (H : DiscreteLichnerowicz.LatticeTensorField),
      singleCurvatureExtension 0 N H = doubleCurvatureExtension 0 N H) ∧
    (∀ N : ℕ,
      (singleCurvatureExtension rho N :
          DiscreteLichnerowicz.LatticeTensorField → DiscreteLichnerowicz.LatticeTensorField) ≠
        (doubleCurvatureExtension rho N :
          DiscreteLichnerowicz.LatticeTensorField → DiscreteLichnerowicz.LatticeTensorField)) ∧
    Filter.Tendsto
      (fun N : ℕ => curvedDiscreteEigenvalue 1 rho N k)
      Filter.atTop (nhds (curvedContinuumEigenvalue 1 rho k)) ∧
    Filter.Tendsto
      (fun N : ℕ => curvedDiscreteEigenvalue 2 rho N k)
      Filter.atTop (nhds (curvedContinuumEigenvalue 2 rho k)) ∧
    curvedContinuumEigenvalue 1 rho k ≠
      curvedContinuumEigenvalue 2 rho k :=
  ⟨extensions_agree_on_entire_flat_specialization,
    fun N => extensions_distinct_at_nonzero_curvature rho hrho N,
    curvedDiscreteEigenvalue_tendsto 1 rho k,
    curvedDiscreteEigenvalue_tendsto 2 rho k,
    curvedContinuumEigenvalues_distinct rho hrho k⟩

/-! ## Exact missing curved discretization-consistency premise -/

/-- A curved discrete spectrum converges to its proposed curved continuum
spectrum at every curvature and wavenumber.  This is the Gap 4 target shape,
kept separate from the premise below. -/
def CurvedSpectrumConverges
    (discreteCurved : ℝ → ℕ → ℕ → ℝ)
    (continuumCurved : ℝ → ℕ → ℝ) : Prop :=
  ∀ rho k,
    Filter.Tendsto (fun N => discreteCurved rho N k)
      Filter.atTop (nhds (continuumCurved rho k))

/-- The exact missing consistency premise relative to the certified flat
theorem: the discrete curvature correction converges to the continuum
curvature correction.  This does not assume the curved target itself; it
isolates the part absent from `DiscreteLichnerowicz`. -/
def CurvatureCorrectionConsistent
    (discreteCurved : ℝ → ℕ → ℕ → ℝ)
    (continuumCurved : ℝ → ℕ → ℝ) : Prop :=
  ∀ rho k,
    Filter.Tendsto
      (fun N =>
        discreteCurved rho N k - DiscreteLichnerowicz.discreteEigenvalue N k)
      Filter.atTop
      (nhds
        (continuumCurved rho k - DiscreteLichnerowicz.lichnerowiczFlatEigenvalue k))

/-- Quantitative certificate form of curvature-correction consistency. -/
def CurvatureCorrectionRateBound
    (discreteCurved : ℝ → ℕ → ℕ → ℝ)
    (continuumCurved : ℝ → ℕ → ℝ) : Prop :=
  ∀ rho k, ∃ C : ℝ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    |(discreteCurved rho N k - DiscreteLichnerowicz.discreteEigenvalue N k) -
        (continuumCurved rho k - DiscreteLichnerowicz.lichnerowiczFlatEigenvalue k)|
      ≤ C / (N : ℝ) ^ 2

/-- Blocker theorem: because the flat branch already converges, full curved
convergence is equivalent to convergence of precisely the omitted curvature
correction.  Thus the flat theorem cannot discharge the curved target unless
this independent consistency premise is supplied. -/
theorem curvedSpectrumConverges_iff_curvatureCorrectionConsistent
    (discreteCurved : ℝ → ℕ → ℕ → ℝ)
    (continuumCurved : ℝ → ℕ → ℝ) :
    CurvedSpectrumConverges discreteCurved continuumCurved ↔
      CurvatureCorrectionConsistent discreteCurved continuumCurved := by
  constructor
  · intro hCurved rho k
    exact (hCurved rho k).sub (DiscreteLichnerowicz.discreteEigenvalue_tendsto k)
  · intro hCorrection rho k
    have hSum :=
      (DiscreteLichnerowicz.discreteEigenvalue_tendsto k).add (hCorrection rho k)
    convert hSum using 1
    · funext N
      ring
    · congr 1
      rw [DiscreteLichnerowicz.lichnerowiczFlatEigenvalue]
      ring_nf

/-- A quantitative `C / N^2` bound on the curvature correction supplies the
exact missing consistency premise, using the spectral convergence toolkit. -/
theorem curvatureCorrectionConsistent_of_rateBound
    (discreteCurved : ℝ → ℕ → ℕ → ℝ)
    (continuumCurved : ℝ → ℕ → ℝ)
    (hRate : CurvatureCorrectionRateBound discreteCurved continuumCurved) :
    CurvatureCorrectionConsistent discreteCurved continuumCurved := by
  intro rho k
  obtain ⟨C, N0, hBound⟩ := hRate rho k
  exact Gravity.Analysis.eigenvalue_limit_of_uniform_bound
    (fun N => discreteCurved rho N k - DiscreteLichnerowicz.discreteEigenvalue N k)
    (continuumCurved rho k - DiscreteLichnerowicz.lichnerowiczFlatEigenvalue k)
    C N0 hBound

/-- Package theorem in the direction needed by a future curved
discretization: a proved correction-rate estimate, combined with the
existing flat convergence theorem, yields curved spectral convergence. -/
theorem curvedSpectrumConverges_of_correctionRateBound
    (discreteCurved : ℝ → ℕ → ℕ → ℝ)
    (continuumCurved : ℝ → ℕ → ℝ)
    (hRate : CurvatureCorrectionRateBound discreteCurved continuumCurved) :
    CurvedSpectrumConverges discreteCurved continuumCurved :=
  (curvedSpectrumConverges_iff_curvatureCorrectionConsistent
    discreteCurved continuumCurved).2
      (curvatureCorrectionConsistent_of_rateBound
        discreteCurved continuumCurved hRate)

/-- Every scalar-coupling countermodel has a zero-error correction-rate
certificate.  Hence consistency alone cannot select the physical coupling;
the continuum curvature endomorphism itself must be independently derived. -/
theorem curvedEigenvalueFamily_rateBound (coupling : ℝ) :
    CurvatureCorrectionRateBound
      (fun rho N k => curvedDiscreteEigenvalue coupling rho N k)
      (fun rho k => curvedContinuumEigenvalue coupling rho k) := by
  intro rho k
  refine ⟨0, 1, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  simp only [curvedDiscreteEigenvalue, curvedContinuumEigenvalue]
  rw [show
      (DiscreteLichnerowicz.discreteEigenvalue N k + coupling * rho -
          DiscreteLichnerowicz.discreteEigenvalue N k) -
        (DiscreteLichnerowicz.lichnerowiczFlatEigenvalue k + coupling * rho -
          DiscreteLichnerowicz.lichnerowiczFlatEigenvalue k) = 0 by ring]
  simp

/-- Final certified blocker.  Coefficients one and two both satisfy the same
flat specialization and the same quantitative correction-consistency shape,
yet they are distinct at every nonzero curvature.  Therefore the existing
flat spectrum theorem plus generic consistency machinery does not determine
the curved Lichnerowicz curvature coupling. -/
theorem gap4_curvature_coupling_blocker
    (rho : ℝ) (hrho : rho ≠ 0) :
    (∀ (N : ℕ) (H : DiscreteLichnerowicz.LatticeTensorField),
      singleCurvatureExtension 0 N H = doubleCurvatureExtension 0 N H) ∧
    (∀ N : ℕ,
      (singleCurvatureExtension rho N :
          DiscreteLichnerowicz.LatticeTensorField → DiscreteLichnerowicz.LatticeTensorField) ≠
        (doubleCurvatureExtension rho N :
          DiscreteLichnerowicz.LatticeTensorField → DiscreteLichnerowicz.LatticeTensorField)) ∧
    CurvatureCorrectionRateBound
      (fun r N k => curvedDiscreteEigenvalue 1 r N k)
      (fun r k => curvedContinuumEigenvalue 1 r k) ∧
    CurvatureCorrectionRateBound
      (fun r N k => curvedDiscreteEigenvalue 2 r N k)
      (fun r k => curvedContinuumEigenvalue 2 r k) :=
  ⟨extensions_agree_on_entire_flat_specialization,
    fun N => extensions_distinct_at_nonzero_curvature rho hrho N,
    curvedEigenvalueFamily_rateBound 1,
    curvedEigenvalueFamily_rateBound 2⟩

end

end CurvedOperatorUnderdetermination
end SevenGaps
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.SevenGaps.CurvedOperatorUnderdetermination.extensions_agree_on_entire_flat_specialization
#print axioms IndisputableMonolith.Gravity.SevenGaps.CurvedOperatorUnderdetermination.extensions_distinct_at_nonzero_curvature
#print axioms IndisputableMonolith.Gravity.SevenGaps.CurvedOperatorUnderdetermination.flat_spectrum_underdetermines_curvature_coupling
#print axioms IndisputableMonolith.Gravity.SevenGaps.CurvedOperatorUnderdetermination.curvedSpectrumConverges_iff_curvatureCorrectionConsistent
#print axioms IndisputableMonolith.Gravity.SevenGaps.CurvedOperatorUnderdetermination.curvedSpectrumConverges_of_correctionRateBound
#print axioms IndisputableMonolith.Gravity.SevenGaps.CurvedOperatorUnderdetermination.gap4_curvature_coupling_blocker
