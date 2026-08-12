import Mathlib
import IndisputableMonolith.Gravity.Analysis.ContinuumTTSecondVariation4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactMidpointM2TTIdentity4D

/-!
# Regge's normalization constant, derived and then measured by the dictionary

Arc 2, step 7, second half.  `ContinuumTTSecondVariation4D` derived, from the
Levi-Civita connection alone and with no access to anything on the Regge side,
that the phase average of `d²/dt² ∫ R √g` per unit volume on a real
transverse-traceless cosine wave is

  `ehFace H k = -(1/4) · |k|² · ‖H‖²_F`.

This module puts that beside the banked dictionary value and asks what constant
relates them.

## A4, the fourth classical input

The discrete object is the **Regge action** `Σ_h A_h δ_h`, area times deficit
(the generator's own header: `S'' = Σ_h (dA_h)(dδ_h)`).  That is not
`∫ R √g`; Regge's normalization is

  `Σ_h A_h δ_h = ρ · ∫ R √g`,  with  `ρ = 1/2`.

This module does **not** assume `ρ`.  It leaves it free, shows the dictionary
forces `ρ = 1/2` (§4), refutes `ρ = 1` which is what the frozen preflight
implicitly used (§5), and checks `ρ = 1/2` independently against Gauss-Bonnet on
two triangulated spheres (§6).

## The result

The factor of two between the computed `-(1/8)` and the frozen `-(1/4)` is
Regge's normalization constant.  Both numbers are correct; they are faces of two
different actions.  `discreteBookkeepingFactor := 2` is `1/ρ`, and it is
derivable, so the historical gate did not fail because the Regge computation was
wrong.  It failed because the two sides were varying different functionals.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeNormalizationDerived4D

open BigOperators
open EdgeTTDecomposition4D
  (Mat4 IsTT momentumSq axisWave axisTTPlus axisTTPlus_isTT)
open ReggeExactFlatHessianBlochSymbol4D (exactMidpointBlochM2)
open ReggeExactMidpointM2TTIdentity4D
  (frobeniusNormSq waveNormSq exactMidpointBlochM2_eq_neg_eighth_frobenius_tt)
open ContinuumTTSecondVariation4D
  (ehFace frobSq phaseAverage densityOfPhase phaseAverage_const_mul phaseAverage_cos_sq)

noncomputable section

abbrev Wave4 := Fin 4 → ℝ

/-! ## §1. The two sides use the same two scalars -/

theorem frobSq_eq (H : Mat4) : frobSq H = frobeniusNormSq H := rfl

theorem momentumSq_eq (k : Wave4) : momentumSq k = waveNormSq k := rfl

/-! ## §2. A4 with the constant left free -/

/-- **A4, unfixed.**  If `Σ_h A_h δ_h = ρ · ∫ R √g`, then the continuum face the
discrete Regge Hessian must be compared against is `ρ` times the derived
Einstein-Hilbert face.  `ρ` is a free real here and is pinned in §4. -/
def reggeFace (ρ : ℝ) (H : Mat4) (k : Wave4) : ℝ := ρ * ehFace H k

/-- Regge's normalization constant, `Σ_h A_h δ_h = (1/2) ∫ R √g`.  Checked
independently in §6. -/
def reggeNormalization : ℝ := 1 / 2

theorem reggeFace_eq (ρ : ℝ) (H : Mat4) (k : Wave4) :
    reggeFace ρ H k = -(ρ / 4) * frobeniusNormSq H * waveNormSq k := by
  unfold reggeFace ehFace
  rw [frobSq_eq, momentumSq_eq]
  ring

/-! ## §3. P2: the match -/

/-- **P2.**  At Regge's normalization the derived continuum face equals the
banked dictionary m² moment exactly, for every transverse-traceless `H` at every
momentum `k`.  No residual factor, and no tolerance: both sides are exact. -/
theorem reggeFace_eq_dictionary (H : Mat4) (k : Wave4) (hTT : IsTT k H) :
    reggeFace reggeNormalization H k = exactMidpointBlochM2 H k := by
  rw [exactMidpointBlochM2_eq_neg_eighth_frobenius_tt H k hTT, reggeFace_eq]
  unfold reggeNormalization
  ring

/-! ## §4. P3: the dictionary measures Regge's constant -/

/-- **P3.**  The 1,208 rows, built from exact Heron areas and Gram dihedral
derivatives with no input from any continuum theorem, force `ρ = 1/2`.  This is a
check that could have failed. -/
theorem regge_normalization_pinned (H : Mat4) (k : Wave4) (hTT : IsTT k H) (ρ : ℝ)
    (hne : frobeniusNormSq H * waveNormSq k ≠ 0)
    (h : reggeFace ρ H k = exactMidpointBlochM2 H k) :
    ρ = 1 / 2 := by
  rw [exactMidpointBlochM2_eq_neg_eighth_frobenius_tt H k hTT, reggeFace_eq] at h
  have hc : (ρ / 4 - 1 / 8) * (frobeniusNormSq H * waveNormSq k) = 0 := by
    linear_combination -h
  rcases mul_eq_zero.mp hc with h1 | h2
  · linarith
  · exact absurd h2 hne

/-! ## §5. Discrimination: the instrument fires, and the wrong constants fail -/

theorem frobeniusNormSq_axisTTPlus : frobeniusNormSq axisTTPlus = 2 := by
  norm_num [frobeniusNormSq, Fin.sum_univ_four, axisTTPlus]

theorem waveNormSq_axisWave : waveNormSq axisWave = 1 := by
  norm_num [waveNormSq, Fin.sum_univ_four, axisWave]

theorem witness_nonzero : frobeniusNormSq axisTTPlus * waveNormSq axisWave ≠ 0 := by
  rw [frobeniusNormSq_axisTTPlus, waveNormSq_axisWave]
  norm_num

/-- **Discrimination 4.**  The witness carries a nonzero value, so the agreement
of §3 is not two zeros meeting. -/
theorem dictionary_witness_value :
    exactMidpointBlochM2 axisTTPlus axisWave = -(1 / 4) := by
  rw [exactMidpointBlochM2_eq_neg_eighth_frobenius_tt axisTTPlus axisWave axisTTPlus_isTT,
    frobeniusNormSq_axisTTPlus, waveNormSq_axisWave]
  norm_num

/-- **Discrimination 2.**  `ρ = 1`, which is what comparing the discrete Regge
action against `∫ R √g` assumes, and what the frozen preflight did, is refuted at
the witness. -/
theorem rho_one_fails :
    reggeFace 1 axisTTPlus axisWave ≠ exactMidpointBlochM2 axisTTPlus axisWave := by
  rw [reggeFace_eq, dictionary_witness_value, frobeniusNormSq_axisTTPlus,
    waveNormSq_axisWave]
  norm_num

/-- **Discrimination 3.**  Every `ρ ≠ 1/2` is refuted, so the constant is pinned
and not merely consistent. -/
theorem rho_pinned_at_witness (ρ : ℝ)
    (h : reggeFace ρ axisTTPlus axisWave = exactMidpointBlochM2 axisTTPlus axisWave) :
    ρ = 1 / 2 :=
  regge_normalization_pinned axisTTPlus axisWave axisTTPlus_isTT ρ witness_nonzero h

/-! ## §6. A4 checked independently, in two dimensions

A hinge in two dimensions is a vertex and its `(d-2)`-volume is `1`, so the Regge
action is the plain deficit sum `Σ_v δ_v`.  Gauss-Bonnet gives `∫ K √g = 2πχ`,
and `R = 2K` in two dimensions, so `∫ R √g = 4πχ`.  Regge's constant is therefore
`2πχ / 4πχ = 1/2` on every closed surface, independent of topology.  Checked on
two triangulations of the sphere with different vertex counts and different
vertex degrees; a wrong constant fails both. -/

/-- Tetrahedron: four vertices, each meeting three equilateral triangles. -/
theorem tetrahedron_deficit_sum :
    (4 : ℝ) * (2 * Real.pi - 3 * (Real.pi / 3)) = 4 * Real.pi := by ring

/-- Octahedron: six vertices, each meeting four equilateral triangles. -/
theorem octahedron_deficit_sum :
    (6 : ℝ) * (2 * Real.pi - 4 * (Real.pi / 3)) = 4 * Real.pi := by ring

/-- `∫ R √g` on the sphere: Gauss-Bonnet gives `∫K√g = 2πχ = 4π`, and `R = 2K`. -/
def sphereEHIntegral : ℝ := 2 * (2 * Real.pi * 2)

/-- Both polyhedra give a deficit sum of `4π`, and `4π = (1/2) · 8π`. -/
theorem regge_constant_from_gauss_bonnet :
    (4 : ℝ) * Real.pi = reggeNormalization * sphereEHIntegral := by
  unfold reggeNormalization sphereEHIntegral
  ring

/-- The same check refutes `ρ = 1`: it would demand a deficit sum of `8π`, and
both polyhedra give `4π`. -/
theorem gauss_bonnet_refutes_rho_one :
    (4 : ℝ) * Real.pi ≠ 1 * sphereEHIntegral := by
  unfold sphereEHIntegral
  intro h
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  linarith

/-! ## §7. A second route to the same continuum face

The `-h·G⁽¹⁾` density of `ContinuumTTSecondVariation4D` §5 is one textbook form.
The other is the quadratic Lagrangian `-(1/4) ∂_λ h_{μν} ∂^λ h^{μν}`, whose
second derivative along `t h` is `-(1/2) ∂h·∂h`, giving a density in `sin²`
rather than `cos²`.  The two densities differ pointwise, because they differ by a
total derivative, and agree on average.  Agreement of two independent textbook
forms is a check on A3's normalization. -/

theorem phaseAverage_sin_sq : phaseAverage (fun θ => Real.sin θ ^ 2) = 1 / 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold phaseAverage
  rw [integral_sin_sq, Real.sin_two_pi, Real.sin_zero]
  field_simp
  ring

/-- Density of the quadratic-Lagrangian route, as a function of the phase. -/
def lagrangianDensityOfPhase (H : Mat4) (k : Wave4) (θ : ℝ) : ℝ :=
  -((1 / 2 : ℝ) * waveNormSq k * frobeniusNormSq H) * Real.sin θ ^ 2

theorem lagrangian_route_same_face (H : Mat4) (k : Wave4) :
    phaseAverage (lagrangianDensityOfPhase H k) = ehFace H k := by
  unfold lagrangianDensityOfPhase ehFace
  rw [phaseAverage_const_mul, phaseAverage_sin_sq, frobSq_eq, momentumSq_eq]
  ring

/-- The two routes really are different densities: at zero phase one vanishes and
the other does not.  They agree only after averaging, which is what makes their
agreement informative. -/
theorem two_routes_differ_pointwise (H : Mat4) (k : Wave4)
    (hne : waveNormSq k * frobeniusNormSq H ≠ 0) :
    lagrangianDensityOfPhase H k 0 ≠ densityOfPhase H k 0 := by
  have hl : lagrangianDensityOfPhase H k 0 = 0 := by
    unfold lagrangianDensityOfPhase
    rw [Real.sin_zero]
    ring
  have hd : densityOfPhase H k 0
      = -((1 / 2 : ℝ) * (waveNormSq k * frobeniusNormSq H)) := by
    unfold densityOfPhase
    rw [frobSq_eq, momentumSq_eq, Real.cos_zero]
    ring
  rw [hl, hd]
  intro h
  exact hne (by linarith)

/-! ## §8. P4: what the tree's constants actually are -/

/-- **P4.**  `discreteBookkeepingFactor = 2` is `1/ρ`, Regge's normalization
constant inverted.  It is not bookkeeping and it is not a fudge; it is derivable,
and §6 derives it. -/
theorem discreteBookkeepingFactor_is_inverse_regge :
    ReggeExactFlatHessianNormGate4D.discreteBookkeepingFactor * reggeNormalization = 1 := by
  unfold reggeNormalization
  rw [ReggeExactFlatHessianNormGate4D.discreteBookkeepingFactor_eq_two]
  norm_num

/-- **The frozen preflight coefficient was never a wrong number.**  It is exactly
the derived Einstein-Hilbert face, per unit Frobenius and per unit momentum.  It
is the right face for `∫ R √g` and the wrong face for `Σ_h A_h δ_h`, which is
what the dictionary tabulates. -/
theorem frozen_preflight_is_the_eh_integral_face (H : Mat4) (k : Wave4) :
    ehFace H k
      = ReggeExactFlatHessianNormGate4D.frozenPreflightEHCoefficient
          * frobeniusNormSq H * waveNormSq k := by
  unfold ehFace ReggeExactFlatHessianNormGate4D.frozenPreflightEHCoefficient
    ReggeExactFlatHessianSymbol4D.einsteinHilbertTTCoefficient4D
  rw [frobSq_eq, momentumSq_eq]
  ring

/-- And the banked `-(1/8)` is exactly the face of the discrete action.  Both
constants in the tree are correct faces of different functionals. -/
theorem exact_unit_coefficient_is_the_regge_face (H : Mat4) (k : Wave4) :
    reggeFace reggeNormalization H k
      = ReggeExactFlatHessianNormGate4D.exactUnitFrobeniusTTCoefficient
          * frobeniusNormSq H * waveNormSq k := by
  unfold reggeFace reggeNormalization ehFace
    ReggeExactFlatHessianNormGate4D.exactUnitFrobeniusTTCoefficient
    ReggeExactFlatHessianSymbol4D.exactHessianM2UnitFrobeniusTTCoeff
  rw [frobSq_eq, momentumSq_eq]
  ring

/-! ## §9. A gate that can fail

`ReggeExactFlatHessianNormGate4D.NormalizationGatePass` is the Bool literal
`true`, so it reports success no matter what any coefficient in the tree is; it
cannot discriminate.  The proposition below is its discriminating replacement:
each conjunct is an equation or a refutation over the actual constants, and
changing any coefficient in the tree breaks one of them. -/

def NormalizationGateDischarged : Prop :=
  (∀ H : Mat4, ∀ k : Wave4, IsTT k H →
      reggeFace reggeNormalization H k = exactMidpointBlochM2 H k)
    ∧ (∀ ρ : ℝ, reggeFace ρ axisTTPlus axisWave
        = exactMidpointBlochM2 axisTTPlus axisWave → ρ = 1 / 2)
    ∧ reggeFace 1 axisTTPlus axisWave ≠ exactMidpointBlochM2 axisTTPlus axisWave
    ∧ exactMidpointBlochM2 axisTTPlus axisWave = -(1 / 4)
    ∧ (4 : ℝ) * Real.pi = reggeNormalization * sphereEHIntegral
    ∧ (4 : ℝ) * Real.pi ≠ 1 * sphereEHIntegral

theorem normalizationGateDischarged : NormalizationGateDischarged :=
  ⟨fun H k hTT => reggeFace_eq_dictionary H k hTT,
   rho_pinned_at_witness,
   rho_one_fails,
   dictionary_witness_value,
   regge_constant_from_gauss_bonnet,
   gauss_bonnet_refutes_rho_one⟩

/-- Everything step 7 claims, in one proposition. -/
def Step7Cert : Prop :=
  NormalizationGateDischarged
    ∧ (∀ H : Mat4, ∀ k : Wave4, phaseAverage (lagrangianDensityOfPhase H k) = ehFace H k)
    ∧ ReggeExactFlatHessianNormGate4D.discreteBookkeepingFactor * reggeNormalization = 1
    ∧ (∀ H : Mat4, ∀ k : Wave4, ehFace H k
        = ReggeExactFlatHessianNormGate4D.frozenPreflightEHCoefficient
            * frobeniusNormSq H * waveNormSq k)
    ∧ (4 : ℝ) * (2 * Real.pi - 3 * (Real.pi / 3)) = 4 * Real.pi
    ∧ (6 : ℝ) * (2 * Real.pi - 4 * (Real.pi / 3)) = 4 * Real.pi

theorem step7Cert : Step7Cert :=
  ⟨normalizationGateDischarged,
   lagrangian_route_same_face,
   discreteBookkeepingFactor_is_inverse_regge,
   frozen_preflight_is_the_eh_integral_face,
   tetrahedron_deficit_sum,
   octahedron_deficit_sum⟩

/-! ## §10. Status strings -/

/-- What is now derived, and what remains assumed. -/
def typedResidual_arc2_normalization : String :=
  "CLOSED: arc 2's factor of two is Regge's normalization constant, Σ_h A_h δ_h = (1/2)∫R√g. \
The continuum face is DERIVED in ContinuumTTSecondVariation4D from the Levi-Civita \
connection with no access to the Regge side; the dictionary then PINS ρ = 1/2 on the whole \
TT space at every momentum, and ρ = 1 is refuted at the witness. ρ = 1/2 is separately \
checked against Gauss-Bonnet on two triangulated spheres. REMAINING ASSUMPTION: A3, that \
d²/dt² ∫√gR = -∫ h·G⁽¹⁾, cross-checked here against the quadratic-Lagrangian route. \
NOT CLOSED BY THIS: the geometric mesh Tendsto that S_RS_converges_EH_4d needs; this \
settles the coefficient, not the convergence."

/-- The naming defect this step exposes, recorded rather than silently renamed. -/
def typedResidual_naming_defect : String :=
  "NAMING: ReggeExactFlatHessianNormGate4D.continuumEHDiscreteFace computes \
discreteBookkeepingFactor * exactUnitFrobeniusTTCoefficient * frobeniusSq = -(1/4)·F, which \
is the face of ∫R√g and NOT the face of the discrete Regge action, whose face is -(1/8)·F. \
The name says the opposite of what the function returns. Left in place because downstream \
modules depend on it; readers should use ReggeNormalizationDerived4D.reggeFace instead. \
Likewise NormalizationGatePass is the Bool literal true and cannot fail; its discriminating \
replacement is NormalizationGateDischarged in §9."

end

end ReggeNormalizationDerived4D
end Analysis
end Gravity
end IndisputableMonolith
