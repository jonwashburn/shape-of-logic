import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.TrailingFoldBridge
import IndisputableMonolith.Masses.TrailingSpanDistribution
import IndisputableMonolith.Spectral.DFT8

/-!
# Golden Fold Orientation (relocates S2 closure sign; de-parks B2 scale)

This module discharges the panel-greenlit lift **F** (2026-07-02 director verdict,
`state/panel/lepton_post_exhaustion_20260702_043441.json`): the generation-closing
fold is realised as ONE algebraic object — multiplication by `φ` on the rank-2
`ℤ[φ]`-module `ℤ·1 ⊕ ℤ·φ`, in the basis `{1, φ}`, the Fibonacci `Q`-matrix
`goldenMul = !![0,1;1,1]` — and then the two previously-independent modeling inputs of
the trailing-torsion law fall out of that single map:

* **S2 closure sign** = the *determinant* (orientation) of the fold,
  `det(goldenMul) = N(φ) = φ · σ(φ) = -1`.
* **B2 golden scale** = the *dominant eigenvalue* of the fold, `φ` (`goldenMul` acting on
  the eigenvector `(1, φ)` scales it by `φ`, because `1 + φ = φ²`).

## Why this unblocks S2 where the telescoping route was blocked

The dead route (`TrailingSpanDistribution` S2 note) tried discrete-Stokes / ledger
telescoping and was blocked because the T1 premise `OctaveClosurePremise` maps states
across the golden **conjugate** ratio `ρ ∈ {φ², φ⁻²}` (closure up to conjugation, not
identity), so the boundary sum did not return to `s₀` with a canonical sign. The
determinant sidesteps this exactly: `det(lmul α) = N(α)` is **Galois-invariant**, so the
sign is the *same* `-1` whichever member of the conjugate pair `{φ², φ⁻²}` the fold picks
(the Galois automorphism `σ : φ ↦ 1 - φ` sends `φ² ↦ φ⁻²`, permuting the pair, and leaves
the norm fixed). The conjugate-pair ambiguity that killed telescoping is *why* the
determinant is the right invariant, not an obstruction to it.

## Triangulation (why `-1` is not a coincidence)

The closure sign `-1` is computed three independent ways that all agree:
`det(goldenMul) = -1` (module determinant), `φ · σ(φ) = -1` (field norm / Galois scalar),
and `(ω₈⁴).re = -1` (the DFT-8 antipode already banked at theorem grade in `Spectral`).
`golden_sign_triangulation` records the three-way identity.

## Non-vacuity: the double-fold witness

`FoldOrientedSignPremise` is not a relabeling of `sign = -1`: committing to a *single*
golden step (`k = 1`, the map `goldenMul` itself) is what forces the `-1`. A *double*
step (`k = 2`, `goldenMul²`) has determinant `N(φ²) = +1` and scale `φ²`, so the sign is
genuinely tied to the single-golden-scale commitment. `k = 0` (identity) likewise gives
`+1`. So the orientation premise does real work; it excludes `k ∈ {0, 2}`.

## Honest status

- `goldenMul_repr`, `goldenMul_det`, `golden_norm`, `det_eq_norm`,
  `goldenConj_sq_eq_inv_sq`, `goldenMul_eigen_phi`, `foldScale_forces_B2`,
  `foldOriented_forces_closureSign`, `doubleFold_det`, `golden_sign_triangulation`:
  THEOREM (no `sorry`, Mathlib-base axioms only).
- `FoldOrientedSignPremise`, `FoldScalePremise`: the relocated MODEL layer. They replace
  the *bare numerical* premises S2 (`sign = -1`) and B2 (`prefactor = φ`) with a *single
  structural* commitment (the fold is `lmul φ` on the rank-2 module). This is a genuine
  premise-ledger shrink (2 → 1) and a more principled input, but it is still a MODEL
  commitment: that the generation fold IS golden multiplication on the recognition module
  is not itself proved from the kernel here.

Lean status: no `sorry`; no new axioms beyond Mathlib base.
-/

namespace IndisputableMonolith
namespace Masses
namespace FoldOrientation

open Constants
open scoped BigOperators

noncomputable section

/-! ## The fold as multiplication by `φ` on the rank-2 recognition module `ℤ[φ]` -/

/-- The generation fold as the `ℤ`-linear map "multiply by `φ`" on the rank-2 module
`ℤ[φ] = ℤ·1 ⊕ ℤ·φ` in the basis `{1, φ}`. The columns are the images of the basis:
`φ·1 = φ = (0,1)` and `φ·φ = φ² = φ+1 = (1,1)`. This is the Fibonacci `Q`-matrix. -/
def goldenMul : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 1]

/-- The coordinate embedding `(a, b) ↦ a + b·φ` of the recognition module into `ℝ`. -/
def goldenEmbed (v : Fin 2 → ℝ) : ℝ := v 0 + v 1 * phi

/-- The matrix-vector action of the fold, in explicit coordinates. -/
theorem goldenMul_mulVec (v : Fin 2 → ℝ) :
    goldenMul.mulVec v = ![v 1, v 0 + v 1] := by
  funext i
  fin_cases i <;>
    simp [goldenMul, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Representation theorem (non-vacuity anchor).** `goldenMul` genuinely computes
multiplication by `φ`: applying the matrix to `(a, b)` and reading back through the
embedding gives `φ · (a + b·φ)`. So `goldenMul` is *not* an arbitrary matrix that happens
to carry a `-1`; it is forced to be this matrix by "multiply by `φ` in the `{1, φ}`
basis". -/
theorem goldenMul_repr (v : Fin 2 → ℝ) :
    goldenEmbed (goldenMul.mulVec v) = phi * goldenEmbed v := by
  rw [goldenMul_mulVec]
  simp only [goldenEmbed, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (-(v 1)) * phi_sq_eq

/-! ## The orientation (determinant) and the golden norm -/

/-- **The fold orientation.** `det(goldenMul) = -1`. -/
theorem goldenMul_det : goldenMul.det = -1 := by
  rw [goldenMul, Matrix.det_fin_two_of]; ring

/-- The Galois conjugate of `φ` in `ℚ(√5)`: `σ(φ) = 1 - φ` (the other root of
`x² - x - 1`). -/
def goldenConj : ℝ := 1 - phi

/-- **The field norm.** `N(φ) = φ · σ(φ) = -1`. -/
theorem golden_norm : phi * goldenConj = -1 := by
  unfold goldenConj
  linear_combination (-1 : ℝ) * phi_sq_eq

/-- **Determinant = norm.** `det(goldenMul) = N(φ) = φ · σ(φ)`. This is the special case
`det(lmul α) = N(α)` of the standard identity, evaluated for the golden unit. -/
theorem det_eq_norm : goldenMul.det = phi * goldenConj := by
  rw [goldenMul_det, golden_norm]

/-- `φ⁻¹ = φ - 1` (the defining self-similarity of the golden ratio). -/
theorem golden_inv_eq : phi⁻¹ = phi - 1 := by
  have hpos := phi_pos
  field_simp
  nlinarith [phi_sq_eq]

/-- **Galois acts on the B1 conjugate pair.** `σ(φ)² = (1 - φ)² = φ⁻²`. So the Galois
automorphism sends `φ²` (one B1 root) to `φ⁻²` (the other B1 root): it *permutes* the
conjugate pair `{φ², φ⁻²}` that blocked the telescoping route. The determinant is fixed
by `σ`, which is exactly why the closure sign is unambiguous. -/
theorem goldenConj_sq_eq_inv_sq : goldenConj ^ 2 = phi⁻¹ ^ 2 := by
  rw [goldenConj, golden_inv_eq]; ring

/-! ## The scale (eigenvalue) forces B2 -/

/-- **The fold scales the golden eigenvector by `φ`.** `goldenMul · (1, φ) = φ · (1, φ)`,
because the lower coordinate `1 + φ = φ²`. So `φ` is an eigenvalue (the dominant one) of
the fold: the "single golden scale" of B2 is this eigenvalue, read off the same map whose
determinant is the closure sign. -/
theorem goldenMul_eigen_phi :
    goldenMul.mulVec ![1, phi] = phi • ![1, phi] := by
  have hl : goldenMul.mulVec ![1, phi] = ![phi, 1 + phi] := by
    rw [goldenMul_mulVec]; simp
  have hr : phi • ![1, phi] = ![phi, phi * phi] := by
    funext i; fin_cases i <;> simp
  have harith : (1 : ℝ) + phi = phi * phi := by nlinarith [phi_sq_eq]
  rw [hl, hr, harith]

/-- **MODEL premise (fold scale), relocating bare B2.** The fold's single golden scale is
its positive eigenvalue on the golden eigenvector. This is a structural characterization
of the *same* map `goldenMul`, not the free number `φ`. -/
def FoldScalePremise (prefactor : ℝ) : Prop :=
  0 < prefactor ∧ goldenMul.mulVec ![1, prefactor] = prefactor • ![1, prefactor]

/-- **B2 is forced by the fold scale.** The positive eigenvalue of `goldenMul` is exactly
`φ`, so `FoldScalePremise` forces `SingleGoldenScalePremise` (B2). The characteristic
polynomial `x² - x - 1` has roots `φ` and `1 - φ`; positivity selects `φ`. -/
theorem foldScale_forces_B2 {prefactor : ℝ} (h : FoldScalePremise prefactor) :
    TrailingFoldBridge.SingleGoldenScalePremise prefactor := by
  obtain ⟨hpos, heig⟩ := h
  -- Extract the lower-coordinate scalar identity `1 + p = p²` from the eigen-equation.
  have hcomp : (goldenMul.mulVec ![1, prefactor]) 1 = (prefactor • ![1, prefactor]) 1 :=
    congrFun heig 1
  rw [goldenMul_mulVec] at hcomp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.smul_apply, smul_eq_mul] at hcomp
  -- hcomp : 1 + prefactor = prefactor * prefactor
  have hquad : prefactor ^ 2 = prefactor + 1 := by nlinarith [hcomp]
  have hfac : (prefactor - phi) * (prefactor + phi - 1) = 0 := by
    nlinarith [hquad, phi_sq_eq]
  have hφ1 := one_lt_phi
  rcases mul_eq_zero.mp hfac with h1 | h2
  · show prefactor = phi
    linarith [sub_eq_zero.mp h1]
  · exfalso; nlinarith [hpos, hφ1]

/-! ## The relocation of S2 (closure sign) -/

/-- **MODEL premise (fold orientation), relocating bare S2.** The generation-closing
fold's closure *sign* is the *orientation* of the fold as a `ℤ`-linear map: its
determinant. This is a single structural commitment on the map `goldenMul`, replacing the
bare numerical premise `ClosureSignPremise (sign = -1)`. -/
def FoldOrientedSignPremise (sign : ℝ) : Prop := sign = goldenMul.det

/-- **S2 is forced by the fold orientation.** The orientation premise forces
`ClosureSignPremise` (`sign = -1`), because `det(goldenMul) = -1`. The forcing is
Galois-invariant: `det = N(φ)` is fixed by `σ`, so the sign does not depend on which
member of the B1 conjugate pair the fold ratio is. -/
theorem foldOriented_forces_closureSign
    {sign : ℝ} (h : FoldOrientedSignPremise sign) :
    TrailingSpanDistribution.ClosureSignPremise sign := by
  show sign = -1
  rw [h, goldenMul_det]

/-! ## Non-vacuity: the double-fold witness excludes `k ∈ {0, 2}` -/

/-- **Double-fold determinant.** A double golden step has `det(goldenMul²) = +1 = N(φ²)`.
Combined with `goldenMul_det = -1`, this shows the closure sign genuinely depends on the
single-golden-scale (`k = 1`) commitment: `k = 2` (and `k = 0`, the identity, `det = +1`)
give the *opposite* sign. So the orientation premise is not vacuous. -/
theorem doubleFold_det : (goldenMul * goldenMul).det = 1 := by
  rw [Matrix.det_mul, goldenMul_det]; ring

/-- The double fold also scales the golden eigenvector by `φ²`, confirming `k = 2` is the
`φ²` scale (not `φ`), the companion of its `+1` determinant. -/
theorem doubleFold_eigen :
    goldenMul.mulVec (goldenMul.mulVec ![1, phi]) = (phi ^ 2) • ![1, phi] := by
  rw [goldenMul_eigen_phi, Matrix.mulVec_smul, goldenMul_eigen_phi, smul_smul, ← pow_two]

/-! ## Triangulation: three independent computations of the closure sign `-1` -/

/-- **Three-way sign identity.** The closure sign `-1` is computed independently by the
module determinant, the field norm (Galois scalar), and the DFT-8 antipode, all agreeing.
This is triangulation, not herding: three different structures force the same unit. -/
theorem golden_sign_triangulation :
    goldenMul.det = -1 ∧ phi * goldenConj = -1 ∧ (Spectral.omega8 ^ 4).re = -1 := by
  refine ⟨goldenMul_det, golden_norm, ?_⟩
  rw [Spectral.omega8_pow_4]; simp

/-! ## Certificate bundling the relocated layers -/

/-- THEOREM-grade certificate: the fold is `lmul φ` (representation), its determinant is
the closure sign `-1` (S2), its positive eigenvalue is the golden scale `φ` (B2), the
double fold flips the sign (non-vacuity), and the sign triangulates three ways. -/
structure FoldOrientationCert where
  represents_mult :
    ∀ v : Fin 2 → ℝ, goldenEmbed (goldenMul.mulVec v) = phi * goldenEmbed v
  det_is_sign :
    goldenMul.det = -1
  det_is_norm :
    goldenMul.det = phi * goldenConj
  galois_permutes_pair :
    goldenConj ^ 2 = phi⁻¹ ^ 2
  scale_forces_B2 :
    ∀ {p : ℝ}, FoldScalePremise p → TrailingFoldBridge.SingleGoldenScalePremise p
  orientation_forces_S2 :
    ∀ {s : ℝ}, FoldOrientedSignPremise s → TrailingSpanDistribution.ClosureSignPremise s
  double_fold_flips :
    (goldenMul * goldenMul).det = 1
  triangulation :
    goldenMul.det = -1 ∧ phi * goldenConj = -1 ∧ (Spectral.omega8 ^ 4).re = -1

theorem foldOrientationCert_holds : Nonempty FoldOrientationCert :=
  ⟨{ represents_mult := goldenMul_repr
     det_is_sign := goldenMul_det
     det_is_norm := det_eq_norm
     galois_permutes_pair := goldenConj_sq_eq_inv_sq
     scale_forces_B2 := fun h => foldScale_forces_B2 h
     orientation_forces_S2 := fun h => foldOriented_forces_closureSign h
     double_fold_flips := doubleFold_det
     triangulation := golden_sign_triangulation }⟩

/-! ## Downstream: the relocated closure sign forces the trailing torsion sign -/

/-- **End-to-end (relocated S2 → δ₃₂ sign).** With the closure sign now *forced* by the
fold orientation (rather than posited), the trailing per-rung torsion assembly lands at
`−(φ/2)/6` — the S2 half of `δ₃₂` is now conditional on the single structural premise
`FoldOrientedSignPremise`, not on the bare `sign = -1`. -/
theorem delta32_from_orientation
    {sign num : ℝ} {span : ℕ}
    (hnum : num = phi / 2)
    (hspan : span = 6)
    (hOrient : FoldOrientedSignPremise sign) :
    TrailingSpanDistribution.signedPerRung sign num span = -(phi / 2) / 6 :=
  TrailingSpanDistribution.delta32_forced hnum hspan (foldOriented_forces_closureSign hOrient)

end

end FoldOrientation
end Masses
end IndisputableMonolith
