import Mathlib
import IndisputableMonolith.Gravity.Analysis.SRSConvergesEH4D
import IndisputableMonolith.Gravity.Analysis.GeometricFoldVsDictionary4D

/-!
# What `S_RS_converges_EH_4d_closed` establishes, and what it excludes

Arc 2, step 8, task 2.  `SRSConvergesEH4D` is the ledger-facing export module and
is left untouched; this module states its scope from outside, as theorems rather
than as a docstring.

## The reading

`S_RS_converges_EH_4d` is `Regge4DContinuumEHTarget ∧ Regge4DContinuumGaugeZeroTarget`.
The first conjunct says: for every nonzero integer mode and every
transverse-traceless polarization, the mesh sequence bound by
`Regge4DContinuumSymbolIs`, divided by the mesh momentum norm, converges to
`continuumEHScaleExplicitFace E`.  Two facts fix what that means.

1. The bound sequence is `finiteExactMidpointBlochSymbol`, the algebraic 1,208-row
   dictionary, not the geometric hinge fold.  The limit is genuinely `j`-dependent
   and is not a constant face, so the 2026 revert of the constant-face inhabitation
   is respected.
2. The limit value is `-(1/8) · ‖E‖²_F`, which arc 2 step 7 derived to be the
   **Regge action's** transverse-traceless face, equal to `ρ` times the
   Einstein-Hilbert face with `ρ = 1/2`.

So the theorem says the dictionary mesh symbol converges to the Regge action's
second variation.  That is the correct target for a Regge action and it is
derived.  What the theorem's *name* suggests, convergence to the Einstein-Hilbert
face, is false and provably so: §2 below shows the sequence cannot converge to the
Einstein-Hilbert face on any polarization of nonzero Frobenius mass, because the
limit is unique and the two candidate values differ by the factor `1/ρ`.

## What it does not reach

The geometric hinge fold.  R1, `TypedResidual_fold_eq_midpointBloch`, is the only
statement in the tree that would carry this limit to the mesh, and it has no
inhabitant.  `GeometricFoldVsDictionary4D` measures the gap: at both banked
transverse-traceless witnesses the dictionary's m² is exactly twice the geometric
hinge m² moment, with the factor pinned against 1 and 4.  §3 turns that
measurement into a conditional refutation of R1, with the two remaining premises
stated explicitly rather than assumed.

## Tags

* THEOREM: §1, §2, §3, at the base triple.
* Scope of §2: the exclusion is per mode and per polarization of nonzero
  Frobenius mass, and it is an exclusion about this mesh sequence only.
* Not claimed: that R1 is refuted outright.  §3 is a conditional, and its two
  premises are the honest residual.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace SRSConvergesScope4D

open Filter Topology
open Regge4DContinuumPreflight
open EdgeTTDecomposition4D (IsTT axisTTPlus)
open ReggeBlochM2Symbol4D (symbolDir)
open ReggeExactFlatHessianBlochSymbol4D (exactMidpointBlochSymbol exactMidpointBlochM2)
open ReggeBlochStarEdgeOrigins4D (m2AllOrbitMomentDistinctHingeEdgeOrigins)
open SRSConvergesEH4D (TypedResidual_fold_eq_midpointBloch S_RS_converges_EH_4d_closed)

noncomputable section

abbrev Mat4 := Regge4DContinuumPreflight.Mat4
abbrev Wave4 := Regge4DContinuumPreflight.Wave4

/-! ## §1. The limit value is the Regge action face, which is `ρ` times the
Einstein-Hilbert face -/

/-- The value the convergence theorem converges to, in closed form. -/
theorem srs_limit_value (E : Mat4) :
    continuumEHScaleExplicitFace E = -(1 / 8 : ℝ) * frobeniusNormSq E :=
  continuumEHScaleExplicitFace_eq E

/-- The Einstein-Hilbert face for the same polarization, derived in step 7 and
carried here through the preflight's own name for it. -/
theorem eh_face_value (E : Mat4) :
    discreteExactReggeContinuumFaceCoeff E
      = (2 : ℝ) * (-(1 / 8 : ℝ)) * frobeniusNormSq E :=
  discreteExactReggeContinuumFaceCoeff_eq E

/-- **The scope statement.**  The limit is Regge's normalization times the
Einstein-Hilbert face, so the theorem is about the Regge action. -/
theorem srs_limit_is_regge_normalization_times_eh (E : Mat4) :
    continuumEHScaleExplicitFace E
      = ReggeNormalizationDerived4D.reggeNormalization
          * discreteExactReggeContinuumFaceCoeff E := by
  rw [srs_limit_value, eh_face_value, ReggeNormalizationDerived4D.reggeNormalization]
  ring

/-- And the two are different wherever the polarization carries mass, which is
what makes the previous line a correction and not a restatement. -/
theorem srs_limit_ne_eh_face (E : Mat4) (hE : frobeniusNormSq E ≠ 0) :
    continuumEHScaleExplicitFace E ≠ discreteExactReggeContinuumFaceCoeff E := by
  rw [srs_limit_value, eh_face_value]
  intro h
  apply hE
  have : (-(1 / 8 : ℝ)) * frobeniusNormSq E = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h2
  · exact absurd h1 (by norm_num)
  · exact h2

/-! ## §2. What the convergence claim excludes -/

/-- **THEOREM.**  The mesh sequence provably does **not** converge to the
Einstein-Hilbert face, on any nonzero mode and any transverse-traceless
polarization carrying Frobenius mass.  This is the exclusion the convergence
claim buys: the limit exists, it is unique, and it is the Regge face. -/
theorem mesh_sequence_does_not_converge_to_eh_face
    (m : IntMode4) (E : Mat4) (hm : m ≠ 0)
    (hTT : IsTT (fun i => (m i : ℝ)) E) (hE : frobeniusNormSq E ≠ 0) :
    ¬ Regge4DContinuumSymbolIs m E (discreteExactReggeContinuumFaceCoeff E) := by
  intro hEH
  have hRegge : Regge4DContinuumSymbolIs m E (continuumEHScaleExplicitFace E) :=
    S_RS_converges_EH_4d_closed.1 m E hm hTT
  exact srs_limit_ne_eh_face E hE (continuumSymbolIs_unique hRegge hEH)

/-- The positive half, restated so the pair reads as one scoped verdict. -/
theorem mesh_sequence_converges_to_the_regge_face
    (m : IntMode4) (E : Mat4) (hm : m ≠ 0)
    (hTT : IsTT (fun i => (m i : ℝ)) E) :
    Regge4DContinuumSymbolIs m E
      (ReggeNormalizationDerived4D.reggeNormalization
        * discreteExactReggeContinuumFaceCoeff E) := by
  rw [← srs_limit_is_regge_normalization_times_eh E]
  exact S_RS_converges_EH_4d_closed.1 m E hm hTT

/-! ## §3. R1, conditionally refuted, with the two remaining premises named

R1 asserts that the geometric fold and the dictionary are equal *as functions*.
Any functional of the symbol therefore takes the same value on both.  The two
premises below say only that each side's banked m² certificate is such a
functional of that side's symbol, which is what the phrase "the m² moment of"
means.  Neither is proved anywhere in the tree, and naming them is the point.
-/

/-- **THEOREM.**  Under the two naming premises, R1 is false.  `moment` is an
arbitrary functional on symbol functions, so this uses nothing about how a
Taylor coefficient is computed. -/
theorem R1_fails_if_the_moments_read_their_symbols
    (moment : (Wave4 → ℝ) → ℝ)
    (hFold : moment (fun k => Regge4DExactActionSymbol.exactFlatCrossTermFold axisTTPlus k)
      = m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir)
    (hDict : moment (fun k => exactMidpointBlochSymbol axisTTPlus k)
      = exactMidpointBlochM2 axisTTPlus symbolDir) :
    ¬ TypedResidual_fold_eq_midpointBloch := by
  intro hR1
  have hfun :
      (fun k => Regge4DExactActionSymbol.exactFlatCrossTermFold axisTTPlus k)
        = (fun k => exactMidpointBlochSymbol axisTTPlus k) :=
    funext (fun k => hR1 axisTTPlus k)
  rw [hfun, hDict] at hFold
  exact GeometricFoldVsDictionary4D.geom_ne_dict_axisTTPlus hFold.symm

/-- The premises are not vacuous: the inequality they collide with is a pair of
kernel-checked values, and it is strict. -/
theorem the_collision_is_real :
    m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir
        ≠ exactMidpointBlochM2 axisTTPlus symbolDir ∧
      exactMidpointBlochM2 axisTTPlus symbolDir
        = 2 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir :=
  ⟨GeometricFoldVsDictionary4D.geom_ne_dict_axisTTPlus,
    GeometricFoldVsDictionary4D.dict_eq_two_geom_axisTTPlus⟩

/-! ## §4. The scoped verdict as one statement -/

/-- Everything step 8 licenses about the convergence claim, in one Prop that can
fail: the mesh sequence converges to the Regge face, it does not converge to the
Einstein-Hilbert face, and the geometric side differs from the sequence by a
factor of two at the banked witness. -/
def Step8ScopedVerdict : Prop :=
  (∀ (m : IntMode4) (E : Mat4), m ≠ 0 → IsTT (fun i => (m i : ℝ)) E →
      Regge4DContinuumSymbolIs m E
        (ReggeNormalizationDerived4D.reggeNormalization
          * discreteExactReggeContinuumFaceCoeff E))
    ∧ (∀ (m : IntMode4) (E : Mat4), m ≠ 0 → IsTT (fun i => (m i : ℝ)) E →
        frobeniusNormSq E ≠ 0 →
          ¬ Regge4DContinuumSymbolIs m E (discreteExactReggeContinuumFaceCoeff E))
    ∧ (m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir
        ≠ exactMidpointBlochM2 axisTTPlus symbolDir)

theorem step8ScopedVerdict_holds : Step8ScopedVerdict :=
  ⟨fun m E hm hTT => mesh_sequence_converges_to_the_regge_face m E hm hTT,
    fun m E hm hTT hE => mesh_sequence_does_not_converge_to_eh_face m E hm hTT hE,
    GeometricFoldVsDictionary4D.geom_ne_dict_axisTTPlus⟩

end

end SRSConvergesScope4D
end Analysis
end Gravity
end IndisputableMonolith
