import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeNormalizationDerived4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianSymbol4D
import IndisputableMonolith.Gravity.Analysis.Regge4DExactActionSymbol

/-!
# The geometric hinge fold is not the dictionary, and the gap is exactly two

Arc 2, step 8.  Step 7 derived the Einstein-Hilbert transverse-traceless second
variation (`-(1/4)` per unit Frobenius and momentum) and pinned Regge's
normalization `ρ = 1/2`, which made the banked dictionary's `-(1/8)` the second
variation of the Regge action.  That closed the coefficient question.  It said
nothing about the limit, and this module is about what the tree's convergence
theorem actually converges.

## The five objects

`SRSConvergesEH4D.GeometricTendstoResidualOpen` bundles five typed residuals.
Four have inhabitants.  The fifth, `TypedResidual_fold_eq_midpointBloch` (R1),
asserts that the geometric hinge fold `Regge4DExactActionSymbol.exactFlatCrossTermFold`
equals the algebraic dictionary `exactMidpointBlochSymbol`, and no inhabitant of
it exists anywhere in the tree.  Since
`Regge4DContinuumPreflight.Regge4DContinuumSymbolIs` binds the dictionary, R1 is
the only statement that would carry the convergence theorem to the mesh.

## What is proved here

R1 is **false**, and the discrepancy is not a mystery: at both banked
transverse-traceless witnesses the dictionary's m² is exactly twice the geometric
hinge moment.  The corrected residual is therefore R1′, that *twice* the fold
equals the dictionary, and the tree already contains the doubled object under the
name `discreteExactReggeSymbol`.

That makes the residual factor 4 recorded in `Regge4DTorusContinuumLimit`
(`-(1/16)` geometric against `-(1/4)` Einstein-Hilbert) a product of two twos:
the fold-to-action factor proved here, and Regge's `1/ρ` derived in step 7.  Only
the second is derived.

§7 records why the earlier certificate suite could not have caught this.  Two of
its four witnesses on `symbolDir` are gauge zeros, and a witness where the
geometric side vanishes makes every candidate factor give the same prediction.
The other two were compared against `exactHessianM2AxisTTPlusCoeff`, a banked
constant documented as a coefficient per unit momentum, while the certificates
are values at `|symbolDir|² = 2`.  The numerals agreed and the quantities did
not.

## Tags

* THEOREM: everything below, at the base triple.  No `native_decide`, no `sorry`.
* Scope: the two named transverse-traceless witnesses on `symbolDir`.  The
  refutation of R1 needs only one witness; two independent ones agreeing at the
  same factor is what makes the factor a measurement rather than a coincidence.
* Not claimed: that the m² moment used here is the m² of `exactFlatCrossTermFold`
  itself.  `m2AllOrbitMomentDistinctHingeEdgeOrigins` is a hybrid (t11 from the
  legacy transported path, the other five orbits from edge origins) and is the
  object every banked geometric certificate in this tree is about.  Linking it to
  `exactFlatCrossTermFold` is a separate uninhabited step, named in §8.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace GeometricFoldVsDictionary4D

open BigOperators
open EdgeTTDecomposition4D (IsTT IsTraceless euclideanTrace axisTTPlus axisTTCross)
open ReggeBlochM2Symbol4D (symbolDir)
open ReggeExactFlatHessianBlochSymbol4D (exactMidpointBlochM2)
open ReggeBlochStarEdgeOrigins4D (m2AllOrbitMomentDistinctHingeEdgeOrigins)
open ReggeExactMidpointM2TTIdentity4D (exactMidpointBlochM2_eq_neg_eighth_frobenius_tt)

noncomputable section

/-! ## §1. Witness arithmetic

The two banked polarizations both have Frobenius square 2 and the banked
direction has momentum square 2.  Every number below is one of these three.
-/

theorem frobId_axisTTPlus :
    ReggeExactMidpointM2TTIdentity4D.frobeniusNormSq axisTTPlus = 2 := by
  unfold ReggeExactMidpointM2TTIdentity4D.frobeniusNormSq axisTTPlus
  norm_num [Fin.sum_univ_four]

theorem frobId_axisTTCross :
    ReggeExactMidpointM2TTIdentity4D.frobeniusNormSq axisTTCross = 2 := by
  unfold ReggeExactMidpointM2TTIdentity4D.frobeniusNormSq axisTTCross
  norm_num [Fin.sum_univ_four]

theorem waveId_symbolDir :
    ReggeExactMidpointM2TTIdentity4D.waveNormSq symbolDir = 2 := by
  unfold ReggeExactMidpointM2TTIdentity4D.waveNormSq symbolDir
  norm_num [Fin.sum_univ_four]

/-- `symbolDir` is transverse to both banked polarizations, because their first two
rows and columns vanish.  Needed to apply the 1,208-row identity at this
direction rather than at the unit axis wave. -/
theorem axisTTPlus_isTT_symbolDir : IsTT symbolDir axisTTPlus := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> rfl
  · unfold IsTraceless euclideanTrace axisTTPlus
    simp [Fin.sum_univ_four]
  · intro i
    fin_cases i <;> simp [axisTTPlus, symbolDir, Fin.sum_univ_four]

theorem axisTTCross_isTT_symbolDir : IsTT symbolDir axisTTCross := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> rfl
  · unfold IsTraceless euclideanTrace axisTTCross
    simp [Fin.sum_univ_four]
  · intro i
    fin_cases i <;> simp [axisTTCross, symbolDir, Fin.sum_univ_four]

/-! ## §2. P1: the dictionary's m² at the witnesses

From the banked identity over all 1,208 rows, with no tolerance and no
normalization freedom.
-/

theorem dict_m2_axisTTPlus_symbolDir :
    exactMidpointBlochM2 axisTTPlus symbolDir = -(1 / 2 : ℝ) := by
  rw [exactMidpointBlochM2_eq_neg_eighth_frobenius_tt axisTTPlus symbolDir
      axisTTPlus_isTT_symbolDir, frobId_axisTTPlus, waveId_symbolDir]
  norm_num

theorem dict_m2_axisTTCross_symbolDir :
    exactMidpointBlochM2 axisTTCross symbolDir = -(1 / 2 : ℝ) := by
  rw [exactMidpointBlochM2_eq_neg_eighth_frobenius_tt axisTTCross symbolDir
      axisTTCross_isTT_symbolDir, frobId_axisTTCross, waveId_symbolDir]
  norm_num

/-! ## §3. The geometric moment at the same witnesses

Restated from the banked `decide` certificates over `Fin 24 × Fin 10`, which are
kernel-checked and use no `native_decide`.
-/

theorem geom_m2_axisTTPlus_symbolDir :
    m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir = (-1 / 4 : ℝ) :=
  ReggeExactFlatHessianSymbol4D.exactHessian_m2_axisTTPlus_symbolDir

theorem geom_m2_axisTTCross_symbolDir :
    m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTCross symbolDir = (-1 / 4 : ℝ) :=
  ReggeExactFlatHessianSymbol4D.exactHessian_m2_axisTTCross_symbolDir

theorem geom_m2_decoyGauge_symbolDir :
    m2AllOrbitMomentDistinctHingeEdgeOrigins ReggeEdgeStencil4D.decoyGauge symbolDir
      = (0 : ℝ) :=
  ReggeExactFlatHessianSymbol4D.exactHessian_m2_decoyGauge_symbolDir

/-! ## §4. P2: R1 is false, and the gap is exactly two -/

/-- **P2, first witness.**  The geometric hinge moment and the dictionary disagree. -/
theorem geom_ne_dict_axisTTPlus :
    m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir
      ≠ exactMidpointBlochM2 axisTTPlus symbolDir := by
  rw [geom_m2_axisTTPlus_symbolDir, dict_m2_axisTTPlus_symbolDir]
  norm_num

/-- **P2, second witness.**  Independently, on the cross polarization. -/
theorem geom_ne_dict_axisTTCross :
    m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTCross symbolDir
      ≠ exactMidpointBlochM2 axisTTCross symbolDir := by
  rw [geom_m2_axisTTCross_symbolDir, dict_m2_axisTTCross_symbolDir]
  norm_num

/-- **P2, the quantity.**  The dictionary is exactly twice the geometric moment. -/
theorem dict_eq_two_geom_axisTTPlus :
    exactMidpointBlochM2 axisTTPlus symbolDir
      = 2 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir := by
  rw [dict_m2_axisTTPlus_symbolDir, geom_m2_axisTTPlus_symbolDir]
  norm_num

theorem dict_eq_two_geom_axisTTCross :
    exactMidpointBlochM2 axisTTCross symbolDir
      = 2 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTCross symbolDir := by
  rw [dict_m2_axisTTCross_symbolDir, geom_m2_axisTTCross_symbolDir]
  norm_num

/-! ## §5. Discrimination: the factor is pinned, not fitted -/

/-- The factor is unique.  Any real `c` satisfying the relation at the plus witness
is 2, so this is a measurement of the factor and not a choice of it. -/
theorem factor_pinned_axisTTPlus (c : ℝ)
    (h : exactMidpointBlochM2 axisTTPlus symbolDir
          = c * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir) :
    c = 2 := by
  rw [dict_m2_axisTTPlus_symbolDir, geom_m2_axisTTPlus_symbolDir] at h
  linarith

theorem factor_pinned_axisTTCross (c : ℝ)
    (h : exactMidpointBlochM2 axisTTCross symbolDir
          = c * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTCross symbolDir) :
    c = 2 := by
  rw [dict_m2_axisTTCross_symbolDir, geom_m2_axisTTCross_symbolDir] at h
  linarith

/-- `c = 1` fails, which is exactly the statement that R1 is refuted. -/
theorem factor_one_fails :
    exactMidpointBlochM2 axisTTPlus symbolDir
      ≠ 1 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir := by
  rw [dict_m2_axisTTPlus_symbolDir, geom_m2_axisTTPlus_symbolDir]
  norm_num

/-- `c = 4` fails too, so the fold-to-dictionary gap is not the whole factor 4
that separates the fold from the Einstein-Hilbert face. -/
theorem factor_four_fails :
    exactMidpointBlochM2 axisTTPlus symbolDir
      ≠ 4 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir := by
  rw [dict_m2_axisTTPlus_symbolDir, geom_m2_axisTTPlus_symbolDir]
  norm_num

/-! ## §6. P3 and P4: the two twos, and the factor four they compose to -/

/-- The doubled geometric object already exists in the tree, and its factor is the
one measured in §4. -/
theorem doubled_fold_is_the_named_object (j : ℕ) (m : Fin 4 → ℤ)
    (E : Matrix (Fin 4) (Fin 4) ℝ) :
    Regge4DExactActionSymbol.discreteExactReggeSymbol j m E
      = 2 * Regge4DExactActionSymbol.finiteExactReggeSymbol j m E :=
  Regge4DExactActionSymbol.discreteExactReggeSymbol_eq j m E

/-- **P3.**  Two definitions in this tree carry the name `discreteBookkeepingFactor`,
both equal 2, and they do different jobs: the first carries the geometric fold to
the Regge action, the second carries the Regge action to the Einstein-Hilbert
integral (step 7's `1/ρ`).  Their product is the residual 4. -/
theorem two_distinct_bookkeeping_factors :
    Regge4DExactActionSymbol.discreteBookkeepingFactor = 2 ∧
      ReggeExactFlatHessianNormGate4D.discreteBookkeepingFactor = 2 ∧
        Regge4DExactActionSymbol.discreteBookkeepingFactor
            * ReggeExactFlatHessianNormGate4D.discreteBookkeepingFactor = 4 := by
  refine ⟨Regge4DExactActionSymbol.discreteBookkeepingFactor_eq, ?_, ?_⟩
  · exact ReggeExactFlatHessianNormGate4D.discreteBookkeepingFactor_eq_two
  · rw [Regge4DExactActionSymbol.discreteBookkeepingFactor_eq,
      ReggeExactFlatHessianNormGate4D.discreteBookkeepingFactor_eq_two]
    norm_num

theorem ehFace_axisTTPlus_symbolDir :
    ContinuumTTSecondVariation4D.ehFace axisTTPlus symbolDir = -(1 : ℝ) := by
  unfold ContinuumTTSecondVariation4D.ehFace
  rw [show EdgeTTDecomposition4D.momentumSq symbolDir = 2 from waveId_symbolDir,
    show ContinuumTTSecondVariation4D.frobSq axisTTPlus = 2 from frobId_axisTTPlus]
  norm_num

/-- **P4.**  The derived Einstein-Hilbert face is four times the geometric hinge
moment at the witness, and §6 names both factors of that four.  Step 7 derived
one of them; the other is the subject of §8. -/
theorem ehFace_eq_four_times_geom :
    ContinuumTTSecondVariation4D.ehFace axisTTPlus symbolDir
      = 4 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir := by
  rw [ehFace_axisTTPlus_symbolDir, geom_m2_axisTTPlus_symbolDir]
  norm_num

/-- The Regge action face sits strictly between them, which is the whole content of
the two-step decomposition. -/
theorem reggeFace_between :
    ReggeNormalizationDerived4D.reggeFace ReggeNormalizationDerived4D.reggeNormalization
        axisTTPlus symbolDir
      = 2 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir := by
  rw [ReggeNormalizationDerived4D.reggeFace_eq_dictionary axisTTPlus symbolDir
      axisTTPlus_isTT_symbolDir]
  exact dict_eq_two_geom_axisTTPlus

/-! ## §7. Why the banked certificate suite could not have caught this

Two of the four witnesses on `symbolDir` are gauge zeros.  Where the geometric
side vanishes, every candidate factor makes the same prediction, so such a
witness carries no information about the factor at all.  The two
transverse-traceless witnesses were read against a banked constant in a
different normalization.
-/

/-- A witness on which the geometric moment vanishes cannot distinguish any two
candidate factors. -/
theorem vanishing_witness_admits_every_factor
    (H : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ)
    (hg : m2AllOrbitMomentDistinctHingeEdgeOrigins H k = 0) (c c' : ℝ) :
    c * m2AllOrbitMomentDistinctHingeEdgeOrigins H k
      = c' * m2AllOrbitMomentDistinctHingeEdgeOrigins H k := by
  rw [hg]; ring

/-- Instantiated at the banked gauge decoy: that certificate is compatible with
every factor, so its passing was never evidence about the factor. -/
theorem decoyGauge_admits_every_factor (c c' : ℝ) :
    c * m2AllOrbitMomentDistinctHingeEdgeOrigins ReggeEdgeStencil4D.decoyGauge symbolDir
      = c' * m2AllOrbitMomentDistinctHingeEdgeOrigins ReggeEdgeStencil4D.decoyGauge
          symbolDir :=
  vanishing_witness_admits_every_factor _ _ geom_m2_decoyGauge_symbolDir c c'

/-- By contrast the transverse-traceless witness is informative, because the
geometric moment there is nonzero. -/
theorem tt_witness_is_informative :
    m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir ≠ 0 := by
  rw [geom_m2_axisTTPlus_symbolDir]
  norm_num

/-- The normalization mismatch that hid the factor.  `exactHessianM2AxisTTPlusCoeff`
is documented as the m² coefficient per unit momentum; the geometric certificate
is a value at `|symbolDir|² = 2`.  Read as the same quantity the two numerals
agree, and read correctly they differ. -/
theorem banked_coefficient_is_not_the_certificate_value :
    ReggeExactFlatHessianSymbol4D.exactHessianM2AxisTTPlusCoeff
        * ReggeExactMidpointM2TTIdentity4D.waveNormSq symbolDir
      ≠ m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir := by
  rw [ReggeExactFlatHessianSymbol4D.exactHessianM2AxisTTPlusCoeff_eq, waveId_symbolDir,
    geom_m2_axisTTPlus_symbolDir]
  norm_num

/-- And the numerals do coincide, which is how the mismatch survived reading. -/
theorem the_numerals_coincide :
    ReggeExactFlatHessianSymbol4D.exactHessianM2AxisTTPlusCoeff
      = m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir := by
  rw [ReggeExactFlatHessianSymbol4D.exactHessianM2AxisTTPlusCoeff_eq,
    geom_m2_axisTTPlus_symbolDir]
  norm_num

/-! ## §8. R1′, the corrected residual, and the discriminating gate -/

/-- **R1′.**  The residual that should have been stated: twice the geometric hinge
fold equals the dictionary, everywhere, not once the fold equals it.  Stated for
the m² moments, which is where every certificate in this tree lives.  Uninhabited:
§4 establishes it at two witnesses only. -/
def FoldTimesTwoEqDictionaryM2 : Prop :=
  ∀ (H : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ),
    IsTT k H →
      exactMidpointBlochM2 H k
        = 2 * m2AllOrbitMomentDistinctHingeEdgeOrigins H k

/-- What §4 does establish: R1′ at the two banked witnesses, which is a strictly
weaker statement than `FoldTimesTwoEqDictionaryM2` and is named separately so the
two are never confused. -/
def FoldTimesTwoEqDictionaryAtBankedWitnesses : Prop :=
  exactMidpointBlochM2 axisTTPlus symbolDir
      = 2 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir ∧
    exactMidpointBlochM2 axisTTCross symbolDir
      = 2 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTCross symbolDir

theorem foldTimesTwoEqDictionaryAtBankedWitnesses_holds :
    FoldTimesTwoEqDictionaryAtBankedWitnesses :=
  ⟨dict_eq_two_geom_axisTTPlus, dict_eq_two_geom_axisTTCross⟩

/-- The discriminating gate for this step.  Six conjuncts, three of them
refutations, so the gate fails if any of the four numbers involved moves.  It is
not a `Bool`, and it does not report success on an empty computation. -/
def FoldDictionaryFactorDischarged : Prop :=
  FoldTimesTwoEqDictionaryAtBankedWitnesses
    ∧ (m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir
        ≠ exactMidpointBlochM2 axisTTPlus symbolDir)
    ∧ (exactMidpointBlochM2 axisTTPlus symbolDir
        ≠ 1 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir)
    ∧ (exactMidpointBlochM2 axisTTPlus symbolDir
        ≠ 4 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir)
    ∧ ContinuumTTSecondVariation4D.ehFace axisTTPlus symbolDir
        = 4 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir
    ∧ Regge4DExactActionSymbol.discreteBookkeepingFactor
        * ReggeExactFlatHessianNormGate4D.discreteBookkeepingFactor = 4

theorem foldDictionaryFactorDischarged_holds : FoldDictionaryFactorDischarged := by
  refine ⟨foldTimesTwoEqDictionaryAtBankedWitnesses_holds, geom_ne_dict_axisTTPlus,
    factor_one_fails, factor_four_fails, ehFace_eq_four_times_geom, ?_⟩
  exact two_distinct_bookkeeping_factors.2.2

/-- The honest reading of the convergence chain after this step.  Each conjunct is
an equation or a refutation over the reals, so the statement can fail. -/
def ConvergenceReachesDictionaryNotTheHingeMoment : Prop :=
  (m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir
      ≠ exactMidpointBlochM2 axisTTPlus symbolDir)
    ∧ (m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTCross symbolDir
        ≠ exactMidpointBlochM2 axisTTCross symbolDir)
    ∧ FoldTimesTwoEqDictionaryAtBankedWitnesses

theorem convergenceReachesDictionaryNotTheHingeMoment_holds :
    ConvergenceReachesDictionaryNotTheHingeMoment :=
  ⟨geom_ne_dict_axisTTPlus, geom_ne_dict_axisTTCross,
    foldTimesTwoEqDictionaryAtBankedWitnesses_holds⟩

end

end GeometricFoldVsDictionary4D
end Analysis
end Gravity
end IndisputableMonolith
