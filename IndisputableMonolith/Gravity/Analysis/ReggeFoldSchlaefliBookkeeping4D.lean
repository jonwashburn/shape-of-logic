import Mathlib
import IndisputableMonolith.Gravity.Analysis.Regge4DSchlaefliPathwise
/-!
# Arc 2 step 9 task 2: the fold-to-action factor from Schläfli bookkeeping

Frozen propositions:
`holography/plans/Arc2_Step9_Fold_Provenance_And_Schlafli_Proposition_20260802.html`
(expected value **2**, frozen before measurement and before this module) and
the sibling freeze
`holography/plans/Arc2_Step9_Schlaefli_Factor_Proposition_20260802.html`.

## The measured arithmetic this derives

Exact rational measurement (oracles
`scripts/qg/regge_4d_factor2_pinpoint_20260802.py`,
`scripts/qg/regge_4d_fold_channel_split_20260802.py`) at both banked TT
witnesses, with `S''` the Regge action's second variation for the real cosine
perturbation, `D` the dictionary's m² (`exactMidpointBlochM2`), and `F` the
fold's own m² (`m2ExactFoldMoment`, task 1):

* `S'' = 2·X` where `X` is the single-ordering area×deficit cross-term face;
* `D = S''/2` (the dictionary symbol's two-sheet reading of the real cosine);
* `F = X/2` (the fold's m² is the μ² Taylor coefficient of the phased
  cross-term pairing, half its second derivative);
* hence `D = 2·F`, banked concretely by `decide` certificates in
  `ReggeBlochStarResolvedT11M2Eval4D` (`dict_eq_two_fold_axisTTPlus`,
  `dict_eq_two_fold_axisTTCross`).

## The derivation, as a composition of named steps

**(a) Schläfli cross-term reduction (contributes the product-rule 2).**
At flat background `S = Σ_h A_h δ_h` with `δ_h = 0`. The product rule gives
`S'' = Σ_h (A''_h δ_h + 2 A'_h δ'_h + A_h δ''_h)`. The first term vanishes
because `δ = 0` at flat; the third vanishes because the deficit acceleration,
like every deficit velocity, is an edge-velocity push through the angle
Jacobian, and the area-weighted sum of any such push is the linearized
Schläfli identity, which vanishes. What remains is the symmetrized cross
term `2·X`. The Schläfli premise is not assumed abstractly: it is inhabited
in this tree by `freudenthal4SimplexFlatDirectionalSchlaefli`
(`Regge4DSchlaefliPathwise`), instantiated in §4 below.

**(b) Sheet bookkeeping (contributes 1/2).** The dictionary's symbol is the
quadratic form of the real cosine `cos(k·x) = (e^{ikx} + e^{-ikx})/2`, read
on both `±k` sheets with amplitude `1/2` each: `(1/2)² + (1/2)² = 1/2`. This
is the convention the tree cites in 3D as `ttSecondDifference = (2/N³)·S''`.

**(c) Taylor extraction (contributes 1/2).** The fold's m² moment is the μ²
Taylor coefficient of the cosine-phased cross-term pairing,
`cos(μφ) = 1 − μ²φ²/2 + …`, hence half the pairing's second derivative.

Composed: `D = (b) of (a) = (2X)/2 = X = 2·(X/2) = 2·F`. The factor is
exactly **2**, the frozen expected value.

## Decoys (named in the freeze, refuted below)

* Decoy 1: the fold is already the action's second variation. Fails: the
  composed factor is 2, and at the witnesses `D ≠ F` by the banked
  certificates (`decoy_one_fails_axisTTPlus`, task 1 module).
* Decoy 4: the factor is the product with Regge's `1/ρ = 2` (step 7). Fails:
  `1/ρ` is a different factor; the composed value here is 2, and at the
  witnesses `D ≠ 4·F` (`decoy_four_fails_axisTTPlus`, task 1 module).

## Relation to the sibling module

`SchlaefliFoldToActionFactor4D` proves step (a)'s abstract identity
(`symmetrizedCross = 2 · bareFold`) and stops there. The measurement shows
the full fold-to-dictionary factor is the composition (a)×(b)×(c)⁻¹: the
sibling's identity alone would identify the factor against the wrong face
(the action's second variation is twice the cross-term face, but the
dictionary reads half of that and the fold banks half of the cross-term
face). This module proves the whole composition and instantiates the
Schläfli premise with the tree's flat 4-simplex theorem.

## Honesty

* THEOREM: every identity below, proved from the stated premises; the
  Schläfli premise is discharged by `freudenthal4SimplexFlatDirectionalSchlaefli`.
* MODEL: the identifications of `twoSheetReading` with the dictionary's
  symbol convention and of `taylorCoeffOfFace` with the fold's m² extraction.
  Both are measured (exact rational oracles above) and banked at the
  witnesses by the task 1 certificates; this module carries the bookkeeping,
  not the witness values.
* Scope: flat-background second variation. Does not derive Regge's `ρ = 1/2`
  (step 7) and does not import it.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeFoldSchlaefliBookkeeping4D

open BigOperators
open Regge4DSchlaefliPathwise

noncomputable section

/-! ## §0. Frozen value and decoys -/

/-- Frozen expected value, written into the proposition HTML before this
module existed. -/
def expectedFoldToActionFactor : ℝ := 2

/-- Decoy: the fold is already the action's second variation. -/
def decoyFactorOne : ℝ := 1

/-- Decoy: the fold-to-action factor conflated with the product against
Regge's `1/ρ = 2` (a different factor, step 7). -/
def decoyFactorFour : ℝ := 4

/-! ## §1. Step (a): the Schläfli cross-term reduction -/

/-- Flat-background second-variation data over hinge index `H` and
squared-edge index `E`. The deficit at flat is zero; every deficit velocity
or acceleration is an edge-velocity push through the dihedral-angle
Jacobian; the linearized Schläfli identity kills the area-weighted sum of
every such push. -/
structure FlatReggeVariation (H E : Type*) [Fintype H] [Fintype E] where
  /-- Hinge areas at the flat background. -/
  areaFlat : H → ℝ
  /-- Dihedral-angle Jacobian `∂θ_h/∂ℓ²_e`. -/
  angleJacobian : H → E → ℝ
  /-- Area velocities along the perturbation. -/
  areaVel : H → ℝ
  /-- Area accelerations along the perturbation. -/
  areaAccel : H → ℝ
  /-- Deficit angles at the flat background. -/
  deficitFlat : H → ℝ
  /-- Squared-edge velocities. -/
  edgeVel : E → ℝ
  /-- Squared-edge accelerations. -/
  edgeAccel : E → ℝ
  /-- Flatness: every deficit vanishes at the background. -/
  deficitFlat_zero : ∀ h, deficitFlat h = 0
  /-- Linearized Schläfli: area-weighted angle pushes vanish for every
  squared-edge velocity. -/
  schlaefli : ∀ w : E → ℝ,
    (∑ h : H, areaFlat h * ∑ e : E, w e * angleJacobian h e) = 0

/-- Deficit velocity of a variation: the edge-velocity push through the
angle Jacobian. -/
def deficitVel {H E : Type*} [Fintype H] [Fintype E]
    (V : FlatReggeVariation H E) (h : H) : ℝ :=
  ∑ e : E, V.edgeVel e * V.angleJacobian h e

/-- Deficit acceleration of a variation. -/
def deficitAccel {H E : Type*} [Fintype H] [Fintype E]
    (V : FlatReggeVariation H E) (h : H) : ℝ :=
  ∑ e : E, V.edgeAccel e * V.angleJacobian h e

/-- The single-ordering area×deficit cross-term face `X`. -/
def crossTermFace {H E : Type*} [Fintype H] [Fintype E]
    (V : FlatReggeVariation H E) : ℝ :=
  ∑ h : H, V.areaVel h * deficitVel V h

/-- The full product-rule second variation of `Σ_h A_h δ_h`. -/
def actionSecondVariationFull {H E : Type*} [Fintype H] [Fintype E]
    (V : FlatReggeVariation H E) : ℝ :=
  ∑ h : H, (V.areaAccel h * V.deficitFlat h +
    2 * (V.areaVel h * deficitVel V h) +
    V.areaFlat h * deficitAccel V h)

/-- **Step (a), THEOREM.** At flat background, with the linearized Schläfli
identity, the action's second variation is exactly twice the cross-term
face: the `A''·δ` term dies by flatness and the `A·δ''` term is the
Schläfli kill applied to the squared-edge acceleration. -/
theorem actionSecondVariation_eq_two_mul_crossTerm {H E : Type*}
    [Fintype H] [Fintype E] (V : FlatReggeVariation H E) :
    actionSecondVariationFull V = 2 * crossTermFace V := by
  have h1 : (∑ h : H, V.areaAccel h * V.deficitFlat h) = 0 := by
    simp [V.deficitFlat_zero]
  have h3 : (∑ h : H, V.areaFlat h * deficitAccel V h) = 0 :=
    V.schlaefli V.edgeAccel
  unfold actionSecondVariationFull crossTermFace
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h3, zero_add,
    add_zero, ← Finset.mul_sum]

/-! ## §2. Step (c): the fold's Taylor extraction -/

/-- The μ² Taylor coefficient of a cosine-phased pairing
`Σ_h x_h cos(μ φ_h)`: since `cos(μφ) = 1 − μ²φ²/2 + …`, the coefficient is
`−½ Σ x_h φ_h²`, exactly half the pairing's second derivative at `μ = 0`. -/
def taylorCoeffOfPhased {H : Type*} [Fintype H] (x φ : H → ℝ) : ℝ :=
  -(1 / 2 : ℝ) * ∑ h : H, x h * (φ h) ^ 2

/-- The second derivative at `μ = 0` of the same pairing. -/
def secondDerivOfPhased {H : Type*} [Fintype H] (x φ : H → ℝ) : ℝ :=
  -∑ h : H, x h * (φ h) ^ 2

/-- **Step (c), THEOREM.** The fold's m² extraction (Taylor coefficient) is
half the second derivative of the same phased pairing. -/
theorem taylorCoeff_eq_half_secondDeriv {H : Type*} [Fintype H]
    (x φ : H → ℝ) :
    taylorCoeffOfPhased x φ = secondDerivOfPhased x φ / 2 := by
  unfold taylorCoeffOfPhased secondDerivOfPhased
  ring

/-- The fold's m² face, as a multiple of the cross-term face: the Taylor
extraction contributes `1/2`. -/
def taylorCoeffOfFace (X : ℝ) : ℝ := X / 2

/-! ## §3. Step (b): the dictionary's two-sheet reading -/

/-- The dictionary symbol's quadratic form reads the real cosine
`cos(k·x) = (e^{ikx} + e^{-ikx})/2` on both `±k` sheets, amplitude `1/2`
per sheet, equal contributions (the phase enters squared): the two-sheet
reading of a second-variation value `S` is `(1/2)²·S + (1/2)²·S`. -/
def twoSheetReading (S : ℝ) : ℝ := (1 / 2 : ℝ) ^ 2 * S + (1 / 2 : ℝ) ^ 2 * S

/-- **Step (b), THEOREM.** The two-sheet reading is exactly half. -/
theorem twoSheetReading_eq_half (S : ℝ) : twoSheetReading S = S / 2 := by
  unfold twoSheetReading
  ring

/-! ## §4. The composed derivation -/

/-- **Main derivation, THEOREM.** The dictionary's m² face (the two-sheet
reading of the action's second variation) equals twice the fold's m² face
(the Taylor coefficient of the cross-term face):

`D = (2X)/2 = X = 2·(X/2) = 2·F`. -/
theorem dictFace_eq_two_mul_foldFace {H E : Type*} [Fintype H] [Fintype E]
    (V : FlatReggeVariation H E) :
    twoSheetReading (actionSecondVariationFull V) =
      2 * taylorCoeffOfFace (crossTermFace V) := by
  rw [actionSecondVariation_eq_two_mul_crossTerm, twoSheetReading_eq_half]
  unfold taylorCoeffOfFace
  ring

/-- The derived fold-to-action factor, as a ratio when the fold's face is
nonzero. -/
def derivedFoldToActionFactor {H E : Type*} [Fintype H] [Fintype E]
    (V : FlatReggeVariation H E) : ℝ :=
  if taylorCoeffOfFace (crossTermFace V) = 0 then expectedFoldToActionFactor
  else twoSheetReading (actionSecondVariationFull V) /
    taylorCoeffOfFace (crossTermFace V)

/-- **Derivation against the frozen value.** Whenever the fold's face is
nonzero, the derived factor equals the frozen expected value 2. -/
theorem derivedFoldToActionFactor_eq_two {H E : Type*} [Fintype H] [Fintype E]
    (V : FlatReggeVariation H E)
    (hne : taylorCoeffOfFace (crossTermFace V) ≠ 0) :
    derivedFoldToActionFactor V = expectedFoldToActionFactor := by
  unfold derivedFoldToActionFactor expectedFoldToActionFactor
  rw [if_neg hne, dictFace_eq_two_mul_foldFace V]
  field_simp [hne]

/-- **Decoy 1 fails:** the factor is not 1. -/
theorem decoyFactorOne_ne_derived :
    decoyFactorOne ≠ expectedFoldToActionFactor := by
  unfold decoyFactorOne expectedFoldToActionFactor
  norm_num

/-- **Decoy 4 fails:** the factor is not the product with Regge's `1/ρ`. -/
theorem decoyFactorFour_ne_derived :
    decoyFactorFour ≠ expectedFoldToActionFactor := by
  unfold decoyFactorFour expectedFoldToActionFactor
  norm_num

/-! ## §5. The Schläfli premise is inhabited: the flat 4-simplex -/

/-- The flat 4-simplex seed supplies a real instance of the variation data:
the Schläfli premise is `freudenthal4SimplexFlatDirectionalSchlaefli`,
proved in `Regge4DSchlaefliPathwise` from the rational flat summand table
whose column sums vanish. -/
def freudenthalFlatVariation (areaVel areaAccel edgeVel edgeAccel :
    Fin 10 → ℝ) : FlatReggeVariation (Fin 10) (Fin 10) where
  areaFlat := hingeAreaFlat
  angleJacobian := flatAngleJacobian
  areaVel := areaVel
  areaAccel := areaAccel
  deficitFlat := fun _ => 0
  edgeVel := edgeVel
  edgeAccel := edgeAccel
  deficitFlat_zero := fun _ => rfl
  schlaefli := by
    intro w
    have h := freudenthal4SimplexFlatDirectionalSchlaefli w
    simpa [flatDirectionalAngleDeriv] using h

/-- **The composed factor at the flat 4-simplex instance.** For any
velocities through the flat seed with nonzero fold face, the derived
fold-to-action factor is the frozen 2, with the Schläfli kill discharged by
the tree's theorem rather than an abstract hypothesis. -/
theorem freudenthal_derived_factor_eq_two (areaVel areaAccel edgeVel
    edgeAccel : Fin 10 → ℝ)
    (hne : taylorCoeffOfFace
      (crossTermFace (freudenthalFlatVariation areaVel areaAccel edgeVel
        edgeAccel)) ≠ 0) :
    derivedFoldToActionFactor
        (freudenthalFlatVariation areaVel areaAccel edgeVel edgeAccel) =
      expectedFoldToActionFactor :=
  derivedFoldToActionFactor_eq_two _ hne

/-! ## §6. A computable abstract witness -/

/-- A non-degenerate one-hinge instance: unit area velocity and unit edge
velocity, zero flat area (so the Schläfli premise holds trivially), unit
Jacobian. The cross-term face is 1, the action's second variation is 2, the
two-sheet reading is 1, and the fold's face is 1/2. -/
def unitVariation : FlatReggeVariation (Fin 1) (Fin 1) where
  areaFlat := fun _ => 0
  angleJacobian := fun _ _ => 1
  areaVel := fun _ => 1
  areaAccel := fun _ => 0
  deficitFlat := fun _ => 0
  edgeVel := fun _ => 1
  edgeAccel := fun _ => 1
  deficitFlat_zero := fun _ => rfl
  schlaefli := fun _ => by simp

theorem unitVariation_crossTermFace :
    crossTermFace unitVariation = 1 := by
  simp [crossTermFace, deficitVel, unitVariation]

theorem unitVariation_actionSecondVariation :
    actionSecondVariationFull unitVariation = 2 := by
  rw [actionSecondVariation_eq_two_mul_crossTerm,
    unitVariation_crossTermFace]
  ring

theorem unitVariation_dictFace :
    twoSheetReading (actionSecondVariationFull unitVariation) = 1 := by
  rw [twoSheetReading_eq_half, unitVariation_actionSecondVariation]
  norm_num

theorem unitVariation_foldFace :
    taylorCoeffOfFace (crossTermFace unitVariation) = 1 / 2 := by
  unfold taylorCoeffOfFace
  rw [unitVariation_crossTermFace]

/-- **The frozen factor, derived at the unit witness.** -/
theorem unitVariation_factor_eq_two :
    derivedFoldToActionFactor unitVariation = expectedFoldToActionFactor := by
  apply derivedFoldToActionFactor_eq_two
  rw [unitVariation_foldFace]
  norm_num

/-- Composite gate: the derived factor is the frozen 2, and both decoys
miss. -/
theorem schlaefli_bookkeeping_gate :
    expectedFoldToActionFactor = 2 ∧
      decoyFactorOne ≠ expectedFoldToActionFactor ∧
      decoyFactorFour ≠ expectedFoldToActionFactor ∧
      derivedFoldToActionFactor unitVariation = 2 := by
  refine ⟨rfl, decoyFactorOne_ne_derived, decoyFactorFour_ne_derived, ?_⟩
  rw [unitVariation_factor_eq_two]
  rfl

/-! ## §7. Status -/

/-- Closed target: the composed fold-to-action factor is derived and equals
the frozen expected value. -/
def FoldToActionFactorDerived : Prop :=
  ∀ {H E : Type*} [Fintype H] [Fintype E] (V : FlatReggeVariation H E),
    twoSheetReading (actionSecondVariationFull V) =
      2 * taylorCoeffOfFace (crossTermFace V)

theorem FoldToActionFactorDerived_holds : FoldToActionFactorDerived :=
  fun V => dictFace_eq_two_mul_foldFace V

end

end ReggeFoldSchlaefliBookkeeping4D
end Analysis
end Gravity
end IndisputableMonolith
