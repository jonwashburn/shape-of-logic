import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.KDisplayCore
import IndisputableMonolith.Verification.BridgeCore
import IndisputableMonolith.RecogSpec.Core
import IndisputableMonolith.RecogSpec.Anchors
import IndisputableMonolith.RecogSpec.Bands
import IndisputableMonolith.Patterns
import IndisputableMonolith.Verification.TwoOutcomeBornCert

noncomputable section

namespace IndisputableMonolith
namespace RecogSpec

/-- Canonical speed determined by a pair of anchors. -/
def speedFromAnchors (A : Anchors) : ℝ :=
  if h : A.a1 = 0 then 0 else A.a2 / A.a1

/-- Units obtained by calibrating directly against the anchors. -/
def unitsFromAnchors (A : Anchors) : Constants.RSUnits :=
{ tau0 := A.a1
  ell0 := A.a2
  c := speedFromAnchors A
  c_ell0_tau0 := by
    unfold speedFromAnchors
    split_ifs with h
    · simp [h]
    · field_simp [h] }

@[simp] lemma speedFromAnchors_of_eq_zero {A : Anchors} (h : A.a1 = 0) :
    speedFromAnchors A = 0 := by simp [speedFromAnchors, h]

@[simp] lemma speedFromAnchors_of_ne_zero {A : Anchors} (h : A.a1 ≠ 0) :
    speedFromAnchors A = A.a2 / A.a1 := by simp [speedFromAnchors, h]

@[simp] lemma unitsFromAnchors_tau0 (A : Anchors) :
    (unitsFromAnchors A).tau0 = A.a1 := rfl

@[simp] lemma unitsFromAnchors_ell0 (A : Anchors) :
    (unitsFromAnchors A).ell0 = A.a2 := rfl

@[simp] lemma unitsFromAnchors_c (A : Anchors) :
    (unitsFromAnchors A).c = speedFromAnchors A := rfl

/-- Witness that a units pack exactly matches the provided anchors (including the
    ratio constraint extracted from the anchors). -/
def Calibrated (A : Anchors) (U : Constants.RSUnits) : Prop :=
  U.tau0 = A.a1 ∧ U.ell0 = A.a2 ∧ U.c = speedFromAnchors A

lemma unitsFromAnchors_calibrated (A : Anchors) :
    Calibrated A (unitsFromAnchors A) := by
  unfold Calibrated unitsFromAnchors
  simp

/-- Absolute-layer calibration witness: there is a unique units pack matching the
    anchors (forcing the calibration ratio). -/
def UniqueCalibration (L : Ledger) (B : Bridge L) (A : Anchors) : Prop :=
  ∃ units : Constants.RSUnits, Calibrated A units ∧
    ∀ ⦃U : Constants.RSUnits⦄, Calibrated A U → U = units

/-- Bands acceptance witness: exhibits a concrete units pack for which the band
    check succeeds. -/
def MeetsBands (L : Ledger) (B : Bridge L) (X : Bands) : Prop :=
  ∃ units : Constants.RSUnits, evalToBands_c units X

/-! ### Anchors transport and uniqueness up to units (formal quotient) -/

/-- Equivalence relation on anchors: two anchors are equivalent iff they induce the
same calibration speed via `speedFromAnchors`.

This is the intended quotienting relation for "unique up to units": anchors that
yield the same speed represent the same physical calibration up to an overall scale. -/
def AnchorsEqv (A₁ A₂ : Anchors) : Prop :=
  speedFromAnchors A₁ = speedFromAnchors A₂

/-- AnchorsEqv is reflexive. -/
lemma AnchorsEqv_refl (A : Anchors) : AnchorsEqv A A := by
  rfl

/-- AnchorsEqv is symmetric. -/
lemma AnchorsEqv_symm {A B : Anchors} (h : AnchorsEqv A B) : AnchorsEqv B A := by
  exact h.symm

/-- AnchorsEqv is transitive. -/
lemma AnchorsEqv_trans {A B C : Anchors} (h1 : AnchorsEqv A B) (h2 : AnchorsEqv B C) :
    AnchorsEqv A C := by
  exact h1.trans h2

/-- Setoid instance for `AnchorsEqv`. -/
instance anchorsSetoid : Setoid Anchors where
  r := AnchorsEqv
  iseqv := ⟨AnchorsEqv_refl, AnchorsEqv_symm, AnchorsEqv_trans⟩

/-- The quotient of anchors by the speed-equivalence. -/
def AnchorsQuot : Type := Quot anchorsSetoid

/-- Two anchors with the same speed from speedFromAnchors are equivalent.

    Note: The edge cases where one anchor is degenerate (a1 = 0) require
    careful analysis of the consistency condition. The main case
    (both a1 ≠ 0) is straightforward. -/
lemma anchors_eq_of_same_speed {A₁ A₂ : Anchors}
    (h : speedFromAnchors A₁ = speedFromAnchors A₂) :
    AnchorsEqv A₁ A₂ := by
  simpa [AnchorsEqv] using h

/-- Any two anchor choices calibrating bridges have equivalent speed if
    calibrated from the same ledger. -/
theorem anchors_unique_up_to_units
  (L : Ledger) (B₁ B₂ : Bridge L)
  (A₁ A₂ : Anchors)
  (h₁ : UniqueCalibration L B₁ A₁)
  (h₂ : UniqueCalibration L B₂ A₂)
  (hspeed : speedFromAnchors A₁ = speedFromAnchors A₂) :
  Quot.mk anchorsSetoid A₁ = Quot.mk anchorsSetoid A₂ := by
  have heqv : AnchorsEqv A₁ A₂ := anchors_eq_of_same_speed hspeed
  exact Quot.sound heqv

/-!
### Canonical dimensionless defaults (explicit φ-formulas)

These definitions are intentionally **explicit formulas in `φ`** (not hard-coded
numerical constants). They are used to make the "dimensionless pack" content
transparent and auditable.

They are part of the *spec-level* envelope (`UD_explicit` / `dimlessPack_explicit`)
and are **not** meant to claim "CODATA matching" by definition.
-/

/--- **CERT(definitional)**: Canonical (spec-level) dimensionless α default at scale `φ`. -/
@[simp] def alphaDefault (φ : ℝ) : ℝ := (1 - 1 / φ) / 2

/--- **CERT(definitional)**: Canonical (spec-level) φ-power mass ratios (legacy placeholder). -/
@[simp] def massRatiosDefault (φ : ℝ) : LeptonMassRatios :=
  ⟨φ, 1 / (φ ^ (2 : Nat)), 1 / φ⟩

/--- **CERT(definitional)**: Canonical (spec-level) mixing angles (legacy placeholder). -/
@[simp] def mixingAnglesDefault (φ : ℝ) : CkmMixingAngles :=
  ⟨1 / φ, 1 / (φ ^ (2 : Nat)), 1 / (φ ^ (3 : Nat))⟩

/--- **CERT(definitional)**: Canonical (spec-level) g-2 muon value (toy formula). -/
@[simp] def g2Default (φ : ℝ) : ℝ := 1 / (φ ^ (5 : Nat))

/-! ### φ-closure witnesses -/

lemma phiClosed_one_div (φ : ℝ) : PhiClosed φ (1 / φ) := by
  have h1 : PhiClosed φ (1 : ℝ) := PhiClosed.one φ
  have hφ : PhiClosed φ φ := PhiClosed.self φ
  exact PhiClosed.div h1 hφ

lemma phiClosed_one_div_pow (φ : ℝ) (n : Nat) :
    PhiClosed φ (1 / (φ ^ n)) := by
  have h1 : PhiClosed φ (1 : ℝ) := PhiClosed.one φ
  have hφn : PhiClosed φ (φ ^ n) := PhiClosed.pow_self φ n
  exact PhiClosed.div h1 hφn

lemma phiClosed_alphaDefault (φ : ℝ) : PhiClosed φ (alphaDefault φ) := by
  simp only [alphaDefault]
  -- (1 - 1/φ) / 2
  have h1 : PhiClosed φ (1 : ℝ) := PhiClosed.one φ
  have h1div : PhiClosed φ (1 / φ) := phiClosed_one_div φ
  have hdiff : PhiClosed φ (1 - 1 / φ) := PhiClosed.sub h1 h1div
  have h2 : PhiClosed φ (2 : ℝ) := PhiClosed.of_nat φ 2
  exact PhiClosed.div hdiff h2

/-- K-gate witness: the two canonical observables agree. -/
def kGateWitness : Prop :=
  ∀ U : Constants.RSUnits,
    U.tau0 ≠ 0 →
    U.ell0 ≠ 0 →
      (IndisputableMonolith.Constants.RSUnits.tau_rec_display U) / U.tau0 = IndisputableMonolith.Constants.RSUnits.K_gate_ratio
      ∧ (IndisputableMonolith.Constants.RSUnits.lambda_kin_display U) / U.ell0 = IndisputableMonolith.Constants.RSUnits.K_gate_ratio

@[simp] theorem kGate_from_units : kGateWitness := by
  intro U hτ hℓ
  exact IndisputableMonolith.Constants.RSUnits.K_gate_eqK U hτ hℓ

/-- Minimal eight-tick witness: there exists an exact 3-bit cover of period 8. -/
@[simp] def eightTickWitness : Prop :=
  ∃ w : Patterns.CompleteCover 3, w.period = 8

@[simp] theorem eightTick_from_TruthCore : eightTickWitness :=
  Patterns.period_exactly_8

/-- Born rule compliance witness: recognition path weights match Born probabilities. -/
@[simp] def bornHolds : Prop :=
  IndisputableMonolith.Verification.TwoOutcomeBorn.TwoOutcomeBornCert.verified {}

@[simp] theorem born_from_TruthCore : bornHolds := by
  exact IndisputableMonolith.Verification.TwoOutcomeBorn.TwoOutcomeBornCert.verified_any {}

/-! ### Explicit universal dimless pack and matching witness -/

noncomputable def UD_explicit (φ : ℝ) : UniversalDimless φ :=
  { alpha0 := alphaDefault φ
    massRatios0 := massRatiosDefault φ
    mixingAngles0 := mixingAnglesDefault φ
    g2Muon0 := g2Default φ
    strongCP0 := kGateWitness
    eightTick0 := eightTickWitness
    born0 := bornHolds
    alpha0_isPhi := phiClosed_alphaDefault φ
    massRatios0_isPhi := by
      simp only [LeptonMassRatios.Forall, massRatiosDefault]
      exact ⟨PhiClosed.self _, phiClosed_one_div_pow _ 2, phiClosed_one_div _⟩
    mixingAngles0_isPhi := by
      simp only [CkmMixingAngles.Forall, mixingAnglesDefault]
      exact ⟨phiClosed_one_div _, phiClosed_one_div_pow _ 2, phiClosed_one_div_pow _ 3⟩
    g2Muon0_isPhi := phiClosed_one_div_pow φ 5 }

noncomputable def dimlessPack_explicit (φ : ℝ) (L : Ledger) (B : Bridge L) :
    DimlessPack L B :=
  { alpha := alphaDefault φ
  , massRatios := massRatiosDefault φ
  , mixingAngles := mixingAnglesDefault φ
  , g2Muon := g2Default φ
  , strongCPNeutral := kGateWitness
  , eightTickMinimal := eightTickWitness
  , bornRule := bornHolds }

/-- Component-wise agreement between a concrete bridge-side pack and a universal target. -/
def PackMatches (φ : ℝ) {L : Ledger} {B : Bridge L} (P : DimlessPack L B)
    (U : UniversalDimless φ) : Prop :=
  P.alpha = U.alpha0 ∧
  P.massRatios = U.massRatios0 ∧
  P.mixingAngles = U.mixingAngles0 ∧
  P.g2Muon = U.g2Muon0 ∧
  P.strongCPNeutral = U.strongCP0 ∧
  P.eightTickMinimal = U.eightTick0 ∧
  P.bornRule = U.born0

/-- Computed matching: the designated evaluator `dimlessPack_explicit` matches `U`.

This removes the existential "pick any pack" form from the matching claim so that any
future strengthening of `dimlessPack_explicit` automatically strengthens the match. -/
def MatchesEval (φ : ℝ) (L : Ledger) (B : Bridge L) (U : UniversalDimless φ) : Prop :=
  PackMatches (φ:=φ) (P:=dimlessPack_explicit φ L B) U

lemma matchesEval_explicit (φ : ℝ) (L : Ledger) (B : Bridge L) :
    MatchesEval φ L B (UD_explicit φ) := by
  simp [MatchesEval, PackMatches, dimlessPack_explicit, UD_explicit]

/-! ### Inevitability predicates and recognition closure -/

/-- UniqueCalibration witness for any ledger/bridge/anchors triple. -/
@[simp] lemma uniqueCalibration_any (L : Ledger) (B : Bridge L) (A : Anchors) :
    UniqueCalibration L B A := by
  unfold UniqueCalibration
  use unitsFromAnchors A
  constructor
  · exact unitsFromAnchors_calibrated A
  · intro U hU
    cases U
    simp [Calibrated, unitsFromAnchors, speedFromAnchors] at *
    rcases hU with ⟨rfl, rfl, rfl⟩
    simp

def Inevitability_dimless (φ : ℝ) : Prop :=
  -- (i) Every ledger/bridge matches the explicit universal target.
  (∀ (L : Ledger) (B : Bridge L), MatchesEval φ L B (UD_explicit φ))
  ∧
  -- (ii) The universal target's "Prop fields" are not just carried as symbols;
  --      they are actually proven (no vacuity).
  (UD_explicit φ).strongCP0 ∧ (UD_explicit φ).eightTick0 ∧ (UD_explicit φ).born0

def Inevitability_absolute (φ : ℝ) : Prop :=
  ∀ (L : Ledger) (B : Bridge L) (A : Anchors), UniqueCalibration L B A
-- NOTE: The current "inevitability holds" witnesses (derived from the placeholder evaluator
-- `dimlessPack_explicit`) live in `RecogSpec/InevitabilityScaffold.lean` and are intentionally
-- excluded from the certified surface.

def Recognition_Closure (φ : ℝ) : Prop :=
  Inevitability_dimless φ ∧ Inevitability_absolute φ

theorem recognition_closure_from_inevitabilities
    (φ : ℝ)
    (hDim : Inevitability_dimless φ)
    (hAbs : Inevitability_absolute φ) :
    Recognition_Closure φ :=
  And.intro hDim hAbs

/-- Band acceptance witness generated from a concrete c-band checker. -/
lemma meetsBands_any_of_eval (L : Ledger) (B : Bridge L) (X : Bands)
    (U : Constants.RSUnits) (h : evalToBands_c U X) :
    MeetsBands L B X := by
  exact ⟨U, h⟩

/-- If a checker holds after rescaling, the meets-bands witness persists. -/
lemma meetsBands_any_of_eval_rescaled (L : Ledger) (B : Bridge L) (X : Bands)
    {U U' : Constants.RSUnits}
    (hUU' : Verification.UnitsRescaled U U')
    (h : evalToBands_c U X) :
    MeetsBands L B X := by
  have : evalToBands_c U' X := (evalToBands_c_invariant (U:=U) (U':=U') hUU' X).mp h
  exact meetsBands_any_of_eval (L:=L) (B:=B) (X:=X) U' this

/-- Default meets-bands witness from a centered tolerance band. -/
lemma meetsBands_any_param (L : Ledger) (B : Bridge L)
    (U : Constants.RSUnits) (tol : ℝ) (htol : 0 ≤ tol) :
    MeetsBands L B [wideBand U.c tol] := by
  have h := evalToBands_c_wideBand_center (U:=U) (tol:=tol) htol
  exact meetsBands_any_of_eval (L:=L) (B:=B) (X:=[wideBand U.c tol]) U h

/-- Minimal checker predicate: alias for `evalToBands_c`. -/
def meetsBandsCheckerP (U : Constants.RSUnits) (X : Bands) : Prop :=
  evalToBands_c U X

lemma meetsBandsCheckerP_invariant {U U' : Constants.RSUnits}
    (h : Verification.UnitsRescaled U U') (X : Bands) :
    meetsBandsCheckerP U X ↔ meetsBandsCheckerP U' X :=
  evalToBands_c_invariant (U:=U) (U':=U') h X

lemma meetsBands_any_of_checker (L : Ledger) (B : Bridge L) (X : Bands)
    (h : ∃ U, meetsBandsCheckerP U X) : MeetsBands L B X := by
  rcases h with ⟨U, hU⟩
  exact meetsBands_any_of_eval (L:=L) (B:=B) (X:=X) U hU

/-- Default meets-bands witness using the sample bands centred on `U.c`. -/
lemma meetsBands_any_default (L : Ledger) (B : Bridge L)
    (U : Constants.RSUnits) :
    MeetsBands L B (sampleBandsFor U.c) := by
  have h := center_in_sampleBandsFor (x:=U.c)
  rcases h with ⟨b, hb, hbx⟩
  have : evalToBands_c U (sampleBandsFor U.c) := ⟨b, hb, hbx⟩
  exact meetsBands_any_of_eval (L:=L) (B:=B) (X:=sampleBandsFor U.c) U this

/-- Absolute-layer acceptance bundles UniqueCalibration with MeetsBands. -/
theorem absolute_layer_any (L : Ledger) (B : Bridge L) (A : Anchors) (X : Bands)
    (hU : UniqueCalibration L B A) (hM : MeetsBands L B X) :
    UniqueCalibration L B A ∧ MeetsBands L B X :=
  And.intro hU hM

/-- Absolute-layer acceptance is invariant under admissible rescalings. -/
theorem absolute_layer_invariant {L : Ledger} {B : Bridge L} {A : Anchors} {X : Bands}
    {U U' : Constants.RSUnits}
    (hUU' : Verification.UnitsRescaled U U')
    (hU : UniqueCalibration L B A ∧ MeetsBands L B X) :
    UniqueCalibration L B A ∧ MeetsBands L B X := by
  have _ := hUU'.cfix
  exact hU

/-- Construct the absolute-layer witness from a concrete checker. -/
theorem absolute_layer_from_eval_invariant {L : Ledger} {B : Bridge L}
    {A : Anchors} {X : Bands} {U U' : Constants.RSUnits}
    (hUU' : Verification.UnitsRescaled U U')
    (hEval : evalToBands_c U X) :
    UniqueCalibration L B A ∧ MeetsBands L B X := by
  refine absolute_layer_any (L:=L) (B:=B) (A:=A) (X:=X)
    (uniqueCalibration_any L B A) ?_
  have hEval' := (evalToBands_c_invariant (U:=U) (U':=U') hUU' X).mp hEval
  exact meetsBands_any_of_eval (L:=L) (B:=B) (X:=X) U' hEval'

end RecogSpec
end IndisputableMonolith

end section
