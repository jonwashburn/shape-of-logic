import Mathlib
import IndisputableMonolith.Foundation.GaugeLieCompletionFromCube

/-!
# Standard Model Hypercharge Layer from the Cube Completion

This module continues `P0-S2-01` from
`planning/REALITY_DERIVATION_PUNCHLIST.md`.

`GaugeLieCompletionFromCube` proves the compact gauge-factor skeleton:

* `SU(3) x SU(2) x U(1)`
* recognition-axis counts `(3,2,1)`
* carrier counts `(8,3,1)`

The next question is whether the Standard Model fermion multiplets and
hypercharges can be represented in the same cube-completion units.

Here we use the canonical hypercharge denominator `6`, i.e. every
hypercharge is represented by the integer `Y6 = 6Y`.

For one left-handed generation, including the sterile/right-handed neutrino
as the hypercharge-zero completion:

* `Q_L`: multiplicity 6, `Y6 = 1`
* `u^c_L`: multiplicity 3, `Y6 = -4`
* `d^c_L`: multiplicity 3, `Y6 = 2`
* `L_L`: multiplicity 2, `Y6 = -3`
* `e^c_L`: multiplicity 1, `Y6 = 6`
* `nu^c_L`: multiplicity 1, `Y6 = 0`

This gives `16` Weyl states per generation and exact cancellation of the
`SU(3)^2 U(1)`, `SU(2)^2 U(1)`, gravitational-`U(1)`, and `U(1)^3`
anomaly sums in integer arithmetic.

This is still not a proof that these hypercharges are uniquely forced.
It is the exact anomaly-free SM hypercharge layer expressed in the cube
completion's `1/6` unit.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Foundation.SMHyperchargeFromCube

open GaugeLieCompletionFromCube

/-- One left-handed generation of SM Weyl multiplets. -/
inductive WeylMultiplet where
  | quarkDoublet
  | upConjugate
  | downConjugate
  | leptonDoublet
  | electronConjugate
  | neutrinoConjugate
  deriving DecidableEq, Repr, BEq, Fintype

theorem weylMultiplet_count : Fintype.card WeylMultiplet = 6 := by
  decide

/-- Number of Weyl states carried by each multiplet, including color and weak components. -/
def weylMultiplicity : WeylMultiplet -> ℕ
  | .quarkDoublet => 6
  | .upConjugate => 3
  | .downConjugate => 3
  | .leptonDoublet => 2
  | .electronConjugate => 1
  | .neutrinoConjugate => 1

/-- Hypercharge in sixths: `Y6 = 6Y`. -/
def hypercharge6 : WeylMultiplet -> ℤ
  | .quarkDoublet => 1      -- Y =  1/6
  | .upConjugate => -4      -- Y = -2/3
  | .downConjugate => 2     -- Y =  1/3
  | .leptonDoublet => -3    -- Y = -1/2
  | .electronConjugate => 6 -- Y =  1
  | .neutrinoConjugate => 0 -- Y =  0

/-- The Higgs doublet has `Y = 1/2`, i.e. `Y6 = 3`. -/
def higgsHypercharge6 : ℤ := 3

theorem higgsHypercharge6_eq : higgsHypercharge6 = 3 := rfl

/-- One generation has `6 + 3 + 3 + 2 + 1 + 1 = 16` Weyl states. -/
def generationWeylStateCount : ℕ :=
  weylMultiplicity .quarkDoublet +
  weylMultiplicity .upConjugate +
  weylMultiplicity .downConjugate +
  weylMultiplicity .leptonDoublet +
  weylMultiplicity .electronConjugate +
  weylMultiplicity .neutrinoConjugate

theorem generationWeylStateCount_eq_16 : generationWeylStateCount = 16 := by
  native_decide

/-- Three generations contain `48 = |B3|` Weyl states in this accounting. -/
def threeGenerationWeylStateCount : ℕ := 3 * generationWeylStateCount

theorem threeGenerationWeylStateCount_eq_48 :
    threeGenerationWeylStateCount = Fintype.card (GaugeFromCube.SignedPerm 3) := by
  rw [GaugeFromCube.cube_aut_order]
  native_decide

/-! ## Exact anomaly sums in `Y6 = 6Y` units -/

/-- `SU(3)^2 U(1)` anomaly in sixth-units: `2Y_Q + Y_u^c + Y_d^c = 0`. -/
def su3SquaredU1Anomaly6 : ℤ :=
  2 * hypercharge6 .quarkDoublet +
  hypercharge6 .upConjugate +
  hypercharge6 .downConjugate

theorem su3SquaredU1Anomaly6_eq_zero : su3SquaredU1Anomaly6 = 0 := by
  native_decide

/-- `SU(2)^2 U(1)` anomaly: `3Y_Q + Y_L = 0`. -/
def su2SquaredU1Anomaly6 : ℤ :=
  3 * hypercharge6 .quarkDoublet +
  hypercharge6 .leptonDoublet

theorem su2SquaredU1Anomaly6_eq_zero : su2SquaredU1Anomaly6 = 0 := by
  native_decide

/-- Gravitational-`U(1)` anomaly, scaled by 6. -/
def gravitationalU1Anomaly6 : ℤ :=
  6 * hypercharge6 .quarkDoublet +
  3 * hypercharge6 .upConjugate +
  3 * hypercharge6 .downConjugate +
  2 * hypercharge6 .leptonDoublet +
  hypercharge6 .electronConjugate +
  hypercharge6 .neutrinoConjugate

theorem gravitationalU1Anomaly6_eq_zero : gravitationalU1Anomaly6 = 0 := by
  native_decide

/-- Cubic `U(1)^3` anomaly, scaled by `6^3`. -/
def cubicU1Anomaly6 : ℤ :=
  6 * (hypercharge6 .quarkDoublet)^3 +
  3 * (hypercharge6 .upConjugate)^3 +
  3 * (hypercharge6 .downConjugate)^3 +
  2 * (hypercharge6 .leptonDoublet)^3 +
  (hypercharge6 .electronConjugate)^3 +
  (hypercharge6 .neutrinoConjugate)^3

theorem cubicU1Anomaly6_eq_zero : cubicU1Anomaly6 = 0 := by
  native_decide

/-! ## Electric charges in sixth-units -/

/-- Weak isospin third component in sixth-units: `T3_6 = 6T3 = ±3`. -/
inductive WeakComponent where
  | upper
  | lower
  deriving DecidableEq, Repr, BEq, Fintype

def weakT3_6 : WeakComponent -> ℤ
  | .upper => 3
  | .lower => -3

/-- Electric charge in sixth-units: `Q6 = 6Q = T3_6 + Y6`. -/
def electricCharge6 (m : WeylMultiplet) (c : WeakComponent) : ℤ :=
  weakT3_6 c + hypercharge6 m

theorem quark_doublet_charges :
    electricCharge6 .quarkDoublet .upper = 4 ∧
    electricCharge6 .quarkDoublet .lower = -2 := by
  native_decide

theorem lepton_doublet_charges :
    electricCharge6 .leptonDoublet .upper = 0 ∧
    electricCharge6 .leptonDoublet .lower = -6 := by
  native_decide

structure SMHyperchargeCert where
  six_multiplets : Fintype.card WeylMultiplet = 6
  one_generation_16 : generationWeylStateCount = 16
  three_generations_b3 : threeGenerationWeylStateCount =
    Fintype.card (GaugeFromCube.SignedPerm 3)
  su3_anomaly_zero : su3SquaredU1Anomaly6 = 0
  su2_anomaly_zero : su2SquaredU1Anomaly6 = 0
  gravitational_anomaly_zero : gravitationalU1Anomaly6 = 0
  cubic_anomaly_zero : cubicU1Anomaly6 = 0
  quark_charges : electricCharge6 .quarkDoublet .upper = 4 ∧
    electricCharge6 .quarkDoublet .lower = -2
  lepton_charges : electricCharge6 .leptonDoublet .upper = 0 ∧
    electricCharge6 .leptonDoublet .lower = -6
  higgs_y6 : higgsHypercharge6 = 3

def smHyperchargeCert : SMHyperchargeCert where
  six_multiplets := weylMultiplet_count
  one_generation_16 := generationWeylStateCount_eq_16
  three_generations_b3 := threeGenerationWeylStateCount_eq_48
  su3_anomaly_zero := su3SquaredU1Anomaly6_eq_zero
  su2_anomaly_zero := su2SquaredU1Anomaly6_eq_zero
  gravitational_anomaly_zero := gravitationalU1Anomaly6_eq_zero
  cubic_anomaly_zero := cubicU1Anomaly6_eq_zero
  quark_charges := quark_doublet_charges
  lepton_charges := lepton_doublet_charges
  higgs_y6 := higgsHypercharge6_eq

end IndisputableMonolith.Foundation.SMHyperchargeFromCube
