import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.ParticleGenerations
import IndisputableMonolith.Foundation.GrayCodeChirality
import IndisputableMonolith.Foundation.GaugeFromCube
import IndisputableMonolith.StandardModel.JarlskogInvariant

/-!
# Sakharov Conditions from the RS Ledger

Baryogenesis (the creation of the matter-antimatter asymmetry) requires
three conditions (Sakharov, 1967):

1. **Baryon number violation** (B violation)
2. **C and CP violation**
3. **Departure from thermal equilibrium**

This module proves TWO structural facts (a ΔB bookkeeping identity and
J_CP ≠ 0) and carries the THIRD condition (departure from equilibrium) as an
explicit, underived hypothesis parameter. An earlier revision claimed all
three were derived "with zero imported physics"; that was false (the
out-of-equilibrium condition was a `True` placeholder) and is corrected
below. Baryon number as a ledger winding charge is itself an
interpretation, not a derived anomaly structure (audit FQ4).

## Derivation

### Condition 1: Baryon Number Violation
On the Z³ ledger, baryon number is a winding charge along one axis
(WindingCharges). Sphaleron-like processes correspond to collective
8-tick phase rotations that change all three winding numbers
simultaneously. The ledger allows this because the double-entry
structure permits balanced multi-axis rotations.

The B-violation rate scales with the weak coupling:
  Γ_sph ∝ α_W⁵ T⁴
(standard sphaleron-rate scaling, imported from the SM literature; α_W is
NOT derived here).

### Condition 2: CP Violation
PROVED in CPPhaseDerivation: the Berry phase of the chiral Gray code
cycle gives δ_CKM ≠ 0, hence J_CP > 0 (JarlskogInvariant).

### Condition 3: Out of Equilibrium — HYPOTHESIS, NOT DERIVED
Whether the electroweak transition is first order is an open
thermal-field-theory question; in the minimal SM with m_H ≈ 125 GeV it is a
crossover. No RS derivation exists. The condition is carried below as an
explicit hypothesis parameter on every downstream statement.

## Main Results

1. `SakharovConditions EWFirstOrder`: structure packaging the two proved
   pieces plus the named out-of-equilibrium hypothesis
2. `sakharov_from_RS (hEW)`: CONDITIONAL assembly given the hypothesis
3. `sphaleron_changes_B_by_3`, `sphaleron_preserves_b_minus_l`: ΔB bookkeeping
4. `cp_source_positive`: CP violation from J_CP > 0 (structural)
-/

namespace IndisputableMonolith
namespace Cosmology
namespace SakharovFromLedger

open Constants
open Foundation.ParticleGenerations
open Foundation.GrayCodeChirality
open StandardModel.JarlskogInvariant

/-! ## Part 1: Baryon Number as Winding Charge

Baryon number B is one of three independent topological charges on Z³.
It is conserved under local deformations but can change under global
(sphaleron) processes that rotate all three axes simultaneously. -/

/-- The three independent conservation laws in D = 3. -/
theorem three_conservation_laws : face_pairs 3 = 3 := rfl

/-- Sphaleron processes change baryon number by ΔB = N_gen = 3 per event.
    This is because each generation contributes one unit of B-violation,
    and there are exactly 3 generations (from D = 3). -/
def deltaB_per_sphaleron : ℕ := face_pairs 3

theorem sphaleron_changes_B_by_3 : deltaB_per_sphaleron = 3 := rfl

/-- Sphaleron events change lepton number by the same amount as baryon
    number (one unit per generation, 3 generations). This is imported SM
    anomaly bookkeeping, not a ledger derivation (audit FQ4). -/
def deltaL_per_sphaleron : ℕ := face_pairs 3

/-- B − L is unchanged per sphaleron event: ΔB = ΔL, so Δ(B−L) = 0.
    (An earlier revision stated this as the tautology `ΔB = ΔB`, which
    carried no content; corrected to the actual invariant.) -/
theorem sphaleron_preserves_b_minus_l :
    (deltaB_per_sphaleron : ℤ) - (deltaL_per_sphaleron : ℤ) = 0 := by
  simp [deltaB_per_sphaleron, deltaL_per_sphaleron]

/-! ## Part 2: CP Violation Source Term

The Jarlskog invariant J_CP provides the CP-violating source term for
baryogenesis. It enters the baryon production rate as:

  ε_CP ∝ J_CP × (mass factors)

where the mass factors involve the torsion-induced mass hierarchy. -/

/-- CP violation source: J_CP > 0 from JarlskogInvariant. -/
theorem cp_source_positive : jarlskog_structural > 0 := jarlskog_positive

/-- The CP asymmetry parameter ε is proportional to J_CP. -/
noncomputable def cp_asymmetry_parameter : ℝ := jarlskog_structural

theorem cp_asymmetry_nonzero : cp_asymmetry_parameter ≠ 0 :=
  ne_of_gt jarlskog_positive

/-! ## Part 3: Electroweak Phase Transition

The EW phase transition temperature T_EW lies on the φ-ladder. Above T_EW,
the Higgs VEV is zero (symmetric phase); below, it acquires a nonzero value.

In RS, the Higgs field is not fundamental — it emerges from the ε⁴ term
of J(e^ε) = cosh(ε) − 1. The VEV v = 246 GeV sits on a specific φ-rung. -/

/-! **PHYSICAL HYPOTHESIS (NOT DERIVED — corrected 2026-07-06).**

An earlier revision defined `ew_transition_is_first_order : Prop := True` and
"proved" it with `trivial`. The 2026 internal audit correctly identified this
as a vacuous placeholder wearing a physics name. It is retracted.

The honest status: whether the electroweak phase transition is first order is
a hard thermal-field-theory question. In the minimal Standard Model with
m_H ≈ 125 GeV the transition is in fact a CROSSOVER (Kajantie–Laine–
Rummukainen–Shaposhnikov 1996), so a first-order transition requires
beyond-SM dynamics. No RS derivation of this exists, and this repository has
no finite-temperature effective potential with which even to STATE it
faithfully.

Rather than fake content, everything downstream is PARAMETERIZED over an
abstract proposition `EWFirstOrder : Prop`. The dependence is therefore
visible in every type signature, and no theorem in this repository
discharges it. -/

/-! ## Part 4: Sakharov Conditions Assembled (conditionally) -/

/-- The three Sakharov conditions, parameterized over the UNDERIVED
    out-of-equilibrium proposition. `EWFirstOrder` is an abstract Prop:
    this repository cannot state it faithfully, let alone prove it. -/
structure SakharovConditions (EWFirstOrder : Prop) where
  b_violation : deltaB_per_sphaleron = 3
  cp_violation : cp_asymmetry_parameter ≠ 0
  out_of_eq : EWFirstOrder

/-- **CONDITIONAL assembly**: given the out-of-equilibrium hypothesis
    (NOT derived here; a crossover in the minimal SM), the two structural
    conditions (ΔB per sphaleron event, J_CP ≠ 0) combine with it into the
    Sakharov package. This is bookkeeping of the two proved pieces plus one
    named hypothesis — NOT a derivation of baryogenesis. -/
def sakharov_from_RS {EWFirstOrder : Prop} (hEW : EWFirstOrder) :
    SakharovConditions EWFirstOrder where
  b_violation := rfl
  cp_violation := cp_asymmetry_nonzero
  out_of_eq := hEW

/-- Conditional statement: two structural facts hold unconditionally; the
    third (out-of-equilibrium) is carried as an explicit hypothesis. The
    earlier claim that all three were "derived (not postulated)" is
    retracted. -/
theorem baryogenesis_possible {EWFirstOrder : Prop} (hEW : EWFirstOrder) :
    deltaB_per_sphaleron = 3 ∧ cp_asymmetry_parameter ≠ 0 ∧ EWFirstOrder :=
  ⟨rfl, cp_asymmetry_nonzero, hEW⟩

end SakharovFromLedger
end Cosmology
end IndisputableMonolith
