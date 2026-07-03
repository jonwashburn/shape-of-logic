import Mathlib
import IndisputableMonolith.Bridge.CosmicZDisplayMap
import IndisputableMonolith.Masses.DisplayBridgeAlgebra

/-!
# Cosmic-Z Display Formula Interface

`CosmicZDisplayMap.lean` proves the correct discrete input surface for the
missing particle-mass bridge: the charged-sector display map must see the
pair `(ZOf f, rung f)`, not only `ZOf f`.

This file adds the next layer: the formal interface for a future
first-principles display formula over that key. It deliberately does not claim
the physical formula has been derived. Instead, it proves the transport
properties that any such formula will inherit once the theorem-grade
theta/RG/cosmic-Z law is supplied.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Bridge
namespace CosmicZDisplayFormula

open IndisputableMonolith.Bridge.CosmicZDisplayMap
open IndisputableMonolith.Masses.DisplayBridgeAlgebra
open IndisputableMonolith.RSBridge
open IndisputableMonolith.Masses.HeavyQuarkFullClosureObstruction

/-- The finite display key used by the charged mass spectrum. -/
abbrev DisplayKey := ℤ × ℤ

/-- A candidate cosmic-Z display formula. The final closure must replace the
audit lookup by a formula derived from theta/RG/cosmic-Z dynamics. -/
structure CosmicZFormula where
  shift : DisplayKey → ℝ

/-- Species-level shift obtained by evaluating the formula at `(ZOf f, rung f)`. -/
noncomputable def speciesShift (F : CosmicZFormula) (f : Fermion) : ℝ :=
  F.shift (zRungKey f)

/-- Formula evaluation is key-respecting by construction. -/
theorem speciesShift_eq_of_same_key
    (F : CosmicZFormula) {f g : Fermion}
    (h : zRungKey f = zRungKey g) :
    speciesShift F f = speciesShift F g := by
  unfold speciesShift
  rw [h]

/-- Heavy-quark match predicate for the later physical formula. This is the
exact condition the future theorem must prove without using the audit lookup. -/
def HeavyQuarkShiftMatch (F : CosmicZFormula) : Prop :=
  ZRungHeavyQuarkShift F.shift

/-- Audit formula induced by the evaluated raw-shift table. This is a witness
that the interface is expressive enough; it is not the physical derivation. -/
noncomputable def evaluatedAuditFormula : CosmicZFormula where
  shift := evaluatedZRungShift

theorem evaluatedAuditFormula_matches_heavy_quarks :
    HeavyQuarkShiftMatch evaluatedAuditFormula :=
  evaluated_zRung_shift_matches

/-- Charm and top can be split by a key-sensitive formula because their
`(ZOf,rung)` keys differ. The particular witness here is the audit formula. -/
theorem exists_key_formula_splits_charm_top :
    ∃ F : CosmicZFormula, speciesShift F .c ≠ speciesShift F .t := by
  refine ⟨evaluatedAuditFormula, ?_⟩
  unfold speciesShift evaluatedAuditFormula
  have hmatch := evaluatedAuditFormula_matches_heavy_quarks
  unfold HeavyQuarkShiftMatch ZRungHeavyQuarkShift at hmatch
  obtain ⟨hc, _, ht⟩ := hmatch
  obtain ⟨_, _, hct⟩ := required_exponents_not_equal
  intro hsame
  exact hct (by
    calc
      charm_required_phi_exponent = evaluatedZRungShift (zRungKey .c) := hc.symm
      _ = evaluatedZRungShift (zRungKey .t) := hsame
      _ = top_required_phi_exponent := ht)

/-- The charged display key table is already complete and collision-free. -/
theorem charged_display_key_table_ready :
    chargedZRungKeys.Nodup ∧
    chargedZRungKeys =
      [(1332, 2), (1332, 13), (1332, 19),
       (276, 4), (276, 15), (276, 21),
       (24, 4), (24, 15), (24, 21)] :=
  ⟨charged_zRung_keys_nodup, charged_zRung_keys_eval⟩

/-- Displayed MeV masses are already in algebraic normal form. This theorem
exports the mass-side handoff needed by the future formula theorem. -/
theorem displayed_mass_normal_form :
    ∀ s r, IndisputableMonolith.Masses.Verification.rs_mass_MeV s r =
      displayedSectorMass s r :=
  rs_mass_MeV_eq_displayedSectorMass

/-- Contract for the eventual theorem-grade display formula. It has two parts:

1. the formula is defined on the proven charged `(ZOf,rung)` key table;
2. it matches the heavy-quark raw-shift obstruction constants.

The second part is still an audit target here. A future module must replace it
with a derivation from theta/RG/cosmic-Z dynamics. -/
structure CosmicZDisplayFormulaInterfaceCert where
  charged_keys_ready :
    chargedZRungKeys.Nodup ∧
    chargedZRungKeys =
      [(1332, 2), (1332, 13), (1332, 19),
       (276, 4), (276, 15), (276, 21),
       (24, 4), (24, 15), (24, 21)]
  displayed_mass_algebra :
    ∀ s r, IndisputableMonolith.Masses.Verification.rs_mass_MeV s r =
      displayedSectorMass s r
  formula_respects_keys :
    ∀ (F : CosmicZFormula) {f g : Fermion},
      zRungKey f = zRungKey g →
      speciesShift F f = speciesShift F g
  audit_formula_matches_heavy_quarks :
    HeavyQuarkShiftMatch evaluatedAuditFormula
  key_formula_can_split_charm_top :
    ∃ F : CosmicZFormula, speciesShift F .c ≠ speciesShift F .t

def cosmicZDisplayFormulaInterfaceCert_holds :
    CosmicZDisplayFormulaInterfaceCert where
  charged_keys_ready := charged_display_key_table_ready
  displayed_mass_algebra := displayed_mass_normal_form
  formula_respects_keys := fun F {f} {g} h => speciesShift_eq_of_same_key F (f := f) (g := g) h
  audit_formula_matches_heavy_quarks := evaluatedAuditFormula_matches_heavy_quarks
  key_formula_can_split_charm_top := exists_key_formula_splits_charm_top

end CosmicZDisplayFormula
end Bridge
end IndisputableMonolith
