import Mathlib
import IndisputableMonolith.Bridge.EcohScaleReconciliation
import IndisputableMonolith.Masses.RSBridge.Anchor

/-!
# Cosmic-Z Display Map Shape

This module formalizes the next bridge target after the `tau_n` SI audit.

The previous audit proves that raw heavy-quark masses obtained from the
non-circular `tau_n` bridge cannot be repaired by one universal φ-shift, and
cannot be repaired by a `ZOf`-only shift. This file proves the complementary
shape fact: the pair `(ZOf f, rung f)` separates the heavy-quark channels that
`ZOf` alone cannot separate.

This is still an audit/interface module, not the final physical closure. The
actual cosmic-Z display map must derive the shift from recognition dynamics,
theta phase, or the RG running window. The theorem here says what data that map
must be allowed to see.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Bridge
namespace CosmicZDisplayMap

open IndisputableMonolith.RSBridge
open IndisputableMonolith.Masses.HeavyQuarkFullClosureObstruction

/-- The minimal discrete key suggested by the raw heavy-quark obstruction:
topological charge plus rung/generation location. -/
noncomputable def zRungKey (f : Fermion) : ℤ × ℤ :=
  (ZOf f, rung f)

theorem charm_key : zRungKey .c = (276, 15) := by
  norm_num [zRungKey, ZOf, tildeQ, sectorOf, rung]

theorem bottom_key : zRungKey .b = (24, 21) := by
  norm_num [zRungKey, ZOf, tildeQ, sectorOf, rung]

theorem top_key : zRungKey .t = (276, 21) := by
  norm_num [zRungKey, ZOf, tildeQ, sectorOf, rung]

/-- Charm and top are the decisive obstruction to a Z-only correction: same
`ZOf`, different rung. -/
theorem charm_top_same_Z_different_rung :
    ZOf .c = ZOf .t ∧ rung .c ≠ rung .t := by
  constructor
  · norm_num [ZOf, tildeQ, sectorOf]
  · norm_num [rung]

/-- The `(ZOf, rung)` key separates the heavy channels used in the raw bridge
obstruction. -/
theorem heavy_quark_zRung_keys_pairwise_distinct :
    zRungKey .c ≠ zRungKey .b ∧
    zRungKey .c ≠ zRungKey .t ∧
    zRungKey .b ≠ zRungKey .t := by
  constructor
  · norm_num [zRungKey, ZOf, tildeQ, sectorOf, rung]
  constructor
  · norm_num [zRungKey, ZOf, tildeQ, sectorOf, rung]
  · norm_num [zRungKey, ZOf, tildeQ, sectorOf, rung]

/-- The charged fermions, in the order used by the mass-spectrum display table. -/
def chargedFermions : List Fermion :=
  [.e, .mu, .tau, .u, .c, .t, .d, .s, .b]

/-- The `(ZOf, rung)` display keys for all charged fermions. -/
noncomputable def chargedZRungKeys : List (ℤ × ℤ) :=
  chargedFermions.map zRungKey

/-- Evaluated charged-sector display keys. This is pure structural data from
the already-forced Z-map and rung assignments. -/
theorem charged_zRung_keys_eval :
    chargedZRungKeys =
      [(1332, 2), (1332, 13), (1332, 19),
       (276, 4), (276, 15), (276, 21),
       (24, 4), (24, 15), (24, 21)] := by
  norm_num [chargedZRungKeys, chargedFermions, zRungKey, ZOf, tildeQ, sectorOf, rung]

/-- The `(ZOf, rung)` key is collision-free on the charged fermion spectrum. -/
theorem charged_zRung_keys_nodup : chargedZRungKeys.Nodup := by
  rw [charged_zRung_keys_eval]
  decide

/-- A display shift indexed by `(ZOf, rung)` can at least represent the
evaluated raw heavy-quark obstruction constants. This is only a representation
witness, not a derivation of those constants. -/
def ZRungHeavyQuarkShift (shift : ℤ × ℤ → ℝ) : Prop :=
  shift (zRungKey .c) = charm_required_phi_exponent ∧
  shift (zRungKey .b) = bottom_required_phi_exponent ∧
  shift (zRungKey .t) = top_required_phi_exponent

/-- Lookup table for the evaluated audit constants, indexed by `(ZOf, rung)`.
This is intentionally tagged as an audit witness: the final theory must replace
this lookup with a first-principles cosmic-Z/RG formula. -/
noncomputable def evaluatedZRungShift : ℤ × ℤ → ℝ :=
  fun key =>
    if key = zRungKey .c then charm_required_phi_exponent
    else if key = zRungKey .b then bottom_required_phi_exponent
    else if key = zRungKey .t then top_required_phi_exponent
    else 0

theorem evaluated_zRung_shift_matches :
    ZRungHeavyQuarkShift evaluatedZRungShift := by
  unfold ZRungHeavyQuarkShift evaluatedZRungShift
  obtain ⟨hcb, hct, hbt⟩ := heavy_quark_zRung_keys_pairwise_distinct
  constructor
  · simp
  constructor
  · simp [hcb.symm]
  · simp [hct.symm, hbt.symm]

/-- The map-shape certificate for the next closure pass. It packages three
facts:

1. `ZOf` alone is too coarse.
2. `(ZOf, rung)` separates the heavy channels.
3. `(ZOf, rung)` can represent the evaluated shifts, though this is not yet a
   first-principles derivation. -/
structure CosmicZDisplayMapShapeCert where
  no_Z_only_shift :
    ¬ ∃ shift : ℤ → ℝ, EcohScaleReconciliation.ZOnlyHeavyQuarkShift shift
  charm_top_same_Z_different_rung :
    ZOf .c = ZOf .t ∧ rung .c ≠ rung .t
  zRung_keys_pairwise_distinct :
    zRungKey .c ≠ zRungKey .b ∧
    zRungKey .c ≠ zRungKey .t ∧
    zRungKey .b ≠ zRungKey .t
  charged_key_table_eval :
    chargedZRungKeys =
      [(1332, 2), (1332, 13), (1332, 19),
       (276, 4), (276, 15), (276, 21),
       (24, 4), (24, 15), (24, 21)]
  charged_key_table_nodup :
    chargedZRungKeys.Nodup
  zRung_audit_lookup_exists :
    ∃ shift : ℤ × ℤ → ℝ, ZRungHeavyQuarkShift shift

def cosmicZDisplayMapShapeCert_holds : CosmicZDisplayMapShapeCert where
  no_Z_only_shift := EcohScaleReconciliation.no_z_only_heavy_quark_shift
  charm_top_same_Z_different_rung := charm_top_same_Z_different_rung
  zRung_keys_pairwise_distinct := heavy_quark_zRung_keys_pairwise_distinct
  charged_key_table_eval := charged_zRung_keys_eval
  charged_key_table_nodup := charged_zRung_keys_nodup
  zRung_audit_lookup_exists := ⟨evaluatedZRungShift, evaluated_zRung_shift_matches⟩

end CosmicZDisplayMap
end Bridge
end IndisputableMonolith
