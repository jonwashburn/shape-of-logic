import Mathlib
import IndisputableMonolith.Masses.Anchor
import IndisputableMonolith.Verification.ZMapTopologicalDerivation

/-!
# Masses Z-Map Forcing Bridge

This module upstreams the partial O2/O3 closure into the canonical mass-layer
namespace.

It packages two concrete facts:
1. Integerization scale closure (in the currently adopted parity-constrained class):
   `k = 6` is the smallest positive even scale that integerizes SM charges.
2. The canonical anchor charge map evaluates to the expected family values:
   `Z_lepton = 1332`, `Z_up = 276`, `Z_down = 24`.

This is not full first-principles closure yet, but it makes the current forcing
progress directly consumable from `Masses.*`.
-/

namespace IndisputableMonolith
namespace Masses
namespace ZMapForcing

open Anchor
open Verification.ZMapTopologicalDerivation

/-- `k = 6` is the smallest positive even integerization scale for SM charges. -/
theorem smallest_positive_even_integerization_scale :
    integerizes_all 6 ∧
      (∀ k : ℕ, 0 < k → Even k → integerizes_all k → 6 ≤ k) :=
  six_smallest_positive_even_integerizer

/-- Canonical color offset from 3-cube edge-direction count. -/
theorem canonical_color_offset : edge_direction_count = 4 :=
  edge_direction_eq_four

/-- Canonical mass-layer charge map values for the three charged families. -/
theorem anchor_charge_map_values :
    ChargeIndex.Z Sector.Lepton (-1) = 1332 ∧
    ChargeIndex.Z Sector.UpQuark (2 / 3) = 276 ∧
    ChargeIndex.Z Sector.DownQuark (-1 / 3) = 24 := by
  native_decide

/-- Mass-layer bridge: if a topology-compatible family
    (`Z_lepton = aQ̃² + bQ̃⁴`, `Z_quark = c + aQ̃² + bQ̃⁴`) matches the canonical
    anchor outputs, then `(a,b,c)` are forced to `(1,1,4)`. -/
theorem canonical_tuple_forced_from_anchor_outputs
    {a b c : ℤ}
    (hlep : Z_lepton a b = ChargeIndex.Z Sector.Lepton (-1))
    (hup : Z_up_with_offset c a b = ChargeIndex.Z Sector.UpQuark (2 / 3))
    (hdown : Z_down_with_offset c a b = ChargeIndex.Z Sector.DownQuark (-1 / 3)) :
    a = 1 ∧ b = 1 ∧ c = 4 := by
  rcases anchor_charge_map_values with ⟨hℓv, huv, hdv⟩
  have hlep' : Z_lepton a b = 1332 := by
    calc
      Z_lepton a b = ChargeIndex.Z Sector.Lepton (-1) := hlep
      _ = 1332 := hℓv
  have hup' : Z_up_with_offset c a b = 276 := by
    calc
      Z_up_with_offset c a b = ChargeIndex.Z Sector.UpQuark (2 / 3) := hup
      _ = 276 := huv
  have hdown' : Z_down_with_offset c a b = 24 := by
    calc
      Z_down_with_offset c a b = ChargeIndex.Z Sector.DownQuark (-1 / 3) := hdown
      _ = 24 := hdv
  exact full_anchor_tuple_forces_coefficients_and_offset hlep' hup' hdown'

/-- Topology-only selection-rule bridge:
if a topology-compatible complete polynomial family is ordered and satisfies the
minimal complete coefficient budget, then the coefficients are forced to
`(a,b) = (1,1)`. -/
theorem complete_ordered_min_budget_forces_unit_coeffs
    {a b : ℤ}
    (ha : a ≥ 1)
    (hb : b ≥ 1)
    (hord : ordered_hierarchy a b)
    (hmin : a + b = 2) :
    a = 1 ∧ b = 1 :=
  Verification.ZMapTopologicalDerivation.complete_ordered_min_budget_forces_unit_coeffs
    ha hb hord hmin

/-- Upstreamed minimizer-form selection rule bridge for O2':
any complete ordered minimizer in the topology family is forced to `(a,b)=(1,1)`. -/
theorem complete_ordered_minimizer_forces_unit_coeffs
    {a b : ℤ}
    (hmin : complete_ordered_minimizer a b) :
    a = 1 ∧ b = 1 :=
  Verification.ZMapTopologicalDerivation.complete_ordered_minimizer_forces_unit_coeffs hmin

/-- Upstreamed joint first-principles Z-map tuple forcing:
if `(k, a, b, c)` satisfies smallest-positive-even integerization + minimal-complete-ordered
coefficients + edge-direction color offset, then `(k, a, b, c) = (6, 1, 1, 4)`. -/
theorem zmap_canonical_tuple_forced_from_first_principles
    {k : ℕ} {a b c : ℤ}
    (hk_pos : 0 < k) (hk_even : Even k)
    (hint : integerizes_all k)
    (hmin_k : ∀ k' : ℕ, 0 < k' → Even k' → integerizes_all k' → k ≤ k')
    (hminab : complete_ordered_minimizer a b)
    (hc : c = (edge_direction_count : ℤ)) :
    k = 6 ∧ a = 1 ∧ b = 1 ∧ c = 4 :=
  Verification.ZMapTopologicalDerivation.zmap_canonical_tuple_forced_from_first_principles
    hk_pos hk_even hint hmin_k hminab hc

/-- Upstreamed converse: canonical `(6, 1, 1, 4)` satisfies all first-principles
characterization conditions. -/
theorem zmap_canonical_tuple_satisfies_first_principles :
    integerizes_all 6 ∧
    (∀ k' : ℕ, 0 < k' → Even k' → integerizes_all k' → 6 ≤ k') ∧
    complete_ordered_minimizer 1 1 ∧
    (4 : ℤ) = (edge_direction_count : ℤ) :=
  Verification.ZMapTopologicalDerivation.zmap_canonical_tuple_satisfies_first_principles

/-- Upstreamed bundled first-principles tuple predicate for the Z-map lane. -/
def first_principles_zmap_tuple (k : ℕ) (a b c : ℤ) : Prop :=
  Verification.ZMapTopologicalDerivation.first_principles_zmap_tuple k a b c

/-- Upstreamed iff characterization:
`(k, a, b, c)` is canonical iff it satisfies the bundled first-principles
tuple constraints. -/
theorem canonical_tuple_iff_first_principles (k : ℕ) (a b c : ℤ) :
    first_principles_zmap_tuple k a b c ↔ (k = 6 ∧ a = 1 ∧ b = 1 ∧ c = 4) :=
  Verification.ZMapTopologicalDerivation.canonical_tuple_iff_first_principles k a b c

end ZMapForcing
end Masses
end IndisputableMonolith
