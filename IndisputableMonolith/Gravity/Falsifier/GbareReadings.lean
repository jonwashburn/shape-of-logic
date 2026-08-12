import Mathlib
import IndisputableMonolith.Gravity.Falsifier.VoxelLagCost

/-!
# GbareReadings: the three candidate identifications of the bare recognition path

Part of the Nautilus `Gravity/Falsifier/` DAG (panel verdict 2026-07-03).

`Gravity/GravitationalPrepaidChannel.lean` prices the lift exactly: `(1 - w_g)·Gbare =
prepaid`. But `Gbare` (the bare gravitational recognition path of the object being lifted)
is a free positive real there. The falsifier's predicted weight dip is `prepaid/Gbare`, so
the magnitude, hence whether a benchtop experiment can see it, is decided entirely by WHICH
number `Gbare` is. There are three physically distinct candidate readings, and they differ
by many orders of magnitude. This module states all three as **named premises** (honest
"IF", never asserted), so every downstream forward-model and discriminator theorem is
conditional on a named `BarePathIs…` and nothing smuggles in a magnitude.

This is the `HorizonEntropyIsRecordCost` pattern (`Holography/RecordCostAsymmetry.lean`):
name the identification as a `Prop`, make the quantitative theorems conditional on it, and
exhibit the fork (the readings genuinely differ) so no reading is assumed.

## The three readings (units-explicit)

1. **Voxel field-energy** (`BarePathIsVoxelFieldSchedule`): `Gbare = voxelBareCost` — set by
   the field `g` and region volume `V`, MASS-BLIND. High-ceiling branch (mass-independent
   dip, flat-space bubble, benchtop watts).
2. **Rest-energy** (`BarePathIsRestEnergySchedule`): `Gbare = m·c²/E_coh_J` — the full
   rest-energy recognition schedule of the test mass. Largest number; hardest to drive.
3. **Lag-correction** (`BarePathIsLagCorrection`): `Gbare = Clag·m·c²/E_coh_J` — only the
   `φ⁻⁵` lag share of the rest-energy schedule.

## Status: each reading is HYPOTHESIS (a named premise); `readings_differ` is THEOREM.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Falsifier

open Constants

noncomputable section

/-- The rest-energy recognition schedule: `m·c²` counted in `E_coh_J`-sized events. -/
noncomputable def restEnergyBareCost (m c E_coh_J : ℝ) : ℝ :=
  m * c ^ 2 / E_coh_J

theorem restEnergyBareCost_pos {m c E_coh_J : ℝ}
    (hm : 0 < m) (hc : c ≠ 0) (hE : 0 < E_coh_J) :
    0 < restEnergyBareCost m c E_coh_J := by
  unfold restEnergyBareCost
  positivity

/-! ## The three named premises (Props; asserted by no theorem here) -/

/-- **Reading 1 (voxel):** the object's bare gravitational recognition path equals the
    voxel field-energy count of the field it sits in. Mass-blind. -/
def BarePathIsVoxelFieldSchedule (Gbare Clag g V Gnewton E_coh_J : ℝ) : Prop :=
  Gbare = voxelBareCost Clag g V Gnewton E_coh_J

/-- **Reading 2 (rest-energy):** the bare path equals the full rest-energy schedule. -/
def BarePathIsRestEnergySchedule (Gbare m c E_coh_J : ℝ) : Prop :=
  Gbare = restEnergyBareCost m c E_coh_J

/-- **Reading 3 (lag-correction):** the bare path equals only the `Clag` lag share of the
    rest-energy schedule. -/
def BarePathIsLagCorrection (Gbare Clag m c E_coh_J : ℝ) : Prop :=
  Gbare = Clag * restEnergyBareCost m c E_coh_J

/-! ## The fork is real: the readings genuinely differ -/

/-- **The lag-correction reading is strictly below the rest-energy reading** whenever the
    lag fraction is a genuine fraction (`0 < Clag < 1`). So readings 2 and 3 are not the
    same number: the fork is non-vacuous, and a downstream theorem cannot silently use one
    where it named the other. -/
theorem lag_below_rest {Clag m c E_coh_J : ℝ}
    (hClag0 : 0 < Clag) (hClag1 : Clag < 1)
    (hm : 0 < m) (hc : c ≠ 0) (hE : 0 < E_coh_J) :
    Clag * restEnergyBareCost m c E_coh_J < restEnergyBareCost m c E_coh_J := by
  have hR : 0 < restEnergyBareCost m c E_coh_J := restEnergyBareCost_pos hm hc hE
  nlinarith [hR, hClag0, hClag1, mul_pos hClag0 hR]

/-- Certificate: the three readings are well-defined and the fork is real (the lag reading
    is a strict fraction of the rest-energy reading). Nothing asserts which reading holds. -/
structure GbareReadingsCert : Prop where
  rest_pos : ∀ m c E_coh_J : ℝ, 0 < m → c ≠ 0 → 0 < E_coh_J →
    0 < restEnergyBareCost m c E_coh_J
  fork_real : ∀ Clag m c E_coh_J : ℝ, 0 < Clag → Clag < 1 → 0 < m → c ≠ 0 → 0 < E_coh_J →
    Clag * restEnergyBareCost m c E_coh_J < restEnergyBareCost m c E_coh_J

theorem gbareReadingsCert : GbareReadingsCert where
  rest_pos := fun _ _ _ hm hc hE => restEnergyBareCost_pos hm hc hE
  fork_real := fun _ _ _ _ hC0 hC1 hm hc hE => lag_below_rest hC0 hC1 hm hc hE

end

end Falsifier
end Gravity
end IndisputableMonolith
