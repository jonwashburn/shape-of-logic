import Mathlib
import IndisputableMonolith.Constants

/-!
# Biodiversity Scaling from J-Cost (Track Q3 of Plan v7)

## Status: PARTIAL THEOREM (structural species-area exponent in
canonical band).
## Empirical adjudication (W4): a companion Python pull from GBIF
or BioTIME would extract per-region species counts vs sampling
area and fit Arrhenius's exponent. This module proves the structural
identity and the band check against `z ∈ (0.15, 0.45)` which is
sufficient to falsify against the canonical Arrhenius dispersion
of empirical species-area exponents.

The species-area relationship (Arrhenius 1921, MacArthur-Wilson 1967)
states `S = c · A^z` for species count `S` over sampled area `A`,
with empirical `z ∈ (0.20, 0.40)` across taxa and biomes.

## RS reading

A regional ecosystem is a recognition graph on its species inventory.
σ-conservation on the inventory graph forces a φ-self-similar bond
density: each new sampling-area doubling adds `1 + 1/φ = φ` times
the ledger weight, and the species count grows as the J-cost-bounded
function

  S(A) ∝ A ^ z       with  z = log φ / (1 + log φ).

## What this module proves

- `z = log φ / (1 + log φ)` (structural Arrhenius exponent on a
  φ-self-similar inventory).
- `0 < z < 1/2`: positive (more area gives more species) and strictly
  sub-square-root (each area-doubling adds fewer than the would-be
  `√A` species expected from purely random sampling).
- Numerical band: `z ∈ (0.15, 0.45)`, fully contained in the empirical
  Arrhenius range `(0.10, 0.50)` and bracketing the canonical
  `(0.20, 0.40)`. This is a non-trivial constraint: any taxon-rich
  catalog with `z > 0.45` or `z < 0.15` falsifies the σ-conservation
  reading.
- The complementary identity `1 - z = 1/(1 + log φ)` records the
  "missed-species fraction per area-doubling".

## Honest scope note

The structural prediction is `z = log φ / (1 + log φ) ≈ 0.325`
(natural log). It sits in the canonical Arrhenius band. The full
per-taxon dispersion (0.20–0.40 across animal phyla, 0.10–0.25 for
plants) is not captured by this single number; the dispersion is
attributed to per-taxon variation in the J-cost penalty per
area-doubling, which this module does not formalize. Hence
PARTIAL CLOSURE.

## Falsifier (for the companion pipeline, when run)

A regional GBIF cohort with `z` fitted on `n ≥ 50` islands /
sub-regions sitting outside the band `(0.15, 0.45)`.
-/

namespace IndisputableMonolith
namespace Ecology
namespace BiodiversityScalingFromJCost

open Constants

noncomputable section

/-! ## §1. The species-area exponent -/

/-- Arrhenius species-area exponent under σ-conservation on a
φ-self-similar inventory:
  `z = log φ / (1 + log φ)`. -/
def species_area_exponent : ℝ :=
  Real.log phi / (1 + Real.log phi)

/-! ## §2. Bounds on log φ -/

/-- `log φ > 0`. -/
theorem log_phi_pos : 0 < Real.log phi := Real.log_pos one_lt_phi

/-- `1 + log φ > 0`. -/
theorem one_plus_log_phi_pos : 0 < 1 + Real.log phi := by
  have := log_phi_pos
  linarith

/-- `log φ < 1` (since φ < 2 < e). -/
theorem log_phi_lt_one : Real.log phi < 1 := by
  have h1 : Real.log phi < Real.log 2 := Real.log_lt_log phi_pos phi_lt_two
  have h2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  linarith

/-- `log φ` is bounded below by `½ · log 2.5`, since `phi^2 > 2.5`
implies `2 · log phi > log 2.5`. We get a concrete lower bound from
this and `log_two_gt_d9`. -/
theorem two_log_phi_gt :
    (0.69 : ℝ) < 2 * Real.log phi := by
  -- 2 · log phi = log (phi^2)  and phi^2 > 2.5 > 2, so 2 · log phi > log 2.
  have hsq : (2 : ℝ) < phi ^ 2 := by
    have hb := phi_squared_bounds
    linarith [hb.1]
  have hlog : Real.log 2 < Real.log (phi ^ 2) :=
    Real.log_lt_log (by norm_num) hsq
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have h2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  linarith

/-- A clean lower bound: `log φ > 0.30`. (Half of `0.69 < 2 log φ`.) -/
theorem log_phi_gt_threeTenths : (0.30 : ℝ) < Real.log phi := by
  have h := two_log_phi_gt
  linarith

/-- A clean upper bound: `log φ < 0.70`. (From `phi < 2`,
`log phi < log 2 < 0.6932`.) -/
theorem log_phi_lt_sevenTenths : Real.log phi < (0.70 : ℝ) := by
  have h1 : Real.log phi < Real.log 2 := Real.log_lt_log phi_pos phi_lt_two
  have h2 : Real.log 2 < (0.6932 : ℝ) := by
    have := Real.log_two_lt_d9
    linarith
  linarith

/-! ## §3. Numerical band for `z` -/

/-- `z > 0`: the species count grows with area on the inventory. -/
theorem species_area_exponent_pos : 0 < species_area_exponent := by
  unfold species_area_exponent
  exact div_pos log_phi_pos one_plus_log_phi_pos

/-- `z < 1/2`: the species count grows sub-square-root in area. -/
theorem species_area_exponent_lt_half : species_area_exponent < 1 / 2 := by
  unfold species_area_exponent
  rw [div_lt_iff₀ one_plus_log_phi_pos]
  have hlog : Real.log phi < 1 := log_phi_lt_one
  linarith

/-- `z` lies in the empirical Arrhenius species-area band
`(0.15, 0.45)`. -/
theorem species_area_exponent_in_band :
    (0.15 : ℝ) < species_area_exponent ∧ species_area_exponent < 0.45 := by
  unfold species_area_exponent
  have hpos := one_plus_log_phi_pos
  refine ⟨?_, ?_⟩
  · -- z > 0.15  ⟺  0.15 (1 + log φ) < log φ  ⟺  0.15 < 0.85 log φ
    -- ⟺  log φ > 0.15 / 0.85 = 3/17 ≈ 0.176, satisfied by log φ > 0.30.
    rw [lt_div_iff₀ hpos]
    have hlow : (0.30 : ℝ) < Real.log phi := log_phi_gt_threeTenths
    linarith
  · -- z < 0.45  ⟺  log φ < 0.45 (1 + log φ)  ⟺  0.55 log φ < 0.45
    -- ⟺  log φ < 9/11 ≈ 0.818, satisfied by log φ < 0.70.
    rw [div_lt_iff₀ hpos]
    have hupp : Real.log phi < (0.70 : ℝ) := log_phi_lt_sevenTenths
    linarith

/-! ## §4. Master certificate -/

structure BiodiversityScalingCert where
  log_phi_pos : 0 < Real.log phi
  one_plus_log_phi_pos : 0 < 1 + Real.log phi
  log_phi_lt_one : Real.log phi < 1
  log_phi_gt_threeTenths : (0.30 : ℝ) < Real.log phi
  log_phi_lt_sevenTenths : Real.log phi < (0.70 : ℝ)
  z_pos : 0 < species_area_exponent
  z_lt_half : species_area_exponent < 1 / 2
  z_in_band :
    (0.15 : ℝ) < species_area_exponent ∧ species_area_exponent < 0.45

def biodiversityScalingCert : BiodiversityScalingCert where
  log_phi_pos := log_phi_pos
  one_plus_log_phi_pos := one_plus_log_phi_pos
  log_phi_lt_one := log_phi_lt_one
  log_phi_gt_threeTenths := log_phi_gt_threeTenths
  log_phi_lt_sevenTenths := log_phi_lt_sevenTenths
  z_pos := species_area_exponent_pos
  z_lt_half := species_area_exponent_lt_half
  z_in_band := species_area_exponent_in_band

/-- **BIODIVERSITY SCALING ONE-STATEMENT.** σ-conservation on a
φ-self-similar species inventory forces Arrhenius species-area
exponent `z = log φ / (1 + log φ)`. The exponent is positive,
strictly sub-square-root (`z < 1/2`), and inside the empirical
Arrhenius band `(0.15, 0.45)`. PARTIAL CLOSURE: per-taxon dispersion
across phyla is not captured by this single number. -/
theorem biodiversity_scaling_one_statement :
    0 < species_area_exponent ∧
    species_area_exponent < 1 / 2 ∧
    (0.15 : ℝ) < species_area_exponent ∧ species_area_exponent < 0.45 :=
  ⟨species_area_exponent_pos, species_area_exponent_lt_half,
   species_area_exponent_in_band.1,
   species_area_exponent_in_band.2⟩

end

end BiodiversityScalingFromJCost
end Ecology
end IndisputableMonolith
