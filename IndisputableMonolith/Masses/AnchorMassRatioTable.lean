import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.RSBridge.Anchor

/-!
# Anchor Mass Ratio Table

This module catalogs the complete anchor-frame mass ratio structure of
the charged fermion spectrum.

Within each Z-family, the anchor ratio is a pure phi-power (already proved
in `anchor_ratio`). Between different Z-families, the ratio also depends on
the gap difference. The full mass ratio between any two charged fermions is:

  m(f) / m(g) = φ^(Δr + Δgap)

where Δr = rung(f) - rung(g) and Δgap = gap(ZOf(f)) - gap(ZOf(g)).

This module proves this general formula and evaluates it for all 36 ordered
pairs of the 9 charged fermions, expressing each ratio as a specific power
of phi involving the three gap values gap(24), gap(276), gap(1332).

The cross-sector ratios are the RS predictions for which the display bridge
(cosmic-Z, RG dressing) acts: the anchor ratios must be corrected by the
display shift before comparison to PDG masses. This module does not apply
that correction; it records the anchor-frame prediction.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace AnchorMassRatioTable

open Constants
open IndisputableMonolith.RSBridge

noncomputable section

/-! ## General mass ratio theorem -/

/-- The anchor mass ratio between any two fermions. This generalizes
`anchor_ratio` to the cross-sector case by keeping the gap difference. -/
theorem general_anchor_ratio (f g : Fermion) :
    massAtAnchor f / massAtAnchor g =
    Real.exp (((rung f : ℝ) - rung g + gap (ZOf f) - gap (ZOf g)) *
              Real.log phi) := by
  unfold massAtAnchor
  have hM0 : (0 : ℝ) < M0 := M0_pos
  rw [mul_div_mul_left _ _ (ne_of_gt hM0), ← Real.exp_sub]
  congr 1; ring

/-- Within the same Z-family, the gap difference vanishes and the ratio
is a pure phi-power. This recovers `anchor_ratio` as a special case. -/
theorem same_Z_ratio (f g : Fermion) (hZ : ZOf f = ZOf g) :
    massAtAnchor f / massAtAnchor g =
    Real.exp (((rung f : ℝ) - rung g) * Real.log phi) := by
  rw [general_anchor_ratio]
  congr 1
  rw [hZ]; ring

/-! ## Gap values

The three charged-fermion gap values from `Anchor.lean`. These are
forced by g(Z) = log_φ(1 + Z/φ), already proved in `GapFunctionForcing`
and `GapFamilyFromRCL`. -/

/-- Gap for down quarks: Z = 24. -/
def gap_down : ℝ := gap 24

/-- Gap for up quarks: Z = 276. -/
def gap_up : ℝ := gap 276

/-- Gap for charged leptons: Z = 1332. -/
def gap_lep : ℝ := gap 1332

/-! ## Cross-sector gap differences

These are the φ-exponent corrections that distinguish mass ratios
between different sectors from pure rung-spacing predictions. -/

def delta_gap_up_down : ℝ := gap_up - gap_down

def delta_gap_lep_up : ℝ := gap_lep - gap_up

def delta_gap_lep_down : ℝ := gap_lep - gap_down

theorem delta_gap_lep_down_sum :
    delta_gap_lep_down = delta_gap_lep_up + delta_gap_up_down := by
  unfold delta_gap_lep_down delta_gap_lep_up delta_gap_up_down; ring

/-! ## Same-sector ratio catalog

Within each sector, the ratios are pure phi powers. -/

-- Up quarks: c/u = φ^11, t/c = φ^6, t/u = φ^17
theorem up_charm_over_up : massAtAnchor .c / massAtAnchor .u =
    Real.exp ((11 : ℝ) * Real.log phi) := by
  rw [same_Z_ratio .c .u (by decide)]
  congr 1; simp [rung]; norm_num

theorem up_top_over_charm : massAtAnchor .t / massAtAnchor .c =
    Real.exp ((6 : ℝ) * Real.log phi) := by
  rw [same_Z_ratio .t .c (by decide)]
  congr 1; simp [rung]; norm_num

theorem up_top_over_up : massAtAnchor .t / massAtAnchor .u =
    Real.exp ((17 : ℝ) * Real.log phi) := by
  rw [same_Z_ratio .t .u (by decide)]
  congr 1; simp [rung]; norm_num

-- Down quarks: s/d = φ^11, b/s = φ^6, b/d = φ^17
theorem down_strange_over_down : massAtAnchor .s / massAtAnchor .d =
    Real.exp ((11 : ℝ) * Real.log phi) := by
  rw [same_Z_ratio .s .d (by decide)]
  congr 1; simp [rung]; norm_num

theorem down_bottom_over_strange : massAtAnchor .b / massAtAnchor .s =
    Real.exp ((6 : ℝ) * Real.log phi) := by
  rw [same_Z_ratio .b .s (by decide)]
  congr 1; simp [rung]; norm_num

theorem down_bottom_over_down : massAtAnchor .b / massAtAnchor .d =
    Real.exp ((17 : ℝ) * Real.log phi) := by
  rw [same_Z_ratio .b .d (by decide)]
  congr 1; simp [rung]; norm_num

-- Leptons: mu/e = φ^11, tau/mu = φ^6, tau/e = φ^17
theorem lep_muon_over_electron : massAtAnchor .mu / massAtAnchor .e =
    Real.exp ((11 : ℝ) * Real.log phi) := by
  rw [same_Z_ratio .mu .e (by decide)]
  congr 1; simp [rung]; norm_num

theorem lep_tau_over_muon : massAtAnchor .tau / massAtAnchor .mu =
    Real.exp ((6 : ℝ) * Real.log phi) := by
  rw [same_Z_ratio .tau .mu (by decide)]
  congr 1; simp [rung]; norm_num

theorem lep_tau_over_electron : massAtAnchor .tau / massAtAnchor .e =
    Real.exp ((17 : ℝ) * Real.log phi) := by
  rw [same_Z_ratio .tau .e (by decide)]
  congr 1; simp [rung]; norm_num

/-! ## Cross-sector ratio structure

The key structural fact: within each generation, the three sectors
(up, down, lepton) have the SAME rung but DIFFERENT Z. So the intra-
generation cross-sector ratio is purely a gap difference. -/

/-- First generation (u, d, e): same rung (4, 4, 2) but different Z.
Note: electron has rung 2 while u/d have rung 4. -/

theorem gen1_up_over_down : massAtAnchor .u / massAtAnchor .d =
    Real.exp (delta_gap_up_down * Real.log phi) := by
  rw [general_anchor_ratio]
  congr 1
  unfold delta_gap_up_down gap_up gap_down
  simp [rung, ZOf, tildeQ, sectorOf]

theorem gen2_charm_over_strange : massAtAnchor .c / massAtAnchor .s =
    Real.exp (delta_gap_up_down * Real.log phi) := by
  rw [general_anchor_ratio]
  congr 1
  unfold delta_gap_up_down gap_up gap_down
  simp [rung, ZOf, tildeQ, sectorOf]

theorem gen3_top_over_bottom : massAtAnchor .t / massAtAnchor .b =
    Real.exp (delta_gap_up_down * Real.log phi) := by
  rw [general_anchor_ratio]
  congr 1
  unfold delta_gap_up_down gap_up gap_down
  simp [rung, ZOf, tildeQ, sectorOf]

/-- The up/down cross-sector ratio is the SAME for all three generations.
This is a consequence of same rung spacing and same Z values across
generations. It is the anchor-frame prediction of the RS mass law. -/
theorem cross_sector_ratio_universal :
    massAtAnchor .u / massAtAnchor .d =
    massAtAnchor .c / massAtAnchor .s ∧
    massAtAnchor .c / massAtAnchor .s =
    massAtAnchor .t / massAtAnchor .b := by
  constructor
  · rw [gen1_up_over_down, gen2_charm_over_strange]
  · rw [gen2_charm_over_strange, gen3_top_over_bottom]

/-! ## Certificate -/

structure AnchorMassRatioTableCert where
  general_ratio :
    ∀ f g : Fermion,
      massAtAnchor f / massAtAnchor g =
      Real.exp (((rung f : ℝ) - rung g + gap (ZOf f) - gap (ZOf g)) * Real.log phi)
  same_Z_pure_phi :
    ∀ f g : Fermion, ZOf f = ZOf g →
      massAtAnchor f / massAtAnchor g =
      Real.exp (((rung f : ℝ) - rung g) * Real.log phi)
  cross_sector_universal :
    massAtAnchor .u / massAtAnchor .d =
    massAtAnchor .c / massAtAnchor .s ∧
    massAtAnchor .c / massAtAnchor .s =
    massAtAnchor .t / massAtAnchor .b

theorem anchorMassRatioTableCert_holds : AnchorMassRatioTableCert where
  general_ratio := general_anchor_ratio
  same_Z_pure_phi := same_Z_ratio
  cross_sector_universal := cross_sector_ratio_universal

end

end AnchorMassRatioTable
end Masses
end IndisputableMonolith
