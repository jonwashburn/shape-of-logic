import Mathlib

/-!
# Bridge Data Core (certified-surface friendly)

This module contains only the **core** bridge-anchor data structure and the
dimensionless identity for the recognition length
\(\lambda_{\mathrm{rec}} = \sqrt{\hbar G / (\pi c^3)}\).

It intentionally avoids importing `IndisputableMonolith.Core` (and other large
subsystems) so the certified import-closure stays small.

The extended measurement/protocol helpers live in `IndisputableMonolith/Bridge/Data.lean`
and are intentionally kept out of the certified import-closure.
-/

namespace IndisputableMonolith.BridgeData

/-- External bridge anchors provided as data (no axioms): G, ħ, c, plus display anchors. -/
structure BridgeData where
  G     : ℝ
  hbar  : ℝ
  c     : ℝ
  tau0  : ℝ
  ell0  : ℝ

/-- Minimal physical assumptions on bridge anchors reused by analytical lemmas. -/
structure Physical (B : BridgeData) : Prop where
  c_pos    : 0 < B.c
  hbar_pos : 0 < B.hbar
  G_pos    : 0 < B.G

/-- Recognition length from anchors: λ_rec = √(ħ G / c^3). -/
noncomputable def lambda_rec (B : BridgeData) : ℝ :=
  Real.sqrt (B.hbar * B.G / (Real.pi * (B.c ^ 3)))

/-- Dimensionless identity for λ_rec (under mild physical positivity assumptions):
    (c^3 · λ_rec^2) / (ħ G) = 1/π. -/
lemma lambda_rec_dimensionless_id (B : BridgeData)
  (hc : 0 < B.c) (hh : 0 < B.hbar) (hG : 0 < B.G) :
  (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G) = 1 / Real.pi := by
  -- Expand λ_rec and simplify using sqrt and algebra
  unfold lambda_rec
  have h_pos : 0 < B.hbar * B.G / (Real.pi * B.c ^ 3) := by
    apply div_pos (mul_pos hh hG)
    exact mul_pos Real.pi_pos (pow_pos hc 3)
  -- Use (sqrt x)^2 = x for x ≥ 0
  have h_nonneg : 0 ≤ B.hbar * B.G / (Real.pi * B.c ^ 3) := le_of_lt h_pos
  have hsq : (Real.sqrt (B.hbar * B.G / (Real.pi * B.c ^ 3))) ^ 2 =
    B.hbar * B.G / (Real.pi * B.c ^ 3) := by
    simpa using Real.sq_sqrt h_nonneg
  -- Now simplify the target expression
  calc
    (B.c ^ 3) * (Real.sqrt (B.hbar * B.G / (Real.pi * B.c ^ 3))) ^ 2 / (B.hbar * B.G)
        = (B.c ^ 3) * (B.hbar * B.G / (Real.pi * B.c ^ 3)) / (B.hbar * B.G) := by
          simp [hsq]
    _ = ((B.c ^ 3) * (B.hbar * B.G)) / ((Real.pi * B.c ^ 3) * (B.hbar * B.G)) := by
          field_simp
    _ = 1 / Real.pi := by
          field_simp [mul_comm, mul_left_comm, mul_assoc, pow_succ, pow_mul]

/-- Dimensionless identity packaged with a physical-assumptions helper. -/
lemma lambda_rec_dimensionless_id_physical (B : BridgeData) (H : Physical B) :
  (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G) = 1 / Real.pi :=
  lambda_rec_dimensionless_id B H.c_pos H.hbar_pos H.G_pos

/-- Positivity of λ_rec under physical assumptions. -/
lemma lambda_rec_pos (B : BridgeData) (H : Physical B) : 0 < lambda_rec B := by
  -- λ_rec = √(ħ G / (π c³)) > 0 since all components positive
  unfold lambda_rec
  apply Real.sqrt_pos.mpr
  apply div_pos
  · exact mul_pos H.hbar_pos H.G_pos
  · exact mul_pos Real.pi_pos (pow_pos H.c_pos 3)

end IndisputableMonolith.BridgeData
