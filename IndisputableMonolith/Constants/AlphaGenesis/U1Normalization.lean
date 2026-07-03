import Mathlib
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Constants.AlphaDerivation
import IndisputableMonolith.Numerics.Interval.AlphaBounds

/-!
# Alpha Genesis M11: U(1) coupling-normalization verdict (quarantine)

This module records the result of the make-or-break test: can the α seed
`4π·11` be promoted from an IDENTIFICATION ("channel-budget bridge") to a
THEOREM about a U(1) coupling normalization on the cube `Q₃`?

## The test

`Foundation.GaugeFromCube` derives the U(1) *group* (the parity quotient
`ℤ/2` of `Aut(Q₃) = B₃`), but never touches the α pipeline. A genuine
coupling-normalization theorem would read the inverse coupling off a
gauge-invariant U(1) Maxwell action on the cube. The QED normalization is
`α = e²/(4π)`, i.e. `α⁻¹ = (4π)·(stiffness)/e²`; the seed reads
`stiffness = 11` (passive edges) and `e² = 1`.

## The result (negative, sharp)

A gauge-invariant U(1) action on the cube graph counts **independent plaquette
field strengths**, i.e. the cycle rank of the 1-skeleton:
`b₁ = E − V + 1 = 12 − 8 + 1 = 5` (equivalently `6` faces `− 1` Bianchi/closure
relation). Gauge fixing removes `V − 1 = 7` link redundancies (one U(1) phase
per vertex, minus the global phase), leaving `12 − 7 = 5` physical link modes,
the same `5`.

The seed's `11 = E − 1` removes only the single *active* edge, NOT the `7` gauge
redundancies. So `11` is a **ledger recognition-channel count, not a
gauge-invariant photon stiffness** (which is `5`). The two disagree:
`11 ≠ 5` (`seed_channel_count_ne_gauge_dof`).

Consequently a genuine gauge-invariant Maxwell seed on the cube is
`4π·5 = 20π ≈ 62.8`, which is excluded from being `α⁻¹` by a wide margin
(`gauge_invariant_seed_excluded`: `< 63 < 137.030 < alphaInv`).

## Verdict

The channel-budget reading of `α⁻¹ = 4π·11` does NOT promote to a U(1)
coupling-normalization theorem. The `11` is a ledger channel count, not the
gauge-invariant photon degree-of-freedom count (`5`). The seed remains a
striking, cross-consistent *ledger* number (the same `11` appears in
`Ω_Λ = 11/16`, CKM, `η_B = φ⁻⁴⁴`, and `44 = 4·11`), but its identity with the
electromagnetic coupling is an identification at the ledger level, not a derived
gauge normalization. The honest formal object is the CONDITIONAL
`SeedNormalizationReading` below, whose third premise is exactly the
ledger-vs-gauge mismatch.

STATUS: THEOREM (the combinatorial verdict); QUARANTINE (imports CODATA band
only through `alphaInv` numeric bounds).
-/

namespace IndisputableMonolith
namespace Constants
namespace AlphaGenesis
namespace U1Normalization

open Constants.AlphaDerivation

/-! ## Gauge-invariant photon degree-of-freedom count on the cube -/

/-- Independent plaquette field strengths of a U(1) gauge field on the cube
graph = the cycle rank (first Betti number) of the 1-skeleton, `b₁ = E − V + 1`.
For `Q₃`: `12 − 8 + 1 = 5`. -/
def cube_cycle_rank : ℕ := cube_edges D - cube_vertices D + 1

theorem cube_cycle_rank_eq_5 : cube_cycle_rank = 5 := by
  unfold cube_cycle_rank; native_decide

/-- The same count via faces minus the single global Bianchi/closure relation
(`∏_faces F = 1`): `6 − 1 = 5`. -/
theorem gauge_dof_via_faces : cube_faces D - 1 = cube_cycle_rank := by
  rw [cube_cycle_rank_eq_5]; native_decide

/-- The U(1) gauge redundancy on the 12 link variables: one phase per vertex,
minus the global phase that acts trivially, `V − 1 = 7`. -/
def gauge_redundancy : ℕ := cube_vertices D - 1

theorem gauge_redundancy_eq_7 : gauge_redundancy = 7 := by
  unfold gauge_redundancy; native_decide

/-- Physical link modes = link variables − gauge redundancy = `E − (V − 1)`,
which equals the cycle rank: `12 − 7 = 5`. The two routes to the
gauge-invariant photon count agree. -/
theorem physical_link_dof_eq_cycle_rank :
    cube_edges D - gauge_redundancy = cube_cycle_rank := by
  rw [gauge_redundancy_eq_7, cube_cycle_rank_eq_5]; native_decide

/-! ## The seed channel count is the ledger count, not the gauge count -/

/-- The α seed channel count is the passive-edge count `E − 1 = 11`. This removes
only the single active edge, not the `V − 1 = 7` gauge redundancies. -/
theorem seed_channel_count : passive_field_edges D = 11 := passive_edges_at_D3

/-- **VERDICT (combinatorial core).** The seed channel count `11` is NOT the
gauge-invariant photon degree-of-freedom count `5`. A gauge-invariant Maxwell
normalization on the cube would use the cycle rank, not the passive-edge count. -/
theorem seed_channel_count_ne_gauge_dof :
    passive_field_edges D ≠ cube_cycle_rank := by
  rw [seed_channel_count, cube_cycle_rank_eq_5]; norm_num

/-! ## The gauge-invariant seed cannot be `α⁻¹` -/

/-- The gauge-invariant Maxwell seed on the cube: `(4π) × (cycle rank)`. -/
noncomputable def gauge_invariant_seed : ℝ := 4 * Real.pi * (cube_cycle_rank : ℝ)

theorem gauge_invariant_seed_eq_20pi : gauge_invariant_seed = 20 * Real.pi := by
  unfold gauge_invariant_seed
  rw [cube_cycle_rank_eq_5]
  push_cast
  ring

/-- The gauge-invariant seed `20π ≈ 62.8` is excluded from being `α⁻¹` by a wide
margin: `gauge_invariant_seed < 63 < 137.030 < alphaInv`. So the genuine
gauge-invariant U(1) normalization on the cube cannot be the source of the
electromagnetic coupling; the seed's `137`-scale value requires the ledger
channel count `11`, not the gauge count `5`. -/
theorem gauge_invariant_seed_excluded :
    gauge_invariant_seed < Constants.alphaInv := by
  rw [gauge_invariant_seed_eq_20pi]
  have hpi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have h1 : (20 : ℝ) * Real.pi < 63 := by nlinarith [hpi]
  have h2 : (137.030 : ℝ) < Constants.alphaInv := Numerics.alphaInv_gt
  linarith

/-! ## The honest conditional reading -/

/-- A reading of the α seed `4π·11` as a U(1) coupling normalization. The seed
equals `(4π) × (stiffness)` with `e² = 1` ONLY under three inputs, the third of
which is precisely the ledger-vs-gauge mismatch: the stiffness used is the
passive-edge (ledger channel) count, which is NOT the gauge-invariant cycle
rank. So this is an identification, not a gauge-theory theorem. -/
structure SeedNormalizationReading : Prop where
  /-- (i) MODEL: Heaviside–Lorentz convention `α = e²/(4π)`. -/
  hl_convention : True
  /-- (ii) IDENTIFICATION: bare charge quantum `e² = 1` (J-cost Hessian `= 1`;
  the particle/antiparticle double-entry factor of `2` is not independently
  ruled out here). -/
  charge_unit_one : True
  /-- (iii) IDENTIFICATION (the load-bearing one): the photon stiffness is taken
  to be the passive-edge ledger channel count `11`, which is NOT the
  gauge-invariant cycle rank `5`. -/
  stiffness_is_ledger_not_gauge : passive_field_edges D ≠ cube_cycle_rank

/-- The honest reading is inhabited, and its load-bearing premise is the proved
ledger-vs-gauge mismatch. This certifies the reading as an identification (it
holds), not a derivation (the gauge count would give `5`, not `11`). -/
def seedNormalizationReading : SeedNormalizationReading where
  hl_convention := trivial
  charge_unit_one := trivial
  stiffness_is_ledger_not_gauge := seed_channel_count_ne_gauge_dof

/-- **U(1) normalization verdict certificate.** Bundles the make-or-break result:
the gauge-invariant photon count on the cube is `5` (two independent routes
agree), the seed uses the ledger channel count `11 ≠ 5`, and the genuine
gauge-invariant seed `20π` is excluded from `α⁻¹`. The channel-budget reading is
therefore an identification at the ledger level, not a derived U(1) coupling
normalization. -/
structure U1NormalizationVerdict : Prop where
  gauge_dof_is_5 : cube_cycle_rank = 5
  gauge_dof_two_routes_agree : cube_edges D - gauge_redundancy = cube_cycle_rank
  seed_uses_ledger_count : passive_field_edges D = 11
  ledger_ne_gauge : passive_field_edges D ≠ cube_cycle_rank
  gauge_seed_excluded : gauge_invariant_seed < Constants.alphaInv

def u1NormalizationVerdict : U1NormalizationVerdict where
  gauge_dof_is_5 := cube_cycle_rank_eq_5
  gauge_dof_two_routes_agree := physical_link_dof_eq_cycle_rank
  seed_uses_ledger_count := seed_channel_count
  ledger_ne_gauge := seed_channel_count_ne_gauge_dof
  gauge_seed_excluded := gauge_invariant_seed_excluded

end U1Normalization
end AlphaGenesis
end Constants
end IndisputableMonolith
