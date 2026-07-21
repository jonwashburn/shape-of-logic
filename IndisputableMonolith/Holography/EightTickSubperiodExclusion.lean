import Mathlib
import IndisputableMonolith.Holography.PixelLocal

/-!
# EightTickSubperiodExclusion: no proper divisor of 8 realizes the admissible census

LEG-B of the Bekenstein-Hawking coefficient program (panel directive 2026-07-02,
`plans/RS_Bekenstein_Quarter_Master_Plan_20260701.html`) needs the DISCRETE half of
the deficit-free-period argument: the Euclidean period of the analytically continued
recognition cycle is the FULL 8-tick turn (hence one full `2π`), not a proper
sub-multiple (a conical deficit). The continuum half is the KMS window lemma
(`legb_kms_window_unique`, loop-owned). This module supplies the discrete half as a
kernel-`decide` enumeration on the forced substrate.

## The statement

Work on the boundary plaquette configurations `FaceCfg = Fin 16` of
`Holography.PixelLocal` (one recognition bit per vertex of a cube face). A
recognition walk advances by single-bit flips (one vertex posting per tick, the
Gray-code discipline of the 8-tick cube traversal, `Patterns.period_exactly_8`).
A walk of length `d` is *closed* when it returns to its starting configuration,
and *census-complete* when it visits at least one representative of each of the
four admissible ledger-closed sectors of `PixelLocal.admissibleSectors_eq`
(the `D₄`-orbits `{0}`, `{3,6,12,9}`, `{5,10}`, `{15}`).

**THEOREM (axiom-clean, by `decide`).** For every proper divisor `d ∈ {1, 2, 4}`
of 8, NO closed length-`d` flip walk is census-complete; and a closed length-8
flip walk that is census-complete EXISTS (witness: flips `[0,1,2,3,0,2,1,3]` from
`0000`, visiting `0 → 1 → 3 → 7 → 15 → 14 → 10 → 8 → 0`, which meets all four
orbits at `0, 3, 10, 15`).

The obstruction for `d ∈ {1,2}` is cardinality (a closed 1- or 2-walk visits at
most 2 distinct configurations, but 4 orbits must be met); for `d = 4` it is
parity (bit-flip steps alternate the parity of the popcount, so a closed 4-walk
visits at most 2 distinct even-parity configurations, again short of the 4 orbits;
the full enumeration over all 16 × 4⁴ = 4096 walks is what `decide` checks).

## What this proves for LEG-B, and what it does not (honest scope)

THEOREM: the minimal closed recognition walk that exhibits the complete admissible
sector census on the forced D=3 substrate has length exactly 8. A `d`-shift-invariant
counting with `d | 8`, `d < 8` cannot see all four sectors, so identifying ticks
modulo a proper divisor of 8 (the discrete analog of a conical deficit `2π/n`)
destroys the admissible census. Combined with `legb_eight_tick_circle_period`
(one full 8-tick cycle = one full `2π` turn of the continued clock), this forces
the census-preserving Euclidean period to be the FULL `2π/κ`, discretely.

OPEN (not proved here): that the physical Euclidean continuation must PRESERVE the
census (the finite-J-cost / regularity condition at the horizon fixed point). That
is the B2 physics core, still owned by the derive captain. This module removes the
"which sub-period?" freedom once census preservation is granted; it does not grant it.
-/

namespace IndisputableMonolith
namespace Holography
namespace EightTickSubperiodExclusion

open PixelLocal

/-- One recognition tick on a boundary plaquette: flip the bit of vertex `i`
(one vertex posting per tick, the Gray-code step of the 8-tick traversal). -/
def flip (c : FaceCfg) (i : Fin 4) : FaceCfg :=
  ⟨(c.val ^^^ (1 <<< i.val)) % 16, Nat.mod_lt _ (by decide)⟩

/-- The endpoint of a flip walk from `s` through the tick sequence `fs`. -/
def walkEnd : FaceCfg → List (Fin 4) → FaceCfg
  | s, [] => s
  | s, i :: fs => walkEnd (flip s i) fs

/-- Every configuration a flip walk visits (including the start). -/
def walkVisits : FaceCfg → List (Fin 4) → List FaceCfg
  | s, [] => [s]
  | s, i :: fs => s :: walkVisits (flip s i) fs

/-- The walk meets the given `D₄`-orbit (listed by its member values). -/
def hits (s : FaceCfg) (fs : List (Fin 4)) (orbit : List Nat) : Bool :=
  (walkVisits s fs).any fun c => orbit.contains c.val

/-- Census completeness: the walk meets all four admissible ledger-closed sectors
of `PixelLocal.admissibleSectors_eq` (as full `D₄`-orbits: the empty loop `{0}`,
the adjacent-edge loops `{3,6,12,9}`, the diagonal loops `{5,10}`, and the full
loop `{15}`). -/
def censusComplete (s : FaceCfg) (fs : List (Fin 4)) : Bool :=
  hits s fs [0] && hits s fs [3, 6, 12, 9] && hits s fs [5, 10] && hits s fs [15]

/-- **d = 1 excluded**: no closed 1-tick walk is census-complete (cardinality:
it visits at most 2 configurations; 4 orbits are required). -/
theorem no_subperiod_one :
    ∀ (s : FaceCfg) (fs : Fin 1 → Fin 4),
      walkEnd s (List.ofFn fs) = s → censusComplete s (List.ofFn fs) = false := by
  decide

/-- **d = 2 excluded**: no closed 2-tick walk is census-complete (cardinality). -/
theorem no_subperiod_two :
    ∀ (s : FaceCfg) (fs : Fin 2 → Fin 4),
      walkEnd s (List.ofFn fs) = s → censusComplete s (List.ofFn fs) = false := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- **d = 4 excluded**: no closed 4-tick walk is census-complete. The mechanism is
parity: single-bit flips alternate popcount parity, so a closed 4-walk sees at most
2 distinct even-parity configurations, short of the 4 required orbits. The proof is
the full kernel enumeration of all 16 × 4⁴ = 4096 walks. -/
theorem no_subperiod_four :
    ∀ (s : FaceCfg) (fs : Fin 4 → Fin 4),
      walkEnd s (List.ofFn fs) = s → censusComplete s (List.ofFn fs) = false := by
  decide

/-- **d = 8 realizes the census**: a closed 8-tick flip walk exhibiting all four
admissible sectors exists. Witness: from `0000`, flip vertices `0,1,2,3,0,2,1,3`,
visiting `0 → 1 → 3 → 7 → 15 → 14 → 10 → 8 → 0` (orbits met at `0, 3, 15, 10`). -/
theorem eight_tick_census_witness :
    ∃ (s : FaceCfg) (fs : Fin 8 → Fin 4),
      walkEnd s (List.ofFn fs) = s ∧ censusComplete s (List.ofFn fs) = true := by
  exact ⟨0, ![0, 1, 2, 3, 0, 2, 1, 3], by decide, by decide⟩

/-- **The subperiod-exclusion capstone**: among the divisors of 8, the census-complete
closed walk lengths begin exactly at 8. Every proper divisor fails; 8 succeeds. This
is the discrete deficit-free-period statement: identifying the recognition cycle
modulo a proper divisor of 8 (the discrete conical deficit `2π/n`) destroys the
admissible sector census, so the census-preserving period is the full 8-tick turn. -/
theorem minimal_census_period_eight :
    (∀ (s : FaceCfg) (fs : Fin 1 → Fin 4),
        walkEnd s (List.ofFn fs) = s → censusComplete s (List.ofFn fs) = false) ∧
    (∀ (s : FaceCfg) (fs : Fin 2 → Fin 4),
        walkEnd s (List.ofFn fs) = s → censusComplete s (List.ofFn fs) = false) ∧
    (∀ (s : FaceCfg) (fs : Fin 4 → Fin 4),
        walkEnd s (List.ofFn fs) = s → censusComplete s (List.ofFn fs) = false) ∧
    (∃ (s : FaceCfg) (fs : Fin 8 → Fin 4),
        walkEnd s (List.ofFn fs) = s ∧ censusComplete s (List.ofFn fs) = true) :=
  ⟨no_subperiod_one, no_subperiod_two, no_subperiod_four, eight_tick_census_witness⟩

end EightTickSubperiodExclusion
end Holography
end IndisputableMonolith
