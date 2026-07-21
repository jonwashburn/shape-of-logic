import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import IndisputableMonolith.Holography.PixelLocal

/-!
# PixelGluedPlaquette (LB1): the recognition-sector count is NOT area-additive

This module settles the panel's first "live bet" (LB1) on GAP 1 (the count→area
ansatz). The single boundary pixel (one cube face) carries exactly `4` ledger-closed
sectors modulo its `D₄` stabilizer (`PixelLocal.recognition_sector_count`). If that
integer were an AREA DENSITY — i.e. if the sector count were the multiplicative
coefficient on an extensive area — then a region of TWICE the area should carry twice
the count. We test this directly by gluing two faces along a shared edge (a 2×1 domino,
twice the area of one face) and enumerating its sectors with the identical machinery.

## The construction (parallel to `PixelLocal`)

A 2×1 domino has 6 vertices in a 2-row × 3-column grid (top `0 1 2`, bottom `3 4 5`),
packed into the 6 low bits of `Fin 64`. It is the union of two unit faces:

* left face, cyclic `0-1-4-3`;
* right face, cyclic `1-2-5-4` (sharing edge `1-4` with the left face).

**Ledger closure** requires BOTH unit faces to post a balanced loop (each face's 4
vertex bits XOR to 0). **The stabilizer** is the symmetry group of the 2×1 rectangle,
the Klein four-group `Z₂ × Z₂` (identity, horizontal mirror, vertical mirror, 180°
rotation) — *not* `D₄`, because the rectangle is not a square. Sectors are counted by
canonical (numerically smallest) orbit representative, exactly as in `PixelLocal`.

## The finding (machine-checked, axiom-clean)

`glued_sector_count`: the domino carries exactly **9** sectors, not `2 · 4 = 8`. The
count is **super-additive**: `9 = 2·4 + 1`, the `+1` being the boundary correction from
the shared edge. So the sector count does NOT scale as a clean area density; the
per-pixel integer `4` is not an area coefficient in the extensive sense.

This is evidence AGAINST the count→area ansatz (GAP 1), not for it. It does not refute
the framework — the integer `4` per face is still a theorem — but it shows that
identifying that integer as the multiplicative area coefficient `a_pix = 4·H·ℓ_P²` is a
genuine modeling step, not a consequence of the enumeration. Closing GAP 1 cannot route
through "the count IS the area"; the count is not extensive.

Axiom-clean (`propext, Classical.choice, Quot.sound`); every theorem is `by decide`.
-/

namespace IndisputableMonolith
namespace Holography
namespace PixelGluedPlaquette

/-- A glued 2×1 domino configuration: one recognition bit on each of the 6 vertices of a
2-row × 3-column grid (top `0 1 2`, bottom `3 4 5`), packed into the 6 low bits of a
`Fin 64`. -/
abbrev DominoCfg := Fin 64

/-- Vertex bit `i ∈ Fin 6` of a domino configuration. -/
def vbit (c : DominoCfg) (i : Fin 6) : Bool := Nat.testBit c.val i.val

/-- **Ledger closure** on the domino: BOTH unit faces post a balanced (zero-sum) ledger
loop. Left face `0-1-4-3` even parity AND right face `1-2-5-4` even parity. -/
def closed (c : DominoCfg) : Bool :=
  (! (vbit c 0 ^^ vbit c 1 ^^ vbit c 4 ^^ vbit c 3)) &&
  (! (vbit c 1 ^^ vbit c 2 ^^ vbit c 5 ^^ vbit c 4))

/-- **The domino stabilizer** = the Klein four-group of the 2×1 rectangle: identity,
horizontal mirror `(0 2)(3 5)`, vertical mirror `(0 3)(1 4)(2 5)`, 180° rotation
`(0 5)(1 4)(2 3)`, as permutations of the 6 vertices. -/
def dominoStabilizer : List (Fin 6 → Fin 6) :=
  [ ![0, 1, 2, 3, 4, 5], ![2, 1, 0, 5, 4, 3], ![3, 4, 5, 0, 1, 2], ![5, 4, 3, 2, 1, 0] ]

/-- Act on a domino configuration by a vertex permutation, reassembling the 6 bits. -/
def actBy (σ : Fin 6 → Fin 6) (c : DominoCfg) : DominoCfg :=
  ⟨ ((if vbit c (σ 0) then 1 else 0) + (if vbit c (σ 1) then 2 else 0)
      + (if vbit c (σ 2) then 4 else 0) + (if vbit c (σ 3) then 8 else 0)
      + (if vbit c (σ 4) then 16 else 0) + (if vbit c (σ 5) then 32 else 0)) % 64,
    Nat.mod_lt _ (by decide) ⟩

/-- A configuration is its sector's canonical representative iff it is the numerically
smallest configuration in its Klein-4 orbit. -/
def isSectorRep (c : DominoCfg) : Bool :=
  dominoStabilizer.all (fun σ => decide (c ≤ actBy σ c))

/-- **The admissible sectors of the glued 2×1 domino**: ledger-closed (both faces)
configurations modulo the rectangle stabilizer, counted by canonical representative. -/
def admissibleSectors : Finset DominoCfg :=
  Finset.univ.filter (fun c => closed c = true ∧ isSectorRep c = true)

/-- **THEOREM (axiom-clean, by `decide`). The glued 2×1 domino carries exactly 9
recognition sectors** — NOT `2 · 4 = 8`. -/
theorem glued_sector_count : admissibleSectors.card = 9 := by decide

/-- **The sector count is super-additive (the LB1 finding).** Two faces glued along an
edge give `9 = 2·4 + 1`, where `4` is the single-face count
(`PixelLocal.recognition_sector_count`) and the `+1` is the shared-edge correction. The
count is therefore NOT an extensive area density: the per-pixel integer `4` is not the
area coefficient in the additive sense. -/
theorem glued_super_additive :
    admissibleSectors.card = 2 * PixelLocal.admissibleSectors.card + 1 := by decide

/-- The explicit nine orbit minima of the domino. -/
theorem admissibleSectors_eq :
    admissibleSectors = ({0, 7, 9, 14, 18, 21, 27, 45, 63} : Finset DominoCfg) := by decide

end PixelGluedPlaquette
end Holography
end IndisputableMonolith
