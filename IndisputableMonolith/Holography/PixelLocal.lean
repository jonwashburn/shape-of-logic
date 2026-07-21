import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card

/-!
# PixelLocal: the forced recognition-sector count on the D=3, 8=2³ lattice

The RS holography panel (2026-06-29/30) split the recognition-pixel area
`a_pix = 4 · H · ℓ_P²` into three quantities that must be derived **separately**:
the integer `4`, the per-event entropy `H = (φ+2) log φ`, and the area scale `ℓ_P²`.
`H` is already a theorem (`RecognitionEventCapacity.forcedEntropy`); `ℓ_P²` is blocked
by a scale-invariance no-go (`Consciousness.PixelScaleNoGo`). This module attacks the
remaining quantity, the integer, on the **actually forced discrete substrate** rather
than by importing continuum isotropy or any Bekenstein-Hawking input.

## The greenlit construction

The forced 8-tick cell in D=3 is the cube `2³`: 8 vertices, 6 faces. A **boundary
recognition pixel** is one cube face, a square plaquette with 4 vertices. Put one
recognition bit on each vertex (`Fin 16` = the 4 low bits). The forced substrate
contributes exactly two structures, and nothing else:

* **Ledger closure.** A closed recognition loop posts a balanced (zero-sum) ledger
  around the plaquette, so the 4 vertex bits XOR to 0 (even parity). This is the only
  admissibility condition, and it comes from the recognition ledger, not from geometry.
* **The face stabilizer.** Two boundary configurations that differ only by a symmetry
  of the square are the same physical sector, so we quotient by the square's symmetry
  group `D₄` (4 rotations + 4 reflections, the 8 elements that fix the plaquette).

`card(AdmissibleBoundarySectors / FaceStabilizer)` is then a finite, `decide`-able
number. **It comes out to exactly 4** — the four orbits are the empty loop `0000`, the
two adjacent-edge loops modulo rotation, the two diagonal loops, and the full loop
`1111`. That is `2^(D-1) = 2² = 4` realized concretely on the forced lattice.

## What this proves, and what it does not (honest scope)

THEOREM (axiom-clean): the count is 4. No `H`, no `ℓ_P`, no area quantity appears in
any definition here; the result is pure plaquette combinatorics on the forced 8 = 2³
substrate. This is the substrate-native realization of the geometric coefficient the
paper writes as `4`.

OPEN (deliberately not proved here, two distinct gaps the panel flagged):
1. **Count → area-coefficient link.** Many cube invariants equal 4 in D=3 (edges per
   face, transverse DOF, `χ·2`). That this *sector* count is the *area* coefficient in
   `a_pix = c · H · ℓ_P²` is a separate argument, not the enumeration.
2. **The length scale `ℓ_P²`.** Provably unreachable from the current dimensionless
   theorem data (`Consciousness.PixelScaleNoGo.area_not_fixed_by_dimensionless`); a new
   forced J-cost / action normalization carrying a length is required first.

So this module supplies the forced integer and nothing more. It does not let anyone
claim a "derived Bekenstein 1/4"; it closes the integer leg of the three-leg split and
points the autonomous loop at the two remaining legs.
-/

namespace IndisputableMonolith
namespace Holography
namespace PixelLocal

/-- A boundary plaquette configuration: one recognition bit on each of the 4 vertices
of a cube face, packed into the 4 low bits of a `Fin 16`. -/
abbrev FaceCfg := Fin 16

/-- Vertex bit `i ∈ Fin 4` of a face configuration. -/
def vbit (c : FaceCfg) (i : Fin 4) : Bool := Nat.testBit c.val i.val

/-- **Ledger closure** on the plaquette: the 4 vertex bits XOR to 0 (even parity).
A closed recognition loop posts a balanced (zero-sum) ledger around the face. -/
def closed (c : FaceCfg) : Bool :=
  ! (vbit c 0 ^^ vbit c 1 ^^ vbit c 2 ^^ vbit c 3)

/-- **The face stabilizer `D₄`**: the 8 symmetries of the square (4 rotations +
4 reflections), as permutations of the 4 vertices arranged in cyclic order 0-1-2-3. -/
def faceStabilizer : List (Fin 4 → Fin 4) :=
  [ ![0, 1, 2, 3], ![1, 2, 3, 0], ![2, 3, 0, 1], ![3, 0, 1, 2],
    ![0, 3, 2, 1], ![2, 1, 0, 3], ![1, 0, 3, 2], ![3, 2, 1, 0] ]

/-- Act on a face configuration by a vertex permutation, reassembling the 4 bits. -/
def actBy (σ : Fin 4 → Fin 4) (c : FaceCfg) : FaceCfg :=
  ⟨ ((if vbit c (σ 0) then 1 else 0) + (if vbit c (σ 1) then 2 else 0)
      + (if vbit c (σ 2) then 4 else 0) + (if vbit c (σ 3) then 8 else 0)) % 16,
    Nat.mod_lt _ (by decide) ⟩

/-- A configuration is the canonical representative of its sector iff it is the
numerically smallest configuration in its `D₄`-orbit. -/
def isSectorRep (c : FaceCfg) : Bool :=
  faceStabilizer.all (fun σ => decide (c ≤ actBy σ c))

/-- **The admissible boundary sectors of one cube face**: ledger-closed plaquette
configurations modulo the face stabilizer `D₄`, counted by canonical representative. -/
def admissibleSectors : Finset FaceCfg :=
  Finset.univ.filter (fun c => closed c = true ∧ isSectorRep c = true)

/-- **THEOREM (axiom-clean, by `decide`). The D=3 forced lattice yields exactly 4
recognition sectors per boundary face.**

`card(AdmissibleBoundarySectors / FaceStabilizer) = 4 = 2^(D-1)`. No `H`, no `ℓ_P`,
no area input enters any definition; the count is pure ledger-closed plaquette
combinatorics on the forced 8 = 2³ substrate. -/
theorem recognition_sector_count : admissibleSectors.card = 4 := by decide

/-- The four sectors are exactly the orbit minima `{0000, 0011, 0101, 1111}`
(empty loop, an adjacent-edge loop, a diagonal loop, the full loop). -/
theorem admissibleSectors_eq :
    admissibleSectors = ({0, 3, 5, 15} : Finset FaceCfg) := by decide

/-- The geometric exponent realized: `2^(D-1)` at `D = 3` is the sector count. -/
theorem sector_count_eq_two_pow : admissibleSectors.card = 2 ^ (3 - 1) := by decide

/-- The forced 8-tick cell in D=3 is the cube: `2³ = 8` vertices. -/
theorem cube_vertices : Fintype.card (Fin 3 → Bool) = 8 := by decide

/-- The cube has 6 faces (an axis together with a side). -/
theorem cube_faces : Fintype.card (Fin 3 × Bool) = 6 := by decide

end PixelLocal
end Holography
end IndisputableMonolith
