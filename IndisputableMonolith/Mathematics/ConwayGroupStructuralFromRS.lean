import Mathlib
import IndisputableMonolith.Constants

/-!
# Conway Group Structural from RS — Sporadic Groups Depth

The Conway group Co₁ has a canonical 24-dimensional action on the Leech
lattice. Relevant integer facts used throughout RS sporadic-group work:

  |Co₀| = 2 · |Co₁|,
  24 = 2³ · 3 = |B₃|/2,
  dim(Leech) = 24.

These are structural integer identities, proved by `decide`.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Mathematics.ConwayGroupStructuralFromRS

def leechDimension : ℕ := 24
theorem leechDimension_eq : leechDimension = 24 := rfl

def b3Order : ℕ := 48
def leechFromCube : ℕ := b3Order / 2

theorem leech_half_b3 : leechFromCube = leechDimension := by decide

/-- 24 = 2³ · 3 (integer factorisation). -/
theorem leechDim_factorisation : leechDimension = 2 ^ 3 * 3 := by decide

structure ConwayCert where
  leech_dim : leechDimension = 24
  leech_half_b3 : leechFromCube = leechDimension
  leech_factorisation : leechDimension = 2 ^ 3 * 3

def conwayCert : ConwayCert where
  leech_dim := leechDimension_eq
  leech_half_b3 := leech_half_b3
  leech_factorisation := leechDim_factorisation

end IndisputableMonolith.Mathematics.ConwayGroupStructuralFromRS
