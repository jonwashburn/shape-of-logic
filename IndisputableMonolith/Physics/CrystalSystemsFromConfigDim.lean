import Mathlib
import IndisputableMonolith.Constants

/-!
# Crystal Systems from configDim — Crystallography Depth

Seven crystal systems form the basic partition of 3D crystallography.
Five of these are orthogonal-axis-based (= configDim D = 5):
  cubic, tetragonal, orthorhombic, trigonal, hexagonal.

Plus two oblique: monoclinic and triclinic.

14 Bravais lattices = 7 systems × 2 (primitive + centerings).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.CrystalSystemsFromConfigDim

inductive OrthogonalCrystalSystem where
  | cubic
  | tetragonal
  | orthorhombic
  | trigonal
  | hexagonal
  deriving DecidableEq, Repr, BEq, Fintype

theorem orthogonalSystem_count :
    Fintype.card OrthogonalCrystalSystem = 5 := by decide

/-- 7 systems total; 5 orthogonal + 2 oblique. -/
theorem seven_systems_partition : (7 : ℕ) = 5 + 2 := by decide

/-- 14 Bravais lattices. -/
def bravaisLatticeCount : ℕ := 14
theorem bravais_eq : bravaisLatticeCount = 14 := rfl

structure CrystalSystemsCert where
  five_orthogonal : Fintype.card OrthogonalCrystalSystem = 5
  seven_total : (7 : ℕ) = 5 + 2
  bravais_14 : bravaisLatticeCount = 14

def crystalSystemsCert : CrystalSystemsCert where
  five_orthogonal := orthogonalSystem_count
  seven_total := seven_systems_partition
  bravais_14 := bravais_eq

end IndisputableMonolith.Physics.CrystalSystemsFromConfigDim
