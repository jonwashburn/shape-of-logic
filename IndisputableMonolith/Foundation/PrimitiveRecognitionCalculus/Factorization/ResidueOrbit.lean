/-
  PrimitiveRecognitionCalculus/Factorization/ResidueOrbit.lean

  δ-native residues modulo an orbit position, defined by the existing native
  remainder operation. Nat modular arithmetic appears only as a verifier
  display surface.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Factorization.ChartTransition

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-- The native residue of `a` modulo a nonzero orbit modulus `N`. -/
def residue (N : DistinctionNat) (hN : N ≠ zero) (a : DistinctionNat) :
    DistinctionNat :=
  remainder a N hN

/-- Native equality of residues modulo `N`. -/
def sameResidue (N : DistinctionNat) (hN : N ≠ zero)
    (a b : DistinctionNat) : Prop :=
  residue N hN a = residue N hN b

theorem residue_toNat (N : DistinctionNat) (hN : N ≠ zero)
    (a : DistinctionNat) :
    (residue N hN a).toNat = a.toNat % N.toNat := by
  unfold residue
  exact remainder_toNat a N hN

theorem sameResidue_iff_mod_eq (N : DistinctionNat) (hN : N ≠ zero)
    (a b : DistinctionNat) :
    sameResidue N hN a b ↔ a.toNat % N.toNat = b.toNat % N.toNat := by
  constructor
  · intro h
    have hnat := congrArg DistinctionNat.toNat h
    simpa [sameResidue, residue_toNat] using hnat
  · intro h
    unfold sameResidue
    apply toNat_inj
    simpa [residue_toNat] using h

theorem sameResidue_refl (N : DistinctionNat) (hN : N ≠ zero)
    (a : DistinctionNat) :
    sameResidue N hN a a := by
  unfold sameResidue
  rfl

theorem sameResidue_symm {N a b : DistinctionNat} {hN : N ≠ zero}
    (h : sameResidue N hN a b) :
    sameResidue N hN b a := by
  unfold sameResidue at h ⊢
  exact h.symm

theorem sameResidue_trans {N a b c : DistinctionNat} {hN : N ≠ zero}
    (hab : sameResidue N hN a b) (hbc : sameResidue N hN b c) :
    sameResidue N hN a c := by
  unfold sameResidue at hab hbc ⊢
  exact hab.trans hbc

theorem sameResidue_add {N a b c d : DistinctionNat} {hN : N ≠ zero}
    (hab : sameResidue N hN a b) (hcd : sameResidue N hN c d) :
    sameResidue N hN (a + c) (b + d) := by
  rw [sameResidue_iff_mod_eq] at hab hcd ⊢
  rw [toNat_add, toNat_add]
  calc
    (a.toNat + c.toNat) % N.toNat
        = (a.toNat % N.toNat + c.toNat % N.toNat) % N.toNat := by
          exact Nat.add_mod a.toNat c.toNat N.toNat
    _ = (b.toNat % N.toNat + d.toNat % N.toNat) % N.toNat := by
          rw [hab, hcd]
    _ = (b.toNat + d.toNat) % N.toNat := by
          exact (Nat.add_mod b.toNat d.toNat N.toNat).symm

theorem sameResidue_mul {N a b c d : DistinctionNat} {hN : N ≠ zero}
    (hab : sameResidue N hN a b) (hcd : sameResidue N hN c d) :
    sameResidue N hN (a * c) (b * d) := by
  rw [sameResidue_iff_mod_eq] at hab hcd ⊢
  rw [toNat_mul, toNat_mul]
  calc
    (a.toNat * c.toNat) % N.toNat
        = (a.toNat % N.toNat * (c.toNat % N.toNat)) % N.toNat := by
          exact Nat.mul_mod a.toNat c.toNat N.toNat
    _ = (b.toNat % N.toNat * (d.toNat % N.toNat)) % N.toNat := by
          rw [hab, hcd]
    _ = (b.toNat * d.toNat) % N.toNat := by
          exact (Nat.mul_mod b.toNat d.toNat N.toNat).symm

/-- Residue-level addition represented back on orbit positions. -/
def residueAdd (N : DistinctionNat) (hN : N ≠ zero)
    (a b : DistinctionNat) : DistinctionNat :=
  residue N hN (a + b)

/-- Residue-level multiplication represented back on orbit positions. -/
def residueMul (N : DistinctionNat) (hN : N ≠ zero)
    (a b : DistinctionNat) : DistinctionNat :=
  residue N hN (a * b)

theorem residueAdd_toNat_mod (N : DistinctionNat) (hN : N ≠ zero)
    (a b : DistinctionNat) :
    (residueAdd N hN a b).toNat =
      (a.toNat + b.toNat) % N.toNat := by
  unfold residueAdd
  rw [residue_toNat, toNat_add]

theorem residueMul_toNat_mod (N : DistinctionNat) (hN : N ≠ zero)
    (a b : DistinctionNat) :
    (residueMul N hN a b).toNat =
      (a.toNat * b.toNat) % N.toNat := by
  unfold residueMul
  rw [residue_toNat, toNat_mul]

/-- Certificate for the residue orbit layer. -/
structure ResidueOrbitCertificate : Prop where
  residue_display :
    ∀ (N : DistinctionNat) (hN : N ≠ zero) (a : DistinctionNat),
      (residue N hN a).toNat = a.toNat % N.toNat
  same_residue_display :
    ∀ (N : DistinctionNat) (hN : N ≠ zero) (a b : DistinctionNat),
      sameResidue N hN a b ↔ a.toNat % N.toNat = b.toNat % N.toNat
  same_residue_refl :
    ∀ (N : DistinctionNat) (hN : N ≠ zero) (a : DistinctionNat),
      sameResidue N hN a a
  same_residue_symm :
    ∀ {N a b : DistinctionNat} {hN : N ≠ zero},
      sameResidue N hN a b → sameResidue N hN b a
  same_residue_trans :
    ∀ {N a b c : DistinctionNat} {hN : N ≠ zero},
      sameResidue N hN a b → sameResidue N hN b c →
        sameResidue N hN a c
  same_residue_add :
    ∀ {N a b c d : DistinctionNat} {hN : N ≠ zero},
      sameResidue N hN a b → sameResidue N hN c d →
        sameResidue N hN (a + c) (b + d)
  same_residue_mul :
    ∀ {N a b c d : DistinctionNat} {hN : N ≠ zero},
      sameResidue N hN a b → sameResidue N hN c d →
        sameResidue N hN (a * c) (b * d)
  residue_add_display :
    ∀ (N : DistinctionNat) (hN : N ≠ zero) (a b : DistinctionNat),
      (residueAdd N hN a b).toNat = (a.toNat + b.toNat) % N.toNat
  residue_mul_display :
    ∀ (N : DistinctionNat) (hN : N ≠ zero) (a b : DistinctionNat),
      (residueMul N hN a b).toNat = (a.toNat * b.toNat) % N.toNat

theorem residue_orbit_certificate : ResidueOrbitCertificate where
  residue_display := residue_toNat
  same_residue_display := sameResidue_iff_mod_eq
  same_residue_refl := sameResidue_refl
  same_residue_symm := by
    intro N a b hN h
    exact sameResidue_symm h
  same_residue_trans := by
    intro N a b c hN hab hbc
    exact sameResidue_trans hab hbc
  same_residue_add := by
    intro N a b c d hN hab hcd
    exact sameResidue_add hab hcd
  same_residue_mul := by
    intro N a b c d hN hab hcd
    exact sameResidue_mul hab hcd
  residue_add_display := residueAdd_toNat_mod
  residue_mul_display := residueMul_toNat_mod

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
