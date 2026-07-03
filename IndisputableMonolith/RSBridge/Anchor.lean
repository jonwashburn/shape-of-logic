import Mathlib
import IndisputableMonolith.Constants

/-!
# RSBridge Anchor: Fermion Species, Z-Map, and Gap Function

This module defines the core bridge between the recognition framework and particle physics:

1. **Fermion**: The 12 Standard Model fermions (6 quarks + 3 leptons + 3 neutrinos).
2. **ZOf**: The charge-indexed integer Z_i = q̃² + q̃⁴ (+ 4 for quarks).
3. **gap (F)**: The display function F(Z) = ln(1 + Z/φ) / ln(φ).
4. **massAtAnchor**: The mass at the anchor scale μ⋆.
5. **anchor_ratio**: Family mass ratios are pure φ-powers for equal-Z species.

## Relation to RG Transport

The `gap` function F(Z) is the **closed form** that the integrated RG residue
`f_i(μ⋆)` is claimed to equal at the anchor scale. See:
- `Physics/RGTransport.lean` for the mathematical framework of γ and ∫γ.
- `Physics/AnchorPolicy.lean` for the axiom `display_identity_at_anchor`.

The claim of Single Anchor Phenomenology is:
  `(1/ln φ) ∫_{ln μ⋆}^{ln m_phys} γ_i(μ) d(ln μ) ≈ gap(ZOf i)`

with tolerance ~1e-6.
-/

namespace IndisputableMonolith
namespace RSBridge

inductive Sector | up | down | lepton | neutrino
deriving DecidableEq, Repr

inductive Fermion
| d | s | b | u | c | t | e | mu | tau | nu1 | nu2 | nu3
deriving DecidableEq, Repr, Inhabited

def sectorOf : Fermion → Sector
| .d | .s | .b => .down
| .u | .c | .t => .up
| .e | .mu | .tau => .lepton
| .nu1 | .nu2 | .nu3 => .neutrino

def tildeQ : Fermion → ℤ
| .u | .c | .t => 4
| .d | .s | .b => -2
| .e | .mu | .tau => -6
| .nu1 | .nu2 | .nu3 => 0

def ZOf (f : Fermion) : ℤ :=
  let q := tildeQ f
  match sectorOf f with
  | .up | .down => 4 + q*q + q*q*q*q
  | .lepton     =>     q*q + q*q*q*q
  | .neutrino   => 0

/-- The display function F(Z) = ln(1 + Z/φ) / ln(φ).

    This is the **closed form** that the integrated RG residue is claimed to equal
    at the anchor scale μ⋆. The claim is:
      `f_i(μ⋆) = gap(ZOf i)`
    where `f_i(μ⋆)` is the integral of the mass anomalous dimension.

    **Properties**:
    - F(0) = 0
    - F is monotonically increasing for Z > -φ
    - For large Z: F(Z) ≈ log_φ(Z)

    **Canonical values** (charged fermions):
    - F(24)   ≈ 5.74   (down quarks, q̃ = -2)
    - F(276)  ≈ 10.69  (up quarks, q̃ = +4)
    - F(1332) ≈ 13.95  (leptons, q̃ = -6) -/
noncomputable def gap (Z : ℤ) : ℝ :=
  (Real.log (1 + (Z : ℝ) / (Constants.phi))) / (Real.log (Constants.phi))

notation "𝓕(" Z ")" => gap Z

/-- The residue at the anchor for a fermion species.

    This is the **definitional** (closed-form) residue: `F(Z_i) = gap(ZOf f)`.

    **Relation to the axiom `f_residue`**: The physics claim (stated as an axiom in
    `AnchorPolicy.lean`) is that the RG-transport residue equals this value:
      `f_residue f μ⋆ = residueAtAnchor f`
    This is verified numerically by external tools. -/
noncomputable def residueAtAnchor (f : Fermion) : ℝ := gap (ZOf f)

theorem anchorEquality (f : Fermion) : residueAtAnchor f = gap (ZOf f) := by rfl

theorem equalZ_residue (f g : Fermion) (hZ : ZOf f = ZOf g) :
  residueAtAnchor f = residueAtAnchor g := by
  simp [residueAtAnchor, hZ]

noncomputable def rung : Fermion → ℤ
| .e   => 2   | .mu  => 13  | .tau => 19
| .u   => 4   | .c   => 15  | .t   => 21
| .d   => 4   | .s   => 15  | .b   => 21
| .nu1 => 0   | .nu2 => 11  | .nu3 => 19

def M0 : ℝ := 1
@[simp] theorem M0_pos : 0 < M0 := by
  dsimp [M0]; norm_num

noncomputable def massAtAnchor (f : Fermion) : ℝ :=
  M0 * Real.exp (((rung f : ℝ) - 8 + gap (ZOf f)) * Real.log (Constants.phi))

theorem anchor_ratio (f g : Fermion) (hZ : ZOf f = ZOf g) :
  massAtAnchor f / massAtAnchor g =
    Real.exp (((rung f : ℝ) - rung g) * Real.log (Constants.phi)) := by
  unfold massAtAnchor
  set Af := ((rung f : ℝ) - 8 + gap (ZOf f)) * Real.log (Constants.phi)
  set Ag := ((rung g : ℝ) - 8 + gap (ZOf g)) * Real.log (Constants.phi)
  -- Since M0=1, factor cancels directly
  calc
    (M0 * Real.exp Af) / (M0 * Real.exp Ag)
        = (Real.exp Af) / (Real.exp Ag) := by simpa [M0]
    _ = Real.exp (Af - Ag) := by
              simpa [Real.exp_sub] using (Real.exp_sub Af Ag).symm
    _ = Real.exp ((((rung f : ℝ) - 8 + gap (ZOf f)) - ((rung g : ℝ) - 8 + gap (ZOf g)))
                   * Real.log (Constants.phi)) := by
              have : Af - Ag
                    = (((rung f : ℝ) - 8 + gap (ZOf f)) - ((rung g : ℝ) - 8 + gap (ZOf g)))
                       * Real.log (Constants.phi) := by
                        simp [Af, Ag, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                              mul_add, add_mul]
              have h' :
                ((rung f : ℝ) - 8 + gap (ZOf f)) - ((rung g : ℝ) - 8 + gap (ZOf g))
                = (rung f : ℝ) - rung g + (gap (ZOf f) - gap (ZOf g)) := by ring
              simpa [this, h']
    _ = Real.exp (((rung f : ℝ) - rung g) * Real.log (Constants.phi)) := by
              simpa [hZ, sub_self, add_zero, add_comm, add_left_comm, add_assoc, mul_add,
                     add_right_comm, mul_comm, mul_left_comm, mul_assoc]

structure ResidueCert where
  f  : Fermion
  lo : ℚ
  hi : ℚ
  lo_le_hi : lo ≤ hi

def ResidueCert.valid (c : ResidueCert) : Prop :=
  (c.lo : ℝ) ≤ gap (ZOf c.f) ∧ gap (ZOf c.f) ≤ (c.hi : ℝ)

/-! ### Generation indexing (three disjoint families) -/

/-- Generation index (0,1,2) assigned by rung/sector ordering. -/
def genOf : Fermion → Fin 3
| .e   => ⟨0, by decide⟩ | .mu  => ⟨1, by decide⟩ | .tau => ⟨2, by decide⟩
| .u   => ⟨0, by decide⟩ | .c   => ⟨1, by decide⟩ | .t   => ⟨2, by decide⟩
| .d   => ⟨0, by decide⟩ | .s   => ⟨1, by decide⟩ | .b   => ⟨2, by decide⟩
| .nu1 => ⟨0, by decide⟩ | .nu2 => ⟨1, by decide⟩ | .nu3 => ⟨2, by decide⟩

/-- Surjectivity of the generation index: there are exactly three generations. -/
theorem genOf_surjective : Function.Surjective genOf := by
  intro i
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
    fin_cases i <;> simp
  rcases h with h0 | h12
  · -- i = 0
    refine ⟨Fermion.e, ?_⟩
    apply Fin.ext
    simp [genOf, h0]
  · rcases h12 with h1 | h2
    · -- i = 1
      refine ⟨Fermion.mu, ?_⟩
      apply Fin.ext
      simp [genOf, h1]
    · -- i = 2
      refine ⟨Fermion.tau, ?_⟩
      apply Fin.ext
      simp [genOf, h2]

/-! ### Admissible family encoding via rung residue classes and equal‑Z -/

/-- Rung residue class modulo 360 (the joint sync scale of 8‑beat and rung‑45). -/
def rungResidueClass (a : ℤ) : Set Fermion :=
  { f | Int.ModEq (360 : ℤ) (rung f) a }

/-- An admissible family is a set of fermions that share a single Z value
    (equal‑Z degeneracy at μ*) and land on a common rung residue class
    modulo 360. This packages the “equal‑Z + rung‑offset” policy encoding. -/
structure AdmissibleFamily (S : Set Fermion) : Prop where
  equalZ_const : ∃ Z0 : ℤ, ∀ {f}, f ∈ S → ZOf f = Z0
  rung_residue : ∃ a : ℤ, ∀ {f}, f ∈ S → Int.ModEq (360 : ℤ) (rung f) a


end RSBridge
end IndisputableMonolith
