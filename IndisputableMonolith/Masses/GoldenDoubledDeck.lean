import Mathlib
import IndisputableMonolith.Masses.GoldenMonodromyReturn
import IndisputableMonolith.Masses.GoldenMonodromyCarrier
import IndisputableMonolith.Masses.GoldenDeckNoGo

/-!
# The Doubled Algebraic-Mapping-Torus Deck (GDB Stage 3b)

Stage 3a (`GoldenDeckNoGo`) proved the two no-go theorems: for `k ≠ 0` no `GL₂(ℤ)` matrix
conjugates the return map `F = returnMap k` to its inverse (trace obstruction, `k ≠ −k`), and the
only involutions commuting with the golden monodromy are `±1` (the `5p² = 1` golden-discriminant
kill). So an orientation-reversing deck **cannot live on a single fiber** at the golden value.

This module builds the construction the panel prescribed instead: the **doubled algebraic mapping
torus**. Double the chain complex of the fiber (`C₁ = ℤ⁴ ⊕ ℤ⁴`, `C₀ = ℤ⁴ ⊕ ℤ⁴`), give the two
sheets opposite monodromies (`M` on sheet 1, `M⁻¹` on sheet 2 — the algebraic shadow of the
orientation double cover, where the deck reverses the circle direction), and take the deck

  `D = [[0, M], [M⁻¹, 0]]`  (edges),   `D₀ = [[0, ε], [ε, 0]]`  (vertices).

## What is proved (all THEOREM-grade, parametric in the crossing word `cr`)

* **Involution**: `D² = 1` and `D₀² = 1` (`deckEdge_mul_deckEdge`, `deckVertex_mul_deckVertex`),
  using the Stage 3a integral inverse `M⁻¹ = (1 − k·s)·ε` (shear nilpotence).
* **Freeness certificate, block shape**: both decks have **identically zero diagonal**
  (`deckEdge_diag_zero`, `deckVertex_diag_zero`) — no cell is fixed with a nonzero coefficient —
  and **trace 0** (`deckEdge_trace`, `deckVertex_trace`), so the Lefschetz number of the deck is
  `tr(D₀) − tr(D₁) = 0` (`deck_lefschetz`), exactly as a fixed-point-free involution demands.
  This replaces the broken "nontrivial `H₁` action" acceptance check that Stage 3a killed.
* **Nontriviality**: `D ≠ ±1` by the trace (`0 ≠ ±8`), so the deck is not the trivial `±1`
  centralizer element of no-go #2 (`deckEdge_ne_one`, `deckEdge_ne_neg_one`).
* **Chain map / equivariance**: the doubled boundary `∂̂ = diag(∂, ∂)` intertwines the decks:
  `∂̂ ∘ D = D₀ ∘ ∂̂` (`doubledBoundary_mul_deckEdge`), from the Stage 3a chain-map facts
  `∂M = ε∂` and the new `∂M⁻¹ = ε∂` (`boundary_mul_monodromyInv`).
* **THE HEADLINE — the no-go is resolved on the double**: the deck conjugates the doubled
  monodromy `M̂ = diag(M, M⁻¹)` to its inverse, `D · M̂ · D = M̂⁻¹`
  (`deck_conj_doubledMonodromy`). On one fiber this conjugation is *impossible* for `k ≠ 0`
  (no-go #1); on the doubled complex the sheet swap absorbs the trace obstruction
  (`tr(M̂) = tr(M) + tr(M⁻¹) = tr(M̂⁻¹)` — the obstruction cancels identically).
* **Transfer identities** (the algebraic double-cover certificate): with projection
  `π = [I | M]` and transfer `t = [I ; M⁻¹]` (and `[I | ε]`, `[I ; ε]` on vertices):
  `π ∘ t = 2·1` (degree two) and `t ∘ π = 1 + D` (the image of the transfer is the
  `D`-invariants), plus `π ∘ D = π` and `D ∘ t = t` (the projection is deck-invariant and the
  transfer lands in the invariants), and both are chain maps
  (`boundary_mul_projEdge`, `doubledBoundary_mul_transfEdge`).
* **Golden instantiation**: everything specializes to `cr = hopfWord` (`linkingNumber = 1`, the
  golden word), giving the golden doubled deck (`golden_deck_involution`,
  `golden_deck_conjugates`).

## Honest status

* Everything here is THEOREM-grade integer block linear algebra on the banked Stage 3a objects;
  `#print axioms` = Mathlib base only, no `native_decide`, no new axioms.
* **MODEL premise (inherited from the carrier module):** that the finite complex models the link
  complement fiber and the Wang/orientation-character identifications. Nothing new is assumed.
* **OPEN (Stage 4)**: descending the doubled deck to a geometric statement (equivariant
  `H₁`/torsion of the double, the quotient identification, and the golden selection argument on
  the doubled torsion) — seeded to the lift loop as Stage 4a–4e.
-/

namespace IndisputableMonolith
namespace Masses
namespace GoldenDoubledDeck

open Matrix
open IndisputableMonolith.Masses.GoldenMonodromyReturn
open IndisputableMonolith.Masses.GoldenMonodromyCarrier
open IndisputableMonolith.Masses.GoldenDeckNoGo

/-! ## Part A — the integral monodromy inverse as a named object -/

/-- The explicit integral inverse of the carrier monodromy: `M⁻¹ = (1 − k·shear) · exchange`
(Stage 3a proved `M · M⁻¹ = 1` via shear nilpotence; `mul_eq_one_comm` gives the left inverse). -/
def monodromyInv (cr : List Crossing) : Matrix (Fin 4) (Fin 4) ℤ :=
  (1 - linkingNumber cr • shearBlock) * exchange

theorem monodromy_mul_monodromyInv (cr : List Crossing) :
    monodromy cr * monodromyInv cr = 1 :=
  monodromy_mul_inv cr

/-- Left inverse from right inverse (square integer matrices). -/
theorem monodromyInv_mul_monodromy (cr : List Crossing) :
    monodromyInv cr * monodromy cr = 1 :=
  Matrix.mul_eq_one_comm.mp (monodromy_mul_monodromyInv cr)

/-- **The inverse monodromy is a chain map covering the vertex exchange**: `∂ ∘ M⁻¹ = ε ∘ ∂`.
The mirror of Stage 3a's `boundary_mul_monodromy`, and the second input the doubled deck's
equivariance needs. -/
theorem boundary_mul_monodromyInv (cr : List Crossing) :
    boundary * monodromyInv cr = exchange * boundary := by
  unfold monodromyInv
  rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul,
    boundary_mul_shearBlock, smul_zero, sub_zero, boundary_mul_exchange]

/-! ## Part B — the doubled complex and the deck -/

/-- The doubled edge space is `ℤ⁴ ⊕ ℤ⁴` (two sheets of the fiber's edge chains). -/
abbrev Doubled := (Fin 4 ⊕ Fin 4)

/-- The doubled boundary `∂̂ = diag(∂, ∂)`: each sheet carries the fiber boundary. -/
def doubledBoundary : Matrix Doubled Doubled ℤ :=
  Matrix.fromBlocks boundary 0 0 boundary

/-- The doubled monodromy `M̂ = diag(M, M⁻¹)`: the two sheets carry **opposite** monodromies
(the orientation double cover — the deck reverses the circle direction, so transport around the
circle goes forward on one sheet and backward on the other). -/
def doubledMonodromy (cr : List Crossing) : Matrix Doubled Doubled ℤ :=
  Matrix.fromBlocks (monodromy cr) 0 0 (monodromyInv cr)

/-- The inverse doubled monodromy `M̂⁻¹ = diag(M⁻¹, M)`. -/
def doubledMonodromyInv (cr : List Crossing) : Matrix Doubled Doubled ℤ :=
  Matrix.fromBlocks (monodromyInv cr) 0 0 (monodromy cr)

/-- **The doubled AMT deck on edges**: `D = [[0, M], [M⁻¹, 0]]` — swap the sheets, twisting by
the monodromy one way and its integral inverse the other. -/
def deckEdge (cr : List Crossing) : Matrix Doubled Doubled ℤ :=
  Matrix.fromBlocks 0 (monodromy cr) (monodromyInv cr) 0

/-- **The doubled deck on vertices**: `D₀ = [[0, ε], [ε, 0]]` — swap the sheets, twisting by the
vertex exchange (which is its own inverse). -/
def deckVertex : Matrix Doubled Doubled ℤ :=
  Matrix.fromBlocks 0 exchange exchange 0

/-- `M̂ · M̂⁻¹ = 1`: the doubled monodromy is unimodular with the explicit block-diagonal
integral inverse. -/
theorem doubledMonodromy_mul_inv (cr : List Crossing) :
    doubledMonodromy cr * doubledMonodromyInv cr = 1 := by
  unfold doubledMonodromy doubledMonodromyInv
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    monodromy_mul_monodromyInv, monodromyInv_mul_monodromy]
  exact Matrix.fromBlocks_one

/-! ## Part C — the deck is a free involution (block-shape certificate) -/

/-- **`D² = 1`**: the doubled deck is an involution. The off-diagonal blocks compose to
`M · M⁻¹ = 1` and `M⁻¹ · M = 1` — this is exactly where Stage 3a's shear-nilpotence
(integrality of `M⁻¹`) is spent. -/
theorem deckEdge_mul_deckEdge (cr : List Crossing) :
    deckEdge cr * deckEdge cr = 1 := by
  unfold deckEdge
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    monodromy_mul_monodromyInv, monodromyInv_mul_monodromy]
  exact Matrix.fromBlocks_one

/-- **`D₀² = 1`**: the vertex deck is an involution (`ε² = 1`). -/
theorem deckVertex_mul_deckVertex : deckVertex * deckVertex = 1 := by
  unfold deckVertex
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, exchange_mul_exchange]
  exact Matrix.fromBlocks_one

/-- **Freeness at the cell level, edges**: the deck's diagonal is identically zero — no edge cell
is fixed with a nonzero coefficient. This is the block-shape certificate that replaces the broken
"`H₁` action" check (Stage 3a no-go #2: any commuting involution acts as `±1` on `H₁`). -/
theorem deckEdge_diag_zero (cr : List Crossing) (i : Doubled) :
    deckEdge cr i i = 0 := by
  rcases i with i | i <;> simp [deckEdge]

/-- **Freeness at the cell level, vertices**: zero diagonal. -/
theorem deckVertex_diag_zero (i : Doubled) : deckVertex i i = 0 := by
  rcases i with i | i <;> simp [deckVertex]

/-- Block trace: `tr [[A,B],[C,D]] = tr A + tr D` (not currently in Mathlib for `fromBlocks`). -/
theorem trace_fromBlocks {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n n ℤ) (B : Matrix n m ℤ) (C : Matrix m n ℤ) (D : Matrix m m ℤ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

/-- `tr D = 0` on edges (zero diagonal blocks). -/
theorem deckEdge_trace (cr : List Crossing) : (deckEdge cr).trace = 0 := by
  unfold deckEdge
  rw [trace_fromBlocks]
  simp

/-- `tr D₀ = 0` on vertices. -/
theorem deckVertex_trace : deckVertex.trace = 0 := by
  unfold deckVertex
  rw [trace_fromBlocks]
  simp

/-- **The Lefschetz number of the deck vanishes**: `Λ(D) = tr(D₀) − tr(D₁) = 0`, exactly as a
fixed-point-free (free) involution demands. A fixed cell would contribute `±1` to a diagonal. -/
theorem deck_lefschetz (cr : List Crossing) :
    deckVertex.trace - (deckEdge cr).trace = 0 := by
  rw [deckVertex_trace, deckEdge_trace, sub_zero]

/-- **Nontriviality #1**: `D ≠ 1` — the trace separates them (`0 ≠ 8`). So the deck is not the
trivial centralizer element that no-go #2 allows. -/
theorem deckEdge_ne_one (cr : List Crossing) : deckEdge cr ≠ 1 := by
  intro h
  have htr := congrArg Matrix.trace h
  rw [deckEdge_trace, Matrix.trace_one] at htr
  simp at htr

/-- **Nontriviality #2**: `D ≠ −1` (`0 ≠ −8`). -/
theorem deckEdge_ne_neg_one (cr : List Crossing) : deckEdge cr ≠ -1 := by
  intro h
  have htr := congrArg Matrix.trace h
  rw [deckEdge_trace, Matrix.trace_neg, Matrix.trace_one] at htr
  simp at htr

/-! ## Part D — equivariance: the deck is a chain map on the double -/

/-- **Deck equivariance**: `∂̂ ∘ D = D₀ ∘ ∂̂` — the doubled deck is a genuine chain map, covering
the vertex deck. Off-diagonal blocks reduce to the two chain-map facts `∂M = ε∂` (Stage 3a) and
`∂M⁻¹ = ε∂` (Part A). -/
theorem doubledBoundary_mul_deckEdge (cr : List Crossing) :
    doubledBoundary * deckEdge cr = deckVertex * doubledBoundary := by
  unfold doubledBoundary deckEdge deckVertex
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [boundary_mul_monodromy, boundary_mul_monodromyInv]

/-- The doubled monodromy is a chain map covering `diag(ε, ε)` — both sheets' monodromies cover
the same vertex exchange. -/
theorem doubledBoundary_mul_doubledMonodromy (cr : List Crossing) :
    doubledBoundary * doubledMonodromy cr
      = Matrix.fromBlocks exchange 0 0 exchange * doubledBoundary := by
  unfold doubledBoundary doubledMonodromy
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [boundary_mul_monodromy, boundary_mul_monodromyInv]

/-! ## Part E — THE HEADLINE: the deck conjugates `M̂` to `M̂⁻¹` -/

/-- **THE RESOLUTION OF NO-GO #1 ON THE DOUBLE.** The deck conjugates the doubled monodromy to
its inverse:

  `D · M̂ · D = M̂⁻¹`.

On a **single** fiber this conjugation is impossible for `k ≠ 0` (Stage 3a
`no_inverse_conjugation`: `tr F = k ≠ −k = tr F⁻¹`). On the **doubled** complex the sheet swap
absorbs the obstruction: `tr M̂ = tr M + tr M⁻¹ = tr M̂⁻¹` identically, and the conjugation is
realized by a genuinely free involution (`D² = 1`, zero diagonal, trace 0). This is the exact
algebraic statement of "the orientation-reversing symmetry lives on the orientation double cover,
not on the fiber". -/
theorem deck_conj_doubledMonodromy (cr : List Crossing) :
    deckEdge cr * doubledMonodromy cr * deckEdge cr = doubledMonodromyInv cr := by
  unfold deckEdge doubledMonodromy doubledMonodromyInv
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [monodromy_mul_monodromyInv, monodromyInv_mul_monodromy]

/-- Equivalent form (using `D² = 1`): `D · M̂ = M̂⁻¹ · D` — the deck anti-commutes with the
circle transport, i.e. reverses the circle direction. -/
theorem deck_reverses_monodromy (cr : List Crossing) :
    deckEdge cr * doubledMonodromy cr = doubledMonodromyInv cr * deckEdge cr := by
  have h := congrArg (· * deckEdge cr) (deck_conj_doubledMonodromy cr)
  simpa [Matrix.mul_assoc, deckEdge_mul_deckEdge] using h

/-! ## Part F — transfer identities (the algebraic double-cover certificate) -/

/-- The projection `π₁ = [I | M]` from the double to the base (edges): sheet 1 maps by the
identity, sheet 2 by the monodromy. -/
def projEdge (cr : List Crossing) : Matrix (Fin 4) Doubled ℤ :=
  Matrix.fromCols 1 (monodromy cr)

/-- The transfer `t₁ = [I ; M⁻¹]` from the base into the double (edges). -/
def transfEdge (cr : List Crossing) : Matrix Doubled (Fin 4) ℤ :=
  Matrix.fromRows 1 (monodromyInv cr)

/-- The projection `π₀ = [I | ε]` on vertices. -/
def projVertex : Matrix (Fin 4) Doubled ℤ :=
  Matrix.fromCols 1 exchange

/-- The transfer `t₀ = [I ; ε]` on vertices. -/
def transfVertex : Matrix Doubled (Fin 4) ℤ :=
  Matrix.fromRows 1 exchange

/-- **Transfer identity #1 (edges)**: `π ∘ t = 2·1` — the composite is multiplication by the
degree of the double cover. -/
theorem projEdge_mul_transfEdge (cr : List Crossing) :
    projEdge cr * transfEdge cr = 2 • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  unfold projEdge transfEdge
  rw [Matrix.fromCols_mul_fromRows, Matrix.one_mul, monodromy_mul_monodromyInv, two_smul]

/-- **Transfer identity #2 (edges)**: `t ∘ π = 1 + D` — the transfer composite is the invariant
projector (times 2): its image is exactly the `D`-invariant chains. -/
theorem transfEdge_mul_projEdge (cr : List Crossing) :
    transfEdge cr * projEdge cr = 1 + deckEdge cr := by
  unfold transfEdge projEdge deckEdge
  rw [Matrix.fromRows_mul_fromCols,
    show (1 : Matrix Doubled Doubled ℤ) = Matrix.fromBlocks 1 0 0 1 from
      Matrix.fromBlocks_one.symm,
    Matrix.fromBlocks_add]
  simp [monodromyInv_mul_monodromy]

/-- **Transfer identity #1 (vertices)**: `π₀ ∘ t₀ = 2·1`. -/
theorem projVertex_mul_transfVertex :
    projVertex * transfVertex = 2 • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  unfold projVertex transfVertex
  rw [Matrix.fromCols_mul_fromRows, Matrix.one_mul, exchange_mul_exchange, two_smul]

/-- **Transfer identity #2 (vertices)**: `t₀ ∘ π₀ = 1 + D₀`. -/
theorem transfVertex_mul_projVertex :
    transfVertex * projVertex = 1 + deckVertex := by
  unfold transfVertex projVertex deckVertex
  rw [Matrix.fromRows_mul_fromCols,
    show (1 : Matrix Doubled Doubled ℤ) = Matrix.fromBlocks 1 0 0 1 from
      Matrix.fromBlocks_one.symm,
    Matrix.fromBlocks_add]
  simp [exchange_mul_exchange]

/-- **The projection is deck-invariant**: `π ∘ D = π` — the base sees the two sheets as one. -/
theorem projEdge_mul_deckEdge (cr : List Crossing) :
    projEdge cr * deckEdge cr = projEdge cr := by
  unfold projEdge deckEdge
  rw [Matrix.fromCols_mul_fromBlocks]
  simp [monodromy_mul_monodromyInv]

/-- **The transfer lands in the invariants**: `D ∘ t = t`. -/
theorem deckEdge_mul_transfEdge (cr : List Crossing) :
    deckEdge cr * transfEdge cr = transfEdge cr := by
  unfold deckEdge transfEdge
  rw [Matrix.fromBlocks_mul_fromRows]
  simp [monodromy_mul_monodromyInv]

/-- **The projection is a chain map**: `∂ ∘ π₁ = π₀ ∘ ∂̂`. -/
theorem boundary_mul_projEdge (cr : List Crossing) :
    boundary * projEdge cr = projVertex * doubledBoundary := by
  unfold projEdge projVertex doubledBoundary
  rw [Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks]
  simp [boundary_mul_monodromy]

/-- **The transfer is a chain map**: `∂̂ ∘ t₁ = t₀ ∘ ∂`. -/
theorem doubledBoundary_mul_transfEdge (cr : List Crossing) :
    doubledBoundary * transfEdge cr = transfVertex * boundary := by
  unfold doubledBoundary transfEdge transfVertex
  rw [Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
  simp [boundary_mul_monodromyInv]

/-! ## Part G — golden instantiation (`cr = hopfWord`, `k = 1`) -/

/-- The golden doubled deck is an involution. -/
theorem golden_deck_involution :
    deckEdge hopfWord * deckEdge hopfWord = 1 :=
  deckEdge_mul_deckEdge hopfWord

/-- **The golden conjugation exists on the double** — precisely the conjugation that Stage 3a's
`no_inverse_conjugation_golden` proves impossible on the single fiber. -/
theorem golden_deck_conjugates :
    deckEdge hopfWord * doubledMonodromy hopfWord * deckEdge hopfWord
      = doubledMonodromyInv hopfWord :=
  deck_conj_doubledMonodromy hopfWord

/-! ## Certificate bundling GDB Stage 3b -/

/-- THEOREM-grade certificate for **GDB Stage 3b**: the doubled algebraic-mapping-torus deck
`D = [[0,M],[M⁻¹,0]]` is a free involution (`D² = 1`, zero diagonal, trace 0, Lefschetz 0),
nontrivial (`D ≠ ±1`), a chain map covering the vertex deck (`∂̂D = D₀∂̂`), it conjugates the
doubled monodromy to its inverse (`DM̂D = M̂⁻¹` — the exact conjugation no-go #1 forbids on a
single fiber), and the projection/transfer pair certifies the algebraic double cover
(`πt = 2`, `tπ = 1 + D`, both chain maps, `πD = π`, `Dt = t`). All parametric in the crossing
word, hence valid at the golden word `hopfWord`. -/
structure DoubledDeckCert : Prop where
  deck_involution : ∀ cr : List Crossing, deckEdge cr * deckEdge cr = 1
  deck_vertex_involution : deckVertex * deckVertex = 1
  deck_free_diag : ∀ cr : List Crossing, ∀ i : Doubled, deckEdge cr i i = 0
  deck_trace_zero : ∀ cr : List Crossing, (deckEdge cr).trace = 0
  deck_lefschetz_zero : ∀ cr : List Crossing, deckVertex.trace - (deckEdge cr).trace = 0
  deck_nontrivial : ∀ cr : List Crossing, deckEdge cr ≠ 1 ∧ deckEdge cr ≠ -1
  deck_chain_map : ∀ cr : List Crossing,
    doubledBoundary * deckEdge cr = deckVertex * doubledBoundary
  deck_conjugates : ∀ cr : List Crossing,
    deckEdge cr * doubledMonodromy cr * deckEdge cr = doubledMonodromyInv cr
  transfer_degree : ∀ cr : List Crossing,
    projEdge cr * transfEdge cr = 2 • (1 : Matrix (Fin 4) (Fin 4) ℤ)
  transfer_invariants : ∀ cr : List Crossing,
    transfEdge cr * projEdge cr = 1 + deckEdge cr
  proj_deck_invariant : ∀ cr : List Crossing, projEdge cr * deckEdge cr = projEdge cr
  proj_chain_map : ∀ cr : List Crossing,
    boundary * projEdge cr = projVertex * doubledBoundary
  transf_chain_map : ∀ cr : List Crossing,
    doubledBoundary * transfEdge cr = transfVertex * boundary

theorem doubledDeckCert_holds : DoubledDeckCert where
  deck_involution := deckEdge_mul_deckEdge
  deck_vertex_involution := deckVertex_mul_deckVertex
  deck_free_diag := deckEdge_diag_zero
  deck_trace_zero := deckEdge_trace
  deck_lefschetz_zero := deck_lefschetz
  deck_nontrivial := fun cr => ⟨deckEdge_ne_one cr, deckEdge_ne_neg_one cr⟩
  deck_chain_map := doubledBoundary_mul_deckEdge
  deck_conjugates := deck_conj_doubledMonodromy
  transfer_degree := projEdge_mul_transfEdge
  transfer_invariants := transfEdge_mul_projEdge
  proj_deck_invariant := projEdge_mul_deckEdge
  proj_chain_map := boundary_mul_projEdge
  transf_chain_map := doubledBoundary_mul_transfEdge

end GoldenDoubledDeck
end Masses
end IndisputableMonolith
