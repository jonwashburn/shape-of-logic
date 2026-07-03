import Mathlib
import IndisputableMonolith.Masses.GoldenMonodromyReturn
import IndisputableMonolith.Masses.GoldenMonodromyCarrier

/-!
# Chain-Map Certificates and the Deck No-Go Theorems (GDB Stage 3a)

The GDB panel (7-model debate + judge, 2026-07-01) rebuilt Stage 3 as two halves. This module is
**Stage 3a**, the panel's "first step (tonight, one file)": certify that the banked carrier
monodromy is a genuine chain map (micro-lemmas, `decide`-checkable), and prove the two **no-go
theorems** that kill the naive fiberwise deck-involution search before Stage 3b builds the doubled
algebraic-mapping-torus deck.

## Part A — chain-map micro-lemmas (the systemic-kill check, all green)

The panel: "First conjunct red = systemic kill (the monodromy isn't even a chain map)." All green:

* `boundary_mul_shearBlock` — `∂ ∘ shear = 0`: the shear image consists of cycles.
* `shearBlock_mul_shearBlock` — `shear² = 0`: the shear is nilpotent. This is what makes the
  transport **unimodular with an integral inverse** (`(1 + k·s)⁻¹ = 1 − k·s`), the fact Stage 3b's
  doubled deck `D = [[0,M],[M⁻¹,0]]` needs for `M⁻¹` to be integral.
* `boundary_mul_exchange` — `∂ ∘ exchange = exchange ∘ ∂`: the exchange is a chain map covering
  the vertex exchange (the same permutation matrix acts in both degrees).
* `boundary_mul_transport` / `boundary_mul_monodromy` — the transport is a chain map covering the
  **identity** on vertices, hence the full monodromy is a chain map covering the vertex exchange.

**Honest correction of the panel list.** The panel's fourth identity `shearBlock * boundary = 0`
is **false** as a raw 4×4 product (row 0 of the shear picks up row 2 of the boundary); we prove
the disequality `shearBlock_mul_boundary_ne_zero` so the record cannot silently regress. The
identity is also not the degree-correct chain-map condition: `shear` maps edges → edges while
`boundary` maps edges → vertices, so the composite `shear ∘ ∂` is type-crossed. The correct
statement is `boundary_mul_transport : ∂ ∘ (1 + k·shear) = ∂` (transport covers the identity),
which holds and is what descent-to-`H₁` actually uses.

## Part B — no-go #1: the trace obstruction (`no_inverse_conjugation`)

No `P ∈ GL₂(ℤ)` conjugates `returnMap k` to its inverse when `k ≠ 0`: conjugation preserves the
trace, `trace F = k`, and `trace F⁻¹ = −k` (the explicit integral inverse `returnMapInv k =
!![−k,1;1,0]`). So an orientation-reversing fiberwise deck (which would have to intertwine `F`
with `F⁻¹`) **cannot exist at the golden value** — the obstruction `k ≠ −k` activates exactly
away from the involutive control `k = 0`, where the conjugation exists trivially
(`unlink_conjugates_to_inverse`: `returnMap 0` is its own inverse).

## Part C — no-go #2: the golden centralizer (`commuting_involution_pm_one`)

Any integer matrix commuting with the golden monodromy `F = returnMap 1` lies in `ℤ[F]`
(`commutant_golden`: `E = p·I + q·F`, an entrywise computation). If such an `E` is an involution,
then using the golden relation `F² = F + 1`:
`E² = (p² + q²)·I + (2pq + q²)·F = I` forces `q(2p + q) = 0`; the branch `q = −2p` demands
**`5p² = 1`** — the golden discriminant `√5` appearing as the integer obstruction — which is
impossible, so `q = 0` and `E = ±I`. **The only involutions commuting with the golden monodromy
are `±1`.** Together with Part B this proves the fiberwise 4×4 deck search the earlier plan
proposed ends in a false kill or a junk pass: any candidate deck acts on `H₁` as `±1` (trivially),
exactly the critic's note that "nontrivial H₁ action" is the wrong acceptance check. The right
construction is Stage 3b's **doubled** algebraic mapping torus, where freeness is certified by the
block shape (zero diagonal, trace 0), not by an H₁ action.

## Honest status

* Everything here is THEOREM-grade integer linear algebra on banked objects; `#print axioms` =
  Mathlib base only, no `native_decide`.
* **MODEL premise (inherited, stated in the carrier module):** that the finite complex is the
  link complement and the Wang/orientation-character identifications. Nothing new is assumed.
* **OPEN (Stage 3b):** the doubled AMT deck `D = [[0,M],[M⁻¹,0]]` with `D² = 1`, zero diagonal,
  trace 0, and the transfer identities — seeded to the lift loop as the next lake-gated target.
-/

namespace IndisputableMonolith
namespace Masses
namespace GoldenDeckNoGo

open Matrix
open IndisputableMonolith.Masses.GoldenMonodromyReturn
open IndisputableMonolith.Masses.GoldenMonodromyCarrier

/-! ## Part A — chain-map micro-lemmas on the carrier -/

/-- **Shear image ⊆ cycles.** `∂ ∘ shear = 0`: every sheared chain is a cycle. -/
theorem boundary_mul_shearBlock : boundary * shearBlock = 0 := by decide

/-- **The shear is nilpotent**: `shear² = 0`. This is the source of the transport's integral
inverse (`(1 + k·s)(1 − k·s) = 1`), the fact Stage 3b's `M⁻¹` needs to be integral. -/
theorem shearBlock_mul_shearBlock : shearBlock * shearBlock = 0 := by decide

theorem shearBlock_sq : shearBlock ^ 2 = 0 := by
  rw [sq]; exact shearBlock_mul_shearBlock

/-- **The exchange is a chain map** covering the vertex exchange: `∂ ∘ ε = ε ∘ ∂` (the same
permutation matrix `(0 2)(1 3)` acts on edges and on vertices). -/
theorem boundary_mul_exchange : boundary * exchange = exchange * boundary := by decide

/-- **The exchange is an involution**: `ε² = 1`. -/
theorem exchange_mul_exchange : exchange * exchange = 1 := by decide

/-- **Honest correction of the panel list.** The panel's proposed identity
`shearBlock * boundary = 0` is FALSE as a raw matrix product (the composite is type-crossed:
`boundary` maps edges → vertices while `shear` maps edges → edges). Recorded as a disequality so
the correction cannot silently regress; the degree-correct statement is
`boundary_mul_transport` below. -/
theorem shearBlock_mul_boundary_ne_zero : shearBlock * boundary ≠ 0 := by decide

/-- **The transport is a chain map covering the identity on vertices**: `∂ ∘ (1 + k·s) = ∂`.
Immediate from `∂ ∘ s = 0`; this is the degree-correct form of the panel's fourth identity. -/
theorem boundary_mul_transport (cr : List Crossing) :
    boundary * transport cr = boundary := by
  unfold transport
  rw [mul_add, mul_one, Matrix.mul_smul, boundary_mul_shearBlock, smul_zero, add_zero]

/-- **THE SYSTEMIC-KILL CHECK, GREEN: the monodromy is a chain map** covering the vertex
exchange: `∂ ∘ (ε ∘ τ) = ε ∘ ∂`. Had this failed, the whole carrier would be dead (the panel's
"first conjunct red = systemic kill"). -/
theorem boundary_mul_monodromy (cr : List Crossing) :
    boundary * monodromy cr = exchange * boundary := by
  unfold monodromy
  rw [← Matrix.mul_assoc, boundary_mul_exchange, Matrix.mul_assoc, boundary_mul_transport]

/-- **The transport is unimodular with an explicit integral inverse**: `(1 + k·s)(1 − k·s) = 1`,
by nilpotence of the shear. This is the `M⁻¹`-integrality input for Stage 3b's doubled deck. -/
theorem transport_mul_transport_neg (cr : List Crossing) :
    transport cr * (1 - linkingNumber cr • shearBlock) = 1 := by
  unfold transport
  rw [mul_sub, mul_one, add_mul, one_mul, Matrix.smul_mul, Matrix.mul_smul,
    shearBlock_mul_shearBlock]
  simp

/-- **The full monodromy is unimodular with an explicit integral inverse**:
`(ε τ) · (τ⁻¹ ε) = 1`. -/
theorem monodromy_mul_inv (cr : List Crossing) :
    monodromy cr * ((1 - linkingNumber cr • shearBlock) * exchange) = 1 := by
  unfold monodromy
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (transport cr), transport_mul_transport_neg,
    Matrix.one_mul, exchange_mul_exchange]

/-! ## Part B — no-go #1: no conjugation of the return map to its inverse (`k ≠ 0`) -/

/-- The explicit integral inverse of the return map: `F⁻¹ = !![−k, 1; 1, 0]`
(adjugate over `det = −1`). -/
def returnMapInv (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![-k, 1; 1, 0]

theorem returnMap_mul_returnMapInv (k : ℤ) : returnMap k * returnMapInv k = 1 := by
  rw [returnMap_closed_form]
  unfold returnMapInv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero]

theorem returnMapInv_mul_returnMap (k : ℤ) : returnMapInv k * returnMap k = 1 := by
  rw [returnMap_closed_form]
  unfold returnMapInv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero]

/-- **The inverse trace is `−k`** — the whole trace obstruction in one line. -/
theorem returnMapInv_trace (k : ℤ) : (returnMapInv k).trace = -k := by
  unfold returnMapInv
  simp [Matrix.trace_fin_two]

/-- At the involutive control `k = 0` the return map is its own inverse. -/
theorem returnMapInv_zero : returnMapInv 0 = returnMap 0 := by
  rw [returnMap_closed_form]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [returnMapInv]

/-- **NO-GO #1 (trace obstruction).** For `k ≠ 0`, no `P ∈ GL₂(ℤ)` conjugates the return map to
its inverse: conjugation preserves the trace, and `trace F = k ≠ −k = trace F⁻¹`. An
orientation-reversing fiberwise deck would have to realize exactly this conjugation, so **no such
deck exists at the golden value** (or any `k ≠ 0`). -/
theorem no_inverse_conjugation (k : ℤ) (hk : k ≠ 0)
    (P : Matrix (Fin 2) (Fin 2) ℤ) (hP : IsUnit P.det) :
    P * returnMap k * P⁻¹ ≠ returnMapInv k := by
  intro h
  have htr := congrArg Matrix.trace h
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hP,
    Matrix.one_mul, returnMap_trace, returnMapInv_trace] at htr
  omega

/-- The golden specialization of no-go #1. -/
theorem no_inverse_conjugation_golden
    (P : Matrix (Fin 2) (Fin 2) ℤ) (hP : IsUnit P.det) :
    P * returnMap 1 * P⁻¹ ≠ returnMapInv 1 :=
  no_inverse_conjugation 1 one_ne_zero P hP

/-- **Positive control (the obstruction is sharp).** At `k = 0` the conjugation exists trivially:
the unlink return map is an involution, hence its own inverse. -/
theorem unlink_conjugates_to_inverse :
    (1 : Matrix (Fin 2) (Fin 2) ℤ) * returnMap 0 * (1 : Matrix (Fin 2) (Fin 2) ℤ)⁻¹
      = returnMapInv 0 := by
  rw [inv_one, Matrix.mul_one, Matrix.one_mul, returnMapInv_zero]

/-! ## Part C — no-go #2: the golden centralizer forces `±1` -/

/-- **The commutant of the golden monodromy is `ℤ[F]`.** Any integer `2×2` matrix commuting with
`F = returnMap 1` is `p·I + q·F` (an entrywise computation: the commutator equations force
`E₁₀ = E₀₁` and `E₁₁ = E₀₀ + E₀₁`). -/
theorem commutant_golden (E : Matrix (Fin 2) (Fin 2) ℤ)
    (h : E * returnMap 1 = returnMap 1 * E) :
    ∃ p q : ℤ, E = p • (1 : Matrix (Fin 2) (Fin 2) ℤ) + q • returnMap 1 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, E = !![a, b; c, d] :=
    ⟨E 0 0, E 0 1, E 1 0, E 1 1, Matrix.eta_fin_two E⟩
  rw [returnMap_closed_form] at h ⊢
  refine ⟨a, b, ?_⟩
  have h00 : (!![a, b; c, d] * !![(0 : ℤ), 1; 1, 1]) 0 0
      = (!![(0 : ℤ), 1; 1, 1] * !![a, b; c, d]) 0 0 := by rw [h]
  have h01 : (!![a, b; c, d] * !![(0 : ℤ), 1; 1, 1]) 0 1
      = (!![(0 : ℤ), 1; 1, 1] * !![a, b; c, d]) 0 1 := by rw [h]
  simp [Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.intCast_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega

/-- **NO-GO #2 (the golden discriminant kill).** The only involutions commuting with the golden
monodromy are `±1`. Writing a commuting `E = p·I + q·F` and squaring with the golden relation
`F² = F + 1`: `E² = 1` forces `q(2p + q) = 0`; the branch `q = −2p` demands `5p² = 1` — the
discriminant of `X² − X − 1` blocking an integer solution — so `q = 0` and `p² = 1`.
A fiberwise deck therefore acts on `H₁` as `±1`: **trivially**. The "nontrivial H₁ action" check
the earlier plan proposed can never fire; freeness must be certified by the doubled block shape
(Stage 3b), not on `H₁`. -/
theorem commuting_involution_pm_one (E : Matrix (Fin 2) (Fin 2) ℤ)
    (hcomm : E * returnMap 1 = returnMap 1 * E) (hinv : E * E = 1) :
    E = 1 ∨ E = -1 := by
  obtain ⟨p, q, rfl⟩ := commutant_golden E hcomm
  rw [returnMap_closed_form] at hinv ⊢
  have h00 : ((p • (1 : Matrix (Fin 2) (Fin 2) ℤ) + q • !![(0 : ℤ), 1; 1, 1])
      * (p • (1 : Matrix (Fin 2) (Fin 2) ℤ) + q • !![(0 : ℤ), 1; 1, 1])) 0 0
      = (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by rw [hinv]
  have h01 : ((p • (1 : Matrix (Fin 2) (Fin 2) ℤ) + q • !![(0 : ℤ), 1; 1, 1])
      * (p • (1 : Matrix (Fin 2) (Fin 2) ℤ) + q • !![(0 : ℤ), 1; 1, 1])) 0 1
      = (1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by rw [hinv]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.intCast_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01
  have hq : q * (2 * p + q) = 0 := by linear_combination h01
  rcases mul_eq_zero.mp hq with hq0 | hqp
  · subst hq0
    have hpp : p * p = 1 := by linear_combination h00
    rcases mul_self_eq_one_iff.mp hpp with rfl | rfl
    · left; simp
    · right
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.add_apply, Matrix.neg_apply]
  · exfalso
    have hq' : q = -(2 * p) := by linarith
    subst hq'
    have h5 : 5 * (p * p) = 1 := by linear_combination h00
    obtain ⟨m, hm0, hm⟩ : ∃ m : ℤ, 0 ≤ m ∧ 5 * m = 1 := ⟨p * p, mul_self_nonneg p, h5⟩
    omega

/-- **Positive control**: `−1` genuinely is a commuting involution, so the classification
`{±1}` is exactly realized (not vacuously empty). -/
theorem neg_one_is_commuting_involution :
    ((-1 : Matrix (Fin 2) (Fin 2) ℤ) * returnMap 1 = returnMap 1 * (-1))
      ∧ ((-1 : Matrix (Fin 2) (Fin 2) ℤ) * (-1) = 1) := by
  constructor
  · rw [neg_one_mul, mul_neg_one]
  · rw [neg_one_mul, neg_neg]

/-! ## Certificate bundling GDB Stage 3a -/

/-- THEOREM-grade certificate for **GDB Stage 3a**: the carrier monodromy is a genuine chain map
(the systemic-kill check, green), the transport and monodromy are unimodular with explicit
integral inverses (via shear nilpotence — the `M⁻¹`-integrality input for Stage 3b), and the two
no-go theorems hold: no `GL₂(ℤ)` conjugation of the return map to its inverse for `k ≠ 0` (trace
obstruction, sharp at the `k = 0` control), and the only involutions commuting with the golden
monodromy are `±1` (the `5p² = 1` golden-discriminant kill). Together: a fiberwise deck involution
is either trivial on `H₁` or nonexistent, so the deck must be built on the **doubled** algebraic
mapping torus (Stage 3b), certified by block shape rather than `H₁` action. -/
structure DeckNoGoCert : Prop where
  shear_image_cycles : boundary * shearBlock = 0
  shear_nilpotent : shearBlock * shearBlock = 0
  exchange_chain_map : boundary * exchange = exchange * boundary
  exchange_involution : exchange * exchange = 1
  transport_chain_map : ∀ cr : List Crossing, boundary * transport cr = boundary
  monodromy_chain_map : ∀ cr : List Crossing, boundary * monodromy cr = exchange * boundary
  transport_unimodular : ∀ cr : List Crossing,
    transport cr * (1 - linkingNumber cr • shearBlock) = 1
  monodromy_unimodular : ∀ cr : List Crossing,
    monodromy cr * ((1 - linkingNumber cr • shearBlock) * exchange) = 1
  no_inverse_conj : ∀ k : ℤ, k ≠ 0 → ∀ P : Matrix (Fin 2) (Fin 2) ℤ, IsUnit P.det →
    P * returnMap k * P⁻¹ ≠ returnMapInv k
  unlink_control : (1 : Matrix (Fin 2) (Fin 2) ℤ) * returnMap 0
    * (1 : Matrix (Fin 2) (Fin 2) ℤ)⁻¹ = returnMapInv 0
  commutant : ∀ E : Matrix (Fin 2) (Fin 2) ℤ, E * returnMap 1 = returnMap 1 * E →
    ∃ p q : ℤ, E = p • (1 : Matrix (Fin 2) (Fin 2) ℤ) + q • returnMap 1
  involutions_pm_one : ∀ E : Matrix (Fin 2) (Fin 2) ℤ, E * returnMap 1 = returnMap 1 * E →
    E * E = 1 → E = 1 ∨ E = -1

theorem deckNoGoCert_holds : DeckNoGoCert where
  shear_image_cycles := boundary_mul_shearBlock
  shear_nilpotent := shearBlock_mul_shearBlock
  exchange_chain_map := boundary_mul_exchange
  exchange_involution := exchange_mul_exchange
  transport_chain_map := boundary_mul_transport
  monodromy_chain_map := boundary_mul_monodromy
  transport_unimodular := transport_mul_transport_neg
  monodromy_unimodular := monodromy_mul_inv
  no_inverse_conj := no_inverse_conjugation
  unlink_control := unlink_conjugates_to_inverse
  commutant := commutant_golden
  involutions_pm_one := commuting_involution_pm_one

end GoldenDeckNoGo
end Masses
end IndisputableMonolith
