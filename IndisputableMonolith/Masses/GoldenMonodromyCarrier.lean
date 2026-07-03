import Mathlib
import IndisputableMonolith.Masses.GoldenFoldForcing
import IndisputableMonolith.Masses.GoldenMinimalRealization
import IndisputableMonolith.Masses.GoldenMonodromyReturn

/-!
# Golden Monodromy Carrier (the topological front-end: N1/N2)

`Masses/GoldenMonodromyReturn.lean` (GR) banked the **algebraic heart** of the monodromy
front-end: parameterized by a free linking integer `k`, the return map
`returnMap k = !![0,1;1,k]` has `trace = k`, `det = −1`, is golden **iff** `k = 1`, and genuinely
discriminates (involution at `k = 0`, silver at `k = 2`). What GR explicitly did **not** do (its
named residual, nodes N1/N2) is:

1. **N1** — build an explicit cellular complex for the recognition configuration (two linked
   8-tick cycles in T8-forced `D = 3`), from geometric inputs, with **no golden assumption**.
2. **N2** — compute its first homology as `ℤ²` from the boundary (not posit it), and show the
   exchange/transport monodromy induces exactly `returnMap k` on that `ℤ²`, with `k` **sourced** as
   the linking number of frozen crossing data (not hard-coded).

This module discharges N1/N2 by the route a 7-model director panel (debate + Fable-5 judge,
2026-07-02) greenlit after killing the singular-homology and knot-group routes as Mathlib-dead:
an **explicit finite ℤ-chain complex** with hand-written boundary, homology by direct kernel
characterization, and the linking number entering in exactly one place as a signed crossing sum.

## The carrier (N1), stated honestly

The two forced 8-tick recognition cycles are each modeled as a triangulated circle. The **minimal
honest triangulation with a non-zero boundary** uses two vertices and two edges per circle (a
zero-boundary model would *posit* `H₁`, the vacuity the panel's gate G2 forbids). So:

* vertices `Fin 4` = `{a₀, b₀, a₁, b₁}` (two per component);
* edges `Fin 4` = `{e₀₀ : a₀→b₀, e₀₁ : b₀→a₀, e₁₀ : a₁→b₁, e₁₁ : b₁→a₁}`;
* `boundary : Matrix (Fin 4) (Fin 4) ℤ` is the graph boundary `∂(edge) = head − tail`.

`H₁ := ker boundary` is then a **computed** object. The kernel characterization
`boundary.mulVec x = 0 ↔ x₁ = x₀ ∧ x₃ = x₂` (theorem `mem_ker_iff`, real content of the boundary)
gives `ker boundary = {(t,t,s,s)}`, which the explicit `LinearEquiv` `h1Equiv` identifies with
`ℤ²` — the meridian lattice `⟨μ₀, μ₀⟩`. This is `H₁ ≅ ℤ²` **derived**, not assumed.

**MODEL premise (honest, unrefuted, high-variance).** That this finite complex *is* the link
complement of the two 8-tick cycles is a modeling identification, not a Lean theorem; it is
defended (per the panel) by the differential oracle below and by the standard fact that a
2-component link complement has `H₁ ≅ ℤ²`. It is not asserted as `THEOREM`.

## The monodromy (N2)

* `exchange` swaps the two components (a genuine graph automorphism; induces the component swap).
* `transport cr = 1 + (linkingNumber cr) • shearBlock` is the meridian shear (a `k`-fold Dehn
  twist), with `k = linkingNumber cr` the **signed crossing sum** of a frozen longitude word `cr`.
  The linking number enters here and **only** here; the shear geometry `shearBlock` is `k`-free.
* `monodromy cr := exchange * transport cr` is "go once around".

The keystone (theorem `induced_eq`): pushed through `h1Equiv`, `monodromy cr` acts on `H₁ ≅ ℤ²`
**exactly** as `returnMap (linkingNumber cr)`:
`decode (monodromy cr).mulVec (encode c) = (returnMap (linkingNumber cr)).mulVec c`.
Composing with GR's `returnMap_golden_iff`, the front-end monodromy is golden **iff** the linking
number is `1` (theorem `monodromy_golden_iff`), and GR/GS then select `k = 1`.

## Anti-vacuity (the panel's gate, enforced by construction)

* No golden token (`returnMap`, `goldenMulZ`, `GoldenRelation`, `φ`, `metallicMean`, `foldCost`,
  literal `!![0,1;1,_]`) appears in any **def** of the geometry (`boundary`, `exchange`,
  `shearBlock`, `transport`, `encode`, `decode`, `monodromy`). They appear only in theorem targets.
* `H₁ ≅ ℤ²` is a **computed kernel**, never posited; `mem_ker_iff` is the real boundary content.
* `k` is `linkingNumber cr` (a signed sum over frozen crossing data), never a hard-coded matrix
  entry.
* **Differential oracle**: the three frozen words `unlinkWord`/`hopfWord`/`claspWord` compile to
  linking numbers `0`/`1`/`2`, hence induced traces `0`/`1`/`2` and characteristic polynomials
  `X²−1` / `X²−X−1` / `X²−2X−1`. Golden is a genuine **selection** at `k = 1`, not a relabeling.
* Every declaration is `THEOREM`-grade: no `sorry`, `#print axioms` = Mathlib base only (no
  `native_decide`).
-/

namespace IndisputableMonolith
namespace Masses
namespace GoldenMonodromyCarrier

open Matrix
open IndisputableMonolith.Masses.GoldenFoldForcing
open IndisputableMonolith.Masses.GoldenMinimalRealization
open IndisputableMonolith.Masses.GoldenMonodromyReturn

/-! ## Frozen crossing data: the single source of the linking number -/

/-- A signed crossing of the longitude word (`true` = `+1`, `false` = `−1`). The linking number
of the two components is the signed sum of these; it is the *only* channel through which the
linking magnitude enters the construction. -/
abbrev Crossing : Type := Bool

/-- The signed contribution of one crossing. -/
def crossingSign (c : Crossing) : ℤ := if c then 1 else -1

/-- The **linking number** of a frozen longitude word: the signed crossing sum. This is the sole
provenance of the return-map trace; nothing else in the geometry knows `k`. -/
def linkingNumber (cr : List Crossing) : ℤ := (cr.map crossingSign).sum

/-- The unlinked control: empty word, linking number `0`. -/
def unlinkWord : List Crossing := []

/-- The Hopf datum: one positive crossing, linking number `1` (the golden case). -/
def hopfWord : List Crossing := [true]

/-- The clasp datum: two positive crossings, linking number `2` (the silver case). -/
def claspWord : List Crossing := [true, true]

@[simp] theorem linkingNumber_unlink : linkingNumber unlinkWord = 0 := by
  simp [linkingNumber, unlinkWord]

@[simp] theorem linkingNumber_hopf : linkingNumber hopfWord = 1 := by
  simp [linkingNumber, hopfWord, crossingSign]

@[simp] theorem linkingNumber_clasp : linkingNumber claspWord = 2 := by
  simp [linkingNumber, claspWord, crossingSign]

/-! ## N1: the explicit cellular carrier (no golden data) -/

/-- **The graph boundary** of the two triangulated 8-tick cycles: rows are vertices
`(a₀,b₀,a₁,b₁)`, columns are edges `(e₀₀,e₀₁,e₁₀,e₁₁)`, entry = `∂(edge) = head − tail`. This is
the N1 complex; it carries **no** linking data and **no** golden data. -/
def boundary : Matrix (Fin 4) (Fin 4) ℤ :=
  !![(-1), 1, 0, 0;
      1, (-1), 0, 0;
      0, 0, (-1), 1;
      0, 0, 1, (-1)]

/-- The first meridian generator `μ₀` (fundamental cycle of component 0, `e₀₀ + e₀₁`). -/
def mer0 : Fin 4 → ℤ := ![1, 1, 0, 0]

/-- The second meridian generator `μ₁` (fundamental cycle of component 1, `e₁₀ + e₁₁`). -/
def mer1 : Fin 4 → ℤ := ![0, 0, 1, 1]

/-- **Kernel characterization (the real boundary content).** A 1-chain is a cycle iff its two
per-component edge coefficients agree: `x₁ = x₀ ∧ x₃ = x₂`. This is what makes `H₁ ≅ ℤ²` a genuine
computation rather than a posit. -/
theorem mem_ker_iff (x : Fin 4 → ℤ) :
    boundary.mulVec x = 0 ↔ (x 1 = x 0 ∧ x 3 = x 2) := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [boundary, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    -- h0 : -x0 + x1 = 0 (a₀ row), reconstruct both equalities
    -- We derive the pair from the a₀ and a₁ rows.
    have ha := congrFun h 0
    have hc := congrFun h 2
    simp [boundary, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one] at ha hc
    exact ⟨by omega, by omega⟩
  · rintro ⟨h01, h23⟩
    funext i
    fin_cases i <;>
      simp [boundary, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega

/-! ## H₁ ≅ ℤ²: the meridian lattice, derived from the kernel -/

/-- Assemble a cycle from meridian coordinates: `encode c = c₀·μ₀ + c₁·μ₁ = (c₀,c₀,c₁,c₁)`. -/
def encode (c : Fin 2 → ℤ) : Fin 4 → ℤ := ![c 0, c 0, c 1, c 1]

/-- Read meridian coordinates off a chain: `decode x = (x₀, x₂)`. -/
def decode (x : Fin 4 → ℤ) : Fin 2 → ℤ := ![x 0, x 2]

theorem encode_mem_ker (c : Fin 2 → ℤ) : boundary.mulVec (encode c) = 0 := by
  rw [mem_ker_iff]
  constructor <;> simp [encode]

@[simp] theorem decode_encode (c : Fin 2 → ℤ) : decode (encode c) = c := by
  funext i; fin_cases i <;> simp [decode, encode]

theorem encode_decode_of_mem_ker {x : Fin 4 → ℤ} (hx : boundary.mulVec x = 0) :
    encode (decode x) = x := by
  rw [mem_ker_iff] at hx
  obtain ⟨h01, h23⟩ := hx
  funext i; fin_cases i <;> simp [encode, decode] <;> omega

/-- **`H₁ ≅ ℤ²`, derived.** The cycle group `ker boundary` (the first homology of the carrier,
since there are no 2-cells) is linearly isomorphic to `ℤ²` via the meridian coordinates. The
inverse is `encode`; `mem_ker_iff` supplies the round-trip on cycles. -/
noncomputable def h1Equiv :
    (LinearMap.ker (Matrix.toLin' boundary)) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := decode x.1
  map_add' x y := by funext i; fin_cases i <;> simp [decode]
  map_smul' a x := by funext i; fin_cases i <;> simp [decode]
  invFun c := ⟨encode c, by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    exact encode_mem_ker c⟩
  left_inv x := by
    apply Subtype.ext
    have hx : boundary.mulVec x.1 = 0 := by
      have h := x.2
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at h
      exact h
    simpa using encode_decode_of_mem_ker hx
  right_inv c := by simp [decode_encode c]

/-! ## N2: the monodromy generators (no golden data, `k` sourced) -/

/-- **Component exchange**: the graph automorphism swapping component 0 ↔ 1
(`e₀ⱼ ↔ e₁ⱼ`, i.e. indices `0↔2`, `1↔3`). A genuine chain automorphism; induces the meridian
swap `μ₀ ↔ μ₁`. Contains no linking or golden data. -/
def exchange : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 1, 0;
      0, 0, 0, 1;
      1, 0, 0, 0;
      0, 1, 0, 0]

/-- The **shear block**: the fixed (`k`-free) geometry of the meridian transport. It adds a copy
of `μ₀` per unit of the `μ₁`-coefficient (column `2`). The linking magnitude is supplied
separately by `linkingNumber`. -/
def shearBlock : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 1, 0;
      0, 0, 1, 0;
      0, 0, 0, 0;
      0, 0, 0, 0]

/-- **Meridian transport by the linking number of `cr`**: `1 + (linkingNumber cr) • shearBlock`,
the `k`-fold Dehn twist dragging one meridian across the other. `k = linkingNumber cr` is the
signed crossing sum; the transport matrix is not otherwise hand-set. -/
def transport (cr : List Crossing) : Matrix (Fin 4) (Fin 4) ℤ :=
  1 + (linkingNumber cr) • shearBlock

/-- **The monodromy return map on the carrier**: go once around = transport then exchange. -/
def monodromy (cr : List Crossing) : Matrix (Fin 4) (Fin 4) ℤ :=
  exchange * transport cr

/-! ### The generators preserve cycles (so they descend to `H₁`) -/

theorem exchange_mem_ker {x : Fin 4 → ℤ} (hx : boundary.mulVec x = 0) :
    boundary.mulVec (exchange.mulVec x) = 0 := by
  rw [mem_ker_iff] at hx ⊢
  obtain ⟨h01, h23⟩ := hx
  refine ⟨?_, ?_⟩ <;>
    simp [exchange, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega

theorem transport_mem_ker (cr : List Crossing) {x : Fin 4 → ℤ}
    (hx : boundary.mulVec x = 0) :
    boundary.mulVec ((transport cr).mulVec x) = 0 := by
  rw [mem_ker_iff] at hx ⊢
  obtain ⟨h01, h23⟩ := hx
  refine ⟨?_, ?_⟩ <;>
    simp [transport, shearBlock,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega

theorem monodromy_mem_ker (cr : List Crossing) {x : Fin 4 → ℤ}
    (hx : boundary.mulVec x = 0) :
    boundary.mulVec ((monodromy cr).mulVec x) = 0 := by
  have : (monodromy cr).mulVec x = exchange.mulVec ((transport cr).mulVec x) := by
    simp [monodromy, Matrix.mulVec_mulVec]
  rw [this]
  exact exchange_mem_ker (transport_mem_ker cr hx)

/-! ## The keystone: the induced action on `H₁ ≅ ℤ²` is `returnMap k` -/

/-- **Transport acts as the shear `!![1,k;0,1]`.** In meridian coordinates,
`decode (transport cr · encode c) = (c₀ + k·c₁, c₁)`, i.e. `linkTransport k · c`. -/
theorem decode_transport_encode (cr : List Crossing) (c : Fin 2 → ℤ) :
    decode ((transport cr).mulVec (encode c))
      = (linkTransport (linkingNumber cr)).mulVec c := by
  funext i
  fin_cases i <;>
    simp [decode, encode, transport, shearBlock, linkTransport,
      Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Exchange acts as the swap `!![0,1;1,0]`.** In meridian coordinates,
`decode (exchange · encode c) = (c₁, c₀)`, i.e. `componentExchange · c`. -/
theorem decode_exchange_encode (c : Fin 2 → ℤ) :
    decode (exchange.mulVec (encode c)) = (componentExchange).mulVec c := by
  funext i
  fin_cases i <;>
    simp [decode, encode, exchange, componentExchange, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **THE KEYSTONE (N2).** Pushed through the meridian identification `H₁ ≅ ℤ²`, the carrier
monodromy `exchange ∘ transport(cr)` acts **exactly** as the banked `returnMap (linkingNumber cr)`:
`decode (monodromy cr · encode c) = returnMap (linkingNumber cr) · c`.

This is the front-end's payoff: the geometry induces `!![0,1;1,k]` with `k` the linking number,
with no golden assumption and `k` sourced from the crossing word. -/
theorem induced_eq (cr : List Crossing) (c : Fin 2 → ℤ) :
    decode ((monodromy cr).mulVec (encode c))
      = (returnMap (linkingNumber cr)).mulVec c := by
  have hmono : (monodromy cr).mulVec (encode c)
      = exchange.mulVec ((transport cr).mulVec (encode c)) := by
    simp [monodromy, Matrix.mulVec_mulVec]
  -- transport first (as a cycle), then exchange, matching returnMap = exchange * transport
  have hker : boundary.mulVec ((transport cr).mulVec (encode c)) = 0 :=
    transport_mem_ker cr (encode_mem_ker c)
  have htrans : encode (decode ((transport cr).mulVec (encode c)))
      = (transport cr).mulVec (encode c) := encode_decode_of_mem_ker hker
  calc
    decode ((monodromy cr).mulVec (encode c))
        = decode (exchange.mulVec ((transport cr).mulVec (encode c))) := by rw [hmono]
    _ = decode (exchange.mulVec (encode (decode ((transport cr).mulVec (encode c))))) := by
          rw [htrans]
    _ = (componentExchange).mulVec (decode ((transport cr).mulVec (encode c))) :=
          decode_exchange_encode _
    _ = (componentExchange).mulVec ((linkTransport (linkingNumber cr)).mulVec c) := by
          rw [decode_transport_encode]
    _ = (componentExchange * linkTransport (linkingNumber cr)).mulVec c := by
          rw [Matrix.mulVec_mulVec]
    _ = (returnMap (linkingNumber cr)).mulVec c := by rw [returnMap]

/-! ## Golden selection and the differential oracle -/

/-- **Golden ⟺ unit linking, on the carrier.** The induced monodromy is golden iff the frozen
word's linking number is `1` — routed through GR's `returnMap_golden_iff`. -/
theorem monodromy_golden_iff (cr : List Crossing) :
    GoldenRelation (returnMap (linkingNumber cr)) ↔ linkingNumber cr = 1 :=
  returnMap_golden_iff (linkingNumber cr)

/-- The induced trace on `H₁` **is** the linking number of the word. -/
theorem induced_trace (cr : List Crossing) :
    (returnMap (linkingNumber cr)).trace = linkingNumber cr :=
  returnMap_trace (linkingNumber cr)

/-- The induced determinant is the structural swap sign `−1`, for every word. -/
theorem induced_det (cr : List Crossing) :
    (returnMap (linkingNumber cr)).det = -1 :=
  returnMap_det (linkingNumber cr)

/-- **Oracle — unlink (`k = 0`).** Trace `0`, involution, **not** golden. -/
theorem oracle_unlink_trace : (returnMap (linkingNumber unlinkWord)).trace = 0 := by
  rw [induced_trace, linkingNumber_unlink]

theorem oracle_unlink_not_golden : ¬ GoldenRelation (returnMap (linkingNumber unlinkWord)) := by
  rw [monodromy_golden_iff, linkingNumber_unlink]; norm_num

/-- **Oracle — Hopf (`k = 1`).** Trace `1`, golden. -/
theorem oracle_hopf_trace : (returnMap (linkingNumber hopfWord)).trace = 1 := by
  rw [induced_trace, linkingNumber_hopf]

theorem oracle_hopf_golden : GoldenRelation (returnMap (linkingNumber hopfWord)) := by
  rw [monodromy_golden_iff, linkingNumber_hopf]

/-- **Oracle — clasp (`k = 2`).** Trace `2`, silver, **not** golden. -/
theorem oracle_clasp_trace : (returnMap (linkingNumber claspWord)).trace = 2 := by
  rw [induced_trace, linkingNumber_clasp]

theorem oracle_clasp_not_golden : ¬ GoldenRelation (returnMap (linkingNumber claspWord)) := by
  rw [monodromy_golden_iff, linkingNumber_clasp]; norm_num

/-! ## Certificate bundling N1/N2 -/

/-- THEOREM-grade certificate for the **topological front-end** (N1/N2): an explicit cellular
carrier with computed `H₁ ≅ ℤ²` (not posited), a monodromy whose induced action on `H₁` is the
banked `returnMap (linkingNumber cr)` with the linking number sourced from frozen crossing data,
golden exactly at unit linking, and a differential oracle (`0/1/2` at unlink/Hopf/clasp).

Explicitly a **MODEL premise** (not asserted here as THEOREM): that the finite carrier *is* the
link complement of the two forced 8-tick cycles. -/
structure MonodromyCarrierCert : Prop where
  /-- `H₁` of the carrier is `ℤ²`, derived as a kernel (not posited). -/
  h1_iso_z2 : Nonempty ((LinearMap.ker (Matrix.toLin' boundary)) ≃ₗ[ℤ] (Fin 2 → ℤ))
  /-- The monodromy preserves cycles (descends to `H₁`). -/
  descends : ∀ (cr : List Crossing) {x : Fin 4 → ℤ},
    boundary.mulVec x = 0 → boundary.mulVec ((monodromy cr).mulVec x) = 0
  /-- The induced action on `H₁ ≅ ℤ²` is exactly `returnMap (linkingNumber cr)`. -/
  induced_is_returnMap : ∀ (cr : List Crossing) (c : Fin 2 → ℤ),
    decode ((monodromy cr).mulVec (encode c)) = (returnMap (linkingNumber cr)).mulVec c
  /-- Golden iff unit linking. -/
  golden_iff_unit : ∀ (cr : List Crossing),
    GoldenRelation (returnMap (linkingNumber cr)) ↔ linkingNumber cr = 1
  /-- Differential: unlink is not golden, Hopf is golden, clasp is not golden. -/
  differential : (¬ GoldenRelation (returnMap (linkingNumber unlinkWord)))
    ∧ GoldenRelation (returnMap (linkingNumber hopfWord))
    ∧ (¬ GoldenRelation (returnMap (linkingNumber claspWord)))

theorem monodromyCarrierCert_holds : MonodromyCarrierCert where
  h1_iso_z2 := ⟨h1Equiv⟩
  descends := fun cr {_x} hx => monodromy_mem_ker cr hx
  induced_is_returnMap := induced_eq
  golden_iff_unit := monodromy_golden_iff
  differential := ⟨oracle_unlink_not_golden, oracle_hopf_golden, oracle_clasp_not_golden⟩

end GoldenMonodromyCarrier
end Masses
end IndisputableMonolith
