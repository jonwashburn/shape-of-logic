import Mathlib
import IndisputableMonolith.Masses.GoldenCarrierAMT

/-!
# GDB Stage 4c: the peripheral inclusion of the boundary torus (link-complement marking)

`GoldenCarrierAMT` (GDB4b) banked the carrier **algebraic mapping torus** as an explicit `4/8/4`
integer chain complex with the **link-complement homology** `H₀ ≅ ℤ`, `H₁ ≅ ℤ`, `H₂ = 0` (the
fiber `ℤ²` collapses because `returnMap 1 − 1` is unimodular). This module builds the **peripheral
system**: the real boundary 2-torus complex `T` and an honest chain map `ι : T → AMT` modeling the
inclusion of the boundary torus of the link complement, and shows the meridian marking descends
along `ι` onto the surviving golden `H₁` generator.

## The obstruction that reshaped this stage (recorded honestly)

The Stage-4c ask was originally written as a **chain homotopy equivalence** `AMT ≃ T` to the
"peripheral torus where the meridian marking lives". That object **cannot exist**. A chain homotopy
equivalence induces isomorphisms on homology, so it would force `H₁(AMT) ≅ H₁(T)`. But the AMT has
`H₁ ≅ ℤ` (`GoldenCarrierAMT.h1Equiv`), while a genuine boundary 2-torus has `H₁ ≅ ℤ²` (meridian `μ`
and longitude `λ`). `ℤ ≇ ℤ²` (different rank). The two facts are exposed side by side below
(`torus_all_cycles`/`torus_no_boundaries` give `H₁(T) = ℤ²`; the AMT equiv gives `H₁(AMT) = ℤ`), so
the impossibility is self-documenting.

The faithful object is therefore the **peripheral INCLUSION**, not an equivalence: the boundary
torus of a link complement is not homotopy equivalent to the complement, it *includes* into it, and
that inclusion is exactly the peripheral system that carries the meridian/longitude marking.

## The peripheral torus complex `T` (1/2/1)

* `C₀ᵀ = ℤ` (one 0-cell), `C₁ᵀ = ℤ²` (two 1-cells: meridian `μ`, longitude `λ`),
  `C₂ᵀ = ℤ` (one 2-cell attached by the commutator `μλμ⁻¹λ⁻¹`, so its abelianized boundary is `0`).
* Both differentials are `0` (`dT1`, `dT2`), so the homology is the chains: `H₀ᵀ = ℤ`, `H₁ᵀ = ℤ²`,
  `H₂ᵀ = ℤ` — the standard homology of the 2-torus.

## The chain map `ι : T → AMT` and the marking descent

* `ι₂ : ℤ → ℤ⁴` is **forced to `0`**: chain-map commutation `d₂ · ι₂ = ι₁ · dT2 = 0` with `d₂`
  injective (`GoldenCarrierAMT.d2_injective`) means `ι₂ = 0`. Topologically: the torus 2-class dies
  in the complement (`H₂(AMT) = 0`). This is genuine content, not a relabeling.
* `ι₁ : ℤ² → ℤ⁸` sends the meridian `μ = (1,0)` to the cycle `g = (1,0,1,0,0,0,0,0)` with
  `ψ(g) = 1` (the surviving golden `H₁` generator), and the longitude `λ = (0,1)` to `d₂·e₀ ∈ im d₂`
  (nullhomologous in the complement). So on `H₁` the induced map `ℤ² → ℤ` is `μ ↦ 1`, `λ ↦ 0`: the
  meridian marking descends onto the golden generator and the longitude collapses. This 2→1 rank
  drop is the real content.
* `ι₀ : ℤ → ℤ⁴` sends the vertex to `e₀` (augmentation `1`, both spaces connected).

## Anti-vacuity

`ι` is NOT an isomorphism and NOT a relabeling: `ι₁` has kernel on `H₁` (the longitude), `ι₂ = 0`,
and the source `T` genuinely has `H₁ = ℤ²`, `H₂ = ℤ` while the target has `H₁ = ℤ`, `H₂ = 0`. The
rank drop `1/2/1 → (H = 1,1,0)` is real and carried by proved facts, never by `sorry`.
-/

namespace IndisputableMonolith
namespace Masses
namespace GoldenCarrierPeripheral

open Matrix
open IndisputableMonolith.Masses.GoldenCarrierAMT

/-! ## The peripheral 2-torus complex `T` (differentials are zero) -/

/-- `dT1 : C₁ᵀ = ℤ² → C₀ᵀ = ℤ`, the 1-skeleton boundary of the torus: both loops are cycles, so
this is the zero map. -/
def dT1 : Matrix (Fin 1) (Fin 2) ℤ := 0

/-- `dT2 : C₂ᵀ = ℤ → C₁ᵀ = ℤ²`, the 2-cell boundary. The 2-cell attaches by the commutator
`μλμ⁻¹λ⁻¹`, whose abelianization is `0`, so this is the zero map. -/
def dT2 : Matrix (Fin 2) (Fin 1) ℤ := 0

/-- `T` is a chain complex: `dT1 · dT2 = 0` (trivially, both are zero). -/
theorem dT1_mul_dT2 : dT1 * dT2 = 0 := by simp [dT1]

/-- **Every torus 1-chain is a cycle** (`ker dT1 = ⊤`), because `dT1 = 0`. -/
theorem torus_all_cycles : LinearMap.ker (Matrix.toLin' dT1) = ⊤ := by
  rw [dT1, map_zero, LinearMap.ker_zero]

/-- **No torus 1-chain is a boundary** (`im dT2 = ⊥`), because `dT2 = 0`. Together with
`torus_all_cycles` this gives `H₁(T) = ker dT1 / im dT2 = ℤ² / 0 = ℤ²`: the boundary torus has
`H₁ ≅ ℤ²`, which is exactly why no equivalence to the `H₁ = ℤ` AMT can exist. -/
theorem torus_no_boundaries : LinearMap.range (Matrix.toLin' dT2) = ⊥ := by
  rw [dT2, map_zero, LinearMap.range_zero]

/-! ## The chain map `ι : T → AMT` -/

/-- `ι₀ : C₀ᵀ = ℤ → C₀ = ℤ⁴`, the vertex inclusion (to `e₀`). -/
def iota0 : Matrix (Fin 4) (Fin 1) ℤ :=
  !![1; 0; 0; 0]

/-- `ι₁ : C₁ᵀ = ℤ² → C₁ = ℤ⁸`. Column `0` (meridian `μ`) is the surviving golden cycle
`g = (1,0,1,0,0,0,0,0)` with `ψ(g) = 1`; column `1` (longitude `λ`) is `d₂·e₀`, a nonzero cycle
lying in `im d₂` (nullhomologous in the complement). -/
def iota1 : Matrix (Fin 8) (Fin 2) ℤ :=
  !![1, 1;
      0, (-1);
      1, 0;
      0, 0;
      0, (-1);
      0, 0;
      0, 1;
      0, 0]

/-- `ι₂ : C₂ᵀ = ℤ → C₂ = ℤ⁴` is **forced to zero** by chain-map commutation with `d₂` injective;
the torus 2-class dies in the complement (`H₂(AMT) = 0`). -/
def iota2 : Matrix (Fin 4) (Fin 1) ℤ := 0

/-! ## `ι` is a chain map -/

/-- **`d₁ · ι₁ = 0`.** Both columns of `ι₁` are AMT 1-cycles (`g` by construction; `d₂·e₀ ∈ im d₂`
and `d₁·d₂ = 0`). Combined with `dT1 = 0` this is the degree-`1` chain-map square. -/
theorem d1_mul_iota1 : d1 * iota1 = 0 := by decide

/-- **Degree-1 chain-map square** `d₁ · ι₁ = ι₀ · dT1`. -/
theorem chain_square_10 : d1 * iota1 = iota0 * dT1 := by
  rw [dT1, Matrix.mul_zero, d1_mul_iota1]

/-- **Degree-2 chain-map square** `d₂ · ι₂ = ι₁ · dT2` (both sides zero: `ι₂ = 0`, `dT2 = 0`). -/
theorem chain_square_21 : d2 * iota2 = iota1 * dT2 := by
  simp [iota2, dT2]

/-- **`ι₂` is forced to be zero.** Chain-map commutation forces `d₂ · ι₂ = ι₁ · dT2 = 0`, and `d₂`
is injective (`GoldenCarrierAMT.d2_injective`), so any chain map has `ι₂ = 0`. The torus 2-class has
nowhere to go: `H₂(AMT) = 0`. -/
theorem iota2_forced_zero
    (φ2 : Matrix (Fin 4) (Fin 1) ℤ) (hφ : d2 * φ2 = iota1 * dT2) :
    φ2 = 0 := by
  have hcol : d2 * φ2 = 0 := by rw [hφ, dT2, Matrix.mul_zero]
  -- each column of φ2 is killed by T2, and T2 is injective
  funext i j
  have h0 : T2 (fun k => φ2 k j) = 0 := by
    rw [T2_apply]
    funext r
    have := congrArg (fun M => M r j) hcol
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hz : (fun k => φ2 k j) = 0 :=
    d2_injective (h0.trans (map_zero T2).symm)
  simpa using congrFun hz i

/-! ## The meridian marking descends onto the golden `H₁` generator -/

/-- The meridian image `ι₁·μ` (with `μ = (1,0)`) is the cycle `g = (1,0,1,0,0,0,0,0)`. -/
theorem iota1_meridian : iota1.mulVec ![1, 0] = ![1, 0, 1, 0, 0, 0, 0, 0] := by
  decide

/-- The longitude image `ι₁·λ` (with `λ = (0,1)`) equals `d₂·e₀`, hence lies in `im d₂`. -/
theorem iota1_longitude_eq_d2 : iota1.mulVec ![0, 1] = d2.mulVec ![1, 0, 0, 0] := by
  decide

/-- The meridian image is an AMT **1-cycle** (`d₁ · (ι₁·μ) = 0`). -/
theorem meridian_is_cycle : d1.mulVec (iota1.mulVec ![1, 0]) = 0 := by
  rw [Matrix.mulVec_mulVec, d1_mul_iota1, Matrix.zero_mulVec]

/-- The meridian image, packaged as an element of the AMT cycle module `K = ker d₁`. -/
noncomputable def meridianCycle : K :=
  ⟨iota1.mulVec ![1, 0], by
    simp only [K, LinearMap.mem_ker, T1_apply]
    exact meridian_is_cycle⟩

/-- **THE MARKING DESCENT (meridian).** The meridian class maps to the **surviving golden
generator** of `H₁(AMT) ≅ ℤ`: `ψ(ι₁·μ) = 1`. Since `h1Equiv` is `ψ` pushed through the quotient,
this says `[ι₁·μ]` generates `H₁(AMT)`. -/
theorem meridian_maps_to_generator : psi meridianCycle = 1 := by
  rw [psi_apply]
  show (meridianCycle : Fin 8 → ℤ) 0 + (meridianCycle : Fin 8 → ℤ) 1 = 1
  simp only [meridianCycle, iota1_meridian]
  decide

/-- **THE MARKING DESCENT (longitude).** The longitude class is **nullhomologous** in the complement:
`ι₁·λ ∈ im d₂`, so `[ι₁·λ] = 0` in `H₁(AMT)`. This is the peripheral fact that the longitude bounds
in a link complement while the meridian survives. -/
theorem longitude_nullhomologous : iota1.mulVec ![0, 1] ∈ LinearMap.range T2 := by
  refine ⟨![1, 0, 0, 0], ?_⟩
  rw [T2_apply, ← iota1_longitude_eq_d2]

/-- The longitude image is itself a **nonzero** 1-cycle (it is `d₂·e₀`, and `d₂` is injective so
`d₂·e₀ ≠ 0`), so the descent is a genuine `ℤ² → ℤ` collapse `λ ↦ 0`, not a vacuous `λ = 0`. -/
theorem longitude_image_ne_zero : iota1.mulVec ![0, 1] ≠ 0 := by
  decide

/-! ## Certificate -/

/-- THEOREM-grade certificate for the **peripheral inclusion** of the boundary torus into the
carrier link complement (GDB Stage 4c, honest reformulation). It bundles:

* the real boundary-torus complex `T` (`H₁(T) = ℤ²` via `torus_all_cycles`/`torus_no_boundaries`),
  exhibiting the `ℤ²`-vs-`ℤ` homology obstruction that rules out any chain homotopy equivalence to
  the `H₁ = ℤ` AMT;
* an honest chain map `ι : T → AMT` (`chain_square_10`, `chain_square_21`);
* `ι₂` **forced to zero** by `d₂` injective (`iota2_forced_zero`): the torus 2-class dies,
  `H₂(AMT) = 0`;
* the **meridian marking descent**: `μ ↦` the surviving golden generator (`ψ = 1`), `λ ↦ 0`
  (nullhomologous), with the longitude image a genuine nonzero cycle collapsing into `im d₂`.

This carries the golden monodromy's `H₁` action onto the meridian marking exactly where it
truthfully lives (the peripheral torus of the link complement), by the topologically faithful
INCLUSION rather than a nonexistent equivalence. -/
structure GoldenCarrierPeripheralCert : Prop where
  /-- `T` is a chain complex. -/
  torus_is_complex : dT1 * dT2 = 0
  /-- `H₁(T)` has rank 2 (`ℤ²`): every 1-chain is a cycle. -/
  torus_h1_cycles : LinearMap.ker (Matrix.toLin' dT1) = ⊤
  /-- `H₁(T)` has rank 2 (`ℤ²`): no 1-chain is a boundary. -/
  torus_h1_no_boundaries : LinearMap.range (Matrix.toLin' dT2) = ⊥
  /-- The AMT target has `H₁ ≅ ℤ` (from GDB4b), so `ℤ² ≇ ℤ`: the equivalence is impossible and the
  faithful object is the inclusion. -/
  amt_h1_iso_z : Nonempty ((K ⧸ LinearMap.range T2') ≃ₗ[ℤ] ℤ)
  /-- `ι` is a chain map (degree-1 square). -/
  chain_map_10 : d1 * iota1 = iota0 * dT1
  /-- `ι` is a chain map (degree-2 square). -/
  chain_map_21 : d2 * iota2 = iota1 * dT2
  /-- `ι₂` is forced to zero by `d₂` injective: the torus 2-class dies (`H₂(AMT) = 0`). -/
  h2_dies : ∀ φ2 : Matrix (Fin 4) (Fin 1) ℤ, d2 * φ2 = iota1 * dT2 → φ2 = 0
  /-- Meridian ↦ surviving golden generator of `H₁(AMT)`. -/
  meridian_to_generator : psi meridianCycle = 1
  /-- Longitude ↦ `0` in `H₁(AMT)` (nullhomologous). -/
  longitude_null : iota1.mulVec ![0, 1] ∈ LinearMap.range T2
  /-- The longitude image is a genuine nonzero cycle (real `ℤ² → ℤ` collapse, not vacuous). -/
  longitude_nonzero : iota1.mulVec ![0, 1] ≠ 0

theorem goldenCarrierPeripheralCert_holds : GoldenCarrierPeripheralCert where
  torus_is_complex := dT1_mul_dT2
  torus_h1_cycles := torus_all_cycles
  torus_h1_no_boundaries := torus_no_boundaries
  amt_h1_iso_z := ⟨h1Equiv⟩
  chain_map_10 := chain_square_10
  chain_map_21 := chain_square_21
  h2_dies := iota2_forced_zero
  meridian_to_generator := meridian_maps_to_generator
  longitude_null := longitude_nullhomologous
  longitude_nonzero := longitude_image_ne_zero

end GoldenCarrierPeripheral
end Masses
end IndisputableMonolith
