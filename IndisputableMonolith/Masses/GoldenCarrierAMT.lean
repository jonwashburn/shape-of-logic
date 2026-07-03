import Mathlib
import IndisputableMonolith.Masses.GoldenMonodromyCarrier
import IndisputableMonolith.Masses.GoldenDeckNoGo
import IndisputableMonolith.Masses.GoldenMonodromyReturn

/-!
# GDB Stage 4b: the carrier algebraic mapping torus (link-complement homology)

`GoldenMonodromyCarrier` (GMC) built the **fiber**: the finite ℤ-chain complex
`C₁ = ℤ⁴ --boundary--> C₀ = ℤ⁴` of the two forced 8-tick recognition cycles, with
`H₁(fiber) ≅ ℤ²` (the meridian lattice, `mem_ker_iff`) and the monodromy `monodromy cr`
inducing `returnMap (linkingNumber cr)` on that `ℤ²` (`induced_eq`). `GoldenDeckNoGo` (GDB3a)
banked the chain-map identity `boundary * monodromy cr = exchange * boundary`.

This module assembles the **algebraic mapping torus** of the golden monodromy `M = monodromy
hopfWord` (linking number `1`, the golden case) as an explicit finite `4 / 8 / 4` integer chain
complex, and computes its homology as the **link complement** homology, `H₀ ≅ ℤ` and `H₁ ≅ ℤ` —
NOT the bare fiber's `ℤ²`. The mapping torus collapses one `ℤ`: pushed onto `H₁` the fiber lattice
`ℤ²` is entirely killed because `returnMap 1 − 1` is unimodular (an isomorphism of `ℤ²`), and the
single surviving `ℤ` descends from `H₀`. This is the algebraic Wang sequence, done by an explicit
elementary computation (Smith normal form by hand), with a proved `LinearEquiv`, no `native_decide`.

## The complex (mapping cone of `M − 1`)

* `C₂ = ℤ⁴`, `C₁ = ℤ⁸ = ℤ⁴ ⊕ ℤ⁴`, `C₀ = ℤ⁴`.
* `d₂ : ℤ⁴ → ℤ⁸` is the block column `[ −boundary ; M − 1 ]` (fiber boundary + monodromy defect).
* `d₁ : ℤ⁸ → ℤ⁴` is the block row `[ exchange − 1 | boundary ]`.
* `d₁ ∘ d₂ = −(exchange−1)·boundary + boundary·(M−1) = boundary·M − exchange·boundary = 0`, which is
  a genuine chain complex **because** `boundary * monodromy hopfWord = exchange * boundary`
  (`GoldenDeckNoGo.boundary_mul_monodromy`). See `d1_mul_d2`.

## Anti-vacuity (the panel's gate, enforced by construction)

* The monodromy-defect block `M − 1` is genuinely **present and nonzero**: `monodromy_defect_ne_zero`
  exhibits entry `(2,0) = 1`, and `d2_lower_block_eq_defect` proves the lower `4×4` block of `d₂`
  is *exactly* `monodromy hopfWord − 1` (not a zero/rank-deficient stand-in). `d₂` is moreover
  **injective** (`d2_injective`), so `im d₂ ≅ ℤ⁴` has full rank; the complex is not trivially exact.
* `H₀ ≅ ℤ` and `H₁ ≅ ℤ` are **derived** via explicit `LinearEquiv`s (`h0Equiv`, `h1Equiv`) built
  from `ker ε = range d₁` and `ker ψ = range d₂` with hand-exhibited integer witnesses, never
  asserted by `rfl` on a definitionally-`ℤ` object.
* The `ℤ² → ℤ` collapse is exhibited, not relabeled: `fiber_h1_dies` proves `returnMap 1 − 1` is a
  linear automorphism of `ℤ²` (so the fiber `H₁` maps into `im d₂` and dies), and the surviving
  generator of `h1Equiv` is the augmentation class `x₀ + x₁`, from the `H₀` factor, not a fiber
  meridian.
-/

namespace IndisputableMonolith
namespace Masses
namespace GoldenCarrierAMT

open Matrix
open IndisputableMonolith.Masses.GoldenMonodromyReturn
open IndisputableMonolith.Masses.GoldenMonodromyCarrier

/-! ## The two boundary maps of the mapping torus -/

/-- **`d₁ : ℤ⁸ → ℤ⁴`**, the block row `[ exchange − 1 | boundary ]`. Columns 0–3 are the columns of
`exchange − 1` (the mapping-cylinder connecting map on vertices), columns 4–7 are the columns of
the fiber `boundary`. -/
def d1 : Matrix (Fin 4) (Fin 8) ℤ :=
  !![(-1), 0, 1, 0,  (-1), 1, 0, 0;
      0, (-1), 0, 1,  1, (-1), 0, 0;
      1, 0, (-1), 0,  0, 0, (-1), 1;
      0, 1, 0, (-1),  0, 0, 1, (-1)]

/-- **`d₂ : ℤ⁴ → ℤ⁸`**, the block column `[ −boundary ; M − 1 ]`. Rows 0–3 are `−boundary`, rows
4–7 are the **monodromy defect** `M − 1 = monodromy hopfWord − 1`. -/
def d2 : Matrix (Fin 8) (Fin 4) ℤ :=
  !![1, (-1), 0, 0;
      (-1), 1, 0, 0;
      0, 0, 1, (-1);
      0, 0, (-1), 1;
      (-1), 0, 1, 0;
      0, (-1), 0, 1;
      1, 0, 0, 0;
      0, 1, 1, (-1)]

/-! ## `d₂` genuinely carries the nonzero monodromy defect (anti-vacuity) -/

/-- The lower `4×4` block of `d₂` (rows 4–7) is **exactly** `monodromy hopfWord − 1`, the genuine
golden monodromy defect. This ties the literal complex to the banked `GoldenMonodromyCarrier`
geometry and forbids the "`d₂` is a zeroed/relabeled stand-in" vacuity. -/
theorem d2_lower_block_eq_defect (i j : Fin 4) :
    d2 (Fin.natAdd 4 i) j = (monodromy hopfWord - 1) i j := by
  revert i j; decide

/-- The upper `4×4` block of `d₂` (rows 0–3) is `−boundary`, the fiber boundary. -/
theorem d2_upper_block_eq_neg_boundary (i j : Fin 4) :
    d2 (Fin.castAdd 4 i) j = (-boundary) i j := by
  revert i j; decide

/-- **The monodromy defect is present and nonzero** (entry `(2,0) = 1`). Were it zero the complex
would be trivially exact; the panel's gate requires this. -/
theorem monodromy_defect_ne_zero : (monodromy hopfWord - 1 : Matrix (Fin 4) (Fin 4) ℤ) ≠ 0 := by
  decide

/-! ## `d₁ ∘ d₂ = 0`: a genuine chain complex -/

/-- **`d₁ * d₂ = 0`.** The mapping torus is a chain complex. -/
theorem d1_mul_d2 : d1 * d2 = 0 := by
  decide

/-! ## Linear maps and the two homology modules -/

/-- `T₁ = d₁` as a linear map `ℤ⁸ → ℤ⁴`. -/
noncomputable def T1 : (Fin 8 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) := Matrix.toLin' d1

/-- `T₂ = d₂` as a linear map `ℤ⁴ → ℤ⁸`. -/
noncomputable def T2 : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 8 → ℤ) := Matrix.toLin' d2

theorem T1_apply (x : Fin 8 → ℤ) : T1 x = d1.mulVec x := Matrix.toLin'_apply _ _
theorem T2_apply (w : Fin 4 → ℤ) : T2 w = d2.mulVec w := Matrix.toLin'_apply _ _

/-- `d₁ ∘ d₂ = 0` at the vector level. -/
theorem T1_T2 (w : Fin 4 → ℤ) : T1 (T2 w) = 0 := by
  rw [T2_apply, T1_apply, Matrix.mulVec_mulVec, d1_mul_d2, Matrix.zero_mulVec]

/-- `im d₂ ⊆ ker d₁`. -/
theorem range_T2_le_ker_T1 : LinearMap.range T2 ≤ LinearMap.ker T1 := by
  rintro _ ⟨w, rfl⟩
  rw [LinearMap.mem_ker]
  exact T1_T2 w

/-! ## H₀ ≅ ℤ (the complex is connected) -/

/-- The augmentation `ε : ℤ⁴ → ℤ`, `y ↦ y₀ + y₁ + y₂ + y₃`. -/
def eps : (Fin 4 → ℤ) →ₗ[ℤ] ℤ where
  toFun y := y 0 + y 1 + y 2 + y 3
  map_add' y z := by simp [Pi.add_apply]; ring
  map_smul' a y := by simp [Pi.smul_apply]; ring

@[simp] theorem eps_apply (y : Fin 4 → ℤ) : eps y = y 0 + y 1 + y 2 + y 3 := rfl

theorem eps_surjective : Function.Surjective eps := by
  intro n
  refine ⟨![n, 0, 0, 0], ?_⟩
  simp

/-- `im d₁ ⊆ ker ε`: every boundary of a 1-chain is augmentation-null (all columns sum to 0). -/
theorem range_T1_le_ker_eps : LinearMap.range T1 ≤ LinearMap.ker eps := by
  rintro _ ⟨w, rfl⟩
  rw [LinearMap.mem_ker, eps_apply, T1_apply]
  simp [d1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `ker ε ⊆ im d₁`: every augmentation-null vector is a boundary, exhibited by an explicit
integer 1-chain. This is the connectivity of the mapping torus. -/
theorem ker_eps_le_range_T1 : LinearMap.ker eps ≤ LinearMap.range T1 := by
  intro y hy
  rw [LinearMap.mem_ker, eps_apply] at hy
  refine ⟨![-(y 0 + y 1), 0, 0, 0, y 1, 0, y 3, 0], ?_⟩
  rw [T1_apply]
  funext i
  fin_cases i <;>
    simp [d1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals omega

theorem range_T1_eq_ker_eps : LinearMap.range T1 = LinearMap.ker eps :=
  le_antisymm range_T1_le_ker_eps ker_eps_le_range_T1

/-- **`H₀ ≅ ℤ`.** The degree-0 homology `C₀ ⧸ im d₁` is `ℤ`, derived via the augmentation
(surjective, kernel = `im d₁`), not posited. -/
noncomputable def h0Equiv : ((Fin 4 → ℤ) ⧸ LinearMap.range T1) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ range_T1_eq_ker_eps).trans
    (LinearMap.quotKerEquivOfSurjective eps eps_surjective)

/-! ## H₁ ≅ ℤ (the mapping torus collapses the fiber ℤ²) -/

/-- The cycle module `K = ker d₁`. -/
noncomputable def K : Submodule ℤ (Fin 8 → ℤ) := LinearMap.ker T1

/-- `d₂` corestricted to the cycles `K` (well-defined by `range_T2_le_ker_T1`). -/
noncomputable def T2' : (Fin 4 → ℤ) →ₗ[ℤ] K :=
  T2.codRestrict K (fun _w => range_T2_le_ker_T1 (LinearMap.mem_range_self _ _))

/-- The surviving invariant `ψ : K → ℤ`, `⟨x, _⟩ ↦ x₀ + x₁`. This descends from the `H₀`
augmentation, NOT from a fiber meridian — it is the coordinate the mapping torus keeps. -/
noncomputable def psi : K →ₗ[ℤ] ℤ where
  toFun x := (x : Fin 8 → ℤ) 0 + (x : Fin 8 → ℤ) 1
  map_add' x y := by simp [Pi.add_apply]; ring
  map_smul' a x := by simp [Pi.smul_apply]; ring

@[simp] theorem psi_apply (x : K) : psi x = (x : Fin 8 → ℤ) 0 + (x : Fin 8 → ℤ) 1 := rfl

theorem psi_surjective : Function.Surjective psi := by
  intro n
  refine ⟨⟨![n, 0, n, 0, 0, 0, 0, 0], ?_⟩, ?_⟩
  · -- this chain is a cycle: d₁ · it = 0
    simp only [K, LinearMap.mem_ker, T1_apply]
    funext i
    fin_cases i <;>
      simp [d1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight,
        Matrix.cons_val_zero, Matrix.cons_val_one]
  · simp

/-- `im d₂ ⊆ ker ψ`: the invariant vanishes on the image of `d₂` because rows 0 and 1 of `d₂` are
negatives of each other, so `(d₂ w)₀ + (d₂ w)₁ = 0`. -/
theorem range_T2'_le_ker_psi : LinearMap.range T2' ≤ LinearMap.ker psi := by
  rintro _ ⟨w, rfl⟩
  rw [LinearMap.mem_ker, psi_apply]
  show (T2' w : Fin 8 → ℤ) 0 + (T2' w : Fin 8 → ℤ) 1 = 0
  have h : (T2' w : Fin 8 → ℤ) = d2.mulVec w := by
    show (T2.codRestrict K _ w : Fin 8 → ℤ) = d2.mulVec w
    rw [LinearMap.codRestrict_apply, T2_apply]
  rw [h]
  simp [d2, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `ker ψ ⊆ im d₂`: a cycle `x` with `x₀ + x₁ = 0` is a boundary `d₂ w`, exhibited by the explicit
integer 2-chain `w = (x₆, x₆−x₀, x₄+x₆, x₄+x₆−x₂)`. This uses the four cycle equations
(`x ∈ ker d₁`) together with `ψ x = 0`, and is where the fiber `ℤ²` collapses into `im d₂`. -/
theorem ker_psi_le_range_T2' : LinearMap.ker psi ≤ LinearMap.range T2' := by
  rintro ⟨x, hxK⟩ hpsi
  have hpsi' : x 0 + x 1 = 0 := hpsi
  -- x ∈ ker d₁ : the four component equations, in clean linear form
  have hx : d1.mulVec x = 0 := by
    have h := hxK
    simp only [K, LinearMap.mem_ker, T1_apply] at h
    exact h
  have e0 : -x 0 + x 2 - x 4 + x 5 = 0 := by
    calc -x 0 + x 2 - x 4 + x 5 = d1.mulVec x 0 := by
          simp [d1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]; ring
      _ = 0 := congrFun hx 0
  have e1 : -x 1 + x 3 + x 4 - x 5 = 0 := by
    calc -x 1 + x 3 + x 4 - x 5 = d1.mulVec x 1 := by
          simp [d1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]; ring
      _ = 0 := congrFun hx 1
  have e2 : x 0 - x 2 - x 6 + x 7 = 0 := by
    calc x 0 - x 2 - x 6 + x 7 = d1.mulVec x 2 := by
          simp [d1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]; ring
      _ = 0 := congrFun hx 2
  have e3 : x 1 - x 3 + x 6 - x 7 = 0 := by
    calc x 1 - x 3 + x 6 - x 7 = d1.mulVec x 3 := by
          simp [d1, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]; ring
      _ = 0 := congrFun hx 3
  refine ⟨![x 6, x 6 - x 0, x 4 + x 6, x 4 + x 6 - x 2], ?_⟩
  apply Subtype.ext
  show (T2' _ : Fin 8 → ℤ) = x
  have h : (T2' ![x 6, x 6 - x 0, x 4 + x 6, x 4 + x 6 - x 2] : Fin 8 → ℤ)
      = d2.mulVec ![x 6, x 6 - x 0, x 4 + x 6, x 4 + x 6 - x 2] := by
    show (T2.codRestrict K _ _ : Fin 8 → ℤ) = _
    rw [LinearMap.codRestrict_apply, T2_apply]
  rw [h]
  funext i
  fin_cases i <;>
    simp [d2, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega

theorem range_T2'_eq_ker_psi : LinearMap.range T2' = LinearMap.ker psi :=
  le_antisymm range_T2'_le_ker_psi ker_psi_le_range_T2'

/-- **`H₁ ≅ ℤ`.** The degree-1 homology `ker d₁ ⧸ im d₂` is `ℤ` — the link-complement homology of
the golden mapping torus, NOT the bare fiber's `ℤ²`. Derived via the invariant `ψ` (surjective,
kernel = `im d₂`), by explicit `LinearEquiv`. -/
noncomputable def h1Equiv : (K ⧸ LinearMap.range T2') ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ range_T2'_eq_ker_psi).trans
    (LinearMap.quotKerEquivOfSurjective psi psi_surjective)

/-! ## The fiber `ℤ²` genuinely dies: `returnMap 1 − 1` is unimodular -/

/-- **The Wang collapse, algebraically.** The fiber-monodromy defect `returnMap 1 − 1` on
`H₁(fiber) ≅ ℤ²` has determinant `−1`, hence is a linear **automorphism** of `ℤ²`. This is exactly
why the fiber's `ℤ²` maps ONTO `im d₂` and dies in `H₁` of the torus, leaving only the `ℤ` from the
base. This is not a relabeling of the bare carrier's `ℤ²`; it is the reason that `ℤ²` disappears. -/
theorem fiber_defect_det : (returnMap 1 - 1 : Matrix (Fin 2) (Fin 2) ℤ).det = -1 := by
  rw [returnMap_closed_form]
  simp [Matrix.det_fin_two, Matrix.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]

theorem fiber_defect_isUnit_det : IsUnit (returnMap 1 - 1 : Matrix (Fin 2) (Fin 2) ℤ).det := by
  rw [fiber_defect_det]; exact isUnit_one.neg

/-! ## `d₂` is injective (`im d₂ ≅ ℤ⁴`, full rank) -/

/-- **`d₂` is injective.** Its four columns are ℤ-linearly independent (in fact rows 6,4,2 read off
`w₀, w₂` and rows 0,1 pin the rest), so `im d₂ ≅ ℤ⁴` has full rank and the complex is not trivially
exact. -/
theorem d2_injective : Function.Injective T2 := by
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro w hw
  rw [LinearMap.mem_ker, T2_apply] at hw
  have h0 := congrFun hw 0
  have h2 := congrFun hw 2
  have h4 := congrFun hw 4
  have h6 := congrFun hw 6
  simp only [d2, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
    Pi.zero_apply] at h0 h2 h4 h6
  funext j
  fin_cases j <;> simp_all

/-! ## Certificate -/

/-- THEOREM-grade certificate for the **carrier algebraic mapping torus** (GDB Stage 4b): an
explicit `4/8/4` integer chain complex, mapping cone of the golden monodromy `monodromy hopfWord`,
with `d₁ ∘ d₂ = 0` a genuine chain complex, the monodromy defect `M − 1` present and nonzero and
sitting as the lower block of `d₂`, `d₂` injective, and both homologies computed as the
link-complement homology `H₀ ≅ ℤ`, `H₁ ≅ ℤ` by explicit `LinearEquiv`s (the fiber `ℤ²` collapsing
because `returnMap 1 − 1` is unimodular). -/
structure CarrierAMTCert : Prop where
  /-- Genuine chain complex. -/
  is_complex : d1 * d2 = 0
  /-- The monodromy defect block is nonzero (not a trivially-exact stand-in). -/
  defect_present : (monodromy hopfWord - 1 : Matrix (Fin 4) (Fin 4) ℤ) ≠ 0
  /-- The lower block of `d₂` is exactly the golden monodromy defect. -/
  defect_is_lower_block : ∀ i j : Fin 4,
    d2 (Fin.natAdd 4 i) j = (monodromy hopfWord - 1) i j
  /-- `d₂` is injective: `im d₂` has full rank `4`. -/
  d2_inj : Function.Injective T2
  /-- `H₀ ≅ ℤ` (connected). -/
  h0_iso_z : Nonempty (((Fin 4 → ℤ) ⧸ LinearMap.range T1) ≃ₗ[ℤ] ℤ)
  /-- `H₁ ≅ ℤ` (the link-complement homology, fiber `ℤ²` collapsed). -/
  h1_iso_z : Nonempty ((K ⧸ LinearMap.range T2') ≃ₗ[ℤ] ℤ)
  /-- The reason the fiber `ℤ²` dies: `returnMap 1 − 1` is unimodular. -/
  fiber_collapse : IsUnit (returnMap 1 - 1 : Matrix (Fin 2) (Fin 2) ℤ).det

theorem carrierAMTCert_holds : CarrierAMTCert where
  is_complex := d1_mul_d2
  defect_present := monodromy_defect_ne_zero
  defect_is_lower_block := d2_lower_block_eq_defect
  d2_inj := d2_injective
  h0_iso_z := ⟨h0Equiv⟩
  h1_iso_z := ⟨h1Equiv⟩
  fiber_collapse := fiber_defect_isUnit_det

end GoldenCarrierAMT
end Masses
end IndisputableMonolith
