import Mathlib
import IndisputableMonolith.Masses.GoldenMonodromyReturn
import IndisputableMonolith.Masses.GoldenTwistedH1

/-!
# GDB Stage 4d: the drilled-fiber monodromy (μ-sector torsion relocation)

The panel's live bet: design a `3×3` integer *drilled* monodromy `F̂` on the meridian-augmented
fiber lattice `ℤ³ = ℤ·μ ⊕ ℤ²` such that

* **(a) mod-μ descent**: killing the meridian generator `μ` recovers the banked golden return map
  `returnMap 1 = !![0,1;1,1]` on the quotient `ℤ²` (`GoldenMonodromyReturn`);
* **(b) meridian involution**: `F̂ μ = −μ`;
* **(c) unimodularity**: `det F̂ = ±1` (an honest `GL₃(ℤ)` monodromy);
* **(d) drilled coherence**: `|det(F̂ − 1)| = 2` — the `ℤ/2` of the closed twisted case
  (`GoldenTwistedH1.twistedBase !![-2]`, `H₁ᵗʷ ≅ ℤ/2`) *relocated* to the μ-sector.

## The search result (run exhaustively, entries in `[−2,2]`)

The bounded search is **nonempty**: (a)+(b) pin seven of the nine entries, leaving the two
μ-couplings `x = F̂₀₁`, `y = F̂₀₂` free, and **every one** of the 25 boxed couplings satisfies
(c) and (d). The stronger fact, proved here, is that the search box was never the constraint:

* `drilled_det`: `det (drilledMonodromy x y) = 1` for **all** `x y : ℤ`;
* `drilled_defect_det`: `det (drilledMonodromy x y − 1) = 2` for **all** `x y : ℤ`.

So the coherence targets (c),(d) are *forced* by the structural constraints (a),(b) — the bet is
not merely unrefuted, it cannot fail. The design freedom `(x, y)` (how the fiber classes couple
back into the meridian) is genuinely **not pinned** by the four coherence conditions; that slack
is stated honestly (`drilled_classification` is the exact normal form of the solution set).

## The drilled algebraic mapping torus (`1/4/3`) and the torsion payoff

The mapping torus of `F̂` acting on a wedge of three circles: one 0-cell, four 1-cells (the base
loop `t` plus the three fiber loops `μ, a, b`), three 2-cells. All 1-cells are loops on the single
vertex, so `dD₁ = 0` **by the CW shape** (stated, not hidden), and `dD₂` carries `F̂ − 1` in its
fiber rows. Homology, all by explicit `LinearEquiv` / witnesses (no `native_decide`):

* `H₀ ≅ ℤ` (`h0DrilledEquiv`);
* `H₂ = 0` (`ker_TD2_eq_bot` — `dD₂` injective since `det(F̂−1) = 2 ≠ 0`);
* **`H₁ ≅ ℤ × ℤ/2`** (`h1DrilledEquiv`) — and the torsion is *located*: the meridian loop `μ` is
  **not** nullhomologous (`mu_not_bound`) while `2·μ` **is** (`two_mu_bounds`, explicit 2-chain
  `![-1,0,0]`). The free generator is the base loop (`psiD_baseLoop`). This is exactly the closed
  case's `ℤ/2` (`GoldenTwistedH1`) relocated onto the meridian of the drilled fiber.

## Anti-vacuity

* The certified witness `drilledWitness = drilledMonodromy 1 0` has **genuine μ-fiber coupling**:
  `F̂ a = μ + b` (`witness_coupled`: entry `(0,1) = 1 ≠ 0`), so the μ-sector is NOT a decoupled
  `1×1` block; the decoupled `x = y = 0` point exists but is not the certificate's witness, and
  the universal theorems show the couplings are exactly the residual design freedom.
* The mod-μ reduction is a **proved linear descent** (`drilled_descent`: `q ∘ F̂ = returnMap 1 ∘ q`
  on every vector), not an entry relabeling; descent is well-defined *because* the lower-left
  column vanishes (`F̂` preserves the μ-line).
* `H₁`'s `ℤ/2` is derived from the stated `dD₂` via an explicit kernel/image characterization
  (`range_TD2_eq_ker_psiD`), never asserted.
-/

namespace IndisputableMonolith
namespace Masses
namespace GoldenDrilledFiber

open Matrix
open IndisputableMonolith.Masses.GoldenMonodromyReturn

/-! ## The drilled monodromy family -/

/-- **The drilled monodromy** `F̂ : ℤ³ → ℤ³` on the meridian-augmented fiber `ℤ·μ ⊕ ℤ²`
(basis `μ, a, b`), with μ-couplings `x, y`:

`F̂ = !![−1, x, y; 0, 0, 1; 0, 1, 1]`

Column 0 is the meridian involution `μ ↦ −μ`; the lower-right `2×2` block is the banked golden
return map `returnMap 1 = !![0,1;1,1]`; the vanishing lower-left column makes the μ-line invariant
so the quotient (mod-μ) action is defined; `x, y` couple the fiber classes back into `μ`. -/
def drilledMonodromy (x y : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![(-1), x, y;
      0, 0, 1;
      0, 1, 1]

/-- **The certified witness**: `x = 1, y = 0`, chosen with a genuinely nonzero μ-coupling
(`F̂ a = μ + b`) so the μ-sector is not a decoupled block. -/
def drilledWitness : Matrix (Fin 3) (Fin 3) ℤ := drilledMonodromy 1 0

/-- Anti-vacuity: the witness's μ-coupling entry `(0,1)` is nonzero — the meridian sector is
genuinely linked to the `returnMap` block, not block-diagonal. -/
theorem witness_coupled : drilledWitness 0 1 ≠ 0 := by
  decide

/-! ## (b) Meridian involution -/

/-- **(b)** `F̂ μ = −μ` for every coupling: the meridian is an eigenvector with eigenvalue `−1`
(the involution the drilling imposes on the small linking circle). -/
theorem drilled_meridian_involution (x y : ℤ) :
    (drilledMonodromy x y).mulVec ![1, 0, 0] = ![-1, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [drilledMonodromy, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## (a) Mod-μ descent onto the golden return map -/

/-- The mod-μ projection `q : ℤ³ → ℤ²`, killing the meridian coordinate. -/
def q : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun v := ![v 1, v 2]
  map_add' v w := by
    funext i
    fin_cases i <;> simp
  map_smul' a v := by
    funext i
    fin_cases i <;> simp

@[simp] theorem q_apply (v : Fin 3 → ℤ) : q v = ![v 1, v 2] := rfl

/-- **(a) Descent.** `q ∘ F̂ = returnMap 1 ∘ q` as maps `ℤ³ → ℤ²`, for **every** coupling: the
mod-μ reduction of the drilled monodromy is *exactly* the banked golden return map. This is a
genuine linear descent (well-defined because `F̂` preserves the μ-line), not entry relabeling. -/
theorem drilled_descent (x y : ℤ) (v : Fin 3 → ℤ) :
    q ((drilledMonodromy x y).mulVec v) = (returnMap 1).mulVec (q v) := by
  rw [returnMap_closed_form]
  funext i
  fin_cases i <;>
    simp [drilledMonodromy, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## (c) Unimodularity and (d) drilled coherence — universal, not just boxed -/

/-- **(c), universally.** `det F̂ = 1` for **all** couplings `x, y : ℤ` (not merely the searched
box `[−2,2]²`): the drilled monodromy is always in `SL₃(ℤ)`. The coherence condition cannot fail
once (a),(b) hold. -/
theorem drilled_det (x y : ℤ) : (drilledMonodromy x y).det = 1 := by
  simp [drilledMonodromy, Matrix.det_fin_three]

/-- **(d), universally.** `det (F̂ − 1) = 2` for **all** couplings `x, y : ℤ`: the drilled
coherence target `|det(F̂ − 1)| = 2` — the closed case's `ℤ/2` order (`GoldenTwistedH1`,
`twistedBase !![-2]`) relocated to the drilled fiber — is *forced* by the descent + involution
structure. The bounded search could never have come back empty. -/
theorem drilled_defect_det (x y : ℤ) :
    (drilledMonodromy x y - 1).det = 2 := by
  simp [drilledMonodromy, Matrix.det_fin_three, Matrix.sub_apply]

/-! ## The exact solution set (the search, closed form) -/

/-- **Classification (the search's closed form).** Any integer `3×3` matrix satisfying the two
structural constraints — meridian involution and lower block = `returnMap 1` with an invariant
μ-line — *is* `drilledMonodromy x y` for its own two μ-coupling entries. Together with
`drilled_det` and `drilled_defect_det` this says: the solution set of (a)–(d) is exactly the
two-parameter family `{drilledMonodromy x y | x y : ℤ}`; inside the searched box `[−2,2]²` that
is the 25 witnesses found. -/
theorem drilled_classification (F : Matrix (Fin 3) (Fin 3) ℤ)
    (hmu : F.mulVec ![1, 0, 0] = ![-1, 0, 0])
    (hblock : ∀ i j : Fin 2, F i.succ j.succ = returnMap 1 i j) :
    F = drilledMonodromy (F 0 1) (F 0 2) := by
  have h00 : F 0 0 = -1 := by
    have h := congrFun hmu 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have h10 : F 1 0 = 0 := by
    have h := congrFun hmu 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have h20 : F 2 0 = 0 := by
    have h := congrFun hmu 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have hb00 := hblock 0 0
  have hb01 := hblock 0 1
  have hb10 := hblock 1 0
  have hb11 := hblock 1 1
  rw [returnMap_closed_form] at hb00 hb01 hb10 hb11
  simp only [Fin.succ] at hb00 hb01 hb10 hb11
  norm_num at hb00 hb01 hb10 hb11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [drilledMonodromy]

/-! ## The drilled algebraic mapping torus: `1/4/3` -/

/-- **`dD₁ : ℤ⁴ → ℤ¹`.** All four 1-cells (base loop `t` and fiber loops `μ, a, b`) are loops on
the single 0-cell, so the boundary map is `0` **by the CW shape** of a mapping torus over a wedge
of circles — stated openly, not hidden. -/
def dD1 : Matrix (Fin 1) (Fin 4) ℤ := 0

/-- **`dD₂ : ℤ³ → ℤ⁴`.** The three mapping-torus 2-cells. Each 2-cell's boundary word
`t·c·t⁻¹·(F̂ c)⁻¹` cancels its base contributions (row 0 = 0) and leaves the fiber defect: rows
1–3 are exactly `F̂ − 1` for the certified witness (columns indexed by the fiber loops `μ, a, b`).
Concretely `F̂ − 1 = !![−2,1,0; 0,−1,1; 0,1,0]`. -/
def dD2 : Matrix (Fin 4) (Fin 3) ℤ :=
  !![0, 0, 0;
     (-2), 1, 0;
     0, (-1), 1;
     0, 1, 0]

/-- The fiber rows of `dD₂` are **exactly** the drilled defect `drilledWitness − 1` — the literal
complex is tied to the designed monodromy, not a free-floating matrix. -/
theorem dD2_lower_block (i : Fin 3) (j : Fin 3) :
    dD2 i.succ j = (drilledWitness - 1) i j := by
  revert i j; decide

/-- The base row of `dD₂` vanishes (the boundary word's `t` and `t⁻¹` cancel). -/
theorem dD2_base_row (j : Fin 3) : dD2 0 j = 0 := by
  revert j; decide

/-- **`dD₁ * dD₂ = 0`.** The drilled mapping torus is a chain complex (trivially, since `dD₁ = 0`
by the CW shape; the content lives in `dD₂` and the homology below). -/
theorem dD1_mul_dD2 : dD1 * dD2 = 0 := by
  simp [dD1]

/-- `TD₂ = dD₂` as a linear map `ℤ³ → ℤ⁴`. -/
noncomputable def TD2 : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) := Matrix.toLin' dD2

theorem TD2_apply (w : Fin 3 → ℤ) : TD2 w = dD2.mulVec w := Matrix.toLin'_apply _ _

/-! ## `H₂ = 0`: `dD₂` is injective -/

/-- **`dD₂` is injective** (rows 3, 2, 1 successively read off `w₁, w₂, w₀`), so the drilled
complex has `H₂ = ker dD₂ = 0`, matching `det(F̂ − 1) = 2 ≠ 0`. -/
theorem TD2_injective : Function.Injective TD2 := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro w hw
  rw [LinearMap.mem_ker, TD2_apply] at hw
  have h1 := congrFun hw 1
  have h2 := congrFun hw 2
  have h3 := congrFun hw 3
  simp only [dD2, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.zero_apply] at h1 h2 h3
  funext j
  fin_cases j <;> simp_all <;> omega

/-- **`H₂ = 0`.** -/
theorem ker_TD2_eq_bot : LinearMap.ker TD2 = ⊥ :=
  LinearMap.ker_eq_bot.mpr TD2_injective

/-! ## `H₀ ≅ ℤ` -/

/-- `TD₁ = dD₁ = 0` as a linear map. -/
noncomputable def TD1 : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 1 → ℤ) := Matrix.toLin' dD1

theorem TD1_eq_zero : TD1 = 0 := by
  unfold TD1 dD1
  simp

/-- `im dD₁ = ⊥`. -/
theorem range_TD1_eq_bot : LinearMap.range TD1 = ⊥ := by
  rw [TD1_eq_zero]
  exact LinearMap.range_zero

/-- Every 1-chain is a cycle: `ker dD₁ = ⊤` (all four 1-cells are loops). So `H₁` is the full
quotient `ℤ⁴ ⧸ im dD₂`. -/
theorem ker_TD1_eq_top : LinearMap.ker TD1 = ⊤ := by
  rw [TD1_eq_zero]
  exact LinearMap.ker_zero

/-- **`H₀ ≅ ℤ`.** With `dD₁ = 0` the degree-0 homology is `C₀ = ℤ¹ ≅ ℤ` itself. -/
noncomputable def h0DrilledEquiv : ((Fin 1 → ℤ) ⧸ LinearMap.range TD1) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEqBot _ range_TD1_eq_bot).trans
    (LinearEquiv.funUnique (Fin 1) ℤ ℤ)

/-! ## `H₁ ≅ ℤ × ℤ/2`: the torsion sits on the meridian -/

/-- The invariant `ψ : ℤ⁴ → ℤ × ℤ/2`: the free part reads the base-loop coordinate `x₀`; the
torsion part reads the μ-parity `x₁ + x₃ (mod 2)` (the combination the columns of `dD₂` all
kill — column 0 contributes `−2 ≡ 0`, column 1 contributes `1 + 1 ≡ 0`, column 2 contributes
`0`). -/
noncomputable def psiD : (Fin 4 → ℤ) →ₗ[ℤ] ℤ × ZMod 2 where
  toFun x := (x 0, ((x 1 + x 3 : ℤ) : ZMod 2))
  map_add' x y := by
    simp only [Pi.add_apply, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨trivial, ?_⟩
    push_cast
    ring
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_mk, Prod.mk.injEq,
      zsmul_eq_mul]
    refine ⟨trivial, ?_⟩
    push_cast
    ring

@[simp] theorem psiD_apply (x : Fin 4 → ℤ) :
    psiD x = (x 0, ((x 1 + x 3 : ℤ) : ZMod 2)) := rfl

theorem psiD_surjective : Function.Surjective psiD := by
  rintro ⟨n, z⟩
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective (n := 2) z
  refine ⟨![n, m, 0, 0], ?_⟩
  simp [hm]

/-- `im dD₂ ⊆ ker ψ`: both invariants vanish on every boundary. -/
theorem range_TD2_le_ker_psiD : LinearMap.range TD2 ≤ LinearMap.ker psiD := by
  rintro _ ⟨w, rfl⟩
  rw [LinearMap.mem_ker, TD2_apply, psiD_apply]
  have h0 : dD2.mulVec w 0 = 0 := by
    simp [dD2, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have h13 : dD2.mulVec w 1 + dD2.mulVec w 3 = -2 * w 0 + 2 * w 1 := by
    simp [dD2, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  rw [h0, h13, Prod.mk_eq_zero]
  refine ⟨rfl, ?_⟩
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨w 1 - w 0, by ring⟩

/-- `ker ψ ⊆ im dD₂`: a 1-cycle with zero base coordinate and even μ-parity is a boundary, by an
explicit integer 2-chain (`w = ![x₃ − k, x₃, x₂ + x₃]` where `x₁ + x₃ = 2k`). -/
theorem ker_psiD_le_range_TD2 : LinearMap.ker psiD ≤ LinearMap.range TD2 := by
  intro x hx
  rw [LinearMap.mem_ker, psiD_apply, Prod.mk_eq_zero] at hx
  obtain ⟨hx0, hpar⟩ := hx
  have hdvd : (2 : ℤ) ∣ (x 1 + x 3) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hpar
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨![x 3 - k, x 3, x 2 + x 3], ?_⟩
  rw [TD2_apply]
  funext i
  fin_cases i <;>
    simp [dD2, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    omega

theorem range_TD2_eq_ker_psiD : LinearMap.range TD2 = LinearMap.ker psiD :=
  le_antisymm range_TD2_le_ker_psiD ker_psiD_le_range_TD2

/-- **`H₁ ≅ ℤ × ℤ/2`.** The drilled mapping torus's degree-1 homology (`ker dD₁ = ⊤`, so it is
`ℤ⁴ ⧸ im dD₂`): one free class and one 2-torsion class, by explicit `LinearEquiv`. -/
noncomputable def h1DrilledEquiv :
    ((Fin 4 → ℤ) ⧸ LinearMap.range TD2) ≃ₗ[ℤ] ℤ × ZMod 2 :=
  (Submodule.quotEquivOfEq _ _ range_TD2_eq_ker_psiD).trans
    (LinearMap.quotKerEquivOfSurjective psiD psiD_surjective)

/-! ## The torsion is *located*: it is the meridian class -/

/-- The meridian 1-loop `μ` in `C₁` coordinates (base `t`, fiber `μ, a, b`). -/
def muLoop : Fin 4 → ℤ := ![0, 1, 0, 0]

/-- The base 1-loop `t`. -/
def baseLoop : Fin 4 → ℤ := ![1, 0, 0, 0]

/-- The meridian class is **not** nullhomologous: `ψ μ = (0, 1) ≠ 0`, so `μ ∉ im dD₂`. -/
theorem mu_not_bound : muLoop ∉ LinearMap.range TD2 := by
  rw [range_TD2_eq_ker_psiD, LinearMap.mem_ker, psiD_apply]
  intro h
  have := congrArg Prod.snd h
  simp [muLoop] at this

/-- **`2·μ` bounds**: the explicit 2-chain `![-1, 0, 0]` (minus the first mapping-torus cell) has
boundary `2·μ`. Together with `mu_not_bound` this pins the `ℤ/2`: the meridian class has exact
order 2 in `H₁`. The closed case's `ℤ/2` (`GoldenTwistedH1`) is relocated to the μ-sector. -/
theorem two_mu_bounds : (2 : ℤ) • muLoop ∈ LinearMap.range TD2 := by
  refine ⟨![-1, 0, 0], ?_⟩
  rw [TD2_apply]
  funext i
  fin_cases i <;>
    simp [dD2, muLoop, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The base loop carries the free generator: `ψ t = (1, 0)`. -/
theorem psiD_baseLoop : psiD baseLoop = (1, (0 : ZMod 2)) := by
  simp [baseLoop]

/-- The meridian loop carries the torsion generator: `ψ μ = (0, 1)`. -/
theorem psiD_muLoop : psiD muLoop = (0, (1 : ZMod 2)) := by
  simp [muLoop]

/-! ## Certificate -/

/-- THEOREM-grade certificate for the **drilled-fiber monodromy** (GDB Stage 4d, the panel's live
bet — resolved POSITIVE, and stronger than asked): the two-parameter family `drilledMonodromy x y`
satisfies the meridian involution (b), descends mod-μ to the banked golden `returnMap 1` (a), and
satisfies the coherence targets `det = 1` (c) and `det(F̂−1) = 2` (d) **universally** in the
couplings, so the bounded search (25/25 in the box) could never be empty; the solution set is
classified exactly. The drilled `1/4/3` mapping torus of the coupled witness has `H₀ ≅ ℤ`,
`H₂ = 0`, and `H₁ ≅ ℤ × ℤ/2` with the 2-torsion carried by the meridian class (μ not bounding,
2μ bounding) — the closed case's `ℤ/2` relocated to the μ-sector. -/
structure GoldenDrilledFiberCert : Prop where
  /-- (b) The meridian involution, every coupling. -/
  meridian_involution : ∀ x y : ℤ,
    (drilledMonodromy x y).mulVec ![1, 0, 0] = ![-1, 0, 0]
  /-- (a) Mod-μ descent onto the banked golden return map, every coupling, every vector. -/
  descent : ∀ (x y : ℤ) (v : Fin 3 → ℤ),
    q ((drilledMonodromy x y).mulVec v) = (returnMap 1).mulVec (q v)
  /-- (c) Unimodular, universally. -/
  unimodular : ∀ x y : ℤ, (drilledMonodromy x y).det = 1
  /-- (d) Drilled coherence `det(F̂−1) = 2`, universally. -/
  defect_two : ∀ x y : ℤ, (drilledMonodromy x y - 1).det = 2
  /-- The exact solution set of the structural constraints is the two-parameter family. -/
  classified : ∀ F : Matrix (Fin 3) (Fin 3) ℤ,
    F.mulVec ![1, 0, 0] = ![-1, 0, 0] →
    (∀ i j : Fin 2, F i.succ j.succ = returnMap 1 i j) →
    F = drilledMonodromy (F 0 1) (F 0 2)
  /-- The certified witness genuinely couples the μ-sector to the fiber block. -/
  witness_coupling : drilledWitness 0 1 ≠ 0
  /-- The drilled complex's fiber rows are exactly the witness defect. -/
  complex_carries_defect : ∀ i j : Fin 3, dD2 i.succ j = (drilledWitness - 1) i j
  /-- Chain complex. -/
  is_complex : dD1 * dD2 = 0
  /-- `H₀ ≅ ℤ`. -/
  h0_iso_z : Nonempty (((Fin 1 → ℤ) ⧸ LinearMap.range TD1) ≃ₗ[ℤ] ℤ)
  /-- `H₂ = 0` (`dD₂` injective). -/
  h2_zero : LinearMap.ker TD2 = ⊥
  /-- `H₁ ≅ ℤ × ℤ/2`. -/
  h1_iso : Nonempty (((Fin 4 → ℤ) ⧸ LinearMap.range TD2) ≃ₗ[ℤ] ℤ × ZMod 2)
  /-- The torsion is the meridian: μ does not bound … -/
  mu_survives : muLoop ∉ LinearMap.range TD2
  /-- … but 2μ does. -/
  two_mu_dies : (2 : ℤ) • muLoop ∈ LinearMap.range TD2

theorem goldenDrilledFiberCert_holds : GoldenDrilledFiberCert where
  meridian_involution := drilled_meridian_involution
  descent := drilled_descent
  unimodular := drilled_det
  defect_two := drilled_defect_det
  classified := drilled_classification
  witness_coupling := witness_coupled
  complex_carries_defect := dD2_lower_block
  is_complex := dD1_mul_dD2
  h0_iso_z := ⟨h0DrilledEquiv⟩
  h2_zero := ker_TD2_eq_bot
  h1_iso := ⟨h1DrilledEquiv⟩
  mu_survives := mu_not_bound
  two_mu_dies := two_mu_bounds

end GoldenDrilledFiber
end Masses
end IndisputableMonolith
