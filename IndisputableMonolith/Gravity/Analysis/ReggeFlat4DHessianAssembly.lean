import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel12
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel13
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel22
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DOrbitClassification
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D

/-!
# Regge 4D flat Hessian assembly (zero-momentum true weights)

QG full-theory campaign: assemble the committed per-orbit star deficit
kernels with Heron area gradients into the flat second-variation class
quadratic of the 4D Regge action, replacing the provisional weight-1
aggregate of `ReggeEdgeStencil4D.finiteTTQuadratic`.

## Tier tags (binding)

* THEOREM: every named theorem below (kernel-checked; no `sorry`, no
  `admit`, no new axioms, no `native_decide`, no `: True` shells).
* Scope: **zero-momentum** (constant edge-class perturbation) per-cell
  Hessian only.  Finite-momentum Bloch phase folding across hinge
  translates is **OPEN**.
* This does **not** prove `S_RS_converges_EH_4d`.
* This does **not** flip `gap_action_recovery`.
* This does **not** reverse-engineer weights from Einstein–Hilbert: all
  orbit counts, area gradients, and deficit kernels come from the
  committed geometry modules imported above.

## What is proved (deliverable A)

1. **Area gradients.** For each of the four committed flat triangle
   representatives `(a,b,c) ∈ {(1,1,2),(1,2,3),(1,3,4),(2,2,4)}`, the
   Heron form `A² = (2ab+2bc+2ca−a²−b²−c²)/16` yields explicit
   `HasDerivAt` theorems for `∂A/∂a`, `∂A/∂b`, `∂A/∂c` at flat, with
   closed values recorded below.
2. **Complement transport (identity on edge classes).** Vertex
   complement `m ↦ m ⊕ 15` preserves difference masks
   (`(u⊕15)⊕(v⊕15) = u⊕v`), so edge-class indices are invariant.
   Therefore the type-`(2,1)` (resp. `(3,1)`) star class kernel equals
   the committed type-`(1,2)` (resp. `(1,3)`) kernel on `Fin 15`.
3. **Zero-momentum true-weight Hessian.** Orbit-count-weighted sum of
   `(dA · c)(dδ · c)` over the six `S₄` types, with counts
   `72/48/48/24/24/24`.
4. **Polarization / bilinearity** of the associated symmetric bilinear
   form.
5. **Evaluations** on `axisTTPlus`, `decoyGauge`, and `decoyTrace`:
   all three equal `0`.  True weights **kill pure gauge** at zero
   momentum (provisional weight-1 gave `32` on the same decoy).
6. **Homothety** direction evaluates to `0`.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeFlat4DHessianAssembly

open BigOperators
open ReggeEdgeStencil4D
open ReggeHinge4DOrbitClassification
open EdgeTTDecomposition4D

noncomputable section

/-! ## §1. Heron area and coordinate derivatives -/

def heronSq (a b c : ℝ) : ℝ :=
  (2 * a * b + 2 * b * c + 2 * c * a - a ^ 2 - b ^ 2 - c ^ 2) / 16

def hingeArea (a b c : ℝ) : ℝ := Real.sqrt (heronSq a b c)

def areaGradA (a b c : ℝ) : ℝ :=
  (b + c - a) / (16 * hingeArea a b c)

def areaGradB (a b c : ℝ) : ℝ :=
  (a + c - b) / (16 * hingeArea a b c)

def areaGradC (a b c : ℝ) : ℝ :=
  (a + b - c) / (16 * hingeArea a b c)

private lemma hasDerivAt_quad_sub_sq (p q t0 : ℝ) :
    HasDerivAt (fun t : ℝ => p * t - t ^ 2 + q) (p - 2 * t0) t0 := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t0) t0 := by
    simpa using hasDerivAt_pow 2 t0
  have hlin := ((hasDerivAt_id t0).const_mul p).sub hpow
  convert hlin.add_const q using 1
  ring

theorem hasDerivAt_heronSq_a (a0 b c : ℝ) :
    HasDerivAt (fun t : ℝ => heronSq t b c) ((b + c - a0) / 8) a0 := by
  have hfun :
      (fun t : ℝ => heronSq t b c) =
        fun t : ℝ =>
          ((2 * b + 2 * c) * t - t ^ 2 + (2 * b * c - b ^ 2 - c ^ 2)) / 16 := by
    funext t; unfold heronSq; ring
  rw [hfun]
  have h :=
    (hasDerivAt_quad_sub_sq (2 * b + 2 * c) (2 * b * c - b ^ 2 - c ^ 2) a0).div_const
      (16 : ℝ)
  convert h using 1
  ring

theorem hasDerivAt_heronSq_b (a b0 c : ℝ) :
    HasDerivAt (fun t : ℝ => heronSq a t c) ((a + c - b0) / 8) b0 := by
  have hfun :
      (fun t : ℝ => heronSq a t c) =
        fun t : ℝ =>
          ((2 * a + 2 * c) * t - t ^ 2 + (2 * a * c - a ^ 2 - c ^ 2)) / 16 := by
    funext t; unfold heronSq; ring
  rw [hfun]
  have h :=
    (hasDerivAt_quad_sub_sq (2 * a + 2 * c) (2 * a * c - a ^ 2 - c ^ 2) b0).div_const
      (16 : ℝ)
  convert h using 1
  ring

theorem hasDerivAt_heronSq_c (a b c0 : ℝ) :
    HasDerivAt (fun t : ℝ => heronSq a b t) ((a + b - c0) / 8) c0 := by
  have hfun :
      (fun t : ℝ => heronSq a b t) =
        fun t : ℝ =>
          ((2 * a + 2 * b) * t - t ^ 2 + (2 * a * b - a ^ 2 - b ^ 2)) / 16 := by
    funext t; unfold heronSq; ring
  rw [hfun]
  have h :=
    (hasDerivAt_quad_sub_sq (2 * a + 2 * b) (2 * a * b - a ^ 2 - b ^ 2) c0).div_const
      (16 : ℝ)
  convert h using 1
  ring

private lemma hasDerivAt_sqrt_heron_coord
    {F : ℝ → ℝ} {t0 F' : ℝ}
    (hF : HasDerivAt F F' t0) (hpos : 0 < F t0) :
    HasDerivAt (fun t : ℝ => Real.sqrt (F t))
      (F' / (2 * Real.sqrt (F t0))) t0 := by
  have hsqrt := (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp t0 hF
  convert hsqrt using 1
  ring

theorem hasDerivAt_hingeArea_a (a0 b c : ℝ) (hpos : 0 < heronSq a0 b c) :
    HasDerivAt (fun t : ℝ => hingeArea t b c) (areaGradA a0 b c) a0 := by
  have h :=
    hasDerivAt_sqrt_heron_coord (hasDerivAt_heronSq_a a0 b c) hpos
  -- Goal derivative equality: areaGradA = heronSq'_a / (2 √heronSq)
  change HasDerivAt (fun t : ℝ => Real.sqrt (heronSq t b c))
      ((b + c - a0) / (16 * Real.sqrt (heronSq a0 b c))) a0
  convert h using 1
  ring

theorem hasDerivAt_hingeArea_b (a b0 c : ℝ) (hpos : 0 < heronSq a b0 c) :
    HasDerivAt (fun t : ℝ => hingeArea a t c) (areaGradB a b0 c) b0 := by
  have h :=
    hasDerivAt_sqrt_heron_coord (hasDerivAt_heronSq_b a b0 c) hpos
  change HasDerivAt (fun t : ℝ => Real.sqrt (heronSq a t c))
      ((a + c - b0) / (16 * Real.sqrt (heronSq a b0 c))) b0
  convert h using 1
  ring

theorem hasDerivAt_hingeArea_c (a b c0 : ℝ) (hpos : 0 < heronSq a b c0) :
    HasDerivAt (fun t : ℝ => hingeArea a b t) (areaGradC a b c0) c0 := by
  have h :=
    hasDerivAt_sqrt_heron_coord (hasDerivAt_heronSq_c a b c0) hpos
  change HasDerivAt (fun t : ℝ => Real.sqrt (heronSq a b t))
      ((a + b - c0) / (16 * Real.sqrt (heronSq a b c0))) c0
  convert h using 1
  ring

/-! ## §2. Flat values on committed representatives -/

theorem heronSq_t11 : heronSq 1 1 2 = 1 / 4 := by unfold heronSq; norm_num
theorem heronSq_t12 : heronSq 1 2 3 = 1 / 2 := by unfold heronSq; norm_num
theorem heronSq_t13 : heronSq 1 3 4 = 3 / 4 := by unfold heronSq; norm_num
theorem heronSq_t22 : heronSq 2 2 4 = 1 := by unfold heronSq; norm_num

theorem hingeArea_t11 : hingeArea 1 1 2 = 1 / 2 := by
  unfold hingeArea
  rw [heronSq_t11, show (1 / 4 : ℝ) = ((1 : ℝ) / 2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem hingeArea_t12 : hingeArea 1 2 3 = Real.sqrt 2 / 2 := by
  unfold hingeArea
  have h : (1 / 2 : ℝ) = (Real.sqrt 2 / 2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  rw [heronSq_t12, h]
  exact Real.sqrt_sq (by positivity)

theorem hingeArea_t13 : hingeArea 1 3 4 = Real.sqrt 3 / 2 := by
  unfold hingeArea
  have h : (3 / 4 : ℝ) = (Real.sqrt 3 / 2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  rw [heronSq_t13, h]
  exact Real.sqrt_sq (by positivity)

theorem hingeArea_t22 : hingeArea 2 2 4 = 1 := by
  unfold hingeArea; rw [heronSq_t22, Real.sqrt_one]

theorem areaGradA_t11 : areaGradA 1 1 2 = 1 / 4 := by
  unfold areaGradA; rw [hingeArea_t11]; norm_num
theorem areaGradB_t11 : areaGradB 1 1 2 = 1 / 4 := by
  unfold areaGradB; rw [hingeArea_t11]; norm_num
theorem areaGradC_t11 : areaGradC 1 1 2 = 0 := by
  unfold areaGradC; rw [hingeArea_t11]; norm_num

theorem areaGradA_t12 : areaGradA 1 2 3 = Real.sqrt 2 / 4 := by
  unfold areaGradA; rw [hingeArea_t12]
  have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hs2]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem areaGradB_t12 : areaGradB 1 2 3 = Real.sqrt 2 / 8 := by
  unfold areaGradB; rw [hingeArea_t12]
  have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hs2]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem areaGradC_t12 : areaGradC 1 2 3 = 0 := by
  unfold areaGradC; rw [hingeArea_t12]; ring

theorem areaGradA_t13 : areaGradA 1 3 4 = Real.sqrt 3 / 4 := by
  unfold areaGradA; rw [hingeArea_t13]
  have hs3 : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hs3]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem areaGradB_t13 : areaGradB 1 3 4 = Real.sqrt 3 / 12 := by
  unfold areaGradB; rw [hingeArea_t13]
  have hs3 : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hs3]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem areaGradC_t13 : areaGradC 1 3 4 = 0 := by
  unfold areaGradC; rw [hingeArea_t13]; ring

theorem areaGradA_t22 : areaGradA 2 2 4 = 1 / 4 := by
  unfold areaGradA; rw [hingeArea_t22]; norm_num
theorem areaGradB_t22 : areaGradB 2 2 4 = 1 / 4 := by
  unfold areaGradB; rw [hingeArea_t22]; norm_num
theorem areaGradC_t22 : areaGradC 2 2 4 = 0 := by
  unfold areaGradC; rw [hingeArea_t22]; norm_num

theorem hasDerivAt_area_t11_a :
    HasDerivAt (fun t : ℝ => hingeArea t 1 2) (1 / 4) 1 := by
  simpa [areaGradA_t11] using
    hasDerivAt_hingeArea_a 1 1 2 (by rw [heronSq_t11]; norm_num)
theorem hasDerivAt_area_t11_b :
    HasDerivAt (fun t : ℝ => hingeArea 1 t 2) (1 / 4) 1 := by
  simpa [areaGradB_t11] using
    hasDerivAt_hingeArea_b 1 1 2 (by rw [heronSq_t11]; norm_num)
theorem hasDerivAt_area_t11_c :
    HasDerivAt (fun t : ℝ => hingeArea 1 1 t) 0 2 := by
  simpa [areaGradC_t11] using
    hasDerivAt_hingeArea_c 1 1 2 (by rw [heronSq_t11]; norm_num)

theorem hasDerivAt_area_t12_a :
    HasDerivAt (fun t : ℝ => hingeArea t 2 3) (Real.sqrt 2 / 4) 1 := by
  simpa [areaGradA_t12] using
    hasDerivAt_hingeArea_a 1 2 3 (by rw [heronSq_t12]; norm_num)
theorem hasDerivAt_area_t12_b :
    HasDerivAt (fun t : ℝ => hingeArea 1 t 3) (Real.sqrt 2 / 8) 2 := by
  simpa [areaGradB_t12] using
    hasDerivAt_hingeArea_b 1 2 3 (by rw [heronSq_t12]; norm_num)
theorem hasDerivAt_area_t12_c :
    HasDerivAt (fun t : ℝ => hingeArea 1 2 t) 0 3 := by
  simpa [areaGradC_t12] using
    hasDerivAt_hingeArea_c 1 2 3 (by rw [heronSq_t12]; norm_num)

theorem hasDerivAt_area_t13_a :
    HasDerivAt (fun t : ℝ => hingeArea t 3 4) (Real.sqrt 3 / 4) 1 := by
  simpa [areaGradA_t13] using
    hasDerivAt_hingeArea_a 1 3 4 (by rw [heronSq_t13]; norm_num)
theorem hasDerivAt_area_t13_b :
    HasDerivAt (fun t : ℝ => hingeArea 1 t 4) (Real.sqrt 3 / 12) 3 := by
  simpa [areaGradB_t13] using
    hasDerivAt_hingeArea_b 1 3 4 (by rw [heronSq_t13]; norm_num)
theorem hasDerivAt_area_t13_c :
    HasDerivAt (fun t : ℝ => hingeArea 1 3 t) 0 4 := by
  simpa [areaGradC_t13] using
    hasDerivAt_hingeArea_c 1 3 4 (by rw [heronSq_t13]; norm_num)

theorem hasDerivAt_area_t22_a :
    HasDerivAt (fun t : ℝ => hingeArea t 2 4) (1 / 4) 2 := by
  simpa [areaGradA_t22] using
    hasDerivAt_hingeArea_a 2 2 4 (by rw [heronSq_t22]; norm_num)
theorem hasDerivAt_area_t22_b :
    HasDerivAt (fun t : ℝ => hingeArea 2 t 4) (1 / 4) 2 := by
  simpa [areaGradB_t22] using
    hasDerivAt_hingeArea_b 2 2 4 (by rw [heronSq_t22]; norm_num)
theorem hasDerivAt_area_t22_c :
    HasDerivAt (fun t : ℝ => hingeArea 2 2 t) 0 4 := by
  simpa [areaGradC_t22] using
    hasDerivAt_hingeArea_c 2 2 4 (by rw [heronSq_t22]; norm_num)

/-! ## §3. Complement transport (identity on edge classes) -/

def complementMask (m : ℕ) : ℕ := Nat.xor m 15

theorem complement_preserves_edge_mask (u v : ℕ) :
    Nat.xor (complementMask u) (complementMask v) = Nat.xor u v := by
  unfold complementMask
  -- (u ^^^ 15) ^^^ (v ^^^ 15) = u ^^^ v
  change (u ^^^ (15 : ℕ)) ^^^ (v ^^^ (15 : ℕ)) = u ^^^ v
  rw [Nat.xor_assoc u 15 (v ^^^ 15)]
  -- u ^^^ (15 ^^^ (v ^^^ 15))
  rw [Nat.xor_comm v 15]
  -- u ^^^ (15 ^^^ (15 ^^^ v))
  rw [← Nat.xor_assoc 15 15 v, Nat.xor_self 15, Nat.zero_xor]

/-- Type `(2,1)` kernel = committed `(1,2)` kernel (identity transport). -/
def kernel21 : Fin 15 → ℝ :=
  ReggeHinge4DStarKernel12.fullStarClassKernel

/-- Type `(3,1)` kernel = committed `(1,3)` kernel (identity transport). -/
def kernel31 : Fin 15 → ℝ :=
  ReggeHinge4DStarKernel13.fullStarClassKernel

theorem kernel21_eq_kernel12 (d : Fin 15) :
    kernel21 d = ReggeHinge4DStarKernel12.fullStarClassKernel d := rfl

theorem kernel31_eq_kernel13 (d : Fin 15) :
    kernel31 d = ReggeHinge4DStarKernel13.fullStarClassKernel d := rfl

theorem complement_swaps_type_reexport (s : Fin 24) (t : Fin 10) :
    ∃ s' : Fin 24, ∃ t' : Fin 10,
      hingeTypePop s' t' =
        ((hingeTypePop s t).2, (hingeTypePop s t).1) :=
  complement_swaps_type s t

/-! ## §4. Area covectors on the 15 classes -/

def areaCov11 : Fin 15 → ℝ
  | ⟨0, _⟩ => 1 / 4
  | ⟨1, _⟩ => 1 / 4
  | ⟨2, _⟩ => 0
  | _ => 0

def areaCov12 : Fin 15 → ℝ
  | ⟨0, _⟩ => Real.sqrt 2 / 4
  | ⟨5, _⟩ => Real.sqrt 2 / 8
  | ⟨6, _⟩ => 0
  | _ => 0

def areaCov21 : Fin 15 → ℝ
  | ⟨2, _⟩ => Real.sqrt 2 / 8
  | ⟨3, _⟩ => Real.sqrt 2 / 4
  | ⟨6, _⟩ => 0
  | _ => 0

def areaCov13 : Fin 15 → ℝ
  | ⟨0, _⟩ => Real.sqrt 3 / 4
  | ⟨13, _⟩ => Real.sqrt 3 / 12
  | ⟨14, _⟩ => 0
  | _ => 0

def areaCov31 : Fin 15 → ℝ
  | ⟨6, _⟩ => Real.sqrt 3 / 12
  | ⟨7, _⟩ => Real.sqrt 3 / 4
  | ⟨14, _⟩ => 0
  | _ => 0

def areaCov22 : Fin 15 → ℝ
  | ⟨2, _⟩ => 1 / 4
  | ⟨11, _⟩ => 1 / 4
  | ⟨14, _⟩ => 0
  | _ => 0

theorem areaCov11_eq_grads :
    areaCov11 0 = areaGradA 1 1 2 ∧
      areaCov11 1 = areaGradB 1 1 2 ∧
        areaCov11 2 = areaGradC 1 1 2 := by
  simp [areaCov11, areaGradA_t11, areaGradB_t11, areaGradC_t11]

theorem areaCov12_eq_grads :
    areaCov12 0 = areaGradA 1 2 3 ∧
      areaCov12 5 = areaGradB 1 2 3 ∧
        areaCov12 6 = areaGradC 1 2 3 := by
  simp [areaCov12, areaGradA_t12, areaGradB_t12, areaGradC_t12]

theorem areaCov22_eq_grads :
    areaCov22 2 = areaGradA 2 2 4 ∧
      areaCov22 11 = areaGradB 2 2 4 ∧
        areaCov22 14 = areaGradC 2 2 4 := by
  simp [areaCov22, areaGradA_t22, areaGradB_t22, areaGradC_t22]

/-! ## §5. Zero-momentum true-weight Hessian -/

def orbitDeficitKernel : HingeOrbitType → Fin 15 → ℝ
  | .t11 => ReggeHinge4DStarKernel.fullStarClassKernel
  | .t12 => ReggeHinge4DStarKernel12.fullStarClassKernel
  | .t21 => kernel21
  | .t13 => ReggeHinge4DStarKernel13.fullStarClassKernel
  | .t31 => kernel31
  | .t22 => ReggeHinge4DStarKernel22.fullStarClassKernel

def orbitAreaCov : HingeOrbitType → Fin 15 → ℝ
  | .t11 => areaCov11
  | .t12 => areaCov12
  | .t21 => areaCov21
  | .t13 => areaCov13
  | .t31 => areaCov31
  | .t22 => areaCov22

def orbitCellCount : HingeOrbitType → ℕ
  | .t11 => 72
  | .t12 => 48
  | .t21 => 48
  | .t13 => 24
  | .t31 => 24
  | .t22 => 24

theorem orbitCellCount_eq_classification (ty : HingeOrbitType) :
    orbitCellCount ty = cellTriangleCount ty.toPop := by
  cases ty <;> rfl

/-- Dot of two class covectors. -/
def coeffDot (v w : Fin 15 → ℝ) : ℝ :=
  ∑ d : Fin 15, v d * w d

def classDot (v : Fin 15 → ℝ) (H : Mat4) : ℝ :=
  coeffDot v (classCoeff H)

def orbitZeroMomQuadratic (ty : HingeOrbitType) (H : Mat4) : ℝ :=
  (orbitCellCount ty : ℝ) *
    classDot (orbitAreaCov ty) H * classDot (orbitDeficitKernel ty) H

def orbitZeroMomBilinear (ty : HingeOrbitType) (A B : Mat4) : ℝ :=
  (orbitCellCount ty : ℝ) / 2 *
    (classDot (orbitAreaCov ty) A * classDot (orbitDeficitKernel ty) B +
      classDot (orbitAreaCov ty) B * classDot (orbitDeficitKernel ty) A)

def trueWeightZeroMomQuadratic (H : Mat4) : ℝ :=
  ∑ ty : HingeOrbitType, orbitZeroMomQuadratic ty H

def trueWeightZeroMomBilinear (A B : Mat4) : ℝ :=
  ∑ ty : HingeOrbitType, orbitZeroMomBilinear ty A B

theorem classDot_add (v : Fin 15 → ℝ) (A B : Mat4) :
    classDot v (A + B) = classDot v A + classDot v B := by
  unfold classDot coeffDot
  simp_rw [classCoeff_add, mul_add, Finset.sum_add_distrib]

theorem classDot_smul (v : Fin 15 → ℝ) (c : ℝ) (A : Mat4) :
    classDot v (c • A) = c * classDot v A := by
  unfold classDot coeffDot
  simp_rw [classCoeff_smul]
  refine Eq.trans ?_ (Finset.mul_sum _ _ c).symm
  refine Finset.sum_congr rfl fun d _ => by ring

theorem orbitZeroMomQuadratic_eq_bilinear (ty : HingeOrbitType) (H : Mat4) :
    orbitZeroMomQuadratic ty H = orbitZeroMomBilinear ty H H := by
  unfold orbitZeroMomQuadratic orbitZeroMomBilinear; ring

theorem trueWeightZeroMomQuadratic_eq_bilinear (H : Mat4) :
    trueWeightZeroMomQuadratic H = trueWeightZeroMomBilinear H H := by
  unfold trueWeightZeroMomQuadratic trueWeightZeroMomBilinear
  exact Finset.sum_congr rfl fun ty _ => orbitZeroMomQuadratic_eq_bilinear ty H

theorem trueWeightZeroMomBilinear_symm (A B : Mat4) :
    trueWeightZeroMomBilinear A B = trueWeightZeroMomBilinear B A := by
  unfold trueWeightZeroMomBilinear orbitZeroMomBilinear
  exact Finset.sum_congr rfl fun ty _ => by ring

theorem trueWeightZeroMomBilinear_add_left (A₁ A₂ B : Mat4) :
    trueWeightZeroMomBilinear (A₁ + A₂) B =
      trueWeightZeroMomBilinear A₁ B + trueWeightZeroMomBilinear A₂ B := by
  unfold trueWeightZeroMomBilinear orbitZeroMomBilinear
  simp_rw [classDot_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ty _ => by ring

theorem trueWeightZeroMomBilinear_smul_left (c : ℝ) (A B : Mat4) :
    trueWeightZeroMomBilinear (c • A) B = c * trueWeightZeroMomBilinear A B := by
  unfold trueWeightZeroMomBilinear orbitZeroMomBilinear
  simp_rw [classDot_smul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ty _ => by ring

theorem trueWeightZeroMomQuadratic_add (A B : Mat4) :
    trueWeightZeroMomQuadratic (A + B) =
      trueWeightZeroMomQuadratic A + trueWeightZeroMomQuadratic B +
        2 * trueWeightZeroMomBilinear A B := by
  -- Expand via bilinearity of classDot and algebra on each orbit summand.
  unfold trueWeightZeroMomQuadratic
  have hty : ∀ ty : HingeOrbitType,
      orbitZeroMomQuadratic ty (A + B) =
        orbitZeroMomQuadratic ty A + orbitZeroMomQuadratic ty B +
          2 * orbitZeroMomBilinear ty A B := by
    intro ty
    unfold orbitZeroMomQuadratic orbitZeroMomBilinear
    simp_rw [classDot_add]
    ring
  simp_rw [hty]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

/-! ## §6. Deficit kernels annihilate named class vectors

Integer sign tables + `decide` on `ℤ`-sums; cast back to `ℝ`.
-/

def axisTTPlusCoeffZ (d : Fin 15) : ℤ :=
  (if classBit d 2 then (1 : ℤ) else 0) - if classBit d 3 then 1 else 0

theorem classCoeff_axisTTPlus_int (d : Fin 15) :
    classCoeff axisTTPlus d = (axisTTPlusCoeffZ d : ℝ) := by
  rw [classCoeff_axisTTPlus]
  unfold axisTTPlusCoeffZ
  cases classBit d 2 <;> cases classBit d 3 <;> norm_num

/-- Integer class coefficients for `axisTTCross`: `2` when bits 2 and 3 are set. -/
def axisTTCrossCoeffZ (d : Fin 15) : ℤ :=
  2 * (if classBit d 2 && classBit d 3 then (1 : ℤ) else 0)

theorem classCoeff_axisTTCross_int (d : Fin 15) :
    classCoeff axisTTCross d = (axisTTCrossCoeffZ d : ℝ) := by
  rw [classCoeff_axisTTCross]
  unfold axisTTCrossCoeffZ
  cases classBit d 2 <;> cases classBit d 3 <;> norm_num

def gaugeBit0 (d : Fin 15) : ℕ := if classBit d 0 then 1 else 0

theorem classCoeff_decoyGauge_bit (d : Fin 15) :
    classCoeff decoyGauge d = (2 : ℝ) * (gaugeBit0 d : ℝ) := by
  unfold decoyGauge gaugeBit0
  rw [classCoeff_gaugePart_axis]
  cases classBit d 0 <;> norm_num

def kernel11Sign (d : Fin 15) : ℤ :=
  match d with
  | ⟨2, _⟩ => -1 | ⟨3, _⟩ => -1 | ⟨6, _⟩ => 1 | ⟨7, _⟩ => -1
  | ⟨10, _⟩ => 1 | ⟨11, _⟩ => 1 | ⟨14, _⟩ => -1
  | _ => 0

theorem kernel11_eq_sign (d : Fin 15) :
    ReggeHinge4DStarKernel.fullStarClassKernel d = (kernel11Sign d : ℝ) := by
  fin_cases d <;> simp [ReggeHinge4DStarKernel.fullStarClassKernel, kernel11Sign]

def kernel12Sign (d : Fin 15) : ℤ :=
  match d with
  | ⟨0, _⟩ => -1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 1 | ⟨3, _⟩ => 1 | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => -1 | ⟨6, _⟩ => -1 | ⟨7, _⟩ => 1 | ⟨8, _⟩ => 1 | ⟨9, _⟩ => -1
  | ⟨10, _⟩ => -1 | ⟨11, _⟩ => -1 | ⟨12, _⟩ => -1 | ⟨13, _⟩ => 1 | ⟨14, _⟩ => 1

theorem kernel12_eq_sign (d : Fin 15) :
    ReggeHinge4DStarKernel12.fullStarClassKernel d =
      (kernel12Sign d : ℝ) * (Real.sqrt 2 / 2) := by
  fin_cases d <;>
    simp [ReggeHinge4DStarKernel12.fullStarClassKernel, kernel12Sign] <;> ring

def kernel13Sign (d : Fin 15) : ℤ :=
  match d with
  | ⟨1, _⟩ => -1 | ⟨3, _⟩ => -1 | ⟨5, _⟩ => 1 | ⟨7, _⟩ => -1
  | ⟨9, _⟩ => 1 | ⟨11, _⟩ => 1 | ⟨13, _⟩ => -1
  | _ => 0

theorem kernel13_eq_sign (d : Fin 15) :
    ReggeHinge4DStarKernel13.fullStarClassKernel d =
      (kernel13Sign d : ℝ) * Real.sqrt 3 := by
  fin_cases d <;>
    simp [ReggeHinge4DStarKernel13.fullStarClassKernel, kernel13Sign]

def kernel22Sign (d : Fin 15) : ℤ :=
  match d with
  | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => -1 | ⟨3, _⟩ => 1 | ⟨4, _⟩ => -1
  | ⟨5, _⟩ => -1 | ⟨6, _⟩ => 1 | ⟨7, _⟩ => 1 | ⟨8, _⟩ => -1 | ⟨9, _⟩ => -1
  | ⟨10, _⟩ => 1 | ⟨11, _⟩ => -1 | ⟨12, _⟩ => 1 | ⟨13, _⟩ => 1 | ⟨14, _⟩ => -1

theorem kernel22_eq_sign (d : Fin 15) :
    ReggeHinge4DStarKernel22.fullStarClassKernel d = (kernel22Sign d : ℝ) := by
  fin_cases d <;> simp [ReggeHinge4DStarKernel22.fullStarClassKernel, kernel22Sign]

def signDotAxis (sign : Fin 15 → ℤ) : ℤ :=
  ∑ d : Fin 15, sign d * axisTTPlusCoeffZ d

def signDotGauge (sign : Fin 15 → ℤ) : ℤ :=
  ∑ d : Fin 15, sign d * (2 * (gaugeBit0 d : ℤ))

theorem signDotAxis_kernel11 : signDotAxis kernel11Sign = 0 := by
  unfold signDotAxis kernel11Sign axisTTPlusCoeffZ classBit maskOf; decide
theorem signDotAxis_kernel12 : signDotAxis kernel12Sign = 0 := by
  unfold signDotAxis kernel12Sign axisTTPlusCoeffZ classBit maskOf; decide
theorem signDotAxis_kernel13 : signDotAxis kernel13Sign = 0 := by
  unfold signDotAxis kernel13Sign axisTTPlusCoeffZ classBit maskOf; decide
theorem signDotAxis_kernel22 : signDotAxis kernel22Sign = 0 := by
  unfold signDotAxis kernel22Sign axisTTPlusCoeffZ classBit maskOf; decide

theorem signDotGauge_kernel11 : signDotGauge kernel11Sign = 0 := by
  unfold signDotGauge kernel11Sign gaugeBit0 classBit maskOf; decide
theorem signDotGauge_kernel12 : signDotGauge kernel12Sign = 0 := by
  unfold signDotGauge kernel12Sign gaugeBit0 classBit maskOf; decide
theorem signDotGauge_kernel13 : signDotGauge kernel13Sign = 0 := by
  unfold signDotGauge kernel13Sign gaugeBit0 classBit maskOf; decide
theorem signDotGauge_kernel22 : signDotGauge kernel22Sign = 0 := by
  unfold signDotGauge kernel22Sign gaugeBit0 classBit maskOf; decide

private lemma sum_sign_axis (sign : Fin 15 → ℤ) :
    (∑ d : Fin 15, (sign d : ℝ) * (axisTTPlusCoeffZ d : ℝ)) =
      (signDotAxis sign : ℝ) := by
  unfold signDotAxis; simp [Int.cast_sum, Int.cast_mul]

private lemma sum_sign_gauge (sign : Fin 15 → ℤ) :
    (∑ d : Fin 15, (sign d : ℝ) * ((2 : ℝ) * (gaugeBit0 d : ℝ))) =
      (signDotGauge sign : ℝ) := by
  unfold signDotGauge
  have h : ∀ d,
      (sign d : ℝ) * ((2 : ℝ) * (gaugeBit0 d : ℝ)) =
        ((sign d * (2 * (gaugeBit0 d : ℤ)) : ℤ) : ℝ) := by
    intro d; push_cast; ring
  simp_rw [h, ← Int.cast_sum]

theorem deficitKernel11_dot_axisTTPlus :
    classDot ReggeHinge4DStarKernel.fullStarClassKernel axisTTPlus = 0 := by
  unfold classDot coeffDot
  simp_rw [kernel11_eq_sign, classCoeff_axisTTPlus_int, sum_sign_axis,
    signDotAxis_kernel11]
  norm_num

theorem deficitKernel22_dot_axisTTPlus :
    classDot ReggeHinge4DStarKernel22.fullStarClassKernel axisTTPlus = 0 := by
  unfold classDot coeffDot
  simp_rw [kernel22_eq_sign, classCoeff_axisTTPlus_int, sum_sign_axis,
    signDotAxis_kernel22]
  norm_num

theorem deficitKernel12_dot_axisTTPlus :
    classDot ReggeHinge4DStarKernel12.fullStarClassKernel axisTTPlus = 0 := by
  unfold classDot coeffDot
  have h :
      (∑ d : Fin 15,
          ReggeHinge4DStarKernel12.fullStarClassKernel d *
            classCoeff axisTTPlus d) =
        (Real.sqrt 2 / 2) *
          ∑ d : Fin 15, (kernel12Sign d : ℝ) * (axisTTPlusCoeffZ d : ℝ) := by
    simp_rw [kernel12_eq_sign, classCoeff_axisTTPlus_int, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [h, sum_sign_axis, signDotAxis_kernel12]
  norm_num

theorem deficitKernel13_dot_axisTTPlus :
    classDot ReggeHinge4DStarKernel13.fullStarClassKernel axisTTPlus = 0 := by
  unfold classDot coeffDot
  have h :
      (∑ d : Fin 15,
          ReggeHinge4DStarKernel13.fullStarClassKernel d *
            classCoeff axisTTPlus d) =
        Real.sqrt 3 *
          ∑ d : Fin 15, (kernel13Sign d : ℝ) * (axisTTPlusCoeffZ d : ℝ) := by
    simp_rw [kernel13_eq_sign, classCoeff_axisTTPlus_int, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [h, sum_sign_axis, signDotAxis_kernel13]
  norm_num

theorem deficitKernel11_dot_decoyGauge :
    classDot ReggeHinge4DStarKernel.fullStarClassKernel decoyGauge = 0 := by
  unfold classDot coeffDot
  simp_rw [kernel11_eq_sign, classCoeff_decoyGauge_bit, sum_sign_gauge,
    signDotGauge_kernel11]
  norm_num

theorem deficitKernel22_dot_decoyGauge :
    classDot ReggeHinge4DStarKernel22.fullStarClassKernel decoyGauge = 0 := by
  unfold classDot coeffDot
  simp_rw [kernel22_eq_sign, classCoeff_decoyGauge_bit, sum_sign_gauge,
    signDotGauge_kernel22]
  norm_num

theorem deficitKernel12_dot_decoyGauge :
    classDot ReggeHinge4DStarKernel12.fullStarClassKernel decoyGauge = 0 := by
  unfold classDot coeffDot
  have h :
      (∑ d : Fin 15,
          ReggeHinge4DStarKernel12.fullStarClassKernel d *
            classCoeff decoyGauge d) =
        (Real.sqrt 2 / 2) *
          ∑ d : Fin 15,
            (kernel12Sign d : ℝ) * ((2 : ℝ) * (gaugeBit0 d : ℝ)) := by
    simp_rw [kernel12_eq_sign, classCoeff_decoyGauge_bit, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [h, sum_sign_gauge, signDotGauge_kernel12]
  norm_num

theorem deficitKernel13_dot_decoyGauge :
    classDot ReggeHinge4DStarKernel13.fullStarClassKernel decoyGauge = 0 := by
  unfold classDot coeffDot
  have h :
      (∑ d : Fin 15,
          ReggeHinge4DStarKernel13.fullStarClassKernel d *
            classCoeff decoyGauge d) =
        Real.sqrt 3 *
          ∑ d : Fin 15,
            (kernel13Sign d : ℝ) * ((2 : ℝ) * (gaugeBit0 d : ℝ)) := by
    simp_rw [kernel13_eq_sign, classCoeff_decoyGauge_bit, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [h, sum_sign_gauge, signDotGauge_kernel13]
  norm_num

theorem deficitKernel11_dot_decoyTrace :
    classDot ReggeHinge4DStarKernel.fullStarClassKernel decoyTrace = 0 := by
  -- classCoeff decoyTrace = classWeightNat; use committed homothety stationarity
  have hv : classCoeff decoyTrace = fun d => (classWeightNat d : ℝ) := by
    funext d; rw [classCoeff_decoyTrace, classDispSq_eq_weight]
  unfold classDot coeffDot
  -- ∑ K * w = ∑ w * K = fullStarDirectional w
  have h :
      (∑ d : Fin 15,
          ReggeHinge4DStarKernel.fullStarClassKernel d *
            classCoeff decoyTrace d) =
        ReggeHinge4DStarKernel.fullStarDirectional
          (fun d => (classWeightNat d : ℝ)) := by
    rw [hv]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  rw [h]
  exact ReggeHinge4DStarKernel.fullStar_homothety_stationary

theorem deficitKernel12_dot_decoyTrace :
    classDot ReggeHinge4DStarKernel12.fullStarClassKernel decoyTrace = 0 := by
  have hv : classCoeff decoyTrace = fun d => (classWeightNat d : ℝ) := by
    funext d; rw [classCoeff_decoyTrace, classDispSq_eq_weight]
  unfold classDot coeffDot
  have h :
      (∑ d : Fin 15,
          ReggeHinge4DStarKernel12.fullStarClassKernel d *
            classCoeff decoyTrace d) =
        ReggeHinge4DStarKernel12.fullStarDirectional
          (fun d => (classWeightNat d : ℝ)) := by
    rw [hv]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  rw [h]
  exact ReggeHinge4DStarKernel12.fullStar_homothety_stationary

theorem deficitKernel13_dot_decoyTrace :
    classDot ReggeHinge4DStarKernel13.fullStarClassKernel decoyTrace = 0 := by
  have hv : classCoeff decoyTrace = fun d => (classWeightNat d : ℝ) := by
    funext d; rw [classCoeff_decoyTrace, classDispSq_eq_weight]
  unfold classDot coeffDot
  have h :
      (∑ d : Fin 15,
          ReggeHinge4DStarKernel13.fullStarClassKernel d *
            classCoeff decoyTrace d) =
        ReggeHinge4DStarKernel13.fullStarDirectional
          (fun d => (classWeightNat d : ℝ)) := by
    rw [hv]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  rw [h]
  exact ReggeHinge4DStarKernel13.fullStar_homothety_stationary

theorem deficitKernel22_dot_decoyTrace :
    classDot ReggeHinge4DStarKernel22.fullStarClassKernel decoyTrace = 0 := by
  have hv : classCoeff decoyTrace = fun d => (classWeightNat d : ℝ) := by
    funext d; rw [classCoeff_decoyTrace, classDispSq_eq_weight]
  unfold classDot coeffDot
  have h :
      (∑ d : Fin 15,
          ReggeHinge4DStarKernel22.fullStarClassKernel d *
            classCoeff decoyTrace d) =
        ReggeHinge4DStarKernel22.fullStarDirectional
          (fun d => (classWeightNat d : ℝ)) := by
    rw [hv]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  rw [h]
  exact ReggeHinge4DStarKernel22.fullStar_homothety_stationary

theorem deficitKernel11_dot_homothety :
    classDot ReggeHinge4DStarKernel.fullStarClassKernel decoyTrace = 0 :=
  deficitKernel11_dot_decoyTrace
theorem deficitKernel12_dot_homothety :
    classDot ReggeHinge4DStarKernel12.fullStarClassKernel decoyTrace = 0 :=
  deficitKernel12_dot_decoyTrace
theorem deficitKernel13_dot_homothety :
    classDot ReggeHinge4DStarKernel13.fullStarClassKernel decoyTrace = 0 :=
  deficitKernel13_dot_decoyTrace
theorem deficitKernel22_dot_homothety :
    classDot ReggeHinge4DStarKernel22.fullStarClassKernel decoyTrace = 0 :=
  deficitKernel22_dot_decoyTrace

theorem orbitDeficit_dot_axisTTPlus (ty : HingeOrbitType) :
    classDot (orbitDeficitKernel ty) axisTTPlus = 0 := by
  cases ty with
  | t11 => exact deficitKernel11_dot_axisTTPlus
  | t12 => exact deficitKernel12_dot_axisTTPlus
  | t21 => simpa [orbitDeficitKernel, kernel21] using
      deficitKernel12_dot_axisTTPlus
  | t13 => exact deficitKernel13_dot_axisTTPlus
  | t31 => simpa [orbitDeficitKernel, kernel31] using
      deficitKernel13_dot_axisTTPlus
  | t22 => exact deficitKernel22_dot_axisTTPlus

theorem orbitDeficit_dot_decoyGauge (ty : HingeOrbitType) :
    classDot (orbitDeficitKernel ty) decoyGauge = 0 := by
  cases ty with
  | t11 => exact deficitKernel11_dot_decoyGauge
  | t12 => exact deficitKernel12_dot_decoyGauge
  | t21 => simpa [orbitDeficitKernel, kernel21] using
      deficitKernel12_dot_decoyGauge
  | t13 => exact deficitKernel13_dot_decoyGauge
  | t31 => simpa [orbitDeficitKernel, kernel31] using
      deficitKernel13_dot_decoyGauge
  | t22 => exact deficitKernel22_dot_decoyGauge

theorem orbitDeficit_dot_decoyTrace (ty : HingeOrbitType) :
    classDot (orbitDeficitKernel ty) decoyTrace = 0 := by
  cases ty with
  | t11 => exact deficitKernel11_dot_decoyTrace
  | t12 => exact deficitKernel12_dot_decoyTrace
  | t21 => simpa [orbitDeficitKernel, kernel21] using
      deficitKernel12_dot_decoyTrace
  | t13 => exact deficitKernel13_dot_decoyTrace
  | t31 => simpa [orbitDeficitKernel, kernel31] using
      deficitKernel13_dot_decoyTrace
  | t22 => exact deficitKernel22_dot_decoyTrace

/-! ## §7. Named evaluations -/

private lemma orbitQuadratic_of_deficit_zero (ty : HingeOrbitType) (H : Mat4)
    (h : classDot (orbitDeficitKernel ty) H = 0) :
    orbitZeroMomQuadratic ty H = 0 := by
  unfold orbitZeroMomQuadratic; rw [h, mul_zero]

theorem trueWeightZeroMomQuadratic_axisTTPlus :
    trueWeightZeroMomQuadratic axisTTPlus = 0 := by
  unfold trueWeightZeroMomQuadratic
  exact Finset.sum_eq_zero fun ty _ =>
    orbitQuadratic_of_deficit_zero ty _ (orbitDeficit_dot_axisTTPlus ty)

theorem trueWeightZeroMomQuadratic_decoyGauge :
    trueWeightZeroMomQuadratic decoyGauge = 0 := by
  unfold trueWeightZeroMomQuadratic
  exact Finset.sum_eq_zero fun ty _ =>
    orbitQuadratic_of_deficit_zero ty _ (orbitDeficit_dot_decoyGauge ty)

theorem trueWeightZeroMomQuadratic_decoyTrace :
    trueWeightZeroMomQuadratic decoyTrace = 0 := by
  unfold trueWeightZeroMomQuadratic
  exact Finset.sum_eq_zero fun ty _ =>
    orbitQuadratic_of_deficit_zero ty _ (orbitDeficit_dot_decoyTrace ty)

def homothetyClassCoeff : Mat4 := decoyTrace

theorem trueWeightZeroMomQuadratic_homothety :
    trueWeightZeroMomQuadratic homothetyClassCoeff = 0 := by
  unfold homothetyClassCoeff
  exact trueWeightZeroMomQuadratic_decoyTrace

theorem trueWeight_kills_gauge_at_zero_momentum :
    trueWeightZeroMomQuadratic decoyGauge = 0 ∧
      finiteTTQuadratic decoyGauge = 32 :=
  ⟨trueWeightZeroMomQuadratic_decoyGauge, finiteTTQuadratic_decoyGauge⟩

/-! ## §8. Status -/

structure Flat4DHessianAssemblyStatus where
  areaGradientsClosed : Bool
  complementTransportClosed : Bool
  zeroMomentumHessianClosed : Bool
  finiteMomentumBlochOpen : Bool
  convergesEH4d : Bool
  gapActionRecovery : Bool

def flat4DHessianAssemblyStatus : Flat4DHessianAssemblyStatus where
  areaGradientsClosed := true
  complementTransportClosed := true
  zeroMomentumHessianClosed := true
  finiteMomentumBlochOpen := true
  convergesEH4d := false
  gapActionRecovery := false

theorem flat4DHessianAssemblyStatus_flags :
    flat4DHessianAssemblyStatus.areaGradientsClosed = true ∧
      flat4DHessianAssemblyStatus.complementTransportClosed = true ∧
        flat4DHessianAssemblyStatus.zeroMomentumHessianClosed = true ∧
          flat4DHessianAssemblyStatus.finiteMomentumBlochOpen = true ∧
            flat4DHessianAssemblyStatus.convergesEH4d = false ∧
              flat4DHessianAssemblyStatus.gapActionRecovery = false := by
  decide

end

end ReggeFlat4DHessianAssembly
end Analysis
end Gravity
end IndisputableMonolith
