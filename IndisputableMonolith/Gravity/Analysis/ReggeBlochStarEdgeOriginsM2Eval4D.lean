import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeBlochStarEdgeOrigins4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbitM2Eval4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochM2Symbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeFlat4DHessianAssembly
/-!
# Edge-origin m² evaluation certificates (fold repair)

Closes the distinct-hinge edge-origin moment on TT / `symbolDir`:

  `m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir = -1/4`
  `m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTCross symbolDir = -1/4`

Orbit slices on plus (edge mode): t11=-3, t12=t21=t31=t22=0, t13=3/2
so `-3/6 + (3/2)/6 = -1/4`.

Also kills the pure-gauge counterexample `gaugePart (1,1,0,0) e₂` and
`decoyGauge` on `symbolDir`.

Integer certificates: radical-cancelled `decide` on `Fin 24 × Fin 10`.
Python oracle: `scripts/qg/regge_4d_fold_position_resolved_20260721.py` (mode=edge).

Does **not** flip `gap_action_recovery`. Forbidden: base0, covering-perm chase.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeBlochStarEdgeOriginsM2Eval4D

open BigOperators
open ReggeEdgeStencil4D
open ReggeHinge4DOrbitClassification
open ReggeBlochFold4D
open ReggeBlochM2Symbol4D
open ReggeBlochOrbitTransport4D
open ReggeBlochTransportedAllOrbit4D
open ReggeBlochAllOrbitSymbol4D (isOrbit phaseScaleDir)
open ReggeBlochStarEdgeOrigins4D
open ReggeBlochTransportedAllOrbitM2Eval4D
open ReggeFlat4DHessianAssembly
open EdgeTTDecomposition4D (axisTTPlus axisTTCross gaugePart)

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev Wave4 := Fin 4 → ℝ

noncomputable section

/-! ## §1. Integer seed edge contributions -/

structure SeedEdgeContribZ where
  cls : Fin 15
  weightZ : ℤ
  originZ : Fin 4 → ℤ

def toReal12 (c : SeedEdgeContribZ) : SeedEdgeContrib where
  cls := c.cls
  weight := (c.weightZ : ℝ) * Real.sqrt 2 / 4
  origin := fun i => (c.originZ i : ℝ)

def toReal13 (c : SeedEdgeContribZ) : SeedEdgeContrib where
  cls := c.cls
  weight := (c.weightZ : ℝ) * Real.sqrt 3 / 12
  origin := fun i => (c.originZ i : ℝ)

def toReal22 (c : SeedEdgeContribZ) : SeedEdgeContrib where
  cls := c.cls
  weight := (c.weightZ : ℝ) / 4
  origin := fun i => (c.originZ i : ℝ)

def seedEdgeContribsZ_t12 : List SeedEdgeContribZ :=
  [

    ⟨(5 : Fin 15), (-1 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(13 : Fin 15), (1 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(3 : Fin 15), (2 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(7 : Fin 15), (1 : ℤ), ![1, 1, 1, 0]⟩,
    ⟨(11 : Fin 15), (-2 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(5 : Fin 15), (-1 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(13 : Fin 15), (1 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(1 : Fin 15), (2 : ℤ), ![1, 0, 1, 0]⟩,
    ⟨(7 : Fin 15), (1 : ℤ), ![1, 1, 1, 0]⟩,
    ⟨(9 : Fin 15), (-2 : ℤ), ![1, 0, 1, 0]⟩,
    ⟨(0 : Fin 15), (-1 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(6 : Fin 15), (-1 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(2 : Fin 15), (2 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(8 : Fin 15), (1 : ℤ), ![0, 0, 0, -1]⟩,
    ⟨(14 : Fin 15), (1 : ℤ), ![0, 0, 0, -1]⟩,
    ⟨(10 : Fin 15), (-2 : ℤ), ![0, 0, 0, -1]⟩,
    ⟨(0 : Fin 15), (-1 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(6 : Fin 15), (-1 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(4 : Fin 15), (2 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(8 : Fin 15), (1 : ℤ), ![0, 0, 0, -1]⟩,
    ⟨(14 : Fin 15), (1 : ℤ), ![0, 0, 0, -1]⟩,
    ⟨(12 : Fin 15), (-2 : ℤ), ![0, 0, 0, -1]⟩

  ]

def seedEdgeContribsZ_t13 : List SeedEdgeContribZ :=
  [

    ⟨(13 : Fin 15), (-2 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(5 : Fin 15), (3 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(11 : Fin 15), (3 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(3 : Fin 15), (-6 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(13 : Fin 15), (-2 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(9 : Fin 15), (3 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(11 : Fin 15), (3 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(7 : Fin 15), (-6 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(13 : Fin 15), (-2 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(5 : Fin 15), (3 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(9 : Fin 15), (3 : ℤ), ![1, 0, 1, 0]⟩,
    ⟨(1 : Fin 15), (-6 : ℤ), ![1, 0, 1, 0]⟩,
    ⟨(13 : Fin 15), (-2 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(11 : Fin 15), (3 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(9 : Fin 15), (3 : ℤ), ![1, 0, 1, 0]⟩,
    ⟨(7 : Fin 15), (-6 : ℤ), ![1, 0, 1, 0]⟩,
    ⟨(13 : Fin 15), (-2 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(9 : Fin 15), (3 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(5 : Fin 15), (3 : ℤ), ![1, 0, 0, 1]⟩,
    ⟨(1 : Fin 15), (-6 : ℤ), ![1, 0, 0, 1]⟩,
    ⟨(13 : Fin 15), (-2 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(11 : Fin 15), (3 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(5 : Fin 15), (3 : ℤ), ![1, 0, 0, 1]⟩,
    ⟨(3 : Fin 15), (-6 : ℤ), ![1, 0, 0, 1]⟩

  ]

def seedEdgeContribsZ_t22 : List SeedEdgeContribZ :=
  [

    ⟨(2 : Fin 15), (-1 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(14 : Fin 15), (-1 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(6 : Fin 15), (2 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(11 : Fin 15), (-1 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(1 : Fin 15), (2 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(3 : Fin 15), (2 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(13 : Fin 15), (2 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(5 : Fin 15), (-4 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(2 : Fin 15), (-1 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(14 : Fin 15), (-1 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(10 : Fin 15), (2 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(11 : Fin 15), (-1 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(1 : Fin 15), (2 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(7 : Fin 15), (2 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(13 : Fin 15), (2 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(9 : Fin 15), (-4 : ℤ), ![1, 0, 0, 0]⟩,
    ⟨(2 : Fin 15), (-1 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(14 : Fin 15), (-1 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(6 : Fin 15), (2 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(11 : Fin 15), (-1 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(0 : Fin 15), (2 : ℤ), ![0, 1, 0, 0]⟩,
    ⟨(3 : Fin 15), (2 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(12 : Fin 15), (2 : ℤ), ![0, 1, 0, 0]⟩,
    ⟨(4 : Fin 15), (-4 : ℤ), ![0, 1, 0, 0]⟩,
    ⟨(2 : Fin 15), (-1 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(14 : Fin 15), (-1 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(10 : Fin 15), (2 : ℤ), ![0, 0, 0, 0]⟩,
    ⟨(11 : Fin 15), (-1 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(0 : Fin 15), (2 : ℤ), ![0, 1, 0, 0]⟩,
    ⟨(7 : Fin 15), (2 : ℤ), ![1, 1, 0, 0]⟩,
    ⟨(12 : Fin 15), (2 : ℤ), ![0, 1, 0, 0]⟩,
    ⟨(8 : Fin 15), (-4 : ℤ), ![0, 1, 0, 0]⟩

  ]

def seedEdgeContribsZ_t21 : List SeedEdgeContribZ := seedEdgeContribsZ_t12
def seedEdgeContribsZ_t31 : List SeedEdgeContribZ := seedEdgeContribsZ_t13

theorem seedEdgeContribsZ_t12_length : seedEdgeContribsZ_t12.length = 22 := rfl
theorem seedEdgeContribsZ_t13_length : seedEdgeContribsZ_t13.length = 24 := rfl
theorem seedEdgeContribsZ_t22_length : seedEdgeContribsZ_t22.length = 32 := rfl

/-! ## §2. Integer phase at edge origins (symbolDir) -/

def hingeBaseZ (s : Fin 24) (t : Fin 10) (i : Fin 4) : ℤ :=
  if Nat.testBit (triangleVertexMasks s t).1 i.val then (1 : ℤ) else 0

def transportOriginZ (p : Fin 24) (off : Fin 4 → ℤ) (i : Fin 4) : ℤ :=
  ∑ j : Fin 4, if coordPermOf p j = i then off j else 0

/-- `2 * phaseScale (base + transportOrigin off) d` for `symbolDir`. -/
def phase2EdgeSymbolZ (s : Fin 24) (t : Fin 10) (p : Fin 24)
    (off : Fin 4 → ℤ) (d : Fin 15) : ℤ :=
  2 * (hingeBaseZ s t 0 + transportOriginZ p off 0 +
        hingeBaseZ s t 1 + transportOriginZ p off 1) +
    (if classBit d 0 then (1 : ℤ) else 0) +
      (if classBit d 1 then (1 : ℤ) else 0)

/-! ## §3. Per-orbit edge Kpp certificates -/

def edgePhase2Z (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) (p : Fin 24)
    (c : SeedEdgeContribZ) : ℤ :=
  c.weightZ * cz (permClass p c.cls) *
    (phase2EdgeSymbolZ s t p c.originZ (permClass p c.cls)) ^ 2

def slotKppEdge (seeds : List SeedEdgeContribZ) (cz : Fin 15 → ℤ)
    (ty : HingeOrbitType) (s : Fin 24) (t : Fin 10) : ℤ :=
  let p := orbitCoveringPerm ty s t
  (seeds.map (edgePhase2Z cz s t p)).sum

def m2OrbitCertZ12Edge (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t12 s t then
    -slotAZ12 cz s t * slotKppEdge seedEdgeContribsZ_t12 cz .t12 s t
  else 0

def m2OrbitCertZ21Edge (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t21 s t then
    -slotAZ21 cz s t * slotKppEdge seedEdgeContribsZ_t21 cz .t21 s t
  else 0

def m2OrbitCertZ13Edge (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t13 s t then
    -slotAZ13 cz s t * slotKppEdge seedEdgeContribsZ_t13 cz .t13 s t
  else 0

def m2OrbitCertZ31Edge (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t31 s t then
    -slotAZ31 cz s t * slotKppEdge seedEdgeContribsZ_t31 cz .t31 s t
  else 0

def m2OrbitCertZ22Edge (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t22 s t then
    -slotAZ22 cz s t * slotKppEdge seedEdgeContribsZ_t22 cz .t22 s t
  else 0

/-! ## §4. Pure-gauge counterexample coefficients -/

/-- `gaugePart m v` for `m=(1,1,0,0)`, `v=e₂`: `2 (D₀+D₁) D₂`. -/
def gaugeM1100E2CoeffZ (d : Fin 15) : ℤ :=
  2 * ((if classBit d 0 then (1 : ℤ) else 0) +
        (if classBit d 1 then (1 : ℤ) else 0)) *
    (if classBit d 2 then (1 : ℤ) else 0)

def gaugeM1100E2 : Mat4 :=
  gaugePart (![(1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ)])
    (![(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ)])

theorem classCoeff_gaugeM1100E2_int (d : Fin 15) :
    classCoeff gaugeM1100E2 d = (gaugeM1100E2CoeffZ d : ℝ) := by
  unfold gaugeM1100E2 gaugeM1100E2CoeffZ
  rw [classCoeff_gaugePart]
  simp [classDisp, Fin.sum_univ_four]

/-! ## §5. Seed table bridges (real ↔ integer) -/

theorem seedEdgeContribs_t12_eq_Z :
    seedEdgeContribs_t12 = seedEdgeContribsZ_t12.map toReal12 := by
  unfold seedEdgeContribs_t12 seedEdgeContribsZ_t12 toReal12
  rfl

theorem seedEdgeContribs_t21_eq_Z :
    seedEdgeContribs_t21 = seedEdgeContribsZ_t21.map toReal12 := by
  simpa [seedEdgeContribs_t21, seedEdgeContribsZ_t21] using seedEdgeContribs_t12_eq_Z

theorem seedEdgeContribs_t13_eq_Z :
    seedEdgeContribs_t13 = seedEdgeContribsZ_t13.map toReal13 := by
  unfold seedEdgeContribs_t13 seedEdgeContribsZ_t13 toReal13
  rfl

theorem seedEdgeContribs_t31_eq_Z :
    seedEdgeContribs_t31 = seedEdgeContribsZ_t31.map toReal13 := by
  simpa [seedEdgeContribs_t31, seedEdgeContribsZ_t31] using seedEdgeContribs_t13_eq_Z

theorem seedEdgeContribs_t22_eq_Z :
    seedEdgeContribs_t22 = seedEdgeContribsZ_t22.map toReal22 := by
  unfold seedEdgeContribs_t22 seedEdgeContribsZ_t22 toReal22
  rfl

/-! ## §6. Phase bridge -/

private lemma transportOrigin_int (p : Fin 24) (off : Fin 4 → ℤ) (i : Fin 4) :
    transportOrigin p (fun j => (off j : ℝ)) i = (transportOriginZ p off i : ℝ) := by
  unfold transportOrigin transportOriginZ
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

private lemma hingeBase_int (s : Fin 24) (t : Fin 10) (i : Fin 4) :
    hingeBase s t i = (hingeBaseZ s t i : ℝ) := by
  unfold hingeBase hingeBaseZ maskCoord
  split_ifs <;> simp

theorem phaseScale_edge_eq_phase2EdgeSymbolZ (s : Fin 24) (t : Fin 10)
    (p : Fin 24) (off : Fin 4 → ℤ) (d : Fin 15) :
    phaseScale
        (fun i => hingeBase s t i + transportOrigin p (fun j => (off j : ℝ)) i) d =
      (phase2EdgeSymbolZ s t p off d : ℝ) / 2 := by
  unfold phaseScale phase2EdgeSymbolZ symbolDir
  simp only [Fin.sum_univ_four]
  have h0 := hingeBase_int s t (0 : Fin 4)
  have h1 := hingeBase_int s t (1 : Fin 4)
  have h2 := hingeBase_int s t (2 : Fin 4)
  have h3 := hingeBase_int s t (3 : Fin 4)
  have t0 := transportOrigin_int p off (0 : Fin 4)
  have t1 := transportOrigin_int p off (1 : Fin 4)
  have t2 := transportOrigin_int p off (2 : Fin 4)
  have t3 := transportOrigin_int p off (3 : Fin 4)
  simp [h0, h1, h2, h3, t0, t1, t2, t3, classDisp]
  --  (x0+x1) + (D0+D1)/2 = (2(x0+x1)+D0+D1)/2
  cases classBit d 0 <;> cases classBit d 1 <;> push_cast <;> ring

/-! ## §7. Radical slot arithmetic (edge Kpp) -/

private lemma sqrt2_mul_self : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
  simpa [pow_two] using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

private lemma sqrt3_mul_self : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := by
  simpa [pow_two] using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)

private lemma radical2_edge_slot_arith (AZ K : ℤ) :
    Real.sqrt 2 * (AZ : ℝ) / 8 *
        (-(1 / 2 : ℝ) * (Real.sqrt 2 * (K : ℝ) / 16)) =
      ((-AZ * K : ℤ) : ℝ) / 128 := by
  have hs := sqrt2_mul_self
  ring_nf
  rw [show (Real.sqrt 2) ^ 2 = (2 : ℝ) by simpa [pow_two] using hs]
  push_cast; ring

private lemma radical3_edge_slot_arith (AZ K : ℤ) :
    Real.sqrt 3 * (AZ : ℝ) / 12 *
        (-(1 / 2 : ℝ) * (Real.sqrt 3 * (K : ℝ) / 48)) =
      ((-AZ * K : ℤ) : ℝ) / 384 := by
  have hs := sqrt3_mul_self
  ring_nf
  rw [show (Real.sqrt 3) ^ 2 = (3 : ℝ) by simpa [pow_two] using hs]
  push_cast; ring

private lemma rational_edge_slot_arith (AZ K : ℤ) :
    (AZ : ℝ) / 4 * (-(1 / 2 : ℝ) * ((K : ℝ) / 16)) =
      ((-AZ * K : ℤ) : ℝ) / 128 := by
  push_cast; ring

private lemma sum_div_const_st (c : ℝ) (f : Fin 24 → Fin 10 → ℝ) :
    (∑ s : Fin 24, ∑ t : Fin 10, f s t / c) =
      (∑ s : Fin 24, ∑ t : Fin 10, f s t) / c := by
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul]

/-! ## §8. Phase² sum = radical × integer Kpp -/

private lemma edgeContribPhase2_toReal12 (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10)
    (p : Fin 24) (c : SeedEdgeContribZ) :
    edgeContribPhase2 p (hingeBase s t) H symbolDir (toReal12 c) =
      Real.sqrt 2 * (edgePhase2Z cz s t p c : ℝ) / 16 := by
  unfold edgeContribPhase2 toReal12 edgePhase2Z
  rw [hH, phaseScaleDir_symbolDir, phaseScale_edge_eq_phase2EdgeSymbolZ]
  push_cast; ring

private lemma edgeContribPhase2_toReal13 (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10)
    (p : Fin 24) (c : SeedEdgeContribZ) :
    edgeContribPhase2 p (hingeBase s t) H symbolDir (toReal13 c) =
      Real.sqrt 3 * (edgePhase2Z cz s t p c : ℝ) / 48 := by
  unfold edgeContribPhase2 toReal13 edgePhase2Z
  rw [hH, phaseScaleDir_symbolDir, phaseScale_edge_eq_phase2EdgeSymbolZ]
  push_cast; ring

private lemma edgeContribPhase2_toReal22 (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10)
    (p : Fin 24) (c : SeedEdgeContribZ) :
    edgeContribPhase2 p (hingeBase s t) H symbolDir (toReal22 c) =
      (edgePhase2Z cz s t p c : ℝ) / 16 := by
  unfold edgeContribPhase2 toReal22 edgePhase2Z
  rw [hH, phaseScaleDir_symbolDir, phaseScale_edge_eq_phase2EdgeSymbolZ]
  push_cast; ring

private lemma list_sum_map_sqrt2_div16 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10)
    (p : Fin 24) (seeds : List SeedEdgeContribZ) (H : Mat4)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) :
    (seeds.map (fun c => edgeContribPhase2 p (hingeBase s t) H symbolDir (toReal12 c))).sum =
      Real.sqrt 2 * ((seeds.map (edgePhase2Z cz s t p)).sum : ℤ) / 16 := by
  induction seeds with
  | nil => simp
  | cons c rest ih =>
    simp [List.map, List.sum_cons, edgeContribPhase2_toReal12 H cz hH s t p c, ih]
    push_cast; ring

private lemma list_sum_map_sqrt3_div48 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10)
    (p : Fin 24) (seeds : List SeedEdgeContribZ) (H : Mat4)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) :
    (seeds.map (fun c => edgeContribPhase2 p (hingeBase s t) H symbolDir (toReal13 c))).sum =
      Real.sqrt 3 * ((seeds.map (edgePhase2Z cz s t p)).sum : ℤ) / 48 := by
  induction seeds with
  | nil => simp
  | cons c rest ih =>
    simp [List.map, List.sum_cons, edgeContribPhase2_toReal13 H cz hH s t p c, ih]
    push_cast; ring

private lemma list_sum_map_div16 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10)
    (p : Fin 24) (seeds : List SeedEdgeContribZ) (H : Mat4)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) :
    (seeds.map (fun c => edgeContribPhase2 p (hingeBase s t) H symbolDir (toReal22 c))).sum =
      ((seeds.map (edgePhase2Z cz s t p)).sum : ℤ) / 16 := by
  induction seeds with
  | nil => simp
  | cons c rest ih =>
    simp [List.map, List.sum_cons, edgeContribPhase2_toReal22 H cz hH s t p c, ih]
    push_cast; ring

theorem slotOrbitDeficitPhase2EdgeOrigins_t12_eq_Z (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    slotOrbitDeficitPhase2EdgeOrigins .t12 H symbolDir s t =
      Real.sqrt 2 *
        (slotKppEdge seedEdgeContribsZ_t12 cz .t12 s t : ℝ) / 16 := by
  unfold slotOrbitDeficitPhase2EdgeOrigins
  simp only [seedEdgeContribs]
  rw [seedEdgeContribs_t12_eq_Z, List.map_map]
  unfold slotKppEdge
  simpa [Function.comp] using
    list_sum_map_sqrt2_div16 cz s t (orbitCoveringPerm .t12 s t)
      seedEdgeContribsZ_t12 H hH

theorem slotOrbitDeficitPhase2EdgeOrigins_t21_eq_Z (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    slotOrbitDeficitPhase2EdgeOrigins .t21 H symbolDir s t =
      Real.sqrt 2 *
        (slotKppEdge seedEdgeContribsZ_t21 cz .t21 s t : ℝ) / 16 := by
  unfold slotOrbitDeficitPhase2EdgeOrigins
  simp only [seedEdgeContribs]
  rw [seedEdgeContribs_t21_eq_Z, List.map_map]
  unfold slotKppEdge
  simpa [Function.comp] using
    list_sum_map_sqrt2_div16 cz s t (orbitCoveringPerm .t21 s t)
      seedEdgeContribsZ_t21 H hH

theorem slotOrbitDeficitPhase2EdgeOrigins_t13_eq_Z (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    slotOrbitDeficitPhase2EdgeOrigins .t13 H symbolDir s t =
      Real.sqrt 3 *
        (slotKppEdge seedEdgeContribsZ_t13 cz .t13 s t : ℝ) / 48 := by
  unfold slotOrbitDeficitPhase2EdgeOrigins
  simp only [seedEdgeContribs]
  rw [seedEdgeContribs_t13_eq_Z, List.map_map]
  unfold slotKppEdge
  simpa [Function.comp] using
    list_sum_map_sqrt3_div48 cz s t (orbitCoveringPerm .t13 s t)
      seedEdgeContribsZ_t13 H hH

theorem slotOrbitDeficitPhase2EdgeOrigins_t31_eq_Z (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    slotOrbitDeficitPhase2EdgeOrigins .t31 H symbolDir s t =
      Real.sqrt 3 *
        (slotKppEdge seedEdgeContribsZ_t31 cz .t31 s t : ℝ) / 48 := by
  unfold slotOrbitDeficitPhase2EdgeOrigins
  simp only [seedEdgeContribs]
  rw [seedEdgeContribs_t31_eq_Z, List.map_map]
  unfold slotKppEdge
  simpa [Function.comp] using
    list_sum_map_sqrt3_div48 cz s t (orbitCoveringPerm .t31 s t)
      seedEdgeContribsZ_t31 H hH

theorem slotOrbitDeficitPhase2EdgeOrigins_t22_eq_Z (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    slotOrbitDeficitPhase2EdgeOrigins .t22 H symbolDir s t =
      (slotKppEdge seedEdgeContribsZ_t22 cz .t22 s t : ℝ) / 16 := by
  unfold slotOrbitDeficitPhase2EdgeOrigins
  simp only [seedEdgeContribs]
  rw [seedEdgeContribs_t22_eq_Z, List.map_map]
  unfold slotKppEdge
  simpa [Function.comp] using
    list_sum_map_div16 cz s t (orbitCoveringPerm .t22 s t)
      seedEdgeContribsZ_t22 H hH

/-! ## §9. Area push helpers (local copies; sibling lemmas are private) -/

private lemma area_push_sqrt2 (areaZ : Fin 15 → ℤ) (cz : Fin 15 → ℤ)
    (p : Fin 24) (H : Mat4) (hH : ∀ d, classCoeff H d = (cz d : ℝ))
    (area : Fin 15 → ℝ)
    (harea : ∀ d, area d = Real.sqrt 2 * (areaZ d : ℝ) / 8) :
    (∑ d0 : Fin 15, area d0 * classCoeff H (permClass p d0)) =
      Real.sqrt 2 *
        (∑ d0 : Fin 15, areaZ d0 * cz (permClass p d0) : ℤ) / 8 := by
  simp_rw [harea, hH]
  calc
    (∑ d0 : Fin 15,
        Real.sqrt 2 * (areaZ d0 : ℝ) / 8 * (cz (permClass p d0) : ℝ)) =
        Real.sqrt 2 / 8 *
          ∑ d0 : Fin 15,
            (areaZ d0 : ℝ) * (cz (permClass p d0) : ℝ) := by
      refine Eq.trans ?_ (Finset.mul_sum _ _ _).symm
      refine Finset.sum_congr rfl fun d0 _ => by ring
    _ = Real.sqrt 2 *
          (∑ d0 : Fin 15, areaZ d0 * cz (permClass p d0) : ℤ) / 8 := by
      rw [Int.cast_sum]
      push_cast; ring

private lemma area_push_sqrt3 (areaZ : Fin 15 → ℤ) (cz : Fin 15 → ℤ)
    (p : Fin 24) (H : Mat4) (hH : ∀ d, classCoeff H d = (cz d : ℝ))
    (area : Fin 15 → ℝ)
    (harea : ∀ d, area d = Real.sqrt 3 * (areaZ d : ℝ) / 12) :
    (∑ d0 : Fin 15, area d0 * classCoeff H (permClass p d0)) =
      Real.sqrt 3 *
        (∑ d0 : Fin 15, areaZ d0 * cz (permClass p d0) : ℤ) / 12 := by
  simp_rw [harea, hH]
  calc
    (∑ d0 : Fin 15,
        Real.sqrt 3 * (areaZ d0 : ℝ) / 12 * (cz (permClass p d0) : ℝ)) =
        Real.sqrt 3 / 12 *
          ∑ d0 : Fin 15,
            (areaZ d0 : ℝ) * (cz (permClass p d0) : ℝ) := by
      refine Eq.trans ?_ (Finset.mul_sum _ _ _).symm
      refine Finset.sum_congr rfl fun d0 _ => by ring
    _ = Real.sqrt 3 *
          (∑ d0 : Fin 15, areaZ d0 * cz (permClass p d0) : ℤ) / 12 := by
      rw [Int.cast_sum]
      push_cast; ring

/-! ## §10. Slot coefficient = certificate / denom -/

theorem m2OrbitSlotCoeffEdgeOrigins_t12_eq_cert (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2OrbitSlotCoeffEdgeOrigins .t12 H symbolDir s t =
      (m2OrbitCertZ12Edge cz s t : ℝ) / 128 := by
  unfold m2OrbitSlotCoeffEdgeOrigins m2OrbitCertZ12Edge
  by_cases ht : isOrbit .t12 s t
  · simp only [ht, ite_true]
    set p := orbitCoveringPerm .t12 s t with hp
    have hA :
        (∑ d : Fin 15, slotOrbitAreaCov .t12 s t d * classCoeff H d) =
          Real.sqrt 2 * (slotAZ12 cz s t : ℝ) / 8 := by
      simp only [slotOrbitAreaCov, transportedOrbitArea, orbitAreaCov]
      rw [sum_mul_pushforward, ← hp]
      simpa [slotAZ12, hp] using
        area_push_sqrt2 area12Z cz p H hH areaCov12 areaCov12_eq_z
    rw [hA, slotOrbitDeficitPhase2EdgeOrigins_t12_eq_Z H cz hH s t]
    exact radical2_edge_slot_arith (slotAZ12 cz s t)
      (slotKppEdge seedEdgeContribsZ_t12 cz .t12 s t)
  · simp [ht]

theorem m2OrbitSlotCoeffEdgeOrigins_t21_eq_cert (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2OrbitSlotCoeffEdgeOrigins .t21 H symbolDir s t =
      (m2OrbitCertZ21Edge cz s t : ℝ) / 128 := by
  unfold m2OrbitSlotCoeffEdgeOrigins m2OrbitCertZ21Edge
  by_cases ht : isOrbit .t21 s t
  · simp only [ht, ite_true]
    set p := orbitCoveringPerm .t21 s t with hp
    have hA :
        (∑ d : Fin 15, slotOrbitAreaCov .t21 s t d * classCoeff H d) =
          Real.sqrt 2 * (slotAZ21 cz s t : ℝ) / 8 := by
      simp only [slotOrbitAreaCov, transportedOrbitArea, orbitAreaCov]
      rw [sum_mul_pushforward, ← hp]
      simpa [slotAZ21, hp] using
        area_push_sqrt2 area21Z cz p H hH areaCov21 areaCov21_eq_z
    rw [hA, slotOrbitDeficitPhase2EdgeOrigins_t21_eq_Z H cz hH s t]
    exact radical2_edge_slot_arith (slotAZ21 cz s t)
      (slotKppEdge seedEdgeContribsZ_t21 cz .t21 s t)
  · simp [ht]

theorem m2OrbitSlotCoeffEdgeOrigins_t13_eq_cert (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2OrbitSlotCoeffEdgeOrigins .t13 H symbolDir s t =
      (m2OrbitCertZ13Edge cz s t : ℝ) / 384 := by
  unfold m2OrbitSlotCoeffEdgeOrigins m2OrbitCertZ13Edge
  by_cases ht : isOrbit .t13 s t
  · simp only [ht, ite_true]
    set p := orbitCoveringPerm .t13 s t with hp
    have hA :
        (∑ d : Fin 15, slotOrbitAreaCov .t13 s t d * classCoeff H d) =
          Real.sqrt 3 * (slotAZ13 cz s t : ℝ) / 12 := by
      simp only [slotOrbitAreaCov, transportedOrbitArea, orbitAreaCov]
      rw [sum_mul_pushforward, ← hp]
      simpa [slotAZ13, hp] using
        area_push_sqrt3 area13Z cz p H hH areaCov13 areaCov13_eq_z
    rw [hA, slotOrbitDeficitPhase2EdgeOrigins_t13_eq_Z H cz hH s t]
    exact radical3_edge_slot_arith (slotAZ13 cz s t)
      (slotKppEdge seedEdgeContribsZ_t13 cz .t13 s t)
  · simp [ht]

theorem m2OrbitSlotCoeffEdgeOrigins_t31_eq_cert (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2OrbitSlotCoeffEdgeOrigins .t31 H symbolDir s t =
      (m2OrbitCertZ31Edge cz s t : ℝ) / 384 := by
  unfold m2OrbitSlotCoeffEdgeOrigins m2OrbitCertZ31Edge
  by_cases ht : isOrbit .t31 s t
  · simp only [ht, ite_true]
    set p := orbitCoveringPerm .t31 s t with hp
    have hA :
        (∑ d : Fin 15, slotOrbitAreaCov .t31 s t d * classCoeff H d) =
          Real.sqrt 3 * (slotAZ31 cz s t : ℝ) / 12 := by
      simp only [slotOrbitAreaCov, transportedOrbitArea, orbitAreaCov]
      rw [sum_mul_pushforward, ← hp]
      simpa [slotAZ31, hp] using
        area_push_sqrt3 area31Z cz p H hH areaCov31 areaCov31_eq_z
    rw [hA, slotOrbitDeficitPhase2EdgeOrigins_t31_eq_Z H cz hH s t]
    exact radical3_edge_slot_arith (slotAZ31 cz s t)
      (slotKppEdge seedEdgeContribsZ_t31 cz .t31 s t)
  · simp [ht]

theorem m2OrbitSlotCoeffEdgeOrigins_t22_eq_cert (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2OrbitSlotCoeffEdgeOrigins .t22 H symbolDir s t =
      (m2OrbitCertZ22Edge cz s t : ℝ) / 128 := by
  unfold m2OrbitSlotCoeffEdgeOrigins m2OrbitCertZ22Edge
  by_cases ht : isOrbit .t22 s t
  · simp only [ht, ite_true]
    set p := orbitCoveringPerm .t22 s t with hp
    have hA :
        (∑ d : Fin 15, slotOrbitAreaCov .t22 s t d * classCoeff H d) =
          (slotAZ22 cz s t : ℝ) / 4 := by
      simp only [slotOrbitAreaCov, transportedOrbitArea, orbitAreaCov]
      rw [sum_mul_pushforward, ← hp]
      unfold slotAZ22
      simp_rw [areaCov22_eq_z, hH]
      calc
        (∑ d0 : Fin 15,
            (area22Z d0 : ℝ) / 4 * (cz (permClass p d0) : ℝ)) =
            (∑ d0 : Fin 15, (area22Z d0 : ℝ) * (cz (permClass p d0) : ℝ)) /
              4 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun d0 _ => by ring
        _ = (∑ d0 : Fin 15, area22Z d0 * cz (permClass p d0) : ℤ) / 4 := by
          rw [Int.cast_sum]; push_cast; rfl
    rw [hA, slotOrbitDeficitPhase2EdgeOrigins_t22_eq_Z H cz hH s t]
    exact rational_edge_slot_arith (slotAZ22 cz s t)
      (slotKppEdge seedEdgeContribsZ_t22 cz .t22 s t)
  · simp [ht]

/-! ## §10. Decidable integer sums (axis plus) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ12Edge_axis :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ12Edge axisTTPlusCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ21Edge_axis :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ21Edge axisTTPlusCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ13Edge_axis :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ13Edge axisTTPlusCoeffZ s t) =
      (576 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ31Edge_axis :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ31Edge axisTTPlusCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ22Edge_axis :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ22Edge axisTTPlusCoeffZ s t) =
      (0 : ℤ) := by
  decide

/-! ## §11. Decidable integer sums (axis cross) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ12Edge_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ12Edge axisTTCrossCoeffZ s t) =
      (-256 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ21Edge_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ21Edge axisTTCrossCoeffZ s t) =
      (128 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ13Edge_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ13Edge axisTTCrossCoeffZ s t) =
      (-576 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ31Edge_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ31Edge axisTTCrossCoeffZ s t) =
      (-576 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ22Edge_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ22Edge axisTTCrossCoeffZ s t) =
      (256 : ℤ) := by
  decide

/-! ## §12. Decidable integer sums (decoyGauge / counterexample) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ12Edge_gauge :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ12Edge decoyGaugeCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ21Edge_gauge :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ21Edge decoyGaugeCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ13Edge_gauge :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ13Edge decoyGaugeCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ31Edge_gauge :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ31Edge decoyGaugeCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ22Edge_gauge :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ22Edge decoyGaugeCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ12Edge_counterex :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ12Edge gaugeM1100E2CoeffZ s t) =
      (256 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ21Edge_counterex :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ21Edge gaugeM1100E2CoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ13Edge_counterex :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ13Edge gaugeM1100E2CoeffZ s t) =
      (-1152 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ31Edge_counterex :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ31Edge gaugeM1100E2CoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2OrbitCertZ22Edge_counterex :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ22Edge gaugeM1100E2CoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
theorem sum_m2SlotCertZ_counterex :
    (∑ s : Fin 24, ∑ t : Fin 10, m2SlotCertZ gaugeM1100E2CoeffZ s t) =
      (0 : ℤ) := by
  decide

/-! ## §13. Per-orbit moment evaluations (plus / symbolDir) -/

theorem m2OrbitMomentEdgeOrigins_t12_axis :
    m2OrbitMomentEdgeOrigins .t12 axisTTPlus symbolDir = (0 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t12_eq_cert axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ12Edge axisTTPlusCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ12Edge_axis
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t21_axis :
    m2OrbitMomentEdgeOrigins .t21 axisTTPlus symbolDir = (0 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t21_eq_cert axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ21Edge axisTTPlusCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ21Edge_axis
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t13_axis :
    m2OrbitMomentEdgeOrigins .t13 axisTTPlus symbolDir = (3 / 2 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t13_eq_cert axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ13Edge axisTTPlusCoeffZ s t : ℝ)) = (576 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ13Edge_axis
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t31_axis :
    m2OrbitMomentEdgeOrigins .t31 axisTTPlus symbolDir = (0 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t31_eq_cert axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ31Edge axisTTPlusCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ31Edge_axis
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t22_axis :
    m2OrbitMomentEdgeOrigins .t22 axisTTPlus symbolDir = (0 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t22_eq_cert axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ22Edge axisTTPlusCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ22Edge_axis
  rw [sum_div_const_st, hsum]; norm_num

/-! ## §14. Distinct-hinge assembly (plus) -/

theorem m2AllOrbitMomentDistinctHingeEdgeOrigins_axisTTPlus_symbolDir :
    m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir =
      (-1 / 4 : ℝ) := by
  unfold m2AllOrbitMomentDistinctHingeEdgeOrigins
  simp only [orbitStarSize]
  rw [m2TransportedOrbitMoment_t11_axis, m2OrbitMomentEdgeOrigins_t12_axis,
    m2OrbitMomentEdgeOrigins_t21_axis, m2OrbitMomentEdgeOrigins_t13_axis,
    m2OrbitMomentEdgeOrigins_t31_axis, m2OrbitMomentEdgeOrigins_t22_axis]
  -- `-3/6 + 0 + 0 + (3/2)/6 = -1/4`
  norm_num

/-! ## §15. Cross orbit slices + distinct-hinge -/

theorem m2OrbitMomentEdgeOrigins_t12_cross :
    m2OrbitMomentEdgeOrigins .t12 axisTTCross symbolDir = (-2 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t12_eq_cert axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ12Edge axisTTCrossCoeffZ s t : ℝ)) = (-256 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ12Edge_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t21_cross :
    m2OrbitMomentEdgeOrigins .t21 axisTTCross symbolDir = (1 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t21_eq_cert axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ21Edge axisTTCrossCoeffZ s t : ℝ)) = (128 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ21Edge_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t13_cross :
    m2OrbitMomentEdgeOrigins .t13 axisTTCross symbolDir = (-3 / 2 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t13_eq_cert axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ13Edge axisTTCrossCoeffZ s t : ℝ)) = (-576 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ13Edge_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t31_cross :
    m2OrbitMomentEdgeOrigins .t31 axisTTCross symbolDir = (-3 / 2 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t31_eq_cert axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ31Edge axisTTCrossCoeffZ s t : ℝ)) = (-576 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ31Edge_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t22_cross :
    m2OrbitMomentEdgeOrigins .t22 axisTTCross symbolDir = (2 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t22_eq_cert axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ22Edge axisTTCrossCoeffZ s t : ℝ)) = (256 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ22Edge_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2AllOrbitMomentDistinctHingeEdgeOrigins_axisTTCross_symbolDir :
    m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTCross symbolDir =
      (-1 / 4 : ℝ) := by
  unfold m2AllOrbitMomentDistinctHingeEdgeOrigins
  simp only [orbitStarSize]
  rw [m2TransportedOrbitMoment_t11_cross, m2OrbitMomentEdgeOrigins_t12_cross,
    m2OrbitMomentEdgeOrigins_t21_cross, m2OrbitMomentEdgeOrigins_t13_cross,
    m2OrbitMomentEdgeOrigins_t31_cross, m2OrbitMomentEdgeOrigins_t22_cross]
  norm_num

/-! ## §16. Gauge vanishing -/

theorem m2OrbitMomentEdgeOrigins_t12_gauge :
    m2OrbitMomentEdgeOrigins .t12 decoyGauge symbolDir = (0 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t12_eq_cert decoyGauge decoyGaugeCoeffZ
    classCoeff_decoyGauge_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ12Edge decoyGaugeCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ12Edge_gauge
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t21_gauge :
    m2OrbitMomentEdgeOrigins .t21 decoyGauge symbolDir = (0 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t21_eq_cert decoyGauge decoyGaugeCoeffZ
    classCoeff_decoyGauge_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ21Edge decoyGaugeCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ21Edge_gauge
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t13_gauge :
    m2OrbitMomentEdgeOrigins .t13 decoyGauge symbolDir = (0 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t13_eq_cert decoyGauge decoyGaugeCoeffZ
    classCoeff_decoyGauge_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ13Edge decoyGaugeCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ13Edge_gauge
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t31_gauge :
    m2OrbitMomentEdgeOrigins .t31 decoyGauge symbolDir = (0 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t31_eq_cert decoyGauge decoyGaugeCoeffZ
    classCoeff_decoyGauge_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ31Edge decoyGaugeCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ31Edge_gauge
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t22_gauge :
    m2OrbitMomentEdgeOrigins .t22 decoyGauge symbolDir = (0 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t22_eq_cert decoyGauge decoyGaugeCoeffZ
    classCoeff_decoyGauge_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ22Edge decoyGaugeCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ22Edge_gauge
  rw [sum_div_const_st, hsum]; norm_num

theorem m2AllOrbitMomentDistinctHingeEdgeOrigins_decoyGauge_symbolDir :
    m2AllOrbitMomentDistinctHingeEdgeOrigins decoyGauge symbolDir = (0 : ℝ) := by
  unfold m2AllOrbitMomentDistinctHingeEdgeOrigins
  simp only [orbitStarSize]
  rw [m2TransportedOrbitMoment_t11_gauge, m2OrbitMomentEdgeOrigins_t12_gauge,
    m2OrbitMomentEdgeOrigins_t21_gauge, m2OrbitMomentEdgeOrigins_t13_gauge,
    m2OrbitMomentEdgeOrigins_t31_gauge, m2OrbitMomentEdgeOrigins_t22_gauge]
  ring

/-! ## §17. Counterexample m=(1,1,0,0), v=e₂ -/

theorem m2Symbol_gaugeM1100E2 : m2Symbol gaugeM1100E2 = (0 : ℝ) := by
  unfold m2Symbol
  simp_rw [m2SlotCoeff_eq_cert gaugeM1100E2 gaugeM1100E2CoeffZ
    classCoeff_gaugeM1100E2_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2SlotCertZ gaugeM1100E2CoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2SlotCertZ_counterex
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t11_counterex :
    m2TransportedOrbitMoment .t11 gaugeM1100E2 symbolDir = (0 : ℝ) := by
  rw [m2TransportedOrbitMoment_t11, m2Symbol_gaugeM1100E2]

theorem m2OrbitMomentEdgeOrigins_t12_counterex :
    m2OrbitMomentEdgeOrigins .t12 gaugeM1100E2 symbolDir = (2 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t12_eq_cert gaugeM1100E2 gaugeM1100E2CoeffZ
    classCoeff_gaugeM1100E2_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ12Edge gaugeM1100E2CoeffZ s t : ℝ)) = (256 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ12Edge_counterex
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t21_counterex :
    m2OrbitMomentEdgeOrigins .t21 gaugeM1100E2 symbolDir = (0 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t21_eq_cert gaugeM1100E2 gaugeM1100E2CoeffZ
    classCoeff_gaugeM1100E2_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ21Edge gaugeM1100E2CoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ21Edge_counterex
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t13_counterex :
    m2OrbitMomentEdgeOrigins .t13 gaugeM1100E2 symbolDir = (-3 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t13_eq_cert gaugeM1100E2 gaugeM1100E2CoeffZ
    classCoeff_gaugeM1100E2_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ13Edge gaugeM1100E2CoeffZ s t : ℝ)) = (-1152 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ13Edge_counterex
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t31_counterex :
    m2OrbitMomentEdgeOrigins .t31 gaugeM1100E2 symbolDir = (0 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t31_eq_cert gaugeM1100E2 gaugeM1100E2CoeffZ
    classCoeff_gaugeM1100E2_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ31Edge gaugeM1100E2CoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ31Edge_counterex
  rw [sum_div_const_st, hsum]; norm_num

theorem m2OrbitMomentEdgeOrigins_t22_counterex :
    m2OrbitMomentEdgeOrigins .t22 gaugeM1100E2 symbolDir = (0 : ℝ) := by
  unfold m2OrbitMomentEdgeOrigins
  simp_rw [m2OrbitSlotCoeffEdgeOrigins_t22_eq_cert gaugeM1100E2 gaugeM1100E2CoeffZ
    classCoeff_gaugeM1100E2_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ22Edge gaugeM1100E2CoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ22Edge_counterex
  rw [sum_div_const_st, hsum]; norm_num

theorem m2AllOrbitMomentDistinctHingeEdgeOrigins_gaugeM1100E2_symbolDir :
    m2AllOrbitMomentDistinctHingeEdgeOrigins gaugeM1100E2 symbolDir = (0 : ℝ) := by
  unfold m2AllOrbitMomentDistinctHingeEdgeOrigins
  simp only [orbitStarSize]
  rw [m2TransportedOrbitMoment_t11_counterex, m2OrbitMomentEdgeOrigins_t12_counterex,
    m2OrbitMomentEdgeOrigins_t21_counterex, m2OrbitMomentEdgeOrigins_t13_counterex,
    m2OrbitMomentEdgeOrigins_t31_counterex, m2OrbitMomentEdgeOrigins_t22_counterex]
  norm_num

/-! ## §18. Status -/

structure EdgeOriginsM2EvalStatus where
  plusSymbolDir : Bool
  crossSymbolDir : Bool
  decoyGaugeSymbolDir : Bool
  counterexM1100E2 : Bool
  gapActionRecovery : Bool
  base0Forbidden : Bool

def edgeOriginsM2EvalStatus : EdgeOriginsM2EvalStatus where
  plusSymbolDir := true
  crossSymbolDir := true
  decoyGaugeSymbolDir := true
  counterexM1100E2 := true
  gapActionRecovery := false
  base0Forbidden := true

theorem edgeOriginsM2EvalStatus_flags :
    edgeOriginsM2EvalStatus.plusSymbolDir = true ∧
      edgeOriginsM2EvalStatus.crossSymbolDir = true ∧
        edgeOriginsM2EvalStatus.decoyGaugeSymbolDir = true ∧
          edgeOriginsM2EvalStatus.counterexM1100E2 = true ∧
            edgeOriginsM2EvalStatus.gapActionRecovery = false ∧
              edgeOriginsM2EvalStatus.base0Forbidden = true := by
  decide

/-- Closed targets (inhabited by the theorems above). -/
def M2EdgeOriginsPlusSymbolDirEval : Prop :=
  m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir = (-1 / 4 : ℝ)

def M2EdgeOriginsCrossSymbolDirEval : Prop :=
  m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTCross symbolDir = (-1 / 4 : ℝ)

def M2EdgeOriginsDecoyGaugeEval : Prop :=
  m2AllOrbitMomentDistinctHingeEdgeOrigins decoyGauge symbolDir = (0 : ℝ)

def M2EdgeOriginsCounterexM1100E2Eval : Prop :=
  m2AllOrbitMomentDistinctHingeEdgeOrigins gaugeM1100E2 symbolDir = (0 : ℝ)

theorem M2EdgeOriginsPlusSymbolDirEval_holds : M2EdgeOriginsPlusSymbolDirEval :=
  m2AllOrbitMomentDistinctHingeEdgeOrigins_axisTTPlus_symbolDir

theorem M2EdgeOriginsCrossSymbolDirEval_holds : M2EdgeOriginsCrossSymbolDirEval :=
  m2AllOrbitMomentDistinctHingeEdgeOrigins_axisTTCross_symbolDir

theorem M2EdgeOriginsDecoyGaugeEval_holds : M2EdgeOriginsDecoyGaugeEval :=
  m2AllOrbitMomentDistinctHingeEdgeOrigins_decoyGauge_symbolDir

theorem M2EdgeOriginsCounterexM1100E2Eval_holds :
    M2EdgeOriginsCounterexM1100E2Eval :=
  m2AllOrbitMomentDistinctHingeEdgeOrigins_gaugeM1100E2_symbolDir

end

end ReggeBlochStarEdgeOriginsM2Eval4D
end Analysis
end Gravity
end IndisputableMonolith
