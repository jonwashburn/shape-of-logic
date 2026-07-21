import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbit4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochM2Symbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeFlat4DHessianAssembly

/-!
# Transported all-orbit m² evaluation certificates

Closes the raw all-orbit moment on `axisTTPlus` / `symbolDir`:

  `m2TransportedAllOrbitMoment axisTTPlus symbolDir = -5/2`

by integer (or radical-cancelled integer) per-orbit certificates, then sum.
Also proves gauge vanishing on `decoyGauge`, and the distinct-hinge
weighted moment (`1/r_τ`):

  `m2TransportedAllOrbitMomentDistinctHinge axisTTPlus symbolDir = -1/4`

(`-3/6 + 2/4 + (-3/2)/6`), with decoy gauge still `0`.

Orbit slices on plus (THEOREM):
t11 = -3, t12 = +2, t13 = -3/2, t21 = t31 = t22 = 0.

Also closes `axisTTCross` / `symbolDir` distinct-hinge isotropy:

  `m2TransportedAllOrbitMomentDistinctHinge axisTTCross symbolDir = -1/4`

(raw all-orbit on cross is `0`; orbit slices differ from plus, but the
`1/r_τ` fold matches).  Normalized plus/cross both give raw `-1/8`.

Axis-aligned ray `e0Dir=(1,0,0,0)` is now Lean-certified: plus
distinct-hinge `0`, cross `-1/8` (normalized `-1/16`).  Plus/cross agree
on `symbolDir` and disagree on bare `e0` (OPEN
`Regge4DContinuumIsotropyBlockedOnAxisMode`).

Full cosine two-jet `A0*K2 + A2*K0` (§12): slotwise `K0 = 0` on
`axisTTPlus` / `axisTTCross` (integer certificates), so full = trunc on
every direction; e0 anisotropy and plus vanishing are **not** repaired
(`Regge4DFullTwoJetRestoresE0PlusVanishing` / `...E0Isotropy` status false).
External probe receipt:
`state/qg_full_theory/probe_fulljet_distinct_hinge_20260721.json`.

Does **not** flip `gap_action_recovery`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeBlochTransportedAllOrbitM2Eval4D

open BigOperators
open ReggeEdgeStencil4D
open ReggeHinge4DOrbitClassification
open ReggeBlochFold4D
open ReggeBlochM2Symbol4D
open ReggeBlochOrbitTransport4D
open ReggeBlochTransportedAllOrbit4D
open ReggeBlochAllOrbitSymbol4D (isOrbit isOrbit_t11_iff_isT11 phaseScaleDir)
open ReggeFlat4DHessianAssembly
open EdgeTTDecomposition4D (axisTTPlus axisTTCross)

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
-- decoyGauge lives in ReggeEdgeStencil4D (already opened above)

noncomputable section

/-! ## §1. Pushforward reindex helpers -/

theorem sum_mul_pushforward (v w : Fin 15 → ℝ) (p : Fin 24) :
    (∑ d : Fin 15, pushforwardClass v p d * w d) =
      ∑ d0 : Fin 15, v d0 * w (permClass p d0) := by
  unfold pushforwardClass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d0 _ => ?_
  have h : ∀ d : Fin 15,
      (if permClass p d0 = d then v d0 else 0) * w d =
        if permClass p d0 = d then v d0 * w d else 0 := by
    intro d; split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_ite_eq]
  simp

theorem sum_mul_pushforward_weighted (v w f : Fin 15 → ℝ) (p : Fin 24) :
    (∑ d : Fin 15, pushforwardClass v p d * w d * f d) =
      ∑ d0 : Fin 15, v d0 * w (permClass p d0) * f (permClass p d0) := by
  unfold pushforwardClass
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d0 _ => ?_
  have h : ∀ d : Fin 15,
      (if permClass p d0 = d then v d0 else 0) * (w d * f d) =
        if permClass p d0 = d then v d0 * (w d * f d) else 0 := by
    intro d; split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_ite_eq]
  simp [mul_assoc]

private lemma sum_div_const_st (c : ℝ) (f : Fin 24 → Fin 10 → ℝ) :
    (∑ s : Fin 24, ∑ t : Fin 10, f s t / c) =
      (∑ s : Fin 24, ∑ t : Fin 10, f s t) / c := by
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul]

private lemma sum_six_orbits (f : HingeOrbitType → ℝ) :
    (∑ ty : HingeOrbitType, f ty) =
      f .t11 + f .t12 + f .t21 + f .t13 + f .t31 + f .t22 := by
  have h : (Finset.univ : Finset HingeOrbitType) =
      insert HingeOrbitType.t11
        (insert HingeOrbitType.t12
          (insert HingeOrbitType.t21
            (insert HingeOrbitType.t13
              (insert HingeOrbitType.t31
                (insert HingeOrbitType.t22 (∅ : Finset HingeOrbitType)))))) := by
    decide
  simp [h, Finset.sum_insert]
  ring

/-! ## §2. Integer area seeds (radical factored out) -/

def area12Z (d : Fin 15) : ℤ :=
  match d with | ⟨0, _⟩ => 2 | ⟨5, _⟩ => 1 | _ => 0

def area21Z (d : Fin 15) : ℤ :=
  match d with | ⟨2, _⟩ => 1 | ⟨3, _⟩ => 2 | _ => 0

def area13Z (d : Fin 15) : ℤ :=
  match d with | ⟨0, _⟩ => 3 | ⟨13, _⟩ => 1 | _ => 0

def area31Z (d : Fin 15) : ℤ :=
  match d with | ⟨6, _⟩ => 1 | ⟨7, _⟩ => 3 | _ => 0

def area22Z (d : Fin 15) : ℤ :=
  match d with | ⟨2, _⟩ => 1 | ⟨11, _⟩ => 1 | _ => 0

theorem areaCov12_eq_z (d : Fin 15) :
    areaCov12 d = Real.sqrt 2 * (area12Z d : ℝ) / 8 := by
  fin_cases d <;> simp [areaCov12, area12Z] <;> ring

theorem areaCov21_eq_z (d : Fin 15) :
    areaCov21 d = Real.sqrt 2 * (area21Z d : ℝ) / 8 := by
  fin_cases d <;> simp [areaCov21, area21Z] <;> ring

theorem areaCov13_eq_z (d : Fin 15) :
    areaCov13 d = Real.sqrt 3 * (area13Z d : ℝ) / 12 := by
  fin_cases d <;> simp [areaCov13, area13Z] <;> ring

theorem areaCov31_eq_z (d : Fin 15) :
    areaCov31 d = Real.sqrt 3 * (area31Z d : ℝ) / 12 := by
  fin_cases d <;> simp [areaCov31, area31Z] <;> ring

theorem areaCov22_eq_z (d : Fin 15) :
    areaCov22 d = (area22Z d : ℝ) / 4 := by
  fin_cases d <;> simp [areaCov22, area22Z] <;> norm_num

/-! ## §3. Per-orbit slot certificates -/

def slotAZ12 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d0 : Fin 15, area12Z d0 * cz (permClass (orbitCoveringPerm .t12 s t) d0)

def slotAZ21 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d0 : Fin 15, area21Z d0 * cz (permClass (orbitCoveringPerm .t21 s t) d0)

def slotAZ13 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d0 : Fin 15, area13Z d0 * cz (permClass (orbitCoveringPerm .t13 s t) d0)

def slotAZ31 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d0 : Fin 15, area31Z d0 * cz (permClass (orbitCoveringPerm .t31 s t) d0)

def slotAZ22 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d0 : Fin 15, area22Z d0 * cz (permClass (orbitCoveringPerm .t22 s t) d0)

def slotKppOrbit (sign : Fin 15 → ℤ) (cz : Fin 15 → ℤ)
    (ty : HingeOrbitType) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d0 : Fin 15,
    sign d0 * cz (permClass (orbitCoveringPerm ty s t) d0) *
      ((phase2Nat s t (permClass (orbitCoveringPerm ty s t) d0) : ℕ) : ℤ) ^ 2

def m2OrbitCertZ12 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t12 s t then -slotAZ12 cz s t * slotKppOrbit kernel12Sign cz .t12 s t
  else 0

def m2OrbitCertZ21 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t21 s t then -slotAZ21 cz s t * slotKppOrbit kernel12Sign cz .t21 s t
  else 0

def m2OrbitCertZ13 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t13 s t then -slotAZ13 cz s t * slotKppOrbit kernel13Sign cz .t13 s t
  else 0

def m2OrbitCertZ31 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t31 s t then -slotAZ31 cz s t * slotKppOrbit kernel13Sign cz .t31 s t
  else 0

def m2OrbitCertZ22 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t22 s t then -slotAZ22 cz s t * slotKppOrbit kernel22Sign cz .t22 s t
  else 0

/-! ## §4. Slot coefficient = certificate / denom -/

private lemma sqrt2_mul_self : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
  simpa [pow_two] using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

private lemma sqrt3_mul_self : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := by
  simpa [pow_two] using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)

private lemma radical2_slot_arith (AZ Kpp : ℤ) :
    Real.sqrt 2 * (AZ : ℝ) / 8 *
        (-(1 / 2 : ℝ) * (Real.sqrt 2 * (Kpp : ℝ) / 8)) =
      ((-AZ * Kpp : ℤ) : ℝ) / 64 := by
  have hs := sqrt2_mul_self
  ring_nf
  rw [show (Real.sqrt 2) ^ 2 = (2 : ℝ) by simpa [pow_two] using hs]
  push_cast; ring

private lemma radical3_slot_arith (AZ Kpp : ℤ) :
    Real.sqrt 3 * (AZ : ℝ) / 12 *
        (-(1 / 2 : ℝ) * (Real.sqrt 3 * (Kpp : ℝ) / 4)) =
      ((-AZ * Kpp : ℤ) : ℝ) / 32 := by
  have hs := sqrt3_mul_self
  ring_nf
  rw [show (Real.sqrt 3) ^ 2 = (3 : ℝ) by simpa [pow_two] using hs]
  push_cast; ring

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

private lemma ker_push_sqrt2_half (cz : Fin 15 → ℤ) (p : Fin 24)
    (H : Mat4) (hH : ∀ d, classCoeff H d = (cz d : ℝ))
    (s : Fin 24) (t : Fin 10) :
    (∑ d0 : Fin 15,
        ReggeHinge4DStarKernel12.fullStarClassKernel d0 *
          classCoeff H (permClass p d0) *
            (phaseScaleDir symbolDir (hingeBase s t) (permClass p d0)) ^ 2) =
      Real.sqrt 2 *
        (∑ d0 : Fin 15,
            kernel12Sign d0 * cz (permClass p d0) *
              ((phase2Nat s t (permClass p d0) : ℕ) : ℤ) ^ 2 : ℤ) / 8 := by
  simp_rw [kernel12_eq_sign, hH, phaseScaleDir_symbolDir, phaseScale_eq_phase2Nat]
  calc
    (∑ d0 : Fin 15,
        ((kernel12Sign d0 : ℝ) * (Real.sqrt 2 / 2)) *
          (cz (permClass p d0) : ℝ) *
            (((phase2Nat s t (permClass p d0) : ℕ) : ℝ) / 2) ^ 2) =
        Real.sqrt 2 / 8 *
          ∑ d0 : Fin 15,
            (kernel12Sign d0 : ℝ) * (cz (permClass p d0) : ℝ) *
              ((phase2Nat s t (permClass p d0) : ℕ) : ℝ) ^ 2 := by
      refine Eq.trans ?_ (Finset.mul_sum _ _ _).symm
      refine Finset.sum_congr rfl fun d0 _ => by ring
    _ = Real.sqrt 2 *
          (∑ d0 : Fin 15,
              kernel12Sign d0 * cz (permClass p d0) *
                ((phase2Nat s t (permClass p d0) : ℕ) : ℤ) ^ 2 : ℤ) / 8 := by
      rw [Int.cast_sum]
      push_cast; ring

private lemma ker_push_sqrt3 (cz : Fin 15 → ℤ) (p : Fin 24)
    (H : Mat4) (hH : ∀ d, classCoeff H d = (cz d : ℝ))
    (s : Fin 24) (t : Fin 10) :
    (∑ d0 : Fin 15,
        ReggeHinge4DStarKernel13.fullStarClassKernel d0 *
          classCoeff H (permClass p d0) *
            (phaseScaleDir symbolDir (hingeBase s t) (permClass p d0)) ^ 2) =
      Real.sqrt 3 *
        (∑ d0 : Fin 15,
            kernel13Sign d0 * cz (permClass p d0) *
              ((phase2Nat s t (permClass p d0) : ℕ) : ℤ) ^ 2 : ℤ) / 4 := by
  simp_rw [kernel13_eq_sign, hH, phaseScaleDir_symbolDir, phaseScale_eq_phase2Nat]
  calc
    (∑ d0 : Fin 15,
        ((kernel13Sign d0 : ℝ) * Real.sqrt 3) *
          (cz (permClass p d0) : ℝ) *
            (((phase2Nat s t (permClass p d0) : ℕ) : ℝ) / 2) ^ 2) =
        Real.sqrt 3 / 4 *
          ∑ d0 : Fin 15,
            (kernel13Sign d0 : ℝ) * (cz (permClass p d0) : ℝ) *
              ((phase2Nat s t (permClass p d0) : ℕ) : ℝ) ^ 2 := by
      refine Eq.trans ?_ (Finset.mul_sum _ _ _).symm
      refine Finset.sum_congr rfl fun d0 _ => by ring
    _ = Real.sqrt 3 *
          (∑ d0 : Fin 15,
              kernel13Sign d0 * cz (permClass p d0) *
                ((phase2Nat s t (permClass p d0) : ℕ) : ℤ) ^ 2 : ℤ) / 4 := by
      rw [Int.cast_sum]
      push_cast; ring

theorem m2TransportedOrbitSlotCoeff_t12_eq_cert (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeff .t12 H symbolDir s t =
      (m2OrbitCertZ12 cz s t : ℝ) / 64 := by
  unfold m2TransportedOrbitSlotCoeff m2TransportedOrbitSlotCoeffTrunc
    m2OrbitCertZ12
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
    have hK :
        (∑ d : Fin 15,
            slotOrbitDeficitKer .t12 s t d * classCoeff H d *
              (phaseScaleDir symbolDir (hingeBase s t) d) ^ 2) =
          Real.sqrt 2 * (slotKppOrbit kernel12Sign cz .t12 s t : ℝ) / 8 := by
      simp only [slotOrbitDeficitKer, transportedOrbitDeficit, orbitSeedKernel]
      rw [sum_mul_pushforward_weighted, ← hp]
      simpa [slotKppOrbit, hp] using ker_push_sqrt2_half cz p H hH s t
    rw [hA, hK]
    exact radical2_slot_arith (slotAZ12 cz s t)
      (slotKppOrbit kernel12Sign cz .t12 s t)
  · simp [ht]

theorem m2TransportedOrbitSlotCoeff_t21_eq_cert (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeff .t21 H symbolDir s t =
      (m2OrbitCertZ21 cz s t : ℝ) / 64 := by
  unfold m2TransportedOrbitSlotCoeff m2TransportedOrbitSlotCoeffTrunc
    m2OrbitCertZ21
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
    have hK :
        (∑ d : Fin 15,
            slotOrbitDeficitKer .t21 s t d * classCoeff H d *
              (phaseScaleDir symbolDir (hingeBase s t) d) ^ 2) =
          Real.sqrt 2 * (slotKppOrbit kernel12Sign cz .t21 s t : ℝ) / 8 := by
      simp only [slotOrbitDeficitKer, transportedOrbitDeficit, orbitSeedKernel,
        kernel21]
      rw [sum_mul_pushforward_weighted, ← hp]
      simpa [slotKppOrbit, hp] using ker_push_sqrt2_half cz p H hH s t
    rw [hA, hK]
    exact radical2_slot_arith (slotAZ21 cz s t)
      (slotKppOrbit kernel12Sign cz .t21 s t)
  · simp [ht]

theorem m2TransportedOrbitSlotCoeff_t13_eq_cert (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeff .t13 H symbolDir s t =
      (m2OrbitCertZ13 cz s t : ℝ) / 32 := by
  unfold m2TransportedOrbitSlotCoeff m2TransportedOrbitSlotCoeffTrunc
    m2OrbitCertZ13
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
    have hK :
        (∑ d : Fin 15,
            slotOrbitDeficitKer .t13 s t d * classCoeff H d *
              (phaseScaleDir symbolDir (hingeBase s t) d) ^ 2) =
          Real.sqrt 3 * (slotKppOrbit kernel13Sign cz .t13 s t : ℝ) / 4 := by
      simp only [slotOrbitDeficitKer, transportedOrbitDeficit, orbitSeedKernel]
      rw [sum_mul_pushforward_weighted, ← hp]
      simpa [slotKppOrbit, hp] using ker_push_sqrt3 cz p H hH s t
    rw [hA, hK]
    exact radical3_slot_arith (slotAZ13 cz s t)
      (slotKppOrbit kernel13Sign cz .t13 s t)
  · simp [ht]

theorem m2TransportedOrbitSlotCoeff_t31_eq_cert (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeff .t31 H symbolDir s t =
      (m2OrbitCertZ31 cz s t : ℝ) / 32 := by
  unfold m2TransportedOrbitSlotCoeff m2TransportedOrbitSlotCoeffTrunc
    m2OrbitCertZ31
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
    have hK :
        (∑ d : Fin 15,
            slotOrbitDeficitKer .t31 s t d * classCoeff H d *
              (phaseScaleDir symbolDir (hingeBase s t) d) ^ 2) =
          Real.sqrt 3 * (slotKppOrbit kernel13Sign cz .t31 s t : ℝ) / 4 := by
      simp only [slotOrbitDeficitKer, transportedOrbitDeficit, orbitSeedKernel,
        kernel31]
      rw [sum_mul_pushforward_weighted, ← hp]
      simpa [slotKppOrbit, hp] using ker_push_sqrt3 cz p H hH s t
    rw [hA, hK]
    exact radical3_slot_arith (slotAZ31 cz s t)
      (slotKppOrbit kernel13Sign cz .t31 s t)
  · simp [ht]

theorem m2TransportedOrbitSlotCoeff_t22_eq_cert (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeff .t22 H symbolDir s t =
      (m2OrbitCertZ22 cz s t : ℝ) / 32 := by
  unfold m2TransportedOrbitSlotCoeff m2TransportedOrbitSlotCoeffTrunc
    m2OrbitCertZ22
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
    have hK :
        (∑ d : Fin 15,
            slotOrbitDeficitKer .t22 s t d * classCoeff H d *
              (phaseScaleDir symbolDir (hingeBase s t) d) ^ 2) =
          (slotKppOrbit kernel22Sign cz .t22 s t : ℝ) / 4 := by
      simp only [slotOrbitDeficitKer, transportedOrbitDeficit, orbitSeedKernel]
      rw [sum_mul_pushforward_weighted, ← hp]
      unfold slotKppOrbit
      simp_rw [kernel22_eq_sign, hH, phaseScaleDir_symbolDir,
        phaseScale_eq_phase2Nat]
      calc
        (∑ d0 : Fin 15,
            (kernel22Sign d0 : ℝ) * (cz (permClass p d0) : ℝ) *
              (((phase2Nat s t (permClass p d0) : ℕ) : ℝ) / 2) ^ 2) =
            (∑ d0 : Fin 15,
                (kernel22Sign d0 : ℝ) * (cz (permClass p d0) : ℝ) *
                  ((phase2Nat s t (permClass p d0) : ℕ) : ℝ) ^ 2) / 4 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun d0 _ => by ring
        _ = (∑ d0 : Fin 15,
                kernel22Sign d0 * cz (permClass p d0) *
                  ((phase2Nat s t (permClass p d0) : ℕ) : ℤ) ^ 2 : ℤ) / 4 := by
          rw [Int.cast_sum]; push_cast; rfl
    rw [hA, hK]
    push_cast; ring
  · simp [ht]

/-! ## §5. Decidable integer sums -/

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ12_axis :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ12 axisTTPlusCoeffZ s t) =
      (128 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ21_axis :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ21 axisTTPlusCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ13_axis :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ13 axisTTPlusCoeffZ s t) =
      (-48 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ31_axis :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ31 axisTTPlusCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ22_axis :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ22 axisTTPlusCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ12_gauge :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ12 decoyGaugeCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ21_gauge :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ21 decoyGaugeCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ13_gauge :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ13 decoyGaugeCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ31_gauge :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ31 decoyGaugeCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ22_gauge :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ22 decoyGaugeCoeffZ s t) =
      (0 : ℤ) := by
  decide

/-! ## §6. Per-orbit moment evaluations -/

theorem m2TransportedOrbitMoment_t12_axis :
    m2TransportedOrbitMoment .t12 axisTTPlus symbolDir = (2 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t12_eq_cert axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ12 axisTTPlusCoeffZ s t : ℝ)) = (128 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ12_axis
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t21_axis :
    m2TransportedOrbitMoment .t21 axisTTPlus symbolDir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t21_eq_cert axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ21 axisTTPlusCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ21_axis
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t13_axis :
    m2TransportedOrbitMoment .t13 axisTTPlus symbolDir = (-3 / 2 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t13_eq_cert axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ13 axisTTPlusCoeffZ s t : ℝ)) = (-48 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ13_axis
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t31_axis :
    m2TransportedOrbitMoment .t31 axisTTPlus symbolDir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t31_eq_cert axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ31 axisTTPlusCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ31_axis
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t22_axis :
    m2TransportedOrbitMoment .t22 axisTTPlus symbolDir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t22_eq_cert axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ22 axisTTPlusCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ22_axis
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t11_axis :
    m2TransportedOrbitMoment .t11 axisTTPlus symbolDir = (-3 : ℝ) := by
  rw [m2TransportedOrbitMoment_t11, m2Symbol_axisTTPlus]

/-! ## §7. All-orbit axis evaluation -/

theorem m2TransportedAllOrbitMoment_axisTTPlus_symbolDir :
    m2TransportedAllOrbitMoment axisTTPlus symbolDir = (-5 / 2 : ℝ) := by
  unfold m2TransportedAllOrbitMoment
  rw [sum_six_orbits]
  rw [m2TransportedOrbitMoment_t11_axis, m2TransportedOrbitMoment_t12_axis,
    m2TransportedOrbitMoment_t21_axis, m2TransportedOrbitMoment_t13_axis,
    m2TransportedOrbitMoment_t31_axis, m2TransportedOrbitMoment_t22_axis]
  norm_num

theorem M2TransportedAllOrbitAxisSymbolDirEvalOpen_holds :
    M2TransportedAllOrbitAxisSymbolDirEvalOpen :=
  m2TransportedAllOrbitMoment_axisTTPlus_symbolDir

/-! ## §8. Gauge vanishing -/

theorem m2TransportedOrbitMoment_t12_gauge :
    m2TransportedOrbitMoment .t12 decoyGauge symbolDir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t12_eq_cert decoyGauge decoyGaugeCoeffZ
    classCoeff_decoyGauge_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ12 decoyGaugeCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ12_gauge
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t21_gauge :
    m2TransportedOrbitMoment .t21 decoyGauge symbolDir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t21_eq_cert decoyGauge decoyGaugeCoeffZ
    classCoeff_decoyGauge_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ21 decoyGaugeCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ21_gauge
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t13_gauge :
    m2TransportedOrbitMoment .t13 decoyGauge symbolDir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t13_eq_cert decoyGauge decoyGaugeCoeffZ
    classCoeff_decoyGauge_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ13 decoyGaugeCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ13_gauge
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t31_gauge :
    m2TransportedOrbitMoment .t31 decoyGauge symbolDir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t31_eq_cert decoyGauge decoyGaugeCoeffZ
    classCoeff_decoyGauge_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ31 decoyGaugeCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ31_gauge
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t22_gauge :
    m2TransportedOrbitMoment .t22 decoyGauge symbolDir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t22_eq_cert decoyGauge decoyGaugeCoeffZ
    classCoeff_decoyGauge_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ22 decoyGaugeCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ22_gauge
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t11_gauge :
    m2TransportedOrbitMoment .t11 decoyGauge symbolDir = (0 : ℝ) := by
  rw [m2TransportedOrbitMoment_t11, m2Symbol_decoyGauge]

theorem m2TransportedAllOrbitMoment_decoyGauge_symbolDir :
    m2TransportedAllOrbitMoment decoyGauge symbolDir = (0 : ℝ) := by
  unfold m2TransportedAllOrbitMoment
  rw [sum_six_orbits]
  rw [m2TransportedOrbitMoment_t11_gauge, m2TransportedOrbitMoment_t12_gauge,
    m2TransportedOrbitMoment_t21_gauge, m2TransportedOrbitMoment_t13_gauge,
    m2TransportedOrbitMoment_t31_gauge, m2TransportedOrbitMoment_t22_gauge]
  ring

/-! ## §9. Distinct-hinge weight `1/r_τ` -/

theorem m2TransportedAllOrbitMomentDistinctHinge_axisTTPlus_symbolDir :
    m2TransportedAllOrbitMomentDistinctHinge axisTTPlus symbolDir =
      (-1 / 4 : ℝ) := by
  unfold m2TransportedAllOrbitMomentDistinctHinge
  rw [sum_six_orbits]
  simp only [orbitStarSize]
  rw [m2TransportedOrbitMoment_t11_axis, m2TransportedOrbitMoment_t12_axis,
    m2TransportedOrbitMoment_t21_axis, m2TransportedOrbitMoment_t13_axis,
    m2TransportedOrbitMoment_t31_axis, m2TransportedOrbitMoment_t22_axis]
  -- `-3/6 + 2/4 + (-3/2)/6 + 0 + 0 + 0 = -1/4`
  norm_num

theorem M2DistinctHingeAxisSymbolDirEvalOpen_holds :
    M2DistinctHingeAxisSymbolDirEvalOpen :=
  m2TransportedAllOrbitMomentDistinctHinge_axisTTPlus_symbolDir

theorem m2TransportedAllOrbitMomentDistinctHinge_decoyGauge_symbolDir :
    m2TransportedAllOrbitMomentDistinctHinge decoyGauge symbolDir =
      (0 : ℝ) := by
  unfold m2TransportedAllOrbitMomentDistinctHinge
  rw [sum_six_orbits]
  simp only [orbitStarSize]
  rw [m2TransportedOrbitMoment_t11_gauge, m2TransportedOrbitMoment_t12_gauge,
    m2TransportedOrbitMoment_t21_gauge, m2TransportedOrbitMoment_t13_gauge,
    m2TransportedOrbitMoment_t31_gauge, m2TransportedOrbitMoment_t22_gauge]
  ring

/-- Frobenius-normalized axis plus: factor `(1/√2)² = 1/2` on the
distinct-hinge raw `-1/4` yields raw moment `-1/8`.  After `/|symbolDir|²`
the continuum face is `-1/16`; EH Tendsto to `-1/4` remains OPEN
(residual factor 4; no fitted rescale). -/
theorem m2TransportedAllOrbitMomentDistinctHinge_axisTTPlusNormalized_symbolDir :
    m2TransportedAllOrbitMomentDistinctHinge
        ((Real.sqrt 2)⁻¹ • axisTTPlus) symbolDir =
      (-1 / 8 : ℝ) := by
  rw [m2TransportedAllOrbitMomentDistinctHinge_smul,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTPlus_symbolDir,
    inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-! ## §10. Axis TT cross certificates on `symbolDir` -/

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2SlotCertZ_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2SlotCertZ axisTTCrossCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ12_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ12 axisTTCrossCoeffZ s t) =
      (-256 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ21_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ21 axisTTCrossCoeffZ s t) =
      (-64 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ13_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ13 axisTTCrossCoeffZ s t) =
      (48 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ31_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ31 axisTTCrossCoeffZ s t) =
      (48 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ22_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ22 axisTTCrossCoeffZ s t) =
      (64 : ℤ) := by
  decide

theorem m2Symbol_axisTTCross : m2Symbol axisTTCross = (0 : ℝ) := by
  unfold m2Symbol
  simp_rw [m2SlotCoeff_eq_cert axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2SlotCertZ axisTTCrossCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2SlotCertZ_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t11_cross :
    m2TransportedOrbitMoment .t11 axisTTCross symbolDir = (0 : ℝ) := by
  rw [m2TransportedOrbitMoment_t11, m2Symbol_axisTTCross]

theorem m2TransportedOrbitMoment_t12_cross :
    m2TransportedOrbitMoment .t12 axisTTCross symbolDir = (-4 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t12_eq_cert axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ12 axisTTCrossCoeffZ s t : ℝ)) = (-256 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ12_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t21_cross :
    m2TransportedOrbitMoment .t21 axisTTCross symbolDir = (-1 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t21_eq_cert axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ21 axisTTCrossCoeffZ s t : ℝ)) = (-64 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ21_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t13_cross :
    m2TransportedOrbitMoment .t13 axisTTCross symbolDir = (3 / 2 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t13_eq_cert axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ13 axisTTCrossCoeffZ s t : ℝ)) = (48 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ13_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t31_cross :
    m2TransportedOrbitMoment .t31 axisTTCross symbolDir = (3 / 2 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t31_eq_cert axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ31 axisTTCrossCoeffZ s t : ℝ)) = (48 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ31_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t22_cross :
    m2TransportedOrbitMoment .t22 axisTTCross symbolDir = (2 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t22_eq_cert axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ22 axisTTCrossCoeffZ s t : ℝ)) = (64 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ22_cross
  rw [sum_div_const_st, hsum]; norm_num

/-- Raw all-orbit (unweighted) on cross / symbolDir is `0`
(`0-4-1+3/2+3/2+2`), unlike plus `-5/2`. -/
theorem m2TransportedAllOrbitMoment_axisTTCross_symbolDir :
    m2TransportedAllOrbitMoment axisTTCross symbolDir = (0 : ℝ) := by
  unfold m2TransportedAllOrbitMoment
  rw [sum_six_orbits]
  rw [m2TransportedOrbitMoment_t11_cross, m2TransportedOrbitMoment_t12_cross,
    m2TransportedOrbitMoment_t21_cross, m2TransportedOrbitMoment_t13_cross,
    m2TransportedOrbitMoment_t31_cross, m2TransportedOrbitMoment_t22_cross]
  norm_num

/-- Distinct-hinge `1/r_τ` on cross / symbolDir equals frozen EH `-1/4`
(`0 + (-4)/4 + (-1)/4 + (3/2)/6 + (3/2)/6 + 2/4`), matching plus. -/
theorem m2TransportedAllOrbitMomentDistinctHinge_axisTTCross_symbolDir :
    m2TransportedAllOrbitMomentDistinctHinge axisTTCross symbolDir =
      (-1 / 4 : ℝ) := by
  unfold m2TransportedAllOrbitMomentDistinctHinge
  rw [sum_six_orbits]
  simp only [orbitStarSize]
  rw [m2TransportedOrbitMoment_t11_cross, m2TransportedOrbitMoment_t12_cross,
    m2TransportedOrbitMoment_t21_cross, m2TransportedOrbitMoment_t13_cross,
    m2TransportedOrbitMoment_t31_cross, m2TransportedOrbitMoment_t22_cross]
  norm_num

/-- Formerly OPEN; now inhabited by the cross distinct-hinge certificate. -/
def M2DistinctHingeAxisTTCrossSymbolDirEvalOpen : Prop :=
  m2TransportedAllOrbitMomentDistinctHinge axisTTCross symbolDir =
    (-1 / 4 : ℝ)

theorem M2DistinctHingeAxisTTCrossSymbolDirEvalOpen_holds :
    M2DistinctHingeAxisTTCrossSymbolDirEvalOpen :=
  m2TransportedAllOrbitMomentDistinctHinge_axisTTCross_symbolDir

theorem m2TransportedAllOrbitMomentDistinctHinge_axisTTCrossNormalized_symbolDir :
    m2TransportedAllOrbitMomentDistinctHinge
        ((Real.sqrt 2)⁻¹ • axisTTCross) symbolDir =
      (-1 / 8 : ℝ) := by
  rw [m2TransportedAllOrbitMomentDistinctHinge_smul,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTCross_symbolDir,
    inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Plus/cross agreement on the Frobenius-normalized distinct-hinge face. -/
theorem m2TransportedDistinctHinge_plus_cross_normalized_agree_symbolDir :
    m2TransportedAllOrbitMomentDistinctHinge
        ((Real.sqrt 2)⁻¹ • axisTTPlus) symbolDir =
      m2TransportedAllOrbitMomentDistinctHinge
        ((Real.sqrt 2)⁻¹ • axisTTCross) symbolDir := by
  rw [m2TransportedAllOrbitMomentDistinctHinge_axisTTPlusNormalized_symbolDir,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTCrossNormalized_symbolDir]

/-! ## §11. Axis-aligned ray `e0Dir = (1,0,0,0)`

Integer phase scaffolding for the lattice axis.  Distinct-hinge moments
(THEOREM below): plus `0`, cross `-1/8`.  Continuum EH needs every
nonzero mode; this axis anisotropy is recorded as
`Regge4DContinuumIsotropyBlockedOnAxisMode` (OPEN, status false).
Geometric cause (MEASURED reading): TT support of plus/cross lives in
the bit-2/3 plane (`classCoeff` = `D₂−D₃` / `2 D₂ D₃`), while
`phaseScaleDir e0Dir` only sees coordinate 0, so the transported
cover does not mix the TT plane into the axis phase the way
`symbolDir = (1,1,0,0)` does.
-/

def e0Dir : Fin 4 → ℝ
  | 0 => 1
  | _ => 0

/-- Integer double-phase along `e0Dir`. -/
def phase2NatE0 (s : Fin 24) (t : Fin 10) (d : Fin 15) : ℕ :=
  2 * (if Nat.testBit (triangleVertexMasks s t).1 0 then 1 else 0) +
    (if classBit d 0 then 1 else 0)

theorem phaseScaleDir_e0Dir (s : Fin 24) (t : Fin 10) (d : Fin 15) :
    phaseScaleDir e0Dir (hingeBase s t) d = (phase2NatE0 s t d : ℝ) / 2 := by
  unfold phaseScaleDir phase2NatE0 hingeBase maskCoord classDisp e0Dir
  simp only [Fin.sum_univ_four]
  by_cases h0 : Nat.testBit (triangleVertexMasks s t).1 0
  · by_cases d0 : classBit d 0 <;> simp [h0, d0] <;> ring
  · by_cases d0 : classBit d 0 <;> simp [h0, d0] <;> ring

theorem e0Dir_normSq :
    (∑ i : Fin 4, e0Dir i * e0Dir i) = (1 : ℝ) := by
  simp [e0Dir, Fin.sum_univ_four]

def slotKppOrbitE0 (sign : Fin 15 → ℤ) (cz : Fin 15 → ℤ)
    (ty : HingeOrbitType) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d0 : Fin 15,
    sign d0 * cz (permClass (orbitCoveringPerm ty s t) d0) *
      ((phase2NatE0 s t (permClass (orbitCoveringPerm ty s t) d0) : ℕ) : ℤ) ^ 2

def m2OrbitCertZ12E0 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t12 s t then -slotAZ12 cz s t * slotKppOrbitE0 kernel12Sign cz .t12 s t
  else 0

def m2OrbitCertZ21E0 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t21 s t then -slotAZ21 cz s t * slotKppOrbitE0 kernel12Sign cz .t21 s t
  else 0

def m2OrbitCertZ13E0 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t13 s t then -slotAZ13 cz s t * slotKppOrbitE0 kernel13Sign cz .t13 s t
  else 0

def m2OrbitCertZ31E0 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t31 s t then -slotAZ31 cz s t * slotKppOrbitE0 kernel13Sign cz .t31 s t
  else 0

def m2OrbitCertZ22E0 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isOrbit .t22 s t then -slotAZ22 cz s t * slotKppOrbitE0 kernel22Sign cz .t22 s t
  else 0

def slotKppZE0 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d0 : Fin 15,
    kernel11Sign d0 * cz (permClass (slotTransportPerm s t) d0) *
      ((phase2NatE0 s t (permClass (slotTransportPerm s t) d0) : ℕ) : ℤ) ^ 2

def m2SlotCertZE0 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isT11 s t then -slotA0Z4 cz s t * slotKppZE0 cz s t else 0

private lemma ker_push_sqrt2_half_e0 (cz : Fin 15 → ℤ) (p : Fin 24)
    (H : Mat4) (hH : ∀ d, classCoeff H d = (cz d : ℝ))
    (s : Fin 24) (t : Fin 10) :
    (∑ d0 : Fin 15,
        ReggeHinge4DStarKernel12.fullStarClassKernel d0 *
          classCoeff H (permClass p d0) *
            (phaseScaleDir e0Dir (hingeBase s t) (permClass p d0)) ^ 2) =
      Real.sqrt 2 *
        (∑ d0 : Fin 15,
            kernel12Sign d0 * cz (permClass p d0) *
              ((phase2NatE0 s t (permClass p d0) : ℕ) : ℤ) ^ 2 : ℤ) / 8 := by
  simp_rw [kernel12_eq_sign, hH, phaseScaleDir_e0Dir]
  calc
    (∑ d0 : Fin 15,
        ((kernel12Sign d0 : ℝ) * (Real.sqrt 2 / 2)) *
          (cz (permClass p d0) : ℝ) *
            (((phase2NatE0 s t (permClass p d0) : ℕ) : ℝ) / 2) ^ 2) =
        Real.sqrt 2 / 8 *
          ∑ d0 : Fin 15,
            (kernel12Sign d0 : ℝ) * (cz (permClass p d0) : ℝ) *
              ((phase2NatE0 s t (permClass p d0) : ℕ) : ℝ) ^ 2 := by
      refine Eq.trans ?_ (Finset.mul_sum _ _ _).symm
      refine Finset.sum_congr rfl fun d0 _ => by ring
    _ = Real.sqrt 2 *
          (∑ d0 : Fin 15,
              kernel12Sign d0 * cz (permClass p d0) *
                ((phase2NatE0 s t (permClass p d0) : ℕ) : ℤ) ^ 2 : ℤ) / 8 := by
      rw [Int.cast_sum]
      push_cast; ring

private lemma ker_push_sqrt3_e0 (cz : Fin 15 → ℤ) (p : Fin 24)
    (H : Mat4) (hH : ∀ d, classCoeff H d = (cz d : ℝ))
    (s : Fin 24) (t : Fin 10) :
    (∑ d0 : Fin 15,
        ReggeHinge4DStarKernel13.fullStarClassKernel d0 *
          classCoeff H (permClass p d0) *
            (phaseScaleDir e0Dir (hingeBase s t) (permClass p d0)) ^ 2) =
      Real.sqrt 3 *
        (∑ d0 : Fin 15,
            kernel13Sign d0 * cz (permClass p d0) *
              ((phase2NatE0 s t (permClass p d0) : ℕ) : ℤ) ^ 2 : ℤ) / 4 := by
  simp_rw [kernel13_eq_sign, hH, phaseScaleDir_e0Dir]
  calc
    (∑ d0 : Fin 15,
        ((kernel13Sign d0 : ℝ) * Real.sqrt 3) *
          (cz (permClass p d0) : ℝ) *
            (((phase2NatE0 s t (permClass p d0) : ℕ) : ℝ) / 2) ^ 2) =
        Real.sqrt 3 / 4 *
          ∑ d0 : Fin 15,
            (kernel13Sign d0 : ℝ) * (cz (permClass p d0) : ℝ) *
              ((phase2NatE0 s t (permClass p d0) : ℕ) : ℝ) ^ 2 := by
      refine Eq.trans ?_ (Finset.mul_sum _ _ _).symm
      refine Finset.sum_congr rfl fun d0 _ => by ring
    _ = Real.sqrt 3 *
          (∑ d0 : Fin 15,
              kernel13Sign d0 * cz (permClass p d0) *
                ((phase2NatE0 s t (permClass p d0) : ℕ) : ℤ) ^ 2 : ℤ) / 4 := by
      rw [Int.cast_sum]
      push_cast; ring

theorem m2TransportedOrbitSlotCoeff_t12_eq_cert_e0 (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeff .t12 H e0Dir s t =
      (m2OrbitCertZ12E0 cz s t : ℝ) / 64 := by
  unfold m2TransportedOrbitSlotCoeff m2TransportedOrbitSlotCoeffTrunc
    m2OrbitCertZ12E0
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
    have hK :
        (∑ d : Fin 15,
            slotOrbitDeficitKer .t12 s t d * classCoeff H d *
              (phaseScaleDir e0Dir (hingeBase s t) d) ^ 2) =
          Real.sqrt 2 * (slotKppOrbitE0 kernel12Sign cz .t12 s t : ℝ) / 8 := by
      simp only [slotOrbitDeficitKer, transportedOrbitDeficit, orbitSeedKernel]
      rw [sum_mul_pushforward_weighted, ← hp]
      simpa [slotKppOrbitE0, hp] using ker_push_sqrt2_half_e0 cz p H hH s t
    rw [hA, hK]
    exact radical2_slot_arith (slotAZ12 cz s t)
      (slotKppOrbitE0 kernel12Sign cz .t12 s t)
  · simp [ht]

theorem m2TransportedOrbitSlotCoeff_t21_eq_cert_e0 (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeff .t21 H e0Dir s t =
      (m2OrbitCertZ21E0 cz s t : ℝ) / 64 := by
  unfold m2TransportedOrbitSlotCoeff m2TransportedOrbitSlotCoeffTrunc
    m2OrbitCertZ21E0
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
    have hK :
        (∑ d : Fin 15,
            slotOrbitDeficitKer .t21 s t d * classCoeff H d *
              (phaseScaleDir e0Dir (hingeBase s t) d) ^ 2) =
          Real.sqrt 2 * (slotKppOrbitE0 kernel12Sign cz .t21 s t : ℝ) / 8 := by
      simp only [slotOrbitDeficitKer, transportedOrbitDeficit, orbitSeedKernel,
        kernel21]
      rw [sum_mul_pushforward_weighted, ← hp]
      simpa [slotKppOrbitE0, hp] using ker_push_sqrt2_half_e0 cz p H hH s t
    rw [hA, hK]
    exact radical2_slot_arith (slotAZ21 cz s t)
      (slotKppOrbitE0 kernel12Sign cz .t21 s t)
  · simp [ht]

theorem m2TransportedOrbitSlotCoeff_t13_eq_cert_e0 (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeff .t13 H e0Dir s t =
      (m2OrbitCertZ13E0 cz s t : ℝ) / 32 := by
  unfold m2TransportedOrbitSlotCoeff m2TransportedOrbitSlotCoeffTrunc
    m2OrbitCertZ13E0
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
    have hK :
        (∑ d : Fin 15,
            slotOrbitDeficitKer .t13 s t d * classCoeff H d *
              (phaseScaleDir e0Dir (hingeBase s t) d) ^ 2) =
          Real.sqrt 3 * (slotKppOrbitE0 kernel13Sign cz .t13 s t : ℝ) / 4 := by
      simp only [slotOrbitDeficitKer, transportedOrbitDeficit, orbitSeedKernel]
      rw [sum_mul_pushforward_weighted, ← hp]
      simpa [slotKppOrbitE0, hp] using ker_push_sqrt3_e0 cz p H hH s t
    rw [hA, hK]
    exact radical3_slot_arith (slotAZ13 cz s t)
      (slotKppOrbitE0 kernel13Sign cz .t13 s t)
  · simp [ht]

theorem m2TransportedOrbitSlotCoeff_t31_eq_cert_e0 (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeff .t31 H e0Dir s t =
      (m2OrbitCertZ31E0 cz s t : ℝ) / 32 := by
  unfold m2TransportedOrbitSlotCoeff m2TransportedOrbitSlotCoeffTrunc
    m2OrbitCertZ31E0
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
    have hK :
        (∑ d : Fin 15,
            slotOrbitDeficitKer .t31 s t d * classCoeff H d *
              (phaseScaleDir e0Dir (hingeBase s t) d) ^ 2) =
          Real.sqrt 3 * (slotKppOrbitE0 kernel13Sign cz .t31 s t : ℝ) / 4 := by
      simp only [slotOrbitDeficitKer, transportedOrbitDeficit, orbitSeedKernel,
        kernel31]
      rw [sum_mul_pushforward_weighted, ← hp]
      simpa [slotKppOrbitE0, hp] using ker_push_sqrt3_e0 cz p H hH s t
    rw [hA, hK]
    exact radical3_slot_arith (slotAZ31 cz s t)
      (slotKppOrbitE0 kernel13Sign cz .t31 s t)
  · simp [ht]

theorem m2TransportedOrbitSlotCoeff_t22_eq_cert_e0 (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeff .t22 H e0Dir s t =
      (m2OrbitCertZ22E0 cz s t : ℝ) / 32 := by
  unfold m2TransportedOrbitSlotCoeff m2TransportedOrbitSlotCoeffTrunc
    m2OrbitCertZ22E0
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
    have hK :
        (∑ d : Fin 15,
            slotOrbitDeficitKer .t22 s t d * classCoeff H d *
              (phaseScaleDir e0Dir (hingeBase s t) d) ^ 2) =
          (slotKppOrbitE0 kernel22Sign cz .t22 s t : ℝ) / 4 := by
      simp only [slotOrbitDeficitKer, transportedOrbitDeficit, orbitSeedKernel]
      rw [sum_mul_pushforward_weighted, ← hp]
      unfold slotKppOrbitE0
      simp_rw [kernel22_eq_sign, hH, phaseScaleDir_e0Dir]
      calc
        (∑ d0 : Fin 15,
            (kernel22Sign d0 : ℝ) * (cz (permClass p d0) : ℝ) *
              (((phase2NatE0 s t (permClass p d0) : ℕ) : ℝ) / 2) ^ 2) =
            (∑ d0 : Fin 15,
                (kernel22Sign d0 : ℝ) * (cz (permClass p d0) : ℝ) *
                  ((phase2NatE0 s t (permClass p d0) : ℕ) : ℝ) ^ 2) / 4 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun d0 _ => by ring
        _ = (∑ d0 : Fin 15,
                kernel22Sign d0 * cz (permClass p d0) *
                  ((phase2NatE0 s t (permClass p d0) : ℕ) : ℤ) ^ 2 : ℤ) / 4 := by
          rw [Int.cast_sum]; push_cast; rfl
    rw [hA, hK]
    push_cast; ring
  · simp [ht]

theorem m2TransportedOrbitSlotCoeff_t11_eq_cert_e0 (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeff .t11 H e0Dir s t =
      (m2SlotCertZE0 cz s t : ℝ) / 32 := by
  unfold m2TransportedOrbitSlotCoeff m2TransportedOrbitSlotCoeffTrunc
    m2SlotCertZE0
  by_cases h : isOrbit .t11 s t
  · have ht : isT11 s t := (isOrbit_t11_iff_isT11 s t).mp h
    simp only [h, ht, ite_true]
    have hA :
        (∑ d : Fin 15, slotOrbitAreaCov .t11 s t d * classCoeff H d) =
          (slotA0Z4 cz s t : ℝ) / 4 := by
      simp only [slotOrbitAreaCov_t11 s t ht]
      unfold slotA0Z4
      have hcast : ∀ d : Fin 15,
          slotAreaCov s t d = ((slotAreaCovZ4 s t d : ℤ) : ℝ) / 4 := by
        intro d
        unfold slotAreaCov slotAreaCovZ4
        split_ifs <;> norm_num
      rw [Int.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hcast, hH]; push_cast; ring
    have hK :
        (∑ d : Fin 15,
            slotOrbitDeficitKer .t11 s t d * classCoeff H d *
              (phaseScaleDir e0Dir (hingeBase s t) d) ^ 2) =
          (slotKppZE0 cz s t : ℝ) / 4 := by
      simp only [slotOrbitDeficitKer_t11]
      have hre :
          (∑ d : Fin 15,
              slotDeficitKer s t d * classCoeff H d *
                (phaseScaleDir e0Dir (hingeBase s t) d) ^ 2) =
            ∑ d0 : Fin 15,
              ReggeHinge4DStarKernel.fullStarClassKernel d0 *
                classCoeff H (permClass (slotTransportPerm s t) d0) *
                  (phaseScaleDir e0Dir (hingeBase s t)
                    (permClass (slotTransportPerm s t) d0)) ^ 2 := by
        unfold slotDeficitKer transportedDeficit
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d0 _ => ?_
        classical
        rw [Finset.sum_eq_single (permClass (slotTransportPerm s t) d0)]
        · simp
        · intro d _ hd
          have : permClass (slotTransportPerm s t) d0 ≠ d := by
            intro heq; exact hd heq.symm
          simp [this]
        · intro huniv; exact (huniv (Finset.mem_univ _)).elim
      rw [hre]
      unfold slotKppZE0
      simp_rw [kernel11_eq_sign, hH, phaseScaleDir_e0Dir]
      rw [Int.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun d0 _ => ?_
      push_cast; ring
    rw [hA, hK]; push_cast; ring
  · have ht : ¬ isT11 s t := fun ht =>
      h ((isOrbit_t11_iff_isT11 s t).mpr ht)
    simp [h, ht]

/-! ### Integer sums on `e0Dir` (probe-confirmed targets) -/

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2SlotCertZE0_plus :
    (∑ s : Fin 24, ∑ t : Fin 10, m2SlotCertZE0 axisTTPlusCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ12E0_plus :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ12E0 axisTTPlusCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ21E0_plus :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ21E0 axisTTPlusCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ13E0_plus :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ13E0 axisTTPlusCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ31E0_plus :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ31E0 axisTTPlusCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ22E0_plus :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ22E0 axisTTPlusCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2SlotCertZE0_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2SlotCertZE0 axisTTCrossCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ12E0_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ12E0 axisTTCrossCoeffZ s t) =
      (-96 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ21E0_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ21E0 axisTTCrossCoeffZ s t) =
      (0 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ13E0_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ13E0 axisTTCrossCoeffZ s t) =
      (24 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ31E0_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ31E0 axisTTCrossCoeffZ s t) =
      (24 : ℤ) := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sum_m2OrbitCertZ22E0_cross :
    (∑ s : Fin 24, ∑ t : Fin 10, m2OrbitCertZ22E0 axisTTCrossCoeffZ s t) =
      (0 : ℤ) := by
  decide

/-! ### Real moments on `e0Dir` -/

theorem m2TransportedOrbitMoment_t11_plus_e0 :
    m2TransportedOrbitMoment .t11 axisTTPlus e0Dir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t11_eq_cert_e0 axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2SlotCertZE0 axisTTPlusCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2SlotCertZE0_plus
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t12_plus_e0 :
    m2TransportedOrbitMoment .t12 axisTTPlus e0Dir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t12_eq_cert_e0 axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ12E0 axisTTPlusCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ12E0_plus
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t21_plus_e0 :
    m2TransportedOrbitMoment .t21 axisTTPlus e0Dir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t21_eq_cert_e0 axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ21E0 axisTTPlusCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ21E0_plus
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t13_plus_e0 :
    m2TransportedOrbitMoment .t13 axisTTPlus e0Dir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t13_eq_cert_e0 axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ13E0 axisTTPlusCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ13E0_plus
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t31_plus_e0 :
    m2TransportedOrbitMoment .t31 axisTTPlus e0Dir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t31_eq_cert_e0 axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ31E0 axisTTPlusCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ31E0_plus
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t22_plus_e0 :
    m2TransportedOrbitMoment .t22 axisTTPlus e0Dir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t22_eq_cert_e0 axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ22E0 axisTTPlusCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ22E0_plus
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedAllOrbitMomentDistinctHinge_axisTTPlus_e0Dir :
    m2TransportedAllOrbitMomentDistinctHinge axisTTPlus e0Dir = (0 : ℝ) := by
  unfold m2TransportedAllOrbitMomentDistinctHinge
  rw [sum_six_orbits]
  simp only [orbitStarSize]
  rw [m2TransportedOrbitMoment_t11_plus_e0, m2TransportedOrbitMoment_t12_plus_e0,
    m2TransportedOrbitMoment_t21_plus_e0, m2TransportedOrbitMoment_t13_plus_e0,
    m2TransportedOrbitMoment_t31_plus_e0, m2TransportedOrbitMoment_t22_plus_e0]
  norm_num

theorem m2TransportedOrbitMoment_t11_cross_e0 :
    m2TransportedOrbitMoment .t11 axisTTCross e0Dir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t11_eq_cert_e0 axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2SlotCertZE0 axisTTCrossCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2SlotCertZE0_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t12_cross_e0 :
    m2TransportedOrbitMoment .t12 axisTTCross e0Dir = (-3 / 2 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t12_eq_cert_e0 axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ12E0 axisTTCrossCoeffZ s t : ℝ)) = (-96 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ12E0_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t21_cross_e0 :
    m2TransportedOrbitMoment .t21 axisTTCross e0Dir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t21_eq_cert_e0 axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ21E0 axisTTCrossCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ21E0_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t13_cross_e0 :
    m2TransportedOrbitMoment .t13 axisTTCross e0Dir = (3 / 4 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t13_eq_cert_e0 axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ13E0 axisTTCrossCoeffZ s t : ℝ)) = (24 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ13E0_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t31_cross_e0 :
    m2TransportedOrbitMoment .t31 axisTTCross e0Dir = (3 / 4 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t31_eq_cert_e0 axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ31E0 axisTTCrossCoeffZ s t : ℝ)) = (24 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ31E0_cross
  rw [sum_div_const_st, hsum]; norm_num

theorem m2TransportedOrbitMoment_t22_cross_e0 :
    m2TransportedOrbitMoment .t22 axisTTCross e0Dir = (0 : ℝ) := by
  unfold m2TransportedOrbitMoment
  simp_rw [m2TransportedOrbitSlotCoeff_t22_eq_cert_e0 axisTTCross axisTTCrossCoeffZ
    classCoeff_axisTTCross_int]
  have hsum :
      (∑ s : Fin 24, ∑ t : Fin 10,
          (m2OrbitCertZ22E0 axisTTCrossCoeffZ s t : ℝ)) = (0 : ℝ) := by
    simpa [Int.cast_sum] using
      congrArg (fun n : ℤ => (n : ℝ)) sum_m2OrbitCertZ22E0_cross
  rw [sum_div_const_st, hsum]; norm_num

/-- Distinct-hinge on cross / e0Dir: `(-3/2)/4 + (3/4)/6 + (3/4)/6 = -1/8`. -/
theorem m2TransportedAllOrbitMomentDistinctHinge_axisTTCross_e0Dir :
    m2TransportedAllOrbitMomentDistinctHinge axisTTCross e0Dir =
      (-1 / 8 : ℝ) := by
  unfold m2TransportedAllOrbitMomentDistinctHinge
  rw [sum_six_orbits]
  simp only [orbitStarSize]
  rw [m2TransportedOrbitMoment_t11_cross_e0, m2TransportedOrbitMoment_t12_cross_e0,
    m2TransportedOrbitMoment_t21_cross_e0, m2TransportedOrbitMoment_t13_cross_e0,
    m2TransportedOrbitMoment_t31_cross_e0, m2TransportedOrbitMoment_t22_cross_e0]
  norm_num

theorem m2TransportedAllOrbitMomentDistinctHinge_axisTTPlusNormalized_e0Dir :
    m2TransportedAllOrbitMomentDistinctHinge
        ((Real.sqrt 2)⁻¹ • axisTTPlus) e0Dir = (0 : ℝ) := by
  rw [m2TransportedAllOrbitMomentDistinctHinge_smul,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTPlus_e0Dir]
  norm_num

theorem m2TransportedAllOrbitMomentDistinctHinge_axisTTCrossNormalized_e0Dir :
    m2TransportedAllOrbitMomentDistinctHinge
        ((Real.sqrt 2)⁻¹ • axisTTCross) e0Dir =
      (-1 / 16 : ℝ) := by
  rw [m2TransportedAllOrbitMomentDistinctHinge_smul,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTCross_e0Dir,
    inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- **OPEN (status false)**: continuum TT isotropy is blocked on the bare
lattice-axis mode `e0Dir`, where plus vanishes and cross gives `-1/8`
(normalized `-1/16`).  Not hidden: EH Tendsto needs every nonzero mode. -/
def Regge4DContinuumIsotropyBlockedOnAxisMode : Prop :=
  m2TransportedAllOrbitMomentDistinctHinge axisTTPlus e0Dir =
    m2TransportedAllOrbitMomentDistinctHinge axisTTCross e0Dir ∧
      m2TransportedAllOrbitMomentDistinctHinge
          ((Real.sqrt 2)⁻¹ • axisTTPlus) e0Dir =
        (-1 / 16 : ℝ)

theorem Regge4DContinuumIsotropyBlockedOnAxisMode_status_false :
    ¬ Regge4DContinuumIsotropyBlockedOnAxisMode := by
  unfold Regge4DContinuumIsotropyBlockedOnAxisMode
  intro h
  have hplus := m2TransportedAllOrbitMomentDistinctHinge_axisTTPlus_e0Dir
  have hcross := m2TransportedAllOrbitMomentDistinctHinge_axisTTCross_e0Dir
  have hne : (0 : ℝ) ≠ (-1 / 8 : ℝ) := by norm_num
  exact hne (hplus.symm.trans (h.1.trans hcross))

theorem axis_mode_plus_cross_disagree_e0Dir :
    m2TransportedAllOrbitMomentDistinctHinge axisTTPlus e0Dir ≠
      m2TransportedAllOrbitMomentDistinctHinge axisTTCross e0Dir := by
  rw [m2TransportedAllOrbitMomentDistinctHinge_axisTTPlus_e0Dir,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTCross_e0Dir]
  norm_num

/-! ## §12. Full cosine two-jet `A0*K2 + A2*K0` vs truncated `A0*K2`

Integer unphased ker dots vanish for TT plus/cross on every slot
(`slotOrbitKerDot_axisTTPlus` / `slotOrbitKerDot_axisTTCross`, via
`slotOrbitKerDotZ_*` decide certificates), so the `A2*K0` summand is
identically zero and full jet equals the truncated `A0*K2` certificates
on every direction.  Consequently e0Dir anisotropy (plus `0`, cross
`-1/8`) and plus vanishing are **not** repaired by restoring `A2*K0`.
Probe receipts: `scripts/probe_m2_full_twojet_e0.py` and
`state/qg_full_theory/probe_fulljet_distinct_hinge_20260721.json`
(MEASURED off-axis faces; THEOREM on the banked axisTTPlus/Cross rays).
-/

/-- Integer unphased transported ker · `cz` (radical factored out). -/
def slotOrbitKerDotZ (sign : Fin 15 → ℤ) (cz : Fin 15 → ℤ)
    (ty : HingeOrbitType) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d0 : Fin 15,
    sign d0 * cz (permClass (orbitCoveringPerm ty s t) d0)

def slotOrbitKerDotZ_of (ty : HingeOrbitType) (cz : Fin 15 → ℤ)
    (s : Fin 24) (t : Fin 10) : ℤ :=
  match ty with
  | .t11 => slotOrbitKerDotZ kernel11Sign cz .t11 s t
  | .t12 => slotOrbitKerDotZ kernel12Sign cz .t12 s t
  | .t21 => slotOrbitKerDotZ kernel12Sign cz .t21 s t
  | .t13 => slotOrbitKerDotZ kernel13Sign cz .t13 s t
  | .t31 => slotOrbitKerDotZ kernel13Sign cz .t31 s t
  | .t22 => slotOrbitKerDotZ kernel22Sign cz .t22 s t

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in
theorem slotOrbitKerDotZ_axisTTPlus :
    ∀ ty : HingeOrbitType, ∀ s : Fin 24, ∀ t : Fin 10,
      slotOrbitKerDotZ_of ty axisTTPlusCoeffZ s t = 0 := by
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in
theorem slotOrbitKerDotZ_axisTTCross :
    ∀ ty : HingeOrbitType, ∀ s : Fin 24, ∀ t : Fin 10,
      slotOrbitKerDotZ_of ty axisTTCrossCoeffZ s t = 0 := by
  decide

private lemma slotOrbitKerDot_reindex (ty : HingeOrbitType) (H : Mat4)
    (s : Fin 24) (t : Fin 10) :
    slotOrbitKerDot ty H s t =
      ∑ d0 : Fin 15,
        orbitSeedKernel ty d0 *
          classCoeff H (permClass (orbitCoveringPerm ty s t) d0) := by
  unfold slotOrbitKerDot slotOrbitDeficitKer transportedOrbitDeficit
  exact sum_mul_pushforward (orbitSeedKernel ty) (classCoeff H)
    (orbitCoveringPerm ty s t)

/-- `orbitSeedKernel = sign * α` (matching `kernel*_eq_sign` order). -/
private lemma slotOrbitKerDot_eq_z_mul (ty : HingeOrbitType) (H : Mat4)
    (cz : Fin 15 → ℤ) (hH : ∀ d, classCoeff H d = (cz d : ℝ))
    (s : Fin 24) (t : Fin 10) (α : ℝ) (sign : Fin 15 → ℤ)
    (hker : ∀ d0, orbitSeedKernel ty d0 = (sign d0 : ℝ) * α) :
    slotOrbitKerDot ty H s t =
      α * (slotOrbitKerDotZ sign cz ty s t : ℝ) := by
  rw [slotOrbitKerDot_reindex]
  simp_rw [hker, hH]
  have hterm : ∀ d0 : Fin 15,
      (sign d0 : ℝ) * α * (cz (permClass (orbitCoveringPerm ty s t) d0) : ℝ) =
        α * ((sign d0 : ℝ) *
          (cz (permClass (orbitCoveringPerm ty s t) d0) : ℝ)) := by
    intro d0; ring
  simp_rw [hterm, ← Finset.mul_sum]
  unfold slotOrbitKerDotZ
  congr 1
  rw [Int.cast_sum]
  push_cast
  rfl

private lemma slotOrbitKerDot_of_z0 (ty : HingeOrbitType) (H : Mat4)
    (cz : Fin 15 → ℤ) (hH : ∀ d, classCoeff H d = (cz d : ℝ))
    (s : Fin 24) (t : Fin 10) (α : ℝ) (sign : Fin 15 → ℤ)
    (hker : ∀ d0, orbitSeedKernel ty d0 = (sign d0 : ℝ) * α)
    (hz : slotOrbitKerDotZ sign cz ty s t = 0) :
    slotOrbitKerDot ty H s t = 0 := by
  rw [slotOrbitKerDot_eq_z_mul ty H cz hH s t α sign hker, hz]
  simp

theorem slotOrbitKerDot_axisTTPlus (ty : HingeOrbitType) (s : Fin 24)
    (t : Fin 10) : slotOrbitKerDot ty axisTTPlus s t = 0 := by
  have hz := slotOrbitKerDotZ_axisTTPlus ty s t
  cases ty with
  | t11 =>
      exact slotOrbitKerDot_of_z0 .t11 axisTTPlus axisTTPlusCoeffZ
        classCoeff_axisTTPlus_int s t 1 kernel11Sign
        (fun d0 => by simpa using kernel11_eq_sign d0)
        (by simpa [slotOrbitKerDotZ_of] using hz)
  | t12 =>
      exact slotOrbitKerDot_of_z0 .t12 axisTTPlus axisTTPlusCoeffZ
        classCoeff_axisTTPlus_int s t (Real.sqrt 2 / 2) kernel12Sign
        (fun d0 => by simpa [orbitSeedKernel] using kernel12_eq_sign d0)
        (by simpa [slotOrbitKerDotZ_of] using hz)
  | t21 =>
      exact slotOrbitKerDot_of_z0 .t21 axisTTPlus axisTTPlusCoeffZ
        classCoeff_axisTTPlus_int s t (Real.sqrt 2 / 2) kernel12Sign
        (fun d0 => by simpa [orbitSeedKernel, kernel21] using kernel12_eq_sign d0)
        (by simpa [slotOrbitKerDotZ_of] using hz)
  | t13 =>
      exact slotOrbitKerDot_of_z0 .t13 axisTTPlus axisTTPlusCoeffZ
        classCoeff_axisTTPlus_int s t (Real.sqrt 3) kernel13Sign
        (fun d0 => by simpa [orbitSeedKernel] using kernel13_eq_sign d0)
        (by simpa [slotOrbitKerDotZ_of] using hz)
  | t31 =>
      exact slotOrbitKerDot_of_z0 .t31 axisTTPlus axisTTPlusCoeffZ
        classCoeff_axisTTPlus_int s t (Real.sqrt 3) kernel13Sign
        (fun d0 => by simpa [orbitSeedKernel, kernel31] using kernel13_eq_sign d0)
        (by simpa [slotOrbitKerDotZ_of] using hz)
  | t22 =>
      exact slotOrbitKerDot_of_z0 .t22 axisTTPlus axisTTPlusCoeffZ
        classCoeff_axisTTPlus_int s t 1 kernel22Sign
        (fun d0 => by simpa using kernel22_eq_sign d0)
        (by simpa [slotOrbitKerDotZ_of] using hz)

theorem slotOrbitKerDot_axisTTCross (ty : HingeOrbitType) (s : Fin 24)
    (t : Fin 10) : slotOrbitKerDot ty axisTTCross s t = 0 := by
  have hz := slotOrbitKerDotZ_axisTTCross ty s t
  cases ty with
  | t11 =>
      exact slotOrbitKerDot_of_z0 .t11 axisTTCross axisTTCrossCoeffZ
        classCoeff_axisTTCross_int s t 1 kernel11Sign
        (fun d0 => by simpa using kernel11_eq_sign d0)
        (by simpa [slotOrbitKerDotZ_of] using hz)
  | t12 =>
      exact slotOrbitKerDot_of_z0 .t12 axisTTCross axisTTCrossCoeffZ
        classCoeff_axisTTCross_int s t (Real.sqrt 2 / 2) kernel12Sign
        (fun d0 => by simpa [orbitSeedKernel] using kernel12_eq_sign d0)
        (by simpa [slotOrbitKerDotZ_of] using hz)
  | t21 =>
      exact slotOrbitKerDot_of_z0 .t21 axisTTCross axisTTCrossCoeffZ
        classCoeff_axisTTCross_int s t (Real.sqrt 2 / 2) kernel12Sign
        (fun d0 => by simpa [orbitSeedKernel, kernel21] using kernel12_eq_sign d0)
        (by simpa [slotOrbitKerDotZ_of] using hz)
  | t13 =>
      exact slotOrbitKerDot_of_z0 .t13 axisTTCross axisTTCrossCoeffZ
        classCoeff_axisTTCross_int s t (Real.sqrt 3) kernel13Sign
        (fun d0 => by simpa [orbitSeedKernel] using kernel13_eq_sign d0)
        (by simpa [slotOrbitKerDotZ_of] using hz)
  | t31 =>
      exact slotOrbitKerDot_of_z0 .t31 axisTTCross axisTTCrossCoeffZ
        classCoeff_axisTTCross_int s t (Real.sqrt 3) kernel13Sign
        (fun d0 => by simpa [orbitSeedKernel, kernel31] using kernel13_eq_sign d0)
        (by simpa [slotOrbitKerDotZ_of] using hz)
  | t22 =>
      exact slotOrbitKerDot_of_z0 .t22 axisTTCross axisTTCrossCoeffZ
        classCoeff_axisTTCross_int s t 1 kernel22Sign
        (fun d0 => by simpa using kernel22_eq_sign d0)
        (by simpa [slotOrbitKerDotZ_of] using hz)

theorem m2TransportedOrbitSlotCoeffFull_eq_trunc_axisTTPlus
    (ty : HingeOrbitType) (dir : Fin 4 → ℝ) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeffFull ty axisTTPlus dir s t =
      m2TransportedOrbitSlotCoeff ty axisTTPlus dir s t :=
  m2TransportedOrbitSlotCoeffFull_eq_trunc_of_ker0 ty axisTTPlus dir s t
    (slotOrbitKerDot_axisTTPlus ty s t)

theorem m2TransportedOrbitSlotCoeffFull_eq_trunc_axisTTCross
    (ty : HingeOrbitType) (dir : Fin 4 → ℝ) (s : Fin 24) (t : Fin 10) :
    m2TransportedOrbitSlotCoeffFull ty axisTTCross dir s t =
      m2TransportedOrbitSlotCoeff ty axisTTCross dir s t :=
  m2TransportedOrbitSlotCoeffFull_eq_trunc_of_ker0 ty axisTTCross dir s t
    (slotOrbitKerDot_axisTTCross ty s t)

theorem m2TransportedAllOrbitMomentDistinctHingeFull_eq_trunc_axisTTPlus
    (dir : Fin 4 → ℝ) :
    m2TransportedAllOrbitMomentDistinctHingeFull axisTTPlus dir =
      m2TransportedAllOrbitMomentDistinctHinge axisTTPlus dir := by
  unfold m2TransportedAllOrbitMomentDistinctHingeFull
    m2TransportedAllOrbitMomentDistinctHinge m2TransportedOrbitMomentFull
    m2TransportedOrbitMoment
  refine Finset.sum_congr rfl fun ty _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun t _ =>
      m2TransportedOrbitSlotCoeffFull_eq_trunc_axisTTPlus ty dir s t

theorem m2TransportedAllOrbitMomentDistinctHingeFull_eq_trunc_axisTTCross
    (dir : Fin 4 → ℝ) :
    m2TransportedAllOrbitMomentDistinctHingeFull axisTTCross dir =
      m2TransportedAllOrbitMomentDistinctHinge axisTTCross dir := by
  unfold m2TransportedAllOrbitMomentDistinctHingeFull
    m2TransportedAllOrbitMomentDistinctHinge m2TransportedOrbitMomentFull
    m2TransportedOrbitMoment
  refine Finset.sum_congr rfl fun ty _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun t _ =>
      m2TransportedOrbitSlotCoeffFull_eq_trunc_axisTTCross ty dir s t

/-- Full two-jet distinct-hinge values on e0Dir: plus `0`, cross `-1/8`
(same as truncated; anisotropy persists). -/
theorem m2TransportedAllOrbitMomentDistinctHingeFull_axisTTPlus_e0Dir :
    m2TransportedAllOrbitMomentDistinctHingeFull axisTTPlus e0Dir =
      (0 : ℝ) := by
  rw [m2TransportedAllOrbitMomentDistinctHingeFull_eq_trunc_axisTTPlus,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTPlus_e0Dir]

theorem m2TransportedAllOrbitMomentDistinctHingeFull_axisTTCross_e0Dir :
    m2TransportedAllOrbitMomentDistinctHingeFull axisTTCross e0Dir =
      (-1 / 8 : ℝ) := by
  rw [m2TransportedAllOrbitMomentDistinctHingeFull_eq_trunc_axisTTCross,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTCross_e0Dir]

theorem m2TransportedAllOrbitMomentDistinctHingeFull_axisTTPlus_symbolDir :
    m2TransportedAllOrbitMomentDistinctHingeFull axisTTPlus symbolDir =
      (-1 / 4 : ℝ) := by
  rw [m2TransportedAllOrbitMomentDistinctHingeFull_eq_trunc_axisTTPlus,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTPlus_symbolDir]

theorem m2TransportedAllOrbitMomentDistinctHingeFull_axisTTCross_symbolDir :
    m2TransportedAllOrbitMomentDistinctHingeFull axisTTCross symbolDir =
      (-1 / 4 : ℝ) := by
  rw [m2TransportedAllOrbitMomentDistinctHingeFull_eq_trunc_axisTTCross,
    m2TransportedAllOrbitMomentDistinctHinge_axisTTCross_symbolDir]

/-- Full jet does **not** restore e0Dir plus/cross isotropy. -/
theorem full_twojet_does_not_repair_e0_anisotropy :
    m2TransportedAllOrbitMomentDistinctHingeFull axisTTPlus e0Dir ≠
      m2TransportedAllOrbitMomentDistinctHingeFull axisTTCross e0Dir := by
  rw [m2TransportedAllOrbitMomentDistinctHingeFull_axisTTPlus_e0Dir,
    m2TransportedAllOrbitMomentDistinctHingeFull_axisTTCross_e0Dir]
  norm_num

/-- Normalized continuum face under full jet on e0: plus `0`, cross `-1/16`
(not EH `-1/4`). -/
theorem continuumFace_fullTwoJet_normalizedCross_e0Dir :
    m2TransportedAllOrbitMomentDistinctHingeFull
          ((Real.sqrt 2)⁻¹ • axisTTCross) e0Dir /
        (∑ i : Fin 4, e0Dir i * e0Dir i) =
      (-1 / 16 : ℝ) := by
  rw [m2TransportedAllOrbitMomentDistinctHingeFull_smul,
    m2TransportedAllOrbitMomentDistinctHingeFull_axisTTCross_e0Dir,
    e0Dir_normSq, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Named restoration claim: full two-jet makes `axisTTPlus` on `e0Dir`
leave zero.  Status false (plus stays `0` because `A2*K0` vanishes). -/
def Regge4DFullTwoJetRestoresE0PlusVanishing : Prop :=
  m2TransportedAllOrbitMomentDistinctHingeFull axisTTPlus e0Dir ≠ (0 : ℝ)

theorem Regge4DFullTwoJetRestoresE0PlusVanishing_status_false :
    ¬ Regge4DFullTwoJetRestoresE0PlusVanishing := by
  intro h
  exact h m2TransportedAllOrbitMomentDistinctHingeFull_axisTTPlus_e0Dir

/-- Named restoration claim: full two-jet restores e0Dir plus/cross
isotropy.  Status false. -/
def Regge4DFullTwoJetRestoresE0Isotropy : Prop :=
  m2TransportedAllOrbitMomentDistinctHingeFull axisTTPlus e0Dir =
    m2TransportedAllOrbitMomentDistinctHingeFull axisTTCross e0Dir

theorem Regge4DFullTwoJetRestoresE0Isotropy_status_false :
    ¬ Regge4DFullTwoJetRestoresE0Isotropy :=
  full_twojet_does_not_repair_e0_anisotropy

structure ReggeBlochFullTwoJetM2Eval4DStatus where
  k0VanishesOnTTPlusCross : Bool
  fullEqualsTruncOnTT : Bool
  e0AnisotropyPersists : Bool
  e0PlusVanishingPersists : Bool
  gapActionRecovery : Bool

def reggeBlochFullTwoJetM2Eval4DStatus :
    ReggeBlochFullTwoJetM2Eval4DStatus where
  k0VanishesOnTTPlusCross := true
  fullEqualsTruncOnTT := true
  e0AnisotropyPersists := true
  e0PlusVanishingPersists := true
  gapActionRecovery := false

theorem reggeBlochFullTwoJetM2Eval4DStatus_flags :
    reggeBlochFullTwoJetM2Eval4DStatus.k0VanishesOnTTPlusCross = true ∧
      reggeBlochFullTwoJetM2Eval4DStatus.fullEqualsTruncOnTT = true ∧
        reggeBlochFullTwoJetM2Eval4DStatus.e0AnisotropyPersists = true ∧
          reggeBlochFullTwoJetM2Eval4DStatus.e0PlusVanishingPersists =
            true ∧
            reggeBlochFullTwoJetM2Eval4DStatus.gapActionRecovery =
              false := by
  decide

theorem full_twojet_does_not_flip_gap_action_recovery :
    reggeBlochFullTwoJetM2Eval4DStatus.gapActionRecovery = false :=
  rfl

end

end ReggeBlochTransportedAllOrbitM2Eval4D
end Analysis
end Gravity
end IndisputableMonolith
