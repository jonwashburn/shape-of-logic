import Mathlib
import IndisputableMonolith.Gravity.ClausiusEinsteinBridge

/-!
# Edge TT decomposition (4D), Lorentzian algebraic layer

QG full-theory campaign, Wave 4 / lane W4-1 (`edge_tt_decomposition`),
Lorentzian specialization of the Euclidean algebraic TT layer in
`EdgeTTDecomposition4D`: transverse-traceless decomposition of symmetric
`4 × 4` real matrices against a Minkowski wave covector on `Fin 4`,
including the physically relevant **null** case.

## Tier tags (binding)

* THEOREM: every named result in this file (kernel-checked; no `sorry`, no
  `admit`, no new axioms, no `native_decide`, no `: True` shells).
* This is the Lorentzian linear-algebra layer of the ledger closing name
  `edge_tt_decomposition`.  It does **not** decompose Regge EDGE
  perturbations on a 4D lattice, does **not** prove `S_RS_converges_EH_4d`,
  does **not** flip `gap_action_recovery`, and attaches no physical
  polarization normalization.

## Conventions

Signature `(-,+,+,+)`.  Covectors are lowered by default.  Index raising
negates the time component: `(raise v) 0 = -v 0` and `(raise v) i = v i`
for spatial `i`.  The Minkowski pairing of covectors is
`minkowskiDot a b = -(a 0)(b 0) + (a 1)(b 1) + (a 2)(b 2) + (a 3)(b 3)`,
equal to `∑ j, a j * (raise b) j`.  The metric-trace of a covariant
symmetric matrix is
`minkowskiTrace H = -(H 0 0) + H 1 1 + H 2 2 + H 3 3` (`η^{ij} H_{ij}`).

Lorentz transversality contracts the second index of `H` against the
**raised** wave covector:
`∀ i, -(H i 0) * m 0 + H i 1 * m 1 + H i 2 * m 2 + H i 3 * m 3 = 0`.

* Non-null: `minkowskiDot m m ≠ 0`, projector
  `P_{ij} = η_{ij} - m_i m_j / (m·m)`.
* Null: `minkowskiDot m m = 0`, `m ≠ 0`, with auxiliary null `l` satisfying
  `minkowskiDot m l ≠ 0`; projector
  `P_{ij} = η_{ij} - (m_i l_j + l_i m_j) / (m·l)`.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace EdgeTTDecompositionLorentz4D

open Matrix BigOperators
open IndisputableMonolith.Gravity.ClausiusEinsteinBridge
  (minkowskiEta4 MinkowskiNull vec4)

noncomputable section

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

def IsSymmetric (H : Mat4) : Prop :=
  ∀ i j : Fin 4, H i j = H j i

/-- Index raising for the `(-,+,+,+)` metric: negate the time component. -/
def raise (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => if i = 0 then -v 0 else v i

/-- Minkowski pairing of covectors: `η^{ij} a_i b_j`. -/
def minkowskiDot (a b : Fin 4 → ℝ) : ℝ :=
  -(a 0) * (b 0) + (a 1) * (b 1) + (a 2) * (b 2) + (a 3) * (b 3)

/-- Metric trace of a covariant matrix: `η^{ij} H_{ij}`. -/
def minkowskiTrace (H : Mat4) : ℝ :=
  -(H 0 0) + H 1 1 + H 2 2 + H 3 3

def IsLorentzTraceless (H : Mat4) : Prop :=
  minkowskiTrace H = 0

/-- Lorentz transversality: contract `H_{ij}` with raised `m^j`. -/
def IsLorentzTransverse (m : Fin 4 → ℝ) (H : Mat4) : Prop :=
  ∀ i : Fin 4, -(H i 0) * m 0 + H i 1 * m 1 + H i 2 * m 2 + H i 3 * m 3 = 0

/-- Algebraic Lorentz TT: symmetric, Minkowski-traceless, Lorentz-transverse. -/
def IsLorentzTT (m : Fin 4 → ℝ) (H : Mat4) : Prop :=
  IsSymmetric H ∧ IsLorentzTraceless H ∧ IsLorentzTransverse m H

def minkowskiEta : Mat4 := minkowskiEta4

def gaugePart (m v : Fin 4 → ℝ) : Mat4 :=
  fun i j => m i * v j + v i * m j

def outerSq (m : Fin 4 → ℝ) : Mat4 :=
  fun i j => m i * m j

def symmetrizedOuter (m l : Fin 4 → ℝ) : Mat4 :=
  fun i j => m i * l j + l i * m j

/-- Lorentz load: `(H · m^♯)_i`. -/
def lorentzLoad (H : Mat4) (m : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => ∑ j : Fin 4, H i j * raise m j

theorem lorentzLoad_eq (H : Mat4) (m : Fin 4 → ℝ) (i : Fin 4) :
    lorentzLoad H m i =
      -(H i 0) * m 0 + H i 1 * m 1 + H i 2 * m 2 + H i 3 * m 3 := by
  unfold lorentzLoad raise
  simp [Fin.sum_univ_four]

theorem IsLorentzTransverse_iff_lorentzLoad (m : Fin 4 → ℝ) (H : Mat4) :
    IsLorentzTransverse m H ↔ ∀ i, lorentzLoad H m i = 0 := by
  constructor
  · intro h i; rw [lorentzLoad_eq]; exact h i
  · intro h i; rw [← lorentzLoad_eq]; exact h i

theorem minkowskiDot_eq_sum (a b : Fin 4 → ℝ) :
    minkowskiDot a b = ∑ i : Fin 4, a i * raise b i := by
  unfold minkowskiDot raise
  simp [Fin.sum_univ_four]

theorem minkowskiDot_comm (a b : Fin 4 → ℝ) :
    minkowskiDot a b = minkowskiDot b a := by
  unfold minkowskiDot; ring

theorem minkowskiTrace_eq_sum (H : Mat4) :
    minkowskiTrace H = ∑ i : Fin 4, ∑ j : Fin 4, minkowskiEta i j * H i j := by
  unfold minkowskiTrace minkowskiEta minkowskiEta4
  simp [Fin.sum_univ_four]

/-! ## §1. Elementary identities -/

theorem gaugePart_symmetric (m v : Fin 4 → ℝ) :
    IsSymmetric (gaugePart m v) := by
  intro i j; unfold gaugePart; ring

theorem outerSq_symmetric (m : Fin 4 → ℝ) :
    IsSymmetric (outerSq m) := by
  intro i j; unfold outerSq; ring

theorem symmetrizedOuter_symmetric (m l : Fin 4 → ℝ) :
    IsSymmetric (symmetrizedOuter m l) := by
  intro i j; unfold symmetrizedOuter; ring

theorem raise_raise (v : Fin 4 → ℝ) : raise (raise v) = v := by
  funext i
  unfold raise
  by_cases h : i = 0
  · subst h; simp
  · simp [h]

theorem lorentzLoad_smul (c : ℝ) (H : Mat4) (m : Fin 4 → ℝ) (i : Fin 4) :
    lorentzLoad (c • H) m i = c * lorentzLoad H m i := by
  unfold lorentzLoad
  simp only [smul_apply, smul_eq_mul, mul_assoc]
  exact (Finset.mul_sum Finset.univ (fun j => H i j * raise m j) c).symm

theorem lorentzLoad_sub (A B : Mat4) (m : Fin 4 → ℝ) (i : Fin 4) :
    lorentzLoad (A - B) m i = lorentzLoad A m i - lorentzLoad B m i := by
  unfold lorentzLoad; simp [sub_mul, Finset.sum_sub_distrib]

theorem lorentzLoad_eta (m : Fin 4 → ℝ) (i : Fin 4) :
    lorentzLoad minkowskiEta m i = m i := by
  rw [lorentzLoad_eq]
  unfold minkowskiEta minkowskiEta4
  fin_cases i <;> simp <;> ring_nf

theorem lorentzLoad_outerSq (m : Fin 4 → ℝ) (i : Fin 4) :
    lorentzLoad (outerSq m) m i = minkowskiDot m m * m i := by
  unfold lorentzLoad outerSq
  calc
    ∑ j : Fin 4, (m i * m j) * raise m j
        = m i * ∑ j : Fin 4, m j * raise m j := by
      simp [mul_assoc, Finset.mul_sum]
    _ = m i * minkowskiDot m m := by rw [← minkowskiDot_eq_sum]
    _ = minkowskiDot m m * m i := by ring

theorem lorentzLoad_symmetrizedOuter (m l : Fin 4 → ℝ) (i : Fin 4) :
    lorentzLoad (symmetrizedOuter m l) m i =
      minkowskiDot l m * m i + minkowskiDot m m * l i := by
  unfold lorentzLoad symmetrizedOuter
  calc
    ∑ j : Fin 4, (m i * l j + l i * m j) * raise m j
        = ∑ j : Fin 4, (m i * (l j * raise m j) + l i * (m j * raise m j)) := by
      refine Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ j : Fin 4, m i * (l j * raise m j)) +
          (∑ j : Fin 4, l i * (m j * raise m j)) := Finset.sum_add_distrib
    _ = m i * ∑ j : Fin 4, l j * raise m j +
          l i * ∑ j : Fin 4, m j * raise m j := by
      simp [Finset.mul_sum]
    _ = m i * minkowskiDot l m + l i * minkowskiDot m m := by
      simp [← minkowskiDot_eq_sum]
    _ = minkowskiDot l m * m i + minkowskiDot m m * l i := by ring

theorem lorentzLoad_symmetrizedOuter_l (m l : Fin 4 → ℝ) (i : Fin 4) :
    lorentzLoad (symmetrizedOuter m l) l i =
      minkowskiDot l l * m i + minkowskiDot m l * l i := by
  unfold lorentzLoad symmetrizedOuter
  calc
    ∑ j : Fin 4, (m i * l j + l i * m j) * raise l j
        = ∑ j : Fin 4, (m i * (l j * raise l j) + l i * (m j * raise l j)) := by
      refine Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ j : Fin 4, m i * (l j * raise l j)) +
          (∑ j : Fin 4, l i * (m j * raise l j)) := Finset.sum_add_distrib
    _ = m i * ∑ j : Fin 4, l j * raise l j +
          l i * ∑ j : Fin 4, m j * raise l j := by
      simp [Finset.mul_sum]
    _ = m i * minkowskiDot l l + l i * minkowskiDot m l := by
      simp [← minkowskiDot_eq_sum]
    _ = minkowskiDot l l * m i + minkowskiDot m l * l i := by ring

theorem lorentzLoad_gaugePart (m v : Fin 4 → ℝ) (i : Fin 4) :
    lorentzLoad (gaugePart m v) m i =
      minkowskiDot m m * v i + m i * minkowskiDot v m := by
  unfold lorentzLoad gaugePart
  calc
    ∑ j : Fin 4, (m i * v j + v i * m j) * raise m j
        = ∑ j : Fin 4, (m i * (v j * raise m j) + v i * (m j * raise m j)) := by
      refine Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ j : Fin 4, m i * (v j * raise m j)) +
          (∑ j : Fin 4, v i * (m j * raise m j)) := Finset.sum_add_distrib
    _ = m i * ∑ j : Fin 4, v j * raise m j +
          v i * ∑ j : Fin 4, m j * raise m j := by
      simp [Finset.mul_sum]
    _ = m i * minkowskiDot v m + v i * minkowskiDot m m := by
      simp [← minkowskiDot_eq_sum]
    _ = minkowskiDot m m * v i + m i * minkowskiDot v m := by ring

theorem minkowskiTrace_smul (c : ℝ) (H : Mat4) :
    minkowskiTrace (c • H) = c * minkowskiTrace H := by
  unfold minkowskiTrace
  simp only [smul_apply, smul_eq_mul]
  ring

theorem minkowskiTrace_sub (A B : Mat4) :
    minkowskiTrace (A - B) = minkowskiTrace A - minkowskiTrace B := by
  unfold minkowskiTrace
  simp only [sub_apply]
  ring

theorem minkowskiTrace_add (A B : Mat4) :
    minkowskiTrace (A + B) = minkowskiTrace A + minkowskiTrace B := by
  unfold minkowskiTrace
  simp only [add_apply]
  ring

theorem minkowskiTrace_eta : minkowskiTrace minkowskiEta = 4 := by
  unfold minkowskiTrace minkowskiEta minkowskiEta4
  simp; norm_num

theorem minkowskiTrace_outerSq (m : Fin 4 → ℝ) :
    minkowskiTrace (outerSq m) = minkowskiDot m m := by
  unfold minkowskiTrace outerSq minkowskiDot; ring

theorem minkowskiTrace_symmetrizedOuter (m l : Fin 4 → ℝ) :
    minkowskiTrace (symmetrizedOuter m l) = 2 * minkowskiDot m l := by
  unfold minkowskiTrace symmetrizedOuter minkowskiDot; ring

theorem minkowskiDot_eq_MinkowskiNull (k : Fin 4 → ℝ) :
    minkowskiDot k k = 0 ↔ MinkowskiNull k := by
  unfold minkowskiDot MinkowskiNull
  constructor <;> intro h <;> linarith

/-! ## §2. Non-null transverse projector and gauge removal -/

def transverseProjector (m : Fin 4 → ℝ) : Mat4 :=
  minkowskiEta - (minkowskiDot m m)⁻¹ • outerSq m

def gaugeVector (m : Fin 4 → ℝ) (H : Mat4) : Fin 4 → ℝ :=
  fun i =>
    let w := lorentzLoad H m
    let s := minkowskiDot m m
    w i / s - m i * minkowskiDot w m / (2 * s ^ 2)

def gaugeCorrected (m : Fin 4 → ℝ) (H : Mat4) : Mat4 :=
  H - gaugePart m (gaugeVector m H)

def residualTrace (m : Fin 4 → ℝ) (H : Mat4) : ℝ :=
  minkowskiTrace (gaugeCorrected m H) / 3

def ttProject (m : Fin 4 → ℝ) (H : Mat4) : Mat4 :=
  gaugeCorrected m H - residualTrace m H • transverseProjector m

theorem minkowskiEta_symmetric : IsSymmetric minkowskiEta := by
  intro i j
  unfold minkowskiEta minkowskiEta4
  by_cases hij : i = j
  · subst hij; rfl
  · simp [hij, Ne.symm hij]

theorem transverseProjector_symmetric (m : Fin 4 → ℝ) :
    IsSymmetric (transverseProjector m) := by
  intro i j
  unfold transverseProjector
  simp only [sub_apply, smul_apply, smul_eq_mul]
  rw [minkowskiEta_symmetric i j, outerSq_symmetric m i j]

theorem lorentzLoad_transverseProjector (m : Fin 4 → ℝ)
    (hm : minkowskiDot m m ≠ 0) (i : Fin 4) :
    lorentzLoad (transverseProjector m) m i = 0 := by
  unfold transverseProjector
  rw [lorentzLoad_sub, lorentzLoad_eta, lorentzLoad_smul, lorentzLoad_outerSq]
  field_simp [hm]; ring

theorem minkowskiDot_gaugeVector (m : Fin 4 → ℝ) (H : Mat4)
    (hm : minkowskiDot m m ≠ 0) :
    minkowskiDot (gaugeVector m H) m =
      minkowskiDot (lorentzLoad H m) m / (2 * minkowskiDot m m) := by
  set w := lorentzLoad H m with hw
  set s := minkowskiDot m m with hs
  have hs0 : s ≠ 0 := hm
  set d := minkowskiDot w m with hd
  have hexpand :
      minkowskiDot (gaugeVector m H) m =
        ∑ i : Fin 4, (w i / s - m i * d / (2 * s ^ 2)) * raise m i := by
    simp only [minkowskiDot_eq_sum, gaugeVector, w, s, d]
  have hsplit :
      ∑ i : Fin 4, (w i / s - m i * d / (2 * s ^ 2)) * raise m i =
        ∑ i : Fin 4, (w i / s) * raise m i -
          ∑ i : Fin 4, (m i * d / (2 * s ^ 2)) * raise m i := by
    simp [sub_mul, Finset.sum_sub_distrib]
  have h1 : ∑ i : Fin 4, (w i / s) * raise m i = d / s := by
    simp only [d, minkowskiDot_eq_sum, div_eq_mul_inv, mul_assoc]
    have :
        ∑ i : Fin 4, s⁻¹ * w i * raise m i =
          s⁻¹ * ∑ i : Fin 4, w i * raise m i := by
      simp [mul_assoc, ← Finset.mul_sum]
    convert this using 1
    · refine Finset.sum_congr rfl fun i _ => by ring
    · ring
  have h2 :
      ∑ i : Fin 4, (m i * d / (2 * s ^ 2)) * raise m i =
        s * d / (2 * s ^ 2) := by
    have :
        ∑ i : Fin 4, m i * raise m i * (d / (2 * s ^ 2)) =
          (∑ i : Fin 4, m i * raise m i) * (d / (2 * s ^ 2)) :=
      (Finset.sum_mul _ _ _).symm
    calc
      ∑ i : Fin 4, (m i * d / (2 * s ^ 2)) * raise m i
          = ∑ i : Fin 4, m i * raise m i * (d / (2 * s ^ 2)) := by
        refine Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i : Fin 4, m i * raise m i) * (d / (2 * s ^ 2)) := this
      _ = s * d / (2 * s ^ 2) := by
        simp [← minkowskiDot_eq_sum, s]; ring
  calc
    minkowskiDot (gaugeVector m H) m
        = ∑ i : Fin 4, (w i / s - m i * d / (2 * s ^ 2)) * raise m i := hexpand
    _ = d / s - s * d / (2 * s ^ 2) := by rw [hsplit, h1, h2]
    _ = d / (2 * s) := by field_simp [hs0]; ring
    _ = minkowskiDot (lorentzLoad H m) m / (2 * minkowskiDot m m) := by
        simp [d, w, s]

theorem lorentzLoad_gaugePart_gaugeVector (m : Fin 4 → ℝ) (H : Mat4)
    (hm : minkowskiDot m m ≠ 0) (i : Fin 4) :
    lorentzLoad (gaugePart m (gaugeVector m H)) m i = lorentzLoad H m i := by
  set w := lorentzLoad H m
  set s := minkowskiDot m m
  set v := gaugeVector m H
  have hs0 : s ≠ 0 := hm
  have hL := lorentzLoad_gaugePart m v i
  have hdot := minkowskiDot_gaugeVector m H hm
  have hvi : v i = w i / s - m i * minkowskiDot w m / (2 * s ^ 2) := rfl
  have key : s * v i + m i * minkowskiDot v m = w i := by
    rw [hvi, show minkowskiDot v m = minkowskiDot w m / (2 * s) from hdot]
    field_simp [hs0]; ring
  rw [hL]; simpa [s, w, v] using key

theorem gaugeCorrected_transverse (m : Fin 4 → ℝ) (H : Mat4)
    (hm : minkowskiDot m m ≠ 0) :
    IsLorentzTransverse m (gaugeCorrected m H) := by
  intro i
  rw [← lorentzLoad_eq]
  simp [gaugeCorrected, lorentzLoad_sub, lorentzLoad_gaugePart_gaugeVector m H hm]

theorem gaugeCorrected_symmetric (m : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) :
    IsSymmetric (gaugeCorrected m H) := by
  intro i j
  simp only [gaugeCorrected, sub_apply]
  rw [hH i j, gaugePart_symmetric m (gaugeVector m H) i j]

theorem minkowskiTrace_transverseProjector (m : Fin 4 → ℝ)
    (hm : minkowskiDot m m ≠ 0) :
    minkowskiTrace (transverseProjector m) = 3 := by
  unfold transverseProjector
  rw [minkowskiTrace_sub, minkowskiTrace_smul, minkowskiTrace_eta,
    minkowskiTrace_outerSq]
  field_simp [hm]; ring

theorem ttProject_symmetric (m : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) :
    IsSymmetric (ttProject m H) := by
  intro i j
  simp only [ttProject, sub_apply, smul_apply, smul_eq_mul]
  rw [gaugeCorrected_symmetric m H hH i j,
    transverseProjector_symmetric m i j]

theorem ttProject_transverse (m : Fin 4 → ℝ) (H : Mat4)
    (hm : minkowskiDot m m ≠ 0) :
    IsLorentzTransverse m (ttProject m H) := by
  intro i
  rw [← lorentzLoad_eq]
  have h1 : lorentzLoad (gaugeCorrected m H) m i = 0 := by
    rw [lorentzLoad_eq]; exact gaugeCorrected_transverse m H hm i
  have h2 := lorentzLoad_transverseProjector m hm i
  simp [ttProject, lorentzLoad_sub, lorentzLoad_smul, h1, h2]

theorem ttProject_traceless (m : Fin 4 → ℝ) (H : Mat4)
    (hm : minkowskiDot m m ≠ 0) :
    IsLorentzTraceless (ttProject m H) := by
  unfold IsLorentzTraceless ttProject residualTrace
  rw [minkowskiTrace_sub, minkowskiTrace_smul,
    minkowskiTrace_transverseProjector m hm]
  ring

theorem ttProject_isLorentzTT (m : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) (hm : minkowskiDot m m ≠ 0) :
    IsLorentzTT m (ttProject m H) :=
  ⟨ttProject_symmetric m H hH, ttProject_traceless m H hm,
    ttProject_transverse m H hm⟩

/-- **THEOREM (non-null Lorentzian algebraic `edge_tt_decomposition`).**
Every symmetric `4 × 4` matrix against a non-null Minkowski wave covector
decomposes as Lorentz-TT + gauge + transverse-trace part. -/
theorem exists_lorentzTTDecomposition (m : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) (hm : minkowskiDot m m ≠ 0) :
    H = ttProject m H + gaugePart m (gaugeVector m H) +
        residualTrace m H • transverseProjector m ∧
      IsLorentzTT m (ttProject m H) := by
  refine ⟨?_, ttProject_isLorentzTT m H hH hm⟩
  unfold ttProject gaugeCorrected; abel

theorem exists_lorentzTTDecomposition' (m : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) (hm : minkowskiDot m m ≠ 0) :
    ∃ (H_TT : Mat4) (v : Fin 4 → ℝ) (β : ℝ),
      H = H_TT + gaugePart m v + β • transverseProjector m ∧
        IsLorentzTT m H_TT :=
  ⟨ttProject m H, gaugeVector m H, residualTrace m H,
    exists_lorentzTTDecomposition m H hH hm⟩

/-! ## §3. Null-frame projector -/

/-- Null-frame transverse projector against null `m` with auxiliary null `l`. -/
def nullProjector (m l : Fin 4 → ℝ) : Mat4 :=
  minkowskiEta - (minkowskiDot m l)⁻¹ • symmetrizedOuter m l

def nullSMixed (m l : Fin 4 → ℝ) (i a : Fin 4) : ℝ :=
  (m i * raise l a + l i * raise m a) / minkowskiDot m l

def kron (i j : Fin 4) : ℝ := if i = j then 1 else 0

def nullPMixed (m l : Fin 4 → ℝ) (i a : Fin 4) : ℝ :=
  kron i a - nullSMixed m l i a

/-- Double mixed projection `(P H P)_{ij} = P_i{}^a H_{ab} P_j{}^b`. -/
def nullPhp (m l : Fin 4 → ℝ) (H : Mat4) : Mat4 :=
  fun i j => ∑ a : Fin 4, ∑ b : Fin 4,
    nullPMixed m l i a * H a b * nullPMixed m l j b

/-- Bilinear remainder `S H S` in the null gap expansion. -/
def nullBilinear (m l : Fin 4 → ℝ) (H : Mat4) : Mat4 :=
  fun i j => ∑ a : Fin 4, ∑ b : Fin 4,
    nullSMixed m l i a * H a b * nullSMixed m l j b

def nullMGaugeVector (m l : Fin 4 → ℝ) (H : Mat4) : Fin 4 → ℝ :=
  fun j => lorentzLoad H l j / minkowskiDot m l

def nullLGaugeVector (m l : Fin 4 → ℝ) (H : Mat4) : Fin 4 → ℝ :=
  fun j => lorentzLoad H m j / minkowskiDot m l

/-- Explicit gap `H - PHP = gauge_m + gauge_l - SHS`. -/
def nullGap (m l : Fin 4 → ℝ) (H : Mat4) : Mat4 :=
  gaugePart m (nullMGaugeVector m l H) +
    gaugePart l (nullLGaugeVector m l H) -
    nullBilinear m l H

def nullTraceCoeff (m l : Fin 4 → ℝ) (H : Mat4) : ℝ :=
  minkowskiTrace (nullPhp m l H) / 2

def nullTTProject (m l : Fin 4 → ℝ) (H : Mat4) : Mat4 :=
  nullPhp m l H - nullTraceCoeff m l H • nullProjector m l

theorem nullProjector_symmetric (m l : Fin 4 → ℝ) :
    IsSymmetric (nullProjector m l) := by
  intro i j
  unfold nullProjector
  simp only [sub_apply, smul_apply, smul_eq_mul]
  rw [minkowskiEta_symmetric i j, symmetrizedOuter_symmetric m l i j]

theorem nullProjector_minkowskiTrace (m l : Fin 4 → ℝ)
    (hml : minkowskiDot m l ≠ 0) :
    minkowskiTrace (nullProjector m l) = 2 := by
  unfold nullProjector
  rw [minkowskiTrace_sub, minkowskiTrace_smul, minkowskiTrace_eta,
    minkowskiTrace_symmetrizedOuter]
  field_simp [hml]; ring

theorem lorentzLoad_nullProjector_m (m l : Fin 4 → ℝ)
    (hm0 : minkowskiDot m m = 0) (hml : minkowskiDot m l ≠ 0)
    (i : Fin 4) :
    lorentzLoad (nullProjector m l) m i = 0 := by
  unfold nullProjector
  rw [lorentzLoad_sub, lorentzLoad_eta, lorentzLoad_smul,
    lorentzLoad_symmetrizedOuter, minkowskiDot_comm l m, hm0]
  field_simp [hml]; ring

theorem lorentzLoad_nullProjector_l (m l : Fin 4 → ℝ)
    (hl0 : minkowskiDot l l = 0) (hml : minkowskiDot m l ≠ 0)
    (i : Fin 4) :
    lorentzLoad (nullProjector m l) l i = 0 := by
  unfold nullProjector
  rw [lorentzLoad_sub, lorentzLoad_eta, lorentzLoad_smul,
    lorentzLoad_symmetrizedOuter_l, hl0]
  field_simp [hml]; ring

theorem sum_kron_left (i : Fin 4) (f : Fin 4 → ℝ) :
    (∑ a : Fin 4, kron i a * f a) = f i := by
  unfold kron
  rw [Finset.sum_eq_single (a := i)]
  · simp
  · intro a _ ha
    rw [if_neg (Ne.symm ha)]; simp
  · intro hi; exact (hi (Finset.mem_univ i)).elim

theorem sum_kron_right (j : Fin 4) (f : Fin 4 → ℝ) :
    (∑ b : Fin 4, f b * kron j b) = f j := by
  unfold kron
  rw [Finset.sum_eq_single (a := j)]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]; simp
  · intro hj; exact (hj (Finset.mem_univ j)).elim

theorem nullPhp_expand_algebra (m l : Fin 4 → ℝ) (H : Mat4) (i j : Fin 4) :
    (∑ a : Fin 4, ∑ b : Fin 4,
        (kron i a - nullSMixed m l i a) * H a b *
          (kron j b - nullSMixed m l j b)) =
      (∑ a : Fin 4, ∑ b : Fin 4, kron i a * H a b * kron j b)
        - (∑ a : Fin 4, ∑ b : Fin 4, nullSMixed m l i a * H a b * kron j b)
        - (∑ a : Fin 4, ∑ b : Fin 4, kron i a * H a b * nullSMixed m l j b)
        + (∑ a : Fin 4, ∑ b : Fin 4,
            nullSMixed m l i a * H a b * nullSMixed m l j b) := by
  have hpoint (a b : Fin 4) :
      (kron i a - nullSMixed m l i a) * H a b *
          (kron j b - nullSMixed m l j b) =
        kron i a * H a b * kron j b
          - nullSMixed m l i a * H a b * kron j b
          - kron i a * H a b * nullSMixed m l j b
          + nullSMixed m l i a * H a b * nullSMixed m l j b := by
    ring
  simp_rw [hpoint]
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem sum_kron_H_kron (H : Mat4) (i j : Fin 4) :
    (∑ a : Fin 4, ∑ b : Fin 4, kron i a * H a b * kron j b) = H i j := by
  calc
    ∑ a : Fin 4, ∑ b : Fin 4, kron i a * H a b * kron j b
        = ∑ a : Fin 4, kron i a * (∑ b : Fin 4, H a b * kron j b) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [mul_assoc, Finset.mul_sum]
    _ = ∑ a : Fin 4, kron i a * H a j := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [sum_kron_right]
    _ = H i j := sum_kron_left i _

theorem sum_S_H_kron (m l : Fin 4 → ℝ) (H : Mat4) (i j : Fin 4) :
    (∑ a : Fin 4, ∑ b : Fin 4, nullSMixed m l i a * H a b * kron j b) =
      ∑ a : Fin 4, nullSMixed m l i a * H a j := by
  refine Finset.sum_congr rfl fun a _ => ?_
  have :
      (∑ b : Fin 4, nullSMixed m l i a * H a b * kron j b) =
        nullSMixed m l i a * ∑ b : Fin 4, H a b * kron j b := by
    simp [mul_assoc, Finset.mul_sum]
  rw [this, sum_kron_right]

theorem sum_kron_H_S (m l : Fin 4 → ℝ) (H : Mat4) (i j : Fin 4) :
    (∑ a : Fin 4, ∑ b : Fin 4, kron i a * H a b * nullSMixed m l j b) =
      ∑ b : Fin 4, H i b * nullSMixed m l j b := by
  calc
    ∑ a : Fin 4, ∑ b : Fin 4, kron i a * H a b * nullSMixed m l j b
        = ∑ a : Fin 4, kron i a * ∑ b : Fin 4, H a b * nullSMixed m l j b := by
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [mul_assoc, Finset.mul_sum]
    _ = ∑ b : Fin 4, H i b * nullSMixed m l j b := by
      rw [sum_kron_left]

theorem nullPhp_entry (m l : Fin 4 → ℝ) (H : Mat4) (i j : Fin 4) :
    nullPhp m l H i j =
      H i j
        - (∑ a : Fin 4, nullSMixed m l i a * H a j)
        - (∑ b : Fin 4, H i b * nullSMixed m l j b)
        + nullBilinear m l H i j := by
  have hexpand := nullPhp_expand_algebra m l H i j
  simp only [nullPhp, nullPMixed, nullBilinear]
  rw [hexpand, sum_kron_H_kron, sum_S_H_kron, sum_kron_H_S]

theorem sum_nullSMixed_H_col (m l : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) (hml : minkowskiDot m l ≠ 0) (i j : Fin 4) :
    (∑ a : Fin 4, nullSMixed m l i a * H a j) =
      m i * (lorentzLoad H l j / minkowskiDot m l) +
        l i * (lorentzLoad H m j / minkowskiDot m l) := by
  set s := minkowskiDot m l with hs
  have hs0 : s ≠ 0 := hml
  have hterm (a : Fin 4) :
      nullSMixed m l i a * H a j =
        (m i / s) * (raise l a * H a j) + (l i / s) * (raise m a * H a j) := by
    unfold nullSMixed
    field_simp [hs0, s]; ring
  have hcol (v : Fin 4 → ℝ) :
      (∑ a : Fin 4, raise v a * H a j) = lorentzLoad H v j := by
    unfold lorentzLoad
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hH a j, mul_comm]
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hcol]
  field_simp [hs0]

theorem sum_H_nullSMixed_row (m l : Fin 4 → ℝ) (H : Mat4)
    (hml : minkowskiDot m l ≠ 0) (i j : Fin 4) :
    (∑ b : Fin 4, H i b * nullSMixed m l j b) =
      m j * (lorentzLoad H l i / minkowskiDot m l) +
        l j * (lorentzLoad H m i / minkowskiDot m l) := by
  set s := minkowskiDot m l with hs
  have hs0 : s ≠ 0 := hml
  have hterm (b : Fin 4) :
      H i b * nullSMixed m l j b =
        (m j / s) * (H i b * raise l b) + (l j / s) * (H i b * raise m b) := by
    unfold nullSMixed
    field_simp [hs0, s]; ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [lorentzLoad]
  field_simp [hs0]

theorem nullGap_entry (m l : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) (hml : minkowskiDot m l ≠ 0) (i j : Fin 4) :
    nullGap m l H i j =
      (∑ a : Fin 4, nullSMixed m l i a * H a j) +
        (∑ b : Fin 4, H i b * nullSMixed m l j b) -
        nullBilinear m l H i j := by
  unfold nullGap gaugePart nullMGaugeVector nullLGaugeVector
  simp only [add_apply, sub_apply]
  rw [sum_nullSMixed_H_col m l H hH hml i j,
    sum_H_nullSMixed_row m l H hml i j]
  ring

/-- Explicit residual identity: `H = PHP + m-gauge + l-gauge - bilinear`. -/
theorem null_gap_expansion (m l : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) (hml : minkowskiDot m l ≠ 0) :
    H = nullPhp m l H + nullGap m l H := by
  ext i j
  have hphp := nullPhp_entry m l H i j
  have hgap := nullGap_entry m l H hH hml i j
  simp only [add_apply]
  linarith

theorem nullPhp_symmetric (m l : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) :
    IsSymmetric (nullPhp m l H) := by
  intro i j
  unfold nullPhp
  calc
    ∑ a : Fin 4, ∑ b : Fin 4,
        nullPMixed m l i a * H a b * nullPMixed m l j b
        = ∑ b : Fin 4, ∑ a : Fin 4,
            nullPMixed m l i a * H a b * nullPMixed m l j b := by
      rw [Finset.sum_comm]
    _ = ∑ b : Fin 4, ∑ a : Fin 4,
            nullPMixed m l j b * H b a * nullPMixed m l i a := by
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      rw [hH a b]; ring
    _ = ∑ a : Fin 4, ∑ b : Fin 4,
        nullPMixed m l j a * H a b * nullPMixed m l i b := by
      rw [Finset.sum_comm]

/-- Core: `∑ j, S j b * m^j = m^b` when `m` is null. -/
theorem sum_nullSMixed_raise_m (m l : Fin 4 → ℝ)
    (hm0 : minkowskiDot m m = 0) (hml : minkowskiDot m l ≠ 0)
    (b : Fin 4) :
    (∑ j : Fin 4, nullSMixed m l j b * raise m j) = raise m b := by
  set s := minkowskiDot m l with hs
  have hs0 : s ≠ 0 := hml
  have hterm (j : Fin 4) :
      nullSMixed m l j b * raise m j =
        (raise l b / s) * (m j * raise m j) +
          (raise m b / s) * (l j * raise m j) := by
    unfold nullSMixed
    field_simp [hs0, s]; ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [← minkowskiDot_eq_sum]
  rw [hm0, minkowskiDot_comm l m]
  field_simp [hs0]; ring

theorem sum_nullPMixed_raise_m (m l : Fin 4 → ℝ)
    (hm0 : minkowskiDot m m = 0) (hml : minkowskiDot m l ≠ 0)
    (b : Fin 4) :
    (∑ j : Fin 4, nullPMixed m l j b * raise m j) = 0 := by
  unfold nullPMixed
  simp only [sub_mul, Finset.sum_sub_distrib]
  have hδ : (∑ j : Fin 4, kron j b * raise m j) = raise m b := by
    -- kron j b = kron b j
    have : ∀ j, kron j b = kron b j := by
      intro j; unfold kron; simp [eq_comm]
    simp_rw [this]
    exact sum_kron_left b (raise m)
  rw [hδ, sum_nullSMixed_raise_m m l hm0 hml b]
  ring

theorem sum_nullSMixed_raise_l (m l : Fin 4 → ℝ)
    (hl0 : minkowskiDot l l = 0) (hml : minkowskiDot m l ≠ 0)
    (b : Fin 4) :
    (∑ j : Fin 4, nullSMixed m l j b * raise l j) = raise l b := by
  set s := minkowskiDot m l with hs
  have hs0 : s ≠ 0 := hml
  have hterm (j : Fin 4) :
      nullSMixed m l j b * raise l j =
        (raise l b / s) * (m j * raise l j) +
          (raise m b / s) * (l j * raise l j) := by
    unfold nullSMixed
    field_simp [hs0, s]; ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [← minkowskiDot_eq_sum]
  rw [hl0]
  field_simp [hs0]; ring

theorem sum_nullPMixed_raise_l (m l : Fin 4 → ℝ)
    (hl0 : minkowskiDot l l = 0) (hml : minkowskiDot m l ≠ 0)
    (b : Fin 4) :
    (∑ j : Fin 4, nullPMixed m l j b * raise l j) = 0 := by
  unfold nullPMixed
  simp only [sub_mul, Finset.sum_sub_distrib]
  have hδ : (∑ j : Fin 4, kron j b * raise l j) = raise l b := by
    have : ∀ j, kron j b = kron b j := by
      intro j; unfold kron; simp [eq_comm]
    simp_rw [this]
    exact sum_kron_left b (raise l)
  rw [hδ, sum_nullSMixed_raise_l m l hl0 hml b]
  ring

theorem nullPhp_lorentzLoad_m (m l : Fin 4 → ℝ) (H : Mat4)
    (hm0 : minkowskiDot m m = 0) (hml : minkowskiDot m l ≠ 0)
    (i : Fin 4) :
    lorentzLoad (nullPhp m l H) m i = 0 := by
  unfold lorentzLoad nullPhp
  have hswap :
      (∑ j : Fin 4,
          (∑ a : Fin 4, ∑ b : Fin 4,
              nullPMixed m l i a * H a b * nullPMixed m l j b) * raise m j) =
        ∑ a : Fin 4, ∑ b : Fin 4,
          nullPMixed m l i a * H a b *
            (∑ j : Fin 4, nullPMixed m l j b * raise m j) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [hswap]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  simp [sum_nullPMixed_raise_m m l hm0 hml b]

theorem nullPhp_transverse_m (m l : Fin 4 → ℝ) (H : Mat4)
    (hm0 : minkowskiDot m m = 0) (hml : minkowskiDot m l ≠ 0) :
    IsLorentzTransverse m (nullPhp m l H) := by
  intro i
  rw [← lorentzLoad_eq]
  exact nullPhp_lorentzLoad_m m l H hm0 hml i

theorem nullPhp_lorentzLoad_l (m l : Fin 4 → ℝ) (H : Mat4)
    (hl0 : minkowskiDot l l = 0) (hml : minkowskiDot m l ≠ 0)
    (i : Fin 4) :
    lorentzLoad (nullPhp m l H) l i = 0 := by
  unfold lorentzLoad nullPhp
  have hswap :
      (∑ j : Fin 4,
          (∑ a : Fin 4, ∑ b : Fin 4,
              nullPMixed m l i a * H a b * nullPMixed m l j b) * raise l j) =
        ∑ a : Fin 4, ∑ b : Fin 4,
          nullPMixed m l i a * H a b *
            (∑ j : Fin 4, nullPMixed m l j b * raise l j) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [hswap]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  simp [sum_nullPMixed_raise_l m l hl0 hml b]

theorem nullPhp_transverse_l (m l : Fin 4 → ℝ) (H : Mat4)
    (hl0 : minkowskiDot l l = 0) (hml : minkowskiDot m l ≠ 0) :
    IsLorentzTransverse l (nullPhp m l H) := by
  intro i
  rw [← lorentzLoad_eq]
  exact nullPhp_lorentzLoad_l m l H hl0 hml i

theorem nullTTProject_symmetric (m l : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) :
    IsSymmetric (nullTTProject m l H) := by
  intro i j
  simp only [nullTTProject, sub_apply, smul_apply, smul_eq_mul]
  rw [nullPhp_symmetric m l H hH i j, nullProjector_symmetric m l i j]

theorem nullTTProject_traceless (m l : Fin 4 → ℝ) (H : Mat4)
    (hml : minkowskiDot m l ≠ 0) :
    IsLorentzTraceless (nullTTProject m l H) := by
  unfold IsLorentzTraceless nullTTProject nullTraceCoeff
  rw [minkowskiTrace_sub, minkowskiTrace_smul,
    nullProjector_minkowskiTrace m l hml]
  ring

theorem nullTTProject_transverse_m (m l : Fin 4 → ℝ) (H : Mat4)
    (hm0 : minkowskiDot m m = 0) (hml : minkowskiDot m l ≠ 0) :
    IsLorentzTransverse m (nullTTProject m l H) := by
  intro i
  rw [← lorentzLoad_eq]
  have h1 := nullPhp_lorentzLoad_m m l H hm0 hml i
  have h2 := lorentzLoad_nullProjector_m m l hm0 hml i
  simp [nullTTProject, lorentzLoad_sub, lorentzLoad_smul, h1, h2]

theorem nullTTProject_transverse_l (m l : Fin 4 → ℝ) (H : Mat4)
    (hl0 : minkowskiDot l l = 0) (hml : minkowskiDot m l ≠ 0) :
    IsLorentzTransverse l (nullTTProject m l H) := by
  intro i
  rw [← lorentzLoad_eq]
  have h1 := nullPhp_lorentzLoad_l m l H hl0 hml i
  have h2 := lorentzLoad_nullProjector_l m l hl0 hml i
  simp [nullTTProject, lorentzLoad_sub, lorentzLoad_smul, h1, h2]

theorem nullTTProject_isLorentzTT (m l : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) (hm0 : minkowskiDot m m = 0)
    (hml : minkowskiDot m l ≠ 0) :
    IsLorentzTT m (nullTTProject m l H) :=
  ⟨nullTTProject_symmetric m l H hH, nullTTProject_traceless m l H hml,
    nullTTProject_transverse_m m l H hm0 hml⟩

/-- **THEOREM (null Lorentzian algebraic `edge_tt_decomposition`).**
Explicit residual identity against a null wave covector with auxiliary null
partner: TT + m-gauge + l-gauge − bilinear + screen-trace part. -/
theorem exists_nullLorentzTTDecomposition (m l : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) (hm0 : minkowskiDot m m = 0)
    (hl0 : minkowskiDot l l = 0) (hml : minkowskiDot m l ≠ 0) :
    H =
        nullTTProject m l H +
          gaugePart m (nullMGaugeVector m l H) +
          gaugePart l (nullLGaugeVector m l H) -
          nullBilinear m l H +
          nullTraceCoeff m l H • nullProjector m l ∧
      IsLorentzTT m (nullTTProject m l H) ∧
      IsLorentzTransverse l (nullTTProject m l H) := by
  refine ⟨?_, nullTTProject_isLorentzTT m l H hH hm0 hml,
    nullTTProject_transverse_l m l H hl0 hml⟩
  have hgap := null_gap_expansion m l H hH hml
  -- H = PHP + (gauge_m + gauge_l - bilinear)
  --   = TT + trCoeff • P + (gauge_m + gauge_l - bilinear)
  calc
    H = nullPhp m l H + nullGap m l H := hgap
    _ = nullPhp m l H +
          (gaugePart m (nullMGaugeVector m l H) +
            gaugePart l (nullLGaugeVector m l H) -
            nullBilinear m l H) := by
      rfl
    _ = (nullPhp m l H - nullTraceCoeff m l H • nullProjector m l) +
          gaugePart m (nullMGaugeVector m l H) +
          gaugePart l (nullLGaugeVector m l H) -
          nullBilinear m l H +
          nullTraceCoeff m l H • nullProjector m l := by
      abel
    _ = nullTTProject m l H +
          gaugePart m (nullMGaugeVector m l H) +
          gaugePart l (nullLGaugeVector m l H) -
          nullBilinear m l H +
          nullTraceCoeff m l H • nullProjector m l := by
      rfl

/-! ## §4. Axis null witness: two independent TT polarizations -/

def nullAxisWave : Fin 4 → ℝ := vec4 1 1 0 0
def nullAxisAux : Fin 4 → ℝ := vec4 1 (-1) 0 0

theorem nullAxisWave_dot : minkowskiDot nullAxisWave nullAxisWave = 0 := by
  unfold minkowskiDot nullAxisWave; simp [vec4]

theorem nullAxisAux_dot : minkowskiDot nullAxisAux nullAxisAux = 0 := by
  unfold minkowskiDot nullAxisAux; simp [vec4]

theorem nullAxis_cross_dot : minkowskiDot nullAxisWave nullAxisAux = -2 := by
  unfold minkowskiDot nullAxisWave nullAxisAux; simp [vec4]; norm_num

theorem nullAxisWave_ne_zero : nullAxisWave ≠ 0 := by
  intro h
  have := congrArg (fun v : Fin 4 → ℝ => v 0) h
  simp [nullAxisWave, vec4] at this

theorem nullAxis_MinkowskiNull :
    MinkowskiNull nullAxisWave :=
  (minkowskiDot_eq_MinkowskiNull nullAxisWave).mp nullAxisWave_dot

/-- Plus polarization `diag(0,0,1,−1)` (unnormalized). -/
def nullAxisTTPlus : Mat4
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0
  | 1, 0 => 0 | 1, 1 => 0 | 1, 2 => 0 | 1, 3 => 0
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 1 | 2, 3 => 0
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => 0 | 3, 3 => -1

/-- Cross polarization `H₂₃ = H₃₂ = 1` (unnormalized). -/
def nullAxisTTCross : Mat4
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0
  | 1, 0 => 0 | 1, 1 => 0 | 1, 2 => 0 | 1, 3 => 0
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 0 | 2, 3 => 1
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => 1 | 3, 3 => 0

theorem nullAxisTTPlus_isLorentzTT :
    IsLorentzTT nullAxisWave nullAxisTTPlus := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> rfl
  · unfold IsLorentzTraceless minkowskiTrace nullAxisTTPlus; norm_num
  · intro i
    fin_cases i <;> simp [nullAxisTTPlus, nullAxisWave, vec4]

theorem nullAxisTTCross_isLorentzTT :
    IsLorentzTT nullAxisWave nullAxisTTCross := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> rfl
  · unfold IsLorentzTraceless minkowskiTrace nullAxisTTCross; norm_num
  · intro i
    fin_cases i <;> simp [nullAxisTTCross, nullAxisWave, vec4]

theorem nullAxisTTPlus_ne_zero : nullAxisTTPlus ≠ 0 := by
  intro h
  have := congrArg (fun M : Mat4 => M 2 2) h
  simp [nullAxisTTPlus] at this

theorem nullAxisTTCross_ne_zero : nullAxisTTCross ≠ 0 := by
  intro h
  have := congrArg (fun M : Mat4 => M 2 3) h
  simp [nullAxisTTCross] at this

theorem nullAxisTT_independent {a b : ℝ}
    (h : a • nullAxisTTPlus + b • nullAxisTTCross = 0) :
    a = 0 ∧ b = 0 := by
  have h22 := congrArg (fun M : Mat4 => M 2 2) h
  have h23 := congrArg (fun M : Mat4 => M 2 3) h
  simp [nullAxisTTPlus, nullAxisTTCross, smul_eq_mul] at h22 h23
  exact ⟨h22, h23⟩

/-! ## §5. Decoys: Euclidean projector fails on the null cone; zero degeneracy -/

/-- Euclidean momentum squared (for the decoy comparison only). -/
def euclideanMomentumSq (m : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, m i * m i

def euclideanTransverseProjector (m : Fin 4 → ℝ) : Mat4 :=
  (1 : Mat4) - (euclideanMomentumSq m)⁻¹ • outerSq m

theorem nullAxis_euclideanMomentumSq :
    euclideanMomentumSq nullAxisWave = 2 := by
  unfold euclideanMomentumSq nullAxisWave
  simp [Fin.sum_univ_four, vec4]; norm_num

theorem lorentzLoad_one (m : Fin 4 → ℝ) (i : Fin 4) :
    lorentzLoad (1 : Mat4) m i = raise m i := by
  unfold lorentzLoad
  simp only [one_apply]
  rw [Finset.sum_eq_single (a := i)]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · intro hi; exact (hi (Finset.mem_univ i)).elim

/-- The Euclidean projector is defined on the null axis (`‖m‖²_E = 2 ≠ 0`),
but it is **not** Lorentz-transverse to that null wave covector. -/
theorem euclideanProjector_not_lorentzTransverse_on_nullAxis :
    ¬ IsLorentzTransverse nullAxisWave
        (euclideanTransverseProjector nullAxisWave) := by
  intro h
  have hL := (IsLorentzTransverse_iff_lorentzLoad _ _).mp h 0
  have key :
      lorentzLoad (euclideanTransverseProjector nullAxisWave) nullAxisWave 0 =
        raise nullAxisWave 0 := by
    unfold euclideanTransverseProjector
    rw [lorentzLoad_sub, lorentzLoad_one, lorentzLoad_smul, lorentzLoad_outerSq,
      nullAxisWave_dot]
    simp [raise, nullAxisWave, vec4]
  rw [key] at hL
  simp [raise, nullAxisWave, vec4] at hL

/-- Naive non-null Lorentz projector hypothesis fails on the null cone. -/
theorem naive_lorentz_projector_hypothesis_fails_on_nullAxis :
    ¬ (minkowskiDot nullAxisWave nullAxisWave ≠ 0) := by
  simp [nullAxisWave_dot]

theorem zero_wave_minkowskiDot :
    minkowskiDot (fun _ : Fin 4 => (0 : ℝ)) (fun _ => 0) = 0 := by
  unfold minkowskiDot; simp

theorem decomposition_hypothesis_fails_at_zero :
    ¬ (minkowskiDot (fun _ : Fin 4 => (0 : ℝ)) (fun _ => 0) ≠ 0) := by
  simp [zero_wave_minkowskiDot]

end

end EdgeTTDecompositionLorentz4D
end Analysis
end Gravity
end IndisputableMonolith
