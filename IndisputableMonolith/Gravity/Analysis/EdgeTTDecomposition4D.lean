import Mathlib

/-!
# Edge TT decomposition (4D), algebraic layer

QG full-theory campaign, Wave 4 / lane W4-1 (`edge_tt_decomposition`),
smallest kernel-checked increment: the **linear-algebra** transverse-traceless
decomposition of symmetric `4 × 4` real matrices against a nonzero Euclidean
wave covector on `Fin 4`.

## Tier tags (binding)

* THEOREM: every named result in this file (kernel-checked; no `sorry`, no
  `admit`, no new axioms, no `native_decide`, no `: True` shells).
* This is the algebraic layer of the ledger closing name
  `edge_tt_decomposition`.  It does **not** decompose Regge EDGE
  perturbations on a 4D lattice, does **not** prove `S_RS_converges_EH_4d`,
  and does **not** flip `gap_action_recovery`.

## Conventions (inherited from 3D `IsTTPolarization`)

The 3D closer chain uses Euclidean trace, Euclidean transversality, and
symmetry.  This module lifts those three conjuncts to `Fin 4` (no Frobenius
pin).  Minkowski/null specialization for the Lorentzian continuum is
deferred; "two polarizations in 4D" is an explicit independent TT pair on
the axis wave vector (unnormalized integer entries).

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace EdgeTTDecomposition4D

open Matrix BigOperators

noncomputable section

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

def IsSymmetric (H : Mat4) : Prop :=
  ∀ i j : Fin 4, H i j = H j i

def euclideanTrace (H : Mat4) : ℝ :=
  ∑ i : Fin 4, H i i

def IsTraceless (H : Mat4) : Prop :=
  euclideanTrace H = 0

def IsTransverse (m : Fin 4 → ℝ) (H : Mat4) : Prop :=
  ∀ i : Fin 4, ∑ j : Fin 4, H i j * m j = 0

/-- Algebraic TT: symmetric, Euclidean-traceless, transverse. -/
def IsTT (m : Fin 4 → ℝ) (H : Mat4) : Prop :=
  IsSymmetric H ∧ IsTraceless H ∧ IsTransverse m H

def momentumSq (m : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, m i * m i

def gaugePart (m v : Fin 4 → ℝ) : Mat4 :=
  fun i j => m i * v j + v i * m j

def outerSq (m : Fin 4 → ℝ) : Mat4 :=
  fun i j => m i * m j

def transverseProjector (m : Fin 4 → ℝ) : Mat4 :=
  (1 : Mat4) - (momentumSq m)⁻¹ • outerSq m

def load (H : Mat4) (m : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => ∑ j : Fin 4, H i j * m j

def dot (a b : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, a i * b i

def gaugeVector (m : Fin 4 → ℝ) (H : Mat4) : Fin 4 → ℝ :=
  fun i =>
    let w := load H m
    let s := momentumSq m
    w i / s - m i * dot w m / (2 * s ^ 2)

def gaugeCorrected (m : Fin 4 → ℝ) (H : Mat4) : Mat4 :=
  H - gaugePart m (gaugeVector m H)

def residualTrace (m : Fin 4 → ℝ) (H : Mat4) : ℝ :=
  euclideanTrace (gaugeCorrected m H) / 3

def ttProject (m : Fin 4 → ℝ) (H : Mat4) : Mat4 :=
  gaugeCorrected m H - residualTrace m H • transverseProjector m

/-! ## §1. Elementary identities -/

theorem gaugePart_symmetric (m v : Fin 4 → ℝ) :
    IsSymmetric (gaugePart m v) := by
  intro i j; unfold gaugePart; ring

theorem outerSq_symmetric (m : Fin 4 → ℝ) :
    IsSymmetric (outerSq m) := by
  intro i j; unfold outerSq; ring

theorem transverseProjector_symmetric (m : Fin 4 → ℝ) :
    IsSymmetric (transverseProjector m) := by
  intro i j
  unfold transverseProjector
  simp only [sub_apply, smul_apply, smul_eq_mul, one_apply]
  rw [outerSq_symmetric m i j]
  cases' eq_or_ne i j with hij hij
  · subst hij; rfl
  · rw [if_neg hij, if_neg (Ne.symm hij)]

theorem load_gaugePart (m v : Fin 4 → ℝ) (i : Fin 4) :
    load (gaugePart m v) m i =
      momentumSq m * v i + m i * dot v m := by
  unfold load gaugePart momentumSq dot
  calc
    ∑ j : Fin 4, (m i * v j + v i * m j) * m j
        = ∑ j : Fin 4, (m i * (v j * m j) + v i * (m j * m j)) := by
      refine Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ j : Fin 4, m i * (v j * m j)) +
          (∑ j : Fin 4, v i * (m j * m j)) := Finset.sum_add_distrib
    _ = m i * ∑ j : Fin 4, v j * m j + v i * ∑ j : Fin 4, m j * m j := by
      simp [Finset.mul_sum]
    _ = (∑ j : Fin 4, m j * m j) * v i + m i * ∑ j : Fin 4, v j * m j := by
      ring

theorem load_smul (c : ℝ) (H : Mat4) (m : Fin 4 → ℝ) (i : Fin 4) :
    load (c • H) m i = c * load H m i := by
  unfold load
  simp only [smul_apply, smul_eq_mul, mul_assoc]
  exact (Finset.mul_sum Finset.univ (fun j => H i j * m j) c).symm

theorem load_sub (A B : Mat4) (m : Fin 4 → ℝ) (i : Fin 4) :
    load (A - B) m i = load A m i - load B m i := by
  unfold load; simp [sub_mul, Finset.sum_sub_distrib]

theorem load_one (m : Fin 4 → ℝ) (i : Fin 4) :
    load (1 : Mat4) m i = m i := by
  unfold load
  simp only [one_apply]
  rw [Finset.sum_eq_single (a := i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem load_outerSq (m : Fin 4 → ℝ) (i : Fin 4) :
    load (outerSq m) m i = momentumSq m * m i := by
  unfold load outerSq momentumSq
  calc
    ∑ j : Fin 4, (m i * m j) * m j
        = m i * ∑ j : Fin 4, m j * m j := by
      simp [mul_assoc, Finset.mul_sum]
    _ = (∑ j : Fin 4, m j * m j) * m i := by ring

theorem load_transverseProjector (m : Fin 4 → ℝ) (hm : momentumSq m ≠ 0)
    (i : Fin 4) :
    load (transverseProjector m) m i = 0 := by
  unfold transverseProjector
  rw [load_sub, load_one, load_smul, load_outerSq]
  field_simp [hm]; ring

/-! ## §2. Gauge removal -/

theorem dot_gaugeVector (m : Fin 4 → ℝ) (H : Mat4)
    (hm : momentumSq m ≠ 0) :
    dot (gaugeVector m H) m = dot (load H m) m / (2 * momentumSq m) := by
  set w := load H m with hw
  set s := momentumSq m with hs
  have hs0 : s ≠ 0 := hm
  set d := dot w m with hd
  -- expand
  have hexpand :
      dot (gaugeVector m H) m =
        ∑ i : Fin 4, (w i / s - m i * d / (2 * s ^ 2)) * m i := by
    simp [dot, gaugeVector, w, s, d]
  have hsplit :
      ∑ i : Fin 4, (w i / s - m i * d / (2 * s ^ 2)) * m i =
        ∑ i : Fin 4, (w i / s) * m i -
          ∑ i : Fin 4, (m i * d / (2 * s ^ 2)) * m i := by
    simp [sub_mul, Finset.sum_sub_distrib]
  have h1 : ∑ i : Fin 4, (w i / s) * m i = d / s := by
    simp only [d, dot, div_eq_mul_inv, mul_assoc]
    -- ∑ (s⁻¹ * wᵢ) * mᵢ = s⁻¹ * ∑ wᵢ mᵢ
    have :
        ∑ i : Fin 4, s⁻¹ * w i * m i = s⁻¹ * ∑ i : Fin 4, w i * m i := by
      simp [mul_assoc, ← Finset.mul_sum]
    convert this using 1
    · refine Finset.sum_congr rfl fun i _ => by ring
    · ring
  have h2 : ∑ i : Fin 4, (m i * d / (2 * s ^ 2)) * m i = s * d / (2 * s ^ 2) := by
    have :
        ∑ i : Fin 4, m i * m i * (d / (2 * s ^ 2)) =
          (∑ i : Fin 4, m i * m i) * (d / (2 * s ^ 2)) :=
      (Finset.sum_mul _ _ _).symm
    calc
      ∑ i : Fin 4, (m i * d / (2 * s ^ 2)) * m i
          = ∑ i : Fin 4, m i * m i * (d / (2 * s ^ 2)) := by
        refine Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i : Fin 4, m i * m i) * (d / (2 * s ^ 2)) := this
      _ = s * d / (2 * s ^ 2) := by
        simp [s, momentumSq]; ring
  calc
    dot (gaugeVector m H) m
        = ∑ i : Fin 4, (w i / s - m i * d / (2 * s ^ 2)) * m i := hexpand
    _ = d / s - s * d / (2 * s ^ 2) := by rw [hsplit, h1, h2]
    _ = d / (2 * s) := by field_simp [hs0]; ring
    _ = dot (load H m) m / (2 * momentumSq m) := by
        simp [d, w, s]

theorem load_gaugePart_gaugeVector (m : Fin 4 → ℝ) (H : Mat4)
    (hm : momentumSq m ≠ 0) (i : Fin 4) :
    load (gaugePart m (gaugeVector m H)) m i = load H m i := by
  set w := load H m
  set s := momentumSq m
  set v := gaugeVector m H
  have hs0 : s ≠ 0 := hm
  have hL := load_gaugePart m v i
  have hdot := dot_gaugeVector m H hm
  have hvi : v i = w i / s - m i * dot w m / (2 * s ^ 2) := rfl
  have key : s * v i + m i * dot v m = w i := by
    rw [hvi, show dot v m = dot w m / (2 * s) from hdot]
    field_simp [hs0]; ring
  rw [hL]; simpa [s, w, v] using key

theorem gaugeCorrected_transverse (m : Fin 4 → ℝ) (H : Mat4)
    (hm : momentumSq m ≠ 0) :
    IsTransverse m (gaugeCorrected m H) := by
  intro i
  change load (gaugeCorrected m H) m i = 0
  simp [gaugeCorrected, load_sub, load_gaugePart_gaugeVector m H hm]

theorem gaugeCorrected_symmetric (m : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) :
    IsSymmetric (gaugeCorrected m H) := by
  intro i j
  simp only [gaugeCorrected, sub_apply]
  rw [hH i j, gaugePart_symmetric m (gaugeVector m H) i j]

/-! ## §3. TT projection -/

theorem euclideanTrace_smul (c : ℝ) (H : Mat4) :
    euclideanTrace (c • H) = c * euclideanTrace H := by
  unfold euclideanTrace
  simp only [smul_apply, smul_eq_mul]
  exact (Finset.mul_sum Finset.univ (fun i => H i i) c).symm

theorem euclideanTrace_sub (A B : Mat4) :
    euclideanTrace (A - B) = euclideanTrace A - euclideanTrace B := by
  unfold euclideanTrace; simp [Finset.sum_sub_distrib]

theorem euclideanTrace_one : euclideanTrace (1 : Mat4) = 4 := by
  unfold euclideanTrace
  rw [Fin.sum_univ_four]
  simp
  norm_num

theorem euclideanTrace_outerSq (m : Fin 4 → ℝ) :
    euclideanTrace (outerSq m) = momentumSq m := rfl

theorem euclideanTrace_transverseProjector (m : Fin 4 → ℝ)
    (hm : momentumSq m ≠ 0) :
    euclideanTrace (transverseProjector m) = 3 := by
  unfold transverseProjector
  rw [euclideanTrace_sub, euclideanTrace_smul, euclideanTrace_one,
    euclideanTrace_outerSq]
  field_simp [hm]; ring

theorem ttProject_symmetric (m : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) :
    IsSymmetric (ttProject m H) := by
  intro i j
  simp only [ttProject, sub_apply, smul_apply, smul_eq_mul]
  rw [gaugeCorrected_symmetric m H hH i j,
    transverseProjector_symmetric m i j]

theorem ttProject_transverse (m : Fin 4 → ℝ) (H : Mat4)
    (hm : momentumSq m ≠ 0) :
    IsTransverse m (ttProject m H) := by
  intro i
  change load (ttProject m H) m i = 0
  have h1 : load (gaugeCorrected m H) m i = 0 :=
    gaugeCorrected_transverse m H hm i
  have h2 := load_transverseProjector m hm i
  simp [ttProject, load_sub, load_smul, h1, h2]

theorem ttProject_traceless (m : Fin 4 → ℝ) (H : Mat4)
    (hm : momentumSq m ≠ 0) :
    IsTraceless (ttProject m H) := by
  unfold IsTraceless ttProject residualTrace
  rw [euclideanTrace_sub, euclideanTrace_smul,
    euclideanTrace_transverseProjector m hm]
  ring

theorem ttProject_isTT (m : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) (hm : momentumSq m ≠ 0) :
    IsTT m (ttProject m H) :=
  ⟨ttProject_symmetric m H hH, ttProject_traceless m H hm,
    ttProject_transverse m H hm⟩

/-- **THEOREM (algebraic `edge_tt_decomposition` layer).**
Every symmetric `4 × 4` matrix against a nonzero Euclidean wave covector
decomposes as TT + gauge + transverse-trace part. -/
theorem exists_edgeTTDecomposition (m : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) (hm : momentumSq m ≠ 0) :
    H = ttProject m H + gaugePart m (gaugeVector m H) +
        residualTrace m H • transverseProjector m ∧
      IsTT m (ttProject m H) := by
  refine ⟨?_, ttProject_isTT m H hH hm⟩
  unfold ttProject gaugeCorrected; abel

theorem exists_edgeTTDecomposition' (m : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) (hm : momentumSq m ≠ 0) :
    ∃ (H_TT : Mat4) (v : Fin 4 → ℝ) (β : ℝ),
      H = H_TT + gaugePart m v + β • transverseProjector m ∧
        IsTT m H_TT :=
  ⟨ttProject m H, gaugeVector m H, residualTrace m H,
    exists_edgeTTDecomposition m H hH hm⟩

/-! ## §4. Nondegeneracy: two independent unnormalized TT polarizations -/

def axisWave : Fin 4 → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 0

theorem axisWave_momentumSq : momentumSq axisWave = 1 := by
  unfold momentumSq axisWave
  simp [Fin.sum_univ_four]

/-- Plus polarization `diag(0,0,1,−1)` (unnormalized). -/
def axisTTPlus : Mat4
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0
  | 1, 0 => 0 | 1, 1 => 0 | 1, 2 => 0 | 1, 3 => 0
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 1 | 2, 3 => 0
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => 0 | 3, 3 => -1

/-- Cross polarization `H₂₃ = H₃₂ = 1` (unnormalized). -/
def axisTTCross : Mat4
  | 0, 0 => 0 | 0, 1 => 0 | 0, 2 => 0 | 0, 3 => 0
  | 1, 0 => 0 | 1, 1 => 0 | 1, 2 => 0 | 1, 3 => 0
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 0 | 2, 3 => 1
  | 3, 0 => 0 | 3, 1 => 0 | 3, 2 => 1 | 3, 3 => 0

theorem axisTTPlus_isTT : IsTT axisWave axisTTPlus := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> rfl
  · unfold IsTraceless euclideanTrace axisTTPlus
    simp [Fin.sum_univ_four]
  · intro i
    fin_cases i <;> simp [axisTTPlus, axisWave, Fin.sum_univ_four]

theorem axisTTCross_isTT : IsTT axisWave axisTTCross := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> rfl
  · unfold IsTraceless euclideanTrace axisTTCross
    simp [Fin.sum_univ_four]
  · intro i
    fin_cases i <;> simp [axisTTCross, axisWave, Fin.sum_univ_four]

theorem axisTTPlus_ne_zero : axisTTPlus ≠ 0 := by
  intro h
  have := congrArg (fun M : Mat4 => M 2 2) h
  simp [axisTTPlus] at this

theorem axisTTCross_ne_zero : axisTTCross ≠ 0 := by
  intro h
  have := congrArg (fun M : Mat4 => M 2 3) h
  simp [axisTTCross] at this

theorem axisTT_independent {a b : ℝ}
    (h : a • axisTTPlus + b • axisTTCross = 0) :
    a = 0 ∧ b = 0 := by
  have h22 := congrArg (fun M : Mat4 => M 2 2) h
  have h23 := congrArg (fun M : Mat4 => M 2 3) h
  simp [axisTTPlus, axisTTCross, smul_eq_mul] at h22 h23
  exact ⟨h22, h23⟩

/-! ## §5. Decoy and zero-momentum degeneracy -/

def decoyLongitudinal : Mat4 :=
  gaugePart axisWave fun i => if i = 0 then (1 : ℝ) else 0

theorem decoyLongitudinal_symmetric : IsSymmetric decoyLongitudinal :=
  gaugePart_symmetric _ _

theorem decoyLongitudinal_not_transverse :
    ¬ IsTransverse axisWave decoyLongitudinal := by
  intro h
  have h0 := h 0
  simp [decoyLongitudinal, gaugePart, axisWave, Fin.sum_univ_four] at h0

theorem decoy_ttProject_isTT :
    IsTT axisWave (ttProject axisWave decoyLongitudinal) :=
  ttProject_isTT axisWave decoyLongitudinal decoyLongitudinal_symmetric
    (by simp [axisWave_momentumSq])

theorem decoy_projection_restores_transverse :
    IsTransverse axisWave (ttProject axisWave decoyLongitudinal) :=
  decoy_ttProject_isTT.2.2

theorem zero_wave_momentumSq :
    momentumSq (fun _ : Fin 4 => (0 : ℝ)) = 0 := by
  unfold momentumSq; simp

theorem decomposition_hypothesis_fails_at_zero :
    ¬ (momentumSq (fun _ : Fin 4 => (0 : ℝ)) ≠ 0) := by
  simp [zero_wave_momentumSq]

end

end EdgeTTDecomposition4D
end Analysis
end Gravity
end IndisputableMonolith
