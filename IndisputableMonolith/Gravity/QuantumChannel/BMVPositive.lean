import Mathlib
import IndisputableMonolith.Gravity.LedgerSuperposition

/-!
# Gravity IV: BMV-Positive Sign (Theorem 3)

This module formalizes the third load-bearing theorem of *Gravity from
Recognition IV: The Quantum Channel*: in the BMV two-mass two-branch
protocol, the linear cost-gradient channel of
`Gravity.LedgerSuperposition` produces a branch-dependent gravitational
phase whose entangling combination `Δφ` is generically nonzero, yielding
a non-product joint state and (equivalently, for pure two-qubit states)
strictly positive entanglement entropy outside a discrete set of revival
times.

We package the algebraic content of T3 explicitly. The two test masses
each have a Left/Right branch index, giving four definite branch states
`{LL, LR, RL, RR}`. After the gravitational interaction, the joint state
acquires a per-branch phase `φ_ab`, and the joint state is a product
state if and only if the entangling combination
`Δφ = φ_LL + φ_RR - φ_LR - φ_RL` is congruent to `0 mod 2π` (equivalently,
the `2×2` amplitude matrix has determinant zero). For non-degenerate BMV
geometry, `Δφ ≠ 0 mod 2π` for every `T ∈ (0, T_rev)`, so the joint
amplitude matrix has nonzero determinant and the joint state is
entangled.

## What is proved here

* `branchAmplitudeMatrix`, `branchPhaseInvariant`: explicit definitions.
* `det_branchAmplitude` : the `2×2` determinant of the branch amplitude
  matrix is `(1/4) (e^{-i(φ_LL+φ_RR)} - e^{-i(φ_LR+φ_RL)})`.
* `det_nonzero_iff_branchPhase_nonzero` : the determinant is zero if and
  only if the entangling combination is `0 mod 2π`.
* `entangled_of_branchPhaseNonzero` : the algebraic entanglement
  witness — the joint state is non-product whenever `Δφ ≠ 0 mod 2π`.
* `branchPhase_weakField` : in the weak-field regime the entangling
  invariant is `(G m₁ m₂ T / ℏ) · (1/r_LL + 1/r_RR − 1/r_LR − 1/r_RL)`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace QuantumChannel
namespace BMVPositive

open Complex

noncomputable section

/-! ## The BMV branch-amplitude matrix -/

/-- The `2×2` complex amplitude matrix of the post-interaction joint
state in the BMV protocol. The four entries are the per-branch
phase factors `e^{-i φ_ab}` for `(a, b) ∈ {LL, LR, RL, RR}`,
multiplied by the prefactor `1/2` from the initial product
`((|L⟩ + |R⟩)/√2) ⊗ ((|L⟩ + |R⟩)/√2)`. -/
def branchAmplitudeMatrix
    (φ_LL φ_LR φ_RL φ_RR : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    (1 / 2 : ℂ) *
      Complex.exp
        (-Complex.I *
          (match i, j with
            | 0, 0 => (φ_LL : ℂ)
            | 0, 1 => (φ_LR : ℂ)
            | 1, 0 => (φ_RL : ℂ)
            | 1, 1 => (φ_RR : ℂ)))

/-- The entangling invariant `Δφ = φ_LL + φ_RR − φ_LR − φ_RL`. -/
def branchPhaseInvariant (φ_LL φ_LR φ_RL φ_RR : ℝ) : ℝ :=
  φ_LL + φ_RR - φ_LR - φ_RL

/-! ## The determinant of the branch amplitude matrix -/

/-- The determinant of the `2×2` BMV amplitude matrix is
`(1/4)·(e^{-i(φ_LL+φ_RR)} − e^{-i(φ_LR+φ_RL)})`. -/
theorem det_branchAmplitude (φ_LL φ_LR φ_RL φ_RR : ℝ) :
    Matrix.det (branchAmplitudeMatrix φ_LL φ_LR φ_RL φ_RR)
      = (1 / 4 : ℂ) *
        (Complex.exp (-Complex.I * ((φ_LL : ℂ) + (φ_RR : ℂ))) -
         Complex.exp (-Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ)))) := by
  unfold branchAmplitudeMatrix
  rw [Matrix.det_fin_two]
  simp only []
  -- det = M(0,0) M(1,1) − M(0,1) M(1,0)
  -- = (1/2 e^{-i φ_LL})(1/2 e^{-i φ_RR}) − (1/2 e^{-i φ_LR})(1/2 e^{-i φ_RL})
  -- = (1/4) (e^{-i (φ_LL+φ_RR)} − e^{-i (φ_LR+φ_RL)})
  have h00 : (-Complex.I) * (φ_LL : ℂ) + -Complex.I * (φ_RR : ℂ)
              = -Complex.I * ((φ_LL : ℂ) + (φ_RR : ℂ)) := by ring
  have h01 : (-Complex.I) * (φ_LR : ℂ) + -Complex.I * (φ_RL : ℂ)
              = -Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ)) := by ring
  rw [show (((1:ℂ) / 2) * Complex.exp (-Complex.I * (φ_LL : ℂ))) *
            (((1:ℂ) / 2) * Complex.exp (-Complex.I * (φ_RR : ℂ)))
        = ((1:ℂ) / 4) *
          (Complex.exp (-Complex.I * (φ_LL : ℂ)) *
           Complex.exp (-Complex.I * (φ_RR : ℂ))) by ring,
      show (((1:ℂ) / 2) * Complex.exp (-Complex.I * (φ_LR : ℂ))) *
            (((1:ℂ) / 2) * Complex.exp (-Complex.I * (φ_RL : ℂ)))
        = ((1:ℂ) / 4) *
          (Complex.exp (-Complex.I * (φ_LR : ℂ)) *
           Complex.exp (-Complex.I * (φ_RL : ℂ))) by ring,
      ← Complex.exp_add, ← Complex.exp_add, h00, h01]
  ring

/-! ## When is the determinant zero?

The complex exponential `e^{-i x}` is invariant under translations of
`x` by `2π`, so the BMV amplitude matrix has zero determinant iff
`(φ_LL + φ_RR) − (φ_LR + φ_RL) ≡ 0 mod 2π`.

We give the algebraic content directly: the determinant equals
`(1/4) e^{-i (φ_LR+φ_RL)} (e^{-i Δφ} − 1)`, so it is zero iff
`e^{-i Δφ} = 1`, iff `Δφ ∈ 2π ℤ`.
-/

/-- The branch determinant factored through the entangling invariant
`Δφ`. -/
theorem det_branchAmplitude_factored
    (φ_LL φ_LR φ_RL φ_RR : ℝ) :
    Matrix.det (branchAmplitudeMatrix φ_LL φ_LR φ_RL φ_RR)
      = (1 / 4 : ℂ) *
        Complex.exp (-Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ))) *
        (Complex.exp
           (-Complex.I * (branchPhaseInvariant φ_LL φ_LR φ_RL φ_RR : ℂ))
           - 1) := by
  rw [det_branchAmplitude]
  unfold branchPhaseInvariant
  -- e^{-i (φ_LL + φ_RR)} − e^{-i (φ_LR + φ_RL)}
  -- = e^{-i (φ_LR + φ_RL)} · (e^{-i ((φ_LL + φ_RR) − (φ_LR + φ_RL))} − 1)
  have hpush :
      Complex.exp (-Complex.I * ((φ_LL : ℂ) + (φ_RR : ℂ)))
          - Complex.exp (-Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ)))
        = Complex.exp (-Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ))) *
            (Complex.exp
              (-Complex.I *
                (((φ_LL : ℂ) + (φ_RR : ℂ)) -
                 ((φ_LR : ℂ) + (φ_RL : ℂ)))) - 1) := by
    have hsum :
        -Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ))
          + (-Complex.I *
              (((φ_LL : ℂ) + (φ_RR : ℂ)) -
               ((φ_LR : ℂ) + (φ_RL : ℂ))))
          = -Complex.I * ((φ_LL : ℂ) + (φ_RR : ℂ)) := by ring
    calc
      Complex.exp (-Complex.I * ((φ_LL : ℂ) + (φ_RR : ℂ)))
            - Complex.exp (-Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ)))
          = Complex.exp
              (-Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ))
               + (-Complex.I *
                   (((φ_LL : ℂ) + (φ_RR : ℂ)) -
                    ((φ_LR : ℂ) + (φ_RL : ℂ)))))
            - Complex.exp (-Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ))) := by
                rw [hsum]
      _ = Complex.exp (-Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ))) *
            Complex.exp
              (-Complex.I *
                (((φ_LL : ℂ) + (φ_RR : ℂ)) -
                 ((φ_LR : ℂ) + (φ_RL : ℂ))))
            - Complex.exp (-Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ))) := by
                rw [Complex.exp_add]
      _ = Complex.exp (-Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ))) *
            (Complex.exp
              (-Complex.I *
                (((φ_LL : ℂ) + (φ_RR : ℂ)) -
                 ((φ_LR : ℂ) + (φ_RL : ℂ)))) - 1) := by ring
  have hcast :
      ((φ_LL + φ_RR - φ_LR - φ_RL : ℝ) : ℂ)
        = ((φ_LL : ℂ) + (φ_RR : ℂ)) - ((φ_LR : ℂ) + (φ_RL : ℂ)) := by
    push_cast
    ring
  rw [hpush, hcast]
  ring

/-- The branch amplitude determinant is nonzero iff the entangling
invariant `Δφ` is not in `2π ℤ`. -/
theorem det_ne_zero_iff_branchPhase_ne_zero
    (φ_LL φ_LR φ_RL φ_RR : ℝ) :
    Matrix.det (branchAmplitudeMatrix φ_LL φ_LR φ_RL φ_RR) ≠ 0
      ↔ Complex.exp
          (-Complex.I * (branchPhaseInvariant φ_LL φ_LR φ_RL φ_RR : ℂ)) ≠ 1 := by
  rw [det_branchAmplitude_factored]
  have h14 : ((1 : ℂ) / 4) ≠ 0 := by norm_num
  have hexp_pos : Complex.exp (-Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ))) ≠ 0 :=
    Complex.exp_ne_zero _
  constructor
  · intro hdet hphase
    apply hdet
    rw [show
          Complex.exp
              (-Complex.I * (branchPhaseInvariant φ_LL φ_LR φ_RL φ_RR : ℂ)) - 1 = 0 by
            rw [hphase]; ring]
    ring
  · intro hphase hprod
    apply hphase
    -- (1/4) · e^{-i(...)} · (exp(...) - 1) = 0 with first two factors nonzero
    -- forces (exp(...) - 1) = 0.
    have habc :
        ((1 : ℂ) / 4) *
          Complex.exp (-Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ))) ≠ 0 :=
      mul_ne_zero h14 hexp_pos
    rcases mul_eq_zero.mp hprod with h | h
    · exact (habc h).elim
    · exact sub_eq_zero.mp h

/-- Algebraic entanglement witness: when the entangling invariant `Δφ`
is not in `2π ℤ`, the BMV branch amplitude matrix has nonzero
determinant, so the corresponding two-qubit pure state is not a product
state. -/
theorem entangled_of_branchPhase_nonzero
    (φ_LL φ_LR φ_RL φ_RR : ℝ)
    (h : Complex.exp
            (-Complex.I * (branchPhaseInvariant φ_LL φ_LR φ_RL φ_RR : ℂ)) ≠ 1) :
    Matrix.det (branchAmplitudeMatrix φ_LL φ_LR φ_RL φ_RR) ≠ 0 := by
  rw [det_ne_zero_iff_branchPhase_ne_zero]
  exact h

/-- A simple sufficient condition: for `Δφ ∈ ℝ` strictly between `0` and
`2π`, the corresponding complex exponential is not `1`, and therefore
the two-qubit state is entangled. This is the version used in the
paper's Theorem 3 (positivity of entanglement entropy on
`(0, T_rev)`). -/
theorem entangled_of_branchPhase_in_open_period
    (φ_LL φ_LR φ_RL φ_RR : ℝ)
    (hlo : 0 < branchPhaseInvariant φ_LL φ_LR φ_RL φ_RR)
    (hhi : branchPhaseInvariant φ_LL φ_LR φ_RL φ_RR < 2 * Real.pi) :
    Matrix.det (branchAmplitudeMatrix φ_LL φ_LR φ_RL φ_RR) ≠ 0 := by
  apply entangled_of_branchPhase_nonzero
  -- We use the Mathlib characterization Complex.exp_eq_one_iff:
  -- exp z = 1 ↔ ∃ n : ℤ, z = n * (2π i).
  intro hexp
  set x : ℝ := branchPhaseInvariant φ_LL φ_LR φ_RL φ_RR with hx
  rw [Complex.exp_eq_one_iff] at hexp
  obtain ⟨n, hn⟩ := hexp
  -- −i · x = n · (2π · i) ⟹ x = −n · 2π
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hxeq : (x : ℂ) = - (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    -- From: -i · x = n · (2π · i), multiply both sides by i:
    --   -i · x · i = n · (2π · i) · i,  i.e.  x = -n · 2π using i·i = -1.
    have h1 : -Complex.I * (x : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hn
    have h2 : (-Complex.I * (x : ℂ)) * Complex.I =
                ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I := by
      rw [h1]
    have hii : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hL : (-Complex.I * (x : ℂ)) * Complex.I = (x : ℂ) := by
      have : (-Complex.I * (x : ℂ)) * Complex.I
              = - (x : ℂ) * (Complex.I * Complex.I) := by ring
      rw [this, hii]; ring
    have hR : ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I
                = - (n : ℂ) * (2 * (Real.pi : ℂ)) := by
      have : ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I
              = (n : ℂ) * (2 * (Real.pi : ℂ)) * (Complex.I * Complex.I) := by ring
      rw [this, hii]; ring
    rw [← hL, h2, hR]
  have hxeqR : x = - (n : ℝ) * (2 * Real.pi) := by
    have := hxeq
    have : (x : ℂ) = ((- (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
      rw [hxeq]; push_cast; ring
    exact_mod_cast this
  -- Now 0 < x < 2π forces 0 < -n · 2π < 2π, i.e. -1 < -n < 1, i.e. n = 0.
  -- But then x = 0, contradicting 0 < x.
  have h2pi_pos : 0 < (2 : ℝ) * Real.pi := by
    have := Real.pi_pos
    linarith
  have hxpos : (0 : ℝ) < - (n : ℝ) * (2 * Real.pi) := by rw [← hxeqR]; exact hlo
  have hxlt : - (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by rw [← hxeqR]; exact hhi
  have hn_pos : (0 : ℝ) < - (n : ℝ) := by
    have := hxpos
    have h := (mul_pos_iff.mp this).resolve_right ?_
    · exact h.1
    · intro ⟨h1, h2⟩; linarith
  have hn_lt_one : - (n : ℝ) < 1 := by
    by_contra hge
    push_neg at hge
    have : (1 : ℝ) * (2 * Real.pi) ≤ - (n : ℝ) * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hge (le_of_lt h2pi_pos)
    linarith
  -- 0 < -n < 1 with n integer is impossible
  have hn_int_pos : 0 < (-n : ℤ) := by
    have hcast : ((-n : ℤ) : ℝ) = - (n : ℝ) := by push_cast; ring
    have := hn_pos
    rw [← hcast] at this
    exact_mod_cast this
  have hn_int_lt_one : (-n : ℤ) < 1 := by
    have hcast : ((-n : ℤ) : ℝ) = - (n : ℝ) := by push_cast; ring
    have := hn_lt_one
    rw [← hcast] at this
    exact_mod_cast this
  omega

/-! ## Weak-field BMV phase formula -/

/-- The weak-field gravitational interaction phase between mass-1 in
branch position `r_a` and mass-2 in branch position `r_b`, accumulated
over time `T`. -/
def weakFieldPhase (G hbar m1 m2 T r : ℝ) : ℝ :=
  G * m1 * m2 * T / (hbar * r)

/-- The weak-field entangling invariant `Δφ` evaluated for a BMV
configuration with the four branch separations `r_LL, r_LR, r_RL, r_RR`. -/
def weakFieldBranchInvariant
    (G hbar m1 m2 T r_LL r_LR r_RL r_RR : ℝ) : ℝ :=
  weakFieldPhase G hbar m1 m2 T r_LL +
    weakFieldPhase G hbar m1 m2 T r_RR -
    weakFieldPhase G hbar m1 m2 T r_LR -
    weakFieldPhase G hbar m1 m2 T r_RL

/-- Closed-form for the weak-field entangling invariant. -/
theorem weakFieldBranchInvariant_eq
    (G hbar m1 m2 T r_LL r_LR r_RL r_RR : ℝ)
    (hhbar : hbar ≠ 0)
    (hLL : r_LL ≠ 0) (hLR : r_LR ≠ 0)
    (hRL : r_RL ≠ 0) (hRR : r_RR ≠ 0) :
    weakFieldBranchInvariant G hbar m1 m2 T r_LL r_LR r_RL r_RR
      = (G * m1 * m2 * T / hbar) *
          (1 / r_LL + 1 / r_RR - 1 / r_LR - 1 / r_RL) := by
  unfold weakFieldBranchInvariant weakFieldPhase
  field_simp

/-! ## Master witness -/

/-- The complete content of T3: given the linear cost-gradient channel
of T2 and the weak-field BMV phase formula, the BMV branch state is
entangled whenever the entangling invariant `Δφ` lies in the open
interval `(0, 2π)`. The witness is `det A ≠ 0`. -/
structure BMVPositiveTheorem where
  /-- The amplitude-matrix determinant in closed form. -/
  det_formula :
    ∀ (φ_LL φ_LR φ_RL φ_RR : ℝ),
      Matrix.det (branchAmplitudeMatrix φ_LL φ_LR φ_RL φ_RR)
        = (1 / 4 : ℂ) *
            Complex.exp (-Complex.I * ((φ_LR : ℂ) + (φ_RL : ℂ))) *
            (Complex.exp
               (-Complex.I *
                 (branchPhaseInvariant φ_LL φ_LR φ_RL φ_RR : ℂ)) - 1)
  /-- Algebraic entanglement witness for `Δφ ∈ (0, 2π)`. -/
  entangled_open_period :
    ∀ (φ_LL φ_LR φ_RL φ_RR : ℝ),
      0 < branchPhaseInvariant φ_LL φ_LR φ_RL φ_RR →
      branchPhaseInvariant φ_LL φ_LR φ_RL φ_RR < 2 * Real.pi →
      Matrix.det (branchAmplitudeMatrix φ_LL φ_LR φ_RL φ_RR) ≠ 0
  /-- Weak-field formula for the entangling invariant. -/
  weakField_formula :
    ∀ (G hbar m1 m2 T r_LL r_LR r_RL r_RR : ℝ),
      hbar ≠ 0 →
      r_LL ≠ 0 → r_LR ≠ 0 → r_RL ≠ 0 → r_RR ≠ 0 →
      weakFieldBranchInvariant G hbar m1 m2 T r_LL r_LR r_RL r_RR
        = (G * m1 * m2 * T / hbar) *
            (1 / r_LL + 1 / r_RR - 1 / r_LR - 1 / r_RL)

/-- The canonical inhabitant of `BMVPositiveTheorem`. -/
def bmvPositiveTheorem : BMVPositiveTheorem where
  det_formula := det_branchAmplitude_factored
  entangled_open_period := entangled_of_branchPhase_in_open_period
  weakField_formula := weakFieldBranchInvariant_eq

theorem bmvPositiveTheorem_inhabited : Nonempty BMVPositiveTheorem :=
  ⟨bmvPositiveTheorem⟩

end

end BMVPositive
end QuantumChannel
end Gravity
end IndisputableMonolith
