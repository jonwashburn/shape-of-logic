import IndisputableMonolith.Gravity.Analysis.FreudenthalStencilPreflight
import IndisputableMonolith.Gravity.Analysis.SpectralConvergence

/-!
# Freudenthal energy limit: rated action-level limit on a sampled witness field

QG full-theory campaign, Phase 2b, panel-locked Test G stage 2 (candidate C8,
tensor-first anisotropic action continuum limit).

Scope statement (panel-mandated): this module and its stage-1 companion
(`FreudenthalStencilPreflight`) develop the action-level continuum limit of
the frozen quadratic energy on the canonical Freudenthal family; scoped
partial; the pillar-2 path-sum flag stays red (flipping it requires the
refinement-indexed measure-weighted sum over inequivalent triangulation
classes).

## Status: THEOREM (everything below is proved, axiom-clean; no sorry, no
## admit, no native_decide, no `: True` shells).

## What this module proves

For the FIXED nonconstant C² witness field `f(x,y,z) = sin(2πx)`
(`witnessField`), sampled onto the side-`N` canonical periodic Freudenthal
family (`sample`):

* `scaledCanonicalEnergy_witness_closed_form`: the `ρ(N)`-normalized
  canonical Regge-Hessian quadratic energy of the sampled field evaluates
  EXACTLY (for every `N > 2`) to
  `A₀[0,0] · 2N² sin²(π/N)` with `A₀[0,0] = 1 + 2√2 + √3` the stage-1
  moment-tensor entry. The trig evaluation is a telescoping identity
  (`sum_cos_shifted_vanishes`), not an estimate.
* `continuumTarget` (defined INDEPENDENTLY of the lattice computation):
  the by-hand continuum energy `∫_{[0,1]³} ⟨∇f, A₀ ∇f⟩ = A₀[0,0] · 2π²`.
  Since `⟨∇f(p), A₀ ∇f(p)⟩ = A₀[0,0] (2π cos(2πp₀))²` depends only on the
  first coordinate, the cube integral reduces by hand to the interval
  integral `∫₀¹ A₀[0,0] (2π cos(2πt))² dt`, which is evaluated IN LEAN
  (`integral_witness_energy_density`, via the closed-form antiderivative);
  the gradient component is justified in Lean by
  `witnessField_section_hasDerivAt`. `continuumTarget_pos`: the target is
  strictly positive (no `0 = 0` trap; `witnessField_nonconstant`).
* `scaledCanonicalEnergy_witness_rate` /
  `freudenthal_witness_energy_limit`: the panel-locked stage-2 observable
  `∃ C N₀, ∀ N ≥ N₀, |scaledCanonicalEnergy N (sample N f) − ∫⟨∇f, A₀∇f⟩| ≤ C/N`
  with the EXPLICIT constant `C = rateConstant = A₀[0,0]·(2π)⁴/24`,
  independent of `N` (`N₀ = 3`); the achieved rate is in fact `C/N²`
  (`witness_closed_form_dist`), consuming the Phase-2a toolkit bound
  `discrete_sine_eigenvalue_expansion` at wavenumber 1.
* `witness_closed_form_tendsto`: the qualitative limit, re-derived through
  the Phase-2a `eigenvalue_limit_of_uniform_bound` squeeze, verifying that
  the two toolkit pieces compose.

Anisotropy note (stage-1 finding, inherited): the continuum quadratic form
is `⟨∇f, A₀ ∇f⟩` with the ANISOTROPIC `A₀ = (1+√2)I + (√2+√3)J`; the
witness field's gradient points along the first axis, so only the diagonal
entry `A₀[0,0] = 1 + 2√2 + √3` enters its target. No isotropy is claimed.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace FreudenthalEnergyLimit

open Geometry.PeriodicFreudenthalTorus
open FreudenthalStencilPreflight

noncomputable section

/-! ## §1. The witness field and its lattice sampling -/

/-- The fixed nonconstant C² witness field `f(p) = sin(2π p₀)` on `ℝ³`. -/
def witnessField (p : Fin 3 → ℝ) : ℝ := Real.sin (2 * Real.pi * p 0)

/-- Sampling a continuum field onto the side-`N` periodic vertex lattice
(vertex `x` sits at the point `x/N` of the unit 3-torus). -/
def sample (N : ℕ) (f : (Fin 3 → ℝ) → ℝ) (x : Vertex N N N) : ℝ :=
  f ![(x.1.val : ℝ) / N, (x.2.1.val : ℝ) / N, (x.2.2.val : ℝ) / N]

/-- The sampled witness field in explicit first-coordinate form. -/
def witnessSample (N : ℕ) (x : Vertex N N N) : ℝ :=
  Real.sin (2 * Real.pi * (x.1.val : ℝ) / N)

theorem sample_witnessField (N : ℕ) (x : Vertex N N N) :
    sample N witnessField x = witnessSample N x := by
  unfold sample witnessField witnessSample
  rw [Matrix.cons_val_zero, mul_div_assoc]

/-- The witness field is nonconstant: it separates `(1/4,0,0)` from the
origin (`sin(π/2) = 1 ≠ 0 = sin 0`). -/
theorem witnessField_nonconstant :
    witnessField ![(1:ℝ)/4, 0, 0] ≠ witnessField ![0, 0, 0] := by
  unfold witnessField
  rw [Matrix.cons_val_zero, Matrix.cons_val_zero]
  have harg : 2 * Real.pi * ((1:ℝ)/4) = Real.pi / 2 := by ring
  rw [harg]
  rw [Real.sin_pi_div_two]
  simp only [mul_zero, Real.sin_zero]
  norm_num

/-! ## §2. The by-hand continuum target and its Lean-checked integral -/

/-- By-hand gradient of the witness field: `∇f(p) = (2π cos(2πp₀), 0, 0)`.
The nonzero component is certified against the one-dimensional section in
`witnessField_section_hasDerivAt`; the vanishing components hold because
`witnessField` does not depend on `p₁, p₂` (definitionally: `p₁, p₂` do not
occur in `witnessField`). -/
def witnessGrad (t : ℝ) : Fin 3 → ℝ := fun i =>
  if i = 0 then 2 * Real.pi * Real.cos (2 * Real.pi * t) else 0

theorem hasDerivAt_sin_const_mul (c t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sin (c * s)) (Real.cos (c * t) * c) t := by
  have h := ((hasDerivAt_id t).const_mul c).sin
  simpa using h

/-- The first gradient component is the honest derivative of the witness
field along the first coordinate axis. -/
theorem witnessField_section_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => witnessField ![s, 0, 0]) (witnessGrad t 0) t := by
  have hg : witnessGrad t 0 = Real.cos (2 * Real.pi * t) * (2 * Real.pi) := by
    show (if (0 : Fin 3) = 0 then 2 * Real.pi * Real.cos (2 * Real.pi * t) else 0) =
      Real.cos (2 * Real.pi * t) * (2 * Real.pi)
    rw [if_pos rfl]
    ring
  rw [hg]
  simp only [witnessField, Matrix.cons_val_zero]
  exact hasDerivAt_sin_const_mul (2 * Real.pi) t

/-- The continuum target `∫_{[0,1]³} ⟨∇f, A₀ ∇f⟩ = A₀[0,0] · 2π²`, defined
INDEPENDENTLY of the lattice computation as an exact constant (by-hand cube
integral; the integrand depends only on the first coordinate, so the cube
integral equals the interval integral certified in
`integral_witness_energy_density`). -/
def continuumTarget : ℝ := stencilMomentTensor 0 0 * (2 * Real.pi ^ (2 : ℕ))

/-- Gate (vi): the continuum target is strictly positive (nonzero limit;
this witness is not in the `0 = 0` trap). -/
theorem continuumTarget_pos : 0 < continuumTarget := by
  unfold continuumTarget
  have hpi : 0 < Real.pi := Real.pi_pos
  exact mul_pos (stencilMomentTensor_diag_pos 0) (by positivity)

/-- Pointwise anisotropic energy density of the witness field:
`⟨∇f, A₀ ∇f⟩(t) = A₀[0,0] · (2π cos(2πt))²`. -/
theorem witness_energy_density_eq (t : ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3,
        stencilMomentTensor i j * witnessGrad t i * witnessGrad t j) =
      stencilMomentTensor 0 0 *
        (2 * Real.pi * Real.cos (2 * Real.pi * t)) ^ (2 : ℕ) := by
  simp only [witnessGrad, Fin.sum_univ_three,
    show ((1 : Fin 3) = 0) = False by decide, show ((2 : Fin 3) = 0) = False by decide,
    if_false, if_true]
  ring

theorem integral_cos_sq_two_pi :
    (∫ x in (0:ℝ)..1, Real.cos (2 * Real.pi * x) ^ (2 : ℕ)) = 1 / 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => t / 2 + Real.sin (4 * Real.pi * t) / (8 * Real.pi))
        (Real.cos (2 * Real.pi * x) ^ (2 : ℕ)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => t / 2) ((1:ℝ) / 2) x := by
      simpa using (hasDerivAt_id x).div_const 2
    have h2 : HasDerivAt (fun t : ℝ => Real.sin (4 * Real.pi * t) / (8 * Real.pi))
        ((Real.cos (4 * Real.pi * x) * (4 * Real.pi)) / (8 * Real.pi)) x :=
      (hasDerivAt_sin_const_mul (4 * Real.pi) x).div_const (8 * Real.pi)
    have hval : (1:ℝ) / 2 + (Real.cos (4 * Real.pi * x) * (4 * Real.pi)) / (8 * Real.pi) =
        Real.cos (2 * Real.pi * x) ^ (2 : ℕ) := by
      rw [Real.cos_sq]
      have h4 : 2 * (2 * Real.pi * x) = 4 * Real.pi * x := by ring
      rw [h4]
      field_simp
      try ring
    rw [← hval]
    exact h1.add h2
  have hcont : Continuous fun x : ℝ => Real.cos (2 * Real.pi * x) ^ (2 : ℕ) := by
    fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 1)
  rw [hint]
  have hsin4 : Real.sin (4 * Real.pi) = 0 := by
    have h := Real.sin_nat_mul_pi 4
    push_cast at h
    exact h
  norm_num [hsin4]

/-- Lean-checked evaluation of the continuum target: the interval integral
of the anisotropic energy density is exactly `continuumTarget`. -/
theorem integral_witness_energy_density :
    (∫ t in (0:ℝ)..1,
        ∑ i : Fin 3, ∑ j : Fin 3,
          stencilMomentTensor i j * witnessGrad t i * witnessGrad t j) =
      continuumTarget := by
  have hpt : (fun t : ℝ =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        stencilMomentTensor i j * witnessGrad t i * witnessGrad t j) =
      fun t : ℝ =>
        (stencilMomentTensor 0 0 * (2 * Real.pi) ^ (2 : ℕ)) *
          Real.cos (2 * Real.pi * t) ^ (2 : ℕ) := by
    funext t
    rw [witness_energy_density_eq]
    ring
  rw [hpt, intervalIntegral.integral_const_mul, integral_cos_sq_two_pi]
  unfold continuumTarget
  ring

/-! ## §3. Exact closed-form evaluation of the sampled lattice energy -/

/-- Periodic wraparound of the sampled sine: shifting one lattice step in
the first coordinate is an honest `+1` inside the sine, including at the
wraparound seam (where both sides are `sin` of a full period). -/
theorem witnessSample_addBit_true (N : ℕ) [NeZero N] (i : Fin N) :
    Real.sin (2 * Real.pi * ((addBit i true).val : ℝ) / N) =
      Real.sin (2 * Real.pi * ((i.val : ℝ) + 1) / N) := by
  have hval : (addBit i true).val = (i.val + 1) % N := rfl
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt i.isLt) with h | h
  · rw [hval, Nat.mod_eq_of_lt h]
    norm_cast
  · have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have h' : i.val + 1 = N := h
    have h1 : ((i.val : ℝ) + 1) = (N : ℝ) := by exact_mod_cast h'
    rw [hval, h', Nat.mod_self, h1]
    have h2 : 2 * Real.pi * (N : ℝ) / N = 2 * Real.pi := by field_simp
    rw [h2]
    simp [Real.sin_two_pi]

/-- Per-vertex evaluation of the seven-class stencil on the sampled witness
field: the three classes with no first-coordinate step contribute zero, and
the four classes stepping in the first coordinate (weights
`1, √2, √2, √3`) sum to exactly the moment-tensor entry `A₀[0,0]`. -/
theorem stencil_inner_sum_witness (N : ℕ) [NeZero N] (x : Vertex N N N) :
    (∑ d : Fin 7, stencilWeight d *
        (witnessSample N (shiftVertex N x d) - witnessSample N x) ^ (2 : ℕ)) =
      stencilMomentTensor 0 0 *
        (Real.sin (2 * Real.pi * ((x.1.val : ℝ) + 1) / N) -
          Real.sin (2 * Real.pi * (x.1.val : ℝ) / N)) ^ (2 : ℕ) := by
  simp only [Fin.sum_univ_seven, shiftVertex, addBits, dispBits, addBit_false,
    witnessSample, witnessSample_addBit_true]
  rw [stencilMomentTensor_eq]
  norm_num [stencilWeight, periodicDispSqEdge, Real.sqrt_one]
  try ring

/-- Telescoping vanishing of the equally spaced cosine sum
`Σ_{k<N} cos((4k+2)π/N) = 0` for `N > 2`
(via `2 sin(2π/N) cos((4k+2)π/N) = sin(4π(k+1)/N) − sin(4πk/N)`). -/
theorem sum_cos_shifted_vanishes (N : ℕ) (hN : 2 < N) :
    (∑ k ∈ Finset.range N, Real.cos ((4 * (k : ℝ) + 2) * Real.pi / N)) = 0 := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    linarith
  have hNgt : (2 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs_pos : 0 < Real.sin (2 * Real.pi / N) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hNpos]
      nlinarith [Real.pi_pos]
  have hs2 : (2 : ℝ) * Real.sin (2 * Real.pi / N) ≠ 0 := by positivity
  have hkey : ∀ k : ℕ,
      2 * Real.sin (2 * Real.pi / N) * Real.cos ((4 * (k : ℝ) + 2) * Real.pi / N) =
        Real.sin (4 * Real.pi * (((k + 1 : ℕ)) : ℝ) / N) -
          Real.sin (4 * Real.pi * ((k : ℕ) : ℝ) / N) := by
    intro k
    rw [Real.sin_sub_sin]
    have h1 : (4 * Real.pi * (((k + 1 : ℕ)) : ℝ) / N - 4 * Real.pi * ((k : ℕ) : ℝ) / N) / 2 =
        2 * Real.pi / N := by
      push_cast
      field_simp
      try ring
    have h2 : (4 * Real.pi * (((k + 1 : ℕ)) : ℝ) / N + 4 * Real.pi * ((k : ℕ) : ℝ) / N) / 2 =
        (4 * (k : ℝ) + 2) * Real.pi / N := by
      push_cast
      field_simp
      try ring
    rw [h1, h2]
  have hend : Real.sin (4 * Real.pi * ((N : ℕ) : ℝ) / N) = 0 := by
    have harg : 4 * Real.pi * ((N : ℕ) : ℝ) / N = ((4 : ℕ) : ℝ) * Real.pi := by
      push_cast
      field_simp
      try ring
    rw [harg]
    exact Real.sin_nat_mul_pi 4
  have h2s : (2 * Real.sin (2 * Real.pi / N)) *
      (∑ k ∈ Finset.range N, Real.cos ((4 * (k : ℝ) + 2) * Real.pi / N)) = 0 := by
    rw [Finset.mul_sum]
    calc (∑ k ∈ Finset.range N,
          2 * Real.sin (2 * Real.pi / N) * Real.cos ((4 * (k : ℝ) + 2) * Real.pi / N))
        = ∑ k ∈ Finset.range N,
            (Real.sin (4 * Real.pi * (((k + 1 : ℕ)) : ℝ) / N) -
              Real.sin (4 * Real.pi * ((k : ℕ) : ℝ) / N)) :=
          Finset.sum_congr rfl fun k _ => hkey k
      _ = Real.sin (4 * Real.pi * ((N : ℕ) : ℝ) / N) -
            Real.sin (4 * Real.pi * ((0 : ℕ) : ℝ) / N) :=
          Finset.sum_range_sub (fun k : ℕ => Real.sin (4 * Real.pi * ((k : ℕ) : ℝ) / N)) N
      _ = 0 := by
          rw [hend]
          norm_num
  exact (mul_eq_zero.mp h2s).resolve_left hs2

/-- Exact evaluation of the first-difference sine sum:
`Σ_{k<N} (sin(2π(k+1)/N) − sin(2πk/N))² = 2N sin²(π/N)` for `N > 2`. -/
theorem sum_range_sq_sinDiff (N : ℕ) (hN : 2 < N) :
    (∑ k ∈ Finset.range N,
        (Real.sin (2 * Real.pi * ((k : ℝ) + 1) / N) -
          Real.sin (2 * Real.pi * (k : ℝ) / N)) ^ (2 : ℕ)) =
      2 * (N : ℝ) * Real.sin (Real.pi / N) ^ (2 : ℕ) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hterm : ∀ k : ℕ,
      (Real.sin (2 * Real.pi * ((k : ℝ) + 1) / N) -
          Real.sin (2 * Real.pi * (k : ℝ) / N)) ^ (2 : ℕ) =
        2 * Real.sin (Real.pi / N) ^ (2 : ℕ) +
          2 * Real.sin (Real.pi / N) ^ (2 : ℕ) *
            Real.cos ((4 * (k : ℝ) + 2) * Real.pi / N) := by
    intro k
    rw [Real.sin_sub_sin]
    have h1 : (2 * Real.pi * ((k : ℝ) + 1) / N - 2 * Real.pi * (k : ℝ) / N) / 2 =
        Real.pi / N := by
      field_simp
      try ring
    have h2 : (2 * Real.pi * ((k : ℝ) + 1) / N + 2 * Real.pi * (k : ℝ) / N) / 2 =
        (2 * (k : ℝ) + 1) * Real.pi / N := by
      field_simp
      try ring
    rw [h1, h2]
    have h3 : 2 * ((2 * (k : ℝ) + 1) * Real.pi / N) = (4 * (k : ℝ) + 2) * Real.pi / N := by
      field_simp
      try ring
    calc (2 * Real.sin (Real.pi / N) * Real.cos ((2 * (k : ℝ) + 1) * Real.pi / N)) ^ (2 : ℕ)
        = 4 * Real.sin (Real.pi / N) ^ (2 : ℕ) *
            Real.cos ((2 * (k : ℝ) + 1) * Real.pi / N) ^ (2 : ℕ) := by ring
      _ = 4 * Real.sin (Real.pi / N) ^ (2 : ℕ) *
            (1 / 2 + Real.cos ((4 * (k : ℝ) + 2) * Real.pi / N) / 2) := by
          rw [Real.cos_sq, h3]
      _ = 2 * Real.sin (Real.pi / N) ^ (2 : ℕ) +
            2 * Real.sin (Real.pi / N) ^ (2 : ℕ) *
              Real.cos ((4 * (k : ℝ) + 2) * Real.pi / N) := by ring
  calc (∑ k ∈ Finset.range N,
        (Real.sin (2 * Real.pi * ((k : ℝ) + 1) / N) -
          Real.sin (2 * Real.pi * (k : ℝ) / N)) ^ (2 : ℕ))
      = ∑ k ∈ Finset.range N,
          (2 * Real.sin (Real.pi / N) ^ (2 : ℕ) +
            2 * Real.sin (Real.pi / N) ^ (2 : ℕ) *
              Real.cos ((4 * (k : ℝ) + 2) * Real.pi / N)) :=
        Finset.sum_congr rfl fun k _ => hterm k
    _ = (N : ℝ) * (2 * Real.sin (Real.pi / N) ^ (2 : ℕ)) +
          2 * Real.sin (Real.pi / N) ^ (2 : ℕ) *
            ∑ k ∈ Finset.range N, Real.cos ((4 * (k : ℝ) + 2) * Real.pi / N) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, ← Finset.mul_sum]
    _ = 2 * (N : ℝ) * Real.sin (Real.pi / N) ^ (2 : ℕ) := by
        rw [sum_cos_shifted_vanishes N hN]
        ring

/-- Aggregation of the per-vertex stencil over the `N³` vertex lattice: the
two free coordinates contribute a factor `N²`. -/
theorem freudenthalStencilEnergy_witness (N : ℕ) [NeZero N] :
    freudenthalStencilEnergy N (witnessSample N) =
      (N : ℝ) ^ (2 : ℕ) * (stencilMomentTensor 0 0 *
        ∑ k ∈ Finset.range N,
          (Real.sin (2 * Real.pi * ((k : ℝ) + 1) / N) -
            Real.sin (2 * Real.pi * (k : ℝ) / N)) ^ (2 : ℕ)) := by
  unfold freudenthalStencilEnergy
  rw [Fintype.sum_prod_type]
  calc (∑ a : Fin N, ∑ bc : Fin N × Fin N, ∑ d : Fin 7,
        stencilWeight d *
          (witnessSample N (shiftVertex N (a, bc) d) - witnessSample N (a, bc)) ^ (2 : ℕ))
      = ∑ a : Fin N, ∑ _bc : Fin N × Fin N,
          stencilMomentTensor 0 0 *
            (Real.sin (2 * Real.pi * ((a.val : ℝ) + 1) / N) -
              Real.sin (2 * Real.pi * (a.val : ℝ) / N)) ^ (2 : ℕ) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun bc _ =>
          stencil_inner_sum_witness N (a, bc)
    _ = ∑ a : Fin N, ((N : ℝ) * (N : ℝ)) *
          (stencilMomentTensor 0 0 *
            (Real.sin (2 * Real.pi * ((a.val : ℝ) + 1) / N) -
              Real.sin (2 * Real.pi * (a.val : ℝ) / N)) ^ (2 : ℕ)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring
    _ = (N : ℝ) ^ (2 : ℕ) * (stencilMomentTensor 0 0 *
          ∑ a : Fin N,
            (Real.sin (2 * Real.pi * ((a.val : ℝ) + 1) / N) -
              Real.sin (2 * Real.pi * (a.val : ℝ) / N)) ^ (2 : ℕ)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
    _ = (N : ℝ) ^ (2 : ℕ) * (stencilMomentTensor 0 0 *
          ∑ k ∈ Finset.range N,
            (Real.sin (2 * Real.pi * ((k : ℝ) + 1) / N) -
              Real.sin (2 * Real.pi * (k : ℝ) / N)) ^ (2 : ℕ)) := by
        rw [Fin.sum_univ_eq_sum_range
          (fun k : ℕ => (Real.sin (2 * Real.pi * ((k : ℝ) + 1) / N) -
            Real.sin (2 * Real.pi * (k : ℝ) / N)) ^ (2 : ℕ)) N]

/-- EXACT closed form of the normalized sampled energy for every `N > 2`:
`scaledCanonicalEnergy N (witnessSample N) = A₀[0,0] · 2N² sin²(π/N)`. -/
theorem scaledCanonicalEnergy_witness_closed_form (N : ℕ) [NeZero N] (hN : 2 < N) :
    scaledCanonicalEnergy N (witnessSample N) =
      stencilMomentTensor 0 0 *
        (2 * (N : ℝ) ^ (2 : ℕ) * Real.sin (Real.pi / N) ^ (2 : ℕ)) := by
  rw [scaledCanonicalEnergy_eq_scaled_stencil N hN, freudenthalStencilEnergy_witness N,
    sum_range_sq_sinDiff N hN]
  unfold stencilNormalization
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  try ring

/-! ## §4. The rated limit -/

/-- The explicit `N`-independent rate constant `C = A₀[0,0] · (2π)⁴ / 24`. -/
def rateConstant : ℝ := stencilMomentTensor 0 0 * (2 * Real.pi) ^ (4 : ℕ) / 24

theorem rateConstant_nonneg : 0 ≤ rateConstant := by
  unfold rateConstant
  have hA : 0 ≤ stencilMomentTensor 0 0 := le_of_lt (stencilMomentTensor_diag_pos 0)
  have hpi : 0 ≤ (2 * Real.pi) ^ (4 : ℕ) := by positivity
  exact div_nonneg (mul_nonneg hA hpi) (by norm_num)

/-- Quantitative distance of the closed form from the continuum target:
`|A₀[0,0]·2N²sin²(π/N) − continuumTarget| ≤ rateConstant/N²`, consuming the
Phase-2a toolkit bound `discrete_sine_eigenvalue_expansion` at wavenumber 1.
The achieved rate is `1/N²`, strictly better than the demanded `1/N`. -/
theorem witness_closed_form_dist (N : ℕ) (hN : 3 ≤ N) :
    |stencilMomentTensor 0 0 *
        (2 * (N : ℝ) ^ (2 : ℕ) * Real.sin (Real.pi / N) ^ (2 : ℕ)) -
      continuumTarget| ≤ rateConstant / (N : ℝ) ^ (2 : ℕ) := by
  have hA : 0 ≤ stencilMomentTensor 0 0 := le_of_lt (stencilMomentTensor_diag_pos 0)
  have hexp := discrete_sine_eigenvalue_expansion 1 N (by omega)
  simp only [Nat.cast_one, mul_one] at hexp
  have hkey : stencilMomentTensor 0 0 *
      (2 * (N : ℝ) ^ (2 : ℕ) * Real.sin (Real.pi / N) ^ (2 : ℕ)) - continuumTarget =
      (stencilMomentTensor 0 0 / 2) *
        (4 * (N : ℝ) ^ 2 * Real.sin (Real.pi / (N : ℝ)) ^ 2 - (2 * Real.pi) ^ 2) := by
    unfold continuumTarget
    ring
  rw [hkey, abs_mul, abs_of_nonneg (div_nonneg hA (by norm_num))]
  calc (stencilMomentTensor 0 0 / 2) *
        |4 * (N : ℝ) ^ 2 * Real.sin (Real.pi / (N : ℝ)) ^ 2 - (2 * Real.pi) ^ 2|
      ≤ (stencilMomentTensor 0 0 / 2) * ((2 * Real.pi) ^ 4 / 12 / (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hexp (div_nonneg hA (by norm_num))
    _ = rateConstant / (N : ℝ) ^ (2 : ℕ) := by
        unfold rateConstant
        ring

/-- Panel-locked stage-2 rate bound, explicit-constant form: for every
`N ≥ 3`,
`|scaledCanonicalEnergy N (sample N witnessField) − continuumTarget| ≤ rateConstant / N`,
with `rateConstant` independent of `N`. -/
theorem scaledCanonicalEnergy_witness_rate (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    |scaledCanonicalEnergy N (sample N witnessField) - continuumTarget| ≤
      rateConstant / (N : ℝ) := by
  have hN2 : 2 < N := hN
  have hs : sample N witnessField = witnessSample N :=
    funext fun x => sample_witnessField N x
  rw [hs, scaledCanonicalEnergy_witness_closed_form N hN2]
  refine le_trans (witness_closed_form_dist N hN) ?_
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hsq : (N : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith
  have hrc : 0 ≤ rateConstant := rateConstant_nonneg
  gcongr

/-- Panel-locked stage-2 observable (existential form): there is a constant
`C` and a threshold `N₀` with
`∀ N ≥ N₀, |scaledCanonicalEnergy N (sample N f) − ∫⟨∇f, A₀∇f⟩| ≤ C/N`
for the fixed nonconstant witness `f = witnessField`; the witnesses are the
explicit `rateConstant` and `N₀ = 3`. -/
theorem freudenthal_witness_energy_limit :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      |scaledCanonicalEnergy N (sample N witnessField) - continuumTarget| ≤
        C / (N : ℝ) := by
  refine ⟨rateConstant, 3, ?_⟩
  intro N _ hN
  exact scaledCanonicalEnergy_witness_rate N hN

/-- The same rate bound stated directly against the Lean-checked integral
of the anisotropic energy density (interval form of `∫⟨∇f, A₀∇f⟩`). -/
theorem freudenthal_witness_energy_rate_integral_form (N : ℕ) [NeZero N]
    (hN : 3 ≤ N) :
    |scaledCanonicalEnergy N (sample N witnessField) -
        ∫ t in (0:ℝ)..1,
          ∑ i : Fin 3, ∑ j : Fin 3,
            stencilMomentTensor i j * witnessGrad t i * witnessGrad t j| ≤
      rateConstant / (N : ℝ) := by
  rw [integral_witness_energy_density]
  exact scaledCanonicalEnergy_witness_rate N hN

/-- Qualitative limit of the closed-form energy sequence, re-derived from
the rate through the Phase-2a toolkit squeeze
`eigenvalue_limit_of_uniform_bound` (toolkit composition check). -/
theorem witness_closed_form_tendsto :
    Filter.Tendsto
      (fun N : ℕ => stencilMomentTensor 0 0 *
        (2 * (N : ℝ) ^ (2 : ℕ) * Real.sin (Real.pi / N) ^ (2 : ℕ)))
      Filter.atTop (nhds continuumTarget) :=
  eigenvalue_limit_of_uniform_bound _ continuumTarget rateConstant 3
    (fun N hN => witness_closed_form_dist N hN)

/-! ## §5. Status record (documentation, not mathematics) -/

/-- Status flags for the Freudenthal energy limit (documentation record;
the mathematics lives in the theorems above, not in these booleans).

Honest scope: with stage 1 this certifies the action-level continuum limit
of the frozen quadratic energy on the canonical Freudenthal family, for one
fixed nonconstant sampled witness field, with an explicit `N`-independent
rate constant. SCOPED PARTIAL: the pillar-2 path-sum flag stays red
(flipping it requires the refinement-indexed measure-weighted sum over
inequivalent triangulation classes); the anisotropic tensor `A₀` (stage-1
finding) governs the target, and no isotropy is claimed. -/
structure EnergyLimitStatus where
  /-- `scaledCanonicalEnergy_witness_closed_form`: exact lattice evaluation
  for every `N > 2` (telescoping identity, not an estimate). -/
  exact_closed_form : Bool
  /-- `continuumTarget` defined independently; `continuumTarget_pos`;
  `integral_witness_energy_density` checked in Lean. -/
  independent_positive_target : Bool
  /-- `scaledCanonicalEnergy_witness_rate`: rate `C/N` with explicit
  `C = rateConstant` independent of `N` (achieved rate `C/N²`). -/
  explicit_rate_constant : Bool
  /-- `witness_closed_form_dist` and `witness_closed_form_tendsto` consume
  the Phase-2a toolkit (`discrete_sine_eigenvalue_expansion`,
  `eigenvalue_limit_of_uniform_bound`). -/
  toolkit_consumed : Bool

/-- The canonical status inhabitant (documentation record, not a proof
obligation). -/
def energyLimitStatus : EnergyLimitStatus where
  exact_closed_form := true
  independent_positive_target := true
  explicit_rate_constant := true
  toolkit_consumed := true

end

end FreudenthalEnergyLimit
end Analysis
end Gravity
end IndisputableMonolith
