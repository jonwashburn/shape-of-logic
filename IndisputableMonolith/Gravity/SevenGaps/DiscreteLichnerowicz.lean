import Mathlib

/-!
# Discrete Lichnerowicz operator: flat 3-torus TT spectrum convergence

Seven-Gaps campaign, Lane 4 ("operator convergence" gap).

This file builds the first genuine Lean connection between the discrete
perturbation spectrum on a lattice and the continuum Lichnerowicz operator,
on the FLAT 3-torus background. Nothing here imports or cites the old
`Relativity/` GW files (which are vacuous).

## AXIS-SECTOR SCOPE (re-tagged 2026-07-15, panel mandate C14)

Every convergence result in this file is proved along the AXIS stencil
sector only: plane waves `k = (k, 0, 0)` acted on by the componentwise
axis-stencil Laplacian `discLap3`. Test G
(`Gravity.Analysis.FreudenthalStencilPreflight` /
`Gravity.Analysis.FreudenthalEnergyLimit`, commits 7b808f75b4 and
1d3ed6da06) kernel-proved that the continuum moment tensor of the
canonical Freudenthal frozen quadratic energy is ANISOTROPIC:
`A₀ = (1+√2)·I + (√2+√3)·J`, with the body-diagonal direction roughly
4.9x stiffer than an axis direction. Axis stencils are blind to that
anisotropy, so the axis-sector results below MUST NOT be read as
isotropic flat-space recovery of the full Lichnerowicz spectrum. The
direction-resolved symbol question is governed by the C10 probe (plan
receipt P-iso, 2026-07-15).

## Representation choice

Lattice functions are represented as N-periodic functions `ℤ → ℂ` (period `N`,
spacing `h = 1/N` on the unit circle), NOT as functions on `ZMod N`. This
avoids `ZMod.val` wraparound arithmetic entirely: the discrete Laplacian
stencil and the Fourier-mode eigenvalue identity hold pointwise for every
`j : ℤ`, and periodicity of the modes (`fourierMode_periodic`) is what
grounds the torus interpretation. 3D lattice sites are `ℤ × ℤ × ℤ` with
periodicity along each axis (`planeH_periodic_axis`, `planeH_shift_yz`).

## Honest tiers

* THEOREM (proved below, axiom-clean):
  - `discLap_fourierMode` / `discLap_fourierMode_apply`: the Fourier mode
    `exp(2πik j/N)` is an eigenvector of the spacing-normalized discrete
    Laplacian with eigenvalue `-(4 N² sin²(πk/N))`.
  - `discreteEigenvalue_tendsto`: for fixed wavenumber `k`, the discrete
    (positive, i.e. minus-Laplacian) eigenvalue `4 N² sin²(πk/N)` of the
    AXIS mode converges to `(2πk)²` as the lattice is refined (`N → ∞`).
    Axis sector only; see the scope note above.
  - `planeH_transverse`: the axis plane wave with first-row-zero polarization
    is exactly discrete-transverse (forward-difference divergence ≡ 0).
  - `epsPlus_*` / `epsCross_*` / `polarizations_linearIndependent`: the two
    standard TT polarizations are symmetric, traceless, first-row/column
    zero, and linearly independent over ℂ.
  - `discLap3_planeH`: the 3D axis plane wave is an eigenvector of the 3D
    discrete Laplacian with the same eigenvalue as the 1D mode.
  - `continuumProfile_hasDerivAt` / `continuumProfile_second_deriv`: the
    continuum plane-wave profile `exp(2πik t)` has second derivative
    `-(2πk)²` times itself, so `(2πk)²` is the genuine `-Δ` eigenvalue of
    the continuum mode along the wave direction.

* MODEL (definitional, justified in docstring, not a curved-space theorem):
  - `lichnerowiczFlatEigenvalue`: on a flat background the Lichnerowicz
    operator on TT tensors reduces to `-Δ` (the Riemann curvature term
    vanishes identically), so its eigenvalue on the wavenumber-`k` TT plane
    wave is `(2πk)²`. We encode this reduction as a definition; no
    curved-space geometry is formalized or claimed here.

* OPEN: curved backgrounds (Schwarzschild, Kerr) and quasinormal-mode
  spectra are NOT treated. See `status` flags at the bottom.

The packaged claim (`discrete_tt_spectrum_converges_to_flat_lichnerowicz`):
discrete TT eigenvalues of AXIS modes converge to `(2πk)²`, the flat
Lichnerowicz eigenvalue on that axis sector. Per the AXIS-SECTOR SCOPE
note above, this is a sector statement, not isotropic flat-space recovery.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace DiscreteLichnerowicz

open Filter Topology

/-! ## 1D core: lattice functions on the unit circle -/

/-- Spacing-normalized 1D discrete Laplacian for a lattice of `N` sites on
the unit circle (spacing `h = 1/N`): `(discLap f) j = (f(j+1) - 2 f(j) + f(j-1)) / h²`. -/
noncomputable def discLap (N : ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun j => (N : ℂ) ^ 2 * (f (j + 1) - 2 * f j + f (j - 1))

/-- Fourier mode of wavenumber `k` on the `N`-site lattice:
`j ↦ exp(2πi k j / N)`. -/
noncomputable def fourierMode (N : ℕ) (k : ℤ) : ℤ → ℂ :=
  fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (j : ℂ) / (N : ℂ))

/-- THEOREM. The Fourier mode is `N`-periodic: it genuinely lives on the
`N`-site discrete circle (torus). For `N = 0` periodicity is trivial. -/
theorem fourierMode_periodic (N : ℕ) (k : ℤ) :
    Function.Periodic (fourierMode N k) (N : ℤ) := by
  intro j
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h.ne'
    simp only [fourierMode]
    have hexp : 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((j + (N : ℤ) : ℤ) : ℂ) / (N : ℂ)
        = 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (j : ℂ) / (N : ℂ)
          + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      field_simp
    rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- One-step shift of the Fourier mode: multiplication by `exp(iθ)` with
`θ = 2πk/N`. -/
lemma fourierMode_step (N : ℕ) (k : ℤ) (j : ℤ) :
    fourierMode N k (j + 1)
      = fourierMode N k j
        * Complex.exp (((2 * Real.pi * (k : ℝ) / (N : ℝ) : ℝ) : ℂ) * Complex.I) := by
  simp only [fourierMode]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- One-step down-shift of the Fourier mode: multiplication by `exp(-iθ)`. -/
lemma fourierMode_step_down (N : ℕ) (k : ℤ) (j : ℤ) :
    fourierMode N k (j - 1)
      = fourierMode N k j
        * Complex.exp (-(((2 * Real.pi * (k : ℝ) / (N : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  simp only [fourierMode]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `exp(iθ) + exp(-iθ) = 2 cos θ` for real `θ` (viewed in ℂ). -/
lemma exp_add_exp_neg_mul_I (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (-((θ : ℂ) * Complex.I))
      = 2 * Complex.cos (θ : ℂ) := by
  rw [show -((θ : ℂ) * Complex.I) = (-(θ : ℂ)) * Complex.I by ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring

/-- THEOREM (pointwise eigenvalue identity). The discrete Laplacian acts on
the Fourier mode by the scalar `-(4 N² sin²(πk/N))`, at every lattice point.
Derivation: `f(j±1) = f(j) exp(±iθ)`, `exp(iθ)+exp(-iθ) = 2cos θ`, and
`2cos θ - 2 = -4 sin²(θ/2)` with `θ = 2πk/N`. -/
theorem discLap_fourierMode_apply (N : ℕ) (k : ℤ) (j : ℤ) :
    discLap N (fourierMode N k) j
      = ((-(4 * (N : ℝ) ^ 2 * Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) ^ 2) : ℝ) : ℂ)
          * fourierMode N k j := by
  have hstep := fourierMode_step N k j
  have hstepd := fourierMode_step_down N k j
  have hsum := exp_add_exp_neg_mul_I (2 * Real.pi * (k : ℝ) / (N : ℝ))
  have hreal : (2 * Real.cos (2 * Real.pi * (k : ℝ) / (N : ℝ)) - 2 : ℝ)
      = -(4 * Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) ^ 2) := by
    have h := Real.sin_sq_eq_half_sub (x := Real.pi * (k : ℝ) / (N : ℝ))
    have h2 : 2 * (Real.pi * (k : ℝ) / (N : ℝ)) = 2 * Real.pi * (k : ℝ) / (N : ℝ) := by
      ring
    rw [h2] at h
    linarith
  simp only [discLap]
  rw [hstep, hstepd]
  rw [show (N : ℂ) ^ 2 *
        (fourierMode N k j
            * Complex.exp (((2 * Real.pi * (k : ℝ) / (N : ℝ) : ℝ) : ℂ) * Complex.I)
          - 2 * fourierMode N k j
          + fourierMode N k j
            * Complex.exp (-(((2 * Real.pi * (k : ℝ) / (N : ℝ) : ℝ) : ℂ) * Complex.I)))
      = (N : ℂ) ^ 2 * fourierMode N k j *
          ((Complex.exp (((2 * Real.pi * (k : ℝ) / (N : ℝ) : ℝ) : ℂ) * Complex.I)
            + Complex.exp (-(((2 * Real.pi * (k : ℝ) / (N : ℝ) : ℝ) : ℂ) * Complex.I))) - 2)
      by ring]
  rw [hsum, ← Complex.ofReal_cos]
  calc (N : ℂ) ^ 2 * fourierMode N k j
        * (2 * ((Real.cos (2 * Real.pi * (k : ℝ) / (N : ℝ)) : ℝ) : ℂ) - 2)
      = ((2 * Real.cos (2 * Real.pi * (k : ℝ) / (N : ℝ)) - 2 : ℝ) : ℂ)
          * ((N : ℂ) ^ 2 * fourierMode N k j) := by
        push_cast
        ring
    _ = ((-(4 * Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) ^ 2) : ℝ) : ℂ)
          * ((N : ℂ) ^ 2 * fourierMode N k j) := by
        rw [hreal]
    _ = ((-(4 * (N : ℝ) ^ 2 * Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) ^ 2) : ℝ) : ℂ)
          * fourierMode N k j := by
        push_cast
        ring

/-- THEOREM (eigenvalue identity, function form).
`discLap (fourierMode k) = -(4 N² sin²(πk/N)) • fourierMode k`. -/
theorem discLap_fourierMode (N : ℕ) (k : ℤ) :
    discLap N (fourierMode N k)
      = (-(4 * (N : ℝ) ^ 2 * Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) ^ 2)) • fourierMode N k := by
  funext j
  rw [Pi.smul_apply, Complex.real_smul]
  exact discLap_fourierMode_apply N k j

/-! ## Convergence of the discrete spectrum -/

/-- The (positive, minus-Laplacian) discrete eigenvalue of the wavenumber-`k`
mode on the `N`-site lattice: `4 N² sin²(πk/N)`. -/
noncomputable def discreteEigenvalue (N k : ℕ) : ℝ :=
  4 * (N : ℝ) ^ 2 * Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) ^ 2

/-- THEOREM (the core convergence result; AXIS SECTOR ONLY). For fixed
wavenumber `k`, the discrete eigenvalue `4 N² sin²(πk/N)` of the AXIS mode
converges to the continuum eigenvalue `(2πk)²` as the lattice is refined.
Proof: `4N² sin²(πk/N) = (2πk)² (sin x / x)²` with `x = πk/N → 0`, and
`sin x / x → 1` at `0` (from `HasDerivAt sin 1 0` via the slope
characterization); the wavenumber `k = 0` is handled separately (both sides
vanish identically).

Scope: this is a statement about axis-aligned modes of the axis-stencil
Laplacian. Test G (`FreudenthalStencilPreflight`/`FreudenthalEnergyLimit`,
commits 7b808f75b4, 1d3ed6da06) kernel-proved the full continuum moment
tensor is anisotropic, `A₀ = (1+√2)I + (√2+√3)J`, which axis stencils
cannot see; do not read this as isotropic flat-space recovery. The
direction-resolved symbol question is governed by the C10 probe (plan
receipt P-iso, 2026-07-15). -/
theorem discreteEigenvalue_tendsto (k : ℕ) :
    Filter.Tendsto (fun N : ℕ => discreteEigenvalue N k) Filter.atTop
      (nhds ((2 * Real.pi * (k : ℝ)) ^ 2)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hzero : (fun N : ℕ => discreteEigenvalue N 0) = fun _ : ℕ => (0 : ℝ) := by
      funext N
      norm_num [discreteEigenvalue]
    rw [hzero]
    have h0 : ((2 * Real.pi * ((0 : ℕ) : ℝ)) ^ 2 : ℝ) = 0 := by norm_num
    rw [h0]
    exact tendsto_const_nhds
  · have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    -- sin y / y → 1 as y → 0 (through nonzero values)
    have hslope : Filter.Tendsto (fun y : ℝ => Real.sin y / y) (𝓝[≠] (0 : ℝ)) (nhds 1) := by
      have h := Real.hasDerivAt_sin 0
      rw [Real.cos_zero] at h
      have h2 := hasDerivAt_iff_tendsto_slope.mp h
      refine h2.congr ?_
      intro y
      rw [slope_def_field]
      simp
    -- x_N = πk/N → 0 within nonzero values
    have hx0 : Filter.Tendsto (fun N : ℕ => Real.pi * (k : ℝ) / (N : ℝ)) Filter.atTop
        (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat (Real.pi * (k : ℝ))
    have hxmem : ∀ᶠ N : ℕ in Filter.atTop,
        Real.pi * (k : ℝ) / (N : ℝ) ∈ ({0}ᶜ : Set ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hpos : 0 < Real.pi * (k : ℝ) / (N : ℝ) :=
        div_pos (mul_pos Real.pi_pos hk') hNpos
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hpos
    have hx : Filter.Tendsto (fun N : ℕ => Real.pi * (k : ℝ) / (N : ℝ)) Filter.atTop
        (𝓝[≠] (0 : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hx0 hxmem
    have hcomp := hslope.comp hx
    simp only [Function.comp_def] at hcomp
    have hmul : Filter.Tendsto
        (fun N : ℕ => (2 * Real.pi * (k : ℝ)) ^ 2
          * (Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) / (Real.pi * (k : ℝ) / (N : ℝ))) ^ 2)
        Filter.atTop (nhds ((2 * Real.pi * (k : ℝ)) ^ 2 * 1 ^ 2)) :=
      tendsto_const_nhds.mul (hcomp.pow 2)
    rw [one_pow, mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hπk : Real.pi * (k : ℝ) ≠ 0 := ne_of_gt (mul_pos Real.pi_pos hk')
    simp only [discreteEigenvalue]
    field_simp
    ring

/-- THEOREM (raw form of the convergence, as in the campaign brief; axis
sector only, see the scope note on `discreteEigenvalue_tendsto`). -/
theorem discrete_eigenvalue_tendsto_raw (k : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => 4 * (N : ℝ) ^ 2 * Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) ^ 2)
      Filter.atTop (nhds ((2 * Real.pi * (k : ℝ)) ^ 2)) :=
  discreteEigenvalue_tendsto k

/-! ## 3D TT layer: lattice tensor fields on the 3-torus -/

/-- 3D lattice site (periodic interpretation: the flat 3-torus). -/
abbrev Site3 : Type := ℤ × ℤ × ℤ

/-- Lattice tensor field: a `3 × 3` complex matrix at every lattice site. -/
abbrev LatticeTensorField : Type := Site3 → Matrix (Fin 3) (Fin 3) ℂ

/-- Lattice unit vectors along the three axes. -/
def unitVec : Fin 3 → Site3
  | 0 => (1, 0, 0)
  | 1 => (0, 1, 0)
  | 2 => (0, 0, 1)

@[simp] lemma fst_add_e0 (x : Site3) : (x + unitVec 0).1 = x.1 + 1 := rfl
@[simp] lemma fst_sub_e0 (x : Site3) : (x - unitVec 0).1 = x.1 - 1 := rfl
@[simp] lemma fst_add_e1 (x : Site3) : (x + unitVec 1).1 = x.1 := add_zero _
@[simp] lemma fst_sub_e1 (x : Site3) : (x - unitVec 1).1 = x.1 := sub_zero _
@[simp] lemma fst_add_e2 (x : Site3) : (x + unitVec 2).1 = x.1 := add_zero _
@[simp] lemma fst_sub_e2 (x : Site3) : (x - unitVec 2).1 = x.1 := sub_zero _

/-- Forward-difference discrete divergence of a lattice tensor field:
`(div H) x b = Σ_a N (H(x + e_a) a b - H(x) a b)`. -/
noncomputable def discDiv (N : ℕ) (H : LatticeTensorField) : Site3 → Fin 3 → ℂ :=
  fun x b => ∑ a : Fin 3, (N : ℂ) * (H (x + unitVec a) a b - H x a b)

/-- 3D discrete Laplacian, componentwise sum of the three 1D stencils. -/
noncomputable def discLap3 (N : ℕ) (H : LatticeTensorField) : LatticeTensorField :=
  fun x => Matrix.of fun i j =>
    ∑ a : Fin 3, (N : ℂ) ^ 2 *
      (H (x + unitVec a) i j - 2 * H x i j + H (x - unitVec a) i j)

/-- Axis plane wave `k = (k, 0, 0)`: the 1D Fourier mode in the first
coordinate times a constant polarization matrix. -/
noncomputable def planeH (N : ℕ) (k : ℤ) (eps : Matrix (Fin 3) (Fin 3) ℂ) :
    LatticeTensorField :=
  fun x => fourierMode N k x.1 • eps

lemma planeH_apply (N : ℕ) (k : ℤ) (eps : Matrix (Fin 3) (Fin 3) ℂ)
    (x : Site3) (i j : Fin 3) :
    planeH N k eps x i j = fourierMode N k x.1 * eps i j := by
  simp [planeH, Matrix.smul_apply, smul_eq_mul]

/-- THEOREM. The axis plane wave is periodic along the wave axis with period
`N` (torus grounding). -/
theorem planeH_periodic_axis (N : ℕ) (k : ℤ) (eps : Matrix (Fin 3) (Fin 3) ℂ)
    (x : Site3) :
    planeH N k eps (x + ((N : ℤ), 0, 0)) = planeH N k eps x := by
  show fourierMode N k (x.1 + (N : ℤ)) • eps = fourierMode N k x.1 • eps
  rw [fourierMode_periodic N k x.1]

/-- THEOREM. The axis plane wave is invariant under arbitrary shifts in the
transverse (y, z) directions; in particular it is periodic along those axes. -/
theorem planeH_shift_yz (N : ℕ) (k : ℤ) (eps : Matrix (Fin 3) (Fin 3) ℂ)
    (x : Site3) (s t : ℤ) :
    planeH N k eps (x + ((0 : ℤ), s, t)) = planeH N k eps x := by
  show fourierMode N k (x.1 + 0) • eps = fourierMode N k x.1 • eps
  rw [add_zero]

/-- THEOREM (discrete transversality). For a polarization with vanishing
first row, the axis plane wave is exactly discrete-transverse: the
forward-difference divergence vanishes identically. Only the `a = 0` term
could contribute (the mode is constant in `y, z`), and `eps 0 b = 0` kills it. -/
theorem planeH_transverse (N : ℕ) (k : ℤ) (eps : Matrix (Fin 3) (Fin 3) ℂ)
    (hrow : ∀ j, eps 0 j = 0) (x : Site3) (b : Fin 3) :
    discDiv N (planeH N k eps) x b = 0 := by
  simp only [discDiv, Fin.sum_univ_three, planeH_apply,
    fst_add_e0, fst_add_e1, fst_add_e2, hrow]
  ring

/-- THEOREM (3D eigenvector identity). The axis plane wave is an eigenvector
of the 3D discrete Laplacian with the SAME eigenvalue as the 1D mode: the
`y, z` stencils act trivially on a mode constant in `y, z`. -/
theorem discLap3_planeH (N : ℕ) (k : ℤ) (eps : Matrix (Fin 3) (Fin 3) ℂ)
    (x : Site3) :
    discLap3 N (planeH N k eps) x
      = (-(4 * (N : ℝ) ^ 2 * Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) ^ 2))
          • planeH N k eps x := by
  ext i j
  simp only [discLap3, Matrix.of_apply, Fin.sum_univ_three, planeH_apply,
    fst_add_e0, fst_sub_e0, fst_add_e1, fst_sub_e1, fst_add_e2, fst_sub_e2,
    Matrix.smul_apply, Complex.real_smul]
  have h1d := discLap_fourierMode_apply N k x.1
  simp only [discLap] at h1d
  linear_combination eps i j * h1d

/-! ## Standard TT polarizations -/

/-- Plus polarization: `diag(0, 1, -1)`. -/
def epsPlus : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 1, 0; 0, 0, -1]

/-- Cross polarization: `E₂₃ + E₃₂`. -/
def epsCross : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, 1; 0, 1, 0]

theorem epsPlus_isSymm : epsPlus.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsPlus]

theorem epsCross_isSymm : epsCross.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epsCross]

theorem epsPlus_traceless : Matrix.trace epsPlus = 0 := by
  rw [Matrix.trace_fin_three]
  show (0 : ℂ) + 1 + (-1) = 0
  norm_num

theorem epsCross_traceless : Matrix.trace epsCross = 0 := by
  rw [Matrix.trace_fin_three]
  show (0 : ℂ) + 0 + 0 = 0
  norm_num

theorem epsPlus_row0 : ∀ j, epsPlus 0 j = 0 := by
  intro j
  fin_cases j <;> simp [epsPlus]

theorem epsCross_row0 : ∀ j, epsCross 0 j = 0 := by
  intro j
  fin_cases j <;> simp [epsCross]

theorem epsPlus_col0 : ∀ i, epsPlus i 0 = 0 := by
  intro i
  fin_cases i <;> simp [epsPlus]

theorem epsCross_col0 : ∀ i, epsCross i 0 = 0 := by
  intro i
  fin_cases i <;> simp [epsCross]

/-- THEOREM. The two standard polarizations are linearly independent over ℂ:
they span the 2D TT polarization space for the axis wave. -/
theorem polarizations_linearIndependent :
    LinearIndependent ℂ ![epsPlus, epsCross] := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have h12 : (![epsPlus, epsCross] 1) 1 2 = (0 : Matrix (Fin 3) (Fin 3) ℂ) 1 2 := by
      rw [h]
    have e1 : (![epsPlus, epsCross] 1) 1 2 = (1 : ℂ) := rfl
    have e2 : ((0 : Matrix (Fin 3) (Fin 3) ℂ) 1 2 : ℂ) = 0 := rfl
    rw [e1, e2] at h12
    exact one_ne_zero h12
  · intro a h
    have h11 : (a • ![epsPlus, epsCross] 1) 1 1 = (![epsPlus, epsCross] 0) 1 1 := by
      rw [h]
    have e1 : (a • ![epsPlus, epsCross] 1) 1 1 = a * 0 := rfl
    have e2 : ((![epsPlus, epsCross] 0) 1 1 : ℂ) = 1 := rfl
    rw [e1, e2, mul_zero] at h11
    exact zero_ne_one h11

/-! ## Flat Lichnerowicz connection (MODEL layer) -/

/-- Continuum plane-wave profile along the wave axis: `t ↦ exp(2πik t)`. -/
noncomputable def continuumProfile (k : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (t : ℂ))

/-- Continuum TT plane wave on the unit 3-torus (axis mode `k = (k,0,0)`). -/
noncomputable def continuumPlaneH (k : ℕ) (eps : Matrix (Fin 3) (Fin 3) ℂ) :
    (ℝ × ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℂ :=
  fun x => continuumProfile k x.1 • eps

/-- THEOREM. First derivative of the continuum profile. -/
theorem continuumProfile_hasDerivAt (k : ℕ) (t : ℝ) :
    HasDerivAt (continuumProfile k)
      (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * continuumProfile k t) t := by
  have hlin : HasDerivAt (fun s : ℝ => 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((s : ℝ) : ℂ))
      (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul
      (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))
  have hcomm : 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * continuumProfile k t
      = continuumProfile k t * (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) := mul_comm _ _
  rw [hcomm]
  exact hlin.cexp

/-- THEOREM. Second derivative of the continuum profile: `-(2πk)²` times the
profile. So `(2πk)²` is the genuine `-d²/dt²` eigenvalue of the continuum
mode along the wave direction (the mode is constant in the transverse
directions). -/
theorem continuumProfile_second_deriv (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * continuumProfile k s)
      (((-((2 * Real.pi * (k : ℝ)) ^ 2) : ℝ) : ℂ) * continuumProfile k t) t := by
  have h := (continuumProfile_hasDerivAt k t).const_mul
    (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))
  have heq : ((-((2 * Real.pi * (k : ℝ)) ^ 2) : ℝ) : ℂ) * continuumProfile k t
      = 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)
        * (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * continuumProfile k t) := by
    push_cast
    linear_combination (-4 * (Real.pi : ℂ) ^ 2 * (k : ℂ) ^ 2 * continuumProfile k t)
      * Complex.I_sq
  rw [heq]
  exact h

/-- MODEL. Flat-background Lichnerowicz eigenvalue on the wavenumber-`k` TT
plane wave: `(2πk)²`.

Justification (why this is the honest definition): the Lichnerowicz operator
on a Ricci-flat background acts on TT perturbations as
`Δ_L h_ab = -∇² h_ab - 2 R_acbd h^cd`. On the FLAT 3-torus the Riemann
tensor vanishes identically, so `Δ_L` reduces to `-∇²` (minus the flat
Laplacian) on TT tensors. The TT plane wave with wavenumber `k` along an
axis of the unit torus has `-∇²` eigenvalue `(2πk)²`; the along-axis part of
this is PROVED above (`continuumProfile_second_deriv`), and the transverse
derivatives vanish because the mode is constant in `y, z`. No curved-space
geometry is formalized here; this definition encodes the flat reduction
only. -/
noncomputable def lichnerowiczFlatEigenvalue (k : ℕ) : ℝ :=
  (2 * Real.pi * (k : ℝ)) ^ 2

/-! ## Package theorem -/

/-- THEOREM + MODEL (package; AXIS SECTOR ONLY). For every wavenumber `k`
and every polarization `eps` with vanishing first row (in particular
`epsPlus`, `epsCross`):

1. the discrete axis plane wave is exactly discrete-transverse at every
   lattice resolution `N`;
2. it is an eigenvector of the 3D discrete Laplacian with eigenvalue
   `-(discreteEigenvalue N k)` at every resolution;
3. the discrete (minus-Laplacian) eigenvalues converge, as the lattice is
   refined, to `(2πk)²` = the flat Lichnerowicz eigenvalue (MODEL
   identification; see `lichnerowiczFlatEigenvalue`).

Items 1-2 and the convergence in 3 are proved; only the name
"Lichnerowicz" on the limit is the MODEL layer.

Scope caveat (panel mandate C14, 2026-07-15): everything here lives in the
AXIS stencil sector, `k = (k, 0, 0)` with the componentwise axis-stencil
Laplacian. Test G (`FreudenthalStencilPreflight`/`FreudenthalEnergyLimit`,
commits 7b808f75b4, 1d3ed6da06) kernel-proved the canonical Freudenthal
frozen quadratic energy has the ANISOTROPIC continuum moment tensor
`A₀ = (1+√2)I + (√2+√3)J` (body diagonal ~4.9x stiffer), which the axis
sector cannot detect. This theorem must therefore NOT be read as isotropic
flat-space recovery of the full Lichnerowicz spectrum; the
direction-resolved symbol question is governed by the C10 probe (plan
receipt P-iso, 2026-07-15). -/
theorem discrete_tt_spectrum_converges_to_flat_lichnerowicz
    (k : ℕ) (eps : Matrix (Fin 3) (Fin 3) ℂ) (hrow : ∀ j, eps 0 j = 0) :
    (∀ (N : ℕ) (x : Site3) (b : Fin 3),
        discDiv N (planeH N (k : ℤ) eps) x b = 0)
    ∧ (∀ (N : ℕ) (x : Site3),
        discLap3 N (planeH N (k : ℤ) eps) x
          = (-(discreteEigenvalue N k)) • planeH N (k : ℤ) eps x)
    ∧ Filter.Tendsto (fun N : ℕ => discreteEigenvalue N k) Filter.atTop
        (nhds (lichnerowiczFlatEigenvalue k)) := by
  refine ⟨fun N x b => planeH_transverse N (k : ℤ) eps hrow x b, fun N x => ?_, ?_⟩
  · have h := discLap3_planeH N (k : ℤ) eps x
    have hcast : (-(discreteEigenvalue N k) : ℝ)
        = -(4 * (N : ℝ) ^ 2 * Real.sin (Real.pi * ((k : ℤ) : ℝ) / (N : ℝ)) ^ 2) := by
      simp [discreteEigenvalue]
    rw [hcast]
    exact h
  · exact discreteEigenvalue_tendsto k

/-! ## Status flags (scoped claim; what remains OPEN) -/

/-- Status record for the "operator convergence" gap. -/
structure OperatorConvergenceStatus where
  /-- Flat 3-torus TT convergence: proved in this file for the AXIS stencil
  sector only (`k = (k,0,0)` modes of the axis-stencil Laplacian). NOT
  isotropic flat-space recovery: Test G kernel-proved the full moment tensor
  is anisotropic, `A₀ = (1+√2)I + (√2+√3)J`. -/
  flat_tt_convergence_proved : Bool
  /-- Curved backgrounds (Schwarzschild, Kerr): NOT formalized; OPEN. -/
  curved_background_open : Bool
  /-- Quasinormal-mode spectra: NOT formalized; OPEN. -/
  qnm_spectrum_open : Bool

/-- The scoped claim of this file, stated plainly: the discrete-to-continuum
operator convergence is PROVED on the flat 3-torus for TT AXIS modes only
(eigenvalue identity at every resolution + spectral convergence to the flat
Lichnerowicz eigenvalue `(2πk)²` on that sector). This is an axis-sector
statement, not isotropic flat-space recovery: Test G
(`FreudenthalStencilPreflight`/`FreudenthalEnergyLimit`, commits 7b808f75b4,
1d3ed6da06) kernel-proved the anisotropic moment tensor
`A₀ = (1+√2)I + (√2+√3)J`; the direction-resolved symbol question is
governed by the C10 probe (plan receipt P-iso, 2026-07-15). Curved
backgrounds and quasinormal-mode spectra remain OPEN: nothing in this file
(and nothing genuine elsewhere in the repository) formalizes them. -/
def status : OperatorConvergenceStatus :=
  { flat_tt_convergence_proved := true
    curved_background_open := true
    qnm_spectrum_open := true }

theorem status_flat_tt_convergence_proved :
    status.flat_tt_convergence_proved = true := rfl

theorem status_curved_background_open :
    status.curved_background_open = true := rfl

theorem status_qnm_spectrum_open :
    status.qnm_spectrum_open = true := rfl

end DiscreteLichnerowicz
end SevenGaps
end Gravity
end IndisputableMonolith
