import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.PhiSupport.Lemmas
import IndisputableMonolith.Cosmology.DarkEnergyWofZStructural
import IndisputableMonolith.Cosmology.BITKernelShapeForcing

/-!
# T9: The Forced Measure on Recognition States

## The problem this module closes

The T-1..T8 chain forces the *shape* of the law: J is the unique cost, φ the
unique scale, 2³ the minimal period, D = 3 the unique dimension. What the
chain did not force is the *weighting*: given the allowed recognition
states, which rule says how much of reality sits in each one? Every
recurring open instance-selection problem in the library (Born weights,
chirality selection, δw₀ saturation, η_B prefactor, rung occupancy) is a
projection of that single missing primitive.

This module derives the rule. **Any admissible weighting of recognition
states is the geometric φ-measure: weight φ⁻¹ per recognition step,
equivalently probability ∝ exp(−(ln φ) · cost)** — the Gibbs rule with the
rate pinned by the self-similar ledger, not chosen.

## The derivation (same machinery that forced J, θ = φ⁻⁴, and K(z))

Lattice layer (recognition is discrete, T2, so this is the fundamental
layer). A weight rule satisfies exactly two premises:

1. **Factorization over independent composition** (`factorizes`). The
   weight of a composite of independent recognition steps is the product of
   the weights. This is the multiplicative shadow of ledger cost
   additivity: a non-factorizing weight would carry correlation with no
   posting that pays for it.
2. **Per-step self-similar balance** (`step_self_similar`). The single-step
   weight satisfies ρ = 1/(1+ρ), the reciprocal self-similarity fixed
   point. By `BITKernelShapeForcing.self_similar_attenuation_forced`
   this forces ρ = φ⁻¹: the only balance equation available to the ledger
   is the fixed point of its own forced reciprocal-shift generator; any
   other ratio imports a second scale, contradicting T6 uniqueness.

These force `w(n) = φ⁻ⁿ` (`RecognitionWeightRule.weight_forced`) — by
literally the same proof as the BIT kernel rung dilution; the conversion
`toRungDilution` exhibits the two objects as identical.

Continuum layer. For weight as a function of a real-valued additive cost,
the premises are factorization over cost addition, antitonicity, and the
calibrated step `f(1) = φ⁻¹`. The theorem `continuum_weight_forced` proves
`f(t) = φ⁻ᵗ` for ALL t ≥ 0 — not merely within a power-law class: the
multiplicative Cauchy equation plus monotonicity pins the function on the
rationals by roots and on the irrationals by an elementary squeeze. This
removes the scale-free-class caveat that the kernel module still carried.

Gibbs form. `φ⁻ᵗ = exp(−(ln φ)·t)` (`contWeight_gibbs`): probability
∝ exp(−cost) with the recognition temperature pinned at 1/ln φ in rung
units. The *form* is forced by factorization; the *rate* by the
self-similar step. Nothing is fitted.

## Structure constants of the forced measure (all THEOREM)

* Partition function: `Z = Σ φ⁻ⁿ = φ²` (`partitionZ_eq_phi_sq`). The
  normalization of the forced measure is φ²; the numerical identity is
  proved here.
* Ground-state share: `P(0) = φ⁻²` (`probMass_zero`).
* Mean occupied rung: `⟨n⟩ = φ` exactly (`meanRung_eq_phi`).

## What the measure does and does not select (honest tags)

* **Chirality (negative result, THEOREM).** The measure is cost-sufficient:
  equal-cost mirror states get equal weight (`weight_blind_to_label`). So
  chirality selection CANNOT come from the forced measure at equal J; it
  requires a J-asymmetry or spontaneous (history) breaking. This sharpens
  the mass-derivation program by closing one road.
* **Born rule (OPEN, with a proved regime).** Near the identity tick the
  forced measure is sub-Gaussian in log-deviation with rate λ/2
  (`sub_gaussian_in_J`), via J(eᵗ) = cosh t − 1 ≥ t²/2. This is the L²
  seed; the full Born bridge to recognition Hilbert space is OPEN
  (closing path: Gaussian regime + the spectral structural identity).
* **δw₀ (reduced from a free real to one integer, CONDITIONAL).** Under
  equilibrium occupancy of rungs 0..N, the BIT today-amplitude is
  `δw₀(N) = J(φ)·(1 − φ^{−(N+1)})` (`deltaW0`); monotone, `< J(φ)`,
  `→ J(φ)`. For any N it exceeds 0.04 (`deltaW0_gt_004`), and for N ≥ 8 it
  is within 5% of the ceiling (`deltaW0_near_ceiling`), giving the dated
  equilibrium prediction `w₀ ∈ (−0.896, −0.88)` (`equilibrium_w0_band`).
  CONDITIONAL on the equilibrium reading (H-theorem OPEN, below).
* **H-theorem (OPEN, named).** T9 forces the unique *stationary*
  weighting. That R̂ evolution converges to it (monotone approach = the RS
  second law) is the remaining dynamical theorem; until it lands, the
  aging/cosmology column's monotone-Z premises remain premises.

## Identifications (the existing constants are this measure)

`θ = φ⁻⁴ = w(4)` (`theta_is_lattice_weight`), `ℏ = φ⁻⁵ = w(5)`
(`hbar_is_lattice_weight`), rung-44 scale `φ⁻⁴⁴ = w(44)`
(`rung44_is_lattice_weight`), BIT kernel dilution `occ(n) = w(n)`
(`kernel_dilution_is_measure`); the full repository additionally identifies
the dimension dilution (`dimension_dilution_is_measure`, outside this
slice). Previously separate "dilution" and "occupancy" laws are one
object: the forced measure.

## Status

THEOREM: lattice forcing, continuum forcing (full Cauchy + monotone
uniqueness), Gibbs form, Z = φ², ⟨n⟩ = φ, sub-Gaussian regime, label
blindness, δw₀ reduction theorems, all identifications.
HYPOTHESIS: the per-step balance premise (third instantiation of the
self-similar-attenuation family: θ, kernel, measure; falsifier: any
forced-rung sector with per-rung weight ≠ φ⁻¹).
OPEN: H-theorem (R̂ convergence to the forced measure); Born bridge;
the cosmic rung count N.

Proposed as **T9** in the forcing chain; wiring into
`UnifiedForcingChain` is left as an explicit follow-up decision.
Zero `sorry`, zero new `axiom`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MeasureForcing

open Constants
open Cost

noncomputable section

/-! ## §0. The step weight -/

/-- The forced per-step weight `ρ = φ⁻¹`. -/
def rho : ℝ := 1 / Constants.phi

theorem rho_pos : 0 < rho := by
  unfold rho
  exact div_pos one_pos phi_pos

theorem rho_nonneg : 0 ≤ rho := rho_pos.le

theorem rho_lt_one : rho < 1 := by
  unfold rho
  rw [div_lt_one phi_pos]
  exact one_lt_phi

theorem rho_le_one : rho ≤ 1 := rho_lt_one.le

theorem rho_ne_one : rho ≠ 1 := ne_of_lt rho_lt_one

/-- Golden identity for the measure: `1 − ρ = φ⁻²`. The normalization gap
of the forced measure is the inverse-square of the scale. -/
theorem one_sub_rho : 1 - rho = 1 / Constants.phi ^ 2 := by
  unfold rho
  have hphi : Constants.phi ≠ 0 := phi_ne_zero
  have hsq : Constants.phi ^ 2 = Constants.phi + 1 := PhiSupport.phi_squared
  field_simp
  nlinarith [hsq]

/-- The lattice weight: `w(n) = φ⁻ⁿ` after `n` recognition steps. -/
def latticeWeight (n : ℕ) : ℝ := (1 / Constants.phi) ^ n

theorem latticeWeight_eq_rho_pow (n : ℕ) : latticeWeight n = rho ^ n := rfl

theorem latticeWeight_pos (n : ℕ) : 0 < latticeWeight n :=
  pow_pos rho_pos n

/-! ## §1. The lattice layer: the weight rule is forced

Two premises (factorization; per-step self-similar balance), identical in
form to the rung-dilution premises that force `θ = φ⁻⁴` and the BIT
kernel. The conversion `toRungDilution` makes the identity literal. -/

/-- A **recognition weight rule**: a positive weight per number of
recognition steps, factorizing over independent composition, with the
single-step weight satisfying the reciprocal self-similar balance. -/
structure RecognitionWeightRule where
  /-- Weight of a state reached by `n` recognition steps. -/
  w : ℕ → ℝ
  /-- Weights are strictly positive. -/
  w_pos : ∀ n, 0 < w n
  /-- **Factorization.** Independent composition multiplies weights
  (multiplicative shadow of ledger cost additivity; unpaid correlation is
  forbidden). -/
  factorizes : ∀ m n : ℕ, w (m + n) = w m * w n
  /-- **Per-step self-similar balance.** The single-step weight is the
  reciprocal self-similarity fixed point `ρ = 1/(1+ρ)` — the only balance
  equation expressible with the ledger's forced reciprocal-shift
  generator. -/
  step_self_similar : w 1 = 1 / (1 + w 1)

namespace RecognitionWeightRule

/-- A weight rule IS a rung dilution (the kernel object): the premises are
field-for-field identical. -/
def toRungDilution (R : RecognitionWeightRule) :
    Cosmology.BITKernelShapeForcing.RungDilution where
  occ := R.w
  occ_pos := R.w_pos
  composes := R.factorizes
  one_rung_self_similar := R.step_self_similar

/-- **T9, LATTICE LAYER: the weight rule is forced to `φ⁻ⁿ`.** -/
theorem weight_forced (R : RecognitionWeightRule) (n : ℕ) :
    R.w n = latticeWeight n :=
  (R.toRungDilution).occ_forced n

/-- Any two weight rules agree everywhere: there is exactly one measure. -/
theorem weight_unique (R S : RecognitionWeightRule) (n : ℕ) :
    R.w n = S.w n := by
  rw [R.weight_forced n, S.weight_forced n]

end RecognitionWeightRule

/-! ## §2. Structure constants of the forced measure -/

/-- The partition function `Z = Σ_{n≥0} φ⁻ⁿ`. -/
def partitionZ : ℝ := ∑' n : ℕ, rho ^ n

/-- **`Z = φ²` exactly.** The normalization of the forced measure is the
square of the forced scale (numerically the same φ² that gates emergent
voice density; that identification is a BRIDGE observation, the identity
here is THEOREM). -/
theorem partitionZ_eq_phi_sq : partitionZ = Constants.phi ^ 2 := by
  unfold partitionZ
  rw [tsum_geometric_of_lt_one rho_nonneg rho_lt_one, one_sub_rho]
  rw [one_div, inv_inv]

/-- The normalized probability mass at `n` steps: `P(n) = (1−ρ)·ρⁿ`. -/
def probMass (n : ℕ) : ℝ := (1 - rho) * rho ^ n

theorem probMass_pos (n : ℕ) : 0 < probMass n := by
  unfold probMass
  have h1 : 0 < 1 - rho := by linarith [rho_lt_one]
  exact mul_pos h1 (pow_pos rho_pos n)

/-- The measure is normalized: `Σ P(n) = 1`. -/
theorem probMass_tsum_one : ∑' n : ℕ, probMass n = 1 := by
  unfold probMass
  rw [tsum_mul_left, tsum_geometric_of_lt_one rho_nonneg rho_lt_one]
  have h1 : 1 - rho ≠ 0 := by
    have := rho_lt_one; intro h; linarith [sub_eq_zero.mp h]
  field_simp

/-- The ground-state share is `φ⁻²`. -/
theorem probMass_zero : probMass 0 = 1 / Constants.phi ^ 2 := by
  unfold probMass
  rw [pow_zero, mul_one, one_sub_rho]

/-- The mean occupied rung `⟨n⟩ = Σ n·P(n)`. -/
def meanRung : ℝ := ∑' n : ℕ, (n : ℝ) * probMass n

/-- **`⟨n⟩ = φ` exactly.** The mean recognition depth of the forced
measure is the golden ratio itself. -/
theorem meanRung_eq_phi : meanRung = Constants.phi := by
  unfold meanRung
  have hre : (fun n : ℕ => (n : ℝ) * probMass n)
      = fun n : ℕ => (1 - rho) * ((n : ℝ) * rho ^ n) := by
    funext n; unfold probMass; ring
  rw [hre, tsum_mul_left]
  have hnorm : ‖rho‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos rho_pos]; exact rho_lt_one
  rw [tsum_coe_mul_geometric_of_norm_lt_one hnorm]
  -- (1 − ρ) · ρ/(1−ρ)² = ρ/(1−ρ) = φ⁻¹·φ² = φ
  rw [one_sub_rho]
  unfold rho
  have hphi : Constants.phi ≠ 0 := phi_ne_zero
  field_simp

/-! ## §3. The continuum layer: full Cauchy + monotone uniqueness

Weight as a function of a real additive cost. Factorization +
antitonicity + the calibrated step force `f(t) = ρᵗ` for ALL `t ≥ 0`,
with no power-law-class restriction: rationals by roots, irrationals by
an elementary order squeeze. -/

section Continuum

variable {f : ℝ → ℝ}

/-- Factorization over cost addition on the nonneg domain. -/
def Factorizes (f : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → f (a + b) = f a * f b

theorem f_zero (hadd : Factorizes f)
    (hanti : AntitoneOn f (Set.Ici 0)) (hstep : f 1 = rho) :
    f 0 = 1 := by
  have h00 : f 0 = f 0 * f 0 := by
    have := hadd 0 0 le_rfl le_rfl
    simpa using this
  have hge : rho ≤ f 0 := by
    have h := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one)
      zero_le_one
    rwa [hstep] at h
  have hpos : 0 < f 0 := lt_of_lt_of_le rho_pos hge
  have hfac : f 0 * (f 0 - 1) = 0 := by nlinarith [h00]
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd h (ne_of_gt hpos)
  · linarith [sub_eq_zero.mp h]

theorem f_nmul (hadd : Factorizes f)
    (hanti : AntitoneOn f (Set.Ici 0)) (hstep : f 1 = rho)
    (x : ℝ) (hx : 0 ≤ x) :
    ∀ k : ℕ, f ((k : ℝ) * x) = f x ^ k := by
  intro k
  induction k with
  | zero => simpa using f_zero hadd hanti hstep
  | succ k ih =>
      have harg : ((k + 1 : ℕ) : ℝ) * x = (k : ℝ) * x + x := by
        push_cast; ring
      have hkx : 0 ≤ (k : ℝ) * x := by positivity
      rw [harg, hadd _ _ hkx hx, ih, pow_succ]

theorem f_nonneg_of_nonneg (hadd : Factorizes f)
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f x := by
  have hh := hadd (x / 2) (x / 2) (by positivity) (by positivity)
  have harg : x / 2 + x / 2 = x := by ring
  rw [harg] at hh
  rw [hh]
  exact mul_self_nonneg _

/-- The rational case: `f(p/q) = ρ^(p/q)` by uniqueness of positive
`q`-th roots. -/
theorem f_rat (hadd : Factorizes f)
    (hanti : AntitoneOn f (Set.Ici 0)) (hstep : f 1 = rho)
    (p q : ℕ) (hq : q ≠ 0) :
    f ((p : ℝ) / (q : ℝ)) = rho ^ ((p : ℝ) / (q : ℝ)) := by
  have hqR : ((q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  set x : ℝ := (p : ℝ) / (q : ℝ) with hxdef
  have hx0 : 0 ≤ x := by positivity
  -- f(x)^q = ρ^p
  have h1 : f ((q : ℝ) * x) = f x ^ q := f_nmul hadd hanti hstep x hx0 q
  have harg : (q : ℝ) * x = (p : ℝ) := by
    rw [hxdef]; field_simp
  have h2 : f ((p : ℝ)) = rho ^ p := by
    have := f_nmul hadd hanti hstep 1 zero_le_one p
    simpa [hstep] using this
  have hkey : f x ^ q = rho ^ p := by rw [← h1, harg, h2]
  -- (ρ^x)^q = ρ^p
  have hpow : (rho ^ x) ^ q = rho ^ p := by
    rw [← Real.rpow_natCast (rho ^ x) q, ← Real.rpow_mul rho_nonneg]
    have hmul : x * (q : ℝ) = (p : ℝ) := by rw [hxdef]; field_simp
    rw [hmul, Real.rpow_natCast]
  -- nonneg q-th roots agree
  have hfx : 0 ≤ f x := f_nonneg_of_nonneg hadd x hx0
  have hrx : 0 ≤ rho ^ x := Real.rpow_nonneg rho_nonneg x
  exact (pow_left_inj₀ hfx hrx hq).mp (hkey.trans hpow.symm)

/-- The rational case via the `ℚ`-cast. -/
theorem f_ratCast (hadd : Factorizes f)
    (hanti : AntitoneOn f (Set.Ici 0)) (hstep : f 1 = rho)
    (q : ℚ) (hq0 : 0 ≤ (q : ℝ)) :
    f ((q : ℝ)) = rho ^ ((q : ℝ)) := by
  have hq0' : 0 ≤ q := by exact_mod_cast hq0
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq0'
  have hden : q.den ≠ 0 := q.den_nz
  have hp : ((q.num.toNat : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  have hcast : ((q : ℝ)) = ((q.num.toNat : ℕ) : ℝ) / ((q.den : ℕ) : ℝ) := by
    rw [Rat.cast_def, hp]
  rw [hcast]
  exact f_rat hadd hanti hstep q.num.toNat q.den hden

/-- **T9, CONTINUUM LAYER (full uniqueness).** Any factorizing, antitone
weight with the calibrated step `f(1) = φ⁻¹` equals `φ⁻ᵗ` at every
`t ≥ 0`. No power-law-class restriction: this is the multiplicative
Cauchy equation pinned by monotonicity. -/
theorem continuum_weight_forced (hadd : Factorizes f)
    (hanti : AntitoneOn f (Set.Ici 0)) (hstep : f 1 = rho) :
    ∀ t : ℝ, 0 ≤ t → f t = rho ^ t := by
  intro t ht
  rcases eq_or_lt_of_le ht with h0 | hpos
  · rw [← h0, Real.rpow_zero]
    exact f_zero hadd hanti hstep
  -- t > 0. Set L := f t and squeeze with rationals.
  set L : ℝ := f t with hL
  -- upper rationals: t ≤ q ⇒ ρ^q ≤ L
  have hub : ∀ q : ℚ, t ≤ (q : ℝ) → rho ^ ((q : ℝ)) ≤ L := by
    intro q hq
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_trans hpos.le hq
    have := hanti (Set.mem_Ici.mpr hpos.le) (Set.mem_Ici.mpr hq0) hq
    rwa [f_ratCast hadd hanti hstep q hq0] at this
  -- lower rationals: 0 ≤ q ≤ t ⇒ L ≤ ρ^q
  have hlb : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ t → L ≤ rho ^ ((q : ℝ)) := by
    intro q hq0 hq
    have := hanti (Set.mem_Ici.mpr hq0) (Set.mem_Ici.mpr hpos.le) hq
    rwa [f_ratCast hadd hanti hstep q hq0] at this
  -- L > 0
  have hLpos : 0 < L := by
    obtain ⟨q, hq⟩ := exists_rat_gt t
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos rho_pos _) (hub q hq.le)
  have hrt_pos : 0 < rho ^ t := Real.rpow_pos_of_pos rho_pos t
  have hlogrho_neg : Real.log rho < 0 := Real.log_neg rho_pos rho_lt_one
  -- trichotomy
  rcases lt_trichotomy L (rho ^ t) with hlt | heq | hgt
  · -- L < ρ^t: find rational q > t with ρ^q > L. Contradiction with hub.
    exfalso
    have hlog : Real.log L < t * Real.log rho := by
      have := Real.log_lt_log hLpos hlt
      rwa [Real.log_rpow rho_pos] at this
    have hkey : t < Real.log L / Real.log rho := by
      rw [lt_div_iff_of_neg hlogrho_neg]
      linarith [hlog]
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hkey
    have hcontra : L < rho ^ ((q : ℝ)) := by
      have hq2' : Real.log L < (q : ℝ) * Real.log rho := by
        have := (lt_div_iff_of_neg hlogrho_neg).mp hq2
        linarith
      have : Real.exp (Real.log L) < Real.exp (Real.log rho * (q : ℝ)) := by
        rw [Real.exp_lt_exp]; linarith
      rwa [Real.exp_log hLpos, ← Real.rpow_def_of_pos rho_pos] at this
    exact absurd (hub q hq1.le) (not_le.mpr hcontra)
  · exact heq
  · -- L > ρ^t: find rational 0 ≤ q < t with ρ^q < L. Contradiction with hlb.
    exfalso
    have hlog : t * Real.log rho < Real.log L := by
      have := Real.log_lt_log hrt_pos hgt
      rwa [Real.log_rpow rho_pos] at this
    have hkey : Real.log L / Real.log rho < t := by
      rw [div_lt_iff_of_neg hlogrho_neg]
      linarith [hlog]
    have hmax : max (Real.log L / Real.log rho) 0 < t := max_lt hkey hpos
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hmax
    have hq0 : (0 : ℝ) ≤ (q : ℝ) :=
      le_of_lt (lt_of_le_of_lt (le_max_right _ _) hq1)
    have hcontra : rho ^ ((q : ℝ)) < L := by
      have hqgt : Real.log L / Real.log rho < (q : ℝ) :=
        lt_of_le_of_lt (le_max_left _ _) hq1
      have hq2' : (q : ℝ) * Real.log rho < Real.log L := by
        have := (div_lt_iff_of_neg hlogrho_neg).mp hqgt
        linarith
      have : Real.exp (Real.log rho * (q : ℝ)) < Real.exp (Real.log L) := by
        rw [Real.exp_lt_exp]; linarith
      rwa [Real.exp_log hLpos, ← Real.rpow_def_of_pos rho_pos] at this
    exact absurd (hlb q hq0 hq2.le) (not_le.mpr hcontra)

end Continuum

/-! ## §4. The Gibbs form: probability ∝ exp(−cost·ln φ) -/

/-- The forced continuum weight `w(t) = ρᵗ = φ⁻ᵗ`. -/
def contWeight (t : ℝ) : ℝ := rho ^ t

/-- The forced weight in inverse-φ-power form. -/
theorem contWeight_eq_phi_rpow_neg (t : ℝ) :
    contWeight t = Constants.phi ^ (-t) := by
  unfold contWeight rho
  rw [one_div, Real.inv_rpow phi_pos.le, ← Real.rpow_neg phi_pos.le]

/-- **THE GIBBS FORM.** The forced weight is the exponential of (−) the
cost, with the rate pinned at `ln φ` per recognition step:
`w(t) = exp(−(ln φ)·t)`. Probability ∝ exp(−cost), nothing fitted. -/
theorem contWeight_gibbs (t : ℝ) :
    contWeight t = Real.exp (-(Real.log Constants.phi) * t) := by
  unfold contWeight
  rw [Real.rpow_def_of_pos rho_pos]
  congr 1
  unfold rho
  rw [one_div, Real.log_inv]

/-- The forced weight satisfies all three continuum premises
(non-vacuity of the uniqueness theorem). -/
theorem contWeight_satisfies_premises :
    Factorizes contWeight ∧
    AntitoneOn contWeight (Set.Ici 0) ∧
    contWeight 1 = rho :=
  ⟨fun a b _ _ => Real.rpow_add rho_pos a b,
   fun _ _ _ _ hab => Real.rpow_le_rpow_of_exponent_ge rho_pos rho_le_one hab,
   Real.rpow_one rho⟩

/-! ## §5. The Born regime: the forced measure is sub-Gaussian in
log-deviation

`J(eᵗ) = cosh t − 1 ≥ t²/2`, so `exp(−λ·J)` is dominated by the Gaussian
`exp(−λt²/2)`. This is the L² seed of the Born bridge (the full bridge is
OPEN). -/

/-- The J-cost of a state at log-deviation `t`: `J(eᵗ) = cosh t − 1`. -/
theorem Jcost_exp_eq_cosh_sub_one (t : ℝ) :
    Cost.Jcost (Real.exp t) = Real.cosh t - 1 := by
  unfold Cost.Jcost
  rw [Real.cosh_eq, ← Real.exp_neg]

private lemma half_sq_le_cosh_sub_one_of_nonneg (s : ℝ) (hs : 0 ≤ s) :
    s ^ 2 / 2 ≤ Real.cosh s - 1 := by
  have hu : 0 ≤ s / 2 := by linarith
  have hsinh : s / 2 ≤ Real.sinh (s / 2) := Real.self_le_sinh_iff.mpr hu
  have hkey : Real.cosh s = 2 * Real.sinh (s / 2) ^ 2 + 1 := by
    have h2 : 2 * (s / 2) = s := by ring
    calc Real.cosh s = Real.cosh (2 * (s / 2)) := by rw [h2]
      _ = Real.cosh (s / 2) ^ 2 + Real.sinh (s / 2) ^ 2 :=
        Real.cosh_two_mul (s / 2)
      _ = (Real.sinh (s / 2) ^ 2 + 1) + Real.sinh (s / 2) ^ 2 := by
        rw [Real.cosh_sq]
      _ = 2 * Real.sinh (s / 2) ^ 2 + 1 := by ring
  nlinarith [hsinh, hu]

/-- `cosh t − 1 ≥ t²/2` for all real `t`. -/
theorem half_sq_le_cosh_sub_one (t : ℝ) :
    t ^ 2 / 2 ≤ Real.cosh t - 1 := by
  rcases le_or_gt 0 t with h | h
  · exact half_sq_le_cosh_sub_one_of_nonneg t h
  · have h' := half_sq_le_cosh_sub_one_of_nonneg (-t) (by linarith)
    rw [Real.cosh_neg] at h'
    calc t ^ 2 / 2 = (-t) ^ 2 / 2 := by ring
      _ ≤ Real.cosh t - 1 := h'

/-- **SUB-GAUSSIAN REGIME (the L² seed).** The forced measure at rate
`λ ≥ 0` in the J-coordinate is dominated by the Gaussian of variance
`1/λ` in log-deviation: `exp(−λ·J(eᵗ)) ≤ exp(−λt²/2)`. -/
theorem sub_gaussian_in_J (lam t : ℝ) (hlam : 0 ≤ lam) :
    Real.exp (-lam * Cost.Jcost (Real.exp t)) ≤
      Real.exp (-lam * (t ^ 2 / 2)) := by
  rw [Jcost_exp_eq_cosh_sub_one]
  rw [Real.exp_le_exp]
  have h := half_sq_le_cosh_sub_one t
  nlinarith [mul_le_mul_of_nonneg_left h hlam]

/-! ## §6. Identifications: the existing constants ARE this measure -/

/-- `θ = φ⁻⁴` is the forced measure at 4 steps. (Public slice: stated
against the defining display `1/φ⁴`; the full repository binds this value
to `Cosmology.DarkEnergyThetaPhiFour.thetaPhiFour`, which is definitionally
identical.) -/
theorem theta_is_lattice_weight :
    (1 : ℝ) / Constants.phi ^ 4 = latticeWeight 4 := by
  unfold latticeWeight
  rw [div_pow, one_pow]

/-- `ℏ = φ⁻⁵` is the forced measure at 5 steps. -/
theorem hbar_is_lattice_weight :
    Constants.hbar = latticeWeight 5 := by
  rw [Constants.hbar_eq_phi_inv_fifth]
  unfold latticeWeight
  rw [Real.rpow_neg phi_pos.le,
    show ((5 : ℝ)) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    div_pow, one_pow, one_div]

/-- The rung-44 scale `φ⁻⁴⁴` is the forced measure at 44 steps. -/
theorem rung44_is_lattice_weight :
    Cosmology.DarkEnergyWofZStructural.phi_neg_44 = latticeWeight 44 := by
  unfold Cosmology.DarkEnergyWofZStructural.phi_neg_44 latticeWeight
  rw [zpow_neg, show ((44 : ℤ)) = ((44 : ℕ) : ℤ) by norm_num,
    zpow_natCast, div_pow, one_pow, one_div]

/-- The BIT kernel rung dilution IS the forced measure. -/
theorem kernel_dilution_is_measure
    (L : Cosmology.BITKernelShapeForcing.RungDilution) (n : ℕ) :
    L.occ n = latticeWeight n :=
  L.occ_forced n

/- NOTE (public slice): the full repository additionally proves
`dimension_dilution_is_measure` (the `θ = φ⁻⁴` dimension-uniform dilution IS
the forced measure) against `Cosmology.DarkEnergyPhiDilutionDerivation`,
which is outside this slice. The lattice-layer instance retained above
(`kernel_dilution_is_measure`) carries the same forcing content via the
self-contained `BITKernelShapeForcing.RungDilution.occ_forced`. -/

/-! ## §7. Cost blindness: the measure cannot select chirality

The forced measure is a function of cost alone. Mirror configurations with
equal J receive equal weight, so chirality selection requires a J-asymmetry
or spontaneous (history) breaking — it CANNOT come from T9. This is a
proved negative result that closes one road for the mass-derivation program. -/

/-- A labeled recognition state: a cost plus a binary label (e.g. L/R
chirality). -/
structure LabeledState where
  cost : ℝ
  label : Bool

/-- A cost-sufficient weight on labeled states: the weight factors through
the cost (T9's cost-sufficiency premise). -/
structure CostSufficientWeight where
  w : LabeledState → ℝ
  cost_sufficient : ∀ s t : LabeledState, s.cost = t.cost → w s = w t

/-- **CHIRALITY NO-GO.** Any cost-sufficient weight assigns equal weight
to the two mirror labels at every cost. -/
theorem weight_blind_to_label (W : CostSufficientWeight) (c : ℝ) :
    W.w ⟨c, true⟩ = W.w ⟨c, false⟩ :=
  W.cost_sufficient _ _ rfl

/-! ## §8. The δw₀ reduction: from a free real to one integer

Under equilibrium occupancy of cosmic-Z rungs `0..N`, the BIT
today-amplitude is the measure-weighted saturation times the
phantom-Carnot ceiling. -/

/-- Closed form of `J(φ)` (public; the private copies elsewhere are not
importable). -/
theorem Jcost_phi_closed_form : Cost.Jcost Constants.phi = Constants.phi - 3 / 2 := by
  unfold Cost.Jcost
  have hphi : Constants.phi ≠ 0 := phi_ne_zero
  have hsq : Constants.phi ^ 2 = Constants.phi + 1 := PhiSupport.phi_squared
  field_simp
  nlinarith [sq_pos_of_pos phi_pos, hsq]

theorem Jcost_phi_gt_011 : 0.11 < Cost.Jcost Constants.phi := by
  rw [Jcost_phi_closed_form]
  linarith [phi_gt_onePointSixOne]

/-- The cumulative measure of rungs `0..N` (the Z-saturation fraction). -/
def saturation (N : ℕ) : ℝ := ∑ n ∈ Finset.range (N + 1), probMass n

/-- Closed form: `saturation N = 1 − ρ^(N+1)`. -/
theorem saturation_closed (N : ℕ) : saturation N = 1 - rho ^ (N + 1) := by
  unfold saturation probMass
  rw [← Finset.mul_sum, geom_sum_eq rho_ne_one]
  have h1 : rho - 1 ≠ 0 := by
    intro h; exact rho_ne_one (by linarith [sub_eq_zero.mp h])
  field_simp
  ring

theorem saturation_lt_one (N : ℕ) : saturation N < 1 := by
  rw [saturation_closed]
  have : 0 < rho ^ (N + 1) := pow_pos rho_pos _
  linarith

theorem saturation_monotone : Monotone saturation := by
  intro N M h
  rw [saturation_closed, saturation_closed]
  have hp : rho ^ (M + 1) ≤ rho ^ (N + 1) :=
    pow_le_pow_of_le_one rho_nonneg rho_le_one (by omega)
  linarith

/-- The saturation tends to 1: deep occupancy exhausts the measure. -/
theorem saturation_tendsto_one :
    Filter.Tendsto saturation Filter.atTop (nhds 1) := by
  have hfun : saturation = fun N => 1 - rho ^ (N + 1) :=
    funext saturation_closed
  rw [hfun]
  have hpow : Filter.Tendsto (fun N : ℕ => rho ^ (N + 1))
      Filter.atTop (nhds 0) := by
    have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one rho_nonneg rho_lt_one
    exact hbase.comp (Filter.tendsto_add_atTop_nat 1)
  have hsub : Filter.Tendsto (fun N : ℕ => 1 - rho ^ (N + 1))
      Filter.atTop (nhds (1 - 0)) :=
    Filter.Tendsto.sub tendsto_const_nhds hpow
  simpa using hsub

/-- The equilibrium BIT today-amplitude with occupancy depth `N`:
`δw₀(N) = J(φ)·saturation(N)`. The free real `δw₀` is reduced to one
integer. -/
def deltaW0 (N : ℕ) : ℝ := Cost.Jcost Constants.phi * saturation N

/-- `δw₀(N)` never reaches the ceiling. -/
theorem deltaW0_lt_ceiling (N : ℕ) :
    deltaW0 N < Cost.Jcost Constants.phi := by
  unfold deltaW0
  have hJ : 0 < Cost.Jcost Constants.phi := Constants.Jcost_phi_pos
  nlinarith [saturation_lt_one N]

/-- `δw₀(N) → J(φ)`: the ceiling is the deep-occupancy limit. -/
theorem deltaW0_tendsto_ceiling :
    Filter.Tendsto deltaW0 Filter.atTop (nhds (Cost.Jcost Constants.phi)) := by
  unfold deltaW0
  have := Filter.Tendsto.const_mul (Cost.Jcost Constants.phi) saturation_tendsto_one
  simpa using this

/-- Numerical step bound: `ρ < 0.6212`. -/
theorem rho_lt_06212 : rho < 0.6212 := by
  unfold rho
  rw [div_lt_iff₀ phi_pos]
  nlinarith [phi_gt_onePointSixOne]

/-- **Equilibrium excludes exact ΛCDM.** For ANY occupancy depth `N`,
`δw₀(N) > 0.04`: under the equilibrium reading the deviation cannot
vanish. A confirmed `|w₀ + 1| < 0.04` falsifies equilibrium T9 occupancy
(not T9 itself). -/
theorem deltaW0_gt_004 (N : ℕ) : 0.04 < deltaW0 N := by
  have hmono := saturation_monotone (Nat.zero_le N)
  have hsat0 : 0.37 < saturation 0 := by
    rw [saturation_closed]
    have : rho ^ (0 + 1) = rho := by ring
    rw [this]
    linarith [rho_lt_06212]
  have hJ := Jcost_phi_gt_011
  have hsat : 0.37 < saturation N := lt_of_lt_of_le hsat0 hmono
  unfold deltaW0
  nlinarith [hJ, hsat]

/-- Numerical: `ρ⁹ < 0.014` (so nine rungs of occupancy already exhaust
98.6% of the measure). -/
theorem rho_pow_nine_lt : rho ^ 9 < 0.014 := by
  have h1 : rho ^ 9 < 0.6212 ^ 9 :=
    pow_lt_pow_left₀ rho_lt_06212 rho_nonneg (by norm_num)
  have h2 : (0.6212 : ℝ) ^ 9 < 0.014 := by norm_num
  linarith

/-- **Near-ceiling saturation.** For `N ≥ 8`, `δw₀(N) > 0.95·J(φ)`:
equilibrium occupancy deeper than eight rungs pins the amplitude within
5% of the phantom-Carnot ceiling. -/
theorem deltaW0_near_ceiling (N : ℕ) (hN : 8 ≤ N) :
    0.95 * Cost.Jcost Constants.phi < deltaW0 N := by
  have hsat8 : 0.98 < saturation 8 := by
    rw [saturation_closed]
    have h9 : rho ^ (8 + 1) = rho ^ 9 := by norm_num
    rw [h9]
    linarith [rho_pow_nine_lt]
  have hmono := saturation_monotone hN
  have hsat : 0.98 < saturation N := lt_of_lt_of_le hsat8 hmono
  have hJ : 0 < Cost.Jcost Constants.phi := Constants.Jcost_phi_pos
  unfold deltaW0
  nlinarith [hJ, hsat]

/-- **THE DATED EQUILIBRIUM BAND (2026-06-09).** For occupancy `N ≥ 8`,
the equilibrium prediction is `w₀ = −1 + δw₀(N) ∈ (−0.896, −0.88)`.
CONDITIONAL on the equilibrium reading (H-theorem OPEN); jointly
falsified with it by DESI Y3+/Roman/Euclid outside the band. -/
theorem equilibrium_w0_band (N : ℕ) (hN : 8 ≤ N) :
    -0.896 < -1 + deltaW0 N ∧ -1 + deltaW0 N < -0.88 := by
  have hnear := deltaW0_near_ceiling N hN
  have hceil := deltaW0_lt_ceiling N
  have hJlo := Jcost_phi_gt_011
  have hJhi : Cost.Jcost Constants.phi < 0.12 :=
    Cosmology.BITKernelShapeForcing.jcost_phi_lt_012
  constructor
  · nlinarith
  · nlinarith

/-! ## §9. Master certificate and the T9 one-statement -/

/-- **T9 MASTER CERTIFICATE: THE FORCED MEASURE (dated 2026-06-09).**

1. Lattice forcing: every weight rule is `φ⁻ⁿ`.
2. Uniqueness: any two weight rules agree.
3. Continuum forcing: every factorizing antitone calibrated weight is
   `φ⁻ᵗ` (full Cauchy + monotone uniqueness, no class restriction).
4. Non-vacuity: the forced weight satisfies the premises.
5. Gibbs form: `w(t) = exp(−(ln φ)·t)`.
6. Partition function `Z = φ²`; ground share `φ⁻²`; mean rung `φ`.
7. Sub-Gaussian Born regime.
8. Cost blindness (chirality no-go).
9. The constants `θ = φ⁻⁴`, `ℏ = φ⁻⁵`, rung-44, and the kernel dilution
   are all instances of the one measure (the full repository adds the
   dimension dilution).
10. δw₀ reduction: bounded, monotone, `→ J(φ)`, `> 0.04` always, near
    ceiling for `N ≥ 8`. -/
structure MeasureForcingCert where
  lattice_forced :
    ∀ (R : RecognitionWeightRule) (n : ℕ), R.w n = latticeWeight n
  lattice_unique :
    ∀ (R S : RecognitionWeightRule) (n : ℕ), R.w n = S.w n
  continuum_forced :
    ∀ f : ℝ → ℝ, Factorizes f → AntitoneOn f (Set.Ici 0) → f 1 = rho →
      ∀ t : ℝ, 0 ≤ t → f t = rho ^ t
  nonvacuous :
    Factorizes contWeight ∧ AntitoneOn contWeight (Set.Ici 0) ∧
      contWeight 1 = rho
  gibbs_form :
    ∀ t : ℝ, contWeight t = Real.exp (-(Real.log Constants.phi) * t)
  partition_eq : partitionZ = Constants.phi ^ 2
  ground_share : probMass 0 = 1 / Constants.phi ^ 2
  mean_rung : meanRung = Constants.phi
  sub_gaussian :
    ∀ lam t : ℝ, 0 ≤ lam →
      Real.exp (-lam * Cost.Jcost (Real.exp t)) ≤
        Real.exp (-lam * (t ^ 2 / 2))
  chirality_no_go :
    ∀ (W : CostSufficientWeight) (c : ℝ),
      W.w ⟨c, true⟩ = W.w ⟨c, false⟩
  theta_instance :
    (1 : ℝ) / Constants.phi ^ 4 = latticeWeight 4
  hbar_instance : Constants.hbar = latticeWeight 5
  rung44_instance :
    Cosmology.DarkEnergyWofZStructural.phi_neg_44 = latticeWeight 44
  kernel_instance :
    ∀ (L : Cosmology.BITKernelShapeForcing.RungDilution) (n : ℕ),
      L.occ n = latticeWeight n
  delta_w0_window :
    ∀ N : ℕ, 0.04 < deltaW0 N ∧ deltaW0 N < Cost.Jcost Constants.phi
  delta_w0_equilibrium_band :
    ∀ N : ℕ, 8 ≤ N →
      -0.896 < -1 + deltaW0 N ∧ -1 + deltaW0 N < -0.88

/-- The master certificate is inhabited. -/
def measureForcingCert : MeasureForcingCert where
  lattice_forced := fun R n => R.weight_forced n
  lattice_unique := fun R S n => R.weight_unique S n
  continuum_forced := fun _ hadd hanti hstep => continuum_weight_forced hadd hanti hstep
  nonvacuous := contWeight_satisfies_premises
  gibbs_form := contWeight_gibbs
  partition_eq := partitionZ_eq_phi_sq
  ground_share := probMass_zero
  mean_rung := meanRung_eq_phi
  sub_gaussian := sub_gaussian_in_J
  chirality_no_go := weight_blind_to_label
  theta_instance := theta_is_lattice_weight
  hbar_instance := hbar_is_lattice_weight
  rung44_instance := rung44_is_lattice_weight
  kernel_instance := kernel_dilution_is_measure
  delta_w0_window := fun N => ⟨deltaW0_gt_004 N, deltaW0_lt_ceiling N⟩
  delta_w0_equilibrium_band := fun N hN => equilibrium_w0_band N hN

/-- **T9, ONE STATEMENT.** Reality weights allowed recognition states by
one unique rule: weight `φ⁻¹` per recognition step on the lattice,
`exp(−(ln φ)·cost)` in the continuum; with partition function `φ²` and
mean rung `φ`; cost-blind (no chirality selection); and reducing the BIT
amplitude to one integer with equilibrium band
`w₀ ∈ (−0.896, −0.88)` for `N ≥ 8`. -/
theorem t9_measure_forced :
    (∀ (R : RecognitionWeightRule) (n : ℕ), R.w n = latticeWeight n) ∧
    (∀ f : ℝ → ℝ, Factorizes f → AntitoneOn f (Set.Ici 0) → f 1 = rho →
      ∀ t : ℝ, 0 ≤ t → f t = rho ^ t) ∧
    partitionZ = Constants.phi ^ 2 ∧
    meanRung = Constants.phi ∧
    (∀ (W : CostSufficientWeight) (c : ℝ),
      W.w ⟨c, true⟩ = W.w ⟨c, false⟩) ∧
    (∀ N : ℕ, 8 ≤ N →
      -0.896 < -1 + deltaW0 N ∧ -1 + deltaW0 N < -0.88) :=
  ⟨fun R n => R.weight_forced n,
   fun _ hadd hanti hstep => continuum_weight_forced hadd hanti hstep,
   partitionZ_eq_phi_sq,
   meanRung_eq_phi,
   weight_blind_to_label,
   equilibrium_w0_band⟩

end

end MeasureForcing
end Foundation
end IndisputableMonolith
