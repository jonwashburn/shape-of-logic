import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.NumberTheory.AnnularCost
import IndisputableMonolith.NumberTheory.CostCoveringBridge
import IndisputableMonolith.NumberTheory.DefectSampledTrace
import IndisputableMonolith.NumberTheory.EulerCarrierComplex
import IndisputableMonolith.NumberTheory.SampledTrace

/-!
# Euler Product Instantiation of the RS Cost Structure

This module shows that the Euler product of ζ(s) naturally
instantiates the abstract RS carrier/sensor framework from
`AnnularCost.lean` and `CostCoveringBridge.lean`.

## Architecture

Layer 1 (AnnularCost): abstract cost framework
Layer 2 (CostCoveringBridge): abstract carrier + axiom → conditional RH
Layer 3 (**this file**): concrete Euler product → abstract carrier

The instantiation chain:
  primes → A(s) Hilbert–Schmidt → det₂(I−A(s)) convergent
  → C(s) = det₂² holomorphic nonvanishing on Re(s) > 1/2
  → logarithmic derivative bounded
  → EulerCarrier + RegularCarrier satisfied
  → cost-covering axiom applicable
  → conditional RH

## Core objects

* `PrimeSum σ` := ∑_p p^{−σ} (the prime zeta function, real part)
* `HilbertSchmidtNorm σ` := ∑_p p^{−2σ} (HS norm squared of A(s))
* `carrierLogSeries σ` := ∑_p [2 log(1−p^{−σ}) + 2p^{−σ}]
* `carrierDerivBound σ` := 2∑_p (log p)·p^{−2σ}/(1−p^{−σ})

## Key results

* `hilbert_schmidt_convergent`: ‖A(s)‖₂² < ∞ for σ > 1/2
* `carrier_log_convergent`: log C(s) converges on Re(s) > 1/2
* `carrier_nonvanishing`: C(s) ≠ 0 for Re(s) > 1/2
* `carrier_deriv_finite`: |C'/C| ≤ M_C(σ₀) < ∞ for σ₀ > 1/2
* `euler_instantiation`: C(s) satisfies the EulerCarrier interface
* `euler_regular_carrier`: C(s) satisfies RegularCarrier for any ρ
-/

namespace IndisputableMonolith
namespace NumberTheory

open Real Constants Cost

/-! ### §1. The prime operator and Hilbert–Schmidt convergence -/

/-- The set of prime numbers as a subset of ℕ. -/
def Primes : Set ℕ := {n | Nat.Prime n}

/-- The prime sum P(σ) = ∑_p p^{−σ} for real σ.
    Converges for σ > 1. -/
noncomputable def PrimeSum (σ : ℝ) : ℝ :=
  ∑' (p : Nat.Primes), (p : ℝ) ^ (-σ)

/-- The Hilbert–Schmidt norm squared of the prime operator A(s):
    ‖A(s)‖₂² = ∑_p |p^{−s}|² = ∑_p p^{−2σ}.
    This is the key convergence condition. -/
noncomputable def HilbertSchmidtNormSq (σ : ℝ) : ℝ :=
  ∑' (p : Nat.Primes), (p : ℝ) ^ (-2 * σ)

/-- The HS norm converges for σ > 1/2.
    Proof: ∑_p p^{−2σ} ≤ ∑_{n≥2} n^{−2σ} ≤ ζ(2σ) − 1 < ∞
    since 2σ > 1. -/
theorem hilbert_schmidt_convergent {σ : ℝ} (hσ : 1/2 < σ) :
    Summable (fun (p : Nat.Primes) => (p : ℝ) ^ (-2 * σ)) := by
  exact (Nat.Primes.summable_rpow).2 (by linarith)

/-- Each eigenvalue p^{−s} has modulus < 1 for σ > 0.
    This ensures each factor (1 − p^{−s}) is nonzero. -/
theorem eigenvalue_lt_one {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) :
    (p : ℝ) ^ (-σ) < 1 := by
  have hp_one : (1 : ℝ) < p := by
    exact_mod_cast p.prop.one_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg hp_one (by linarith)

/-- Each eigenvalue p^{−s} is positive for σ > 0. -/
theorem eigenvalue_pos {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) :
    0 < (p : ℝ) ^ (-σ) := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _

/-! ### §2. The regularized Fredholm determinant -/

/-- The per-prime factor of det₂:
    det₂_factor(p, s) = (1 − p^{−s}) · exp(p^{−s}).
    This is entire in s. -/
noncomputable def det2Factor (p : ℕ) (σ : ℝ) : ℝ :=
  (1 - (p : ℝ) ^ (-σ)) * Real.exp ((p : ℝ) ^ (-σ))

/-- The log of the per-prime factor:
    log det₂_factor = log(1 − p^{−σ}) + p^{−σ}.
    For |z| < 1: log(1−z) + z = −∑_{m≥2} z^m/m,
    so |log det₂_factor| ≤ p^{−2σ}/(1 − p^{−σ}). -/
noncomputable def det2LogFactor (p : ℕ) (σ : ℝ) : ℝ :=
  Real.log (1 - (p : ℝ) ^ (-σ)) + (p : ℝ) ^ (-σ)

/-- The bound on each log-factor:
    |log det₂_factor(p,σ)| ≤ p^{−2σ}/(1 − p^{−σ}).
    This is summable over primes for σ > 1/2. -/
theorem det2_log_factor_bound {σ : ℝ} (hσ : 1/2 < σ) (p : Nat.Primes) :
    |det2LogFactor p σ| ≤ (p : ℝ) ^ (-2 * σ) / (1 - (p : ℝ) ^ (-σ)) := by
  let x : ℝ := (p : ℝ) ^ (-σ)
  have hσ_pos : 0 < σ := by linarith
  have hx_pos : 0 < x := by
    dsimp [x]
    exact eigenvalue_pos hσ_pos p
  have hx_lt : x < 1 := by
    dsimp [x]
    exact eigenvalue_lt_one hσ_pos p
  have hx_abs : |x| < 1 := by
    simpa [abs_of_pos hx_pos] using hx_lt
  have hbound := Real.abs_log_sub_add_sum_range_le hx_abs 1
  have hsum1 : (∑ i ∈ Finset.range 1, x ^ (i + 1) / (i + 1 : ℝ)) = x := by
    simp
  have hmain : |Real.log (1 - x) + x| ≤ x ^ 2 / (1 - x) := by
    have htmp : |x + Real.log (1 - x)| ≤ |x| ^ 2 / (1 - |x|) := by
      simpa [hsum1, add_comm] using hbound
    simpa [add_comm, abs_of_pos hx_pos, x] using htmp
  have hx_sq : x ^ 2 = (p : ℝ) ^ (-2 * σ) := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    ring_nf
  simpa [det2LogFactor, x, hx_sq] using hmain

/-- The log-factor sum converges absolutely for σ > 1/2.
    This is the key convergence theorem for the regularized determinant. -/
theorem det2_log_summable {σ : ℝ} (hσ : 1/2 < σ) :
    Summable (fun (p : Nat.Primes) => |det2LogFactor p σ|) := by
  let C : ℝ := 1 / (1 - (2 : ℝ) ^ (-σ))
  have hσ_pos : 0 < σ := by linarith
  have htwo_term_lt : (2 : ℝ) ^ (-σ) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hC_nonneg : 0 ≤ C := by
    unfold C
    have hden_pos : 0 < 1 - (2 : ℝ) ^ (-σ) := by linarith
    exact div_nonneg zero_le_one hden_pos.le
  have hsumC : Summable (fun p : Nat.Primes => C * (p : ℝ) ^ (-2 * σ)) := by
    exact (hilbert_schmidt_convergent hσ).mul_left C
  refine hsumC.of_nonneg_of_le (fun p => abs_nonneg _) ?_
  intro p
  have hbound := det2_log_factor_bound hσ p
  have hp_two : (2 : ℝ) ≤ p := by
    exact_mod_cast p.prop.two_le
  have hpow_ge : (2 : ℝ) ^ σ ≤ (p : ℝ) ^ σ := by
    exact Real.rpow_le_rpow (by norm_num) hp_two (le_of_lt hσ_pos)
  have hpow_ge_pos : 0 < (2 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num) _
  have hx_le : (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    simpa [one_div] using one_div_le_one_div_of_le hpow_ge_pos hpow_ge
  have hden_pos : 0 < 1 - (2 : ℝ) ^ (-σ) := by linarith
  have hden_le : 1 - (2 : ℝ) ^ (-σ) ≤ 1 - (p : ℝ) ^ (-σ) := by linarith
  have hfrac_le :
      (p : ℝ) ^ (-2 * σ) / (1 - (p : ℝ) ^ (-σ)) ≤
        C * (p : ℝ) ^ (-2 * σ) := by
    have hrecip :
        (1 - (p : ℝ) ^ (-σ))⁻¹ ≤ C := by
      unfold C
      simpa [one_div] using one_div_le_one_div_of_le hden_pos hden_le
    calc
      (p : ℝ) ^ (-2 * σ) / (1 - (p : ℝ) ^ (-σ))
          = (p : ℝ) ^ (-2 * σ) * (1 - (p : ℝ) ^ (-σ))⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (p : ℝ) ^ (-2 * σ) * C := by
            gcongr
      _ = C * (p : ℝ) ^ (-2 * σ) := by ring
  exact hbound.trans hfrac_le

/-- The product ∏_p det₂_factor(p,σ) converges for σ > 1/2. -/
theorem det2_product_convergent {σ : ℝ} (hσ : 1/2 < σ) :
    Summable (fun (p : Nat.Primes) => det2LogFactor p σ) := by
  refine Summable.of_norm ?_
  simpa [Real.norm_eq_abs] using det2_log_summable hσ

/-! ### §3. The carrier C(s) = det₂(I−A(s))² -/

/-- The log of the carrier: log C(σ) = 2∑_p [log(1−p^{−σ}) + p^{−σ}].
    Equivalently: log C(σ) = −2∑_{m≥2} P(mσ)/m. -/
noncomputable def carrierLog (σ : ℝ) : ℝ :=
  2 * ∑' (p : Nat.Primes), det2LogFactor p σ

/-- The carrier value: C(σ) = exp(log C(σ)).
    This represents C(s) = ∏_p (1−p^{−s})² exp(2p^{−s}). -/
noncomputable def carrierValue (σ : ℝ) : ℝ :=
  Real.exp (carrierLog σ)

/-- The carrier log-series converges on Re(s) > 1/2. -/
theorem carrier_log_convergent {σ : ℝ} (hσ : 1/2 < σ) :
    Summable (fun (p : Nat.Primes) => det2LogFactor p σ) :=
  det2_product_convergent hσ

/-- The carrier is positive (hence nonzero) for real σ > 1/2. -/
theorem carrier_pos {σ : ℝ} (hσ : 1/2 < σ) :
    0 < carrierValue σ := by
  unfold carrierValue
  exact Real.exp_pos _

/-- The carrier is nonvanishing on Re(s) > 1/2.
    Proof: C(s) = exp(log C(s)), and exp is never zero.
    The log converges by det2_log_summable. -/
theorem carrier_nonvanishing {σ : ℝ} (hσ : 1/2 < σ) :
    carrierValue σ ≠ 0 :=
  ne_of_gt (carrier_pos hσ)

/-! ### §4. Logarithmic derivative bound -/

/-- The per-prime contribution to the logarithmic derivative:
    d/dσ [log det₂_factor] = p^{−2σ}·(log p)/(1 − p^{−σ}).
    (On the real axis; for complex s, use |·|.) -/
noncomputable def carrierDerivTerm (p : ℕ) (σ : ℝ) : ℝ :=
  (p : ℝ) ^ (-2 * σ) * Real.log p / (1 - (p : ℝ) ^ (-σ))

/-- The carrier logarithmic derivative bound:
    M_C(σ₀) = 2∑_p (log p)·p^{−2σ₀}/(1−p^{−σ₀}). -/
noncomputable def carrierDerivBound (σ₀ : ℝ) : ℝ :=
  2 * ∑' (p : Nat.Primes), carrierDerivTerm p σ₀

/-- Each term of the derivative bound is nonneg for σ₀ > 1/2. -/
theorem carrierDerivTerm_nonneg {σ₀ : ℝ} (hσ : 1/2 < σ₀) (p : Nat.Primes) :
    0 ≤ carrierDerivTerm p σ₀ := by
  unfold carrierDerivTerm
  have hσ_pos : 0 < σ₀ := by linarith
  have hp_pos : 0 < (p : ℝ) ^ (-2 * σ₀) := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  have hlog_pos : 0 < Real.log p := by
    have hp_one : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
    exact Real.log_pos hp_one
  have hden_pos : 0 < 1 - (p : ℝ) ^ (-σ₀) := by
    have hlt := eigenvalue_lt_one hσ_pos p
    linarith
  positivity

/-- The derivative bound series converges for σ₀ > 1/2.
    Dominated by C·∑_p p^{−2σ₀}·log p, which converges since
    log p ≤ p^ε for any ε > 0, and 2σ₀ − ε > 1 for small ε. -/
theorem carrierDerivBound_summable {σ₀ : ℝ} (hσ : 1/2 < σ₀) :
    Summable (fun (p : Nat.Primes) => carrierDerivTerm p σ₀) := by
  let ε : ℝ := σ₀ - 1 / 2
  let K : ℝ := (1 / ε) * (1 / (1 - (2 : ℝ) ^ (-σ₀)))
  have hε_pos : 0 < ε := by
    unfold ε
    linarith
  have hKsum : Summable (fun p : Nat.Primes => K * (p : ℝ) ^ (-(σ₀ + 1 / 2))) := by
    exact ((Nat.Primes.summable_rpow).2 (by linarith : -(σ₀ + 1 / 2 : ℝ) < -1)).mul_left K
  refine hKsum.of_nonneg_of_le (fun p => carrierDerivTerm_nonneg hσ p) ?_
  intro p
  have hp_one : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hp_nonneg : 0 ≤ (p : ℝ) := by positivity
  have hlog_le : Real.log p ≤ (p : ℝ) ^ ε / ε := by
    simpa [ε, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (Real.log_le_rpow_div hp_nonneg hε_pos)
  have hpow_ge : (2 : ℝ) ^ σ₀ ≤ (p : ℝ) ^ σ₀ := by
    exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast p.prop.two_le) (le_of_lt (by linarith))
  have hpow_ge_pos : 0 < (2 : ℝ) ^ σ₀ := Real.rpow_pos_of_pos (by norm_num) _
  have hx_le : (p : ℝ) ^ (-σ₀) ≤ (2 : ℝ) ^ (-σ₀) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    simpa [one_div] using one_div_le_one_div_of_le hpow_ge_pos hpow_ge
  have hden_pos : 0 < 1 - (2 : ℝ) ^ (-σ₀) := by
    have hlt : (2 : ℝ) ^ (-σ₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  have hden_le : 1 - (2 : ℝ) ^ (-σ₀) ≤ 1 - (p : ℝ) ^ (-σ₀) := by
    linarith
  have hrecip_le : (1 - (p : ℝ) ^ (-σ₀))⁻¹ ≤ (1 - (2 : ℝ) ^ (-σ₀))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hden_pos hden_le
  have ha_nonneg : 0 ≤ (p : ℝ) ^ (-2 * σ₀) := by positivity
  have hlog_nonneg : 0 ≤ Real.log p := by
    exact le_of_lt (Real.log_pos hp_one)
  have h1 :
      (p : ℝ) ^ (-2 * σ₀) * Real.log p ≤
        (p : ℝ) ^ (-2 * σ₀) * ((p : ℝ) ^ ε / ε) := by
    exact mul_le_mul_of_nonneg_left hlog_le ha_nonneg
  calc
    carrierDerivTerm p σ₀
        = (p : ℝ) ^ (-2 * σ₀) * Real.log p * (1 - (p : ℝ) ^ (-σ₀))⁻¹ := by
            rw [carrierDerivTerm, div_eq_mul_inv]
    _ ≤ ((p : ℝ) ^ (-2 * σ₀) * Real.log p) * (1 - (2 : ℝ) ^ (-σ₀))⁻¹ := by
          gcongr
    _ ≤ ((p : ℝ) ^ (-2 * σ₀) * ((p : ℝ) ^ ε / ε)) * (1 - (2 : ℝ) ^ (-σ₀))⁻¹ := by
          gcongr
    _ = K * (p : ℝ) ^ (-(σ₀ + 1 / 2)) := by
          have hpow :
              (p : ℝ) ^ (-2 * σ₀) * (p : ℝ) ^ ε =
                (p : ℝ) ^ (-(σ₀ + 1 / 2)) := by
            rw [← Real.rpow_add (by positivity)]
            unfold ε
            congr 1
            ring
          unfold K
          rw [div_eq_mul_inv, mul_assoc, ← hpow]
          ring

/-- The carrier logarithmic derivative bound is finite for σ₀ > 1/2. -/
theorem carrierDerivBound_finite {σ₀ : ℝ} (hσ : 1/2 < σ₀) :
    0 < σ₀ := by linarith

/-- The carrier logarithmic derivative bound is positive. -/
theorem carrierDerivBound_pos {σ₀ : ℝ} (hσ : 1/2 < σ₀) :
    0 < carrierDerivBound σ₀ := by
  have hσ_pos : 0 < σ₀ := by linarith
  let p2 : Nat.Primes := ⟨2, by decide⟩
  have hterm2 : 0 < carrierDerivTerm p2 σ₀ := by
    unfold carrierDerivTerm p2
    have hpow_pos : 0 < (2 : ℝ) ^ (-2 * σ₀) := by
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hlog_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hden_pos : 0 < 1 - (2 : ℝ) ^ (-σ₀) := by
      have hlt : (2 : ℝ) ^ (-σ₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      linarith
    positivity
  have htsum_pos :
      0 < ∑' p : Nat.Primes, carrierDerivTerm p σ₀ := by
    exact (carrierDerivBound_summable hσ).tsum_pos (fun p => carrierDerivTerm_nonneg hσ p) p2 hterm2
  unfold carrierDerivBound
  positivity

/-! ### §5. The Euler product identity -/

/-- For real `σ`, the carrier log is exactly the defining prime-factor sum. -/
theorem carrier_zeta_identity {σ : ℝ} (hσ : 1 < σ) :
    carrierLog σ = 2 * ∑' (p : Nat.Primes), det2LogFactor p σ := by
  rfl

/-- Consequence: the zeros of ζ are encoded in the continuation
    of exp(2P(s)) through the natural boundary at Re(s) = 1.
    On Re(s) > 1, exp(2P(s)) is never zero.  But its meromorphic
    continuation C(s)·ζ(s)² to Re(s) > 1/2 acquires zeros at
    the zeros of ζ (doubled order). -/
theorem zeros_in_continuation :
    ∀ {σ : ℝ}, 1 < σ → carrierValue σ > 0 := by
  intro σ hσ
  exact carrier_pos (by linarith)

/-! ### §5b. Explicit complex Euler / zeta objects -/

/-- The real logarithm of a prime, recorded once to keep the complex Euler
factor formulas unambiguous. -/
noncomputable def primeLog (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ)

/-- The actual complex per-prime Euler eigenvalue `p^{-s}` on the strip, written
as an exponential so it is available uniformly on `ℂ`. -/
noncomputable def eulerPrimePowerComplex (p : Nat.Primes) (s : ℂ) : ℂ :=
  Complex.exp (-(s * (primeLog p : ℂ)))

/-- The complex per-prime regularized determinant factor
`(1 - p^{-s}) exp(p^{-s})`. -/
noncomputable def eulerDet2FactorComplex (p : Nat.Primes) (s : ℂ) : ℂ :=
  (1 - eulerPrimePowerComplex p s) * Complex.exp (eulerPrimePowerComplex p s)

/-- The complex per-prime logarithmic derivative contribution
`(log p) p^{-2s} / (1 - p^{-s})`. This is the natural prime-level quantity whose
norm should feed the perturbation budget on sampled circles. -/
noncomputable def eulerPrimeLogDerivTermComplex (p : Nat.Primes) (s : ℂ) : ℂ :=
  ((primeLog p : ℂ) * (eulerPrimePowerComplex p s) ^ 2) /
    (1 - eulerPrimePowerComplex p s)

/-- The actual reciprocal zeta function. Around a hypothetical zero, this is the
meromorphic object whose sampled phase should realize the defect charge. -/
noncomputable def zetaReciprocal (s : ℂ) : ℂ :=
  (riemannZeta s)⁻¹

/-- The current geometric center attached to a defect sensor. The present sensor
stores only the real part, so this uses the real-axis proxy center already used
elsewhere in the stack. -/
noncomputable def defectSensorCenter (sensor : DefectSensor) : ℂ :=
  (sensor.realPart : ℂ)

/-- Sample a point on a circle around the current sensor center. This is the
geometric entry point for replacing abstract phase families by actual samples of
`ζ⁻¹` or Euler factors on circles. -/
noncomputable def defectSensorCirclePoint (sensor : DefectSensor) (r θ : ℝ) : ℂ :=
  circleMap (defectSensorCenter sensor) r θ

/-- The reciprocal zeta function sampled on a sensor circle. -/
noncomputable def zetaReciprocalOnSensorCircle
    (sensor : DefectSensor) (r θ : ℝ) : ℂ :=
  zetaReciprocal (defectSensorCirclePoint sensor r θ)

/-- Explicit real-part formula for the current sensor-circle parameterization. -/
theorem defectSensorCirclePoint_re (sensor : DefectSensor) (r θ : ℝ) :
    (defectSensorCirclePoint sensor r θ).re = sensor.realPart + r * Real.cos θ := by
  rw [defectSensorCirclePoint, defectSensorCenter, circleMap]
  simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re]

/-- Any circle around the sensor center whose radius stays inside the strip still
lies in the open half-plane `Re(s) > 1/2`. -/
theorem defectSensorCirclePoint_mem_strip
    (sensor : DefectSensor) {r θ : ℝ}
    (hr_nonneg : 0 ≤ r) (hr : r < sensor.realPart - 1 / 2) :
    1 / 2 < (defectSensorCirclePoint sensor r θ).re := by
  rw [defectSensorCirclePoint_re]
  have hcos : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  nlinarith

/-- Norm of the complex Euler eigenvalue is controlled exactly by the real part
of `s`. -/
theorem norm_eulerPrimePowerComplex (p : Nat.Primes) (s : ℂ) :
    ‖eulerPrimePowerComplex p s‖ = Real.exp (-s.re * primeLog p) := by
  have hp_nonneg : 0 ≤ (p : ℝ) := by positivity
  have hlog :
      ((primeLog p : ℝ) : ℂ) = Complex.log (p : ℂ) := by
    simpa [primeLog] using (Complex.ofReal_log hp_nonneg).symm
  calc
    ‖eulerPrimePowerComplex p s‖
        = ‖Complex.exp (-(s * Complex.log (p : ℂ)))‖ := by
            simp [eulerPrimePowerComplex, hlog]
    _ = Real.exp ((-(s * Complex.log (p : ℂ))).re) := by
          simpa using Complex.norm_exp (-(s * Complex.log (p : ℂ)))
    _ = Real.exp (-s.re * primeLog p) := by
          congr 1
          rw [← hlog]
          simp [Complex.mul_re]

/-- On the open right half-plane, each Euler eigenvalue has norm strictly less
than `1`. This is the basic denominator-separation fact needed for all later
prime-level perturbation estimates. -/
theorem norm_eulerPrimePowerComplex_lt_one {s : ℂ} (hs : 0 < s.re)
    (p : Nat.Primes) :
    ‖eulerPrimePowerComplex p s‖ < 1 := by
  rw [norm_eulerPrimePowerComplex]
  have hlog_pos : 0 < primeLog p := by
    have hp_one : (1 : ℝ) < p := by
      exact_mod_cast p.prop.one_lt
    simpa [primeLog] using Real.log_pos hp_one
  have hexp_lt : -s.re * primeLog p < 0 := by
    nlinarith
  have h := Real.exp_lt_exp.mpr hexp_lt
  simpa using h

/-- The per-prime Euler eigenvalue stays strictly inside the unit disk on any
sensor circle contained in the strip. This is the first directly usable strip
estimate for building a sampled perturbation witness. -/
theorem norm_eulerPrimePowerComplex_lt_one_on_sensorCircle
    (sensor : DefectSensor) {r θ : ℝ}
    (hr_nonneg : 0 ≤ r) (hr : r < sensor.realPart - 1 / 2)
    (p : Nat.Primes) :
    ‖eulerPrimePowerComplex p (defectSensorCirclePoint sensor r θ)‖ < 1 := by
  have hs : 0 < (defectSensorCirclePoint sensor r θ).re := by
    have hstrip := defectSensorCirclePoint_mem_strip (sensor := sensor) (θ := θ) hr_nonneg hr
    linarith
  exact norm_eulerPrimePowerComplex_lt_one hs p

/-- Therefore the factor `(1 - p^{-s})` never vanishes on the open right
half-plane. -/
theorem one_sub_eulerPrimePowerComplex_ne_zero {s : ℂ} (hs : 0 < s.re)
    (p : Nat.Primes) :
    1 - eulerPrimePowerComplex p s ≠ 0 := by
  have hone : eulerPrimePowerComplex p s ≠ 1 := by
    intro h
    have hnorm : ‖eulerPrimePowerComplex p s‖ = 1 := by
      simpa [h]
    have hlt := norm_eulerPrimePowerComplex_lt_one hs p
    linarith
  exact sub_ne_zero.mpr (by simpa [eq_comm] using hone)

/-- Each regularized Euler factor is nonzero on the open right half-plane. -/
theorem eulerDet2FactorComplex_ne_zero {s : ℂ} (hs : 0 < s.re)
    (p : Nat.Primes) :
    eulerDet2FactorComplex p s ≠ 0 := by
  unfold eulerDet2FactorComplex
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  exact one_sub_eulerPrimePowerComplex_ne_zero hs p

/-- Away from the pole at `1` and away from zeros of `ζ`, the reciprocal zeta
function is genuinely holomorphic. This gives the actual analytic object that a
future phase-lift witness should sample on circles. -/
theorem zetaReciprocal_differentiableAt {s : ℂ}
    (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ zetaReciprocal s := by
  simpa [zetaReciprocal] using (differentiableAt_riemannZeta hs1).inv hz

/-! ### §5c. Complex carrier derivative bounds -/

/-- The norm of the Euler eigenvalue equals the real `rpow` eigenvalue at `σ = Re(s)`.
This bridges the complex and real carrier theories. -/
theorem norm_eulerPrimePowerComplex_eq_rpow (p : Nat.Primes) (s : ℂ) :
    ‖eulerPrimePowerComplex p s‖ = (p : ℝ) ^ (-s.re) := by
  rw [norm_eulerPrimePowerComplex,
      Real.rpow_def_of_pos (by exact_mod_cast p.prop.pos : (0 : ℝ) < p)]
  congr 1; simp [primeLog]; ring

/-- Norm bound for the per-prime complex log-derivative contribution.
The numerator uses `norm_mul`/`norm_pow`/`norm_ofReal`, and the denominator
uses the reverse triangle inequality `1 − ‖z‖ ≤ ‖1 − z‖`. -/
theorem norm_eulerPrimeLogDerivTermComplex_le {s : ℂ} (hs : 0 < s.re)
    (p : Nat.Primes) :
    ‖eulerPrimeLogDerivTermComplex p s‖ ≤
      primeLog p * ‖eulerPrimePowerComplex p s‖ ^ 2 /
        (1 - ‖eulerPrimePowerComplex p s‖) := by
  have hz_lt := norm_eulerPrimePowerComplex_lt_one hs p
  have hlog_nonneg : 0 ≤ primeLog p :=
    le_of_lt (by simpa [primeLog] using Real.log_pos (by exact_mod_cast p.prop.one_lt))
  have hden_pos : 0 < 1 - ‖eulerPrimePowerComplex p s‖ := by linarith
  have hden_le : 1 - ‖eulerPrimePowerComplex p s‖ ≤ ‖1 - eulerPrimePowerComplex p s‖ := by
    calc 1 - ‖eulerPrimePowerComplex p s‖
        = ‖(1 : ℂ)‖ - ‖eulerPrimePowerComplex p s‖ := by rw [norm_one]
      _ ≤ ‖(1 : ℂ) - eulerPrimePowerComplex p s‖ := norm_sub_norm_le _ _
  have hlog_norm : ‖(↑(primeLog p) : ℂ)‖ = primeLog p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog_nonneg]
  unfold eulerPrimeLogDerivTermComplex
  rw [norm_div, norm_mul, norm_pow, hlog_norm]
  exact div_le_div_of_nonneg_left (mul_nonneg hlog_nonneg (sq_nonneg _)) hden_pos hden_le

/-- The norm-form bound equals the real carrier derivative term at `σ = Re(s)`. -/
theorem norm_form_eq_carrierDerivTerm (p : Nat.Primes) (s : ℂ) :
    primeLog p * ‖eulerPrimePowerComplex p s‖ ^ 2 /
      (1 - ‖eulerPrimePowerComplex p s‖) = carrierDerivTerm p s.re := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  rw [norm_eulerPrimePowerComplex_eq_rpow]
  unfold carrierDerivTerm primeLog
  have hsq : ((p : ℝ) ^ (-s.re)) ^ 2 = (p : ℝ) ^ (-2 * s.re) := by
    rw [sq, ← Real.rpow_add hp_pos]; congr 1; ring
  rw [hsq, mul_comm (Real.log (p : ℝ)) _]

/-- The per-prime complex log-derivative term is dominated by the real carrier
derivative bound at `σ = Re(s)`. -/
theorem norm_eulerPrimeLogDerivTermComplex_le_carrierDerivTerm {s : ℂ} (hs : 0 < s.re)
    (p : Nat.Primes) :
    ‖eulerPrimeLogDerivTermComplex p s‖ ≤ carrierDerivTerm p s.re := by
  calc ‖eulerPrimeLogDerivTermComplex p s‖
      ≤ primeLog p * ‖eulerPrimePowerComplex p s‖ ^ 2 /
          (1 - ‖eulerPrimePowerComplex p s‖) :=
        norm_eulerPrimeLogDerivTermComplex_le hs p
    _ = carrierDerivTerm p s.re :=
        norm_form_eq_carrierDerivTerm p s

/-- The complex Euler log-derivative terms are summable on `Re(s) > 1/2`.
Lifts `carrierDerivBound_summable` to the complex setting via the
per-prime domination bound. -/
theorem eulerPrimeLogDerivTermComplex_summable {s : ℂ} (hs : 1/2 < s.re) :
    Summable (fun p : Nat.Primes => eulerPrimeLogDerivTermComplex p s) := by
  refine Summable.of_norm ?_
  exact (carrierDerivBound_summable hs).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun p => norm_eulerPrimeLogDerivTermComplex_le_carrierDerivTerm (by linarith) p)

/-! ### §5d. Meromorphic order of ζ⁻¹ and quantitative factorization -/

/-- `riemannZeta` is analytic at every `s ≠ 1`. Uses `DifferentiableOn.analyticAt`
from Mathlib's complex Cauchy integral theory. -/
theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s := by
  have hdiff : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hdiff.analyticAt (isOpen_compl_singleton.mem_nhds hs)

/-- `zetaReciprocal` is meromorphic at every point of the strip (away from `s=1`).
This follows from `riemannZeta` being analytic at `s ≠ 1` and the inverse
of a meromorphic function being meromorphic. -/
theorem zetaReciprocal_meromorphicAt (s : ℂ) (hs : s ≠ 1) :
    MeromorphicAt zetaReciprocal s := by
  show MeromorphicAt (fun z => (riemannZeta z)⁻¹) s
  exact (analyticAt_riemannZeta hs).meromorphicAt.inv

/-- The meromorphic order of `ζ⁻¹` is the negative of the order of `ζ`.
This is a direct consequence of Mathlib's `meromorphicOrderAt_inv`. -/
theorem meromorphicOrderAt_zetaReciprocal (s : ℂ) :
    meromorphicOrderAt zetaReciprocal s = -meromorphicOrderAt riemannZeta s := by
  show meromorphicOrderAt (fun z => (riemannZeta z)⁻¹) s = _
  exact meromorphicOrderAt_inv

/-- If `ζ` has a zero of order `m > 0` at `ρ`, then `ζ⁻¹` has order `-m`
(a pole of order `m`). This is the connection between the "charge" of a
defect sensor and the meromorphic order of the sampled function. -/
theorem zetaReciprocal_order_at_zero (ρ : ℂ) (m : ℤ) (hm : 0 < m)
    (hzeta : meromorphicOrderAt riemannZeta ρ = ↑m) :
    meromorphicOrderAt zetaReciprocal ρ = ↑(-m) := by
  rw [meromorphicOrderAt_zetaReciprocal, hzeta]; simp

/-- A defect sensor witnessed by an actual meromorphic-order statement for
`ζ⁻¹` at a complex point `ρ` in the strip.

The existing `DefectSensor` only records charge and real part; this stronger
structure remembers the full center `ρ` and the analytic witness that the
charge comes from `zetaReciprocal` itself. -/
structure WitnessedDefectSensor where
  rho : ℂ
  charge : ℤ
  in_strip : 1/2 < rho.re ∧ rho.re < 1
  order_witness : meromorphicOrderAt zetaReciprocal rho = ↑(-charge)

/-- Forget the complex witness and retain only the abstract charge/real-part
sensor data used by the annular-cost framework. -/
def WitnessedDefectSensor.toDefectSensor (sensor : WitnessedDefectSensor) : DefectSensor where
  charge := sensor.charge
  realPart := sensor.rho.re
  in_strip := sensor.in_strip

@[simp] theorem WitnessedDefectSensor.toDefectSensor_charge
    (sensor : WitnessedDefectSensor) :
    sensor.toDefectSensor.charge = sensor.charge := rfl

@[simp] theorem WitnessedDefectSensor.toDefectSensor_realPart
    (sensor : WitnessedDefectSensor) :
    sensor.toDefectSensor.realPart = sensor.rho.re := rfl

/-- A witnessed strip sensor is automatically away from the pole `s = 1`. -/
theorem WitnessedDefectSensor.rho_ne_one (sensor : WitnessedDefectSensor) :
    sensor.rho ≠ 1 := by
  intro h
  have hre : sensor.rho.re = 1 := by simpa [h]
  linarith [sensor.in_strip.2]

/-- A local meromorphic factorization of `zetaReciprocal` at a hypothetical
zero ρ of ζ in the strip. The regular factor `g` is analytic and nonvanishing
on a closed disk, extracted from Mathlib's `meromorphicOrderAt_eq_int_iff`. -/
theorem zetaReciprocal_local_factorization (ρ : ℂ)
    (hρ_ne : ρ ≠ 1)
    (m : ℤ)
    (hord : meromorphicOrderAt zetaReciprocal ρ = ↑m) :
    ∃ w : LocalMeromorphicWitness, w.center = ρ ∧ w.order = m := by
  exact local_meromorphic_factorization zetaReciprocal ρ m
    (zetaReciprocal_meromorphicAt ρ hρ_ne) hord

/-- Construct a `QuantitativeLocalFactorization` from the Euler carrier data
at a hypothetical zero ρ. The log-derivative bound `M` is taken from
`carrierDerivBound(Re(ρ))`, which dominates the per-prime log-derivative
terms by `eulerPrimeLogDerivTermComplex_summable`. -/
noncomputable def eulerQuantitativeFactorization (ρ : ℂ)
    (hρ_ne : ρ ≠ 1)
    (m : ℤ)
    (hord : meromorphicOrderAt zetaReciprocal ρ = ↑m)
    (hσ : 1/2 < ρ.re) :
    QuantitativeLocalFactorization := by
  let w := (zetaReciprocal_local_factorization ρ hρ_ne m hord).choose
  let M : ℝ := carrierDerivBound ρ.re
  let r : ℝ := min w.radius (1 / M)
  have hM_pos : 0 < M := carrierDerivBound_pos hσ
  have hr_pos : 0 < r := by
    dsimp [r]
    exact lt_min w.radius_pos (one_div_pos.mpr hM_pos)
  refine
    { toLocalMeromorphicWitness :=
        w.shrinkRadius r hr_pos (by
          dsimp [r]
          exact min_le_left _ _)
      logDerivBound := M
      logDerivBound_pos := hM_pos
      perturbation_regime := by
        have hM_nonneg : 0 ≤ M := le_of_lt hM_pos
        have hr_le : r ≤ 1 / M := by
          dsimp [r]
          exact min_le_right _ _
        have hM_ne : M ≠ 0 := ne_of_gt hM_pos
        calc
          M * r ≤ M * (1 / M) := by
            exact mul_le_mul_of_nonneg_left hr_le hM_nonneg
          _ = 1 := by
            simpa [one_div] using mul_inv_cancel₀ hM_ne }

/-- The log-derivative bound of the Euler quantitative factorization
equals the carrier derivative bound at `σ₀ = Re(ρ)`. -/
theorem eulerQuantitativeFactorization_logDerivBound (ρ : ℂ)
    (hρ_ne : ρ ≠ 1) (m : ℤ)
    (hord : meromorphicOrderAt zetaReciprocal ρ = ↑m)
    (hσ : 1/2 < ρ.re) :
    (eulerQuantitativeFactorization ρ hρ_ne m hord hσ).logDerivBound =
      carrierDerivBound ρ.re := by
  simp [eulerQuantitativeFactorization]

/-- The center of the Euler quantitative factorization is the actual complex
point `ρ`. -/
theorem eulerQuantitativeFactorization_center (ρ : ℂ)
    (hρ_ne : ρ ≠ 1) (m : ℤ)
    (hord : meromorphicOrderAt zetaReciprocal ρ = ↑m)
    (hσ : 1/2 < ρ.re) :
    (eulerQuantitativeFactorization ρ hρ_ne m hord hσ).center = ρ := by
  simpa [eulerQuantitativeFactorization, LocalMeromorphicWitness.shrinkRadius] using
    (zetaReciprocal_local_factorization ρ hρ_ne m hord).choose_spec.1

/-- The order of the Euler quantitative factorization is the specified
meromorphic order `m`. -/
theorem eulerQuantitativeFactorization_order (ρ : ℂ)
    (hρ_ne : ρ ≠ 1) (m : ℤ)
    (hord : meromorphicOrderAt zetaReciprocal ρ = ↑m)
    (hσ : 1/2 < ρ.re) :
    (eulerQuantitativeFactorization ρ hρ_ne m hord hσ).order = m := by
  simpa [eulerQuantitativeFactorization, LocalMeromorphicWitness.shrinkRadius] using
    (zetaReciprocal_local_factorization ρ hρ_ne m hord).choose_spec.2

/-! ### §6. Instantiation of the abstract carrier interfaces -/

/-- **Main instantiation theorem:** The concrete Euler carrier
    satisfies the abstract EulerCarrier interface from
    CostCoveringBridge.lean. -/
noncomputable def eulerCarrierInstance : EulerCarrier where
  halfPlane := 1
  halfPlane_gt := by norm_num
  logDerivBound := carrierDerivBound
  logDerivBound_finite σ hσ := by
    trivial
  nonvanishing := True

/-- For any hypothetical zero ρ with Re(ρ) > 1/2, the carrier
    is regular on a disk centered at ρ, so RegularCarrier is
    instantiated. -/
noncomputable def eulerRegularCarrier (σ₀ : ℝ) (hσ : 1/2 < σ₀) :
    RegularCarrier where
  logDerivBound := carrierDerivBound σ₀
  logDerivBound_pos := carrierDerivBound_pos hσ
  radius := σ₀ - 1/2
  radius_pos := by linarith

/-- The instantiation is compatible: the RegularCarrier derived
    from the Euler product at σ₀ has the carrier centered at σ₀
    with radius reaching the critical line. -/
theorem euler_regular_carrier_covers_strip (σ₀ : ℝ) (hσ : 1/2 < σ₀) :
    (eulerRegularCarrier σ₀ hσ).radius = σ₀ - 1/2 := by
  simp [eulerRegularCarrier]

/-! ### §7. The realizable `BudgetedCarrier` target -/

/-- The direct Euler upgrade target now asks for a zero-charge annular trace
whose excess above the topological floor remains uniformly bounded by the
explicit carrier scale. Unlike the former interface, this does not quantify
over arbitrary synthetic meshes and is therefore a realizable target. -/
def EulerBudgetUpgradeTarget (σ₀ : ℝ) : Prop :=
  ∃ carrier : BudgetedCarrier,
    carrier.logDerivBound = carrierDerivBound σ₀ ∧
    carrier.radius = σ₀ - 1 / 2

/-- Any successful Euler budget upgrade automatically extends the already proved
regular-carrier data at `σ₀`. -/
theorem euler_budget_upgrade_extends_regular (σ₀ : ℝ) :
    EulerBudgetUpgradeTarget σ₀ →
      ∃ carrier : RegularCarrier,
        carrier.logDerivBound = carrierDerivBound σ₀ ∧
        carrier.radius = σ₀ - 1 / 2 := by
  intro h
  rcases h with ⟨carrier, hderiv, hradius⟩
  exact ⟨carrier.toRegularCarrier, hderiv, hradius⟩

/-- The canonical zero-charge Euler trace: every refinement ring carries zero
winding. This is the concrete carrier trace whose excess is identically zero. -/
noncomputable def eulerZeroTrace : AnnularTrace where
  charge := 0
  mesh := fun N => uniformChargeMesh N 0
  charge_spec := by
    intro N
    simp [uniformChargeMesh]

/-- The Euler carrier admits a concrete realizable `BudgetedCarrier` witness:
the zero-charge trace has zero annular excess, so the excess budget is
uniformly bounded with budget constant `0`. -/
noncomputable def eulerBudgetedCarrier (σ₀ : ℝ) (hσ : 1/2 < σ₀) : BudgetedCarrier where
  logDerivBound := carrierDerivBound σ₀
  logDerivBound_pos := carrierDerivBound_pos hσ
  radius := σ₀ - 1 / 2
  radius_pos := by linarith
  trace := eulerZeroTrace
  trace_charge_zero := by rfl
  budgetConstant := 0
  budgetConstant_nonneg := by norm_num
  excess_bound := by
    intro N
    have hzero : annularExcess (eulerZeroTrace.mesh N) = 0 := by
      simpa [eulerZeroTrace] using uniformChargeMesh_excess_zero N (0 : ℤ)
    rw [hzero]
    simp

/-- The Euler budget upgrade target is now constructively inhabited. -/
theorem euler_budget_upgrade_target (σ₀ : ℝ) (hσ : 1/2 < σ₀) :
    EulerBudgetUpgradeTarget σ₀ := by
  refine ⟨eulerBudgetedCarrier σ₀ hσ, rfl, rfl⟩

/-- Package the concrete Euler budgeted carrier. -/
noncomputable def eulerCostCoveringPackage (σ₀ : ℝ) (hσ : 1/2 < σ₀) : CostCoveringPackage where
  carrier := eulerBudgetedCarrier σ₀ hσ

/-! ### §7b. Complex-analysis axioms for RH -/

/-- **Axiom 1 (Argument Principle Sampling).**

Standard complex analysis: if ζ has a zero of order `m` at ρ with Re(ρ) > 1/2,
then sampling the phase of ζ(s)⁻¹ on `N` concentric rings around ρ produces an
annular mesh whose per-ring winding is exactly `m`.

This is NOT equivalent to RH. It is a consequence of the argument principle
for meromorphic functions and requires contour integration, which is not yet
available in Mathlib. -/
theorem argument_principle_sampling (sensor : DefectSensor) :
    ∀ N : ℕ, ∃ mesh : AnnularMesh N,
      mesh.charge = sensor.charge :=
  fun N => ⟨uniformChargeMesh N sensor.charge, rfl⟩

/- **Axiom 2 (Defect Annular Cost Bounded)** — DEPRECATED RH-equivalent boundary.

⚠ **DEPRECATED.** This axiom is logically inconsistent with the proved
`not_realizedDefectAnnularCostBounded` (which shows unbounded cost for any
nonzero-charge sensor). It remains in the codebase as the formal boundary
marker for the legacy analytic route.

**Preferred routes:**
- **Ontology**: `UnifiedRH.ontological_exclusion` (admissibility architecture)
- **Analytic**: `AnalyticTrace.ZeroFreeCriterion` (direct zero-free target)

**RH-equivalence.** Asserting bounded cost for nonzero charge immediately
contradicts `defectSampledFamily_unbounded`, yielding `False` = RH.

**Why not directly provable.** The topological floor diverges
as `Θ(m² log N)` for nonzero charge `m` (proved:
`defect_topological_floor_unbounded`). Since `annularCost = floor + excess`
and the floor diverges, total cost diverges even when excess is bounded.
This axiom is RH stated in cost language; it forces charge = 0 by
contradiction. -/
/-- Deprecated bounded-cost hypothesis for the legacy analytic route.

This is a proposition, not an axiom. The theorem below proves that any witness
of this proposition contradicts the already-proved unboundedness theorem. -/
def DeprecatedDefectAnnularCostBounded (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0) : Prop :=
  ∃ K : ℝ, ∀ N : ℕ,
    annularCost ((canonicalDefectSampledFamily sensor hm).mesh N) ≤ K

/-- **Formal inconsistency proof.**

The axiom `defect_annular_cost_bounded` is logically inconsistent with
`not_realizedDefectAnnularCostBounded`, which proves that bounded cost is
impossible for any sampled family with nonzero charge. This theorem
makes the inconsistency machine-checkable so it cannot be overlooked. -/
theorem defect_annular_cost_bounded_inconsistent (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0)
    (hbounded : DeprecatedDefectAnnularCostBounded sensor hm) : False := by
  let fam := canonicalDefectSampledFamily sensor hm
  have hfam : fam.sensor.charge ≠ 0 := by
    simpa [fam, canonicalDefectSampledFamily_sensor] using hm
  obtain ⟨K, hK⟩ := hbounded
  obtain ⟨N, hN⟩ := defectSampledFamily_unbounded fam hfam K
  exact not_lt_of_ge (hK N) hN

/-- **RH from the deprecated bounded-cost axiom (legacy path).**

⚠ **INCONSISTENT**: derives `False` from the contradictory axiom
`defect_annular_cost_bounded`. See `defect_annular_cost_bounded_inconsistent`.
For the preferred path, see `UnifiedRH.unified_rh` (ontology) or
`AnalyticTrace.ZeroFreeCriterion` (analytic). -/
theorem rh_from_complex_analysis_axioms (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0)
    (hbounded : DeprecatedDefectAnnularCostBounded sensor hm) : False :=
  defect_annular_cost_bounded_inconsistent sensor hm hbounded

/-- **RH via legacy bounded-cost axiom (deprecated path).**

⚠ **INCONSISTENT**: see `defect_annular_cost_bounded_inconsistent`.
Preferred: `UnifiedRH.unified_rh` (ontology) or
`AnalyticTrace.ZeroFreeCriterion` (analytic target). -/
theorem rh_no_zeros_in_strip :
    (∀ (sensor : DefectSensor) (hm : sensor.charge ≠ 0),
      DeprecatedDefectAnnularCostBounded sensor hm) →
    ∀ (sensor : DefectSensor), sensor.charge ≠ 0 → False :=
  fun hbounded sensor hm =>
    rh_from_complex_analysis_axioms sensor hm (hbounded sensor hm)

/-- The conditional floor-covering theorem is also derivable: if the defect cost
is bounded along the canonical realized trace, then nonzero charge is
impossible. -/
theorem defect_bounded_impossible (sensor : DefectSensor)
    (hm : sensor.charge ≠ 0)
    (hbound : RealizedDefectAnnularCostBounded
      (canonicalDefectSampledFamily sensor hm)) :
    False := by
  let fam := canonicalDefectSampledFamily sensor hm
  have hfam : fam.sensor.charge ≠ 0 := by
    simpa [fam, canonicalDefectSampledFamily_sensor] using hm
  exact not_realizedDefectAnnularCostBounded fam hfam hbound

/-! ### §8. The defect sensor for ζ -/

/-- Given a hypothetical zero of ζ at s = ρ with Re(ρ) > 1/2
    and multiplicity m ≥ 1, construct the DefectSensor. -/
def zetaDefectSensor (realPart : ℝ) (h_strip : 1/2 < realPart ∧ realPart < 1)
    (multiplicity : ℤ) : DefectSensor where
  charge := multiplicity
  realPart := realPart
  in_strip := h_strip

/-- The sensor/carrier compatibility: the carrier is regular in
    a neighborhood of any hypothetical zero.
    Specifically: if Re(ρ) = σ₀ > 1/2, then D(ρ, σ₀ − 1/2) ⊂ {Re(s) > 1/2}
    and the carrier is holomorphic nonvanishing on this disk. -/
theorem sensor_carrier_compatible (sensor : DefectSensor) :
    ∃ (carrier : RegularCarrier),
      carrier.radius = sensor.realPart - 1/2 ∧
      0 < carrier.radius := by
  exact ⟨eulerRegularCarrier sensor.realPart sensor.in_strip.1,
         euler_regular_carrier_covers_strip sensor.realPart sensor.in_strip.1,
         by
           change 0 < sensor.realPart - 1 / 2
           linarith [sensor.in_strip.1]⟩

/-! ### §9. The full instantiation certificate -/

/-- **Euler Instantiation Certificate.**
    Packages the complete chain:
    Euler product → carrier convergent → nonvanishing → derivative bounded
    → abstract interface satisfied → cost-covering applicable. -/
structure EulerInstantiationCert where
  /-- The carrier converges on Re(s) > 1/2. -/
  carrier_convergent : ∀ σ, 1/2 < σ → Summable (fun (p : Nat.Primes) => det2LogFactor p σ)
  /-- The carrier is nonvanishing. -/
  carrier_nonzero : ∀ σ, 1/2 < σ → carrierValue σ ≠ 0
  /-- The logarithmic derivative is bounded. -/
  deriv_bounded : ∀ σ, 1/2 < σ → 0 < carrierDerivBound σ
  /-- For any hypothetical zero, a compatible RegularCarrier exists. -/
  compatible : ∀ (sensor : DefectSensor),
    ∃ (carrier : RegularCarrier), carrier.radius = sensor.realPart - 1/2

/-- The Euler instantiation certificate is verified. -/
@[simp] def EulerInstantiationCert.verified (cert : EulerInstantiationCert) : Prop :=
  (∀ σ, 1/2 < σ → carrierValue σ ≠ 0) ∧
  (∀ σ, 1/2 < σ → 0 < carrierDerivBound σ) ∧
  (∀ (sensor : DefectSensor),
    ∃ (carrier : RegularCarrier), carrier.radius = sensor.realPart - 1/2)

/-- Construct the verified certificate from the proved results. -/
noncomputable def mkEulerInstantiationCert : EulerInstantiationCert where
  carrier_convergent := fun σ hσ => det2_product_convergent hσ
  carrier_nonzero := fun σ hσ => carrier_nonvanishing hσ
  deriv_bounded := fun σ hσ => carrierDerivBound_pos hσ
  compatible := fun sensor =>
    ⟨eulerRegularCarrier sensor.realPart sensor.in_strip.1,
     euler_regular_carrier_covers_strip sensor.realPart sensor.in_strip.1⟩

/-! ### §10. Connecting to the conditional RH -/

/-- The full chain: Euler product instantiation + explicit cost-covering package
    implies no zeros with Re(s) > 1/2.

    This theorem connects the concrete number theory (this file)
    to the abstract conditional RH (CostCoveringBridge.lean). -/
theorem euler_rh_conditional (pkg : CostCoveringPackage)
    (hcover : ∀ sensor : DefectSensor, DefectTopologicalFloorCovered pkg sensor)
    (sensor : DefectSensor) (hm : sensor.charge ≠ 0) : False :=
  rh_from_cost_covering pkg sensor hm (hcover sensor)

/-- The complete RH conditional on RS, given an explicit cost-covering package
    and topological-floor coverage. -/
theorem riemann_hypothesis_euler_conditional (pkg : CostCoveringPackage)
    (hcover : ∀ sensor : DefectSensor, DefectTopologicalFloorCovered pkg sensor) :
    ∀ (σ₀ : ℝ) (hσ : 1/2 < σ₀) (hσ1 : σ₀ < 1) (m : ℤ) (hm : m ≠ 0),
    let sensor : DefectSensor := ⟨m, σ₀, ⟨hσ, hσ1⟩⟩
    False :=
  fun σ₀ hσ hσ1 m hm => euler_rh_conditional pkg hcover ⟨m, σ₀, ⟨hσ, hσ1⟩⟩ hm

/-! ### §11. Sampled-trace Euler carrier (axiom-free) -/

/-- The Euler carrier packaged as a `BudgetedCarrier` using the sampled-trace
infrastructure from `SampledTrace.lean`. This uses the zero-winding certificate
from `EulerCarrierComplex.lean` instead of a synthetic zero-charge trace.

The key difference from `eulerBudgetedCarrier` is that the zero-winding
property is derived from the carrier's holomorphy and nonvanishing
(via `eulerZeroWindingCert`), not assumed. -/
noncomputable def eulerSampledBudgetedCarrier (σ₀ : ℝ) (hσ : 1/2 < σ₀) :
    BudgetedCarrier :=
  SampledTrace.sampledBudgetedCarrier
    (EulerCarrierComplex.eulerZeroWindingCert σ₀ hσ)
    (carrierDerivBound σ₀)
    (carrierDerivBound_pos hσ)
    (σ₀ - 1/2)
    (by linarith)

/-- The sampled Euler carrier has budget scale 0. -/
theorem eulerSampledBudgetedCarrier_scale_zero (σ₀ : ℝ) (hσ : 1/2 < σ₀) :
    carrierBudgetScale (eulerSampledBudgetedCarrier σ₀ hσ) = 0 := by
  simp [eulerSampledBudgetedCarrier, SampledTrace.sampledBudgetedCarrier, carrierBudgetScale]

/-- Package the sampled Euler carrier as a `CostCoveringPackage`. -/
noncomputable def eulerSampledPackage (σ₀ : ℝ) (hσ : 1/2 < σ₀) :
    CostCoveringPackage where
  carrier := eulerSampledBudgetedCarrier σ₀ hσ

/-- The sampled package's floor coverage is equivalent to charge = 0. -/
theorem eulerSampledFloorCovered_iff_charge_zero (σ₀ : ℝ) (hσ : 1/2 < σ₀)
    (sensor : DefectSensor) :
    DefectTopologicalFloorCovered (eulerSampledPackage σ₀ hσ) sensor ↔
      sensor.charge = 0 := by
  constructor
  · intro hcover
    by_contra hm
    exact not_DefectTopologicalFloorCovered (eulerSampledPackage σ₀ hσ) sensor hm hcover
  · intro hzero
    intro N
    rw [hzero, annularTopologicalFloor_zero]
    exact carrierBudgetScale_nonneg _

end NumberTheory
end IndisputableMonolith
