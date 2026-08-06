import Mathlib
import IndisputableMonolith.Thermodynamics.ForcedResponseSignBlindMobility

/-!
# The half-affinity normal form is detailed balance, and reciprocity is the even part

Written 2026-07-25 in response to a hostile referee read that returned REJECT on the draft
`papers/Recognition_Cost_Is_A_Large_Deviation_Rate_Function_20260725.tex`. Three of its
objections were correct and are recorded here as theorems rather than prose, because a
refutation this program agrees with is worth more formalized than argued about.

## What the referee established

**The mobility framing is empty.** `ForcedResponseSignBlindMobility` weakened the transport
premise from a drive-free mobility to a sign-blind one, and concluded that reciprocity survives
measured Tafel curvature. The conclusion is right and the argument proves nothing, because for
*any* odd flux one may define `M A = j A / (k * sinh (k * A))`, and a ratio of two odd functions
is even. So "there exists an even mobility reproducing `j`" is not a hypothesis about `j` at all:
it is equivalent to `j` being odd. `exists_even_mobility_iff_odd` is that equivalence. Every
appeal to sign-blindness should be replaced by the word odd, and the earlier module's
`generalFlux` apparatus carries no content it did not already have.

**The half is detailed balance, not recognition.** Let `F A` be the log forward rate at drive `A`
and `G A` the log reverse rate, with local detailed balance `F A + G A = A`. Then writing
`P A = F A - A/2` for the deviation from equal splitting,

    j A = exp (F A) - exp (-(G A)) = 2 * exp (P A) * sinh (A/2)

identically (`flux_eq_two_exp_deviation_mul_sinh_half`). The `sinh (A/2)` factor, with its half,
is forced by detailed balance alone and needs no recognition input whatsoever. The draft treated
the agreement of that half with the large-deviation argument scale as a coincidence of two
independent derivations. It is not a coincidence; it is the algebraic identity
`x - y = 2*sqrt(x*y)*sinh((ln x - ln y)/2)` wearing a hat. Claims of novelty for the half are
withdrawn.

**The surviving prediction is a symmetry between opposite drives.** Given detailed balance, the
flux is odd if and only if the deviation `P` is even (`odd_iff_deviation_even`). Since the
measured transfer coefficient is the differential slope `alpha = F'`, an even `P` means
`alpha A + alpha (-A) = 1`: the coefficient measured at `+eta` and at `-eta` must sum to one.
That is genuinely distinct from the detailed-balance constraint `alpha A + beta A = 1`, which
relates the two *directions at one drive*, whereas this relates *one direction at two drives*.
Marcus theory satisfies both. Asymmetric Marcus-Hush violates the second, which is what its
asymmetry parameter measures.

The draft's stated prediction, equality of two constant coefficients, was the special case in
which `P` is quadratic and one insists on constants, and the referee was right that it is
inconsistent with the same draft's Marcus example, where the coefficients are drive-dependent.

## Honest tier

\tier{Theorem} throughout: real analysis, no empirical input. The empirical status of
`alpha A + alpha (-A) = 1` is open pending the reanalysis of published asymmetric Marcus-Hush
fits, and is not asserted here.
-/

namespace IndisputableMonolith
namespace Thermodynamics
namespace ForcedResponseDetailedBalanceNormalForm

open Real
open ForcedResponseSignBlindMobility

noncomputable section

private theorem sinh_ne_zero_of_ne_zero {x : ℝ} (hx : x ≠ 0) : sinh x ≠ 0 := by
  intro h
  exact hx (Real.sinh_injective (by simpa using h))

/-! ## The mobility framing is equivalent to oddness -/

/-- The mobility that reproduces a given flux at bridge scale `k`. Division is total in Lean, so
this is defined everywhere; at `A = 0` both this and the flux it reconstructs vanish. -/
def inducedMobility (j : ℝ → ℝ) (k : ℝ) : ℝ → ℝ :=
  fun A => j A / (k * sinh (k * A))

/-- An odd flux induces an even mobility: a quotient of two odd functions is even. -/
theorem inducedMobility_even_of_odd
    {j : ℝ → ℝ} (hj : ∀ A : ℝ, j (-A) = -j A) (k A : ℝ) :
    inducedMobility j k (-A) = inducedMobility j k A := by
  rw [inducedMobility, inducedMobility, hj A,
    show k * -A = -(k * A) by ring, Real.sinh_neg]
  rw [show k * -sinh (k * A) = -(k * sinh (k * A)) by ring, neg_div_neg_eq]

/-- **The sign-blind premise carries no content beyond oddness.** For any `j`, an even mobility
reproducing `j` at some bridge scale exists exactly when `j` is odd. So the transport apparatus of
`ForcedResponseSignBlindMobility` does not constrain the response; only oddness does. -/
theorem exists_even_mobility_iff_odd (j : ℝ → ℝ) {k : ℝ} (hk : 0 < k) :
    (∃ M : ℝ → ℝ, (∀ A : ℝ, M (-A) = M A) ∧ ∀ A : ℝ, j A = generalFlux M k A) ↔
      (∀ A : ℝ, j (-A) = -j A) := by
  constructor
  · rintro ⟨M, hM, hrep⟩ A
    rw [hrep (-A), hrep A]
    exact generalFlux_odd_of_even_mobility hM k A
  · intro hodd
    refine ⟨inducedMobility j k, inducedMobility_even_of_odd hodd k, fun A => ?_⟩
    rw [generalFlux, inducedMobility]
    rcases eq_or_ne A 0 with rfl | hA
    · -- At zero drive both sides vanish, the left because an odd function does.
      have hj0 : j 0 = 0 := by
        have h := hodd 0
        rw [neg_zero] at h
        linarith
      simp [hj0]
    · have hsinh : k * sinh (k * A) ≠ 0 := by
        have hkA : k * A ≠ 0 := mul_ne_zero (ne_of_gt hk) hA
        exact mul_ne_zero (ne_of_gt hk) (sinh_ne_zero_of_ne_zero hkA)
      field_simp

/-! ## Detailed balance already produces the half-affinity sinh -/

/-- The response built from a log forward rate and a log reverse rate. -/
def responseOfLogRates (F G : ℝ → ℝ) (A : ℝ) : ℝ :=
  exp (F A) - exp (-(G A))

/-- Local detailed balance: the log rates split the drive. -/
def DetailedBalance (F G : ℝ → ℝ) : Prop :=
  ∀ A : ℝ, F A + G A = A

/-- The deviation of the forward log rate from equal splitting. -/
def deviation (F : ℝ → ℝ) : ℝ → ℝ :=
  fun A => F A - A / 2

/-- **Detailed balance alone forces the half-affinity `sinh` normal form.** No recognition input
is used, and no reciprocity: this is an algebraic identity about any pair of rates whose ratio is
the exponential of the drive. Consequently the half in `sinh (A/2)` is not evidence for anything,
and the draft's claim that its agreement with the large-deviation argument scale was a
coincidence of independent derivations is withdrawn. -/
theorem flux_eq_two_exp_deviation_mul_sinh_half
    {F G : ℝ → ℝ} (hDB : DetailedBalance F G) (A : ℝ) :
    responseOfLogRates F G A = 2 * exp (deviation F A) * sinh (A / 2) := by
  have hG : G A = A - F A := by have := hDB A; linarith
  have key : exp (F A - A / 2) * (exp (A / 2) - exp (-(A / 2)))
      = exp (F A) - exp (-(A - F A)) := by
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add,
      show F A - A / 2 + A / 2 = F A by ring,
      show F A - A / 2 + -(A / 2) = -(A - F A) by ring]
  simp only [responseOfLogRates, deviation, hG, Real.sinh_eq]
  rw [← key]
  ring

/-! ## Reciprocity is exactly evenness of the deviation -/

/-- **Given detailed balance, the flux is odd if and only if the deviation is even.** This is the
surviving content of reciprocity for charge transfer. In terms of the differential transfer
coefficient `alpha = F'`, an even deviation says `alpha A + alpha (-A) = 1`: the coefficient
measured at opposite drives sums to one. That is a different statement from the detailed-balance
constraint `alpha A + beta A = 1`, which compares the two directions at a single drive. -/
theorem odd_iff_deviation_even
    {F G : ℝ → ℝ} (hDB : DetailedBalance F G) :
    (∀ A : ℝ, responseOfLogRates F G (-A) = -responseOfLogRates F G A) ↔
      (∀ A : ℝ, deviation F (-A) = deviation F A) := by
  constructor
  · intro hodd A
    -- Both sides are `2 * exp (deviation) * sinh (A/2)`, so cancel the nonzero sinh at a
    -- convenient nonzero drive and then transport the conclusion.
    have key : ∀ B : ℝ, B ≠ 0 → deviation F (-B) = deviation F B := by
      intro B hB
      have h1 := hodd B
      rw [flux_eq_two_exp_deviation_mul_sinh_half hDB (-B),
        flux_eq_two_exp_deviation_mul_sinh_half hDB B] at h1
      rw [show (-B) / 2 = -(B / 2) by ring, Real.sinh_neg] at h1
      have hsB : sinh (B / 2) ≠ 0 :=
        sinh_ne_zero_of_ne_zero (by simpa using hB)
      have hexp : exp (deviation F (-B)) = exp (deviation F B) := by
        have h2 : 2 * exp (deviation F (-B)) * sinh (B / 2)
            = 2 * exp (deviation F B) * sinh (B / 2) := by linear_combination -h1
        have h3 := mul_right_cancel₀ hsB h2
        linarith
      exact Real.exp_eq_exp.mp hexp
    rcases eq_or_ne A 0 with rfl | hA
    · simp
    · exact key A hA
  · intro heven A
    rw [flux_eq_two_exp_deviation_mul_sinh_half hDB (-A),
      flux_eq_two_exp_deviation_mul_sinh_half hDB A, heven A,
      show (-A) / 2 = -(A / 2) by ring, Real.sinh_neg]
    ring

/-- The Marcus deviation, with the factor the draft got wrong. A measured transfer coefficient is
a differential slope, `alpha = dF/dA`, so `alpha A = 1/2 + A/(2*Lambda)` integrates to
`F A = A/2 + A^2/(4*Lambda)` and the deviation is `A^2/(4*Lambda)`, not `A^2/(2*Lambda)`. The
draft placed the coefficient directly in the exponent and so doubled the quadratic term. -/
def marcusDeviation (Lambda : ℝ) : ℝ → ℝ :=
  fun A => A ^ 2 / (4 * Lambda)

/-- The Marcus deviation is even, so Marcus kinetics have an odd current. Reciprocity is
therefore consistent with the measured drift of the transfer coefficient, which was the one
conclusion of the retracted audit that survives. -/
theorem marcusDeviation_even (Lambda A : ℝ) :
    marcusDeviation Lambda (-A) = marcusDeviation Lambda A := by
  simp only [marcusDeviation, neg_sq]

/-- Marcus kinetics are odd, stated through the normal form. -/
theorem marcus_response_odd
    {F G : ℝ → ℝ} (hDB : DetailedBalance F G) (Lambda : ℝ)
    (hF : deviation F = marcusDeviation Lambda) (A : ℝ) :
    responseOfLogRates F G (-A) = -responseOfLogRates F G A := by
  refine (odd_iff_deviation_even hDB).mpr (fun B => ?_) A
  rw [hF]
  exact marcusDeviation_even Lambda B

/-! ## The premise named honestly: state exchange

A second hostile read (four-member panel, 2026-07-25) granted that `alpha A + alpha (-A) = 1` is
genuinely distinct from local detailed balance, and two members proved it by counterexample: for
Butler-Volmer with `F A = log i0 + alpha * A` and `G A = -log i0 + (1-alpha) * A`, detailed balance
holds and the exchange current is well defined, yet `P A = log i0 + (alpha - 1/2) * A` is not even
whenever `alpha` differs from one half. So the relation is not smuggled in.

But the panel also identified a real gap: the relation is *equivalent* to a state-exchange symmetry,
`k_plus A = k_minus (-A)`, and the paper asserted rather than derived the bridge from reciprocity
`J x = J (1/x)` to that symmetry. The bridge is stated here as what it is, an equivalence, so the
premise is visible instead of buried. Reciprocity says the cost is unchanged when the ledger ratio
is inverted, that is when the two states swap which one counts as forward; state exchange is that
same swap at the level of rates. Calling it a premise rather than a consequence is the honest move.
-/

/-- State-exchange symmetry: the forward rate at drive `A` equals the reverse rate at drive `-A`.
Recall `k_plus A = exp (F A)` and `k_minus A = exp (-(G A))` in this parameterization. -/
def StateExchange (F G : ℝ → ℝ) : Prop :=
  ∀ A : ℝ, F A = -(G (-A))

/-- **State exchange is exactly evenness of the deviation, hence exactly reciprocity.** Given
detailed balance, the two are the same hypothesis, so the observable content of
`alpha A + alpha (-A) = 1` is the interchangeability of the two states. -/
theorem stateExchange_iff_deviation_even
    {F G : ℝ → ℝ} (hDB : DetailedBalance F G) :
    StateExchange F G ↔ (∀ A : ℝ, deviation F (-A) = deviation F A) := by
  constructor
  · intro hSE A
    have hG : G (-A) = -A - F (-A) := by have := hDB (-A); linarith
    have hF : F A = A + F (-A) := by
      have := hSE A; rw [hG] at this; linarith
    simp only [deviation]
    linarith
  · intro hev A
    have hG : G (-A) = -A - F (-A) := by have := hDB (-A); linarith
    have h := hev A
    simp only [deviation] at h
    rw [hG]
    linarith

/-! ## The instrument: the even part of the response reads out the asymmetry directly -/

/-- The even part of the response, doubled. This is the quantity a lock-in amplifier measures as
the second harmonic of the current under a small sinusoidal drive, and it is zero for an odd
response. -/
def evenResponse (F G : ℝ → ℝ) (A : ℝ) : ℝ :=
  responseOfLogRates F G A + responseOfLogRates F G (-A)

/-- **The even response is an exact readout of the deviation's asymmetry.** No differentiability,
no fitting, and no model of the barrier: given detailed balance alone, the even part of the
current equals `2 sinh(A/2)` times the difference of the deviation's exponentials at opposite
drives. This is why an even-harmonic null is a direct measurement of reciprocity, and why a
curve-fitting meta-analysis of asymmetry parameters is the wrong instrument for the same question. -/
theorem evenResponse_eq_sinh_mul_exp_diff
    {F G : ℝ → ℝ} (hDB : DetailedBalance F G) (A : ℝ) :
    evenResponse F G A = 2 * sinh (A / 2) * (exp (deviation F A) - exp (deviation F (-A))) := by
  rw [evenResponse, flux_eq_two_exp_deviation_mul_sinh_half hDB A,
    flux_eq_two_exp_deviation_mul_sinh_half hDB (-A),
    show (-A) / 2 = -(A / 2) by ring, Real.sinh_neg]
  ring

/-- Reciprocity kills the even response identically. The contrapositive is the measurement: any
nonzero even component of the current at any drive refutes reciprocity for that system. -/
theorem evenResponse_eq_zero_of_deviation_even
    {F G : ℝ → ℝ} (hDB : DetailedBalance F G)
    (hev : ∀ A : ℝ, deviation F (-A) = deviation F A) (A : ℝ) :
    evenResponse F G A = 0 := by
  rw [evenResponse_eq_sinh_mul_exp_diff hDB A, hev A]
  ring

/-- And a nonzero even response at a single drive refutes it. This is the falsifier in the form an
experiment delivers it: one number, at one drive, with no fit. -/
theorem deviation_not_even_of_evenResponse_ne_zero
    {F G : ℝ → ℝ} (hDB : DetailedBalance F G) {A : ℝ}
    (hne : evenResponse F G A ≠ 0) :
    ¬ (∀ B : ℝ, deviation F (-B) = deviation F B) :=
  fun hev => hne (evenResponse_eq_zero_of_deviation_even hDB hev A)

/-- **A constant deviation is the symmetric law, and only then is the coefficient one half.**
The draft's headline prediction was this special case, and the referee correctly observed that it
is inconsistent with a drive-dependent coefficient. Stated here so the restriction is explicit. -/
theorem deviation_const_iff_symmetric_law
    {F G : ℝ → ℝ} (hDB : DetailedBalance F G) (c : ℝ)
    (hconst : deviation F = fun _ => c) (A : ℝ) :
    responseOfLogRates F G A = 2 * exp c * sinh (A / 2) := by
  rw [flux_eq_two_exp_deviation_mul_sinh_half hDB A, hconst]

end

end ForcedResponseDetailedBalanceNormalForm
end Thermodynamics
end IndisputableMonolith
