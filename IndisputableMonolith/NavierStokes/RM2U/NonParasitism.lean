import IndisputableMonolith.NavierStokes.RM2U.Core
import IndisputableMonolith.NavierStokes.RM2U.EnergyIdentity
import IndisputableMonolith.NavierStokes.RM2U.RM2Closure

/-!
# RM2U.NonParasitism (the single hard gate)

This file is where the RS-aligned “non-parasitism” content should ultimately live.

**Intent:** isolate the only genuinely hard statement as a single hypothesis (temporarily),
so the rest of the RM2U → RM2 pipeline is clean and checkable.

Non-parasitism, in the PDE translation used by the manuscript, is:

> The tail-flux / boundary term at infinity vanishes for the relevant \(\ell=2\) coefficient.

In Lean, this is `TailFluxVanish P.A P.A'`.
-/

namespace IndisputableMonolith
namespace NavierStokes
namespace RM2U

open MeasureTheory Set Filter

/-- Temporary hypothesis: “non-parasitism” for a fixed time-slice coefficient profile. -/
structure NonParasitismHypothesis (P : RM2URadialProfile) : Prop where
  tailFluxVanish : TailFluxVanish P.A P.A'

/-!
## Research bets as isolated interfaces

These are *interfaces*, not proofs: each corresponds to one of the bet docs:

- `docs/RM2U_BET_1_ATTACK.md`
- `docs/RM2U_BET_2_ATTACK.md`
- `docs/RM2U_BET_3_ATTACK.md`

Keeping these in this file ensures the rest of the RM2U→RM2 pipeline remains purely algebraic.
-/

/-- **Bet 1 (integrability route)**: prove integrability of the tail-flux boundary term
`(-A) * (A' * r^2)` and its derivative on `(1,∞)`. -/
structure Bet1BoundaryIntegrableHypothesis (P : RM2URadialProfile) : Prop where
  hB_int :
    IntegrableOn (fun x : ℝ => (-P.A x) * ((P.A' x) * (x ^ 2))) (Set.Ioi (1 : ℝ)) volume
  hB'_int :
    IntegrableOn
      (fun x : ℝ =>
        (-(P.A' x)) * ((P.A' x) * (x ^ 2)) + (-P.A x) * ((P.A'' x) * (x ^ 2) + (P.A' x) * (2 * x)))
      (Set.Ioi (1 : ℝ)) volume

theorem nonParasitism_of_bet1 (P : RM2URadialProfile) (h : Bet1BoundaryIntegrableHypothesis P) :
    NonParasitismHypothesis P :=
  ⟨RM2U.tailFluxVanish_of_integrable (P := P) h.hB_int h.hB'_int⟩

/-!
### Bet 1 helper: `B ∈ L¹((1,∞))` from a weighted \(L^2\) hypothesis

The boundary term is:

`B(r) = (-A r) * (A' r * r^2) = ((-A r) * r) * ((A' r) * r)`.

So a **checkable sufficient condition** for `B ∈ L¹((1,∞))` is:

- `A(r) * r ∈ L²((1,∞))` and
- `A'(r) * r ∈ L²((1,∞))`.

The second condition is already implied by `CoerciveL2Bound` (since it is exactly
`(A')^2 * r^2` integrable). The first is a genuinely stronger tail/moment condition that might be
provable from additional PDE input or a non-resonant-scale argument.
-/

/-- If `A(r) * r ∈ L²((1,∞))` and `A'(r) * r ∈ L²((1,∞))`, then the boundary term
`B(r)=(-A) * (A'*r^2)` is integrable on `(1,∞)`. -/
theorem bet1_boundaryTerm_integrable_of_L2_mul_r
    (P : RM2URadialProfile)
    (hA2r : IntegrableOn (fun r : ℝ => (P.A r) ^ 2 * (r ^ 2)) (Set.Ioi (1 : ℝ)) volume)
    (hA'2r : IntegrableOn (fun r : ℝ => (P.A' r) ^ 2 * (r ^ 2)) (Set.Ioi (1 : ℝ)) volume) :
    IntegrableOn (fun r : ℝ => (-P.A r) * ((P.A' r) * (r ^ 2))) (Set.Ioi (1 : ℝ)) volume := by
  classical
  -- Work on the restricted measure.
  let μ := (volume.restrict (Set.Ioi (1 : ℝ)))

  -- Show `(-A r)*r ∈ L²` and `(A' r)*r ∈ L²`.
  have hcontA : ContinuousOn P.A (Set.Ioi (1 : ℝ)) := by
    intro x hx
    exact (P.hA x hx).continuousAt.continuousWithinAt
  have hcontA' : ContinuousOn P.A' (Set.Ioi (1 : ℝ)) := by
    intro x hx
    exact (P.hA' x hx).continuousAt.continuousWithinAt
  have hf_meas : AEStronglyMeasurable (fun r : ℝ => (-P.A r) * r) μ := by
    have hcont : ContinuousOn (fun r : ℝ => (-P.A r) * r) (Set.Ioi (1 : ℝ)) := by
      simpa using (hcontA.neg.mul (continuous_id.continuousOn))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hg_meas : AEStronglyMeasurable (fun r : ℝ => (P.A' r) * r) μ := by
    have hcont : ContinuousOn (fun r : ℝ => (P.A' r) * r) (Set.Ioi (1 : ℝ)) := by
      simpa using (hcontA'.mul (continuous_id.continuousOn))
    exact hcont.aestronglyMeasurable measurableSet_Ioi

  have hf_L2 : MeasureTheory.MemLp (fun r : ℝ => (-P.A r) * r) 2 μ := by
    -- use `memLp_two_iff_integrable_sq`
    refine (MeasureTheory.memLp_two_iff_integrable_sq (μ := μ) hf_meas).2 ?_
    -- square equals `A^2 * r^2`
    have : Integrable (fun r : ℝ => (P.A r) ^ 2 * (r ^ 2)) μ := by
      simpa [MeasureTheory.IntegrableOn, μ] using hA2r
    -- rewrite the integrand
    simpa [pow_two, μ, mul_assoc, mul_left_comm, mul_comm] using this

  have hg_L2 : MeasureTheory.MemLp (fun r : ℝ => (P.A' r) * r) 2 μ := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq (μ := μ) hg_meas).2 ?_
    have : Integrable (fun r : ℝ => (P.A' r) ^ 2 * (r ^ 2)) μ := by
      simpa [MeasureTheory.IntegrableOn, μ] using hA'2r
    simpa [pow_two, μ, mul_assoc, mul_left_comm, mul_comm] using this

  -- L² × L² → L¹ by Hölder (p=q=2, r=1).
  have hprod : Integrable (fun r : ℝ => ((-P.A r) * r) * ((P.A' r) * r)) μ := by
    -- `HolderTriple 2 2 1` is an instance
    simpa [Pi.mul_def] using (MeasureTheory.MemLp.integrable_mul (μ := μ) hf_L2 hg_L2)

  -- rewrite the product as the boundary term.
  have : Integrable (fun r : ℝ => (-P.A r) * ((P.A' r) * (r ^ 2))) μ := by
    -- pointwise: `((-A)*r) * ((A')*r) = (-A) * (A' * r^2)`
    refine hprod.congr ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro r hr
    ring
  simpa [MeasureTheory.IntegrableOn, μ] using this

/-- Convenience wrapper: if `CoerciveL2Bound P` holds, it suffices to prove only the stronger
weighted \(L^2\) tail moment `∫ (A^2 * r^2) < ∞` to get `B ∈ L¹`. -/
theorem bet1_boundaryTerm_integrable_of_A2r_and_coercive
    (P : RM2URadialProfile)
    (hA2r : IntegrableOn (fun r : ℝ => (P.A r) ^ 2 * (r ^ 2)) (Set.Ioi (1 : ℝ)) volume)
    (hCoercive : CoerciveL2Bound P) :
    IntegrableOn (fun r : ℝ => (-P.A r) * ((P.A' r) * (r ^ 2))) (Set.Ioi (1 : ℝ)) volume :=
  bet1_boundaryTerm_integrable_of_L2_mul_r (P := P) hA2r hCoercive.2

/-!
### Bet 1 (alternate surface): rewrite the `B'` integrand using `rm2uOp`

The “raw” Bet‑1 interface requires integrability of an expression involving `A''`.
Using the algebraic identity in `RM2U.EnergyIdentity`, we can replace that with integrability of
the RM2U operator pairing `rm2uOp*A*r^2` plus the coercive terms (which are already the natural
output of the RM2U energy identity).

This does **not** solve Bet 1, but it shrinks the remaining analytic work to a more PDE-aligned
pairing estimate.
-/

/-- Alternate Bet‑1 interface: keep the same boundary term `B` integrability, but replace the `B'`
integrability surface by the RM2U operator pairing plus coercive \(L^2\) control. -/
structure Bet1BoundaryIntegrableHypothesisAlt (P : RM2URadialProfile) : Prop where
  hB_int :
    IntegrableOn (fun x : ℝ => (-P.A x) * ((P.A' x) * (x ^ 2))) (Set.Ioi (1 : ℝ)) volume
  hPair_int :
    IntegrableOn (fun x : ℝ => (rm2uOp P x) * (P.A x) * (x ^ 2)) (Set.Ioi (1 : ℝ)) volume
  hCoercive : CoerciveL2Bound P

/-- `Bet1BoundaryIntegrableHypothesisAlt` implies the original Bet‑1 hypothesis. -/
theorem bet1_of_bet1Alt (P : RM2URadialProfile) (h : Bet1BoundaryIntegrableHypothesisAlt P) :
    Bet1BoundaryIntegrableHypothesis P := by
  refine ⟨h.hB_int, ?_⟩
  -- Work on the restricted measure.
  let μ := (volume.restrict (Set.Ioi (1 : ℝ)))

  -- Build integrability of the RM2U-rewritten RHS:
  have hPair : Integrable (fun x : ℝ => (rm2uOp P x) * (P.A x) * (x ^ 2)) μ := by
    simpa [IntegrableOn, μ] using h.hPair_int
  have hA2 : Integrable (fun x : ℝ => (P.A x) ^ 2) μ := by
    simpa [IntegrableOn, μ] using h.hCoercive.1
  have hAprime2 : Integrable (fun x : ℝ => (P.A' x) ^ 2 * (x ^ 2)) μ := by
    simpa [IntegrableOn, μ] using h.hCoercive.2

  have hRHS :
      Integrable
        (fun x : ℝ =>
          (rm2uOp P x) * (P.A x) * (x ^ 2)
            - (P.A' x) ^ 2 * (x ^ 2)
            - 6 * (P.A x) ^ 2) μ := by
    -- close under subtraction and scalar multiplication
    have h6A2 : Integrable (fun x : ℝ => 6 * (P.A x) ^ 2) μ := by
      simpa [mul_assoc] using (hA2.const_mul (6 : ℝ))
    exact (hPair.sub hAprime2).sub h6A2

  -- Show the original Bet‑1 integrand agrees a.e. with the rewritten RHS on `(1,∞)`.
  have hAE :
      (fun x : ℝ =>
            (-(P.A' x)) * ((P.A' x) * (x ^ 2))
              + (-P.A x) * ((P.A'' x) * (x ^ 2) + (P.A' x) * (2 * x)))
        =ᵐ[μ]
        (fun x : ℝ =>
          (rm2uOp P x) * (P.A x) * (x ^ 2)
            - (P.A' x) ^ 2 * (x ^ 2)
            - 6 * (P.A x) ^ 2) := by
    -- pointwise on `x > 1` we can apply the algebraic lemma (`x ≠ 0`).
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) (mem_Ioi.1 hx))
    -- rewrite using the proved identity
    simpa using (bet1_boundaryTerm_deriv_integrand_eq (P := P) (r := x) hx0)

  -- Transfer integrability across the a.e. equality.
  have : Integrable
      (fun x : ℝ =>
            (-(P.A' x)) * ((P.A' x) * (x ^ 2))
              + (-P.A x) * ((P.A'' x) * (x ^ 2) + (P.A' x) * (2 * x))) μ :=
    hRHS.congr hAE.symm

  simpa [IntegrableOn, μ] using this

/-- **Bet 2 (self-falsification route)**: encode “if tail-flux does *not* vanish, we reach a contradiction”.
This keeps the interface honest while leaving the contradiction mechanism open. -/
structure Bet2SelfFalsificationHypothesis (P : RM2URadialProfile) : Prop where
  selfFalsify : (¬ TailFluxVanish P.A P.A') → False

/-!
## Bet 2 (prime/non-resonant scale schedule) — skeleton

This section encodes a *generic* contradiction shape that could plausibly use primes/coprime
cycles as a “non-resonant” schedule for extracting disjoint scale contributions.

It does **not** prove RM2U; it just provides a clean interface:

- show that **if** tail-flux does not vanish, then along some (prime) schedule one gets a uniform
  lower bound on the tail export (a “persistent parasitism signal”);
- independently show (from energy / budget / disjointness) that the same schedule forces the
  absolute tail export to be summable;
- contradiction, hence tail-flux must vanish.

The only “prime content” we hard-code here is the existence of a canonical strictly increasing
pairwise-coprime schedule `n ↦ nthPrime n`.
-/

namespace Bet2PrimeSchedule

open Nat

/-- Canonical prime scale schedule: `pₙ = (n)th prime`. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

theorem nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) := by
  -- `Nat.prime_nth_prime` is in `Mathlib/NumberTheory/PrimeCounting`.
  simpa [nthPrime] using (Nat.prime_nth_prime n)

theorem strictMono_nthPrime : StrictMono nthPrime := by
  simpa [nthPrime] using (Nat.nth_strictMono Nat.infinite_setOf_prime)

theorem pairwise_coprime_nthPrime : Pairwise fun i j => Nat.Coprime (nthPrime i) (nthPrime j) := by
  intro i j hij
  have hpi : Nat.Prime (nthPrime i) := nthPrime_prime i
  have hpj : Nat.Prime (nthPrime j) := nthPrime_prime j
  have hne : nthPrime i ≠ nthPrime j := (strictMono_nthPrime.injective.ne hij)
  -- Use `Nat.Prime.coprime_iff_not_dvd` + prime divisibility rigidity.
  refine (Nat.Prime.coprime_iff_not_dvd hpi).2 ?_
  intro hdiv
  have : nthPrime i = nthPrime j := (Nat.prime_dvd_prime_iff_eq hpi hpj).1 hdiv
  exact hne this

/-- A “non-resonant” integer schedule: strictly increasing and pairwise coprime. -/
structure NonResonantSchedule where
  s : ℕ → ℕ
  strictMono : StrictMono s
  pairwise_coprime : Pairwise fun i j => Nat.Coprime (s i) (s j)

/-- The canonical non-resonant schedule given by primes. -/
noncomputable def canonical : NonResonantSchedule :=
  { s := nthPrime
    strictMono := strictMono_nthPrime
    pairwise_coprime := pairwise_coprime_nthPrime }

/-- Generic divergence fact: a uniform positive lower bound on `|a n|` prevents summability. -/
theorem not_summable_of_uniform_abs_lowerBound {a : ℕ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hlow : ∀ n, ε ≤ |a n|) :
    ¬ Summable (fun n => |a n|) := by
  intro hsum
  have ht : Tendsto (fun n => |a n|) atTop (nhds 0) :=
    (Summable.tendsto_atTop_zero hsum)
  -- pick `n` large enough so `|a n| < ε`, contradicting the uniform lower bound.
  have hEvt : ∀ᶠ n in atTop, |a n| < ε := (ht.eventually_lt_const hε)
  rcases (Filter.eventually_atTop.1 hEvt) with ⟨N, hN⟩
  have hcontra : ε ≤ |a N| := hlow N
  exact (not_lt_of_ge hcontra) (hN N (le_rfl))

/-- **Bet 2 prime-schedule interface**:
if non-parasitism fails, you can lower-bound `|tailFlux|` *along the prime schedule*;
and separately you can prove a summability/budget bound along the same schedule. -/
structure PrimeScheduleSelfFalsification (P : RM2URadialProfile) : Prop where
  /-- A lower bound along the prime schedule implied by failure of tail-flux vanishing. -/
  lowerBound_of_notVanish :
    (¬ TailFluxVanish P.A P.A') →
      ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, ε ≤ |tailFlux P.A P.A' (nthPrime n)|
  /-- A (budget/disjointness) summability statement along the same schedule. -/
  summable_abs :
    Summable (fun n : ℕ => |tailFlux P.A P.A' (nthPrime n)|)

/-- The prime-schedule interface yields the standard Bet-2 “self-falsification” hypothesis. -/
theorem bet2_of_primeSchedule (P : RM2URadialProfile) (h : PrimeScheduleSelfFalsification P) :
    Bet2SelfFalsificationHypothesis P := by
  refine ⟨?_⟩
  intro hnot
  rcases h.lowerBound_of_notVanish hnot with ⟨ε, hε, hlow⟩
  have : ¬ Summable (fun n : ℕ => |tailFlux P.A P.A' (nthPrime n)|) :=
    not_summable_of_uniform_abs_lowerBound (a := fun n => tailFlux P.A P.A' (nthPrime n)) hε hlow
  exact this h.summable_abs

end Bet2PrimeSchedule

/-!
### Optional finer-grained Bet 2 interfaces (U-4 / one-cylinder payment view)

The Bet 2 execution plan (`docs/RM2U_BET_2_EXECUTION_PLAN.md`) works at the level of a *single rescaled cylinder*
and derives a contradiction by forcing a strictly-positive “payment” lower bound on that cylinder which is then
incompatible with a small-scale upper bound.

We do **not** have the full PDE objects (ρ, ξ, σ, tail strain fields) formalized in Lean yet, so the most honest
way to reflect that work here is as **Prop-only hypothesis interfaces** parameterized by abstract predicates.

These interfaces are designed to be instantiated later once the running-max cylinder solution objects exist in Lean.
-/

namespace Bet2U4

/-- Abstract normalized cylinder payments.

In the TeX, these are:
- `PayXi r  := (1/r^2) ∬_{Q_r} ρ^{3/2} |∇ξ|^2`
- `PayRho r := (1/r^2) η^{-1} ∬_{Q_r ∩ {1-2η<ρ<1-η}} |∇(ρ^{3/4})|^2`

At the Lean spec layer, we keep them as uninterpreted functions `ℝ → ℝ`. -/
structure Payments where
  payXi : ℝ → ℝ
  payRho : ℝ → ℝ
  payXi_nonneg : ∀ r : ℝ, 0 ≤ payXi r
  payRho_nonneg : ∀ r : ℝ, 0 ≤ payRho r

/-- **U-4 cylinder payment upper bound (spec layer):** normalized payments become small at small scales.

This mirrors TeX Hypothesis `hyp:U4_payment_upper_bound`. We keep the decay modulus abstract. -/
structure U4PaymentUpperBoundHypothesis (P : Payments) : Prop where
  exists_beta :
    ∃ β : ℝ → ℝ,
      (∀ r : ℝ, 0 < r → 0 ≤ β r) ∧
        (∀ ε : ℝ, 0 < ε → ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 → β r ≤ ε) ∧
          ∀ r : ℝ, 0 < r → P.payXi r + P.payRho r ≤ β r

/-- **C2-style vanishing positive injection (spec layer):** a scale-modulus controlling the (scale-invariant)
positive stretching injection `injPos r` on cylinders.

This mirrors TeX Hypothesis `hyp:C2_vanishing_injection` in its scale-invariant form
(`navier-dec-12-rewrite.tex`, Eq. `eq:C2-stretch-hyp`). -/
structure C2VanishingInjectionHypothesis (injPos : ℝ → ℝ) : Prop where
  exists_alpha :
    ∃ α : ℝ → ℝ,
      (∀ r : ℝ, 0 < r → 0 ≤ α r) ∧
        (∀ ε : ℝ, 0 < ε → ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 → α r ≤ ε) ∧
          ∀ r : ℝ, 0 < r → injPos r ≤ α r

/-- Alias for the U-4 “rate-strengthened” injection gate: in practice one instantiates `injPos r` with
`(1/r^2) ∬_{Q_r} ρ^{3/2} σ_+` (once the PDE objects exist in Lean). -/
abbrev U4VanishingInjectionRateHypothesis (injPos : ℝ → ℝ) : Prop :=
  C2VanishingInjectionHypothesis injPos

/-- If the (normalized) positive injection `injPos r` vanishes at small scales, then so does the
rescaled injection `injPos (2*r)`. This is the only “scale-change” bookkeeping we need to match the TeX
convention where many inequalities naturally live on `Q_{2r}`. -/
theorem c2VanishingInjection_comp_two (injPos : ℝ → ℝ) (h : C2VanishingInjectionHypothesis injPos) :
    C2VanishingInjectionHypothesis (fun r => injPos (2 * r)) := by
  classical
  rcases h.exists_alpha with ⟨α, hα_nonneg, hα_lim, hInj_le⟩
  refine ⟨fun r => α (2 * r), ?_, ?_, ?_⟩
  · intro r hr
    have hr2 : 0 < 2 * r := by nlinarith
    exact hα_nonneg (2 * r) hr2
  · intro ε hε
    rcases hα_lim ε hε with ⟨r0, hr0, hr0_bound⟩
    refine ⟨r0 / 2, by nlinarith, ?_⟩
    intro r hr hrr0
    have hr2 : 0 < 2 * r := by nlinarith
    have h2r_le : 2 * r ≤ r0 := by nlinarith
    simpa using hr0_bound (2 * r) hr2 h2r_le
  · intro r hr
    have hr2 : 0 < 2 * r := by nlinarith
    simpa using hInj_le (2 * r) hr2

/-- **C2 ⇒ U4 upper bound** (spec layer): if payments are bounded by positive injection plus a vanishing error,
then vanishing positive injection implies vanishing payments.

This abstracts the TeX deduction
`lem:U4_payment_upper_bound_of_U4_vanishing_injection_rate` once `injPos r` is instantiated by the
**normalized** injection `(1/r^2) ∬_{Q_r} ρ^{3/2} σ_+` and `err r` packages the lower-order running-max
terms (e.g. the `O(r)` errors after dividing by `r^2`). -/
theorem u4PaymentUpperBound_of_injection
    (P : Payments) (injPos err : ℝ → ℝ)
    (hInj : C2VanishingInjectionHypothesis injPos)
    (hErr :
      ∃ e : ℝ → ℝ,
        (∀ r : ℝ, 0 < r → 0 ≤ e r) ∧
          (∀ ε : ℝ, 0 < ε → ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 → e r ≤ ε) ∧
            ∀ r : ℝ, 0 < r → err r ≤ e r)
    (hBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → P.payXi r + P.payRho r ≤ C * injPos r + err r) :
    U4PaymentUpperBoundHypothesis P := by
  classical
  rcases hInj.exists_alpha with ⟨α, hα_nonneg, hα_lim, hInj_le⟩
  rcases hErr with ⟨e, he_nonneg, he_lim, hErr_le⟩
  rcases hBound with ⟨C, hC0, hBound⟩
  refine ⟨fun r => C * α r + e r, ?_, ?_, ?_⟩
  · intro r hr
    exact add_nonneg (mul_nonneg hC0 (hα_nonneg r hr)) (he_nonneg r hr)
  · intro ε hε
    -- split ε into two halves
    have hε2 : 0 < ε / 2 := by nlinarith
    have hpos : 0 < ε / (2 * max C 1) := by
      have hmaxpos : 0 < max C 1 :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
      have hden : 0 < 2 * max C 1 := by nlinarith
      exact div_pos hε hden
    rcases hα_lim (ε / (2 * max C 1)) hpos with ⟨rα, hrα, hrα_bound⟩
    rcases he_lim (ε / 2) hε2 with ⟨re, hre, hre_bound⟩
    refine ⟨min rα re, lt_min hrα hre, ?_⟩
    intro r hr hrr0
    have hrrα : r ≤ rα := le_trans hrr0 (min_le_left _ _)
    have hrre : r ≤ re := le_trans hrr0 (min_le_right _ _)
    have hα : α r ≤ ε / (2 * max C 1) := hrα_bound r hr hrrα
    have he : e r ≤ ε / 2 := hre_bound r hr hrre
    -- bound `C * γ r` by `ε/2`
    have hC1 : C ≤ max C 1 := le_max_left _ _
    have hmaxpos : 0 < max C 1 :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
    have hCα : C * α r ≤ (max C 1) * α r := mul_le_mul_of_nonneg_right hC1 (hα_nonneg r hr)
    have hα' : (max C 1) * α r ≤ (max C 1) * (ε / (2 * max C 1)) :=
      mul_le_mul_of_nonneg_left hα (le_of_lt hmaxpos)
    have hhalf : (max C 1) * (ε / (2 * max C 1)) = ε / 2 := by
      field_simp [ne_of_gt hmaxpos]
    have hCα' : C * α r ≤ ε / 2 := by
      exact hCα.trans (hα'.trans (by simp [hhalf]))
    -- combine
    have : C * α r + e r ≤ ε / 2 + ε / 2 := add_le_add hCα' he
    nlinarith
  · intro r hr
    have hPay : P.payXi r + P.payRho r ≤ C * injPos r + err r := hBound r hr
    have hInj' : injPos r ≤ α r := hInj_le r hr
    have hErr' : err r ≤ e r := hErr_le r hr
    have : C * injPos r + err r ≤ C * α r + e r :=
      add_le_add (mul_le_mul_of_nonneg_left hInj' hC0) hErr'
    exact hPay.trans this

/-- Convenience wrapper: `U4VanishingInjectionRateHypothesis` is just an alias of
`C2VanishingInjectionHypothesis`, intended for the normalized injection rate used by U‑4. -/
theorem u4PaymentUpperBound_of_u4InjectionRate
    (P : Payments) (injRate err : ℝ → ℝ)
    (hInj : U4VanishingInjectionRateHypothesis injRate)
    (hErr :
      ∃ e : ℝ → ℝ,
        (∀ r : ℝ, 0 < r → 0 ≤ e r) ∧
          (∀ ε : ℝ, 0 < ε → ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 → e r ≤ ε) ∧
            ∀ r : ℝ, 0 < r → err r ≤ e r)
    (hBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → P.payXi r + P.payRho r ≤ C * injRate r + err r) :
    U4PaymentUpperBoundHypothesis P := by
  simpa [U4VanishingInjectionRateHypothesis] using
    (u4PaymentUpperBound_of_injection (P := P) (injPos := injRate) (err := err) hInj hErr hBound)

/-- **U-4 payment control interface (spec layer):** the (normalized) payments are bounded by
the (normalized) positive injection rate plus an `o(1)` error.

This mirrors the TeX interface `hyp:U4_payments_controlled_by_injection_rate`.
It is the minimal PDE analytic input needed to turn a vanishing injection rate into
`U4PaymentUpperBoundHypothesis`. -/
structure U4PaymentsControlledByInjectionRateHypothesis
    (P : Payments) (injRate : ℝ → ℝ) : Prop where
  exists_bound :
    ∃ (C : ℝ) (err : ℝ → ℝ),
      0 ≤ C ∧
        (∃ e : ℝ → ℝ,
          (∀ r : ℝ, 0 < r → 0 ≤ e r) ∧
            (∀ ε : ℝ, 0 < ε → ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 → e r ≤ ε) ∧
              ∀ r : ℝ, 0 < r → err r ≤ e r) ∧
          ∀ r : ℝ, 0 < r → P.payXi r + P.payRho r ≤ C * injRate r + err r

/-- **U-4 `PayXi` control by the (normalized) positive injection rate (spec layer). -/
structure U4PayXiControlledByInjectionRateHypothesis
    (P : Payments) (injRate : ℝ → ℝ) : Prop where
  exists_bound :
    ∃ (C : ℝ) (err : ℝ → ℝ),
      0 ≤ C ∧
        (∃ e : ℝ → ℝ,
          (∀ r : ℝ, 0 < r → 0 ≤ e r) ∧
            (∀ ε : ℝ, 0 < ε → ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 → e r ≤ ε) ∧
              ∀ r : ℝ, 0 < r → err r ≤ e r) ∧
          ∀ r : ℝ, 0 < r → P.payXi r ≤ C * injRate (2 * r) + err r

/-- **U-4 `PayRho` control by the (normalized) positive injection rate (spec layer). -/
structure U4PayRhoControlledByInjectionRateHypothesis
    (P : Payments) (injRate : ℝ → ℝ) : Prop where
  exists_bound :
    ∃ (C : ℝ) (err : ℝ → ℝ),
      0 ≤ C ∧
        (∃ e : ℝ → ℝ,
          (∀ r : ℝ, 0 < r → 0 ≤ e r) ∧
            (∀ ε : ℝ, 0 < ε → ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 → e r ≤ ε) ∧
              ∀ r : ℝ, 0 < r → err r ≤ e r) ∧
          ∀ r : ℝ, 0 < r → P.payRho r ≤ C * injRate (2 * r) + err r

/-- **U-4 band-budget reduction to positive injection (spec layer).**

This mirrors TeX Hypothesis `hyp:U4_band_budget_controlled_by_injection_rate`: it abstracts the single
missing analytic step in the PayRho-control gate, namely controlling the scale-critical “budget term”
coming from the band-payment inequality by the (normalized) positive injection rate plus an `o(1)` error. -/
structure U4BandBudgetControlledByInjectionRateHypothesis
    (bandBudget : ℝ → ℝ) (injRate : ℝ → ℝ) : Prop where
  exists_bound :
    ∃ (C : ℝ) (err : ℝ → ℝ),
      0 ≤ C ∧
        (∃ e : ℝ → ℝ,
          (∀ r : ℝ, 0 < r → 0 ≤ e r) ∧
            (∀ ε : ℝ, 0 < ε → ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 → e r ≤ ε) ∧
              ∀ r : ℝ, 0 < r → err r ≤ e r) ∧
          ∀ r : ℝ, 0 < r → bandBudget r ≤ C * injRate (2 * r) + err r

/-- **Bookkeeping lemma (PayRho):** if `PayRho` is bounded by a scale-critical band budget plus an `O(r)`
term (coming from the known band-payment inequality), and that band budget is controlled by the injection
rate plus `o(1)`, then `PayRho` is controlled by the injection rate plus `o(1)`.

This isolates the PDE content to the two hypotheses; the proof here is pure algebra/ε–δ bookkeeping. -/
theorem u4PayRhoControlledByInjectionRate_of_bandBudget
    (P : Payments) (injRate bandBudget : ℝ → ℝ)
    (hBand :
      ∃ C0 : ℝ,
        0 ≤ C0 ∧
          ∀ r : ℝ, 0 < r → P.payRho r ≤ C0 * bandBudget r + C0 * r)
    (hBud : U4BandBudgetControlledByInjectionRateHypothesis bandBudget injRate) :
    U4PayRhoControlledByInjectionRateHypothesis P injRate := by
  classical
  rcases hBand with ⟨C0, hC00, hBand⟩
  rcases hBud.exists_bound with ⟨C1, err1, hC10, hErr1, hBud⟩
  rcases hErr1 with ⟨e1, he1_nonneg, he1_lim, hErr1_le⟩

  -- package the new error term: `C0 * err1 r + C0 * r`
  let err : ℝ → ℝ := fun r => C0 * err1 r + C0 * r
  have hErr :
      ∃ e : ℝ → ℝ,
        (∀ r : ℝ, 0 < r → 0 ≤ e r) ∧
          (∀ ε : ℝ, 0 < ε → ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 → e r ≤ ε) ∧
            ∀ r : ℝ, 0 < r → err r ≤ e r := by
    refine ⟨fun r => C0 * e1 r + C0 * r, ?_, ?_, ?_⟩
    · intro r hr
      exact
        add_nonneg
          (mul_nonneg hC00 (he1_nonneg r hr))
          (mul_nonneg hC00 (le_of_lt hr))
    · intro ε hε
      by_cases hC0 : C0 = 0
      · subst hC0
        refine ⟨1, by norm_num, ?_⟩
        intro r hr hrr0
        -- `e r = 0`, so it suffices that `0 ≤ ε`
        simpa using (le_of_lt hε)
      · have hC0pos : 0 < C0 := lt_of_le_of_ne hC00 (Ne.symm hC0)
        have hden : 0 < 2 * C0 := by nlinarith
        have hε2 : 0 < ε / (2 * C0) := div_pos hε hden
        rcases he1_lim (ε / (2 * C0)) hε2 with ⟨r1, hr1, hr1_bound⟩
        refine ⟨min r1 (ε / (2 * C0)), lt_min hr1 hε2, ?_⟩
        intro r hr hrr0
        have hr_le_r1 : r ≤ r1 := le_trans hrr0 (min_le_left _ _)
        have hr_le_eps : r ≤ ε / (2 * C0) := le_trans hrr0 (min_le_right _ _)
        have he1 : e1 r ≤ ε / (2 * C0) := hr1_bound r hr hr_le_r1
        have hC0e1 : C0 * e1 r ≤ ε / 2 := by
          have : C0 * e1 r ≤ C0 * (ε / (2 * C0)) :=
            mul_le_mul_of_nonneg_left he1 hC00
          have hC0ne : C0 ≠ 0 := hC0
          have hmul : C0 * (ε / (2 * C0)) = ε / 2 := by
            field_simp [hC0ne]
          exact this.trans (by simpa [hmul])
        have hC0r : C0 * r ≤ ε / 2 := by
          have : C0 * r ≤ C0 * (ε / (2 * C0)) :=
            mul_le_mul_of_nonneg_left hr_le_eps hC00
          have hC0ne : C0 ≠ 0 := hC0
          have hmul : C0 * (ε / (2 * C0)) = ε / 2 := by
            field_simp [hC0ne]
          exact this.trans (by simpa [hmul])
        have : C0 * e1 r + C0 * r ≤ ε / 2 + ε / 2 := add_le_add hC0e1 hC0r
        nlinarith
    · intro r hr
      have h1 : C0 * err1 r ≤ C0 * e1 r :=
        mul_le_mul_of_nonneg_left (hErr1_le r hr) hC00
      have : C0 * err1 r + C0 * r ≤ C0 * e1 r + C0 * r := by
        nlinarith [h1]
      simpa [err] using this

  refine ⟨C0 * C1, err, mul_nonneg hC00 hC10, hErr, ?_⟩
  intro r hr
  have hBud' : bandBudget r ≤ C1 * injRate (2 * r) + err1 r := hBud r hr
  have hPay : P.payRho r ≤ C0 * bandBudget r + C0 * r := hBand r hr
  have hPay' : P.payRho r ≤ C0 * (C1 * injRate (2 * r) + err1 r) + C0 * r := by
    have : C0 * bandBudget r ≤ C0 * (C1 * injRate (2 * r) + err1 r) :=
      mul_le_mul_of_nonneg_left hBud' hC00
    have hAdd :
        C0 * bandBudget r + C0 * r ≤ C0 * (C1 * injRate (2 * r) + err1 r) + C0 * r := by
      nlinarith [this]
    exact le_trans hPay hAdd
  -- rearrange into `C * injRate (2*r) + err r`
  have : P.payRho r ≤ (C0 * C1) * injRate (2 * r) + (C0 * err1 r + C0 * r) := by
    -- expand and collect terms
    nlinarith
  simpa [err] using this

/-- **U-4 injection/payment package (spec layer):** bundle the PDE inputs for the U‑4 upper bound:

1) vanishing of the normalized positive injection rate,
2) `PayXi` is controlled by that injection rate plus an `o(1)` error,
3) `PayRho` is controlled by that injection rate plus an `o(1)` error.

This mirrors the TeX blocker `hyp:U4_injection_payment_package` once `injRate r` is instantiated by the
normalized injection `(1/r^2) ∬ ρ^{3/2} σ_+`. -/
structure U4InjectionPaymentPackageHypothesis (P : Payments) (injRate : ℝ → ℝ) : Prop where
  hInj : U4VanishingInjectionRateHypothesis injRate
  hPayXi : U4PayXiControlledByInjectionRateHypothesis P injRate
  hPayRho : U4PayRhoControlledByInjectionRateHypothesis P injRate

/-- If payments are controlled by the injection rate and the injection rate vanishes,
then the U‑4 payment upper bound holds (pure bookkeeping). -/
theorem u4PaymentUpperBound_of_paymentControl
    (P : Payments) (injRate : ℝ → ℝ)
    (hInj : U4VanishingInjectionRateHypothesis injRate)
    (hCtrl : U4PaymentsControlledByInjectionRateHypothesis P injRate) :
    U4PaymentUpperBoundHypothesis P := by
  classical
  rcases hCtrl.exists_bound with ⟨C, err, hC0, hErr, hBound⟩
  exact
    u4PaymentUpperBound_of_u4InjectionRate
      (P := P) (injRate := injRate) (err := err) hInj hErr ⟨C, hC0, hBound⟩

/-- Single-entry version of `u4PaymentUpperBound_of_paymentControl`. -/
theorem u4PaymentUpperBound_of_u4Package
    (P : Payments) (injRate : ℝ → ℝ) (hPkg : U4InjectionPaymentPackageHypothesis P injRate) :
    U4PaymentUpperBoundHypothesis P :=
by
  classical
  rcases hPkg.hPayXi.exists_bound with ⟨Cx, errx, hCx0, hErrx, hXibound⟩
  rcases hPkg.hPayRho.exists_bound with ⟨Cr, errr, hCr0, hErrr, hRhobound⟩
  -- combine the two error bounds
  rcases hErrx with ⟨eX, heX_nonneg, heX_lim, hErrx_le⟩
  rcases hErrr with ⟨eR, heR_nonneg, heR_lim, hErrr_le⟩
  let err : ℝ → ℝ := fun r => errx r + errr r
  have hErr :
      ∃ e : ℝ → ℝ,
        (∀ r : ℝ, 0 < r → 0 ≤ e r) ∧
          (∀ ε : ℝ, 0 < ε → ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 → e r ≤ ε) ∧
            ∀ r : ℝ, 0 < r → err r ≤ e r := by
    refine ⟨fun r => eX r + eR r, ?_, ?_, ?_⟩
    · intro r hr
      exact add_nonneg (heX_nonneg r hr) (heR_nonneg r hr)
    · intro ε hε
      have hε2 : 0 < ε / 2 := by nlinarith
      rcases heX_lim (ε / 2) hε2 with ⟨rX, hrX, hrX_bound⟩
      rcases heR_lim (ε / 2) hε2 with ⟨rR, hrR, hrR_bound⟩
      refine ⟨min rX rR, lt_min hrX hrR, ?_⟩
      intro r hr hrr0
      have hrX' : r ≤ rX := le_trans hrr0 (min_le_left _ _)
      have hrR' : r ≤ rR := le_trans hrr0 (min_le_right _ _)
      have hX : eX r ≤ ε / 2 := hrX_bound r hr hrX'
      have hR : eR r ≤ ε / 2 := hrR_bound r hr hrR'
      have : eX r + eR r ≤ ε / 2 + ε / 2 := add_le_add hX hR
      nlinarith
    · intro r hr
      have hx : errx r ≤ eX r := hErrx_le r hr
      have hr' : errr r ≤ eR r := hErrr_le r hr
      exact add_le_add hx hr'
  have hBound :
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ r : ℝ, 0 < r → P.payXi r + P.payRho r ≤ C * injRate (2 * r) + err r := by
    refine ⟨Cx + Cr, add_nonneg hCx0 hCr0, ?_⟩
    intro r hr
    have hXi : P.payXi r ≤ Cx * injRate (2 * r) + errx r := hXibound r hr
    have hRho : P.payRho r ≤ Cr * injRate (2 * r) + errr r := hRhobound r hr
    have : P.payXi r + P.payRho r ≤ (Cx * injRate (2 * r) + errx r) + (Cr * injRate (2 * r) + errr r) :=
      add_le_add hXi hRho
    -- rearrange
    have :
        P.payXi r + P.payRho r ≤ (Cx + Cr) * injRate (2 * r) + (errx r + errr r) := by
      -- `ring` works but keep it lightweight
      nlinarith
    simpa [err] using this
  -- reduce to the already-proved bookkeeping lemma
  let inj2 : ℝ → ℝ := fun r => injRate (2 * r)
  have hInj2 : U4VanishingInjectionRateHypothesis inj2 := by
    -- `injRate` vanishes ⇒ `injRate ∘ (2*)` vanishes (pure ε–δ bookkeeping)
    simpa [inj2, U4VanishingInjectionRateHypothesis] using
      (c2VanishingInjection_comp_two (injPos := injRate) (h := hPkg.hInj))
  have hBound2 :
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ r : ℝ, 0 < r → P.payXi r + P.payRho r ≤ C * inj2 r + err r := by
    rcases hBound with ⟨C, hC0, hB⟩
    refine ⟨C, hC0, ?_⟩
    intro r hr
    simpa [inj2] using hB r hr
  exact u4PaymentUpperBound_of_u4InjectionRate (P := P) (injRate := inj2) (err := err) hInj2 hErr hBound2

/-- **Route (B-ξ)** interface: “persistent perpendicular tail forcing” implies a twist-or-band payment.

`ForcingEvent ε r` is an abstract predicate encoding:
- top-band persistence on a positive-measure time set, and
- a lower bound `|(I-ξ⊗ξ) S_tail ξ| ≥ c_* ε` on a spatial core.

The conclusion is a scale-consistent lower bound on the *normalized* payments at scale `r`. -/
structure ForcingToTwistOrBandPaymentHypothesis
    (ForcingEvent : ℝ → ℝ → Prop) (P : Payments) : Prop where
  exists_c :
    ∃ c : ℝ,
      0 < c ∧
        ∀ (ε r : ℝ), 0 < ε → 0 < r →
          ForcingEvent ε r →
            c * (ε ^ 2) ≤ P.payXi r + P.payRho r

/-- “Rigid-rotation absorption” guard: if the forcing persists but the payments are small,
then the cylinder lies in a separate explicit structural class (to be ruled out elsewhere).

`AbsorptionClass ε r` should encode the “ODE + affine tail” regime from the TeX
lemma `lem:rigid_rotation_absorption_implies_structure`. -/
structure NoRigidRotationAbsorptionHypothesis
    (ForcingEvent AbsorptionClass : ℝ → ℝ → Prop) (P : Payments) : Prop where
  exists_c :
    ∃ c : ℝ,
      0 < c ∧
        ∀ (ε r : ℝ), 0 < ε → 0 < r →
          ForcingEvent ε r →
            (c * (ε ^ 2) ≤ P.payXi r + P.payRho r) ∨ AbsorptionClass ε r

/-- Optional interface: persistent negative injection on the top band forces band diffusion payment.

`NegativeSigmaEvent ε r` abstracts the event “σ ≤ -c_* ε on the top band for a time-thick subset”. -/
structure NegativeSigmaForcesBandPaymentHypothesis
    (NegativeSigmaEvent : ℝ → ℝ → Prop) (P : Payments) : Prop where
  exists_c :
    ∃ c : ℝ,
      0 < c ∧
        ∀ (ε r : ℝ), 0 < ε → 0 < r →
          NegativeSigmaEvent ε r →
            c * (ε ^ 2) ≤ P.payRho r

/-- **No persistent null alignment (spec layer):** a “large tail strain” event forces a nontrivial interaction with the
vorticity direction (i.e. avoids the null-eigenvector cone everywhere on a time-thick top band set).

At the spec layer this is an abstract implication between two events. -/
structure NoPersistentNullAlignmentHypothesis
    (TailLargeEvent HitEvent : ℝ → ℝ → Prop) : Prop where
  exists_c :
    ∃ c : ℝ,
      0 < c ∧
        ∀ (ε r : ℝ), 0 < ε → 0 < r →
          TailLargeEvent ε r →
            HitEvent ε r

/-- **S3-P bookkeeping (spec layer):** export persistence splits into one of the three “cost channels”.

This is intentionally abstract: it packages the output of the selection/drift-control machinery together with
the algebraic split (`σ` vs perpendicular forcing) into a single logical splitter. -/
structure ExportSplitHypothesis
    (ExportEvent ForcingEvent NegativeSigmaEvent ConcavityEvent : ℝ → ℝ → Prop) : Prop where
  split :
    ∀ (ε r : ℝ),
      0 < ε →
        0 < r →
          ExportEvent ε r →
            ForcingEvent ε r ∨ NegativeSigmaEvent ε r ∨ ConcavityEvent ε r

/-- **Export ⇒ payment/absorption/concavity** (spec layer).

This mirrors TeX Lemma `lem:export_forces_payment_on_cylinder`, but keeps the PDE objects abstract.
The only nontrivial content should sit inside:
- `ExportSplitHypothesis` (selection + bridge into one of the three channels),
- `NoRigidRotationAbsorptionHypothesis` (forcing ⇒ payment ∨ absorption),
- `NegativeSigmaForcesBandPaymentHypothesis` (negative injection ⇒ band payment). -/
structure ExportForcesPaymentHypothesis
    (ExportEvent AbsorptionClass ConcavityEvent : ℝ → ℝ → Prop) (P : Payments) : Prop where
  exists_c :
    ∃ c : ℝ,
      0 < c ∧
        ∀ (ε r : ℝ), 0 < ε → 0 < r →
          ExportEvent ε r →
            (c * (ε ^ 2) ≤ P.payXi r + P.payRho r) ∨ AbsorptionClass ε r ∨ ConcavityEvent ε r

namespace ExportForcesPaymentHypothesis

/-- Build the export→payment bookkeeping lemma from the three abstract implication interfaces. -/
theorem of_split
    {ExportEvent ForcingEvent NegativeSigmaEvent ConcavityEvent AbsorptionClass : ℝ → ℝ → Prop}
    (P : Payments)
    (hSplit : ExportSplitHypothesis ExportEvent ForcingEvent NegativeSigmaEvent ConcavityEvent)
    (hForcing : NoRigidRotationAbsorptionHypothesis ForcingEvent AbsorptionClass P)
    (hNeg : NegativeSigmaForcesBandPaymentHypothesis NegativeSigmaEvent P) :
    ExportForcesPaymentHypothesis ExportEvent AbsorptionClass ConcavityEvent P := by
  classical
  rcases hForcing.exists_c with ⟨cF, hcF_pos, hcF⟩
  rcases hNeg.exists_c with ⟨cN, hcN_pos, hcN⟩
  refine ⟨min cF cN, lt_min hcF_pos hcN_pos, ?_⟩
  intro ε r hε hr hExport
  have hcases := hSplit.split ε r hε hr hExport
  rcases hcases with hF | hrest
  · -- forcing channel
    have hF' := hcF ε r hε hr hF
    rcases hF' with hPay | hAbs
    · left
      have hmin : min cF cN ≤ cF := min_le_left _ _
      exact (mul_le_mul_of_nonneg_right hmin (sq_nonneg ε)).trans hPay
    · right
      exact Or.inl hAbs
  · rcases hrest with hNegEvent | hConc
    · -- negative-sigma channel gives band payment, hence total payment
      have hRho : cN * (ε ^ 2) ≤ P.payRho r := hcN ε r hε hr hNegEvent
      left
      have hmin : min cF cN ≤ cN := min_le_right _ _
      have : min cF cN * (ε ^ 2) ≤ cN * (ε ^ 2) :=
        mul_le_mul_of_nonneg_right hmin (sq_nonneg ε)
      have hRho' : P.payRho r ≤ P.payXi r + P.payRho r :=
        le_add_of_nonneg_left (P.payXi_nonneg r)
      exact this.trans (hRho.trans hRho')
    · right
      exact Or.inr hConc

end ExportForcesPaymentHypothesis

/-- **K-ODE interface (step 1):** absorption-class ⇒ quantitative affine ansatz on a smaller cylinder.

At the spec layer, both “absorption class” and “affine ansatz class” are abstract predicates on `(ε,r)`. -/
structure AbsorptionImpliesAffineAnsatzHypothesis
    (AbsorptionClass AffineAnsatzClass : ℝ → ℝ → Prop) : Prop where
  implies :
    ∀ (ε r : ℝ), 0 < ε → 0 < r →
      AbsorptionClass ε r → AffineAnsatzClass ε r

/-- **K-ODE interface (step 2):** the affine-ansatz class is impossible for running-max ancient elements
below some scale (the ODE contradiction endpoint).

This is the abstraction of TeX Lemma `lem:affine_mode_ode_contradiction`. -/
structure AffineAnsatzImpossibleHypothesis (AffineAnsatzClass : ℝ → ℝ → Prop) : Prop where
  impossible :
    ∀ (ε0 : ℝ),
      0 < ε0 →
        ∃ r0 : ℝ,
          0 < r0 ∧
            ∀ r : ℝ, 0 < r → r ≤ r0 → AffineAnsatzClass ε0 r → False

/-- **K-ODE input:** time-variation control for an abstract “tail strain at the origin” signal `S(t)`.

This mirrors TeX Hypothesis `hyp:tail_strain_time_variation`.
We keep it fully abstract (it will later be instantiated by `t ↦ S_tail^{(k)}(0,t)` once those objects exist in Lean). -/
structure TailStrainTimeVariationHypothesis (α : Type) [NormedAddCommGroup α] (S : ℝ → α) : Prop where
  exists_modulus :
    ∃ ω : ℝ → ℝ,
      (∀ r : ℝ, 0 < r → 0 ≤ ω r) ∧
        (∀ ε : ℝ, 0 < ε → ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 → ω r ≤ ε) ∧
          ∀ r : ℝ, 0 < r →
            ∀ t s : ℝ,
              t ∈ Set.Icc (-(r ^ 2)) 0 →
                s ∈ Set.Icc (-(r ^ 2)) 0 →
                  ‖S t - S s‖ ≤ ω r

/-- Alias matching TeX Hypothesis `hyp:tail_vorticity_L2_time_modulus`.

At the spec layer we keep the ambient normed space abstract; in the intended instantiation,
`β` is an `L^2`-type tail space and `Ω` is the truncated tail vorticity. -/
abbrev TailVorticityL2TimeModulusHypothesis
    (β : Type) [NormedAddCommGroup β] (Ω : ℝ → β) : Prop :=
  TailStrainTimeVariationHypothesis β Ω

/-- **Bridge helper:** if `Ω` has a short-window time-modulus and `S` is Lipschitz in `Ω`,
then `S` inherits a short-window time-modulus.

This mirrors the TeX bridge `hyp:tail_vorticity_L2_time_modulus ⇒ hyp:tail_strain_time_variation`
once the explicit Biot–Savart pairing is packaged as a Lipschitz map on the chosen normed space. -/
theorem tailStrainTimeVariation_of_lipschitz
    {α β : Type} [NormedAddCommGroup α] [NormedAddCommGroup β]
    {Ω : ℝ → β} {S : ℝ → α}
    (hΩ : TailStrainTimeVariationHypothesis β Ω)
    (hLip : ∃ C : ℝ, 0 ≤ C ∧ ∀ t s : ℝ, ‖S t - S s‖ ≤ C * ‖Ω t - Ω s‖) :
    TailStrainTimeVariationHypothesis α S := by
  classical
  rcases hΩ.exists_modulus with ⟨μ, hμ_nonneg, hμ_lim, hμ⟩
  rcases hLip with ⟨C, hC0, hLip⟩
  refine ⟨fun r => C * μ r, ?_, ?_, ?_⟩
  · intro r hr
    exact mul_nonneg hC0 (hμ_nonneg r hr)
  · intro ε hε
    by_cases hCpos : 0 < C
    · have hε' : 0 < ε / C := by exact div_pos hε hCpos
      rcases hμ_lim (ε / C) hε' with ⟨r0, hr0, hr0μ⟩
      refine ⟨r0, hr0, ?_⟩
      intro r hr hrr0
      have : μ r ≤ ε / C := hr0μ r hr hrr0
      -- multiply by C (positive) to get the desired bound
      have : C * μ r ≤ C * (ε / C) := mul_le_mul_of_nonneg_left this (le_of_lt hCpos)
      simpa [mul_assoc, mul_div_cancel₀, ne_of_gt hCpos] using this
    · -- If `C ≤ 0`, then `C * μ r ≤ 0 ≤ ε` for all small windows.
      have hCnonpos : C ≤ 0 := le_of_not_gt hCpos
      refine ⟨1, by norm_num, ?_⟩
      intro r hr _
      have : C * μ r ≤ 0 := by exact mul_nonpos_of_nonpos_of_nonneg hCnonpos (hμ_nonneg r hr)
      exact this.trans (le_of_lt hε)
  · intro r hr t s ht hs
    have h1 : ‖S t - S s‖ ≤ C * ‖Ω t - Ω s‖ := hLip t s
    have h2 : ‖Ω t - Ω s‖ ≤ μ r := hμ r hr t s ht hs
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0)

/-- **Absorption elimination (U-4):** the abstract absorption class cannot occur below some scale.

This mirrors TeX Hypothesis `hyp:absorption_class_impossible`. -/
structure AbsorptionClassImpossibleHypothesis (AbsorptionClass : ℝ → ℝ → Prop) : Prop where
  impossible :
    ∀ (η ε0 : ℝ),
      0 < η →
        0 < ε0 →
          ∃ r0 : ℝ,
            0 < r0 ∧
              ∀ r : ℝ, 0 < r → r ≤ r0 → AbsorptionClass ε0 r → False

/-- **Concavity/peak channel elimination (spec layer):** the concavity event cannot occur below some scale.

This is the abstract way to “kill (P3)” if it is not already absorbed into `payXi`/`payRho`. -/
structure ConcavityImpossibleHypothesis (ConcavityEvent : ℝ → ℝ → Prop) : Prop where
  impossible :
    ∀ (ε0 : ℝ),
      0 < ε0 →
        ∃ r0 : ℝ,
          0 < r0 ∧
            ∀ r : ℝ, 0 < r → r ≤ r0 → ConcavityEvent ε0 r → False

/-- **U-4 one-cylinder contradiction (spec layer):** export persistence at a fixed level is impossible below some scale.

This mirrors TeX Lemma `lem:U4_contradiction_from_export`, but keeps the PDE objects abstract. -/
structure U4NoExportHypothesis (ExportEvent : ℝ → ℝ → Prop) : Prop where
  impossible :
    ∀ (ε0 : ℝ),
      0 < ε0 →
        ∃ r0 : ℝ,
          0 < r0 ∧
            ∀ r : ℝ, 0 < r → r ≤ r0 → ExportEvent ε0 r → False

namespace U4NoExportHypothesis

/-- Build the U-4 contradiction from:
- an export→(payment ∨ absorption ∨ concavity) lower bound,
- an upper bound on payments as `r → 0`,
- impossibility of absorption below some scale,
- impossibility of the concavity channel below some scale.

All constants/moduli remain abstract; this lemma is pure bookkeeping. -/
theorem of_u4
    {ExportEvent AbsorptionClass ConcavityEvent : ℝ → ℝ → Prop}
    (P : Payments)
    (η : ℝ) (hη : 0 < η)
    (hExport : ExportForcesPaymentHypothesis ExportEvent AbsorptionClass ConcavityEvent P)
    (hUpper : U4PaymentUpperBoundHypothesis P)
    (hAbs : AbsorptionClassImpossibleHypothesis AbsorptionClass)
    (hConc : ConcavityImpossibleHypothesis ConcavityEvent) :
    U4NoExportHypothesis ExportEvent := by
  classical
  rcases hExport.exists_c with ⟨c, hc_pos, hc⟩
  rcases hUpper.exists_beta with ⟨β, hβ_nonneg, hβ_lim, hβ⟩
  refine ⟨?_⟩
  intro ε0 hε0
  -- pick a scale where the payment upper bound beats `c * ε0^2`
  have hpos : 0 < c * (ε0 ^ 2) := mul_pos hc_pos (sq_pos_of_pos hε0)
  rcases hβ_lim (c * (ε0 ^ 2) / 2) (by nlinarith) with ⟨rβ, hrβ_pos, hrβ⟩
  -- pick scales killing absorption + concavity at level ε0
  rcases hAbs.impossible η ε0 hη hε0 with ⟨rAbs, hrAbs_pos, hrAbs⟩
  rcases hConc.impossible ε0 hε0 with ⟨rConc, hrConc_pos, hrConc⟩
  refine ⟨min rβ (min rAbs rConc), ?_, ?_⟩
  · exact lt_min hrβ_pos (lt_min hrAbs_pos hrConc_pos)
  · intro r hr hrr0 hEv
    have hrβ' : r ≤ rβ := le_trans hrr0 (min_le_left _ _)
    have hrAbs' : r ≤ rAbs := le_trans (le_trans hrr0 (min_le_right _ _)) (min_le_left _ _)
    have hrConc' : r ≤ rConc := le_trans (le_trans hrr0 (min_le_right _ _)) (min_le_right _ _)
    have hcases := hc ε0 r hε0 hr hEv
    rcases hcases with hPay | hrest
    · -- contradict payment lower bound with the U4 upper bound
      have hUp : P.payXi r + P.payRho r ≤ β r := hβ r hr
      have hβsmall : β r ≤ c * (ε0 ^ 2) / 2 := hrβ r hr hrβ'
      have : c * (ε0 ^ 2) ≤ β r := le_trans hPay hUp
      -- but `β r < c*ε0^2` by `hβsmall`
      have : c * (ε0 ^ 2) ≤ c * (ε0 ^ 2) / 2 := this.trans hβsmall
      nlinarith
    · rcases hrest with hAbsEv | hConcEv
      · exact hrAbs r hr hrAbs' hAbsEv
      · exact hrConc r hr hrConc' hConcEv

end U4NoExportHypothesis

/-- **Bridge (profile → cylinder):** if tail-flux does not vanish, then “export persists” occurs at arbitrarily small scales.

This isolates the PDE/compactness work needed to connect the time-slice profile statement
`¬ TailFluxVanish P.A P.A'` to the U‑4 cylinder predicates. -/
structure TailFluxNonVanishImpliesExportAtSmallScales
    (P : RM2URadialProfile) (ExportEvent : ℝ → ℝ → Prop) : Prop where
  to_export :
    (¬ TailFluxVanish P.A P.A') →
      ∃ ε0 : ℝ, 0 < ε0 ∧
        ∀ r0 : ℝ, 0 < r0 → ∃ r : ℝ, 0 < r ∧ r ≤ r0 ∧ ExportEvent ε0 r

/-- Package the U‑4 contradiction into the time-slice Bet2 interface once the profile→cylinder bridge is supplied. -/
theorem bet2SelfFalsification_of_u4
    (P : RM2URadialProfile) {ExportEvent : ℝ → ℝ → Prop}
    (hBridge : TailFluxNonVanishImpliesExportAtSmallScales P ExportEvent)
    (hNoExport : U4NoExportHypothesis ExportEvent) :
    Bet2SelfFalsificationHypothesis P := by
  classical
  refine ⟨?_⟩
  intro hnot
  rcases hBridge.to_export hnot with ⟨ε0, hε0, hsmall⟩
  rcases hNoExport.impossible ε0 hε0 with ⟨r0, hr0, hno⟩
  rcases hsmall r0 hr0 with ⟨r, hr, hrr0, hEv⟩
  exact hno r hr hrr0 hEv

/-- **E-gate interface (one way to eliminate absorption):** a quasi-2D smallness condition forces triviality.

At the spec layer this is an abstract predicate `Quasi2DEvent` (encoding a scale-invariant smallness statement on a cylinder)
and a conclusion `TrivialEvent` (encoding the contradiction / triviality outcome). -/
structure Quasi2DEliminationHypothesis (Quasi2DEvent TrivialEvent : Prop) : Prop where
  elim : Quasi2DEvent → TrivialEvent

/-- **Backward uniqueness import (Lei–Yang–Yuan 2024, IMRN):**
within the bounded mild + bounded-vorticity class, the solution is uniquely determined by its final data.

At the spec layer we keep the “solution objects” abstract as a type `Sol` and encode only the logical shape. -/
structure BackwardUniquenessNSHypothesis
    (Sol : Type) (IsBoundedMild HasBoundedVorticity : Sol → Prop)
    (AgreeAtTime CoincideUpTo : Sol → Sol → ℝ → Prop) : Prop where
  backward_unique :
    ∀ (u₁ u₂ : Sol) (T : ℝ),
      IsBoundedMild u₁ →
        HasBoundedVorticity u₁ →
          IsBoundedMild u₂ →
            HasBoundedVorticity u₂ →
              AgreeAtTime u₁ u₂ T →
                CoincideUpTo u₁ u₂ T

/-- **E-gate bridge (LYY style):** a quasi-2D event produces a comparison mild solution in an eliminable subclass,
with the same final data at time `T`. This is designed to be paired with `BackwardUniquenessNSHypothesis`. -/
structure Quasi2DToComparisonSolutionHypothesis
    (Sol : Type)
    (IsBoundedMild HasBoundedVorticity : Sol → Prop)
    (Quasi2DEvent : Sol → Prop) (EliminableSubclass : Sol → Prop)
    (AgreeAtTime : Sol → Sol → ℝ → Prop) : Prop where
  exists_comparison :
    ∀ (u : Sol) (T : ℝ),
      IsBoundedMild u →
        HasBoundedVorticity u →
          Quasi2DEvent u →
            ∃ u₂ : Sol,
              IsBoundedMild u₂ ∧
                HasBoundedVorticity u₂ ∧
                  EliminableSubclass u₂ ∧
                    AgreeAtTime u₂ u T

/-- **E-gate bridge (pure symmetry propagation):** from a quasi-2D event we can extract a *nontrivial symmetry*
of the final data, so the symmetry-pushforward solution agrees at time `T`.

This is the “free comparison solution” route: if `Act g u` is always a solution whenever `u` is, then no existence theory is needed. -/
structure Quasi2DToExactSymmetryHypothesis
    (Sol Sym : Type)
    (IsBoundedMild HasBoundedVorticity : Sol → Prop)
    (Act : Sym → Sol → Sol) (Nontrivial : Sym → Prop)
    (Quasi2DEvent : Sol → Prop) (AgreeAtTime : Sol → Sol → ℝ → Prop) : Prop where
  exists_symm :
    ∀ (u : Sol) (T : ℝ),
      IsBoundedMild u →
        HasBoundedVorticity u →
          Quasi2DEvent u →
            ∃ g : Sym, Nontrivial g ∧ AgreeAtTime (Act g u) u T

/-- **E-gate elimination of the symmetry class:** any nontrivial symmetry-invariant candidate is impossible. -/
structure SymmetryClassImpossibleHypothesis
    (Sol Sym : Type) (Act : Sym → Sol → Sol) (Nontrivial : Sym → Prop)
    (CoincideUpTo : Sol → Sol → ℝ → Prop) (TrivialEvent : Prop) : Prop where
  elim :
    ∀ (u : Sol) (T : ℝ),
      (∃ g : Sym, Nontrivial g ∧ CoincideUpTo (Act g u) u T) →
        TrivialEvent

end Bet2U4

theorem nonParasitism_of_bet2 (P : RM2URadialProfile) (h : Bet2SelfFalsificationHypothesis P) :
    NonParasitismHypothesis P := by
  classical
  refine ⟨?_⟩
  by_contra hnot
  exact (h.selfFalsify hnot)

/-- **Bet 3 (inheritance route)**: directly assume the coercive \(L^2\) bound for the profile.
This closes RM2, but does not (by itself) explain *why* the tail flux vanishes. -/
structure Bet3CoerciveL2Hypothesis (P : RM2URadialProfile) : Prop where
  coercive : CoerciveL2Bound P

theorem rm2Closed_of_bet3 (P : RM2URadialProfile) (h : Bet3CoerciveL2Hypothesis P) :
    RM2Closed P.A :=
  RM2U.rm2Closed_of_coerciveL2Bound (P := P) h.coercive

/-!
## End-to-end closure wrappers (so bets plug into RM2)

These are purely compositional: they do not add any new mathematics, they just make it explicit
how each bet closes the simplified `RM2Closed` target once the missing “tailFlux → coercive” step
is supplied (as an interface in `RM2U.EnergyIdentity`).
-/

theorem rm2Closed_of_nonParasitism
    (P : RM2URadialProfile)
    (hNP : NonParasitismHypothesis P)
    (hTC : TailFluxVanishImpliesCoerciveHypothesis P) :
    RM2Closed P.A :=
  RM2U.rm2Closed_of_coerciveL2Bound (P := P)
    (RM2U.coerciveL2Bound_of_tailFluxVanish (P := P) hTC hNP.tailFluxVanish)

theorem rm2Closed_of_bet1
    (P : RM2URadialProfile)
    (h1 : Bet1BoundaryIntegrableHypothesis P)
    (hTC : TailFluxVanishImpliesCoerciveHypothesis P) :
    RM2Closed P.A :=
  rm2Closed_of_nonParasitism (P := P) (nonParasitism_of_bet1 (P := P) h1) hTC

theorem rm2Closed_of_bet2
    (P : RM2URadialProfile)
    (h2 : Bet2SelfFalsificationHypothesis P)
    (hTC : TailFluxVanishImpliesCoerciveHypothesis P) :
    RM2Closed P.A :=
  rm2Closed_of_nonParasitism (P := P) (nonParasitism_of_bet2 (P := P) h2) hTC

/-!
## Planned endgame theorem (currently a placeholder target)

Ultimately we want to connect this to the *running-max ancient element* extracted in
`navier-dec-12-rewrite.tex`:

`runningMaxAncientElement → NonParasitismHypothesis (the associated RM2U profile)`.

We do **not** state it yet, because the repository does not currently contain a Lean definition
of the running-max ancient element in velocity/vorticity variables.
-/

end RM2U
end NavierStokes
end IndisputableMonolith
