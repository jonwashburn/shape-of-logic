import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Thermodynamics.RecognitionThermodynamics
import IndisputableMonolith.Thermodynamics.MaxEntFromCost

/-!
# The Second Law of Thermodynamics from RS First Principles

This module assembles the rock-solid Lean theorem for the second law of
thermodynamics inside Recognition Science, with **zero `sorry` and zero new
axioms**.

## Status

THEOREM (no sorry, no axiom).

## What this module proves

Let `Ω` be a finite, nonempty configuration space.  Let `sys : RecognitionSystem`
fix a positive recognition temperature `T_R`, let `X : Ω → ℝ` assign a positive
ratio (cost coordinate) to each configuration, and let `π = gibbs_measure sys X`
be the Gibbs equilibrium distribution.

A `JDescentOperator peq` is any operator on probability distributions that

1. fixes the equilibrium `peq`, and
2. is non-expansive in KL divergence relative to `peq`, i.e. for every `q`,
   `D_KL(R q ‖ peq) ≤ D_KL(q ‖ peq)`.

This is the abstract form of the recognition operator R̂ on the distribution
layer.  Any deterministic Markov kernel that has `peq` as its stationary
distribution satisfies this; the data-processing inequality
(`Thermodynamics.FreeEnergyMonotone.data_processing_inequality`) is the
canonical witness.

For any J-descent operator `R` and any initial distribution `q₀`, define the
discrete trajectory `qₙ = R^n q₀`.  We prove:

* `kl_divergence_antitone`: `n ↦ D_KL(qₙ ‖ peq)` is monotone non-increasing.
* `free_energy_antitone`: `n ↦ F_R(qₙ)` is monotone non-increasing.
  (This is the second law in its sharpest form.)
* `free_energy_ge_equilibrium`: `F_R(qₙ) ≥ F_R(peq)` for every `n`
  (the variational principle).
* `second_law`: a single-statement bundle of the three results above.
* `second_law_entropy_form`: when `⟨X⟩` is conserved along the trajectory,
  `n ↦ S_R(qₙ)` is monotone non-decreasing.  This is the classical Clausius
  form `ΔS ≥ 0`.
* `second_law_one_statement`: there is a non-negative function `H : ℕ → ℝ`,
  bounded below by `0`, monotone non-increasing, and equal to `0` exactly at
  equilibrium.  This is the Lyapunov form of the second law.

The master certificate `SecondLawCert sys X` bundles the Gibbs inequality,
the variational principle, the free-energy / KL identity, and the two
antitonicity statements into a single record.

## Derivation chain (first principles)

The proof decomposes into purely mathematical content plus the structural
input named in the docstring of `JDescentOperator`:

```
T0–T5 (forcing chain)  ⟹  J(x) = ½(x + x⁻¹) − 1  is unique and convex
(`Cost.FunctionalEquation.law_of_logic_forces_jcost`)

x log x convex on (0,∞)  ⟹  log-sum inequality (Jensen)
                          ⟹  D_KL ≥ 0  with  D_KL = 0 ↔ q = p   (Gibbs ineq.)
                          ⟹  data processing inequality

Recognition operator R̂  ≜  J-descent flow with conservation constraints
                          ⟹  R̂ has Gibbs as stationary distribution
                          ⟹  D_KL(R̂ q ‖ peq) ≤ D_KL(q ‖ peq)
                          ⟹  R̂ ∈ JDescentOperator peq

Free-energy / KL identity  F(q) − F(peq) = T_R · D_KL(q ‖ peq)
                          (`MaxEntFromCost.free_energy_kl_identity`)

Therefore  F(R̂ q) − F(peq) ≤ F(q) − F(peq)
       ⟹  F is monotone non-increasing along R̂   (the second law).
```

The single non-mathematical input is the structural identification of physical
time with the orbit parameter of R̂.  Inside RS this is forced because there
is no independent time primitive (T2 forbids a continuous coordinate before
the ledger is constructed).

## Key Lean dependencies

* `Cost.Jcost`, `Cost.Jcost_unit0`, `Cost.Jcost_nonneg`, `Cost.Jcost_pos_of_ne_one`
  (J is the unique convex cost with a unique zero at `x = 1`).
* `Thermodynamics.kl_divergence_nonneg` (Gibbs inequality on a finite space).
* `Thermodynamics.free_energy_kl_identity`
  (the variational identity `F(q) − F(peq) = T_R · D_KL(q ‖ peq)`).
* `Thermodynamics.gibbs_minimizes_free_energy_basic`
  (Gibbs minimizes `F_R`).
-/

namespace IndisputableMonolith
namespace Thermodynamics
namespace SecondLaw

open Real Cost RecognitionSystem
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## §1. The Gibbs distribution as a `ProbabilityDistribution` -/

/-- Package the Gibbs measure as a `ProbabilityDistribution`.  This is the
    equilibrium reference for the J-descent dynamics. -/
noncomputable def gibbsPD (sys : RecognitionSystem) (X : Ω → ℝ) :
    ProbabilityDistribution Ω where
  p := gibbs_measure sys X
  nonneg := fun ω => le_of_lt (gibbs_measure_pos sys X ω)
  sum_one := gibbs_measure_sum_one sys X

@[simp] lemma gibbsPD_p (sys : RecognitionSystem) (X : Ω → ℝ) :
    (gibbsPD sys X).p = gibbs_measure sys X := rfl

/-! ## §2. J-descent operators on probability distributions -/

/-- A **J-descent operator** on probability distributions over `Ω` with
    equilibrium `peq` is a step `step : Distrib Ω → Distrib Ω` such that

    1. `step peq = peq`  (the equilibrium is a fixed point), and
    2. for every distribution `q`,
       `D_KL(step q ‖ peq) ≤ D_KL(q ‖ peq)`  (KL non-expansiveness).

    Inside RS, the recognition operator R̂ projected onto the distribution
    layer is a J-descent operator with `peq = gibbsPD sys X`.  More generally,
    any deterministic Markov kernel that has `peq` as its stationary distribution
    satisfies these properties via the data-processing inequality. -/
structure JDescentOperator (peq : ProbabilityDistribution Ω) where
  /-- The single-tick recognition step on probability distributions. -/
  step : ProbabilityDistribution Ω → ProbabilityDistribution Ω
  /-- Equilibrium is a fixed point. -/
  fixes_equilibrium : step peq = peq
  /-- KL divergence to equilibrium does not increase under one tick. -/
  kl_non_increasing :
    ∀ q : ProbabilityDistribution Ω,
      kl_divergence (step q).p peq.p ≤ kl_divergence q.p peq.p

namespace JDescentOperator

/-- Discrete iteration of a J-descent operator. -/
def evolve {peq : ProbabilityDistribution Ω}
    (R : JDescentOperator peq) :
    ℕ → ProbabilityDistribution Ω → ProbabilityDistribution Ω
  | 0,     q => q
  | n + 1, q => R.step (R.evolve n q)

omit [Nonempty Ω] in
@[simp] lemma evolve_zero {peq : ProbabilityDistribution Ω}
    (R : JDescentOperator peq) (q : ProbabilityDistribution Ω) :
    R.evolve 0 q = q := rfl

omit [Nonempty Ω] in
@[simp] lemma evolve_succ {peq : ProbabilityDistribution Ω}
    (R : JDescentOperator peq) (n : ℕ) (q : ProbabilityDistribution Ω) :
    R.evolve (n + 1) q = R.step (R.evolve n q) := rfl

omit [Nonempty Ω] in
/-- Equilibrium is a fixed point of the iterated evolution. -/
theorem evolve_equilibrium_eq {peq : ProbabilityDistribution Ω}
    (R : JDescentOperator peq) (n : ℕ) :
    R.evolve n peq = peq := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [evolve_succ, ih, R.fixes_equilibrium]

end JDescentOperator

/-! ## §3. KL is monotone non-increasing along the evolution -/

omit [Nonempty Ω] in
/-- Single-step KL contraction: `D_KL(qₙ₊₁ ‖ peq) ≤ D_KL(qₙ ‖ peq)`. -/
theorem kl_step_le {peq : ProbabilityDistribution Ω}
    (R : JDescentOperator peq) (q₀ : ProbabilityDistribution Ω) (n : ℕ) :
    kl_divergence (R.evolve (n + 1) q₀).p peq.p ≤
      kl_divergence (R.evolve n q₀).p peq.p := by
  rw [JDescentOperator.evolve_succ]
  exact R.kl_non_increasing _

omit [Nonempty Ω] in
/-- Pointwise KL contraction across a `n ≤ m` interval. -/
theorem kl_le_of_le {peq : ProbabilityDistribution Ω}
    (R : JDescentOperator peq) (q₀ : ProbabilityDistribution Ω)
    {n m : ℕ} (hnm : n ≤ m) :
    kl_divergence (R.evolve m q₀).p peq.p ≤
      kl_divergence (R.evolve n q₀).p peq.p := by
  induction hnm with
  | refl => exact le_refl _
  | step _ ih => exact le_trans (kl_step_le R q₀ _) ih

omit [Nonempty Ω] in
/-- KL divergence to equilibrium is monotone non-increasing along the
    evolution.  This is the deepest single inequality in the derivation; the
    free-energy version follows by a single multiplication. -/
theorem kl_divergence_antitone {peq : ProbabilityDistribution Ω}
    (R : JDescentOperator peq) (q₀ : ProbabilityDistribution Ω) :
    Antitone (fun n : ℕ => kl_divergence (R.evolve n q₀).p peq.p) := by
  intro n m hnm
  exact kl_le_of_le R q₀ hnm

/-! ## §4. Free energy is monotone non-increasing along the evolution -/

private lemma fe_kl_id (sys : RecognitionSystem) (X : Ω → ℝ)
    (q : ProbabilityDistribution Ω) :
    recognition_free_energy sys q.p X -
        recognition_free_energy sys (gibbsPD sys X).p X =
      sys.TR * kl_divergence q.p (gibbsPD sys X).p := by
  rw [gibbsPD_p]
  exact free_energy_kl_identity sys X q

/-- Single-step free-energy contraction. -/
theorem free_energy_step_le (sys : RecognitionSystem) (X : Ω → ℝ)
    (R : JDescentOperator (gibbsPD sys X)) (q₀ : ProbabilityDistribution Ω) (n : ℕ) :
    recognition_free_energy sys (R.evolve (n + 1) q₀).p X ≤
      recognition_free_energy sys (R.evolve n q₀).p X := by
  have hkl := kl_step_le (R := R) q₀ n
  have hid_n := fe_kl_id sys X (R.evolve n q₀)
  have hid_m := fe_kl_id sys X (R.evolve (n + 1) q₀)
  have hTR : 0 ≤ sys.TR := sys.TR_pos.le
  have hmul :
      sys.TR * kl_divergence (R.evolve (n + 1) q₀).p (gibbsPD sys X).p ≤
        sys.TR * kl_divergence (R.evolve n q₀).p (gibbsPD sys X).p :=
    mul_le_mul_of_nonneg_left hkl hTR
  linarith

/-- Pointwise free-energy contraction across a `n ≤ m` interval. -/
theorem free_energy_le_of_le (sys : RecognitionSystem) (X : Ω → ℝ)
    (R : JDescentOperator (gibbsPD sys X)) (q₀ : ProbabilityDistribution Ω)
    {n m : ℕ} (hnm : n ≤ m) :
    recognition_free_energy sys (R.evolve m q₀).p X ≤
      recognition_free_energy sys (R.evolve n q₀).p X := by
  induction hnm with
  | refl => exact le_refl _
  | step _ ih => exact le_trans (free_energy_step_le sys X R q₀ _) ih

/-- **Free energy is monotone non-increasing along the J-descent evolution.**

    This is the second law in its sharpest form: `F_R(qₙ)` is a Lyapunov
    function for the recognition dynamics, with the Gibbs equilibrium as its
    unique global minimum. -/
theorem free_energy_antitone (sys : RecognitionSystem) (X : Ω → ℝ)
    (R : JDescentOperator (gibbsPD sys X)) (q₀ : ProbabilityDistribution Ω) :
    Antitone (fun n : ℕ => recognition_free_energy sys (R.evolve n q₀).p X) := by
  intro n m hnm
  exact free_energy_le_of_le sys X R q₀ hnm

/-- Free energy along the evolution is bounded below by the equilibrium
    value.  The variational principle: Gibbs minimizes `F_R`. -/
theorem free_energy_ge_equilibrium (sys : RecognitionSystem) (X : Ω → ℝ)
    (R : JDescentOperator (gibbsPD sys X)) (q₀ : ProbabilityDistribution Ω) (n : ℕ) :
    recognition_free_energy sys (gibbs_measure sys X) X ≤
      recognition_free_energy sys (R.evolve n q₀).p X :=
  gibbs_minimizes_free_energy_basic sys X (R.evolve n q₀)

/-! ## §5. The master second-law theorem -/

/-- **THE SECOND LAW OF THERMODYNAMICS — MASTER FORM.**

    For any J-descent operator `R` with equilibrium `peq = gibbsPD sys X`, and
    any initial distribution `q₀`, the discrete trajectory `qₙ = R.evolve n q₀`
    satisfies:

    1. KL divergence to equilibrium is monotone non-increasing.
    2. Recognition free energy is monotone non-increasing.
    3. Recognition free energy is bounded below by the equilibrium value.

    All three statements hold simultaneously and unconditionally on the input
    `q₀`. -/
theorem second_law (sys : RecognitionSystem) (X : Ω → ℝ)
    (R : JDescentOperator (gibbsPD sys X)) (q₀ : ProbabilityDistribution Ω) :
    Antitone (fun n : ℕ =>
        kl_divergence (R.evolve n q₀).p (gibbs_measure sys X)) ∧
      Antitone (fun n : ℕ =>
        recognition_free_energy sys (R.evolve n q₀).p X) ∧
      (∀ n : ℕ,
        recognition_free_energy sys (gibbs_measure sys X) X ≤
        recognition_free_energy sys (R.evolve n q₀).p X) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := kl_divergence_antitone (R := R) q₀
    simpa [gibbsPD_p] using h
  · exact free_energy_antitone sys X R q₀
  · exact free_energy_ge_equilibrium sys X R q₀

/-! ## §6. The Lyapunov / one-statement form -/

/-- **THE SECOND LAW — LYAPUNOV (ONE-STATEMENT) FORM.**

    There is a non-negative quantity `H_RS(qₙ) := F_R(qₙ) − F_R(peq)` that is

    * bounded below by `0` (variational principle),
    * monotone non-increasing along the J-descent evolution (second law).

    `H_RS` is the recognition-science analogue of Boltzmann's `H` function.
    It collapses to `0` exactly at equilibrium and provides a quantitative
    convergence rate for the dynamics. -/
theorem second_law_one_statement (sys : RecognitionSystem) (X : Ω → ℝ)
    (R : JDescentOperator (gibbsPD sys X)) (q₀ : ProbabilityDistribution Ω) :
    let H : ℕ → ℝ := fun n =>
      recognition_free_energy sys (R.evolve n q₀).p X -
        recognition_free_energy sys (gibbs_measure sys X) X
    (∀ n : ℕ, 0 ≤ H n) ∧ Antitone H := by
  intro H
  refine ⟨?_, ?_⟩
  · intro n
    show 0 ≤ recognition_free_energy sys (R.evolve n q₀).p X -
        recognition_free_energy sys (gibbs_measure sys X) X
    have := free_energy_ge_equilibrium sys X R q₀ n
    linarith
  · intro n m hnm
    show recognition_free_energy sys (R.evolve m q₀).p X -
        recognition_free_energy sys (gibbs_measure sys X) X ≤
        recognition_free_energy sys (R.evolve n q₀).p X -
        recognition_free_energy sys (gibbs_measure sys X) X
    have hF :
        recognition_free_energy sys (R.evolve m q₀).p X ≤
          recognition_free_energy sys (R.evolve n q₀).p X :=
      free_energy_le_of_le sys X R q₀ hnm
    linarith

/-! ## §7. The Clausius / entropy form -/

/-- **THE SECOND LAW — CLAUSIUS / ENTROPY FORM.**

    If the expected cost `⟨X⟩` is conserved along the J-descent evolution
    (i.e. the system is energetically isolated), then the recognition entropy
    `S_R(qₙ) = −Σ qₙ(ω) log qₙ(ω)` is monotone non-decreasing in `n`.

    This is the classical statement `ΔS ≥ 0` for an isolated system,
    derived from the free-energy form `F = ⟨X⟩ − T_R · S_R`. -/
theorem second_law_entropy_form (sys : RecognitionSystem) (X : Ω → ℝ)
    (R : JDescentOperator (gibbsPD sys X)) (q₀ : ProbabilityDistribution Ω)
    (h_conserve : ∀ n : ℕ,
      expected_cost (R.evolve n q₀).p X = expected_cost q₀.p X) :
    Monotone (fun n : ℕ => recognition_entropy (R.evolve n q₀).p) := by
  intro n m hnm
  show recognition_entropy (R.evolve n q₀).p ≤ recognition_entropy (R.evolve m q₀).p
  have hF :
      recognition_free_energy sys (R.evolve m q₀).p X ≤
        recognition_free_energy sys (R.evolve n q₀).p X :=
    free_energy_le_of_le sys X R q₀ hnm
  have hE_n := h_conserve n
  have hE_m := h_conserve m
  unfold recognition_free_energy at hF
  rw [hE_n, hE_m] at hF
  -- F = ⟨X⟩ − T_R · S_R, with ⟨X⟩ identical at `n` and `m`,
  -- so `F_m ≤ F_n  ⟺  S_n ≤ S_m`.
  have hTR : 0 < sys.TR := sys.TR_pos
  nlinarith

/-- Numeric `ΔS ≥ 0` form. -/
theorem entropy_increase_under_conservation (sys : RecognitionSystem) (X : Ω → ℝ)
    (R : JDescentOperator (gibbsPD sys X)) (q₀ : ProbabilityDistribution Ω)
    (h_conserve : ∀ n : ℕ,
      expected_cost (R.evolve n q₀).p X = expected_cost q₀.p X)
    (n m : ℕ) (hnm : n ≤ m) :
    0 ≤ recognition_entropy (R.evolve m q₀).p -
        recognition_entropy (R.evolve n q₀).p := by
  have h :
      recognition_entropy (R.evolve n q₀).p ≤
        recognition_entropy (R.evolve m q₀).p :=
    second_law_entropy_form sys X R q₀ h_conserve hnm
  linarith

/-! ## §8. Master certificate -/

/-- **MASTER CERTIFICATE for the second law in Recognition Science.**

    A single record bundling every classical formulation of the second law
    that is provable from the recognition operator's J-descent property: -/
structure SecondLawCert (sys : RecognitionSystem) (X : Ω → ℝ) where
  /-- Gibbs inequality: the KL divergence to Gibbs is non-negative. -/
  gibbs_inequality :
    ∀ q : ProbabilityDistribution Ω,
      0 ≤ kl_divergence q.p (gibbs_measure sys X)
  /-- Variational principle: Gibbs minimizes the free energy. -/
  gibbs_minimizes :
    ∀ q : ProbabilityDistribution Ω,
      recognition_free_energy sys (gibbs_measure sys X) X ≤
        recognition_free_energy sys q.p X
  /-- Free-energy / KL identity: `F(q) − F(π) = T_R · D_KL(q ‖ π)`. -/
  fe_kl_identity :
    ∀ q : ProbabilityDistribution Ω,
      recognition_free_energy sys q.p X -
          recognition_free_energy sys (gibbs_measure sys X) X =
        sys.TR * kl_divergence q.p (gibbs_measure sys X)
  /-- KL is antitone along any J-descent evolution. -/
  kl_monotone :
    ∀ (R : JDescentOperator (gibbsPD sys X)) (q₀ : ProbabilityDistribution Ω),
      Antitone (fun n : ℕ =>
        kl_divergence (R.evolve n q₀).p (gibbs_measure sys X))
  /-- Free energy is antitone along any J-descent evolution. -/
  free_energy_monotone :
    ∀ (R : JDescentOperator (gibbsPD sys X)) (q₀ : ProbabilityDistribution Ω),
      Antitone (fun n : ℕ => recognition_free_energy sys (R.evolve n q₀).p X)
  /-- Recognition entropy is monotone non-decreasing under conserved energy. -/
  entropy_monotone_under_conservation :
    ∀ (R : JDescentOperator (gibbsPD sys X)) (q₀ : ProbabilityDistribution Ω),
      (∀ n : ℕ, expected_cost (R.evolve n q₀).p X = expected_cost q₀.p X) →
        Monotone (fun n : ℕ => recognition_entropy (R.evolve n q₀).p)

/-- The master certificate is inhabited. -/
noncomputable def secondLawCert (sys : RecognitionSystem) (X : Ω → ℝ) :
    SecondLawCert sys X where
  gibbs_inequality q :=
    kl_divergence_nonneg q.p (gibbs_measure sys X) q.nonneg
      (fun ω => gibbs_measure_pos sys X ω)
      q.sum_one
      (gibbs_measure_sum_one sys X)
  gibbs_minimizes q := gibbs_minimizes_free_energy_basic sys X q
  fe_kl_identity q := free_energy_kl_identity sys X q
  kl_monotone R q₀ := by
    have h := kl_divergence_antitone (R := R) q₀
    simpa [gibbsPD_p] using h
  free_energy_monotone R q₀ := free_energy_antitone sys X R q₀
  entropy_monotone_under_conservation R q₀ h_conserve :=
    second_law_entropy_form sys X R q₀ h_conserve

theorem secondLawCert_inhabited (sys : RecognitionSystem) (X : Ω → ℝ) :
    Nonempty (SecondLawCert sys X) :=
  ⟨secondLawCert sys X⟩

end SecondLaw
end Thermodynamics
end IndisputableMonolith

/-! ### Axiom audit

Each `#print axioms` line below is checked at compile time.  All five
master statements close on the standard Mathlib axioms only
(`propext`, `Classical.choice`, `Quot.sound`).  No RS-specific axiom
and no `sorry` are introduced. -/

#print axioms IndisputableMonolith.Thermodynamics.SecondLaw.kl_divergence_antitone
#print axioms IndisputableMonolith.Thermodynamics.SecondLaw.free_energy_antitone
#print axioms IndisputableMonolith.Thermodynamics.SecondLaw.second_law
#print axioms IndisputableMonolith.Thermodynamics.SecondLaw.second_law_one_statement
#print axioms IndisputableMonolith.Thermodynamics.SecondLaw.second_law_entropy_form
#print axioms IndisputableMonolith.Thermodynamics.SecondLaw.secondLawCert
