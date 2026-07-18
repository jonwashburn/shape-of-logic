import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.ZqPhaseStructure
import IndisputableMonolith.Gravity.SevenGaps.RegulatorRemovalNoGo

/-!
# Seven Gaps, P2-a: the phased quotient cutoff blocker

This module isolates the exact analytic and API obligations for removing the
complexity cutoff from the phased quotient path sum.

The fixed-cap API can express a family of phase models and hence a sequence of
finite quotient sums. Completeness of `ℂ` gives an exact criterion: that
sequence has a limit if and only if it is Cauchy.

The cap-free exact-shell API gives the panel-locked form. `Zcap phase B` sums
the exact quotient shells in `range B`, and `OscillatoryTail phase` uniformly
quantifies every sufficiently late contiguous shell block. Exact telescoping
proves `CauchySeq (Zcap phase) ↔ OscillatoryTail phase`. This is the
cancellation statement that a substrate-derived phase must supply. It is
discriminating: the zero phase has an explicit epsilon-one failure witness.

One bridge is still absent from the current API. `Zq B` uses the capped
quotient `TriangulationClass B`, while the nonduplicating shell decomposition
uses `ExactPathClass n`. `CapShellCompatibility` names the smallest required
cross-API statement: equality of the two finite sums at every cap. Under that
bridge, convergence of the existing phased `Zq` sequence is equivalent to the
exact-shell tail-cancellation criterion.

All limits here remove a complexity cutoff. They are not mesh refinement and
carry no claim about continuum geometry, observations, a convergence rate, a
derived measure, or the full-theory ledger.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace ZqContinuumBlocker

open PathSumMeasure
open QuotientFirstZ
open ZqPhaseStructure
open ExactShellGaugeUV

noncomputable section

/-! ## 1. What the current capped `Zq` API can state -/

/-- A phase choice at every complexity cap. This supplies no cross-cap
coherence by itself. -/
abbrev CapPhaseFamily := ∀ B : ℕ, PhaseModel B

/-- The finite phased quotient sum at each cap. -/
def phasedZqSequence (P : CapPhaseFamily) : ℕ → ℂ :=
  fun B => Zq B (phasedWeight (P B))

/-- Removal of the complexity cap for the existing capped quotient sums.
This is not a mesh-refinement limit. -/
def HasPhasedZqComplexityLimit (P : CapPhaseFamily) : Prop :=
  ∃ L : ℂ, Filter.Tendsto (phasedZqSequence P) Filter.atTop (nhds L)

/-- The exact Cauchy obligation on the existing finite quotient sums. -/
def PhasedZqCauchyCriterion (P : CapPhaseFamily) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ n : ℕ, N ≤ n →
    ‖phasedZqSequence P m - phasedZqSequence P n‖ < ε

/-- **HEADLINE IFF.** The existing phased quotient sums have a
complexity-cutoff limit exactly when their cross-cap differences are Cauchy.
This theorem assumes no convergence and no physical continuum interpretation.
-/
theorem hasPhasedZqComplexityLimit_iff_cauchy (P : CapPhaseFamily) :
    HasPhasedZqComplexityLimit P ↔ PhasedZqCauchyCriterion P := by
  constructor
  · rintro ⟨L, hL⟩
    have hC := (Metric.cauchySeq_iff.mp hL.cauchySeq)
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa only [dist_eq_norm] using hN m hm n hn
  · intro h
    have hC : CauchySeq (phasedZqSequence P) := by
      rw [Metric.cauchySeq_iff]
      exact h
    exact cauchySeq_tendsto_of_complete hC

/-! ## 2. The cap-free exact-shell cutoff and its ordered tails -/

/-- The unregulated phased amplitude of exact complexity shell `n`. -/
def exactShellAmplitude
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) (n : ℕ) : ℂ :=
  ∑ c : ExactPathClass n,
    (classMu c : ℂ) * Complex.exp (Complex.I * (phase n c : ℂ))

/-! ### The binding C1 statement -/

/-- The panel-locked exact-shell complexity cutoff. `Zcap phase B` contains
exactly the quotient shells with indices in `range B`, hence complexities
strictly below `B`. This is a complexity cutoff, not mesh refinement. -/
def Zcap (phase : ∀ n : ℕ, ExactPathClass n → ℝ) (B : ℕ) : ℂ :=
  ∑ n ∈ Finset.range B, exactShellAmplitude phase n

/-- The panel-locked oscillatory-tail requirement. Every sufficiently late
contiguous block of exact quotient shells must be small, uniformly in both
endpoints. No rate and no `Summable` hypothesis are imposed. -/
def OscillatoryTail
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → m ≤ n →
    ‖∑ k ∈ Finset.Ico m n, exactShellAmplitude phase k‖ < ε

/-- **C1 EXACT TELESCOPING.** The difference of two exact-shell cutoffs is
exactly the intervening contiguous shell block. -/
theorem Zcap_telescoping
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    Zcap phase n - Zcap phase m =
      ∑ k ∈ Finset.Ico m n, exactShellAmplitude phase k := by
  exact (Finset.sum_Ico_eq_sub (exactShellAmplitude phase) hmn).symm

/-- **C1 HEADLINE.** The exact-shell cutoff sequence is Cauchy if and only if
every sufficiently late contiguous shell block is uniformly small. This is a
pure complexity-cutoff criterion and assumes no desired convergence. -/
theorem cauchySeq_Zcap_iff_oscillatoryTail
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) :
    CauchySeq (Zcap phase) ↔ OscillatoryTail phase := by
  constructor
  · intro hC
    have hMetric := Metric.cauchySeq_iff.mp hC
    intro ε hε
    obtain ⟨N, hN⟩ := hMetric ε hε
    refine ⟨N, fun m n hm hmn => ?_⟩
    have hn : N ≤ n := le_trans hm hmn
    have hd := hN m hm n hn
    rw [dist_eq_norm] at hd
    rw [← Zcap_telescoping phase hmn, norm_sub_rev]
    exact hd
  · intro htail
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := htail ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rcases le_total m n with hmn | hnm
    · rw [dist_eq_norm, norm_sub_rev, Zcap_telescoping phase hmn]
      exact hN m n hm hmn
    · rw [dist_eq_norm, Zcap_telescoping phase hnm]
      exact hN n m hn hnm

/-- The exact-shell quotient sum through complexity `B`. Each exact complex
occurs in one shell, so this avoids cross-cap duplication. -/
def exactComplexityCutoff
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) (B : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (B + 1), exactShellAmplitude phase n

/-- Existence of the unregulated exact-shell complexity-cutoff limit.
This is not a mesh-refinement limit. -/
def HasExactComplexityCutoffLimit
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) : Prop :=
  ∃ L : ℂ, Filter.Tendsto (exactComplexityCutoff phase) Filter.atTop (nhds L)

/-- The required oscillatory cancellation: every sufficiently late block of
exact shell amplitudes is small. The interval `(m,n]` is represented as
`Ico (m+1) (n+1)`. -/
def ExactShellTailCancellation
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → m ≤ n →
    ‖∑ k ∈ Finset.Ico (m + 1) (n + 1), exactShellAmplitude phase k‖ < ε

/-- The difference between two exact-shell cutoffs is exactly the intervening
ordered shell block. -/
theorem exactComplexityCutoff_sub
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    exactComplexityCutoff phase n - exactComplexityCutoff phase m =
      ∑ k ∈ Finset.Ico (m + 1) (n + 1), exactShellAmplitude phase k := by
  exact (Finset.sum_Ico_eq_sub (exactShellAmplitude phase)
    (Nat.succ_le_succ hmn)).symm

/-- **HEADLINE IFF, ORDERED-TAIL FORM.** The unregulated exact-shell quotient
cutoff has a limit exactly when its late shell blocks cancel in norm. This is
the analytic premise that a substrate-derived oscillatory phase must prove.
-/
theorem hasExactComplexityCutoffLimit_iff_tailCancellation
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) :
    HasExactComplexityCutoffLimit phase ↔ ExactShellTailCancellation phase := by
  constructor
  · rintro ⟨L, hL⟩
    have hC := Metric.cauchySeq_iff.mp hL.cauchySeq
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun m n hm hmn => ?_⟩
    have hn : N ≤ n := le_trans hm hmn
    have hd := hN m hm n hn
    rw [dist_eq_norm] at hd
    rw [← exactComplexityCutoff_sub phase hmn, norm_sub_rev]
    exact hd
  · intro htail
    have hC : CauchySeq (exactComplexityCutoff phase) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := htail ε hε
      refine ⟨N, fun m hm n hn => ?_⟩
      rcases le_total m n with hmn | hnm
      · rw [dist_eq_norm, norm_sub_rev, exactComplexityCutoff_sub phase hmn]
        exact hN m n hm hmn
      · rw [dist_eq_norm, exactComplexityCutoff_sub phase hnm]
        exact hN n m hn hnm
    exact cauchySeq_tendsto_of_complete hC

/-! ## 3. Concrete zero-phase failure witness -/

/-- At zero phase, the unregulated exact shell amplitude is the positive real
shell mass. -/
theorem exactShellAmplitude_zeroPhase (n : ℕ) :
    exactShellAmplitude zeroPhase n = (shellMass n : ℂ) := by
  unfold exactShellAmplitude zeroPhase shellMass
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

/-- **C1 EPSILON-ONE WITNESS.** Beyond every proposed tail threshold there
is a contiguous one-shell block whose zero-phase norm is greater than one.
The bridge is direct: `shellMass_lower` concerns the same cap-free exact
quotient `ExactPathClass` and the same `classMu` used by
`exactShellAmplitude`; it is neither a pre-quotient nor a cap-dependent mass.
-/
theorem zeroPhase_epsilon_one_failure (N : ℕ) :
    ∃ m n : ℕ, N ≤ m ∧ m ≤ n ∧
      1 < ‖∑ k ∈ Finset.Ico m n, exactShellAmplitude zeroPhase k‖ := by
  let k : ℕ := max 2 N
  have hNk : N ≤ k := le_max_right 2 N
  have hsingle :
      ∑ j ∈ Finset.Ico k (k + 1), exactShellAmplitude zeroPhase j =
        exactShellAmplitude zeroPhase k := by
    rw [Finset.sum_Ico_eq_sub (exactShellAmplitude zeroPhase)
      (Nat.le_succ k), Finset.sum_range_succ, add_sub_cancel_left]
  have hk2 : 2 ≤ k := le_max_left 2 N
  have hpowN : k ≤ k ^ (3 * k) :=
    Nat.le_self_pow (by omega) k
  have hpowR : ((k : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) ^ (3 * k) := by
    calc
      ((k : ℕ) : ℝ) ≤ ((k ^ (3 * k) : ℕ) : ℝ) := by
        exact_mod_cast hpowN
      _ = ((k : ℕ) : ℝ) ^ (3 * k) := Nat.cast_pow _ _
  have hkR : (1 : ℝ) < (k : ℕ) := by
    exact_mod_cast (show 1 < k by omega)
  have hmass : (1 : ℝ) < shellMass k := by
    have hlower := RegulatorRemovalNoGo.shellMass_lower k
    linarith
  refine ⟨k, k + 1, hNk, Nat.le_succ k, ?_⟩
  rw [hsingle, exactShellAmplitude_zeroPhase, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (shellMass_pos k)]
  exact hmass

/-- **NON-VACUITY WITNESS.** Zero phase fails the ordered-tail cancellation
criterion. A one-shell late block already has norm greater than one, because
the positive shell masses grow at least as `n^(3n)`. -/
theorem zeroPhase_not_exactShellTailCancellation :
    ¬ ExactShellTailCancellation zeroPhase := by
  intro htail
  obtain ⟨N, hN⟩ := htail 1 one_pos
  let k : ℕ := max 2 N
  have hNk : N ≤ k := le_max_right 2 N
  have hsingle :
      ∑ j ∈ Finset.Ico (k + 1) ((k + 1) + 1),
          exactShellAmplitude zeroPhase j =
        exactShellAmplitude zeroPhase (k + 1) := by
    rw [Finset.sum_Ico_eq_sub (exactShellAmplitude zeroPhase)
      (Nat.le_succ (k + 1)), Finset.sum_range_succ, add_sub_cancel_left]
  have hsmall := hN k (k + 1) hNk (Nat.le_succ k)
  rw [hsingle, exactShellAmplitude_zeroPhase, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (shellMass_pos (k + 1))] at hsmall
  have hk2 : 2 ≤ k := le_max_left 2 N
  have hpowN : k + 1 ≤ (k + 1) ^ (3 * (k + 1)) :=
    Nat.le_self_pow (by omega) (k + 1)
  have hpowR :
      ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ (3 * (k + 1)) := by
    calc
      ((k + 1 : ℕ) : ℝ)
          ≤ (((k + 1) ^ (3 * (k + 1)) : ℕ) : ℝ) := by
            exact_mod_cast hpowN
      _ = ((k + 1 : ℕ) : ℝ) ^ (3 * (k + 1)) := Nat.cast_pow _ _
  have hkR : (1 : ℝ) < (k + 1 : ℕ) := by
    exact_mod_cast (show 1 < k + 1 by omega)
  have hmass : (1 : ℝ) < shellMass (k + 1) := by
    have hlower := RegulatorRemovalNoGo.shellMass_lower (k + 1)
    linarith
  linarith

/-- The panel-locked `OscillatoryTail` criterion fails at zero phase, with
the explicit epsilon-one witness above. -/
theorem zeroPhase_not_oscillatoryTail :
    ¬ OscillatoryTail zeroPhase := by
  intro htail
  obtain ⟨N, hN⟩ := htail 1 one_pos
  obtain ⟨m, n, hm, hmn, hlarge⟩ := zeroPhase_epsilon_one_failure N
  have hsmall := hN m n hm hmn
  linarith

/-- Consequently the exact zero-phase `Zcap` sequence is not Cauchy. -/
theorem zeroPhase_Zcap_not_cauchy :
    ¬ CauchySeq (Zcap zeroPhase) := by
  rw [cauchySeq_Zcap_iff_oscillatoryTail]
  exact zeroPhase_not_oscillatoryTail

/-- Zero phase has no unregulated exact-shell complexity-cutoff limit. -/
theorem not_hasExactComplexityCutoffLimit_zeroPhase :
    ¬ HasExactComplexityCutoffLimit zeroPhase := by
  rw [hasExactComplexityCutoffLimit_iff_tailCancellation]
  exact zeroPhase_not_exactShellTailCancellation

/-- Zero phase fails both available removal routes: the unregulated
complexity cutoff and the positive Gaussian regulator-removal limit. Neither
statement is a mesh-refinement or physical-continuum claim. -/
theorem zeroPhase_fails_both_removal_routes :
    (¬ HasExactComplexityCutoffLimit zeroPhase) ∧
      (¬ HasZRSRegulatorRemoval zeroPhase) :=
  ⟨not_hasExactComplexityCutoffLimit_zeroPhase,
    RegulatorRemovalNoGo.not_hasZRSRegulatorRemoval_zeroPhase⟩

/-! ## 4. The smallest missing bridge from capped `Zq` to exact shells -/

/-- Cross-API compatibility needed to identify the current capped quotient
sum with the nonduplicating exact-shell cutoff. Current definitions do not
supply this equality. A construction should come from an equivalence between
bounded quotient classes at cap `B` and exact quotient classes in shells
`n ≤ B`, preserving the measure and phase. -/
structure CapShellCompatibility (P : CapPhaseFamily)
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) : Prop where
  sum_eq : ∀ B : ℕ,
    phasedZqSequence P B = exactComplexityCutoff phase B

/-- **BLOCKER CERTIFICATE.** Once the missing cap-to-shell compatibility is
supplied, convergence of the existing phased `Zq B` sequence is exactly the
ordered-tail cancellation obligation on exact shells. No desired convergence
is assumed. -/
theorem hasPhasedZqLimit_iff_exactShellTail_of_compatibility
    (P : CapPhaseFamily) (phase : ∀ n : ℕ, ExactPathClass n → ℝ)
    (hcompat : CapShellCompatibility P phase) :
    HasPhasedZqComplexityLimit P ↔ ExactShellTailCancellation phase := by
  have hseq : phasedZqSequence P = exactComplexityCutoff phase :=
    funext hcompat.sum_eq
  unfold HasPhasedZqComplexityLimit
  rw [hseq]
  exact hasExactComplexityCutoffLimit_iff_tailCancellation phase

/-- The zero phase family on the existing capped quotient API. -/
def zeroCapPhaseFamily : CapPhaseFamily :=
  fun _B =>
    { phase := fun _K => 0
      invariant := fun _K _K' _h => rfl }

/-- A zero-phase capped family cannot both agree with the exact-shell
decomposition and have a complexity-cutoff limit. This is a concrete
discriminant for any proposed bridge implementation. -/
theorem zeroPhase_compatibility_and_limit_impossible :
    ¬ (CapShellCompatibility zeroCapPhaseFamily zeroPhase ∧
      HasPhasedZqComplexityLimit zeroCapPhaseFamily) := by
  rintro ⟨hcompat, hlimit⟩
  exact zeroPhase_not_exactShellTailCancellation
    ((hasPhasedZqLimit_iff_exactShellTail_of_compatibility
      zeroCapPhaseFamily zeroPhase hcompat).mp hlimit)

#print axioms Zcap_telescoping
#print axioms cauchySeq_Zcap_iff_oscillatoryTail
#print axioms zeroPhase_epsilon_one_failure
#print axioms zeroPhase_not_oscillatoryTail
#print axioms zeroPhase_Zcap_not_cauchy
#print axioms hasPhasedZqComplexityLimit_iff_cauchy
#print axioms hasExactComplexityCutoffLimit_iff_tailCancellation
#print axioms zeroPhase_not_exactShellTailCancellation
#print axioms not_hasExactComplexityCutoffLimit_zeroPhase
#print axioms zeroPhase_fails_both_removal_routes
#print axioms hasPhasedZqLimit_iff_exactShellTail_of_compatibility
#print axioms zeroPhase_compatibility_and_limit_impossible

end

end ZqContinuumBlocker
end SevenGaps
end Gravity
end IndisputableMonolith
