import IndisputableMonolith.Gravity.SevenGaps.Gap2TickPhaseSubstrate

/-!
# Wave C1 R4 hardening: tick-phase tail blocker / eventual-balance repair

Hardens the R4 residual named in
`plans/QG_WaveC1_Gap2_Residual_DAG_Draft_20260722.txt` after the
cross-family design correction to the R2 receipt:

* (a) Generic bridge: all-shell `TickFiberMassBalanced` makes every
  `exactShellAmplitude` identically zero, so contiguous-block sums vanish
  and yield `ExactShellTailCancellation` / `OscillatoryTail`.
* (b) Finite-head impossibility: shell `0` is a singleton class, so
  `classMu`-mass concentrates in one tick fiber for every `tau`;
  therefore `¬ ∃ tau, TickFiberMassBalanced tau`.
* (c) Eventual-balance repair: `EventuallyTickFiberMassBalanced` kills all
  late amplitudes; the finite head is irrelevant to `OscillatoryTail`.
* (d) Signature-level blocker target `SignatureFin8OscillatoryTailBlocker`
  (defined; neither proved nor assumed).

## Divergence from the R2 receipt assessment

The R2 module docstring claimed per-shell equidistribution /
`ShellAmplitudeVanishes` is insufficient for contiguous-block
cancellation. That is true for the *asymptotic* form of
`ShellAmplitudeVanishes` (late shells merely small). It is false for
*identically zero* amplitudes: under all-shell mass balance every shell
amplitude is definitionally zero, so every contiguous block sum is zero.
No extra estimate is required for the lift.

## What stays OPEN

The R4 residual itself: existence of a substrate phase (escaping the
dead classes) with `OscillatoryTail`. The sharper terminal candidate
`SignatureFin8OscillatoryTailBlocker` is defined here but not proved.

Does NOT flip `gap2_continuum_and_measure`. No `sorry`, `admit`, new
axiom, or `native_decide`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2TickPhaseTailBlocker

open ExactShellGaugeUV
open ZqContinuumBlocker
open Gap2TickPhaseSubstrate

noncomputable section

/-! ## §1. Shell-0 singleton (finite-head geometry) -/

private theorem shellSig_zero_eq (s : ShellSig 0) : s = isolatedSig 0 := by
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.eq_zero _
  · apply Prod.ext <;> exact Fin.eq_zero _

private theorem exactComplex_zero_eq (K : ExactComplex 0 0 0) :
    K = isolatedVertices 0 := by
  cases K with | mk e t =>
  have he : e = (isolatedVertices 0).edgeVerts := funext fun i => i.elim0
  have ht : t = (isolatedVertices 0).tetVerts := funext fun i => i.elim0
  rw [he, ht]

/-- Every class at shell `0` equals the unique empty-complex class. -/
theorem exactPathClass_zero_eq (c : ExactPathClass 0) : c = isolatedClass 0 := by
  cases c with | mk s q =>
  have hs : s = isolatedSig 0 := shellSig_zero_eq s
  subst hs
  refine Sigma.ext rfl ?_
  simp only [heq_eq_eq]
  refine Quotient.inductionOn q fun K => ?_
  rw [exactComplex_zero_eq K]
  rfl

/-- **Finite-head fact.** The exact complexity shell at level `0` is a
singleton: only the empty signature `(0,0,0)` and its unique class. -/
theorem exactPathClass_zero_subsingleton : Subsingleton (ExactPathClass 0) :=
  ⟨fun a b => by rw [exactPathClass_zero_eq a, exactPathClass_zero_eq b]⟩

private theorem finset_univ_exactPathClass_zero :
    (Finset.univ : Finset (ExactPathClass 0)) = {isolatedClass 0} := by
  ext c
  simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
  exact exactPathClass_zero_eq c

/-- For any tick assignment, shell-0 `classMu` mass sits in exactly one
tick fiber (the tick of the unique class); the other seven fibers are empty. -/
theorem tickFiberMass_shell_zero
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) (p : Fin 8) :
    tickFiberMass tau 0 p =
      if tau 0 (isolatedClass 0) = p then classMu (isolatedClass 0) else 0 := by
  unfold tickFiberMass tickFiber
  rw [finset_univ_exactPathClass_zero, Finset.filter_singleton]
  split_ifs with h
  · simp
  · simp

/-- Design-named packaging of the shell-0 degeneracy used by the
all-shell balance impossibility. -/
theorem exactPathClass_zero_subsingleton_or_the_precise_finite_head_fact :
    Subsingleton (ExactPathClass 0) ∧
      ∀ tau : ∀ n : ℕ, ExactPathClass n → Fin 8,
        ∃ p : Fin 8,
          tickFiberMass tau 0 p = classMu (isolatedClass 0) ∧
            ∀ q : Fin 8, q ≠ p → tickFiberMass tau 0 q = 0 := by
  refine ⟨exactPathClass_zero_subsingleton, fun tau => ?_⟩
  refine ⟨tau 0 (isolatedClass 0), ?_, ?_⟩
  · simp [tickFiberMass_shell_zero]
  · intro q hq
    rw [tickFiberMass_shell_zero]
    simp [show tau 0 (isolatedClass 0) ≠ q from Ne.symm hq]

private lemma fin8_add_one_ne (p : Fin 8) : p + 1 ≠ p := by
  intro h
  have hv := congrArg Fin.val h
  have hp : p.val < 8 := p.isLt
  simp only [Fin.val_add] at hv
  have : (p.val + 1) % 8 ≠ p.val := by omega
  exact this hv

/-- **THEOREM.** No Fin-8 tick assignment is mass-balanced on every shell.
Cause: shell `0` concentrates all positive `classMu` mass in a single fiber. -/
theorem no_tickFiberMassBalanced :
    ¬ ∃ tau : ∀ n : ℕ, ExactPathClass n → Fin 8, TickFiberMassBalanced tau := by
  rintro ⟨tau, hbal⟩
  let p : Fin 8 := tau 0 (isolatedClass 0)
  let q : Fin 8 := p + 1
  have hpq : p ≠ q := (fin8_add_one_ne p).symm
  have hm_p : tickFiberMass tau 0 p = classMu (isolatedClass 0) := by
    simp [tickFiberMass_shell_zero, p]
  have hm_q : tickFiberMass tau 0 q = 0 := by
    have hne : tau 0 (isolatedClass 0) ≠ q := hpq
    rw [tickFiberMass_shell_zero]
    simp [hne]
  have heq := hbal 0 p q
  rw [hm_p, hm_q] at heq
  exact (ne_of_gt (classMu_pos (isolatedClass 0))) heq

/-! ## §2. Generic bridge: balance ⇒ identical zero amplitudes ⇒ cancellation -/

/-- Per-shell form of the root-of-unity cancellation (no all-shell hyp). -/
theorem exactShellAmplitude_eq_zero_of_massBalanced_at
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) (n : ℕ)
    (hbal : ∀ p q : Fin 8, tickFiberMass tau n p = tickFiberMass tau n q) :
    exactShellAmplitude (tickDerivedPhase tau) n = 0 := by
  rw [exactShellAmplitude_tick_fiberwise]
  have hconst : ∀ p : Fin 8, tickFiberMass tau n p = tickFiberMass tau n 0 :=
    fun p => hbal p 0
  calc ∑ p : Fin 8, (tickFiberMass tau n p : ℂ) * tickRoot p
      = ∑ p : Fin 8, (tickFiberMass tau n 0 : ℂ) * tickRoot p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hconst p]
    _ = (tickFiberMass tau n 0 : ℂ) * ∑ p : Fin 8, tickRoot p := by
        rw [Finset.mul_sum]
    _ = (tickFiberMass tau n 0 : ℂ) * 0 := by rw [sum_tickRoots_eq_zero]
    _ = 0 := by ring

private theorem sum_amp_eq_zero_of_amps_zero
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ)
    {s : Finset ℕ}
    (h : ∀ k ∈ s, exactShellAmplitude phase k = 0) :
    ∑ k ∈ s, exactShellAmplitude phase k = 0 :=
  Finset.sum_eq_zero h

/-- **BRIDGE (generic).** All-shell tick-fiber mass balance forces every
exact-shell amplitude to vanish identically; contiguous late-block sums of
zeros are zero, hence `ExactShellTailCancellation`. No extra estimate. -/
theorem tickFiberMassBalanced_implies_exactShellTailCancellation
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8)
    (hbal : TickFiberMassBalanced tau) :
    ExactShellTailCancellation (tickDerivedPhase tau) := by
  intro ε hε
  refine ⟨0, fun m n _hm _hmn => ?_⟩
  have hamp :
      ∀ k ∈ Finset.Ico (m + 1) (n + 1),
        exactShellAmplitude (tickDerivedPhase tau) k = 0 :=
    fun k _ => exactShellAmplitude_eq_zero_of_massBalanced tau hbal k
  rw [sum_amp_eq_zero_of_amps_zero _ hamp, norm_zero]
  exact hε

/-- Same bridge for the panel-locked `OscillatoryTail` indexing
(`Ico m n` rather than ordered `Ico (m+1) (n+1)`). -/
theorem tickFiberMassBalanced_implies_oscillatoryTail
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8)
    (hbal : TickFiberMassBalanced tau) :
    OscillatoryTail (tickDerivedPhase tau) := by
  intro ε hε
  refine ⟨0, fun m n _hm _hmn => ?_⟩
  have hamp :
      ∀ k ∈ Finset.Ico m n,
        exactShellAmplitude (tickDerivedPhase tau) k = 0 :=
    fun k _ => exactShellAmplitude_eq_zero_of_massBalanced tau hbal k
  rw [sum_amp_eq_zero_of_amps_zero _ hamp, norm_zero]
  exact hε

/-- Identically-zero amplitudes lift to full `ExactShellTailCancellation`
(the honest extra hypothesis beyond the asymptotic vanishing Prop). -/
theorem exactShellTailCancellation_of_identically_zero_amplitudes
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ)
    (hzero : ∀ n : ℕ, exactShellAmplitude phase n = 0) :
    ExactShellTailCancellation phase := by
  intro ε hε
  refine ⟨0, fun m n _hm _hmn => ?_⟩
  have hamp :
      ∀ k ∈ Finset.Ico (m + 1) (n + 1), exactShellAmplitude phase k = 0 :=
    fun k _ => hzero k
  rw [sum_amp_eq_zero_of_amps_zero _ hamp, norm_zero]
  exact hε

/-! ## §3. Eventual (tail) balance repair -/

/-- Honest credit-bearing repair of all-shell balance: equal fiber mass
from some shell onward. The finite head may be unbalanced. -/
def EventuallyTickFiberMassBalanced
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ p q : Fin 8, tickFiberMass tau n p = tickFiberMass tau n q

/-- **THEOREM.** Eventual mass balance kills every late shell amplitude;
`OscillatoryTail` only constrains late contiguous blocks, so the finite
head is irrelevant. -/
theorem eventuallyTickFiberMassBalanced_implies_oscillatoryTail
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8)
    (hbal : EventuallyTickFiberMassBalanced tau) :
    OscillatoryTail (tickDerivedPhase tau) := by
  obtain ⟨N, hN⟩ := hbal
  intro ε hε
  refine ⟨N, fun m n hm _hmn => ?_⟩
  have hamp :
      ∀ k ∈ Finset.Ico m n,
        exactShellAmplitude (tickDerivedPhase tau) k = 0 := by
    intro k hk
    have hkN : N ≤ k :=
      le_trans hm (Finset.mem_Ico.mp hk).1
    exact exactShellAmplitude_eq_zero_of_massBalanced_at tau k (hN k hkN)
  rw [sum_amp_eq_zero_of_amps_zero _ hamp, norm_zero]
  exact hε

theorem eventuallyTickFiberMassBalanced_implies_exactShellTailCancellation
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8)
    (hbal : EventuallyTickFiberMassBalanced tau) :
    ExactShellTailCancellation (tickDerivedPhase tau) := by
  obtain ⟨N, hN⟩ := hbal
  intro ε hε
  refine ⟨N, fun m n hm _hmn => ?_⟩
  have hamp :
      ∀ k ∈ Finset.Ico (m + 1) (n + 1),
        exactShellAmplitude (tickDerivedPhase tau) k = 0 := by
    intro k hk
    have hk_ge : m + 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkN : N ≤ k := le_trans (Nat.le_succ_of_le hm) hk_ge
    exact exactShellAmplitude_eq_zero_of_massBalanced_at tau k (hN k hkN)
  rw [sum_amp_eq_zero_of_amps_zero _ hamp, norm_zero]
  exact hε

/-! ## §4. Signature-level tick class and blocker target -/

/-- Tick assignments that factor through the shell signature
`(v,e,t)` (no quotient-internal incidence data). -/
def ShellSigTick (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) : Prop :=
  ∃ sigma : ∀ n : ℕ, ShellSig n → Fin 8,
    ∀ n : ℕ, ∀ c : ExactPathClass n, tau n c = sigma n c.1

/-- **DEFINED, neither proved nor assumed.** Sharpened R4 terminal
candidate: no signature-factoring Fin-8 tick yields
`OscillatoryTail` on the derived phase.

Honest status: this Prop is stated precisely as the credit-bearing
blocker target. Proving it needs the fiber-mass computation for all
signature ticks (a separate campaign). It is not assumed anywhere in
this module, and the R4 residual (a substrate phase with
`OscillatoryTail`) remains OPEN. -/
def SignatureFin8OscillatoryTailBlocker : Prop :=
  ¬ ∃ tau : ∀ n : ℕ, ExactPathClass n → Fin 8,
      ShellSigTick tau ∧ OscillatoryTail (tickDerivedPhase tau)

/-! ## §5. Status (no continuum flip) -/

structure Gap2TickPhaseTailBlockerStatus where
  allShellBalanceImpossible : Bool
  eventualBalanceBridgeLanded : Bool
  signatureBlockerDefinedUnproved : Bool
  r4ResidualOpen : Bool
  gap2ContinuumAndMeasure : Bool

def gap2TickPhaseTailBlockerStatus : Gap2TickPhaseTailBlockerStatus where
  allShellBalanceImpossible := true
  eventualBalanceBridgeLanded := true
  signatureBlockerDefinedUnproved := true
  r4ResidualOpen := true
  gap2ContinuumAndMeasure := false

theorem gap2TickPhaseTailBlockerStatus_flags :
    gap2TickPhaseTailBlockerStatus.allShellBalanceImpossible = true ∧
      gap2TickPhaseTailBlockerStatus.eventualBalanceBridgeLanded = true ∧
      gap2TickPhaseTailBlockerStatus.signatureBlockerDefinedUnproved = true ∧
      gap2TickPhaseTailBlockerStatus.r4ResidualOpen = true ∧
      gap2TickPhaseTailBlockerStatus.gap2ContinuumAndMeasure = false := by
  decide

end

end Gap2TickPhaseTailBlocker
end SevenGaps
end Gravity
end IndisputableMonolith
