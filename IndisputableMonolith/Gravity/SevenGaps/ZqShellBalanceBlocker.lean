import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.ZqContinuumBlocker

/-!
# Seven Gaps, P2.4: exact-shell phase-balance blocker

This module attacks the phase obligation in
`ZqContinuumBlocker.OscillatoryTail` without assuming cancellation.

The current carrier facts prove finite exact shells, positive class masses,
large shell mass, and one fixed-cap pairing witness. They do not provide a
substrate action that resolves phases inside every late shell. The theorems
below isolate that missing content.

* `ShellAmplitudeVanishes` is the weakest shell-local necessary condition:
  every individual late exact-shell amplitude must tend to zero.
  `OscillatoryTail` implies it by taking one-shell blocks.
* `eventuallyZeroPhase_not_oscillatoryTail` proves that changing only
  finitely many shells cannot help. In particular, a finite-cap pairing
  certificate cannot imply the uniform tail condition.
* `shellConstant_not_oscillatoryTail` proves that any phase which is
  constant inside each shell fails, even if that shell phase varies
  arbitrarily with complexity. The norm of its shell amplitude is exactly
  the diverging positive shell mass.

Thus the minimal missing P2.4 input is genuine asymptotic intra-shell
balance: at least `ShellAmplitudeVanishes`, and in fact the stronger uniform
contiguous-block control of `OscillatoryTail`. Neither relabeling invariance,
finite-cap pairing, nor a complexity-only phase supplies it.

All limits here concern the complexity cutoff. They are not mesh refinement
and make no geometric-continuum claim. No full-theory flag is changed.

No `sorry`, `admit`, new axiom, or `native_decide`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace ZqShellBalanceBlocker

open ExactShellGaugeUV
open ZqContinuumBlocker

noncomputable section

/-! ## 1. The minimal shell-local necessary premise -/

/-- The shell-local balance condition forced by any uniform oscillatory
tail: individual exact-shell amplitudes tend to zero. This condition is
necessary but does not by itself control accumulation over long blocks. -/
def ShellAmplitudeVanishes
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ‖exactShellAmplitude phase n‖ < ε

/-- A one-shell contiguous block is exactly its shell amplitude. -/
theorem one_shell_block
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Ico n (n + 1), exactShellAmplitude phase k =
      exactShellAmplitude phase n := by
  rw [Finset.sum_Ico_eq_sub (exactShellAmplitude phase) (Nat.le_succ n),
    Finset.sum_range_succ, add_sub_cancel_left]

/-- **NECESSARY BALANCE THEOREM.** Uniform late-block cancellation forces
the individual exact-shell amplitudes to vanish. -/
theorem oscillatoryTail_implies_shellAmplitudeVanishes
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ)
    (htail : OscillatoryTail phase) :
    ShellAmplitudeVanishes phase := by
  intro ε hε
  obtain ⟨N, hN⟩ := htail ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hsmall := hN n (n + 1) hn (Nat.le_succ n)
  rw [one_shell_block] at hsmall
  exact hsmall

/-! ## 2. Finite-cap cancellation cannot imply the tail condition -/

/-- Two exact-shell phases agree from some shell onward. -/
def EventuallyAgrees
    (phase ψ : ∀ n : ℕ, ExactPathClass n → ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ c, phase n c = ψ n c

/-- Exact shell amplitudes agree when all class phases agree on that shell. -/
theorem exactShellAmplitude_congr
    {phase ψ : ∀ n : ℕ, ExactPathClass n → ℝ} {n : ℕ}
    (h : ∀ c, phase n c = ψ n c) :
    exactShellAmplitude phase n = exactShellAmplitude ψ n := by
  unfold exactShellAmplitude
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h c]

/-- One direction of tail transport along eventual phase agreement. -/
theorem oscillatoryTail_of_eventuallyAgrees
    {phase ψ : ∀ n : ℕ, ExactPathClass n → ℝ}
    (hagree : EventuallyAgrees phase ψ)
    (hphase : OscillatoryTail phase) : OscillatoryTail ψ := by
  obtain ⟨N₀, hN₀⟩ := hagree
  intro ε hε
  obtain ⟨N, hN⟩ := hphase ε hε
  refine ⟨max N N₀, fun m n hm hmn => ?_⟩
  have hmN : N ≤ m := le_trans (le_max_left N N₀) hm
  have hmN₀ : N₀ ≤ m := le_trans (le_max_right N N₀) hm
  have heq :
      ∑ k ∈ Finset.Ico m n, exactShellAmplitude ψ k =
        ∑ k ∈ Finset.Ico m n, exactShellAmplitude phase k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hmk : m ≤ k := (Finset.mem_Ico.mp hk).1
    exact (exactShellAmplitude_congr
      (fun c => (hN₀ k (le_trans hmN₀ hmk) c).symm))
  rw [heq]
  exact hN m n hmN hmn

/-- Eventual phase agreement preserves the uniform tail condition. -/
theorem oscillatoryTail_congr_eventually
    {phase ψ : ∀ n : ℕ, ExactPathClass n → ℝ}
    (hagree : EventuallyAgrees phase ψ) :
    OscillatoryTail phase ↔ OscillatoryTail ψ := by
  obtain ⟨N₀, hN₀⟩ := hagree
  constructor
  · exact oscillatoryTail_of_eventuallyAgrees ⟨N₀, hN₀⟩
  · exact oscillatoryTail_of_eventuallyAgrees
      ⟨N₀, fun n hn c => (hN₀ n hn c).symm⟩

/-- A phase which differs from zero only on finitely many shells. This is
the exact abstract shape of any finite-cap phase repair. -/
def EventuallyZeroPhase
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) : Prop :=
  EventuallyAgrees phase zeroPhase

/-- **FINITE-CAP NO-GO.** No phase modification supported on only finitely
many exact shells can satisfy the uniform oscillatory-tail condition. -/
theorem eventuallyZeroPhase_not_oscillatoryTail
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ)
    (hzero : EventuallyZeroPhase phase) :
    ¬ OscillatoryTail phase := by
  intro htail
  have hz : OscillatoryTail zeroPhase :=
    (oscillatoryTail_congr_eventually hzero).mp htail
  exact zeroPhase_not_oscillatoryTail hz

/-- A phase change confined below cap `B` agrees with zero on every shell
at or above `B`. -/
def SupportedBelow
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) (B : ℕ) : Prop :=
  ∀ n : ℕ, B ≤ n → ∀ c, phase n c = 0

/-- A fixed-cap cancellation witness cannot be promoted to a uniform tail
theorem merely by extending it by zero phase beyond the witnessed cap. -/
theorem supportedBelow_not_oscillatoryTail
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) (B : ℕ)
    (hsupp : SupportedBelow phase B) :
    ¬ OscillatoryTail phase :=
  eventuallyZeroPhase_not_oscillatoryTail phase
    ⟨B, fun n hn c => by
      rw [hsupp n hn c]
      rfl⟩

/-! ## 3. Complexity-only phases cannot balance a shell -/

/-- A phase is shell-constant when it does not distinguish classes inside
any exact complexity shell. It may still vary arbitrarily with `n`. -/
def ShellConstant
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) : Prop :=
  ∀ n : ℕ, ∀ c, phase n c = phase n (isolatedClass n)

/-- For a shell-constant phase, the full shell amplitude is its positive
shell mass times one common unit phase. No intra-shell cancellation occurs. -/
theorem exactShellAmplitude_shellConstant
    {phase : ∀ n : ℕ, ExactPathClass n → ℝ}
    (hconst : ShellConstant phase) (n : ℕ) :
    exactShellAmplitude phase n =
      (shellMass n : ℂ) *
        Complex.exp (Complex.I * (phase n (isolatedClass n) : ℂ)) := by
  unfold exactShellAmplitude shellMass
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hconst n c]

/-- The norm of a shell-constant amplitude is exactly the shell mass. -/
theorem norm_exactShellAmplitude_shellConstant
    {phase : ∀ n : ℕ, ExactPathClass n → ℝ}
    (hconst : ShellConstant phase) (n : ℕ) :
    ‖exactShellAmplitude phase n‖ = shellMass n := by
  rw [exactShellAmplitude_shellConstant hconst n, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (shellMass_pos n),
    Complex.norm_exp_I_mul_ofReal, mul_one]

/-- Every shell of complexity at least two has mass strictly above one. -/
theorem one_lt_shellMass_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) < shellMass n := by
  have hpowN : n ≤ n ^ (3 * n) :=
    Nat.le_self_pow (by omega) n
  have hpowR : ((n : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) ^ (3 * n) := by
    calc
      ((n : ℕ) : ℝ) ≤ ((n ^ (3 * n) : ℕ) : ℝ) := by
        exact_mod_cast hpowN
      _ = ((n : ℕ) : ℝ) ^ (3 * n) := Nat.cast_pow n (3 * n)
  have hnR : (1 : ℝ) < (n : ℕ) := by
    exact_mod_cast (show 1 < n by omega)
  have hlower := RegulatorRemovalNoGo.shellMass_lower n
  linarith

/-- A shell-constant phase fails even the weakest shell-local necessary
balance condition. -/
theorem shellConstant_not_shellAmplitudeVanishes
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ)
    (hconst : ShellConstant phase) :
    ¬ ShellAmplitudeVanishes phase := by
  intro hv
  obtain ⟨N, hN⟩ := hv 1 one_pos
  let n : ℕ := max 2 N
  have hnN : N ≤ n := le_max_right 2 N
  have hn2 : 2 ≤ n := le_max_left 2 N
  have hsmall := hN n hnN
  rw [norm_exactShellAmplitude_shellConstant hconst n] at hsmall
  exact (not_lt_of_ge (one_lt_shellMass_of_two_le hn2).le) hsmall

/-- **COMPLEXITY-PHASE NO-GO.** Any phase that only sees shell complexity
fails `OscillatoryTail`, regardless of how its common shell phase varies. -/
theorem shellConstant_not_oscillatoryTail
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ)
    (hconst : ShellConstant phase) :
    ¬ OscillatoryTail phase := by
  intro htail
  exact shellConstant_not_shellAmplitudeVanishes phase hconst
    (oscillatoryTail_implies_shellAmplitudeVanishes phase htail)

/-! ## 4. Certified P2.4 blocker package -/

/-- The certified P2.4 blocker: uniform tails require shell-local
vanishing; finite-shell repairs and complexity-only phases cannot supply it.
The remaining premise is asymptotic intra-shell phase balance from richer
substrate structure. -/
theorem p24_shell_balance_blocker_certificate :
    (∀ phase : ∀ n : ℕ, ExactPathClass n → ℝ,
      OscillatoryTail phase → ShellAmplitudeVanishes phase) ∧
    (∀ phase : ∀ n : ℕ, ExactPathClass n → ℝ,
      EventuallyZeroPhase phase → ¬ OscillatoryTail phase) ∧
    (∀ phase : ∀ n : ℕ, ExactPathClass n → ℝ,
      ShellConstant phase → ¬ OscillatoryTail phase) :=
  ⟨oscillatoryTail_implies_shellAmplitudeVanishes,
    eventuallyZeroPhase_not_oscillatoryTail,
    shellConstant_not_oscillatoryTail⟩

#print axioms oscillatoryTail_implies_shellAmplitudeVanishes
#print axioms eventuallyZeroPhase_not_oscillatoryTail
#print axioms supportedBelow_not_oscillatoryTail
#print axioms shellConstant_not_shellAmplitudeVanishes
#print axioms shellConstant_not_oscillatoryTail
#print axioms p24_shell_balance_blocker_certificate

end

end ZqShellBalanceBlocker
end SevenGaps
end Gravity
end IndisputableMonolith
