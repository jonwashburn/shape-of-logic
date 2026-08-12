import IndisputableMonolith.Gravity.SevenGaps.Gap2TailFiberShiftBridge

/-!
# Gap2 R4: antipodal mass-balance bridge (sufficiency half)

Banks the mechanical sufficiency half of the antipodal weakening
(design `D-qg-gap2-r4-antipodal-design-20260723` /
`plans/QG_Gap2_R4_Antipodal_Design_20260723.html`):

* `EventuallyTickFiberAntipodalMassBalanced`: equal `classMu` mass on
  opposite Fin-8 fibers `p` and `p+4` from some shell onward.
* Antipodal balance kills late shell amplitudes by pairwise cancellation
  (`tickRoot (p+4) = -tickRoot p`), with no rational-independence argument.
* Hence `OscillatoryTail` on the tick-derived phase (mirror of the full
  eventual-balance bridge in `Gap2TickPhaseTailBlocker`).
* `TailAntipodalShift`: mu-preserving tail automorphisms rotating tick
  by `+4`; implies antipodal balance (mirror of `TailFiberShift`).
* Weakening chain: `TailFiberShift → TailAntipodalShift` (compose `+1`
  four times) and full eventual balance → antipodal balance.

## Status

R4 stays OPEN (`TailAntipodalShift` uninhabited). Does NOT flip
`gap2_continuum_and_measure`. The converse (vanishing forces antipodal
balance via Q-independence of `1` and `√2` on rational masses) is
deliberately deferred. No `sorry`, `admit`, new axiom, or `native_decide`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2AntipodalBalanceBridge

open ExactShellGaugeUV
open ZqContinuumBlocker
open Gap2TickPhaseSubstrate
open Gap2TickPhaseTailBlocker
open Gap2TailFiberShiftBridge

noncomputable section

/-! ## §1. Antipodal eventual mass balance -/

/-- Honest weakening of eventual full Fin-8 balance: opposite fibers
`p` and `p+4` carry equal `classMu` mass from some shell onward. -/
def EventuallyTickFiberAntipodalMassBalanced
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ p : Fin 8, tickFiberMass tau n p = tickFiberMass tau n (p + 4)

/-- Full eventual balance specializes to antipodal balance. -/
theorem eventuallyTickFiberMassBalanced_implies_antipodal
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8)
    (hbal : EventuallyTickFiberMassBalanced tau) :
    EventuallyTickFiberAntipodalMassBalanced tau := by
  obtain ⟨N, hN⟩ := hbal
  refine ⟨N, fun n hn p => hN n hn p (p + 4)⟩

/-! ## §2. Root arithmetic: `tickRoot (p+4) = -tickRoot p` -/

private lemma exp_two_pi_I_mul_nat (q : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (q : ℂ)) = 1 := by
  -- In this Mathlib pin: `exp_nat_mul z q : exp (↑q * z) = exp z ^ q`.
  have hpow :
      Complex.exp ((q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I) ^ q :=
    Complex.exp_nat_mul (2 * (Real.pi : ℂ) * Complex.I) q
  have hcomm :
      (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * Complex.I * (q : ℂ) := by
    ring
  calc
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (q : ℂ))
        = Complex.exp ((q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
          rw [hcomm]
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I) ^ q := hpow
      _ = (1 : ℂ) ^ q := by rw [Complex.exp_two_pi_mul_I]
      _ = 1 := one_pow q

private lemma exp_eighth_period (n : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / 8) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n % 8 : ℕ) : ℂ) / 8) := by
  have hn : n = 8 * (n / 8) + n % 8 := (Nat.div_add_mod n 8).symm
  have harg :
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / 8) =
        2 * (Real.pi : ℂ) * Complex.I * ((n / 8 : ℕ) : ℂ) +
          2 * (Real.pi : ℂ) * Complex.I * ((n % 8 : ℕ) : ℂ) / 8 := by
    have hnC : (n : ℂ) = ((8 * (n / 8) + n % 8 : ℕ) : ℂ) := by
      exact congrArg Nat.cast hn
    rw [hnC]
    push_cast
    ring
  calc
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / 8)
        = Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * ((n / 8 : ℕ) : ℂ) +
              2 * (Real.pi : ℂ) * Complex.I * ((n % 8 : ℕ) : ℂ) / 8) := by
          rw [harg]
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n / 8 : ℕ) : ℂ)) *
            Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * ((n % 8 : ℕ) : ℂ) / 8) :=
          Complex.exp_add _ _
      _ = 1 *
            Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * ((n % 8 : ℕ) : ℂ) / 8) := by
          rw [exp_two_pi_I_mul_nat]
      _ = Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * ((n % 8 : ℕ) : ℂ) / 8) := by
          ring

/-- Opposite 8th-root characters negate: `ω^{p+4} = -ω^p`. -/
theorem tickRoot_add_four (p : Fin 8) : tickRoot (p + 4) = -tickRoot p := by
  unfold tickRoot
  have hval : ((p + 4 : Fin 8) : ℕ) = (p.val + 4) % 8 := by
    rw [Fin.val_add]
    rfl
  rw [hval, ← exp_eighth_period (p.val + 4)]
  have hsplit :
      Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * ((p.val + 4 : ℕ) : ℂ) / 8) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (p.val : ℂ) / 8) *
          Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit, Complex.exp_pi_mul_I, mul_neg_one]

/-! ## §3. Antipodal balance ⇒ vanishing shell amplitudes -/

private lemma antipodal_pair_term_eq_zero
    (m : Fin 8 → ℝ) (p : Fin 8)
    (hm : m p = m (p + 4)) :
    (m p : ℂ) * tickRoot p + (m (p + 4) : ℂ) * tickRoot (p + 4) = 0 := by
  rw [hm, tickRoot_add_four]
  ring

private lemma sum_fin8_antipodal_cancel (f : Fin 8 → ℂ)
    (h : ∀ p : Fin 8, f p + f (p + 4) = 0) :
    ∑ p : Fin 8, f p = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have e0 : (0 : Fin 8) + 4 = 4 := rfl
  have e1 : (1 : Fin 8) + 4 = 5 := rfl
  have e2 : (2 : Fin 8) + 4 = 6 := rfl
  have e3 : (3 : Fin 8) + 4 = 7 := rfl
  simp only [Fin.sum_univ_eight, e0, e1, e2, e3] at h0 h1 h2 h3 ⊢
  linear_combination h0 + h1 + h2 + h3

/-- **THEOREM.** Antipodal fiber-mass balance at shell `n` forces
`exactShellAmplitude (tickDerivedPhase tau) n = 0` by four opposite-root
cancellations. No Q-independence. -/
theorem exactShellAmplitude_eq_zero_of_antipodalBalanced_at
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) (n : ℕ)
    (hbal : ∀ p : Fin 8, tickFiberMass tau n p = tickFiberMass tau n (p + 4)) :
    exactShellAmplitude (tickDerivedPhase tau) n = 0 := by
  rw [exactShellAmplitude_tick_fiberwise]
  refine sum_fin8_antipodal_cancel
    (fun p => (tickFiberMass tau n p : ℂ) * tickRoot p) fun p => ?_
  simpa using antipodal_pair_term_eq_zero (tickFiberMass tau n) p (hbal p)

private theorem sum_amp_eq_zero_of_amps_zero
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ)
    {s : Finset ℕ}
    (h : ∀ k ∈ s, exactShellAmplitude phase k = 0) :
    ∑ k ∈ s, exactShellAmplitude phase k = 0 :=
  Finset.sum_eq_zero h

/-- **THEOREM.** Eventual antipodal balance ⇒ `OscillatoryTail` on the
tick-derived phase (finite head irrelevant). -/
theorem eventuallyAntipodalBalanced_implies_oscillatoryTail
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8)
    (hbal : EventuallyTickFiberAntipodalMassBalanced tau) :
    OscillatoryTail (tickDerivedPhase tau) := by
  obtain ⟨N, hN⟩ := hbal
  intro ε hε
  refine ⟨N, fun m n hm _hmn => ?_⟩
  have hamp :
      ∀ k ∈ Finset.Ico m n,
        exactShellAmplitude (tickDerivedPhase tau) k = 0 := by
    intro k hk
    have hkN : N ≤ k := le_trans hm (Finset.mem_Ico.mp hk).1
    exact exactShellAmplitude_eq_zero_of_antipodalBalanced_at tau k (hN k hkN)
  rw [sum_amp_eq_zero_of_amps_zero _ hamp, norm_zero]
  exact hε

/-! ## §4. Conditional structure: `TailAntipodalShift` -/

/-- **CONDITIONAL hyp.** From some shell `N` onward, a family of
exact-path-class automorphisms that rotate the tick by `+4` and preserve
`classMu`. Same shape as `TailFiberShift` with antipodal step. Not
inhabited in this module. -/
structure TailAntipodalShift (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) where
  N : ℕ
  shift : ∀ n : ℕ, N ≤ n → ExactPathClass n ≃ ExactPathClass n
  tick_shift :
    ∀ n : ℕ, ∀ hn : N ≤ n, ∀ c : ExactPathClass n,
      tau n (shift n hn c) = tau n c + 4
  mu_shift :
    ∀ n : ℕ, ∀ hn : N ≤ n, ∀ c : ExactPathClass n,
      classMu (shift n hn c) = classMu c

/-- The antipodal shift restricts to a `classMu`-preserving bijection of
tick fibers `p → p+4`. -/
theorem tickFiberMass_add_four_of_tailAntipodalShift
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) (h : TailAntipodalShift tau)
    {n : ℕ} (hn : h.N ≤ n) (p : Fin 8) :
    tickFiberMass tau n p = tickFiberMass tau n (p + 4) := by
  classical
  let e := h.shift n hn
  have hmap :
      (tickFiber tau n p).map e.toEmbedding = tickFiber tau n (p + 4) := by
    ext d
    simp only [tickFiber, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [h.tick_shift n hn c, hc]
    · intro hd
      refine ⟨e.symm d, ?_, e.apply_symm_apply d⟩
      have htick := h.tick_shift n hn (e.symm d)
      rw [e.apply_symm_apply] at htick
      have : tau n (e.symm d) + 4 = p + 4 := htick.symm.trans hd
      exact add_right_cancel this
  unfold tickFiberMass
  rw [← hmap, Finset.sum_map]
  refine Finset.sum_congr rfl fun c _ => (h.mu_shift n hn c).symm

/-- **BRIDGE.** A `TailAntipodalShift` forces eventual antipodal
fiber-mass balance. -/
theorem eventuallyTickFiberAntipodalMassBalanced_of_tailAntipodalShift
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) (h : TailAntipodalShift tau) :
    EventuallyTickFiberAntipodalMassBalanced tau := by
  refine ⟨h.N, fun n hn p =>
    tickFiberMass_add_four_of_tailAntipodalShift tau h hn p⟩

/-- Abstract composition: antipodal shift ⇒ `OscillatoryTail`. -/
theorem oscillatoryTail_of_tailAntipodalShift
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) (h : TailAntipodalShift tau) :
    OscillatoryTail (tickDerivedPhase tau) :=
  eventuallyAntipodalBalanced_implies_oscillatoryTail tau
    (eventuallyTickFiberAntipodalMassBalanced_of_tailAntipodalShift tau h)

/-! ## §5. Old target is strictly stronger: compose `+1` four times -/

private def equivIterate4 {α : Type*} (e : α ≃ α) : α ≃ α :=
  e.trans (e.trans (e.trans e))

private lemma tick_shift_four
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8)
    {n : ℕ} (e : ExactPathClass n ≃ ExactPathClass n)
    (htick : ∀ c : ExactPathClass n, tau n (e c) = tau n c + 1)
    (c : ExactPathClass n) :
    tau n (equivIterate4 e c) = tau n c + 4 := by
  have h1 : tau n (e c) = tau n c + 1 := htick c
  have h2 : tau n (e (e c)) = tau n (e c) + 1 := htick (e c)
  have h3 : tau n (e (e (e c))) = tau n (e (e c)) + 1 := htick (e (e c))
  have h4 : tau n (e (e (e (e c)))) = tau n (e (e (e c))) + 1 :=
    htick (e (e (e c)))
  change tau n (e (e (e (e c)))) = tau n c + 4
  calc tau n (e (e (e (e c))))
      = tau n (e (e (e c))) + 1 := h4
    _ = tau n (e (e c)) + 1 + 1 := by rw [h3]
    _ = tau n (e c) + 1 + 1 + 1 := by rw [h2]
    _ = tau n c + 1 + 1 + 1 + 1 := by rw [h1]
    _ = tau n c + 4 := by
        ext
        simp only [Fin.val_add]
        omega

private lemma mu_shift_four
    {n : ℕ} (e : ExactPathClass n ≃ ExactPathClass n)
    (hmu : ∀ c : ExactPathClass n, classMu (e c) = classMu c)
    (c : ExactPathClass n) :
    classMu (equivIterate4 e c) = classMu c := by
  change classMu (e (e (e (e c)))) = classMu c
  simp only [hmu]

/-- **THEOREM.** The old `+1` free-action target is strictly stronger:
four compositions yield an antipodal `+4` shift. -/
theorem nonempty_tailAntipodalShift_of_tailFiberShift
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) (h : TailFiberShift tau) :
    Nonempty (TailAntipodalShift tau) := by
  refine ⟨{
    N := h.N
    shift := fun n hn => equivIterate4 (h.shift n hn)
    tick_shift := fun n hn c =>
      tick_shift_four tau (h.shift n hn) (h.tick_shift n hn) c
    mu_shift := fun n hn c =>
      mu_shift_four (h.shift n hn) (h.mu_shift n hn) c
  }⟩

/-! ## §6. Status (R4 open; gap2 unflipped) -/

structure Gap2AntipodalBalanceBridgeStatus where
  antipodalAmplitudeBridgeLanded : Bool
  antipodalOscillatoryTailBridgeLanded : Bool
  tailAntipodalShiftBridgeLanded : Bool
  fiberShiftImpliesAntipodalLanded : Bool
  fullBalanceImpliesAntipodalLanded : Bool
  tailAntipodalShiftInhabited : Bool
  r4ResidualOpen : Bool
  gap2ContinuumAndMeasure : Bool

def gap2AntipodalBalanceBridgeStatus : Gap2AntipodalBalanceBridgeStatus where
  antipodalAmplitudeBridgeLanded := true
  antipodalOscillatoryTailBridgeLanded := true
  tailAntipodalShiftBridgeLanded := true
  fiberShiftImpliesAntipodalLanded := true
  fullBalanceImpliesAntipodalLanded := true
  tailAntipodalShiftInhabited := false
  r4ResidualOpen := true
  gap2ContinuumAndMeasure := false

theorem gap2AntipodalBalanceBridgeStatus_flags :
    gap2AntipodalBalanceBridgeStatus.antipodalAmplitudeBridgeLanded = true ∧
      gap2AntipodalBalanceBridgeStatus.antipodalOscillatoryTailBridgeLanded =
        true ∧
      gap2AntipodalBalanceBridgeStatus.tailAntipodalShiftBridgeLanded = true ∧
      gap2AntipodalBalanceBridgeStatus.fiberShiftImpliesAntipodalLanded =
        true ∧
      gap2AntipodalBalanceBridgeStatus.fullBalanceImpliesAntipodalLanded =
        true ∧
      gap2AntipodalBalanceBridgeStatus.tailAntipodalShiftInhabited = false ∧
      gap2AntipodalBalanceBridgeStatus.r4ResidualOpen = true ∧
      gap2AntipodalBalanceBridgeStatus.gap2ContinuumAndMeasure = false := by
  decide

end

end Gap2AntipodalBalanceBridge
end SevenGaps
end Gravity
end IndisputableMonolith
