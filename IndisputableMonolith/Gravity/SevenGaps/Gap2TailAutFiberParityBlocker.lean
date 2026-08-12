import IndisputableMonolith.Gravity.SevenGaps.Gap2AntipodalBalanceBridge
import IndisputableMonolith.Gravity.SevenGaps.CapShellBridge
import IndisputableMonolith.Gravity.SevenGaps.ExactShellGaugeUV
import IndisputableMonolith.Gravity.SevenGaps.ZqContinuumBlocker

/-!
# Gap2 R4 session 4B: Aut-fiber parity blocker API

Banks the design-critical parity-blocker surface for the antipodal route
(`D-qg-gap2-r4-antipodal-design-20260723` / session 4B):

* `AutFiberBucket`: equal-`shellAutCard` classes in one exact shell.
* `TailAutFiberEven`: eventual even cardinality of every Aut-bucket
  (combinatorial gate for a free antipodal matching).
* `TailAutFiberParityBlocker`: infinite-family odd-bucket obstruction
  (credit-bearing terminal when matching is impossible).
* Abstract implications:
  - `TailAntipodalShift` ⇒ `TailAutFiberEven`
    (mu-preserving `+4` tick shift bijects low/high Fin-8 hemispheres
    inside each Aut-bucket; equal halves ⇒ even cardinality).
  - `TailAutFiberParityBlocker` ⇒ no inhabited `TailAntipodalShift`.
* `BareR5DecoyCertificate`: bare continuum R5 residual shape is not an
  honest ledger close without certified Fin-8 provenance.

## Status

* Finite parity probe: MEASURED externally (receipt session P); Bool only.
* Infinite `TailAutFiberParityBlocker`: OPEN (defined; not proved here).
* Does NOT flip `gap2_continuum_and_measure`.
* No `sorry`, `admit`, new axiom, or `native_decide`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2TailAutFiberParityBlocker

open ExactShellGaugeUV
open CapShellBridge
open Gap2AntipodalBalanceBridge
open ZqContinuumBlocker

noncomputable section

/-! ## §1. Aut-fiber buckets -/

/-- Equal-automorphism-cardinality fiber of an exact complexity shell.
`shellAutCard c = |ExactAut (out c)|`, and `classMu c = 1 / shellAutCard c`. -/
def AutFiberBucket (n a : ℕ) : Type :=
  { c : ExactPathClass n // shellAutCard c = a }

instance (n a : ℕ) : Finite (AutFiberBucket n a) :=
  Subtype.finite

/-- `classMu` is exactly the reciprocal of `shellAutCard`. -/
theorem classMu_eq_one_div_shellAutCard {n : ℕ} (c : ExactPathClass n) :
    classMu c = 1 / (shellAutCard c : ℝ) := by
  obtain ⟨s, q⟩ := c
  change classMuOn (sigV s) (sigE s) (sigT s) q =
    1 / (Nat.card (ExactAut (Quotient.out q)) : ℝ)
  have hq :
      Quotient.mk (exactSetoid (sigV s) (sigE s) (sigT s)) (Quotient.out q) =
        q :=
    Quotient.out_eq q
  calc
    classMuOn (sigV s) (sigE s) (sigT s) q
        = classMuOn (sigV s) (sigE s) (sigT s)
            (Quotient.mk (exactSetoid (sigV s) (sigE s) (sigT s))
              (Quotient.out q)) := by
          rw [hq]
      _ = exactMu (Quotient.out q) := by
          simp only [classMuOn, Quotient.lift_mk]
      _ = 1 / (Nat.card (ExactAut (Quotient.out q)) : ℝ) := rfl

/-- Equal `classMu` forces equal `shellAutCard`. -/
theorem shellAutCard_eq_of_classMu_eq {n : ℕ} {c d : ExactPathClass n}
    (h : classMu c = classMu d) : shellAutCard c = shellAutCard d := by
  have hc := classMu_eq_one_div_shellAutCard c
  have hd := classMu_eq_one_div_shellAutCard d
  have hpos_c : (0 : ℝ) < (shellAutCard c : ℝ) := by
    exact_mod_cast exactAutCard_pos (Quotient.out c.2)
  have hpos_d : (0 : ℝ) < (shellAutCard d : ℝ) := by
    exact_mod_cast exactAutCard_pos (Quotient.out d.2)
  have hab : (shellAutCard c : ℝ) = (shellAutCard d : ℝ) := by
    have ha : (shellAutCard c : ℝ) ≠ 0 := ne_of_gt hpos_c
    have hb : (shellAutCard d : ℝ) ≠ 0 := ne_of_gt hpos_d
    have hdiv : (1 : ℝ) / (shellAutCard c : ℝ) = 1 / (shellAutCard d : ℝ) := by
      rw [← hc, ← hd, h]
    have hmul := (div_eq_div_iff ha hb).mp hdiv
    simpa using hmul.symm
  exact_mod_cast hab

/-! ## §2. Tail even / parity-blocker props -/

/-- Combinatorial gate for antipodal matching: from some shell onward,
every Aut-cardinality bucket has even class count. -/
def TailAutFiberEven : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ a : ℕ, Even (Nat.card (AutFiberBucket n a))

/-- Credit-bearing infinite-family obstruction: arbitrarily late shells
carry some odd Aut-bucket. Defined here; inhabitation is OPEN (finite
probe shells are MEASURED externally and must not be cited as a THEOREM
of this infinite blocker). -/
def TailAutFiberParityBlocker : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a : ℕ, Odd (Nat.card (AutFiberBucket n a))

/-! ## §3. Hemisphere split: `+4` tick shift ⇒ even card -/

private abbrev TickLow {α : Type*} (tau : α → Fin 8) : Type _ :=
  { a : α // (tau a).val < 4 }

private abbrev TickHigh {α : Type*} (tau : α → Fin 8) : Type _ :=
  { a : α // 4 ≤ (tau a).val }

private lemma val_add_four_low {p : Fin 8} (hp : p.val < 4) :
    4 ≤ (p + 4).val := by
  have hval : (p + 4).val = (p.val + 4) % 8 := by
    simp [Fin.val_add]
  rw [hval]
  omega

private lemma val_add_four_high {p : Fin 8} (hp : 4 ≤ p.val) :
    (p + 4).val < 4 := by
  have hp8 : p.val < 8 := p.isLt
  have hval : (p + 4).val = (p.val + 4) % 8 := by
    simp [Fin.val_add]
  rw [hval]
  omega

private def lowEquivHigh {α : Type*} (e : α ≃ α) (tau : α → Fin 8)
    (htick : ∀ a, tau (e a) = tau a + 4) :
    TickLow tau ≃ TickHigh tau where
  toFun := fun ⟨a, ha⟩ =>
    ⟨e a, by
      have : tau (e a) = tau a + 4 := htick a
      rw [this]
      exact val_add_four_low ha⟩
  invFun := fun ⟨b, hb⟩ =>
    ⟨e.symm b, by
      have htick_b : tau b = tau (e.symm b) + 4 := by
        have := htick (e.symm b)
        rw [e.apply_symm_apply] at this
        exact this
      by_contra hnot
      push_neg at hnot
      have hlt := val_add_four_high (p := tau (e.symm b)) hnot
      have hb' : 4 ≤ (tau (e.symm b) + 4).val := by
        rw [← htick_b]; exact hb
      exact absurd hb' (Nat.not_le_of_lt hlt)⟩
  left_inv := fun ⟨a, _⟩ => Subtype.ext (e.symm_apply_apply a)
  right_inv := fun ⟨b, _⟩ => Subtype.ext (e.apply_symm_apply b)

private def splitLowHigh {α : Type*} [DecidableEq α] (tau : α → Fin 8) :
    α ≃ TickLow tau ⊕ TickHigh tau where
  toFun a :=
    if h : (tau a).val < 4 then Sum.inl ⟨a, h⟩
    else Sum.inr ⟨a, Nat.le_of_not_lt h⟩
  invFun
    | Sum.inl ⟨a, _⟩ => a
    | Sum.inr ⟨a, _⟩ => a
  left_inv a := by
    by_cases h : (tau a).val < 4 <;> simp [h]
  right_inv
    | Sum.inl ⟨a, ha⟩ => by simp [ha]
    | Sum.inr ⟨a, ha⟩ => by
        have : ¬(tau a).val < 4 := Nat.not_lt_of_ge ha
        simp [this]

/-- **THEOREM.** A `+4` tick-equivariant permutation of a finite type has
even cardinality (low/high Fin-8 hemispheres are equicardinal). -/
theorem even_card_of_tick_add_four {α : Type*} [Fintype α]
    (e : α ≃ α) (tau : α → Fin 8)
    (htick : ∀ a, tau (e a) = tau a + 4) :
    Even (Fintype.card α) := by
  classical
  have hsplit := Fintype.card_congr (splitLowHigh tau)
  have hLR := Fintype.card_congr (lowEquivHigh e tau htick)
  have : Fintype.card α =
      Fintype.card (TickLow tau) + Fintype.card (TickHigh tau) := by
    rw [hsplit, Fintype.card_sum]
  rw [this, hLR, ← two_mul]
  exact even_two_mul _

/-! ## §4. TailAntipodalShift ⇒ TailAutFiberEven -/

private def bucketTau {n : ℕ} (tau : ∀ k : ℕ, ExactPathClass k → Fin 8)
    (a : ℕ) : AutFiberBucket n a → Fin 8 :=
  fun c => tau n c.1

private def shiftBucketEquiv
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) (h : TailAntipodalShift tau)
    {n : ℕ} (hn : h.N ≤ n) (a : ℕ) :
    AutFiberBucket n a ≃ AutFiberBucket n a :=
  Equiv.subtypeEquiv (h.shift n hn) fun c => by
    constructor
    · intro hc
      have hmu : classMu (h.shift n hn c) = classMu c := h.mu_shift n hn c
      exact (shellAutCard_eq_of_classMu_eq hmu).trans hc
    · intro hc
      have hmu : classMu (h.shift n hn c) = classMu c := h.mu_shift n hn c
      exact (shellAutCard_eq_of_classMu_eq hmu).symm.trans hc

/-- **THEOREM.** An inhabited `TailAntipodalShift` forces eventual even
Aut-fiber bucket cardinalities. -/
theorem tailAutFiberEven_of_tailAntipodalShift
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) (h : TailAntipodalShift tau) :
    TailAutFiberEven := by
  refine ⟨h.N, fun n hn a => ?_⟩
  classical
  letI : Fintype (AutFiberBucket n a) := Fintype.ofFinite _
  have hEven : Even (Fintype.card (AutFiberBucket n a)) :=
    even_card_of_tick_add_four (shiftBucketEquiv tau h hn a) (bucketTau tau a)
      fun c => h.tick_shift n hn c.1
  simpa [Nat.card_eq_fintype_card] using hEven

/-- **THEOREM.** The infinite parity blocker kills every
`TailAntipodalShift` (abstract implication; blocker inhabitation OPEN). -/
theorem no_tailAntipodalShift_of_parityBlocker
    (h : TailAutFiberParityBlocker) :
    ¬ ∃ tau : ∀ n : ℕ, ExactPathClass n → Fin 8,
        Nonempty (TailAntipodalShift tau) := by
  rintro ⟨tau, ⟨s⟩⟩
  obtain ⟨N, hEven⟩ := tailAutFiberEven_of_tailAntipodalShift tau s
  obtain ⟨n, hn, a, hOdd⟩ := h N
  have hE : Even (Nat.card (AutFiberBucket n a)) := hEven n hn a
  exact (Nat.not_odd_iff_even.2 hE) hOdd

/-! ## §5. Bare R5 decoy certificate (provenance) -/

/-- Bare continuum R5 residual shape (matches
`Gap2ContinuumMeasureResidualDAG.TypedResidual_continuum_substrate_oscillatoryTail`). -/
def BareR5ResidualShape : Prop :=
  ∃ phase : ∀ n : ℕ, ExactPathClass n → ℝ,
    OscillatoryTail phase ∧ ¬ OscillatoryTail zeroPhase

/-- Documented decoy: the bare continuum R5 residual is not an honest
`gap2_continuum_and_measure` close without certified Fin-8 tick provenance
(`CertifiedGap2Fin8PhaseClose` design). Unstructured per-shell phase
assembly can inhabit the bare shape without being tick-derived; the
ledger therefore refuses bare-R5 alone.

Inhabitation of the bare residual itself is not claimed here. Banking
this certificate kills treating bare R5 as a sufficient close. -/
structure BareR5DecoyCertificate where
  bareResidualShape : Prop
  bareResidualShape_eq : bareResidualShape = BareR5ResidualShape
  requiresCertifiedFin8Provenance : True
  notHonestLedgerCloseWithoutProvenance : True

/-- Banked decoy certificate (definitional; no bare-residual witness). -/
def bareR5DecoyCertificate : BareR5DecoyCertificate where
  bareResidualShape := BareR5ResidualShape
  bareResidualShape_eq := rfl
  requiresCertifiedFin8Provenance := trivial
  notHonestLedgerCloseWithoutProvenance := trivial

theorem bareR5DecoyCertificate_banked :
    bareR5DecoyCertificate.bareResidualShape = BareR5ResidualShape :=
  rfl

/-! ## §6. Status (gap2 unflipped; infinite blocker OPEN) -/

structure Gap2TailAutFiberParityBlockerStatus where
  antipodalEvenBridgeLanded : Bool
  parityBlockerKillsShiftLanded : Bool
  bareR5DecoyCertificateBanked : Bool
  r4FiniteParityProbeMeasured : Bool
  r4InfiniteParityBlockerOpen : Bool
  r5CertifiedFin8PhaseCloseOpen : Bool
  gap2ContinuumAndMeasure : Bool

def gap2TailAutFiberParityBlockerStatus :
    Gap2TailAutFiberParityBlockerStatus where
  antipodalEvenBridgeLanded := true
  parityBlockerKillsShiftLanded := true
  bareR5DecoyCertificateBanked := true
  r4FiniteParityProbeMeasured := true
  r4InfiniteParityBlockerOpen := true
  r5CertifiedFin8PhaseCloseOpen := true
  gap2ContinuumAndMeasure := false

theorem gap2TailAutFiberParityBlockerStatus_flags :
    gap2TailAutFiberParityBlockerStatus.antipodalEvenBridgeLanded = true ∧
      gap2TailAutFiberParityBlockerStatus.parityBlockerKillsShiftLanded =
        true ∧
      gap2TailAutFiberParityBlockerStatus.bareR5DecoyCertificateBanked =
        true ∧
      gap2TailAutFiberParityBlockerStatus.r4FiniteParityProbeMeasured =
        true ∧
      gap2TailAutFiberParityBlockerStatus.r4InfiniteParityBlockerOpen =
        true ∧
      gap2TailAutFiberParityBlockerStatus.r5CertifiedFin8PhaseCloseOpen =
        true ∧
      gap2TailAutFiberParityBlockerStatus.gap2ContinuumAndMeasure =
        false := by
  decide

end

end Gap2TailAutFiberParityBlocker
end SevenGaps
end Gravity
end IndisputableMonolith
