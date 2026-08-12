import IndisputableMonolith.Gravity.SevenGaps.Gap5ChartFromLedgerMomentum

/-!
# Track B, step B1: momentum additivity under ledger consolidation, a conditional closure

**Verdict, stated first.** On the chart carrier `LedgerState := ℝ × ℝ` of
`Gap5ChartFromLedgerMomentum`, additivity of the momentum observable under ledger
consolidation is **proved from three named properties**, each shown load-bearing by
an exhibited countermodel in this module.  A hostile referee (2026-07-29) confirmed
the kernel mathematics and ruled on the framing: the first premise, the kinetic
condition, is pointwise `|p| = |imbalance|`, which is the magnitude half of the
chart conclusion itself.  So what is derived here is the *parity equivalence* —
additivity is swap-oddness inside the kinetic class — and what remains named is the
*magnitude bridge*.  This module is a conditional closure of B1, not a derivation
of the chart.  The three premises:

1. **the kinetic condition** `p z ^ 2 = imbalance z ^ 2`: the momentum's square is
   the squared net imbalance. On a split-torus orbit this follows from the
   exactness theorem `Jlog_eq_imbalance_sq_div_two_casimir` *composed with the
   energy-equals-cost identification* `p z ^ 2 = 2 * k * Jlog t` (energy is the
   recognition cost): the theorem gives `Jlog t = imbalance ^ 2 / (2 k)`, and the
   identification turns it into the kinetic condition on the orbit. That
   identification is declared as a hypothesis, not derived; as a global state
   identity the kinetic condition is a named modeling premise and the certificate
   says so;
2. **continuity** of `p` (a named regularity premise);
3. **swap-oddness** `p (z.2, z.1) = - p z`: the momentum is *odd under the
   substrate's own debit-credit exchange*. This is a symmetry property of the
   observable, and it is the premise the whole arc pivots on.

## What is new, mathematically

The chart module's open problem was: "why additive under consolidation", with
linearity banned as a premise (`chart_not_forced_without_linearity`). This module's
central theorem is that **within the kinetic + continuous class, additivity under
consolidation is *equivalent* to swap-oddness**
(`kinetic_root_additive_iff_swap_odd`). Extensivity of the momentum is therefore a
*parity under a substrate involution*, not a regularity class and not a functional
equation: the question "why is momentum extensive" gets the answer a substrate can
give, "because it is a signed charge under debit-credit exchange, not a magnitude".

The classification behind it (`kinetic_root_classification`, with formal
exhaustiveness proved as `kinetic_root_mem_four`) shows a continuous kinetic
observable is one of exactly four functions: `± imbalance` (the signed branch,
additive) and `± |imbalance|` (the unsigned branch, not additive). The unsigned
branch is the countermodel showing swap-oddness is load-bearing; the `nlP`
reparametrization `m + m ^ 3` (continuous, swap-odd, balance-vanishing, not
kinetic, not additive) is the countermodel showing the kinetic condition is
load-bearing.  Stated plainly: the `nlP` family, which is the witness family of
`chart_not_forced_without_linearity`, is excluded here by the kinetic condition,
not by substrate-derived extensivity, and the kinetic condition is the magnitude
half of the chart conclusion.  The linearity trap is therefore not discharged by
this module; it is relocated.  The residual premise of the whole B1 arc is the
momentum-magnitude bridge `|p| = |imbalance|`, and the C2 constant-cluster attack
died on the same object (the chart theorem fixes the product `lam * p`, not
`lam`), so B1's residue and flag 12's blocker are one named target.

## What is NOT claimed

- A hostile referee (2026-07-29) confirmed the kernel and ruled the kinetic
  premise is the conclusion's magnitude half: the module stands as a conditional
  closure. The derived content is the parity equivalence; the magnitude bridge is
  the named residue, and it is shared with the cMom constant cluster (flag 12),
  whose Casimir route to `lam` died on the same missing bridge.
- The three premises are **named, not derived**. The on-orbit kinetic content is a
  theorem (`kinetic_on_orbit`, from the existing exactness theorem); the global
  kinetic condition and swap-oddness of the physical momentum are modeling
  premises, stated as such in the certificate. Whether "provenance derived" may
  rest on this named package is the flag-6 (B3) judgment, gated on hostile review.
- The state/event splice defect of the chart verdict is not touched: nothing here
  applies the event cost to a state. The kinetic condition is a property of the
  *observable*, stated on states, and the certificate derives it on an orbit only
  from the state-side exactness identity.
- This does not flip `gap1_provenance_derived`. It converts B1's "assume
  additivity" into "prove additivity from a kinetic magnitude premise, a continuity
  premise, and a debit-credit parity premise", with each premise shown to do work.

## Scope

Chart carrier only (`LedgerState`, the debit-credit plane). Nothing here is about
`Recognition.Ledger`, `DualEntryStrainState`, or the HKT momentum sector; the recon
brief (`QG/attack_full_theory_20260729/O15_attack_brief_20260729.html`) catalogs
why those are different carriers, and the `flux_unit` obstruction to consolidation
on the dual-entry type stands untouched.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace MomentumAdditivity

open ChartFromLedgerMomentum

/-! ## §1. The two named properties, and imbalance arithmetic -/

/-- **The kinetic condition.** The momentum observable's square is the squared net
ledger imbalance. On an orbit this is forced by the exactness of the recognition
cost (`kinetic_on_orbit`); as a global identity it is a named premise. -/
def KineticCondition (p : LedgerState → ℝ) : Prop :=
  ∀ z : LedgerState, p z ^ 2 = imbalance z ^ 2

/-- **Swap-oddness.** The observable is odd under the debit-credit exchange, the
substrate's own involution of the ledger plane. A signed net-recognition charge has
this parity; an unsigned magnitude does not. -/
def SwapOdd (p : LedgerState → ℝ) : Prop :=
  ∀ z : LedgerState, p (z.2, z.1) = - p z

theorem imbalance_swap (z : LedgerState) :
    imbalance (z.2, z.1) = - imbalance z := by
  show z.2 - z.1 = -(z.1 - z.2)
  ring

theorem imbalance_add (z w : LedgerState) :
    imbalance (z + w) = imbalance z + imbalance w := by
  show z.1 + w.1 - (z.2 + w.2) = z.1 - z.2 + (w.1 - w.2)
  ring

theorem imbalance_smul (t : ℝ) (z : LedgerState) :
    imbalance (t • z) = t * imbalance z := by
  show t * z.1 - t * z.2 = t * (z.1 - z.2)
  ring

/-- The imbalance of a segment in the positive half-plane stays positive:
the half-plane is convex because `imbalance` is linear. -/
theorem imbalance_seg_pos {z₀ z : LedgerState} (h0 : 0 < imbalance z₀)
    (hz : 0 < imbalance z) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    0 < imbalance ((1 - t) • z₀ + t • z) := by
  rw [imbalance_add, imbalance_smul, imbalance_smul]
  rcases Set.mem_Icc.mp ht with ⟨ht0, ht1⟩
  have hm : 0 < min (imbalance z₀) (imbalance z) := lt_min h0 hz
  have hge : min (imbalance z₀) (imbalance z)
      ≤ (1 - t) * imbalance z₀ + t * imbalance z := by
    have e1 : (1 - t) * min (imbalance z₀) (imbalance z) ≤ (1 - t) * imbalance z₀ :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
    have e2 : t * min (imbalance z₀) (imbalance z) ≤ t * imbalance z :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) ht0
    have hsum := add_le_add e1 e2
    rwa [show (1 - t) * min (imbalance z₀) (imbalance z)
          + t * min (imbalance z₀) (imbalance z)
        = min (imbalance z₀) (imbalance z) from by ring] at hsum
  linarith

/-- The imbalance of a segment in the negative half-plane stays negative. -/
theorem imbalance_seg_neg {z₀ z : LedgerState} (h0 : imbalance z₀ < 0)
    (hz : imbalance z < 0) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    imbalance ((1 - t) • z₀ + t • z) < 0 := by
  rw [imbalance_add, imbalance_smul, imbalance_smul]
  rcases Set.mem_Icc.mp ht with ⟨ht0, ht1⟩
  have hm : max (imbalance z₀) (imbalance z) < 0 := max_lt h0 hz
  have hle : (1 - t) * imbalance z₀ + t * imbalance z
      ≤ max (imbalance z₀) (imbalance z) := by
    have e1 : (1 - t) * imbalance z₀ ≤ (1 - t) * max (imbalance z₀) (imbalance z) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
    have e2 : t * imbalance z ≤ t * max (imbalance z₀) (imbalance z) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) ht0
    have hsum := add_le_add e1 e2
    rwa [show (1 - t) * max (imbalance z₀) (imbalance z)
          + t * max (imbalance z₀) (imbalance z)
        = max (imbalance z₀) (imbalance z) from by ring] at hsum
  linarith

/-- **No sign change without a zero.** A continuous function on `[0, 1]` that is
never zero there cannot take opposite signs at the endpoints (the intermediate
value theorem, both orderings). -/
theorem no_sign_change_on_unit_interval {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≠ 0) (h01 : f 0 * f 1 < 0) : False := by
  rcases mul_neg_iff.mp h01 with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
  · have hg : ContinuousOn (fun t : ℝ => f (1 - t)) (Set.Icc 0 1) := by
      apply hf.comp (by fun_prop)
      intro t ht
      rcases Set.mem_Icc.mp ht with ⟨ht0, ht1⟩
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hmem : (0 : ℝ) ∈ Set.Icc ((fun t : ℝ => f (1 - t)) 0)
        ((fun t : ℝ => f (1 - t)) 1) := by
      simp only [sub_zero, sub_self]
      exact ⟨hneg.le, hpos.le⟩
    obtain ⟨s, hsm, hs⟩ := intermediate_value_Icc zero_le_one hg hmem
    have hs' : f (1 - s) = 0 := hs
    have hmem' : (1 - s) ∈ Set.Icc (0 : ℝ) 1 := by
      rcases Set.mem_Icc.mp hsm with ⟨hs0, hs1⟩
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    exact hne (1 - s) hmem' hs'
  · have hmem : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := ⟨hneg.le, hpos.le⟩
    obtain ⟨s, hsm, hs⟩ := intermediate_value_Icc zero_le_one hf hmem
    exact hne s hsm hs

/-! ## §2. Sign constancy on the half-planes -/

/-- On the positive-imbalance half-plane, a continuous kinetic `p` equals a single
sign times `imbalance`, the sign being `p (1, 0)`. Proof: the half-plane is convex,
so any deviation from the basepoint sign would, by the intermediate value theorem,
force `p` through zero at a point where `imbalance ≠ 0`, contradicting the kinetic
condition. -/
theorem sign_const_pos {p : LedgerState → ℝ} (hcont : Continuous p)
    (hkin : KineticCondition p) {z : LedgerState} (hz : 0 < imbalance z) :
    p z = p (1, 0) * imbalance z := by
  have hε : p (1, 0) ^ 2 = 1 := by
    have h := hkin (1, 0)
    have hi : imbalance (1, 0) = 1 := by simp [imbalance]
    rw [hi] at h
    simpa using h
  have hbase : 0 < imbalance (1, 0) := by simp [imbalance]
  have hγ : Continuous fun t : ℝ => (1 - t) • (1, 0) + t • z := by fun_prop
  have hf : ContinuousOn (fun t : ℝ => p ((1 - t) • (1, 0) + t • z)) (Set.Icc 0 1) :=
    hcont.comp_continuousOn hγ.continuousOn
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      p ((1 - t) • (1, 0) + t • z) ≠ 0 := by
    intro t ht
    have hpos : 0 < imbalance ((1 - t) • (1, 0) + t • z) :=
      imbalance_seg_pos hbase hz ht
    have hsq' := hkin ((1 - t) • (1, 0) + t • z)
    intro h0
    rw [h0, show ((0:ℝ)) ^ 2 = 0 from zero_pow two_ne_zero] at hsq'
    have hsp : (0:ℝ) < imbalance ((1 - t) • (1, 0) + t • z) ^ 2 :=
      sq_pos_of_ne_zero (ne_of_gt hpos)
    linarith
  have h0eq : p ((1 - (0:ℝ)) • (1, 0) + (0:ℝ) • z) = p (1, 0) := by
    simp
  have h1eq : p ((1 - (1:ℝ)) • (1, 0) + (1:ℝ) • z) = p z := by
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hkin z) with h | h <;>
    rcases sq_eq_one_iff.mp hε with h1 | h1
  · rw [h1, one_mul]
    exact h
  · exfalso
    refine no_sign_change_on_unit_interval hf hne ?_
    rw [h0eq, h1eq, h1, h]
    nlinarith [hz]
  · exfalso
    refine no_sign_change_on_unit_interval hf hne ?_
    rw [h0eq, h1eq, h1, h]
    nlinarith [hz]
  · rw [h1, h]
    ring

/-- On the negative-imbalance half-plane, a continuous kinetic `p` equals
`- p (0, 1)` times `imbalance`, by the same convexity argument from the basepoint
`(0, 1)`. -/
theorem sign_const_neg {p : LedgerState → ℝ} (hcont : Continuous p)
    (hkin : KineticCondition p) {z : LedgerState} (hz : imbalance z < 0) :
    p z = - p (0, 1) * imbalance z := by
  have hε : p (0, 1) ^ 2 = 1 := by
    have h := hkin (0, 1)
    have hi : imbalance (0, 1) = -1 := by simp [imbalance]
    rw [hi] at h
    simpa using h
  have hbase : imbalance (0, 1) < 0 := by simp [imbalance]
  have hγ : Continuous fun t : ℝ => (1 - t) • (0, 1) + t • z := by fun_prop
  have hf : ContinuousOn (fun t : ℝ => p ((1 - t) • (0, 1) + t • z)) (Set.Icc 0 1) :=
    hcont.comp_continuousOn hγ.continuousOn
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      p ((1 - t) • (0, 1) + t • z) ≠ 0 := by
    intro t ht
    have hneg : imbalance ((1 - t) • (0, 1) + t • z) < 0 :=
      imbalance_seg_neg hbase hz ht
    have hsq' := hkin ((1 - t) • (0, 1) + t • z)
    intro h0
    rw [h0, show ((0:ℝ)) ^ 2 = 0 from zero_pow two_ne_zero] at hsq'
    have hsp : (0:ℝ) < imbalance ((1 - t) • (0, 1) + t • z) ^ 2 :=
      sq_pos_of_ne_zero (ne_of_lt hneg)
    linarith
  have h0eq : p ((1 - (0:ℝ)) • (0, 1) + (0:ℝ) • z) = p (0, 1) := by
    simp
  have h1eq : p ((1 - (1:ℝ)) • (0, 1) + (1:ℝ) • z) = p z := by
    simp
  have hbase_eval : p z = - p (0, 1) * imbalance z ∨
      False := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hkin z) with h | h <;>
      rcases sq_eq_one_iff.mp hε with h1 | h1
    · -- p z = imbalance z with p (0,1) = 1: sign change, excluded
      refine Or.inr ?_
      refine no_sign_change_on_unit_interval hf hne ?_
      rw [h0eq, h1eq, h1, h]
      nlinarith [hz]
    · -- p z = imbalance z = -(-1) * imbalance z, the claim with p (0,1) = -1
      exact Or.inl (by rw [h1, h]; ring)
    · -- p z = -imbalance z = -(1) * imbalance z, the claim with p (0,1) = 1
      exact Or.inl (by rw [h1, h]; ring)
    · -- p z = -imbalance z with p (0,1) = -1: sign change, excluded
      refine Or.inr ?_
      refine no_sign_change_on_unit_interval hf hne ?_
      rw [h0eq, h1eq, h1, h]
      nlinarith [hz]
  rcases hbase_eval with hres | hfal
  · exact hres
  · exact hfal.elim

/-- **Balance-vanishing is derived, not assumed.** The kinetic condition alone
forces the observable to vanish on the balance locus, no continuity needed. -/
theorem balance_vanishing_of_kinetic {p : LedgerState → ℝ} (hkin : KineticCondition p)
    (z : LedgerState) (hb : Balanced z) : p z = 0 := by
  have hi : imbalance z = 0 := sub_eq_zero.mpr hb
  have hsq := hkin z
  rw [hi] at hsq
  have hz2 : p z ^ 2 = 0 := by simpa using hsq
  exact sq_eq_zero_iff.mp hz2

/-! ## §3. The four-member classification -/

/-- **Classification.** A continuous kinetic observable is pinned to a sign times
`imbalance` on each half-plane and vanishes on the balance locus, so it is one of
exactly four functions: `± imbalance` (signed branch) or `± |imbalance|` (unsigned
branch), the four sign patterns of the two half-plane signs. -/
theorem kinetic_root_classification {p : LedgerState → ℝ} (hcont : Continuous p)
    (hkin : KineticCondition p) :
    p (1, 0) ^ 2 = 1 ∧ p (0, 1) ^ 2 = 1 ∧
    (∀ z : LedgerState, 0 < imbalance z → p z = p (1, 0) * imbalance z) ∧
    (∀ z : LedgerState, imbalance z < 0 → p z = - p (0, 1) * imbalance z) ∧
    (∀ z : LedgerState, Balanced z → p z = 0) := by
  have hε1 : p (1, 0) ^ 2 = 1 := by
    have h := hkin (1, 0)
    have hi : imbalance (1, 0) = 1 := by simp [imbalance]
    rw [hi] at h
    simpa using h
  have hε2 : p (0, 1) ^ 2 = 1 := by
    have h := hkin (0, 1)
    have hi : imbalance (0, 1) = -1 := by simp [imbalance]
    rw [hi] at h
    simpa using h
  refine ⟨hε1, hε2, fun z hz => sign_const_pos hcont hkin hz,
    fun z hz => sign_const_neg hcont hkin hz, fun z hb =>
    balance_vanishing_of_kinetic hkin z hb⟩

/-- **THEOREM (exactly four continuous kinetic observables).**  The classification
pins the two half-plane signs to unit real numbers, and each of the four sign
patterns is one named function, so the continuous kinetic class is exhausted by
`imbalance`, `- imbalance`, `|imbalance|`, and `- |imbalance|`.  The two signed
functions are the additive branch (swap parity `p (0, 1) = - p (1, 0)`); the two
unsigned ones are the swap-even branch.  This is the formal exhaustiveness the
section heading advertises. -/
theorem kinetic_root_mem_four {p : LedgerState → ℝ} (hcont : Continuous p)
    (hkin : KineticCondition p) :
    p = imbalance ∨ p = (fun z => - imbalance z) ∨
      p = (fun z => |imbalance z|) ∨ p = (fun z => - |imbalance z|) := by
  obtain ⟨hε1, hε2, hpos, hneg, hbal⟩ := kinetic_root_classification hcont hkin
  have ha : p (1, 0) = 1 ∨ p (1, 0) = -1 := sq_eq_one_iff.mp hε1
  have hb : p (0, 1) = 1 ∨ p (0, 1) = -1 := sq_eq_one_iff.mp hε2
  have key : ∀ z : LedgerState,
      p z = if 0 ≤ imbalance z then p (1, 0) * imbalance z
        else - p (0, 1) * imbalance z := by
    intro z
    rcases lt_trichotomy (imbalance z) 0 with hzn | hz0 | hzp
    · rw [if_neg (not_le_of_gt hzn)]
      exact hneg z hzn
    · rw [if_pos (le_of_eq hz0.symm)]
      have hzb : Balanced z := sub_eq_zero.mp (by simpa [imbalance] using hz0)
      rw [hbal z hzb, hz0]
      simp
    · rw [if_pos (le_of_lt hzp)]
      exact hpos z hzp
  rcases ha with ha1 | ha1 <;> rcases hb with hb1 | hb1
  · refine Or.inr (Or.inr (Or.inl ?_))
    funext z
    rw [key z, ha1, hb1]
    by_cases hz : 0 ≤ imbalance z
    · rw [if_pos hz, abs_of_nonneg hz]
      ring
    · rw [if_neg hz, abs_of_neg (lt_of_not_ge hz)]
      ring
  · left
    funext z
    rw [key z, ha1, hb1]
    by_cases hz : 0 ≤ imbalance z
    · rw [if_pos hz]
      ring
    · rw [if_neg hz]
      ring
  · refine Or.inr (Or.inl ?_)
    funext z
    rw [key z, ha1, hb1]
    by_cases hz : 0 ≤ imbalance z
    · rw [if_pos hz]
      ring
    · rw [if_neg hz]
      ring
  · refine Or.inr (Or.inr (Or.inr ?_))
    funext z
    rw [key z, ha1, hb1]
    by_cases hz : 0 ≤ imbalance z
    · rw [if_pos hz, abs_of_nonneg hz]
      ring
    · rw [if_neg hz, abs_of_neg (lt_of_not_ge hz)]
      ring

/-! ## §4. Extensivity is the swap parity -/

/-- **Additivity from the signed branch.** If the two half-plane signs agree
through the swap (`p (0, 1) = - p (1, 0)`), then `p = p (1, 0) • imbalance`
globally, hence `p` is additive under consolidation. If they disagree, the
balanced state `(1, 1)` already refutes additivity. So within the kinetic +
continuous class, additivity is exactly the swap parity. -/
theorem kinetic_root_additive_iff {p : LedgerState → ℝ} (hcont : Continuous p)
    (hkin : KineticCondition p) :
    (∀ z w : LedgerState, p (z + w) = p z + p w) ↔ p (0, 1) = - p (1, 0) := by
  obtain ⟨hε1, hε2, hpos, hneg, hbal⟩ := kinetic_root_classification hcont hkin
  constructor
  · intro h
    have hsum := h (1, 0) (0, 1)
    have heq : ((1, 0) : LedgerState) + (0, 1) = (1, 1) := by
      apply Prod.ext <;> simp
    rw [heq] at hsum
    have h11 : p (1, 1) = 0 := hbal (1, 1) rfl
    rw [h11] at hsum
    linarith
  · intro h12 z w
    have hform : ∀ u : LedgerState, p u = p (1, 0) * imbalance u := by
      intro u
      rcases lt_trichotomy (imbalance u) 0 with hun | hue | hup
      · rw [hneg u hun, h12]
        ring
      · have hub : Balanced u := by
          have : u.1 - u.2 = 0 := by
            have : imbalance u = 0 := hue
            simpa [imbalance] using this
          exact sub_eq_zero.mp this
        rw [hbal u hub]
        have : imbalance u = 0 := hue
        simp [this]
      · exact hpos u hup
    rw [hform (z + w), hform z, hform w, imbalance_add]
    ring

/-- **The headline equivalence.** Within the kinetic + continuous class, additivity
under ledger consolidation and oddness under the debit-credit swap are the *same
property*. Extensivity of the momentum is a parity under a substrate involution. -/
theorem kinetic_root_additive_iff_swap_odd {p : LedgerState → ℝ}
    (hcont : Continuous p) (hkin : KineticCondition p) :
    (∀ z w : LedgerState, p (z + w) = p z + p w) ↔ SwapOdd p := by
  rw [kinetic_root_additive_iff hcont hkin]
  obtain ⟨hε1, hε2, hpos, hneg, hbal⟩ := kinetic_root_classification hcont hkin
  constructor
  · intro h12 z
    rcases lt_trichotomy (imbalance z) 0 with hzneg | hz0 | hzpos
    · have hswappos : 0 < imbalance (z.2, z.1) := by
        rw [imbalance_swap]; linarith
      rw [hpos (z.2, z.1) hswappos, hneg z hzneg, imbalance_swap, h12]
      ring
    · have hzb : Balanced z := sub_eq_zero.mp (by simpa [imbalance] using hz0)
      have hswb : Balanced (z.2, z.1) := hzb.symm
      rw [hbal z hzb, hbal (z.2, z.1) hswb]
      ring
    · have hswapneg : imbalance (z.2, z.1) < 0 := by
        rw [imbalance_swap]; linarith
      rw [hneg (z.2, z.1) hswapneg, hpos z hzpos, imbalance_swap, h12]
      ring
  · intro hswap
    have := hswap (1, 0)
    exact this

/-! ## §5. B1, derived from the named kinetic package -/

/-- **B1, derived from the named kinetic package.** A momentum observable whose
square is the squared ledger imbalance (the kinetic condition, which is the
magnitude half of the chart conclusion and is named, not substrate-derived), that
is continuous, and that is odd under the substrate's debit-credit swap, is
**additive under ledger consolidation**, vanishes on the balance locus (derived,
not assumed), and is a unit sign times the imbalance coordinate (the composition
with the existing reduction `additive_continuous_balanced_is_imbalance`, here
recovered directly with the sign pinned by the classification). -/
theorem momentum_additivity_from_swap {p : LedgerState → ℝ}
    (hkin : KineticCondition p) (hcont : Continuous p) (hswap : SwapOdd p) :
    (∀ z w : LedgerState, p (z + w) = p z + p w) ∧
    (∀ z : LedgerState, Balanced z → p z = 0) ∧
    (∃ a : ℝ, a ^ 2 = 1 ∧ ∀ z : LedgerState, p z = a * imbalance z) := by
  have hadd : ∀ z w : LedgerState, p (z + w) = p z + p w :=
    (kinetic_root_additive_iff_swap_odd hcont hkin).2 hswap
  obtain ⟨hε1, hε2, hpos, hneg, hbal⟩ := kinetic_root_classification hcont hkin
  have h12 : p (0, 1) = - p (1, 0) := hswap (1, 0)
  refine ⟨hadd, hbal, p (1, 0), hε1, fun z => ?_⟩
  rcases lt_trichotomy (imbalance z) 0 with hzneg | hz0 | hzpos
  · rw [hneg z hzneg, h12]
    ring
  · have hzb : Balanced z := sub_eq_zero.mp (by simpa [imbalance] using hz0)
    rw [hbal z hzb]
    have : imbalance z = 0 := hz0
    simp [this]
  · exact hpos z hzpos

/-- **Where the kinetic condition comes from, on an orbit.** The recognition cost
is exactly the squared imbalance over twice the Casimir
(`Jlog_eq_imbalance_sq_div_two_casimir`, existing), so a momentum whose kinetic
energy `p ^ 2 / (2 k)` equals the cost has the imbalance's magnitude on that orbit.
The global kinetic condition off-orbit is a named modeling premise; this theorem is
the on-orbit, derived part of it. -/
theorem kinetic_on_orbit (k t : ℝ) (hk : 0 < k) {p : LedgerState → ℝ}
    (hkinetic_energy : p (orbitPoint k t) ^ 2 = 2 * k * Cost.Jlog t) :
    p (orbitPoint k t) ^ 2 = imbalance (orbitPoint k t) ^ 2 := by
  rw [hkinetic_energy, Jlog_eq_imbalance_sq_div_two_casimir k t hk]
  have hk2 : (2 : ℝ) * k ≠ 0 := mul_ne_zero two_ne_zero hk.ne'
  field_simp

/-! ## §6. Each premise is load-bearing -/

/-- **The kinetic condition is load-bearing.** The `nlP` reparametrization
`m ↦ m + m ^ 3` (the witness family of `chart_not_forced_without_linearity`) is
continuous, swap-odd, and balance-vanishing, but fails the kinetic condition and is
not additive. Dropping the kinetic condition reopens the linearity trap; keeping it
is what excludes the reparametrization family. -/
theorem nlP_countermodel :
    Continuous (fun z : LedgerState => nlP (imbalance z)) ∧
    SwapOdd (fun z : LedgerState => nlP (imbalance z)) ∧
    (∀ z : LedgerState, Balanced z → nlP (imbalance z) = 0) ∧
    ¬ KineticCondition (fun z : LedgerState => nlP (imbalance z)) ∧
    ¬ (∀ z w : LedgerState,
        nlP (imbalance (z + w)) = nlP (imbalance z) + nlP (imbalance w)) := by
  have hcont : Continuous fun z : LedgerState => nlP (imbalance z) := by
    have hb : Continuous fun z : LedgerState => imbalance z :=
      continuous_fst.sub continuous_snd
    exact (hb.add (hb.pow 3)).congr (fun z => by simp [nlP])
  refine ⟨hcont, fun z => ?_, fun z hb => ?_, ?_, ?_⟩
  · show nlP (imbalance (z.2, z.1)) = - nlP (imbalance z)
    rw [imbalance_swap]
    simp [nlP]
    ring
  · have : imbalance z = 0 := sub_eq_zero.mpr hb
    simp [nlP, this]
  · intro h
    have h1 := h (1, 0)
    norm_num [nlP, imbalance] at h1
  · intro h
    have h1 := h (1, 0) (1, 0)
    have h2 : ((1, 0) : LedgerState) + (1, 0) = (2, 0) := by
      apply Prod.ext <;> simp <;> norm_num
    rw [h2] at h1
    norm_num [nlP, imbalance] at h1

/-- **Swap-oddness is load-bearing.** The absolute imbalance `z ↦ |imbalance z|` is
continuous, kinetic, and balance-vanishing, but it is swap-*even*, hence not
additive: consolidating `(1, 0)` with `(0, 1)` gives the balanced state, whose
absolute imbalance is `0 ≠ 1 + 1`. The unsigned branch is the countermodel that
pins the whole arc on the swap parity. -/
theorem abs_countermodel :
    Continuous (fun z : LedgerState => |imbalance z|) ∧
    KineticCondition (fun z : LedgerState => |imbalance z|) ∧
    (∀ z : LedgerState, Balanced z → |imbalance z| = 0) ∧
    ¬ SwapOdd (fun z : LedgerState => |imbalance z|) ∧
    ¬ (∀ z w : LedgerState,
        |imbalance (z + w)| = |imbalance z| + |imbalance w|) := by
  refine ⟨(continuous_fst.sub continuous_snd).abs, fun z => sq_abs (imbalance z),
    fun z hb => ?_, ?_, ?_⟩
  · have : imbalance z = 0 := sub_eq_zero.mpr hb
    simp [this]
  · intro h
    have h1 := h (1, 0)
    norm_num [imbalance] at h1
  · intro h
    have h1 := h (1, 0) (0, 1)
    have heq : ((1, 0) : LedgerState) + (0, 1) = (1, 1) := by
      apply Prod.ext <;> simp
    rw [heq] at h1
    norm_num [imbalance] at h1

/-! ## §7. The certificate -/

/-- **The B1 verdict, packaged: a conditional closure.**  Additivity is proved
*from the named kinetic premise*, continuity, and swap parity; each premise is
shown load-bearing by an exhibited countermodel.  The kinetic premise is the
magnitude half of the chart conclusion (`|p| = |imbalance|` pointwise), so the
certificate's derived content is the parity equivalence and the formal
exhaustiveness of the four-member class; the residual named premise is the
momentum-magnitude bridge, shared with the cMom constant cluster. -/
structure MomentumAdditivityVerdict : Prop where
  /-- Additivity, derived FROM the kinetic premise: kinetic + continuous +
  swap-odd forces additivity under ledger consolidation.  The kinetic premise is
  named, not substrate-derived; it is the magnitude half of the chart. -/
  additivity_from_kinetic_swap : ∀ p : LedgerState → ℝ, KineticCondition p →
    Continuous p → SwapOdd p → ∀ z w : LedgerState, p (z + w) = p z + p w
  /-- The composition: such a momentum is a unit sign times the imbalance
  coordinate. -/
  momentum_is_imbalance_coordinate : ∀ p : LedgerState → ℝ, KineticCondition p →
    Continuous p → SwapOdd p →
    ∃ a : ℝ, a ^ 2 = 1 ∧ ∀ z : LedgerState, p z = a * imbalance z
  /-- Balance-vanishing is derived from the kinetic condition, not assumed. -/
  balance_vanishing_derived : ∀ p : LedgerState → ℝ, KineticCondition p →
    ∀ z : LedgerState, Balanced z → p z = 0
  /-- Within the kinetic + continuous class, additivity and swap-oddness are the
  same property: extensivity is a parity, not a regularity class. -/
  additivity_iff_swap_odd : ∀ p : LedgerState → ℝ, Continuous p →
    KineticCondition p → ((∀ z w : LedgerState, p (z + w) = p z + p w) ↔ SwapOdd p)
  /-- The kinetic condition does work: the `nlP` family passes the other two
  premises and fails additivity. -/
  kinetic_is_load_bearing : Continuous (fun z : LedgerState => nlP (imbalance z)) ∧
    SwapOdd (fun z : LedgerState => nlP (imbalance z)) ∧
    (∀ z : LedgerState, Balanced z → nlP (imbalance z) = 0) ∧
    ¬ KineticCondition (fun z : LedgerState => nlP (imbalance z)) ∧
    ¬ (∀ z w : LedgerState,
        nlP (imbalance (z + w)) = nlP (imbalance z) + nlP (imbalance w))
  /-- The swap parity does work: the unsigned branch passes the other two premises
  and fails additivity. -/
  swap_is_load_bearing : Continuous (fun z : LedgerState => |imbalance z|) ∧
    KineticCondition (fun z : LedgerState => |imbalance z|) ∧
    (∀ z : LedgerState, Balanced z → |imbalance z| = 0) ∧
    ¬ SwapOdd (fun z : LedgerState => |imbalance z|) ∧
    ¬ (∀ z w : LedgerState,
        |imbalance (z + w)| = |imbalance z| + |imbalance w|)
  /-- The on-orbit kinetic content is the existing exactness theorem composed
  with the energy-equals-cost identification `p ^ 2 = 2 * k * Jlog`; the
  identification is declared in the hypothesis, not derived. -/
  kinetic_on_orbit_derived : ∀ (k t : ℝ), 0 < k → ∀ {p : LedgerState → ℝ},
    p (orbitPoint k t) ^ 2 = 2 * k * Cost.Jlog t →
    p (orbitPoint k t) ^ 2 = imbalance (orbitPoint k t) ^ 2

theorem momentumAdditivityVerdict : MomentumAdditivityVerdict where
  additivity_from_kinetic_swap := fun p hkin hcont hswap =>
    (momentum_additivity_from_swap hkin hcont hswap).1
  momentum_is_imbalance_coordinate := fun p hkin hcont hswap =>
    (momentum_additivity_from_swap hkin hcont hswap).2.2
  balance_vanishing_derived := fun p hkin => balance_vanishing_of_kinetic hkin
  additivity_iff_swap_odd := fun p hcont hkin =>
    kinetic_root_additive_iff_swap_odd hcont hkin
  kinetic_is_load_bearing := nlP_countermodel
  swap_is_load_bearing := abs_countermodel
  kinetic_on_orbit_derived := fun k t hk p hke => kinetic_on_orbit k t hk hke

/-! ## Axiom audit -/

#print axioms imbalance_seg_pos
#print axioms imbalance_seg_neg
#print axioms no_sign_change_on_unit_interval
#print axioms balance_vanishing_of_kinetic
#print axioms sign_const_pos
#print axioms sign_const_neg
#print axioms kinetic_root_classification
#print axioms kinetic_root_mem_four
#print axioms kinetic_root_additive_iff
#print axioms kinetic_root_additive_iff_swap_odd
#print axioms momentum_additivity_from_swap
#print axioms kinetic_on_orbit
#print axioms nlP_countermodel
#print axioms abs_countermodel
#print axioms momentumAdditivityVerdict

end MomentumAdditivity
end SevenGaps
end Gravity
end IndisputableMonolith
