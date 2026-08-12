import IndisputableMonolith.Gravity.SevenGaps.Gap5MomentumAdditivityComposition

/-!
# Net-imbalance package from posting-level incidence

**Verdict, stated first.** Of the three charged outcomes, **(c) LANDED** as the
headline and **(b) LANDED** as the supporting no-go; **(a) is not derived**.

The consumer package waiting upstream is
`ReadsNetImbalance` (P1) and `AdditiveOnDebitAxis` (P2), which with continuity
and unit force full consolidation additivity and `EnergyEqualsCost`. The prior
composition-law attack showed those two properties are not forced by ambient
RCL plus companions, and identified P2 as the selecting property among
P1-satisfying observables (`|imbalance|` and `nlPUnit` pass P1, fail P2).

This module imports the next layer of ledger posting structure beyond the
composition law: **column posting incidence** (a state's momentum is the sum of
its pure-debit and pure-credit contributions). That structure is named, not
derived from σ = 0 or from RCL. Under incidence together with debit-credit
parity (`SwapOdd`), P1 and P2 become equivalent, so the two-property frontier
collapses to a single 1D Cauchy obligation on the debit axis. Sufficiency
through the existing consumer is kernel-checked both ways.

The same incidence layer does **not** by itself force that Cauchy obligation:
the cube-difference observable `z ↦ z.1³ − z.2³` is continuous, swap-odd,
balance-vanishing, unit-normalized, and column-incident, yet fails both P1 and
P2. Scope (per `L-qg-witness-is-not-a-class-20260729`): that is a concrete
package witness on the stated `LedgerState` carrier, not a class theorem.

## What is NOT claimed

* No flag flip. Flags 6 and 12 still rest on `EnergyEqualsCost`; the remaining
  named input is 1D debit-axis additivity (equivalently P1) under posting
  incidence and swap-oddness.
* Column posting incidence is a named posting-level hypothesis, not a theorem
  of the symplectic or RCL modules. Deriving it from deeper substrate structure
  is OPEN and is the natural next attack if the 1D Cauchy side closes first.
* B1's kinetic-conditional additivity is neither used nor strengthened.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace NetImbalanceDerivation

open ChartFromLedgerMomentum MomentumAdditivity MomentumAdditivityComposition
open MomentumMagnitudeBridge EnergyEqualsCostDerivation

noncomputable section

/-! ## §0. Posting-level column incidence -/

/-- **Column posting incidence.** The momentum of a mixed debit-credit state is
the sum of the pure-debit contribution and the pure-credit contribution. This
is the posting-level claim that the two columns contribute independently; it is
strictly beyond the recognition composition law (which never mentions a
momentum observable). -/
def PostingIncidence (p : LedgerState → ℝ) : Prop :=
  ∀ d c : ℝ, p (d, c) = p (d, 0) + p (0, c)

/-- Under debit-credit swap-oddness, a pure credit is the negation of the
matching pure debit. -/
theorem axisOdd_of_swapOdd {p : LedgerState → ℝ} (hswap : SwapOdd p) :
    ∀ n : ℝ, p (0, n) = - p (n, 0) := by
  intro n
  simpa using hswap (n, (0 : ℝ))

/-- The ledger state decomposes as a pure-debit net charge plus a balanced
offset: `z = (imbalance z, 0) + (z.2, z.2)`. -/
theorem state_eq_netDebit_plus_balanced (z : LedgerState) :
    z = ((imbalance z, (0 : ℝ)) : LedgerState) + (z.2, z.2) := by
  apply Prod.ext
  · change z.1 = (z.1 - z.2) + z.2
    ring
  · simp

theorem balanced_snd_pair (z : LedgerState) :
    ChartFromLedgerMomentum.Balanced ((z.2, z.2) : LedgerState) :=
  rfl

/-! ## §1. Under incidence + swap-odd, P1 ↔ P2 -/

/-- From posting incidence and swap-oddness, the momentum is the difference of
the two pure-column readings: `p (d, c) = p (d, 0) - p (c, 0)`. -/
theorem posting_form_of_incidence_swap
    {p : LedgerState → ℝ} (hinc : PostingIncidence p) (hswap : SwapOdd p)
    (d c : ℝ) : p (d, c) = p (d, 0) - p (c, 0) := by
  have haxis := axisOdd_of_swapOdd hswap
  calc p (d, c) = p (d, 0) + p (0, c) := hinc d c
    _ = p (d, 0) + (- p (c, 0)) := by rw [haxis c]
    _ = p (d, 0) - p (c, 0) := by ring

/-- **Equivalence of the two remaining inputs.** Under column posting incidence
and debit-credit parity, net-imbalance reading is equivalent to 1D additivity on
the debit axis. The two-property frontier therefore collapses to one. -/
theorem readsNet_iff_additiveOnDebit_of_posting
    {p : LedgerState → ℝ} (hinc : PostingIncidence p) (hswap : SwapOdd p) :
    ReadsNetImbalance p ↔ AdditiveOnDebitAxis p := by
  have hform := posting_form_of_incidence_swap hinc hswap
  constructor
  · intro hread m n
    have himb : imbalance ((m + n, n) : LedgerState) = m := by
      change (m + n) - n = m
      ring
    have h1 : p (m + n, n) = p (m, 0) := by
      calc p (m + n, n) = p (imbalance (m + n, n), 0) := hread (m + n, n)
        _ = p (m, 0) := by rw [himb]
    have h2 : p (m + n, n) = p (m + n, 0) - p (n, 0) := hform (m + n) n
    linarith
  · intro hadd1 z
    have hdiff : ∀ a b : ℝ, p (a, 0) - p (b, 0) = p (a - b, 0) := by
      intro a b
      have h := hadd1 (a - b) b
      have hab : (a - b + b : ℝ) = a := by ring
      rw [hab] at h
      linarith
    calc p z = p (z.1, z.2) := rfl
      _ = p (z.1, 0) - p (z.2, 0) := hform z.1 z.2
      _ = p (z.1 - z.2, 0) := hdiff z.1 z.2
      _ = p (imbalance z, 0) := rfl

/-! ## §2. Sufficiency: incidence + swap + one of P1/P2 discharges EEC -/

/-- Under posting incidence and swap-oddness, debit-axis additivity, continuity,
and unit normalization force full consolidation additivity, derived
balance-vanishing, and `EnergyEqualsCost`. No kinetic hypothesis. -/
theorem energyEqualsCost_of_posting_incidence_additive_unit
    (p : LedgerState → ℝ)
    (hinc : PostingIncidence p)
    (hswap : SwapOdd p)
    (hadd1 : AdditiveOnDebitAxis p)
    (hcont : Continuous p)
    (hunit : p (1, 0) ^ 2 = 1) :
    (∀ z w : LedgerState, p (z + w) = p z + p w) ∧
      (∀ z : LedgerState, ChartFromLedgerMomentum.Balanced z → p z = 0) ∧
      MomentumMagnitudeBridge.EnergyEqualsCost p := by
  have hread : ReadsNetImbalance p :=
    (readsNet_iff_additiveOnDebit_of_posting hinc hswap).mpr hadd1
  exact energyEqualsCost_of_net_imbalance_reading_additive_unit p hread hadd1 hcont hunit

/-- Symmetric form: net-imbalance reading in place of debit-axis additivity. -/
theorem energyEqualsCost_of_posting_incidence_readsNet_unit
    (p : LedgerState → ℝ)
    (hinc : PostingIncidence p)
    (hswap : SwapOdd p)
    (hread : ReadsNetImbalance p)
    (hcont : Continuous p)
    (hunit : p (1, 0) ^ 2 = 1) :
    (∀ z w : LedgerState, p (z + w) = p z + p w) ∧
      (∀ z : LedgerState, ChartFromLedgerMomentum.Balanced z → p z = 0) ∧
      MomentumMagnitudeBridge.EnergyEqualsCost p := by
  have hadd1 : AdditiveOnDebitAxis p :=
    (readsNet_iff_additiveOnDebit_of_posting hinc hswap).mp hread
  exact energyEqualsCost_of_net_imbalance_reading_additive_unit p hread hadd1 hcont hunit

/-! ## §3. Inhabitation: imbalance sits in the posting package -/

theorem imbalance_posting_incidence : PostingIncidence imbalance := by
  intro d c
  change d - c = (d - 0) + (0 - c)
  ring

theorem imbalance_swap_odd : SwapOdd imbalance := by
  intro z
  change z.2 - z.1 = -(z.1 - z.2)
  ring

theorem imbalance_inhabits_posting_package :
    PostingIncidence imbalance ∧ SwapOdd imbalance ∧
      ReadsNetImbalance imbalance ∧ AdditiveOnDebitAxis imbalance ∧
      Continuous imbalance ∧ imbalance ((1, 0) : LedgerState) ^ 2 = 1 :=
  ⟨imbalance_posting_incidence, imbalance_swap_odd,
    imbalance_reads_net_and_additive_on_axis.1,
    imbalance_reads_net_and_additive_on_axis.2.1,
    imbalance_reads_net_and_additive_on_axis.2.2.1,
    imbalance_reads_net_and_additive_on_axis.2.2.2⟩

/-! ## §4. No-go: incidence + swap + companions do not force P1/P2 -/

/-- Cube-difference observable: column-separable and swap-odd, but not a
function of net imbalance alone. -/
def cubeDiff (z : LedgerState) : ℝ := z.1 ^ 3 - z.2 ^ 3

theorem cubeDiff_posting_incidence : PostingIncidence cubeDiff := by
  intro d c
  change d ^ 3 - c ^ 3 = (d ^ 3 - (0 : ℝ) ^ 3) + ((0 : ℝ) ^ 3 - c ^ 3)
  ring

theorem cubeDiff_swap_odd : SwapOdd cubeDiff := by
  intro z
  change z.2 ^ 3 - z.1 ^ 3 = -(z.1 ^ 3 - z.2 ^ 3)
  ring

theorem cubeDiff_continuous : Continuous cubeDiff :=
  (continuous_fst.pow 3).sub (continuous_snd.pow 3)

theorem cubeDiff_balance_vanishing :
    ∀ z : LedgerState, ChartFromLedgerMomentum.Balanced z → cubeDiff z = 0 := by
  intro z hz
  change z.1 = z.2 at hz
  simp [cubeDiff, hz]

theorem cubeDiff_unit : cubeDiff (1, 0) ^ 2 = 1 := by
  norm_num [cubeDiff]

theorem cubeDiff_not_additiveOnDebitAxis :
    ¬ AdditiveOnDebitAxis cubeDiff := by
  intro h
  have h1 := h (1 : ℝ) (1 : ℝ)
  -- LHS: cubeDiff (1,0) + cubeDiff (1,0) = 1 + 1 = 2
  -- RHS: cubeDiff (2,0) = 8
  change (1 : ℝ) ^ 3 - (0 : ℝ) ^ 3 + ((1 : ℝ) ^ 3 - (0 : ℝ) ^ 3)
      = (1 + 1 : ℝ) ^ 3 - (0 : ℝ) ^ 3 at h1
  norm_num at h1

theorem cubeDiff_not_readsNetImbalance :
    ¬ ReadsNetImbalance cubeDiff := by
  intro h
  -- At z = (2, 1): cubeDiff = 7, imbalance = 1, cubeDiff (1,0) = 1
  have h1 := h ((2, 1) : LedgerState)
  change (2 : ℝ) ^ 3 - (1 : ℝ) ^ 3
      = ((2 : ℝ) - (1 : ℝ)) ^ 3 - (0 : ℝ) ^ 3 at h1
  norm_num at h1

/-- **NO-GO (incidence does not select the Cauchy property).** On the stated
`LedgerState` carrier there is a continuous, swap-odd, balance-vanishing,
unit-normalized, column-incident momentum (`cubeDiff`) that fails both
`ReadsNetImbalance` and `AdditiveOnDebitAxis`. Column posting incidence plus
debit-credit parity plus the three consumer companions therefore cannot force
the remaining 1D Cauchy input.

Quantifier written first: ambient posting incidence of this concrete observable
together with the concrete package. Not a ∀ over a class of posting systems. -/
theorem posting_incidence_does_not_force_debit_axis_additivity :
    PostingIncidence cubeDiff ∧ SwapOdd cubeDiff ∧
      Continuous cubeDiff ∧
      (∀ z : LedgerState, ChartFromLedgerMomentum.Balanced z → cubeDiff z = 0) ∧
      cubeDiff (1, 0) ^ 2 = 1 ∧
      ¬ AdditiveOnDebitAxis cubeDiff ∧
      ¬ ReadsNetImbalance cubeDiff :=
  ⟨cubeDiff_posting_incidence, cubeDiff_swap_odd, cubeDiff_continuous,
    cubeDiff_balance_vanishing, cubeDiff_unit,
    cubeDiff_not_additiveOnDebitAxis, cubeDiff_not_readsNetImbalance⟩

/-! ## §5. Prior countermodels fail posting incidence (incidence is selecting) -/

theorem abs_imbalance_not_posting_incidence :
    ¬ PostingIncidence (fun z : LedgerState => |imbalance z|) := by
  intro h
  -- At (1,1): LHS = |0| = 0; RHS = |1| + |-1| = 2
  have h1 := h (1 : ℝ) (1 : ℝ)
  change |(1 : ℝ) - 1| = |(1 : ℝ) - 0| + |(0 : ℝ) - 1| at h1
  norm_num at h1

theorem nlPUnit_not_posting_incidence :
    ¬ PostingIncidence nlPUnit := by
  intro h
  -- At (2,1): LHS = nlP(1)/2 = 1; RHS = nlP(2)/2 + nlP(-1)/2 = 5 + (-1) = 4
  have h1 := h (2 : ℝ) (1 : ℝ)
  simp only [nlPUnit, nlP, imbalance] at h1
  norm_num at h1

/-- Absolute imbalance and the unit-normalized nlP reparametrization both fail
column posting incidence. Naming incidence therefore excludes the composition-
law no-go witnesses; the remaining obstruction is the cube-difference family
(and its continuous cousins), which fail the 1D Cauchy property. -/
theorem prior_nogo_witnesses_fail_posting_incidence :
    ¬ PostingIncidence (fun z : LedgerState => |imbalance z|) ∧
      ¬ PostingIncidence nlPUnit :=
  ⟨abs_imbalance_not_posting_incidence, nlPUnit_not_posting_incidence⟩

/-! ## §6. Certificate -/

/-- **The net-imbalance posting-incidence verdict.** (c): under column posting
incidence and swap-oddness, P1 ↔ P2, and either plus continuity and unit
discharges `EnergyEqualsCost` through the upstream consumer; imbalance inhabits
the package. (b): incidence plus companions still admit a non-Cauchy witness
(`cubeDiff`). (a): no derivation of P1/P2 from incidence alone. -/
structure NetImbalanceDerivationVerdict : Prop where
  posting_collapses_P1_P2 :
    ∀ p : LedgerState → ℝ, PostingIncidence p → SwapOdd p →
      (ReadsNetImbalance p ↔ AdditiveOnDebitAxis p)
  sufficient_via_additive :
    ∀ p : LedgerState → ℝ, PostingIncidence p → SwapOdd p →
      AdditiveOnDebitAxis p → Continuous p → p (1, 0) ^ 2 = 1 →
        (∀ z w : LedgerState, p (z + w) = p z + p w) ∧
          (∀ z : LedgerState, ChartFromLedgerMomentum.Balanced z → p z = 0) ∧
          MomentumMagnitudeBridge.EnergyEqualsCost p
  sufficient_via_readsNet :
    ∀ p : LedgerState → ℝ, PostingIncidence p → SwapOdd p →
      ReadsNetImbalance p → Continuous p → p (1, 0) ^ 2 = 1 →
        (∀ z w : LedgerState, p (z + w) = p z + p w) ∧
          (∀ z : LedgerState, ChartFromLedgerMomentum.Balanced z → p z = 0) ∧
          MomentumMagnitudeBridge.EnergyEqualsCost p
  imbalance_inhabits :
    PostingIncidence imbalance ∧ SwapOdd imbalance ∧
      ReadsNetImbalance imbalance ∧ AdditiveOnDebitAxis imbalance ∧
      Continuous imbalance ∧ imbalance ((1, 0) : LedgerState) ^ 2 = 1
  incidence_does_not_force_cauchy :
    PostingIncidence cubeDiff ∧ SwapOdd cubeDiff ∧
      Continuous cubeDiff ∧
      (∀ z : LedgerState, ChartFromLedgerMomentum.Balanced z → cubeDiff z = 0) ∧
      cubeDiff (1, 0) ^ 2 = 1 ∧
      ¬ AdditiveOnDebitAxis cubeDiff ∧
      ¬ ReadsNetImbalance cubeDiff
  prior_witnesses_fail_incidence :
    ¬ PostingIncidence (fun z : LedgerState => |imbalance z|) ∧
      ¬ PostingIncidence nlPUnit

theorem netImbalanceDerivationVerdict : NetImbalanceDerivationVerdict where
  posting_collapses_P1_P2 := fun _ hinc hswap =>
    readsNet_iff_additiveOnDebit_of_posting hinc hswap
  sufficient_via_additive :=
    energyEqualsCost_of_posting_incidence_additive_unit
  sufficient_via_readsNet :=
    energyEqualsCost_of_posting_incidence_readsNet_unit
  imbalance_inhabits := imbalance_inhabits_posting_package
  incidence_does_not_force_cauchy :=
    posting_incidence_does_not_force_debit_axis_additivity
  prior_witnesses_fail_incidence := prior_nogo_witnesses_fail_posting_incidence

/-! ## Axiom audit -/

#print axioms axisOdd_of_swapOdd
#print axioms posting_form_of_incidence_swap
#print axioms readsNet_iff_additiveOnDebit_of_posting
#print axioms energyEqualsCost_of_posting_incidence_additive_unit
#print axioms energyEqualsCost_of_posting_incidence_readsNet_unit
#print axioms imbalance_inhabits_posting_package
#print axioms cubeDiff_not_additiveOnDebitAxis
#print axioms cubeDiff_not_readsNetImbalance
#print axioms posting_incidence_does_not_force_debit_axis_additivity
#print axioms abs_imbalance_not_posting_incidence
#print axioms nlPUnit_not_posting_incidence
#print axioms prior_nogo_witnesses_fail_posting_incidence
#print axioms netImbalanceDerivationVerdict

end
end NetImbalanceDerivation
end SevenGaps
end Gravity
end IndisputableMonolith
