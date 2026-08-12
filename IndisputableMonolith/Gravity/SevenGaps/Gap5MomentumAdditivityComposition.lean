import IndisputableMonolith.Gravity.SevenGaps.Gap5EnergyEqualsCostDerivation
import IndisputableMonolith.Cost.SymplecticAction

/-!
# Unconditional momentum additivity: composition-law attack

**Verdict, stated first.** Of the three charged outcomes, **(b) LANDED** as the
headline and **(c) LANDED** as the constructive corollary; **(a) is refuted by
the no-go**, not merely unbuilt.

The consumer
`energyEqualsCost_of_additive_continuous_balanced_unit` already proves that
additivity under ledger consolidation, continuity, balance-vanishing, and unit
normalization `p (1,0) ^ 2 = 1` force `EnergyEqualsCost`. This module attacks
the remaining premise: unconditional additivity, from the recognition
composition law. B1's kinetic-conditional additivity is not an input.

## (b) The no-go: the composition law does not select additivity

The recognition composition law (`SatisfiesCompositionLaw`) is a constraint on
cost functionals `F : ℝ → ℝ` of positive ledger ratios. On the stated chart
carrier `LedgerState`, the ambient recognition cost is `Cost.Jcost`, and it
satisfies the law (`jcost_satisfiesCompositionLaw_via_symplectic`). That fact
is independent of any choice of momentum observable `p : LedgerState → ℝ`: the
law never mentions `p`.

The same carrier admits two continuous, balance-vanishing, unit-normalized
momentum observables that disagree on additivity under consolidation:

* `imbalance`, which is additive (`imbalance_is_additive_continuous_balanced`);
* the absolute imbalance `z ↦ |imbalance z|`, which fails additivity at the
  consolidation of `(1,0)` with `(0,1)` (`abs_imbalance_not_additive`).

Both packages pass every companion the consumer still consumes except
additivity itself. Hence on this stated system, no derivation whose only
inputs are the recognition composition law (the ambient cost being an RCL
solution) together with continuity, balance-vanishing, and unit normalization
can conclude additivity: the data admit both packages
(`momentum_additivity_independent_of_composition_law`).

Scope (per `L-qg-witness-is-not-a-class-20260729`): the theorem is a
two-package witness on the stated `LedgerState` chart system with ambient cost
`Jcost`. It is not a quantified class theorem over all cost systems, and the
prose does not say "class" or "general."

A second witness in the swap-odd sector: the unit-normalized reparametrization
`nlP ∘ imbalance / 2` is continuous, swap-odd, balance-vanishing, and
unit-normalized, yet fails additivity (`nlP_unit_not_additive`). So even
adding debit-credit parity to the companions does not restore additivity
without a kinetic / EnergyEqualsCost-like hypothesis (which this module
refuses as input).

## (c) The sharper reduction: net-imbalance reading plus 1D Cauchy

Full two-argument additivity on `LedgerState` is stronger than what the
consumer needs as a named posting property. The strictly simpler package

1. **net-imbalance reading** `ReadsNetImbalance p`:
   `∀ z, p z = p (imbalance z, 0)`
   (cancelling a balanced debit-credit pair never changes the momentum),
2. **1D additivity on the debit axis**
   `∀ m n, p (m, 0) + p (n, 0) = p (m + n, 0)`,
3. continuity of `p`,
4. unit normalization `p (1, 0) ^ 2 = 1`,

already forces `p = ± imbalance`, hence full consolidation additivity, hence
`EnergyEqualsCost p`
(`energyEqualsCost_of_net_imbalance_reading_additive_unit`). Balance-vanishing
is derived, not assumed. This is the chart successor's remaining named input,
stated as a one-dimensional Cauchy problem on the net charge together with the
structural claim that momentum reads only that charge.

## What is NOT claimed

* No flag flip. Flags 6 and 12 still rest on `EnergyEqualsCost`; the premise
  is not discharged, because additivity (equivalently, the net-imbalance
  reading package) is not derived from the composition law.
* The no-go kills derivations from the composition law plus the consumer
  companions alone. It does not touch a derivation that imports a further
  non-cost structure of the ledger (for example a proof of
  `ReadsNetImbalance` from posting axioms).
* B1's kinetic-conditional additivity is neither used nor strengthened.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace MomentumAdditivityComposition

open ChartFromLedgerMomentum MomentumAdditivity MomentumMagnitudeBridge
open EnergyEqualsCostDerivation
open Cost.FunctionalEquation

noncomputable section

/-! ## §0. Ambient composition law on the stated carrier -/

/-- **The chart system's recognition cost satisfies the composition law.**
Imported from the symplectic derivation: σ = 0 area preservation supplies the
trace identity that is `SatisfiesCompositionLaw` for `Jcost`. -/
theorem chart_cost_satisfies_composition_law :
    SatisfiesCompositionLaw Cost.Jcost :=
  Cost.SymplecticAction.jcost_satisfiesCompositionLaw_via_symplectic

/-- The composition law is a property of the cost alone: it holds of `Jcost`
regardless of which momentum observable is under discussion. -/
theorem composition_law_ignores_momentum (_p : LedgerState → ℝ) :
    SatisfiesCompositionLaw Cost.Jcost :=
  chart_cost_satisfies_composition_law

/-! ## §1. Companions shared by the witness packages -/

theorem imbalance_unit : imbalance ((1, 0) : LedgerState) ^ 2 = 1 := by
  simp [imbalance]

theorem imbalance_balance_vanishing :
    ∀ z : LedgerState, Balanced z → imbalance z = 0 :=
  fun z hz => show imbalance z = 0 from sub_eq_zero.mpr hz

theorem abs_imbalance_continuous : Continuous fun z : LedgerState => |imbalance z| :=
  (continuous_fst.sub continuous_snd).abs

theorem abs_imbalance_balance_vanishing :
    ∀ z : LedgerState, Balanced z → |imbalance z| = 0 := by
  intro z hz
  simp [imbalance, show z.1 = z.2 from hz]

theorem abs_imbalance_unit :
    (fun z : LedgerState => |imbalance z|) (1, 0) ^ 2 = 1 := by
  simp [imbalance]

/-- Absolute imbalance fails consolidation additivity: consolidating a pure
debit with a pure credit yields the balanced state, whose absolute imbalance
is `0 ≠ 1 + 1`. -/
theorem abs_imbalance_not_additive :
    ¬ ∀ z w : LedgerState,
        |imbalance (z + w)| = |imbalance z| + |imbalance w| := by
  intro h
  have h1 := h (1, 0) (0, 1)
  have heq : ((1, 0) : LedgerState) + (0, 1) = (1, 1) := by
    apply Prod.ext <;> simp
  rw [heq] at h1
  norm_num [imbalance] at h1

/-! ## §2. The additive package, and the consumer fires -/

/-- **The additive package:** continuous, balance-vanishing, unit-normalized,
and additive. The consumer theorem therefore yields `EnergyEqualsCost`. -/
theorem imbalance_additive_package :
    Continuous imbalance ∧
      (∀ z : LedgerState, Balanced z → imbalance z = 0) ∧
      imbalance ((1, 0) : LedgerState) ^ 2 = 1 ∧
      (∀ z w : LedgerState, imbalance (z + w) = imbalance z + imbalance w) ∧
      EnergyEqualsCost imbalance :=
  ⟨continuous_imbalance, imbalance_balance_vanishing, imbalance_unit,
    fun z w => by simp [imbalance]; ring,
    energy_equals_cost_of_imbalance⟩

/-! ## §3. The non-additive package (absolute imbalance) -/

/-- **The absolute-imbalance package:** continuous, balance-vanishing,
unit-normalized, and *not* additive. Lives on the same carrier with the same
RCL cost as the additive package. -/
theorem abs_imbalance_package :
    Continuous (fun z : LedgerState => |imbalance z|) ∧
      (∀ z : LedgerState, Balanced z → |imbalance z| = 0) ∧
      (fun z : LedgerState => |imbalance z|) (1, 0) ^ 2 = 1 ∧
      ¬ (∀ z w : LedgerState,
          |imbalance (z + w)| = |imbalance z| + |imbalance w|) :=
  ⟨abs_imbalance_continuous, abs_imbalance_balance_vanishing, abs_imbalance_unit,
    abs_imbalance_not_additive⟩

/-! ## §4. Headline no-go (scoped to the stated system) -/

/-- **NO-GO (composition-law independence of additivity).** On the stated
`LedgerState` chart system whose recognition cost `Jcost` satisfies the
composition law, there exist two continuous, balance-vanishing,
unit-normalized momentum observables that disagree on consolidation
additivity: `imbalance` (additive, and therefore `EnergyEqualsCost`) and
`|imbalance|` (not additive). The composition law plus those three companions
therefore cannot force additivity on this system.

Quantifier written first: the theorem is a conjunction of (i) the ambient cost
satisfies RCL and (ii) two concrete packages on this one carrier. It is not a
∀-quantified statement over a class of cost systems. -/
theorem momentum_additivity_independent_of_composition_law :
    SatisfiesCompositionLaw Cost.Jcost ∧
    (Continuous imbalance ∧
      (∀ z : LedgerState, Balanced z → imbalance z = 0) ∧
      imbalance ((1, 0) : LedgerState) ^ 2 = 1 ∧
      (∀ z w : LedgerState, imbalance (z + w) = imbalance z + imbalance w) ∧
      EnergyEqualsCost imbalance) ∧
    (Continuous (fun z : LedgerState => |imbalance z|) ∧
      (∀ z : LedgerState, Balanced z → |imbalance z| = 0) ∧
      (fun z : LedgerState => |imbalance z|) (1, 0) ^ 2 = 1 ∧
      ¬ (∀ z w : LedgerState,
          |imbalance (z + w)| = |imbalance z| + |imbalance w|)) :=
  ⟨chart_cost_satisfies_composition_law, imbalance_additive_package,
    abs_imbalance_package⟩

/-! ## §5. Swap-odd sector: unit-normalized nlP also fails additivity -/

/-- Unit-normalized reparametrization of the imbalance through `nlP`. -/
def nlPUnit (z : LedgerState) : ℝ := nlP (imbalance z) / 2

theorem nlPUnit_continuous : Continuous nlPUnit := by
  have hb : Continuous fun z : LedgerState => imbalance z :=
    continuous_fst.sub continuous_snd
  exact ((hb.add (hb.pow 3)).div_const 2).congr fun z => by simp [nlPUnit, nlP]

theorem nlPUnit_swap_odd : SwapOdd nlPUnit := by
  intro z
  show nlP (imbalance (z.2, z.1)) / 2 = -(nlP (imbalance z) / 2)
  rw [imbalance_swap]
  simp [nlP]
  ring

theorem nlPUnit_balance_vanishing :
    ∀ z : LedgerState, Balanced z → nlPUnit z = 0 := by
  intro z hz
  have : imbalance z = 0 := sub_eq_zero.mpr hz
  simp [nlPUnit, nlP, this]

theorem nlPUnit_unit : nlPUnit (1, 0) ^ 2 = 1 := by
  norm_num [nlPUnit, nlP, imbalance]

theorem nlPUnit_not_additive :
    ¬ ∀ z w : LedgerState, nlPUnit (z + w) = nlPUnit z + nlPUnit w := by
  intro h
  have h1 := h (1, 0) (1, 0)
  have h2 : ((1, 0) : LedgerState) + (1, 0) = (2, 0) := by
    apply Prod.ext
    · simp; norm_num
    · simp
  rw [h2] at h1
  -- nlPUnit (2,0) = nlP 2 / 2 = (2+8)/2 = 5
  -- nlPUnit (1,0) + nlPUnit (1,0) = 1 + 1 = 2
  norm_num [nlPUnit, nlP, imbalance] at h1

/-- **Swap-odd witness.** Continuity, swap-oddness, balance-vanishing, and unit
normalization still leave room for a non-additive momentum (`nlPUnit`). Debit-
credit parity is not a substitute for the kinetic condition. -/
theorem nlPUnit_package :
    Continuous nlPUnit ∧ SwapOdd nlPUnit ∧
      (∀ z : LedgerState, Balanced z → nlPUnit z = 0) ∧
      nlPUnit (1, 0) ^ 2 = 1 ∧
      ¬ (∀ z w : LedgerState, nlPUnit (z + w) = nlPUnit z + nlPUnit w) :=
  ⟨nlPUnit_continuous, nlPUnit_swap_odd, nlPUnit_balance_vanishing, nlPUnit_unit,
    nlPUnit_not_additive⟩

/-! ## §6. Sharper reduction: net-imbalance reading + 1D Cauchy -/

/-- **Net-imbalance reading.** The momentum depends only on the net charge:
cancelling a balanced debit-credit pair leaves the observable unchanged.
Equivalent form: `p z = p (imbalance z, 0)`. -/
def ReadsNetImbalance (p : LedgerState → ℝ) : Prop :=
  ∀ z : LedgerState, p z = p (imbalance z, 0)

/-- 1D additivity of `p` along the pure-debit axis. -/
def AdditiveOnDebitAxis (p : LedgerState → ℝ) : Prop :=
  ∀ m n : ℝ, p (m, 0) + p (n, 0) = p (m + n, 0)

/-- Under net-imbalance reading and 1D additivity, balance-vanishing is derived. -/
theorem balance_vanishing_of_net_imbalance_reading
    {p : LedgerState → ℝ} (hread : ReadsNetImbalance p)
    (hadd1 : AdditiveOnDebitAxis p) :
    ∀ z : LedgerState, Balanced z → p z = 0 := by
  intro z hz
  have himb : imbalance z = 0 := sub_eq_zero.mpr hz
  have h0 : p (0, 0) = 0 := by
    have h := hadd1 0 0
    simp only [add_zero] at h
    linarith
  rw [hread, himb]
  exact h0

/-- Continuous additive maps `ℝ → ℝ` are multiplication by the value at `1`. -/
private theorem continuous_additive_real
    (f : ℝ → ℝ) (hadd : ∀ m n : ℝ, f (m + n) = f m + f n) (hcont : Continuous f) :
    ∀ m : ℝ, f m = m * f 1 := by
  have hzero : f 0 = 0 := by
    have h := hadd 0 0
    simp only [add_zero] at h
    linarith
  let F : ℝ →+ ℝ :=
    { toFun := f, map_zero' := hzero, map_add' := hadd }
  let L : ℝ →ₗ[ℝ] ℝ := F.toRealLinearMap hcont
  intro m
  have hL : L m = f m := rfl
  have h1 : L 1 = f 1 := rfl
  calc f m = L m := hL.symm
    _ = m • L 1 := by rw [← map_smul]; simp
    _ = m * f 1 := by rw [h1, smul_eq_mul]

/-- **The sharper discharge.** Net-imbalance reading, 1D debit-axis additivity,
continuity, and unit normalization force `p = ± imbalance`, hence full
consolidation additivity and `EnergyEqualsCost`. No kinetic hypothesis. -/
theorem energyEqualsCost_of_net_imbalance_reading_additive_unit
    (p : LedgerState → ℝ)
    (hread : ReadsNetImbalance p)
    (hadd1 : AdditiveOnDebitAxis p)
    (hcont : Continuous p)
    (hunit : p (1, 0) ^ 2 = 1) :
    (∀ z w : LedgerState, p (z + w) = p z + p w) ∧
      (∀ z : LedgerState, Balanced z → p z = 0) ∧
      EnergyEqualsCost p := by
  let f : ℝ → ℝ := fun m => p (m, 0)
  have hfadd : ∀ m n : ℝ, f (m + n) = f m + f n := fun m n => (hadd1 m n).symm
  have hfcont : Continuous f := by
    have hpath : Continuous fun m : ℝ => ((m, (0 : ℝ)) : LedgerState) :=
      Continuous.prodMk continuous_id continuous_const
    exact hcont.comp hpath
  have hfform := continuous_additive_real f hfadd hfcont
  have hform : ∀ z : LedgerState, p z = p (1, 0) * imbalance z := by
    intro z
    calc p z = p (imbalance z, 0) := hread z
      _ = f (imbalance z) := rfl
      _ = imbalance z * f 1 := hfform (imbalance z)
      _ = p (1, 0) * imbalance z := by simp [f]; ring
  have hadd : ∀ z w : LedgerState, p (z + w) = p z + p w := by
    intro z w
    rw [hform (z + w), hform z, hform w, imbalance_add]
    ring
  have hbal := balance_vanishing_of_net_imbalance_reading hread hadd1
  exact ⟨hadd, hbal,
    energyEqualsCost_of_additive_continuous_balanced_unit p hadd hcont hbal hunit⟩

/-- The imbalance itself inhabits the sharper package, so the reduction is not
vacuous. -/
theorem imbalance_reads_net_and_additive_on_axis :
    ReadsNetImbalance imbalance ∧ AdditiveOnDebitAxis imbalance ∧
      Continuous imbalance ∧ imbalance ((1, 0) : LedgerState) ^ 2 = 1 :=
  ⟨fun z => by simp [imbalance],
    fun m n => by
      have h := imbalance_add (m, (0 : ℝ)) (n, 0)
      -- h : imbalance ((m,0)+(n,0)) = imbalance (m,0) + imbalance (n,0)
      have heq : ((m, (0 : ℝ)) : LedgerState) + (n, 0) = (m + n, 0) := by
        apply Prod.ext
        · simp
        · simp
      rw [heq] at h
      exact h.symm,
    continuous_imbalance, imbalance_unit⟩

/-! ## §7. Certificate -/

/-- **The additivity-attack verdict, packaged.** (b): the ambient cost satisfies
RCL, and two companion-matching packages on this carrier disagree on
additivity; a swap-odd unit-normalized package also fails additivity. (c):
net-imbalance reading + 1D Cauchy + continuity + unit discharges full
additivity and `EnergyEqualsCost`. -/
structure MomentumAdditivityCompositionVerdict : Prop where
  ambient_cost_satisfies_rcl : SatisfiesCompositionLaw Cost.Jcost
  composition_law_independence :
    SatisfiesCompositionLaw Cost.Jcost ∧
    (Continuous imbalance ∧
      (∀ z : LedgerState, Balanced z → imbalance z = 0) ∧
      imbalance ((1, 0) : LedgerState) ^ 2 = 1 ∧
      (∀ z w : LedgerState, imbalance (z + w) = imbalance z + imbalance w) ∧
      EnergyEqualsCost imbalance) ∧
    (Continuous (fun z : LedgerState => |imbalance z|) ∧
      (∀ z : LedgerState, Balanced z → |imbalance z| = 0) ∧
      (fun z : LedgerState => |imbalance z|) (1, 0) ^ 2 = 1 ∧
      ¬ (∀ z w : LedgerState,
          |imbalance (z + w)| = |imbalance z| + |imbalance w|))
  swap_odd_unit_still_not_additive :
    Continuous nlPUnit ∧ SwapOdd nlPUnit ∧
      (∀ z : LedgerState, Balanced z → nlPUnit z = 0) ∧
      nlPUnit (1, 0) ^ 2 = 1 ∧
      ¬ (∀ z w : LedgerState, nlPUnit (z + w) = nlPUnit z + nlPUnit w)
  sufficient_net_imbalance_reading :
    ∀ p : LedgerState → ℝ, ReadsNetImbalance p → AdditiveOnDebitAxis p →
      Continuous p → p (1, 0) ^ 2 = 1 →
        (∀ z w : LedgerState, p (z + w) = p z + p w) ∧
          (∀ z : LedgerState, Balanced z → p z = 0) ∧
          EnergyEqualsCost p
  imbalance_inhabits_sharper_package :
    ReadsNetImbalance imbalance ∧ AdditiveOnDebitAxis imbalance ∧
      Continuous imbalance ∧ imbalance ((1, 0) : LedgerState) ^ 2 = 1

theorem momentumAdditivityCompositionVerdict :
    MomentumAdditivityCompositionVerdict where
  ambient_cost_satisfies_rcl := chart_cost_satisfies_composition_law
  composition_law_independence := momentum_additivity_independent_of_composition_law
  swap_odd_unit_still_not_additive := nlPUnit_package
  sufficient_net_imbalance_reading :=
    energyEqualsCost_of_net_imbalance_reading_additive_unit
  imbalance_inhabits_sharper_package := imbalance_reads_net_and_additive_on_axis

/-! ## Axiom audit -/

#print axioms chart_cost_satisfies_composition_law
#print axioms composition_law_ignores_momentum
#print axioms imbalance_unit
#print axioms abs_imbalance_not_additive
#print axioms imbalance_additive_package
#print axioms abs_imbalance_package
#print axioms momentum_additivity_independent_of_composition_law
#print axioms nlPUnit_continuous
#print axioms nlPUnit_swap_odd
#print axioms nlPUnit_not_additive
#print axioms nlPUnit_package
#print axioms balance_vanishing_of_net_imbalance_reading
#print axioms energyEqualsCost_of_net_imbalance_reading_additive_unit
#print axioms imbalance_reads_net_and_additive_on_axis
#print axioms momentumAdditivityCompositionVerdict

end
end MomentumAdditivityComposition
end SevenGaps
end Gravity
end IndisputableMonolith
