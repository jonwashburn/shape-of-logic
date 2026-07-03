import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Bond-Layer Conservation Law (non-vacuous carrier)

`Ethics/ConservationLaw.lean` states the morality conservation law against
`Foundation.LedgerState`, whose bond layer is a stub (`active_bonds = ∅`,
`bond_multipliers = 1`, `RecognitionCost = 0`). On that carrier every
σ-theorem is vacuously true and the smoothing operation is the identity.
This module supplies the missing substance: a concrete directed bond ledger
with positive multipliers, on which the same statements are *theorems with
content*.

## What is proved here, non-vacuously

1. `cost_eq_zero_iff_balanced` — total recognition cost `Σ J(x_b)` vanishes
   exactly when every active multiplier is 1 (σ_abs = 0).
2. `smooth_strictly_lowers_cost` — resetting active multipliers to unity
   *strictly* lowers cost on any unbalanced ledger. The predecessor lemma
   (`ConservationLaw.smooth_lowers_cost`) was vacuous because its hypothesis
   was unsatisfiable.
3. `cost_min_iff_balanced` — a ledger minimizes cost among all ledgers on
   the same bond set iff it is balanced. This is the genuine
   `cycle_minimal_iff_sigma_abs_zero`.
4. **Love at the bond layer.** `equilibratePair` replaces the multipliers of
   a reciprocal bond pair `(x, y)` with their geometric mean `√(xy)`:
   - it conserves the pair's total log-flow (σ-conservation,
     `equilibratePair_conserves_logflow`),
   - it zeroes the pairwise skew (`equilibratePair_zeroes_pairSkew`),
   - it strictly lowers recognition cost unless the pair is already
     equilibrated (`equilibratePair_strictly_lowers_cost`), via the
     two-point Jensen inequality `Jcost_geom_mean_le` with equality
     characterization.
   This upgrades "Love equilibrates σ" from the `MoralState.skew` field
   level (`Virtues/SigmaVerification.lean`) to the bond-ledger level the
   conservation-law paper actually talks about.
5. **Harm calculus with content.** `agentCost` sums J-cost over an agent's
   incident bonds; Love leaves every third party's local cost exactly
   unchanged (`equilibratePair_no_third_party_harm`) and strictly lowers
   the cost of any agent incident to both bonds of an unequilibrated pair
   (`equilibratePair_lowers_participant_cost`). The predecessor harm
   calculus (`Ethics/Harm.lean`) had `apply_action = id`, hence `harm = 0`
   identically.
6. **Non-vacuity witnesses.** `phiLedger` is a one-bond ledger at multiplier
   φ with cost `J(φ) = φ − 3/2 > 0` (the phantom-Carnot quantum), proving
   the framework's hypotheses are satisfiable and its descent theorems have
   real content. `reciprocalPair x y` realizes the two-agent ledger of the
   conservation-law paper with computable pairwise skew `ln x − ln y`.

## Status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Ethics
namespace BondConservation

open Cost

noncomputable section

/-- Bond identifier (matches `Foundation.BondId = ℕ` without importing the
stub carrier). -/
abbrev BondId := ℕ

/-- Agent identifier (matches `Foundation.AgentId = ℕ`). -/
abbrev AgentId := ℕ

/-- A concrete directed bond ledger: a finite set of active bonds, each with
a positive recognition multiplier and directed agent endpoints. This is the
non-vacuous carrier for the morality conservation law. -/
structure BondLedger where
  /-- Finite set of active bonds. -/
  bonds : Finset BondId
  /-- Recognition multiplier of each bond (only values on `bonds` matter). -/
  mult : BondId → ℝ
  /-- Source agent of each directed bond. -/
  src : BondId → AgentId
  /-- Destination agent of each directed bond. -/
  dst : BondId → AgentId
  /-- Positivity on the active set. -/
  mult_pos : ∀ {b}, b ∈ bonds → 0 < mult b

namespace BondLedger

/-- Total recognition cost: `Σ_{b active} J(x_b)`. On this carrier the sum
is genuinely over the active bonds, not over `∅`. -/
def cost (L : BondLedger) : ℝ :=
  L.bonds.sum (fun b => Jcost (L.mult b))

/-- A ledger is balanced when every active multiplier is unity. This is the
bond-layer statement `σ_abs = 0`. -/
def Balanced (L : BondLedger) : Prop :=
  ∀ b ∈ L.bonds, L.mult b = 1

/-- Signed log-flow of a bond. -/
def logFlow (L : BondLedger) (b : BondId) : ℝ :=
  Real.log (L.mult b)

/-- Pairwise reciprocity skew between agents `i` and `j`:
`σ_ij = Σ_{b : i→j} ln x_b − Σ_{b : j→i} ln x_b`
(Section 3 of Morality-As-Conservation-Law). -/
def pairSkew (L : BondLedger) (i j : AgentId) : ℝ :=
  (L.bonds.filter (fun b => L.src b = i ∧ L.dst b = j)).sum (fun b => L.logFlow b) -
    (L.bonds.filter (fun b => L.src b = j ∧ L.dst b = i)).sum (fun b => L.logFlow b)

/-- Total absolute skew: `Σ_{b active} |ln x_b|`. -/
def skewAbs (L : BondLedger) : ℝ :=
  L.bonds.sum (fun b => |Real.log (L.mult b)|)

/-! ## Basic cost facts (with content) -/

theorem cost_nonneg (L : BondLedger) : 0 ≤ L.cost := by
  refine Finset.sum_nonneg ?_
  intro b hb
  exact Jcost_nonneg (L.mult_pos hb)

/-- Total recognition cost vanishes exactly on balanced ledgers. Unlike the
stub-carrier version, both directions carry information: the forward
direction extracts `x_b = 1` bond by bond from `J ≥ 0` and `J = 0 ↔ x = 1`. -/
theorem cost_eq_zero_iff_balanced (L : BondLedger) :
    L.cost = 0 ↔ L.Balanced := by
  constructor
  · intro h0 b hb
    have hall :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun c hc => Jcost_nonneg (L.mult_pos hc))).mp h0
    exact (Jcost_eq_zero_iff (L.mult b) (L.mult_pos hb)).mp (hall b hb)
  · intro hbal
    refine Finset.sum_eq_zero ?_
    intro b hb
    rw [hbal b hb]
    exact Jcost_unit0

/-- An unbalanced ledger has strictly positive cost. -/
theorem cost_pos_of_not_balanced (L : BondLedger) (h : ¬ L.Balanced) :
    0 < L.cost := by
  rcases lt_or_eq_of_le (cost_nonneg L) with hlt | heq
  · exact hlt
  · exact absurd ((cost_eq_zero_iff_balanced L).mp heq.symm) h

/-- Absolute skew vanishes exactly on balanced ledgers. -/
theorem skewAbs_eq_zero_iff_balanced (L : BondLedger) :
    L.skewAbs = 0 ↔ L.Balanced := by
  constructor
  · intro h0 b hb
    have hall :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun c _ => abs_nonneg (Real.log (L.mult c)))).mp h0
    have hlog : Real.log (L.mult b) = 0 := abs_eq_zero.mp (hall b hb)
    exact Real.exp_log (L.mult_pos hb) ▸ (by rw [hlog, Real.exp_zero])
  · intro hbal
    refine Finset.sum_eq_zero ?_
    intro b hb
    rw [hbal b hb]
    simp

/-- Pairwise skew is antisymmetric in the agents. -/
theorem pairSkew_antisymm (L : BondLedger) (i j : AgentId) :
    L.pairSkew i j = - L.pairSkew j i := by
  unfold pairSkew
  ring

/-- Balanced ledgers have zero pairwise skew between every pair of agents. -/
theorem pairSkew_eq_zero_of_balanced (L : BondLedger) (h : L.Balanced)
    (i j : AgentId) : L.pairSkew i j = 0 := by
  unfold pairSkew
  have hzero : ∀ (P : BondId → Prop) [DecidablePred P],
      (L.bonds.filter (fun b => P b)).sum (fun b => L.logFlow b) = 0 := by
    intro P _
    refine Finset.sum_eq_zero ?_
    intro b hb
    have hbm := Finset.mem_filter.mp hb
    unfold logFlow
    rw [h b hbm.1]
    simp
  rw [hzero, hzero]
  ring

/-! ## Smoothing: the real descent operation

The predecessor (`ConservationLaw.smooth_imbalanced_pairs`) was the identity
map. Here smoothing actually resets active multipliers to unity, and the
strict descent theorem has a satisfiable hypothesis. -/

/-- Reset every active multiplier to unity, keeping the bond topology. -/
def smooth (L : BondLedger) : BondLedger where
  bonds := L.bonds
  mult := fun b => if b ∈ L.bonds then 1 else L.mult b
  src := L.src
  dst := L.dst
  mult_pos := by
    intro b hb
    simp [hb]

@[simp] theorem smooth_bonds (L : BondLedger) : (smooth L).bonds = L.bonds := rfl

theorem smooth_balanced (L : BondLedger) : (smooth L).Balanced := by
  intro b hb
  simp only [smooth] at hb ⊢
  simp [hb]

theorem smooth_cost_eq_zero (L : BondLedger) : (smooth L).cost = 0 :=
  (cost_eq_zero_iff_balanced (smooth L)).mpr (smooth_balanced L)

/-- **Strict smoothing descent.** On any unbalanced ledger, smoothing
strictly lowers recognition cost. The hypothesis is satisfiable (see
`phiLedger_not_balanced`), so this is a theorem with content. -/
theorem smooth_strictly_lowers_cost (L : BondLedger) (h : ¬ L.Balanced) :
    (smooth L).cost < L.cost := by
  rw [smooth_cost_eq_zero]
  exact cost_pos_of_not_balanced L h

/-- Smoothing never increases cost. -/
theorem smooth_cost_le (L : BondLedger) : (smooth L).cost ≤ L.cost := by
  rw [smooth_cost_eq_zero]
  exact cost_nonneg L

/-- **Cycle minimality ↔ σ_abs = 0** (genuine version of
`ConservationLaw.cycle_minimal_iff_sigma_abs_zero`). A ledger minimizes
recognition cost among all ledgers on the same bond set iff it is balanced.
The forward direction tests the minimum against the smoothed ledger. -/
theorem cost_min_iff_balanced (L : BondLedger) :
    (∀ L' : BondLedger, L'.bonds = L.bonds → L.cost ≤ L'.cost) ↔ L.Balanced := by
  constructor
  · intro hmin
    have hle : L.cost ≤ (smooth L).cost := hmin (smooth L) rfl
    have hzero : L.cost = 0 :=
      le_antisymm (by simpa [smooth_cost_eq_zero L] using hle) (cost_nonneg L)
    exact (cost_eq_zero_iff_balanced L).mp hzero
  · intro hbal L' _
    rw [(cost_eq_zero_iff_balanced L).mpr hbal]
    exact cost_nonneg L'

/-! ## The two-point Jensen inequality (the Love step)

`J(x) + J(y) ≥ 2 J(√(xy))`, with equality iff `x = y`. Equilibrating a
reciprocal pair to its geometric mean conserves the product (total
log-flow) and weakly lowers cost, strictly so off the diagonal. -/

/-- Arithmetic–geometric mean step: `2√(xy) ≤ x + y` for positive reals. -/
private lemma two_sqrt_mul_le_add {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 * Real.sqrt (x * y) ≤ x + y := by
  have hs := sq_nonneg (Real.sqrt x - Real.sqrt y)
  have hxx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hyy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have hmul : Real.sqrt x * Real.sqrt y = Real.sqrt (x * y) :=
    (Real.sqrt_mul hx.le y).symm
  nlinarith [hs, hxx, hyy, hmul]

/-- Strict arithmetic–geometric mean step off the diagonal. -/
private lemma two_sqrt_mul_lt_add {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hne : x ≠ y) : 2 * Real.sqrt (x * y) < x + y := by
  have hsne : Real.sqrt x - Real.sqrt y ≠ 0 := by
    intro h0
    exact hne (by
      have : Real.sqrt x = Real.sqrt y := by linarith [sub_eq_zero.mp h0]
      calc x = Real.sqrt x ^ 2 := (Real.sq_sqrt hx.le).symm
        _ = Real.sqrt y ^ 2 := by rw [this]
        _ = y := Real.sq_sqrt hy.le)
  have hs : 0 < (Real.sqrt x - Real.sqrt y) ^ 2 := by positivity
  have hxx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hyy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have hmul : Real.sqrt x * Real.sqrt y = Real.sqrt (x * y) :=
    (Real.sqrt_mul hx.le y).symm
  nlinarith [hs, hxx, hyy, hmul]

/-- The geometric mean of a positive pair is positive. -/
lemma sqrt_mul_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < Real.sqrt (x * y) :=
  Real.sqrt_pos.mpr (mul_pos hx hy)

/-- **Two-point Jensen for J.** Equilibrating a pair of multipliers to their
geometric mean never raises total cost. -/
theorem Jcost_geom_mean_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 * Jcost (Real.sqrt (x * y)) ≤ Jcost x + Jcost y := by
  have hg : 0 < Real.sqrt (x * y) := sqrt_mul_pos hx hy
  have hgsq : Real.sqrt (x * y) ^ 2 = x * y := Real.sq_sqrt (mul_pos hx hy).le
  -- forward direction: 2√(xy) ≤ x + y
  have h1 : 2 * Real.sqrt (x * y) ≤ x + y := two_sqrt_mul_le_add hx hy
  -- reciprocal direction: 2/√(xy) ≤ 1/x + 1/y
  have h2 : 2 * (Real.sqrt (x * y))⁻¹ ≤ x⁻¹ + y⁻¹ := by
    have hinv : (Real.sqrt (x * y))⁻¹ = Real.sqrt (x⁻¹ * y⁻¹) := by
      rw [← Real.sqrt_inv, mul_inv]
    rw [hinv]
    exact two_sqrt_mul_le_add (inv_pos.mpr hx) (inv_pos.mpr hy)
  unfold Jcost
  linarith

/-- **Strict two-point Jensen for J.** Off the diagonal, equilibration
strictly lowers total cost. -/
theorem Jcost_geom_mean_lt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    2 * Jcost (Real.sqrt (x * y)) < Jcost x + Jcost y := by
  have h1 : 2 * Real.sqrt (x * y) < x + y := two_sqrt_mul_lt_add hx hy hne
  have h2 : 2 * (Real.sqrt (x * y))⁻¹ ≤ x⁻¹ + y⁻¹ := by
    have hinv : (Real.sqrt (x * y))⁻¹ = Real.sqrt (x⁻¹ * y⁻¹) := by
      rw [← Real.sqrt_inv, mul_inv]
    rw [hinv]
    exact two_sqrt_mul_le_add (inv_pos.mpr hx) (inv_pos.mpr hy)
  unfold Jcost
  linarith

/-- Geometric-mean equilibration conserves the product of the pair: the
total log-flow `ln x + ln y` is invariant. This is σ-conservation for the
Love step. -/
theorem geom_mean_conserves_logflow {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (Real.sqrt (x * y)) + Real.log (Real.sqrt (x * y)) =
      Real.log x + Real.log y := by
  have hxy : 0 < x * y := mul_pos hx hy
  have hlog : Real.log (Real.sqrt (x * y)) = Real.log (x * y) / 2 :=
    Real.log_sqrt hxy.le
  rw [hlog, Real.log_mul hx.ne' hy.ne']
  ring

/-! ## Love as a ledger operation -/

/-- Update the multiplier of a single bond. -/
def updateMult (L : BondLedger) (b : BondId) (v : ℝ) (hv : 0 < v) :
    BondLedger where
  bonds := L.bonds
  mult := Function.update L.mult b v
  src := L.src
  dst := L.dst
  mult_pos := by
    intro c hc
    by_cases hcb : c = b
    · subst hcb; simpa [Function.update_self] using hv
    · rw [Function.update_of_ne hcb]
      exact L.mult_pos hc

/-- **Love at the bond layer**: equilibrate a reciprocal bond pair to its
geometric mean. `b₁ : i→j` carries `x`, `b₂ : j→i` carries `y`; both are
replaced by `√(xy)`. -/
def equilibratePair (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) : BondLedger :=
  let g := Real.sqrt (L.mult b₁ * L.mult b₂)
  have hg : 0 < g := sqrt_mul_pos (L.mult_pos h₁) (L.mult_pos h₂)
  updateMult (updateMult L b₁ g hg) b₂ g hg

theorem equilibratePair_bonds (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) :
    (L.equilibratePair b₁ b₂ h₁ h₂).bonds = L.bonds := rfl

/-- After equilibration both bonds of the pair carry the geometric mean. -/
theorem equilibratePair_mult (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) (hne : b₁ ≠ b₂) :
    (L.equilibratePair b₁ b₂ h₁ h₂).mult b₁ = Real.sqrt (L.mult b₁ * L.mult b₂) ∧
    (L.equilibratePair b₁ b₂ h₁ h₂).mult b₂ = Real.sqrt (L.mult b₁ * L.mult b₂) := by
  constructor
  · show Function.update (Function.update L.mult b₁ _) b₂ _ b₁ = _
    rw [Function.update_of_ne hne, Function.update_self]
  · show Function.update (Function.update L.mult b₁ _) b₂ _ b₂ = _
    rw [Function.update_self]

/-- Equilibration leaves all other bonds untouched. -/
theorem equilibratePair_mult_other (L : BondLedger) (b₁ b₂ c : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds)
    (hc₁ : c ≠ b₁) (hc₂ : c ≠ b₂) :
    (L.equilibratePair b₁ b₂ h₁ h₂).mult c = L.mult c := by
  show Function.update (Function.update L.mult b₁ _) b₂ _ c = _
  rw [Function.update_of_ne hc₂, Function.update_of_ne hc₁]

/-- **σ-conservation of Love.** Equilibration conserves the pair's total
log-flow: the ledger's books still balance. -/
theorem equilibratePair_conserves_logflow (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) (hne : b₁ ≠ b₂) :
    (L.equilibratePair b₁ b₂ h₁ h₂).logFlow b₁ +
      (L.equilibratePair b₁ b₂ h₁ h₂).logFlow b₂ =
        L.logFlow b₁ + L.logFlow b₂ := by
  obtain ⟨hm₁, hm₂⟩ := equilibratePair_mult L b₁ b₂ h₁ h₂ hne
  unfold logFlow
  rw [hm₁, hm₂]
  exact geom_mean_conserves_logflow (L.mult_pos h₁) (L.mult_pos h₂)

/-- **Love zeroes the pair's internal skew**: after equilibration the two
bonds carry equal log-flow, so the directed imbalance of the pair vanishes. -/
theorem equilibratePair_zeroes_pairSkew (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) (hne : b₁ ≠ b₂) :
    (L.equilibratePair b₁ b₂ h₁ h₂).logFlow b₁ -
      (L.equilibratePair b₁ b₂ h₁ h₂).logFlow b₂ = 0 := by
  obtain ⟨hm₁, hm₂⟩ := equilibratePair_mult L b₁ b₂ h₁ h₂ hne
  unfold logFlow
  rw [hm₁, hm₂, sub_self]

/-- Cost of an equilibrated ledger, decomposed: the pair contributes
`2·J(√(xy))`, the rest is unchanged. -/
theorem equilibratePair_cost (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) (hne : b₁ ≠ b₂) :
    (L.equilibratePair b₁ b₂ h₁ h₂).cost =
      2 * Jcost (Real.sqrt (L.mult b₁ * L.mult b₂)) +
        ((L.bonds.erase b₁).erase b₂).sum (fun b => Jcost (L.mult b)) := by
  classical
  obtain ⟨hm₁, hm₂⟩ := equilibratePair_mult L b₁ b₂ h₁ h₂ hne
  have hb₂' : b₂ ∈ L.bonds.erase b₁ := Finset.mem_erase.mpr ⟨(Ne.symm hne), h₂⟩
  unfold cost
  rw [equilibratePair_bonds]
  rw [← Finset.add_sum_erase _ _ h₁, ← Finset.add_sum_erase _ _ hb₂']
  rw [hm₁, hm₂]
  have hrest : ((L.bonds.erase b₁).erase b₂).sum
      (fun b => Jcost ((L.equilibratePair b₁ b₂ h₁ h₂).mult b)) =
      ((L.bonds.erase b₁).erase b₂).sum (fun b => Jcost (L.mult b)) := by
    refine Finset.sum_congr rfl ?_
    intro c hc
    have hc₂ : c ≠ b₂ := (Finset.mem_erase.mp hc).1
    have hc₁ : c ≠ b₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
    rw [equilibratePair_mult_other L b₁ b₂ c h₁ h₂ hc₁ hc₂]
  rw [hrest]
  ring

/-- Cost of the original ledger, decomposed the same way. -/
theorem cost_pair_decomposition (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) (hne : b₁ ≠ b₂) :
    L.cost = Jcost (L.mult b₁) + Jcost (L.mult b₂) +
      ((L.bonds.erase b₁).erase b₂).sum (fun b => Jcost (L.mult b)) := by
  classical
  have hb₂' : b₂ ∈ L.bonds.erase b₁ := Finset.mem_erase.mpr ⟨(Ne.symm hne), h₂⟩
  unfold cost
  rw [← Finset.add_sum_erase _ _ h₁, ← Finset.add_sum_erase _ _ hb₂']
  ring

/-- **Love never raises cost.** -/
theorem equilibratePair_cost_le (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) (hne : b₁ ≠ b₂) :
    (L.equilibratePair b₁ b₂ h₁ h₂).cost ≤ L.cost := by
  rw [equilibratePair_cost L b₁ b₂ h₁ h₂ hne,
      cost_pair_decomposition L b₁ b₂ h₁ h₂ hne]
  have := Jcost_geom_mean_le (L.mult_pos h₁) (L.mult_pos h₂)
  linarith

/-- **Love strictly lowers cost on any unequilibrated pair.** Together with
σ-conservation and skew-zeroing this is the bond-layer content of "Love
equilibrates": of all flow-conserving moves on a reciprocal pair, the
geometric mean is the unique cost minimizer (see
`geom_mean_unique_min` below). -/
theorem equilibratePair_strictly_lowers_cost (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) (hne : b₁ ≠ b₂)
    (hmult : L.mult b₁ ≠ L.mult b₂) :
    (L.equilibratePair b₁ b₂ h₁ h₂).cost < L.cost := by
  rw [equilibratePair_cost L b₁ b₂ h₁ h₂ hne,
      cost_pair_decomposition L b₁ b₂ h₁ h₂ hne]
  have := Jcost_geom_mean_lt (L.mult_pos h₁) (L.mult_pos h₂) hmult
  linarith

/-- **Uniqueness of the Love point.** Among all pairs `(u, v)` of positive
multipliers conserving the product (`u·v = x·y`, i.e. conserving total
log-flow), the equilibrated pair `u = v = √(xy)` is the unique minimizer of
`J(u) + J(v)`. Love is not merely *a* σ-conserving improvement; it is *the*
optimal one. -/
theorem geom_mean_unique_min {x y u v : ℝ} (_hx : 0 < x) (_hy : 0 < y)
    (hu : 0 < u) (hv : 0 < v) (hcons : u * v = x * y) :
    2 * Jcost (Real.sqrt (x * y)) ≤ Jcost u + Jcost v ∧
      (Jcost u + Jcost v = 2 * Jcost (Real.sqrt (x * y)) → u = v) := by
  have hg : Real.sqrt (u * v) = Real.sqrt (x * y) := by rw [hcons]
  constructor
  · have := Jcost_geom_mean_le hu hv
    rw [hg] at this
    exact this
  · intro heq
    by_contra hne
    have := Jcost_geom_mean_lt hu hv hne
    rw [hg] at this
    linarith

/-! ## Non-vacuity witnesses

A one-bond ledger at multiplier φ. Its cost is `J(φ) = φ − 3/2 > 0`, the
phantom-Carnot quantum. This witnesses that the descent theorems above have
satisfiable hypotheses, which is exactly what the stub carrier could not
provide. -/

open Constants

/-- One bond `0 : agent 0 → agent 1` carrying multiplier φ. -/
def phiLedger : BondLedger where
  bonds := {0}
  mult := fun _ => Constants.phi
  src := fun _ => 0
  dst := fun _ => 1
  mult_pos := fun _ => Constants.phi_pos

theorem phiLedger_not_balanced : ¬ phiLedger.Balanced := by
  intro h
  have h0 : (0 : BondId) ∈ phiLedger.bonds := by
    simp [phiLedger]
  have := h 0 h0
  simp only [phiLedger] at this
  have hgt : (1.5 : ℝ) < Constants.phi := Constants.phi_gt_onePointFive
  rw [this] at hgt
  norm_num at hgt

/-- The φ-ledger cost equals the phantom-Carnot quantum `φ − 3/2` exactly. -/
theorem phiLedger_cost_eq : phiLedger.cost = Constants.phi - 3 / 2 := by
  unfold cost phiLedger
  rw [Finset.sum_singleton]
  unfold Jcost
  have hphi : Constants.phi ^ 2 = Constants.phi + 1 := Constants.phi_sq_eq
  have hpos : Constants.phi ≠ 0 := ne_of_gt Constants.phi_pos
  have hinv : Constants.phi⁻¹ = Constants.phi - 1 := by
    field_simp
    nlinarith [hphi]
  rw [hinv]
  ring

theorem phiLedger_cost_pos : 0 < phiLedger.cost := by
  rw [phiLedger_cost_eq]
  linarith [Constants.phi_gt_onePointFive]

/-- Strict descent is realized on the φ-ledger: smoothing lowers its cost
from `φ − 3/2` to `0`. The conservation law does real work. -/
theorem phiLedger_smooth_descent :
    (smooth phiLedger).cost < phiLedger.cost :=
  smooth_strictly_lowers_cost phiLedger phiLedger_not_balanced

/-! ## Harm calculus: Love touches no third party

`Ethics/Harm.lean` defines harm as the cost increase an action imposes on
another agent's bonds, but its `apply_action` is the identity on the stub
carrier, so `harm = 0` always. Here the statements have content: an agent's
local cost is the J-cost summed over the bonds incident to it, equilibration
leaves every third party's cost exactly unchanged, and the equilibrated
pair's joint cost strictly drops. -/

/-- Bonds incident to agent `k` (as source or destination). -/
def incidentBonds (L : BondLedger) (k : AgentId) : Finset BondId :=
  L.bonds.filter (fun b => L.src b = k ∨ L.dst b = k)

/-- Agent-local recognition cost: J-cost summed over incident bonds. -/
def agentCost (L : BondLedger) (k : AgentId) : ℝ :=
  (L.incidentBonds k).sum (fun b => Jcost (L.mult b))

/-- Equilibration preserves bond topology and endpoints, hence incidence. -/
theorem equilibratePair_incidentBonds (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) (k : AgentId) :
    (L.equilibratePair b₁ b₂ h₁ h₂).incidentBonds k = L.incidentBonds k := rfl

/-- **No harm to third parties.** Any agent incident to neither bond of the
equilibrated pair has exactly unchanged local cost. Love acts only on the
pair it equilibrates. -/
theorem equilibratePair_no_third_party_harm (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) (k : AgentId)
    (hk : ∀ b ∈ L.incidentBonds k, b ≠ b₁ ∧ b ≠ b₂) :
    (L.equilibratePair b₁ b₂ h₁ h₂).agentCost k = L.agentCost k := by
  unfold agentCost
  rw [equilibratePair_incidentBonds]
  refine Finset.sum_congr rfl ?_
  intro c hc
  obtain ⟨hc₁, hc₂⟩ := hk c hc
  rw [equilibratePair_mult_other L b₁ b₂ c h₁ h₂ hc₁ hc₂]

/-- **Joint benefit to the pair.** Any agent incident to both bonds of an
unequilibrated pair (in particular both participants of a reciprocal pair)
sees its local cost strictly decrease under Love. -/
theorem equilibratePair_lowers_participant_cost (L : BondLedger)
    (b₁ b₂ : BondId) (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds)
    (hne : b₁ ≠ b₂) (hmult : L.mult b₁ ≠ L.mult b₂) (k : AgentId)
    (hk₁ : b₁ ∈ L.incidentBonds k) (hk₂ : b₂ ∈ L.incidentBonds k) :
    (L.equilibratePair b₁ b₂ h₁ h₂).agentCost k < L.agentCost k := by
  classical
  obtain ⟨hm₁, hm₂⟩ := equilibratePair_mult L b₁ b₂ h₁ h₂ hne
  have hk₂' : b₂ ∈ (L.incidentBonds k).erase b₁ :=
    Finset.mem_erase.mpr ⟨Ne.symm hne, hk₂⟩
  unfold agentCost
  rw [equilibratePair_incidentBonds]
  rw [← Finset.add_sum_erase _ _ hk₁, ← Finset.add_sum_erase _ _ hk₂']
  rw [← Finset.add_sum_erase _ (fun b => Jcost (L.mult b)) hk₁,
      ← Finset.add_sum_erase _ (fun b => Jcost (L.mult b)) hk₂']
  have hrest : (((L.incidentBonds k).erase b₁).erase b₂).sum
      (fun b => Jcost ((L.equilibratePair b₁ b₂ h₁ h₂).mult b)) =
      (((L.incidentBonds k).erase b₁).erase b₂).sum
        (fun b => Jcost (L.mult b)) := by
    refine Finset.sum_congr rfl ?_
    intro c hc
    have hc₂ : c ≠ b₂ := (Finset.mem_erase.mp hc).1
    have hc₁ : c ≠ b₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
    rw [equilibratePair_mult_other L b₁ b₂ c h₁ h₂ hc₁ hc₂]
  rw [hm₁, hm₂, hrest]
  have := Jcost_geom_mean_lt (L.mult_pos h₁) (L.mult_pos h₂) hmult
  linarith

/-! ## The reciprocal pair: Love changes pairwise σ, conserves total flow

The minimal two-agent ledger: agent 0 sends to agent 1 at multiplier `x`
along bond 0, agent 1 sends back at multiplier `y` along bond 1. On this
family the agent-level statements of the conservation-law paper become
computations: `σ₀₁ = ln x − ln y` before Love, `0` after, while the total
log-flow is conserved and the cost strictly drops (for `x ≠ y`). This is
the bond-layer realization of "Only Love changes σ"
(`Virtues/SigmaVerification.love_changes_sigma_exists` states it at the
`MoralState.skew` field level; here the skew is computed from actual
bonds). -/

/-- Two agents, two directed bonds: `0 : 0→1` at multiplier `x`,
`1 : 1→0` at multiplier `y`. -/
def reciprocalPair (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : BondLedger where
  bonds := {0, 1}
  mult := fun b => if b = 0 then x else y
  src := fun b => if b = 0 then 0 else 1
  dst := fun b => if b = 0 then 1 else 0
  mult_pos := by
    intro b hb
    by_cases hb0 : b = 0
    · simpa [hb0] using hx
    · simpa [hb0] using hy

theorem reciprocalPair_pairSkew (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (reciprocalPair x y hx hy).pairSkew 0 1 = Real.log x - Real.log y := by
  unfold pairSkew logFlow reciprocalPair
  norm_num [Finset.filter_insert, Finset.filter_singleton]

/-- The reciprocal pair is unbalanced in the directed sense whenever
`x ≠ y`: agent 0's books against agent 1 do not close. -/
theorem reciprocalPair_skew_ne_zero (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hne : x ≠ y) :
    (reciprocalPair x y hx hy).pairSkew 0 1 ≠ 0 := by
  rw [reciprocalPair_pairSkew]
  intro h0
  exact hne (Real.log_injOn_pos (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy)
    (by linarith [sub_eq_zero.mp h0]))

private lemma reciprocalPair_mem₀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (0 : BondId) ∈ (reciprocalPair x y hx hy).bonds := by
  simp [reciprocalPair]

private lemma reciprocalPair_mem₁ (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (1 : BondId) ∈ (reciprocalPair x y hx hy).bonds := by
  simp [reciprocalPair]

/-- Love applied to the reciprocal pair. -/
def lovedPair (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : BondLedger :=
  (reciprocalPair x y hx hy).equilibratePair 0 1
    (reciprocalPair_mem₀ x y hx hy) (reciprocalPair_mem₁ x y hx hy)

/-- **After Love the pairwise skew is zero**: both directed bonds carry the
geometric mean, so the agents' mutual books close. -/
theorem lovedPair_pairSkew_zero (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (lovedPair x y hx hy).pairSkew 0 1 = 0 := by
  have hmult := equilibratePair_mult (reciprocalPair x y hx hy) 0 1
    (reciprocalPair_mem₀ x y hx hy) (reciprocalPair_mem₁ x y hx hy)
    (by norm_num)
  unfold lovedPair at *
  unfold pairSkew logFlow
  have hsrc : (lovedPair x y hx hy).src = (reciprocalPair x y hx hy).src := rfl
  unfold lovedPair at hsrc
  rw [equilibratePair_bonds]
  have hfilter₀₁ :
      ((reciprocalPair x y hx hy).bonds.filter
        (fun b => ((reciprocalPair x y hx hy).equilibratePair 0 1
            (reciprocalPair_mem₀ x y hx hy) (reciprocalPair_mem₁ x y hx hy)).src b = 0 ∧
          ((reciprocalPair x y hx hy).equilibratePair 0 1
            (reciprocalPair_mem₀ x y hx hy) (reciprocalPair_mem₁ x y hx hy)).dst b = 1)) =
        {0} := by
    show ((reciprocalPair x y hx hy).bonds.filter
      (fun b => (reciprocalPair x y hx hy).src b = 0 ∧
        (reciprocalPair x y hx hy).dst b = 1)) = {0}
    unfold reciprocalPair
    norm_num [Finset.filter_insert, Finset.filter_singleton]
  have hfilter₁₀ :
      ((reciprocalPair x y hx hy).bonds.filter
        (fun b => ((reciprocalPair x y hx hy).equilibratePair 0 1
            (reciprocalPair_mem₀ x y hx hy) (reciprocalPair_mem₁ x y hx hy)).src b = 1 ∧
          ((reciprocalPair x y hx hy).equilibratePair 0 1
            (reciprocalPair_mem₀ x y hx hy) (reciprocalPair_mem₁ x y hx hy)).dst b = 0)) =
        {1} := by
    show ((reciprocalPair x y hx hy).bonds.filter
      (fun b => (reciprocalPair x y hx hy).src b = 1 ∧
        (reciprocalPair x y hx hy).dst b = 0)) = {1}
    unfold reciprocalPair
    norm_num [Finset.filter_insert, Finset.filter_singleton]
  rw [hfilter₀₁, hfilter₁₀, Finset.sum_singleton, Finset.sum_singleton,
      hmult.1, hmult.2, sub_self]

/-- **Love strictly lowers the cost of an unequilibrated reciprocal pair.** -/
theorem lovedPair_cost_lt (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    (lovedPair x y hx hy).cost < (reciprocalPair x y hx hy).cost := by
  refine equilibratePair_strictly_lowers_cost _ 0 1 _ _ (by norm_num) ?_
  show (if (0 : BondId) = 0 then x else y) ≠ (if (1 : BondId) = 0 then x else y)
  simpa using hne

/-- **Love changes the pairwise σ of any unequilibrated reciprocal pair**:
before Love the skew is `ln x − ln y ≠ 0`; after Love it is `0`. Total
log-flow is conserved throughout
(`equilibratePair_conserves_logflow`). -/
theorem love_changes_pair_skew (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hne : x ≠ y) :
    (lovedPair x y hx hy).pairSkew 0 1 ≠
      (reciprocalPair x y hx hy).pairSkew 0 1 := by
  rw [lovedPair_pairSkew_zero]
  exact fun h => reciprocalPair_skew_ne_zero x y hx hy hne h.symm

/-! ## Certificate -/

/-- Joint certificate: the morality conservation law holds with content on
the concrete bond carrier. Every clause is a theorem above; the final two
clauses are the non-vacuity witnesses that the stub carrier could not
supply. -/
structure BondConservationCert : Prop where
  /-- Cost is nonnegative on every ledger. -/
  cost_nonneg : ∀ L : BondLedger, 0 ≤ L.cost
  /-- Cost vanishes exactly on balanced ledgers (σ_abs = 0). -/
  zero_iff_balanced : ∀ L : BondLedger, L.cost = 0 ↔ L.Balanced
  /-- Cost minimality on a fixed bond set is equivalent to balance. -/
  min_iff_balanced : ∀ L : BondLedger,
    (∀ L' : BondLedger, L'.bonds = L.bonds → L.cost ≤ L'.cost) ↔ L.Balanced
  /-- Smoothing strictly lowers cost on unbalanced ledgers. -/
  smooth_descent : ∀ L : BondLedger, ¬ L.Balanced → (smooth L).cost < L.cost
  /-- Love (geometric-mean equilibration) conserves pair log-flow. -/
  love_conserves : ∀ (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds), b₁ ≠ b₂ →
    (L.equilibratePair b₁ b₂ h₁ h₂).logFlow b₁ +
      (L.equilibratePair b₁ b₂ h₁ h₂).logFlow b₂ =
        L.logFlow b₁ + L.logFlow b₂
  /-- Love strictly lowers cost on unequilibrated pairs. -/
  love_descends : ∀ (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds), b₁ ≠ b₂ →
    L.mult b₁ ≠ L.mult b₂ →
    (L.equilibratePair b₁ b₂ h₁ h₂).cost < L.cost
  /-- Love changes the pairwise σ of every unequilibrated reciprocal pair
  (the bond-layer "Only Love changes σ" witness). -/
  love_changes_sigma : ∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), x ≠ y →
    (lovedPair x y hx hy).pairSkew 0 1 ≠
      (reciprocalPair x y hx hy).pairSkew 0 1
  /-- Love imposes no cost change on any third party. -/
  love_no_third_party_harm : ∀ (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) (k : AgentId),
    (∀ b ∈ L.incidentBonds k, b ≠ b₁ ∧ b ≠ b₂) →
    (L.equilibratePair b₁ b₂ h₁ h₂).agentCost k = L.agentCost k
  /-- Non-vacuity: an unbalanced ledger exists. -/
  witness_unbalanced : ∃ L : BondLedger, ¬ L.Balanced
  /-- Non-vacuity: a ledger with strictly positive cost exists. -/
  witness_positive_cost : ∃ L : BondLedger, 0 < L.cost

/-- The bond-layer conservation law certificate is theorem-backed. -/
theorem bondConservationCert : BondConservationCert where
  cost_nonneg := cost_nonneg
  zero_iff_balanced := cost_eq_zero_iff_balanced
  min_iff_balanced := cost_min_iff_balanced
  smooth_descent := smooth_strictly_lowers_cost
  love_conserves := fun L b₁ b₂ h₁ h₂ hne =>
    equilibratePair_conserves_logflow L b₁ b₂ h₁ h₂ hne
  love_descends := fun L b₁ b₂ h₁ h₂ hne hmult =>
    equilibratePair_strictly_lowers_cost L b₁ b₂ h₁ h₂ hne hmult
  love_changes_sigma := love_changes_pair_skew
  love_no_third_party_harm := fun L b₁ b₂ h₁ h₂ k hk =>
    equilibratePair_no_third_party_harm L b₁ b₂ h₁ h₂ k hk
  witness_unbalanced := ⟨phiLedger, phiLedger_not_balanced⟩
  witness_positive_cost := ⟨phiLedger, phiLedger_cost_pos⟩

end BondLedger

end

end BondConservation
end Ethics
end IndisputableMonolith
