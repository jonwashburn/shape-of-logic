import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.Ethics.BondConservation

/-!
# The Seam Floor: Bond Persistence, Market Clearing, Seam Origination

Three theorems closing the gap named in
`economics/True_Economics_Floor_20260610.html` between "the floor of
economics is defined and instrumented" and "the floor is forced."

## 1. Bond persistence (credit is unavoidable)

A bounded recognizer settles at most one posting per tick (T2
serialization; see `Foundation/Atomicity.lean` for the constructive
one-per-tick schedule). If cumulative posting demand exceeds elapsed
ticks, the open-bond set is nonempty at every tick:
`bond_persistence`. Sufficient condition: demand of two or more
postings per tick (`demand_two_forces_excess`, the minimal seam
configuration: one posting on each side of a cut).

## 2. Economics H-theorem (market clearing)

On the non-vacuous bond carrier `Ethics.BondConservation.BondLedger`:

* `equilibratePair_totalLogFlow`: local pair settlement conserves the
  ledger's total log-flow (σ-conservation of the local move).
* `marketClear`: the global σ-conserving relaxation, sending every
  active multiplier to the ledger's geometric mean.
* `marketClear_totalLogFlow`: the relaxation conserves total log-flow.
* `marketClear_cost_le` (n-point Jensen via `convexOn_cosh`):
  relaxation never raises recognition cost.
* `marketClear_cost_lt`: strictly lowers it on any non-uniform ledger.
* `marketClear_uniform`, `marketClear_idem`: the relaxed state is
  uniform and is a fixed point (convergence, with J strictly
  decreasing en route).
* `exists_improving_pair_iff_not_uniform`: the fixed points of the
  *local* settlement dynamics are exactly the uniform ledgers; on any
  non-uniform ledger some pair trade strictly lowers J.
* `marketClear_balanced_iff`: the cleared state is fully balanced
  (σ_abs = 0) iff the ledger's total log-flow is zero. Markets clear
  to balance exactly on globally σ-zero books; otherwise they clear to
  the uniform spread of the residual.

## 3. Seam origination (the economy exists)

* `bond_posts_two_ledgers`: every directed bond between distinct
  agents is incident to exactly the two parties: a posting's conjugate
  lives on someone else's books (two-sidedness, packaged).
* `pairSkew_single_bond`: a lone unbalanced bond between two agents is
  a seam carrying nonzero skew.
* `cost_pos_of_seam`: nonzero seam skew forces strictly positive
  recognition cost. Skew across a seam is priced, by J, always.
* `economy_exists`: there is a ledger with two distinct agents, a
  nonzero seam skew between them, and positive cost (witness: the
  φ-bond ledger). "The economy exists" is a theorem.

Certificate: `SeamFloor.seamFloorCert`.

Status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith

/-! ## Part 1: Bond persistence -/

namespace Economics
namespace Recognition
namespace SeamFloor

/-- Cumulative posting demand through tick `t` (ticks `0..t`). -/
def cumDemand (d : ℕ → ℕ) (t : ℕ) : ℕ :=
  ∑ s ∈ Finset.range (t + 1), d s

/-- A serial settlement process against posting demand `d`: cumulative
settlements through tick `t`, bounded by one settlement per tick
(serialization, T2) and by the postings actually opened. -/
structure SerialSettlement (d : ℕ → ℕ) where
  /-- Cumulative postings settled by end of tick `t`. -/
  settled : ℕ → ℕ
  /-- One settlement per tick: ticks `0..t` are `t + 1` ticks. -/
  capacity : ∀ t, settled t ≤ t + 1
  /-- Cannot settle postings that were never opened. -/
  feasible : ∀ t, settled t ≤ cumDemand d t

/-- Open bonds at tick `t`: postings opened but not yet settled. -/
def openBonds (d : ℕ → ℕ) (S : SerialSettlement d) (t : ℕ) : ℕ :=
  cumDemand d t - S.settled t

/-- **Bond persistence.** If cumulative demand strictly exceeds serial
capacity at every tick, the open-bond set is nonempty at every tick,
for every admissible settlement policy. Credit is not chosen; it is
the unavoidable bookkeeping state of finite serial recognizers. -/
theorem bond_persistence {d : ℕ → ℕ} (S : SerialSettlement d)
    (hdemand : ∀ t, t + 1 < cumDemand d t) :
    ∀ t, 0 < openBonds d S t := by
  intro t
  have h1 : S.settled t ≤ t + 1 := S.capacity t
  have h2 : t + 1 < cumDemand d t := hdemand t
  unfold openBonds
  omega

/-- Two postings per tick already exceed serial capacity cumulatively.
This is the minimal seam configuration: one posting opened on each
side of a cut, against one settlement slot. -/
theorem demand_two_forces_excess {d : ℕ → ℕ} (h2 : ∀ s, 2 ≤ d s) :
    ∀ t, t + 1 < cumDemand d t := by
  intro t
  have hsum : 2 * (t + 1) ≤ cumDemand d t := by
    calc 2 * (t + 1)
        = ∑ _s ∈ Finset.range (t + 1), 2 := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
      _ ≤ ∑ s ∈ Finset.range (t + 1), d s :=
          Finset.sum_le_sum (fun s _ => h2 s)
  unfold cumDemand at *
  omega

/-- **Credit is unavoidable** under the minimal seam demand: any
population posting at least two recognitions per tick against serial
settlement holds a nonempty open-bond set at every tick. -/
theorem credit_unavoidable {d : ℕ → ℕ} (h2 : ∀ s, 2 ≤ d s)
    (S : SerialSettlement d) : ∀ t, 0 < openBonds d S t :=
  bond_persistence S (demand_two_forces_excess h2)

end SeamFloor
end Recognition
end Economics

/-! ## Part 2: Economics H-theorem (market clearing on the bond ledger) -/

namespace Ethics
namespace BondConservation
namespace BondLedger

open Cost

noncomputable section

/-- `cosh` is convex on ℝ (sum of two convex exponentials). -/
private lemma convexOn_cosh : ConvexOn ℝ Set.univ Real.cosh := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hx1 := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have hx2 := convexOn_exp.2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) ha hb hab
  simp only [smul_eq_mul] at hx1 hx2 ⊢
  rw [Real.cosh_eq, Real.cosh_eq, Real.cosh_eq]
  have hneg : a * -x + b * -y = -(a * x + b * y) := by ring
  rw [hneg] at hx2
  linarith

/-- `J` in log coordinates: `J(x) = cosh(ln x) − 1` for positive `x`. -/
private lemma Jcost_eq_cosh_log {x : ℝ} (hx : 0 < x) :
    Jcost x = Real.cosh (Real.log x) - 1 := by
  have h : Real.cosh (Real.log x) = (x + x⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_log hx, Real.exp_neg, Real.exp_log hx]
  unfold Jcost
  rw [h]

/-- Total log-flow of a ledger: `Σ_{b active} ln x_b`. The conserved
quantity of every σ-conserving settlement move. -/
def totalLogFlow (L : BondLedger) : ℝ :=
  L.bonds.sum (fun b => L.logFlow b)

/-- **Local settlement conserves total log-flow.** Pair equilibration
changes only the two bonds it touches, and their joint log-flow is
invariant; hence the ledger total is invariant. σ-conservation of the
local market move. -/
theorem equilibratePair_totalLogFlow (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) (hne : b₁ ≠ b₂) :
    (L.equilibratePair b₁ b₂ h₁ h₂).totalLogFlow = L.totalLogFlow := by
  classical
  have hb₂' : b₂ ∈ L.bonds.erase b₁ := Finset.mem_erase.mpr ⟨Ne.symm hne, h₂⟩
  have hpair := equilibratePair_conserves_logflow L b₁ b₂ h₁ h₂ hne
  have hrest : ((L.bonds.erase b₁).erase b₂).sum
      (fun b => (L.equilibratePair b₁ b₂ h₁ h₂).logFlow b) =
      ((L.bonds.erase b₁).erase b₂).sum (fun b => L.logFlow b) := by
    refine Finset.sum_congr rfl ?_
    intro c hc
    have hc₂ : c ≠ b₂ := (Finset.mem_erase.mp hc).1
    have hc₁ : c ≠ b₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
    show Real.log ((L.equilibratePair b₁ b₂ h₁ h₂).mult c) = Real.log (L.mult c)
    rw [equilibratePair_mult_other L b₁ b₂ c h₁ h₂ hc₁ hc₂]
  unfold totalLogFlow
  rw [show (L.equilibratePair b₁ b₂ h₁ h₂).bonds = L.bonds from rfl]
  rw [← Finset.add_sum_erase _ _ h₁, ← Finset.add_sum_erase _ _ hb₂']
  rw [← Finset.add_sum_erase _ (fun b => L.logFlow b) h₁,
      ← Finset.add_sum_erase _ (fun b => L.logFlow b) hb₂']
  rw [hrest]
  linarith [hpair]

/-- Geometric mean of the active multipliers (in log coordinates: the
mean log-flow, exponentiated). -/
def geoMean (L : BondLedger) : ℝ :=
  Real.exp (L.totalLogFlow / (L.bonds.card : ℝ))

lemma geoMean_pos (L : BondLedger) : 0 < L.geoMean := Real.exp_pos _

/-- **Market clearing**: the global σ-conserving relaxation. Every
active multiplier is sent to the ledger's geometric mean. -/
def marketClear (L : BondLedger) : BondLedger where
  bonds := L.bonds
  mult := fun b => if b ∈ L.bonds then L.geoMean else L.mult b
  src := L.src
  dst := L.dst
  mult_pos := by
    intro b hb
    have hb' : b ∈ L.bonds := hb
    simp only [if_pos hb']
    exact L.geoMean_pos

@[simp] theorem marketClear_bonds (L : BondLedger) :
    (marketClear L).bonds = L.bonds := rfl

theorem marketClear_mult (L : BondLedger) {b : BondId} (hb : b ∈ L.bonds) :
    (marketClear L).mult b = L.geoMean := by
  show (if b ∈ L.bonds then L.geoMean else L.mult b) = L.geoMean
  rw [if_pos hb]

/-- A ledger is uniform when all active multipliers agree. The rest
state of the settlement dynamics. -/
def UniformMult (L : BondLedger) : Prop :=
  ∀ b₁ ∈ L.bonds, ∀ b₂ ∈ L.bonds, L.mult b₁ = L.mult b₂

/-- The cleared ledger is uniform. -/
theorem marketClear_uniform (L : BondLedger) : UniformMult (marketClear L) := by
  intro b₁ hb₁ b₂ hb₂
  have h₁ : b₁ ∈ L.bonds := hb₁
  have h₂ : b₂ ∈ L.bonds := hb₂
  rw [marketClear_mult L h₁, marketClear_mult L h₂]

/-- Market clearing conserves total log-flow: it is a lawful
(σ-conserving) move. -/
theorem marketClear_totalLogFlow (L : BondLedger) (hne : L.bonds.Nonempty) :
    (marketClear L).totalLogFlow = L.totalLogFlow := by
  classical
  have hcard : ((L.bonds.card : ℝ)) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hne).ne'
  have h1 : ∀ b ∈ L.bonds,
      (marketClear L).logFlow b = L.totalLogFlow / (L.bonds.card : ℝ) := by
    intro b hb
    show Real.log ((marketClear L).mult b) = _
    rw [marketClear_mult L hb]
    exact Real.log_exp _
  calc (marketClear L).totalLogFlow
      = ∑ b ∈ L.bonds, (marketClear L).logFlow b := rfl
    _ = ∑ _b ∈ L.bonds, (L.totalLogFlow / (L.bonds.card : ℝ)) :=
        Finset.sum_congr rfl h1
    _ = (L.bonds.card : ℝ) * (L.totalLogFlow / (L.bonds.card : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = L.totalLogFlow := by field_simp

/-- Cost of the cleared ledger: `n · J(geoMean)`. -/
theorem marketClear_cost (L : BondLedger) :
    (marketClear L).cost = (L.bonds.card : ℝ) * Jcost L.geoMean := by
  classical
  have h1 : ∀ b ∈ L.bonds,
      Jcost ((marketClear L).mult b) = Jcost L.geoMean := by
    intro b hb
    rw [marketClear_mult L hb]
  calc (marketClear L).cost
      = ∑ b ∈ L.bonds, Jcost ((marketClear L).mult b) := rfl
    _ = ∑ _b ∈ L.bonds, Jcost L.geoMean := Finset.sum_congr rfl h1
    _ = (L.bonds.card : ℝ) * Jcost L.geoMean := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **H-theorem, weak form (n-point Jensen).** Market clearing never
raises recognition cost: among all multiplier assignments with the
ledger's total log-flow, the uniform geometric-mean state is a cost
minimizer. -/
theorem marketClear_cost_le (L : BondLedger) (hne : L.bonds.Nonempty) :
    (marketClear L).cost ≤ L.cost := by
  classical
  have hn0 : 0 < L.bonds.card := Finset.card_pos.mpr hne
  have hnR : (0 : ℝ) < (L.bonds.card : ℝ) := by exact_mod_cast hn0
  have hsum : ∑ _b ∈ L.bonds, ((L.bonds.card : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hjensen := convexOn_cosh.map_sum_le (t := L.bonds)
      (w := fun _ => ((L.bonds.card : ℝ))⁻¹)
      (p := fun b => Real.log (L.mult b))
      (fun _ _ => by positivity) hsum (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hjensen
  have harg : ∑ b ∈ L.bonds, ((L.bonds.card : ℝ))⁻¹ * Real.log (L.mult b)
      = L.totalLogFlow / (L.bonds.card : ℝ) := by
    rw [← Finset.mul_sum]
    rw [div_eq_inv_mul]
    rfl
  rw [harg] at hjensen
  have hmul : (L.bonds.card : ℝ) *
      Real.cosh (L.totalLogFlow / (L.bonds.card : ℝ))
      ≤ ∑ b ∈ L.bonds, Real.cosh (Real.log (L.mult b)) := by
    have hstep := mul_le_mul_of_nonneg_left hjensen (le_of_lt hnR)
    rw [Finset.mul_sum] at hstep
    calc (L.bonds.card : ℝ) * Real.cosh (L.totalLogFlow / (L.bonds.card : ℝ))
        ≤ ∑ b ∈ L.bonds, (L.bonds.card : ℝ) *
            (((L.bonds.card : ℝ))⁻¹ * Real.cosh (Real.log (L.mult b))) := hstep
      _ = ∑ b ∈ L.bonds, Real.cosh (Real.log (L.mult b)) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          field_simp
  have hcostL : L.cost
      = (∑ b ∈ L.bonds, Real.cosh (Real.log (L.mult b))) - (L.bonds.card : ℝ) := by
    have h1 : ∀ b ∈ L.bonds,
        Jcost (L.mult b) = Real.cosh (Real.log (L.mult b)) - 1 :=
      fun b hb => Jcost_eq_cosh_log (L.mult_pos hb)
    calc L.cost
        = ∑ b ∈ L.bonds, Jcost (L.mult b) := rfl
      _ = ∑ b ∈ L.bonds, (Real.cosh (Real.log (L.mult b)) - 1) :=
          Finset.sum_congr rfl h1
      _ = (∑ b ∈ L.bonds, Real.cosh (Real.log (L.mult b)))
            - (L.bonds.card : ℝ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcostC : (marketClear L).cost
      = (L.bonds.card : ℝ) * Real.cosh (L.totalLogFlow / (L.bonds.card : ℝ))
        - (L.bonds.card : ℝ) := by
    rw [marketClear_cost L, Jcost_eq_cosh_log L.geoMean_pos]
    show (L.bonds.card : ℝ) *
        (Real.cosh (Real.log (Real.exp (L.totalLogFlow / (L.bonds.card : ℝ)))) - 1)
        = _
    rw [Real.log_exp]
    ring
  linarith

/-- If a pair settles at equal multipliers, equilibration leaves cost
exactly unchanged: uniform pairs are rest points of the local move. -/
theorem equilibratePair_cost_of_eq_mult (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds) (hne : b₁ ≠ b₂)
    (hm : L.mult b₁ = L.mult b₂) :
    (L.equilibratePair b₁ b₂ h₁ h₂).cost = L.cost := by
  rw [equilibratePair_cost L b₁ b₂ h₁ h₂ hne,
      cost_pair_decomposition L b₁ b₂ h₁ h₂ hne]
  have hx : 0 < L.mult b₁ := L.mult_pos h₁
  have hsqrt : Real.sqrt (L.mult b₁ * L.mult b₂) = L.mult b₁ := by
    rw [← hm, Real.sqrt_mul_self hx.le]
  rw [hsqrt, hm]
  ring

/-- **Fixed points of the local settlement dynamics are exactly the
uniform ledgers.** A strictly improving pair trade exists iff the
ledger is not uniform. Together with `equilibratePair_strictly_lowers_cost`
this characterizes market rest: no profitable trade remains exactly
when all multipliers agree. -/
theorem exists_improving_pair_iff_not_uniform (L : BondLedger) :
    (∃ (b₁ b₂ : BondId) (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds),
        b₁ ≠ b₂ ∧ (L.equilibratePair b₁ b₂ h₁ h₂).cost < L.cost)
      ↔ ¬ UniformMult L := by
  constructor
  · rintro ⟨b₁, b₂, h₁, h₂, hne, hlt⟩ huni
    have hm : L.mult b₁ = L.mult b₂ := huni b₁ h₁ b₂ h₂
    rw [equilibratePair_cost_of_eq_mult L b₁ b₂ h₁ h₂ hne hm] at hlt
    exact lt_irrefl _ hlt
  · intro huni
    unfold UniformMult at huni
    push_neg at huni
    obtain ⟨b₁, h₁, b₂, h₂, hm⟩ := huni
    have hne : b₁ ≠ b₂ := by
      rintro rfl
      exact hm rfl
    exact ⟨b₁, b₂, h₁, h₂, hne,
      equilibratePair_strictly_lowers_cost L b₁ b₂ h₁ h₂ hne hm⟩

/-- **H-theorem, strict form.** On any non-uniform ledger, market
clearing strictly lowers recognition cost. Route: one strict local
settlement, then the weak Jensen bound on the settled ledger, whose
geometric mean is unchanged because the local move conserved total
log-flow. -/
theorem marketClear_cost_lt (L : BondLedger) (huni : ¬ UniformMult L) :
    (marketClear L).cost < L.cost := by
  classical
  unfold UniformMult at huni
  push_neg at huni
  obtain ⟨b₁, h₁, b₂, h₂, hm⟩ := huni
  have hbne : b₁ ≠ b₂ := by
    rintro rfl
    exact hm rfl
  have hlt : (L.equilibratePair b₁ b₂ h₁ h₂).cost < L.cost :=
    equilibratePair_strictly_lowers_cost L b₁ b₂ h₁ h₂ hbne hm
  have hflow : (L.equilibratePair b₁ b₂ h₁ h₂).totalLogFlow = L.totalLogFlow :=
    equilibratePair_totalLogFlow L b₁ b₂ h₁ h₂ hbne
  have hgeo : (L.equilibratePair b₁ b₂ h₁ h₂).geoMean = L.geoMean := by
    unfold geoMean
    rw [hflow]
    rfl
  have hne' : (L.equilibratePair b₁ b₂ h₁ h₂).bonds.Nonempty := ⟨b₁, h₁⟩
  have hje : (marketClear (L.equilibratePair b₁ b₂ h₁ h₂)).cost
      ≤ (L.equilibratePair b₁ b₂ h₁ h₂).cost :=
    marketClear_cost_le _ hne'
  have hceq : (marketClear L).cost
      = (marketClear (L.equilibratePair b₁ b₂ h₁ h₂)).cost := by
    rw [marketClear_cost, marketClear_cost,
        show (L.equilibratePair b₁ b₂ h₁ h₂).bonds = L.bonds from rfl, hgeo]
  linarith

/-- Two bond ledgers with the same data fields are equal (the
positivity proof field carries no information). -/
theorem ext' {L M : BondLedger} (hb : L.bonds = M.bonds)
    (hm : L.mult = M.mult) (hs : L.src = M.src) (hd : L.dst = M.dst) :
    L = M := by
  cases L
  cases M
  dsimp at hb hm hs hd
  subst hb
  subst hm
  subst hs
  subst hd
  rfl

/-- **Convergence in one step.** Market clearing is idempotent: the
cleared state is the rest state of the relaxation. With
`marketClear_cost_lt` this is the H-theorem's convergence clause: J
strictly decreases into the uniform state and then stays. -/
theorem marketClear_idem (L : BondLedger) (hne : L.bonds.Nonempty) :
    marketClear (marketClear L) = marketClear L := by
  have hg : (marketClear L).geoMean = L.geoMean := by
    unfold geoMean
    rw [marketClear_totalLogFlow L hne]
    rfl
  refine ext' rfl ?_ rfl rfl
  funext b
  show (if b ∈ (marketClear L).bonds then (marketClear L).geoMean
        else (marketClear L).mult b)
      = (if b ∈ L.bonds then L.geoMean else L.mult b)
  by_cases hb : b ∈ L.bonds
  · have hb' : b ∈ (marketClear L).bonds := hb
    rw [if_pos hb', if_pos hb, hg]
  · have hb' : b ∉ (marketClear L).bonds := hb
    rw [if_neg hb', if_neg hb]
    show (if b ∈ L.bonds then L.geoMean else L.mult b) = L.mult b
    rw [if_neg hb]

/-- **Markets clear to balance exactly on σ-zero books.** The cleared
ledger is fully balanced (every multiplier 1, σ_abs = 0) iff the total
log-flow of the original ledger is zero. A ledger with residual net
flow clears to the uniform spread of that residual, not to unity:
conservation is respected, never erased. -/
theorem marketClear_balanced_iff (L : BondLedger) (hne : L.bonds.Nonempty) :
    (marketClear L).Balanced ↔ L.totalLogFlow = 0 := by
  constructor
  · intro hb
    obtain ⟨b, hbmem⟩ := hne
    have hball : (marketClear L).mult b = 1 := hb b hbmem
    rw [marketClear_mult L hbmem] at hball
    have h0 : L.totalLogFlow / (L.bonds.card : ℝ) = 0 := by
      have hexp : Real.exp (L.totalLogFlow / (L.bonds.card : ℝ)) = 1 := hball
      have hlog := congrArg Real.log hexp
      rwa [Real.log_exp, Real.log_one] at hlog
    have hcard : ((L.bonds.card : ℝ)) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨b, hbmem⟩).ne'
    rcases div_eq_zero_iff.mp h0 with h | h
    · exact h
    · exact absurd h hcard
  · intro hS b hbmem
    have hbmem' : b ∈ L.bonds := hbmem
    rw [marketClear_mult L hbmem']
    unfold geoMean
    rw [hS, zero_div, Real.exp_zero]

end

end BondLedger
end BondConservation
end Ethics

/-! ## Part 3: Seam origination and the certificate -/

namespace Economics
namespace Recognition
namespace SeamFloor

open Ethics.BondConservation
open Ethics.BondConservation.BondLedger
open Cost

noncomputable section

/-- **Two-sidedness, packaged.** Every active bond between distinct
agents posts on exactly two ledgers: the source's and the
destination's. A posting's conjugate lives on someone else's books. -/
theorem bond_posts_two_ledgers (L : BondLedger) {b : BondId}
    (hb : b ∈ L.bonds) (hsd : L.src b ≠ L.dst b) :
    ∃ i j : AgentId, i ≠ j ∧
      b ∈ L.incidentBonds i ∧ b ∈ L.incidentBonds j := by
  refine ⟨L.src b, L.dst b, hsd, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hb, Or.inl rfl⟩
  · exact Finset.mem_filter.mpr ⟨hb, Or.inr rfl⟩

/-- A lone bond between two agents is a seam: its skew is the log of
its multiplier. -/
theorem pairSkew_single_bond (L : BondLedger) {b : BondId} {i j : AgentId}
    (hfwd : L.bonds.filter (fun c => L.src c = i ∧ L.dst c = j) = {b})
    (hbwd : L.bonds.filter (fun c => L.src c = j ∧ L.dst c = i) = ∅) :
    L.pairSkew i j = Real.log (L.mult b) := by
  unfold BondLedger.pairSkew
  rw [hfwd, hbwd, Finset.sum_singleton, Finset.sum_empty]
  show L.logFlow b - 0 = Real.log (L.mult b)
  unfold BondLedger.logFlow
  ring

/-- **Seam skew is priced.** Nonzero pairwise skew between any two
agents forces strictly positive recognition cost on the ledger. -/
theorem cost_pos_of_seam (L : BondLedger) {i j : AgentId}
    (h : L.pairSkew i j ≠ 0) : 0 < L.cost := by
  apply cost_pos_of_not_balanced
  intro hbal
  exact h (pairSkew_eq_zero_of_balanced L hbal i j)

/-- The φ-bond ledger's seam skew between its two agents is `ln φ`. -/
theorem phiLedger_pairSkew :
    BondLedger.phiLedger.pairSkew 0 1 = Real.log Constants.phi := by
  unfold BondLedger.pairSkew BondLedger.logFlow BondLedger.phiLedger
  norm_num [Finset.filter_singleton]

/-- `ln φ ≠ 0`. -/
theorem log_phi_ne_zero : Real.log Constants.phi ≠ 0 := by
  have h1 : (1 : ℝ) < Constants.phi := by
    linarith [Constants.phi_gt_onePointFive]
  exact ne_of_gt (Real.log_pos h1)

/-- **The economy exists.** There is a bond ledger with two distinct
agents, nonzero seam skew between them, and strictly positive
recognition cost. Witness: a single bond at multiplier φ, whose cost
is the phantom-Carnot quantum `φ − 3/2`. -/
theorem economy_exists :
    ∃ (L : BondLedger) (i j : AgentId), i ≠ j ∧
      L.pairSkew i j ≠ 0 ∧ 0 < L.cost := by
  refine ⟨BondLedger.phiLedger, 0, 1, by norm_num, ?_,
    BondLedger.phiLedger_cost_pos⟩
  rw [phiLedger_pairSkew]
  exact log_phi_ne_zero

/-- **Seam floor certificate.** The three theorems of the floor: bond
persistence (credit forced by serial capacity), the market-clearing
H-theorem (σ-conserving relaxation strictly descends J into the
uniform rest state, which is fully balanced exactly on σ-zero books),
and seam origination (two-sidedness, priced skew, and the existence of
the economy as a theorem). -/
structure SeamFloorCert : Prop where
  /-- Demand above serial capacity forces a nonempty open-bond set at
  every tick. -/
  bond_persistence : ∀ (d : ℕ → ℕ) (S : SerialSettlement d),
    (∀ t, t + 1 < cumDemand d t) → ∀ t, 0 < openBonds d S t
  /-- Local pair settlement conserves total log-flow. -/
  local_move_conserves : ∀ (L : BondLedger) (b₁ b₂ : BondId)
    (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds), b₁ ≠ b₂ →
    (L.equilibratePair b₁ b₂ h₁ h₂).totalLogFlow = L.totalLogFlow
  /-- Market clearing conserves total log-flow. -/
  clearing_conserves : ∀ L : BondLedger, L.bonds.Nonempty →
    (marketClear L).totalLogFlow = L.totalLogFlow
  /-- Market clearing never raises J. -/
  clearing_descends_weak : ∀ L : BondLedger, L.bonds.Nonempty →
    (marketClear L).cost ≤ L.cost
  /-- Market clearing strictly lowers J off the uniform rest state. -/
  clearing_descends_strict : ∀ L : BondLedger, ¬ UniformMult L →
    (marketClear L).cost < L.cost
  /-- The cleared state is a fixed point: convergence in one step. -/
  clearing_converges : ∀ L : BondLedger, L.bonds.Nonempty →
    marketClear (marketClear L) = marketClear L
  /-- No profitable trade remains iff the ledger is uniform. -/
  rest_iff_uniform : ∀ L : BondLedger,
    (∃ (b₁ b₂ : BondId) (h₁ : b₁ ∈ L.bonds) (h₂ : b₂ ∈ L.bonds),
        b₁ ≠ b₂ ∧ (L.equilibratePair b₁ b₂ h₁ h₂).cost < L.cost)
      ↔ ¬ UniformMult L
  /-- The cleared state is balanced iff total log-flow is zero. -/
  clears_to_balance_iff : ∀ L : BondLedger, L.bonds.Nonempty →
    ((marketClear L).Balanced ↔ L.totalLogFlow = 0)
  /-- Nonzero seam skew forces positive cost. -/
  seam_priced : ∀ (L : BondLedger) (i j : AgentId),
    L.pairSkew i j ≠ 0 → 0 < L.cost
  /-- The economy exists: a ledger with two agents, nonzero seam skew,
  and positive cost. -/
  economy_exists : ∃ (L : BondLedger) (i j : AgentId), i ≠ j ∧
    L.pairSkew i j ≠ 0 ∧ 0 < L.cost

/-- The seam floor certificate is theorem-backed. -/
theorem seamFloorCert : SeamFloorCert where
  bond_persistence := fun _ S h => bond_persistence S h
  local_move_conserves := fun L b₁ b₂ h₁ h₂ hne =>
    equilibratePair_totalLogFlow L b₁ b₂ h₁ h₂ hne
  clearing_conserves := fun L hne => marketClear_totalLogFlow L hne
  clearing_descends_weak := fun L hne => marketClear_cost_le L hne
  clearing_descends_strict := fun L huni => marketClear_cost_lt L huni
  clearing_converges := fun L hne => marketClear_idem L hne
  rest_iff_uniform := fun L => exists_improving_pair_iff_not_uniform L
  clears_to_balance_iff := fun L hne => marketClear_balanced_iff L hne
  seam_priced := fun L _ _ h => cost_pos_of_seam L h
  economy_exists := economy_exists

end

end SeamFloor
end Recognition
end Economics

end IndisputableMonolith
