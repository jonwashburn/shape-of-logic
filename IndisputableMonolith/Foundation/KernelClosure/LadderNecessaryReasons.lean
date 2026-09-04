import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.RowZeroReconciliation
import IndisputableMonolith.Foundation.GrowthFloorPhysicsBoundary
import IndisputableMonolith.Foundation.PhiForcingUnconditional

/-!
# Kernel premise closure census: the ladder (rows 4 through 7)

The kernel's three weight members (`weight_pos`, `weight_factorizes`,
`step_self_similar`) and the two `RealizedHierarchy` fields
(`ratio_self_similar`, `additive_posting`) are one object seen from two
sides: the measure side and the framework side. This module is the
necessary-reasons census for that object.

## Stratum fact first

The golden step is not available on the countable carrier
(`PublicSpine.phi_scale_is_a_purchase`, re-exported in row zero). The census
therefore targets the closed observable framework, whose observable is
real-valued, and asks which of the five members the framework forces.

## Rows and verdicts

1. **Uniformity from `no_continuous_moduli`** (the plan's lead route).
   REFUTED as a derivation, with the mechanism exposed:
   * `no_continuous_moduli` is a consequence of `S_countable`
     (`no_continuous_moduli_of_countable`): it carries no content the
     framework did not already have.
   * The banked theorem `no_moduli_forces_uniform_ratios` has a hypothesis
     (every positive real is an observable value) that no closed observable
     framework satisfies (`lifts_all_positive_contradicts_countable`), so it
     is vacuous on every framework.
   * A countable framework with additive posting and non-uniform ratios
     exists (`linearFramework`). Uniformity is not forced.
2. **Additive posting from join additivity.** REFUTED as a derivation from
   the framework: a countable framework with uniform ratios and no additive
   posting exists (`doublingFramework`). The two hierarchy fields are
   independent of each other over frameworks (`hierarchy_fields_independent`).
3. **Rung-2 generation and two-sidedness.** On a uniform ladder with
   adjacent closure, "rung 2 is a join of two lower rungs" is equivalent to
   additive posting (`gen2_iff_additive_under_uniform_closure`). So the
   two-input join is not a third premise: it is additive posting with the
   pairing left open, and closure picks the pairing.
4. **Weights.** DERIVED from the realized hierarchy. The hierarchy's own
   weight `levels 0 / levels n` is positive, factorizes, and satisfies the
   self-similar step (`hierarchyWeight_rule`), and every weight satisfying
   the three members equals it (`weight_premises_reduce_to_hierarchy`). The
   step equation alone admits the negative root `-φ`
   (`negative_root_weight`), so positivity is the row that selects; and the
   step equation is additive posting on the inverse weights
   (`step_iff_inverse_additive`). Rows 4 through 6 of the kernel are one
   MODEL row: the weight is the hierarchy's weight.
5. **Hierarchy existence.** PRICED. The Boolean framework carries no realized
   hierarchy at all (`boolFramework_no_realized_hierarchy`); the self-
   registry obstruction holds on it and delivers nothing
   (`self_registry_does_not_deliver_hierarchy`); an infinite orbit with a
   nontrivial observable delivers nothing (`linearFramework`). A realized
   hierarchy does exist on a countable framework (`phiFramework`), so the
   premise is satisfiable and load-bearing.

## What the purchase buys

Dropping uniformity while keeping the recurrence still gives φ as the
asymptotic ratio (`phi_asymptotic_without_uniformity`, re-exported from
`PhiForcingUnconditional`). Uniformity buys exactness at every rung, not φ.

## Verdict

**PRICED PURCHASE** at the framework stratum, with the price exact: two
qualitative premises on the orbit of the observable, self-similarity of the
ratio and additivity of the join, each with a countermodel satisfying the
other and every framework axiom. The three weight members are DERIVED from
those two. The banned row ("least cost selects φ") is not walked.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace LadderCensus

open ClosedFramework
open HierarchyRealization
open HierarchyRealizationObstruction
open MeasureForcing

noncomputable section

/-! ## Row 1: uniformity from `no_continuous_moduli` -/

/-- **`no_continuous_moduli` is redundant.** A countable state space admits
no injection from the reals. The framework axiom the plan hoped to lean on
is a consequence of `S_countable`. -/
theorem no_continuous_moduli_of_countable {S : Type}
    (hc : ∃ f : ℕ → S, Function.Surjective f) :
    ∀ embed : ℝ → S, ¬ Function.Injective embed := by
  obtain ⟨f, hf⟩ := hc
  intro embed hinj
  haveI : Countable S := hf.countable
  haveI : Countable ℝ := hinj.countable
  exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr inferInstance)

/-- **The banked uniformity route is vacuous.** No closed observable
framework realizes every positive real as an observable value, so the
hypothesis `carrier_lifts_perturbations` of `no_moduli_forces_uniform_ratios`
is never satisfied. -/
theorem lifts_all_positive_contradicts_countable (F : ClosedObservableFramework) :
    ¬ (∀ v : ℝ, 0 < v → ∃ s : F.S, F.r s = v) := by
  intro h
  choose lift hlift using fun t : ℝ => h (Real.exp t) (Real.exp_pos t)
  refine F.no_continuous_moduli lift (fun t₁ t₂ heq => ?_)
  have h1 := hlift t₁
  have h2 := hlift t₂
  rw [heq] at h1
  exact Real.exp_injective (h1.symm.trans h2)

/-- The orbit levels of a framework from a base state. -/
def orbitLevels' (F : ClosedObservableFramework) (base : F.S) (k : ℕ) : ℝ :=
  F.r (F.T^[k] base)

/-- Uniform ratios along the orbit. -/
def OrbitUniform (F : ClosedObservableFramework) (base : F.S) : Prop :=
  ∀ k, orbitLevels' F base (k + 2) / orbitLevels' F base (k + 1) =
    orbitLevels' F base (k + 1) / orbitLevels' F base k

/-- Additive posting along the orbit. -/
def OrbitAdditive (F : ClosedObservableFramework) (base : F.S) : Prop :=
  orbitLevels' F base 2 = orbitLevels' F base 1 + orbitLevels' F base 0

/-- A framework on `ℕ` with a chosen positive observable and the successor
dynamics. Every such framework is closed and observable. -/
def natFramework (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hnt : ∃ a b, r a ≠ r b) :
    ClosedObservableFramework where
  S := ℕ
  T := Nat.succ
  r := r
  r_pos := hr
  nontrivial := hnt
  S_countable := ⟨id, Function.surjective_id⟩
  no_continuous_moduli := no_continuous_moduli_of_countable ⟨id, Function.surjective_id⟩
  charge := fun _ => 0
  charge_conserved := fun _ => rfl

/-- The base state `0` of a framework on `ℕ`. -/
def natBase (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hnt : ∃ a b, r a ≠ r b) :
    (natFramework r hr hnt).S := (0 : ℕ)

theorem natFramework_iterate (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hnt : ∃ a b, r a ≠ r b)
    (k : ℕ) : (natFramework r hr hnt).T^[k] (natBase r hr hnt) = (k : ℕ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl

theorem natFramework_levels (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hnt : ∃ a b, r a ≠ r b)
    (k : ℕ) : orbitLevels' (natFramework r hr hnt) (natBase r hr hnt) k = r k := by
  unfold orbitLevels'
  rw [natFramework_iterate]
  rfl

/-- **Countermodel for row 1.** Levels `1, 2, 3, …`: additive posting holds
(`3 = 2 + 1`), the ratios `2, 3/2` are not uniform. -/
def linearFramework : ClosedObservableFramework :=
  natFramework (fun n => (n : ℝ) + 1) (fun n => by positivity) ⟨0, 1, by norm_num⟩

def linearBase : linearFramework.S :=
  natBase (fun n => (n : ℝ) + 1) (fun n => by positivity) ⟨0, 1, by norm_num⟩

theorem linearFramework_additive : OrbitAdditive linearFramework linearBase := by
  unfold OrbitAdditive linearFramework linearBase
  rw [natFramework_levels, natFramework_levels, natFramework_levels]
  norm_num

theorem linearFramework_not_uniform : ¬ OrbitUniform linearFramework linearBase := by
  intro h
  have h0 := h 0
  unfold linearFramework linearBase at h0
  rw [natFramework_levels, natFramework_levels, natFramework_levels] at h0
  norm_num at h0

/-- **Row 1 verdict.** Uniformity is not forced by the framework, even in
the presence of additive posting. -/
theorem uniformity_not_forced :
    ∃ (F : ClosedObservableFramework) (base : F.S),
      OrbitAdditive F base ∧ ¬ OrbitUniform F base :=
  ⟨linearFramework, linearBase, linearFramework_additive, linearFramework_not_uniform⟩

/-! ## Row 2: additive posting from join additivity -/

/-- **Countermodel for row 2.** Levels `1, 2, 4, …`: the ratio is uniformly
`2`, and `4 ≠ 2 + 1`. -/
def doublingFramework : ClosedObservableFramework :=
  natFramework (fun n => (2 : ℝ) ^ n) (fun n => by positivity) ⟨0, 1, by norm_num⟩

def doublingBase : doublingFramework.S :=
  natBase (fun n => (2 : ℝ) ^ n) (fun n => by positivity) ⟨0, 1, by norm_num⟩

theorem doublingFramework_uniform : OrbitUniform doublingFramework doublingBase := by
  intro k
  unfold doublingFramework doublingBase
  rw [natFramework_levels, natFramework_levels, natFramework_levels]
  have h1 : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  rw [div_eq_div_iff h1 h2]
  ring

theorem doublingFramework_not_additive : ¬ OrbitAdditive doublingFramework doublingBase := by
  unfold OrbitAdditive doublingFramework doublingBase
  rw [natFramework_levels, natFramework_levels, natFramework_levels]
  norm_num

/-- **Row 2 verdict, and the independence of the two fields.** Each
hierarchy field has a countable framework satisfying it and failing the
other. Neither is forced, and neither forces the other. -/
theorem hierarchy_fields_independent :
    (∃ (F : ClosedObservableFramework) (base : F.S),
      OrbitAdditive F base ∧ ¬ OrbitUniform F base) ∧
    (∃ (F : ClosedObservableFramework) (base : F.S),
      OrbitUniform F base ∧ ¬ OrbitAdditive F base) :=
  ⟨uniformity_not_forced,
    ⟨doublingFramework, doublingBase, doublingFramework_uniform,
      doublingFramework_not_additive⟩⟩

/-! ## Row 3: rung-2 generation is additive posting with the pairing open -/

/-- **Under uniformity and adjacent closure, rung-2 generation is additive
posting.** The forward direction is `uniform_closure_generation_forces_phi`
plus the golden equation; the backward direction is the pairing `(0, 1)`. -/
theorem gen2_iff_additive_under_uniform_closure
    (s : ℕ → ℝ) (r : ℝ) (hr : 1 < r) (h0 : 0 < s 0)
    (hunif : ∀ n, s (n + 1) = r * s n)
    (hcl0 : ∃ m : ℕ, 2 ≤ m ∧ s m = s 0 + s 1) :
    (∃ a b : ℕ, a ≤ b ∧ b < 2 ∧ s 2 = s a + s b) ↔ s 2 = s 1 + s 0 := by
  constructor
  · intro hgen
    have hphi := GrowthFloorPhysicsBoundary.uniform_closure_generation_forces_phi
      s r hr h0 hunif hcl0 hgen
    have h1 : s 1 = r * s 0 := hunif 0
    have h2 : s 2 = r * s 1 := hunif 1
    rw [h2, h1, hphi]
    have hsq : Constants.phi ^ 2 = Constants.phi + 1 := Constants.phi_sq_eq
    nlinarith [hsq]
  · intro hadd
    exact ⟨0, 1, by norm_num, by norm_num, by rw [hadd]; ring⟩

/-! ## Row 4: the weights are the hierarchy's weights -/

/-- A factorizing positive weight is a power of its step. -/
theorem factorizes_pow (w : ℕ → ℝ) (hpos : ∀ n, 0 < w n)
    (hfac : ∀ m n, w (m + n) = w m * w n) : ∀ n, w n = (w 1) ^ n := by
  have h0 : w 0 = 1 := by
    have := hfac 0 0
    simp only [Nat.add_zero] at this
    have hne : w 0 ≠ 0 := ne_of_gt (hpos 0)
    have : w 0 * (w 0 - 1) = 0 := by linarith [this]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · linarith
  intro n
  induction n with
  | zero => simpa using h0
  | succ k ih => rw [hfac k 1, ih, pow_succ]

/-- **The step equation has two roots.** `w₁ = 1 / (1 + w₁)` holds exactly
when `w₁ = φ⁻¹` or `w₁ = -φ`. -/
theorem step_roots (x : ℝ) (hx : x ≠ -1) :
    x = 1 / (1 + x) ↔ (x = 1 / Constants.phi ∨ x = -Constants.phi) := by
  have hphi : Constants.phi ≠ 0 := Constants.phi_ne_zero
  have hsq : Constants.phi ^ 2 = Constants.phi + 1 := Constants.phi_sq_eq
  have h1x : 1 + x ≠ 0 := by
    intro h; apply hx; linarith
  have hkey : x = 1 / (1 + x) ↔ x ^ 2 + x - 1 = 0 := by
    rw [eq_div_iff h1x]
    constructor <;> intro h <;> nlinarith [h]
  have hinv : 1 / Constants.phi = Constants.phi - 1 := by
    rw [div_eq_iff hphi]
    nlinarith [hsq]
  have hfac : x ^ 2 + x - 1 = (x - 1 / Constants.phi) * (x + Constants.phi) := by
    rw [hinv]
    linear_combination hsq
  rw [hkey, hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- **Positivity is the selecting row.** The negative root `-φ` generates a
weight that factorizes and satisfies the step equation, and is not positive.
-/
theorem negative_root_weight :
    (∀ m n : ℕ, (-Constants.phi) ^ (m + n) = (-Constants.phi) ^ m * (-Constants.phi) ^ n) ∧
      (-Constants.phi) ^ 1 = 1 / (1 + (-Constants.phi) ^ 1) ∧
      ¬ (∀ n : ℕ, 0 < (-Constants.phi) ^ n) := by
  refine ⟨fun m n => pow_add _ _ _, ?_, ?_⟩
  · rw [pow_one]
    have hne : -Constants.phi ≠ -1 := by
      intro h
      have := Constants.one_lt_phi
      linarith
    exact (step_roots _ hne).mpr (Or.inr rfl)
  · intro h
    have := h 1
    rw [pow_one] at this
    linarith [Constants.phi_pos]

/-- **The step equation is additive posting on the inverse weights.** For a
positive factorizing weight, `w₁ = 1 / (1 + w₁)` holds exactly when
`1 / w₂ = 1 / w₁ + 1 / w₀`. The measure side and the framework side are one
equation. -/
theorem step_iff_inverse_additive (w : ℕ → ℝ) (hpos : ∀ n, 0 < w n)
    (hfac : ∀ m n, w (m + n) = w m * w n) :
    w 1 = 1 / (1 + w 1) ↔ 1 / w 2 = 1 / w 1 + 1 / w 0 := by
  have hp := factorizes_pow w hpos hfac
  have h0 : w 0 = 1 := by simpa using hp 0
  have h2 : w 2 = w 1 ^ 2 := hp 2
  have hw1 : w 1 ≠ 0 := ne_of_gt (hpos 1)
  have h1w : 1 + w 1 ≠ 0 := by linarith [hpos 1]
  rw [h2, h0]
  constructor
  · intro h
    rw [eq_div_iff h1w] at h
    field_simp
    nlinarith [h]
  · intro h
    field_simp at h
    rw [eq_div_iff h1w]
    nlinarith [h]

/-- The hierarchy's own weight: the base level over the `n`-th level. -/
def hierarchyWeight (F : ClosedObservableFramework) (H : RealizedHierarchy F) (n : ℕ) : ℝ :=
  H.levels 0 / H.levels n

/-- Every level of a realized hierarchy is `φ ^ n` times the base level. -/
theorem realized_levels_phi_pow (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    ∀ n, H.levels n = Constants.phi ^ n * H.levels 0 := by
  have hratio : (realized_to_ladder F H).ratio = Constants.phi :=
    realized_hierarchy_forces_phi F H
  have hstep : ∀ k, H.levels (k + 1) = Constants.phi * H.levels k := by
    intro k
    have := (realized_to_ladder F H).uniform_scaling k
    rw [hratio] at this
    exact this
  intro n
  induction n with
  | zero => simp
  | succ k ih => rw [hstep k, ih, pow_succ]; ring

/-- **The hierarchy's weight satisfies the three kernel weight members.** -/
theorem hierarchyWeight_rule (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    (∀ n, 0 < hierarchyWeight F H n) ∧
      (∀ m n, hierarchyWeight F H (m + n) = hierarchyWeight F H m * hierarchyWeight F H n) ∧
      hierarchyWeight F H 1 = 1 / (1 + hierarchyWeight F H 1) := by
  have hphi : Constants.phi ≠ 0 := Constants.phi_ne_zero
  have hsq : Constants.phi ^ 2 = Constants.phi + 1 := Constants.phi_sq_eq
  have h0 : H.levels 0 ≠ 0 := ne_of_gt (H.levels_pos 0)
  have hinv : 1 / Constants.phi = Constants.phi - 1 := by
    rw [div_eq_iff hphi]
    nlinarith [hsq]
  have hw : ∀ n, hierarchyWeight F H n = (1 / Constants.phi) ^ n := by
    intro n
    unfold hierarchyWeight
    rw [realized_levels_phi_pow F H n, mul_comm, div_mul_eq_div_div, div_self h0,
      one_div, one_div, inv_pow]
  refine ⟨fun n => div_pos (H.levels_pos 0) (H.levels_pos n), ?_, ?_⟩
  · intro m n
    rw [hw, hw, hw, pow_add]
  · rw [hw, pow_one, hinv]
    have : (1 : ℝ) + (Constants.phi - 1) = Constants.phi := by ring
    rw [this]
    exact hinv.symm

/-- The hierarchy's weight is a recognition weight rule. -/
def hierarchyWeightRule (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    RecognitionWeightRule where
  w := hierarchyWeight F H
  w_pos := (hierarchyWeight_rule F H).1
  factorizes := (hierarchyWeight_rule F H).2.1
  step_self_similar := (hierarchyWeight_rule F H).2.2

/-- **Rows 4 through 6 reduce to the hierarchy.** A weight satisfies the
three kernel members exactly when it is the hierarchy's weight. -/
theorem weight_premises_reduce_to_hierarchy (F : ClosedObservableFramework)
    (H : RealizedHierarchy F) (w : ℕ → ℝ) :
    ((∀ n, 0 < w n) ∧ (∀ m n, w (m + n) = w m * w n) ∧ w 1 = 1 / (1 + w 1))
      ↔ w = hierarchyWeight F H := by
  constructor
  · rintro ⟨hpos, hfac, hstep⟩
    funext n
    have h1 : w n = latticeWeight n :=
      RecognitionWeightRule.weight_forced ⟨w, hpos, hfac, hstep⟩ n
    have h2 : hierarchyWeight F H n = latticeWeight n :=
      RecognitionWeightRule.weight_forced (hierarchyWeightRule F H) n
    rw [h1, h2]
  · rintro rfl
    exact hierarchyWeight_rule F H

/-! ## Row 5: hierarchy existence -/

/-- **The Boolean framework carries no realized hierarchy.** Its observable
takes two values and a realized hierarchy needs three strictly increasing
levels. -/
theorem boolFramework_no_realized_hierarchy : IsEmpty (RealizedHierarchy boolFramework) := by
  refine ⟨fun H => ?_⟩
  have hpos0 := H.levels_pos 0
  have hpos1 := H.levels_pos 1
  have hgrow : H.levels 0 < H.levels 1 := by
    have := H.growth
    rw [one_lt_div hpos0] at this
    exact this
  have hgrow2 : H.levels 1 < H.levels 2 := by
    have hss := H.ratio_self_similar 0
    have h : 1 < H.levels 2 / H.levels 1 := by
      rw [hss]
      exact H.growth
    rw [one_lt_div hpos1] at h
    exact h
  -- Every level is `1` or `2`.
  have hval : ∀ k, H.levels k = 1 ∨ H.levels k = 2 := by
    intro k
    rw [H.levels_eq k]
    cases boolFramework.T^[k] H.baseState
    · left; rfl
    · right; rfl
  rcases hval 0 with h0 | h0 <;> rcases hval 1 with h1 | h1 <;> rcases hval 2 with h2 | h2 <;>
    linarith

/-- **The self-registry obstruction delivers no hierarchy.** It holds on the
Boolean framework's state space, on which no realized hierarchy exists. -/
theorem self_registry_does_not_deliver_hierarchy :
    (¬ ∃ post : (boolFramework.S → Bool) → boolFramework.S, Function.Injective post) ∧
      IsEmpty (RealizedHierarchy boolFramework) :=
  ⟨PerfectRecognition.no_complete_self_registry _, boolFramework_no_realized_hierarchy⟩

/-- **A realized hierarchy does exist on a countable framework.** Levels
`φ ^ n` on `ℕ`. The premise is satisfiable, so the census is not vacuous. -/
def phiFramework : ClosedObservableFramework :=
  natFramework (fun n => Constants.phi ^ n) (fun n => pow_pos Constants.phi_pos n)
    ⟨0, 1, by
      simp only [pow_zero, pow_one]
      exact ne_of_lt Constants.one_lt_phi⟩

def phiBase : phiFramework.S :=
  natBase (fun n => Constants.phi ^ n) (fun n => pow_pos Constants.phi_pos n)
    ⟨0, 1, by
      simp only [pow_zero, pow_one]
      exact ne_of_lt Constants.one_lt_phi⟩

def phiHierarchy : RealizedHierarchy phiFramework where
  baseState := phiBase
  levels := fun k => Constants.phi ^ k
  levels_eq := fun k => by
    show Constants.phi ^ k = orbitLevels' phiFramework phiBase k
    unfold phiFramework phiBase
    rw [natFramework_levels]
  levels_pos := fun k => pow_pos Constants.phi_pos k
  growth := by
    simp only [pow_one, pow_zero, div_one]
    exact Constants.one_lt_phi
  ratio_self_similar := fun k => by
    have h1 : Constants.phi ^ (k + 1) ≠ 0 := pow_ne_zero _ Constants.phi_ne_zero
    have h2 : Constants.phi ^ k ≠ 0 := pow_ne_zero _ Constants.phi_ne_zero
    rw [div_eq_div_iff h1 h2]
    ring
  additive_posting := by
    simp only [pow_one, pow_zero]
    exact Constants.phi_sq_eq

/-! ## What the purchase buys -/

/-- **Without uniformity, φ is still the asymptotic ratio.** Any positive
ladder with the adjacent recurrence has inter-level ratio tending to φ.
Uniformity buys exactness at every rung, not the value. -/
theorem phi_asymptotic_without_uniformity (s : ℕ → ℝ) (hpos : ∀ n, 0 < s n)
    (hrec : ∀ n, s (n + 2) = s (n + 1) + s n) :
    Filter.Tendsto (fun n => s (n + 1) / s n) Filter.atTop (nhds Constants.phi) :=
  Foundation.ratio_tendsto_phi hpos hrec

/-! ## Certificate -/

structure LadderCensusCert : Prop where
  moduli_redundant :
    ∀ {S : Type}, (∃ f : ℕ → S, Function.Surjective f) →
      ∀ embed : ℝ → S, ¬ Function.Injective embed
  banked_route_vacuous :
    ∀ F : ClosedObservableFramework, ¬ (∀ v : ℝ, 0 < v → ∃ s : F.S, F.r s = v)
  fields_independent :
    (∃ (F : ClosedObservableFramework) (base : F.S),
      OrbitAdditive F base ∧ ¬ OrbitUniform F base) ∧
    (∃ (F : ClosedObservableFramework) (base : F.S),
      OrbitUniform F base ∧ ¬ OrbitAdditive F base)
  weights_reduce :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F) (w : ℕ → ℝ),
      ((∀ n, 0 < w n) ∧ (∀ m n, w (m + n) = w m * w n) ∧ w 1 = 1 / (1 + w 1))
        ↔ w = hierarchyWeight F H
  positivity_selects : ¬ (∀ n : ℕ, 0 < (-Constants.phi) ^ n)
  hierarchy_load_bearing : IsEmpty (RealizedHierarchy boolFramework)
  hierarchy_satisfiable : Nonempty (RealizedHierarchy phiFramework)

theorem ladderCensusCert_holds : LadderCensusCert where
  moduli_redundant := fun hc => no_continuous_moduli_of_countable hc
  banked_route_vacuous := lifts_all_positive_contradicts_countable
  fields_independent := hierarchy_fields_independent
  weights_reduce := weight_premises_reduce_to_hierarchy
  positivity_selects := negative_root_weight.2.2
  hierarchy_load_bearing := boolFramework_no_realized_hierarchy
  hierarchy_satisfiable := ⟨phiHierarchy⟩

/-! ## Audits -/

#print axioms no_continuous_moduli_of_countable
#print axioms lifts_all_positive_contradicts_countable
#print axioms uniformity_not_forced
#print axioms hierarchy_fields_independent
#print axioms gen2_iff_additive_under_uniform_closure
#print axioms step_roots
#print axioms negative_root_weight
#print axioms step_iff_inverse_additive
#print axioms weight_premises_reduce_to_hierarchy
#print axioms boolFramework_no_realized_hierarchy
#print axioms phi_asymptotic_without_uniformity
#print axioms ladderCensusCert_holds

end

end LadderCensus
end KernelClosure
end Foundation
end IndisputableMonolith
