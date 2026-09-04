import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetHarness
import IndisputableMonolith.Foundation.KernelClosure.LadderNecessaryReasons
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow4Hierarchy

/-!
# Cutset row 4, second pass: the ladder from two floor words

The kernel's ladder sentence is the `RealizedHierarchy` pair
`ratio_self_similar` (uniform ratios along the orbit) and `additive_posting`
(`levels 2 = levels 1 + levels 0`). Arc 1 (`CutsetRow4Hierarchy`) left two
residuals: a "reads a floor" blade for uniformity, and the generation rule for
additivity. This module states both as words of the floor with no numeral and
no pairing, and proves they force the pair, hence `φ`.

## The two words

* **Similarity** (4a). The floor step is one rule at every floor: `T` rescales
  every reading by one factor, `r (T s) = ρ * r s` for all states `s`. A
  recognizer at any floor runs the same law; floors differ by a unit.
* **Join-built** (4b). T3 read on the tower: every level above the base pair
  is the join of two earlier levels (`JoinGenerated`), and the join of two
  adjacent levels is a level (`JoinClosed`). No pairing is chosen and no
  numeral appears; "two" is the arity of a join.

## What is proved

* `orbitUniform_of_similarity`: similarity gives uniform ratios on every orbit.
* `similarity_ratio_eq_phi`: similarity plus join-built forces the step factor
  to be `φ`; growth (`1 < ρ`) is derived, not assumed.
* `additive_of_similarity_joinBuilt`: the additive field follows.
* `realizedHierarchy_of_blade`: the two words inhabit `RealizedHierarchy`, so
  `realized_hierarchy_forces_phi` applies.
* Planted positive `phiFramework` passes both words; planted negative
  `doublingFramework` (ratio `2`) is join-generated but not join-closed:
  `1 + 2 = 3` is not a power of two.
* `linearFramework` fails similarity (`2 ≠ 3/2`).

## Shape, stated honestly

* 4b is a **merge under uniformity**: `joinBuilt_of_uniform_additive` shows the
  sentence already implies join-built, and the census theorem
  `gen2_iff_additive_under_uniform_closure` said the same. What changes is the
  premise's form: the pairing `(0, 1)` and the equation `s 2 = s 1 + s 0` are
  replaced by "built by joins, closed under joins", and the pairing is derived.
* 4a is a **cut across orbits and a merge along one orbit**:
  `twoOrbitFramework` is uniform and additive on the base orbit (ratio `φ`)
  and runs ratio `3` on a second orbit, so it satisfies the sentence and fails
  similarity. On a single orbit, similarity is uniformity in other words. The
  content the blade carries beyond the sentence is exactly "the same step
  everywhere", which is what a floor step is.

Verdict for the ledger: MODEL. The hierarchy premise becomes two definitions
of floor words (the step is a similarity; the tower is join-built); `φ` is a
theorem under them. Nothing here derives similarity from the framework axioms:
the census countermodels (`linearFramework`) still stand for that question.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row4Ladder

open ClosedFramework HierarchyRealization LadderCensus

noncomputable section

/-! ## Orbit levels -/

theorem orbitLevels_pos (F : ClosedObservableFramework) (base : F.S) (k : ℕ) :
    0 < orbitLevels' F base k := F.r_pos _

theorem orbitLevels_succ (F : ClosedObservableFramework) (base : F.S) (k : ℕ) :
    orbitLevels' F base (k + 1) = F.r (F.T (F.T^[k] base)) := by
  unfold orbitLevels'
  rw [Function.iterate_succ_apply']

/-! ## 4a: the floor step is one rule at every floor -/

/-- **Similarity.** The step rescales every reading by one factor. -/
def Similarity (F : ClosedObservableFramework) : Prop :=
  ∃ ρ : ℝ, ∀ s, F.r (F.T s) = ρ * F.r s

theorem similarity_levels_succ {F : ClosedObservableFramework} {ρ : ℝ}
    (h : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (k : ℕ) :
    orbitLevels' F base (k + 1) = ρ * orbitLevels' F base k := by
  rw [orbitLevels_succ, h]
  rfl

theorem similarity_levels_pow {F : ClosedObservableFramework} {ρ : ℝ}
    (h : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (k : ℕ) :
    orbitLevels' F base k = ρ ^ k * orbitLevels' F base 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [similarity_levels_succ h, ih]; ring

theorem similarity_ratio_pos {F : ClosedObservableFramework} {ρ : ℝ}
    (h : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) : 0 < ρ := by
  have h1 := similarity_levels_succ h base 0
  have p0 := orbitLevels_pos F base 0
  have p1 := orbitLevels_pos F base 1
  by_contra hneg
  push_neg at hneg
  nlinarith

/-- Similarity gives uniform ratios along every orbit. -/
theorem orbitUniform_of_similarity (F : ClosedObservableFramework) (h : Similarity F)
    (base : F.S) : OrbitUniform F base := by
  obtain ⟨ρ, hρ⟩ := h
  intro k
  have h1 : orbitLevels' F base (k + 2) = ρ * orbitLevels' F base (k + 1) :=
    similarity_levels_succ hρ base (k + 1)
  have h2 := similarity_levels_succ hρ base k
  have p1 : orbitLevels' F base (k + 1) ≠ 0 := (orbitLevels_pos F base _).ne'
  have p0 : orbitLevels' F base k ≠ 0 := (orbitLevels_pos F base _).ne'
  rw [h1, mul_div_assoc, div_self p1, mul_one, h2, mul_div_assoc, div_self p0, mul_one]

/-- The planted positive passes: `φ ^ (n+1) = φ * φ ^ n`. -/
theorem phiFramework_similarity : Similarity phiFramework :=
  ⟨Constants.phi, fun (n : ℕ) => by
    show Constants.phi ^ (n + 1) = Constants.phi * Constants.phi ^ n
    ring⟩

/-- The linear ladder fails similarity: its first two steps have factors
`2` and `3/2`. -/
theorem linearFramework_not_similarity : ¬ Similarity linearFramework := by
  rintro ⟨ρ, h⟩
  have h0 : ((Nat.succ 0 : ℕ) : ℝ) + 1 = ρ * (((0 : ℕ) : ℝ) + 1) :=
    h (show linearFramework.S from (0 : ℕ))
  have h1 : ((Nat.succ 1 : ℕ) : ℝ) + 1 = ρ * (((1 : ℕ) : ℝ) + 1) :=
    h (show linearFramework.S from (1 : ℕ))
  norm_num at h0 h1
  linarith

/-! ## 4b: the tower is built by joins -/

/-- Every level above the base pair is the join of two earlier levels. -/
def JoinGenerated (s : ℕ → ℝ) : Prop :=
  ∀ n, 2 ≤ n → ∃ a b, a ≤ b ∧ b < n ∧ s n = s a + s b

/-- The join of two adjacent levels is a level. -/
def JoinClosed (s : ℕ → ℝ) : Prop :=
  ∀ k, ∃ m, s m = s k + s (k + 1)

/-- T3 read on the tower. -/
def JoinBuilt (s : ℕ → ℝ) : Prop := JoinGenerated s ∧ JoinClosed s

theorem phi_pow_add_two (j : ℕ) :
    Constants.phi ^ (j + 2) = Constants.phi ^ j + Constants.phi ^ (j + 1) := by
  have h := Constants.phi_sq_eq
  calc Constants.phi ^ (j + 2) = Constants.phi ^ j * Constants.phi ^ 2 := by ring
    _ = Constants.phi ^ j * (Constants.phi + 1) := by rw [h]
    _ = Constants.phi ^ j + Constants.phi ^ (j + 1) := by ring

theorem phi_joinGenerated : JoinGenerated (fun n => Constants.phi ^ n) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  exact ⟨j, j + 1, by omega, by omega, phi_pow_add_two j⟩

theorem phi_joinClosed : JoinClosed (fun n => Constants.phi ^ n) :=
  fun k => ⟨k + 2, phi_pow_add_two k⟩

theorem phi_levels : orbitLevels' phiFramework phiBase = fun n => Constants.phi ^ n := by
  funext n
  unfold phiFramework phiBase
  rw [natFramework_levels]

theorem phi_joinBuilt : JoinBuilt (orbitLevels' phiFramework phiBase) := by
  rw [phi_levels]
  exact ⟨phi_joinGenerated, phi_joinClosed⟩

theorem doubling_levels :
    orbitLevels' doublingFramework doublingBase = fun n => (2 : ℝ) ^ n := by
  funext n
  unfold doublingFramework doublingBase
  rw [natFramework_levels]

theorem two_pow_ne_three (m : ℕ) : (2 : ℝ) ^ m ≠ 3 := by
  rcases m with _ | _ | m
  · norm_num
  · norm_num
  · have h1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have h4 : (2 : ℝ) ^ (m + 1 + 1) = 4 * 2 ^ m := by ring
    rw [h4]
    intro h
    linarith

/-- The doubling ladder is join-generated (`4 = 2 + 2`) but not join-closed:
`1 + 2 = 3` is not a level. -/
theorem doubling_not_joinClosed :
    ¬ JoinClosed (orbitLevels' doublingFramework doublingBase) := by
  rw [doubling_levels]
  intro h
  obtain ⟨m, hm⟩ := h 0
  have h3 : (2 : ℝ) ^ m = 3 := by
    simp only [pow_zero, zero_add, pow_one] at hm
    linarith
  exact two_pow_ne_three m h3

/-! ## The exclusion: similarity and join-built force the pair -/

/-- Growth is derived: a nonincreasing ladder cannot be join-generated. -/
theorem similarity_ratio_gt_one {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S)
    (hgen : JoinGenerated (orbitLevels' F base)) : 1 < ρ := by
  have hpos : ∀ k, 0 < orbitLevels' F base k := orbitLevels_pos F base
  have hpow := similarity_levels_pow hρ base
  have hρpos := similarity_ratio_pos hρ base
  by_contra hle
  push_neg at hle
  obtain ⟨a, b, hab, hb, h2⟩ := hgen 2 le_rfl
  have hmono : ∀ i, i ≤ 2 → orbitLevels' F base 2 ≤ orbitLevels' F base i := by
    intro i hi
    rw [hpow 2, hpow i]
    have : ρ ^ 2 ≤ ρ ^ i := pow_le_pow_of_le_one hρpos.le hle hi
    exact mul_le_mul_of_nonneg_right this (hpos 0).le
  have ha := hmono a (by omega)
  have hb' := hmono b (by omega)
  linarith [hpos 2]

/-- **Similarity and join-built force `φ`.** -/
theorem similarity_ratio_eq_phi {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S)
    (hj : JoinBuilt (orbitLevels' F base)) : ρ = Constants.phi := by
  obtain ⟨hgen, hcl⟩ := hj
  have hpos : ∀ k, 0 < orbitLevels' F base k := orbitLevels_pos F base
  have hunif : ∀ n, orbitLevels' F base (n + 1) = ρ * orbitLevels' F base n :=
    similarity_levels_succ hρ base
  have hρ1 : 1 < ρ := similarity_ratio_gt_one hρ base hgen
  have hpow := similarity_levels_pow hρ base
  have hcl0 : ∃ m : ℕ, 2 ≤ m ∧ orbitLevels' F base m =
      orbitLevels' F base 0 + orbitLevels' F base 1 := by
    obtain ⟨m, hm⟩ := hcl 0
    have hm' : orbitLevels' F base m = orbitLevels' F base 0 + orbitLevels' F base 1 := hm
    refine ⟨m, ?_, hm'⟩
    by_contra hlt
    push_neg at hlt
    have hle : m ≤ 1 := by omega
    have hmono : orbitLevels' F base m ≤ orbitLevels' F base 1 := by
      rw [hpow m, hpow 1]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hρ1.le hle) (hpos 0).le
    linarith [hpos 0]
  have hgen2 : ∃ a b : ℕ, a ≤ b ∧ b < 2 ∧
      orbitLevels' F base 2 = orbitLevels' F base a + orbitLevels' F base b :=
    hgen 2 le_rfl
  exact GrowthFloorPhysicsBoundary.uniform_closure_generation_forces_phi
    (orbitLevels' F base) ρ hρ1 (hpos 0) hunif hcl0 hgen2

/-- The additive field follows from the two words. -/
theorem additive_of_similarity_joinBuilt (F : ClosedObservableFramework) (base : F.S)
    (hs : Similarity F) (hj : JoinBuilt (orbitLevels' F base)) : OrbitAdditive F base := by
  obtain ⟨ρ, hρ⟩ := hs
  have hφ := similarity_ratio_eq_phi hρ base hj
  have hpow := similarity_levels_pow hρ base
  show orbitLevels' F base 2 = orbitLevels' F base 1 + orbitLevels' F base 0
  rw [hpow 2, hpow 1, hφ, pow_one, Constants.phi_sq_eq]
  ring

/-- Growth, for the `RealizedHierarchy` record. -/
theorem growth_of_similarity_joinGenerated (F : ClosedObservableFramework) (base : F.S)
    (hs : Similarity F) (hgen : JoinGenerated (orbitLevels' F base)) :
    1 < orbitLevels' F base 1 / orbitLevels' F base 0 := by
  obtain ⟨ρ, hρ⟩ := hs
  have h1 := similarity_levels_succ hρ base 0
  have p0 : orbitLevels' F base 0 ≠ 0 := (orbitLevels_pos F base 0).ne'
  rw [h1, mul_div_assoc, div_self p0, mul_one]
  exact similarity_ratio_gt_one hρ base hgen

/-- **The two words inhabit the hierarchy.** -/
def realizedHierarchy_of_blade (F : ClosedObservableFramework) (base : F.S)
    (hs : Similarity F) (hj : JoinBuilt (orbitLevels' F base)) : RealizedHierarchy F where
  baseState := base
  levels := orbitLevels' F base
  levels_eq := fun _ => rfl
  levels_pos := orbitLevels_pos F base
  growth := growth_of_similarity_joinGenerated F base hs hj.1
  ratio_self_similar := orbitUniform_of_similarity F hs base
  additive_posting := additive_of_similarity_joinBuilt F base hs hj

/-- The banked end-to-end theorem applies to the words' hierarchy. -/
theorem blade_forces_phi (F : ClosedObservableFramework) (base : F.S)
    (hs : Similarity F) (hj : JoinBuilt (orbitLevels' F base)) :
    (realized_to_ladder F (realizedHierarchy_of_blade F base hs hj)).ratio = PhiForcing.φ :=
  realized_hierarchy_forces_phi F _

/-! ## Shape: what the sentence already implies -/

theorem uniform_step (F : ClosedObservableFramework) (base : F.S) (hu : OrbitUniform F base)
    (k : ℕ) : orbitLevels' F base (k + 1) =
      (orbitLevels' F base 1 / orbitLevels' F base 0) * orbitLevels' F base k := by
  induction k with
  | zero =>
      rw [div_mul_eq_mul_div, mul_div_assoc, div_self (orbitLevels_pos F base 0).ne', mul_one]
  | succ k ih =>
      have h := hu k
      have hk : orbitLevels' F base (k + 1) / orbitLevels' F base k =
          orbitLevels' F base 1 / orbitLevels' F base 0 := by
        rw [ih, mul_div_assoc, div_self (orbitLevels_pos F base k).ne', mul_one]
      rw [hk, div_eq_iff (orbitLevels_pos F base (k + 1)).ne'] at h
      exact h

theorem uniform_pow (F : ClosedObservableFramework) (base : F.S) (hu : OrbitUniform F base)
    (k : ℕ) : orbitLevels' F base k =
      (orbitLevels' F base 1 / orbitLevels' F base 0) ^ k * orbitLevels' F base 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [uniform_step F base hu, ih]; ring

/-- **4b is a merge under uniformity.** Uniform and additive already give
join-built, with the pairing `(k, k+1)` at every rung. -/
theorem joinBuilt_of_uniform_additive (F : ClosedObservableFramework) (base : F.S)
    (hu : OrbitUniform F base) (ha : OrbitAdditive F base) :
    JoinBuilt (orbitLevels' F base) := by
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = orbitLevels' F base 1 / orbitLevels' F base 0 := ⟨_, rfl⟩
  have hpow : ∀ k, orbitLevels' F base k = ρ ^ k * orbitLevels' F base 0 := by
    intro k
    rw [hρdef]
    exact uniform_pow F base hu k
  have h0 := orbitLevels_pos F base 0
  have hs1 : orbitLevels' F base 1 = ρ * orbitLevels' F base 0 := by
    have := hpow 1
    rwa [pow_one] at this
  have hρ : ρ ^ 2 = ρ + 1 := by
    have h : orbitLevels' F base 2 = orbitLevels' F base 1 + orbitLevels' F base 0 := ha
    rw [hpow 2, hs1] at h
    have hz : (ρ ^ 2 - ρ - 1) * orbitLevels' F base 0 = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with h' | h'
    · linarith
    · exact absurd h' h0.ne'
  have hrec : ∀ k, orbitLevels' F base (k + 2) =
      orbitLevels' F base k + orbitLevels' F base (k + 1) := by
    intro k
    rw [hpow (k + 2), hpow k, hpow (k + 1)]
    have : ρ ^ (k + 2) = ρ ^ k * ρ ^ 2 := by ring
    rw [this, hρ]
    ring
  refine ⟨?_, fun k => ⟨k + 2, hrec k⟩⟩
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  exact ⟨j, j + 1, by omega, by omega, hrec j⟩

/-! ## Strictness across orbits -/

/-- Two orbits, ratio `φ` on one and `3` on the other. -/
def twoOrbitFramework : ClosedObservableFramework where
  S := Bool × ℕ
  T := fun p => (p.1, p.2 + 1)
  r := fun p => if p.1 then Constants.phi ^ p.2 else (3 : ℝ) ^ p.2
  r_pos := fun p => by
    show 0 < (if p.1 = true then Constants.phi ^ p.2 else (3 : ℝ) ^ p.2)
    split_ifs
    · exact pow_pos Constants.phi_pos _
    · positivity
  nontrivial := ⟨(true, 0), (false, 1), by norm_num⟩
  S_countable := exists_surjective_nat _
  no_continuous_moduli := no_continuous_moduli_of_countable (exists_surjective_nat _)
  charge := fun _ => 0
  charge_conserved := fun _ => rfl

def twoOrbitBase : twoOrbitFramework.S := (true, 0)

theorem twoOrbit_iterate (k : ℕ) :
    twoOrbitFramework.T^[k] twoOrbitBase = ((true, k) : Bool × ℕ) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem twoOrbit_levels (k : ℕ) :
    orbitLevels' twoOrbitFramework twoOrbitBase k = Constants.phi ^ k := by
  unfold orbitLevels'
  rw [twoOrbit_iterate]
  simp [twoOrbitFramework]

theorem twoOrbit_uniform : OrbitUniform twoOrbitFramework twoOrbitBase := by
  intro k
  rw [twoOrbit_levels, twoOrbit_levels, twoOrbit_levels]
  have h1 : Constants.phi ^ (k + 1) ≠ 0 := pow_ne_zero _ Constants.phi_ne_zero
  have h2 : Constants.phi ^ k ≠ 0 := pow_ne_zero _ Constants.phi_ne_zero
  rw [div_eq_div_iff h1 h2]
  ring

theorem twoOrbit_additive : OrbitAdditive twoOrbitFramework twoOrbitBase := by
  unfold OrbitAdditive
  rw [twoOrbit_levels, twoOrbit_levels, twoOrbit_levels]
  simp only [pow_zero, pow_one]
  exact Constants.phi_sq_eq

/-- The sentence holds on the base orbit, but the step is not one rule. -/
theorem twoOrbit_not_similarity : ¬ Similarity twoOrbitFramework := by
  rintro ⟨ρ, h⟩
  have h0 := h (show twoOrbitFramework.S from (true, 0))
  have h1 := h (show twoOrbitFramework.S from (false, 0))
  simp [twoOrbitFramework] at h0 h1
  have hφ : Constants.phi = 3 := by linarith
  have hsq := Constants.phi_sq_eq
  rw [hφ] at hsq
  norm_num at hsq

/-- **4a is a cut across orbits.** The sentence does not imply the blade. -/
theorem sentence_not_blade :
    (OrbitUniform twoOrbitFramework twoOrbitBase ∧ OrbitAdditive twoOrbitFramework twoOrbitBase) ∧
      ¬ Similarity twoOrbitFramework :=
  ⟨⟨twoOrbit_uniform, twoOrbit_additive⟩, twoOrbit_not_similarity⟩

/-! ## The row -/

/-- A framework with a base state. -/
abbrev Based := (F : ClosedObservableFramework) × F.S

/-- **Row 4 in the harness.** Sentence: the two hierarchy fields. Blade: the
step is a similarity and the tower is join-built. Real: the `φ` ladder.
Violator: the doubling ladder. -/
def row : CutsetRow Based where
  Floor := fun _ => True
  Sentence := fun p => OrbitUniform p.1 p.2 ∧ OrbitAdditive p.1 p.2
  Blade := fun p => Similarity p.1 ∧ JoinBuilt (orbitLevels' p.1 p.2)
  provenance := .definition
    "the floor step is one rule at every floor (a similarity); the tower is built by joins and closed under joins (T3)"
  real := ⟨phiFramework, phiBase⟩
  real_floor := trivial
  blade_real := ⟨phiFramework_similarity, phi_joinBuilt⟩
  violator := ⟨doublingFramework, doublingBase⟩
  violator_floor := trivial
  violator_violates := fun h => doublingFramework_not_additive h.2
  blade_kills_violator := fun h => doubling_not_joinClosed h.2.2
  exclusion := fun p _ hs hb =>
    hs ⟨orbitUniform_of_similarity p.1 hb.1 p.2,
      additive_of_similarity_joinBuilt p.1 p.2 hb.1 hb.2⟩

/-! ## Certificate -/

structure Cert : Prop where
  similarity_uniform : ∀ (F : ClosedObservableFramework), Similarity F →
    ∀ base : F.S, OrbitUniform F base
  forces_phi : ∀ (F : ClosedObservableFramework) (ρ : ℝ),
    (∀ s, F.r (F.T s) = ρ * F.r s) → ∀ base : F.S,
      JoinBuilt (orbitLevels' F base) → ρ = Constants.phi
  hierarchy : ∀ (F : ClosedObservableFramework) (base : F.S),
    Similarity F → JoinBuilt (orbitLevels' F base) → Nonempty (RealizedHierarchy F)
  real_passes : Similarity phiFramework ∧ JoinBuilt (orbitLevels' phiFramework phiBase)
  linear_fails : ¬ Similarity linearFramework
  doubling_fails : ¬ JoinClosed (orbitLevels' doublingFramework doublingBase)
  merge_4b : ∀ (F : ClosedObservableFramework) (base : F.S),
    OrbitUniform F base → OrbitAdditive F base → JoinBuilt (orbitLevels' F base)
  cut_4a : (OrbitUniform twoOrbitFramework twoOrbitBase ∧
      OrbitAdditive twoOrbitFramework twoOrbitBase) ∧ ¬ Similarity twoOrbitFramework
  row_forces : ∀ p, row.Floor p → row.Blade p → row.Sentence p
  row_class_nonempty : ∃ p, row.Floor p ∧ ¬ row.Sentence p

theorem cert : Cert where
  similarity_uniform := orbitUniform_of_similarity
  forces_phi := fun _ _ hρ base hj => similarity_ratio_eq_phi hρ base hj
  hierarchy := fun F base hs hj => ⟨realizedHierarchy_of_blade F base hs hj⟩
  real_passes := ⟨phiFramework_similarity, phi_joinBuilt⟩
  linear_fails := linearFramework_not_similarity
  doubling_fails := doubling_not_joinClosed
  merge_4b := joinBuilt_of_uniform_additive
  cut_4a := sentence_not_blade
  row_forces := row.forces
  row_class_nonempty := row.class_nonempty

end

end Row4Ladder
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
