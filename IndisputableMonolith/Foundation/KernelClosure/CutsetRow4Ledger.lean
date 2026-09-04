import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow4Ladder

/-!
# Cutset row 4, promoted: what the ladder's alternatives break

Row 4 (`CutsetRow4Ladder`) closed the realized hierarchy under two definitions:
the floor step is one rule at every floor (`Similarity`) and the tower is built
by joins and closed under joins (`JoinBuilt`). Three alternatives were excluded
by those words: the linear ladder `n+1`, the doubling ladder `2^n`, and the
two-orbit ladder (φ on one orbit, 3 on another). This module names the floor
fact each one breaks.

## 4a: similarity from one rule and unit freedom

Two facts the floor already has:

* one rule at every floor: the octave step is a single equivalence at every
  floor (`OctaveFloorStep.towerEquiv`); read on the observable, the step acts on
  readings by one rule `g`, `r (T s) = g (r s)` for all states (`UniformRule`);
* unit freedom (row 1, gauge): rescaling the unit rescales every reading alike,
  so the rule commutes with rescaling, `g (c x) = c g x` (`ScaleCovariant`).

Together they force `g x = g 1 · x`: the step is multiplication by one number
(`similarity_of_covariant`). Similarity is no longer a definition; it is what a
one-rule, unit-free step is.

* The linear ladder breaks unit freedom: its rule `x ↦ x + 1` adds a fixed
  unit, and no scale-covariant rule agrees with it (`linear_not_covariant`).
* The two-orbit ladder breaks one rule: at reading `1` it steps to `φ` on one
  orbit and to `3` on the other (`twoOrbit_not_uniformRule`).

## 4b: φ from independent joins and least count

A hierarchy is a tower whose levels are composed of earlier levels (that is
what the word means; it is the residual definition of this row). T3 says the
cost of a join of independent parts is the sum. A step that joins level `n`
with an earlier level is `s (n+1) = s n + s (n-k)` for a lag `k`
(`LagJoin`). Two floor facts constrain the lag:

* independence (T3): the two parts are distinct levels, so `k ≥ 1`. The
  doubling ladder is the self-join `k = 0` (`doubling_is_self_join`): its
  "two parts" are the same level twice, not independent parts. With any lag
  `k ≥ 1` it fails (`doubling_not_lagJoin_pos`).
* least count (T2, blade B2, the same selection row 3b used): the least
  positive lag is `1`, the adjacent join. Larger lags give other ladders (the
  lag-2 ladder's ratio satisfies `ρ³ = ρ² + 1`, which φ does not,
  `phi_not_lag_two`).

Similarity with the adjacent join gives `ρ² = ρ + 1`, so `ρ = φ`
(`phi_of_similarity_adjacentJoin`), and join-closure is then a theorem
(`joinClosed_of_adjacentJoin`), not a definition.

## Status

Linear: impossible (breaks unit freedom, a gauge fact). Two-orbit: impossible
(breaks one rule, a floor theorem transported to the observable). Doubling:
impossible (breaks T3 independence). Lag `k ≥ 2`: excluded by least count, the
same selection as row 3b (count reading). What remains of the definitions is
one sentence: a hierarchy's levels are composed of earlier levels. Everything
else about φ is a theorem under it.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row4Ledger

open ClosedFramework HierarchyRealization LadderCensus Row4Ladder

noncomputable section

/-! ## 4a: one rule, unit-free -/

/-- The step acts on readings by one rule at every state. -/
def UniformRule (F : ClosedObservableFramework) : Prop :=
  ∃ g : ℝ → ℝ, ∀ s, F.r (F.T s) = g (F.r s)

/-- Unit freedom on a rule: rescaling the unit rescales the rule's output alike. -/
def ScaleCovariant (g : ℝ → ℝ) : Prop :=
  ∀ c x : ℝ, 0 < c → 0 < x → g (c * x) = c * g x

/-- One rule at every floor, and the rule is unit-free. -/
def Covariant (F : ClosedObservableFramework) : Prop :=
  ∃ g : ℝ → ℝ, ScaleCovariant g ∧ ∀ s, F.r (F.T s) = g (F.r s)

theorem scaleCovariant_eq_mul {g : ℝ → ℝ} (hg : ScaleCovariant g) {x : ℝ} (hx : 0 < x) :
    g x = g 1 * x := by
  have := hg x 1 hx one_pos
  rw [mul_one] at this
  rw [this, mul_comm]

/-- **Similarity is a theorem of one rule plus unit freedom.** -/
theorem similarity_of_covariant (F : ClosedObservableFramework) (h : Covariant F) :
    Similarity F := by
  obtain ⟨g, hg, hstep⟩ := h
  refine ⟨g 1, fun s => ?_⟩
  rw [hstep s, scaleCovariant_eq_mul hg (F.r_pos s)]

theorem covariant_of_similarity (F : ClosedObservableFramework) (h : Similarity F) :
    Covariant F := by
  obtain ⟨ρ, hρ⟩ := h
  refine ⟨fun x => ρ * x, fun c x _ _ => by ring, hρ⟩

theorem covariant_iff_similarity (F : ClosedObservableFramework) :
    Covariant F ↔ Similarity F :=
  ⟨similarity_of_covariant F, covariant_of_similarity F⟩

/-- The linear ladder breaks unit freedom: no scale-covariant rule adds one. -/
theorem linear_not_covariant : ¬ Covariant linearFramework := by
  intro h
  exact linearFramework_not_similarity (similarity_of_covariant _ h)

/-- The two-orbit ladder breaks one rule: from reading `1` it steps to `φ` on
one orbit and to `3` on the other. -/
theorem twoOrbit_not_uniformRule : ¬ UniformRule twoOrbitFramework := by
  rintro ⟨g, hg⟩
  have h1 : twoOrbitFramework.r (twoOrbitFramework.T (true, 0)) =
      g (twoOrbitFramework.r (true, 0)) := hg (true, 0)
  have h2 : twoOrbitFramework.r (twoOrbitFramework.T (false, 0)) =
      g (twoOrbitFramework.r (false, 0)) := hg (false, 0)
  have e1 : twoOrbitFramework.r (twoOrbitFramework.T (true, 0)) = Constants.phi := by
    show (if (true : Bool) = true then Constants.phi ^ (0 + 1) else (3 : ℝ) ^ (0 + 1)) = _
    simp
  have e2 : twoOrbitFramework.r (twoOrbitFramework.T (false, 0)) = 3 := by
    show (if (false : Bool) = true then Constants.phi ^ (0 + 1) else (3 : ℝ) ^ (0 + 1)) = _
    simp
  have b1 : twoOrbitFramework.r (true, 0) = 1 := by
    show (if (true : Bool) = true then Constants.phi ^ 0 else (3 : ℝ) ^ 0) = _
    simp
  have b2 : twoOrbitFramework.r (false, 0) = 1 := by
    show (if (false : Bool) = true then Constants.phi ^ 0 else (3 : ℝ) ^ 0) = _
    simp
  rw [e1, b1] at h1
  rw [e2, b2] at h2
  have : Constants.phi = 3 := h1.trans h2.symm
  linarith [Constants.phi_lt_two]

/-! ## 4b: independent joins and least count -/

/-- The step joins level `n + k` with level `n`: a join with lag `k`. -/
def LagJoin (s : ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ n, s (n + k + 1) = s (n + k) + s n

/-- The adjacent join: lag one. -/
def AdjacentJoin (s : ℕ → ℝ) : Prop := LagJoin s 1

/-- The doubling ladder is the self-join: lag zero, the same level twice. -/
theorem doubling_is_self_join : LagJoin (fun n => (2 : ℝ) ^ n) 0 := by
  intro n
  simp only [add_zero]
  ring

/-- With any positive lag the doubling ladder fails: `2^(k+1) ≠ 2^k + 1`. -/
theorem doubling_not_lagJoin_pos (k : ℕ) (hk : 1 ≤ k) : ¬ LagJoin (fun n => (2 : ℝ) ^ n) k := by
  intro h
  have h0 := h 0
  simp only [zero_add, pow_zero] at h0
  have : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
  rw [this] at h0
  have hk2 : (2 : ℝ) ^ k ≥ 2 := by
    calc (2 : ℝ) ^ k ≥ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hk
      _ = 2 := by norm_num
  linarith

/-- The positive root of `x² = x + 1` is `φ`. -/
theorem eq_phi_of_sq_eq_add_one {x : ℝ} (hx : 0 < x) (h : x ^ 2 = x + 1) :
    x = Constants.phi := by
  have hφ := Constants.phi_sq_eq
  have hfac : (x - Constants.phi) * (x + Constants.phi - 1) = 0 := by
    nlinarith [hφ, h]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · linarith
  · exfalso
    have := Constants.one_lt_phi
    linarith

/-- **Similarity with the adjacent join forces φ.** -/
theorem phi_of_similarity_adjacentJoin {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S)
    (hj : AdjacentJoin (orbitLevels' F base)) : ρ = Constants.phi := by
  have hpow := similarity_levels_pow hρ base
  have hρpos := similarity_ratio_pos hρ base
  have h := hj 0
  simp only [zero_add] at h
  rw [hpow 2, hpow 1, hpow 0] at h
  have h0 := orbitLevels_pos F base 0
  have hq : ρ ^ 2 = ρ + 1 := by
    have : (ρ ^ 2 - ρ - 1) * orbitLevels' F base 0 = 0 := by
      simp only [pow_zero, one_mul, pow_one] at h
      linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact absurd h1 h0.ne'
  exact eq_phi_of_sq_eq_add_one hρpos hq

/-- Join-closure is a theorem of the adjacent join. -/
theorem joinClosed_of_adjacentJoin (s : ℕ → ℝ) (hj : AdjacentJoin s) : JoinClosed s := by
  intro k
  refine ⟨k + 2, ?_⟩
  have := hj k
  rw [add_comm (s (k + 1)) (s k)] at this
  exact this

/-- Join-generation is a theorem of the adjacent join. -/
theorem joinGenerated_of_adjacentJoin (s : ℕ → ℝ) (hj : AdjacentJoin s) : JoinGenerated s := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  refine ⟨m, m + 1, by omega, by omega, ?_⟩
  have := hj m
  rw [add_comm (s (m + 1)) (s m)] at this
  exact this

theorem joinBuilt_of_adjacentJoin (s : ℕ → ℝ) (hj : AdjacentJoin s) : JoinBuilt s :=
  ⟨joinGenerated_of_adjacentJoin s hj, joinClosed_of_adjacentJoin s hj⟩

/-- The φ ladder is the adjacent join. -/
theorem phi_adjacentJoin : AdjacentJoin (fun n => Constants.phi ^ n) := by
  intro n
  simp only []
  have := phi_pow_add_two n
  rw [show n + 1 + 1 = n + 2 from rfl, this, add_comm]

/-- A lag-`k` join under similarity gives `ρ^(k+1) = ρ^k + 1`. -/
theorem lag_ratio {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (k : ℕ)
    (hj : LagJoin (orbitLevels' F base) k) : ρ ^ (k + 1) = ρ ^ k + 1 := by
  have hpow := similarity_levels_pow hρ base
  have h := hj 0
  simp only [zero_add] at h
  rw [hpow (k + 1), hpow k, hpow 0] at h
  have h0 := orbitLevels_pos F base 0
  simp only [pow_zero, one_mul] at h
  have : (ρ ^ (k + 1) - ρ ^ k - 1) * orbitLevels' F base 0 = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 h0.ne'

/-- φ is not the lag-two ladder's ratio: `φ³ ≠ φ² + 1`. -/
theorem phi_not_lag_two : Constants.phi ^ 3 ≠ Constants.phi ^ 2 + 1 := by
  rw [Constants.phi_cubed_eq, Constants.phi_sq_eq]
  intro h
  have := Constants.phi_ne_one
  apply this
  linarith

/-! ## The chain -/

/-- **From floor facts to φ.** One rule, unit freedom, independent adjacent
joins: the ratio is φ and the hierarchy is realized. -/
theorem phi_of_covariant_adjacentJoin (F : ClosedObservableFramework) (base : F.S)
    (hc : Covariant F) (hj : AdjacentJoin (orbitLevels' F base)) :
    ∃ ρ, (∀ s, F.r (F.T s) = ρ * F.r s) ∧ ρ = Constants.phi := by
  obtain ⟨ρ, hρ⟩ := similarity_of_covariant F hc
  exact ⟨ρ, hρ, phi_of_similarity_adjacentJoin hρ base hj⟩

theorem blade_of_covariant_adjacentJoin (F : ClosedObservableFramework) (base : F.S)
    (hc : Covariant F) (hj : AdjacentJoin (orbitLevels' F base)) :
    Similarity F ∧ JoinBuilt (orbitLevels' F base) :=
  ⟨similarity_of_covariant F hc, joinBuilt_of_adjacentJoin _ hj⟩

/-! ## Certificate -/

structure RowCert : Prop where
  /-- 4a: one rule plus unit freedom is similarity. -/
  similarity_from_floor : ∀ F : ClosedObservableFramework, Covariant F ↔ Similarity F
  /-- Linear breaks unit freedom. -/
  linear_impossible : ¬ Covariant linearFramework
  /-- Two-orbit breaks one rule. -/
  twoOrbit_impossible : ¬ UniformRule twoOrbitFramework
  /-- Doubling is the self-join and no independent join. -/
  doubling_self_join : LagJoin (fun n => (2 : ℝ) ^ n) 0 ∧
    ∀ k, 1 ≤ k → ¬ LagJoin (fun n => (2 : ℝ) ^ n) k
  /-- Least count picks lag one; lag two is a different ladder. -/
  lag_two_is_not_phi : Constants.phi ^ 3 ≠ Constants.phi ^ 2 + 1
  /-- Adjacent join under similarity is φ. -/
  phi_forced : ∀ (F : ClosedObservableFramework) (ρ : ℝ) (base : F.S),
    (∀ s, F.r (F.T s) = ρ * F.r s) → AdjacentJoin (orbitLevels' F base) → ρ = Constants.phi
  /-- Join-built is a theorem of the adjacent join. -/
  joinBuilt_derived : ∀ s : ℕ → ℝ, AdjacentJoin s → JoinBuilt s
  /-- The φ ladder is the adjacent join. -/
  phi_is_adjacent : AdjacentJoin (fun n => Constants.phi ^ n)
  /-- The row 4 blade follows from the floor facts. -/
  blade_derived : ∀ (F : ClosedObservableFramework) (base : F.S),
    Covariant F → AdjacentJoin (orbitLevels' F base) →
      Similarity F ∧ JoinBuilt (orbitLevels' F base)

theorem cert : RowCert where
  similarity_from_floor := covariant_iff_similarity
  linear_impossible := linear_not_covariant
  twoOrbit_impossible := twoOrbit_not_uniformRule
  doubling_self_join := ⟨doubling_is_self_join, doubling_not_lagJoin_pos⟩
  lag_two_is_not_phi := phi_not_lag_two
  phi_forced := fun _ _ base hρ hj => phi_of_similarity_adjacentJoin hρ base hj
  joinBuilt_derived := joinBuilt_of_adjacentJoin
  phi_is_adjacent := phi_adjacentJoin
  blade_derived := blade_of_covariant_adjacentJoin

end

end Row4Ledger
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
