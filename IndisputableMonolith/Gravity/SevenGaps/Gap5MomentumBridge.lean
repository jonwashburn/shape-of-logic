import IndisputableMonolith.Gravity.SevenGaps.Gap5NetImbalanceDerivation

/-!
# The momentum-magnitude bridge: the scale wall, the exact residual, and what the bridge buys

**Verdict, stated first.** The momentum-magnitude bridge `|p| = |imbalance|` does
**not** derive from the conjunction of every momentum-selecting property the
substrate arc has produced, and this module kernel-checks that wall with the
selection package named exactly. The exhibited family is the scaled ray

    scaledImbalance a z := a * imbalance z        (a ≠ 0)

Every selection property used anywhere in the six-module arc
(`Gap5ChartFromLedgerMomentum` through `Gap5NetImbalanceDerivation`) is
**scale-invariant**: continuity, swap-oddness under the debit-credit exchange,
additivity under ledger consolidation, balance-vanishing, column posting
incidence, net-imbalance reading, debit-axis Cauchy additivity, and
canonical-momentum status against the ledger total all hold of the whole ray at
once (`scaleFreePackage_on_ray`). The bridge holds on the ray exactly at the
unit scale, in three kernel-checked equivalent forms:

    KineticCondition (scaledImbalance a)   ↔  a ^ 2 = 1
    EnergyEqualsCost (scaledImbalance a)   ↔  a ^ 2 = 1
    scaledImbalance a (1, 0) ^ 2 = 1       ↔  a ^ 2 = 1

Hence the conjunction of the scale-free package cannot force the bridge
(`bridge_not_forced_by_scale_free_package`): the unit and double scales agree on
everything the substrate fixes and disagree on the bridge
(`exhibited_pair_disagrees_on_bridge`). The entire residual of flags 6 and 12 on
this lane is one real condition: **the momentum's scale in posting units**. A
derivation must therefore import a scale-bearing premise, and the library names
exactly one candidate: `EnergyEqualsCost` ("energy is the recognition cost"), a
foundational identification of the same kind as T10's R4, recorded as a named
premise in `Gap5MomentumMagnitudeBridge` and shown independent of the B1 package
there. The alternative door is the posting-dynamics conversion theorem
`IsPhysicalMomentumFromPostingDynamics p → p = imbalance` for a stated
scale-bearing predicate, named in the campaign ledger and absent from the
library; the naive generator version of it is already refuted (the orbit
Hamiltonian vector field is `(d / 2, -c / 2)`, not the imbalance).

## The sign is a second, independent residue

The magnitude bridge is sign-blind. `scaledImbalance (-1)` passes the whole
scale-free package and the unit scale, satisfies the kinetic condition and
`EnergyEqualsCost`, and is not `imbalance` (`sign_not_forced_with_unit_scale`).
So even the scale-free package plus the unit scale does not force the signed
identity `p = imbalance`; the sign is pinned only by the signed chart theorem
(`chart_is_the_imbalance_coordinate`), exactly as the campaign plan records.
The constants cluster never sees the sign: `cKin = 2 * lam ^ 2` and
`cMom = 4 * cKin * cGrad` depend on `lam` only through `lam ^ 2`.

## What the bridge buys, kernel-checked as conditionals

1. Equating the stipulated half-imbalance chart `t = 2 * arsinh (lam * p)` with
   the derived imbalance-coordinate chart forces the chart product
   `lam * p = imbalance / (2 * sqrt k)` on every orbit
   (`chart_product_of_stipulated_chart`, via `arsinh` injectivity).
2. With the signed bridge `p = imbalance` the product cancels at any unbalanced
   orbit point: `lam = 1 / (2 * sqrt k)` (`lam_of_signed_bridge`), and at the
   balanced ground state's Casimir `k = 1` this is `lam = 1 / 2`
   (`lam_ground_state_of_signed_bridge`).
3. The magnitude bridge alone (no sign) pins `lam ^ 2 = 1 / (4 * k)` on every
   orbit (`lam_sq_of_magnitude_bridge`), hence at the ground state
   `cKin = 1 / 2` and `cMom = 2 * cGrad`
   (`constants_cluster_of_magnitude_bridge`). The bridge therefore reduces the
   flag-12 constants cluster by one derived number and one derived ratio:
   `{lam, cKin, cGrad, cMom}` with two equations becomes `{cGrad, cMom}` with
   `cMom = 2 * cGrad`, leaving `cGrad` the cluster's one free constant.

## What is NOT claimed

* No flag flip, and no new premise is asserted as derived. The wall is a
  theorem about the named package on the stated `LedgerState` chart carrier
  (quantifier first, per `L-qg-witness-is-not-a-class-20260729`): it refutes
  derivations whose inputs are the scale-free selection properties of the
  existing arc, all at once. It does not touch a derivation importing a
  scale-bearing premise (`EnergyEqualsCost` accepted as a foundational MODEL,
  or a posting-dynamics conversion with scale content).
* The B1 conditional closure is neither used nor strengthened. B1's residue and
  flag 12's blocker are the scale, and the scale is now exhibited as a single
  real condition rather than a predicate on observables.
* The two prior walls this one conjoins stay theorem: the Hamiltonian-data
  polarization witness (`energyEqualsCost_independent_of_hamiltonian_data`)
  and the composition-law independence witness
  (`momentum_additivity_independent_of_composition_law`).

## Scope

Chart carrier `LedgerState` only. No flag moves.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace MomentumBridge

open ChartFromLedgerMomentum MomentumAdditivity MomentumMagnitudeBridge
open EnergyEqualsCostDerivation MomentumAdditivityComposition NetImbalanceDerivation

noncomputable section

/-! ## §0. The scaled ray -/

/-- The scaled imbalance ray: the momentum observable at scale `a` in posting
units. `a = 1` is the library `imbalance`; the bridge asks why `a ^ 2 = 1`. -/
def scaledImbalance (a : ℝ) (z : LedgerState) : ℝ := a * imbalance z

/-! ## §1. Every selection property of the arc is scale-invariant -/

theorem scaledImbalance_continuous (a : ℝ) : Continuous (scaledImbalance a) :=
  continuous_const.mul continuous_imbalance

theorem scaledImbalance_swapOdd (a : ℝ) : SwapOdd (scaledImbalance a) := by
  intro z
  show a * imbalance (z.2, z.1) = -(a * imbalance z)
  rw [imbalance_swap]
  ring

theorem scaledImbalance_additive (a : ℝ) (z w : LedgerState) :
    scaledImbalance a (z + w) = scaledImbalance a z + scaledImbalance a w := by
  show a * imbalance (z + w) = a * imbalance z + a * imbalance w
  rw [imbalance_add]
  ring

theorem scaledImbalance_balance_vanishing (a : ℝ) (z : LedgerState) (hz : Balanced z) :
    scaledImbalance a z = 0 := by
  have hi : imbalance z = 0 := sub_eq_zero.mpr hz
  show a * imbalance z = 0
  rw [hi, mul_zero]

theorem scaledImbalance_postingIncidence (a : ℝ) :
    PostingIncidence (scaledImbalance a) := by
  intro d c
  show a * imbalance (d, c) = a * imbalance (d, 0) + a * imbalance (0, c)
  simp only [imbalance, sub_zero, zero_sub]
  ring

theorem scaledImbalance_readsNet (a : ℝ) : ReadsNetImbalance (scaledImbalance a) := by
  intro z
  show a * imbalance z = a * imbalance (imbalance z, 0)
  simp only [imbalance, sub_zero]

theorem scaledImbalance_additiveOnDebitAxis (a : ℝ) :
    AdditiveOnDebitAxis (scaledImbalance a) := by
  intro m n
  show a * imbalance (m, 0) + a * imbalance (n, 0) = a * imbalance (m + n, 0)
  simp only [imbalance, sub_zero]
  ring

/-- The Poisson bracket of the scaled imbalance with the ledger total, in the
coefficient form of `EnergyEqualsCostDerivation.poissonLin`: `{a • imbalance,
total} = 2 a`, nonzero at every nonzero scale. Canonical-momentum status is
therefore scale-invariant. -/
theorem scaledImbalance_conjugate_bracket (a : ℝ) :
    poissonLin a (-a) 1 1 = 2 * a := by
  show a * 1 - (-a) * 1 = 2 * a
  ring

/-! ## §2. The bridge on the ray is exactly the unit-scale condition -/

theorem scaledImbalance_unit_sq (a : ℝ) :
    scaledImbalance a ((1, 0) : LedgerState) ^ 2 = a ^ 2 := by
  simp only [scaledImbalance, imbalance, sub_zero, mul_one]

/-- **The kinetic condition on the ray is `a ^ 2 = 1`.** Forward by evaluation
at the pure unit debit; backward by factoring the square. -/
theorem kineticCondition_on_ray_iff (a : ℝ) :
    KineticCondition (scaledImbalance a) ↔ a ^ 2 = 1 := by
  constructor
  · intro h
    have h1 := h ((1, 0) : LedgerState)
    have hi : imbalance ((1, 0) : LedgerState) = 1 := by simp [imbalance]
    rw [hi, scaledImbalance_unit_sq, one_pow] at h1
    exact h1
  · intro h z
    show (a * imbalance z) ^ 2 = imbalance z ^ 2
    rw [mul_pow, h, one_mul]

/-- **Energy-equals-cost on the ray is `a ^ 2 = 1`.** Forward by cancelling the
orbit imbalance at a point where it is nonzero; backward by the existing
exactness theorem `energy_equals_cost_of_imbalance`. -/
theorem energyEqualsCost_on_ray_iff (a : ℝ) :
    EnergyEqualsCost (scaledImbalance a) ↔ a ^ 2 = 1 := by
  constructor
  · intro h
    have h1 := h 1 2 one_pos
    change (a * imbalance (orbitPoint (1 : ℝ) 2)) ^ 2 =
      2 * (1 : ℝ) * Cost.Jlog 2 at h1
    have hbase := energy_equals_cost_of_imbalance 1 2 one_pos
    have himb_ne : imbalance (orbitPoint (1 : ℝ) 2) ≠ 0 := by
      have e : imbalance (orbitPoint (1 : ℝ) 2) = 2 * Real.sinh 1 := by
        rw [orbitPoint_imbalance, Real.sqrt_one, one_mul,
          show (2 : ℝ) / 2 = 1 from by norm_num]
      have hsin : 0 < Real.sinh 1 := by
        have hs := Real.sinh_lt_sinh.mpr (by norm_num : (0 : ℝ) < 1)
        rwa [Real.sinh_zero] at hs
      rw [e]
      exact (mul_pos (by norm_num) hsin).ne'
    have e : (a * imbalance (orbitPoint (1 : ℝ) 2)) ^ 2 =
        imbalance (orbitPoint (1 : ℝ) 2) ^ 2 := h1.trans hbase.symm
    rw [mul_pow] at e
    have e2 : a ^ 2 * imbalance (orbitPoint (1 : ℝ) 2) ^ 2 =
        1 * imbalance (orbitPoint (1 : ℝ) 2) ^ 2 := by
      rw [e, one_mul]
    exact mul_right_cancel₀ (pow_ne_zero 2 himb_ne) e2
  · intro h k t hk
    show (a * imbalance (orbitPoint k t)) ^ 2 = 2 * k * Cost.Jlog t
    rw [mul_pow, h, one_mul]
    exact energy_equals_cost_of_imbalance k t hk

/-- The unit normalization on the ray is the same condition. -/
theorem unit_norm_on_ray_iff (a : ℝ) :
    scaledImbalance a ((1, 0) : LedgerState) ^ 2 = 1 ↔ a ^ 2 = 1 := by
  rw [scaledImbalance_unit_sq]

/-! ## §3. The scale-free package, named exactly, and the wall -/

/-- **The scale-free momentum package: X, named exactly.** Every property the
six-module substrate arc used to select the momentum observable, gathered as
one predicate. The wall theorem below shows the package holds of the whole
scaled ray, while the bridge holds only at unit scale. -/
structure ScaleFreeMomentumPackage (p : LedgerState → ℝ) : Prop where
  /-- Regularity premise of the B1 certificate. -/
  continuous : Continuous p
  /-- Oddness under the substrate's debit-credit exchange. -/
  swap_odd : SwapOdd p
  /-- Extensivity under ledger consolidation. -/
  consolidation_additive : ∀ z w : LedgerState, p (z + w) = p z + p w
  /-- Vanishing on the double-entry balance locus. -/
  balance_vanishing : ∀ z : LedgerState, Balanced z → p z = 0
  /-- Column posting incidence: the two columns contribute independently. -/
  posting_incidence : PostingIncidence p
  /-- The momentum reads only the net charge. -/
  reads_net_imbalance : ReadsNetImbalance p
  /-- The one-dimensional Cauchy property on the pure-debit axis. -/
  debit_axis_additive : AdditiveOnDebitAxis p
  /-- Canonical-momentum status: `p` is a linear observable with nonzero
  Poisson bracket against the ledger total (conjugate up to normalization). -/
  canonical_bracket : ∃ a₁ b₁ : ℝ, poissonLin a₁ b₁ 1 1 ≠ 0 ∧
    (∀ z : LedgerState, p z = a₁ * z.1 + b₁ * z.2)

/-- **The package is scale-invariant.** Every nonzero rescaling of the
imbalance satisfies all eight selection properties at once. -/
theorem scaleFreePackage_on_ray {a : ℝ} (ha : a ≠ 0) :
    ScaleFreeMomentumPackage (scaledImbalance a) where
  continuous := scaledImbalance_continuous a
  swap_odd := scaledImbalance_swapOdd a
  consolidation_additive := scaledImbalance_additive a
  balance_vanishing := scaledImbalance_balance_vanishing a
  posting_incidence := scaledImbalance_postingIncidence a
  reads_net_imbalance := scaledImbalance_readsNet a
  debit_axis_additive := scaledImbalance_additiveOnDebitAxis a
  canonical_bracket :=
    ⟨a, -a, by
      rw [scaledImbalance_conjugate_bracket]
      exact mul_ne_zero two_ne_zero ha,
      fun z => by
        simp only [scaledImbalance, imbalance]
        ring⟩

/-- **THE WALL: the bridge is not forced by the scale-free package.** The
eight-property package holds of the entire ray (`∀ a ≠ 0`); the kinetic
condition, `EnergyEqualsCost`, and the unit normalization each hold on the ray
exactly at `a ^ 2 = 1`; and the double-scale member exhibits all eight
properties together with the failure of the bridge. X is the package above,
named property by property. -/
theorem bridge_not_forced_by_scale_free_package :
    (∀ a : ℝ, a ≠ 0 → ScaleFreeMomentumPackage (scaledImbalance a)) ∧
    (∀ a : ℝ, KineticCondition (scaledImbalance a) ↔ a ^ 2 = 1) ∧
    (∀ a : ℝ, EnergyEqualsCost (scaledImbalance a) ↔ a ^ 2 = 1) ∧
    (∀ a : ℝ, scaledImbalance a ((1, 0) : LedgerState) ^ 2 = 1 ↔ a ^ 2 = 1) ∧
    (ScaleFreeMomentumPackage (scaledImbalance 2) ∧
      ¬ KineticCondition (scaledImbalance 2) ∧
      ¬ EnergyEqualsCost (scaledImbalance 2)) ∧
    (ScaleFreeMomentumPackage (scaledImbalance 1) ∧
      KineticCondition (scaledImbalance 1) ∧
      EnergyEqualsCost (scaledImbalance 1)) :=
  ⟨fun a ha => scaleFreePackage_on_ray ha,
    kineticCondition_on_ray_iff, energyEqualsCost_on_ray_iff, unit_norm_on_ray_iff,
    ⟨scaleFreePackage_on_ray two_ne_zero,
      (kineticCondition_on_ray_iff 2).not.mpr (by norm_num),
      (energyEqualsCost_on_ray_iff 2).not.mpr (by norm_num)⟩,
    ⟨scaleFreePackage_on_ray one_ne_zero,
      (kineticCondition_on_ray_iff 1).mpr (by norm_num),
      (energyEqualsCost_on_ray_iff 1).mpr (by norm_num)⟩⟩

/-- **The exhibited pair.** Unit and double scale agree on everything the
substrate fixes (all eight selection properties) and disagree on the bridge.
This is the "agreeing on X, differing on the bridge" witness the campaign asked
for, with X the package named above. -/
theorem exhibited_pair_disagrees_on_bridge :
    ScaleFreeMomentumPackage (scaledImbalance 1) ∧
    ScaleFreeMomentumPackage (scaledImbalance 2) ∧
    KineticCondition (scaledImbalance 1) ∧ ¬ KineticCondition (scaledImbalance 2) :=
  ⟨scaleFreePackage_on_ray one_ne_zero, scaleFreePackage_on_ray two_ne_zero,
    (kineticCondition_on_ray_iff 1).mpr (by norm_num),
    (kineticCondition_on_ray_iff 2).not.mpr (by norm_num)⟩

/-! ## §4. The sign is a second residue -/

/-- **The sign wall.** `scaledImbalance (-1)` passes the entire scale-free
package, the unit scale, the kinetic condition, and `EnergyEqualsCost`, and is
not `imbalance`. The scale-free package plus the unit scale therefore does not
force the signed identity `p = imbalance`; the sign is pinned only by the
signed chart. The magnitude bridge and the constants cluster are sign-blind. -/
theorem sign_not_forced_with_unit_scale :
    ScaleFreeMomentumPackage (scaledImbalance (-1)) ∧
    scaledImbalance (-1) ((1, 0) : LedgerState) ^ 2 = 1 ∧
    KineticCondition (scaledImbalance (-1)) ∧
    EnergyEqualsCost (scaledImbalance (-1)) ∧
    scaledImbalance (-1) ≠ imbalance := by
  refine ⟨scaleFreePackage_on_ray (by norm_num), ?_, ?_, ?_, ?_⟩
  · rw [scaledImbalance_unit_sq]
    norm_num
  · exact (kineticCondition_on_ray_iff _).mpr (by norm_num)
  · exact (energyEqualsCost_on_ray_iff _).mpr (by norm_num)
  · intro h
    have h1 := congrFun h ((1, 0) : LedgerState)
    have e1 : scaledImbalance (-1) ((1, 0) : LedgerState) = -1 := by
      simp only [scaledImbalance, imbalance, sub_zero, mul_one]
    have e2 : imbalance ((1, 0) : LedgerState) = 1 := by simp [imbalance]
    rw [e1, e2] at h1
    norm_num at h1

/-! ## §5. What the bridge buys on the cMom cluster -/

/-- **The chart product from the two chart forms.** The stipulated chart
`t = 2 * arsinh (lam * p)` and the derived imbalance-coordinate chart
(`chart_is_the_imbalance_coordinate`) agree on every orbit, and `arsinh` is
injective, so `lam * p = imbalance / (2 * sqrt k)` on every orbit. This is the
joint product the C2 Casimir lead could not split. -/
theorem chart_product_of_stipulated_chart (k lam : ℝ) (p : LedgerState → ℝ)
    (hk : 0 < k)
    (hstip : ∀ t : ℝ, t = 2 * Real.arsinh (lam * p (orbitPoint k t))) (t : ℝ) :
    lam * p (orbitPoint k t) = imbalance (orbitPoint k t) / (2 * Real.sqrt k) := by
  have h2 := chart_is_the_imbalance_coordinate k t hk
  have h3 : 2 * Real.arsinh (lam * p (orbitPoint k t)) =
      2 * Real.arsinh (imbalance (orbitPoint k t) / (2 * Real.sqrt k)) := by
    rw [← hstip t]
    exact h2
  have h4 : Real.arsinh (lam * p (orbitPoint k t)) =
      Real.arsinh (imbalance (orbitPoint k t) / (2 * Real.sqrt k)) := by
    linarith [h3]
  exact Real.arsinh_injective h4

/-- The orbit imbalance at `t = 2 * arsinh 1` is `2 * sqrt k`, nonzero at
positive Casimir: the cancellation point for splitting the chart product. -/
theorem imbalance_orbitPoint_at_two_arsinh_one (k : ℝ) :
    imbalance (orbitPoint k (2 * Real.arsinh 1)) = 2 * Real.sqrt k := by
  rw [orbitPoint_imbalance,
    show (2 * Real.arsinh (1 : ℝ)) / 2 = Real.arsinh 1 from by ring,
    Real.sinh_arsinh]
  ring

/-- **With the signed bridge, the chart's free constant is the inverse ledger
scale.** `lam = 1 / (2 * sqrt k)`: the product the C2 Casimir lead wanted is
split by the bridge, and `k` is the only remaining freedom (the orbit's
Casimir, fixed at `1` on the balanced ground state). -/
theorem lam_of_signed_bridge (k lam : ℝ) (hk : 0 < k)
    (hchart : ∀ t : ℝ, lam * imbalance (orbitPoint k t) =
      imbalance (orbitPoint k t) / (2 * Real.sqrt k)) :
    lam = 1 / (2 * Real.sqrt k) := by
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have himb := imbalance_orbitPoint_at_two_arsinh_one k
  have hne : imbalance (orbitPoint k (2 * Real.arsinh 1)) ≠ 0 := by
    rw [himb]
    exact (mul_pos (by norm_num) hsk).ne'
  have h0 := hchart (2 * Real.arsinh 1)
  rw [himb] at h0
  have h1 : lam * (2 * Real.sqrt k) = 1 := by
    rw [h0]
    exact div_self (mul_ne_zero two_ne_zero hsk.ne')
  exact (eq_div_iff (mul_ne_zero two_ne_zero hsk.ne')).mpr h1

/-- The signed bridge composed with the stipulated chart: `lam` is the inverse
ledger scale. This is the C2 Casimir lead's conclusion, now with its premise
(the signed bridge) named in the hypothesis instead of smuggled. -/
theorem lam_of_signed_bridge_at_stipulated_chart (k lam : ℝ) (p : LedgerState → ℝ)
    (hk : 0 < k) (hp : p = imbalance)
    (hstip : ∀ t : ℝ, t = 2 * Real.arsinh (lam * p (orbitPoint k t))) :
    lam = 1 / (2 * Real.sqrt k) := by
  apply lam_of_signed_bridge k lam hk
  intro t
  have h := chart_product_of_stipulated_chart k lam p hk hstip t
  rwa [hp] at h

/-- **The magnitude bridge alone pins `lam ^ 2` on every orbit.** Squaring the
chart product and using the kinetic identity kills the momentum factor and the
sign: no signed identification is needed for the constants cluster. -/
theorem lam_sq_of_magnitude_bridge (k lam : ℝ) (p : LedgerState → ℝ) (hk : 0 < k)
    (hkin : ∀ t : ℝ, p (orbitPoint k t) ^ 2 = imbalance (orbitPoint k t) ^ 2)
    (hchart : ∀ t : ℝ, lam * p (orbitPoint k t) =
      imbalance (orbitPoint k t) / (2 * Real.sqrt k)) :
    lam ^ 2 = 1 / (4 * k) := by
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have himb := imbalance_orbitPoint_at_two_arsinh_one k
  have hne : imbalance (orbitPoint k (2 * Real.arsinh 1)) ≠ 0 := by
    rw [himb]
    exact (mul_pos (by norm_num) hsk).ne'
  have h0 := hchart (2 * Real.arsinh 1)
  have hk0 := hkin (2 * Real.arsinh 1)
  have hsq : lam ^ 2 * p (orbitPoint k (2 * Real.arsinh 1)) ^ 2 =
      imbalance (orbitPoint k (2 * Real.arsinh 1)) ^ 2 / (4 * k) := by
    have e : (lam * p (orbitPoint k (2 * Real.arsinh 1))) ^ 2 =
        (imbalance (orbitPoint k (2 * Real.arsinh 1)) / (2 * Real.sqrt k)) ^ 2 := by
      rw [h0]
    rw [mul_pow, div_pow] at e
    have hden : (2 * Real.sqrt k) ^ 2 = 4 * k := by
      calc (2 * Real.sqrt k) ^ 2 = 4 * (Real.sqrt k ^ 2) := by ring
        _ = 4 * k := by rw [Real.sq_sqrt hk.le]
    rw [hden] at e
    exact e
  rw [hk0] at hsq
  have hm2 : imbalance (orbitPoint k (2 * Real.arsinh 1)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hne
  have hsq2 : lam ^ 2 * imbalance (orbitPoint k (2 * Real.arsinh 1)) ^ 2 =
      (1 / (4 * k)) * imbalance (orbitPoint k (2 * Real.arsinh 1)) ^ 2 := by
    rw [hsq, ← mul_one_div (imbalance (orbitPoint k (2 * Real.arsinh 1)) ^ 2) (4 * k)]
    exact mul_comm _ _
  exact mul_right_cancel₀ hm2 hsq2

/-- **What the bridge buys on `cMom = 4 * cKin * cGrad`.** At the balanced
ground state's Casimir (`k = 1`) the magnitude bridge gives `lam ^ 2 = 1 / 4`;
with `cKin = 2 * lam ^ 2` derived this is `cKin = 1 / 2`, and the cMom equation
collapses to `cMom = 2 * cGrad`. One derived number and one derived ratio;
`cGrad` remains the cluster's one free constant. -/
theorem constants_cluster_of_magnitude_bridge {lam cKin cGrad cMom : ℝ}
    (hlam : lam ^ 2 = 1 / 4) (hcKin : cKin = 2 * lam ^ 2)
    (hcMom : cMom = 4 * cKin * cGrad) :
    cKin = 1 / 2 ∧ cMom = 2 * cGrad := by
  refine ⟨?_, ?_⟩
  · rw [hcKin, hlam]
    norm_num
  · rw [hcMom, hcKin, hlam]
    ring

/-- At the ground state the signed bridge gives `lam = 1 / 2`. -/
theorem lam_ground_state_of_signed_bridge {lam : ℝ}
    (hstip : ∀ t : ℝ, t = 2 * Real.arsinh (lam * imbalance (orbitPoint 1 t))) :
    lam = 1 / 2 := by
  have h := lam_of_signed_bridge_at_stipulated_chart 1 lam imbalance one_pos rfl hstip
  rwa [Real.sqrt_one, mul_one] at h

/-- The full ground-state cluster from the signed bridge, composed:
`lam = 1 / 2`, `cKin = 1 / 2`, `cMom = 2 * cGrad`. -/
theorem ground_state_cluster_of_signed_bridge {lam cKin cGrad cMom : ℝ}
    (hstip : ∀ t : ℝ, t = 2 * Real.arsinh (lam * imbalance (orbitPoint 1 t)))
    (hcKin : cKin = 2 * lam ^ 2) (hcMom : cMom = 4 * cKin * cGrad) :
    lam = 1 / 2 ∧ cKin = 1 / 2 ∧ cMom = 2 * cGrad := by
  have hlam := lam_ground_state_of_signed_bridge hstip
  refine ⟨hlam, ?_, ?_⟩
  · rw [hcKin, hlam]
    norm_num
  · rw [hcMom, hcKin, hlam]
    ring

/-! ## §6. The verdict certificate -/

/-- **The bridge verdict, packaged.** The scale-free package is scale-invariant;
the bridge on the ray is exactly the unit-scale condition in three equivalent
forms; the unit/double pair disagrees on the bridge while agreeing on the
package; the sign survives the unit scale; and the bridge's downstream content
for the cMom cluster is the four conditional theorems. -/
structure MomentumBridgeVerdict : Prop where
  /-- X, named exactly, holds of the whole ray. -/
  package_scale_free : ∀ a : ℝ, a ≠ 0 → ScaleFreeMomentumPackage (scaledImbalance a)
  /-- The kinetic condition on the ray is the unit-scale condition. -/
  kinetic_on_ray_iff_unit : ∀ a : ℝ, KineticCondition (scaledImbalance a) ↔ a ^ 2 = 1
  /-- Energy-equals-cost on the ray is the unit-scale condition. -/
  eec_on_ray_iff_unit : ∀ a : ℝ, EnergyEqualsCost (scaledImbalance a) ↔ a ^ 2 = 1
  /-- The unit normalization on the ray is the unit-scale condition. -/
  unit_norm_on_ray_iff_unit : ∀ a : ℝ,
    scaledImbalance a ((1, 0) : LedgerState) ^ 2 = 1 ↔ a ^ 2 = 1
  /-- The wall, pair form. -/
  pair_disagrees_on_bridge :
    ScaleFreeMomentumPackage (scaledImbalance 1) ∧
    ScaleFreeMomentumPackage (scaledImbalance 2) ∧
    KineticCondition (scaledImbalance 1) ∧ ¬ KineticCondition (scaledImbalance 2)
  /-- The sign wall. -/
  sign_free_at_unit_scale :
    ScaleFreeMomentumPackage (scaledImbalance (-1)) ∧
    scaledImbalance (-1) ((1, 0) : LedgerState) ^ 2 = 1 ∧
    KineticCondition (scaledImbalance (-1)) ∧
    EnergyEqualsCost (scaledImbalance (-1)) ∧
    scaledImbalance (-1) ≠ imbalance
  /-- The chart product from the two chart forms. -/
  chart_product : ∀ (k lam : ℝ) (p : LedgerState → ℝ), 0 < k →
    (∀ t : ℝ, t = 2 * Real.arsinh (lam * p (orbitPoint k t))) → ∀ t : ℝ,
      lam * p (orbitPoint k t) = imbalance (orbitPoint k t) / (2 * Real.sqrt k)
  /-- Signed bridge splits the product. -/
  lam_of_signed : ∀ (k lam : ℝ), 0 < k →
    (∀ t : ℝ, lam * imbalance (orbitPoint k t) =
      imbalance (orbitPoint k t) / (2 * Real.sqrt k)) →
      lam = 1 / (2 * Real.sqrt k)
  /-- Magnitude bridge pins `lam ^ 2`. -/
  lam_sq_of_magnitude : ∀ (k lam : ℝ) (p : LedgerState → ℝ), 0 < k →
    (∀ t : ℝ, p (orbitPoint k t) ^ 2 = imbalance (orbitPoint k t) ^ 2) →
    (∀ t : ℝ, lam * p (orbitPoint k t) =
      imbalance (orbitPoint k t) / (2 * Real.sqrt k)) →
      lam ^ 2 = 1 / (4 * k)
  /-- Ground-state constants from the magnitude bridge. -/
  ground_cluster_of_magnitude : ∀ lam cKin cGrad cMom : ℝ,
    lam ^ 2 = 1 / 4 → cKin = 2 * lam ^ 2 → cMom = 4 * cKin * cGrad →
      cKin = 1 / 2 ∧ cMom = 2 * cGrad
  /-- Ground-state `lam` from the signed bridge. -/
  ground_lam_of_signed : ∀ lam : ℝ,
    (∀ t : ℝ, t = 2 * Real.arsinh (lam * imbalance (orbitPoint 1 t))) → lam = 1 / 2

theorem momentumBridgeVerdict : MomentumBridgeVerdict where
  package_scale_free := fun _a ha => scaleFreePackage_on_ray ha
  kinetic_on_ray_iff_unit := kineticCondition_on_ray_iff
  eec_on_ray_iff_unit := energyEqualsCost_on_ray_iff
  unit_norm_on_ray_iff_unit := unit_norm_on_ray_iff
  pair_disagrees_on_bridge := exhibited_pair_disagrees_on_bridge
  sign_free_at_unit_scale := sign_not_forced_with_unit_scale
  chart_product := chart_product_of_stipulated_chart
  lam_of_signed := lam_of_signed_bridge
  lam_sq_of_magnitude := lam_sq_of_magnitude_bridge
  ground_cluster_of_magnitude := fun lam cKin cGrad cMom =>
    constants_cluster_of_magnitude_bridge (lam := lam) (cKin := cKin) (cGrad := cGrad)
      (cMom := cMom)
  ground_lam_of_signed := fun lam => lam_ground_state_of_signed_bridge (lam := lam)

/-! ## Axiom audit -/

#print axioms scaledImbalance_continuous
#print axioms scaledImbalance_swapOdd
#print axioms scaledImbalance_additive
#print axioms scaledImbalance_balance_vanishing
#print axioms scaledImbalance_postingIncidence
#print axioms scaledImbalance_readsNet
#print axioms scaledImbalance_additiveOnDebitAxis
#print axioms scaledImbalance_conjugate_bracket
#print axioms scaledImbalance_unit_sq
#print axioms kineticCondition_on_ray_iff
#print axioms energyEqualsCost_on_ray_iff
#print axioms unit_norm_on_ray_iff
#print axioms scaleFreePackage_on_ray
#print axioms bridge_not_forced_by_scale_free_package
#print axioms exhibited_pair_disagrees_on_bridge
#print axioms sign_not_forced_with_unit_scale
#print axioms chart_product_of_stipulated_chart
#print axioms imbalance_orbitPoint_at_two_arsinh_one
#print axioms lam_of_signed_bridge
#print axioms lam_of_signed_bridge_at_stipulated_chart
#print axioms lam_sq_of_magnitude_bridge
#print axioms constants_cluster_of_magnitude_bridge
#print axioms lam_ground_state_of_signed_bridge
#print axioms ground_state_cluster_of_signed_bridge
#print axioms momentumBridgeVerdict

end

end MomentumBridge
end SevenGaps
end Gravity
end IndisputableMonolith
