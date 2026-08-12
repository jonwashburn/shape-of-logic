import IndisputableMonolith.Gravity.SevenGaps.Gap5MomentumBridge

/-!
# Hostile probe for A24 Gap5MomentumBridge (review 2026-07-30)

Adversarial module against `Gap5MomentumBridge`. Edits nothing in the reviewed
module. Leave uncommitted.

Attacks:
1. Ray witness: `scaleFreePackage_on_ray` at `a = 2`, kinetic/EEC iff `a^2 = 1`.
2. Sign residue: `scaledImbalance (-1)` passes package + kinetic + EEC, ≠ imbalance.
3. Chart product at a concrete orbit point (stipulated vs derived forms).
4. Ground-state algebra: `lam^2 = 1/4` ⇒ `cKin = 1/2 ∧ cMom = 2 cGrad`.
5. Axiom re-audit on five load-bearing certificates (incl. the wall and cluster).
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap5MomentumBridgeHostileProbe

open ChartFromLedgerMomentum MomentumAdditivity MomentumMagnitudeBridge
open EnergyEqualsCostDerivation MomentumBridge

noncomputable section

/-! ## 1. Ray witness at a = 2 -/

theorem probe_package_at_two :
    ScaleFreeMomentumPackage (scaledImbalance 2) :=
  scaleFreePackage_on_ray two_ne_zero

theorem probe_kinetic_iff_unit (a : ℝ) :
    KineticCondition (scaledImbalance a) ↔ a ^ 2 = 1 :=
  kineticCondition_on_ray_iff a

theorem probe_kinetic_fails_at_two :
    ¬ KineticCondition (scaledImbalance 2) :=
  (kineticCondition_on_ray_iff 2).not.mpr (by norm_num)

theorem probe_eec_fails_at_two :
    ¬ EnergyEqualsCost (scaledImbalance 2) :=
  (energyEqualsCost_on_ray_iff 2).not.mpr (by norm_num)

theorem probe_kinetic_holds_at_one :
    KineticCondition (scaledImbalance 1) :=
  (kineticCondition_on_ray_iff 1).mpr (by norm_num)

theorem probe_wall :
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
  bridge_not_forced_by_scale_free_package

theorem probe_exhibited_pair :
    ScaleFreeMomentumPackage (scaledImbalance 1) ∧
    ScaleFreeMomentumPackage (scaledImbalance 2) ∧
    KineticCondition (scaledImbalance 1) ∧ ¬ KineticCondition (scaledImbalance 2) :=
  exhibited_pair_disagrees_on_bridge

/-! ## 2. Sign residue at unit scale -/

theorem probe_sign_wall :
    ScaleFreeMomentumPackage (scaledImbalance (-1)) ∧
    scaledImbalance (-1) ((1, 0) : LedgerState) ^ 2 = 1 ∧
    KineticCondition (scaledImbalance (-1)) ∧
    EnergyEqualsCost (scaledImbalance (-1)) ∧
    scaledImbalance (-1) ≠ imbalance :=
  sign_not_forced_with_unit_scale

theorem probe_neg_one_is_neg_imbalance (z : LedgerState) :
    scaledImbalance (-1) z = - imbalance z := by
  simp only [scaledImbalance]
  ring

theorem probe_neg_one_ne_imbalance_at_unit_debit :
    scaledImbalance (-1) ((1, 0) : LedgerState) ≠
      imbalance ((1, 0) : LedgerState) := by
  simp only [scaledImbalance, imbalance, sub_zero, mul_one]
  norm_num

/-! ## 3. Chart product: stipulated form matches library derived chart -/

/-- Instantiating the stipulated chart at `p = imbalance` and
`lam = 1/(2√k)` recovers the library theorem `chart_is_the_imbalance_coordinate`. -/
theorem probe_stipulated_matches_derived (k t : ℝ) (hk : 0 < k) :
    t = 2 * Real.arsinh
      ((1 / (2 * Real.sqrt k)) * imbalance (orbitPoint k t)) := by
  have h := chart_is_the_imbalance_coordinate k t hk
  -- rewrite the derived chart into the stipulated half-imbalance shape
  have e : (1 / (2 * Real.sqrt k)) * imbalance (orbitPoint k t) =
      imbalance (orbitPoint k t) / (2 * Real.sqrt k) := by
    field_simp
  rwa [e]

theorem probe_chart_product_on_imbalance (k : ℝ) (hk : 0 < k) (t : ℝ) :
    (1 / (2 * Real.sqrt k)) * imbalance (orbitPoint k t) =
      imbalance (orbitPoint k t) / (2 * Real.sqrt k) := by
  have hstip : ∀ s : ℝ,
      s = 2 * Real.arsinh
        ((1 / (2 * Real.sqrt k)) * imbalance (orbitPoint k s)) :=
    fun s => probe_stipulated_matches_derived k s hk
  exact chart_product_of_stipulated_chart k (1 / (2 * Real.sqrt k))
    imbalance hk hstip t

/-! ## 4. Ground-state constants cluster (k = 1 ⇒ lam² = 1/4) -/

theorem probe_lam_sq_at_ground_from_bridge (lam : ℝ) (p : LedgerState → ℝ)
    (hkin : ∀ t : ℝ, p (orbitPoint 1 t) ^ 2 = imbalance (orbitPoint 1 t) ^ 2)
    (hchart : ∀ t : ℝ, lam * p (orbitPoint 1 t) =
      imbalance (orbitPoint 1 t) / (2 * Real.sqrt 1)) :
    lam ^ 2 = 1 / 4 := by
  have h := lam_sq_of_magnitude_bridge 1 lam p one_pos hkin hchart
  rwa [mul_one] at h

theorem probe_constants_cluster (lam cKin cGrad cMom : ℝ)
    (hlam : lam ^ 2 = 1 / 4) (hcKin : cKin = 2 * lam ^ 2)
    (hcMom : cMom = 4 * cKin * cGrad) :
    cKin = 1 / 2 ∧ cMom = 2 * cGrad :=
  constants_cluster_of_magnitude_bridge (lam := lam) (cKin := cKin)
    (cGrad := cGrad) (cMom := cMom) hlam hcKin hcMom

/-- Off ground state the same algebra gives `cKin = 1/(2k)` when
`lam^2 = 1/(4k)` and `cKin = 2 lam^2`. -/
theorem probe_cKin_k_dependence (k lam cKin : ℝ) (hk : 0 < k)
    (hlam : lam ^ 2 = 1 / (4 * k)) (hcKin : cKin = 2 * lam ^ 2) :
    cKin = 1 / (2 * k) := by
  rw [hcKin, hlam]
  field_simp
  ring

end

#print axioms probe_package_at_two
#print axioms probe_kinetic_iff_unit
#print axioms probe_wall
#print axioms probe_sign_wall
#print axioms probe_constants_cluster

end Gap5MomentumBridgeHostileProbe
end SevenGaps
end Gravity
end IndisputableMonolith
