import Mathlib
import IndisputableMonolith.Masses.Anchor
import IndisputableMonolith.Verification.YardstickAssignmentPrinciple

/-!
# Yardstick Assignment Choice-Set Enumeration (O1 Progress)

This module makes the O1 discussion explicit as a finite combinatorial search:

- Start from the four candidate `B_pow` values and the four candidate `r0` values.
- Enumerate all sector-to-value assignments (all permutations).
- Filter by structural constraints used in the Yardstick discussion.

The resulting valid choice sets collapse to singletons for both `B_pow` and `r0`
under these constraints.
-/

namespace IndisputableMonolith
namespace Verification
namespace YardstickAssignmentChoiceSet

open Masses.Anchor

/-! ## `B_pow` assignment search -/

structure BPowAssignment where
  lepton : ℤ
  up : ℤ
  down : ℤ
  ew : ℤ
  deriving Repr, DecidableEq

def canonicalBPow : BPowAssignment :=
  { lepton := -(2 * (E_passive : ℤ))
  , up := -(A : ℤ)
  , down := 2 * (E_total : ℤ) - 1
  , ew := (A : ℤ) }

/-- Orientation-reflected counterpart of `canonicalBPow` (same magnitudes, flipped active-edge sign). -/
def mirroredBPow : BPowAssignment :=
  { lepton := -(2 * (E_passive : ℤ))
  , up := (A : ℤ)
  , down := 2 * (E_total : ℤ) - 1
  , ew := -(A : ℤ) }

def bPowValuePool : List ℤ :=
  [ -(2 * (E_passive : ℤ))
  , -(A : ℤ)
  , 2 * (E_total : ℤ) - 1
  , (A : ℤ) ]

theorem bpow_pool_matches_anchor_formulas :
    bPowValuePool =
      [B_pow .Lepton, B_pow .UpQuark, B_pow .DownQuark, B_pow .Electroweak] := by
  rfl

def listToBPowAssignment? : List ℤ → Option BPowAssignment
  | [l, u, d, e] => some { lepton := l, up := u, down := d, ew := e }
  | _ => none

def allBPowAssignments : List BPowAssignment :=
  (bPowValuePool.permutations.filterMap listToBPowAssignment?)

/-- Structural B_pow sum target (`A = 1`). -/
def bpowSumTarget : ℤ := (A : ℤ)

theorem bpow_sum_target_eq_one : bpowSumTarget = 1 := by
  native_decide

theorem bpow_sum_target_matches_principle :
    bpowSumTarget =
      (B_pow .Lepton + B_pow .UpQuark + B_pow .DownQuark + B_pow .Electroweak) := by
  calc
    bpowSumTarget = 1 := bpow_sum_target_eq_one
    _ = (B_pow .Lepton + B_pow .UpQuark + B_pow .DownQuark + B_pow .Electroweak) := by
      symm
      exact YardstickAssignmentPrinciple.B_pow_sum

/-- Structural constraints used to filter `B_pow` assignments. -/
def bpowStructuralConstraints (a : BPowAssignment) : Bool :=
  decide (a.up = -a.ew) &&
  decide ((Int.natAbs a.lepton : ℤ) + (Int.natAbs a.ew : ℤ) = a.down) &&
  decide (a.up < 0) &&
  decide (0 < a.ew) &&
  decide (a.lepton + a.up + a.down + a.ew = bpowSumTarget)

/-- Prop-level version of `bpowStructuralConstraints`. -/
def bpowPrincipleConstraints (a : BPowAssignment) : Prop :=
  a.up = -a.ew ∧
  ((Int.natAbs a.lepton : ℤ) + (Int.natAbs a.ew : ℤ) = a.down) ∧
  a.up < 0 ∧
  0 < a.ew ∧
  (a.lepton + a.up + a.down + a.ew = bpowSumTarget)

def validBPowAssignments : List BPowAssignment :=
  allBPowAssignments.filter bpowStructuralConstraints

theorem all_bpow_assignments_count : allBPowAssignments.length = 24 := by
  native_decide

theorem valid_bpow_assignment_count : validBPowAssignments.length = 1 := by
  native_decide

theorem valid_bpow_assignments_are_singleton :
    validBPowAssignments = [canonicalBPow] := by
  native_decide

theorem bpow_constraints_true_iff (a : BPowAssignment) :
    bpowStructuralConstraints a = true ↔ bpowPrincipleConstraints a := by
  unfold bpowStructuralConstraints bpowPrincipleConstraints
  simp
  tauto

theorem bpow_constraints_force_canonical (a : BPowAssignment)
    (ha : a ∈ allBPowAssignments)
    (hP : bpowPrincipleConstraints a) :
    a = canonicalBPow := by
  have htrue : bpowStructuralConstraints a = true := (bpow_constraints_true_iff a).2 hP
  have hmem : a ∈ validBPowAssignments := by
    unfold validBPowAssignments
    exact List.mem_filter.mpr ⟨ha, htrue⟩
  rw [valid_bpow_assignments_are_singleton] at hmem
  simpa using hmem

/-- Normal form implied by `B_pow` principle constraints:
    active-edge pair is fixed (`ew = 1`, `up = -1`), the down value is `1 - lepton`,
    and lepton is necessarily nonpositive. -/
theorem bpow_principle_normal_form (a : BPowAssignment)
    (hP : bpowPrincipleConstraints a) :
    a.ew = 1 ∧ a.up = -1 ∧ a.down = 1 - a.lepton ∧ a.lepton ≤ 0 := by
  rcases hP with ⟨hSign, hComp, _hUpNeg, hEwPos, hSum⟩
  have hsum' : a.lepton + a.down = bpowSumTarget := by
    nlinarith [hSum, hSign]
  have hsum1 : a.lepton + a.down = 1 := by
    simpa [bpow_sum_target_eq_one] using hsum'
  have hCompAbs : |a.lepton| + |a.ew| = a.down := by
    simpa [Int.natCast_natAbs] using hComp
  have hAbsEw : |a.ew| = a.ew := by
    simpa using (abs_of_nonneg (le_of_lt hEwPos))
  have hCore : a.lepton + |a.lepton| + a.ew = 1 := by
    nlinarith [hsum1, hCompAbs, hAbsEw]
  have hEwGe1 : (1 : ℤ) ≤ a.ew := by
    simpa using (Int.add_one_le_iff.mpr hEwPos)
  have hLe0sum : a.lepton + |a.lepton| ≤ 0 := by
    nlinarith [hCore, hEwGe1]
  have hTwoLeptonLe : 2 * a.lepton ≤ a.lepton + |a.lepton| := by
    nlinarith [le_abs_self a.lepton]
  have hLnonpos : a.lepton ≤ 0 := by
    have h2l_le0 : 2 * a.lepton ≤ 0 := le_trans hTwoLeptonLe hLe0sum
    nlinarith [h2l_le0]
  have hAbsLnonpos : |a.lepton| = -a.lepton := by
    simpa using (abs_of_nonpos hLnonpos)
  have hEw1 : a.ew = 1 := by
    nlinarith [hCore, hAbsLnonpos]
  have hUpNegOne : a.up = -1 := by
    nlinarith [hSign, hEw1]
  have hDownForm : a.down = 1 - a.lepton := by
    nlinarith [hsum1]
  exact ⟨hEw1, hUpNegOne, hDownForm, hLnonpos⟩

/-- Unrestricted forcing (no finite-pool membership): once the lepton sector is fixed
    to passive-edge coupling `-2E_p`, the principle constraints force the full
    canonical `B_pow` assignment. -/
theorem bpow_unrestricted_forcing_from_passive_coupling (a : BPowAssignment)
    (hLepton : a.lepton = -(2 * (E_passive : ℤ)))
    (hP : bpowPrincipleConstraints a) :
    a = canonicalBPow := by
  rcases hP with ⟨hSign, hComp, hUpNeg, hEwPos, hSum⟩
  have hsum' : a.lepton + a.down = bpowSumTarget := by
    nlinarith [hSum, hSign]
  have hsum1 : a.lepton + a.down = 1 := by
    simpa [bpow_sum_target_eq_one] using hsum'
  have hl22 : a.lepton = -22 := by
    calc
      a.lepton = -(2 * (E_passive : ℤ)) := hLepton
      _ = -22 := by native_decide
  have hd23 : a.down = 23 := by
    nlinarith [hsum1, hl22]
  have hLAbs : (Int.natAbs a.lepton : ℤ) = 22 := by
    rw [hl22]
    native_decide
  have hEAbs : (Int.natAbs a.ew : ℤ) = 1 := by
    nlinarith [hComp, hLAbs, hd23]
  have hEAbsNat : Int.natAbs a.ew = Int.natAbs (1 : ℤ) := by
    exact_mod_cast hEAbs
  have hEw1 : a.ew = 1 := by
    exact (Int.natAbs_inj_of_nonneg_of_nonneg (le_of_lt hEwPos) (by norm_num)).1 hEAbsNat
  have hUpNegOne : a.up = -1 := by
    nlinarith [hSign, hEw1]
  rcases a with ⟨l, u, d, e⟩
  simp at hl22 hUpNegOne hd23 hEw1
  subst l
  subst u
  subst d
  subst e
  rfl

/-- Unrestricted forcing with weaker role input: fixing the down-sector amplification
    `2E_total - 1` plus principle constraints already forces the canonical `B_pow`. -/
theorem bpow_unrestricted_forcing_from_down_role (a : BPowAssignment)
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hP : bpowPrincipleConstraints a) :
    a = canonicalBPow := by
  rcases hP with ⟨hSign, hComp, hUpNeg, hEwPos, hSum⟩
  have hsum' : a.lepton + a.down = bpowSumTarget := by
    nlinarith [hSum, hSign]
  have hd23 : a.down = 23 := by
    calc
      a.down = 2 * (E_total : ℤ) - 1 := hDown
      _ = 23 := by native_decide
  have hl22 : a.lepton = -22 := by
    have hsum1 : a.lepton + a.down = 1 := by simpa [bpow_sum_target_eq_one] using hsum'
    nlinarith [hsum1, hd23]
  have hLepton : a.lepton = -(2 * (E_passive : ℤ)) := by
    calc
      a.lepton = -22 := hl22
      _ = -(2 * (E_passive : ℤ)) := by native_decide
  exact bpow_unrestricted_forcing_from_passive_coupling a hLepton
    ⟨hSign, hComp, hUpNeg, hEwPos, hSum⟩

/-- From down-role fixation plus sign-duality and structural sum,
    the lepton role is forced to passive-edge coupling. -/
theorem bpow_lepton_forced_from_down_role_and_sign_sum (a : BPowAssignment)
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hSign : a.up = -a.ew)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget) :
    a.lepton = -(2 * (E_passive : ℤ)) := by
  have hsum' : a.lepton + a.down = bpowSumTarget := by
    nlinarith [hSum, hSign]
  have hsum1 : a.lepton + a.down = 1 := by
    simpa [bpow_sum_target_eq_one] using hsum'
  have hd23 : a.down = 23 := by
    calc
      a.down = 2 * (E_total : ℤ) - 1 := hDown
      _ = 23 := by native_decide
  have hl22 : a.lepton = -22 := by
    nlinarith [hsum1, hd23]
  calc
    a.lepton = -22 := hl22
    _ = -(2 * (E_passive : ℤ)) := by native_decide

/-- Under sign-duality + structural sum, the passive-edge lepton role and down-role
    amplification are equivalent assumptions. -/
theorem bpow_lepton_role_iff_down_role_under_sign_sum (a : BPowAssignment)
    (hSign : a.up = -a.ew)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget) :
    (a.lepton = -(2 * (E_passive : ℤ))) ↔ (a.down = 2 * (E_total : ℤ) - 1) := by
  have hsum' : a.lepton + a.down = bpowSumTarget := by
    nlinarith [hSum, hSign]
  have hsum1 : a.lepton + a.down = 1 := by
    simpa [bpow_sum_target_eq_one] using hsum'
  constructor
  · intro hLepton
    have hLepton22 : a.lepton = -22 := by
      calc
        a.lepton = -(2 * (E_passive : ℤ)) := hLepton
        _ = -22 := by native_decide
    have hDown23 : a.down = 23 := by
      nlinarith [hsum1, hLepton22]
    calc
      a.down = 23 := hDown23
      _ = 2 * (E_total : ℤ) - 1 := by native_decide
  · intro hDown
    have hDown23 : a.down = 23 := by
      calc
        a.down = 2 * (E_total : ℤ) - 1 := hDown
        _ = 23 := by native_decide
    have hLepton22 : a.lepton = -22 := by
      nlinarith [hsum1, hDown23]
    calc
      a.lepton = -22 := hLepton22
      _ = -(2 * (E_passive : ℤ)) := by native_decide

/-- With passive-edge lepton role and down-role fixed, structural sum forces active-edge sign duality. -/
theorem bpow_sign_forced_from_lepton_down_sum (a : BPowAssignment)
    (hLepton : a.lepton = -(2 * (E_passive : ℤ)))
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget) :
    a.up = -a.ew := by
  have hsum1 : a.lepton + a.up + a.down + a.ew = 1 := by
    simpa [bpow_sum_target_eq_one] using hSum
  have hLepton22 : a.lepton = -22 := by
    calc
      a.lepton = -(2 * (E_passive : ℤ)) := hLepton
      _ = -22 := by native_decide
  have hDown23 : a.down = 23 := by
    calc
      a.down = 2 * (E_total : ℤ) - 1 := hDown
      _ = 23 := by native_decide
  have hup_plus_ew_zero : a.up + a.ew = 0 := by
    nlinarith [hsum1, hLepton22, hDown23]
  nlinarith [hup_plus_ew_zero]

/-- Under edge-role assumptions (down role, sign duality, active-edge unit magnitude
    with positive EW orientation, and structural sum), the full `B_pow` principle
    constraints are derived. -/
theorem bpow_principle_constraints_forced_from_edge_roles (a : BPowAssignment)
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hSign : a.up = -a.ew)
    (hEwPos : 0 < a.ew)
    (hEwMag : Int.natAbs a.ew = A)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget) :
    bpowPrincipleConstraints a := by
  have hLepton : a.lepton = -(2 * (E_passive : ℤ)) :=
    bpow_lepton_forced_from_down_role_and_sign_sum a hDown hSign hSum
  have hDown23 : a.down = 23 := by
    calc
      a.down = 2 * (E_total : ℤ) - 1 := hDown
      _ = 23 := by native_decide
  have hLepton22 : a.lepton = -22 := by
    calc
      a.lepton = -(2 * (E_passive : ℤ)) := hLepton
      _ = -22 := by native_decide
  have hEwAbsNat : Int.natAbs a.ew = Int.natAbs (1 : ℤ) := by
    have hA1 : A = 1 := by native_decide
    rw [hA1] at hEwMag
    simpa using hEwMag
  have hEw1 : a.ew = 1 := by
    exact (Int.natAbs_inj_of_nonneg_of_nonneg (le_of_lt hEwPos) (by norm_num)).1 hEwAbsNat
  have hUpNegOne : a.up = -1 := by
    nlinarith [hSign, hEw1]
  have hUpNeg : a.up < 0 := by
    nlinarith [hUpNegOne]
  have hComp : (Int.natAbs a.lepton : ℤ) + (Int.natAbs a.ew : ℤ) = a.down := by
    simp [hLepton22, hEw1, hDown23]
  exact ⟨hSign, hComp, hUpNeg, hEwPos, hSum⟩

/-- Same derivation using passive-edge lepton role instead of explicit down-role input. -/
theorem bpow_principle_constraints_forced_from_passive_active_roles (a : BPowAssignment)
    (hLepton : a.lepton = -(2 * (E_passive : ℤ)))
    (hSign : a.up = -a.ew)
    (hEwPos : 0 < a.ew)
    (hEwMag : Int.natAbs a.ew = A)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget) :
    bpowPrincipleConstraints a := by
  have hDown : a.down = 2 * (E_total : ℤ) - 1 :=
    (bpow_lepton_role_iff_down_role_under_sign_sum a hSign hSum).1 hLepton
  exact bpow_principle_constraints_forced_from_edge_roles a hDown hSign hEwPos hEwMag hSum

/-- Boolean-filter version of the previous derivation theorem. -/
theorem bpow_bool_constraints_forced_from_edge_roles (a : BPowAssignment)
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hSign : a.up = -a.ew)
    (hEwPos : 0 < a.ew)
    (hEwMag : Int.natAbs a.ew = A)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget) :
    bpowStructuralConstraints a = true := by
  exact (bpow_constraints_true_iff a).2 <|
    bpow_principle_constraints_forced_from_edge_roles a hDown hSign hEwPos hEwMag hSum

/-- Boolean-filter version using passive-edge lepton role input. -/
theorem bpow_bool_constraints_forced_from_passive_active_roles (a : BPowAssignment)
    (hLepton : a.lepton = -(2 * (E_passive : ℤ)))
    (hSign : a.up = -a.ew)
    (hEwPos : 0 < a.ew)
    (hEwMag : Int.natAbs a.ew = A)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget) :
    bpowStructuralConstraints a = true := by
  exact (bpow_constraints_true_iff a).2 <|
    bpow_principle_constraints_forced_from_passive_active_roles a hLepton hSign hEwPos hEwMag hSum

/-- Unrestricted canonical forcing from edge-role assumptions (no finite enumeration). -/
theorem bpow_unrestricted_forcing_from_edge_roles (a : BPowAssignment)
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hSign : a.up = -a.ew)
    (hEwPos : 0 < a.ew)
    (hEwMag : Int.natAbs a.ew = A)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget) :
    a = canonicalBPow := by
  have hP := bpow_principle_constraints_forced_from_edge_roles a hDown hSign hEwPos hEwMag hSum
  exact bpow_unrestricted_forcing_from_down_role a hDown hP

/-- Unrestricted canonical forcing via passive-edge + active-edge role inputs. -/
theorem bpow_unrestricted_forcing_from_passive_active_roles (a : BPowAssignment)
    (hLepton : a.lepton = -(2 * (E_passive : ℤ)))
    (hSign : a.up = -a.ew)
    (hEwPos : 0 < a.ew)
    (hEwMag : Int.natAbs a.ew = A)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget) :
    a = canonicalBPow := by
  have hDown : a.down = 2 * (E_total : ℤ) - 1 :=
    (bpow_lepton_role_iff_down_role_under_sign_sum a hSign hSum).1 hLepton
  exact bpow_unrestricted_forcing_from_edge_roles a hDown hSign hEwPos hEwMag hSum

/-- Unrestricted canonical forcing via passive/down roles without an explicit sign assumption. -/
theorem bpow_unrestricted_forcing_from_passive_down_roles (a : BPowAssignment)
    (hLepton : a.lepton = -(2 * (E_passive : ℤ)))
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hEwPos : 0 < a.ew)
    (hEwMag : Int.natAbs a.ew = A)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget) :
    a = canonicalBPow := by
  have hSign : a.up = -a.ew :=
    bpow_sign_forced_from_lepton_down_sum a hLepton hDown hSum
  exact bpow_unrestricted_forcing_from_edge_roles a hDown hSign hEwPos hEwMag hSum

/-- Without an orientation choice, down-role + sign-duality + structural sum + active-unit
    magnitude leaves exactly two `B_pow` branches: canonical and its mirrored orientation. -/
theorem bpow_two_branch_under_down_role (a : BPowAssignment)
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hSign : a.up = -a.ew)
    (hEwMag : Int.natAbs a.ew = A)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget) :
    a = canonicalBPow ∨ a = mirroredBPow := by
  have hLepton : a.lepton = -(2 * (E_passive : ℤ)) :=
    bpow_lepton_forced_from_down_role_and_sign_sum a hDown hSign hSum
  have hDownForm : a.down = 2 * (E_total : ℤ) - 1 := hDown
  have hA1 : A = 1 := by native_decide
  have hEwAbsNat : Int.natAbs a.ew = Int.natAbs (1 : ℤ) := by
    rw [hA1] at hEwMag
    simpa using hEwMag
  rcases Int.natAbs_eq_natAbs_iff.mp hEwAbsNat with hEwOne | hEwNegOne
  · have hUp : a.up = -(A : ℤ) := by
      have hEwA : a.ew = (A : ℤ) := by simpa [hA1] using hEwOne
      nlinarith [hSign, hEwA]
    rcases a with ⟨l, u, d, e⟩
    simp at hLepton hUp hDownForm hEwOne
    subst l
    subst u
    subst d
    subst e
    left
    rfl
  · have hUp : a.up = (A : ℤ) := by
      have hEwNegA : a.ew = -(A : ℤ) := by simpa [hA1] using hEwNegOne
      nlinarith [hSign, hEwNegA]
    rcases a with ⟨l, u, d, e⟩
    simp at hLepton hUp hDownForm hEwNegOne
    subst l
    subst u
    subst d
    subst e
    right
    rfl

/-- Positive EW orientation selects the canonical branch from `bpow_two_branch_under_down_role`. -/
theorem bpow_orientation_selects_canonical_from_two_branch (a : BPowAssignment)
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hSign : a.up = -a.ew)
    (hEwMag : Int.natAbs a.ew = A)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget)
    (hEwPos : 0 < a.ew) :
    a = canonicalBPow := by
  rcases bpow_two_branch_under_down_role a hDown hSign hEwMag hSum with hcan | hmirror
  · exact hcan
  · exfalso
    have hmirror_not_pos : ¬ (0 < mirroredBPow.ew) := by
      native_decide
    exact hmirror_not_pos (by simpa [hmirror] using hEwPos)

/-- Passive/down roles + structural sum already determine sign-duality, so branch selection
    can be stated without an explicit sign assumption. -/
theorem bpow_orientation_selects_canonical_from_passive_down_roles (a : BPowAssignment)
    (hLepton : a.lepton = -(2 * (E_passive : ℤ)))
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hEwMag : Int.natAbs a.ew = A)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget)
    (hEwPos : 0 < a.ew) :
    a = canonicalBPow := by
  have hSign : a.up = -a.ew :=
    bpow_sign_forced_from_lepton_down_sum a hLepton hDown hSum
  exact bpow_orientation_selects_canonical_from_two_branch a hDown hSign hEwMag hSum hEwPos

/-- Under down-role + sign-duality + structural sum (+ positive EW orientation),
    full `B_pow` principle constraints are equivalent to the active-edge unit
    magnitude condition `natAbs ew = A`. -/
theorem bpow_principle_iff_active_unit_under_down_role (a : BPowAssignment)
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hSign : a.up = -a.ew)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget)
    (hEwPos : 0 < a.ew) :
    bpowPrincipleConstraints a ↔ Int.natAbs a.ew = A := by
  constructor
  · intro hP
    rcases hP with ⟨_hSign', hComp, _hUpNeg, _hEwPos', _hSum'⟩
    have hLepton : a.lepton = -(2 * (E_passive : ℤ)) :=
      bpow_lepton_forced_from_down_role_and_sign_sum a hDown hSign hSum
    have hLepton22 : a.lepton = -22 := by
      calc
        a.lepton = -(2 * (E_passive : ℤ)) := hLepton
        _ = -22 := by native_decide
    have hDown23 : a.down = 23 := by
      calc
        a.down = 2 * (E_total : ℤ) - 1 := hDown
        _ = 23 := by native_decide
    have hLAbs : (Int.natAbs a.lepton : ℤ) = 22 := by
      rw [hLepton22]
      native_decide
    have hEAbsZ : (Int.natAbs a.ew : ℤ) = 1 := by
      nlinarith [hComp, hLAbs, hDown23]
    have hEAbsNat : Int.natAbs a.ew = 1 := by
      exact_mod_cast hEAbsZ
    have hA1 : A = 1 := by native_decide
    simpa [hA1] using hEAbsNat
  · intro hEwMag
    exact bpow_principle_constraints_forced_from_edge_roles a hDown hSign hEwPos hEwMag hSum

/-- Same equivalence using passive/down roles and structural sum, with sign derived internally. -/
theorem bpow_principle_iff_active_unit_under_passive_down_roles (a : BPowAssignment)
    (hLepton : a.lepton = -(2 * (E_passive : ℤ)))
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget)
    (hEwPos : 0 < a.ew) :
    bpowPrincipleConstraints a ↔ Int.natAbs a.ew = A := by
  have hSign : a.up = -a.ew :=
    bpow_sign_forced_from_lepton_down_sum a hLepton hDown hSum
  exact bpow_principle_iff_active_unit_under_down_role a hDown hSign hSum hEwPos

/-- Boolean-filter equivalence form of `bpow_principle_iff_active_unit_under_down_role`. -/
theorem bpow_bool_constraints_iff_active_unit_under_down_role (a : BPowAssignment)
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hSign : a.up = -a.ew)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget)
    (hEwPos : 0 < a.ew) :
    bpowStructuralConstraints a = true ↔ Int.natAbs a.ew = A := by
  rw [bpow_constraints_true_iff]
  exact bpow_principle_iff_active_unit_under_down_role a hDown hSign hSum hEwPos

/-- Boolean-filter equivalence form using passive/down roles and structural sum. -/
theorem bpow_bool_constraints_iff_active_unit_under_passive_down_roles (a : BPowAssignment)
    (hLepton : a.lepton = -(2 * (E_passive : ℤ)))
    (hDown : a.down = 2 * (E_total : ℤ) - 1)
    (hSum : a.lepton + a.up + a.down + a.ew = bpowSumTarget)
    (hEwPos : 0 < a.ew) :
    bpowStructuralConstraints a = true ↔ Int.natAbs a.ew = A := by
  rw [bpow_constraints_true_iff]
  exact bpow_principle_iff_active_unit_under_passive_down_roles a hLepton hDown hSum hEwPos

/-! ## `r0` assignment search -/

structure R0Assignment where
  lepton : ℤ
  up : ℤ
  down : ℤ
  ew : ℤ
  deriving Repr, DecidableEq

def canonicalR0 : R0Assignment :=
  { lepton := 4 * (W : ℤ) - 6
  , up := 2 * (W : ℤ) + (A : ℤ)
  , down := (E_total : ℤ) - (W : ℤ)
  , ew := 3 * (W : ℤ) + 4 }

def r0ValuePool : List ℤ :=
  [ 4 * (W : ℤ) - 6
  , 2 * (W : ℤ) + (A : ℤ)
  , (E_total : ℤ) - (W : ℤ)
  , 3 * (W : ℤ) + 4 ]

theorem r0_pool_matches_anchor_formulas :
    r0ValuePool =
      [r0 .Lepton, r0 .UpQuark, r0 .DownQuark, r0 .Electroweak] := by
  rfl

def listToR0Assignment? : List ℤ → Option R0Assignment
  | [l, u, d, e] => some { lepton := l, up := u, down := d, ew := e }
  | _ => none

def allR0Assignments : List R0Assignment :=
  (r0ValuePool.permutations.filterMap listToR0Assignment?)

/-- Structural r0 sum target (`V * W + E_passive = 147`). -/
def r0SumTarget : ℤ :=
  (Constants.AlphaDerivation.cube_vertices Constants.AlphaDerivation.D : ℤ) *
    (Constants.AlphaDerivation.wallpaper_groups : ℤ) +
    (Constants.AlphaDerivation.passive_field_edges Constants.AlphaDerivation.D : ℤ)

theorem r0_sum_target_eq_147 : r0SumTarget = 147 := by
  native_decide

theorem r0_sum_target_matches_principle :
    r0SumTarget =
      (r0 .Lepton + r0 .UpQuark + r0 .DownQuark + r0 .Electroweak) := by
  calc
    r0SumTarget = 147 := r0_sum_target_eq_147
    _ = (r0 .Lepton + r0 .UpQuark + r0 .DownQuark + r0 .Electroweak) := by
      symm
      exact YardstickAssignmentPrinciple.r0_sum

/-- Structural constraints used to filter `r0` assignments. -/
def r0StructuralConstraints (a : R0Assignment) : Bool :=
  decide (a.down < 0) &&
  decide (a.lepton > a.ew) &&
  decide (a.ew > a.up) &&
  decide (a.lepton + a.up + a.down + a.ew = r0SumTarget)

/-- Prop-level version of `r0StructuralConstraints`. -/
def r0PrincipleConstraints (a : R0Assignment) : Prop :=
  a.down < 0 ∧
  a.lepton > a.ew ∧
  a.ew > a.up ∧
  (a.lepton + a.up + a.down + a.ew = r0SumTarget)

def validR0Assignments : List R0Assignment :=
  allR0Assignments.filter r0StructuralConstraints

theorem all_r0_assignments_count : allR0Assignments.length = 24 := by
  native_decide

theorem valid_r0_assignment_count : validR0Assignments.length = 1 := by
  native_decide

theorem valid_r0_assignments_are_singleton :
    validR0Assignments = [canonicalR0] := by
  native_decide

theorem r0_constraints_true_iff (a : R0Assignment) :
    r0StructuralConstraints a = true ↔ r0PrincipleConstraints a := by
  unfold r0StructuralConstraints r0PrincipleConstraints
  simp
  tauto

theorem r0_constraints_force_canonical (a : R0Assignment)
    (ha : a ∈ allR0Assignments)
    (hP : r0PrincipleConstraints a) :
    a = canonicalR0 := by
  have htrue : r0StructuralConstraints a = true := (r0_constraints_true_iff a).2 hP
  have hmem : a ∈ validR0Assignments := by
    unfold validR0Assignments
    exact List.mem_filter.mpr ⟨ha, htrue⟩
  rw [valid_r0_assignments_are_singleton] at hmem
  simpa using hmem

/-- Unrestricted forcing (no finite-pool membership): if the up/down affine roles and
    lepton-vs-EW depth gap are fixed by the cube hierarchy, the structural sum target
    already forces the full canonical `r0` assignment. -/
theorem r0_unrestricted_forcing_from_affine_roles_and_sum (a : R0Assignment)
    (hUpRole : a.up = 2 * (W : ℤ) + (A : ℤ))
    (hDownRole : a.down = (E_total : ℤ) - (W : ℤ))
    (hDepthGap : a.lepton - a.ew = (W : ℤ) - 10)
    (hSum : a.lepton + a.up + a.down + a.ew = r0SumTarget) :
    a = canonicalR0 := by
  have hsum147 : a.lepton + a.up + a.down + a.ew = 147 := by
    simpa [r0_sum_target_eq_147] using hSum
  have hUp35 : a.up = 35 := by
    calc
      a.up = 2 * (W : ℤ) + (A : ℤ) := hUpRole
      _ = 35 := by native_decide
  have hDownNeg5 : a.down = -5 := by
    calc
      a.down = (E_total : ℤ) - (W : ℤ) := hDownRole
      _ = -5 := by native_decide
  have hGap7 : a.lepton - a.ew = 7 := by
    calc
      a.lepton - a.ew = (W : ℤ) - 10 := hDepthGap
      _ = 7 := by native_decide
  have hLeptonPlusEw : a.lepton + a.ew = 117 := by
    nlinarith [hsum147, hUp35, hDownNeg5]
  have hLepton62 : a.lepton = 62 := by
    nlinarith [hLeptonPlusEw, hGap7]
  have hEw55 : a.ew = 55 := by
    nlinarith [hLeptonPlusEw, hGap7]
  rcases a with ⟨l, u, d, e⟩
  simp at hLepton62 hUp35 hDownNeg5 hEw55
  subst l
  subst u
  subst d
  subst e
  rfl

/-- Under fixed affine up/down roles and structural sum, the depth-gap condition is
    equivalent to fixing the EW rung to its canonical affine formula. -/
theorem r0_depth_gap_iff_ew_role_under_affine_roles_and_sum (a : R0Assignment)
    (hUpRole : a.up = 2 * (W : ℤ) + (A : ℤ))
    (hDownRole : a.down = (E_total : ℤ) - (W : ℤ))
    (hSum : a.lepton + a.up + a.down + a.ew = r0SumTarget) :
    (a.lepton - a.ew = (W : ℤ) - 10) ↔ (a.ew = 3 * (W : ℤ) + 4) := by
  have hsum147 : a.lepton + a.up + a.down + a.ew = 147 := by
    simpa [r0_sum_target_eq_147] using hSum
  have hUp35 : a.up = 35 := by
    calc
      a.up = 2 * (W : ℤ) + (A : ℤ) := hUpRole
      _ = 35 := by native_decide
  have hDownNeg5 : a.down = -5 := by
    calc
      a.down = (E_total : ℤ) - (W : ℤ) := hDownRole
      _ = -5 := by native_decide
  have hLeptonPlusEw : a.lepton + a.ew = 117 := by
    nlinarith [hsum147, hUp35, hDownNeg5]
  constructor
  · intro hDepthGap
    have hGap7 : a.lepton - a.ew = 7 := by
      calc
        a.lepton - a.ew = (W : ℤ) - 10 := hDepthGap
        _ = 7 := by native_decide
    have hEw55 : a.ew = 55 := by
      nlinarith [hLeptonPlusEw, hGap7]
    calc
      a.ew = 55 := hEw55
      _ = 3 * (W : ℤ) + 4 := by native_decide
  · intro hEwRole
    have hEw55 : a.ew = 55 := by
      calc
        a.ew = 3 * (W : ℤ) + 4 := hEwRole
        _ = 55 := by native_decide
    have hLepton62 : a.lepton = 62 := by
      nlinarith [hLeptonPlusEw, hEw55]
    have hGap7 : a.lepton - a.ew = 7 := by
      nlinarith [hLepton62, hEw55]
    calc
      a.lepton - a.ew = 7 := hGap7
      _ = (W : ℤ) - 10 := by native_decide

/-- Alternate unrestricted forcing route: fix affine up/down roles, EW affine role,
    and structural sum; depth gap is then forced and canonical `r0` follows. -/
theorem r0_unrestricted_forcing_from_affine_roles_and_ew_role (a : R0Assignment)
    (hUpRole : a.up = 2 * (W : ℤ) + (A : ℤ))
    (hDownRole : a.down = (E_total : ℤ) - (W : ℤ))
    (hEwRole : a.ew = 3 * (W : ℤ) + 4)
    (hSum : a.lepton + a.up + a.down + a.ew = r0SumTarget) :
    a = canonicalR0 := by
  have hDepthGap : a.lepton - a.ew = (W : ℤ) - 10 :=
    (r0_depth_gap_iff_ew_role_under_affine_roles_and_sum a hUpRole hDownRole hSum).2 hEwRole
  exact r0_unrestricted_forcing_from_affine_roles_and_sum a hUpRole hDownRole hDepthGap hSum

/-- Unrestricted forcing (no finite-pool membership): under affine roles + depth gap,
    the full principle constraints force canonical `r0`. -/
theorem r0_unrestricted_forcing_from_affine_roles (a : R0Assignment)
    (hUpRole : a.up = 2 * (W : ℤ) + (A : ℤ))
    (hDownRole : a.down = (E_total : ℤ) - (W : ℤ))
    (hDepthGap : a.lepton - a.ew = (W : ℤ) - 10)
    (hP : r0PrincipleConstraints a) :
    a = canonicalR0 := by
  rcases hP with ⟨_hDownNeg, _hLeptonGtEw, _hEwGtUp, hSum⟩
  exact r0_unrestricted_forcing_from_affine_roles_and_sum a hUpRole hDownRole hDepthGap hSum

/-- Under fixed affine up/down roles and depth gap, full prop-level `r0` constraints
    are equivalent to the structural sum target alone (order conjuncts become derived). -/
theorem r0_principle_iff_sum_under_affine_roles_and_depth_gap (a : R0Assignment)
    (hUpRole : a.up = 2 * (W : ℤ) + (A : ℤ))
    (hDownRole : a.down = (E_total : ℤ) - (W : ℤ))
    (hDepthGap : a.lepton - a.ew = (W : ℤ) - 10) :
    r0PrincipleConstraints a ↔
      (a.lepton + a.up + a.down + a.ew = r0SumTarget) := by
  constructor
  · intro hP
    exact hP.2.2.2
  · intro hSum
    have hcanon : a = canonicalR0 :=
      r0_unrestricted_forcing_from_affine_roles_and_sum a hUpRole hDownRole hDepthGap hSum
    rw [hcanon]
    unfold r0PrincipleConstraints canonicalR0
    repeat' constructor <;> native_decide

/-- Boolean filter form of `r0_principle_iff_sum_under_affine_roles_and_depth_gap`. -/
theorem r0_bool_constraints_iff_sum_under_affine_roles_and_depth_gap (a : R0Assignment)
    (hUpRole : a.up = 2 * (W : ℤ) + (A : ℤ))
    (hDownRole : a.down = (E_total : ℤ) - (W : ℤ))
    (hDepthGap : a.lepton - a.ew = (W : ℤ) - 10) :
    r0StructuralConstraints a = true ↔
      (a.lepton + a.up + a.down + a.ew = r0SumTarget) := by
  rw [r0_constraints_true_iff]
  exact r0_principle_iff_sum_under_affine_roles_and_depth_gap a hUpRole hDownRole hDepthGap

/-- Once affine roles + depth gap + structural sum are fixed, the full
    prop-level `r0` principle constraints are derived (no independent order axioms). -/
theorem r0_principle_constraints_forced_from_affine_roles_and_sum (a : R0Assignment)
    (hUpRole : a.up = 2 * (W : ℤ) + (A : ℤ))
    (hDownRole : a.down = (E_total : ℤ) - (W : ℤ))
    (hDepthGap : a.lepton - a.ew = (W : ℤ) - 10)
    (hSum : a.lepton + a.up + a.down + a.ew = r0SumTarget) :
    r0PrincipleConstraints a := by
  have hcanon : a = canonicalR0 :=
    r0_unrestricted_forcing_from_affine_roles_and_sum a hUpRole hDownRole hDepthGap hSum
  rw [hcanon]
  unfold r0PrincipleConstraints canonicalR0
  repeat' constructor <;> native_decide

/-- Boolean filter form of the previous theorem. -/
theorem r0_bool_constraints_forced_from_affine_roles_and_sum (a : R0Assignment)
    (hUpRole : a.up = 2 * (W : ℤ) + (A : ℤ))
    (hDownRole : a.down = (E_total : ℤ) - (W : ℤ))
    (hDepthGap : a.lepton - a.ew = (W : ℤ) - 10)
    (hSum : a.lepton + a.up + a.down + a.ew = r0SumTarget) :
    r0StructuralConstraints a = true := by
  exact (r0_constraints_true_iff a).2 <|
    r0_principle_constraints_forced_from_affine_roles_and_sum a hUpRole hDownRole hDepthGap hSum

/-! ## Link to `Masses.Anchor` -/

def anchorBPowAssignment : BPowAssignment :=
  { lepton := B_pow .Lepton
  , up := B_pow .UpQuark
  , down := B_pow .DownQuark
  , ew := B_pow .Electroweak }

def anchorR0Assignment : R0Assignment :=
  { lepton := r0 .Lepton
  , up := r0 .UpQuark
  , down := r0 .DownQuark
  , ew := r0 .Electroweak }

theorem anchor_bpow_matches_canonical :
    anchorBPowAssignment = canonicalBPow := by
  native_decide

theorem anchor_r0_matches_canonical :
    anchorR0Assignment = canonicalR0 := by
  native_decide

theorem anchor_is_unique_valid_bpow :
    anchorBPowAssignment ∈ validBPowAssignments := by
  rw [valid_bpow_assignments_are_singleton, anchor_bpow_matches_canonical]
  simp

theorem anchor_is_unique_valid_r0 :
    anchorR0Assignment ∈ validR0Assignments := by
  rw [valid_r0_assignments_are_singleton, anchor_r0_matches_canonical]
  simp

/-- The `B_pow` filter constraints are satisfied by the anchor assignment,
    with each conjunct matching a proved structural identity from
    `YardstickAssignmentPrinciple`. -/
theorem anchor_bpow_structural_identities :
    anchorBPowAssignment.up = -anchorBPowAssignment.ew ∧
    ((Int.natAbs anchorBPowAssignment.lepton : ℤ) +
      (Int.natAbs anchorBPowAssignment.ew : ℤ) = anchorBPowAssignment.down) ∧
    anchorBPowAssignment.up < 0 ∧
    0 < anchorBPowAssignment.ew ∧
    (anchorBPowAssignment.lepton + anchorBPowAssignment.up +
      anchorBPowAssignment.down + anchorBPowAssignment.ew = bpowSumTarget) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [anchorBPowAssignment]
  · simpa [anchorBPowAssignment] using
      YardstickAssignmentPrinciple.lepton_ew_natAbs_complement_down
  · simpa [anchorBPowAssignment] using
      YardstickAssignmentPrinciple.up_negative_and_ew_positive.1
  · simpa [anchorBPowAssignment] using
      YardstickAssignmentPrinciple.up_negative_and_ew_positive.2
  · simpa [anchorBPowAssignment, add_comm, add_left_comm, add_assoc] using
      bpow_sum_target_matches_principle.symm

theorem anchor_bpow_constraints_from_principle :
    bpowStructuralConstraints anchorBPowAssignment = true := by
  rcases anchor_bpow_structural_identities with ⟨hSign, _hComp, hUpNeg, hEwPos, hSum⟩
  have hCompAbs : |anchorBPowAssignment.lepton| + |anchorBPowAssignment.ew| = anchorBPowAssignment.down := by
    simpa [anchorBPowAssignment] using YardstickAssignmentPrinciple.lepton_ew_complement_down
  have dSign : decide (anchorBPowAssignment.up = -anchorBPowAssignment.ew) = true :=
    decide_eq_true hSign
  have dUpNeg : decide (anchorBPowAssignment.up < 0) = true := decide_eq_true hUpNeg
  have dEwPos : decide (0 < anchorBPowAssignment.ew) = true := decide_eq_true hEwPos
  have dSum :
      decide (anchorBPowAssignment.lepton + anchorBPowAssignment.up +
        anchorBPowAssignment.down + anchorBPowAssignment.ew = bpowSumTarget) = true :=
    decide_eq_true hSum
  unfold bpowStructuralConstraints
  simp [hCompAbs, dSign, dUpNeg, dEwPos, dSum]

/-- The `r0` filter constraints are satisfied by the anchor assignment,
    and each conjunct corresponds to proved ordering/sum identities. -/
theorem anchor_r0_structural_identities :
    anchorR0Assignment.down < 0 ∧
    anchorR0Assignment.lepton > anchorR0Assignment.ew ∧
    anchorR0Assignment.ew > anchorR0Assignment.up ∧
    (anchorR0Assignment.lepton + anchorR0Assignment.up +
      anchorR0Assignment.down + anchorR0Assignment.ew = r0SumTarget) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [anchorR0Assignment] using YardstickAssignmentPrinciple.r0_order_constraints.1
  · simpa [anchorR0Assignment] using YardstickAssignmentPrinciple.r0_order_constraints.2.1
  · simpa [anchorR0Assignment] using YardstickAssignmentPrinciple.r0_order_constraints.2.2
  · simpa [anchorR0Assignment, add_comm, add_left_comm, add_assoc] using
      r0_sum_target_matches_principle.symm

theorem anchor_r0_constraints_from_principle :
    r0StructuralConstraints anchorR0Assignment = true := by
  rcases anchor_r0_structural_identities with ⟨hDownNeg, hLeptonGtEw, hEwGtUp, hSum⟩
  have dDownNeg : decide (anchorR0Assignment.down < 0) = true := decide_eq_true hDownNeg
  have dLeptonGtEw : decide (anchorR0Assignment.lepton > anchorR0Assignment.ew) = true :=
    decide_eq_true hLeptonGtEw
  have dEwGtUp : decide (anchorR0Assignment.ew > anchorR0Assignment.up) = true :=
    decide_eq_true hEwGtUp
  have dSum :
      decide (anchorR0Assignment.lepton + anchorR0Assignment.up +
        anchorR0Assignment.down + anchorR0Assignment.ew = r0SumTarget) = true :=
    decide_eq_true hSum
  unfold r0StructuralConstraints
  simp [dDownNeg, dLeptonGtEw, dEwGtUp, dSum]

/-- Enumerated-choice closure summary for O1 (current constraint set). -/
theorem yardstick_choice_sets_collapsed :
    validBPowAssignments = [canonicalBPow] ∧
    validR0Assignments = [canonicalR0] := by
  exact ⟨valid_bpow_assignments_are_singleton, valid_r0_assignments_are_singleton⟩

/-- Joint unrestricted forcing: once the cube-role couplings are fixed, both
    yardstick layers are forced by role-kernel assumptions plus structural sums,
    without finite enumeration and without directly assuming full filter bundles. -/
theorem yardstick_unrestricted_forcing_from_role_kernels_and_sums
    (b : BPowAssignment) (r : R0Assignment)
    (hbLepton : b.lepton = -(2 * (E_passive : ℤ)))
    (hbDown : b.down = 2 * (E_total : ℤ) - 1)
    (hbEwPos : 0 < b.ew)
    (hbEwMag : Int.natAbs b.ew = A)
    (hbSum : b.lepton + b.up + b.down + b.ew = bpowSumTarget)
    (hrUpRole : r.up = 2 * (W : ℤ) + (A : ℤ))
    (hrDownRole : r.down = (E_total : ℤ) - (W : ℤ))
    (hrDepthGap : r.lepton - r.ew = (W : ℤ) - 10)
    (hrSum : r.lepton + r.up + r.down + r.ew = r0SumTarget) :
    b = canonicalBPow ∧ r = canonicalR0 := by
  exact
    ⟨ bpow_unrestricted_forcing_from_passive_down_roles
        b hbLepton hbDown hbEwPos hbEwMag hbSum
    , r0_unrestricted_forcing_from_affine_roles_and_sum
        r hrUpRole hrDownRole hrDepthGap hrSum ⟩

/-- Joint unrestricted forcing: once the cube-role couplings are fixed, both
    yardstick layers are forced to their canonical assignments without finite enumeration.
    This version uses only the structural sum on the `r0` side (order/filter conjuncts
    are derived under affine roles + depth gap). -/
theorem yardstick_unrestricted_forcing_from_cube_roles_and_r0_sum
    (b : BPowAssignment) (r : R0Assignment)
    (hbLepton : b.lepton = -(2 * (E_passive : ℤ)))
    (hbP : bpowPrincipleConstraints b)
    (hrUpRole : r.up = 2 * (W : ℤ) + (A : ℤ))
    (hrDownRole : r.down = (E_total : ℤ) - (W : ℤ))
    (hrDepthGap : r.lepton - r.ew = (W : ℤ) - 10)
    (hrSum : r.lepton + r.up + r.down + r.ew = r0SumTarget) :
    b = canonicalBPow ∧ r = canonicalR0 := by
  exact
    ⟨ bpow_unrestricted_forcing_from_passive_coupling b hbLepton hbP
    , r0_unrestricted_forcing_from_affine_roles_and_sum r hrUpRole hrDownRole hrDepthGap hrSum ⟩

/-- Joint unrestricted forcing: once the cube-role couplings are fixed, both
    yardstick layers are forced to their canonical assignments without finite enumeration. -/
theorem yardstick_unrestricted_forcing_from_cube_roles
    (b : BPowAssignment) (r : R0Assignment)
    (hbLepton : b.lepton = -(2 * (E_passive : ℤ)))
    (hbP : bpowPrincipleConstraints b)
    (hrUpRole : r.up = 2 * (W : ℤ) + (A : ℤ))
    (hrDownRole : r.down = (E_total : ℤ) - (W : ℤ))
    (hrDepthGap : r.lepton - r.ew = (W : ℤ) - 10)
    (hrP : r0PrincipleConstraints r) :
    b = canonicalBPow ∧ r = canonicalR0 := by
  exact yardstick_unrestricted_forcing_from_cube_roles_and_r0_sum
    b r hbLepton hbP hrUpRole hrDownRole hrDepthGap hrP.2.2.2

/-- Cube-partition principle packaging:
    role-kernel assumptions plus structural sums force the full admissibility filter
    family for both `B_pow` and `r0` (without finite enumeration). -/
theorem yardstick_filter_family_forced_from_cube_partition_principle
    (b : BPowAssignment) (r : R0Assignment)
    (hbLepton : b.lepton = -(2 * (E_passive : ℤ)))
    (hbDown : b.down = 2 * (E_total : ℤ) - 1)
    (hbEwPos : 0 < b.ew)
    (hbEwMag : Int.natAbs b.ew = A)
    (hbSum : b.lepton + b.up + b.down + b.ew = bpowSumTarget)
    (hrUpRole : r.up = 2 * (W : ℤ) + (A : ℤ))
    (hrDownRole : r.down = (E_total : ℤ) - (W : ℤ))
    (hrDepthGap : r.lepton - r.ew = (W : ℤ) - 10)
    (hrSum : r.lepton + r.up + r.down + r.ew = r0SumTarget) :
    bpowPrincipleConstraints b ∧ r0PrincipleConstraints r := by
  refine ⟨?_, ?_⟩
  · have hbSign : b.up = -b.ew :=
      bpow_sign_forced_from_lepton_down_sum b hbLepton hbDown hbSum
    exact bpow_principle_constraints_forced_from_edge_roles
      b hbDown hbSign hbEwPos hbEwMag hbSum
  · exact r0_principle_constraints_forced_from_affine_roles_and_sum
      r hrUpRole hrDownRole hrDepthGap hrSum

/-- Cube-partition first-principles forcing:
    once the role kernels and structural sums are fixed, sector yardstick assignments
    are uniquely forced to the canonical formulas. -/
theorem yardstick_assignment_forced_from_cube_partition_principle
    (b : BPowAssignment) (r : R0Assignment)
    (hbLepton : b.lepton = -(2 * (E_passive : ℤ)))
    (hbDown : b.down = 2 * (E_total : ℤ) - 1)
    (hbEwPos : 0 < b.ew)
    (hbEwMag : Int.natAbs b.ew = A)
    (hbSum : b.lepton + b.up + b.down + b.ew = bpowSumTarget)
    (hrUpRole : r.up = 2 * (W : ℤ) + (A : ℤ))
    (hrDownRole : r.down = (E_total : ℤ) - (W : ℤ))
    (hrDepthGap : r.lepton - r.ew = (W : ℤ) - 10)
    (hrSum : r.lepton + r.up + r.down + r.ew = r0SumTarget) :
    b = canonicalBPow ∧ r = canonicalR0 := by
  exact yardstick_unrestricted_forcing_from_role_kernels_and_sums
    b r hbLepton hbDown hbEwPos hbEwMag hbSum hrUpRole hrDownRole hrDepthGap hrSum

/-- O1' uniqueness surface (iff form):
    canonical yardstick assignments are equivalent to the cube-partition
    role-kernel + structural-sum principle package. -/
theorem yardstick_assignment_iff_cube_partition_principle
    (b : BPowAssignment) (r : R0Assignment) :
    (b = canonicalBPow ∧ r = canonicalR0) ↔
      (b.lepton = -(2 * (E_passive : ℤ)) ∧
       b.down = 2 * (E_total : ℤ) - 1 ∧
       0 < b.ew ∧
       Int.natAbs b.ew = A ∧
       (b.lepton + b.up + b.down + b.ew = bpowSumTarget) ∧
       r.up = 2 * (W : ℤ) + (A : ℤ) ∧
       r.down = (E_total : ℤ) - (W : ℤ) ∧
       r.lepton - r.ew = (W : ℤ) - 10 ∧
       (r.lepton + r.up + r.down + r.ew = r0SumTarget)) := by
  constructor
  · intro h
    rcases h with ⟨hb, hr⟩
    subst hb
    subst hr
    repeat' constructor <;> native_decide
  · intro h
    rcases h with ⟨hbLepton, hbDown, hbEwPos, hbEwMag, hbSum, hrUpRole, hrDownRole, hrDepthGap, hrSum⟩
    exact yardstick_assignment_forced_from_cube_partition_principle
      b r hbLepton hbDown hbEwPos hbEwMag hbSum hrUpRole hrDownRole hrDepthGap hrSum

end YardstickAssignmentChoiceSet
end Verification
end IndisputableMonolith
