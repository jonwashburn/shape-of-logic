import IndisputableMonolith.Foundation.HierarchyDynamics
import IndisputableMonolith.Foundation.HierarchyRealizationObstruction
import IndisputableMonolith.Foundation.PostingExtensivity
import IndisputableMonolith.Foundation.PhiForcingDerived
import IndisputableMonolith.Foundation.PublicSpine.SelectedScaleClosure
import IndisputableMonolith.Constants

/-!
# SelectedClosureNecessity — Lane B hard-half binder

Necessity (not uniqueness) for the selected short closure that forces φ.

Already THEOREM under `isClosed` / `recipShift`: uniqueness of φ
(`SelectedScaleClosure`, `phi_forcing_complete`).

This module banks the stronger Recognition package `P_closure`:

1. **Exclude inadmissible ledgers:** Bool closed-observable orbits do not
   carry additive ℝ scale posting, so they are not Recognition scale ledgers
   under the disclosed extensivity predicate (`AdmissibleScaleLedger`).
2. **Locality + zero-param (1,1):** disclosed as
   `ClosureNecessityPremises` (`LocalBinaryRecurrence` + minimality).
3. **Fibonacci ⇒ `isClosed` ⇒ φ** via `HierarchyDynamics` /
   `HierarchyEmergence` / `PhiForcingDerived`.
4. **Plastic independence** retained from `SelectedScaleClosure`.

## Honesty

`ClosedObservableFramework` alone does **not** force additive posting
(`closedFramework_does_not_force_additive_posting`). Extensivity /
local binary recurrence are therefore **disclosed** content fields of
`P_closure` (COND), not derived from the bare framework. Fake-closure ban:
this file does not put `additive_posting : True` or assume `isClosed` as
the premise that claims to derive `isClosed`.

Plan: `plans/PartI_Hard_Half_Closure_Plan_20260723.html` Lane B.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine

open HierarchyRealizationObstruction
open HierarchyDynamics
open HierarchyEmergence
open PhiForcingDerived
open PostingExtensivity
open ClosedFramework
open Constants

/-! ## Step 1: Extensivity predicate and Bool exclusion -/

/-- Operational Recognition ledger extensivity: the orbit-defined scale
levels carry additive ℝ posting of scale work at the first binary
composition step (`L₂ = L₁ + L₀`).

This is the content of posting extensivity compatible with ledger work
addition (see `PostingExtensivity` / RCL posting potential). It is
**not** definitionally `GeometricScaleSequence.isClosed` (powers of a
ratio), and it is not `True`. -/
def CarriesAdditiveScalePosting (F : ClosedObservableFramework) (base : F.S) :
    Prop :=
  F.r (F.T^[2] base) = F.r (F.T^[1] base) + F.r base

/-- An admissible Recognition scale ledger: a closed-observable framework
whose base orbit carries additive ℝ scale posting. -/
structure AdmissibleScaleLedger where
  F : ClosedObservableFramework
  base : F.S
  extensive : CarriesAdditiveScalePosting F base

/-- The Bool closed-observable countermodel orbit fails additive ℝ scale
posting, hence is not an admissible Recognition scale ledger. -/
theorem bool_orbit_not_admissible :
    ¬ CarriesAdditiveScalePosting boolFramework baseState :=
  orbit_not_additive_posting

/-- Package form: the Bool obstruction base cannot inhabit
`AdmissibleScaleLedger`. -/
theorem boolFramework_not_admissible_scale_ledger :
    ¬ ∃ (_ext : CarriesAdditiveScalePosting boolFramework baseState),
      True := by
  intro h
  exact bool_orbit_not_admissible h.1

/-! ## Step 2–4: Disclosed P_closure → Fibonacci → isClosed → φ -/

/-- Geometric scale sequence associated to a uniform ladder ratio. -/
noncomputable def ladderToGeometric (L : UniformScaleLadder) :
    GeometricScaleSequence where
  ratio := L.ratio
  ratio_pos := lt_trans (by norm_num : (0 : ℝ) < 1) L.ratio_gt_one
  ratio_ne_one := ne_of_gt L.ratio_gt_one

/-- Disclosed stronger premises for selected scale closure (`P_closure`):
uniform geometric ladder, local binary recurrence with positive integer
coefficients, and zero-parameter minimality (`max(a,b) = 1`).

Locality and the recurrence itself are **disclosed** (COND): they are not
forced by `ClosedObservableFramework` alone. Zero-param then forces
`(a,b) = (1,1)` by pure arithmetic (`zero_param_forces_unit_coefficients`). -/
structure ClosureNecessityPremises where
  recurrence : LocalBinaryRecurrence
  minimal : IsMinimalRecurrence recurrence

/-- Under disclosed `P_closure`, the ladder satisfies Fibonacci posting
`L₂ = L₁ + L₀`. -/
theorem premises_force_fibonacci (P : ClosureNecessityPremises) :
    P.recurrence.ladder.levels 2 =
      P.recurrence.ladder.levels 1 + P.recurrence.ladder.levels 0 := by
  have ⟨ha1, hb1⟩ :=
    zero_param_forces_unit_coefficients
      P.recurrence.coeff_a P.recurrence.coeff_b
      P.recurrence.coeff_a_pos P.recurrence.coeff_b_pos P.minimal
  exact unit_coefficients_give_fibonacci
    P.recurrence.ladder P.recurrence.coeff_a P.recurrence.coeff_b
    ha1 hb1 P.recurrence.local_recurrence

/-- Fibonacci posting on a uniform ladder forces geometric `isClosed`
(`S0 + S1 = S2` on powers of the ratio). -/
theorem fibonacci_forces_isClosed (L : UniformScaleLadder)
    (h : L.levels 2 = L.levels 1 + L.levels 0) :
    (ladderToGeometric L).isClosed := by
  have hgold := locality_forces_additive_composition L h
  unfold GeometricScaleSequence.isClosed ledgerCompose GeometricScaleSequence.scale
    ladderToGeometric
  simp only [pow_zero, pow_one]
  -- goal: 1 + L.ratio = L.ratio ^ 2
  have : L.ratio ^ 2 = L.ratio + 1 := hgold
  linarith

/-- Disclosed `P_closure` forces geometric `isClosed` on the ladder ratio. -/
theorem premises_force_isClosed (P : ClosureNecessityPremises) :
    (ladderToGeometric P.recurrence.ladder).isClosed :=
  fibonacci_forces_isClosed P.recurrence.ladder (premises_force_fibonacci P)

/-- Disclosed `P_closure` forces the scale ratio to be φ
(`HierarchyDynamics.hierarchy_dynamics_forces_phi`). -/
theorem premises_force_phi (P : ClosureNecessityPremises) :
    P.recurrence.ladder.ratio = phi := by
  have h := hierarchy_dynamics_forces_phi P.recurrence P.minimal
  -- `hierarchy_dynamics_forces_phi` returns `PhiForcing.φ`; same value as `phi`.
  simpa [PhiForcing.φ, phi] using h

/-- Admissible orbit posting on a uniform ladder is the Fibonacci relation,
hence yields `isClosed` and φ. -/
theorem admissible_uniform_forces_phi (L : UniformScaleLadder)
    (h : L.levels 2 = L.levels 1 + L.levels 0) :
    L.ratio = phi := by
  have hφ := hierarchy_emergence_forces_phi L h
  simpa [PhiForcing.φ, phi] using hφ

/-! ## Necessity binder -/

/-- **Selected scale-closure necessity binder** (`P_closure` package).

Inhabited under disclosed Recognition ledger premises. Does **not** claim
that `ClosedObservableFramework` alone forces additive posting or φ. -/
structure SelectedClosureNecessity : Prop where
  /-- Bool closed-observable orbits are inadmissible as Recognition scale
  ledgers under additive ℝ scale posting. -/
  inadmissible_bool :
    ¬ CarriesAdditiveScalePosting boolFramework baseState
  /-- Disclosed uniform + local binary + zero-param `(1,1)` forces Fibonacci
  posting on the ladder. -/
  from_premises_fibonacci :
    ∀ P : ClosureNecessityPremises,
      P.recurrence.ladder.levels 2 =
        P.recurrence.ladder.levels 1 + P.recurrence.ladder.levels 0
  /-- Same package forces geometric `isClosed` (`S0+S1=S2`). -/
  from_premises_isClosed :
    ∀ P : ClosureNecessityPremises,
      (ladderToGeometric P.recurrence.ladder).isClosed
  /-- Same package forces the ratio to be φ. -/
  from_premises_phi :
    ∀ P : ClosureNecessityPremises, P.recurrence.ladder.ratio = phi
  /-- Extensivity / additive scale posting is disclosed COND: not forced by
  `ClosedObservableFramework` alone (obstruction countermodel). -/
  additive_posting_disclosed_not_forced :
    ∃ (F : ClosedObservableFramework) (base : F.S),
      ¬ CarriesAdditiveScalePosting F base
  /-- Alternate cubic short closure still admits a positive root ≠ φ. -/
  plastic_independence :
    ∃ r : ℝ, 0 < r ∧ r ≠ phi ∧ r ^ 3 = r + 1

/-- The selected-closure necessity binder holds (sorry-free).

Tag: necessity of φ under disclosed `P_closure` is THEOREM; the status of
deriving extensivity / locality from still-earlier structure alone remains
OPEN / COND (`additive_posting_disclosed_not_forced`). -/
theorem selectedClosureNecessity_holds : SelectedClosureNecessity where
  inadmissible_bool := bool_orbit_not_admissible
  from_premises_fibonacci := premises_force_fibonacci
  from_premises_isClosed := premises_force_isClosed
  from_premises_phi := premises_force_phi
  additive_posting_disclosed_not_forced := by
    obtain ⟨F, base, h⟩ := closedFramework_does_not_force_additive_posting
    exact ⟨F, base, h⟩
  plastic_independence := exists_plastic_root_ne_phi

end PublicSpine
end Foundation
end IndisputableMonolith
