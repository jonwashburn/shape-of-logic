import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.SymplecticAction

/-!
# Is the half-imbalance chart derived, or stipulated? **VERDICT: STIPULATED.**

## The verdict, stated first

**The claim `C` below FAILED its own pre-registered criteria.** The chart is not
derived, and with the geometry route already closed, Pillar 1 has no surviving named
route by which a recognition primitive derives classical gravity.

The four parts are all true and are all still here, kernel-clean. What failed is the
*attribution*, which is the fifth time in this programme that a correct theorem
carried a wrong attribution. Three independent defects, each verified against the
frozen criteria below rather than argued about:

1. **The smuggled premise, decisive.** Part 2 selects the imbalance among *linear*
   observables. Drop linearity and the tolerated family is infinite-dimensional:
   `m + m ^ 3` is a strictly monotone coordinate vanishing exactly on the balance
   locus, its coordinate change with `s / (1 + 3 m ^ 2)` is area-preserving so it is
   genuinely canonical, and the cost is not quadratic in it
   (`chart_not_forced_without_linearity`). Nothing in the substrate forces the
   momentum observable to be linear: recognition *events* are linear maps, but linear
   dynamics does not imply linear canonical coordinates. The frozen fail criterion
   "the tolerated chart family is positive-dimensional" is therefore met, and it was
   written down before the answer was known.
2. **A state/event splice.** `Cost.SymplecticAction` assigns cost to an *event*:
   `traceCost (diagSL x) = Jcost x`. Part 4 applies the cost to a *state's* ratio.
   The event carrying the balanced state to `orbitPoint k t` is
   `diagSL (exp (t / 2))`, whose substrate cost is `Jlog (t / 2)`, not the `Jlog t`
   part 4 uses (`event_cost_differs_from_state_cost`). So part 1's symplectic
   provenance does not license part 4, and the two halves are about different
   objects.
3. **No net reduction in what is assumed.** The theorems mention neither the ADM
   momentum `p` nor `lam`. The equation the physics still needs is
   `lam * p = m / (2 * sqrt k)`, which on a fixed orbit is *logically equivalent* to
   the chart it was supposed to derive. The gain is presentational: a transcendental
   stipulation becomes a linear one. Presentational gain restated as derivation is
   exactly what went wrong four times before, so it is recorded as a gain in
   exposition and not in provenance.

Two further hits worth keeping. Part 1 is a renaming: `ConservesSigma` is *defined*
as `det M = 1`, so "sigma-conservation is symplectic" is a definitional unfolding.
And sigma-conservation does not preserve the imbalance at all, since `diagSL 2`
conserves it while carrying `(1,1)` to `(2, 1/2)`, so the imbalance is not the
sigma-privileged observable and no write-up may say it is.

**What survives, at its honest strength.** `Jlog t = imbalance ^ 2 / (2 * casimir)`
is exact and true, and it is a one-line rearrangement of `J`'s definition,
`J (d / c) = (d - c) ^ 2 / (2 d c)`. It is a clean reformulation of the recognition
cost, not a derivation of anything. Anyone quoting it must say that.

Verdict reached after a hostile cross-family read, with all three decisive
computations reverified independently before conceding. Frozen criteria committed at
`81620cd46d`, first verdict at `afb610fa84`, refutation formalized below.

## The frozen record, unedited

Everything from here to the end of this docstring was committed at `81620cd46d`
before any theorem in the file was written, so that the git history is the audit
trail and a reader need not trust the author
(`L-qg-freeze-the-candidate-before-you-price-it`). It is preserved verbatim,
including the parts the verdict above overturns. That is the point of freezing.

## The question

`HKTKineticFromRecognitionCost.exactCostKineticProfile` posts the exact
recognition cost of the momentum channel read in the chart

  `t = 2 * Real.arsinh (lam * p)`,

and in that chart the cost is exactly quadratic (`Jlog_two_arsinh`), which is the
premise Hojman-Kuchar-Teitelboim rigidity needs. A cross-family panel then showed
the clause is empty as a test of recognition, for two reasons proved in
`Gap5ReparamAttackOnConstraintSector`: the chart is `J`'s own inverse, so *any*
function quadratic in it is a multiple of `J` (`chart_alone_forces_the_cost`); and
the chart is **typed in as a literal**, with nothing deriving it.

Section 4 of `HKTKineticFromRecognitionCost` proves that the rival identification
`t = kappa * p`, momentum linear in the log-imbalance, is *excluded*: it makes the
momentum response `sinh` and the algebra demands linear
(`no_exact_cost_kinetic_canonicalMom`). So the whole constraint-sector claim turns
on which of two coordinates on the same ledger is the momentum, and the repo
currently supplies no reason to prefer either.

## The frozen claim under test

`C`: **the substrate's own symplectic structure selects the half-imbalance chart,
because `lam * p` is the ledger's canonical momentum.**

Concretely, the claim to be proved or refuted has four parts, in order.

1. The recognition ledger's phase space is the debit-credit plane, and
   sigma-conservation makes it symplectic. Already a theorem:
   `Cost.SymplecticAction.conservesSigma_iff_preservesArea`.
2. On the debit-credit plane there is, up to scale, exactly **one** linear
   functional vanishing at the balanced ground state `(1,1)`, namely the net
   imbalance `m = d - c`. This selection mentions the cost nowhere.
3. `m` is a canonical momentum: it is symplectically conjugate to the ledger
   total `s = d + c`, up to a constant.
4. On a split-torus orbit of Casimir `d * c = k > 0` the recognition cost of the
   ledger ratio is **exactly** half the squared imbalance over the Casimir,
   `Jlog t = m ^ 2 / (2 * k)`, with no truncation. Hence
   `lam * p = m / (2 * sqrt k)` reproduces `exactCostKineticProfile` and the
   chart's free constant `lam` is the ledger scale rather than a fitted number.

## Pass criteria, fixed in advance

`C` passes only if all four hold, and additionally:

- **Grep test.** A recognition primitive appears in the statement, not the
  motivation. Here: `Cost.Jlog` / `Cost.Jcost` and `ConservesSigma`.
- **Deletion test.** Removing the primitive breaks the result. Here: part 4 must
  fail for a cost that is not `J`.
- **Chart test** (`L-never-test-a-primitive-in-a-chart-built-from-it`, the test
  this file exists to satisfy). The coordinate must be derived independently of
  the primitive under test. Part 2 is the whole load: `m` is selected by linear
  algebra and the ground state alone, with `J` absent from the statement. If part
  2 needed `J`, `C` fails however pretty parts 3 and 4 are.
- **Reparametrization attack, run by the author before any write-up.** Exhibit
  the family of charts the argument still tolerates and show it is a point, not a
  family. Concretely: if `chi` is any increasing function fixing `0`, is
  `chi(m)` also selected? Part 2's linearity is what must exclude it, and the
  exclusion must be a theorem in this file, not a remark.

## Fail criteria, equally fixed in advance

`C` fails if part 2 requires the cost to select `m`; or if part 4 holds only to
second order rather than exactly; or if the tolerated chart family is
positive-dimensional. A failure closes the last named Pillar 1 provenance route
and is written up at equal effort, per the binding plan
`plans/QG_Pillar1_Provenance_Verdict_Master_Plan_20260726.html`.

## What `C` does not decide, stated before the result is known

Even a full pass leaves one bridge: that the ledger's canonical momentum **is**
the ADM momentum conjugate to the spatial metric. `C` replaces an unexplained
`arsinh` literal with a named identification of two momenta. That is strictly
better and it is not the same as closed, and no write-up of this file may say
otherwise. `C` also does not fix the magnitude: the Casimir `k` is free, so
`cKin = 2 * lam ^ 2` stays a positivity statement, exactly as the
`HKTKineticFromRecognitionCost` header already records.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace ChartFromLedgerMomentum

noncomputable section

open Cost

/-! ## The objects under test, defined before anything is claimed about them -/

/-- A ledger state: a debit-credit pair. This is the phase space of
`Cost.SymplecticAction`, whose area form sigma-conservation preserves. -/
abbrev LedgerState := ℝ × ℝ

/-- The balanced ground state: equal debit and credit, the sigma = 0 state at
which the recognition cost vanishes. -/
def balanced : LedgerState := (1, 1)

/-- The net imbalance of a ledger state. Candidate for the ledger's canonical
momentum. Defined by subtraction; no cost appears. -/
def imbalance (z : LedgerState) : ℝ := z.1 - z.2

/-- The ledger total. Candidate for the coordinate conjugate to the imbalance. -/
def total (z : LedgerState) : ℝ := z.1 + z.2

/-- The Casimir of the split-torus action `(d, c) ↦ (x d, c / x)`: the one
combination every sigma-conserving diagonal event fixes. -/
def casimir (z : LedgerState) : ℝ := z.1 * z.2

/-- The split-torus orbit point at log-ratio `t` and Casimir `k`: the ledger state
with `d / c = exp t` and `d * c = k`. The description holds only for `0 ≤ k`, since
`Real.sqrt` of a negative is `0` and the point degenerates to the origin; every
theorem below therefore carries a positivity hypothesis. -/
def orbitPoint (k t : ℝ) : LedgerState :=
  (Real.sqrt k * Real.exp (t / 2), Real.sqrt k * Real.exp (-t / 2))

/-- A linear functional on the debit-credit plane, written by its coefficients so
that "linear" is a property of the data rather than a promise in a comment. -/
def linFunctional (a b : ℝ) (z : LedgerState) : ℝ := a * z.1 + b * z.2

/-- The predicate part 2 is about: a linear functional vanishing at balance. The
recognition cost is absent from this definition, which is the point. -/
def VanishesAtBalanced (a b : ℝ) : Prop := linFunctional a b balanced = 0

/-- A ledger state is balanced when its debit equals its credit. This is the
defining constraint of double-entry bookkeeping and it is prior to any cost: it
mentions no functional, no primitive, and no normalization. It is used below to
strengthen part 2 so that the selection of the momentum coordinate does not depend
on where the *cost* vanishes. -/
def Balanced (z : LedgerState) : Prop := z.1 = z.2

/-! ## Part 2. The imbalance is the unique linear observable vanishing at balance

This is the load-bearing part, and it is the one the chart test asks about
(`L-never-test-a-primitive-in-a-chart-built-from-it`). Nothing below mentions
`Jcost`, `Jlog`, or any recognition primitive: the selection is linear algebra
together with the location of the ground state. That is what distinguishes this
from the profile clause, whose coordinate was chosen so that the cost would look
quadratic in it. -/

/-- A linear functional on the ledger plane vanishes at the balanced state exactly
when its coefficients are opposite. -/
theorem vanishesAtBalanced_iff (a b : ℝ) : VanishesAtBalanced a b ↔ b = -a := by
  unfold VanishesAtBalanced linFunctional balanced
  constructor
  · intro h; simp at h; linarith
  · intro h; simp [h]

/-- **The imbalance is forced, up to scale.** Every linear observable on the
debit-credit plane that vanishes at the balanced ground state is a scalar multiple
of the net imbalance. The recognition cost appears nowhere in the hypothesis, so
this selection cannot be an artefact of the cost's shape. -/
theorem imbalance_is_the_unique_linear_selection (a b : ℝ)
    (h : VanishesAtBalanced a b) :
    ∀ z : LedgerState, linFunctional a b z = a * imbalance z := by
  rw [vanishesAtBalanced_iff] at h
  intro z
  simp [linFunctional, imbalance, h]
  ring

/-- The imbalance is itself such an observable, so the previous theorem is not
vacuous. -/
theorem imbalance_vanishesAtBalanced : VanishesAtBalanced 1 (-1) := by
  simp [vanishesAtBalanced_iff]

theorem linFunctional_one_neg_one (z : LedgerState) :
    linFunctional 1 (-1) z = imbalance z := by
  simp [linFunctional, imbalance]; ring

/-! ### Part 2, strengthened so the ground state is not the cost's

The version above selects the imbalance from vanishing at the single normalized
state `(1,1)`, which invites the objection that `(1,1)` was located by asking where
the recognition cost vanishes. The objection is answered by using the whole
double-entry balance locus `{d = c}` instead, which is the bookkeeping constraint
itself. The conclusion is unchanged, so nothing here depends on the normalization,
and the selection of the momentum coordinate is now downstream of double-entry
alone. -/

/-- A linear observable vanishes on the entire balanced locus exactly when its
coefficients are opposite. The forward direction needs only one balanced state, but
the hypothesis no longer privileges any particular one. -/
theorem vanishesOnBalancedLocus_iff (a b : ℝ) :
    (∀ z : LedgerState, Balanced z → linFunctional a b z = 0) ↔ b = -a := by
  constructor
  · intro h
    have h1 := h (1, 1) rfl
    simp [linFunctional] at h1
    linarith
  · intro h z hz
    simp only [Balanced] at hz
    simp [linFunctional, h, hz]

/-- **The imbalance is forced by double-entry alone.** Every linear observable on
the ledger plane that vanishes on the balanced locus is a scalar multiple of the net
imbalance. No cost, no primitive, and no normalization appears in the hypothesis, so
this is the version that satisfies the chart test without argument. -/
theorem imbalance_forced_by_balance_locus (a b : ℝ)
    (h : ∀ z : LedgerState, Balanced z → linFunctional a b z = 0) :
    ∀ z : LedgerState, linFunctional a b z = a * imbalance z := by
  rw [vanishesOnBalancedLocus_iff] at h
  intro z
  simp [linFunctional, imbalance, h]
  ring

/-- **The tolerated family is one-dimensional, and its parameter is scale.** The
reparametrization attack, run against this file's own claim: the set of coordinates
part 2 admits is exactly `{a • imbalance}`, so it is a single ray rather than a
positive-dimensional family of charts. Compare O5, where the level-set argument
tolerated every increasing reparametrization fixing the rungs and therefore
identified nothing. The surviving scale is not a loophole that was overlooked; it
is the ledger scale, and it is the same freedom already recorded as unfixed in the
`HKTKineticFromRecognitionCost` header. -/
theorem tolerated_family_is_a_scale_ray :
    {f : LedgerState → ℝ | ∃ a b : ℝ, VanishesAtBalanced a b ∧ f = linFunctional a b}
      = {f : LedgerState → ℝ | ∃ a : ℝ, f = fun z => a * imbalance z} := by
  ext f
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨a, funext (imbalance_is_the_unique_linear_selection a b hab)⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a, -a, by simp [vanishesAtBalanced_iff], funext fun z => ?_⟩
    simp [linFunctional, imbalance]; ring

/-! ## Part 3. The imbalance is a canonical momentum

`Cost.SymplecticAction` proves that sigma-conservation is preservation of the
ledger area form. Here the imbalance-total coordinate change is shown to rescale
that form by a constant, which is what makes `(imbalance, total)` a canonical pair
up to normalization, so calling the imbalance a momentum is a statement about the
substrate's symplectic structure and not a naming convention. -/

/-- The ledger state as a vector, so the area form of `Cost.SymplecticAction`
applies to it. -/
def toVec (z : LedgerState) : Fin 2 → ℝ := ![z.1, z.2]

/-- The change of coordinates from debit-credit to imbalance-total. -/
def imbalanceTotalMap : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 1, 1]

theorem imbalanceTotalMap_apply (z : LedgerState) :
    imbalanceTotalMap.mulVec (toVec z) = ![imbalance z, total z] := by
  funext i
  fin_cases i <;>
    simp [imbalanceTotalMap, toVec, imbalance, total, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> ring

theorem imbalanceTotalMap_det : imbalanceTotalMap.det = 2 := by
  simp [imbalanceTotalMap, Matrix.det_fin_two_of]; ring

/-- **The imbalance and the total are canonically conjugate up to a constant.**
The coordinate change rescales the ledger area form by exactly `2`, so it is
symplectic after normalization. Hence the imbalance is a momentum in the
substrate's own symplectic structure, the one sigma-conservation forces. -/
theorem imbalance_total_is_a_canonical_pair (v w : Fin 2 → ℝ) :
    Cost.SymplecticAction.areaForm (imbalanceTotalMap.mulVec v)
        (imbalanceTotalMap.mulVec w)
      = 2 * Cost.SymplecticAction.areaForm v w := by
  rw [Cost.SymplecticAction.areaForm_mulVec, imbalanceTotalMap_det]

/-! ## Part 4. The recognition cost is exactly the squared imbalance

No truncation, no jet, no fitted coefficient: an identity on every split-torus
orbit, with the Casimir supplying the normalization. -/

/-- The recognition cost in the log-imbalance chart is twice the squared
half-imbalance. This is `Jlog t = cosh t - 1 = 2 sinh (t/2) ^ 2` written so that
the right-hand side is the object part 4 is about. -/
theorem Jlog_eq_two_sinh_half_sq (t : ℝ) :
    Cost.Jlog t = 2 * Real.sinh (t / 2) ^ 2 := by
  have hc : Real.cosh t = 2 * Real.sinh (t / 2) ^ 2 + 1 := by
    rw [show t = 2 * (t / 2) from by ring, Real.cosh_two_mul, Real.cosh_sq]
    ring
  rw [Cost.Jlog_as_cosh, hc]
  ring

theorem orbitPoint_casimir (k t : ℝ) (hk : 0 ≤ k) :
    casimir (orbitPoint k t) = k := by
  have hsq : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk
  have hexp : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
    rw [← Real.exp_add, show t / 2 + -t / 2 = (0 : ℝ) from by ring, Real.exp_zero]
  simp only [casimir, orbitPoint]
  calc Real.sqrt k * Real.exp (t / 2) * (Real.sqrt k * Real.exp (-t / 2))
      = (Real.sqrt k * Real.sqrt k) * (Real.exp (t / 2) * Real.exp (-t / 2)) := by ring
    _ = k := by rw [hsq, hexp, mul_one]

/-- The imbalance of the orbit point is the half-imbalance sine, scaled by the
square root of the Casimir. -/
theorem orbitPoint_imbalance (k t : ℝ) :
    imbalance (orbitPoint k t) = Real.sqrt k * (2 * Real.sinh (t / 2)) := by
  simp only [imbalance, orbitPoint, Real.sinh_eq]
  rw [show (-t / 2 : ℝ) = -(t / 2) by ring]
  ring

/-- **The recognition cost is exactly half the squared ledger imbalance.** On the
split-torus orbit of Casimir `k > 0`, the cost of the ledger ratio equals
`m ^ 2 / (2 k)` where `m` is the net imbalance of the ledger state. Exact, not a
second-order jet: this is the identity that the profile clause was reaching for,
now with its coordinate supplied by part 2 instead of typed in. -/
theorem Jlog_eq_imbalance_sq_div_two_casimir (k t : ℝ) (hk : 0 < k) :
    Cost.Jlog t = imbalance (orbitPoint k t) ^ 2 / (2 * k) := by
  have hsq : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk.le
  rw [orbitPoint_imbalance, Jlog_eq_two_sinh_half_sq]
  field_simp
  nlinarith [hsq]

/-- The chart variable of `exactCostKineticProfile`, identified. The literal
`lam * p` in that profile is the ledger's net imbalance in units of twice the
square root of the Casimir, so the chart's free constant is the ledger scale. -/
theorem chart_variable_is_the_normalized_imbalance (k t : ℝ) (hk : 0 < k) :
    Real.sinh (t / 2) = imbalance (orbitPoint k t) / (2 * Real.sqrt k) := by
  have hne : Real.sqrt k ≠ 0 := by
    simpa using Real.sqrt_ne_zero'.mpr hk
  rw [orbitPoint_imbalance]
  field_simp

/-- **The chart, derived.** The half-imbalance chart `t = 2 arsinh (lam * p)` is
exactly the statement that the momentum is the ledger's net imbalance at scale
`lam = 1 / (2 sqrt k)`. The `arsinh` is not a coordinate choice; it is the inverse
of the map from log-ratio to imbalance. -/
theorem chart_is_the_imbalance_coordinate (k t : ℝ) (hk : 0 < k) :
    t = 2 * Real.arsinh (imbalance (orbitPoint k t) / (2 * Real.sqrt k)) := by
  rw [← chart_variable_is_the_normalized_imbalance k t hk, Real.arsinh_sinh]
  ring

/-! ## The deletion test

Part 2 selects the coordinate without the cost, so the chart test is satisfied by
construction. The deletion test is the other direction: the exactness in part 4 is
a property of the recognition cost and fails for a neighbouring cost. -/

theorem sinh_two_arsinh (u : ℝ) :
    Real.sinh (2 * Real.arsinh u) = 2 * u * Real.sqrt (1 + u ^ 2) := by
  rw [Real.sinh_two_mul, Real.sinh_arsinh, Real.cosh_arsinh]

/-- The second power cost, `x ↦ J (x ^ 2)`, in the log chart, and the nearest
neighbour of the recognition cost inside the power family. Correction after a hostile
read: this cost *does* satisfy the composition law
(`Gap5ReparamAttackOnConstraintSector.powCost_satisfiesCompositionLaw`) and what
excludes it is calibration (`isCalibrated_powCost_iff`), so an earlier version of this
docstring was simply wrong about which property fails. -/
def powTwoJlog (t : ℝ) : ℝ := Real.cosh (2 * t) - 1

/-- **Deleting the recognition cost breaks part 4.** The second power cost is not a
quadratic function of the ledger imbalance: in the imbalance coordinate it is
quartic. So "the cost is exactly the squared imbalance" is a fact about `J` and not
about the coordinate, which is precisely what the profile clause could not say
about itself. -/
theorem powTwoJlog_not_quadratic_in_imbalance :
    ¬ ∃ C : ℝ, ∀ u : ℝ, powTwoJlog (2 * Real.arsinh u) = C * u ^ 2 := by
  rintro ⟨C, hC⟩
  have key : ∀ u : ℝ, powTwoJlog (2 * Real.arsinh u) = 8 * u ^ 2 * (1 + u ^ 2) := by
    intro u
    have hs : Real.sqrt (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) = 1 + u ^ 2 :=
      Real.mul_self_sqrt (by positivity)
    have hpt : powTwoJlog (2 * Real.arsinh u) = Cost.Jlog (4 * Real.arsinh u) := by
      simp only [powTwoJlog, Cost.Jlog_as_cosh,
        show 2 * (2 * Real.arsinh u) = 4 * Real.arsinh u from by ring]
    rw [hpt, Jlog_eq_two_sinh_half_sq,
      show 4 * Real.arsinh u / 2 = 2 * Real.arsinh u from by ring, sinh_two_arsinh]
    nlinarith [hs]
  have h1 := hC 1
  have h2 := hC 2
  rw [key 1] at h1
  rw [key 2] at h2
  norm_num at h1 h2
  linarith

/-! ## The refutation

Formalized alongside the result it refutes, which is this programme's standing
practice for a killed attribution (the O5 counterexample is kept the same way). Two
defects are made into theorems here so that no future reader can restore the claim
by reading only the parts that worked.

### Defect 1, decisive: linearity is doing all the work

The referee's coordinate. `nlP` is strictly monotone and vanishes exactly on the
balance locus, so it is a legitimate coordinate by every criterion part 2 imposed
except linearity. Paired with `nlQ` the coordinate change is area-preserving, so it
is canonical too, and the cost is not quadratic in it. Hence part 2's selection of
the imbalance is an artefact of restricting to linear observables. -/

/-- The nonlinear momentum coordinate that defeats part 2. -/
def nlP (m : ℝ) : ℝ := m + m ^ 3

/-- Its area-preserving partner, so the pair is canonical and not merely a
relabelling of one axis. -/
def nlQ (m s : ℝ) : ℝ := s / (1 + 3 * m ^ 2)

theorem nlP_factor (m : ℝ) : nlP m = m * (1 + m ^ 2) := by
  simp [nlP]; ring

/-- `nlP` vanishes exactly where the imbalance does, so it respects the double-entry
balance locus just as the imbalance does. -/
theorem nlP_eq_zero_iff (m : ℝ) : nlP m = 0 ↔ m = 0 := by
  rw [nlP_factor, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · nlinarith [sq_nonneg m]
  · intro h; exact Or.inl h

/-- `nlP` is a strictly monotone reparametrization, hence a genuine coordinate. -/
theorem nlP_strictMono : StrictMono nlP := by
  intro a b hab
  simp only [nlP]
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

theorem nlP_hasDerivAt (m : ℝ) : HasDerivAt nlP (1 + 3 * m ^ 2) m := by
  have h : HasDerivAt (fun x : ℝ => x + x ^ 3) (1 + 3 * m ^ 2) m := by
    simpa using (hasDerivAt_id m).add ((hasDerivAt_id m).pow 3)
  exact h

/-- `nlP` does not depend on the conjugate coordinate, which is why the Jacobian
determinant below is `1` whatever the remaining partial derivative is. -/
theorem nlP_hasDerivAt_snd (m s : ℝ) :
    HasDerivAt (fun _ : ℝ => nlP m) 0 s := hasDerivAt_const s (nlP m)

theorem nlQ_hasDerivAt_snd (m s : ℝ) :
    HasDerivAt (fun y : ℝ => nlQ m y) (1 / (1 + 3 * m ^ 2)) s := by
  have hne : (1 : ℝ) + 3 * m ^ 2 ≠ 0 := by positivity
  simpa [nlQ, div_eq_mul_inv, one_div] using
    (hasDerivAt_id s).mul_const ((1 + 3 * m ^ 2)⁻¹)

/-- **The nonlinear coordinate change is area-preserving.** Its Jacobian determinant
is `1`, with the diagonal entries supplied by `nlP_hasDerivAt` and
`nlQ_hasDerivAt_snd` and the upper-right entry by `nlP_hasDerivAt_snd`. The
determinant is `1` for *every* value of the remaining partial derivative `q`, which
is why that derivative never has to be computed. So `(nlP, nlQ)` is a canonical pair,
and the counterexample survives demanding that the momentum coordinate be
canonical. -/
theorem nl_jacobian_det_eq_one (m q : ℝ) :
    Matrix.det !![1 + 3 * m ^ 2, 0; q, 1 / (1 + 3 * m ^ 2)] = 1 := by
  have hne : (1 : ℝ) + 3 * m ^ 2 ≠ 0 := by positivity
  simp [Matrix.det_fin_two_of]
  field_simp

/-- **The cost is not quadratic in the nonlinear coordinate.** At unit Casimir the
cost is `m ^ 2 / 2`, and no single constant makes that a multiple of `nlP m ^ 2`:
the coefficient would have to be `1 / 8` at `m = 1` and `1 / 50` at `m = 2`. -/
theorem cost_not_quadratic_in_nlP :
    ¬ ∃ C : ℝ, ∀ m : ℝ, m ^ 2 / 2 = C * nlP m ^ 2 := by
  rintro ⟨C, hC⟩
  have h1 := hC 1
  have h2 := hC 2
  simp only [nlP] at h1 h2
  norm_num at h1 h2
  linarith

/-- **Defect 1, assembled: the chart is not forced once linearity is dropped.**
There is a strictly monotone coordinate, vanishing exactly on the balance locus and
belonging to an area-preserving pair, in which the recognition cost is not quadratic.
So part 2 selects the imbalance by fiat, and the frozen fail criterion "the tolerated
chart family is positive-dimensional" is met. This is the same failure shape as O5,
where the argument tolerated every increasing reparametrization fixing the rungs. -/
theorem chart_not_forced_without_linearity :
    ∃ g : ℝ → ℝ, StrictMono g ∧ (∀ m : ℝ, g m = 0 ↔ m = 0)
      ∧ (∀ m q : ℝ, Matrix.det !![1 + 3 * m ^ 2, 0; q, 1 / (1 + 3 * m ^ 2)] = 1)
      ∧ ¬ ∃ C : ℝ, ∀ m : ℝ, m ^ 2 / 2 = C * g m ^ 2 :=
  ⟨nlP, nlP_strictMono, nlP_eq_zero_iff, nl_jacobian_det_eq_one,
    cost_not_quadratic_in_nlP⟩

/-! ### Defect 2: part 4 costs a state, part 1 costs an event

`Cost.SymplecticAction.traceCost_diagSL` gives the cost of an *event*. The event
carrying the balanced state to `orbitPoint k t` is `diagSL (exp (t / 2))`, so the
substrate's cost of that event is `Jlog (t / 2)`. Part 4 uses `Jlog t`. They differ,
so the symplectic provenance imported in part 1 does not license part 4. -/

/-- The two readings disagree, so the splice is real and not a matter of convention.
Witnessed at `t = 2`: the event cost is `Jlog 1` and part 4's cost is `Jlog 2`. -/
theorem event_cost_differs_from_state_cost : Cost.Jlog 1 ≠ Cost.Jlog 2 := by
  rw [Jlog_eq_two_sinh_half_sq, Jlog_eq_two_sinh_half_sq]
  have h0 : 0 < Real.sinh (1 / 2 : ℝ) := by
    have h := Real.sinh_lt_sinh.mpr (show (0 : ℝ) < 1 / 2 by norm_num)
    simpa using h
  have hlt : Real.sinh (1 / 2 : ℝ) < Real.sinh (2 / 2 : ℝ) := by
    apply Real.sinh_lt_sinh.mpr; norm_num
  intro h
  nlinarith [h0, hlt]

/-- The event that carries the balanced state of Casimir `k` to `orbitPoint k t` has
eigenvalue `exp (t / 2)`, which is the fact that produces the mismatch above. -/
theorem orbitPoint_is_reached_by_event (k t : ℝ) :
    orbitPoint k t
      = (Real.exp (t / 2) * Real.sqrt k, (Real.exp (t / 2))⁻¹ * Real.sqrt k) := by
  simp only [orbitPoint, Prod.mk.injEq]
  rw [show (-t / 2 : ℝ) = -(t / 2) by ring, Real.exp_neg]
  exact ⟨by ring, by ring⟩

/-! ## The successor, reduced

The refutation above leaves exactly one repair: force linearity from the substrate. This
section does the cheap half of that repair honestly, by showing that **linearity is not
the premise actually needed**. A strictly weaker and far more physical premise suffices:
that the momentum observable is *additive under ledger consolidation*.

Consolidating two double-entry ledgers is componentwise addition of debits and credits,
which is what aggregating accounts means, and it is the addition `LedgerState` already
carries. An observable that is additive under it, and continuous, is linear by Cauchy's
functional equation, and then part 2 forces it to be the imbalance. So the open problem
shrinks from "why linear", which is a regularity class and therefore the wrong kind of
question, to "why additive under consolidation", which is extensivity and is the kind of
thing a substrate can answer.

**This is a reduction and not a closure, and the distinction is the whole lesson of this
module.** Additivity is a *premise* of the theorem below, not a consequence of anything
proved anywhere in this repository. `Foundation.JHessianGolden.additivePosting` is not
it: that result says the total *cost* is the sum of per-coordinate costs,
`Phi(x) = sum J(x i)`, which is a statement about the cost and not about any observable.
Reading it as the additivity below would repeat defect 2 exactly, a splice between two
objects that are both written as sums. Anyone continuing this line must discharge
additivity from the substrate, and must run the admissible-class test on whatever they
use to do it. -/

/-- **The reduction: additive plus continuous plus vanishing on balance forces the
imbalance.** Linearity never has to be assumed. Consolidation additivity and continuity
give `ℝ`-linearity, and then the double-entry balance locus pins the observable to a
multiple of the net imbalance.

Read the premises literally. `hadd` is additivity under the componentwise addition of
ledgers, which is consolidation. `hcont` is continuity. `hbal` is the double-entry
balance condition and mentions no cost. Nothing here is a recognition primitive, which
is the point: this theorem is the *conditional*, and the open problem is its
hypothesis. -/
theorem additive_continuous_balanced_is_imbalance
    (f : LedgerState → ℝ)
    (hadd : ∀ z w : LedgerState, f (z + w) = f z + f w)
    (hcont : Continuous f)
    (hbal : ∀ z : LedgerState, Balanced z → f z = 0) :
    ∃ a : ℝ, ∀ z : LedgerState, f z = a * imbalance z := by
  have hzero : f 0 = 0 := by
    have h := hadd 0 0
    simp only [add_zero] at h
    linarith
  let F : LedgerState →+ ℝ :=
    { toFun := f, map_zero' := hzero, map_add' := hadd }
  let L : LedgerState →ₗ[ℝ] ℝ := F.toRealLinearMap hcont
  have hLf : ∀ z : LedgerState, L z = f z := fun _ => rfl
  have hone : f ((1, 1) : LedgerState) = 0 := hbal (1, 1) rfl
  have hneg : f ((0, 1) : LedgerState) = -f ((1, 0) : LedgerState) := by
    have h := hadd (1, 0) (0, 1)
    have he : ((1, 0) : LedgerState) + ((0, 1) : LedgerState) = (1, 1) := by
      apply Prod.ext <;> simp
    rw [he, hone] at h
    linarith
  refine ⟨f (1, 0), fun z => ?_⟩
  have hsplit : z = z.1 • ((1, 0) : LedgerState) + z.2 • ((0, 1) : LedgerState) := by
    apply Prod.ext <;> simp
  have hL : f z = z.1 * f (1, 0) + z.2 * f (0, 1) := by
    rw [← hLf z]
    conv_lhs => rw [hsplit]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hLf, hLf]
  rw [hL, hneg, imbalance]
  ring

/-- The imbalance itself satisfies all three hypotheses, so the reduction is not
vacuous and the conditional has at least one inhabitant. -/
theorem imbalance_is_additive_continuous_balanced :
    (∀ z w : LedgerState, imbalance (z + w) = imbalance z + imbalance w)
      ∧ Continuous imbalance
      ∧ (∀ z : LedgerState, Balanced z → imbalance z = 0) := by
  refine ⟨fun z w => by simp [imbalance]; ring, ?_, fun z hz => ?_⟩
  · exact (continuous_fst.sub continuous_snd)
  · simp only [Balanced] at hz
    simp [imbalance, hz]

/-! ## The verdict certificate

Every field below is a theorem of this file, and the certificate is deliberately
*not* named for the claim, because the claim failed. The first six fields are the
four frozen parts and their two tests, all true. The last two fields are the defects
that make the parts insufficient. A reader who wants the parts must take the defects
with them, which is the entire purpose of packaging them in one structure. -/

/-- **The chart is stipulated, not derived: parts and defects together.** The four
frozen parts hold, and two independent defects make them insufficient for the
attribution. See the verdict at the top of this module for the third defect, that the
remaining ADM identification is logically equivalent to the chart it was to derive
and so is not formalizable as a gain. -/
structure ChartStipulatedVerdict : Prop where
  /-- Part 1, imported: sigma-conservation is preservation of the ledger area form. -/
  sigma_is_symplectic :
    ∀ M : Matrix (Fin 2) (Fin 2) ℝ,
      Cost.SymplecticAction.ConservesSigma M ↔
        ∀ v w : Fin 2 → ℝ,
          Cost.SymplecticAction.areaForm (M.mulVec v) (M.mulVec w)
            = Cost.SymplecticAction.areaForm v w
  /-- Part 2, the load-bearing one: the coordinate is selected by linear algebra
  and the double-entry balance locus, with no recognition primitive and no chosen
  normalization in the hypothesis. -/
  imbalance_forced :
    ∀ a b : ℝ, (∀ z : LedgerState, Balanced z → linFunctional a b z = 0) →
      ∀ z : LedgerState, linFunctional a b z = a * imbalance z
  /-- Part 2's reparametrization attack *within the linear class*: the tolerated
  family is the line of scalar multiples, including the zero functional. Note this is
  a line and not a ray, and it is the tolerated family only after linearity has
  already been assumed, which is what defect 1 below attacks. -/
  tolerated_linear_family_is_a_line :
    {f : LedgerState → ℝ | ∃ a b : ℝ, VanishesAtBalanced a b ∧ f = linFunctional a b}
      = {f : LedgerState → ℝ | ∃ a : ℝ, f = fun z => a * imbalance z}
  /-- Part 3: the imbalance is a canonical momentum. -/
  imbalance_is_a_momentum :
    ∀ v w : Fin 2 → ℝ,
      Cost.SymplecticAction.areaForm (imbalanceTotalMap.mulVec v)
          (imbalanceTotalMap.mulVec w)
        = 2 * Cost.SymplecticAction.areaForm v w
  /-- Part 4: the cost is exactly the squared imbalance over twice the Casimir. -/
  cost_is_squared_imbalance :
    ∀ k t : ℝ, 0 < k → Cost.Jlog t = imbalance (orbitPoint k t) ^ 2 / (2 * k)
  /-- Part 4's corollary: the stipulated chart is that coordinate. -/
  chart_is_derived :
    ∀ k t : ℝ, 0 < k →
      t = 2 * Real.arsinh (imbalance (orbitPoint k t) / (2 * Real.sqrt k))
  /-- The deletion test: a neighbouring cost fails part 4. Passing this is necessary
  and, as the earlier panel showed for `oscCost_not_quadratic_in_log_chart`, far from
  sufficient, since the chart forces the cost anyway. -/
  deletion_test :
    ¬ ∃ C : ℝ, ∀ u : ℝ, powTwoJlog (2 * Real.arsinh u) = C * u ^ 2
  /-- **Defect 1, decisive.** Drop linearity and the tolerated coordinate family is
  infinite-dimensional: there is a strictly monotone coordinate vanishing exactly on
  the balance locus, belonging to an area-preserving pair, in which the cost is not
  quadratic. -/
  linearity_is_load_bearing :
    ∃ g : ℝ → ℝ, StrictMono g ∧ (∀ m : ℝ, g m = 0 ↔ m = 0)
      ∧ (∀ m q : ℝ, Matrix.det !![1 + 3 * m ^ 2, 0; q, 1 / (1 + 3 * m ^ 2)] = 1)
      ∧ ¬ ∃ C : ℝ, ∀ m : ℝ, m ^ 2 / 2 = C * g m ^ 2
  /-- **Defect 2.** The symplectic module costs an event, part 4 costs a state, and
  the two disagree, so part 1 does not license part 4. -/
  state_event_splice : Cost.Jlog 1 ≠ Cost.Jlog 2
  /-- **The successor, as a conditional.** Linearity never needs to be assumed:
  additivity under ledger consolidation plus continuity plus vanishing on the balance
  locus already forces the imbalance. The open problem is the additivity hypothesis,
  which nothing in this repository currently supplies. -/
  reduction_to_additivity :
    ∀ f : LedgerState → ℝ,
      (∀ z w : LedgerState, f (z + w) = f z + f w) → Continuous f →
        (∀ z : LedgerState, Balanced z → f z = 0) →
          ∃ a : ℝ, ∀ z : LedgerState, f z = a * imbalance z

theorem chartStipulatedVerdict : ChartStipulatedVerdict where
  sigma_is_symplectic := Cost.SymplecticAction.conservesSigma_iff_preservesArea
  imbalance_forced := imbalance_forced_by_balance_locus
  tolerated_linear_family_is_a_line := tolerated_family_is_a_scale_ray
  imbalance_is_a_momentum := imbalance_total_is_a_canonical_pair
  cost_is_squared_imbalance := Jlog_eq_imbalance_sq_div_two_casimir
  chart_is_derived := chart_is_the_imbalance_coordinate
  deletion_test := powTwoJlog_not_quadratic_in_imbalance
  linearity_is_load_bearing := chart_not_forced_without_linearity
  state_event_splice := event_cost_differs_from_state_cost
  reduction_to_additivity := additive_continuous_balanced_is_imbalance

/-! ## Axiom audit -/

#print axioms vanishesAtBalanced_iff
#print axioms imbalance_is_the_unique_linear_selection
#print axioms vanishesOnBalancedLocus_iff
#print axioms imbalance_forced_by_balance_locus
#print axioms tolerated_family_is_a_scale_ray
#print axioms imbalanceTotalMap_det
#print axioms imbalance_total_is_a_canonical_pair
#print axioms Jlog_eq_two_sinh_half_sq
#print axioms orbitPoint_casimir
#print axioms orbitPoint_imbalance
#print axioms Jlog_eq_imbalance_sq_div_two_casimir
#print axioms chart_variable_is_the_normalized_imbalance
#print axioms chart_is_the_imbalance_coordinate
#print axioms sinh_two_arsinh
#print axioms powTwoJlog_not_quadratic_in_imbalance
#print axioms nlP_eq_zero_iff
#print axioms nlP_strictMono
#print axioms nlP_hasDerivAt
#print axioms nlQ_hasDerivAt_snd
#print axioms nl_jacobian_det_eq_one
#print axioms cost_not_quadratic_in_nlP
#print axioms chart_not_forced_without_linearity
#print axioms event_cost_differs_from_state_cost
#print axioms orbitPoint_is_reached_by_event
#print axioms additive_continuous_balanced_is_imbalance
#print axioms imbalance_is_additive_continuous_balanced
#print axioms chartStipulatedVerdict

end

end ChartFromLedgerMomentum
end SevenGaps
end Gravity
end IndisputableMonolith
