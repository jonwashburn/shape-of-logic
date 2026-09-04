import Mathlib
import IndisputableMonolith.Foundation.RecognitionKernel
import IndisputableMonolith.Foundation.KernelClosure.RowZeroReconciliation
import IndisputableMonolith.Foundation.KernelClosure.ProductCoefficientGauge
import IndisputableMonolith.Foundation.KernelClosure.CalibrationNecessaryReasons
import IndisputableMonolith.Foundation.KernelClosure.LadderNecessaryReasons
import IndisputableMonolith.Foundation.KernelClosure.LinkingDetectionNecessaryReasons
import IndisputableMonolith.Foundation.KernelClosure.FloorAndClock
import IndisputableMonolith.Foundation.KernelClosure.ClockFromCompletion
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow6Tick
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow4Hierarchy
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow3Calibration
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow2Cost
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow5Erasure
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow4Ladder
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow1Ratio
import IndisputableMonolith.Foundation.KernelClosure.CutsetRowContinuum
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow5Ledger
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow5RecogGeom
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow5PlanarMarker
import IndisputableMonolith.Foundation.KernelClosure.CutsetRowContinuumLedger
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow6Ledger
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow6Lossless
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow4Ledger
import IndisputableMonolith.Foundation.KernelClosure.CutsetRowA1Floor
import IndisputableMonolith.Foundation.KernelClosure.CutsetRowA2Join
import IndisputableMonolith.Foundation.KernelClosure.CutsetRowA2JoinCost
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow5Tower
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow5Threading
import IndisputableMonolith.Foundation.KernelClosure.CutsetOneWord

/-!
# The kernel purchase ledger

One terminal verdict per free premise of the Recognition Kernel, each inhabited
by a theorem from its census module, and the kernel restated over the surviving
qualitative premises.

## Verdicts

Every premise ends in exactly one of: `derived s` (proved from a strictly
lower stratum), `gauge` (content-free, with invariance theorem and consumer
audit), `purchase s cm` (irreducible at stratum `s`, countermodel `cm` named),
`statement` (the ambient fragment, which has no lower stratum), `openTarget`
(consistent, terminal named-axiom class, residual named), `model d` (closed by
a named definition `d`, with every consequence a theorem under it), `routed`
(an identification seam owned by another programme).

| premise | verdict | content theorem |
|---|---|---|
| product coefficient `2` | GAUGE; the ratio-dependence sub-sentence of the composition law is cross-floor unit freedom in other words (`scaleInvariant_iff_ratioDependent`, a merge, cutset 2026-09-02): the difference and Hamming-style costs fail it, `J` passes; on the reals the composition law is a theorem under floor readability (`compositionLaw_of_floorReadable`, continuum row) given the native ledger on counts | `ProductCoefficientGauge.productCoefficientGaugeCert_holds`, `Cutset.Row1Ratio.cert`, `Cutset.RowContinuum.cert` |
| calibration `= 1` | DERIVED at `traceClosure` from carrier-native + automorphism, one EXTERNAL theorem (six exponentials); cutset (2026-09-02): carrier-native is T2's "postings are counts" read on the cost value (blade = sentence, so a merge not a cut); on count exponents least count and reachability both select the unit with no import (`countRow`), so the import is bypassed by the count reading; under floor readability the real cost is calibrated with no import at all (`calibrated_of_floorReadable`, continuum row, MODEL) | `CalibrationCensus.calibration_derived_tagged`, `Cutset.Row3Calibration.cert`, `Cutset.RowContinuum.cert` |
| linking detection | DERIVED at `deltaOnly` (promoted 2026-09-03, `CutsetRow5Ledger`): the word "record" is gone. A ledger state is a pattern, a post is a bit flip, and a transition that posts no bit is no transition (`recognitionFree_iff_eq`, pattern extensionality). Read the kinematics into the ledger with its own hypothesis (deformation is recognition-free) and the `posted` clause (the posted pair and the split are distinct ledger states, i.e. space keeps the record of the act): DEP is a theorem (`dep_of_ledgerRealized`) and `D = 3` follows (`ledgerRealized_forces_D3`). The `D = 4` realization admits no such reading at all (`d4_not_ledgerRealized`, over every reading): its unlinking changes a ledger state without a post. Blade and sentence coincide (`ledgerRealized_iff_dep`); the earlier record blade was stronger than the floor requires (parity kinematics). What remains is the `posted` clause itself, and it is not forced by the ledger: a ledger may read every placement of the pair as one state and keep the record in its cells (`dep_not_forced_by_realization_layer`; desk round 2026-09-03). Said of space instead of the act it is RG2 of Recognition Geometry (`CutsetRow5RecogGeom`, 2026-09-03): the placements of two loops form a recognition geometry (some invariant recognizer tells two placements apart, `RecogGeom.Recognizer.nontrivial`) iff two motion classes exist (`recognitionGeometry_iff_two_classes`) iff `D = 3` (`recognitionGeometry_forces_D3`, `recognitionGeometry_at_three`); off three every invariant recognizer is constant (`invariantRecognizer_constant_off_three`), the cells-only ledger is a world with a ledger and no space. The identification "space = recognition geometry of trace placements" is MODEL (the theory's account of space), not a ledger theorem; the sentence names no dimension. Tower test (`CutsetRow5Tower`, 2026-09-03): position is a ledger fact (a lattice point is its floor patterns, the item at floor `k` is division by `2^k`, `addressD_iterate_apply`), every floor reader is moved by a carry (`floorReader_moves`), and a reader of positions that no unit step changes is constant (`invariant_reader_constant`); so no recognizer built from position is both motion-invariant and nontrivial (`no_invariant_positional_recognizer`), and placements read as positions are no recognition geometry in any dimension (`no_positional_geometry`). The tower neither supplies nor contradicts RG2 on placements: a record that survives motion is a record of how the traces sit, not where, and the ledger's reading of the act through such an invariant is the one sentence that remains. Arc 12 (design page S): `RecognitionGeometry` is existential over all functions of the placements, so the cells-only world satisfies it too; the kernel does not carry the difference between containing a reader and reading it. Arc 13 (`CutsetRow5Threading`) names the two traces in the tower: the pass below is the Gray cycle on the corners of one item, the pass above is the Gray cycle on items under the same rule, and the record is read when the pass above goes through the item. Decided facts: the cycle flips the belt axis on exactly the even steps and every corner has one belt edge (`flipAxis_spec`, `belt_even`, `one_belt_edge`); projected along the belt axis it goes once around the square (`belt_winds_once`); the pass above runs along the belt axis at every item it reads (`through_along_belt`); the reverse run completes the same item and is another run (`grayRev_surjective`, `grayRev_ne`), the address is blind to the difference, and the circulation is not (`circulation_gray = 4`, `circulation_grayRev = -4`, `circulation_bounce = 0`). Topological reading, documented: in three dimensions the pass above threads the belt of every item it reads (linking one); in four it threads nothing. The sentence is now: the floor above reads a completed recognition by threading it (a placement fact, three dimensions) rather than as an address (every dimension); equivalently, the record of a completion is signed (T4 entries) rather than an unsigned address (T1 cells), since the circulation is the only sign a closed balanced run has and threading is what reads it. In the tree's own words this is persistence (`RequirementFromLedgerClosure.PersistedPostedDistinction`, a genuine input: `persistence_not_forced`) with the carrier premise of `RegistrationIsCochain` (one substrate, every account on a region of it); the tower supplies the witness (the pass above is the account that reads the sign, in three dimensions), not the premise | `LinkingDetection.LinkingDetectionCensusCert_holds`, `Cutset.Row5Erasure.cert`, `Cutset.Row5Ledger.cert`, `Cutset.Row5RecogGeom.cert`, `Cutset.Row5Tower.cert`, `Cutset.Row5Threading.cert` |
| weight positivity | DERIVED from the realized hierarchy | `LadderCensus.weight_premises_reduce_to_hierarchy` |
| weight factorization | DERIVED from the realized hierarchy | same |
| self-similar step | DERIVED from the realized hierarchy | same |
| realized hierarchy | MODEL (closed 2026-09-02 by cutset): the two fields are two floor words with no numeral and no pairing. (4a) the floor step is one rule at every floor, `r (T s) = ρ * r s` for all states (`Similarity`); (4b) the tower is built by joins and closed under joins (`JoinBuilt`, T3 on the tower). Together they force `ρ = φ` (`similarity_ratio_eq_phi`), growth included, and inhabit `RealizedHierarchy` (`realizedHierarchy_of_blade`). Shape: 4b is a merge under uniformity (`joinBuilt_of_uniform_additive`: the pairing `(0,1)` was never a third premise); 4a is a cut across orbits (`twoOrbitFramework`: uniform and additive on the base orbit, ratio 3 on another) and uniformity in other words along one orbit. Nothing derives similarity from the framework axioms (`linearFramework` still fails it); `doublingFramework` is join-generated (`4 = 2 + 2`) but not join-closed (`1 + 2 = 3`); `boolFramework` has no floor above (B1); the address tower is uniform at 8 and not additive. Promoted 2026-09-03 (`CutsetRow4Ledger`): similarity is a theorem of one rule at every floor plus unit freedom (`similarity_of_covariant`); the linear ladder breaks unit freedom (`linear_not_covariant`), the two-orbit ladder breaks one rule (`twoOrbit_not_uniformRule`), the doubling ladder is the self-join and no independent join (`doubling_not_lagJoin_pos`, T3 independence), and least count picks the adjacent join over larger lags (`phi_not_lag_two`). Under similarity the adjacent join forces φ (`phi_of_similarity_adjacentJoin`) and join-built is derived (`joinBuilt_of_adjacentJoin`). Sharpened 2026-09-03 (`CutsetRowA2Join`): the ladder is not the address tower (ratio `2^D`, not additive, `towerCount_no_realized_hierarchy`), so this row is about cost. Among uniform two-part joins (`TwoPartJoin s a b`), equal parts (`a = b`) give `ρ^(b+1) = 2` (`equalLag_ratio`: doubling, `√2`, …) and φ is never such a ratio (`phi_not_equalLag`); distinct parts of least count are the adjacent join and force φ (`phi_of_least_distinct`). The one word left: the two parts of a level are *distinct* earlier levels. Two parts is T1, uniform lag is one rule, least count is T2; "distinct" is the word "hierarchy" itself. Relocated 2026-09-03 (`CutsetRowA2JoinCost`): the two parts of a join stand in a ratio with a recognition cost `J(part/part)`; equal parts have ratio one and join cost zero at every lag (`joinCost_equal_zero`, `J 1 = 0`), distinct parts have ratio `ρ^(b-a)` with `ρ > 1` (growth is derived from the join itself, `twoPartJoin_growth`) and positive join cost (`joinCost_distinct_pos`), so a join is costly iff its parts are distinct (`costly_iff_distinct`). The equal-part alternative is located inside the theory rather than excluded: the floor tower's scale ladder `2^F` is the lag-zero equal-part join with join cost zero (`tower_join_balanced`), the balanced cost-free ladder that space's floor step is. The word is now: a level's join is a recognition (its two sides are compared at a cost); "distinct" is a theorem of `J 1 = 0` under it | `LadderCensus.ladderCensusCert_holds`, `Cutset.Row4Hierarchy.cert`, `Cutset.Row4Ladder.cert`, `Cutset.Row4Ledger.cert`, `Cutset.RowA2Join.cert`, `Cutset.RowA2JoinCost.cert` |
| ambient theory T-2 | STATEMENT (one universe, empty inductive, functions, equality) | `FloorAndClock.t2Fragment_holds` |
| clock identification | MODEL (closed 2026-09-02): completion = occupying one item of the floor above; the clock is the finest recognizer of change, and the finest change is one bit (`finestStep_iff_oneBit`, least count), so "one post per tick" is derived; coverage derived (`passOccupiesItem_iff_surjective`); member of `SemanticClockLaw`; step rules excluded. Promoted 2026-09-03 (`CutsetRow6Ledger`): the stutter is impossible (a step that posts no bit is not a tick, `tick_iff_not_recognitionFree`); the jump is a coarsening, not a clock of its own (every tick of distance n is n posts, `exists_post_path`; the coarse clock forgets the order of posts, `two_bit_two_orders`, and needs a sampling rule the ledger never posted). Closed 2026-09-03 (`CutsetRow6Lossless`): the ledger is the *lossless* record of recognition events (the published definition of the ledger), and a clock is lossless iff it decodes to the post sequence (`lossless_recovers`, `lossless_of_recovers`); every sampling clock of rate `k ≥ 2` is lossy (`sample_not_lossless`: the two orders of a two-bit change have the same record at every rate). So "one post per tick" is a theorem of losslessness, with no identification left in it. Completion closed 2026-09-03 (`CutsetRowA1Floor`): the floor above is a ledger of the same kind (T1: two-sided cells, each reading one cell below by a coarsening); a cell with `n` states is two-sided iff `n = 2` (`cell_twoSided_iff`), and if every cell is read and the item's fiber is one floor of states then every factor is two (`fiber_pattern_iff`), so the item is the halving (`coarseAddress_two`) and "occupies an item" has no free factor. Decoys: no floor above (`m = 1`, the bounce and the face) and three-sided cells (`m = 3`) are not pattern spaces (`one_not_pattern`, `three_not_pattern`); the mixed floor `(4,2,1)` passes the count and fails cellwise (`mixed_count_passes`, `mixed_cellwise_fails`). Coverage is re-derived for every per-cell floor (`occupiesCoarseItem_iff_surjective`, `coverage_reached`). What remains of row 6 is only that a floor above exists, which is row 4's existence half | `FloorAndClock.FloorAndClockCert_holds`, `ClockFromCompletion.cert`, `Cutset.Row6Tick.cert`, `Cutset.Row6Ledger.cert`, `Cutset.Row6Lossless.cert`, `Cutset.RowA1Floor.cert` |

Routed, not restaged: closed-matter carriers (T10 box), the dark-energy dilution
law and its seed (Cosmology census), the pinned rung integers (mass programme).

The continuum (cutset row, 2026-09-02): MODEL. The native ledger pins the cost
at every count ratio with no continuity; the step to the line was the one
remaining purchase. The floor word "the cost of a ratio the floor does not post
is what its floors read" (`RowContinuum.FloorReadable`, the readings being the
octave tower's count ratios) carries the answer to the reals
(`eq_jcost_of_floorReadable`); continuity, the composition law on the reals,
monotone imbalance and calibration are theorems under it. The violator is the
classical wild solution `cosh (a (log x)) - 1`, `a` additive and not linear: it
satisfies the composition law on the whole line, equals `J` at every rational,
and fails the blade (`wildCost_compositionLaw`, `wildCost_not_floorReadable`).
No kernel sentence is PURCHASE. Row 5's definition (record) has since been
replaced by a floor theorem (`CutsetRow5Ledger`). For the continuum, the
alternative is not a distinct ledger object (`CutsetRowContinuumLedger`): the
floor has no continuum coordinates, every candidate cost either differs from `J`
at a count ratio (then it is not a structural native cost) or agrees with `J` at
every count ratio (then it is the same ledger object; the wild cost is of this
kind, `wild_indistinguishable_from_jcost`), and floor readability only selects
the presentation on the reals. Rows 4 and 6 were promoted the same day (`CutsetRow4Ledger`, `CutsetRow6Ledger`):
the linear, two-orbit and doubling ladders each break a floor fact (unit
freedom, one rule, T3 independence), the stutter is not a tick, and the coarse
clock is a sampling of the post sequence. The clock residual closed the same day
(`CutsetRow6Lossless`): the ledger is lossless, the only lossless clock is the
post sequence, every sampling is lossy. Arc 11 (2026-09-03) split what was
called one sentence into two objects and closed one of them. Row 6's completion
clause is closed (`CutsetRowA1Floor`): a floor above that is a ledger of the same
kind (T1 cells, every cell read) halves, so "completed = occupies one item" is
the halving with no free factor; what row 6 still rests on is that a floor above
exists, which is row 4's existence half. Row 4's sentence is about cost, not the
address tower (`CutsetRowA2Join`): every alternative join is now named (equal
parts give roots of two, never φ; larger lags fail least count), and the one
word left is that a level's two parts are *distinct* earlier levels; Arc 12
(`CutsetRowA2JoinCost`) relocates it: equal parts are a balanced join (cost
`J 1 = 0`, the tower's own scale ladder), distinct parts are a costly join, so
the word is that a level's join is a recognition. Row 5's
remaining sentence is that the placements of the ledger's traces are a space in
the theory's sense (RG2, `CutsetRow5RecogGeom`); the tower does not decide it
(`CutsetRow5Tower`: position readers are moved by carries, motion-invariant
readers of position are constant), so the record the placement keeps is a
motion invariant, and the identification is that the ledger reads the act
through one. Arc 12 (design page `plans/Kernel_Cutset_Arc12_Design_S_Space_20260903.txt`)
found that `RecognitionGeometry` is existential over all functions of the
configuration, so it holds in the cells-only world too: the difference between
"reads" and "contains" is not in the kernel, and no kernel theorem can force
the word without a finer definition of what the ledger reads. Two sentences
remain, both words of ordinary use said precisely: "a level's join is a
recognition" (its two sides are compared at a cost; distinct is then a theorem)
and "the ledger's pairing of the two traces is their placement pairing"; Arc 13
(`CutsetRow5Threading`) names the traces (the pass below and the pass above
through its item) and sharpens the second to: the record of a completion is
signed (its circulation, read by threading) rather than an unsigned address.

**The two sentences are one** (`CutsetOneWord`, 2026-09-03). Both are the
deformation-erasure principle, DEP: recognition-free deformation cannot carry a
completed recognition to its balanced configuration. The join is a kinematics
whose balanced configuration is ratio `1` (`J 1 = 0`) and whose realized one is
the join ratio; DEP for it is exactly "the parts are distinct"
(`hierarchy_word_iff_dep`). Persistence is DEP for the spatial pair, in both
directions (`persistence_iff_dep`). What separates the row that closed from the
row that did not is one property, rigidity (`dep_rigid_iff`): where no
configuration changes without a post (a ratio, whose change costs `J`; the
discrete tower, where every step posts a bit) DEP is bare distinctness and holds
whenever the two configurations differ, selecting nothing; where a motion can
post nothing (continuous isotopy of traces, the only relation through which
`D = 3` is forced) DEP is stability, distinctness does not give it
(`config_distinctness_does_not_force_dep`), and a complete realization refutes it
(`dep_not_forced_by_realization_layer`). So the kernel alone, being rigid, fixes
no dimension; the one sentence the kernel does not derive is DEP in a substrate
with free motion, and in that substrate it selects three. Read as a statement
about the ledger it is that the *pairing* of an act (which debit with which
credit) is posted content rather than bookkeeping: the kernel ledger
(`Recognition.Ledger`) posts column totals, which provably cannot carry it
(`registration_external`), so the pairing survives, if at all, in the placement
of the traces; that it survives is the sentence.

## The restated kernel

`RecognitionKernelV2` carries no numeral as an assumption. Its cost sector is
the composition law with an unknown product coefficient (the gauge), a
nondegeneracy clause in place of normalization, a monotone-imbalance clause in
place of continuity, and the two qualitative postulates of row 2 applied to
whatever exponent the cost turns out to have. Its linking sector is DEP on some
spatial realization. Its ladder sector is the realized hierarchy as a parameter,
with no weight fields at all: the weights are derived. `kernelV2_forces_spine`
recovers the recognition cost up to the amplitude gauge, `φ`, `D = 3`, the eight
ticks, and the forced measure, given the named external theorem.

`RecognitionKernel` stays in the tree, demoted to the historical statement with
numerals, exactly as `public_spine_dual` was kept beside its successor.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure

open Cost
open Cost.FunctionalEquation
open ClosedFramework
open HierarchyRealization
open MeasureForcing
open PrimitiveRecognitionCalculus
open PrimitiveRecognitionCalculus.PRCJCost
open LinkingNecessity

noncomputable section

/-! ## The verdict type and the premise index -/

/-- Terminal states of a premise row. -/
inductive Verdict
  | derived (s : StrengthTag)
  | gauge
  | purchase (s : StrengthTag) (countermodel : String)
  | statement
  | openTarget (terminalClass : String)
  | model (definition : String)
  | routed (owner : String) (closingTheorem : String)
  deriving Repr

/-- The premise rows: the six kernel fields, the hierarchy parameter, the two
rows outside the structure, and the three routed seams. -/
inductive Premise
  | productCoefficient
  | calibration
  | linkingDetection
  | weightPos
  | weightFactorizes
  | stepSelfSimilar
  | realizedHierarchy
  | ambientTheory
  | clockIdentification
  | matterCarriers
  | darkEnergyDilution
  | rungIntegers
  deriving DecidableEq, Repr

/-- The ledger. -/
def verdict : Premise → Verdict
  | .productCoefficient => .gauge
  | .calibration => .derived .traceClosure
  | .linkingDetection => .derived .deltaOnly
  | .weightPos => .derived .traceClosure
  | .weightFactorizes => .derived .traceClosure
  | .stepSelfSimilar => .derived .traceClosure
  | .realizedHierarchy =>
      .model "a level's join is a recognition: its two parts are compared at a cost; equal parts are balanced (J 1 = 0, the tower's own scale ladder, cost-free), distinct parts cost, so distinct is a theorem under the word; two parts is T1, one rule at every floor and unit freedom give similarity, least count picks the adjacent pair, the ratio is phi and join-closure follows"
  | .ambientTheory => .statement
  | .clockIdentification =>
      .model "a floor above exists (row 4's existence half); given it, the floor above is a ledger of the same kind and halves (T1 on its cells), so completion is occupying one item with no free factor; one post per tick is derived: the ledger is lossless, the only lossless clock is the post sequence, every sampling is lossy"
  | .matterCarriers => .routed "T10 box" "closed-matter carriers from raw stable patterns"
  | .darkEnergyDilution => .routed "Cosmology census" "OmegaLambdaInevitableReasons closure"
  | .rungIntegers => .routed "mass programme" "eighteen pinned integers, last named route"

/-! ## Row contents: what each verdict is inhabited by -/

/-- Row 4 through 6 content: the three weight members are exactly "the weight
is the hierarchy's weight". -/
def WeightsDerived : Prop :=
  ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F) (w : ℕ → ℝ),
    ((∀ n, 0 < w n) ∧ (∀ m n, w (m + n) = w m * w n) ∧ w 1 = 1 / (1 + w 1))
      ↔ w = LadderCensus.hierarchyWeight F H

/-- The content of each row, as a proposition. Routed rows carry `True` and
are not census rows; they are placeholders naming the owner. -/
def content : Premise → Prop
  | .productCoefficient =>
      ProductCoefficientGauge.ProductCoefficientGaugeCert ∧ Cutset.Row1Ratio.Cert
  | .calibration =>
      (TraceRationalExponent.SixExponentialsTraceInput →
        PublicSpine.Tagged StrengthTag.traceClosure
          (∀ c : ℝ, 0 < c → CalibrationCensus.CarrierNative (Cost.UnitForcedFromCarrier.gaugeCost c) →
            Cost.UnitForcedFromCarrier.CharacterIsAutomorphism c →
            IsCalibrated (Cost.UnitForcedFromCarrier.gaugeCost c))) ∧
        Cutset.Row3Calibration.Cert
  | .linkingDetection =>
      LinkingDetection.LinkingDetectionCensusCert ∧ Cutset.Row5Erasure.Cert ∧ Cutset.Row5Ledger.Cert ∧
        Cutset.Row5RecogGeom.Cert ∧ Cutset.Row5Tower.Cert ∧ Cutset.Row5PlanarMarker.Cert ∧
        Cutset.Row5Threading.Cert ∧ Cutset.OneWord.Cert
  | .weightPos => WeightsDerived
  | .weightFactorizes => WeightsDerived
  | .stepSelfSimilar => WeightsDerived
  | .realizedHierarchy =>
      IsEmpty (RealizedHierarchy HierarchyRealizationObstruction.boolFramework) ∧
        Nonempty (RealizedHierarchy LadderCensus.phiFramework) ∧
        LadderCensus.LadderCensusCert ∧ Cutset.Row4Hierarchy.Cert ∧ Cutset.Row4Ladder.Cert ∧
        Cutset.Row4Ledger.RowCert ∧ Cutset.RowA2Join.Cert ∧ Cutset.RowA2JoinCost.Cert
  | .ambientTheory => FloorAndClock.T2Fragment
  | .clockIdentification =>
      FloorAndClock.FloorAndClockCert ∧ ClockFromCompletion.Cert ∧ Cutset.Row6Tick.Cert ∧
        Cutset.Row6Ledger.RowCert ∧ Cutset.Row6Lossless.Cert ∧ Cutset.RowA1Floor.Cert
  | .matterCarriers => True
  | .darkEnergyDilution => True
  | .rungIntegers => True

theorem weightsDerived_holds : WeightsDerived :=
  LadderCensus.weight_premises_reduce_to_hierarchy

/-- **The two kernel cost fields, priced by cutset (2026-09-02).** They are
fields of `RecognitionKernelV2`, not ledger rows, so they carry no `Premise`.
`nondegenerate` is derived from T1's dichotomy read on ratios (`row2a`, a cut:
every gauge member passes the blade, the constants fail it). `monotone_imbalance`
splits: its "no reward" half is T1 nonnegativity (the cosine cost
`cos (log x) - 1` is a composition-law solution that rewards imbalance and is
killed by it), its regularity half is the continuum row below. -/
theorem kernelFields_cutset : Cutset.Row2Cost.Cert := Cutset.Row2Cost.cert

/-- **The continuum, closed by cutset (2026-09-02).** Given the native ledger on
count ratios, a floor-readable cost is `J` on the positives; the composition law
on the reals, monotone imbalance and calibration follow. The wild solution is
the planted negative: lawful on the line, `J` on every rational, not readable. -/
theorem continuum_cutset : Cutset.RowContinuum.Cert := Cutset.RowContinuum.cert

/-- **The continuum's alternative is not a distinct ledger object (2026-09-03).**
Every candidate cost is `J` at every count ratio or is not a structural native
cost; the wild cost is `J` to the ledger; floor readability selects one
presentation on the reals and `J` is it. -/
theorem continuum_ledger_status : Cutset.RowContinuumLedger.Cert :=
  Cutset.RowContinuumLedger.cert

/-- **Bundle theorem.** Every row's content holds. -/
theorem content_holds : ∀ p : Premise, content p
  | .productCoefficient =>
      ⟨ProductCoefficientGauge.productCoefficientGaugeCert_holds, Cutset.Row1Ratio.cert⟩
  | .calibration =>
      ⟨fun hsix => CalibrationCensus.calibration_derived_tagged hsix, Cutset.Row3Calibration.cert⟩
  | .linkingDetection =>
      ⟨LinkingDetection.LinkingDetectionCensusCert_holds, Cutset.Row5Erasure.cert, Cutset.Row5Ledger.cert,
        Cutset.Row5RecogGeom.cert, Cutset.Row5Tower.cert, Cutset.Row5PlanarMarker.cert,
        Cutset.Row5Threading.cert, Cutset.OneWord.cert⟩
  | .weightPos => weightsDerived_holds
  | .weightFactorizes => weightsDerived_holds
  | .stepSelfSimilar => weightsDerived_holds
  | .realizedHierarchy =>
      ⟨LadderCensus.boolFramework_no_realized_hierarchy, ⟨LadderCensus.phiHierarchy⟩,
        LadderCensus.ladderCensusCert_holds, Cutset.Row4Hierarchy.cert, Cutset.Row4Ladder.cert,
        Cutset.Row4Ledger.cert, Cutset.RowA2Join.cert, Cutset.RowA2JoinCost.cert⟩
  | .ambientTheory => FloorAndClock.t2Fragment_holds
  | .clockIdentification =>
      ⟨FloorAndClock.FloorAndClockCert_holds, ClockFromCompletion.cert, Cutset.Row6Tick.cert,
        Cutset.Row6Ledger.cert, Cutset.Row6Lossless.cert, Cutset.RowA1Floor.cert⟩
  | .matterCarriers => trivial
  | .darkEnergyDilution => trivial
  | .rungIntegers => trivial

/-- No census row is left without a terminal verdict, and no census row is
routed: routing is reserved for the three identification seams. -/
theorem census_rows_terminal :
    ∀ p : Premise,
      (∃ o t, verdict p = .routed o t) ↔
        (p = .matterCarriers ∨ p = .darkEnergyDilution ∨ p = .rungIntegers) := by
  intro p
  cases p <;> simp [verdict]

/-! ## The restated kernel -/

/-- **Recognition Kernel, restated.** No numeral is assumed. The cost is an
unknown `F` with an unknown product coefficient `κ`; the hierarchy is a
parameter (its price is on the ledger); the weights are absent because they
are derived. -/
structure RecognitionKernelV2
    (F : ℝ → ℝ) (κ : ℝ) (D : ℕ)
    (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr) : Prop where
  /-- The product coefficient is a positive unit choice (row 1: GAUGE). -/
  product_coefficient_pos : 0 < κ
  /-- The composition law with that coefficient. -/
  composition_law : KernelIndependence.SatisfiesCompositionLawGen κ F
  /-- The cost distinguishes some two ratios (replaces normalization). -/
  nondegenerate : ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ F x ≠ F y
  /-- A larger log-imbalance never costs less (replaces continuity). -/
  monotone_imbalance : MonotoneOn (Cost.FunctionalEquation.H F) (Set.Ici (0 : ℝ))
  /-- Row 2's two qualitative postulates, applied to whatever exponent the
  amplitude-normalized cost turns out to have. -/
  native_automorphism :
    ∀ c : ℝ, 0 < c →
      (∀ x : ℝ, 0 < x → amplitudeRescale (κ / 2) F x = costLambda c x) →
        CalibrationCensus.CarrierNative (Cost.UnitForcedFromCarrier.gaugeCost c) ∧
          Cost.UnitForcedFromCarrier.CharacterIsAutomorphism c
  /-- Row 3's priced premise: some spatial dual-pair realization in dimension
  `D` satisfies the deformation-erasure principle. -/
  deformation_erasure : ∃ R : SpatialDualPairRealization D, DeformationErasurePrinciple R.kin

/-- The spine the restated kernel delivers. -/
structure KernelSpineV2
    (F : ℝ → ℝ) (κ : ℝ) (D : ℕ)
    (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr) : Prop where
  t_minus2_distinction : NothingToDistinction.Nothing ≠ NothingToDistinction.Something
  /-- T5: the amplitude-normalized cost is the recognition cost. -/
  cost_is_jcost : ∀ x : ℝ, 0 < x → (κ / 2) * F x = Cost.Jcost x
  scale_is_phi : (HierarchyRealization.realized_to_ladder Fr H).ratio = PhiForcing.φ
  dimension_is_three : D = 3
  eight_tick : DimensionForcing.EightTickFromDimension D = 8
  /-- T9: the hierarchy's own weight is the forced measure. No weight premise. -/
  weight_is_forced : ∀ n : ℕ, LadderCensus.hierarchyWeight Fr H n = MeasureForcing.latticeWeight n

/-! ### Lemmas for the cost sector -/

theorem costLambda_neg (c x : ℝ) : costLambda (-c) x = costLambda c x := by
  simp only [costLambda, neg_neg]
  ring

theorem costLambda_zero (x : ℝ) (hx : 0 < x) : costLambda 0 x = 0 := by
  simp [costLambda, Real.rpow_zero]

/-- A nondegenerate composition-law solution is normalized: the only other
branch is the constant `-1`. -/
theorem normalized_of_nondegenerate (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F)
    (hnd : ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ F x ≠ F y) : IsNormalized F := by
  have h := hComp 1 1 (by norm_num) (by norm_num)
  have hquad : F 1 * (F 1 + 1) = 0 := by
    simp only [mul_one, div_one] at h
    nlinarith
  rcases mul_eq_zero.mp hquad with h0 | hneg
  · exact h0
  · exfalso
    have hF1 : F 1 = -1 := by linarith
    obtain ⟨x, y, hx, hy, hne⟩ := hnd
    have hconst : ∀ z : ℝ, 0 < z → F z = -1 := by
      intro z hz
      have hz1 := hComp z 1 hz (by norm_num)
      simp only [mul_one, div_one] at hz1
      rw [hF1] at hz1
      linarith
    exact hne ((hconst x hx).trans (hconst y hy).symm)

/-- Monotonicity of the log-profile survives positive amplitude rescaling. -/
theorem monotone_H_amplitudeRescale (a : ℝ) (ha : 0 < a) (F : ℝ → ℝ)
    (h : MonotoneOn (H F) (Set.Ici (0 : ℝ))) :
    MonotoneOn (H (amplitudeRescale a F)) (Set.Ici (0 : ℝ)) := by
  intro s hs t ht hst
  have := h hs ht hst
  simp only [H, G, amplitudeRescale] at this ⊢
  nlinarith

/-- **The restated kernel forces the spine**, given the one named external
theorem (six exponentials). The cost is recovered up to its amplitude gauge. -/
theorem kernelV2_forces_spine
    (hsix : TraceRationalExponent.SixExponentialsTraceInput)
    {F : ℝ → ℝ} {κ : ℝ} {D : ℕ}
    {Fr : ClosedObservableFramework} {H : RealizedHierarchy Fr}
    (K : RecognitionKernelV2 F κ D Fr H) :
    KernelSpineV2 F κ D Fr H where
  t_minus2_distinction := NothingToDistinction.nothing_ne_something
  cost_is_jcost := by
    set F' := amplitudeRescale (κ / 2) F with hF'
    have hκ2 : 0 < κ / 2 := by linarith [K.product_coefficient_pos]
    have hComp : SatisfiesCompositionLaw F' :=
      KernelIndependence.compositionGen_scaled κ F K.composition_law
    have hnd : ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ F' x ≠ F' y := by
      obtain ⟨x, y, hx, hy, hne⟩ := K.nondegenerate
      refine ⟨x, y, hx, hy, ?_⟩
      simp only [hF', amplitudeRescale]
      intro h
      exact hne (mul_left_cancel₀ hκ2.ne' h)
    have hNorm : IsNormalized F' := normalized_of_nondegenerate F' hComp hnd
    have hRecip : IsReciprocalCost F' := composition_law_forces_reciprocity F' hNorm hComp
    have hMono : MonotoneOn (Cost.FunctionalEquation.H F') (Set.Ici (0 : ℝ)) :=
      monotone_H_amplitudeRescale (κ / 2) hκ2 F K.monotone_imbalance
    obtain ⟨c, hc⟩ := composition_law_monotone_forces_costLambda F' hRecip hNorm hComp hMono
    -- the exponent is nonzero, and may be taken positive
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨x, y, hx, hy, hne⟩ := hnd
      exact hne (by rw [hc x hx, hc y hy, costLambda_zero x hx, costLambda_zero y hy])
    obtain ⟨c', hc'pos, hc'⟩ : ∃ c' : ℝ, 0 < c' ∧ ∀ x : ℝ, 0 < x → F' x = costLambda c' x := by
      rcases lt_or_gt_of_ne hc0 with hneg | hpos
      · exact ⟨-c, by linarith, fun x hx => by rw [hc x hx, costLambda_neg]⟩
      · exact ⟨c, hpos, hc⟩
    obtain ⟨hnat, haut⟩ := K.native_automorphism c' hc'pos hc'
    have hc1 : c' = 1 := (CalibrationCensus.calibration_derived hsix hc'pos hnat haut).1
    intro x hx
    have := hc' x hx
    simp only [hF', amplitudeRescale] at this
    rw [this, hc1, costLambda_one_eq_jcost x hx]
  scale_is_phi := HierarchyRealization.realized_hierarchy_forces_phi Fr H
  dimension_is_three := by
    obtain ⟨R, hR⟩ := K.deformation_erasure
    exact dep_forces_D3 D R hR
  eight_tick := by
    obtain ⟨R, hR⟩ := K.deformation_erasure
    rw [dep_forces_D3 D R hR]
    rfl
  weight_is_forced := fun n =>
    MeasureForcing.RecognitionWeightRule.weight_forced (LadderCensus.hierarchyWeightRule Fr H) n

/-! ### Anti-vacuity and the demotion -/

/-- The restated kernel is satisfiable: the recognition cost at the unit
amplitude, `D = 3` with the hierarchy's own realization, any realized
hierarchy. -/
theorem recognitionKernelV2_canonical
    (hsix : TraceRationalExponent.SixExponentialsTraceInput)
    (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr) :
    RecognitionKernelV2 Cost.Jcost 2 3 Fr H where
  product_coefficient_pos := by norm_num
  composition_law := by
    have h := CostUniqueness.Jcost_satisfies_composition_law
    intro x y hx hy
    have := h x y hx hy
    linarith
  nondegenerate := ⟨1, 2, by norm_num, by norm_num, by
    simp only [Cost.Jcost]; norm_num⟩
  monotone_imbalance := by
    intro s hs t ht hst
    simp only [Cost.FunctionalEquation.H, Cost.FunctionalEquation.G, Cost.Jcost]
    have hs0 : (0 : ℝ) ≤ s := hs
    have hes : Real.exp s + (Real.exp s)⁻¹ = 2 * Real.cosh s := by
      rw [Real.cosh_eq, Real.exp_neg]; ring
    have het : Real.exp t + (Real.exp t)⁻¹ = 2 * Real.cosh t := by
      rw [Real.cosh_eq, Real.exp_neg]; ring
    rw [hes, het]
    have : Real.cosh s ≤ Real.cosh t :=
      Real.cosh_le_cosh.mpr (by
        rw [abs_of_nonneg hs0, abs_of_nonneg (hs0.trans hst)]; exact hst)
    linarith
  native_automorphism := by
    intro c hc hF
    have h2 : (2 : ℝ) / 2 = 1 := by norm_num
    have hJ : ∀ x : ℝ, 0 < x → Cost.Jcost x = costLambda c x := by
      intro x hx
      have := hF x hx
      simp only [amplitudeRescale, h2, one_mul] at this
      exact this
    have hc1 : c = 1 := by
      have h1 := hJ 2 (by norm_num)
      rw [← costLambda_one_eq_jcost 2 (by norm_num)] at h1
      -- `costLambda 1 2 = costLambda c 2` with both exponents positive forces `c = 1`
      have hmono : ∀ a b : ℝ, 0 < a → 0 < b → costLambda a 2 = costLambda b 2 → a = b := by
        intro a b ha hb hab
        simp only [costLambda] at hab
        have h2a : (2 : ℝ) ^ (-a) = ((2 : ℝ) ^ a)⁻¹ := Real.rpow_neg (by norm_num) a
        have h2b : (2 : ℝ) ^ (-b) = ((2 : ℝ) ^ b)⁻¹ := Real.rpow_neg (by norm_num) b
        rw [h2a, h2b] at hab
        have hpa : (1 : ℝ) < (2 : ℝ) ^ a := Real.one_lt_rpow (by norm_num) ha
        have hpb : (1 : ℝ) < (2 : ℝ) ^ b := Real.one_lt_rpow (by norm_num) hb
        have hkey : (2 : ℝ) ^ a = (2 : ℝ) ^ b := by
          set u := (2 : ℝ) ^ a with hu
          set v := (2 : ℝ) ^ b with hv
          have hu0 : 0 < u := by linarith
          have hv0 : 0 < v := by linarith
          have : u + u⁻¹ = v + v⁻¹ := by linarith
          have h' : (u - v) * (u * v - 1) = 0 := by
            field_simp at this
            nlinarith [this]
          rcases mul_eq_zero.mp h' with h1 | h1
          · linarith
          · nlinarith
        have hlog : a * Real.log 2 = b * Real.log 2 := by
          rw [← Real.log_rpow (by norm_num : (0 : ℝ) < 2), ← Real.log_rpow (by norm_num : (0 : ℝ) < 2),
            hkey]
        have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        exact mul_right_cancel₀ hl2.ne' hlog
      exact (hmono 1 c one_pos hc h1).symm
    subst hc1
    refine ⟨?_, ?_⟩
    · have := CalibrationCensus.carrierNative_nat 1
      simpa using this
    · intro q hq
      exact ⟨q, hq, by simp⟩
  deformation_erasure := by
    obtain ⟨F0, H0⟩ := LinkingFromHierarchy.jRealizedHierarchy
    exact ⟨hierarchySpatialRealization F0 H0, hierarchy_realization_satisfies_dep F0 H0⟩

/-- **Demotion, not deletion.** Every historical kernel is a restated kernel at
the unit amplitude, provided its cost passes the two qualitative postulates on
its exponent and its linking detector comes with a DEP realization. The
converse direction is `kernelV2_forces_spine`. -/
theorem recognitionKernel_to_V2
    {F : ℝ → ℝ} {D : ℕ} {w : ℕ → ℝ}
    {Fr : ClosedObservableFramework} {H : RealizedHierarchy Fr}
    (K : RecognitionKernel F D w Fr H)
    (hdep : ∃ R : SpatialDualPairRealization D, DeformationErasurePrinciple R.kin) :
    RecognitionKernelV2 F 2 D Fr H where
  product_coefficient_pos := by norm_num
  composition_law := by
    intro x y hx hy
    have := K.composition_law x y hx hy
    linarith
  nondegenerate := by
    have hJ := composition_calibration_forces_jcost F K.composition_law K.calibration
    refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    rw [hJ 1 one_pos, hJ 2 (by norm_num)]
    simp only [Cost.Jcost]; norm_num
  monotone_imbalance := by
    have hJ := composition_calibration_forces_jcost F K.composition_law K.calibration
    intro s hs t ht hst
    simp only [Cost.FunctionalEquation.H, Cost.FunctionalEquation.G]
    rw [hJ _ (Real.exp_pos s), hJ _ (Real.exp_pos t)]
    simp only [Cost.Jcost]
    have hs0 : (0 : ℝ) ≤ s := hs
    have hes : Real.exp s + (Real.exp s)⁻¹ = 2 * Real.cosh s := by
      rw [Real.cosh_eq, Real.exp_neg]; ring
    have het : Real.exp t + (Real.exp t)⁻¹ = 2 * Real.cosh t := by
      rw [Real.cosh_eq, Real.exp_neg]; ring
    rw [hes, het]
    have : Real.cosh s ≤ Real.cosh t :=
      Real.cosh_le_cosh.mpr (by
        rw [abs_of_nonneg hs0, abs_of_nonneg (hs0.trans hst)]; exact hst)
    linarith
  native_automorphism := by
    have hJ := composition_calibration_forces_jcost F K.composition_law K.calibration
    intro c hc hF
    have h2 : (2 : ℝ) / 2 = 1 := by norm_num
    have hcal : IsCalibrated (costLambda c) := by
      have hG : G F = G (costLambda c) := by
        funext t
        have := hF (Real.exp t) (Real.exp_pos t)
        simp only [amplitudeRescale, h2, one_mul] at this
        simpa [G] using this
      have := K.calibration
      simp only [IsCalibrated] at this ⊢
      rw [← hG]; exact this
    have hc1 : c = 1 := by
      have := calibration_value_costLambda c
      simp only [IsCalibrated] at hcal
      rw [this] at hcal
      nlinarith [hcal, hc]
    subst hc1
    refine ⟨?_, ?_⟩
    · have := CalibrationCensus.carrierNative_nat 1
      simpa using this
    · intro q hq
      exact ⟨q, hq, by simp⟩
  deformation_erasure := hdep

/-! ## Certificate -/

structure KernelPurchaseLedgerCert : Prop where
  all_rows_hold : ∀ p : Premise, content p
  routed_only_seams :
    ∀ p : Premise,
      (∃ o t, verdict p = .routed o t) ↔
        (p = .matterCarriers ∨ p = .darkEnergyDilution ∨ p = .rungIntegers)
  v2_forces_spine :
    TraceRationalExponent.SixExponentialsTraceInput →
      ∀ {F : ℝ → ℝ} {κ : ℝ} {D : ℕ} {Fr : ClosedObservableFramework} {H : RealizedHierarchy Fr},
        RecognitionKernelV2 F κ D Fr H → KernelSpineV2 F κ D Fr H
  v2_satisfiable :
    TraceRationalExponent.SixExponentialsTraceInput →
      ∀ (Fr : ClosedObservableFramework) (H : RealizedHierarchy Fr),
        RecognitionKernelV2 Cost.Jcost 2 3 Fr H

theorem kernelPurchaseLedgerCert_holds : KernelPurchaseLedgerCert where
  all_rows_hold := content_holds
  routed_only_seams := census_rows_terminal
  v2_forces_spine := fun hsix _ _ _ _ _ K => kernelV2_forces_spine hsix K
  v2_satisfiable := recognitionKernelV2_canonical

end
end KernelClosure
end Foundation
end IndisputableMonolith
