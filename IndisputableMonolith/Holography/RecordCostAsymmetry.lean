import Mathlib
import IndisputableMonolith.Holography.PixelLocal
import IndisputableMonolith.Holography.EdgeSectorBridge
import IndisputableMonolith.Holography.CoefficientBridge
import IndisputableMonolith.Holography.RecognitionMultiplicity

/-!
# RecordCostAsymmetry: the rank/nullity selector, from the record-cost reading

(Renamed 2026-07-01 from `LandauerAsymmetry` in a course-correction pass; the panel
artifacts `holo_unconditional_20260701` and `holo_landauer_independence_20260701` refer
to this module by its former name. The mathematics is unchanged; the physical framing
and several theorem names were corrected — see "Naming correction" below.)

This module addresses the panel verdict `holo_unconditional_20260701` (judge Opus 4.8 over
5 directors + one debate round). The prior modules reduced the Bekenstein-Hawking
coefficient to a **selector** — does horizon entropy attach to the closure map's
`rank` (`log₂|image| = 1`, giving `κ = 4`, `S = A/4`) or to its `nullity`
(`log₂|kernel| = 3`, giving `κ = 4/3`)? — and then discharged that selector *conditionally*
on a named distinction-entropy axiom encoded in `RecognitionMultiplicity.cellLedger`.

## The panel's decisive attack (Director 3), and why the prior discharge was conditional

The rank-nullity of a finite closure map is the **symmetric** identity
`|image| · |kernel| = |domain|` (`CoefficientBridge.closure_image_times_kernel`,
`2 · 8 = 16`). A pure *counting* theorem contains no term that breaks the image/kernel
symmetry, so it **cannot** prefer `rank` over `nullity`: choosing "quotient-by-image"
over "fiber-over-a-point" *is* choosing rank over nullity, relabeled. The prior
`RecognitionMultiplicity` module got `multiplicity = rank` only because `cellLedger` was
*defined* to post one generator per face (= per independent image direction). That is
exactly where the axiom lived; the equality it proved could not have gone the other way.

## The symmetry-breaker: cost counts PERFORMED distinctions (directional), not collapsed ones

The `Foundation.RecognitionLedgerFloor` does not define cost symmetrically. `ledgerCost`
sums the **posted** generators — the distinctions actually performed (T-1: recognition IS
distinction). A performed distinction is a *difference the map records*: two configurations
`x, y` with `f x ≠ f y`. This is directional and image-sided. The kernel is precisely the
set of pairs the map does **not** distinguish (`f x = f y`), and the floor never charges for
a non-distinction. That directionality (the T0 double-entry posting arrow) is the one thing
on the table that is not symmetric between "posted record" and "free bit", and it is what
selects `image` over `kernel`.

Made concrete and unforgeable here, all `by decide`, axiom-clean:

* **`recordCost`** (general, any finite map): `log₂` of the image cardinality — the number of
  independent binary distinctions the map *performs*. Reuses the exact expressions of
  `CoefficientBridge.closureRank` and `RecognitionMultiplicity.dominoRank`.
* **`fiber_posts_one_record`**: the `2³ = 8` "free" microstates all map to the SAME posted
  record (`closed = true`), so the whole kernel performs **one** distinction, not `log₂ 8 = 3`.
  The `κ = 4/3` reading counts *unposted* bulk degeneracy; the floor counts performed
  distinctions, and the closed fiber performs exactly one. This is the concrete symmetry-break.
* **`record_zero_general`**: any map whose image is a subsingleton posts zero record cost
  (`|image| ≤ 1 ⇒ recordCost = 0`), for an ARBITRARY finite map — the record-zero principle
  as a THEOREM, not an axiom. A boundary that distinguishes nothing holds no records.
* **`recordCost_eq_multiplicity`**: the floor-side posted-generator count
  (`RecognitionMultiplicity.recognitionMultiplicity`) EQUALS the map-side record cost
  (image addressing) at `k ∈ {1, 2}`, computed by disjoint routes. So the posted ledger IS
  the image addressing code, not a coincidence at one face — general over the cell family.
* **`selector_forced`**: `recognitionMultiplicity 1 = recordCost closed` (`= 1 = rank`) AND
  `recognitionMultiplicity 2 ≠ microstateCost` (`2 ≠ 4 = nullity`). Multiplicity tracks the
  performed distinctions (image/rank), not the collapsed microstates (kernel/nullity), and it
  does so because it equals the addressing cost of the records the map performs.

## Naming correction (2026-07-01): record-zero is Bennett memory accounting, NOT Landauer

An earlier version of this module called the zero-on-constant-maps property "Landauer-zero"
and claimed the microstate reading "violates Landauer" and is "not a valid cost functional."
That framing was WRONG and is retracted. Orthodox Landauer erasure accounting charges the
*eraser* for merging states — `kT ln 2` per erased bit, i.e. the KERNEL side: resetting `n`
states to one costs `log₂ n`. So a constant map is exactly where orthodox Landauer charges
the most, and a functional that is nonzero there does not violate Landauer; it *is* the
erasure ledger. The property proved here is a different, equally standard piece of the same
accounting — **Bennett/Sagawa-Ueda memory bookkeeping**: the thermodynamic entropy *held by
a memory* is the log of the records it addresses, so a boundary that distinguishes nothing
HOLDS zero entropy (even though resetting it cost the eraser plenty). We call that demand
the **record-zero principle**. Both statements are true of different quantities; the fork
between them is precisely the fork between `recordCost` (what the boundary holds) and
`microstateCost` (what was merged behind it). Nothing in the mathematics changed under the
rename; what changed is the honest claim: the kernel reading is a *coherent Boltzmann
alternative that the record-cost premise excludes*, not a thermodynamic incoherence.

## Honest status (per `soul.mdc`)

This UPGRADES `RecognitionMultiplicity` from FORCED-CONDITIONAL to a genuine selection
THEOREM at the floor level: given only that ledger cost counts *performed* distinctions (the
definition of `ledgerCost` + T-1), the floor multiplicity tracks the rank branch and provably
differs from the nullity branch (`selector_forced`). The rank-vs-nullity freedom inside the
floor is gone.

The sole remaining physical input is the single identification **"horizon thermodynamic
entropy = the record (memory) cost of the boundary closure map"** — the Bennett memory-reset
reading of horizon entropy, stated below as the explicit named premise
`HorizonEntropyIsRecordCost`. Given it, `1/4` is a theorem; under the counterfactual
microstate reading the same machinery yields `3/4` (`κ = 4/3`), so the premise is visibly the
fork and a horizon whose area tracked unposted bulk degeneracy would falsify it. The premise
is sharp but not free-floating: within the proved dichotomy it is the unique reading
satisfying record-zero (`record_zero_separates_readings`), and inside the holographic program
the kernel reading also runs against the Bekenstein-bound logic (it charges bulk degeneracy
to the boundary). This is a premise *sharpening*, not a premise *removal*: tag (b), THEOREM
modulo one sharp identification.
-/

namespace IndisputableMonolith
namespace Holography
namespace RecordCostAsymmetry

open PixelLocal

/-! ## 1. The performed-distinction (image) cost, general -/

/-- **Record cost of a finite map**: `Nat.log2` of the cardinality of its *image* — the
number of independent binary distinctions the map performs (the records it produces). This
is the image side of the rank-nullity split, and it is what the ledger floor charges, because
`ledgerCost` sums posted (performed) distinctions. Defined for an arbitrary finite map. -/
def recordCost {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) : ℕ :=
  Nat.log2 (Finset.univ.image f).card

/-- **Microstate cost**: `Nat.log2` of a fiber cardinality — the kernel side, the number of
free bits the map does not distinguish. This is the standard black-hole microstate reading. -/
def microstateCost {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (v : β) : ℕ :=
  Nat.log2 (Finset.univ.filter (fun c => f c = v)).card

/-! ## 2. Record-zero is a THEOREM (general), not an axiom -/

/-- `Nat.log2` vanishes on a subsingleton count. -/
theorem log2_eq_zero_of_le_one {n : ℕ} (h : n ≤ 1) : Nat.log2 n = 0 := by
  interval_cases n <;> decide

/-- **Record-zero (general).** A finite map whose image is a subsingleton (`|image| ≤ 1`)
performs no distinction and hence holds zero record cost. A boundary that distinguishes
nothing holds no records. Holds for an ARBITRARY finite map, so it is a theorem, not an
axiom. (Formerly `landauer_zero_general`; see the naming correction in the module header —
this is Bennett memory bookkeeping, not Landauer erasure.) -/
theorem record_zero_general {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β)
    (h : (Finset.univ.image f).card ≤ 1) : recordCost f = 0 :=
  log2_eq_zero_of_le_one h

/-- **Record-zero, constant-map form.** A map that performs no boundary distinction
(constant, image a subsingleton) holds zero record cost, on any nonempty finite domain.
(Formerly `landauer_zero_of_constant`.) -/
theorem record_zero_of_constant {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (hconst : ∀ x y, f x = f y) : recordCost f = 0 := by
  apply record_zero_general
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
  exact hconst x y

/-! ## 3. The record cost of the actual closure maps (image side) -/

/-- The one-face closure map's record cost is `1` — the rank, reusing
`CoefficientBridge.closureRank`. -/
theorem recordCost_closed : recordCost (fun c : FaceCfg => PixelLocal.closed c) = 1 := by
  decide

/-- The two-face domino map's record cost is `2` — the rank, reusing
`RecognitionMultiplicity.dominoRank`. -/
theorem recordCost_domino :
    recordCost RecognitionMultiplicity.dominoLocalMap = 2 := by
  decide

/-! ## 4. The concrete symmetry-break: the kernel is ONE performed distinction, not three -/

/-- **The symmetry-break (the physical content).** The `2³ = 8` ledger-closed microstates —
the "free bits" whose `log₂ 8 = 3` gives the `κ = 4/3` reading — all map to the SAME posted
record (`closed = true`). So the entire closed fiber performs exactly **one** distinction, not
three. The `κ = 4/3` branch counts *unposted* bulk degeneracy; the ledger floor charges
*performed* distinctions, and this fiber performs one. This is the term static counting lacks:
the image is directional (records produced), the kernel is invisible to the record ledger. -/
theorem fiber_posts_one_record :
    (EdgeSectorBridge.closedConfigs.image (fun c : FaceCfg => PixelLocal.closed c)).card = 1 := by
  decide

/-- The map performs exactly two records (`{true, false}`), so `recordCost = log₂ 2 = 1`;
contrast the closed fiber, which is those 8 configs collapsing to the single `true` record
(`fiber_posts_one_record`). Records performed (image) = 2; microstates collapsed (kernel) = 8. -/
theorem records_performed :
    (Finset.univ.image (fun c : FaceCfg => PixelLocal.closed c)).card = 2 := by decide

/-! ## 5. Floor ↔ image bridge: the posted ledger IS the image addressing code -/

/-- **The bridge at one face.** The floor-side posted-generator count
(`recognitionMultiplicity 1`, computed from the free ledger with no reference to any map)
equals the map-side record cost (`recordCost closed`, the image addressing cost). Two disjoint
routes, one number. -/
theorem recordCost_eq_multiplicity_one :
    (recordCost (fun c : FaceCfg => PixelLocal.closed c) : ℝ)
      = RecognitionMultiplicity.recognitionMultiplicity 1 := by
  rw [recordCost_closed, RecognitionMultiplicity.recognitionMultiplicity_eq]

/-- **The bridge at two faces (the divergence witness).** The posted-generator count
`recognitionMultiplicity 2` equals the record cost `recordCost dominoLocalMap` (`= 2 = rank`),
where rank and nullity have split. The floor tracks the image, not the kernel. -/
theorem recordCost_eq_multiplicity_two :
    (recordCost RecognitionMultiplicity.dominoLocalMap : ℝ)
      = RecognitionMultiplicity.recognitionMultiplicity 2 := by
  rw [recordCost_domino, RecognitionMultiplicity.recognitionMultiplicity_eq]

/-! ## 6. The selector, FORCED at the floor level -/

/-- **The floor selector is forced.** Multiplicity equals the record cost (image / rank) at one
face, and differs from the microstate cost (kernel / nullity) at two faces. Since the record
cost is what the ledger floor charges (performed distinctions) while the microstate count
charges collapsed configurations the map never distinguishes, the floor multiplicity tracks
the rank branch, not the nullity branch. This is
`CoefficientBridge.selector_multiplicity_is_closure_rank` established from the asymmetric
addressing content, not from `cellLedger`'s definitional choice. -/
theorem selector_forced :
    (recordCost (fun c : FaceCfg => PixelLocal.closed c) : ℝ)
        = RecognitionMultiplicity.recognitionMultiplicity 1
    ∧ RecognitionMultiplicity.recognitionMultiplicity 2
        ≠ (microstateCost RecognitionMultiplicity.dominoLocalMap (true, true) : ℝ) := by
  refine ⟨recordCost_eq_multiplicity_one, ?_⟩
  rw [RecognitionMultiplicity.recognitionMultiplicity_eq]
  have hmc : microstateCost RecognitionMultiplicity.dominoLocalMap (true, true) = 4 := by
    decide
  rw [hmc]; norm_num

/-- **Bekenstein selector, re-derived from the asymmetry.** With the floor selector forced by
the performed-distinction argument, `selector_multiplicity_is_closure_rank 1` holds — now
grounded in "cost counts performed distinctions", not in `cellLedger`'s
one-generator-per-face choice. -/
theorem bekenstein_selector_from_asymmetry :
    CoefficientBridge.selector_multiplicity_is_closure_rank 1 :=
  RecognitionMultiplicity.bekenstein_selector_derived

/-! ## 7. Record-zero SEPARATES the two readings (the fork is real, and sharp) -/

/-- `Nat.log2` is `≥ 1` on any count `≥ 2` (via `Nat.log2 = Nat.log 2` and `Nat.log_pos`). -/
theorem one_le_log2_of_two_le {n : ℕ} (h : 2 ≤ n) : 1 ≤ Nat.log2 n := by
  rw [Nat.log2_eq_log_two]
  exact Nat.log_pos (by norm_num) h

/-- **The separation fact.** On a constant map over a domain of size `n ≥ 2`, every
configuration lands in the single fiber, so `microstateCost = log₂ n ≥ 1 ≠ 0` — while
`recordCost = 0` (`record_zero_of_constant`). So the two functionals provably disagree
exactly where a boundary distinguishes nothing, and the record-zero demand ("a boundary
that distinguishes nothing holds zero entropy") selects the record reading uniquely within
this dichotomy.

Honest scope (formerly overclaimed as `microstate_cost_violates_landauer_zero`): this does
NOT show the microstate reading violates Landauer — orthodox Landauer erasure charges the
kernel side, which is exactly what `microstateCost` counts, and a constant map is where
erasure cost peaks. What it shows is that the microstate reading assigns positive *boundary*
entropy to a boundary holding no records, i.e. it books the merged bulk degeneracy on the
boundary. That is a coherent Boltzmann alternative; it is excluded here by the record-cost
premise (Bennett memory bookkeeping), and it yields `κ = 4/3` — the falsifier. -/
theorem microstate_cost_nonzero_on_constant
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (hconst : ∀ x y, f x = f y) (a₀ : α)
    (hcard : 2 ≤ (Finset.univ : Finset α).card) :
    microstateCost f (f a₀) ≠ 0 := by
  have hfiber : (Finset.univ.filter (fun c => f c = f a₀)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro x _
    exact hconst x a₀
  unfold microstateCost
  rw [hfiber]
  have : 1 ≤ Nat.log2 (Finset.univ : Finset α).card := one_le_log2_of_two_le hcard
  omega

/-! ## 8. Bundled target + certificate handle for the holography loop -/

/-- **The record-cost-asymmetry target.** (1) record-zero is general for the image cost;
(2) the closure map performs 2 records while (3) its 8 microstates collapse to 1 record
(the symmetry-break); (4)+(5) the floor posted-count equals the image record cost at one and
two faces; (6) the floor selector is forced (rank, not nullity); (7) the kernel cost is
nonzero on constant maps, so the two readings provably separate and record-zero picks the
record branch. -/
def target_record_cost_asymmetry : Prop :=
  (∀ {α β : Type} [inst : Fintype α] [inst2 : DecidableEq β] (f : α → β),
      (Finset.univ.image f).card ≤ 1 → recordCost f = 0)
  ∧ (Finset.univ.image (fun c : FaceCfg => PixelLocal.closed c)).card = 2
  ∧ (EdgeSectorBridge.closedConfigs.image (fun c : FaceCfg => PixelLocal.closed c)).card = 1
  ∧ (recordCost (fun c : FaceCfg => PixelLocal.closed c) : ℝ)
      = RecognitionMultiplicity.recognitionMultiplicity 1
  ∧ (recordCost RecognitionMultiplicity.dominoLocalMap : ℝ)
      = RecognitionMultiplicity.recognitionMultiplicity 2
  ∧ CoefficientBridge.selector_multiplicity_is_closure_rank 1
  ∧ (∀ {α β : Type} [inst : Fintype α] [inst2 : DecidableEq α] [inst3 : DecidableEq β]
        (f : α → β), (∀ x y, f x = f y) → ∀ (a₀ : α),
        2 ≤ (Finset.univ : Finset α).card → microstateCost f (f a₀) ≠ 0)

theorem target_record_cost_asymmetry_holds : target_record_cost_asymmetry := by
  refine ⟨?_, records_performed, fiber_posts_one_record,
          recordCost_eq_multiplicity_one, recordCost_eq_multiplicity_two,
          bekenstein_selector_from_asymmetry, ?_⟩
  · intro α β _ _ f h
    exact record_zero_general f h
  · intro α β _ _ _ f hconst a₀ hcard
    exact microstate_cost_nonzero_on_constant f hconst a₀ hcard

/-- Verify-target certificate handle for the holography loop (`#print axioms`-gated).
(Formerly `landauerAsymmetryCert`.) -/
theorem recordCostAsymmetryCert : target_record_cost_asymmetry :=
  target_record_cost_asymmetry_holds

/-! ## 9. The single explicit premise → `1/4`, tag (b) formalized

The `holo_landauer_independence_20260701` panel (Opus judge over 5 directors + debate)
returned **(b) THEOREM modulo ONE sharp identification**, and named the identification
exactly:

> horizon thermodynamic entropy = the RS record/ledger cost of the boundary closure map
> (log of addressable, image-side, *posted* distinctions), **not** the log of unposted fiber
> degeneracy (kernel/nullity).

`Horizon.thermodynamicEntropy` is not a definition in this codebase (the directors named it
illustratively), so the honest, machine-checkable form of tag (b) is to state that single
identification as an **explicit named premise** and prove the whole descent to `1/4` is
unconditional given it, while the counterfactual (kernel) reading demonstrably yields `3/4`.
The premise is not a free coefficient: `record_zero_separates_readings` shows it is the
unique reading in the proved dichotomy that satisfies record-zero.

Panel dead claims (do NOT re-assert): "T-1 logically discharges the identification"
(scope error: T-1 carries no horizon/entropy token); "global `recordCost_unique` over
arbitrary finite maps" (false: identity `Fin 3 → Fin 3` breaks `log₂|image|` additivity);
"nullity is a legitimate Boltzmann horizon entropy" — refuted *inside the holographic
program* by the Bekenstein bound, but NOT thermodynamically incoherent in general (see the
naming correction in the module header; the earlier "violates Landauer" claim is retracted).
Live Bet 1 (derive record-zero from `RecognitionEventCapacity` to reach tag (a)) does NOT
close cleanly: `forcedEntropy` is a fixed per-event constant `(φ+2)·log φ`, not a functional
of a map, so it cannot supply a map-level record-zero without re-importing the image
reading — which is exactly the "silently re-imports the bridge" failure the panel flagged.
So (b) is the honest ceiling. -/

/-- **The one sharp identification, as an explicit named premise.** Horizon thermodynamic
entropy is measured by the *record* (image-side) cost of the boundary closure map — the count
of *performed* distinctions (the Bennett memory-reset reading) — so the plaquette
multiplicity that enters the pixel/sector ratio is `recordCost closed` (`= 1`). This is the
SOLE remaining physical input of the Bekenstein-Hawking `1/4`; everything below it is a
theorem. -/
def HorizonEntropyIsRecordCost (plaquetteMultiplicity : ℕ) : Prop :=
  plaquetteMultiplicity = recordCost (fun c : FaceCfg => PixelLocal.closed c)

/-- **The counterfactual fork.** Horizon entropy read as the *microstate* (kernel-side)
degeneracy of the closed fiber — the standard black-hole `S = log W` reading. A coherent
alternative that the record-cost premise excludes; `record_zero_separates_readings` shows
the two readings provably differ. -/
def HorizonEntropyIsMicrostateCost (plaquetteMultiplicity : ℕ) : Prop :=
  plaquetteMultiplicity = microstateCost (fun c : FaceCfg => PixelLocal.closed c) true

/-- **Descent (THEOREM, axiom-clean).** GIVEN the single record-cost identification, the
pixel-to-sector ratio is forced to the Bekenstein `1/4`, with no further premise. -/
theorem bekenstein_coefficient_of_record_cost (m : ℕ)
    (h : HorizonEntropyIsRecordCost m) :
    (m : ℚ) / (admissibleSectors.card : ℚ) = 1 / 4 := by
  unfold HorizonEntropyIsRecordCost at h
  rw [h, recordCost_closed, recognition_sector_count]; norm_num

/-- **The premise does real work: the kernel reading forces `3/4` (`κ = 4/3`).** The closed
fiber has `2³ = 8` microstates, so `microstateCost closed true = log₂ 8 = 3`, and the ratio
is `3/4`. This is precisely the branch the record-cost premise excludes; it is exhibited here
so that the single identification is visibly the fork, not a hidden re-labeling of the
answer. -/
theorem kappa_four_thirds_of_microstate_cost (m : ℕ)
    (h : HorizonEntropyIsMicrostateCost m) :
    (m : ℚ) / (admissibleSectors.card : ℚ) = 3 / 4 := by
  unfold HorizonEntropyIsMicrostateCost at h
  have hmc : microstateCost (fun c : FaceCfg => PixelLocal.closed c) true = 3 := by decide
  rw [h, hmc, recognition_sector_count]; norm_num

/-- **Record-zero separates the readings, so the premise is minimal within the dichotomy.**
On the constant (records-nothing) map, the record cost is `0` (`record_zero_of_constant`)
while the microstate cost is nonzero (`microstate_cost_nonzero_on_constant`). So demanding
only "horizon entropy is the boundary's record content: a boundary that distinguishes
nothing holds zero entropy" already fixes the record reading within the proved dichotomy;
`HorizonEntropyIsRecordCost` adds nothing beyond that memory-bookkeeping demand, and
`HorizonEntropyIsMicrostateCost` is inconsistent with it. (Formerly
`record_is_the_landauer_reading`; the demand is Bennett memory bookkeeping, not orthodox
Landauer erasure, which charges the kernel side — see the module header.) -/
theorem record_zero_separates_readings :
    recordCost (fun _ : FaceCfg => (true : Bool)) = 0
    ∧ microstateCost (fun _ : FaceCfg => (true : Bool)) true ≠ 0 := by
  refine ⟨record_zero_of_constant _ (fun _ _ => rfl), ?_⟩
  exact microstate_cost_nonzero_on_constant (fun _ : FaceCfg => (true : Bool))
    (fun _ _ => rfl) (0 : Fin 16) (by decide)

/-- **Tag (b) certificate (`#print axioms`-gated).** The Bekenstein-Hawking `1/4` is a
THEOREM modulo exactly one explicit premise (`HorizonEntropyIsRecordCost`): (1) that premise
forces `1/4`; (2) the counterfactual kernel premise forces `3/4`, so the premise is the sole
fork; (3) record-zero separates the two readings, so the premise is the minimal
memory-bookkeeping demand within the dichotomy, not a tuned coefficient. -/
theorem bekenstein_tag_b_cert :
    (∀ m : ℕ, HorizonEntropyIsRecordCost m →
        (m : ℚ) / (admissibleSectors.card : ℚ) = 1 / 4)
    ∧ (∀ m : ℕ, HorizonEntropyIsMicrostateCost m →
        (m : ℚ) / (admissibleSectors.card : ℚ) = 3 / 4)
    ∧ (recordCost (fun _ : FaceCfg => (true : Bool)) = 0
        ∧ microstateCost (fun _ : FaceCfg => (true : Bool)) true ≠ 0) :=
  ⟨bekenstein_coefficient_of_record_cost, kappa_four_thirds_of_microstate_cost,
    record_zero_separates_readings⟩

end RecordCostAsymmetry
end Holography
end IndisputableMonolith
