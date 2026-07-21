import IndisputableMonolith.Holography.CoefficientBridge
import IndisputableMonolith.Holography.PixelGluedPlaquette
import IndisputableMonolith.Foundation.RecognitionLedgerFloor

/-!
# RecognitionMultiplicity: the selector ENCODED as a T-1 ledger (rank-consistency check)

**RETAGGED (adversarial panel `holo_mult_fable_20260702`, judge Fable 5 over 6 directors
+ one debate round): CONDITIONAL on a modeling choice, NOT a derivation.** The earlier
headline ("the Bekenstein 1/4 selector, DERIVED from the ledger floor, FORCED conditional
on T-1") is retracted on proof-term evidence:

* `bekenstein_selector_derived` never references `recognitionMultiplicity` or `cellLedger`;
  its proof term closes `1 = closureRank` directly. The ledger construction is not
  load-bearing in the payoff theorem.
* `cellLedger` types ONE generator per face **by fiat**. A mirror `cellLedgerNullity`
  (three generators per face, one per free bit) is equally T-1-consistent, equally
  axiom-clean, equally additive, and yields its own "divergence witness" for the opposite
  branch. Bare T-1 underdetermines the ledger's shape, so the shape IS the selector,
  encoded rather than derived.

What survives (the theorems are all true and stay): this module is a **rank-consistency
check** — IF one posts one distinction per face (the rank reading of T-1), THEN the ledger
multiplicity provably tracks the closure rank and provably diverges from the nullity on
the domino. It rules the two readings mutually exclusive; it does not select between them.
The candidate non-circular selector argument is gluing-invariance/extensivity (rank stays
1 per face under gluing; nullity does not: 3 → 4 ≠ 6 on the domino), formalized in the
quad module `PixelQuadPlaquette` — see there for the live forcing argument.

Prior history: `T9CarrierBridge` proved the selector EQUIVALENT to an abstract
`T9CarrierUniversality` (a step-map surjectivity postulate) and showed T9 multiplicativity
alone does not force it. This module then re-encoded the selector at the T-1 ledger floor;
the `holo_mult_fable_20260702` audit found that encoding to be a modeling choice, not a
forcing. The tag chain is: postulate (`T9CarrierBridge`) → modeling choice (here) →
candidate consistency-forcing (quad extensivity, OPEN until landed).

## The three independent quantities (each computed by different machinery)

For a cell built of `k` D=3-forced unit faces (each a minimal closed recognition loop):

1. **`recognitionMultiplicity k`** — the recognition ledger cost
   (`Foundation.RecognitionLedgerFloor.ledgerCost`, unit weight) of the cell's defect
   ledger, one primitive posted double-entry distinction per face. This is grounded
   OUTSIDE holography in the T-1/T0 free ledger floor; it never mentions the closure map.
   `recognitionMultiplicity_eq : recognitionMultiplicity k = k`.

2. **rank** — `Nat.log2` of the cardinality of the *image* of the cell's local closure map
   (`k` independent GF(2) parity functionals). `k = 1`: `CoefficientBridge.closureRank = 1`
   (image `PixelLocal.closed`). `k = 2`: `dominoRank = 2` (image of the two-face map).

3. **nullity** — `Nat.log2` of the *kernel* cardinality (the free/undistinguished bits).
   `k = 1`: `CoefficientBridge.freeBits = 3`. `k = 2`: `dominoNullity = 4`.

## The result (theorems axiom-clean and true; their SCOPE is conditional)

* `multiplicity_eq_rank_one` / `multiplicity_eq_rank_two`: multiplicity = rank at `k ∈ {1,2}`.
  True, but the multiplicity side inherits `cellLedger`'s one-generator-per-face choice, so
  this is a consistency check of the rank reading, not an independent derivation of it.
* `multiplicity_ne_nullity_two`: `recognitionMultiplicity 2 = 2 ≠ 4 = dominoNullity`. Under
  the rank reading, multiplicity diverges from nullity: the two readings are mutually
  exclusive. (The mirror `cellLedgerNullity` construction produces the symmetric witness for
  the other branch, so this witness does not adjudicate between them.)
* `bekenstein_selector_derived`: `selector_multiplicity_is_closure_rank 1` holds. NOTE: the
  proof term closes `1 = closureRank` directly and does not consume the ledger construction;
  see the retag header. The name is kept for downstream stability
  (`RecordCostAsymmetry.bekenstein_selector_from_asymmetry` re-exports it).
* `coefficient_is_one_quarter_derived`: the pixel/sector ratio is `1/4` GIVEN the rank
  reading. CONDITIONAL on the `cellLedger` modeling choice.

## Honest scope (post-audit)

This is a **non-standard entropy assignment**, and we state it as such. Standard black-hole
microstate counting (Strominger-Vafa, LQG) sets `S = log(microstates)`, and here the
microstates ARE the nullity (3 free bits at one face), which would give `κ = 4/3`, NOT `1/4`.
RS reads entropy as attaching to the posted DISTINCTION (rank) because `ledgerCost` counts
performed distinctions. But the audit established that T-1 alone does not fix how many
distinctions a closed plaquette posts: `cellLedger`'s one-per-face is a CHOICE (the mirror
three-per-face ledger is equally consistent). So the `1/4` here is CONDITIONAL on that
choice. The open, non-circular route to forcing rank is the extensivity/gluing-invariance
argument (demanding an area law exist forces the extensive branch, and only rank is
extensive), which lives in the quad module — not here.
-/

namespace IndisputableMonolith
namespace Holography
namespace RecognitionMultiplicity

open PixelGluedPlaquette

/-! ## 1. Recognition multiplicity from the ledger floor (independent of any closure map) -/

/-- The **defect ledger of a `k`-face cell**: `k` distinct primitive posted distinctions,
one per D=3-forced unit face, each of multiplicity one. This is a MODELING CHOICE, not a
T-1 consequence (audit `holo_mult_fable_20260702`): T-1 says a closed recognition loop
posts distinctions but does not fix HOW MANY per face. One-per-face encodes the rank
reading; a mirror three-per-face ledger (one per free bit) would encode the nullity
reading and is equally T-1-consistent. The choice made here is what downstream theorems
are conditional on. It knows only the face count — nothing about the closure map. -/
noncomputable def cellLedger : ℕ → Foundation.RecognitionLedgerFloor.DefectLedger ℕ
  | 0 => 0
  | (k+1) => cellLedger k + Finsupp.single k 1

/-- The **recognition multiplicity** of a `k`-face cell: its recognition ledger cost under
unit weight (`Foundation.RecognitionLedgerFloor.ledgerCost`). By construction this is the
count of posted distinctions, grounded in the T-1/T0 floor, NOT the closure map's rank. -/
noncomputable def recognitionMultiplicity (k : ℕ) : ℝ :=
  Foundation.RecognitionLedgerFloor.ledgerCost (fun _ => (1 : ℝ)) (cellLedger k)

/-- **The ledger multiplicity is the face count `k`.** Proved from the free ledger floor
(`ledgerCost_add` + `ledgerCost_single`, i.e. `two_independent_same_defects` generalized),
with no reference whatsoever to the closure map. -/
theorem recognitionMultiplicity_eq (k : ℕ) : recognitionMultiplicity k = (k : ℝ) := by
  induction k with
  | zero => simp [recognitionMultiplicity, cellLedger]
  | succ n ih =>
      simp only [recognitionMultiplicity, cellLedger] at *
      rw [Foundation.RecognitionLedgerFloor.ledgerCost_add,
          Foundation.RecognitionLedgerFloor.ledgerCost_single, ih]
      push_cast
      ring

/-! ## 2. The two-face divergence witness: rank 2 ≠ nullity 4 (from the enumerated map) -/

/-- Left-face closure of the two-face domino (`0-1-4-3` even parity). -/
def dominoLeftClosed (c : DominoCfg) : Bool :=
  ! (vbit c 0 ^^ vbit c 1 ^^ vbit c 4 ^^ vbit c 3)

/-- Right-face closure of the two-face domino (`1-2-5-4` even parity). -/
def dominoRightClosed (c : DominoCfg) : Bool :=
  ! (vbit c 1 ^^ vbit c 2 ^^ vbit c 5 ^^ vbit c 4)

/-- The **local closure map** of the two-face domino: the pair of the two face parities.
Its image is all of `Bool × Bool` (the two constraints are independent), so its rank is 2. -/
def dominoLocalMap (c : DominoCfg) : Bool × Bool := (dominoLeftClosed c, dominoRightClosed c)

/-- **Rank of the two-face domino** = `Nat.log2` of the image cardinality of `dominoLocalMap`
(`|image| = 4 = 2²`, both parities independently achievable). Read off the actual map. -/
def dominoRank : ℕ := Nat.log2 (Finset.univ.image dominoLocalMap).card

/-- **Nullity of the two-face domino** = `Nat.log2` of the kernel cardinality (both faces
closed: `16 = 2⁴` configs), the free/undistinguished bits. -/
def dominoNullity : ℕ :=
  Nat.log2 (Finset.univ.filter (fun c => dominoLocalMap c = (true, true))).card

theorem dominoRank_eq_two : dominoRank = 2 := by decide

theorem dominoNullity_eq_four : dominoNullity = 4 := by decide

/-- **First-isomorphism check of the actual two-face map.** `|image| · |kernel| = |domain|`
(`4 · 16 = 64`), pinning rank 2 and nullity 4 without any hand-typed subtraction. -/
theorem domino_image_times_kernel :
    (Finset.univ.image dominoLocalMap).card
      * (Finset.univ.filter (fun c => dominoLocalMap c = (true, true))).card
      = (Finset.univ : Finset DominoCfg).card := by decide

/-! ## 3. The bridge: multiplicity = rank ≠ nullity -/

/-- **Bridge at one face (the selector's target).** The ledger multiplicity of one plaquette
equals the closure rank. Computed by two disjoint routes: `recognitionMultiplicity 1` from
the ledger floor, `CoefficientBridge.closureRank` from the image of `PixelLocal.closed`. -/
theorem multiplicity_eq_rank_one :
    recognitionMultiplicity 1 = (CoefficientBridge.closureRank : ℝ) := by
  rw [recognitionMultiplicity_eq, CoefficientBridge.closureRank_eq_one]

/-- **Bridge at two faces (the divergence witness).** `recognitionMultiplicity 2 = 2 = dominoRank`
— the ledger multiplicity tracks the rank even where rank and nullity have split apart. -/
theorem multiplicity_eq_rank_two :
    recognitionMultiplicity 2 = (dominoRank : ℝ) := by
  rw [recognitionMultiplicity_eq, dominoRank_eq_two]

/-- **The divergence witness — scoped.** `recognitionMultiplicity 2 = 2`, but the nullity is
`4`, so `2 ≠ 4`: UNDER the rank reading encoded in `cellLedger`, multiplicity diverges from
nullity, so the two readings are mutually exclusive. It does NOT rule out the `κ = 4/3`
branch on its own: the mirror `cellLedgerNullity` (three generators per face) yields the
symmetric witness `6 ≠ 2` for the other branch. What it does establish non-trivially: a
dependent gluing would have broken `multiplicity = rank` even under this reading. -/
theorem multiplicity_ne_nullity_two :
    recognitionMultiplicity 2 ≠ (dominoNullity : ℝ) := by
  rw [recognitionMultiplicity_eq, dominoNullity_eq_four]; norm_num

/-! ## 4. The payoff, retagged: the Bekenstein 1/4 selector, CONDITIONAL on the rank reading -/

/-- **CONDITIONAL (modeling choice): the Bekenstein selector.**
`selector_multiplicity_is_closure_rank 1` holds. AUDIT NOTE (`holo_mult_fable_20260702`):
the proof term below closes `1 = closureRank` directly and never consumes
`recognitionMultiplicity` or `cellLedger` — the ledger construction is not load-bearing
here, so this theorem does not DERIVE the selector from T-1; it instantiates the rank
reading. The name `_derived` is kept only for downstream stability
(`RecordCostAsymmetry` re-exports it). GAP 1's selector remains open pending the
extensivity/gluing-invariance forcing in the quad module. -/
theorem bekenstein_selector_derived :
    CoefficientBridge.selector_multiplicity_is_closure_rank 1 := by
  unfold CoefficientBridge.selector_multiplicity_is_closure_rank
  rw [CoefficientBridge.closureRank_eq_one]

/-- **CONDITIONAL (modeling choice): the Bekenstein-Hawking coefficient `1/4`.** The
pixel-to-sector ratio is exactly `1/4` GIVEN the rank reading of the selector. Conditional
on the `cellLedger` one-generator-per-face choice, NOT forced by T-1 alone (audit
`holo_mult_fable_20260702`). The name `_derived` is kept for downstream stability. -/
theorem coefficient_is_one_quarter_derived :
    (1 : ℚ) / (PixelLocal.admissibleSectors.card : ℚ) = 1 / 4 :=
  CoefficientBridge.bekenstein_of_selector 1 bekenstein_selector_derived

/-! ## 5. Bundled target + certificate handle for the holography loop -/

/-- **The consistency-check bundle** (retagged; see header). Multiplicity = rank at one and
two faces, multiplicity ≠ nullity at two faces (the scoped divergence witness), the selector
instantiated under the rank reading, and the conditional coefficient `1/4`. -/
def target_recognition_multiplicity : Prop :=
  recognitionMultiplicity 1 = (CoefficientBridge.closureRank : ℝ)
  ∧ recognitionMultiplicity 2 = (dominoRank : ℝ)
  ∧ recognitionMultiplicity 2 ≠ (dominoNullity : ℝ)
  ∧ (Finset.univ.image dominoLocalMap).card
      * (Finset.univ.filter (fun c => dominoLocalMap c = (true, true))).card
      = (Finset.univ : Finset DominoCfg).card
  ∧ CoefficientBridge.selector_multiplicity_is_closure_rank 1
  ∧ (1 : ℚ) / (PixelLocal.admissibleSectors.card : ℚ) = 1 / 4

theorem target_recognition_multiplicity_holds : target_recognition_multiplicity :=
  ⟨multiplicity_eq_rank_one, multiplicity_eq_rank_two, multiplicity_ne_nullity_two,
   domino_image_times_kernel, bekenstein_selector_derived, coefficient_is_one_quarter_derived⟩

/-- Verify-target certificate handle for the holography loop (`#print axioms`-gated). -/
theorem recognitionMultiplicityCert : target_recognition_multiplicity :=
  target_recognition_multiplicity_holds

end RecognitionMultiplicity
end Holography
end IndisputableMonolith
