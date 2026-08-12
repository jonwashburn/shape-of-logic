import IndisputableMonolith.Gravity.SevenGaps.Gap2IncidenceSilenceVerdict

/-!
# Gap 2: insertion stationarity, the gluing law, and the bare-posting wall

## WORLD

**Exact goal.** Derive `Gap2GaugeVolume.GluingLaw`, hence the inverse-factorial
labeled weight and `GaugeCountingPrinciple`, from recognition-ledger structure;
or prove a scoped no-go naming the missing structure.

**Permitted premises.** The banked posting operation (`postAt` /
`LedgerPostingAdjacency.post`), its schedules and reachability, disjoint union
and the compiled label-interleaving arithmetic. No use of `mu`, `Aut`, the
answer at the atoms, or a renamed gauge-counting premise in the derivation.

**Judge.** Lean kernel, with the ordinary Mathlib base triple only. The live
`gap2_measure_derived` flag is immutable in this arc.

**Epistemic status before this module.** `GluingLaw` was proved sufficient and
satisfiable, but not derived from recognition structure. Mere relabeling
invariance ("label indifference") is refuted as a selector. Posting plus gluing
leaves character fugacities free. Charge-restriction routes are closed.

## Verdict

The positive conditional closes exactly: **insertion stationarity is equivalent
to the gluing law.** The needed recurrence is

    f (n+1) · (n+1) = f n,

with empty and singleton weights fixed to one. It uniquely forces `f n = 1/n!`,
and therefore gives `GluingLaw` and gauge counting.

The bare posting model does not derive that recurrence. Its elementary moves at
carrier size `n` are choices of one existing account and one of two sides, hence
`2n` moves. Label insertion has `n+1` slots. The counts already disagree at
`n = 2` (`4 ≠ 3`). More fundamentally, `postAt` preserves the carrier type;
it changes a ledger column and has no operation `Fin n → Fin (n+1)`.

This is a scoped no-go, not an impossibility theorem. It kills only derivations
from the present bare posting move set by equirated-move counting. The surviving
object is a **label-insertion kernel**: an operation that enlarges the carrier,
counts its `n+1` insertion slots, and proves stationarity of the weight under
that operation. No such object exists in the current ledger API.

Companion report:
`QG/attack_full_theory_20260729/A70_Gap2_Gluing_Law_Stationarity_20260804.html`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2GluingLawStationarity

open PathSumMeasure ExactShellGaugePreflight
open Gap2GaugeVolume Gap2GluingDerivation
open Gap2LatticeKindRule Gap2DynamicsKindRule FullTheoryLedger
open Analysis.RecognitionDualEntryEnrichment4D

noncomputable section

/-! ## §1. The exact stationarity condition -/

/-- The missing local law. `f` is the weight of one index set. The empty and
singleton carriers have unit weight, and adding one new label has `n+1`
interleaving slots. Stationarity balances the combined weight over those slots
against the old weight. This mentions neither `mu`, `Aut`, nor factorials. -/
structure InsertionStationarity (f : ℕ → ℝ) : Prop where
  unit : f 0 = 1
  atom : f 1 = 1
  insert : ∀ n : ℕ, f (n + 1) * (n + 1 : ℝ) = f n

/-- Insertion stationarity uniquely forces the inverse factorial. THEOREM. -/
theorem insertionStationarity_forces_inverse_factorial {f : ℕ → ℝ}
    (h : InsertionStationarity f) :
    ∀ n : ℕ, f n = 1 / (Nat.factorial n : ℝ) := by
  intro n
  induction n with
  | zero =>
      simpa using h.unit
  | succ k ih =>
      have hs := h.insert k
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hval : f (k + 1) = f k / ((k : ℝ) + 1) :=
        eq_div_of_mul_eq hk1.ne' hs
      rw [hval, ih, Nat.factorial_succ]
      push_cast
      field_simp

/-- The gluing law implies insertion stationarity by specializing shuffle to
an `n`-label carrier glued to one atom. THEOREM. -/
theorem gluingLaw_gives_insertionStationarity {f : ℕ → ℝ}
    (h : GluingLaw f) : InsertionStationarity f where
  unit := h.unit
  atom := h.atom
  insert := by
    intro n
    have hs := h.shuffle n 1
    rw [h.atom, mul_one, Nat.choose_succ_self_right] at hs
    simpa [Nat.cast_add, Nat.cast_one] using hs

/-- Insertion stationarity supplies the whole gluing law, not only the
one-label recurrence: uniqueness identifies `f` with inverse factorial, whose
full shuffle law is already kernel-proved. THEOREM. -/
theorem insertionStationarity_gives_gluingLaw {f : ℕ → ℝ}
    (h : InsertionStationarity f) : GluingLaw f := by
  have hf : f = fun n => 1 / (Nat.factorial n : ℝ) := by
    funext n
    exact insertionStationarity_forces_inverse_factorial h n
  rw [hf]
  exact inverseFactorial_gluingLaw

/-- Exact reduction: the gluing law and insertion stationarity are equivalent.
THEOREM. -/
theorem gluingLaw_iff_insertionStationarity {f : ℕ → ℝ} :
    GluingLaw f ↔ InsertionStationarity f :=
  ⟨gluingLaw_gives_insertionStationarity,
    insertionStationarity_gives_gluingLaw⟩

/-- The local stationarity law therefore discharges the gauge-counting
principle through the already-proved gluing bridge. THEOREM. -/
theorem insertionStationarity_gives_gaugeCounting (B : ℕ) {f : ℕ → ℝ}
    (h : InsertionStationarity f) :
    MeasureSubstrateBlocker.GaugeCountingPrinciple
      (classMass (B := B) (fun K => f K.nV * f K.nE * f K.nT)) :=
  gluingLaw_gives_gaugeCounting B (insertionStationarity_gives_gluingLaw h)

/-! ## §2. What the current move set actually counts -/

/-- A bare posting move chooses one existing account and one of the two ledger
sides. `Fin 2` is the finite form of `LedgerPostingAdjacency.Side`. -/
abbrev BarePostingMove (n : ℕ) := Fin n × Fin 2

/-- A label insertion into a linearized `n`-label carrier chooses one of its
`n+1` slots. This is the move count the stationarity recurrence needs. -/
abbrev LabelInsertionSlot (n : ℕ) := Fin (n + 1)

/-- The current posting move set has `2n` elementary choices. THEOREM. -/
theorem barePostingMove_card (n : ℕ) :
    Fintype.card (BarePostingMove n) = 2 * n := by
  simp [BarePostingMove, Nat.mul_comm]

/-- Label insertion has `n+1` slots. THEOREM. -/
theorem labelInsertionSlot_card (n : ℕ) :
    Fintype.card (LabelInsertionSlot n) = n + 1 := by
  simp [LabelInsertionSlot]

/-- Discriminating witness: at carrier size two, the bare posting degree is
four while label insertion needs three slots. Thus equirating the present
posting moves cannot produce the insertion factor. THEOREM. -/
theorem bare_posting_degree_not_insertion_degree_at_two :
    Fintype.card (BarePostingMove 2) ≠
      Fintype.card (LabelInsertionSlot 2) := by
  norm_num [barePostingMove_card, labelInsertionSlot_card]

/-- There is no universal identification of the bare posting move count with
the insertion-slot count. THEOREM. -/
theorem no_bare_posting_count_is_insertion_count :
    ¬ (∀ n : ℕ, Fintype.card (BarePostingMove n) =
      Fintype.card (LabelInsertionSlot n)) := by
  intro h
  exact bare_posting_degree_not_insertion_degree_at_two (h 2)

/-! ## §2b. The three-kind interleaving count is not a posting degree -/

/-- Bare atomic posting moves on the union of two three-kind index carriers.
The six sizes are exactly the arguments of `Gap2GluingDerivation.interleave`. -/
abbrev BareUnionPostingMove
    (a b c a' b' c' : ℕ) :=
  Fin (a + a' + (b + b') + (c + c')) × Fin 2

/-- The union's bare posting degree is twice its total number of existing
accounts. It is additive in the carrier sizes, not binomial. THEOREM. -/
theorem bareUnionPostingMove_card (a b c a' b' c' : ℕ) :
    Fintype.card (BareUnionPostingMove a b c a' b' c') =
      2 * (a + a' + (b + b') + (c + c')) := by
  simp [BareUnionPostingMove, Nat.mul_comm]

/-- Direct Door-2 discriminator. Gluing two one-vertex carriers has binomial
interleaving count two, while the current atomic posting degree on the union is
four. Thus the binomial on the shuffle identity is not the degree of the bare
posting graph. THEOREM. -/
theorem bare_union_posting_degree_not_interleave_two_vertices :
    Fintype.card (BareUnionPostingMove 1 0 0 1 0 0) ≠
      interleave 1 0 0 1 0 0 := by
  norm_num [bareUnionPostingMove_card, interleave]

/-- No universal equation identifies the present posting degree with the
three-kind gluing interleaving count. This rules out only that direct
equirated-move-count route. THEOREM. -/
theorem no_bare_posting_degree_supplies_interleave :
    ¬ (∀ a b c a' b' c' : ℕ,
      Fintype.card (BareUnionPostingMove a b c a' b' c') =
        interleave a b c a' b' c') := by
  intro h
  exact bare_union_posting_degree_not_interleave_two_vertices
    (h 1 0 0 1 0 0)

/-! ## §3. Underdetermination by the bare posting dynamics -/

/-- A weight attached to the current posting dynamics. The dynamics itself is
fixed by `postAt`; the only additional field is the size weight whose selection
is at issue. -/
structure PostingWeightedWorld where
  weight : ℕ → ℝ

/-- Reachability in a weighted world is exactly the existing bare posting
reachability; it cannot inspect the attached weight. -/
def WorldReachable {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (_w : PostingWeightedWorld)
    (L₁ L₂ : Recognition.Ledger (discreteCarrier Λ)) : Prop :=
  PostReachable L₁ L₂

/-- Any two attached weights are indistinguishable to every bare posting
reachability question. THEOREM. -/
theorem bare_posting_blind_to_weight
    (w₁ w₂ : PostingWeightedWorld)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (L₁ L₂ : Recognition.Ledger (discreteCarrier Λ)) :
    WorldReachable w₁ L₁ L₂ ↔ WorldReachable w₂ L₁ L₂ :=
  Iff.rfl

/-- The intended inverse-factorial world. -/
def factorialWorld : PostingWeightedWorld where
  weight := fun n => 1 / (Nat.factorial n : ℝ)

/-- A known-wrong constant-weight world with identical posting dynamics. -/
def constantWorld : PostingWeightedWorld where
  weight := fun _ => 1

/-- The intended world satisfies insertion stationarity. THEOREM. -/
theorem factorialWorld_stationary :
    InsertionStationarity factorialWorld.weight :=
  gluingLaw_gives_insertionStationarity inverseFactorial_gluingLaw

/-- The constant-weight decoy fails insertion stationarity at `n = 1`.
THEOREM. -/
theorem constantWorld_not_stationary :
    ¬ InsertionStationarity constantWorld.weight := by
  intro h
  have hs := h.insert 1
  norm_num [constantWorld] at hs

/-- **SCOPED NO-GO.** Two worlds share every bare posting reachability fact,
while one satisfies insertion stationarity and the other does not. Therefore
the current posting dynamics alone does not select the stationarity law. The
surviving route must add a carrier-enlarging label-insertion kernel. THEOREM. -/
theorem bare_posting_does_not_force_insertion_stationarity :
    InsertionStationarity factorialWorld.weight ∧
      ¬ InsertionStationarity constantWorld.weight ∧
      (∀ {Λ : Type} [Fintype Λ] [DecidableEq Λ]
        (L₁ L₂ : Recognition.Ledger (discreteCarrier Λ)),
        WorldReachable factorialWorld L₁ L₂ ↔
          WorldReachable constantWorld L₁ L₂) :=
  ⟨factorialWorld_stationary, constantWorld_not_stationary,
    fun L₁ L₂ => bare_posting_blind_to_weight factorialWorld constantWorld L₁ L₂⟩

/-! ## §4. Named missing object and immutable flag -/

/-- Combinatorial half of label insertion: for every slot, an embedding of the
old carrier that misses that slot and covers every other label. Weight-free. -/
structure LabelInsertionGeometry where
  enlarge : ∀ n : ℕ, LabelInsertionSlot n → Fin n ↪ Fin (n + 1)
  misses_inserted : ∀ (n : ℕ) (slot : LabelInsertionSlot n) (i : Fin n),
    enlarge n slot i ≠ slot
  covers_old : ∀ (n : ℕ) (slot : LabelInsertionSlot n)
    (j : Fin (n + 1)), j ≠ slot → ∃ i : Fin n, enlarge n slot i = j

/-- **THEOREM.** The standard order-preserving skip map (`Fin.succAboveEmb`)
inhabits the combinatorial half. So the missing Gap-2 object is not the
embedding arithmetic; it is a dynamics that forces stationarity on some weight. -/
def succAboveGeometry : LabelInsertionGeometry where
  enlarge := fun _ slot => Fin.succAboveEmb slot
  misses_inserted := fun _ slot i => Fin.succAbove_ne slot i
  covers_old := fun _n slot j hj =>
    (Fin.exists_succAbove_eq (x := j) (y := slot) hj : ∃ i : Fin _n, slot.succAbove i = j)

theorem succAboveGeometry_inhabited : Nonempty LabelInsertionGeometry :=
  ⟨succAboveGeometry⟩

/-- The exact structure missing from the current ledger API. Geometry plus a
weight that is stationary under the `n+1` insertions. The geometry half is
inhabited (`succAboveGeometry`); the stationarity half remains OPEN as a
recognition-dynamics derivation. -/
structure LabelInsertionKernel (f : ℕ → ℝ) where
  geometry : LabelInsertionGeometry
  unit : f 0 = 1
  atom : f 1 = 1
  stationarity : ∀ n : ℕ, f (n + 1) * (n + 1 : ℝ) = f n

/-- Package geometry with insertion stationarity into a kernel. -/
def LabelInsertionKernel.ofStationarity {f : ℕ → ℝ}
    (g : LabelInsertionGeometry) (h : InsertionStationarity f) :
    LabelInsertionKernel f :=
  ⟨g, h.unit, h.atom, h.insert⟩

/-- Inverse-factorial world plus `succAbove` geometry yields a kernel.
This does **not** derive stationarity from recognition; it shows the interface
is satisfiable once stationarity is granted. -/
def factorialSuccAboveKernel : LabelInsertionKernel factorialWorld.weight :=
  LabelInsertionKernel.ofStationarity succAboveGeometry factorialWorld_stationary

/-- A label-insertion kernel supplies insertion stationarity. THEOREM. -/
theorem labelInsertionKernel_gives_stationarity {f : ℕ → ℝ}
    (h : LabelInsertionKernel f) : InsertionStationarity f :=
  ⟨h.unit, h.atom, h.stationarity⟩

/-- A label-insertion kernel closes the gluing-law and gauge-counting debt.
THEOREM. -/
theorem labelInsertionKernel_gives_gaugeCounting (B : ℕ) {f : ℕ → ℝ}
    (h : LabelInsertionKernel f) :
    MeasureSubstrateBlocker.GaugeCountingPrinciple
      (classMass (B := B) (fun K => f K.nV * f K.nE * f K.nT)) :=
  insertionStationarity_gives_gaugeCounting B
    (labelInsertionKernel_gives_stationarity h)

/-- The live Gap-2 measure flag is not moved by this scoped no-go. THEOREM
(`rfl`). -/
theorem gap2_measure_derived_unmoved :
    fullTheoryBenchmarks.gap2_measure_derived = true :=
  rfl

/-! ## §5. Certificate -/

structure GluingLawStationarityCert : Prop where
  exact_reduction : ∀ {f : ℕ → ℝ},
    GluingLaw f ↔ InsertionStationarity f
  bare_move_count_wrong :
    ¬ (∀ n : ℕ, Fintype.card (BarePostingMove n) =
      Fintype.card (LabelInsertionSlot n))
  bare_interleaving_count_wrong :
    ¬ (∀ a b c a' b' c' : ℕ,
      Fintype.card (BareUnionPostingMove a b c a' b' c') =
        interleave a b c a' b' c')
  bare_dynamics_underdetermines :
    InsertionStationarity factorialWorld.weight ∧
      ¬ InsertionStationarity constantWorld.weight
  geometry_inhabited : Nonempty LabelInsertionGeometry
  missing_object_closes : ∀ (B : ℕ) {f : ℕ → ℝ},
    LabelInsertionKernel f →
      MeasureSubstrateBlocker.GaugeCountingPrinciple
        (classMass (B := B) (fun K => f K.nV * f K.nE * f K.nT))
  measure_flag_unmoved :
    fullTheoryBenchmarks.gap2_measure_derived = true

theorem gluingLawStationarityCert : GluingLawStationarityCert where
  exact_reduction := gluingLaw_iff_insertionStationarity
  bare_move_count_wrong := no_bare_posting_count_is_insertion_count
  bare_interleaving_count_wrong :=
    no_bare_posting_degree_supplies_interleave
  bare_dynamics_underdetermines :=
    ⟨factorialWorld_stationary, constantWorld_not_stationary⟩
  geometry_inhabited := succAboveGeometry_inhabited
  missing_object_closes := fun B {_} h =>
    labelInsertionKernel_gives_gaugeCounting B h
  measure_flag_unmoved := gap2_measure_derived_unmoved

end
end Gap2GluingLawStationarity
end SevenGaps
end Gravity
end IndisputableMonolith
