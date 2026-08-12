import IndisputableMonolith.Gravity.SevenGaps.MeasureSubstrateBlocker
import IndisputableMonolith.Gravity.Analysis.RecognitionDualEntryEnrichment4D

/-!
# Wave C1 R5: gauge-counting measure from posted-history presentation

Implements the adjudicated Codex design for gap2 gauge counting from
history (`plans/QG_WaveC1_Gap2_Residual_DAG_Draft_20260722.txt` residual R5),
repaired post-critic (Wave C1 R5 REPAIR 2026-07-22).

## Core idea

A `PostedBoundedHistory` is a labeled bounded complex whose incidence indices
are posting-alphabet elements of a dual-entry ledger state. History
relabeling is posting-alphabet gauge redundancy. The class measure is defined
as

```
ν(c) = (# histories presenting c) / (history gauge volume of c)
```

and is proved to satisfy `GaugeCountingPrinciple` by explicit bijections with
the banked orbit/pair counts. Equality with `gaugeOrbitMass` is obtained ONLY
through `gaugeCountingPrinciple_iff_eq_gaugeOrbitMass` (never by defining `ν`
to be that mass).

## Honest scoping (design adjudication)

The dual-entry columns **anchor** the substrate reading (ledger-native
carrier: postings over a `DualEntryStrainState`). The **count** is driven by
the posting/relabel presentation degrees of freedom. Arbitrary dual-entry
state fields would inflate the history count and break the counting identity,
so counted histories **carry** the dual-entry state and pin it to the
canonical balanced zero state (`debit = credit = 0`, `mag = 0`) by a Prop
field. Dual-entry is therefore present-and-pinned, not erased.

## Non-circularity (honest boundary)

"Does not mention Aut/mu" is a meta-level property of the definitional layer.
The formal layer proves counting theorems for the **named** definition
`nuBuild`. Non-circularity is certified by the definition text of `nuBuild`
together with the paired `rfl` audit certificates:

* `nuBuild_def_history_only` — `nuBuild` is definitionally the history-count
  quotient;
* `circularNu_def_is_gaugeOrbitMass` — the circular decoy is definitionally
  `gaugeOrbitMass`.

There is no `∃`-package that formally discharges non-circularity; a reader
audits the named definition plus those two certificates. The discharge
headline is `gap2_gauge_counting_from_history_discharged`.

## Honesty / scope

* Does **not** flip `gap2_continuum_and_measure` or continuum Bools.
* Status Bools `pathSumMeasureStatus.substrate_measure_derived` and
  `gaugePreflightStatus.counting_principle_derived_from_ledger` are
  flipped in Wave C1 R6 (`Gap2MeasureStatusBinding`), bound to
  `gap2_gauge_counting_from_history_discharged` in the same commit.
* No `sorry`, `admit`, new axiom, or `native_decide`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace GaugeHistoryMeasure

open PathSumMeasure
open ExactShellGaugePreflight
open MeasureSubstrateBlocker
open Analysis.RecognitionDualEntryEnrichment4D

noncomputable section

variable {B : ℕ}

/-! ## §1. Posted histories (ledger-native carrier) -/

/-- Posting alphabet of a labeled complex: one letter per vertex, edge, and
tet index (avoids universe/counting inflation). -/
abbrev PostingAlphabet (K : BoundedComplex B) : Type :=
  Fin K.nV ⊕ Fin K.nE ⊕ Fin K.nT

/-- Canonical balanced zero dual-entry state (normalized counting substrate). -/
def balancedZeroState (Λ : Type*) : DualEntryStrainState Λ where
  debit := fun _ => 0
  credit := fun _ => 0
  mag := fun _ => 0
  mag_nonneg := fun _ => le_rfl
  flux_unit := fun _ => by
    simp only [sub_self, abs_zero]
    exact zero_le_one

/-- **Ledger-native history carrier.** A labeled bounded complex together with
a dual-entry strain state on its posting alphabet. Posting maps are the
canonical injections into `PostingAlphabet` (see `vertexPost` / `edgePost` /
`tetPost`). -/
structure PostedBoundedHistory (B : ℕ) where
  K : BoundedComplex B
  state : DualEntryStrainState (PostingAlphabet K)

namespace PostedBoundedHistory

variable {B : ℕ} (H : PostedBoundedHistory B)

/-- Vertex posting map (canonical left injection). -/
def vertexPost : Fin H.K.nV → PostingAlphabet H.K :=
  Sum.inl

/-- Edge posting map (canonical mid injection). -/
def edgePost : Fin H.K.nE → PostingAlphabet H.K :=
  fun e => Sum.inr (Sum.inl e)

/-- Tet posting map (canonical right injection). -/
def tetPost : Fin H.K.nT → PostingAlphabet H.K :=
  fun t => Sum.inr (Sum.inr t)

theorem vertexPost_injective : Function.Injective H.vertexPost :=
  Sum.inl_injective

theorem edgePost_injective : Function.Injective H.edgePost := by
  intro e₁ e₂ h
  exact Sum.inl_injective (Sum.inr_injective h)

theorem tetPost_injective : Function.Injective H.tetPost := by
  intro t₁ t₂ h
  exact Sum.inr_injective (Sum.inr_injective h)

end PostedBoundedHistory

/-- Canonical history presentation of a labeled complex: zero dual-entry state
and the complex's own incidence as the posting presentation. -/
def canonicalHistory (K : BoundedComplex B) : PostedBoundedHistory B where
  K := K
  state := balancedZeroState _

/-- State-canonical posted histories equal the canonical presentation. -/
theorem PostedBoundedHistory.eq_canonicalHistory
    (H : PostedBoundedHistory B)
    (h : H.state = balancedZeroState (PostingAlphabet H.K)) :
    H = canonicalHistory H.K := by
  cases H with | mk K state
  -- `subst` rejects the raw hypothesis: `state` occurs syntactically in
  -- `PostingAlphabet { K := K, state := state }.K` before reduction.
  change state = balancedZeroState (PostingAlphabet K) at h
  subst h
  rfl

/-! ## §2. Counted (normalized) histories — state-carrying -/

/-- **Counted history.** Carries the full posted carrier (complex + dual-entry
state) with state pinned to the canonical balanced zero. The state is present
in the counted type; canonicality is a Prop field, not an erasure. -/
structure CanonicalHistory (B : ℕ) where
  H : PostedBoundedHistory B
  state_canonical : H.state = balancedZeroState (PostingAlphabet H.K)

namespace CanonicalHistory

variable {B : ℕ}

/-- The posted carrier (state present). -/
abbrev toPosted (CH : CanonicalHistory B) : PostedBoundedHistory B := CH.H

/-- Underlying labeled complex. -/
def underlying (CH : CanonicalHistory B) : BoundedComplex B := CH.H.K

/-- Build the unique counted history presenting a labeled complex. -/
def ofComplex (K : BoundedComplex B) : CanonicalHistory B where
  H := canonicalHistory K
  state_canonical := rfl

@[ext] theorem ext {CH₁ CH₂ : CanonicalHistory B} (h : CH₁.H = CH₂.H) :
    CH₁ = CH₂ := by
  cases CH₁; cases CH₂; cases h; rfl

/-- Posted carrier of a counted history is the canonical presentation. -/
theorem toPosted_eq_canonicalHistory (CH : CanonicalHistory B) :
    CH.toPosted = canonicalHistory CH.underlying :=
  PostedBoundedHistory.eq_canonicalHistory CH.H CH.state_canonical

/-- Triangulation class presented by this history. -/
def classOf (CH : CanonicalHistory B) : TriangulationClass B :=
  Quotient.mk (relabelSetoid B) CH.underlying

/-- For each labeled complex, the state-canonicality fiber of counted
histories is a singleton (`Unique` is Type-valued, so this is a `def`). -/
noncomputable def fiber_unique (K : BoundedComplex B) :
    Unique {CH : CanonicalHistory B // CH.underlying = K} where
  default := ⟨ofComplex K, rfl⟩
  uniq := by
    intro ⟨CH, hK⟩
    apply Subtype.ext
    apply CanonicalHistory.ext
    -- `hK : CH.underlying = K` (after unfold); rewrite under `canonicalHistory`.
    calc
      CH.H = canonicalHistory CH.underlying := CH.toPosted_eq_canonicalHistory
      _ = canonicalHistory K := congrArg canonicalHistory hK
      _ = (ofComplex K).H := rfl

/-- Counted histories ↔ labeled complexes; the state-canonicality fiber
collapses by `toPosted_eq_canonicalHistory` / `fiber_unique`. -/
def equivUnderlying : CanonicalHistory B ≃ BoundedComplex B where
  toFun := underlying
  invFun := ofComplex
  left_inv := fun CH => by
    -- Need `ofComplex (underlying CH) = CH`. After `ext`, Lean asks for
    -- `(ofComplex _).H = CH.H`, i.e. the symmetric of `toPosted_eq_canonicalHistory`.
    refine CanonicalHistory.ext ?_
    change canonicalHistory CH.underlying = CH.H
    exact (CH.toPosted_eq_canonicalHistory).symm
  right_inv := fun _ => rfl

instance instFinite : Finite (CanonicalHistory B) :=
  Finite.of_equiv _ equivUnderlying.symm

@[simp] theorem classOf_ofComplex (K : BoundedComplex B) :
    (ofComplex K).classOf = Quotient.mk (relabelSetoid B) K :=
  rfl

@[simp] theorem toPosted_ofComplex (K : BoundedComplex B) :
    (ofComplex K).toPosted = canonicalHistory K :=
  rfl

@[simp] theorem underlying_ofComplex (K : BoundedComplex B) :
    (ofComplex K).underlying = K :=
  rfl

end CanonicalHistory

/-! ## §3. History relabeling (posting-level gauge redundancy) -/

/-- Alphabet transport induced by index bijections. -/
def postingAlphEquiv {K K' : BoundedComplex B}
    (vEquiv : Fin K.nV ≃ Fin K'.nV)
    (eEquiv : Fin K.nE ≃ Fin K'.nE)
    (tEquiv : Fin K.nT ≃ Fin K'.nT) :
    PostingAlphabet K ≃ PostingAlphabet K' :=
  Equiv.sumCongr vEquiv (Equiv.sumCongr eEquiv tEquiv)

/-- **History relabeling (posting-level).** Index bijections together with
incidence preservation (as in `Relabel`) AND posting-transport compatibility:
the alphabet transport induced by the index bijections must commute with the
canonical vertex/edge/tet posting maps. This is a genuinely different
structure from `Relabel`; agreement is a theorem, not a definition. -/
structure HistoryRelabel {B : ℕ} (H H' : PostedBoundedHistory B) where
  vEquiv : Fin H.K.nV ≃ Fin H'.K.nV
  eEquiv : Fin H.K.nE ≃ Fin H'.K.nE
  tEquiv : Fin H.K.nT ≃ Fin H'.K.nT
  edge_comm : ∀ e : Fin H.K.nE,
    H'.K.edgeVerts (eEquiv e) = Prod.map vEquiv vEquiv (H.K.edgeVerts e)
  tet_comm : ∀ (t : Fin H.K.nT) (i : Fin 4),
    H'.K.tetVerts (tEquiv t) i = vEquiv (H.K.tetVerts t i)
  vertexPost_comm : ∀ v : Fin H.K.nV,
    H'.vertexPost (vEquiv v) =
      postingAlphEquiv vEquiv eEquiv tEquiv (H.vertexPost v)
  edgePost_comm : ∀ e : Fin H.K.nE,
    H'.edgePost (eEquiv e) =
      postingAlphEquiv vEquiv eEquiv tEquiv (H.edgePost e)
  tetPost_comm : ∀ t : Fin H.K.nT,
    H'.tetPost (tEquiv t) =
      postingAlphEquiv vEquiv eEquiv tEquiv (H.tetPost t)

namespace HistoryRelabel

variable {B : ℕ} {H H' : PostedBoundedHistory B}

/-- Forget posting-transport fields to obtain a complex `Relabel`. -/
def toRelabel (r : HistoryRelabel H H') : Relabel H.K H'.K where
  vEquiv := r.vEquiv
  eEquiv := r.eEquiv
  tEquiv := r.tEquiv
  edge_comm := r.edge_comm
  tet_comm := r.tet_comm

/-- Transport a complex `Relabel` to a posting-level `HistoryRelabel` by
equipping the induced alphabet transport; posting-commutation holds by the
canonical definition of `vertexPost` / `edgePost` / `tetPost`. -/
def ofRelabel (r : Relabel H.K H'.K) : HistoryRelabel H H' where
  vEquiv := r.vEquiv
  eEquiv := r.eEquiv
  tEquiv := r.tEquiv
  edge_comm := r.edge_comm
  tet_comm := r.tet_comm
  vertexPost_comm := fun _ => rfl
  edgePost_comm := fun _ => rfl
  tetPost_comm := fun _ => rfl

/-- Extensionality: a history relabeling is determined by its index
bijections (commutation / posting fields are propositions). -/
@[ext] theorem ext {r s : HistoryRelabel H H'}
    (hv : r.vEquiv = s.vEquiv) (he : r.eEquiv = s.eEquiv)
    (ht : r.tEquiv = s.tEquiv) : r = s := by
  cases r; cases s
  cases hv; cases he; cases ht
  rfl

end HistoryRelabel

/-- Posting-level history relabeling is equivalent to complex relabeling.
Constructed (forget posting fields / equip induced alphabet transport);
not `Equiv.refl`, not definitional. -/
def historyRelabel_equiv_relabel (H H' : PostedBoundedHistory B) :
    HistoryRelabel H H' ≃ Relabel H.K H'.K where
  toFun := HistoryRelabel.toRelabel
  invFun := HistoryRelabel.ofRelabel
  left_inv := fun r => by
    apply HistoryRelabel.ext
    · rfl
    · rfl
    · rfl
  right_inv := fun r => by
    cases r
    rfl

/-- On canonical presentations, specialize the general equivalence. -/
def historyRelabel_equiv_relabel_canonical (K K' : BoundedComplex B) :
    HistoryRelabel (canonicalHistory K) (canonicalHistory K') ≃ Relabel K K' :=
  historyRelabel_equiv_relabel (canonicalHistory K) (canonicalHistory K')

instance instFiniteHistoryRelabel (H H' : PostedBoundedHistory B) :
    Finite (HistoryRelabel H H') :=
  Finite.of_equiv _ (historyRelabel_equiv_relabel H H').symm

/-! ## §4. History counting (definitional layer: no Aut / mu / banked mass) -/

/-- Number of counted histories presenting class `c`.
DEFINITION: history class cardinality only. -/
noncomputable def historyOrbitCardClass (c : TriangulationClass B) : ℕ :=
  Nat.card {H : CanonicalHistory B // H.classOf = c}

/-- History gauge volume of class `c`: pairs `(H, r)` with `H` presenting `c`
and `r` a history relabeling from the canonical presentation of `Quotient.out c`
to `H`. DEFINITION: history / HistoryRelabel cardinality only. -/
noncomputable def historyPairCountClass (c : TriangulationClass B) : ℕ :=
  Nat.card
    (Σ H : {H : CanonicalHistory B // H.classOf = c},
      HistoryRelabel (canonicalHistory (Quotient.out c)) H.val.toPosted)

/-- Trivial enrichment carrier (keeps the `Enrich → …` shape of `nuBuild`
without carrying Aut/mu data). -/
structure GaugeHistoryEnrichment : Type where
  mk ::

/-- **History-built class mass.** Labeled history copies per unit of history
gauge volume. DEFINITION mentions only `historyOrbitCardClass` and
`historyPairCountClass`. -/
noncomputable def nuBuild (_E : GaugeHistoryEnrichment) (B : ℕ)
    (c : TriangulationClass B) : ℝ :=
  (historyOrbitCardClass c : ℝ) / (historyPairCountClass c : ℝ)

/-- **History-only definitional certificate.** `nuBuild` is definitionally
the history-count quotient — not `gaugeOrbitMass`, not `1/|Aut|`. Paired with
`circularNu_def_is_gaugeOrbitMass` this is the mechanical non-circularity
audit surface. -/
theorem nuBuild_def_history_only :
    nuBuild =
      fun (_E : GaugeHistoryEnrichment) (B : ℕ) (c : TriangulationClass B) =>
        (historyOrbitCardClass c : ℝ) / (historyPairCountClass c : ℝ) :=
  rfl

/-! ## §5. Bridge layer (may mention banked orbit / pair counts) -/

/-- Counted histories of class `c` ↔ labeled complexes with class `c`.
Routes through the state-carrying counted type; the state-canonicality fiber
is collapsed by `CanonicalHistory.equivUnderlying` / `fiber_unique`. -/
def history_class_equiv_mk (c : TriangulationClass B) :
    {H : CanonicalHistory B // H.classOf = c} ≃
      {K : BoundedComplex B // Quotient.mk (relabelSetoid B) K = c} where
  toFun H := ⟨H.val.underlying, H.property⟩
  invFun K := ⟨CanonicalHistory.ofComplex K.val, K.property⟩
  left_inv := fun H => by
    apply Subtype.ext
    exact CanonicalHistory.equivUnderlying.left_inv H.val
  right_inv := fun _ => rfl

/-- Labeled complexes of class `c` ↔ the relabeling orbit of `Quotient.out c`
(banked pattern from `ExactShellGaugePreflight`). -/
def class_mk_equiv_orbit (c : TriangulationClass B) :
    {K : BoundedComplex B // Quotient.mk (relabelSetoid B) K = c} ≃
      {K' : BoundedComplex B // Equivalent (Quotient.out c) K'} := by
  have hc : Quotient.mk (relabelSetoid B) (Quotient.out c) = c :=
    Quotient.out_eq c
  exact Equiv.subtypeEquivRight fun K =>
    ⟨fun hK => Quotient.exact (hc.trans hK.symm),
     fun hE => by
       have h1 :
           Quotient.mk (relabelSetoid B) (Quotient.out c) =
             Quotient.mk (relabelSetoid B) K :=
         Quotient.sound hE
       exact h1.symm.trans hc⟩

/-- History class fiber ↔ banked gauge orbit of the out-representative. -/
def history_class_equiv_orbit (c : TriangulationClass B) :
    {H : CanonicalHistory B // H.classOf = c} ≃
      {K' : BoundedComplex B // Equivalent (Quotient.out c) K'} :=
  (history_class_equiv_mk c).trans (class_mk_equiv_orbit c)

theorem historyOrbitCardClass_eq_orbitCardClass (c : TriangulationClass B) :
    historyOrbitCardClass c = orbitCardClass c := by
  have hc : Quotient.mk (relabelSetoid B) (Quotient.out c) = c :=
    Quotient.out_eq c
  unfold historyOrbitCardClass
  rw [Nat.card_congr (history_class_equiv_orbit c)]
  have hcard :
      Nat.card {K' : BoundedComplex B // Equivalent (Quotient.out c) K'} =
        gaugeOrbitCard (Quotient.out c) :=
    rfl
  rw [hcard]
  conv_rhs => rw [← hc]
  rfl

/-- History-pair sigma ↔ banked pair sigma on the out-representative.
Uses the `historyRelabel_equiv_relabel` equivalence, not `Equiv.refl`.
`H.val.toPosted.K` is definitionally `H.val.underlying`, matching the
orbit representative produced by `history_class_equiv_orbit`. -/
def history_pair_equiv_pair (c : TriangulationClass B) :
    (Σ H : {H : CanonicalHistory B // H.classOf = c},
        HistoryRelabel (canonicalHistory (Quotient.out c)) H.val.toPosted) ≃
      (Σ K' : {K' : BoundedComplex B // Equivalent (Quotient.out c) K'},
        Relabel (Quotient.out c) K'.val) :=
  Equiv.sigmaCongr (history_class_equiv_orbit c) fun H =>
    historyRelabel_equiv_relabel
      (canonicalHistory (Quotient.out c)) H.val.toPosted

theorem historyPairCountClass_eq_pairCountClass (c : TriangulationClass B) :
    historyPairCountClass c = pairCountClass c := by
  have hc : Quotient.mk (relabelSetoid B) (Quotient.out c) = c :=
    Quotient.out_eq c
  unfold historyPairCountClass
  rw [Nat.card_congr (history_pair_equiv_pair c)]
  have hcard :
      Nat.card
          (Σ K' : {K' : BoundedComplex B // Equivalent (Quotient.out c) K'},
            Relabel (Quotient.out c) K'.val) =
        pairCount (Quotient.out c) :=
    rfl
  rw [hcard]
  conv_rhs => rw [← hc]
  rfl

theorem historyPairCountClass_pos (c : TriangulationClass B) :
    0 < historyPairCountClass c := by
  rw [historyPairCountClass_eq_pairCountClass]
  exact pairCountClass_pos c

/-! ## §6. Headlines -/

/-- **HEADLINE.** The history-built mass satisfies normalized gauge counting. -/
theorem nuBuild_gaugeCounting (E : GaugeHistoryEnrichment) (B : ℕ) :
    GaugeCountingPrinciple (nuBuild E B) := by
  intro c
  unfold nuBuild
  have hp : (pairCountClass c : ℝ) ≠ 0 := by
    exact_mod_cast (pairCountClass_pos c).ne'
  rw [historyOrbitCardClass_eq_orbitCardClass,
    historyPairCountClass_eq_pairCountClass, div_mul_cancel₀ _ hp]

/-- **HEADLINE.** History-built mass equals the banked gauge-orbit mass,
derived via the counting-principle uniqueness IFF — not by definitional
unfolding of `nuBuild` to `gaugeOrbitMass`. -/
theorem nuBuild_eq_gaugeOrbitMass (E : GaugeHistoryEnrichment) (B : ℕ) :
    nuBuild E B = gaugeOrbitMass :=
  (gaugeCountingPrinciple_iff_eq_gaugeOrbitMass (nuBuild E B)).mp
    (nuBuild_gaugeCounting E B)

/-! ## §7. Named-witness discharge (route (b); no fake ∃-package) -/

/-- **HEADLINE.** Gap2 gauge-counting from history, discharged for the named
builder `nuBuild`: counting principle + equality via uniqueness IFF.
Non-circularity is certified outside this Prop by the definition text of
`nuBuild` and the paired `rfl` certificates `nuBuild_def_history_only` /
`circularNu_def_is_gaugeOrbitMass`. -/
theorem gap2_gauge_counting_from_history_discharged :
    (∀ (E : GaugeHistoryEnrichment) (B : ℕ),
      GaugeCountingPrinciple (nuBuild E B)) ∧
    (∀ (E : GaugeHistoryEnrichment) (B : ℕ),
      nuBuild E B = gaugeOrbitMass) :=
  ⟨nuBuild_gaugeCounting, nuBuild_eq_gaugeOrbitMass⟩

/-- Compatibility Prop for downstream DAG wiring. States the named-witness
discharge; does **not** claim an `∃`-package discharges non-circularity. -/
def TypedResidual_gap2_gauge_counting_from_history : Prop :=
  (∀ (E : GaugeHistoryEnrichment) (B : ℕ),
    GaugeCountingPrinciple (nuBuild E B)) ∧
  (∀ (E : GaugeHistoryEnrichment) (B : ℕ),
    nuBuild E B = gaugeOrbitMass)

/-- **HEADLINE.** R5 closed by the named posted-history construction. -/
theorem typedResidual_gap2_gauge_counting_from_history_closed :
    TypedResidual_gap2_gauge_counting_from_history :=
  gap2_gauge_counting_from_history_discharged

theorem TypedResidual_gap2_gauge_counting_from_history_closed :
    TypedResidual_gap2_gauge_counting_from_history :=
  typedResidual_gap2_gauge_counting_from_history_closed

/-! ## §8. Decoys (paired `rfl` audit surface) -/

/-- **Circular decoy:** mass defined as the banked gauge-orbit mass.
Satisfies `GaugeCountingPrinciple`, but is definitionally the banked mass
(`circularNu_def_is_gaugeOrbitMass`), so it cannot supply the history-only
`rfl` certificate `nuBuild_def_history_only`. -/
def circularNu (_E : GaugeHistoryEnrichment) :
    ∀ B, TriangulationClass B → ℝ :=
  fun _B => gaugeOrbitMass

theorem circularNu_def_is_gaugeOrbitMass :
    circularNu =
      fun (_E : GaugeHistoryEnrichment) (_B : ℕ) =>
        (gaugeOrbitMass : TriangulationClass _ → ℝ) :=
  rfl

theorem circularNu_satisfies_gaugeCounting
    (E : GaugeHistoryEnrichment) (B : ℕ) :
    GaugeCountingPrinciple (circularNu E B) :=
  gaugeOrbitMass_satisfies

/-- Uniform class-mass decoy fails gauge counting (re-export). -/
theorem decoy_uniformClassMass_not_gaugeCounting (B : ℕ) (hB : 2 ≤ B) :
    ¬ GaugeCountingPrinciple
      (uniformClassMass : TriangulationClass B → ℝ) :=
  uniformClassMass_not_gaugeCounting B hB

/-- Audit package: paired `rfl` certificates distinguish `nuBuild` from
`circularNu`; counting holds for `nuBuild` and fails for uniform. -/
theorem gap2_history_measure_decoy_anchors (B : ℕ) (hB : 2 ≤ B) :
    (nuBuild =
        fun (_E : GaugeHistoryEnrichment) (B : ℕ) (c : TriangulationClass B) =>
          (historyOrbitCardClass c : ℝ) / (historyPairCountClass c : ℝ)) ∧
      (circularNu = fun _ _ => gaugeOrbitMass) ∧
      GaugeCountingPrinciple
        (circularNu GaugeHistoryEnrichment.mk B) ∧
      ¬ GaugeCountingPrinciple
        (uniformClassMass : TriangulationClass B → ℝ) ∧
      GaugeCountingPrinciple
        (nuBuild GaugeHistoryEnrichment.mk B) ∧
      nuBuild GaugeHistoryEnrichment.mk B = gaugeOrbitMass :=
  ⟨nuBuild_def_history_only, circularNu_def_is_gaugeOrbitMass,
    circularNu_satisfies_gaugeCounting _ B,
    decoy_uniformClassMass_not_gaugeCounting B hB,
    nuBuild_gaugeCounting _ B, nuBuild_eq_gaugeOrbitMass _ B⟩

end

end GaugeHistoryMeasure
end SevenGaps
end Gravity
end IndisputableMonolith
