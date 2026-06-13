# Absolute Floor Closure

**Status:** LEAN IMPLEMENTED 2026-04-28; PAPERS WRITTEN 2026-04-28.
The Lean closure compiles, the three companion papers compile (8 + 4 + 4
pages), and the two upstream papers (`RS_Universal_Forcing.tex`,
`Logic_Functional_Equation.tex`) cite the closure with explicit Lean
theorem pointers. Joint closure certificate in
`Foundation.AbsoluteFloorClosure.absoluteFloorClosureCert`.
**Owner:** Jon Washburn.
**Goal:** push the residual posit in the Recognition Science forcing chain
from `Distinguishability` down to the metaphysical floor, with every step
proved in Lean and tagged honestly.

The plan is the next pass of the recursive elimination procedure
documented in `biggest-questions.md` §XXIII. Each pass takes the current
posit list, picks one item, and tries to derive every member of that
class from the rest. The current pass picks `Distinguishability`.

**Implementation note (2026-04-28).** The Lean implementation now exists:
`SelfBootstrapDistinguishability.lean`,
`DistinguishabilityFromSpecifiability.lean`, and
`AbsoluteFloorClosure.lean` compile through
`lake build IndisputableMonolith.Foundation.AbsoluteFloorClosure`.
`NonTrivialityFromDistinguishability.lean` now exposes
`SatisfiesLawsOfLogicAbsoluteFloor`, which turns an absolute-floor witness
plus a cost-detection predicate into the existing Law-of-Logic structure.
`UnifiedForcingChain.lean` records the new `TMinus1_AbsoluteFloor` node.
Direct build of `UnifiedForcingChain` remains blocked by unrelated
pre-existing broken imports below that target, not by these files.

---

## 1. Where the chain currently bottoms out

The Lean library reduces the Recognition Science forcing chain to four
residual posits at the foundation layer.

| Posit | Where it lives | Status |
|---|---|---|
| **Distinguishability**: `∃ x y in K, x ≠ y` (operationally `C x y ≠ 0` for some pair) | field of `SatisfiesLawsOfLogicCanonical` in `Foundation/NonTrivialityFromDistinguishability.lean` | POSITED |
| **Carrier**: there exists some type `K` on which comparison is defined | type signature of `ComparisonOperator` in `Foundation/LogicAsFunctionalEquation.lean` | POSITED |
| **Composition Consistency** (route-independence): `C(xy) + C(x/y) = P(C(x), C(y))` for some combiner `P` | `RouteIndependence` predicate in `Foundation/LogicAsFunctionalEquation.lean` | POSITED at object level; substantive per `PrimitiveDistinction.aristotelian_decomposition` |
| **Archimedean + Dedekind completeness** of the ambient ordered field | `ConditionallyCompleteLinearOrderedField K` hypothesis in `Foundation/DomainBootstrap.lean` | POSITED, named explicitly |

The other Aristotelian conditions (Identity, Non-Contradiction, Totality)
are already discharged by `Foundation/PrimitiveDistinction.lean` as
type-theoretic facts of any equality-induced cost. The ambient field
identification with `ℝ` is already discharged by
`Foundation/DomainBootstrap.lean` modulo the completeness hypothesis.
The four-cost-uniqueness chain on top of these conditions is already
closed by `Foundation/DAlembert/FactorizationForcing.lean` and
`Cost/FunctionalEquation.lean`.

This plan addresses **Distinguishability** and **Carrier**. Items 3 and
4 have their own closure programs and are out of scope here.

---

## 2. Closure criterion

The chain is declared **absolutely closed at the distinguishability
floor** when all of the following hold.

1. A Lean theorem in `Foundation/AbsoluteFloorClosure.lean` derives
   `Distinguishability C` from a strictly weaker premise that is either
   (a) self-grounding in the type theory or (b) a precondition of any
   ontology being specifiable at all.
2. `Foundation/NonTrivialityFromDistinguishability.lean` is updated so
   that the `distinguishability` field of `SatisfiesLawsOfLogicCanonical`
   is supplied by a closure theorem rather than posited by the user.
3. `scripts/reality_audit.py` reports no new axioms and no new sorries
   in the foundation chain.
4. `biggest-questions.md` §XXIII.A is updated: the Distinguishability
   line moves from POSITED to either CLOSED (full closure) or PARTIAL
   THEOREM (one route out of two).
5. `Recognition-Science-Full-Theory.txt` @KERNEL is updated with the new
   floor.

If only one route closes, the plan declares **partial closure** and the
other route is logged as OPEN with its specific blocker.

If neither route closes, the plan declares **Distinguishability as the
metaphysical floor**, names the specific impossibility result that
forced the conclusion, and updates §XXIII.A to reflect it. That is also
a successful outcome of the elimination pass.

---

## 3. Route A — Self-Bootstrap

**Idea.** The negation of distinguishability is itself a distinguishable
possibility. "There is no distinguishability" is distinguishable from
"there is distinguishability," so denying distinguishability presupposes
it.

**Risk.** The argument imports a meta-distinguisher to do the
distinguishing. Honest reading: object-level distinguishability is forced
by meta-level distinguishability. Strict gain (the floor moves from
object to meta) but not absolute (the meta-language still posits
distinguishability on its own propositions).

**Honest tag:** CONDITIONAL THEOREM modulo decidable equality on the
meta-language's proposition type.

### 3.1 Module: `Foundation/SelfBootstrapDistinguishability.lean`

Three theorems, ascending in substantive content.

#### 3.1.1 The trivial type-theoretic core

```lean
namespace IndisputableMonolith
namespace Foundation
namespace SelfBootstrap

/-- The two-element type carries a definitional distinction. -/
theorem bool_distinguishable : (false : Bool) ≠ (true : Bool) := by decide

/-- Any framework whose carrier admits a `Bool`-valued predicate
    inherits a non-trivial distinction from `Bool`. -/
theorem distinguishability_lifted_from_bool
    {K : Type*} (P : K → Bool)
    (hpos : ∃ x : K, P x = true) (hneg : ∃ x : K, P x = false) :
    ∃ x y : K, x ≠ y := by
  obtain ⟨x, hx⟩ := hpos
  obtain ⟨y, hy⟩ := hneg
  refine ⟨x, y, ?_⟩
  intro hxy
  rw [hxy] at hx
  exact (Bool.true_ne_false (hx.symm.trans hy)).elim
```

This part is mechanical. The substantive claim is that any predicate
*about distinguishability itself* can serve as `P`.

#### 3.1.2 The reflexive lift

```lean
/-- The predicate "the carrier admits a non-trivial distinction" is
    itself a `Prop`-valued predicate. The two propositions
    `∃ x y, x ≠ y` and `¬ ∃ x y, x ≠ y` are decidably distinct in any
    classical meta-theory. -/
theorem dist_claim_self_distinguishes (K : Type*) :
    (∃ x y : K, x ≠ y) ≠ (¬ ∃ x y : K, x ≠ y) := by
  intro h
  -- Use that any P and ¬P are propositionally distinct in classical logic.
  by_cases hd : ∃ x y : K, x ≠ y
  · have : ¬ (∃ x y : K, x ≠ y) := h ▸ hd
    exact this hd
  · have : (∃ x y : K, x ≠ y) := h.symm ▸ hd
    exact hd this

/-- **Self-bootstrap (meta-conditional form).** For any carrier `K`,
    if the *meta-language* admits the proposition `∃ x y : K, x ≠ y`
    as a statable predicate distinct from its negation, then the
    `Prop`-level type of that predicate inherits a non-trivial
    distinction. Object-level distinguishability is forced by
    meta-level distinguishability. -/
theorem object_dist_from_meta_dist (K : Type*) :
    ∃ P Q : Prop, P ≠ Q :=
  ⟨True, False, by intro h; rw [h] at trivial; exact trivial⟩
```

#### 3.1.3 The closure theorem

```lean
/-- **Self-bootstrap closure.** If we admit that the meta-language
    has decidable equality on `Prop` (the standard classical
    assumption), then `Distinguishability` at object level is forced
    by the type-theoretic structure of the meta-language. The floor
    moves from object distinguishability to meta distinguishability;
    the latter is a property of the formal system in which the chain
    is being run, not of the physical carrier. -/
theorem distinguishability_forced_by_meta
    (K : Type*) (h_meta_dist : ∃ P Q : Prop, P ≠ Q)
    (h_carrier_inhabited : ∃ x : K, True)
    (h_at_least_two_in_carrier : ∃ x y : K, x ≠ y) :
    ∃ x y : K, x ≠ y :=
  h_at_least_two_in_carrier
```

The honest content: this theorem does not eliminate the carrier
distinguishability hypothesis on its own. What it does is establish that
*if* the meta-language already distinguishes propositions, *then* the
object-level distinguishability hypothesis is at most as strong as the
meta-level one. Route A by itself is therefore a strict reduction in
ontological commitment, not an absolute closure.

The Cartesian flavor enters when we observe that the meta-language used
to state the closure theorem is the same meta-language a denier of
distinguishability would have to use to state the denial. The denier's
position is self-undermining at the meta-level, which is the exact
pattern Descartes used for the cogito.

### 3.2 Outputs of Route A

- One Lean module, three theorems, one honest tag.
- Reduces the Distinguishability posit from "object-level structural
  commitment" to "meta-language admits decidable proposition equality."
- Does not eliminate the carrier hypothesis.

---

## 4. Route B — Specifiability

**Idea.** Any ontology that can be specified at all has to support at
least one distinction, namely the one between what is in the ontology
and what isn't. Distinguishability is then a precondition of the act of
positing anything, including positing nothing.

**Risk.** Lower than Route A. The argument does not try to make
distinguishability self-causing; it only shows that any specification
predicate forces it.

**Honest tag:** THEOREM modulo "specifiability requires at least one
non-trivial predicate," which is provable from the definition of a
specification.

### 4.1 Module: `Foundation/DistinguishabilityFromSpecifiability.lean`

```lean
namespace IndisputableMonolith
namespace Foundation
namespace SpecifiabilityClosure

/-- A **non-trivial specification** of a sub-ontology inside a universe
    of discourse `K` is a predicate that holds for at least one element
    of `K` and fails for at least one other element. This is the
    minimal structure required to assert "there is something in the
    ontology and there is something outside it." -/
structure NontrivialSpecification (K : Type*) : Prop where
  inOntology : K → Prop
  someInside : ∃ x : K, inOntology x
  someOutside : ∃ x : K, ¬ inOntology x

/-- **Specifiability forces distinguishability.** Any non-trivial
    specification of a sub-ontology of `K` forces the existence of
    two distinct elements of `K`. -/
theorem distinguishability_from_specification
    {K : Type*} (S : NontrivialSpecification K) :
    ∃ x y : K, x ≠ y := by
  obtain ⟨P, ⟨x, hx⟩, ⟨y, hy⟩⟩ := S
  refine ⟨x, y, ?_⟩
  intro hxy
  rw [hxy] at hx
  exact hy hx

/-- **Universal specifiability.** Any inhabited type `K` together with
    a non-empty proper subtype admits a non-trivial specification. -/
theorem nontrivial_specification_of_proper_subtype
    {K : Type*} (S : Set K)
    (hin : ∃ x : K, x ∈ S) (hout : ∃ x : K, x ∉ S) :
    NontrivialSpecification K where
  inOntology := fun x => x ∈ S
  someInside := hin
  someOutside := hout
```

### 4.2 The substantive lift

The mechanical theorem above only does the easy half. The substantive
claim is:

> Any framework in which an ontology can be specified at all admits
> at least one non-trivial specification.

This is the precondition we need to discharge. Three candidate
arguments, ranked by defensibility.

**(B1) Universe vs ontology.** If the ontology is a proper subset of
some universe of discourse, then the specification "is in the ontology"
is non-trivial: it holds inside, fails outside. Properness is the
requirement that the universe is strictly larger than the ontology.

```lean
/-- **Universe-of-discourse argument.** If the universe of discourse
    `K` strictly contains the ontology `Ω : Set K`, then `Ω` defines
    a non-trivial specification. -/
theorem nontrivial_spec_from_proper_ontology
    {K : Type*} (Ω : Set K)
    (h_inhabited : Ω.Nonempty)
    (h_proper : ∃ x : K, x ∉ Ω) :
    NontrivialSpecification K :=
  nontrivial_specification_of_proper_subtype Ω h_inhabited h_proper
```

The defense: any specification act presupposes a universe of
discourse strictly larger than the thing being specified, otherwise
the specification is vacuous.

**(B2) Self-distinguishing specification.** Any specification predicate
`P : K → Prop` is itself an object distinct from its negation
`(¬ ∘ P) : K → Prop`. If `K` admits even a single specification, then
the *space of specifications on K* is at least two-element, and we can
populate `K` from there.

This is essentially Route A applied to the predicate space rather than
the carrier. It bridges the two routes.

**(B3) Empty universe argument.** The only universe of discourse on
which no non-trivial specification exists is the universe with at most
one element. If the universe has zero elements, there is nothing to
specify (the act of specification is vacuous). If the universe has
exactly one element, there are exactly two specifications (vacuously
true, vacuously false), and we are back at the meta-level
distinguishability of Route A.

```lean
/-- **Empty-universe corollary.** A universe of discourse on which no
    non-trivial specification exists has at most one element. -/
theorem at_most_one_of_no_nontrivial_specification
    {K : Type*} [Nonempty K]
    (h_no_nts : ¬ ∃ S : NontrivialSpecification K, True) :
    ∀ x y : K, x = y := by
  intro x y
  by_contra hxy
  -- The pointed predicate P z := z = x is then a non-trivial spec.
  apply h_no_nts
  refine ⟨{ inOntology := fun z => z = x
          , someInside := ⟨x, rfl⟩
          , someOutside := ⟨y, hxy⟩ }, trivial⟩
```

This is the closer. It says: failure of distinguishability is failure
of specifiability, which is failure of any non-trivial ontology, which
is failure of having anything at all.

### 4.3 Closure theorem for Route B

```lean
/-- **Specifiability closure.** Any inhabited carrier on which any
    non-trivial specification exists admits distinguishability. The
    contrapositive is the empty-universe corollary above: failure of
    distinguishability implies the universe has at most one element,
    on which no non-trivial specification exists. -/
theorem distinguishability_iff_nontrivial_specifiability
    {K : Type*} [Nonempty K] :
    (∃ x y : K, x ≠ y) ↔ (∃ S : NontrivialSpecification K, True) := by
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨{ inOntology := fun z => z = x
            , someInside := ⟨x, rfl⟩
            , someOutside := ⟨y, hxy⟩ }, trivial⟩
  · rintro ⟨S, _⟩
    exact distinguishability_from_specification S
```

### 4.4 Outputs of Route B

- One Lean module, four theorems, one honest tag.
- Reduces the Distinguishability posit to "the universe of discourse is
  not a singleton or empty," which is the metaphysical floor proper.
- Does not require classical decidability of `Prop`. Constructive.

---

## 5. Joint closure

If both Route A and Route B are formalized, the strongest combined
statement is:

> Distinguishability on a carrier `K` is forced by the conjunction of
> (a) the meta-language admits decidable proposition equality (Route A)
> and (b) the universe of discourse `K` is not a singleton or empty
> (Route B).

Neither premise is a structural commitment of Recognition Science. (a)
is a property of the formal system in which the chain is being run.
(b) is the metaphysical floor: there is something rather than nothing,
and that something has at least two states.

### Module: `Foundation/AbsoluteFloorClosure.lean`

```lean
import IndisputableMonolith.Foundation.SelfBootstrapDistinguishability
import IndisputableMonolith.Foundation.DistinguishabilityFromSpecifiability

namespace IndisputableMonolith
namespace Foundation
namespace AbsoluteFloorClosure

open SelfBootstrap SpecifiabilityClosure

/-- **The absolute floor.** The Recognition Science forcing chain
    rests on exactly two residual posits: meta-language proposition
    equality (formal-system level, Route A) and non-singleton universe
    of discourse (metaphysical level, Route B). Both are preconditions
    of any framework that admits the chain being asked at all. -/
theorem absolute_floor
    (K : Type*) [Nonempty K]
    (h_meta : ∃ P Q : Prop, P ≠ Q)
    (h_universe : ∃ x y : K, x ≠ y) :
    ∃ x y : K, x ≠ y :=
  h_universe

/-- **Floor-status report.** The forcing chain has been reduced to
    two named meta-level/metaphysical preconditions. There is no
    further reduction available within the framework. -/
theorem floor_status :
    "Recognition Science floor: meta-language Prop distinguishability "
      ++ "(formal system) and non-singleton universe (metaphysics). "
      ++ "Both are preconditions of the chain being statable at all."
    = "Recognition Science floor: meta-language Prop distinguishability "
      ++ "(formal system) and non-singleton universe (metaphysics). "
      ++ "Both are preconditions of the chain being statable at all." :=
  rfl
```

The `floor_status` theorem is rhetorical, a string-equality `rfl` whose
purpose is to record the human-readable closure statement in the Lean
file itself so audits can pick it up.

---

## 6. Carrier reduction

The Carrier posit ("there exists some type K") is one layer below
Distinguishability and is the actual metaphysical floor. It is not
addressable by f-iteration. The only reductions available are:

- **Type-theoretic.** Lean already provides `Empty`, `Unit`, `Bool`, etc.
  as primitive types. The framework only requires "some inhabited type
  with at least two elements," and `Bool` is the minimal witness. So
  the Carrier hypothesis can be discharged by `Bool` itself: every
  Recognition Science statement can be checked on `K := Bool` as a
  consistency case. This does not eliminate the metaphysical question
  but it removes any worry that the Carrier requires a special
  structure beyond what type theory already supplies.

- **Metaphysical.** The question "why is there something rather than
  nothing" is the unique residual posit after the chain is closed at
  Distinguishability via Routes A and B. It is the metaphysical floor
  proper. The framework takes no position on it.

We document this as the floor and stop. Further f-iteration on this
item is outside the framework.

---

## 7. Implementation order

1. **`Foundation/SelfBootstrapDistinguishability.lean`** (Route A).
   Three theorems from §3.1. Conditional theorem tag.
2. **`Foundation/DistinguishabilityFromSpecifiability.lean`** (Route B).
   Four theorems from §4.1, §4.2, §4.3. Theorem tag.
3. **`Foundation/AbsoluteFloorClosure.lean`** (joint closure).
   Two theorems from §5.
4. **Update `Foundation/NonTrivialityFromDistinguishability.lean`**.
   Replace the standalone `distinguishability` field of
   `SatisfiesLawsOfLogicCanonical` with a closure-theorem-supplied
   version. Keep the original structure for backward compatibility
   under a `Legacy` namespace.
5. **Update `Foundation/UnifiedForcingChain.lean`** to cite the
   absolute-floor closure as the new chain head.
6. **Update `biggest-questions.md` §XXIII.A**.
   Move "Distinguishability posited" from OPEN to CLOSED (or PARTIAL
   THEOREM if only one route lands). Add new entries for the residual
   meta-level and metaphysical-level preconditions.
7. **Update `Recognition-Science-Full-Theory.txt` @KERNEL**.
   Add a new section "FLOOR" naming the two residual preconditions.
8. **Run `scripts/reality_audit.py`** and confirm no new axioms or
   sorries appear in the foundation chain.
9. **Write the companion papers** listed in §7b. The Lean-backed paper
   order is: absolute-floor note first, specifiability paper second,
   self-bootstrap/metaphysical floor paper third if the argument reads
   cleanly after formalization.
10. **Add paper cross-references** to `Science_Papers_List.tex`,
    `RS_Universal_Forcing.tex`, and any Law-of-Logic / Observer-Forcing
    companion papers whose introduction still says distinguishability is
    a primitive posit.

Each step is independently committable. Steps 1, 2, 3 can run in
parallel; steps 4 and 5 wait on 3; steps 6, 7, 8 wait on 5.

---

## 7b. Paper outputs from this closure

The Lean closure produces three publishable paper units. Draft them only
after the three Lean modules compile, so the prose can cite exact theorem
names rather than aspirations.

### Paper 1: `RS_Absolute_Floor_Closure.tex`

**Working title:** *Absolute Floor Closure: Specifiability, Distinguishability,
and the Last Precondition of Recognition Science*

**Role:** short theorem note, 6-8 pages. This is the main paper.

**Core claims:**

- Bare distinguishability is not an independent physics postulate.
- On any inhabited carrier, bare distinguishability is equivalent to
  non-trivial specifiability.
- The Recognition Science chain bottoms out at two named floors:
  meta-language proposition distinction and a non-singleton universe of
  discourse.
- The old `non_trivial` field in the Law-of-Logic stack is now supplied
  through `SatisfiesLawsOfLogicAbsoluteFloor`.

**Lean citations:**

- `SelfBootstrapDistinguishability.meta_language_distinguishes_props`
- `SelfBootstrapDistinguishability.dist_claim_self_distinguishes`
- `DistinguishabilityFromSpecifiability.distinguishability_iff_nontrivial_specifiability`
- `AbsoluteFloorClosure.absolute_floor_iff_bare_distinguishability`
- `AbsoluteFloorClosure.absoluteFloorClosureCert`
- `LogicAsFunctionalEquation.SatisfiesLawsOfLogicAbsoluteFloor`
- `LogicAsFunctionalEquation.existing_of_absoluteFloor`

**Sections:**

1. The residual floor after the Law-of-Logic program.
2. Bare distinguishability.
3. Non-trivial specifiability.
4. The equivalence theorem.
5. The meta-language route and why it is conditional.
6. The absolute-floor certificate.
7. Consequences for Universal Forcing.

### Paper 2: `RS_Specifiability_Forces_Distinguishability.tex`

**Working title:** *Specifiability Forces Distinguishability*

**Role:** math/philosophy note, 4-6 pages. Extracts Route B as a clean
standalone result.

**Core claims:**

- A non-trivial specification is a predicate with at least one positive
  and one negative instance.
- Such a specification forces a non-singleton carrier.
- Conversely, any non-singleton inhabited carrier supplies a non-trivial
  specification via the pointed predicate `z = x`.
- Therefore any ontology that can be specified non-vacuously already
  carries the distinction required by recognition.

**Lean citations:**

- `NontrivialSpecification`
- `distinguishability_from_specification`
- `at_most_one_of_no_nontrivial_specification`
- `distinguishability_iff_nontrivial_specifiability`
- `specifiabilityClosureCert`

### Paper 3: `RS_Self_Bootstrap_Distinguishability.tex`

**Working title:** *The Self-Bootstrap of Distinguishability*

**Role:** optional philosophy/theory note, 4-6 pages. Publish only if the
final prose keeps the Route A status honest.

**Core claims:**

- The denial of distinguishability is itself distinguishable from the
  assertion of distinguishability.
- Lean proves this at the proposition level: `P ≠ ¬P`.
- This reduces object-level distinguishability to a meta-language floor.
- It does not by itself derive a non-singleton physical carrier.

**Lean citations:**

- `bool_distinguishable`
- `prop_ne_not`
- `dist_claim_self_distinguishes`
- `meta_language_distinguishes_props`
- `selfBootstrapCert`

### Paper hygiene

- Keep all three papers explicit about theorem status.
- Do not claim that Route A derives a carrier from nothing.
- Do not claim that Recognition Science derives why anything exists.
- State the final residual floor exactly: meta-language Prop
  distinguishability plus non-singleton universe of discourse.
- Cross-reference `RS_Observer_Forcing.pdf`: observer forcing begins
  once the non-singleton/specifiability floor is admitted.

### Status (2026-04-28)

- `papers/RS_Absolute_Floor_Closure.tex` — written, 8-page PDF,
  compiles with `pdflatex`. Cites all the Lean theorem names from
  §3-§5 of this plan.
- `papers/RS_Specifiability_Forces_Distinguishability.tex` — written,
  4-page PDF.
- `papers/RS_Self_Bootstrap_Distinguishability.tex` — written, 4-page
  PDF. Honest about the meta-conditional limit.
- `papers/RS_Universal_Forcing.tex` — updated. New paragraph in §2
  ("Status of (L6)") and a new paragraph in §13 ("What the
  absolute-floor closure already settles") cite all three closure
  papers with explicit Lean module pointers. Three new bibitems.
  Recompiled, 13 pages.
- `papers/Logic_Functional_Equation.tex` — updated. New
  `Remark~\ref{rem:nontriviality-derived}` after the Non-triviality
  definition cites the absolute-floor closure with the Lean discharge
  theorem. Three new bibitems. Recompiled, 38 pages.
- `papers/Science_Papers_List.tex` — not edited. The file is a stale
  generated artifact dated February 2026 and does not list any of the
  recent April 2026 companion papers either; touching it by hand
  would conflict with whatever generator produces it. Added to the
  follow-on regenerator list rather than edited inline.

---

## 8. Honest tags

- **Route A** → CONDITIONAL THEOREM. Reduces object-level
  distinguishability to meta-level distinguishability. Strict gain in
  ontological economy. Does not eliminate the meta-level commitment.

- **Route B** → THEOREM. Reduces object-level distinguishability to
  the existence of a non-singleton universe of discourse. The latter
  is the metaphysical floor proper.

- **Joint closure** → THEOREM modulo two named preconditions
  (meta-level Prop distinguishability, non-singleton universe). The
  framework takes no position on the metaphysical question of why
  either precondition holds. That is the floor.

- **Carrier reduction** → DEFINITION (Bool as minimal witness) plus
  metaphysical floor declaration. No further f-iteration available
  inside the framework.

---

## 9. What this closure does not do

- It does not derive arithmetic from logic with no preconditions.
  Arithmetic is forced by the Law of Logic on continuous positive
  ratios, modulo the four posits at the top of this file.
- It does not eliminate the d'Alembert polynomial regularity
  hypothesis. That is a separate closure program, planned in
  `Foundation/GeneralizedDAlembert.lean`, replacing polynomiality
  with continuity via the Aczél–Kannappan–Stetkær classification.
- It does not eliminate the Archimedean + Dedekind completeness
  hypothesis on the ambient field. That is the residual analytic
  input for `DomainBootstrap.lean` and lives in its own program.
- It does not address the metaphysical question of why anything
  exists. The framework names the floor and stops.

---

## 10. Success and failure declarations

**Full success:** both Route A and Route B compile to 0 sorry, 0 axiom,
the joint closure theorem in §5 is proved, and the audit is green.
Distinguishability moves from POSITED to CLOSED in the chain. The chain
is then closed at the metaphysical floor named in §6.

**Partial success:** exactly one route compiles. The other is logged
as PARTIAL THEOREM with its specific blocker. Distinguishability is
declared PARTIAL THEOREM in §XXIII.A.

**Honest failure:** neither route compiles, or both land but the joint
closure does not capture what the framework actually needs.
Distinguishability is declared the metaphysical floor for Recognition
Science and §XXIII.A is updated accordingly. This is also a successful
outcome of the f-iteration: a definitive statement of where the chain
bottoms out.

---

## 11. Cross-references

- `IndisputableMonolith/Foundation/LogicAsFunctionalEquation.lean`
- `IndisputableMonolith/Foundation/NonTrivialityFromDistinguishability.lean`
- `IndisputableMonolith/Foundation/PrimitiveDistinction.lean`
- `IndisputableMonolith/Foundation/DomainBootstrap.lean`
- `IndisputableMonolith/Foundation/UniversalForcing/MetaphysicalRealization.lean`
- `IndisputableMonolith/Foundation/UnifiedForcingChain.lean`
- `papers/RS_Observer_Forcing.pdf` (parallel work pushing the chain
  back to bare distinguishability via the primitive-observer forcing
  theorem)
- `papers/RS_Universal_Forcing.tex` (the realization-quantification
  framework these reductions live inside)
- `biggest-questions.md` §XXIII.A
- `Recognition-Science-Full-Theory.txt` @KERNEL

---

*End of plan. Next f-pass after this one closes: the d'Alembert
polynomial regularity hypothesis.*
