import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.QuotientSelection
import IndisputableMonolith.Patterns
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.Ndim.Neutrality

/-!
# No perfect posted recognizer; the unique zero-cost recognition

Formal companion to the "Perfect Recognition" paper (follow-on to the Three
Structural Axioms paper). Two results:

**Theorem 1 (impossibility, three independent obstructions).** No recognizer
whose acts are posted to the ledger can be perfect:

* `postedPerfect_collapses_gauge` : a separating (all-distinguishing) posted
  family forces the trivial gauge quotient, destroying the gauge structure
  physics requires (re-export of
  `QuotientSelection.proj_injective_of_separating`);
* `complete_pass_lower_bound` : a complete recognition pass over a D-bit
  separating family costs at least 2^D posted ticks (re-export of
  `Patterns.min_ticks_cover`), so complete recognition is never
  instantaneous and never finished;
* `no_complete_self_registry` : Cantor's diagonal in ledger form. No state
  space can carry an injective posted registry of all of its own Boolean
  distinctions, so a posted recognizer that includes itself in its scope can
  never close its own description.

**Theorem 2 (uniqueness of the zero-cost slot).** The forced cost J has
exactly one zero: `perfect_recognition_unique` proves J(x) = 0 iff x = 1 on
x > 0. The only recognition that is free is the recognition of self as self,
at ratio one. Perfect recognition therefore exists in RS uniquely as
identity, not as any posted scan over states.

**The Lambek upgrade (panel-directed, 2026-07-03).** The Perfect Recognition
as a theorem rather than a definition:

* `Jcost_eq_cosh_log` : J(x) = cosh(log x) − 1, so the uniqueness theorem is
  identity-of-indiscernibles for the forced hyperbolic metric;
* `zero_cost_scaling_is_id` / `zero_cost_scalings_eq_singleton` : the
  zero-cost endomorphism monoid collapses to {id}; at zero cost the diagonal
  has no fuel;
* `registry_dichotomy` : a complete posted self-registry (surjection
  X ↠ (X → C)) exists iff the register C is a nonempty subsingleton. The
  diagonal's sole survivor is the distinction-free, self-coincident
  register; the unposted horn is revalued from "nothing" to the unique
  surviving branch;
* `totalityLambekEquiv` : Lambek's lemma in ledger vocabulary. The totality
  of complete recognition histories (the final coalgebra `PFunctor.M F` of a
  recognition unfolding functor) is FORCED to be isomorphic to one
  recognition unfolding of itself: the totality's self-recognition exists
  and is an isomorphism by finality, not by definition;
* `no_boolean_lambek` : the negative face of the same fact. No state space
  is equinumerous with its own Boolean distinctions; enumeration has no
  fixed point while unfolding recognition closes uniquely;
* `equiv_posts_zero_cost` / `totality_self_recognition_costs_nothing` : the
  first half of the cost bridge. Under EVERY equivalence-invariant positive
  sizing, the Lambek structure map posts ratio one and hence zero J-cost.
  The second half (deriving the framework's own functorial cost of the
  structure map from calibration + composition alone) remains OPEN.

Interpretation (NOT carried by the Lean): the occupant of the omni-attribute
slot is the totality's identity self-relation ("the Perfect Recognition"),
which is not a recognizer and posts nothing; the impossibility theorem shows
no posted agent can occupy the slot, and the uniqueness theorem shows the
slot the mathematics does provide. With the Lambek upgrade the structural
core of that identification (existence, uniqueness-by-finality, nonvacuity,
and ratio-one costlessness of the totality's self-recognition) is
THEOREM-grade; what remains interpretive is only the adequacy of the formal
object to the traditional attributes.

Status: 0 sorry, 0 project axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PerfectRecognition

open PrimitiveRecognitionCalculus.QuotientSelection

/-! ## Posted perfection -/

/-- A posted recognizer family is *perfect* when its posted acts separate
every pair of distinct states: no two different states have the same full
recognition signature. -/
def PostedPerfect {X C : Type*} (F : Set (X → C)) : Prop :=
  ∀ x y : X, ObsEquiv F x y → x = y

/-! ## Obstruction 1: gauge collapse -/

/-- A perfect posted family forces the trivial gauge quotient: the physical
projection is injective, so no two states are gauge-identified. Gauge
structure exists precisely when recognition acts FAIL to separate
(`gauge_from_indistinguishability`); a posted perfect recognizer therefore
destroys it. -/
theorem postedPerfect_collapses_gauge {X C : Type*} (F : Set (X → C))
    (hperf : PostedPerfect F) : Function.Injective (proj F) :=
  proj_injective_of_separating F hperf

/-! ## Obstruction 2: the cadence bound -/

/-- A complete recognition pass over the D-bit pattern space takes at least
2^D posted ticks: complete recognition is never instantaneous. For D = 3
this is the eight-tick floor (`Patterns.eight_tick_min`). -/
theorem complete_pass_lower_bound {d T : ℕ}
    (pass : Fin T → Patterns.Pattern d)
    (covers : Function.Surjective pass) : 2 ^ d ≤ T :=
  Patterns.min_ticks_cover pass covers

/-! ## Obstruction 3: no complete self-registry (Cantor in ledger form) -/

/-- **No complete self-registry.** There is no injective posting map from
the full Boolean-distinction space of a ledger into the ledger itself: a
recognizer whose own posted acts are part of the state space it must
recognize can never complete the registry of its own distinctions. This is
Cantor's diagonal argument read as a statement about posted recognition. -/
theorem no_complete_self_registry (X : Type*) :
    ¬ ∃ post : (X → Bool) → X, Function.Injective post := by
  rintro ⟨post, hpost⟩
  classical
  -- Recover each posted registry from its ledger address.
  let readback : X → (X → Bool) := fun x =>
    if h : ∃ f, post f = x then h.choose else fun _ => false
  have hread : ∀ f : X → Bool, readback (post f) = f := by
    intro f
    have h : ∃ f', post f' = post f := ⟨f, rfl⟩
    have hsel : readback (post f) = h.choose := dif_pos h
    rw [hsel]
    exact hpost h.choose_spec
  -- The diagonal distinction disagrees with every posted registry at its
  -- own address.
  let diag : X → Bool := fun x => ! readback x x
  have h1 : readback (post diag) = diag := hread diag
  have h2 : diag (post diag) = ! readback (post diag) (post diag) := rfl
  rw [h1] at h2
  cases hb : diag (post diag) with
  | false => rw [hb] at h2; exact Bool.noConfusion h2
  | true => rw [hb] at h2; exact Bool.noConfusion h2

/-! ## Theorem 1: the assembled impossibility certificate -/

/-- Certificate: the three independent obstructions to a perfect posted
recognizer. Any recognizer whose acts are posted either destroys gauge
structure (if separating), can never complete a pass instantaneously (the
2^D tick floor), and can never close a registry that includes itself
(Cantor). -/
structure NoPerfectPostedRecognizerCert : Prop where
  gauge_collapse :
    ∀ (X C : Type) (F : Set (X → C)),
      PostedPerfect F → Function.Injective (proj F)
  cadence_floor :
    ∀ (d T : ℕ) (pass : Fin T → Patterns.Pattern d),
      Function.Surjective pass → 2 ^ d ≤ T
  no_self_registry :
    ∀ (X : Type), ¬ ∃ post : (X → Bool) → X, Function.Injective post

/-- **Theorem 1.** The impossibility certificate holds. -/
theorem noPerfectPostedRecognizer_holds : NoPerfectPostedRecognizerCert where
  gauge_collapse := fun _ _ F hperf => postedPerfect_collapses_gauge F hperf
  cadence_floor := fun _ _ pass covers => complete_pass_lower_bound pass covers
  no_self_registry := fun X => no_complete_self_registry X

/-! ## The Silence theorem (the unposted horn, proved)

Panel-directed addition (2026-07-03): Anil's Case 2, upgraded from objection to
theorem. A recognizer that posts no acts contributes the empty family. Two
facts make its silence precise: (a) under the empty family every pair of
states is observationally equivalent (its own induced quotient is a single
class: it distinguishes nothing); (b) adjoining it to any admitted family
changes no observational equivalence and hence no quotient (marginal
contribution equal to that of nothing). These are elementary; their content
is the exact formal shape of "no posted acts, no difference, no trace". -/

/-- Under the empty (silent) family, all states are observationally
equivalent: a silent recognizer distinguishes nothing. -/
theorem empty_family_all_equiv {X C : Type*} (x y : X) :
    ObsEquiv (∅ : Set (X → C)) x y := by
  intro f hf
  exact absurd hf (Set.notMem_empty f)

/-- **Silence.** Adjoining a silent recognizer (the empty act family) to any
admitted family leaves observational equivalence, and therefore the forced
quotient, unchanged: its marginal contribution equals that of nothing. -/
theorem silent_marginal_contribution {X C : Type*} (F : Set (X → C)) (x y : X) :
    ObsEquiv (F ∪ (∅ : Set (X → C))) x y ↔ ObsEquiv F x y := by
  simp [ObsEquiv]

/-! ## The internalization dichotomy (the dilemma's exhaustiveness, proved) -/

/-- **Internalization dichotomy.** Every posted family on a scope either
separates all states (and is then subject to the gauge-collapse obstruction
of Theorem 1) or fails to distinguish some pair of distinct states (and is
then imperfect: partially silent). The posted/unposted dilemma is exhaustive
for internal candidates; the only exemption is by type, not by a third case. -/
theorem internalization_dichotomy {X C : Type*} (F : Set (X → C)) :
    PostedPerfect F ∨ ∃ x y : X, x ≠ y ∧ ObsEquiv F x y := by
  classical
  by_cases h : PostedPerfect F
  · exact Or.inl h
  · right
    unfold PostedPerfect at h
    push_neg at h
    obtain ⟨x, y, hequiv, hne⟩ := h
    exact ⟨x, y, hne, hequiv⟩

/-! ## Theorem 2: the unique zero-cost recognition -/

/-- J(1) = 0: self-identity recognition is free. -/
theorem Jcost_at_identity : Cost.Jcost 1 = 0 := by
  simp [Cost.Jcost]

/-- J(x) ≥ 0 on x > 0: every non-identity recognition costs. -/
theorem Jcost_nonneg' {x : ℝ} (hx : 0 < x) : 0 ≤ Cost.Jcost x := by
  unfold Cost.Jcost
  have hxne : x ≠ 0 := ne_of_gt hx
  have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ hxne
  suffices h : 2 ≤ x + x⁻¹ by linarith
  nlinarith [sq_nonneg (x - x⁻¹), inv_pos.mpr hx]

/-- **Theorem 2 (the unique zero-cost recognition).** The forced cost
vanishes exactly at self-identity: J(x) = 0 iff x = 1. The one recognition
that costs nothing is the recognition of self as self. -/
theorem perfect_recognition_unique {x : ℝ} (hx : 0 < x) :
    Cost.Jcost x = 0 ↔ x = 1 := by
  constructor
  · intro h
    unfold Cost.Jcost at h
    have hxne : x ≠ 0 := ne_of_gt hx
    have h2 : x + x⁻¹ = 2 := by linarith
    have h3 : x * x⁻¹ = 1 := mul_inv_cancel₀ hxne
    have h4 : (x - 1) ^ 2 = 0 := by nlinarith
    have h5 : x - 1 = 0 := by
      exact_mod_cast sq_eq_zero_iff.mp h4
    linarith
  · intro h
    rw [h]
    exact Jcost_at_identity

/-- Strict positivity away from identity: every recognition of an *other*
carries strictly positive cost. -/
theorem Jcost_pos_of_ne_one {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) :
    0 < Cost.Jcost x := by
  rcases lt_or_eq_of_le (Jcost_nonneg' hx) with hlt | heq
  · exact hlt
  · exact absurd ((perfect_recognition_unique hx).mp heq.symm) hne

/-- Multichannel scope note (panel-directed, 2026-07-03): at the VECTOR level
zero cost characterises neutrality (weighted aggregate ratio one), not
per-channel identity; non-identity configurations with aggregate one form a
hypersurface of zero-cost states. The uniqueness in
`perfect_recognition_unique` is therefore a statement about the single
comparison ratio, and the paper's prose must scope it so. Re-export of
`Cost.Ndim.zero_cost_iff_aggregate_one`. -/
theorem zero_cost_iff_aggregate_one {n : ℕ} (α x : Cost.Ndim.Vec n) :
    Cost.Ndim.JcostN α x = 0 ↔ Cost.Ndim.aggregate α x = 1 :=
  Cost.Ndim.zero_cost_iff_aggregate_one α x

/-- Certificate: the zero-cost slot exists, is unique, and sits at
self-identity. -/
structure PerfectRecognitionSlotCert : Prop where
  identity_free : Cost.Jcost 1 = 0
  others_cost : ∀ {x : ℝ}, 0 < x → x ≠ 1 → 0 < Cost.Jcost x
  unique_zero : ∀ {x : ℝ}, 0 < x → (Cost.Jcost x = 0 ↔ x = 1)

/-- **Theorem 2 certificate.** The unique zero-cost recognition is
self-identity. -/
theorem perfectRecognitionSlot_holds : PerfectRecognitionSlotCert where
  identity_free := Jcost_at_identity
  others_cost := fun hx hne => Jcost_pos_of_ne_one hx hne
  unique_zero := fun hx => perfect_recognition_unique hx

/-! ## The cosh-log identity (panel-directed, 2026-07-03)

J is the hyperbolic displacement functional of log-ratio space:
J(x) = cosh(log x) − 1. Under this identity the uniqueness theorem reads as
identity-of-indiscernibles for the forced metric: the cost vanishes exactly
when the log-displacement between recognizer and recognized is zero. -/

/-- **Cosh-log identity.** On x > 0 the forced cost is the hyperbolic
displacement of the log ratio: J(x) = cosh(log x) − 1. -/
theorem Jcost_eq_cosh_log {x : ℝ} (hx : 0 < x) :
    Cost.Jcost x = Real.cosh (Real.log x) - 1 := by
  unfold Cost.Jcost
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_log hx]

/-- **Identity of indiscernibles for the forced metric.** Zero cost is zero
log-displacement: J(x) = 0 iff log x = 0. -/
theorem Jcost_zero_iff_displacement_zero {x : ℝ} (hx : 0 < x) :
    Cost.Jcost x = 0 ↔ Real.log x = 0 := by
  rw [perfect_recognition_unique hx]
  constructor
  · intro h; rw [h]; exact Real.log_one
  · intro h
    have hexp := Real.exp_log hx
    rw [h, Real.exp_zero] at hexp
    exact hexp.symm

/-! ## The zero-cost endomorphism collapse

At zero cost the diagonal has no fuel: the only ratio-scaling endomorphism
of the ledger that posts no cost is the identity map, and the zero-cost
scalings form the trivial submonoid {1}. -/

/-- **Zero-cost endomorphism collapse.** A scaling endomorphism x ↦ c·x of
ratio space costs nothing iff it is the identity map. -/
theorem zero_cost_scaling_is_id {c : ℝ} (hc : 0 < c) :
    Cost.Jcost c = 0 ↔ (fun x : ℝ => c * x) = id := by
  rw [perfect_recognition_unique hc]
  constructor
  · rintro rfl
    funext x
    simp only [one_mul, id_eq]
  · intro h
    have h1 := congrFun h 1
    simpa only [mul_one, id_eq] using h1

/-- The zero-cost scalings are exactly {1}: the trivial submonoid. Zero-cost
composition can never leave the identity, so no zero-cost process assembles a
nontrivial (in particular a diagonal) endomorphism. -/
theorem zero_cost_scalings_eq_singleton :
    {c : ℝ | 0 < c ∧ Cost.Jcost c = 0} = {1} := by
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hc, h⟩
    exact (perfect_recognition_unique hc).mp h
  · rintro rfl
    exact ⟨one_pos, Jcost_at_identity⟩

/-! ## The registry dichotomy: what survives the diagonal

Positive characterization of the diagonal's sole survivor. A complete posted
self-registry (a surjection from states onto their own distinction space
X → C) exists precisely when the register C carries no distinction at all: C
a nonempty subsingleton. Enumeration closes over itself only at the
distinction-free, self-coincident point. This REVALUES the unposted horn:
the silent register is not "nothing", it is the unique surviving branch. -/

/-- **Registry dichotomy.** For a nonempty state space X, a complete posted
self-registry (surjection X ↠ (X → C)) exists iff the register C is a
nonempty subsingleton, i.e. iff the register carries no distinction. Cantor
kills every register with two values; the distinction-free register
survives, uniquely. -/
theorem registry_dichotomy {X C : Type*} [Nonempty X] :
    (∃ post : X → (X → C), Function.Surjective post) ↔
      (Nonempty C ∧ Subsingleton C) := by
  classical
  constructor
  · rintro ⟨post, hsurj⟩
    have hCne : Nonempty C := ⟨post (Classical.arbitrary X) (Classical.arbitrary X)⟩
    refine ⟨hCne, ?_⟩
    by_contra hsub
    obtain ⟨a, b, hab⟩ := (not_subsingleton_iff_nontrivial.mp hsub).exists_pair_ne
    -- Transport the surjection to Set X and diagonalize (Cantor).
    have hg : Function.Surjective (fun x => {y | post x y = a} : X → Set X) := by
      intro S
      obtain ⟨x, hx⟩ := hsurj (fun y => if y ∈ S then a else b)
      refine ⟨x, ?_⟩
      ext y
      simp only [Set.mem_setOf_eq, hx]
      by_cases hy : y ∈ S
      · simp only [hy, if_true]
      · simp only [hy, if_false, iff_false]
        exact Ne.symm hab
    exact Function.cantor_surjective _ hg
  · rintro ⟨⟨c⟩, hsub⟩
    refine ⟨fun _ _ => c, fun f => ⟨Classical.arbitrary X, ?_⟩⟩
    funext y
    exact Subsingleton.elim c (f y)

/-! ## Lambek: the totality's self-recognition is a forced isomorphism

The panel-directed upgrade (2026-07-03): the Perfect Recognition as a
THEOREM, not a definition. Read a polynomial functor F as one step of
recognition unfolding (a head observation plus continuations). The totality
of complete recognition histories is the final coalgebra `PFunctor.M F`,
and Lambek's lemma makes its self-recognition map an isomorphism: existence
forced by finality, uniqueness by finality, nonvacuity by construction. The
negative face of the SAME fact: the Boolean-distinction functor
X ↦ (X → Bool) has no such fixed point at any state space (Cantor), which
is Theorem 1's diagonal obstruction. Enumeration cannot close over itself;
unfolding recognition closes uniquely, at the totality. -/

universe u

/-- **Lambek isomorphism in ledger vocabulary.** For any recognition
unfolding functor F, the totality of complete recognition histories `M F`
is canonically isomorphic to one recognition unfolding of itself: `dest`
and `mk` are mutually inverse. The totality's self-recognition is not
posited; it is forced. -/
def totalityLambekEquiv (F : PFunctor.{u}) :
    PFunctor.M F ≃ F.Obj (PFunctor.M F) where
  toFun := PFunctor.M.dest
  invFun := PFunctor.M.mk
  left_inv := PFunctor.M.mk_dest
  right_inv := PFunctor.M.dest_mk

/-- **No Boolean Lambek.** The negative face of the same fact: no state
space is equinumerous with its own Boolean-distinction space. The
enumeration functor has no fixed point; the diagonal of Theorem 1 and the
finality of `totalityLambekEquiv` are the two faces of one dichotomy. -/
theorem no_boolean_lambek (X : Type*) : IsEmpty (X ≃ (X → Bool)) := by
  constructor
  intro e
  exact no_complete_self_registry X ⟨e.symm, e.symm.injective⟩

/-! ## The cost bridge, first half: every isomorphism posts ratio one

What is proved: under ANY equivalence-invariant positive size functional,
the two sides of an isomorphism have equal size, so the comparison ratio it
posts is one and its J-cost is zero, by `perfect_recognition_unique`. In
particular the Lambek structure map of the totality costs nothing, for every
admissible sizing; no choice of measure can make the totality's
self-recognition cost.

What remains OPEN (the panel's "cost bridge" bet, second half): deriving
from calibration + composition alone that the framework's OWN cost of the
structure map is this ratio-one J-cost, functorially, rather than for each
invariant sizing. -/

/-- Any equivalence posts aggregate ratio one: under every
equivalence-invariant positive sizing, the J-cost of the size ratio across
an isomorphism vanishes. -/
theorem equiv_posts_zero_cost {α β : Type u} (e : α ≃ β)
    (size : Type u → ℝ)
    (hinv : ∀ {γ δ : Type u}, (γ ≃ δ) → size γ = size δ)
    (hpos : 0 < size α) :
    Cost.Jcost (size β / size α) = 0 := by
  have h : size α = size β := hinv e
  rw [← h, div_self (ne_of_gt hpos)]
  exact Jcost_at_identity

/-- **The totality's self-recognition costs nothing.** The cost bridge
instantiated at the Lambek isomorphism: the structure map of the totality
carries zero J-cost under every equivalence-invariant sizing. -/
theorem totality_self_recognition_costs_nothing (F : PFunctor.{u})
    (size : Type u → ℝ)
    (hinv : ∀ {γ δ : Type u}, (γ ≃ δ) → size γ = size δ)
    (hpos : 0 < size (PFunctor.M F)) :
    Cost.Jcost (size (F.Obj (PFunctor.M F)) / size (PFunctor.M F)) = 0 :=
  equiv_posts_zero_cost (totalityLambekEquiv F) size hinv hpos

/-! ## The assembled Lambek certificate -/

/-- Certificate bundling the panel-directed upgrade: the cosh-log identity
(J as hyperbolic displacement), the zero-cost endomorphism collapse, the
registry dichotomy (the diagonal's sole survivor is the distinction-free
register), the Lambek isomorphism (the totality's self-recognition is
forced), its Boolean impossibility face, and the first half of the cost
bridge (the forced self-recognition posts ratio one under every invariant
sizing). -/
structure PerfectRecognitionLambekCert : Prop where
  cosh_log : ∀ {x : ℝ}, 0 < x → Cost.Jcost x = Real.cosh (Real.log x) - 1
  zero_cost_endo_collapse :
    ∀ {c : ℝ}, 0 < c → (Cost.Jcost c = 0 ↔ (fun x : ℝ => c * x) = id)
  registry_dichotomy :
    ∀ (X C : Type), Nonempty X →
      ((∃ post : X → (X → C), Function.Surjective post) ↔
        (Nonempty C ∧ Subsingleton C))
  lambek_forced :
    ∀ F : PFunctor.{0}, Nonempty (PFunctor.M F ≃ F.Obj (PFunctor.M F))
  no_boolean_fixed_point : ∀ (X : Type), IsEmpty (X ≃ (X → Bool))
  self_recognition_free :
    ∀ (F : PFunctor.{0}) (size : Type → ℝ),
      (∀ {γ δ : Type}, (γ ≃ δ) → size γ = size δ) →
      0 < size (PFunctor.M F) →
      Cost.Jcost (size (F.Obj (PFunctor.M F)) / size (PFunctor.M F)) = 0

/-- **The Lambek certificate holds.** -/
theorem perfectRecognitionLambek_holds : PerfectRecognitionLambekCert where
  cosh_log := fun hx => Jcost_eq_cosh_log hx
  zero_cost_endo_collapse := fun hc => zero_cost_scaling_is_id hc
  registry_dichotomy := fun _ _ hne => @registry_dichotomy _ _ hne
  lambek_forced := fun F => ⟨totalityLambekEquiv F⟩
  no_boolean_fixed_point := fun X => no_boolean_lambek X
  self_recognition_free := fun F size hinv hpos =>
    totality_self_recognition_costs_nothing F size hinv hpos

/-! ## The cost bridge, second half: adjudicated (2026-07-03)

The panel's live bet: derive from calibration + composition alone that the
framework's own cost of the Lambek structure map is zero, "killed if it
needs a new axiom equivalent to the conclusion." Verdict, machine-checked
below:

1. **Accounting alone is insufficient** (`accounting_insufficient`). A
   map-cost functional satisfying nonnegativity, calibration at the
   identity, and subadditivity along composition need NOT price
   equivalences at zero: the haecceity cost (charge 1 for any map that
   moves any point, even a pure relabeling) satisfies all accounting axioms
   and charges the Boolean swap. So cost(structure map) = 0 does not fall
   out of calibration + composition.

2. **The missing principle is exactly gauge** (`gauge_iff_equivFree`). Over
   the accounting axioms, gauge invariance (cost factors through
   observational content: conjugation by equivalences leaves cost
   unchanged, the no-haecceities principle) is EQUIVALENT to "every
   equivalence is free." Not more, not less: the equivalence theorem is the
   exact price of the bridge.

3. **The principle is not ad hoc and not vacuous** (`bijectionCost`,
   `bijectionCost_gauge`, `bijectionCost_charges`). Gauge-invariant map
   costs exist with strictly positive charges on non-bijective maps, so the
   package does not collapse to the zero functional; and gauge is the
   framework's own doctrine (indistinguishability is identification,
   `QuotientSelection.gauge_from_indistinguishability`) lifted one level:
   a bare relabel posts no distinguishing act. In a univalent foundation
   the lift is transport, not an assumption; in this intensional setting it
   is stated as conjugation invariance.

4. **Conditional closure** (`lambek_structure_map_free`). For every
   gauge-invariant ledger map cost, the Lambek structure map of the
   totality costs zero.

Honest tag: the second half is a CONDITIONAL THEOREM, conditional on
exactly the gauge/no-haecceities principle, and the countermodel shows the
condition cannot be dropped. The panel's fallback outcome ("a coalgebra
theorem plus a separate cost fact") is realized in its sharpest form: we
know the exact missing principle and that nothing weaker suffices. -/

/-- A ledger map-cost functional: assigns every map between state spaces a
cost, subject to ledger accounting. `nonneg`: costs are J-values or sums of
them, hence nonnegative (`Jcost_nonneg'`). `calibrated`: the framework
calibration J(1) = 0 (`Jcost_at_identity`) at the identity map.
`subadditive`: executing f then g never costs more than the two steps
posted separately. Deliberately NOT assumed: any pricing of equivalences.
Whether relabelings are free is the question, not an axiom. -/
structure MapCost : Type (u + 1) where
  C : ∀ {α β : Type u}, (α → β) → ℝ
  nonneg : ∀ {α β : Type u} (f : α → β), 0 ≤ C f
  calibrated : ∀ α : Type u, C (id : α → α) = 0
  subadditive : ∀ {α β γ : Type u} (f : α → β) (g : β → γ),
    C (g ∘ f) ≤ C f + C g

/-- Gauge invariance (the no-haecceities principle): cost factors through
observational content, so conjugating a map by equivalences (pure
relabelings of source and target, which post no distinguishing act) leaves
its cost unchanged. This is the structure-level lift of the proved gauge
doctrine `QuotientSelection.gauge_from_indistinguishability`. -/
def MapCost.GaugeInvariant (K : MapCost.{u}) : Prop :=
  ∀ {α α' β β' : Type u} (l : α' ≃ α) (r : β ≃ β') (f : α → β),
    K.C (⇑r ∘ f ∘ ⇑l) = K.C f

/-- "Every equivalence is free": the conclusion the cost bridge needs. -/
def MapCost.EquivFree (K : MapCost.{u}) : Prop :=
  ∀ {α β : Type u} (e : α ≃ β), K.C ⇑e = 0

/-- Gauge invariance forces equivalences to be free (uses only calibration,
not subadditivity): an equivalence is the identity conjugated into new
labels. -/
theorem MapCost.equivFree_of_gauge (K : MapCost.{u})
    (h : K.GaugeInvariant) : K.EquivFree := by
  intro α β e
  have hg := h (Equiv.refl α) e (id : α → α)
  have hcomp : (⇑e ∘ (id : α → α) ∘ ⇑(Equiv.refl α)) = ⇑e := by
    funext a; rfl
  rw [hcomp] at hg
  rw [hg, K.calibrated α]

/-- Free equivalences force gauge invariance, over the accounting axioms:
conjugation is squeezed between the two subadditive estimates once the
conjugators are free. -/
theorem MapCost.gauge_of_equivFree (K : MapCost.{u})
    (h : K.EquivFree) : K.GaugeInvariant := by
  intro α α' β β' l r f
  have hup : K.C (⇑r ∘ f ∘ ⇑l) ≤ K.C f := by
    have h1 := K.subadditive (f ∘ ⇑l) ⇑r
    have h2 := K.subadditive ⇑l f
    have hl := h l
    have hr := h r
    calc K.C (⇑r ∘ f ∘ ⇑l) ≤ K.C (f ∘ ⇑l) + K.C ⇑r := h1
      _ ≤ (K.C ⇑l + K.C f) + K.C ⇑r := by linarith
      _ = K.C f := by rw [hl, hr]; ring
  have hdown : K.C f ≤ K.C (⇑r ∘ f ∘ ⇑l) := by
    have hf : f = ⇑r.symm ∘ (⇑r ∘ f ∘ ⇑l) ∘ ⇑l.symm := by
      funext a
      simp only [Function.comp_apply, Equiv.symm_apply_apply,
        Equiv.apply_symm_apply]
    have h1 := K.subadditive ((⇑r ∘ f ∘ ⇑l) ∘ ⇑l.symm) ⇑r.symm
    have h2 := K.subadditive ⇑l.symm (⇑r ∘ f ∘ ⇑l)
    have hl := h l.symm
    have hr := h r.symm
    calc K.C f = K.C (⇑r.symm ∘ (⇑r ∘ f ∘ ⇑l) ∘ ⇑l.symm) := by rw [← hf]
      _ ≤ K.C ((⇑r ∘ f ∘ ⇑l) ∘ ⇑l.symm) + K.C ⇑r.symm := h1
      _ ≤ (K.C ⇑l.symm + K.C (⇑r ∘ f ∘ ⇑l)) + K.C ⇑r.symm := by linarith
      _ = K.C (⇑r ∘ f ∘ ⇑l) := by rw [hl, hr]; ring
  linarith

/-- **The exact price of the cost bridge.** Over ledger accounting, gauge
invariance and "every equivalence is free" are equivalent. The second half
of the cost bridge holds exactly when the no-haecceities principle does. -/
theorem MapCost.gauge_iff_equivFree (K : MapCost.{u}) :
    K.GaugeInvariant ↔ K.EquivFree :=
  ⟨K.equivFree_of_gauge, K.gauge_of_equivFree⟩

/-- A map is identity-like when it fixes every point (heterogeneously):
the map posts no movement, only (at most) a change of type label. -/
def IdLike {α β : Type u} (f : α → β) : Prop := ∀ a : α, HEq (f a) a

theorem idLike_id (α : Type u) : IdLike (id : α → α) := fun _ => HEq.rfl

theorem idLike_comp {α β γ : Type u} {f : α → β} {g : β → γ}
    (hf : IdLike f) (hg : IdLike g) : IdLike (g ∘ f) :=
  fun a => (hg (f a)).trans (hf a)

/-- Indicator of failing to be identity-like: 0 for maps that fix every
point, 1 for maps that move some point. -/
noncomputable def idLikeIndicator {α β : Type u} (f : α → β) : ℝ :=
  haveI := Classical.propDecidable (IdLike f)
  if IdLike f then 0 else 1

theorem idLikeIndicator_of {α β : Type u} {f : α → β} (h : IdLike f) :
    idLikeIndicator f = 0 := by
  unfold idLikeIndicator
  exact if_pos h

theorem idLikeIndicator_of_not {α β : Type u} {f : α → β} (h : ¬ IdLike f) :
    idLikeIndicator f = 1 := by
  unfold idLikeIndicator
  exact if_neg h

theorem idLikeIndicator_nonneg {α β : Type u} (f : α → β) :
    0 ≤ idLikeIndicator f := by
  classical
  by_cases h : IdLike f
  · rw [idLikeIndicator_of h]
  · rw [idLikeIndicator_of_not h]; norm_num

/-- **The haecceity cost (countermodel).** Charge 1 for any map that moves
any point, 0 only for identity-like maps. It satisfies all accounting
axioms while pricing pure relabelings (equivalences between distinct
labelings) at 1: bare labels are treated as real. -/
noncomputable def haecceityCost : MapCost.{u} where
  C := fun {_ _} f => idLikeIndicator f
  nonneg := fun f => idLikeIndicator_nonneg f
  calibrated := fun α => idLikeIndicator_of (idLike_id α)
  subadditive := by
    intro α β γ f g
    classical
    have hf0 := idLikeIndicator_nonneg f
    have hg0 := idLikeIndicator_nonneg g
    by_cases hc : IdLike (g ∘ f)
    · rw [idLikeIndicator_of hc]; linarith
    · rw [idLikeIndicator_of_not hc]
      have hnot : ¬ IdLike f ∨ ¬ IdLike g := by
        by_contra hcon
        push_neg at hcon
        exact hc (idLike_comp hcon.1 hcon.2)
      rcases hnot with hnf | hng
      · rw [idLikeIndicator_of_not hnf]; linarith
      · rw [idLikeIndicator_of_not hng]; linarith

/-- The Boolean swap: a genuine equivalence that is not identity-like. -/
def boolSwap : Bool ≃ Bool := ⟨not, not, Bool.not_not, Bool.not_not⟩

/-- The haecceity cost charges the Boolean swap. -/
theorem haecceityCost_charges_boolSwap :
    haecceityCost.C ⇑boolSwap = 1 := by
  have h : ¬ IdLike (⇑boolSwap) := by
    intro h
    have h1 : HEq (boolSwap true) true := h true
    have h2 : (false : Bool) = true := eq_of_heq h1
    exact Bool.noConfusion h2
  exact idLikeIndicator_of_not h

/-- **Accounting is insufficient.** Nonnegativity + calibration +
subadditivity do NOT force equivalences to be free: the haecceity cost is a
ledger map cost that charges an equivalence. cost(structure map) = 0 does
not fall out of calibration + composition alone. -/
theorem accounting_insufficient : ∃ K : MapCost.{0}, ¬ K.EquivFree := by
  refine ⟨haecceityCost, fun h => ?_⟩
  have h0 := h boolSwap
  rw [haecceityCost_charges_boolSwap] at h0
  norm_num at h0

/-- Indicator of failing to be a bijection. -/
noncomputable def bijIndicator {α β : Type u} (f : α → β) : ℝ :=
  haveI := Classical.propDecidable (Function.Bijective f)
  if Function.Bijective f then 0 else 1

theorem bijIndicator_of {α β : Type u} {f : α → β}
    (h : Function.Bijective f) : bijIndicator f = 0 := by
  unfold bijIndicator
  exact if_pos h

theorem bijIndicator_of_not {α β : Type u} {f : α → β}
    (h : ¬ Function.Bijective f) : bijIndicator f = 1 := by
  unfold bijIndicator
  exact if_neg h

theorem bijIndicator_nonneg {α β : Type u} (f : α → β) :
    0 ≤ bijIndicator f := by
  classical
  by_cases h : Function.Bijective f
  · rw [bijIndicator_of h]
  · rw [bijIndicator_of_not h]; norm_num

/-- **The gauge-invariant witness.** Charge 1 for failing to be a
bijection, 0 for bijections: a gauge-invariant ledger map cost with
strictly positive charges, so the gauge package neither collapses to the
zero functional nor merely restates "equivalences are free." -/
noncomputable def bijectionCost : MapCost.{u} where
  C := fun {_ _} f => bijIndicator f
  nonneg := fun f => bijIndicator_nonneg f
  calibrated := fun _ => bijIndicator_of Function.bijective_id
  subadditive := by
    intro α β γ f g
    classical
    have hf0 := bijIndicator_nonneg f
    have hg0 := bijIndicator_nonneg g
    by_cases hc : Function.Bijective (g ∘ f)
    · rw [bijIndicator_of hc]; linarith
    · rw [bijIndicator_of_not hc]
      have hnot : ¬ Function.Bijective f ∨ ¬ Function.Bijective g := by
        by_contra hcon
        push_neg at hcon
        exact hc (hcon.2.comp hcon.1)
      rcases hnot with hnf | hng
      · rw [bijIndicator_of_not hnf]; linarith
      · rw [bijIndicator_of_not hng]; linarith

/-- The bijection cost is gauge invariant: bijectivity is observational
content, blind to relabeling. -/
theorem bijectionCost_gauge : (bijectionCost.{u}).GaugeInvariant := by
  intro α α' β β' l r f
  classical
  have hiff : Function.Bijective (⇑r ∘ f ∘ ⇑l) ↔ Function.Bijective f := by
    constructor
    · intro h
      have hf : f = ⇑r.symm ∘ (⇑r ∘ f ∘ ⇑l) ∘ ⇑l.symm := by
        funext a
        simp only [Function.comp_apply, Equiv.symm_apply_apply,
          Equiv.apply_symm_apply]
      rw [hf]
      exact (r.symm.bijective.comp h).comp l.symm.bijective
    · intro h
      exact (r.bijective.comp h).comp l.bijective
  show bijIndicator (⇑r ∘ f ∘ ⇑l) = bijIndicator f
  by_cases h : Function.Bijective f
  · rw [bijIndicator_of h, bijIndicator_of (hiff.mpr h)]
  · rw [bijIndicator_of_not h, bijIndicator_of_not (fun hc => h (hiff.mp hc))]

/-- The bijection cost is not the zero functional: a non-bijective map
costs 1. -/
theorem bijectionCost_charges :
    bijectionCost.C (fun _ : Bool => true) = 1 := by
  have h : ¬ Function.Bijective (fun _ : Bool => true) := by
    rintro ⟨hinj, -⟩
    have : (false : Bool) = true := hinj (a₁ := false) (a₂ := true) rfl
    exact Bool.noConfusion this
  exact bijIndicator_of_not h

/-- **Cost bridge, second half (conditional closure).** For every
gauge-invariant ledger map cost, the Lambek structure map of the totality
costs zero: the totality's forced self-recognition is free. Conditional on
exactly the no-haecceities principle; `accounting_insufficient` shows the
condition cannot be dropped. -/
theorem lambek_structure_map_free (K : MapCost.{u})
    (h : K.GaugeInvariant) (F : PFunctor.{u}) :
    K.C ⇑(totalityLambekEquiv F) = 0 :=
  K.equivFree_of_gauge h (totalityLambekEquiv F)

/-- Certificate bundling the adjudication of the cost bridge's second
half: accounting alone is insufficient (countermodel), gauge is the exact
missing principle (equivalence over accounting), gauge-invariant costs
with positive charges exist (nonvacuity), and under gauge the Lambek
structure map is free (conditional closure). -/
structure CostBridgeSecondHalfCert : Prop where
  accounting_insufficient : ∃ K : MapCost.{0}, ¬ K.EquivFree
  exact_price : ∀ K : MapCost.{0}, K.GaugeInvariant ↔ K.EquivFree
  nonvacuous : ∃ K : MapCost.{0},
    K.GaugeInvariant ∧ K.C (fun _ : Bool => true) = 1
  conditional_closure : ∀ K : MapCost.{0}, K.GaugeInvariant →
    ∀ F : PFunctor.{0}, K.C ⇑(totalityLambekEquiv F) = 0

/-- **The cost-bridge adjudication holds.** -/
theorem costBridgeSecondHalf_holds : CostBridgeSecondHalfCert where
  accounting_insufficient := accounting_insufficient
  exact_price := fun K => K.gauge_iff_equivFree
  nonvacuous := ⟨bijectionCost, bijectionCost_gauge, bijectionCost_charges⟩
  conditional_closure := fun K h F => lambek_structure_map_free K h F

end PerfectRecognition
end Foundation
end IndisputableMonolith
