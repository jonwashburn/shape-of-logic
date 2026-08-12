import IndisputableMonolith.Gravity.SevenGaps.Gap2NonEquivariantPosting

/-!
# Gap 2: can posting plus gluing force unit sector fugacity?  No, and the reason is exact

`Gap2GluingDerivation.closedForm` reduces the path-sum measure's residual freedom to three positive
constants: a size-blind weight satisfying the four carrier gluing instances is the inverse gauge
volume times one fugacity per index type, and `characterSize u v w` realizes every triple
(`residue_is_exactly_three_positive_constants`).  `gibbs_of_unit_fugacities` then gets the measure
from `f 1 0 0 = f 1 1 0 = f 1 0 1 = 1`.  That last hypothesis is the premise the Gap-2 measure
rests on, recorded as unit sector fugacity.

`Gap2NonEquivariantPosting` sharpened the posting-layer criterion: for every letter cost, posting
`mu` is exactly orbit mean one on the Boltzmann numerator
(`posts_mu_iff_numeratorMass_eq_orbitCard`), and a continuum of non-equivariant costs
(`tiltedCost t`) meets it.  The open question this module was opened to answer: does the
posting layer, together with the gluing law, force the three constants to one?

## The answer, in three theorems

**No, and the countermodel is the best-behaved cost in the formalism.**  `characterCost u v w`
charges every vertex letter `-log u`, every edge letter `-log v`, every tetrahedron letter
`-log w`.  It is kind-only and gauge-equivariant, so it satisfies the posting layer's named
structural conditions (`KindOnly`, and with it `ChargesCountsOnly`, `FixedKindTotals`, and
`CostSizeBlind`), and

* `postedWeight_characterCost`: its posted weight is *exactly* `sizeWeight (characterSize u v w)`,
  so the kind-rate family and the gluing derivation's three-constant residue are the same family,
  under the substitution `u = exp(-cV)`, `v = exp(-cE)`, `w = exp(-cT)`;
* `characterSize_carrierShuffle` (imported) and `characterSize_gluesAt`: it satisfies the gluing
  law at all four carrier families and in fact at **every** eligible pair, for every positive
  triple;
* `unitFugacity_characterSize_iff`: its fugacity is unit exactly when `u = v = w = 1`.

So `gluing_and_posting_do_not_force_unit_fugacity`: for every non-unit positive triple there is a
kind-only equivariant letter cost whose posted weight is size-blind, whose induced size function
satisfies the gluing law everywhere, and whose sector fugacity is not unit.  The gluing law
constrains the *shape* of the fugacity (it must be a character) and nothing about its value.

**What does force it is a restatement of the conclusion.**  `unitFugacity_iff_mu_at_atoms`: for
any size function whatever, unit sector fugacity holds **if and only if** the class mass of its
size-blind weight equals `mu` at the three atoms.  And `unitFugacity_iff_normalizedAtTheAtoms`:
it holds if and only if the labeled weight is `1` there, which is `NormalizedAtTheAtoms`.  Three
names, one statement.  So the premise is not a normalization convention sitting beside the
conclusion; it is three instances of the conclusion, at the three smallest complexes.

**Hence the charged no-go direction is three instances of its own conclusion, and the gluing
hypothesis in it is idle.**
`posts_mu_at_atoms_forces_unit_fugacity` derives unit fugacity from posting `mu` at three
complexes with **no** gluing hypothesis and no positivity.  A conditional whose conclusion follows
from one hypothesis alone, where that hypothesis names the target measure, derives nothing.
`gluing_hypothesis_is_idle` states both halves side by side so the shape cannot be misread.

## The charged first step: does the tilted family's posted weight satisfy the gluing law?

Yes at the class-mass level, with unit fugacity, and trivially so.  `CarrierShuffle` is a
predicate on size functions, and the tilted posted weight is not one
(`postedWeight_tiltedCost_not_sizeWeight`, from the imported non-invariance).  What it does have
is a class mass, and because the family posts `mu` that class mass coincides with the size-blind
Gibbs one at every complex and every cap
(`tiltedCost_classMass_eq_classMass_gibbsSize`), so the size function representing it is
`gibbsSize`, which glues and is unit
(`tiltedCost_classMass_glues_with_unit_fugacity`).  The tilted family is therefore **not** a
non-unit-fugacity countermodel, and `no_posting_countermodel_with_nonunit_fugacity` shows nothing
that posts `mu` can be one: posting `mu` and non-unit fugacity are contradictory by construction.
That closes the countermodel direction as charged, and relocates the real countermodel to the
mu-free question, which is where `characterCost` answers it.

## What this does NOT show

**It does not show unit fugacity is unreachable.**  It shows it is not reachable from the two
inputs named here, the posting layer's structural conditions and the gluing law, in any
combination that does not name `mu` or the atom values.  A genuinely new physical input that
fixes the weight of a single vertex, a single loop, and a single degenerate tetrahedron would
close the premise; this module says exactly what such an input has to do, which is more than
"three constants" said before.

**It does not weaken anything already proved.**  `posting_cost_derives_mu` still derives the
measure from kind-only plus `NormalizedAtTheAtoms`; what this module adds is that its second
hypothesis is the premise rather than an extra convenience, so that derivation relocates the
premise onto the posting layer without discharging it.  The countermodel is consistent with it:
`characterCost u v w` fails `NormalizedAtTheAtoms` for every non-unit triple, which is exactly
`characterCost_posts_mu_iff`.

**The countermodel family is not new; the identification is.**  A kind-only cost with nonzero
rates was already known not to give the Gibbs weight
(`Gap2PostingCostDerivation.linearCost_atoms_force_zero` runs on that fact).  What is new here is
that the kind-rate family *is* `characterSize`, the exact residue of the gluing derivation, so the
two modules' leftover freedoms are one freedom and no gluing family can shrink it.

**It says nothing about what a substrate posts.**  Same MODEL attachments as the imported
posting modules: `LetterCost` read as a charging rule, `historyCost` as ledger additivity over
postings, and the Boltzmann form.  This module adds none.

## Honest tagging

Every declaration below is THEOREM, kernel-checked in this module, audited by `#print axioms` at
the foot at the base triple only.  **Strength.**  All statements are exact equalities and
equivalences of reals over unbounded families, not agreements to a tolerance.  The countermodel is
a three-parameter continuum, and the three equivalences (`unitFugacity_iff_mu_at_atoms`,
`unitFugacity_iff_normalizedAtTheAtoms`, `unitFugacity_characterSize_iff`) are iffs quantified
over all size functions, so none of them is a one-witness claim.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2FugacityPostingGluing

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume Gap2GluingDerivation
open GaugeHistoryMeasure Gap2SizeBlindnessReach Gap2PostingCostDerivation
open Gap2NonEquivariantPosting

noncomputable section

variable {B : ℕ}

/-! ## §1. Unit sector fugacity, named, and three ways of saying it

The premise of `gibbs_of_unit_fugacities` as a predicate, so it can appear on both sides of an
equivalence.  Nothing here mentions the posting layer. -/

/-- **Unit sector fugacity**: the size function is one at each of the three atoms.  This is
literally the hypothesis triple of `Gap2GluingDerivation.CarrierShuffle.gibbs_of_unit_fugacities`,
and it is the premise flag 8 of the full-theory ledger stands on. -/
def UnitFugacity (f : ℕ → ℕ → ℕ → ℝ) : Prop :=
  f 1 0 0 = 1 ∧ f 1 1 0 = 1 ∧ f 1 0 1 = 1

/-- The Gibbs weight of a labeled complex is the Gibbs size function at its three sizes.  A cast
identity: both are the reciprocal of the same product of factorials. -/
theorem gibbsWeight_eq_gibbsSize (K : BoundedComplex B) :
    gibbsWeight K = gibbsSize K.nV K.nE K.nT := by
  unfold gibbsWeight gibbsSize
  push_cast
  ring

/-- **THEOREM (the bridge).**  A size-blind weight has class mass `mu` at a complex exactly when
its size function agrees with `gibbsSize` at that complex's size triple.  The orbit count cancels;
this is `classMass_sizeWeight` against `mu_eq_orbitCard_mul_gibbsWeight`, and it is the only
computation the rest of §1 needs. -/
theorem classMass_sizeWeight_eq_mu_iff (f : ℕ → ℕ → ℕ → ℝ) (K : BoundedComplex B) :
    classMass (sizeWeight f) (Quotient.mk (relabelSetoid B) K) = mu K
      ↔ f K.nV K.nE K.nT = gibbsSize K.nV K.nE K.nT := by
  have horb : (0 : ℝ) < (gaugeOrbitCard K : ℝ) := by
    exact_mod_cast gaugeOrbitCard_pos K
  rw [classMass_sizeWeight, mu_eq_orbitCard_mul_gibbsWeight, gibbsWeight_eq_gibbsSize]
  constructor
  · intro h
    exact mul_left_cancel₀ horb.ne' h
  · intro h
    rw [h]

/-- The Gibbs size function is one at every atom size triple, which is why the unit point is the
intended one. -/
theorem gibbsSize_eq_one_at_atom_sizes {b c : ℕ} (hbc : b + c ≤ 1) : gibbsSize 1 b c = 1 := by
  have hb : b = 0 ∨ b = 1 := by omega
  have hc : c = 0 ∨ c = 1 := by omega
  rcases hb with hb | hb <;> rcases hc with hc | hc
  · rw [hb, hc]; norm_num [gibbsSize, Nat.factorial]
  · rw [hb, hc]; norm_num [gibbsSize, Nat.factorial]
  · rw [hb, hc]; norm_num [gibbsSize, Nat.factorial]
  · omega

theorem gibbsSize_unitFugacity : UnitFugacity gibbsSize :=
  ⟨gibbsSize_eq_one_at_atom_sizes (by norm_num),
    gibbsSize_eq_one_at_atom_sizes (by norm_num),
    gibbsSize_eq_one_at_atom_sizes (by norm_num)⟩

/-- **THEOREM (the premise IS three instances of the conclusion).**  For every size function
whatever, positive or not, gluing or not, unit sector fugacity holds if and only if the class mass
of its size-blind weight equals `mu` at every complex with one vertex and at most one incidence,
i.e. at the three atoms.

This is the load-bearing statement of the module and it is an equivalence, not an implication.
Read the two directions separately.  Left to right says the premise is enough to get `mu` at the
atoms, which nobody doubted.  Right to left says the premise is *no more than* `mu` at the atoms:
any principle that yields unit fugacity has already yielded three values of the measure it was
supposed to be deriving.  Any condition that forces unit fugacity thereby determines the measure
at the three atoms: that is a requirement on such a condition, not a proof that none exists, and
it is the precise form of the obstruction the rest of this module measures. -/
theorem unitFugacity_iff_mu_at_atoms (f : ℕ → ℕ → ℕ → ℝ) :
    UnitFugacity f
      ↔ ∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
          classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') K) = mu K := by
  constructor
  · rintro ⟨h1, h2, h3⟩ B' K hv hi
    rw [classMass_sizeWeight_eq_mu_iff]
    have hgs : gibbsSize K.nV K.nE K.nT = 1 := by
      rw [hv]
      exact gibbsSize_eq_one_at_atom_sizes hi
    rw [hgs]
    have hb : K.nE = 0 ∨ K.nE = 1 := by omega
    have hc : K.nT = 0 ∨ K.nT = 1 := by omega
    rcases hb with hb | hb <;> rcases hc with hc | hc
    · rw [hv, hb, hc]; exact h1
    · rw [hv, hb, hc]; exact h3
    · rw [hv, hb, hc]; exact h2
    · omega
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hK := h _ (bouquet 0 0) rfl (by norm_num)
      rw [classMass_sizeWeight_eq_mu_iff] at hK
      simpa [gibbsSize, Nat.factorial] using hK
    · have hK := h _ (bouquet 1 0) rfl (by norm_num)
      rw [classMass_sizeWeight_eq_mu_iff] at hK
      simpa [gibbsSize, Nat.factorial] using hK
    · have hK := h _ (bouquet 0 1) rfl (by norm_num)
      rw [classMass_sizeWeight_eq_mu_iff] at hK
      simpa [gibbsSize, Nat.factorial] using hK

/-- **THEOREM (the premise is also exactly the labeled normalization).**  Unit sector fugacity on
the size function holds if and only if the labeled size-blind weight is `NormalizedAtTheAtoms`,
which is the premise `Gap2PostingCostDerivation` uses in place of gluing.  So the two derivations
in the library do not rest on two different premises: they rest on the same one, written once as a
condition on a size function and once as a condition on a labeled weight.  The bridge between the
two writings is `Gap2PostingCostDerivation.postedWeight_sizeBlind` together with the
`SizeBlind`-to-`sizeWeight` equivalence: a size-blind posted weight is a `sizeWeight`, so
`NormalizedAtTheAtoms` on it is exactly this theorem's right side. -/
theorem unitFugacity_iff_normalizedAtTheAtoms (f : ℕ → ℕ → ℕ → ℝ) :
    UnitFugacity f ↔ NormalizedAtTheAtoms (fun _ K => sizeWeight f K) := by
  constructor
  · rintro ⟨h1, h2, h3⟩ B' K hv hi
    show f K.nV K.nE K.nT = 1
    have hb : K.nE = 0 ∨ K.nE = 1 := by omega
    have hc : K.nT = 0 ∨ K.nT = 1 := by omega
    rcases hb with hb | hb <;> rcases hc with hc | hc
    · rw [hv, hb, hc]; exact h1
    · rw [hv, hb, hc]; exact h3
    · rw [hv, hb, hc]; exact h2
    · omega
  · intro h
    exact ⟨by simpa [sizeWeight] using h _ (bouquet 0 0) rfl (by norm_num),
      by simpa [sizeWeight] using h _ (bouquet 1 0) rfl (by norm_num),
      by simpa [sizeWeight] using h _ (bouquet 0 1) rfl (by norm_num)⟩

/-! ## §2. The countermodel cost: one fugacity per index type, charged per letter

A letter cost that charges each letter a fixed amount by kind.  Its posted weight is computed
exactly, and it turns out to be the gluing derivation's three-constant residue on the nose. -/

/-- The **character cost**: every vertex letter costs `-log u`, every edge letter `-log v`, every
tetrahedron letter `-log w`.  Kind-only by construction, so the best-behaved shape a letter cost
can have; nothing here reads a label, an incidence, or a size. -/
def characterCost (u v w : ℝ) : LetterCost := fun _ _ a =>
  match a with
  | Sum.inl _ => -Real.log u
  | Sum.inr (Sum.inl _) => -Real.log v
  | Sum.inr (Sum.inr _) => -Real.log w

theorem characterCost_kindRates (u v w : ℝ) :
    KindRates (characterCost u v w) (-Real.log u) (-Real.log v) (-Real.log w) := by
  intro B' K
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem characterCost_kindOnly (u v w : ℝ) : KindOnly (characterCost u v w) :=
  ⟨-Real.log u, -Real.log v, -Real.log w, characterCost_kindRates u v w⟩

/-- **THEOREM (the character cost is gauge-equivariant).**  A letter's charge depends only on
which of the three blocks it lies in, and the alphabet transport a relabeling induces is a
block-diagonal sum congruence, so it never moves a letter between blocks. -/
theorem characterCost_equivariant (u v w : ℝ) : Equivariant (characterCost u v w) := by
  intro B' K K' r a
  rcases a with x | (y | z) <;> rfl

theorem historyCost_characterCost (u v w : ℝ) (B' : ℕ) (K : BoundedComplex B') :
    historyCost (characterCost u v w) B' K
      = -Real.log u * (K.nV : ℝ) + -Real.log v * (K.nE : ℝ) + -Real.log w * (K.nT : ℝ) :=
  historyCost_of_kindRates (characterCost_kindRates u v w) B' K

/-- A positive real raised to a natural power, through the exponential.  Proved by induction
rather than cited so no Mathlib naming drift can break the module. -/
theorem exp_log_mul_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.exp (Real.log x * (n : ℝ)) = x ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hstep : Real.log x * ((k + 1 : ℕ) : ℝ) = Real.log x * (k : ℝ) + Real.log x := by
        push_cast; ring
      rw [hstep, Real.exp_add, ih, Real.exp_log hx, pow_succ]

/-- **THEOREM (the Boltzmann numerator of the character cost).**  Exactly one fugacity factor per
cell: `u^nV · v^nE · w^nT`.  This is where the name comes from, and it is a computation, not a
design choice: the charge is per letter and the alphabet has one letter per cell. -/
theorem exp_neg_historyCost_characterCost {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (B' : ℕ) (K : BoundedComplex B') :
    Real.exp (-(historyCost (characterCost u v w) B' K))
      = u ^ K.nV * v ^ K.nE * w ^ K.nT := by
  rw [historyCost_characterCost]
  have hneg : -(-Real.log u * (K.nV : ℝ) + -Real.log v * (K.nE : ℝ) + -Real.log w * (K.nT : ℝ))
      = Real.log u * (K.nV : ℝ) + (Real.log v * (K.nE : ℝ) + Real.log w * (K.nT : ℝ)) := by
    ring
  rw [hneg, Real.exp_add, Real.exp_add, exp_log_mul_nat hu, exp_log_mul_nat hv,
    exp_log_mul_nat hw]
  ring

/-- **THEOREM (the identification, and the point of the module).**  The posted weight of the
character cost is *exactly* the size-blind weight of `characterSize u v w`, the three-constant
residue `Gap2GluingDerivation` was left with.  So the kind-rate family at the posting layer and
the residue of the gluing derivation are the same family, under `u = exp(-cV)`, `v = exp(-cE)`,
`w = exp(-cT)`.  Everything in §3 is read off this equality. -/
theorem postedWeight_characterCost {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (B' : ℕ) (K : BoundedComplex B') :
    postedWeight (characterCost u v w) B' K = sizeWeight (characterSize u v w) K := by
  unfold postedWeight sizeWeight characterSize gibbsWeight gaugeVol
  rw [exp_neg_historyCost_characterCost hu hv hw, mul_one_div]

theorem postedWeight_characterCost_eq {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (B' : ℕ) :
    postedWeight (characterCost u v w) B'
      = fun K : BoundedComplex B' => sizeWeight (characterSize u v w) K := by
  funext K
  exact postedWeight_characterCost hu hv hw B' K

theorem postedWeight_characterCost_sizeBlind (u v w : ℝ) :
    SizeBlind (postedWeight (characterCost u v w)) :=
  postedWeight_sizeBlind (characterCost_kindOnly u v w)

/-! ### The fugacity of the character cost, computed -/

theorem characterSize_atom_vertex (u v w : ℝ) : characterSize u v w 1 0 0 = u := by
  unfold characterSize gaugeVol
  norm_num [Nat.factorial]

theorem characterSize_atom_edge (u v w : ℝ) : characterSize u v w 1 1 0 = u * v := by
  unfold characterSize gaugeVol
  norm_num [Nat.factorial]

theorem characterSize_atom_tet (u v w : ℝ) : characterSize u v w 1 0 1 = u * w := by
  unfold characterSize gaugeVol
  norm_num [Nat.factorial]

/-- **THEOREM (the fugacity is unit exactly at the unit triple).**  So the family is faithfully
parametrized by its fugacity and the countermodel below is not hiding at the intended point. -/
theorem unitFugacity_characterSize_iff {u v w : ℝ} :
    UnitFugacity (characterSize u v w) ↔ (u = 1 ∧ v = 1 ∧ w = 1) := by
  unfold UnitFugacity
  rw [characterSize_atom_vertex, characterSize_atom_edge, characterSize_atom_tet]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [h1, one_mul] at h2 h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    norm_num

/-- The character cost satisfies the gluing premise at **every** eligible pair, not only at the
four carrier families, and for every positive triple.  `characterSize_shuffle` holds
unconditionally, and `gluesAt_of_shuffle` transports it wherever the automorphism counts
multiply. -/
theorem characterSize_gluesAt (u v w : ℝ) {B B' : ℕ} (K : BoundedComplex B)
    (L : BoundedComplex B')
    (haut : Nat.card (Aut (dunion K L)) = Nat.card (Aut K) * Nat.card (Aut L)) :
    GluesAt (characterSize u v w) K L :=
  gluesAt_of_shuffle _ K L haut (characterSize_shuffle u v w _ _ _ _ _ _)

/-! ## §3. The countermodel: posting structure plus gluing leaves the fugacity free -/

/-- **THEOREM (the countermodel, packaged).**  For every positive triple, the character cost is
kind-only, gauge-equivariant, has a size-blind posted weight equal to `characterSize u v w`, and
that size function satisfies the gluing law at all four carrier families and at every eligible
pair, with fugacity `(u, u·v, u·w)`.  Six conjuncts, all exact. -/
theorem characterCost_countermodel {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    KindOnly (characterCost u v w)
      ∧ Equivariant (characterCost u v w)
      ∧ SizeBlind (postedWeight (characterCost u v w))
      ∧ (∀ (B' : ℕ) (K : BoundedComplex B'),
          postedWeight (characterCost u v w) B' K = sizeWeight (characterSize u v w) K)
      ∧ CarrierShuffle (characterSize u v w)
      ∧ (characterSize u v w 1 0 0 = u ∧ characterSize u v w 1 1 0 = u * v
          ∧ characterSize u v w 1 0 1 = u * w) :=
  ⟨characterCost_kindOnly u v w, characterCost_equivariant u v w,
    postedWeight_characterCost_sizeBlind u v w,
    fun B' K => postedWeight_characterCost hu hv hw B' K,
    characterSize_carrierShuffle hu hv hw,
    ⟨characterSize_atom_vertex u v w, characterSize_atom_edge u v w,
      characterSize_atom_tet u v w⟩⟩

/-- **THE HEADLINE.**  The posting layer's structural conditions plus the gluing law do **not**
force unit sector fugacity.  For every positive triple other than `(1,1,1)` there is a letter cost
which is kind-only and gauge-equivariant, whose posted weight is size-blind and equal to the
size-blind weight of a size function satisfying the gluing law, and whose sector fugacity is not
unit.

This refutes the natural formalization of the no-go direction: "if the posted weight's class mass
as a function of sector sizes satisfies `CarrierShuffle`, the fugacity character is trivial".  It
is false, and the witness is a continuum of the best-behaved costs in the formalism.  The gluing
law does real work, but only on the *shape* of the fugacity: `closedForm` says it must be a
character rather than an arbitrary function of the three sizes.  Its value is untouched. -/
theorem gluing_and_posting_do_not_force_unit_fugacity {u v w : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hw : 0 < w) (hne : ¬ (u = 1 ∧ v = 1 ∧ w = 1)) :
    ∃ (c : LetterCost) (f : ℕ → ℕ → ℕ → ℝ),
      KindOnly c ∧ Equivariant c ∧ SizeBlind (postedWeight c)
        ∧ (∀ (B' : ℕ) (K : BoundedComplex B'), postedWeight c B' K = sizeWeight f K)
        ∧ CarrierShuffle f
        ∧ ¬ UnitFugacity f := by
  refine ⟨characterCost u v w, characterSize u v w, characterCost_kindOnly u v w,
    characterCost_equivariant u v w, postedWeight_characterCost_sizeBlind u v w,
    fun B' K => postedWeight_characterCost hu hv hw B' K,
    characterSize_carrierShuffle hu hv hw, ?_⟩
  intro hUF
  exact hne (unitFugacity_characterSize_iff.mp hUF)

/-- **THEOREM (what separates the countermodel from the intended point, exactly).**  The character
cost posts `mu` if and only if its triple is `(1,1,1)`.  So the condition that fails on the
countermodel is not any structural condition at the posting layer and not the gluing law; it is
posting the measure, which is the conclusion.  This is also the compatibility receipt against
`Gap2PostingCostDerivation.posting_cost_derives_mu`: that theorem's second hypothesis,
`NormalizedAtTheAtoms`, is what the countermodel violates, and by
`unitFugacity_iff_normalizedAtTheAtoms` that hypothesis is unit fugacity itself. -/
theorem characterCost_posts_mu_iff {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    (∀ (B' : ℕ) (K : BoundedComplex B'),
        classMass (postedWeight (characterCost u v w) B') (Quotient.mk (relabelSetoid B') K)
          = mu K)
      ↔ (u = 1 ∧ v = 1 ∧ w = 1) := by
  have hrw : ∀ (B' : ℕ) (K : BoundedComplex B'),
      classMass (postedWeight (characterCost u v w) B') (Quotient.mk (relabelSetoid B') K)
        = classMass (sizeWeight (characterSize u v w)) (Quotient.mk (relabelSetoid B') K) := by
    intro B' K
    rw [postedWeight_characterCost_eq hu hv hw B']
  constructor
  · intro h
    refine unitFugacity_characterSize_iff.mp ((unitFugacity_iff_mu_at_atoms _).mpr ?_)
    intro B' K hv' hi
    rw [← hrw B' K]
    exact h B' K
  · rintro ⟨h1, h2, h3⟩ B' K
    rw [hrw B' K, h1, h2, h3, ← gibbsSize_eq_characterSize_one]
    exact (classMass_sizeWeight_eq_mu_iff gibbsSize K).mpr rfl

/-! ## §4. Why the charged no-go direction restates its conclusion: the gluing hypothesis is idle -/

/-- **THEOREM (posting `mu` at three complexes forces unit fugacity, with no gluing).**  No
positivity, no `CarrierShuffle`, no posting-layer structure: three instances of "the class mass is
`mu`" give the premise directly.  This is the backward half of `unitFugacity_iff_mu_at_atoms`,
named separately because it is the theorem the charged no-go direction asks for, and because
seeing that it needs none of the other hypotheses is the point. -/
theorem posts_mu_at_atoms_forces_unit_fugacity (f : ℕ → ℕ → ℕ → ℝ)
    (h : ∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
      classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') K) = mu K) :
    UnitFugacity f :=
  (unitFugacity_iff_mu_at_atoms f).mpr h

/-- **THEOREM (posting `mu` everywhere forces the whole Gibbs size function).**  Same restatement
at
full strength: if a size-blind weight's class mass is `mu` at every complex, its size function is
`gibbsSize` at every size triple any complex realizes.  `closedForm` is not used and no gluing
premise appears. -/
theorem posts_mu_forces_gibbsSize (f : ℕ → ℕ → ℕ → ℝ)
    (h : ∀ (B' : ℕ) (K : BoundedComplex B'),
      classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') K) = mu K)
    (K : BoundedComplex B) : f K.nV K.nE K.nT = gibbsSize K.nV K.nE K.nT :=
  (classMass_sizeWeight_eq_mu_iff f K).mp (h B K)

/-- **THEOREM (the gluing hypothesis in the no-go is idle, and the no-go is therefore a
restatement).**  Two conjuncts, side by side so the shape cannot be misread.

1.  Posting `mu` at the three atoms forces unit fugacity **with no gluing hypothesis at all**.
    So the charged conditional "posts `mu` and glues, therefore unit fugacity" is true, and its
    gluing hypothesis does no work.
2.  The gluing law alone, together with every structural condition the posting layer can impose,
    is satisfied by size functions with fugacity as far from unit as one likes.  So the work in
    the conditional is being done entirely by the hypothesis that names `mu`.

A conditional whose only load-bearing hypothesis is three values of its own conclusion does not
derive anything.  That is the honest verdict on this route, and it is why the second conjunct is
the result worth banking. -/
theorem gluing_hypothesis_is_idle :
    (∀ f : ℕ → ℕ → ℕ → ℝ,
        (∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
            classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') K) = mu K) →
          UnitFugacity f)
      ∧ (∀ u v w : ℝ, 0 < u → 0 < v → 0 < w → ¬ (u = 1 ∧ v = 1 ∧ w = 1) →
          ∃ (c : LetterCost) (f : ℕ → ℕ → ℕ → ℝ),
            KindOnly c ∧ Equivariant c ∧ SizeBlind (postedWeight c)
              ∧ (∀ (B' : ℕ) (K : BoundedComplex B'), postedWeight c B' K = sizeWeight f K)
              ∧ CarrierShuffle f
              ∧ ¬ UnitFugacity f) :=
  ⟨fun f h => posts_mu_at_atoms_forces_unit_fugacity f h,
    fun _ _ _ hu hv hw hne => gluing_and_posting_do_not_force_unit_fugacity hu hv hw hne⟩

/-! ## §5. The charged first step: the tilted family, and why no mu-posting countermodel exists -/

/-- **THEOREM (the tilted family's posted weight is not size-blind at all).**  There is no size
function whose size-blind weight it equals, because a size-blind weight is relabeling-invariant and
the tilted posted weight is not (`postedWeight_tiltedCost_not_invariant`).  So `CarrierShuffle`,
which is a predicate on size functions, does not apply to it directly; the only object of the
tilted family that the gluing law can see is its class mass. -/
theorem postedWeight_tiltedCost_not_sizeWeight {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0) :
    ¬ ∃ f : ℕ → ℕ → ℕ → ℝ,
        ∀ K : BoundedComplex 3, postedWeight (tiltedCost t) 3 K = sizeWeight f K := by
  rintro ⟨f, hf⟩
  refine postedWeight_tiltedCost_not_invariant ht ht0 ?_
  intro K K' hEq
  rw [hf K, hf K', sizeWeight_invariant f hEq]

/-- **THEOREM (the tilted family's class mass IS the Gibbs one).**  At every cap and every
complex, because the family posts `mu` and `mu` is the class mass of the size-blind Gibbs weight.
The size function representing the tilted class mass is therefore `gibbsSize`. -/
theorem tiltedCost_classMass_eq_classMass_gibbsSize {t : ℝ} (ht : |t| < 1) (B' : ℕ)
    (K : BoundedComplex B') :
    classMass (postedWeight (tiltedCost t) B') (Quotient.mk (relabelSetoid B') K)
      = classMass (sizeWeight gibbsSize) (Quotient.mk (relabelSetoid B') K) := by
  rw [tiltedCost_posts_mu ht B' K]
  exact ((classMass_sizeWeight_eq_mu_iff gibbsSize K).mpr rfl).symm

/-- **THEOREM (the charged first step, answered).**  The tilted family's class mass satisfies the
gluing law, with unit fugacity, at every cap and every complex.  The answer is yes and it is
forced, not accidental: posting `mu` is exactly agreeing with the Gibbs class mass, and the Gibbs
size function glues and is unit.

So the tilted family is **not** a countermodel to the premise: it exhibits the premise.  The
underdetermination it established lives entirely at the labeled level, below the class mass, where
`CarrierShuffle` cannot see it. -/
theorem tiltedCost_classMass_glues_with_unit_fugacity {t : ℝ} (ht : |t| < 1) :
    (∀ (B' : ℕ) (K : BoundedComplex B'),
        classMass (postedWeight (tiltedCost t) B') (Quotient.mk (relabelSetoid B') K)
          = classMass (sizeWeight gibbsSize) (Quotient.mk (relabelSetoid B') K))
      ∧ CarrierShuffle gibbsSize
      ∧ UnitFugacity gibbsSize :=
  ⟨fun B' K => tiltedCost_classMass_eq_classMass_gibbsSize ht B' K,
    gibbsSize_carrierShuffle, gibbsSize_unitFugacity⟩

/-- **THEOREM (no mu-posting countermodel can exist).**  If a letter cost posts `mu` at the
three atoms, and its class mass there is represented by a size function, that size function has
unit fugacity.  Equivariant or not, kind-only or not, gluing or not.  The cost variable is a
spectator: the two hypotheses together are exactly `classMass (sizeWeight f) = mu` at the atoms,
so the content is the backward half of `unitFugacity_iff_mu_at_atoms` transported across the
representation.

This closes the countermodel direction as it was charged: "a cost that posts `mu` whose posted
weight is gluing-multiplicative with non-unit fugacity" is not merely unfound, it is
contradictory.  Which is why the real countermodel had to be sought after dropping the reference
to `mu`, and §3 is where it lives. -/
theorem no_posting_countermodel_with_nonunit_fugacity (c : LetterCost) (f : ℕ → ℕ → ℕ → ℝ)
    (hpost : ∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
      classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K) = mu K)
    (hrep : ∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
      classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K)
        = classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') K)) :
    UnitFugacity f := by
  refine (unitFugacity_iff_mu_at_atoms f).mpr ?_
  intro B' K hv hi
  rw [← hrep B' K hv hi]
  exact hpost B' K hv hi

/-! ## §6. The verdict, and the navigation index -/

/-- **THE VERDICT.**  Five parts, and together they settle flag 8's premise question in the
negative for this route while saying exactly what remains.

1.  Unit sector fugacity is equivalent to `mu` at the three atoms
    (`unitFugacity_iff_mu_at_atoms`), and equivalent to `NormalizedAtTheAtoms` on the labeled
    weight (`unitFugacity_iff_normalizedAtTheAtoms`).  The premise, the normalization, and three
    instances of the conclusion are one statement.
2.  Therefore posting `mu` forces the premise with no gluing hypothesis, so the charged no-go is a
    restatement rather than a derivation.
3.  The gluing law plus the posting layer's named structural conditions leaves the
    fugacity entirely free: a kind-only, gauge-equivariant letter cost realizes every positive
    triple, with a size-blind posted weight satisfying the gluing law at every eligible pair.
4.  No cost that posts `mu` can be a non-unit-fugacity countermodel; the contradiction is
    definitional.
5.  The tilted family of `Gap2NonEquivariantPosting` exhibits the premise rather than
    threatening it: its class mass is the Gibbs one and its underdetermination is invisible below
    the class mass. -/
theorem fugacity_posting_gluing_verdict :
    (∀ f : ℕ → ℕ → ℕ → ℝ, UnitFugacity f
        ↔ ∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
            classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') K) = mu K)
      ∧ (∀ f : ℕ → ℕ → ℕ → ℝ,
          UnitFugacity f ↔ NormalizedAtTheAtoms (fun _ K => sizeWeight f K))
      ∧ (∀ u v w : ℝ, 0 < u → 0 < v → 0 < w → ¬ (u = 1 ∧ v = 1 ∧ w = 1) →
          ∃ (c : LetterCost) (f : ℕ → ℕ → ℕ → ℝ),
            KindOnly c ∧ Equivariant c ∧ SizeBlind (postedWeight c)
              ∧ (∀ (B' : ℕ) (K : BoundedComplex B'), postedWeight c B' K = sizeWeight f K)
              ∧ CarrierShuffle f ∧ ¬ UnitFugacity f)
      ∧ (∀ (c : LetterCost) (f : ℕ → ℕ → ℕ → ℝ),
          (∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
              classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K) = mu K) →
            (∀ (B' : ℕ) (K : BoundedComplex B'), K.nV = 1 → K.nE + K.nT ≤ 1 →
                classMass (postedWeight c B') (Quotient.mk (relabelSetoid B') K)
                  = classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') K)) →
              UnitFugacity f)
      ∧ (CarrierShuffle gibbsSize ∧ UnitFugacity gibbsSize) :=
  ⟨unitFugacity_iff_mu_at_atoms, unitFugacity_iff_normalizedAtTheAtoms,
    fun _ _ _ hu hv hw hne => gluing_and_posting_do_not_force_unit_fugacity hu hv hw hne,
    fun c f hpost hrep => no_posting_countermodel_with_nonunit_fugacity c f hpost hrep,
    ⟨gibbsSize_carrierShuffle, gibbsSize_unitFugacity⟩⟩

/-- Navigation record.  Fields are assigned by hand; the evidence is the named theorem in each
docstring, not the `rfl` projection. -/
structure Index : Type where
  /-- Unit sector fugacity is exactly `mu` at the three atoms. -/
  premise_is_mu_at_the_atoms : Bool
  /-- It is also exactly `NormalizedAtTheAtoms`, so the library's two derivations share one
  premise. -/
  premise_is_the_atom_normalization : Bool
  /-- The kind-rate posting family IS the gluing derivation's three-constant residue. -/
  kindRates_is_the_residue : Bool
  /-- SETTLED (this module): posting structure plus the gluing law does NOT force unit
  fugacity, witnessed by a continuum of kind-only equivariant costs. -/
  posting_plus_gluing_leaves_fugacity_free : Bool
  /-- SETTLED: no cost that posts `mu` can be a non-unit-fugacity countermodel. -/
  no_mu_posting_countermodel : Bool
  /-- SETTLED: the tilted family exhibits the premise rather than threatening it. -/
  tilted_family_glues_with_unit_fugacity : Bool
  /-- NOT proved, and refuted for this route: that unit sector fugacity is derivable from
  posting-layer structure together with the gluing law. -/
  unit_fugacity_derived : Bool
  /-- NOT proved: that unit sector fugacity is underivable in general.  What is shown is that it
  is not reachable from these two inputs without naming the measure. -/
  unit_fugacity_shown_underivable : Bool

def index : Index where
  premise_is_mu_at_the_atoms := true
  premise_is_the_atom_normalization := true
  kindRates_is_the_residue := true
  posting_plus_gluing_leaves_fugacity_free := true
  no_mu_posting_countermodel := true
  tilted_family_glues_with_unit_fugacity := true
  unit_fugacity_derived := false
  unit_fugacity_shown_underivable := false

theorem index_premise_is_mu_at_atoms : index.premise_is_mu_at_the_atoms = true := rfl
theorem index_fugacity_free : index.posting_plus_gluing_leaves_fugacity_free = true := rfl
theorem index_no_countermodel : index.no_mu_posting_countermodel = true := rfl
theorem index_premise_not_derived : index.unit_fugacity_derived = false := rfl
theorem index_not_shown_underivable : index.unit_fugacity_shown_underivable = false := rfl

end

#print axioms gibbsWeight_eq_gibbsSize
#print axioms classMass_sizeWeight_eq_mu_iff
#print axioms unitFugacity_iff_mu_at_atoms
#print axioms unitFugacity_iff_normalizedAtTheAtoms
#print axioms characterCost_kindOnly
#print axioms characterCost_equivariant
#print axioms exp_neg_historyCost_characterCost
#print axioms postedWeight_characterCost
#print axioms unitFugacity_characterSize_iff
#print axioms characterSize_gluesAt
#print axioms characterCost_countermodel
#print axioms gluing_and_posting_do_not_force_unit_fugacity
#print axioms characterCost_posts_mu_iff
#print axioms posts_mu_at_atoms_forces_unit_fugacity
#print axioms posts_mu_forces_gibbsSize
#print axioms gluing_hypothesis_is_idle
#print axioms postedWeight_tiltedCost_not_sizeWeight
#print axioms tiltedCost_classMass_eq_classMass_gibbsSize
#print axioms tiltedCost_classMass_glues_with_unit_fugacity
#print axioms no_posting_countermodel_with_nonunit_fugacity
#print axioms fugacity_posting_gluing_verdict

end Gap2FugacityPostingGluing
end SevenGaps
end Gravity
end IndisputableMonolith
