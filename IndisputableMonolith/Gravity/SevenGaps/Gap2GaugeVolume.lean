import IndisputableMonolith.Gravity.SevenGaps.MeasureSubstrateBlocker

/-!
# Gap 2: the gauge volume is the order of the sector's relabeling group

## What this module does

`ExactShellGaugePreflight` derives `mu K = 1/|Aut K|` from a MODEL premise it
calls the *pair-counting principle*: the class mass is labeled copies per unit
of gauge volume, where the gauge volume `pairCount K` counts pairs
`(K', r)` of an orbit member and a relabeling witness.  That premise reads as
an invented bookkeeping convention, and `MeasureSubstrateBlocker` records the
open task as "derive normalized gauge counting from richer ledger structure".

This module identifies the premise by computing the gauge volume:

  `pairCount K = (K.nV)! * (K.nE)! * (K.nT)!`

The gauge volume carries **no information about the complex**: it is the order of the
full relabeling group of `K`'s size sector, `S_nV × S_nE × S_nT`.  So the premise can
be restated without the invented quantity, as

  class weight  =  (labeled presentations of the class) / (relabelings in the sector)

and `labelDensity_eq_mu` proves this ratio is exactly `1/|Aut K|`, the discrete
Faddeev-Popov form.

## What the premise is NOT (revised 2026-07-28 after adversarial review)

An earlier version of this header called the premise **label indifference**, "each
labeling counted once and none preferred", and treated a size-only divisor as
physically inert.  A four-seat adversarial review at maximum effort returned the same
objection from all four seats, and it is correct.  §6c now proves it:

* `fugacityWeight_invariant`: for **any** function `a` of the three index sizes, the
  weight `a(sizes)/(nV! nE! nT!)` is relabeling-invariant.  So label indifference,
  honestly formalized as "the weight is a class function", is satisfied by an entire
  family and does not select the Gibbs weight.  The name undershoots the premise.
* `gaugeCounting_iff_fugacity_one`: the gauge-counting principle is exactly the member
  of that family with `a ≡ 1`.  So the premise is the choice of **unit cross-sector
  fugacity**: one positive real per size sector, set to one.
* `fugacity_absorbs_into_action`: that factor can be moved between the measure and the
  action, `S ↦ S - log a`, without changing any weighted sum.  Only the product is
  determined, so "the measure is forced" is relative to a booking convention.

The residue is therefore not inert.  A size-only divisor is a reweighting *between*
sectors, and in a discrete gravity path sum it competes with the bare cosmological
constant.  What genuinely closed is the *localization* of the premise: from an opaque
invented quantity to one positive function on the sector lattice, with its group made
explicit.

## Status tiers (honest tagging)

**THEOREM (proved below, 0 sorry, 0 new axioms beyond the base triple):**
* `pairCount_eq_factorials`: the gauge volume is `nV! * nE! * nT!`.
* `pairCount_congr_sizes`: hence the gauge volume is a function of the index
  sizes only, so it cannot distinguish complexes within a size sector.
* `orbitCard_mul_autCard`: orbit-stabilizer in sector form,
  `|orbit K| * |Aut K| = nV! * nE! * nT!` (the factorization
  `pairCount = orbitCard * autCard` is `ExactShellGaugePreflight`'s; the new
  content is the closed form of the right-hand side).
* `labelDensity_eq_mu`: the count of labeled presentations of `K` per relabeling
  in the sector equals `mu K = 1/|Aut K|`.
* `gaugeCounting_iff_labelIndifference`: `GaugeCountingPrinciple ν` holds
  exactly when `ν` is that label density.  An equivalence, so it restates the
  premise without discharging it.
* §6c: the residual freedom in closed form, as above.

**MODEL:** any reading of the above as licensing the premise.  The equivalences are
theorems; the claim that a standard name ("Gibbs", "Faddeev-Popov") supplies a reason
is not, and the four-seat review was unanimous on that point.

## The premise reduced, not just named (§6d)

The review's two strongest seats converged on the same route as the only one that
would *close* rather than relocate: the shuffle identity
`f(m+n) · C(m+n, m) = f(m) · f(n)`.  §6d proves it.

* `gluingLaw_forces_inverse_factorial`: the inverse factorial is the **unique**
  size-indexed weight satisfying that identity, given unit weight on the empty and
  singleton index sets.
* `gluingLaw_gives_gaugeCounting`: therefore the gluing law **implies** the
  gauge-counting principle.
* `inverseFactorial_gluingLaw`: and the law is satisfiable, so the implication is not
  vacuous.

So the debt changes shape.  What the theory owes is no longer a normalization ("the
sector fugacity is one") but a locality statement: the weight of an assembled
configuration times the number of ways to interleave the parts' labels equals the
product of the parts' weights.  That is a better place for the debt to sit, because
recognition cost is additive over independent parts, which supplies the right-hand
side for free; the open question is whether the ledger supplies the interleaving count
on the left.

**OPEN:** derivation of the gluing law from recognition structure.
`Gap2LedgerSiteBlindness` blocks one route, reading the measure off ledger cost values
under a free encoding.  Note the scope: that is a proof of *underdetermination* by cost
values, not a proof that no cost-based argument exists.  A second route the review
named and nobody has attacked: stationarity of the ledger's own *move set* under
insertion, which would force `π(N+1)/π(N) = 1/(N+1)` from equirated names rather than
from any cost value.

**Strength.**  The identification is an equality of natural numbers, not an agreement
to a tolerance, and the uniqueness in §6 quantifies over every relabeling-invariant
real weight.  But that uniqueness inherits its absolute normalization from the equality
form of `GaugeCountingPrinciple`: replace the equality by `∃ λ > 0` and a one-parameter
family per sector survives.  The absence of a free scale is bookkeeping, not rigidity.

**Refuted objection, recorded for the next reader.**  The review's highest-confidence
single claim (0.8) was that `nE!` and `nT!` are artifacts of a carrier without
well-formedness conditions, and that imposing injectivity on `edgeVerts` and `tetVerts`
would collapse `pairCount` to `nV!`.  The carrier does indeed carry no such conditions,
but the inference fails, and `QG/attack_gap2_20260728/rigidity_probe.lean` refutes it
with a compiled witness: a complex with injective `edgeVerts` and `tetVerts` whose pair
count is `4`, not `nV! = 2`.  The reason is that `pairCount` ranges over *targets*, and
permuting cell names produces a different target; injectivity pins `eEquiv` only with
the target held fixed, which is `Aut K`, not the pair space.

## Proof notes
No `decide` / `native_decide`; the bijection to the sector group is explicit.
The dependent-size transport is discharged by destructuring the target complex
and substituting the three size equalities, after which every cast is `rfl`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2GaugeVolume

open PathSumMeasure
open ExactShellGaugePreflight

variable {B : ℕ}

/-! ## §1. Index sizes are relabeling invariants -/

/-- A relabeling forces equal vertex counts. -/
theorem size_v {K K' : BoundedComplex B} (r : Relabel K K') : K.nV = K'.nV := by
  simpa using Fintype.card_congr r.vEquiv

/-- A relabeling forces equal edge counts. -/
theorem size_e {K K' : BoundedComplex B} (r : Relabel K K') : K.nE = K'.nE := by
  simpa using Fintype.card_congr r.eEquiv

/-- A relabeling forces equal tetrahedron counts. -/
theorem size_t {K K' : BoundedComplex B} (r : Relabel K K') : K.nT = K'.nT := by
  simpa using Fintype.card_congr r.tEquiv

/-! ## §2. The relabeling group of a size sector, and the pushforward -/

/-- The relabeling group of `K`'s size sector: independent permutations of the
vertex, edge and tetrahedron index sets.  This is the gauge group of the
labeling, and nothing about `K` beyond its three sizes enters. -/
abbrev SectorGroup (K : BoundedComplex B) : Type :=
  Equiv.Perm (Fin K.nV) × Equiv.Perm (Fin K.nE) × Equiv.Perm (Fin K.nT)

/-- Pushforward of `K` along a triple of index permutations: relabel the data,
keep the sizes. -/
def push (K : BoundedComplex B) (g : SectorGroup K) : BoundedComplex B where
  nV := K.nV
  nE := K.nE
  nT := K.nT
  hV := K.hV
  hE := K.hE
  hT := K.hT
  edgeVerts := fun e => Prod.map g.1 g.1 (K.edgeVerts (g.2.1.symm e))
  tetVerts := fun t i => g.1 (K.tetVerts (g.2.2.symm t) i)

/-- The canonical relabeling witness from `K` onto its pushforward. -/
def pushRel (K : BoundedComplex B) (g : SectorGroup K) : Relabel K (push K g) where
  vEquiv := g.1
  eEquiv := g.2.1
  tEquiv := g.2.2
  edge_comm := by intro e; simp [push]
  tet_comm := by intro t i; simp [push]

/-- Every pushforward is gauge-equivalent to the original. -/
theorem equivalent_push (K : BoundedComplex B) (g : SectorGroup K) :
    Equivalent K (push K g) := ⟨pushRel K g⟩

/-! ## §3. The (target, witness) pair space is the sector group

The bijection is the mathematical content of this module: a pair
`(K', r : Relabel K K')` is *nothing more* than a triple of index
permutations, because the commutation conditions pin `K'` to be the
pushforward of `K` along that triple. -/

/-- The total space of (target, witness) pairs out of `K`. -/
abbrev PairSpace (K : BoundedComplex B) : Type := Σ K' : BoundedComplex B, Relabel K K'

/-- Restricting the target to the orbit changes nothing: the witness type is
empty off the orbit, and on the orbit the subtype proof is irrelevant. -/
def pairSpaceEquiv (K : BoundedComplex B) :
    (Σ K' : {K' : BoundedComplex B // Equivalent K K'}, Relabel K K'.val) ≃ PairSpace K where
  toFun p := ⟨p.1.val, p.2⟩
  invFun p := ⟨⟨p.1, ⟨p.2⟩⟩, p.2⟩
  left_inv p := by obtain ⟨⟨K', h⟩, r⟩ := p; rfl
  right_inv p := by obtain ⟨K', r⟩ := p; rfl

/-- A size equality that is reflexive transports trivially. -/
theorem finCongr_self {n : ℕ} (h : n = n) : finCongr h = Equiv.refl (Fin n) := by
  ext x
  simp

/-- Read a witness as an element of the sector group: legitimate because the
sizes agree (§1). -/
def toSector {K : BoundedComplex B} (p : PairSpace K) : SectorGroup K :=
  (p.2.vEquiv.trans (finCongr (size_v p.2)).symm,
   p.2.eEquiv.trans (finCongr (size_e p.2)).symm,
   p.2.tEquiv.trans (finCongr (size_t p.2)).symm)

/-- Build a pair from a sector group element by pushing forward. -/
def ofSector (K : BoundedComplex B) (g : SectorGroup K) : PairSpace K :=
  ⟨push K g, pushRel K g⟩

theorem toSector_ofSector (K : BoundedComplex B) (g : SectorGroup K) :
    toSector (ofSector K g) = g :=
  Prod.ext (Equiv.ext fun _ => Fin.ext rfl)
    (Prod.ext (Equiv.ext fun _ => Fin.ext rfl) (Equiv.ext fun _ => Fin.ext rfl))

/-- **The pinning lemma.**  A relabeling witness determines its own target: the
commutation conditions force `K'` to be the pushforward of `K` along the
witness's index permutations.  Stated with value-level hypotheses (`Fin.val`)
so that no dependent-size transport appears in the statement. -/
theorem target_eq_push {K K' : BoundedComplex B} (r : Relabel K K') (g : SectorGroup K)
    (hv : ∀ x : Fin K.nV, (r.vEquiv x).val = (g.1 x).val)
    (he : ∀ x : Fin K.nE, (r.eEquiv x).val = (g.2.1 x).val)
    (ht : ∀ x : Fin K.nT, (r.tEquiv x).val = (g.2.2 x).val) :
    K' = push K g := by
  have hnv : K.nV = K'.nV := size_v r
  have hne : K.nE = K'.nE := size_e r
  have hnt : K.nT = K'.nT := size_t r
  obtain ⟨nV', nE', nT', hV', hE', hT', ev', tv'⟩ := K'
  subst hnv
  subst hne
  subst hnt
  have hvv : ∀ z, r.vEquiv z = g.1 z := fun z => Fin.ext (hv z)
  have hev : ev' = fun x => Prod.map g.1 g.1 (K.edgeVerts (g.2.1.symm x)) := by
    funext x
    have hx : r.eEquiv (g.2.1.symm x) = x := by
      apply Fin.ext
      rw [he]
      simp
    have h : ev' x = Prod.map r.vEquiv r.vEquiv (K.edgeVerts (g.2.1.symm x)) := by
      have h0 := r.edge_comm (g.2.1.symm x)
      rw [hx] at h0
      exact h0
    rw [h]
    simp [Prod.map, hvv]
  have htv : tv' = fun x i => g.1 (K.tetVerts (g.2.2.symm x) i) := by
    funext x i
    have hx : r.tEquiv (g.2.2.symm x) = x := by
      apply Fin.ext
      rw [ht]
      simp
    have h : tv' x i = r.vEquiv (K.tetVerts (g.2.2.symm x) i) := by
      have h0 := r.tet_comm (g.2.2.symm x) i
      rw [hx] at h0
      exact h0
    rw [h, hvv]
  rw [hev, htv]
  rfl

theorem ofSector_toSector (K : BoundedComplex B) (p : PairSpace K) :
    ofSector K (toSector p) = p := by
  obtain ⟨K', r⟩ := p
  obtain ⟨g, hg⟩ : ∃ g : SectorGroup K, g = toSector (⟨K', r⟩ : PairSpace K) := ⟨_, rfl⟩
  have hv : ∀ x : Fin K.nV, (r.vEquiv x).val = (g.1 x).val := by
    intro x; rw [hg]; rfl
  have he : ∀ x : Fin K.nE, (r.eEquiv x).val = (g.2.1 x).val := by
    intro x; rw [hg]; rfl
  have ht : ∀ x : Fin K.nT, (r.tEquiv x).val = (g.2.2 x).val := by
    intro x; rw [hg]; rfl
  have hK : K' = push K g := target_eq_push r g hv he ht
  subst hK
  have hrel : pushRel K g = r :=
    Relabel.ext (Equiv.ext fun x => (Fin.ext (hv x)).symm)
      (Equiv.ext fun x => (Fin.ext (he x)).symm)
      (Equiv.ext fun x => (Fin.ext (ht x)).symm)
  rw [← hg]
  exact congrArg (fun w => (⟨push K g, w⟩ : PairSpace K)) hrel

/-- **THEOREM (the pair space is the gauge group).**  The (target, witness)
pairs out of `K` are in explicit bijection with the triples of index
permutations. -/
def sectorEquiv (K : BoundedComplex B) : PairSpace K ≃ SectorGroup K where
  toFun := toSector
  invFun := ofSector K
  left_inv := ofSector_toSector K
  right_inv := toSector_ofSector K

/-! ## §4. The gauge volume is a factorial -/

/-- The order of the sector group. -/
theorem card_sectorGroup (K : BoundedComplex B) :
    Nat.card (SectorGroup K)
      = Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) := by
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]

/-- **THEOREM (the gauge volume is the sector group order).**  The quantity
`ExactShellGaugePreflight` calls the gauge volume of `K`'s orbit is exactly
`nV! * nE! * nT!`: the number of ways to label the index sets.  It contains no
information about the incidence data of `K`. -/
theorem pairCount_eq_factorials (K : BoundedComplex B) :
    pairCount K = Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) := by
  unfold pairCount
  rw [Nat.card_congr (pairSpaceEquiv K), Nat.card_congr (sectorEquiv K), card_sectorGroup]

/-- **COROLLARY.**  The gauge volume is a function of the three index sizes
alone.  So dividing by it cannot express a physical choice about the complex;
it is a normalization of the label count. -/
theorem pairCount_congr_sizes {K K' : BoundedComplex B}
    (hV : K.nV = K'.nV) (hE : K.nE = K'.nE) (hT : K.nT = K'.nT) :
    pairCount K = pairCount K' := by
  rw [pairCount_eq_factorials, pairCount_eq_factorials, hV, hE, hT]

/-- **THEOREM (orbit-stabilizer, sector form).**  Labeled presentations times
automorphisms equals labelings. -/
theorem orbitCard_mul_autCard (K : BoundedComplex B) :
    gaugeOrbitCard K * Nat.card (Aut K)
      = Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) := by
  rw [← pairCount_eq_orbitCard_mul_autCard, pairCount_eq_factorials]

/-! ## §5. The premise, named: label indifference -/

/-- The **label density** of `K`: the number of distinct labeled complexes in `K`'s
class, divided by the number of relabelings available in the sector.  Written with no
reference to `Aut`, `mu`, or relabeling witnesses: only orbit size and the factorials
of the index sizes.

**Not a probability.**  Adversarial review (2026-07-28) correctly flagged an earlier
gloss here, "the fraction of available labelings that present the class", as false:
`equivalent_push` proves every sector permutation sends `K` to a complex in the same
class, so that fraction is `1`.  The numerator counts *objects* and the denominator
counts *transformations*, which is groupoid cardinality, not a fraction of a sample
space. -/
noncomputable def labelDensity (K : BoundedComplex B) : ℝ :=
  (gaugeOrbitCard K : ℝ)
    / ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)

/-- **THEOREM (Gibbs identification).**  The label density is exactly the
symmetry-factor measure: `|orbit| / (number of labelings) = 1/|Aut|`. -/
theorem labelDensity_eq_mu (K : BoundedComplex B) : labelDensity K = mu K := by
  have hpos : (0 : ℝ) < (gaugeOrbitCard K : ℝ) := by
    exact_mod_cast gaugeOrbitCard_pos K
  unfold labelDensity mu
  rw [← orbitCard_mul_autCard K, Nat.cast_mul, div_mul_eq_div_div, div_self hpos.ne']

/-- **THEOREM (premise identification).**  The gauge-counting principle, the
undischarged MODEL premise of the Gap-2 measure derivation, holds exactly when the
class weight is the label density: the orbit's size over the sector's relabeling
count, stated without `Aut`, `mu`, or witnesses.

This is an equivalence of two ways of writing the same premise, so it identifies the
premise without discharging it.  §6c proves that the name "label indifference"
undershoots it. -/
theorem gaugeCounting_iff_labelIndifference (ν : TriangulationClass B → ℝ) :
    MeasureSubstrateBlocker.GaugeCountingPrinciple ν ↔
      ∀ K : BoundedComplex B,
        ν (Quotient.mk (relabelSetoid B) K) = labelDensity K := by
  rw [MeasureSubstrateBlocker.gaugeCountingPrinciple_iff_mu_on_representatives]
  constructor
  · intro h K
    rw [h K, labelDensity_eq_mu]
  · intro h K
    rw [h K, labelDensity_eq_mu]

/-- **THEOREM (the gauge volume carries no incidence information).**  Two complexes
with the same index sizes are divided by the same gauge volume, so the divisor cannot
express any choice that distinguishes complexes *within* a size sector.

**This does not make the divisor inert**, and an earlier docstring here claimed it
did.  A size-only divisor is exactly a reweighting *between* sectors, which in a
discrete path sum is physically consequential: it competes with the bare cosmological
constant.  §6c gives the surviving freedom in closed form. -/
theorem gaugeVolume_is_size_data (K K' : BoundedComplex B)
    (hV : K.nV = K'.nV) (hE : K.nE = K'.nE) (hT : K.nT = K'.nT) :
    pairCount K = pairCount K' ∧
      pairCount K = Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) :=
  ⟨pairCount_congr_sizes hV hE hT, pairCount_eq_factorials K⟩

/-! ## §6. The premise at the substrate level: the Gibbs weight

§5 states the premise as a property of the class weight.  The substrate does not
work with classes: it works with labeled configurations.  So the question is
which *labeled* weight induces the RS measure.  The answer is unique and it is
the Gibbs weight: each labeled complex enters with the reciprocal of the number
of ways to label it. -/

open scoped Classical in
/-- The class mass induced by a labeled weight: the total weight of the labeled
configurations that present the class. -/
noncomputable def classMass (w : BoundedComplex B → ℝ) (c : TriangulationClass B) : ℝ :=
  ∑ K : BoundedComplex B, if Quotient.mk (relabelSetoid B) K = c then w K else 0

/-- A class representative is equivalent to any complex presenting the class. -/
theorem equivalent_out (K : BoundedComplex B) :
    Equivalent (Quotient.out (Quotient.mk (relabelSetoid B) K)) K :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (relabelSetoid B) K))

/-- The number of labeled complexes presenting a class is the orbit count. -/
theorem fiber_card (c : TriangulationClass B) :
    Nat.card {K : BoundedComplex B // Quotient.mk (relabelSetoid B) K = c}
      = orbitCardClass c := by
  have hc : Quotient.mk (relabelSetoid B) (Quotient.out c) = c := Quotient.out_eq c
  have e : {K : BoundedComplex B // Quotient.mk (relabelSetoid B) K = c}
      ≃ {K' : BoundedComplex B // Equivalent (Quotient.out c) K'} :=
    Equiv.subtypeEquivRight fun K =>
      ⟨fun hK => Quotient.exact (hc.trans hK.symm),
       fun hE => (Quotient.sound hE).symm.trans hc⟩
  rw [Nat.card_congr e]
  conv_rhs => rw [← hc]
  rfl

/-- **THEOREM.**  A relabeling-invariant labeled weight induces the class mass
`orbit size times the common weight of the orbit`. -/
theorem classMass_of_invariant (w : BoundedComplex B → ℝ)
    (hinv : ∀ K K', Equivalent K K' → w K = w K') (c : TriangulationClass B) :
    classMass w c = (orbitCardClass c : ℝ) * w (Quotient.out c) := by
  classical
  have hc : Quotient.mk (relabelSetoid B) (Quotient.out c) = c := Quotient.out_eq c
  have hstep : ∀ K : BoundedComplex B,
      (if Quotient.mk (relabelSetoid B) K = c then w K else 0)
        = (if Quotient.mk (relabelSetoid B) K = c then (1 : ℝ) else 0)
            * w (Quotient.out c) := by
    intro K
    by_cases h : Quotient.mk (relabelSetoid B) K = c
    · simp only [h, if_true, one_mul]
      exact hinv K (Quotient.out c) (Quotient.exact (h.trans hc.symm))
    · simp only [h, if_false, zero_mul]
  have hcount : ∑ K : BoundedComplex B,
      (if Quotient.mk (relabelSetoid B) K = c then (1 : ℝ) else 0)
        = (orbitCardClass c : ℝ) := by
    rw [Finset.sum_boole, ← fiber_card c, Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold classMass
  rw [Finset.sum_congr rfl fun K _ => hstep K, ← Finset.sum_mul, hcount]

/-- The **Gibbs weight** of a labeled complex: one unit of recognition shared
evenly over the ways of labeling it.  This is the premise, stated at the
substrate level, with no reference to automorphisms, orbits, or classes. -/
noncomputable def gibbsWeight (K : BoundedComplex B) : ℝ :=
  1 / ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)

/-- The Gibbs weight is relabeling-invariant, because the index sizes are. -/
theorem gibbsWeight_invariant {K K' : BoundedComplex B} (h : Equivalent K K') :
    gibbsWeight K = gibbsWeight K' := by
  obtain ⟨r⟩ := h
  unfold gibbsWeight
  rw [size_v r, size_e r, size_t r]

theorem gaugeVolume_pos (K : BoundedComplex B) :
    (0 : ℝ) < ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ) := by
  have h : 0 < Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) :=
    Nat.mul_pos K.nV.factorial_pos (Nat.mul_pos K.nE.factorial_pos K.nT.factorial_pos)
  exact_mod_cast h

/-- **THEOREM (substrate premise, sufficiency).**  The Gibbs weight induces
exactly the RS path-sum measure: its class mass satisfies the gauge-counting
principle, hence equals `1/|Aut|` on every class. -/
theorem gibbs_induces_measure (B : ℕ) :
    MeasureSubstrateBlocker.GaugeCountingPrinciple
      (classMass (gibbsWeight : BoundedComplex B → ℝ)) := by
  intro c
  rw [classMass_of_invariant _ (fun _ _ h => gibbsWeight_invariant h) c]
  have hK := Quotient.out_eq c
  have hpc : (pairCountClass c : ℝ)
      = ((Nat.factorial (Quotient.out c).nV
          * (Nat.factorial (Quotient.out c).nE * Nat.factorial (Quotient.out c).nT) : ℕ) : ℝ) := by
    conv_lhs => rw [← hK]
    rw [pairCountClass_mk, pairCount_eq_factorials]
  rw [hpc]
  unfold gibbsWeight
  field_simp

/-- **THEOREM (substrate premise, uniqueness).**  Among relabeling-invariant
labeled weights, the Gibbs weight is the ONLY one whose class mass satisfies the
gauge-counting principle.  So the premise behind the Gap-2 measure is exactly:
a labeled configuration carries the reciprocal of its label count. -/
theorem invariant_weight_gives_measure_iff (w : BoundedComplex B → ℝ)
    (hinv : ∀ K K', Equivalent K K' → w K = w K') :
    MeasureSubstrateBlocker.GaugeCountingPrinciple (classMass w) ↔
      ∀ K : BoundedComplex B, w K = gibbsWeight K := by
  constructor
  · intro h K
    have hc := h (Quotient.mk (relabelSetoid B) K)
    rw [classMass_of_invariant w hinv] at hc
    have hwout : w (Quotient.out (Quotient.mk (relabelSetoid B) K)) = w K :=
      hinv _ _ (equivalent_out K)
    rw [hwout, pairCountClass_mk, pairCount_eq_factorials, orbitCardClass_mk] at hc
    have horb : (0 : ℝ) < (gaugeOrbitCard K : ℝ) := by
      exact_mod_cast gaugeOrbitCard_pos K
    have hvol := gaugeVolume_pos K
    have h1 : (gaugeOrbitCard K : ℝ)
        * (w K * ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ))
        = (gaugeOrbitCard K : ℝ) * 1 := by
      rw [mul_one, ← mul_assoc]
      exact hc
    have h2 := mul_left_cancel₀ horb.ne' h1
    unfold gibbsWeight
    rw [eq_div_iff hvol.ne']
    exact h2
  · intro h
    have hw : w = (gibbsWeight : BoundedComplex B → ℝ) := funext h
    rw [hw]
    exact gibbs_induces_measure B

/-- **THEOREM (the premise in one line).**  The RS path-sum measure is uniform
labeled counting divided by the number of labelings.  `classMass (fun _ => 1)` is
the count of labeled presentations of the class, and multiplying the Gibbs class
mass by the sector's gauge volume returns exactly that count.  This is the
discrete Faddeev-Popov statement: sum over labeled configurations, divide once by
the gauge volume. -/
theorem measure_is_uniform_count_over_gauge_volume (c : TriangulationClass B) :
    classMass (gibbsWeight : BoundedComplex B → ℝ) c
        * ((Nat.factorial (Quotient.out c).nV
            * (Nat.factorial (Quotient.out c).nE
              * Nat.factorial (Quotient.out c).nT) : ℕ) : ℝ)
      = classMass (fun _ => (1 : ℝ)) c := by
  rw [classMass_of_invariant _ (fun _ _ h => gibbsWeight_invariant h) c,
    classMass_of_invariant _ (fun _ _ _ => rfl) c]
  have hvol := gaugeVolume_pos (Quotient.out c)
  unfold gibbsWeight
  field_simp

/-! ## §6b. Where the premise actually bites: across sectors, not inside one

The premise is often read as answering "why `1/|Aut|` and not the uniform class
weight".  Inside one size sector it does not have to: the ratio of two class
weights is forced to be the ratio of their labeled-presentation counts, which is
what one posting per labeled configuration already gives, with no normalization
chosen.  What the premise fixes is the RELATIVE normalization of different size
sectors, and that factor is the ratio of gauge volumes. -/

/-- **THEOREM (inside a sector the measure is uniform labeled counting).**  If `ν`
satisfies the gauge-counting principle then for any two complexes with the same
index sizes the class weights are in the ratio of the labeled-presentation
counts.  No normalization enters: this is exactly what counting labeled
configurations equally gives. -/
theorem sector_ratio_is_orbit_ratio (ν : TriangulationClass B → ℝ)
    (h : MeasureSubstrateBlocker.GaugeCountingPrinciple ν)
    (K K' : BoundedComplex B)
    (hV : K.nV = K'.nV) (hE : K.nE = K'.nE) (hT : K.nT = K'.nT) :
    ν (Quotient.mk (relabelSetoid B) K) * (gaugeOrbitCard K' : ℝ)
      = ν (Quotient.mk (relabelSetoid B) K') * (gaugeOrbitCard K : ℝ) := by
  have hk := h (Quotient.mk (relabelSetoid B) K)
  have hk' := h (Quotient.mk (relabelSetoid B) K')
  rw [pairCountClass_mk, orbitCardClass_mk, pairCount_eq_factorials] at hk
  rw [pairCountClass_mk, orbitCardClass_mk, pairCount_eq_factorials] at hk'
  rw [hV, hE, hT] at hk
  have hvol := gaugeVolume_pos K'
  have h1 : (ν (Quotient.mk (relabelSetoid B) K) * (gaugeOrbitCard K' : ℝ))
      * ((Nat.factorial K'.nV * (Nat.factorial K'.nE * Nat.factorial K'.nT) : ℕ) : ℝ)
      = (ν (Quotient.mk (relabelSetoid B) K') * (gaugeOrbitCard K : ℝ))
      * ((Nat.factorial K'.nV * (Nat.factorial K'.nE * Nat.factorial K'.nT) : ℕ) : ℝ) := by
    calc (ν (Quotient.mk (relabelSetoid B) K) * (gaugeOrbitCard K' : ℝ))
          * ((Nat.factorial K'.nV * (Nat.factorial K'.nE * Nat.factorial K'.nT) : ℕ) : ℝ)
        = (ν (Quotient.mk (relabelSetoid B) K)
            * ((Nat.factorial K'.nV
                * (Nat.factorial K'.nE * Nat.factorial K'.nT) : ℕ) : ℝ))
          * (gaugeOrbitCard K' : ℝ) := by ring
      _ = (gaugeOrbitCard K : ℝ) * (gaugeOrbitCard K' : ℝ) := by rw [hk]
      _ = (ν (Quotient.mk (relabelSetoid B) K')
            * ((Nat.factorial K'.nV
                * (Nat.factorial K'.nE * Nat.factorial K'.nT) : ℕ) : ℝ))
          * (gaugeOrbitCard K : ℝ) := by rw [hk']; ring
      _ = _ := by ring
  exact mul_right_cancel₀ hvol.ne' h1

/-- **THEOREM (what the premise adds).**  The class weight given by one posting
per labeled configuration is the labeled-presentation count, and it equals the
gauge-counting weight multiplied by the sector's gauge volume.  So the entire
content of the premise beyond within-sector counting is the cross-sector factor
`1/(nV! nE! nT!)`, which is extensive in the index sizes and is therefore the
kind of term an action carries, not a statement about the class. -/
theorem uniformLabeled_eq_mu_times_gaugeVolume (K : BoundedComplex B) :
    (gaugeOrbitCard K : ℝ)
      = mu K * ((Nat.factorial K.nV
          * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ) := by
  have haut : (0 : ℝ) < (Nat.card (Aut K) : ℝ) := by exact_mod_cast autCard_pos K
  have hfact : ((Nat.factorial K.nV
      * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)
      = (gaugeOrbitCard K : ℝ) * (Nat.card (Aut K) : ℝ) := by
    rw [← orbitCard_mul_autCard K]
    push_cast
    ring
  rw [hfact]
  unfold mu
  field_simp

/-! ## §6c. The exact residual freedom: one number per size sector

An adversarial review of this module (2026-07-28, four independent seats at maximum
effort) returned the same objection from all four, and it lands.  `pairCount_congr_sizes`
shows the divisor carries no incidence information, but it does **not** follow that
dividing by it is physically inert, because a size-dependent normalization reweights
whole size sectors against each other, and in a discrete gravity path sum the
size-dependence of the measure competes with the bare cosmological constant.

Two seats independently prescribed the same repair: formalize the family of weights
that label indifference actually permits, and prove that the gauge-counting principle
is the single member with unit normalization.  That is what this section does.  The
conclusion is that "label indifference" **undershoots** the premise: every member of
the family below is relabeling-invariant, so indifference does not select one. -/

/-- A **sector fugacity**: any assignment of a real number to the three index sizes.
Divided by the gauge volume it gives a labeled weight. -/
noncomputable def fugacityWeight (a : ℕ → ℕ → ℕ → ℝ) (K : BoundedComplex B) : ℝ :=
  a K.nV K.nE K.nT
    / ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)

/-- **THEOREM (indifference does not constrain the fugacity).**  Every sector
fugacity gives a relabeling-invariant labeled weight.  So label indifference in the
honest sense, that the weight is a class function, is satisfied by the whole family
and cannot pick out the Gibbs weight. -/
theorem fugacityWeight_invariant (a : ℕ → ℕ → ℕ → ℝ) {K K' : BoundedComplex B}
    (h : Equivalent K K') : fugacityWeight a K = fugacityWeight a K' := by
  obtain ⟨r⟩ := h
  unfold fugacityWeight
  rw [size_v r, size_e r, size_t r]

/-- The Gibbs weight is the member of the family with fugacity identically one. -/
theorem gibbsWeight_eq_fugacity_one (K : BoundedComplex B) :
    gibbsWeight K = fugacityWeight (fun _ _ _ => (1 : ℝ)) K := rfl

/-- The class mass of a sector-fugacity weight is the fugacity times the RS
measure. -/
theorem classMass_fugacity_mk (a : ℕ → ℕ → ℕ → ℝ) (K : BoundedComplex B) :
    classMass (fugacityWeight a) (Quotient.mk (relabelSetoid B) K)
      = a K.nV K.nE K.nT * mu K := by
  rw [classMass_of_invariant _ (fun _ _ h => fugacityWeight_invariant a h) _,
    fugacityWeight_invariant a (equivalent_out K), orbitCardClass_mk]
  unfold fugacityWeight
  rw [← labelDensity_eq_mu]
  unfold labelDensity
  ring

/-- The RS measure is strictly positive, so it can be cancelled. -/
theorem mu_pos (K : BoundedComplex B) : 0 < mu K := by
  unfold mu
  have h : (0 : ℝ) < (Nat.card (Aut K) : ℝ) := by exact_mod_cast autCard_pos K
  exact one_div_pos.mpr h

/-- **THEOREM (the premise, named exactly).**  The gauge-counting principle holds for
a sector-fugacity weight exactly when the fugacity is one in every sector that is
actually occupied.  Combined with `fugacityWeight_invariant`, this says precisely
what the undischarged premise is: not indifference to labels, which the whole family
has, but the choice of **unit cross-sector fugacity**.  That is one positive real per
size sector, set to one by fiat. -/
theorem gaugeCounting_iff_fugacity_one (a : ℕ → ℕ → ℕ → ℝ) :
    MeasureSubstrateBlocker.GaugeCountingPrinciple
        (classMass (B := B) (fugacityWeight (B := B) a))
      ↔ ∀ K : BoundedComplex B, a K.nV K.nE K.nT = 1 := by
  rw [gaugeCounting_iff_labelIndifference]
  constructor
  · intro h K
    have hK := h K
    rw [classMass_fugacity_mk, labelDensity_eq_mu] at hK
    have := mu_pos K
    field_simp at hK
    exact hK
  · intro h K
    rw [classMass_fugacity_mk, labelDensity_eq_mu, h K, one_mul]

/-- **THEOREM (the freedom is unsplittable).**  A sector fugacity can be moved out of
the measure and into the action without changing any weighted sum: reweighting the
measure by `a` is the same as shifting the action by `-log a`.  So "the measure is
forced" holds only relative to a convention about where the sector factor is booked;
only the product of measure and Boltzmann factor is determined. -/
theorem fugacity_absorbs_into_action (a : ℕ → ℕ → ℕ → ℝ) (S : BoundedComplex B → ℝ)
    (K : BoundedComplex B) (ha : 0 < a K.nV K.nE K.nT) :
    fugacityWeight a K * Real.exp (-S K)
      = gibbsWeight K
        * Real.exp (-(S K - Real.log (a K.nV K.nE K.nT))) := by
  have hvol : (0 : ℝ)
      < ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ) :=
    gaugeVolume_pos K
  unfold fugacityWeight gibbsWeight
  rw [neg_sub, Real.exp_sub, Real.exp_log ha, Real.exp_neg]
  ring

/-! ## §6d. Reducing the premise: gluing multiplicativity forces the factorial

§6c leaves the premise as "the sector fugacity is one", which is a bare choice.  Two
seats of the adversarial review converged independently on the one route they judged
to *close* rather than relocate: the factorial is the unique solution of a shuffle
identity, so the premise can be transmuted into a **locality** axiom about assembling
configurations from parts.

Read `f n` as the weight carried by one index set of size `n`.  The gluing law says:
take a configuration of size `m + n` that is assembled from a part of size `m` and a
part of size `n`.  There are `C(m+n, m)` ways to interleave the two blocks of labels
into the combined index set.  The law asserts that the assembled weight, multiplied by
the number of interleavings, is the product of the parts' weights.  That is
multiplicativity of the weight under disjoint union, with the label bookkeeping done
honestly, and it is a statement about how independent parts compose rather than a
choice of normalization.

This is a **reduction, not a discharge**: the gluing law is itself unproved from
recognition structure.  What changes is the shape of the debt.  Cost in a recognition
ledger is additive over independent parts, so a weight of the form `exp(-cost)` is
multiplicative over independent parts, which is the right-hand side of the shuffle
identity for free.  The open question becomes whether the ledger supplies the
interleaving count on the left, which is a question about how the ledger individuates
labels and is the kind of question `Gap2LedgerSiteBlindness` does not block. -/

/-- A **gluing law** for a size-indexed weight.  `unit`: the empty index set carries
weight one.  `atom`: a single label carries weight one, fixing the scale.  `shuffle`:
assembling a size-`m` part and a size-`n` part is multiplicative once the `C(m+n, m)`
interleavings of the label blocks are counted. -/
structure GluingLaw (f : ℕ → ℝ) : Prop where
  unit : f 0 = 1
  atom : f 1 = 1
  shuffle : ∀ m n : ℕ, f (m + n) * (Nat.choose (m + n) m : ℝ) = f m * f n

/-- **THEOREM (the gluing law forces the factorial).**  The inverse factorial is the
unique size-indexed weight satisfying the gluing law.  So "divide by the number of
labelings" is not an independent convention: it is the only weight that composes
multiplicatively under gluing. -/
theorem gluingLaw_forces_inverse_factorial {f : ℕ → ℝ} (h : GluingLaw f) :
    ∀ n : ℕ, f n = 1 / (Nat.factorial n : ℝ) := by
  intro n
  induction n with
  | zero => simpa using h.unit
  | succ k ih =>
      have hs := h.shuffle k 1
      rw [h.atom, mul_one, Nat.choose_succ_self_right] at hs
      have hk1 : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
      have hfact : (0 : ℝ) < (Nat.factorial k : ℝ) := by
        exact_mod_cast Nat.factorial_pos k
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hs
      have hval : f (k + 1) = f k / ((k : ℝ) + 1) :=
        eq_div_of_mul_eq hk1.ne' hs
      rw [hval, ih, Nat.factorial_succ]
      push_cast
      field_simp

/-- The Gibbs weight is the product of one inverse factorial per index set. -/
theorem gibbsWeight_factorizes (K : BoundedComplex B) :
    gibbsWeight K
      = (1 / (Nat.factorial K.nV : ℝ)) * (1 / (Nat.factorial K.nE : ℝ))
        * (1 / (Nat.factorial K.nT : ℝ)) := by
  unfold gibbsWeight
  push_cast
  field_simp

/-- **THEOREM (the premise reduces to gluing).**  Any size-indexed weight satisfying
the gluing law induces, index set by index set, exactly the Gibbs weight.  Combined
with `gibbs_induces_measure` this means the gluing law *implies* the gauge-counting
principle, so the unit-fugacity choice of §6c is discharged by a locality axiom rather
than asserted. -/
theorem gluingLaw_gives_gibbsWeight {f : ℕ → ℝ} (h : GluingLaw f)
    (K : BoundedComplex B) :
    f K.nV * f K.nE * f K.nT = gibbsWeight K := by
  rw [gluingLaw_forces_inverse_factorial h K.nV,
    gluingLaw_forces_inverse_factorial h K.nE,
    gluingLaw_forces_inverse_factorial h K.nT, gibbsWeight_factorizes]

/-- **THEOREM (gluing implies the gauge-counting principle).**  The premise behind the
Gap-2 measure follows from the gluing law.  This is the sharpest available statement of
what the theory still owes: not a normalization, but multiplicativity under
assembly. -/
theorem gluingLaw_gives_gaugeCounting (B : ℕ) {f : ℕ → ℝ} (h : GluingLaw f) :
    MeasureSubstrateBlocker.GaugeCountingPrinciple
      (classMass (B := B) (fun K => f K.nV * f K.nE * f K.nT)) := by
  have hfun : (fun K : BoundedComplex B => f K.nV * f K.nE * f K.nT)
      = (gibbsWeight : BoundedComplex B → ℝ) := by
    funext K
    exact gluingLaw_gives_gibbsWeight h K
  rw [hfun]
  exact gibbs_induces_measure B

/-- The gluing law is satisfiable: the inverse factorial is a model, so the reduction
is not vacuous.  `Nat.add_choose_le`-style bookkeeping is the whole content. -/
theorem inverseFactorial_gluingLaw :
    GluingLaw (fun n => 1 / (Nat.factorial n : ℝ)) where
  unit := by norm_num
  atom := by norm_num
  shuffle := by
    intro m n
    have hkey : (Nat.choose (m + n) m) * (Nat.factorial m * Nat.factorial n)
        = Nat.factorial (m + n) := by
      have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n)
      simpa [Nat.add_sub_cancel_left, mul_assoc] using h
    have hm : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hn : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hmn : (0 : ℝ) < (Nat.factorial (m + n) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (m + n)
    have hcast : ((Nat.choose (m + n) m : ℕ) : ℝ)
        * ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))
        = (Nat.factorial (m + n) : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hkey
    field_simp
    linarith [hcast]

/-! ## §7. Certificate -/

/-- What this module establishes about the Gap-2 premise. -/
structure GaugeVolumeStatus where
  /-- The gauge volume is proved equal to the order of the sector group. -/
  gauge_volume_is_group_order : Bool
  /-- The gauge volume is proved to carry no incidence information. -/
  gauge_volume_size_only : Bool
  /-- The measure is proved equal to the label density. -/
  measure_is_label_density : Bool
  /-- The premise is proved equivalent to unit cross-sector fugacity: one positive
  real per size sector, set to one.  This is the exact naming of the premise. -/
  premise_is_unit_sector_fugacity : Bool
  /-- Label indifference alone is proved NOT to select the premise: the whole
  sector-fugacity family is relabeling-invariant.  Retired reading, kept false so a
  later reader cannot revive it. -/
  premise_is_label_indifference : Bool
  /-- The residual sector factor is proved absorbable into the action, so the measure
  is determined only up to that booking convention. -/
  residue_absorbable_into_action : Bool
  /-- The premise is proved to follow from a gluing law: multiplicativity of the
  weight under assembly, with label interleavings counted.  A reduction of the debt,
  not a discharge, since the gluing law is itself not derived from the ledger. -/
  premise_reduces_to_gluing : Bool
  /-- The Gibbs weight is proved to be the unique relabeling-invariant labeled
  weight whose class mass is the RS measure. -/
  gibbs_weight_unique : Bool
  /-- Label indifference itself is NOT derived from the ledger cost function;
  `Gap2LedgerSiteBlindness` proves that route is blocked. -/
  indifference_derived_from_cost : Bool

/-- Status after this module. -/
def gaugeVolumeStatus : GaugeVolumeStatus where
  gauge_volume_is_group_order := true
  gauge_volume_size_only := true
  measure_is_label_density := true
  premise_is_unit_sector_fugacity := true
  premise_is_label_indifference := false
  residue_absorbable_into_action := true
  premise_reduces_to_gluing := true
  gibbs_weight_unique := true
  indifference_derived_from_cost := false

theorem status_group_order : gaugeVolumeStatus.gauge_volume_is_group_order = true := rfl
theorem status_size_only : gaugeVolumeStatus.gauge_volume_size_only = true := rfl
theorem status_label_density : gaugeVolumeStatus.measure_is_label_density = true := rfl
theorem status_premise_named : gaugeVolumeStatus.premise_is_unit_sector_fugacity = true := rfl
/-- Retired by adversarial review 2026-07-28; `fugacityWeight_invariant` is the proof. -/
theorem status_indifference_undershoots :
    gaugeVolumeStatus.premise_is_label_indifference = false := rfl
theorem status_absorbable : gaugeVolumeStatus.residue_absorbable_into_action = true := rfl
theorem status_gluing : gaugeVolumeStatus.premise_reduces_to_gluing = true := rfl
theorem status_gibbs_unique : gaugeVolumeStatus.gibbs_weight_unique = true := rfl
/-- OPEN by construction: cost cannot supply label indifference. -/
theorem status_cost_route_open : gaugeVolumeStatus.indifference_derived_from_cost = false := rfl

/-- **Grounding theorem.**  The flags are backed by the actual theorems. -/
theorem gaugeVolume_grounded (B : ℕ) :
    (∀ K : BoundedComplex B,
        pairCount K = Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT)) ∧
    (∀ K K' : BoundedComplex B, K.nV = K'.nV → K.nE = K'.nE → K.nT = K'.nT →
        pairCount K = pairCount K') ∧
    (∀ K : BoundedComplex B, labelDensity K = mu K) ∧
    (∀ ν : TriangulationClass B → ℝ,
        MeasureSubstrateBlocker.GaugeCountingPrinciple ν ↔
          ∀ K : BoundedComplex B,
            ν (Quotient.mk (relabelSetoid B) K) = labelDensity K) ∧
    MeasureSubstrateBlocker.GaugeCountingPrinciple
      (classMass (gibbsWeight : BoundedComplex B → ℝ)) ∧
    (∀ w : BoundedComplex B → ℝ, (∀ K K', Equivalent K K' → w K = w K') →
        (MeasureSubstrateBlocker.GaugeCountingPrinciple (classMass w) ↔
          ∀ K : BoundedComplex B, w K = gibbsWeight K)) :=
  ⟨pairCount_eq_factorials,
   fun _ _ hV hE hT => pairCount_congr_sizes hV hE hT,
   labelDensity_eq_mu,
   gaugeCounting_iff_labelIndifference,
   gibbs_induces_measure B,
   invariant_weight_gives_measure_iff⟩

end Gap2GaugeVolume
end SevenGaps
end Gravity
end IndisputableMonolith
