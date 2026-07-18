import IndisputableMonolith.Gravity.SevenGaps.PathSumMeasure

/-!
# Seven Gaps, gauge preflight: DERIVING the 1/|Aut| measure from gauge counting

## What this module does

`PathSumMeasure` POSTULATES the symmetry-factor measure `mu K = 1/|Aut K|`
(standard discrete-gravity convention).  This module DERIVES that measure
from pure gauge counting, with a definition of the gauge mass that never
mentions `mu` or `Aut`:

* `gaugeOrbitCard K`  = number of labeled complexes equivalent to `K`
  (the size of `K`'s relabeling orbit inside the bounded universe).
* `pairCount K`       = number of pairs `(K', r)` with `K'` in the orbit of
  `K` and `r : Relabel K K'` a concrete gauge witness (the gauge volume of
  the orbit).  DEFINITION mentions only `Equivalent` and `Relabel`.
* `gaugeOrbitMass c`  = `orbitCard c / pairCount c` on the quotient
  `TriangulationClass B`: labeled copies per unit of gauge volume.
  DEFINITION mentions only the two counting quantities above.

## Status tiers (honest tagging)

**THEOREM (proved below, 0 sorry, 0 new axioms):**
* Torsor/orbit-stabilizer (`torsorEquiv`, `relabelingCount_eq_autCard`):
  for equivalent `K K'`, the relabeling witnesses `Relabel K K'` are a
  torsor over `Aut K`, so `|Relabel K K'| = |Aut K|`; hence the total
  `(copy, witness)` pair count factorizes as
  `pairCount K = gaugeOrbitCard K * |Aut K|`
  (`pairCount_eq_orbitCard_mul_autCard`).
* Representative independence (`gaugeOrbitCard_congr`, `pairCount_congr`,
  `gaugeMassRep_congr`): the counting quantities are class functions, so
  the quotient lifts `orbitCardClass`/`pairCountClass`/`gaugeOrbitMass`
  are well-defined.
* **The derivation** (`gaugeOrbitMass_eq_mu`): the counting-defined mass
  of the class of `K` equals `mu K = 1/|Aut K|`.  GIVEN the pair-counting
  principle (the MODEL premise below), the `1/|Aut|` factor follows from
  orbit-stabilizer; what is put in by hand is the choice that gauge
  volume equals the `(copy, witness)` pair count (a per-labeled-copy
  principle would give the quotient-uniform measure instead).
* Existence + uniqueness (`gaugeOrbitMass_mul_pairCount`,
  `gaugeCountingMass_unique`): `gaugeOrbitMass` satisfies the counting
  property `ν c * pairCount c = orbitCard c`, and any class mass `ν`
  satisfying it equals `gaugeOrbitMass`.  The counting principle pins
  the measure.
* Path-sum corollary (`labeledZ_eq_orbitWeighted_classSum`): for a
  relabeling-invariant weight, the labeled path sum `Z` equals the
  class sum `Σ_c orbitCard c * gaugeOrbitMass c * w(rep c)`.

**MODEL (the named premise, now explicit instead of hidden):**
* The COUNTING PRINCIPLE itself: uniform gauge density on labeled
  representatives (each `(copy, witness)` pair carries equal weight, and
  the physical mass of a class is labeled copies divided by gauge
  volume).  This module derives `1/|Aut|` FROM that principle; it does
  NOT derive the principle from the ledger.  That residue is recorded in
  `gaugePreflightStatus.counting_principle_derived_from_ledger = false`.

## Kill-condition audit (panel live-bet 1)

The bet survives: `pairCount` and `gaugeOrbitMass` are DEFINED without
reference to `mu` or `Aut` (only `Equivalent`, `Relabel`, and `Nat.card`);
`Aut` appears exclusively in THEOREM statements/proofs relating the
counting quantities to the postulated measure.  The pair-count route did
not collapse to a definitional restatement.

## Ledger note

The decision to flip any `FullTheoryLedger` flag on the strength of this
derivation belongs to the CONDUCTOR; this module mutates no ledger.

## Proof notes
* No `decide`/`native_decide`; cardinalities are never computed
  numerically.
* Groupoid data (`Relabel.refl/symm/trans`) is REUSED from
  `PathSumMeasure`, not redefined; the two cancellation laws needed for
  the torsor are proved pointwise inside `torsorEquiv`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace ExactShellGaugePreflight

open PathSumMeasure

variable {B : ℕ}

/-! ## §1. The gauge groupoid (T1)

Identity, inverse, and composition of relabelings already exist in
`PathSumMeasure` (`Relabel.refl`, `Relabel.symm`, `Relabel.trans`) with the
setoid `relabelSetoid` proving they implement a genuine equivalence.  We
add only the equivalence-relation restatements used below. -/

/-- Reflexivity of the gauge relation (identity relabeling). -/
theorem equivalent_refl (K : BoundedComplex B) : Equivalent K K :=
  ⟨Relabel.refl K⟩

/-- Symmetry of the gauge relation (inverse relabeling). -/
theorem equivalent_symm {K K' : BoundedComplex B} (h : Equivalent K K') :
    Equivalent K' K :=
  h.elim fun r => ⟨r.symm⟩

/-- Transitivity of the gauge relation (composite relabeling). -/
theorem equivalent_trans {K₁ K₂ K₃ : BoundedComplex B}
    (h₁ : Equivalent K₁ K₂) (h₂ : Equivalent K₂ K₃) : Equivalent K₁ K₃ :=
  h₁.elim fun r => h₂.elim fun s => ⟨r.trans s⟩

/-- **THEOREM.**  The relabeling witnesses between ANY two bounded complexes
form a finite type (inject into the finite triple of index bijections;
generalizes `PathSumMeasure.instFiniteAut` beyond the diagonal). -/
instance instFiniteRelabel (K K' : BoundedComplex B) : Finite (Relabel K K') :=
  Finite.of_injective _ (Relabel.toEquivTriple_injective (K := K) (K' := K'))

/-! ## §2. Gauge counting quantities (T2)

Both are pure counts: neither definition mentions `mu` or `Aut`. -/

/-- The size of `K`'s relabeling orbit inside the bounded universe: the
number of labeled complexes gauge-equivalent to `K`.  Finite because the
universe `BoundedComplex B` is a `Fintype`. -/
noncomputable def gaugeOrbitCard (K : BoundedComplex B) : ℕ :=
  Nat.card {K' : BoundedComplex B // Equivalent K K'}

/-- The number of relabeling witnesses from `K` to `K'`. -/
noncomputable def relabelingCount (K K' : BoundedComplex B) : ℕ :=
  Nat.card (Relabel K K')

/-- The gauge volume of `K`'s orbit: the total number of pairs `(K', r)`
where `K'` is a labeled complex in the orbit of `K` and `r` is a concrete
relabeling witness `K → K'`.  DEFINITION mentions only `Equivalent` and
`Relabel` (pure counting; no `mu`, no `Aut`). -/
noncomputable def pairCount (K : BoundedComplex B) : ℕ :=
  Nat.card (Σ K' : {K' : BoundedComplex B // Equivalent K K'}, Relabel K K'.val)

/-- The orbit contains `K` itself, so the orbit count is positive. -/
theorem gaugeOrbitCard_pos (K : BoundedComplex B) : 0 < gaugeOrbitCard K := by
  haveI : Nonempty {K' : BoundedComplex B // Equivalent K K'} :=
    ⟨⟨K, equivalent_refl K⟩⟩
  exact Nat.card_pos

/-! ## §3. Orbit-stabilizer: the load-bearing torsor theorem (T3) -/

/-- **THEOREM (torsor).**  Fixing one witness `r0 : Relabel K K'`, the map
`a ↦ a.trans r0` is a bijection `Aut K ≃ Relabel K K'`: the witnesses
between equivalent complexes are a torsor over the automorphism group. -/
def torsorEquiv {K K' : BoundedComplex B} (r0 : Relabel K K') :
    Aut K ≃ Relabel K K' where
  toFun a := a.trans r0
  invFun r := r.trans r0.symm
  left_inv a := by
    apply Relabel.ext <;>
      · apply Equiv.ext
        intro x
        simp only [Relabel.trans_vEquiv, Relabel.trans_eEquiv, Relabel.trans_tEquiv,
          Relabel.symm_vEquiv, Relabel.symm_eEquiv, Relabel.symm_tEquiv,
          Equiv.trans_apply, Equiv.symm_apply_apply]
  right_inv r := by
    apply Relabel.ext <;>
      · apply Equiv.ext
        intro x
        simp only [Relabel.trans_vEquiv, Relabel.trans_eEquiv, Relabel.trans_tEquiv,
          Relabel.symm_vEquiv, Relabel.symm_eEquiv, Relabel.symm_tEquiv,
          Equiv.trans_apply, Equiv.apply_symm_apply]

/-- **THEOREM (orbit-stabilizer, cardinal form).**  For equivalent
complexes, the witness count equals the automorphism count. -/
theorem relabelingCount_eq_autCard {K K' : BoundedComplex B}
    (h : Equivalent K K') : relabelingCount K K' = Nat.card (Aut K) := by
  obtain ⟨r0⟩ := h
  unfold relabelingCount
  exact (Nat.card_congr (torsorEquiv r0)).symm

/-- **THEOREM (pair-count factorization).**  The gauge volume of the orbit
is the orbit size times the automorphism count: every fiber of the
projection `(K', r) ↦ K'` is a torsor over `Aut K`. -/
theorem pairCount_eq_orbitCard_mul_autCard (K : BoundedComplex B) :
    pairCount K = gaugeOrbitCard K * Nat.card (Aut K) := by
  have e : (Σ K' : {K' : BoundedComplex B // Equivalent K K'}, Relabel K K'.val)
      ≃ {K' : BoundedComplex B // Equivalent K K'} × Aut K :=
    Equiv.sigmaEquivProdOfEquiv fun K' =>
      (torsorEquiv (Classical.choice K'.property)).symm
  unfold pairCount gaugeOrbitCard
  rw [Nat.card_congr e, Nat.card_prod]

/-- The gauge volume is positive (the orbit is nonempty and `Aut` contains
the identity). -/
theorem pairCount_pos (K : BoundedComplex B) : 0 < pairCount K := by
  rw [pairCount_eq_orbitCard_mul_autCard]
  exact Nat.mul_pos (gaugeOrbitCard_pos K) (autCard_pos K)

/-! ## §4. Representative independence (well-definedness on classes) -/

/-- The orbit count is a class function. -/
theorem gaugeOrbitCard_congr {K K' : BoundedComplex B} (h : Equivalent K K') :
    gaugeOrbitCard K = gaugeOrbitCard K' :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _L =>
    ⟨fun hK => equivalent_trans (equivalent_symm h) hK,
     fun hK' => equivalent_trans h hK'⟩)

/-- The automorphism count is a class function (conjugation bijection,
reusing `PathSumMeasure.Relabel.autCongr`). -/
theorem autCard_congr {K K' : BoundedComplex B} (h : Equivalent K K') :
    Nat.card (Aut K) = Nat.card (Aut K') := by
  obtain ⟨r⟩ := h
  exact Nat.card_congr r.autCongr

/-- The gauge volume is a class function: `pairCount` is independent of the
choice of base representative. -/
theorem pairCount_congr {K K' : BoundedComplex B} (h : Equivalent K K') :
    pairCount K = pairCount K' := by
  rw [pairCount_eq_orbitCard_mul_autCard, pairCount_eq_orbitCard_mul_autCard,
    gaugeOrbitCard_congr h, autCard_congr h]

/-- **LEMMA (well-definedness).**  The representative-level counting ratio
(labeled copies per unit of gauge volume) is independent of the chosen
representative. -/
theorem gaugeMassRep_congr {K K' : BoundedComplex B} (h : Equivalent K K') :
    (gaugeOrbitCard K : ℝ) / (pairCount K : ℝ) =
      (gaugeOrbitCard K' : ℝ) / (pairCount K' : ℝ) := by
  rw [gaugeOrbitCard_congr h, pairCount_congr h]

/-! ## §5. The gauge-counting mass on classes (T4) -/

/-- The orbit count as a function of the class. -/
noncomputable def orbitCardClass (c : TriangulationClass B) : ℕ :=
  Quotient.liftOn c gaugeOrbitCard fun _ _ h => gaugeOrbitCard_congr h

@[simp] theorem orbitCardClass_mk (K : BoundedComplex B) :
    orbitCardClass (Quotient.mk (relabelSetoid B) K) = gaugeOrbitCard K := rfl

/-- The gauge volume as a function of the class. -/
noncomputable def pairCountClass (c : TriangulationClass B) : ℕ :=
  Quotient.liftOn c pairCount fun _ _ h => pairCount_congr h

@[simp] theorem pairCountClass_mk (K : BoundedComplex B) :
    pairCountClass (Quotient.mk (relabelSetoid B) K) = pairCount K := rfl

theorem pairCountClass_pos (c : TriangulationClass B) : 0 < pairCountClass c :=
  Quotient.inductionOn c fun K => pairCount_pos K

/-- **The gauge-counting mass of a class**: labeled copies per unit of
gauge volume.  DEFINITION mentions only the two counting quantities
(`orbitCardClass`, `pairCountClass`); no `mu`, no `Aut`.  This is the
explicit counting principle: uniform gauge density on labeled
representatives. -/
noncomputable def gaugeOrbitMass (c : TriangulationClass B) : ℝ :=
  (orbitCardClass c : ℝ) / (pairCountClass c : ℝ)

/-- **THEOREM (the derivation).**  The counting-defined class mass equals
the postulated symmetry-factor measure: GIVEN the pair-counting principle,
`1/|Aut|` follows from orbit-stabilizer (`pairCount = orbitCard * |Aut|`)
rather than being written into the definition. -/
theorem gaugeOrbitMass_eq_mu (K : BoundedComplex B) :
    gaugeOrbitMass (Quotient.mk (relabelSetoid B) K) = mu K := by
  have ho : (gaugeOrbitCard K : ℝ) ≠ 0 := by
    exact_mod_cast (gaugeOrbitCard_pos K).ne'
  unfold gaugeOrbitMass mu
  rw [orbitCardClass_mk, pairCountClass_mk, pairCount_eq_orbitCard_mul_autCard,
    Nat.cast_mul, div_mul_eq_div_div, div_self ho]

/-! ## §6. Existence + uniqueness: the counting principle pins the measure (T5) -/

/-- **THEOREM (existence).**  `gaugeOrbitMass` itself satisfies the
normalized gauge-divided counting property; together with
`gaugeCountingMass_unique` this pins the measure (existence + uniqueness,
not uniqueness alone). -/
theorem gaugeOrbitMass_mul_pairCount (c : TriangulationClass B) :
    gaugeOrbitMass c * (pairCountClass c : ℝ) = (orbitCardClass c : ℝ) := by
  have hp : (pairCountClass c : ℝ) ≠ 0 := by
    exact_mod_cast (pairCountClass_pos c).ne'
  unfold gaugeOrbitMass
  rw [div_mul_cancel₀ _ hp]

/-- **THEOREM (uniqueness).**  Any class-mass assignment satisfying the
normalized gauge-divided counting property (`ν c * pairCount c =
orbitCard c` for every class) equals `gaugeOrbitMass`.  Given the counting
principle (the explicit MODEL premise of this module), the measure is
unique; combined with `gaugeOrbitMass_eq_mu`, it is forced to be
`1/|Aut|`. -/
theorem gaugeCountingMass_unique (ν : TriangulationClass B → ℝ)
    (hν : ∀ c, ν c * (pairCountClass c : ℝ) = (orbitCardClass c : ℝ))
    (c : TriangulationClass B) : ν c = gaugeOrbitMass c := by
  have hp : (pairCountClass c : ℝ) ≠ 0 := by
    exact_mod_cast (pairCountClass_pos c).ne'
  unfold gaugeOrbitMass
  rw [eq_div_iff hp]
  exact hν c

/-! ## §7. Path-sum corollary: labeled Z as an orbit-weighted class sum (T6) -/

/-- Noncomputable enumeration of the finite class quotient (needed only to
STATE the class sum; `triangulationClass_finite` supplies finiteness). -/
noncomputable instance instFintypeTriangulationClass (B : ℕ) :
    Fintype (TriangulationClass B) :=
  Fintype.ofFinite _

/-- **THEOREM (diagnostic fragment).**  For a relabeling-invariant weight,
the labeled path sum with the `1/|Aut|` measure equals the class sum
weighted by orbit size times the COUNTING-DERIVED mass:
`Z = Σ_c orbitCard c * gaugeOrbitMass c * w(rep c)`.
The measure in `Z` is now carried entirely by counting data. -/
theorem labeledZ_eq_orbitWeighted_classSum (B : ℕ) (w : BoundedComplex B → ℂ)
    (hinv : ∀ K K', Equivalent K K' → w K = w K') :
    Z B w = ∑ c : TriangulationClass B,
      (orbitCardClass c : ℂ) * (gaugeOrbitMass c : ℂ) * w (Quotient.out c) := by
  classical
  unfold Z
  rw [← Fintype.sum_fiberwise
    (fun K : BoundedComplex B => Quotient.mk (relabelSetoid B) K)
    (fun K : BoundedComplex B => (mu K : ℂ) * w K)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc : Quotient.mk (relabelSetoid B) (Quotient.out c) = c := Quotient.out_eq c
  have hmem : ∀ K : {K : BoundedComplex B // Quotient.mk (relabelSetoid B) K = c},
      Equivalent (Quotient.out c) K.val := fun K =>
    Quotient.exact (hc.trans K.property.symm)
  have hmass : gaugeOrbitMass c = mu (Quotient.out c) := by
    conv_lhs => rw [← hc]
    exact gaugeOrbitMass_eq_mu (Quotient.out c)
  have e : {K : BoundedComplex B // Quotient.mk (relabelSetoid B) K = c}
      ≃ {K' : BoundedComplex B // Equivalent (Quotient.out c) K'} :=
    Equiv.subtypeEquivRight fun K =>
      ⟨fun hK => Quotient.exact (hc.trans hK.symm),
       fun hE => by
        have h1 : Quotient.mk (relabelSetoid B) (Quotient.out c)
            = Quotient.mk (relabelSetoid B) K := Quotient.sound hE
        exact h1.symm.trans hc⟩
  have hcard : Fintype.card {K : BoundedComplex B // Quotient.mk (relabelSetoid B) K = c}
      = orbitCardClass c := by
    rw [Fintype.card_eq_nat_card, Nat.card_congr e]
    conv_rhs => rw [← hc]
    rfl
  calc ∑ K : {K : BoundedComplex B // Quotient.mk (relabelSetoid B) K = c},
        (mu K.val : ℂ) * w K.val
      = ∑ _K : {K : BoundedComplex B // Quotient.mk (relabelSetoid B) K = c},
          (mu (Quotient.out c) : ℂ) * w (Quotient.out c) :=
        Finset.sum_congr rfl fun K _ =>
          (summand_class_constant B w hinv (hmem K)).symm
    _ = (Fintype.card {K : BoundedComplex B // Quotient.mk (relabelSetoid B) K = c} : ℂ) *
          ((mu (Quotient.out c) : ℂ) * w (Quotient.out c)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (orbitCardClass c : ℂ) * (gaugeOrbitMass c : ℂ) * w (Quotient.out c) := by
        rw [hcard, hmass, mul_assoc]

/-! ## §8. Status ledger (T7)

All `true` flags are rfl-forced and grounded by `gaugePreflight_grounded`;
the `false` flag names the explicit residue.  The `FullTheoryLedger` flag
decision belongs to the conductor; nothing here mutates it. -/

/-- What is proved and what remains the named premise in this module. -/
structure GaugePreflightStatus where
  gauge_torsor_proved : Bool
  measure_derived_from_counting : Bool
  uniqueness_proved : Bool
  counting_principle_derived_from_ledger : Bool

/-- Status after this module: the torsor, the derivation, and uniqueness
are theorems; the uniform-gauge-density counting principle is the explicit
MODEL premise, not derived from the ledger. -/
def gaugePreflightStatus : GaugePreflightStatus where
  gauge_torsor_proved := true
  measure_derived_from_counting := true
  uniqueness_proved := true
  counting_principle_derived_from_ledger := false

theorem status_gauge_torsor :
    gaugePreflightStatus.gauge_torsor_proved = true := rfl
theorem status_measure_derived :
    gaugePreflightStatus.measure_derived_from_counting = true := rfl
theorem status_uniqueness :
    gaugePreflightStatus.uniqueness_proved = true := rfl
/-- OPEN residue: the counting principle itself (uniform gauge density on
labeled representatives) is the named premise, not a ledger theorem. -/
theorem status_counting_principle_open :
    gaugePreflightStatus.counting_principle_derived_from_ledger = false := rfl

/-- **Grounding theorem.**  The status flags are backed by the actual
theorems: orbit-stabilizer, pair-count factorization, the derivation
`gaugeOrbitMass = mu`, and uniqueness. -/
theorem gaugePreflight_grounded (B : ℕ) :
    (∀ K K' : BoundedComplex B, Equivalent K K' →
        relabelingCount K K' = Nat.card (Aut K)) ∧
    (∀ K : BoundedComplex B,
        pairCount K = gaugeOrbitCard K * Nat.card (Aut K)) ∧
    (∀ K : BoundedComplex B,
        gaugeOrbitMass (Quotient.mk (relabelSetoid B) K) = mu K) ∧
    (∀ ν : TriangulationClass B → ℝ,
        (∀ c, ν c * (pairCountClass c : ℝ) = (orbitCardClass c : ℝ)) →
        ∀ c, ν c = gaugeOrbitMass c) :=
  ⟨fun _ _ h => relabelingCount_eq_autCard h,
   pairCount_eq_orbitCard_mul_autCard,
   gaugeOrbitMass_eq_mu,
   gaugeCountingMass_unique⟩

end ExactShellGaugePreflight
end SevenGaps
end Gravity
end IndisputableMonolith
