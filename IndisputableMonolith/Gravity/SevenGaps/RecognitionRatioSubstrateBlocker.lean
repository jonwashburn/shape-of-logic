import IndisputableMonolith.Gravity.SevenGaps.StationarityBridgeClosure

/-!
# P2.1 terminal: the bare ledger lacks a deficit-source constitutive coupling

## Headline

`recognition_ratio_derived` does not follow from a bare
`RecognitionLedger`.  The missing premise is a **signed deficit-source
constitutive coupling**: a source strength `c_sigma = kappa_sigma *
delta_sigma`, coupled linearly to the total strain in the J-cost action.

This is an exact blocker package, not a status flag:

* coboundary strains telescope to zero around every closed cycle;
* imposing the desired total-strain budget already assumes the ratio
  conclusion, so the constrained-budget route is circular;
* one and the same bare two-cell J-ledger is induced by opposite signed
  source orientations, so no selector from bare ledgers can recover the
  signed source universally;
* after the named constitutive coupling is supplied, J-stationarity derives
  the recognition-ratio bridge and its cubic remainder;
* the sourced construction has a nontrivial, uniformly admissible
  small-mesh family.

The missing premise below does not mention `xRatio`, `Real.log`, or the
desired ratio relation.  It supplies only the source data and its linear
coupling to the already proved J-cost action.  Thus the positive result does
not define the desired bridge as an assumption.

Status: every declaration is THEOREM or definitional MODEL as identified
below.  There is no `sorry`, `admit`, new axiom, `native_decide`, boolean
status record, or `FullTheoryLedger` flag change.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps

/-! ## 1. The exact missing premise -/

/-- **MODEL (the exact premise missing from the bare ledger).**

A signed deficit-source constitutive coupling supplies a channel count, the
hinge coupling and signed geometric deficit, and a source strength satisfying

`sourceStrength sigma = kappa sigma * geometricDeficit sigma`.

It also supplies the positive mesh scale and the structural small-source
bound needed by the cubic estimate.  No field mentions the recognition
ratio or its logarithm. -/
structure DeficitSourceConstitutiveCoupling (H : Type*) where
  channels : ℕ
  channels_pos : 1 ≤ channels
  kappa : H → ℝ
  geometricDeficit : H → ℝ
  sourceStrength : H → ℝ
  source_eq : ∀ σ, sourceStrength σ = kappa σ * geometricDeficit σ
  meshScale : ℝ
  meshScale_pos : 0 < meshScale
  source_dominated :
    ∀ σ, |sourceStrength σ| ≤ (channels : ℝ) * meshScale

/-- The constitutive action named by the missing premise: summed J-cost
minus the signed source coupled linearly to total strain. -/
noncomputable def deficitSourceAction {H : Type*}
    (C : DeficitSourceConstitutiveCoupling H) (σ : H)
    (t : Fin C.channels → ℝ) : ℝ :=
  sourcedAction C.channels (C.sourceStrength σ) t

/-- **THEOREM (kernel identification of the premise).** The constitutive
action is exactly the summed J-cost of the exponential strains minus the
linear deficit-source term.  This identifies the missing premise inside the
kernel without assuming any ratio relation. -/
theorem deficitSourceAction_eq_jcost_sum {H : Type*}
    (C : DeficitSourceConstitutiveCoupling H) (σ : H)
    (t : Fin C.channels → ℝ) :
    deficitSourceAction C σ t
      = (∑ i, Cost.Jcost (Real.exp (t i)))
          - C.sourceStrength σ / C.channels * ∑ i, t i :=
  sourcedAction_eq_jcost_sum C.channels (C.sourceStrength σ) t

/-! ## 2. Supplying the premise closes the conditional derivation -/

/-- The bridge derived from the named constitutive coupling by the unique
global minimizer of `deficitSourceAction`.  Its ratio relation is proved by
`stationaryRatio_cubic`; it is not a field of the premise. -/
noncomputable def ratioBridgeFromDeficitSourceCoupling {H : Type*}
    (C : DeficitSourceConstitutiveCoupling H) :
    RecognitionRatioBridge H :=
  recognitionRatioBridge_ofStationarity C.channels C.channels_pos
    C.kappa C.geometricDeficit C.meshScale C.meshScale_pos
    (fun σ => by
      rw [← C.source_eq σ]
      exact C.source_dominated σ)

/-- **THEOREM (the conditional `recognition_ratio_derived`).** Once the
named deficit-source constitutive coupling is supplied, J-stationarity
derives the bridge relation with explicit remainder constant `n / 6`.
No hypothesis states a fact about `xRatio` or `log xRatio`. -/
theorem recognition_ratio_derived_of_deficit_source_coupling {H : Type*}
    (C : DeficitSourceConstitutiveCoupling H) (σ : H) :
    |Real.log ((ratioBridgeFromDeficitSourceCoupling C).xRatio σ)
        - C.kappa σ * C.geometricDeficit σ|
      ≤ (C.channels : ℝ) / 6 * C.meshScale ^ 3 :=
  (ratioBridgeFromDeficitSourceCoupling C).ratio_relation σ

/-- **THEOREM (stationarity receipt).** The ratio in the conditional
derivation is the exponential of the total strain of the unique sourced
minimizer. -/
theorem deficitSourceCoupling_logRatio_eq_minimizer_strain {H : Type*}
    (C : DeficitSourceConstitutiveCoupling H) (σ : H) :
    Real.log ((ratioBridgeFromDeficitSourceCoupling C).xRatio σ)
      = ∑ i, sourcedMinimizer C.channels (C.sourceStrength σ) i := by
  rw [C.source_eq σ]
  exact ofStationarity_log_xRatio_eq_minimizer_strain C.channels
    C.channels_pos C.kappa C.geometricDeficit C.meshScale
    C.meshScale_pos
    (fun τ => by
      rw [← C.source_eq τ]
      exact C.source_dominated τ)
    σ

/-! ## 3. The bare ledger cannot select the signed source -/

/-- The bare two-cell ledger induced by the exact unit-coupled witness with
signed source parameter `d`. -/
noncomputable def signBlindBareLedger (d : ℝ) :
    RecognitionLedger.RecognitionLedger (Fin 2) :=
  ratioBridgeLedger (twoHingeWitnessBridge d)

/-- Two recognition ledgers with the same cost function are equal (the
remaining fields are proofs). -/
private theorem recognitionLedger_cost_ext {Λ : Type*} [Fintype Λ]
    [DecidableEq Λ] {L L' : RecognitionLedger.RecognitionLedger Λ}
    (h : L.cost = L'.cost) : L = L' := by
  cases L
  cases L'
  subst h
  rfl

/-- **THEOREM (same bare ledger, opposite signed source).** Reversing the
source orientation leaves every J-cost, hence the entire bare recognition
ledger, unchanged. -/
theorem signBlindBareLedger_neg_eq (d : ℝ) :
    signBlindBareLedger (-d) = signBlindBareLedger d := by
  apply recognitionLedger_cost_ext
  funext i j
  rw [show (signBlindBareLedger (-d)).cost i j
      = Cost.Jcost ((twoHingeWitnessBridge (-d)).xRatio i
          / (twoHingeWitnessBridge (-d)).xRatio j) from
        ratioBridgeLedger_cost (twoHingeWitnessBridge (-d)) i j]
  rw [show (signBlindBareLedger d).cost i j
      = Cost.Jcost ((twoHingeWitnessBridge d).xRatio i
          / (twoHingeWitnessBridge d).xRatio j) from
        ratioBridgeLedger_cost (twoHingeWitnessBridge d) i j]
  have hratio :
      (twoHingeWitnessBridge (-d)).xRatio i
          / (twoHingeWitnessBridge (-d)).xRatio j
        = ((twoHingeWitnessBridge d).xRatio i
            / (twoHingeWitnessBridge d).xRatio j)⁻¹ := by
    rw [twoHingeWitnessBridge_xRatio_neg d i,
      twoHingeWitnessBridge_xRatio_neg d j, inv_div_inv, inv_div]
  rw [hratio]
  exact (Cost.Jcost_symm
    (div_pos ((twoHingeWitnessBridge d).xRatio_pos i)
      ((twoHingeWitnessBridge d).xRatio_pos j))).symm

/-- A proposed universal recovery of the signed unit-coupled source from a
bare two-cell ledger.  The next theorem proves that no such selector exists. -/
def RecoversSignedSourceFromBareLedger
    (select : RecognitionLedger.RecognitionLedger (Fin 2) → ℝ) : Prop :=
  ∀ d : ℝ, select (signBlindBareLedger d) = d

/-- **THEOREM (the exact bare-ledger blocker).** No function of a bare
`RecognitionLedger (Fin 2)` can universally recover the signed source of
the exact unit-coupled witness family.  The ledgers at sources `1` and `-1`
are equal, while the required outputs are different.  Therefore signed
deficit-source orientation is extra constitutive data, not information
contained in the bare ledger. -/
theorem no_bare_ledger_selector_recovers_signed_source :
    ¬ ∃ select : RecognitionLedger.RecognitionLedger (Fin 2) → ℝ,
      RecoversSignedSourceFromBareLedger select := by
  rintro ⟨select, hselect⟩
  have hneg := hselect (-1)
  have hpos := hselect 1
  rw [signBlindBareLedger_neg_eq 1] at hneg
  norm_num at hneg hpos
  linarith

/-! ## 4. A nontrivial source-backed family exists -/

/-- **THEOREM (nontrivial source-backed family).** For every nonzero
coupling and positive channel count, the quadratic sourced family is
uniformly admissible.  Its source is exactly `n*h^2`, and at every nonzero
mesh both its geometric deficit and stationary log-ratio are nonzero.
Thus the conditional positive route is populated by a genuine small-mesh
family rather than a zero-source or fixed-mesh witness. -/
theorem nontrivial_source_backed_family_exists
    (n : ℕ) (hn : 1 ≤ n) (h₀ kappa : ℝ) (hκ : kappa ≠ 0) :
    ∃ F : RecognitionRatioFamily,
      F.IsAdmissible h₀ kappa ((n : ℝ) / |kappa|)
          ((n : ℝ) * h₀ ^ 3 / 6) ∧
      (∀ h, kappa * F.deficit h = (n : ℝ) * h ^ 2) ∧
      (∀ h, h ≠ 0 →
        F.deficit h ≠ 0 ∧ 0 < Real.log (F.ratio h)) := by
  refine ⟨quadraticSourceFamily n kappa,
    quadraticSourceFamily_isAdmissible n hn h₀ kappa hκ, ?_, ?_⟩
  · intro h
    show kappa * ((n : ℝ) / kappa * h ^ 2) = (n : ℝ) * h ^ 2
    field_simp
  · intro h hh
    exact ⟨quadraticSourceFamily_deficit_ne_zero n hn kappa h hκ hh,
      quadraticSourceFamily_logRatio_pos n hn kappa h hκ hh⟩

/-! ## 5. Exact P2.1 terminal package -/

/-- A proposition-valued certificate collecting the exact P2.1 terminal.
Unlike the historical status records, every field is mathematical content. -/
structure RecognitionRatioSubstrateBlockerCertificate : Prop where
  coboundary_cycle_telescope :
    ∀ {Λ : Type*} {s : Λ → Λ → ℝ}, IsCoboundary s →
      ∀ (v : ℕ → Λ) (m : ℕ), v m = v 0 →
        ∑ k ∈ Finset.range m, s (v k) (v (k + 1)) = 0
  imposed_budget_is_circular :
    ∀ {n : ℕ} (t : Fin n → ℝ) (kappa delta : ℝ),
      (∑ i, t i = kappa * delta) →
        naiveLogRatio n t = kappa * delta
  bare_ledger_cannot_recover_signed_source :
    ¬ ∃ select : RecognitionLedger.RecognitionLedger (Fin 2) → ℝ,
      RecoversSignedSourceFromBareLedger select
  coupling_derives_ratio :
    ∀ {H : Type*} (C : DeficitSourceConstitutiveCoupling H) (σ : H),
      |Real.log ((ratioBridgeFromDeficitSourceCoupling C).xRatio σ)
          - C.kappa σ * C.geometricDeficit σ|
        ≤ (C.channels : ℝ) / 6 * C.meshScale ^ 3
  nontrivial_source_family :
    ∀ (n : ℕ), 1 ≤ n → ∀ (h₀ kappa : ℝ), kappa ≠ 0 →
      ∃ F : RecognitionRatioFamily,
        F.IsAdmissible h₀ kappa ((n : ℝ) / |kappa|)
            ((n : ℝ) * h₀ ^ 3 / 6) ∧
        (∀ h, kappa * F.deficit h = (n : ℝ) * h ^ 2) ∧
        (∀ h, h ≠ 0 →
          F.deficit h ≠ 0 ∧ 0 < Real.log (F.ratio h))

/-- **P2.1 HEADLINE THEOREM (strongest honest terminal).**

The exact missing premise preventing `recognition_ratio_derived` from the
bare `RecognitionLedger` is `DeficitSourceConstitutiveCoupling`: a signed
source `c_sigma = kappa_sigma * delta_sigma` linearly coupled to total
strain in the J-cost action.  Coboundary circulation gives zero, an imposed
budget is circular, and the bare J-ledger cannot choose between opposite
source orientations.  With that named premise supplied, J-stationarity
derives the ratio bridge, and a nontrivial uniform source-backed family
exists. -/
theorem recognition_ratio_derived_bare_ledger_terminal :
    RecognitionRatioSubstrateBlockerCertificate where
  coboundary_cycle_telescope := by
    intro Λ s hs v m hcycle
    exact closedCycle_coboundary_sum_eq_zero hs v m hcycle
  imposed_budget_is_circular := by
    intro n t kappa delta hbudget
    exact budget_implies_ratio_without_stationarity t kappa delta hbudget
  bare_ledger_cannot_recover_signed_source :=
    no_bare_ledger_selector_recovers_signed_source
  coupling_derives_ratio := by
    intro H C σ
    exact recognition_ratio_derived_of_deficit_source_coupling C σ
  nontrivial_source_family := by
    intro n hn h₀ kappa hκ
    exact nontrivial_source_backed_family_exists n hn h₀ kappa hκ

#print axioms recognition_ratio_derived_bare_ledger_terminal
#print axioms no_bare_ledger_selector_recovers_signed_source
#print axioms recognition_ratio_derived_of_deficit_source_coupling
#print axioms nontrivial_source_backed_family_exists

end SevenGaps
end Gravity
end IndisputableMonolith
