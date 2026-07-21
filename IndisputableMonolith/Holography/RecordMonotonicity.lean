import Mathlib
import IndisputableMonolith.Holography.CellInjection

/-!
# RecordMonotonicity: no free erasure ⇒ weak complementarity (on the forced cell)

Step 3 of the entropy-fork development chain (panel `holo_unconditional_20260701`; step 1
was the cell-injection test `CellInjection.lean`, step 2 the Clausius selector
`ClausiusSelector.lean`; plan `plans/RS_Entropy_Fork_Development_Plan_20260701.html`).
The full holography manuscript (`holography/papers/Recognition_Holography_20260629.tex`) confesses
that recognition complementarity is its strongest premise and isolates the minimal
sufficient form: *weak complementarity* = an injection from physical bulk states into the
boundary letter space. This module derives that injection on the forced D=3 cell from
record accounting, replacing the monolithic complementarity premise with two strictly
weaker, independently falsifiable inputs.

## The argument, and what carries which tag

1. **The ledger books balance (THEOREM).** Boundary heat is the posted record flux,
   channel by channel (the same posting rule as `ClausiusSelector.stepHeat`, here summed
   over the six face channels). The flux is EXACT against the record-weight potential:
   along any bulk trajectory, `pathHeat = Φ(end) − Φ(start)` (`books_balance`). So a
   posted bit can never be silently destroyed: an erasure (weight drop) is always exported
   as negative boundary heat (`erasure_exports_debit`), and a zero-heat step preserves the
   record weight exactly (`no_free_erasure`). This is the generalized-second-law
   bookkeeping — "no free erasure of the posted record" — proved, not assumed, for the
   posting rule itself.

2. **Gauge classes are exactly kernel cosets (THEOREM, `decide`).** Call two bulk
   configurations gauge-related when they carry the same boundary record (`gaugeRel`).
   This relation is exactly the coset structure of the 16-element record kernel isolated
   by the injection test: `gaugeRel c c' ↔ xorCfg c c' ∈ recordKernel`
   (`gauge_iff_kernel`). The only candidate violations of complementarity are the 16
   global parity moves — a named, finite, explicitly classified set.

3. **No posting-compatible protocol separates a gauge pair (THEOREM).** A dynamics `U`
   is *record-compatible* when it never manufactures a boundary distinction between two
   states whose difference was never posted; `recordCompatible_iff_no_free_record` shows
   this is literally the "no free record" condition — the difference-ledger form of the
   no-free-erasure discipline of (1), now imposed on dynamics. Any finite protocol built
   from record-compatible steps preserves gauge equivalence (`no_protocol_separates`), so
   gauge pairs are operationally inseparable (`gauge_never_separated`).

4. **Weak complementarity (THEOREM on the quotient; conditional operationally).**
   Quotient the cell by `gaugeRel`: the record readout descends to an INJECTION
   `physRecord : PhysState ↪ records` (`weak_complementarity`) — bulk physical states
   embed in the boundary record space, with 16 physical states = 16 posted records = 4
   posted bits against a 6-bit boundary capacity (`holographic_bound_of_weak_comp`).
   Operationally: for ANY notion of physical distinguishability that is witnessed by
   posting-compatible protocols (`KernelIsGauge dist`), record-equal states are
   physically indistinguishable (`weak_complementarity_of_gsl`).

## What is input (honest tags, per `soul.mdc`)

* INPUT (MODEL, inherited): boundary heat = posted record flux, one signed bit per face
  flip (the posting rule of `ClausiusSelector`, applied per channel).
* INPUT (HYPOTHESIS, named, falsifiable): `KernelIsGauge dist` — every physical
  distinguishing experiment factors through posting-compatible protocols. FALSIFIER
  (`kernelIsGauge_falsifier`): exhibit a physical process separating two record-equal
  configurations, i.e. a dynamics that creates a boundary distinction with no posted
  source. That would realize the manuscript's countermodel and break weak
  complementarity.
* DERIVED (THEOREM, axiom-clean): everything else — the balance law, the coset
  classification, protocol closure, the quotient injection, and the counting.

Net effect on the manuscript: the single monolithic complementarity premise is replaced
by (a) the posting rule already carried by the Clausius selector, and (b) the
no-free-record condition on dynamics. The erasure half of the GSL is DISCHARGED (it is
the balance theorem); only the creation half remains a physical premise. This is
strictly weaker than what the manuscript assumed, which is the panel's step-3 target.
-/

namespace IndisputableMonolith
namespace Holography
namespace RecordMonotonicity

open CellInjection

/- The `decide` proofs enumerate pairs over `Fin 256`; same budget rationale as
`CellInjection`: the kernel still checks every case. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## 1. The ledger books balance: no free erasure is a THEOREM of the posting rule -/

/-- **Per-channel posted flux** between two boundary records: the signed sum, over the
face channels, of one bit per record flip (`+1` up, `−1` down, `0` unchanged). This is
the six-channel form of `ClausiusSelector.stepHeat` — the same MODEL input (boundary
heat = posted ledger flux), applied per face. -/
def recordFlux (r r' : List Bool) : ℤ :=
  (List.zipWith (fun b b' => (if b' then (1 : ℤ) else 0) - (if b then 1 else 0)) r r').sum

/-- **Record weight**: total posted bits of a boundary record (the record potential). -/
def recordWeight (r : List Bool) : ℤ :=
  (r.map (fun b => if b then (1 : ℤ) else 0)).sum

/-- The flux is exact: between equal-length records it is the difference of the record
weights. Nothing is created or destroyed off the books. -/
theorem recordFlux_eq_weight_sub (r : List Bool) :
    ∀ r' : List Bool, r.length = r'.length →
      recordFlux r r' = recordWeight r' - recordWeight r := by
  induction r with
  | nil =>
    intro r' h
    cases r' with
    | nil => simp [recordFlux, recordWeight]
    | cons b' t' => simp at h
  | cons b t ih =>
    intro r' h
    cases r' with
    | nil => simp at h
    | cons b' t' =>
      have ht : t.length = t'.length := by simpa using h
      have hrec := ih t' ht
      simp only [recordFlux, recordWeight, List.zipWith_cons_cons, List.map_cons,
        List.sum_cons] at hrec ⊢
      rw [hrec]
      ring

/-- A record posts zero flux against itself. -/
theorem recordFlux_self (r : List Bool) : recordFlux r r = 0 := by
  rw [recordFlux_eq_weight_sub r r rfl]
  ring

/-- The record potential of a cell configuration: posted bits on its six faces. -/
def cellPotential (c : CellCfg) : ℤ := recordWeight (faceRecord c)

/-- Boundary heat of one bulk step: the posted flux across the six face channels. -/
def stepHeatCell (c c' : CellCfg) : ℤ := recordFlux (faceRecord c) (faceRecord c')

theorem faceRecord_length (c : CellCfg) : (faceRecord c).length = 6 := rfl

/-- One bulk step posts exactly the change of the record potential: `δQ = ΔΦ`. -/
theorem stepHeatCell_eq_potential (c c' : CellCfg) :
    stepHeatCell c c' = cellPotential c' - cellPotential c :=
  recordFlux_eq_weight_sub _ _ (by rw [faceRecord_length, faceRecord_length])

/-- Total boundary heat along a bulk trajectory (step-by-step posted flux). -/
def pathHeatCell : List CellCfg → ℤ
  | [] => 0
  | [_] => 0
  | c :: c' :: rest => stepHeatCell c c' + pathHeatCell (c' :: rest)

/-- **The books balance (the GSL's erasure half, as a THEOREM).** Along any bulk
trajectory the total posted heat equals the change of the record potential. A record bit
can therefore never disappear silently: every erasure along the way is exported to the
boundary as negative heat, every posting imported as positive heat. -/
theorem books_balance (c : CellCfg) (p : List CellCfg) :
    pathHeatCell (c :: p) = cellPotential (p.getLastD c) - cellPotential c := by
  induction p generalizing c with
  | nil => simp [pathHeatCell]
  | cons c' rest ih =>
    simp only [pathHeatCell, List.getLastD_cons, stepHeatCell_eq_potential, ih c']
    ring

/-- **No free erasure, step form.** A step that posts nothing preserves the record
weight exactly; erasing a posted bit without exporting the debit is impossible under the
posting rule. -/
theorem no_free_erasure (c c' : CellCfg) (h : stepHeatCell c c' = 0) :
    cellPotential c' = cellPotential c := by
  have hb := stepHeatCell_eq_potential c c'
  omega

/-- Erasure exports the debit: any weight decrease shows up as strictly negative
boundary heat (double entry — the debit lands at the boundary, it is not destroyed). -/
theorem erasure_exports_debit (c c' : CellCfg) (h : cellPotential c' < cellPotential c) :
    stepHeatCell c c' < 0 := by
  rw [stepHeatCell_eq_potential]
  omega

/-- **Record monotonicity** (the GSL predicate on trajectories): the record potential
never decreases along the path. -/
def RecordMonotone (p : List CellCfg) : Prop :=
  List.IsChain (fun c c' => cellPotential c ≤ cellPotential c') p

/-- A closed-system trajectory — one that exports no heat at any step — is
record-monotone. (With the balance theorem: the GSL for the posted record is bookkeeping,
not an extra law.) -/
theorem recordMonotone_of_no_export (p : List CellCfg)
    (h : List.IsChain (fun c c' => 0 ≤ stepHeatCell c c') p) : RecordMonotone p := by
  refine List.IsChain.imp ?_ h
  intro c c' hcc
  have hb := stepHeatCell_eq_potential c c'
  omega

/-! ## 2. Gauge classes are exactly the kernel cosets -/

/-- **Gauge relation**: two bulk configurations carry the same boundary record. The
candidate "physically identical" relation of the fork selector (an unposted difference is
not a performed distinction). -/
def gaugeRel (c c' : CellCfg) : Prop := faceRecord c = faceRecord c'

instance : DecidableRel gaugeRel :=
  fun c c' => inferInstanceAs (Decidable (faceRecord c = faceRecord c'))

theorem gaugeRel_equivalence : Equivalence gaugeRel :=
  ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- Gauge motion is heat-free: a gauge step posts nothing on any channel. -/
theorem gauge_step_zero_heat (c c' : CellCfg) (h : gaugeRel c c') :
    stepHeatCell c c' = 0 := by
  have h' : faceRecord c = faceRecord c' := h
  unfold stepHeatCell
  rw [h']
  exact recordFlux_self _

/-- Silent moves are exactly the kernel (re-export of the injection test's
classification). -/
theorem silent_iff_kernel (d : CellCfg) :
    (∀ c : CellCfg, faceRecord (xorCfg c d) = faceRecord c) ↔ d ∈ recordKernel :=
  invisible_iff_kernel d

theorem mem_recordKernel_iff (d : CellCfg) :
    d ∈ recordKernel ↔ faceRecord d = faceRecord cell0 := by
  simp [recordKernel]

/-- Gauge relation, kernel-predicate form (checked over all 65 536 pairs). -/
theorem gauge_iff_kernel_record :
    ∀ c c' : CellCfg, gaugeRel c c' ↔ faceRecord (xorCfg c c') = faceRecord cell0 := by
  decide

/-- **Gauge classes = kernel cosets.** Two configurations are gauge-related iff their
difference lies in the 16-element record kernel of `CellInjection`. The entire candidate
failure of complementarity is the coset structure of one named finite group. -/
theorem gauge_iff_kernel (c c' : CellCfg) :
    gaugeRel c c' ↔ xorCfg c c' ∈ recordKernel := by
  rw [mem_recordKernel_iff]
  exact gauge_iff_kernel_record c c'

/-! ## 3. No posting-compatible protocol separates a gauge pair -/

/-- A bulk dynamics is **record-compatible** when it never turns an unposted difference
into a posted one: gauge-related inputs go to gauge-related outputs. -/
def RecordCompatible (U : CellCfg → CellCfg) : Prop :=
  ∀ c c', gaugeRel c c' → gaugeRel (U c) (U c')

/-- A dynamics **creates a free record** when some gauge pair (identical posted data,
zero-heat difference channel) is driven to distinct boundary records — a boundary
distinction with no posted source. -/
def CreatesFreeRecord (U : CellCfg → CellCfg) : Prop :=
  ∃ c c', gaugeRel c c' ∧ ¬ gaugeRel (U c) (U c')

/-- Record compatibility IS the no-free-record condition: the GSL discipline of Part 1
(nothing enters or leaves the books unposted), imposed on dynamics. -/
theorem recordCompatible_iff_no_free_record (U : CellCfg → CellCfg) :
    RecordCompatible U ↔ ¬ CreatesFreeRecord U := by
  constructor
  · rintro hU ⟨c, c', hcc, hne⟩
    exact hne (hU c c' hcc)
  · intro h c c' hcc
    by_contra hne
    exact h ⟨c, c', hcc, hne⟩

/-- Run a finite protocol (a list of bulk evolution steps) on a configuration. -/
def runProtocol (Us : List (CellCfg → CellCfg)) (c : CellCfg) : CellCfg :=
  Us.foldl (fun x U => U x) c

/-- **Protocol closure.** Any finite protocol whose every step is record-compatible
preserves gauge equivalence: it cannot separate states whose difference was never
posted. -/
theorem no_protocol_separates (Us : List (CellCfg → CellCfg))
    (hUs : ∀ U ∈ Us, RecordCompatible U) :
    ∀ c c', gaugeRel c c' → gaugeRel (runProtocol Us c) (runProtocol Us c') := by
  induction Us with
  | nil => intro c c' h; exact h
  | cons U rest ih =>
    intro c c' h
    have h1 : gaugeRel (U c) (U c') := hUs U List.mem_cons_self c c' h
    have h2 := ih (fun V hV => hUs V (List.mem_cons_of_mem U hV)) (U c) (U c') h1
    simpa [runProtocol, List.foldl_cons] using h2

/-- Two configurations are **operationally separated** when some posting-compatible
protocol drives them to distinct boundary records. -/
def Separated (c c' : CellCfg) : Prop :=
  ∃ Us : List (CellCfg → CellCfg), (∀ U ∈ Us, RecordCompatible U) ∧
    ¬ gaugeRel (runProtocol Us c) (runProtocol Us c')

/-- **Gauge pairs are operationally inseparable** by posting-compatible protocols. -/
theorem gauge_never_separated (c c' : CellCfg) (h : gaugeRel c c') : ¬ Separated c c' := by
  rintro ⟨Us, hUs, hne⟩
  exact hne (no_protocol_separates Us hUs c c' h)

/-! ## 4. Weak complementarity: the injection on the gauge quotient -/

/-- The gauge setoid on cell configurations. -/
def gaugeSetoid : Setoid CellCfg := ⟨gaugeRel, gaugeRel_equivalence⟩

/-- **Physical states of the cell**: bulk configurations modulo gauge (= modulo the
16-element record kernel, by `gauge_iff_kernel`). -/
def PhysState : Type := Quotient gaugeSetoid

/-- The physical state carried by a bulk configuration. -/
def physState (c : CellCfg) : PhysState := Quotient.mk gaugeSetoid c

/-- The boundary record of a physical state (well-defined by construction). -/
def physRecord : PhysState → List Bool :=
  Quotient.lift faceRecord (fun _ _ h => h)

@[simp] theorem physRecord_mk (c : CellCfg) : physRecord (physState c) = faceRecord c :=
  rfl

/-- **WEAK COMPLEMENTARITY (quotient form, THEOREM).** The boundary record readout is
injective on physical states: distinct physical states of the bulk carry distinct
boundary records. This is the injection `bulk_phys(B) ↪ records(∂B)` the holography
manuscript assumes; here it is a theorem of the gauge quotient. -/
theorem weak_complementarity : Function.Injective physRecord := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro c c' h
  exact Quotient.sound h

/-- Every physical state's record is a posted record. -/
theorem physRecord_mem_image (s : PhysState) :
    physRecord s ∈ Finset.univ.image faceRecord := by
  refine Quotient.inductionOn s ?_
  intro c
  exact Finset.mem_image_of_mem faceRecord (Finset.mem_univ c)

/-- No ghost records: every posted record is realized by a physical state. With
`weak_complementarity`, physical states biject with posted records. -/
theorem physRecord_surjective_on_records :
    ∀ r ∈ Finset.univ.image faceRecord, ∃ s : PhysState, physRecord s = r := by
  intro r hr
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
  exact ⟨physState c, rfl⟩

/-- 16 posted records = 16 physical states = 4 posted bits (re-export of the cell rank
computation of the injection test). -/
theorem physState_records_card : (Finset.univ.image faceRecord).card = 16 :=
  record_image_card

/-- **The holographic bound through weak complementarity.** The physical states of the
8-vertex bulk embed (via `weak_complementarity` + `physRecord_mem_image`) into the
posted-record set: 16 states = 4 posted bits, strictly inside the 6-bit boundary record
capacity — the cell-scale instance of the boundary access law
(`HolographicAccessBound.access_bounded_by_aperture`). -/
theorem holographic_bound_of_weak_comp :
    (Finset.univ.image faceRecord).card ≤ 2 ^ 6 := by
  rw [physState_records_card]
  norm_num

/-! ## 5. The conditional headline and its falsifier -/

/-- **The named premise (`KernelIsGauge`, HYPOTHESIS).** A physical distinguishability
relation `dist` respects the ledger when every physical distinction is witnessed by a
posting-compatible protocol. This is the operational content of "the record kernel is
gauge": distinguishing bulk states requires posting the difference. -/
def KernelIsGauge (dist : CellCfg → CellCfg → Prop) : Prop :=
  ∀ c c', dist c c' → Separated c c'

/-- **WEAK COMPLEMENTARITY FROM THE GSL (the step-3 headline).** For any physical
distinguishability witnessed by posting-compatible protocols, record-equal bulk states
are physically indistinguishable: the manuscript's complementarity injection holds with
the monolithic premise replaced by the no-free-record discipline. -/
theorem weak_complementarity_of_gsl (dist : CellCfg → CellCfg → Prop)
    (hG : KernelIsGauge dist) (c c' : CellCfg) (h : gaugeRel c c') : ¬ dist c c' :=
  fun hd => gauge_never_separated c c' h (hG c c' hd)

/-- **The falsifier horn, stated.** If any physical process distinguishes two
record-equal configurations (a global parity move made observable), then `KernelIsGauge`
fails for that physics and weak complementarity breaks — the manuscript's countermodel is
realized. The fork inside step 3 is honest: this module isolates the breaking set (the 16
kernel moves); it does not prove no physics ever separates them. -/
theorem kernelIsGauge_falsifier (dist : CellCfg → CellCfg → Prop) (c c' : CellCfg)
    (h : gaugeRel c c') (hd : dist c c') : ¬ KernelIsGauge dist :=
  fun hG => weak_complementarity_of_gsl dist hG c c' h hd

/-! ## 6. Bundled target + certificate handle -/

/-- **The record-monotonicity target.** (1) Boundary heat is exact against the record
potential (no free erasure — the GSL's erasure half as bookkeeping); (2) gauge classes
are exactly the kernel cosets; (3) posting-compatible protocols never separate gauge
pairs; (4) the record readout is injective on physical states (weak complementarity);
(5) under the named `KernelIsGauge` premise, record-equal states are physically
indistinguishable; (6) 16 physical states = 4 posted bits within the 6-bit boundary
capacity. -/
def target_record_monotonicity : Prop :=
  (∀ c c' : CellCfg, stepHeatCell c c' = cellPotential c' - cellPotential c)
  ∧ (∀ c c' : CellCfg, gaugeRel c c' ↔ xorCfg c c' ∈ recordKernel)
  ∧ (∀ (Us : List (CellCfg → CellCfg)), (∀ U ∈ Us, RecordCompatible U) →
      ∀ c c', gaugeRel c c' → gaugeRel (runProtocol Us c) (runProtocol Us c'))
  ∧ Function.Injective physRecord
  ∧ (∀ (dist : CellCfg → CellCfg → Prop), KernelIsGauge dist →
      ∀ c c', gaugeRel c c' → ¬ dist c c')
  ∧ (Finset.univ.image faceRecord).card = 16

theorem target_record_monotonicity_holds : target_record_monotonicity :=
  ⟨stepHeatCell_eq_potential, gauge_iff_kernel, no_protocol_separates,
   weak_complementarity, weak_complementarity_of_gsl, physState_records_card⟩

/-- Verify-target certificate handle (`#print axioms`-gated). -/
theorem recordMonotonicityCert : target_record_monotonicity :=
  target_record_monotonicity_holds

end RecordMonotonicity
end Holography
end IndisputableMonolith
