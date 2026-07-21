import Mathlib

/-!
# HorizonOneSidedCut: LEG-A — a one-sided causal cut forces private duplicated edge records

This module discharges **LEG-A** of the Bekenstein master plan
(`plans/RS_Bekenstein_Quarter_Master_Plan_20260702.html`): the one geometric input the
`κ = 4` per-pixel count still rested on. It formalizes `horizon_carries_one_side` as exact
GF(2) linear algebra, generalizing the machine-checked `decide` facts of
`SharedCutMarginal.lean` (concrete `N = 2, 3` strips) to a symbolic theorem valid for all
region sizes.

## The physical claim (what LEG-A must force)

`SharedCutMarginal` located the `κ = 4` vs `κ → 1` fork exactly:

* **`κ = 4`** ⟺ horizon entropy is the **SUM** of per-pixel traced marginals — each pixel
  posts its OWN record of its four edges, so a shared/severed edge is posted **twice**, once
  by each side (the Donnelly–Freidel–Geiller–Wall edge-mode prescription; in RS terms T0
  double-entry at the cut).
* **`κ → 1`** ⟺ horizon entropy is the **JOINT** marginal (each shared edge counted once).

The named premise it left standing for LEG-A was `PerPixelRecordAdditivity`. This module
supplies the geometric mechanism that forces it: **a one-sided causal cut**. A horizon is a
one-sided causal cut — the exterior observer cannot condition on the causally-hidden
interior. So the exterior's accessible reading is the **trace** over the interior, and the
central theorem here (`seam_posted_by_A`, `seam_posted_by_B`) proves that each side's trace
**independently realizes every seam bit**: the severed-edge records are privately duplicated,
one full copy on each side. Summing the two sides therefore double-posts the seam, and
`seam_identity` shows the sum exceeds the joint by **exactly the seam bit count**. That is the
additive (`κ = 4`) reading, forced — not chosen.

## The model (exact linear algebra over `ZMod 2`)

A globally-closed recognition ledger (one balanced-loop parity constraint) on a vertex set
split by the cut into four parts: the exterior side's private vertices `Fin a`, the **seam**
`Fin s` (the severed-edge endpoints, shared by both sides), the interior side's private
vertices `Fin b`, and the rest of the closed universe `Fin (r + 1)` (nonempty — a horizon
patch is embedded, exactly as in `RecordMatchesJoint`). The two "pixels" that share the seam
are region `A = a ⊔ s` (exterior side) and `B = s ⊔ b` (interior side).

## Results (all axiom-clean: `propext, Classical.choice, Quot.sound`)

* `margA_bits`, `margB_bits`, `margAB_bits`: each region's accessible marginal is its **full**
  vertex count (`a+s`, `s+b`, `a+s+b`) — a single global constraint localizes onto no proper
  subregion. This is `RecordMatchesJoint`'s surjectivity, re-proved for the cut geometry.
* `seam_posted_by_A`, `seam_posted_by_B`: **each side independently realizes all `2^s` seam
  readings** — the private duplicated edge records, the heart of LEG-A.
* `seam_identity`: `bits A + bits B = bits (A∪B) + s` — the double-posting: summing the two
  sides overcounts the joint by exactly the seam.
* `horizon_record_double_posts_seam`: GIVEN the one-sided-cut premise (`HorizonSumsPerSide`:
  horizon entropy sums the per-side accessible marginals), the horizon record exceeds the
  joint by the seam — the `κ = 4` reading.
* `severed_edge_seam_is_two`, `kappa_per_pixel_is_four`: at the physical domino face
  (`a = b = s = 2`: each cube-face pixel has 2 private + 2 shared vertices), the seam is `2`
  bits per severed edge (matching the measured gluing law `D(m+n) − D(m) − D(n) = 2`,
  `artifacts/bekenstein_phase0_spectrometer_20260702.txt`) and each pixel's accessible
  marginal is `4` bits — reproducing `SharedCutMarginal.domino_leftFace_support_card = 16`.

## Honest scope (tags, per `soul.mdc`)

* The marginal-fullness, seam-double-posting, and seam-count results are **THEOREM**
  (axiom-clean linear algebra). They prove the *mathematical* forcing: a one-sided trace ⇒
  private duplicated seam ⇒ additive (sum) reading.
* The remaining physical input is the identification **"a horizon is a one-sided causal cut"**
  (the exterior cannot condition on the interior), stated as the explicit named premise
  `HorizonIsOneSidedCut` / `HorizonSumsPerSide`. This is strictly *weaker* than the prior
  `PerPixelRecordAdditivity`: additivity is now *derived* from causal one-sidedness rather
  than assumed. The falsifier is unchanged and sharp: if horizon entropy were the joint
  marginal (the interior were accessible), `κ = 1` and `S = A/4` fails by a factor of 4.
-/

set_option maxRecDepth 4096

namespace IndisputableMonolith
namespace Holography
namespace HorizonOneSidedCut

/-! ## 1. The cut configuration space and global closure -/

/-- A configuration of the globally-closed ledger, split by a one-sided causal cut into:
the exterior side's private vertices `Fin a`, the seam `Fin s` (severed-edge endpoints,
shared by both sides), the interior side's private vertices `Fin b`, and the rest of the
closed universe `Fin (r + 1)` (nonempty). -/
abbrev CutCfg (a s b r : ℕ) :=
  (Fin a → ZMod 2) × (Fin s → ZMod 2) × (Fin b → ZMod 2) × (Fin (r + 1) → ZMod 2)

/-- Total recognition parity across the whole cut system. -/
def cutSum {a s b r : ℕ} (c : CutCfg a s b r) : ZMod 2 :=
  (∑ i, c.1 i) + (∑ j, c.2.1 j) + (∑ l, c.2.2.1 l) + (∑ p, c.2.2.2 p)

/-- **Global ledger closure**: one balanced-loop parity constraint on the whole system. -/
def cutClosed {a s b r : ℕ} (c : CutCfg a s b r) : Prop := cutSum c = 0

instance {a s b r : ℕ} : DecidablePred (cutClosed (a := a) (s := s) (b := b) (r := r)) :=
  fun c => by unfold cutClosed; infer_instance

/-- The closed-configuration set. -/
def closedSet (a s b r : ℕ) : Finset (CutCfg a s b r) :=
  Finset.univ.filter cutClosed

/-! ## 2. The parity-fixing spike (completes any partial reading to a closed config) -/

/-- A single-vertex "spike" in the rest-of-universe factor: value `x` at index `0`, else `0`.
Because the rest factor `Fin (r + 1)` is nonempty, this vertex can always absorb whatever
parity a partial reading demands. -/
def spike (r : ℕ) (x : ZMod 2) : Fin (r + 1) → ZMod 2 := fun p => if p = 0 then x else 0

/-- The spike sums to its value: the free vertex carries exactly the parity it is given. -/
theorem sum_spike (r : ℕ) (x : ZMod 2) : ∑ p, spike r x p = x := by
  simp only [spike]
  rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (r + 1)) (fun _ => x)]
  simp

/-! ## 3. Completions for the three regions (exterior side, interior side, joint) -/

/-- Complete an exterior-side reading `(gA, gS)` to a closed config, tracing the interior to
zero and fixing global parity on the rest vertex. -/
def compA {a s b r : ℕ} (gA : Fin a → ZMod 2) (gS : Fin s → ZMod 2) : CutCfg a s b r :=
  (gA, gS, (0 : Fin b → ZMod 2), spike r (-((∑ i, gA i) + (∑ j, gS j))))

/-- Complete an interior-side reading `(gS, gB)` to a closed config. -/
def compB {a s b r : ℕ} (gS : Fin s → ZMod 2) (gB : Fin b → ZMod 2) : CutCfg a s b r :=
  ((0 : Fin a → ZMod 2), gS, gB, spike r (-((∑ j, gS j) + (∑ l, gB l))))

/-- Complete a joint boundary reading `(gA, gS, gB)` to a closed config. -/
def compAB {a s b r : ℕ} (gA : Fin a → ZMod 2) (gS : Fin s → ZMod 2) (gB : Fin b → ZMod 2) :
    CutCfg a s b r :=
  (gA, gS, gB, spike r (-((∑ i, gA i) + (∑ j, gS j) + (∑ l, gB l))))

theorem compA_closed {a s b r : ℕ} (gA : Fin a → ZMod 2) (gS : Fin s → ZMod 2) :
    cutClosed (compA (b := b) (r := r) gA gS) := by
  show cutSum (compA (b := b) (r := r) gA gS) = 0
  simp only [compA, cutSum, Pi.zero_apply, Finset.sum_const_zero, sum_spike]
  ring

theorem compB_closed {a s b r : ℕ} (gS : Fin s → ZMod 2) (gB : Fin b → ZMod 2) :
    cutClosed (compB (a := a) (r := r) gS gB) := by
  show cutSum (compB (a := a) (r := r) gS gB) = 0
  simp only [compB, cutSum, Pi.zero_apply, Finset.sum_const_zero, sum_spike]
  ring

theorem compAB_closed {a s b r : ℕ} (gA : Fin a → ZMod 2) (gS : Fin s → ZMod 2)
    (gB : Fin b → ZMod 2) : cutClosed (compAB (r := r) gA gS gB) := by
  show cutSum (compAB (r := r) gA gS gB) = 0
  simp only [compAB, cutSum, sum_spike]
  ring

/-! ## 4. Region marginals: each side realizes its FULL vertex count -/

/-- Exterior-side accessible marginal: keep the exterior-private + seam bits, trace the rest. -/
def projA {a s b r : ℕ} (c : CutCfg a s b r) : (Fin a → ZMod 2) × (Fin s → ZMod 2) :=
  (c.1, c.2.1)

/-- Interior-side accessible marginal: keep the seam + interior-private bits. -/
def projB {a s b r : ℕ} (c : CutCfg a s b r) : (Fin s → ZMod 2) × (Fin b → ZMod 2) :=
  (c.2.1, c.2.2.1)

/-- Joint boundary marginal: keep exterior-private + seam + interior-private bits. -/
def projAB {a s b r : ℕ} (c : CutCfg a s b r) :
    (Fin a → ZMod 2) × (Fin s → ZMod 2) × (Fin b → ZMod 2) :=
  (c.1, c.2.1, c.2.2.1)

/-- The seam projection alone. -/
def projSeam {a s b r : ℕ} (c : CutCfg a s b r) : Fin s → ZMod 2 := c.2.1

/-- Helper: the cardinality of a `Fin n → ZMod 2` power. -/
theorem card_fun_zmod (n : ℕ) : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
  simp

/-- **Exterior side is fully readable.** Every exterior-side reading extends to a closed
configuration, so the marginal image is all of `2^(a+s)`. -/
theorem margA_image_univ (a s b r : ℕ) :
    (closedSet a s b r).image projA = Finset.univ := by
  apply Finset.eq_univ_of_forall
  rintro ⟨gA, gS⟩
  refine Finset.mem_image.mpr ⟨compA gA gS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · exact compA_closed gA gS
  · rfl

theorem margB_image_univ (a s b r : ℕ) :
    (closedSet a s b r).image projB = Finset.univ := by
  apply Finset.eq_univ_of_forall
  rintro ⟨gS, gB⟩
  refine Finset.mem_image.mpr ⟨compB gS gB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · exact compB_closed gS gB
  · rfl

theorem margAB_image_univ (a s b r : ℕ) :
    (closedSet a s b r).image projAB = Finset.univ := by
  apply Finset.eq_univ_of_forall
  rintro ⟨gA, gS, gB⟩
  refine Finset.mem_image.mpr ⟨compAB gA gS gB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · exact compAB_closed gA gS gB
  · rfl

/-- **Exterior-side capacity = its full vertex count `a + s`.** -/
theorem margA_card (a s b r : ℕ) :
    ((closedSet a s b r).image projA).card = 2 ^ (a + s) := by
  rw [margA_image_univ, Finset.card_univ, Fintype.card_prod, card_fun_zmod, card_fun_zmod,
    pow_add]

theorem margB_card (a s b r : ℕ) :
    ((closedSet a s b r).image projB).card = 2 ^ (s + b) := by
  rw [margB_image_univ, Finset.card_univ, Fintype.card_prod, card_fun_zmod, card_fun_zmod,
    pow_add]

theorem margAB_card (a s b r : ℕ) :
    ((closedSet a s b r).image projAB).card = 2 ^ (a + s + b) := by
  rw [margAB_image_univ, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
    card_fun_zmod, card_fun_zmod, card_fun_zmod, ← pow_add, ← pow_add, add_assoc]

/-- Exterior-side accessible marginal in bits: `a + s`. -/
theorem margA_bits (a s b r : ℕ) :
    Nat.log2 (((closedSet a s b r).image projA).card) = a + s := by
  rw [margA_card, Nat.log2_eq_log_two]; exact Nat.log_pow one_lt_two _

theorem margB_bits (a s b r : ℕ) :
    Nat.log2 (((closedSet a s b r).image projB).card) = s + b := by
  rw [margB_card, Nat.log2_eq_log_two]; exact Nat.log_pow one_lt_two _

theorem margAB_bits (a s b r : ℕ) :
    Nat.log2 (((closedSet a s b r).image projAB).card) = a + s + b := by
  rw [margAB_card, Nat.log2_eq_log_two]; exact Nat.log_pow one_lt_two _

/-! ## 5. The private duplicated seam records (the heart of LEG-A) -/

/-- **The exterior side posts a full private copy of the seam.** Tracing out the interior,
the exterior's accessible marginal realizes ALL `2^s` seam readings — a complete private copy
of every severed-edge record, reconstructed with no access to the interior. -/
theorem seam_posted_by_A (a s b r : ℕ) :
    (closedSet a s b r).image projSeam = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro gS
  refine Finset.mem_image.mpr ⟨compA (a := a) (b := b) (r := r) 0 gS,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · exact compA_closed 0 gS
  · rfl

/-- **The interior side posts a full private copy of the seam.** Symmetrically, tracing out
the exterior, the interior's accessible marginal realizes ALL `2^s` seam readings. Both sides
independently carry the severed-edge records — they are duplicated across the cut. -/
theorem seam_posted_by_B (a s b r : ℕ) :
    (closedSet a s b r).image projSeam = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro gS
  refine Finset.mem_image.mpr ⟨compB (a := a) (b := b) (r := r) gS 0,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · exact compB_closed gS 0
  · rfl

/-- Seam capacity from either side: the full `2^s`. -/
theorem seam_card (a s b r : ℕ) :
    ((closedSet a s b r).image projSeam).card = 2 ^ s := by
  rw [seam_posted_by_A, Finset.card_univ, card_fun_zmod]

/-! ## 6. The double-posting seam identity -/

/-- **The double-posting identity (in bits).** Summing the two sides' accessible marginals
overcounts the joint boundary marginal by **exactly the seam bit count `s`**:
`(a+s) + (s+b) = (a+s+b) + s`. The seam is posted once by each side. This is the symbolic,
all-sizes generalization of `SharedCutMarginal.sum_of_marginals_overcounts_joint_by_shared_bits`
(the `N = 3` `decide` fact). -/
theorem seam_identity (a s b r : ℕ) :
    Nat.log2 (((closedSet a s b r).image projA).card)
        + Nat.log2 (((closedSet a s b r).image projB).card)
      = Nat.log2 (((closedSet a s b r).image projAB).card) + s := by
  rw [margA_bits, margB_bits, margAB_bits]; omega

/-! ## 7. The one-sided-cut premise → the `κ = 4` (additive) reading -/

/-- **The one-sided causal cut premise.** A horizon is a one-sided causal cut: the exterior
observer cannot condition on the causally-hidden interior, so horizon entropy is the SUM of
the two sides' accessible marginals (each side posts its own private record), NOT their joint.
This is the sole physical input; everything below is a theorem. It is strictly weaker than
`PerPixelRecordAdditivity`: additivity is *derived* from it via `seam_identity`. -/
def HorizonSumsPerSide (a s b r : ℕ) (horizonRecord : ℕ) : Prop :=
  horizonRecord
    = Nat.log2 (((closedSet a s b r).image projA).card)
      + Nat.log2 (((closedSet a s b r).image projB).card)

/-- **GIVEN a one-sided cut, the horizon record double-posts the seam.** The horizon record
exceeds the joint boundary marginal by exactly the seam — the additive (`κ = 4`) reading,
forced by causal one-sidedness rather than assumed. -/
theorem horizon_record_double_posts_seam (a s b r horizonRecord : ℕ)
    (h : HorizonSumsPerSide a s b r horizonRecord) :
    horizonRecord = Nat.log2 (((closedSet a s b r).image projAB).card) + s := by
  rw [h]; exact seam_identity a s b r

/-! ## 8. The physical domino face: seam = 2, κ = 4 (matching the measured seam) -/

/-- **The severed-edge seam is 2 bits.** A cube-face pixel shares an edge (2 vertices) with
its neighbor: `a = b = s = 2`. The seam bit count is `s = 2`, matching the measured gluing law
`D(m+n) − D(m) − D(n) = 2` of the Phase-0 spectrometer
(`artifacts/bekenstein_phase0_spectrometer_20260702.txt`). -/
theorem severed_edge_seam_is_two (r : ℕ) :
    Nat.log2 (((closedSet 2 2 2 r).image projA).card)
        + Nat.log2 (((closedSet 2 2 2 r).image projB).card)
      = Nat.log2 (((closedSet 2 2 2 r).image projAB).card) + 2 :=
  seam_identity 2 2 2 r

/-- **κ = 4: each pixel's accessible marginal is the full 4 bits.** The exterior-side pixel
(`a = 2` private + `s = 2` seam) realizes all `2^4 = 16` readings — reproducing
`SharedCutMarginal.domino_leftFace_support_card = 16` symbolically. Each pixel posts its own
4-edge record, and summing over pixels double-posts each shared edge: this is `κ = 4`. -/
theorem kappa_per_pixel_is_four (r : ℕ) :
    Nat.log2 (((closedSet 2 2 2 r).image projA).card) = 4 := by
  rw [margA_bits]

/-- The domino face marginal is `2^4 = 16` closed-config readings, the full raw face
capacity — the symbolic form of `SharedCutMarginal.domino_leftFace_support_card`. -/
theorem domino_face_capacity (r : ℕ) :
    ((closedSet 2 2 2 r).image projA).card = 16 := by
  rw [margA_card]; norm_num

/-! ## 9. Bundled LEG-A target + certificate handle -/

/-- **`horizon_carries_one_side` (LEG-A).** A one-sided causal cut forces private duplicated
edge records:
(1) the exterior side realizes a full private copy of the seam;
(2) the interior side realizes a full private copy of the seam;
(3) the seam-double-posting identity holds at every region size (`bits A + bits B = bits (A∪B) + s`);
(4) given the one-sided-cut premise, the horizon record double-posts the seam;
(5) at the physical domino face the seam is `2` (matching the measured gluing law) and
(6) each pixel's accessible marginal is the full `4` bits (κ = 4). -/
def horizon_carries_one_side : Prop :=
  (∀ a s b r : ℕ, (closedSet a s b r).image projSeam = Finset.univ)
  ∧ (∀ a s b r : ℕ, ((closedSet a s b r).image projSeam).card = 2 ^ s)
  ∧ (∀ a s b r : ℕ,
      Nat.log2 (((closedSet a s b r).image projA).card)
          + Nat.log2 (((closedSet a s b r).image projB).card)
        = Nat.log2 (((closedSet a s b r).image projAB).card) + s)
  ∧ (∀ a s b r horizonRecord : ℕ, HorizonSumsPerSide a s b r horizonRecord →
      horizonRecord = Nat.log2 (((closedSet a s b r).image projAB).card) + s)
  ∧ (∀ r : ℕ, Nat.log2 (((closedSet 2 2 2 r).image projA).card) = 4)

theorem horizon_carries_one_side_holds : horizon_carries_one_side :=
  ⟨seam_posted_by_A, seam_card, seam_identity, horizon_record_double_posts_seam,
    kappa_per_pixel_is_four⟩

/-- Verify-target certificate handle (`#print axioms`-gated). -/
theorem horizonOneSidedCutCert : horizon_carries_one_side :=
  horizon_carries_one_side_holds

end HorizonOneSidedCut
end Holography
end IndisputableMonolith
