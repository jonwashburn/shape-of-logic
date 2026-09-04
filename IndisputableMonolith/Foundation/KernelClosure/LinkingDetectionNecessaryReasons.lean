import Mathlib
import IndisputableMonolith.Foundation.LinkingNecessity
import IndisputableMonolith.Foundation.RecognitionToLinkingSeam
import IndisputableMonolith.Foundation.PublicSpineLinkingClosure
import IndisputableMonolith.Foundation.ParityClassDirections
import IndisputableMonolith.Foundation.ClosedObservableFramework

/-!
# Kernel closure census, row 3: linking detection

The kernel's third premise says space detects nontrivial linking of a circle.
Given it, `D = 3` is a theorem (`PublicSpineLinkingClosure.forces_D3`), and
`bare_recognition_does_not_force_DetectsNontrivialLinking` is the typed wall:
recognition structure alone does not deliver the detector. The census therefore
targets the **deformation-erasure principle** (DEP): a posted dual-pair
distinction is carried by a deformation-invariant integer pairing that does
not vanish on the realized pair. DEP plus the banked content-typed premises
gives the detector (`LinkingNecessity.dep_forces_D3`).

## What this module settles

**Lead route (conservation gives DEP): refuted as a derivation, located as a
restatement.** Ledger conservation (`ClosedObservableFramework.charge_conserved`)
does give a deformation-invariant charge on every orbit kinematics
(`orbit_charge_invariant`), and the balanced `σ`-charge of the dual pair is a
conserved pairing observable on every kinematics (`balancedCharge`). But it
vanishes on the pair as well as on the split (`balancedCharge_vanishes`), so it
separates nothing; and `dep_iff_separating_conserved_charge` shows DEP *is* the
statement that some conserved charge separates pair from split. Conservation
supplies the invariance half of DEP for free; the non-vanishing half is the whole
content. The route is circular, not false.

**Parity selector census: two of three inputs derived, one priced.**
`ParityClassDirections.balanced_equiangular_spanning_iff_three` selects `D = 3`
from three properties of the even parity class. Here:

* `balanced_iff_ne_one`: Balanced is a property of the class itself, true in
  every dimension with a second axis. DERIVED (given a second distinction).
* `spanning_iff_separating_and_nonempty`: Spanning is exactly "the class
  addresses axes individually" plus "there is an axis"; and separating fails
  only at `D = 2`. DERIVED from axis separability plus nontriviality.
* `isotropy_does_not_give_equiangular`: "no preferred direction" (isotropy of
  the direction second moment) holds for every `D ≥ 3` and does not deliver
  Equiangular. The row is REFUTED; Equiangular stays the priced premise.

So each selector has exactly one priced qualitative premise: DEP for the
linking selector, Equiangular (tightness of the class) for the parity selector.
`parity_selector_iff_dep_realizable` proves the two selectors are equivalent:
the parity triple holds iff some spatial dual-pair realization satisfies DEP.
That is the strongest available form of this row: two independent selectors,
one shared verdict, with the price named on each side.

**Decoy.** `fourDimRealization` still refutes "spatial realization alone", and
the `D = 4` parity class is balanced, spanning and isotropic while failing
Equiangular, so neither priced premise is a restatement of the others.

**Verdict.** PRICED PURCHASE at DEP (equivalently at Equiangular), with the
`D = 4` realization as countermodel. Exclusion of `D = 1, 2` needs nothing new.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace LinkingDetection

open LinkingNecessity ParityClassDirections ClosedFramework

/-! ## Stratum facts re-exported -/

/-- Detects gives three, unconditionally. -/
theorem row3_detects_forces_three :
    ∀ D : ℕ, PublicSpine.DetectsNontrivialLinking D → D = 3 :=
  PublicSpineLinkingClosure.forces_D3

/-- The typed wall: recognition supply toward linking coexists with a
realization on which DEP fails, so recognition structure alone does not supply
the detector. -/
theorem row3_wall :
    ∃ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
      ¬ DeformationErasurePrinciple R.kin :=
  RecognitionToLinkingSeam.recognition_supply_and_dep_obstruction.2

/-- DEP on a spatial dual-pair realization forces `D = 3`. -/
theorem row3_dep_forces_three (D : ℕ) (R : SpatialDualPairRealization D)
    (h : DeformationErasurePrinciple R.kin) : D = 3 :=
  dep_forces_D3 D R h

/-- The realization layer alone does not force DEP (`D = 4` decoy). -/
theorem row3_realization_alone_insufficient :
    ¬ DeformationErasurePrinciple fourDimRealization.kin :=
  unlinkedKinematics_refutes_dep

/-! ## Lead route: conservation gives DEP? -/

/-- The balanced `σ`-charge of the dual pair: total winding of debit and credit
loops. It is a deformation-invariant integer observable on every kinematics
because it is constant. -/
def balancedCharge (X : PairKinematics) : PairingObservable X where
  pairing := fun _ => 0
  deform_invariant := fun _ _ _ => rfl
  split_zero := rfl

/-- The balanced charge vanishes on the pair, as `dual_pair_balanced` says of the
dual loops (`+1 + (-1) = 0`). It separates nothing. -/
theorem balancedCharge_vanishes (X : PairKinematics) :
    (balancedCharge X).pairing X.pair = 0 := rfl

/-- The conservation route's actual content: DEP is precisely the existence of a
deformation-invariant integer charge that is zero on the split and nonzero on
the pair. Conservation supplies the first clause on any orbit; the second is the
whole premise. -/
theorem dep_iff_separating_conserved_charge (X : PairKinematics) :
    DeformationErasurePrinciple X ↔
      ∃ q : X.Config → ℤ,
        (∀ a b, X.deform a b → q a = q b) ∧ q X.split = 0 ∧ q X.pair ≠ 0 := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P.pairing, P.deform_invariant, P.split_zero, hP⟩
  · rintro ⟨q, hinv, hsplit, hpair⟩
    exact ⟨⟨q, hinv, hsplit⟩, hpair⟩

/-- Every kinematics carries a conserved pairing observable, and some kinematics
refute DEP: so "a conserved charge exists" does not imply DEP. -/
theorem conserved_observable_does_not_imply_dep :
    (∀ X : PairKinematics, Nonempty (PairingObservable X)) ∧
      ∃ X : PairKinematics, ¬ DeformationErasurePrinciple X :=
  ⟨fun X => ⟨balancedCharge X⟩,
   ⟨fourDimRealization.kin, unlinkedKinematics_refutes_dep⟩⟩

/-- Orbit kinematics of a closed observable framework: configurations are
states, and two states are deformation-related when the recognition map
connects them (symmetric-transitive closure of one step). -/
def orbitKinematics (F : ClosedObservableFramework) (pair split : F.S) :
    PairKinematics where
  Config := F.S
  deform := Relation.EqvGen (fun a b => b = F.T a)
  deform_refl := fun c => Relation.EqvGen.refl c
  deform_symm := fun h => Relation.EqvGen.symm _ _ h
  deform_trans := fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂
  pair := pair
  split := split

/-- Ledger conservation makes the framework charge a deformation invariant on
every orbit kinematics. This is the half of DEP that conservation delivers. -/
theorem orbit_charge_invariant (F : ClosedObservableFramework) (pair split : F.S)
    (a b : F.S) (h : (orbitKinematics F pair split).deform a b) :
    F.charge a = F.charge b := by
  induction h with
  | rel x y hxy => rw [hxy, F.charge_conserved]
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- If the framework carries an integer-quantized conserved charge that places
the pair and the split in different sectors, DEP holds on the orbit kinematics.
The sector separation is the premise; conservation only transports it. -/
theorem dep_of_quantized_separating_charge (F : ClosedObservableFramework)
    (pair split : F.S) (q : F.S → ℤ) (hq : ∀ s, q (F.T s) = q s)
    (hsplit : q split = 0) (hpair : q pair ≠ 0) :
    DeformationErasurePrinciple (orbitKinematics F pair split) := by
  refine ⟨⟨q, ?_, hsplit⟩, hpair⟩
  intro a b h
  induction h with
  | rel x y hxy => rw [hxy, hq]
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Decoy for the conservation route: on an orbit kinematics whose pair and
split are connected by recognition steps, no conserved charge separates them,
so DEP fails however much conservation holds. -/
theorem no_dep_when_pair_reaches_split (F : ClosedObservableFramework)
    (pair split : F.S)
    (hreach : (orbitKinematics F pair split).deform pair split) :
    ¬ DeformationErasurePrinciple (orbitKinematics F pair split) := by
  rintro ⟨P, hP⟩
  apply hP
  have h1 := P.deform_invariant _ _ hreach
  have h2 := P.split_zero
  exact h1.trans h2

/-! ## Parity selector census -/

/-- **Balanced is a class property.** In any dimension with a second axis, the
even parity class is balanced along every axis: toggling the axis together with
a second one negates the direction and preserves parity. Balanced fails only at
`D = 1`, where there is no partner axis. -/
theorem balanced_iff_ne_one (D : ℕ) : Balanced D ↔ D ≠ 1 := by
  constructor
  · intro h hD
    subst hD
    exact not_balanced_one h
  · intro hD i
    rcases Nat.lt_or_ge D 2 with hlt | hge
    · interval_cases D
      · exact absurd i.isLt (by omega)
      · exact absurd rfl hD
    · obtain ⟨j, hij⟩ : ∃ j : Fin D, j ≠ i := by
        by_cases h0 : (i : ℕ) = 0
        · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
        · exact ⟨⟨0, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
      set t : Finset (Fin D) := {i, j} with ht
      have hcard_t : t.card = 2 := by
        rw [ht, Finset.card_pair (Ne.symm hij)]
      have hi_t : i ∈ t := by simp [ht]
      have hj_t : j ∈ t := by simp [ht]
      apply Finset.sum_involution (fun s _ => symmDiff s t)
      · intro s _
        simp only [dir]
        by_cases hi : i ∈ s
        · have : i ∉ symmDiff s t := by
            simp [Finset.mem_symmDiff, hi, hi_t]
          simp [hi, this]
        · have : i ∈ symmDiff s t := by
            simp [Finset.mem_symmDiff, hi, hi_t]
          simp [hi, this]
      · intro s _ _ heq
        have : i ∈ symmDiff s t ↔ i ∈ s := by rw [heq]
        simp [Finset.mem_symmDiff, hi_t] at this
      · intro s hs
        rw [mem_evenClass] at hs
        show symmDiff s t ∈ evenClass D
        rw [mem_evenClass]
        have h1 : (s \ t).card + (s ∩ t).card = s.card :=
          Finset.card_sdiff_add_card_inter s t
        have h2 : (t \ s).card + (t ∩ s).card = t.card :=
          Finset.card_sdiff_add_card_inter t s
        have hcup : (symmDiff s t).card = (s \ t).card + (t \ s).card := by
          rw [symmDiff_def, Finset.sup_eq_union,
            Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
        have hint : (s ∩ t).card = (t ∩ s).card := by rw [Finset.inter_comm]
        omega
      · intro s _
        simp [symmDiff_symmDiff_cancel_right]

/-- The class addresses axes individually: for every two distinct axes there is
a closed history on which their directions differ. -/
def Separating (D : ℕ) : Prop :=
  ∀ i j : Fin D, i ≠ j → ∃ s ∈ evenClass D, dir s i ≠ dir s j

/-- In `D = 2` the even class is `{∅, {0,1}}`: both axes always move together. -/
theorem not_separating_two : ¬ Separating 2 := by
  intro h
  obtain ⟨s, hs, hne⟩ := h 0 1 (by decide)
  revert hne hs
  revert s
  decide

/-- With three or more axes, `{i, k}` for a third axis `k` separates `i` from `j`. -/
theorem separating_of_three_le (D : ℕ) (hD : 3 ≤ D) : Separating D := by
  intro i j hij
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin D, k ≠ i ∧ k ≠ j := by
    have : ∃ k : Fin D, k ∉ ({i, j} : Finset (Fin D)) := by
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset (Fin D)) ⊆ {i, j} := fun k _ => hcon k
      have := Finset.card_le_card hsub
      simp only [Finset.card_univ, Fintype.card_fin] at this
      have h2 : ({i, j} : Finset (Fin D)).card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨k, hk⟩ := this
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact ⟨k, hk.1, hk.2⟩
  refine ⟨{i, k}, ?_, ?_⟩
  · rw [mem_evenClass, Finset.card_pair (Ne.symm hki)]
  · have hi : i ∈ ({i, k} : Finset (Fin D)) := by simp
    have hj : j ∉ ({i, k} : Finset (Fin D)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hij, Ne.symm hkj⟩
    simp [dir, hi, hj]

/-- Separating fails at exactly `D = 2`. -/
theorem separating_iff_ne_two (D : ℕ) : Separating D ↔ D ≠ 2 := by
  constructor
  · intro h hD; subst hD; exact not_separating_two h
  · intro hD
    rcases Nat.lt_or_ge D 3 with hlt | hge
    · interval_cases D
      · intro i; exact absurd i.isLt (by omega)
      · intro i j hij
        exact absurd (Subsingleton.elim i j) hij
      · exact absurd rfl hD
    · exact separating_of_three_le D hge

/-- The exact dimension profile of Spanning. -/
theorem spanning_iff (D : ℕ) : Spanning D ↔ (D = 1 ∨ 3 ≤ D) := by
  constructor
  · intro h
    rcases Nat.lt_or_ge D 3 with hlt | hge
    · interval_cases D
      · exact absurd h not_spanning_zero
      · left; rfl
      · exact absurd h not_spanning_two
    · right; exact hge
  · rintro (h | h)
    · subst h; exact spanning_one
    · exact spanning_of_three_le h

/-- **Spanning is derived** from two qualitative facts: the class addresses axes
individually, and there is at least one axis. Neither is a numeral. -/
theorem spanning_iff_separating_and_nonempty (D : ℕ) :
    Spanning D ↔ (Separating D ∧ D ≠ 0) := by
  rw [spanning_iff, separating_iff_ne_two]
  omega

/-- **Isotropy does not give Equiangular.** The direction second moment of the
even class has no preferred direction for every `D ≥ 3` (`isotropy_offdiag`),
including `D = 4`, where Equiangular fails. "No preferred direction" is not the
premise that selects three; the row is refuted. -/
theorem isotropy_does_not_give_equiangular :
    (∀ i j : Fin 4, i ≠ j →
      ∑ s ∈ evenClass 4, dir s i * dir s j = 0) ∧ ¬ Equiangular 4 :=
  ⟨fun _ _ hij => isotropy_offdiag (by norm_num) hij, not_equiangular_of_four_le le_rfl⟩

/-- The parity selector restated with every input's dimension profile visible:
`D ≠ 0` (an axis exists), Separating (`D ≠ 2`), Balanced (`D ≠ 1`), and
Equiangular (`D ≤ 3`). Only Equiangular bounds `D` from above; it is the priced
member of this selector. -/
theorem parity_selector_profile (D : ℕ) :
    (Balanced D ∧ Equiangular D ∧ Spanning D) ↔
      (D ≠ 0 ∧ D ≠ 1 ∧ D ≠ 2 ∧ D ≤ 3) := by
  rw [balanced_iff_ne_one, equiangular_iff_le_three, spanning_iff]
  omega

/-- Equiangular is the one input the class itself does not supply: with `D = 4`
the class is balanced, spanning and isotropic and Equiangular fails. -/
theorem equiangular_is_the_price :
    Balanced 4 ∧ Spanning 4 ∧ ¬ Equiangular 4 :=
  ⟨(balanced_iff_ne_one 4).mpr (by norm_num),
   spanning_of_three_le (by norm_num),
   not_equiangular_of_four_le le_rfl⟩

/-! ## The two selectors agree -/

/-- **Two selectors, one verdict.** The parity triple holds in dimension `D`
iff some spatial dual-pair realization in dimension `D` satisfies DEP. The
priced premise on the left is Equiangular; on the right it is DEP. -/
theorem parity_selector_iff_dep_realizable (D : ℕ) :
    (Balanced D ∧ Equiangular D ∧ Spanning D) ↔
      ∃ R : SpatialDualPairRealization D, DeformationErasurePrinciple R.kin := by
  rw [balanced_equiangular_spanning_iff_three]
  constructor
  · intro hD
    subst hD
    obtain ⟨F, H⟩ := LinkingFromHierarchy.jRealizedHierarchy
    exact ⟨hierarchySpatialRealization F H, hierarchy_realization_satisfies_dep F H⟩
  · rintro ⟨R, hR⟩
    exact dep_forces_D3 D R hR

/-! ## Row certificate -/

/-- Certificate for row 3. -/
structure LinkingDetectionCensusCert : Prop where
  detects_forces_three : ∀ D : ℕ, PublicSpine.DetectsNontrivialLinking D → D = 3
  wall : ∃ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
    ¬ DeformationErasurePrinciple R.kin
  dep_forces_three :
    ∀ D (R : SpatialDualPairRealization D), DeformationErasurePrinciple R.kin → D = 3
  realization_insufficient : ¬ DeformationErasurePrinciple fourDimRealization.kin
  conservation_circular :
    ∀ X : PairKinematics, DeformationErasurePrinciple X ↔
      ∃ q : X.Config → ℤ,
        (∀ a b, X.deform a b → q a = q b) ∧ q X.split = 0 ∧ q X.pair ≠ 0
  conservation_not_sufficient :
    (∀ X : PairKinematics, Nonempty (PairingObservable X)) ∧
      ∃ X : PairKinematics, ¬ DeformationErasurePrinciple X
  balanced_derived : ∀ D, Balanced D ↔ D ≠ 1
  spanning_derived : ∀ D, Spanning D ↔ (Separating D ∧ D ≠ 0)
  isotropy_refuted :
    (∀ i j : Fin 4, i ≠ j → ∑ s ∈ evenClass 4, dir s i * dir s j = 0) ∧ ¬ Equiangular 4
  equiangular_priced : Balanced 4 ∧ Spanning 4 ∧ ¬ Equiangular 4
  selectors_agree : ∀ D,
    (Balanced D ∧ Equiangular D ∧ Spanning D) ↔
      ∃ R : SpatialDualPairRealization D, DeformationErasurePrinciple R.kin

theorem LinkingDetectionCensusCert_holds : LinkingDetectionCensusCert where
  detects_forces_three := row3_detects_forces_three
  wall := row3_wall
  dep_forces_three := row3_dep_forces_three
  realization_insufficient := row3_realization_alone_insufficient
  conservation_circular := dep_iff_separating_conserved_charge
  conservation_not_sufficient := conserved_observable_does_not_imply_dep
  balanced_derived := balanced_iff_ne_one
  spanning_derived := spanning_iff_separating_and_nonempty
  isotropy_refuted := isotropy_does_not_give_equiangular
  equiangular_priced := equiangular_is_the_price
  selectors_agree := parity_selector_iff_dep_realizable

end LinkingDetection
end KernelClosure
end Foundation
end IndisputableMonolith
