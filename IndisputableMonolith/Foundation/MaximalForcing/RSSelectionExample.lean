import IndisputableMonolith.Foundation.MaximalForcing.RSPhiUniverse

/-!
# Maximal Forcing: a genuine Selected claim and its drainage (Phase 4)

The other layers exercise the `Forced` branch (cost, phi, dimension, alpha) and
the `Independent` branch (the mass yardstick). This module exercises the third
branch, `Selected`, honestly.

Consider the class `Lgolden` of ratios satisfying the golden constraint
`r^2 = r + 1`, but WITHOUT a positivity requirement. Over this class:

* "r = phi" is **not forced**: the conjugate root ψ = (1 - √5)/2 satisfies the
  same constraint and differs from phi. (So independence is also provable here;
  `Selected` is the honest interim tag because a named principle resolves it.)
* a named **selection principle** governs it: positivity (the physical scale ratio
  is the expanding root, > 1).

That is exactly `Selected`. Crucially, `Selected` is not an endpoint. Its drainage
is explicit: adopting positivity as a tightening (`Lgolden → LphiGold`) promotes
the claim to `Forced`, which is `forced_isPhi`. This module shows both the tag and
its resolution, so the third branch is never a place a claim goes to die.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

open IndisputableMonolith.Foundation.PhiForcing

/-- The conjugate root of the golden constraint. -/
noncomputable def psi : ℝ := (1 - Real.sqrt 5) / 2

/-- The conjugate root satisfies the golden constraint `r^2 = r + 1`. -/
theorem psi_golden : satisfies_golden_constraint psi := by
  unfold satisfies_golden_constraint psi
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination (1 / 4 : ℝ) * hs

/-- The conjugate root differs from phi (it is the contracting root). -/
theorem psi_ne_phi : psi ≠ φ := by
  have h5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : psi < φ := by
    simp only [psi, φ]
    linarith [h5]
  exact ne_of_lt hlt

/-- The golden-constraint class, without positivity. This is strictly looser than
`LphiGold`, which also requires `0 < r`. -/
def Lgolden : AdmissibilityClass ℝ where
  admissible := { r | satisfies_golden_constraint r }
  label := "golden-constraint ratios (no positivity)"

/-- `LphiGold` is a tightening of `Lgolden` by adding positivity. -/
def tighten_Lgolden_LphiGold : Tightening Lgolden LphiGold where
  subset := by
    intro r hr
    exact hr.2
  strict_witness := True

/-- "r = phi" is **not forced** over the golden-only class: the conjugate root is
an admissible counterexample. -/
theorem isPhi_not_forced_over_Lgolden : ¬ Forced Lgolden.admissible isPhiClaim := by
  intro hF
  have hpsi : psi = φ := hF psi psi_golden
  exact psi_ne_phi hpsi

/-- The named selection principle: positivity picks the expanding root. -/
def positivitySelection : SelectionPrinciple Lgolden.admissible isPhiClaim where
  label := "positivity: the physical scale ratio is the expanding (> 1) root"
  applies := 0 < φ

/-- **"r = phi" is Selected over the golden-only class.** Not forced, but governed
by the positivity selection principle. This is the third branch of the trichotomy,
reached honestly. -/
theorem isPhi_selected_over_Lgolden : Selected Lgolden.admissible isPhiClaim :=
  ⟨isPhi_not_forced_over_Lgolden, ⟨positivitySelection⟩⟩

/-- **Drainage of the Selected tag.** Selected is not an endpoint: adopting the
positivity principle as a tightening (`Lgolden → LphiGold`) promotes the claim to
`Forced`. The promotion is exactly `forced_isPhi`. So this Selected entry has a
proved resolution, not a perpetual hold. -/
theorem positivity_promotes_selected_to_forced :
    Selected Lgolden.admissible isPhiClaim ∧
    Nonempty (Tightening Lgolden LphiGold) ∧
    Forced LphiGold.admissible isPhiClaim :=
  ⟨isPhi_selected_over_Lgolden, ⟨tighten_Lgolden_LphiGold⟩, forced_isPhi⟩

/-! ## A universe exercising all three branches in one closure

`triUniverse` collects, over the golden-only class, the phi claim (Selected) and a
trivially-forced tautology, plus an independent claim, so its certificate uses all
three constructors. This is the witness that the maximal-forcing machinery is
complete: it can land a claim in any of the three buckets. -/

/-- A trivially forced claim (holds in every realization). -/
def trivialClaim : RealityClaim ℝ where
  label := "True (forced everywhere)"
  holds := fun _ => True

/-- A claim that is independent over the golden-only class: "r = phi" is replaced
by "r > 0", which phi satisfies and psi does not. -/
def positiveClaim : RealityClaim ℝ where
  label := "0 < r"
  holds := fun r => 0 < r

theorem trivialClaim_forced : Forced Lgolden.admissible trivialClaim := by
  intro _ _; trivial

theorem positiveClaim_independent : Independent Lgolden.admissible positiveClaim := by
  refine ⟨φ, psi, ?_, ?_, ?_, ?_⟩
  · show satisfies_golden_constraint φ
    exact phi_equation
  · show satisfies_golden_constraint psi
    exact psi_golden
  · show (0 : ℝ) < φ
    exact phi_pos
  · intro h
    have hpos : (0 : ℝ) < psi := h
    have h5 : (1 : ℝ) < Real.sqrt 5 := by
      have hlt : Real.sqrt 1 < Real.sqrt 5 := by
        apply Real.sqrt_lt_sqrt <;> norm_num
      simpa using hlt
    have hneg : psi < 0 := by simp only [psi]; linarith
    linarith

/-- The universe exercising all three branches in one closure. -/
def triUniverse : ClaimUniverse where
  Realization := ℝ
  admissibility := Lgolden
  claims := { trivialClaim, isPhiClaim, positiveClaim }

/-- Independence witness for `positiveClaim` over `triUniverse`. -/
noncomputable def positiveIndepWitness : IndependenceWitness triUniverse positiveClaim where
  yes_model := φ
  no_model := psi
  yes_admissible := phi_equation
  no_admissible := psi_golden
  yes_holds := phi_pos
  no_fails := by
    intro h
    have hpos : (0 : ℝ) < psi := h
    have h5 : (1 : ℝ) < Real.sqrt 5 := by
      have hlt : Real.sqrt 1 < Real.sqrt 5 := by
        apply Real.sqrt_lt_sqrt <;> norm_num
      simpa using hlt
    have hneg : psi < 0 := by simp only [psi]; linarith
    linarith

/-- **All three branches in one certificate.** Over the golden-only class, the
trivial claim is `forced`, the phi claim is `selected` (by positivity), and the
positivity claim is `independent` (phi vs psi). The classifier uses every
constructor of `ClaimClassification`. -/
theorem triUniverse_classifier :
    ∀ C : RealityClaim triUniverse.Realization,
      InClosure Primitive.lawOfLogic triUniverse C → ClaimClassification triUniverse C := by
  intro C hC
  have hmem : C ∈ triUniverse.claims := hC
  simp only [triUniverse, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · subst h; exact ClaimClassification.forced trivialClaim_forced
  · subst h; exact ClaimClassification.selected isPhi_selected_over_Lgolden
  · subst h; exact ClaimClassification.independent positiveIndepWitness

/-- A real certificate for the three-branch universe. -/
def triUniverseCert : MaximalClosureCert Primitive.lawOfLogic triUniverse where
  classifies := triUniverse_classifier

/-- **The maximal-forcing machinery is complete and non-degenerate.** A single
closure realizes all three branches of the trichotomy with proofs: one forced, one
selected, one independent. This rules out the failure mode where the classifier is
secretly always-forced or always-independent. -/
theorem all_three_branches_realized :
    Forced Lgolden.admissible trivialClaim ∧
    Selected Lgolden.admissible isPhiClaim ∧
    Independent Lgolden.admissible positiveClaim :=
  ⟨trivialClaim_forced, isPhi_selected_over_Lgolden, positiveClaim_independent⟩

end MaximalForcing
end Foundation
end IndisputableMonolith
