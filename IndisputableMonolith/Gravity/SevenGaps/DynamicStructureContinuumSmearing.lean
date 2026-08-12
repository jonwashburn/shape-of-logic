import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureBracket
import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureFunctionBlocker
import IndisputableMonolith.Gravity.SevenGaps.WeightedHypersurfaceBracket

/-!
# Wave C2 R3: dynamic structure-function continuum smearing

Extends the banked fixed-background continuum reach
`BackgroundWeightedContinuumReach` / `weightedStructureSum_tendsto` so that
the structure-function profile is induced by a continuum field profile `q`
through the same law that inhabits the dynamic lattice bracket:

    G(x) = 1 + (q x)^2

i.e. the continuum shape of `concreteDynamicInverseMetric` along `q`.
The package is witnessed by the HamDyn family
(`PhaseSpaceDependentHamiltonianConstruction concreteDynamicInverseMetric`).

## Honesty

* This rung is the **smearing half** of the continuum story. The sampled-lapse
  Wronskian rate-`h` limit remains OPEN inside the ledger terminal R4
  (`dirac_algebra_continuum_limit`); this module does **not** introduce or
  claim that name.
* Does **not** flip `gap5_constraint_recovery`.
* Admissible class: `ContinuousOn q (Icc 0 1)` (no narrowing to global
  `Continuous` was required).
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace DynamicStructureContinuumSmearing

open HypersurfaceDeformation WeightedHypersurfaceBracket
open DynamicStructureFunctionBlocker DynamicStructureBracket

noncomputable section

open Filter Topology

/-! ## Continuum structure profile induced by a field -/

/-- MODEL. Continuum shape of `concreteDynamicInverseMetric` along a field
profile: `G(x) = 1 + (q x)^2`. -/
def dynamicStructureProfile (q : ℝ → ℝ) : ℝ → ℝ :=
  fun x => 1 + (q x) ^ 2

/-- Continuity of the induced structure profile on the unit interval. -/
theorem continuousOn_dynamicStructureProfile
    (q : ℝ → ℝ) (hq : ContinuousOn q (Set.Icc 0 1)) :
    ContinuousOn (dynamicStructureProfile q) (Set.Icc 0 1) := by
  unfold dynamicStructureProfile
  exact continuousOn_const.add (hq.pow 2)

/-- THEOREM (binding lemma). On any phase point whose configuration sample
at site `j` equals the field profile at sample location `t`, the lattice
structure function equals the continuum profile value. -/
theorem concreteDynamicInverseMetric_eq_dynamicStructureProfile
    (q : ℝ → ℝ) (x : PhaseSpace 2) (j : ZMod 2) (t : ℝ)
    (hx : x.1 j = q t) :
    concreteDynamicInverseMetric x j = dynamicStructureProfile q t := by
  simp [concreteDynamicInverseMetric, dynamicStructureProfile, hx]

/-- Specialization to the Riemann-sum sample points `k/N`. -/
theorem concreteDynamicInverseMetric_eq_sample
    (q : ℝ → ℝ) (N k : ℕ) (x : PhaseSpace 2) (j : ZMod 2)
    (hx : x.1 j = q ((k : ℝ) / (N : ℝ))) :
    concreteDynamicInverseMetric x j =
      1 + (q ((k : ℝ) / (N : ℝ))) ^ 2 := by
  simpa [dynamicStructureProfile] using
    concreteDynamicInverseMetric_eq_dynamicStructureProfile q x j
      ((k : ℝ) / (N : ℝ)) hx

/-! ## Dynamic continuum reach -/

/-- Continuum smearing reach for a field-induced structure profile:
h-scaled lattice sums of `G * (Wr * S)` tend to the integral on `[0,1]`,
with `G = dynamicStructureProfile q`. Unlike
`BackgroundWeightedContinuumReach`, the structure profile is a named
function of the field data through `1 + q^2`. -/
def DynamicWeightedContinuumReach (q : ℝ → ℝ) : Prop :=
  ∀ (Wr S : ℝ → ℝ),
    ContinuousOn Wr (Set.Icc 0 1) →
    ContinuousOn S (Set.Icc 0 1) →
    Tendsto
      (fun N : ℕ => (1 / (N : ℝ)) * ∑ k ∈ Finset.range N,
        dynamicStructureProfile q ((k : ℝ) / (N : ℝ)) *
          (Wr ((k : ℝ) / (N : ℝ)) * S ((k : ℝ) / (N : ℝ))))
      atTop (nhds (∫ x in (0 : ℝ)..1,
        dynamicStructureProfile q x * (Wr x * S x)))

/-- THEOREM. Every continuous-on-`[0,1]` field profile induces a dynamic
continuum reach via composition through `1 + q^2` and the banked
fixed-background quadrature. -/
theorem dynamic_weighted_continuum_reach
    (q : ℝ → ℝ) (hq : ContinuousOn q (Set.Icc 0 1)) :
    DynamicWeightedContinuumReach q := by
  intro Wr S hWr hS
  exact background_weighted_continuum_reach
      (dynamicStructureProfile q)
      (continuousOn_dynamicStructureProfile q hq) Wr S hWr hS

/-! ## Decoy: fixed-background reach alone does not discharge R3 -/

/-- DECOY certificate. The constant field profiles `q₁ ≡ 0` and `q₂ ≡ 1`
induce distinct structure profiles (`G ≡ 1` vs `G ≡ 2` at `x = 0`), so no
single fixed background weight covers the dynamic family. Re-exporting
`weightedStructureSum_tendsto` under a new name with a phase-independent
`W` would therefore miss this rung. -/
theorem background_weighted_reach_misses_dynamic_family :
    dynamicStructureProfile (fun _ => (0 : ℝ)) (0 : ℝ) ≠
      dynamicStructureProfile (fun _ => (1 : ℝ)) (0 : ℝ) := by
  simp [dynamicStructureProfile]

/-- Stronger decoy: there is no single fixed profile `W` that equals
`dynamicStructureProfile q` for every continuous field profile `q`. -/
theorem no_fixed_profile_equals_all_dynamic_profiles :
    ¬ ∃ W : ℝ → ℝ,
      ∀ q : ℝ → ℝ, ContinuousOn q (Set.Icc 0 1) →
        W = dynamicStructureProfile q := by
  intro ⟨W, hW⟩
  have h0 := hW (fun _ => (0 : ℝ)) continuousOn_const
  have h1 := hW (fun _ => (1 : ℝ)) continuousOn_const
  have hEq :
      dynamicStructureProfile (fun _ => (0 : ℝ)) =
        dynamicStructureProfile (fun _ => (1 : ℝ)) := by
    rw [← h0, ← h1]
  exact background_weighted_reach_misses_dynamic_family (congrFun hEq 0)

/-! ## Packaged residual (Wave C2 R3) -/

/-- Typed residual: dynamic continuum smearing witnessed by the HamDyn
family. Conjoins (1) reach for every admissible field profile, (2) binding
of the continuum law to `concreteDynamicInverseMetric` on sampled phase
points, (3) the already-banked Hamiltonian inhabitant. -/
def TypedResidual_gap5_dynamic_continuum_smearing : Prop :=
  (∀ q : ℝ → ℝ, ContinuousOn q (Set.Icc 0 1) →
      DynamicWeightedContinuumReach q) ∧
    (∀ (q : ℝ → ℝ) (x : PhaseSpace 2) (j : ZMod 2) (t : ℝ),
      x.1 j = q t →
        concreteDynamicInverseMetric x j = dynamicStructureProfile q t) ∧
      Nonempty
        (PhaseSpaceDependentHamiltonianConstruction concreteDynamicInverseMetric)

/-- THEOREM (R3 headline). The dynamic continuum-smearing residual holds. -/
theorem typedResidual_gap5_dynamic_continuum_smearing :
    TypedResidual_gap5_dynamic_continuum_smearing :=
  ⟨fun q hq => dynamic_weighted_continuum_reach q hq,
    fun q x j t hx =>
      concreteDynamicInverseMetric_eq_dynamicStructureProfile q x j t hx,
    typedResidual_dynamic_bracket_concrete_two_site⟩

/-! ### Axiom receipts -/

#print axioms continuousOn_dynamicStructureProfile
#print axioms concreteDynamicInverseMetric_eq_dynamicStructureProfile
#print axioms dynamic_weighted_continuum_reach
#print axioms background_weighted_reach_misses_dynamic_family
#print axioms no_fixed_profile_equals_all_dynamic_profiles
#print axioms typedResidual_gap5_dynamic_continuum_smearing

end
end DynamicStructureContinuumSmearing
end SevenGaps
end Gravity
end IndisputableMonolith
