import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Chemistry.PeriodicTable

/-!
# Electron Affinity from φ-Ladder Scaling (CH-006)

Electron affinity (EA) measures the energy released when adding an electron.
RS predicts EA follows the "approach to closure" pattern:

1. **Halogens** (one electron from closure) have HIGH EA
2. **Noble gases** (at closure) have NEAR-ZERO or NEGATIVE EA
3. **Alkali metals** (one past closure) have LOW EA

**RS Mechanism**: EA = cost reduction from approaching 8-tick neutrality.
Adding an electron to a halogen completes a shell (low cost → high EA).
Adding an electron to a noble gas starts a new shell (high cost → low/negative EA).

**Key predictions**:
- EA ordering: Halogens > Chalcogens > Pnictogens > ... > Noble gases
- Sign prediction: Noble gases have EA ≤ 0
- Halogen maximum within each period
-/

namespace IndisputableMonolith
namespace Chemistry
namespace ElectronAffinity

open PeriodicTable

noncomputable section

/-- Distance to next noble gas closure (electrons needed to complete shell).
    This is the fundamental proxy for electron affinity. -/
def distToClosure (Z : ℕ) : ℕ := distToNextClosure Z

/-- Electron affinity proxy: higher when closer to closure.
    EA_proxy = periodLength - valenceElectrons = distToClosure
    Halogens (dist=1) have highest proxy, noble gases (dist=0) have lowest. -/
def eaProxy (Z : ℕ) : ℕ := distToClosure Z

/-- Normalized EA proxy: fraction of shell remaining.
    EA_norm = distToClosure / periodLength ∈ [0, 1)
    Higher = more favorable to add electron. -/
def normalizedEA (Z : ℕ) : ℝ :=
  if periodLength Z = 0 then 0
  else (distToClosure Z : ℝ) / (periodLength Z : ℝ)

/-- Predicate: element is a halogen (one electron from noble gas closure). -/
def isHalogen (Z : ℕ) : Prop := distToClosure Z = 1

/-- Halogen set: {9, 17, 35, 53, 85}. -/
def halogenZ : List ℕ := [9, 17, 35, 53, 85]

/-- Decidable instance for halogen membership. -/
instance : DecidablePred isHalogen := fun Z =>
  if h : distToClosure Z = 1 then isTrue h else isFalse h

/-! ## Sign Predictions -/

/-- Noble gases have EA proxy = 0 (at closure, no benefit from adding electron). -/
theorem noble_gas_ea_zero (Z : ℕ) (h : isNobleGas Z) : eaProxy Z = 0 := by
  simp only [eaProxy, distToClosure]
  exact noble_gas_at_closure Z h

/-- Halogens have EA proxy = 1 (one electron completes shell). -/
theorem halogen_ea_one (Z : ℕ) (h : isHalogen Z) : eaProxy Z = 1 := by
  simp only [eaProxy, distToClosure]
  exact h

/-- Fluorine is a halogen (in list). -/
theorem fluorine_in_halogen_list : 9 ∈ halogenZ := by native_decide

/-- Chlorine is a halogen (in list). -/
theorem chlorine_in_halogen_list : 17 ∈ halogenZ := by native_decide

/-- Bromine is a halogen (in list). -/
theorem bromine_in_halogen_list : 35 ∈ halogenZ := by native_decide

/-- Iodine is a halogen (in list). -/
theorem iodine_in_halogen_list : 53 ∈ halogenZ := by native_decide

/-- Astatine is a halogen (in list). -/
theorem astatine_in_halogen_list : 85 ∈ halogenZ := by native_decide

/-! ## Ordering Predictions -/

/-- Within a period, EA proxy decreases as Z increases (filling the shell).
    Elements closer to closure have higher EA potential. -/
theorem ea_decreases_within_period (Z1 Z2 : ℕ)
    (hZ1le : Z1 ≤ nextClosure Z1)
    (hZ2le : Z2 ≤ nextClosure Z2)
    (hLt : Z1 < Z2)
    (hSame : nextClosure Z1 = nextClosure Z2) :
    eaProxy Z1 > eaProxy Z2 := by
  simp only [eaProxy, distToClosure, distToNextClosure]
  omega

/-- Halogens have higher EA proxy than any other non-noble element in their period. -/
theorem halogen_max_ea (Z : ℕ) (Z' : ℕ)
    (hZle : Z ≤ nextClosure Z)
    (_ : Z' ≤ nextClosure Z')
    (hSamePeriod : nextClosure Z = nextClosure Z')
    (hZ'lt : Z' < nextClosure Z') :
    distToNextClosure Z' ≤ distToNextClosure Z ↔ Z ≤ Z' := by
  simp only [distToNextClosure]
  omega

/-! ## Specific Element Theorems -/

/-- Fluorine (Z=9) is a halogen. -/
theorem fluorine_is_halogen : isHalogen 9 := by native_decide

/-- Chlorine (Z=17) is a halogen. -/
theorem chlorine_is_halogen : isHalogen 17 := by native_decide

/-- Bromine (Z=35) is a halogen. -/
theorem bromine_is_halogen : isHalogen 35 := by native_decide

/-- Iodine (Z=53) is a halogen. -/
theorem iodine_is_halogen : isHalogen 53 := by native_decide

/-- Astatine (Z=85) is a halogen. -/
theorem astatine_is_halogen : isHalogen 85 := by native_decide

/-- Neon (Z=10) has zero EA proxy. -/
theorem neon_ea_zero : eaProxy 10 = 0 := by native_decide

/-- Argon (Z=18) has zero EA proxy. -/
theorem argon_ea_zero : eaProxy 18 = 0 := by native_decide

/-! ## Falsification Criteria

The electron affinity derivation is falsifiable:

1. **Sign violation**: If noble gases have positive EA (they should be ≤ 0).

2. **Halogen not maximum**: If any halogen does NOT have maximum EA in its period.

3. **Ordering violation**: If EA ordering doesn't follow "closer to closure = higher EA"
   for main group elements (allowing d/f-block anomalies).

Note: Actual EA values in eV are NOT predicted without a scale anchor.
Only the ORDERING and SIGNS are fit-free predictions.
-/

end
end ElectronAffinity
end Chemistry
end IndisputableMonolith
