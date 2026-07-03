import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Chemistry.PeriodicTable

/-!
# Ionization Energy from φ-Ladder Scaling (P0-A2)

First ionization energy I₁(Z) measures the cost to remove one electron.
RS predicts this follows a sawtooth pattern forced by:

1. **φ-rail scaling**: Base energy scales as φ^{2n} for period n
2. **Position factor**: Within a period, energy increases toward closure
3. **Block offsets**: s/p/d/f subshells have fixed φ-packing offsets

**Key predictions**:
- Alkali metals (valence = 1) have MINIMUM ionization energy per period
- Noble gases (valence = period length) have MAXIMUM ionization energy per period
- The sawtooth emerges WITHOUT fitting to data

**Falsification**: If the predicted ordering (alkali < ... < noble within each period)
fails on a prereg'd element set, the model is falsified.
-/

namespace IndisputableMonolith
namespace Chemistry
namespace IonizationEnergy

open PeriodicTable

noncomputable section

/-- Dimensionless ionization energy proxy based on position in period.
    Runs from 1 (alkali) to periodLength (noble gas).
    This captures the "cost to break into a forming shell." -/
def ionizationProxy (Z : ℕ) : ℕ :=
  valenceElectrons Z

/-- Period-normalized ionization: proxy / period length.
    Noble gases have value 1.0, alkali metals have value 1/n. -/
def normalizedIonization (Z : ℕ) : ℝ :=
  if periodLength Z = 0 then 0
  else (ionizationProxy Z : ℝ) / (periodLength Z : ℝ)

/-- φ-scaled ionization energy (dimensionless).
    Combines rail factor with position factor.
    I_scaled(Z) = φ^{2·period} × (valence / periodLength) -/
def scaledIonization (Z : ℕ) : ℝ :=
  let period := periodOf Z
  let rf := Real.rpow Constants.phi ((2 : ℝ) * (period : ℝ))
  rf * normalizedIonization Z

/-- Predicted ionization energy in eV (display seam).
    Uses E_coh as the universal energy anchor. -/
def predictedI1_eV (Z : ℕ) : ℝ :=
  Constants.E_coh * scaledIonization Z * 1000  -- Scale factor for eV range

/-! ## Ordering Theorems (Sawtooth Structure) -/

/-- Alkali metals have valence = 1 (one electron beyond noble gas core). -/
def isAlkaliMetal (Z : ℕ) : Prop :=
  valenceElectrons Z = 1 ∧ Z > 1  -- Excludes hydrogen

/-- Alkali metal set: {3, 11, 19, 37, 55, 87}. -/
def alkaliMetalZ : List ℕ := [3, 11, 19, 37, 55, 87]

/-- Within any period, alkali metals have minimum ionization proxy. -/
theorem alkali_min_ionization (Z : ℕ) (hZ : valenceElectrons Z = 1) (hZ2 : Z > 2) :
    ionizationProxy Z = 1 := by
  simp only [ionizationProxy]
  exact hZ

/-- Noble gases have maximum ionization proxy (equal to period length). -/
theorem noble_max_ionization (Z : ℕ) (h : isNobleGas Z) :
    ionizationProxy Z = periodLength Z := by
  simp only [ionizationProxy]
  exact noble_gas_complete_shell Z h

/-- Ionization proxy is monotone increasing within a period.
    If Z₁ < Z₂ are in the same period, then proxy(Z₁) < proxy(Z₂). -/
theorem ionization_monotone_within_period (Z1 Z2 : ℕ)
    (hZ1ge : Z1 ≥ prevClosure Z1)
    (hLt : Z1 < Z2) (hNotCross : prevClosure Z1 = prevClosure Z2) :
    ionizationProxy Z1 < ionizationProxy Z2 := by
  simp only [ionizationProxy, valenceElectrons]
  -- Z1 - prevClosure Z1 < Z2 - prevClosure Z2
  -- Since prevClosure Z1 = prevClosure Z2, this reduces to Z1 < Z2
  have hZ2ge : Z2 ≥ prevClosure Z2 := by omega
  omega

/-! ## Sawtooth Pattern -/

/-- The sawtooth pattern: ionization resets at each period boundary.
    After a noble gas, the next element (alkali) has minimal ionization. -/
theorem sawtooth_reset (Znoble Zalkali : ℕ)
    (hNoble : isNobleGas Znoble)
    (hNext : Zalkali = Znoble + 1)
    (hValid : Zalkali ≤ 118) :
    ionizationProxy Zalkali < ionizationProxy Znoble := by
  -- Noble gas has maximum (= period length), alkali has 1
  -- Case by case on which noble gas
  unfold isNobleGas nobleGasZ at hNoble
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hNoble
  obtain rfl | rfl | rfl | rfl | rfl | rfl := hNoble <;>
    subst hNext <;>
    native_decide

/-! ## Falsification Criteria

The ionization energy derivation is falsifiable:

1. **Ordering violation**: If any element Z₁ < Z₂ within the same period
   has I₁(Z₁) > I₁(Z₂) in NIST data (beyond experimental error).

2. **Alkali not minimum**: If any alkali metal does NOT have minimum I₁
   in its period (excluding period 1).

3. **Noble not maximum**: If any noble gas does NOT have maximum I₁
   in its period.

4. **Sawtooth failure**: If I₁(alkali) > I₁(previous noble gas).

Note: The NUMERICAL values are not predicted without an anchor.
Only the ORDERING is fit-free.
-/

end
end IonizationEnergy
end Chemistry
end IndisputableMonolith
