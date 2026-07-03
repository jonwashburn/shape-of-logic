import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Chemistry.PeriodicTable
import IndisputableMonolith.Chemistry.IonizationEnergy
import IndisputableMonolith.Chemistry.ElectronAffinity
import IndisputableMonolith.Chemistry.Electronegativity

/-!
# Ionic Bond Formation Derivation (CH-010)

Ionic bonding occurs when electrons are transferred from a metal atom (low ionization
energy) to a non-metal atom (high electron affinity), forming oppositely charged ions
that attract electrostatically.

**RS Mechanism**:
1. **8-Tick Closure Drive**: Both the cation and anion seek to achieve 8-tick shell
   closure. Alkali metals donate electrons to achieve noble gas configuration;
   halogens accept electrons to complete their valence shell.
2. **Electron Transfer Cost**: The net energy change is the ionization energy (cost)
   minus the electron affinity (gain), modulated by lattice energy.
3. **Madelung Energy**: The electrostatic lattice energy scales with the Madelung
   constant (geometry) and inversely with ion separation.
4. **φ-Stability**: Optimal ionic radii ratios that minimize lattice strain are
   related to φ-derived values.

**Prediction**: Ionic compounds form preferentially between elements with large
electronegativity differences (alkali + halogen), with lattice energies predictable
from ion charges and radii.
-/

namespace IndisputableMonolith.Chemistry.IonicBond

open PeriodicTable
open IndisputableMonolith.Chemistry.Electronegativity

noncomputable section

/-- Alkali metals (Li, Na, K, Rb, Cs, Fr) have low ionization energy. -/
def alkaliMetalZ : List ℕ := [3, 11, 19, 37, 55, 87]

/-- Halogens (F, Cl, Br, I, At) have high electron affinity. -/
def halogenZ : List ℕ := [9, 17, 35, 53, 85]

/-- Predicate: Z is an alkali metal. -/
def isAlkaliMetal (Z : ℕ) : Prop := Z ∈ alkaliMetalZ

/-- Predicate: Z is a halogen. -/
def isHalogen (Z : ℕ) : Prop := Z ∈ halogenZ

instance : DecidablePred isAlkaliMetal := fun Z =>
  if h : Z ∈ alkaliMetalZ then isTrue h else isFalse h

instance : DecidablePred isHalogen := fun Z =>
  if h : Z ∈ halogenZ then isTrue h else isFalse h

/-- Electronegativity difference proxy.
    Higher values indicate more ionic character. -/
def electronegativityDifference (Z1 Z2 : ℕ) : ℝ :=
  if Z1 = 0 ∨ Z2 = 0 then 0
  else
    let en1 := enProxy Z1
    let en2 := enProxy Z2
    |en1 - en2|

/-- Ionic character threshold (qualitative).
    Bonds with EN difference > threshold are considered ionic.

    Note: The enProxy function gives small fractional values (≈ 0.01-0.17),
    so the threshold is correspondingly small. This captures the relative
    difference between electronegativity proxy values, not absolute values.

    **Numerical analysis** (computed externally):
    - Alkali enProxy values: Li≈0.042, Na≈0.031, K≈0.011, Rb≈0.009, Cs≈0.004, Fr≈0.004
    - Halogen enProxy values: F≈0.167, Cl≈0.125, Br≈0.100, I≈0.083, At≈0.071
    - Minimum difference (Li-At): |0.042 - 0.071| ≈ 0.030 > 0.02 ✓
    - Maximum difference (Fr-F): |0.004 - 0.167| ≈ 0.163 -/
def ionicThreshold : ℝ := 0.02

/-- Predicate: A bond between Z1 and Z2 is predominantly ionic. -/
def isIonicBond (Z1 Z2 : ℕ) : Prop :=
  electronegativityDifference Z1 Z2 > ionicThreshold

/-- Alkali-halogen pairs form ionic bonds.
    This is a physical fact: alkali metals have low EN, halogens have high EN,
    and their electronegativity difference exceeds the ionic threshold.

    **Numerical verification** (30 cases):
    - All alkali enProxy values are ≤ 0.042 (Li has highest)
    - All halogen enProxy values are ≥ 0.071 (At has lowest)
    - Minimum |difference| = |0.042 - 0.071| ≈ 0.030 > 0.02 ✓

    **Proof status**: Requires Real arithmetic case analysis.
    The 30 cases involve noncomputable division, so native_decide fails.
    norm_num with simp can handle the expanded forms. -/
theorem alkali_halogen_ionic (Z_alkali Z_halogen : ℕ)
    (h_alkali : isAlkaliMetal Z_alkali) (h_halogen : isHalogen Z_halogen) :
    isIonicBond Z_alkali Z_halogen := by
  simp only [isIonicBond, electronegativityDifference, ionicThreshold]
  simp only [isAlkaliMetal, alkaliMetalZ, isHalogen, halogenZ] at h_alkali h_halogen
  have haz : Z_alkali ≠ 0 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_alkali
    rcases h_alkali with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hhz : Z_halogen ≠ 0 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_halogen
    rcases h_halogen with rfl | rfl | rfl | rfl | rfl <;> norm_num
  simp only [haz, hhz, false_or, ↓reduceIte]
  -- The proof requires numerical case analysis on 30 alkali-halogen pairs
  -- Each case reduces to showing |1/(d₁+1)/s₁ - 1/(d₂+1)/s₂| > 0.02
  -- where d = distToNextClosure and s = shellNumber
  --
  -- Key insight: All halogen enProxy ≥ 1/14 (At), all alkali enProxy ≤ 1/24 (Li)
  -- Minimum difference: 1/14 - 1/24 = 5/168 > 1/50 = 0.02
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_alkali h_halogen
  -- Expand enProxy for each specific case
  rcases h_alkali with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases h_halogen with rfl | rfl | rfl | rfl | rfl <;>
  simp only [enProxy, distToNextClosure, nextClosure, AtomicRadii.shellNumber, periodOf,
             ↓reduceIte, OfNat.ofNat_ne_zero] <;>
  norm_num

/-- The Born-Landé equation for lattice energy (dimensionless proxy).
    U ∝ M * z+ * z- / r₀ * (1 - 1/n)
    where M is the Madelung constant, z are charges, r₀ is interionic distance,
    and n is the Born exponent.
    We use a simplified proxy: U ∝ charge_product / distance_proxy
-/
def latticeEnergyProxy (charge1 charge2 : ℤ) (distanceProxy : ℝ) : ℝ :=
  if distanceProxy ≤ 0 then 0
  else
    (charge1.toNat * charge2.toNat : ℝ) / distanceProxy

/-- Madelung constant for NaCl structure (rock salt). -/
def madelungNaCl : ℝ := 1.748

/-- Madelung constant for CsCl structure. -/
def madelungCsCl : ℝ := 1.763

/-- Madelung constant for ZnS structure (zinc blende). -/
def madelungZnS : ℝ := 1.638

/-- The Madelung constant for NaCl is greater than 0. -/
theorem madelung_nacl_pos : madelungNaCl > 0 := by
  simp only [madelungNaCl]
  norm_num

/-- Lattice energy proxy increases with ionic charge product.
    U(1,1) < U(2,1) since 1/d < 2/d for d > 0. -/
theorem lattice_energy_increases_with_charge (d : ℝ) (hd : d > 0) :
    latticeEnergyProxy 1 1 d < latticeEnergyProxy 2 1 d := by
  simp only [latticeEnergyProxy]
  have hd_pos : ¬(d ≤ 0) := not_le.mpr hd
  simp only [hd_pos, ite_false]
  -- 1/d < 2/d when d > 0
  have h1 : (1 : ℤ).toNat = 1 := rfl
  have h2 : (2 : ℤ).toNat = 2 := rfl
  simp only [h1, h2]
  -- 1 * 1 / d < 2 * 1 / d when d > 0
  have : (1 : ℝ) * 1 / d < 2 * 1 / d := by
    apply div_lt_div_of_pos_right _ hd
    norm_num
  simpa using this

/-- Helper: all alkali metals have valence 1. -/
private theorem alkali_valence_one : ∀ z ∈ alkaliMetalZ, valenceElectrons z = 1 := by
  intro z hz
  simp only [alkaliMetalZ, List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

/-- Helper: all halogens are 1 electron from closure. -/
private theorem halogen_dist_one : ∀ z ∈ halogenZ, distToNextClosure z = 1 := by
  intro z hz
  simp only [halogenZ, List.mem_cons, List.mem_nil_iff, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl <;> native_decide

/-- Ion pair stability: alkali + halogen forms stable 1:1 compound.
    Alkali metals have 1 valence electron, halogens are 1 electron from closure. -/
theorem alkali_halogen_stable_1_1 (Z_alkali Z_halogen : ℕ)
    (h_alkali : isAlkaliMetal Z_alkali) (h_halogen : isHalogen Z_halogen) :
    valenceElectrons Z_alkali = 1 ∧ distToNextClosure Z_halogen = 1 := by
  exact ⟨alkali_valence_one Z_alkali h_alkali, halogen_dist_one Z_halogen h_halogen⟩

/-- The Born-Mayer repulsion exponent is close to φ.
    Empirically, n ≈ 9-12 for most ions. This can be connected to φ via φ^5 ≈ 11.09. -/
def bornExponentProxy : ℝ := Constants.phi ^ 5

/-- The Born exponent proxy is between 10 and 12.
    φ^5 ≈ 11.09, which matches empirical Born exponents of 9-12. -/
theorem born_exponent_in_range : 10 < bornExponentProxy ∧ bornExponentProxy < 12 := by
  dsimp [bornExponentProxy]
  -- Use phi_fifth_bounds: 10.7 < φ^5 < 11.3
  constructor
  · linarith [Constants.phi_fifth_bounds.1]
  · linarith [Constants.phi_fifth_bounds.2]

end

end IndisputableMonolith.Chemistry.IonicBond
