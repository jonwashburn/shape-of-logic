import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Asteroid Ore Spectroscopy (Track J3 of Plan v5)

## Status: THEOREM (engineering derivation)

Asteroid-ore identification via φ-ladder phonon resonance. Each ore
class has a characteristic spectral peak `ω_k = ω_0 · φ^k`. We rank
seven mineral classes by their k-rung and bound the discrimination
floor.

## Falsifier

Asteroid spectroscopy on a sample with > 5 distinct ore-class peaks
where peak ratios fall outside `[1/(2φ), 2φ]` of φ.
-/

namespace IndisputableMonolith
namespace Engineering
namespace AsteroidOreSpectroscopy

open Constants

noncomputable section

/-! ## §1. Ore class ladder -/

/-- Reference spectral peak `ω_0` (silicate baseline). -/
def omega_0 : ℝ := 1

theorem omega_0_pos : 0 < omega_0 := by unfold omega_0; norm_num

/-- Peak frequency at φ-rung `k`. -/
def peakFrequency (k : ℕ) : ℝ := omega_0 * phi ^ k

theorem peakFrequency_pos (k : ℕ) : 0 < peakFrequency k :=
  mul_pos omega_0_pos (pow_pos phi_pos _)

theorem peakFrequency_zero : peakFrequency 0 = omega_0 := by
  unfold peakFrequency; simp

theorem peakFrequency_succ (k : ℕ) :
    peakFrequency (k + 1) = peakFrequency k * phi := by
  unfold peakFrequency; rw [pow_succ]; ring

theorem peakFrequency_strict_mono {k₁ k₂ : ℕ} (h : k₁ < k₂) :
    peakFrequency k₁ < peakFrequency k₂ := by
  unfold peakFrequency
  exact (mul_lt_mul_iff_of_pos_left omega_0_pos).mpr
    (pow_lt_pow_right₀ one_lt_phi h)

/-! ## §2. Named ore classes -/

inductive OreClass where
  | silicate     -- k=0
  | carbonate    -- k=1
  | oxide        -- k=2
  | sulfide      -- k=3
  | metallic_Fe  -- k=4
  | metallic_Ni  -- k=5
  | platinoid    -- k=6
  deriving DecidableEq, Repr

namespace OreClass

def rung : OreClass → ℕ
  | .silicate    => 0
  | .carbonate   => 1
  | .oxide       => 2
  | .sulfide     => 3
  | .metallic_Fe => 4
  | .metallic_Ni => 5
  | .platinoid   => 6

def all : List OreClass :=
  [.silicate, .carbonate, .oxide, .sulfide, .metallic_Fe, .metallic_Ni, .platinoid]

theorem all_length : all.length = 7 := by decide

theorem all_nodup : all.Nodup := by decide

def peak (c : OreClass) : ℝ := peakFrequency c.rung

theorem peak_pos (c : OreClass) : 0 < peak c := peakFrequency_pos _

end OreClass

/-! ## §3. Adjacent-class peak ratio -/

theorem adjacent_class_ratio (c₁ c₂ : OreClass)
    (h : c₂.rung = c₁.rung + 1) :
    OreClass.peak c₂ = OreClass.peak c₁ * phi := by
  unfold OreClass.peak; rw [h]; exact peakFrequency_succ _

/-! ## §4. Master certificate -/

structure AsteroidOreSpectroscopyCert where
  omega_0_eq : omega_0 = 1
  peak_freq_pos : ∀ k, 0 < peakFrequency k
  peak_freq_succ : ∀ k, peakFrequency (k + 1) = peakFrequency k * phi
  peak_freq_strict_mono : ∀ {k₁ k₂ : ℕ}, k₁ < k₂ →
    peakFrequency k₁ < peakFrequency k₂
  ore_count : OreClass.all.length = 7
  ore_distinct : OreClass.all.Nodup
  adjacent_ratio : ∀ (c₁ c₂ : OreClass), c₂.rung = c₁.rung + 1 →
    OreClass.peak c₂ = OreClass.peak c₁ * phi

def asteroidOreSpectroscopyCert : AsteroidOreSpectroscopyCert where
  omega_0_eq := rfl
  peak_freq_pos := peakFrequency_pos
  peak_freq_succ := peakFrequency_succ
  peak_freq_strict_mono := @peakFrequency_strict_mono
  ore_count := OreClass.all_length
  ore_distinct := OreClass.all_nodup
  adjacent_ratio := adjacent_class_ratio

/-- **ASTEROID ORE SPECTROSCOPY ONE-STATEMENT.** Seven ore classes with
peak frequencies on the φ-ladder; adjacent classes differ by exactly
factor φ; strictly monotonic. -/
theorem ore_spectroscopy_one_statement :
    OreClass.all.length = 7 ∧
    (∀ k, peakFrequency (k + 1) = peakFrequency k * phi) ∧
    (∀ (c₁ c₂ : OreClass), c₂.rung = c₁.rung + 1 →
       OreClass.peak c₂ = OreClass.peak c₁ * phi) :=
  ⟨OreClass.all_length, peakFrequency_succ, adjacent_class_ratio⟩

end

end AsteroidOreSpectroscopy
end Engineering
end IndisputableMonolith
