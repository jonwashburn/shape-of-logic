import IndisputableMonolith.Mathematics.HodgeCycleClassMap

/-!
# Integral Rounding for Finite Cycle Lattices

This file isolates the denominator-scheduling and integer-rounding part of the
Hodge final push.  It is finite linear algebra: a real cycle with controlled
rounding error yields an integer cycle after choosing a denominator large enough
relative to the stage rounding constant.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeIntegralRounding

open HodgeClassicalStatement

universe u

/-- A denominator schedule for finite-stage rounding constants. -/
structure DenominatorSchedule where
  D : ℕ → ℕ
  D_pos : ∀ k, 0 < D k
  dominates_rounding : ∀ k (G : ℝ), 0 ≤ G → G / (D k : ℝ) ≤ G / (k + 1 : ℝ)
  inv_tends_to_zero_bound : ∀ k, (1 : ℝ) / (D k : ℝ) ≤ (1 : ℝ) / (k + 1 : ℝ)

/-- A minimal finite integer cycle-lattice interface.  The fields do not claim
geometry; they only encode finite-stage real-to-integer rounding data. -/
structure IntegerCycleLattice where
  realCycle : Type u
  integerCycle : Type u
  toReal : integerCycle → realCycle
  roundingConstant : ℕ → ℝ
  roundingConstant_nonneg : ∀ k, 0 ≤ roundingConstant k
  round : ℕ → realCycle → integerCycle
  roundingError : ℕ → realCycle → ℝ
  roundingError_nonneg : ∀ k z, 0 ≤ roundingError k z
  roundingError_bound : ∀ k z, roundingError k z ≤ roundingConstant k

/-- A real cycle-density datum before integer rounding. -/
structure RealCycleDensityData
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p) where
  lattice : IntegerCycleLattice.{u}
  realWitness :
    ∀ (α : RationalHodgeClass.{u, u} X p)
      (_hcompat : α.cohomologyClass = cl.targetCohomology),
      lattice.realCycle
  realMoment :
    ∀ (α : RationalHodgeClass.{u, u} X p)
      (_hcompat : α.cohomologyClass = cl.targetCohomology),
      lattice.realCycle → cl.targetCohomology.carrier
  realMoment_exact :
    ∀ (α : RationalHodgeClass.{u, u} X p)
      (hcompat : α.cohomologyClass = cl.targetCohomology),
      realMoment α hcompat (realWitness α hcompat) =
        RationalHodgeClass.castClassVector α hcompat

/-- Integer rounded cycle-density data produced from real data plus a
denominator schedule. -/
structure IntegerCycleDensityData
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p) where
  realData : RealCycleDensityData cl
  schedule : DenominatorSchedule
  integerWitness :
    ∀ (_k : ℕ)
      (α : RationalHodgeClass.{u, u} X p)
      (_hcompat : α.cohomologyClass = cl.targetCohomology),
      realData.lattice.integerCycle
  normalizedError : ℕ → ℝ
  normalizedError_nonneg : ∀ k, 0 ≤ normalizedError k
  normalizedError_bound :
    ∀ k,
      normalizedError k ≤
        realData.lattice.roundingConstant k / (schedule.D k : ℝ)

/-- The finite linear-algebra rounding estimate: denominator domination pushes
the normalized error below the stage rounding constant divided by `k+1`. -/
theorem integer_cycle_density_from_real_cycle_density
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {cl : CanonicalCycleClassMap.{u} X p}
    (D : IntegerCycleDensityData cl)
    (k : ℕ) :
    D.normalizedError k ≤
      D.realData.lattice.roundingConstant k / (k + 1 : ℝ) := by
  exact le_trans (D.normalizedError_bound k)
    (D.schedule.dominates_rounding k
      (D.realData.lattice.roundingConstant k)
      (D.realData.lattice.roundingConstant_nonneg k))

end HodgeIntegralRounding
end Mathematics
end IndisputableMonolith
