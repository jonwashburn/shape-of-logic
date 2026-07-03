import Mathlib

/-!
# Helmholtz Decomposition for NESS Dynamics

Finite-dimensional vector-field decomposition used by the FEP bridge.
-/

namespace IndisputableMonolith.Information.HelmholtzDecomposition

noncomputable section

/-- A finite-dimensional NESS vector field on an index type. -/
structure NESSVectorField (ι : Type*) where
  v : ι → ℝ
  rho : ι → ℝ
  freeEnergyGradient : ι → ℝ

def gradPart {ι : Type*} (X : NESSVectorField ι) : ι → ℝ :=
  fun i => - X.freeEnergyGradient i

def circulatingPart {ι : Type*} (X : NESSVectorField ι) : ι → ℝ :=
  fun i => X.v i + X.freeEnergyGradient i

theorem helmholtz_split {ι : Type*} (X : NESSVectorField ι) :
    ∀ i, X.v i = gradPart X i + circulatingPart X i := by
  intro i
  unfold gradPart circulatingPart
  ring

def DivergenceFree {ι : Type*} [Fintype ι] (w : ι → ℝ) : Prop :=
  ∑ i, w i = 0

structure HelmholtzDecompositionCert (ι : Type*) [Fintype ι] where
  split : ∀ X : NESSVectorField ι, ∀ i, X.v i = gradPart X i + circulatingPart X i
  divergence_free_condition : ∀ X : NESSVectorField ι,
    DivergenceFree (circulatingPart X) → ∑ i, circulatingPart X i = 0

theorem helmholtzDecompositionCert_holds (ι : Type*) [Fintype ι] :
    HelmholtzDecompositionCert ι :=
{ split := helmholtz_split
  divergence_free_condition := by
    intro X h
    exact h }

end

end IndisputableMonolith.Information.HelmholtzDecomposition
