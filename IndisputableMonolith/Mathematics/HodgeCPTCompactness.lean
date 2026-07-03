import Mathlib
import IndisputableMonolith.Mathematics.HodgePhaseLatticeRealization

/-!
# Referee-Grade CPT Compactness Interface

This module starts Phase 5 of the referee-grade Hodge closure track.

The certificate-layer proof contains a scalar compactness estimate for
mass-normalized duals and a recognition-bandlimit wrapper.  A referee-grade
formalization must replace those wrappers by actual minimizers, actual dual
chains, actual norms, primitive nonconcentration, and a proof that
checkerboard dual representatives are replaced by bounded CPT-minimal
representatives.

This file isolates that analytic target.  It does not yet prove the analytic
compactness theorem from Mathlib-native analysis.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeCPTCompactness

open HodgeClassicalStatement
open HodgeChainsAndCurrents
open HodgeFixedCoverRealization
open HodgePhaseLatticeRealization

universe u

/-- Dual chain data paired with a primal chain complex. -/
structure DualChainData
    {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X) where
  dualAt : ℕ → Type u
  zero : (n : ℕ) → dualAt n
  add : {n : ℕ} → dualAt n → dualAt n → dualAt n
  neg : {n : ℕ} → dualAt n → dualAt n
  coboundary : (n : ℕ) → dualAt n → dualAt (n + 1)
  add_assoc : ∀ {n : ℕ} (a b c : dualAt n),
    add (add a b) c = add a (add b c)
  add_comm : ∀ {n : ℕ} (a b : dualAt n), add a b = add b a
  add_zero : ∀ {n : ℕ} (η : dualAt n), add η (zero n) = η
  zero_add : ∀ {n : ℕ} (η : dualAt n), add (zero n) η = η
  add_neg : ∀ {n : ℕ} (η : dualAt n), add η (neg η) = zero n
  neg_neg : ∀ {n : ℕ} (η : dualAt n), neg (neg η) = η
  neg_zero : ∀ {n : ℕ}, neg (zero n) = zero n
  pairing : {n : ℕ} → dualAt n → Chain C n → ℝ
  pairing_zero_left : ∀ {n : ℕ} (c : Chain C n),
    pairing (zero n) c = 0
  pairing_add_left : ∀ {n : ℕ} (η₁ η₂ : dualAt n) (c : Chain C n),
    pairing (add η₁ η₂) c = pairing η₁ c + pairing η₂ c
  pairing_zero_right : ∀ {n : ℕ} (η : dualAt n),
    pairing η (C.zero n) = 0
  pairing_neg_left : ∀ {n : ℕ} (η : dualAt n) (c : Chain C n),
    pairing (neg η) c = -(pairing η c)
  pairing_add_right : ∀ {n : ℕ} (η : dualAt n) (c₁ c₂ : Chain C n),
    pairing η (C.add c₁ c₂) = pairing η c₁ + pairing η c₂
  pairing_neg_right : ∀ {n : ℕ} (η : dualAt n) (c : Chain C n),
    pairing η (C.neg c) = -(pairing η c)
  coboundary_add : ∀ {n : ℕ} (η₁ η₂ : dualAt n),
    coboundary n (add η₁ η₂) = add (coboundary n η₁) (coboundary n η₂)
  coboundary_neg : ∀ {n : ℕ} (η : dualAt n),
    coboundary n (neg η) = neg (coboundary n η)
  coboundary_zero : ∀ {n : ℕ},
    coboundary n (zero n) = zero (n + 1)
  coboundary_squared_zero : ∀ (n : ℕ) (η : dualAt n),
    coboundary (n + 1) (coboundary n η) = zero (n + 2)

/-- Each degree of a dual chain complex carries an abelian group structure. -/
instance DualChainData.instAddCommGroup {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (D : DualChainData C) (n : ℕ) : AddCommGroup (D.dualAt n) where
  add := D.add
  zero := D.zero n
  neg := D.neg
  sub a b := D.add a (D.neg b)
  nsmul := fun k x => @nsmulRec _ ⟨D.zero n⟩ ⟨D.add⟩ k x
  zsmul := fun k x => @zsmulRec _ ⟨D.zero n⟩ ⟨D.add⟩ ⟨D.neg⟩
    (fun k x => @nsmulRec _ ⟨D.zero n⟩ ⟨D.add⟩ k x) k x
  add_assoc := D.add_assoc
  zero_add := D.zero_add
  add_zero := D.add_zero
  neg_add_cancel := fun a => (D.add_comm _ _).trans (D.add_neg a)
  add_comm := D.add_comm
  sub_eq_add_neg := fun _ _ => rfl
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

/-- Coboundary on dual chains as a Mathlib `AddMonoidHom`. -/
def DualChainData.coboundaryHom {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (D : DualChainData C) (n : ℕ) : D.dualAt n →+ D.dualAt (n + 1) where
  toFun := D.coboundary n
  map_zero' := by exact D.coboundary_zero
  map_add' := by exact D.coboundary_add

/-- The square of the coboundary is zero: δ_{n+1} ∘ δ_n = 0 as `AddMonoidHom`. -/
theorem DualChainData.coboundary_comp_eq_zero {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (D : DualChainData C) (n : ℕ) :
    (D.coboundaryHom (n + 1)).comp (D.coboundaryHom n) = 0 :=
  AddMonoidHom.ext fun η => D.coboundary_squared_zero n η

/-- The image of δ_n lies in the kernel of δ_{n+1}: the cochain analogue
of the homological algebra inclusion im ⊆ ker. -/
theorem DualChainData.range_coboundary_le_ker {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (D : DualChainData C) (n : ℕ) :
    (D.coboundaryHom n).range ≤ (D.coboundaryHom (n + 1)).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  obtain ⟨y, rfl⟩ := hx
  exact D.coboundary_squared_zero n y

/-- Dual cocycles: Z^n = ker(δ_n) as an `AddSubgroup`. -/
def DualChainData.cocycles {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (D : DualChainData C) (n : ℕ) : AddSubgroup (D.dualAt n) :=
  (D.coboundaryHom n).ker

/-- Dual coboundaries at degree n+1: B^{n+1} = im(δ_n). -/
def DualChainData.coboundariesAt {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (D : DualChainData C) (n : ℕ) : AddSubgroup (D.dualAt (n + 1)) :=
  (D.coboundaryHom n).range

/-- Dual coboundaries are contained in dual cocycles:
B^{n+1} ⊆ Z^{n+1} for dual chains. -/
theorem DualChainData.coboundariesAt_le_cocycles
    {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (D : DualChainData C) (n : ℕ) :
    D.coboundariesAt n ≤ D.cocycles (n + 1) :=
  D.range_coboundary_le_ker n

/-- For each fixed chain c, pairing η ↦ pairing η c is an additive homomorphism. -/
def DualChainData.pairingLeftHom {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (D : DualChainData C) {n : ℕ} (c : Chain C n) : D.dualAt n →+ ℝ where
  toFun η := D.pairing η c
  map_zero' := by exact D.pairing_zero_left c
  map_add' η₁ η₂ := by exact D.pairing_add_left η₁ η₂ c

/-- For each fixed dual η, pairing c ↦ pairing η c is an additive homomorphism. -/
def DualChainData.pairingRightHom {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (D : DualChainData C) {n : ℕ} (η : D.dualAt n) : Chain C n →+ ℝ where
  toFun c := D.pairing η c
  map_zero' := by exact D.pairing_zero_right η
  map_add' c₁ c₂ := by exact D.pairing_add_right η c₁ c₂

/-- Mass-normalized recognition norm on dual chains. -/
structure MassNormalizedRecognitionNorm
    {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (D : DualChainData C) where
  linfDensity : {n : ℕ} → D.dualAt n → ℝ
  scaleGradient : {n : ℕ} → D.dualAt n → ℝ
  linfDensity_nonneg : ∀ {n : ℕ} (η : D.dualAt n), 0 ≤ linfDensity η
  scaleGradient_nonneg : ∀ {n : ℕ} (η : D.dualAt n), 0 ≤ scaleGradient η

namespace MassNormalizedRecognitionNorm

/-- Total recognition norm. -/
def recNorm
    {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    {D : DualChainData C}
    (N : MassNormalizedRecognitionNorm D)
    {n : ℕ}
    (η : D.dualAt n) : ℝ :=
  N.linfDensity η + N.scaleGradient η

theorem recNorm_nonneg
    {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    {D : DualChainData C}
    (N : MassNormalizedRecognitionNorm D)
    {n : ℕ}
    (η : D.dualAt n) :
    0 ≤ N.recNorm η :=
  add_nonneg (N.linfDensity_nonneg η) (N.scaleGradient_nonneg η)

end MassNormalizedRecognitionNorm

/-- CPT energy functional on an affine dual-obstruction class. -/
structure CPTEnergyFunctional
    {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    {D : DualChainData C}
    (N : MassNormalizedRecognitionNorm D) where
  energy : {n : ℕ} → D.dualAt n → ℝ
  energy_nonneg : ∀ {n : ℕ} (η : D.dualAt n), 0 ≤ energy η
  controls_recognition_norm : ∀ {n : ℕ} (η : D.dualAt n),
    N.recNorm η ≤ energy η

/-- Affine class of dual representatives for one obstruction. -/
structure DualObstructionClass
    {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (D : DualChainData C)
    (n : ℕ) where
  representative : Type u
  representative_nonempty : Nonempty representative
  toDual : representative → D.dualAt n
  obstructionPairing : representative → ℝ
  samePairingOnObstruction :
    ∀ r s : representative, obstructionPairing r = obstructionPairing s

/-- The representative type of a dual obstruction class is nonempty. -/
instance DualObstructionClass.instNonempty {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    {D : DualChainData C}
    {n : ℕ}
    (A : DualObstructionClass D n) : Nonempty A.representative :=
  A.representative_nonempty

/-- CPT-minimal representative in an affine obstruction class. -/
structure CPTMinimalRepresentative
    {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    {D : DualChainData C}
    {N : MassNormalizedRecognitionNorm D}
    (E : CPTEnergyFunctional N)
    {n : ℕ}
    (A : DualObstructionClass D n) where
  representative : A.representative
  minimality : ∀ r : A.representative,
    E.energy (A.toDual representative) ≤ E.energy (A.toDual r)

/-- Primitive phase nonconcentration as actual bounded dual representative
data. -/
structure PrimitivePhaseNonconcentrationData
    {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    {D : DualChainData C}
    (N : MassNormalizedRecognitionNorm D) where
  densityBound : ℝ
  gradientBound : ℝ
  densityBound_nonneg : 0 ≤ densityBound
  gradientBound_nonneg : 0 ≤ gradientBound
  bounded_representatives :
    ∀ {n : ℕ} (η : D.dualAt n),
      N.linfDensity η ≤ densityBound →
      N.scaleGradient η ≤ gradientBound →
      N.recNorm η ≤ densityBound + gradientBound

/-- No-checkerboard theorem target: raw high-frequency duals are not used in
the final representative; CPT minimization selects a bounded representative
in the same obstruction class. -/
structure NoCheckerboardAfterCPT
    {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    {D : DualChainData C}
    {N : MassNormalizedRecognitionNorm D}
    (E : CPTEnergyFunctional N) where
  replacement :
    ∀ {n : ℕ} (A : DualObstructionClass D n),
      CPTMinimalRepresentative E A
  replacementBound :
    ∀ {n : ℕ} (_A : DualObstructionClass D n), ℝ
  replacementBound_nonneg :
    ∀ {n : ℕ} (A : DualObstructionClass D n),
      0 ≤ replacementBound A
  replacement_bounded :
    ∀ {n : ℕ} (A : DualObstructionClass D n),
      N.recNorm (A.toDual (replacement A).representative) ≤ replacementBound A

/-- Recognition bandlimit as a genuine boundedness theorem for CPT-minimal
dual representatives. -/
structure RecognitionBandlimitData
    {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    {D : DualChainData C}
    {N : MassNormalizedRecognitionNorm D}
    (E : CPTEnergyFunctional N) where
  admissibilityBound :
    ∀ {n : ℕ} (A : DualObstructionClass D n)
      (_m : CPTMinimalRepresentative E A),
      ℝ
  admissibilityBound_nonneg :
    ∀ {n : ℕ} (A : DualObstructionClass D n)
      (m : CPTMinimalRepresentative E A),
      0 ≤ admissibilityBound A m
  admissibility_bound :
    ∀ {n : ℕ} (A : DualObstructionClass D n)
      (m : CPTMinimalRepresentative E A),
      N.recNorm (A.toDual m.representative) ≤ admissibilityBound A m
  bound_controls_components :
    ∀ {n : ℕ} (A : DualObstructionClass D n)
      (m : CPTMinimalRepresentative E A)
      {B : ℝ},
      0 ≤ B →
      N.recNorm (A.toDual m.representative) ≤ B →
      N.linfDensity (A.toDual m.representative) ≤ B ∧
        N.scaleGradient (A.toDual m.representative) ≤ B

/-- Full Phase-5 compactness package. -/
structure RefereeCPTCompactnessPackage
    (X : SmoothProjectiveComplexVariety.{u})
    (p : ℕ)
    (chains : RefereeChainCurrentPackage X p)
    (cover : RefereeFixedCoverPackage X)
    (phase : RefereePhaseLatticePackage X cover) where
  duals : DualChainData chains.chains
  recognitionNorm : MassNormalizedRecognitionNorm duals
  cptEnergy : CPTEnergyFunctional recognitionNorm
  primitiveNonconcentration : PrimitivePhaseNonconcentrationData recognitionNorm
  noCheckerboard : NoCheckerboardAfterCPT cptEnergy
  recognitionBandlimit : RecognitionBandlimitData cptEnergy

/-- Phase-5 target: construct the analytic compactness package from real
chain/current and phase-lattice data. -/
def RefereeCPTCompactnessTarget : Prop :=
  ∀ (X : SmoothProjectiveComplexVariety.{u})
    (p : ℕ)
    (chains : RefereeChainCurrentPackage X p)
    (cover : RefereeFixedCoverPackage X)
    (phase : RefereePhaseLatticePackage X cover),
    Nonempty (RefereeCPTCompactnessPackage X p chains cover phase)

/-- Phase-5 completion marker: the analytic compactness target has been
isolated using actual norm/minimizer/nonconcentration interfaces. -/
theorem phase5_cpt_compactness_target_is_isolated :
    RefereeCPTCompactnessTarget.{u} = RefereeCPTCompactnessTarget.{u} :=
  rfl

end HodgeCPTCompactness
end Mathematics
end IndisputableMonolith

