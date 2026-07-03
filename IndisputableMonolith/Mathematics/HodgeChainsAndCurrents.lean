import Mathlib
import IndisputableMonolith.Mathematics.HodgeClassicalStatement

/-!
# Referee-Grade Chains and Currents Interface

This module starts Phase 2 of the referee-grade Hodge closure track.

The certificate-layer proof uses predicates such as
`IsClosed := True`, `IsComplexStiefel := True`,
`IsRecognitionAdmissible := True`, and `HasFixedDenominator := True`.
Those are acceptable only in the certificate layer.  A referee-grade
formalization needs actual chain and current objects with boundary maps,
norms, fixed-denominator data, and complex type predicates.

This file introduces the semantic interfaces that must replace those
certificate predicates.  It deliberately does not prove the analytic
theorems yet.  Later phases must instantiate these interfaces using
Mathlib-native geometry/current/cohomology APIs or exact named classical
inputs.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeChainsAndCurrents

open HodgeClassicalStatement

universe u

/-- Chain complex data over a smooth projective complex variety.

The boundary map and zero chains are data, so closedness is no longer an
uninterpreted `True` predicate. -/
structure ChainComplexData (X : SmoothProjectiveComplexVariety.{u}) where
  chainAt : ℕ → Type u
  zero : (n : ℕ) → chainAt n
  add : {n : ℕ} → chainAt n → chainAt n → chainAt n
  neg : {n : ℕ} → chainAt n → chainAt n
  boundary : (n : ℕ) → chainAt n → chainAt n
  add_assoc : ∀ {n : ℕ} (a b c : chainAt n), add (add a b) c = add a (add b c)
  add_comm : ∀ {n : ℕ} (a b : chainAt n), add a b = add b a
  add_zero : ∀ {n : ℕ} (c : chainAt n), add c (zero n) = c
  zero_add : ∀ {n : ℕ} (c : chainAt n), add (zero n) c = c
  add_neg : ∀ {n : ℕ} (c : chainAt n), add c (neg c) = zero n
  neg_neg : ∀ {n : ℕ} (c : chainAt n), neg (neg c) = c
  neg_zero : ∀ {n : ℕ}, neg (zero n) = zero n
  boundary_add : ∀ {n : ℕ} (c₁ c₂ : chainAt n),
    boundary n (add c₁ c₂) = add (boundary n c₁) (boundary n c₂)
  boundary_neg : ∀ {n : ℕ} (c : chainAt n),
    boundary n (neg c) = neg (boundary n c)
  boundary_squared_zero : ∀ (n : ℕ) (c : chainAt n),
    boundary n (boundary n c) = zero n
  boundary_zero : ∀ (n : ℕ), boundary n (zero n) = zero n

/-- Each degree of a chain complex carries an abelian group structure. -/
instance ChainComplexData.instAddCommGroup {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X) (n : ℕ) : AddCommGroup (C.chainAt n) where
  add := C.add
  zero := C.zero n
  neg := C.neg
  sub a b := C.add a (C.neg b)
  nsmul := fun k x => @nsmulRec _ ⟨C.zero n⟩ ⟨C.add⟩ k x
  zsmul := fun k x => @zsmulRec _ ⟨C.zero n⟩ ⟨C.add⟩ ⟨C.neg⟩
    (fun k x => @nsmulRec _ ⟨C.zero n⟩ ⟨C.add⟩ k x) k x
  add_assoc := C.add_assoc
  zero_add := C.zero_add
  add_zero := C.add_zero
  neg_add_cancel := fun a => (C.add_comm _ _).trans (C.add_neg a)
  add_comm := C.add_comm
  sub_eq_add_neg := fun _ _ => rfl
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

/-- Boundary as a Mathlib `AddMonoidHom`. -/
def ChainComplexData.boundaryHom {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X) (n : ℕ) : C.chainAt n →+ C.chainAt n where
  toFun := C.boundary n
  map_zero' := by exact C.boundary_zero n
  map_add' := by exact C.boundary_add

/-- The square of the boundary morphism is zero: ∂ ∘ ∂ = 0 as an `AddMonoidHom`. -/
theorem ChainComplexData.boundary_comp_eq_zero {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X) (n : ℕ) :
    (C.boundaryHom n).comp (C.boundaryHom n) = 0 :=
  AddMonoidHom.ext fun c => C.boundary_squared_zero n c

/-- The image of ∂ lies in the kernel of ∂: the foundational property of
homological algebra, connecting to Mathlib's `AddSubgroup` infrastructure. -/
theorem ChainComplexData.range_boundary_le_ker {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X) (n : ℕ) :
    (C.boundaryHom n).range ≤ (C.boundaryHom n).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  obtain ⟨y, rfl⟩ := hx
  exact C.boundary_squared_zero n y

/-- Cycles: chains in the kernel of ∂. This is the Mathlib-native `AddSubgroup`
of degree-n cycles Z_n = ker(∂_n). -/
def ChainComplexData.cycles {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X) (n : ℕ) : AddSubgroup (C.chainAt n) :=
  (C.boundaryHom n).ker

/-- Boundaries: chains in the image of ∂. For degree n, B_n = im(∂_n),
where ∂_n maps from degree n to degree n. Since our complex has
∂_n : chainAt n → chainAt n, boundaries at n come from applying ∂. -/
def ChainComplexData.boundaries {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X) (n : ℕ) : AddSubgroup (C.chainAt n) :=
  (C.boundaryHom n).range

/-- Boundaries are contained in cycles: B_n ⊆ Z_n. -/
theorem ChainComplexData.boundaries_le_cycles {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X) (n : ℕ) :
    C.boundaries n ≤ C.cycles n :=
  C.range_boundary_le_ker n

/-- A chain in degree `n`. -/
abbrev Chain {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X) (n : ℕ) : Type u :=
  C.chainAt n

/-- Closed chain: the boundary is the zero chain. -/
def IsClosedChain
    {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X)
    (n : ℕ)
    (c : Chain C n) : Prop :=
  C.boundary n c = C.zero n

/-- `IsClosedChain` is equivalent to membership in `AddMonoidHom.ker` of the
boundary morphism. -/
theorem IsClosedChain_iff_mem_ker
    {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X)
    (n : ℕ)
    (c : Chain C n) :
    IsClosedChain C n c ↔ c ∈ (C.boundaryHom n).ker := by
  constructor
  · intro h; rw [AddMonoidHom.mem_ker]; exact h
  · intro h; rw [AddMonoidHom.mem_ker] at h; exact h

/-- Chain mass norm data (seminorm axioms). -/
structure MassNormData
    {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X) where
  mass : {n : ℕ} → Chain C n → ℝ
  mass_nonneg : ∀ {n : ℕ} (c : Chain C n), 0 ≤ mass c
  mass_zero : ∀ {n : ℕ}, mass (C.zero n) = 0
  mass_neg : ∀ {n : ℕ} (c : Chain C n), mass (C.neg c) = mass c
  mass_triangle : ∀ {n : ℕ} (c₁ c₂ : Chain C n),
    mass (C.add c₁ c₂) ≤ mass c₁ + mass c₂

/-- Mass as a Mathlib `Norm` instance on chains. -/
instance MassNormData.instNorm {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (M : MassNormData C) (n : ℕ) : Norm (Chain C n) where
  norm := M.mass

/-- Chain mass as a Mathlib `AddGroupSeminorm`. -/
def MassNormData.toAddGroupSeminorm {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (M : MassNormData C) (n : ℕ) : AddGroupSeminorm (Chain C n) where
  toFun := M.mass
  map_zero' := M.mass_zero
  add_le' := M.mass_triangle
  neg' := M.mass_neg

/-- Flat norm data on chains (seminorm axioms). -/
structure FlatNormData
    {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X) where
  flatNorm : {n : ℕ} → Chain C n → ℝ
  flatNorm_nonneg : ∀ {n : ℕ} (c : Chain C n), 0 ≤ flatNorm c
  flatNorm_zero : ∀ {n : ℕ}, flatNorm (C.zero n) = 0
  flatNorm_neg : ∀ {n : ℕ} (c : Chain C n), flatNorm (C.neg c) = flatNorm c
  flatNorm_triangle : ∀ {n : ℕ} (c₁ c₂ : Chain C n),
    flatNorm (C.add c₁ c₂) ≤ flatNorm c₁ + flatNorm c₂

/-- Chain flat norm as a Mathlib `AddGroupSeminorm`. -/
def FlatNormData.toAddGroupSeminorm {X : SmoothProjectiveComplexVariety.{u}}
    {C : ChainComplexData X}
    (F : FlatNormData C) (n : ℕ) : AddGroupSeminorm (Chain C n) where
  toFun := F.flatNorm
  map_zero' := F.flatNorm_zero
  add_le' := F.flatNorm_triangle
  neg' := F.flatNorm_neg

/-- Fixed-denominator rational chain data.

This replaces the certificate predicate `HasFixedDenominator := True`. -/
structure FixedDenominatorChain
    {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X)
    (n : ℕ) where
  denominator : ℕ
  denominator_pos : 0 < denominator
  chain : Chain C n
  coefficientIndex : Type u
  coefficientIndex_fintype : Fintype coefficientIndex
  numerator : coefficientIndex → ℤ
  denominator_bounds_numerator : ∀ i, Int.natAbs (numerator i) ≤ denominator

instance {X : SmoothProjectiveComplexVariety.{u}} {C : ChainComplexData X} {n : ℕ}
    (q : FixedDenominatorChain C n) : Fintype q.coefficientIndex :=
  q.coefficientIndex_fintype

/-- Current space data associated to a smooth projective complex variety. -/
structure CurrentSpaceData (X : SmoothProjectiveComplexVariety.{u}) where
  current : ℕ → Type u
  zero : (n : ℕ) → current n
  add : {n : ℕ} → current n → current n → current n
  neg : {n : ℕ} → current n → current n
  smul : ℝ → {n : ℕ} → current n → current n
  boundary : (n : ℕ) → current n → current n
  mass : {n : ℕ} → current n → ℝ
  flatNorm : {n : ℕ} → current n → ℝ
  flatDistance : {n : ℕ} → current n → current n → ℝ
  testForm : ℕ → Type u
  evaluate : {n : ℕ} → current n → testForm n → ℝ
  isNonPPTestForm : (p : ℕ) → testForm (dualCurrentDegree X p) → Prop
  add_assoc : ∀ {n : ℕ} (R S T : current n), add (add R S) T = add R (add S T)
  add_comm : ∀ {n : ℕ} (S T : current n), add S T = add T S
  add_zero : ∀ {n : ℕ} (T : current n), add T (zero n) = T
  zero_add : ∀ {n : ℕ} (T : current n), add (zero n) T = T
  add_neg : ∀ {n : ℕ} (T : current n), add T (neg T) = zero n
  neg_neg : ∀ {n : ℕ} (T : current n), neg (neg T) = T
  neg_zero : ∀ {n : ℕ}, neg (zero n) = zero n
  smul_zero : ∀ (r : ℝ) {n : ℕ}, smul r (zero n) = zero n
  smul_add : ∀ (r : ℝ) {n : ℕ} (S T : current n),
    smul r (add S T) = add (smul r S) (smul r T)
  smul_one : ∀ {n : ℕ} (T : current n), smul 1 T = T
  smul_neg : ∀ (r : ℝ) {n : ℕ} (T : current n),
    smul r (neg T) = neg (smul r T)
  smul_smul : ∀ (r s : ℝ) {n : ℕ} (T : current n),
    smul r (smul s T) = smul (r * s) T
  zero_smul : ∀ {n : ℕ} (T : current n), smul 0 T = zero n
  add_smul : ∀ (r s : ℝ) {n : ℕ} (T : current n),
    smul (r + s) T = add (smul r T) (smul s T)
  evaluate_add_left : ∀ {n : ℕ} (S T : current n) (φ : testForm n),
    evaluate (add S T) φ = evaluate S φ + evaluate T φ
  evaluate_zero_left : ∀ {n : ℕ} (φ : testForm n),
    evaluate (zero n) φ = 0
  evaluate_smul_left : ∀ (r : ℝ) {n : ℕ} (T : current n) (φ : testForm n),
    evaluate (smul r T) φ = r * evaluate T φ
  mass_nonneg : ∀ {n : ℕ} (T : current n), 0 ≤ mass T
  mass_zero : ∀ {n : ℕ}, mass (zero n) = 0
  mass_neg : ∀ {n : ℕ} (T : current n), mass (neg T) = mass T
  mass_triangle : ∀ {n : ℕ} (S T : current n),
    mass (add S T) ≤ mass S + mass T
  flatNorm_nonneg : ∀ {n : ℕ} (T : current n), 0 ≤ flatNorm T
  flatNorm_zero : ∀ {n : ℕ}, flatNorm (zero n) = 0
  flatNorm_neg : ∀ {n : ℕ} (T : current n), flatNorm (neg T) = flatNorm T
  flatNorm_triangle : ∀ {n : ℕ} (S T : current n),
    flatNorm (add S T) ≤ flatNorm S + flatNorm T
  flatNorm_le_mass : ∀ {n : ℕ} (T : current n), flatNorm T ≤ mass T
  evaluate_neg_left : ∀ {n : ℕ} (T : current n) (φ : testForm n),
    evaluate (neg T) φ = -(evaluate T φ)
  flatDistance_nonneg : ∀ {n : ℕ} (S T : current n), 0 ≤ flatDistance S T
  flatDistance_self : ∀ {n : ℕ} (T : current n), flatDistance T T = 0
  flatDistance_symm : ∀ {n : ℕ} (S T : current n),
    flatDistance S T = flatDistance T S
  flatDistance_triangle : ∀ {n : ℕ} (R S T : current n),
    flatDistance R T ≤ flatDistance R S + flatDistance S T
  boundary_add : ∀ {n : ℕ} (S T : current n),
    boundary n (add S T) = add (boundary n S) (boundary n T)
  boundary_neg : ∀ {n : ℕ} (T : current n),
    boundary n (neg T) = neg (boundary n T)
  boundary_smul : ∀ (r : ℝ) {n : ℕ} (T : current n),
    boundary n (smul r T) = smul r (boundary n T)
  boundary_squared_zero : ∀ (n : ℕ) (T : current n),
    boundary n (boundary n T) = zero n
  boundary_zero : ∀ (n : ℕ), boundary n (zero n) = zero n

/-- Each degree of a current space carries an abelian group structure. -/
instance CurrentSpaceData.instAddCommGroup {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) : AddCommGroup (K.current n) where
  add := K.add
  zero := K.zero n
  neg := K.neg
  sub a b := K.add a (K.neg b)
  nsmul := fun k x => @nsmulRec _ ⟨K.zero n⟩ ⟨K.add⟩ k x
  zsmul := fun k x => @zsmulRec _ ⟨K.zero n⟩ ⟨K.add⟩ ⟨K.neg⟩
    (fun k x => @nsmulRec _ ⟨K.zero n⟩ ⟨K.add⟩ k x) k x
  add_assoc := K.add_assoc
  zero_add := K.zero_add
  add_zero := K.add_zero
  neg_add_cancel := fun a => (K.add_comm _ _).trans (K.add_neg a)
  add_comm := K.add_comm
  sub_eq_add_neg := fun _ _ => rfl
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

/-- Scalar multiplication on currents. -/
instance CurrentSpaceData.instSMul {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) : SMul ℝ (K.current n) where
  smul r x := K.smul r x

/-- Each degree of a current space carries an ℝ-module structure. -/
instance CurrentSpaceData.instModule {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) : Module ℝ (K.current n) where
  one_smul x := by exact K.smul_one x
  mul_smul r s x := by exact (K.smul_smul r s x).symm
  smul_zero r := by exact K.smul_zero r
  smul_add r x y := by exact K.smul_add r x y
  add_smul r s x := by exact K.add_smul r s x
  zero_smul x := by exact K.zero_smul x

/-- Boundary on currents as a Mathlib `LinearMap` (ℝ-linear endomorphism). -/
def CurrentSpaceData.boundaryLinear {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) : K.current n →ₗ[ℝ] K.current n where
  toFun := K.boundary n
  map_add' := by exact K.boundary_add
  map_smul' r x := by exact K.boundary_smul r x

/-- The square of the current boundary is zero: ∂ ∘ ∂ = 0 as a `LinearMap`. -/
theorem CurrentSpaceData.boundary_comp_eq_zero {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) :
    (K.boundaryLinear n).comp (K.boundaryLinear n) = 0 :=
  LinearMap.ext fun T => K.boundary_squared_zero n T

/-- The image of ∂ lies in the kernel of ∂ for currents (ℝ-linear version). -/
theorem CurrentSpaceData.range_boundary_le_ker {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) :
    LinearMap.range (K.boundaryLinear n) ≤ LinearMap.ker (K.boundaryLinear n) := by
  intro x hx
  rw [LinearMap.mem_ker]
  obtain ⟨y, rfl⟩ := hx
  exact K.boundary_squared_zero n y

/-- Each degree of a current space carries a pseudometric from the flat distance. -/
instance CurrentSpaceData.instPseudoMetricSpace {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) : PseudoMetricSpace (K.current n) where
  dist := K.flatDistance
  dist_self := K.flatDistance_self
  dist_comm := K.flatDistance_symm
  dist_triangle := K.flatDistance_triangle

/-- Mass as a Mathlib `Norm` instance on currents. -/
instance CurrentSpaceData.instNorm {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) : Norm (K.current n) where
  norm := K.mass

/-- Current mass as a Mathlib `AddGroupSeminorm`. -/
def CurrentSpaceData.massAddGroupSeminorm {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) : AddGroupSeminorm (K.current n) where
  toFun := K.mass
  map_zero' := K.mass_zero
  add_le' := K.mass_triangle
  neg' := K.mass_neg

/-- Current flat norm as a Mathlib `AddGroupSeminorm`. -/
def CurrentSpaceData.flatNormAddGroupSeminorm {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) : AddGroupSeminorm (K.current n) where
  toFun := K.flatNorm
  map_zero' := K.flatNorm_zero
  add_le' := K.flatNorm_triangle
  neg' := K.flatNorm_neg

/-- Cocycles: currents in the kernel of ∂. Z^n = ker(∂_n) as a `Submodule ℝ`. -/
def CurrentSpaceData.cocycles {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) : Submodule ℝ (K.current n) :=
  LinearMap.ker (K.boundaryLinear n)

/-- Coboundaries: currents in the image of ∂. B^n = im(∂_n) as a `Submodule ℝ`. -/
def CurrentSpaceData.coboundaries {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) : Submodule ℝ (K.current n) :=
  LinearMap.range (K.boundaryLinear n)

/-- Coboundaries are contained in cocycles: B^n ⊆ Z^n for currents. -/
theorem CurrentSpaceData.coboundaries_le_cocycles {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) :
    K.coboundaries n ≤ K.cocycles n :=
  K.range_boundary_le_ker n

/-- The flat norm seminorm is dominated by the mass seminorm on currents.
This is the Mathlib-native formulation of `flatNorm_le_mass`. -/
theorem CurrentSpaceData.flatNormSeminorm_le_massSeminorm
    {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) (n : ℕ) :
    K.flatNormAddGroupSeminorm n ≤ K.massAddGroupSeminorm n :=
  fun T => K.flatNorm_le_mass T

/-- For each fixed test form φ, evaluation T ↦ evaluate T φ is an ℝ-linear
functional from the current space to ℝ. -/
def CurrentSpaceData.evaluateLinear {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X) {n : ℕ} (φ : K.testForm n) :
    K.current n →ₗ[ℝ] ℝ where
  toFun T := K.evaluate T φ
  map_add' S T := by exact K.evaluate_add_left S T φ
  map_smul' r T := by exact K.evaluate_smul_left r T φ

/-- Closed current: the current boundary is zero. -/
def IsClosedCurrent
    {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X)
    (n : ℕ)
    (T : K.current n) : Prop :=
  K.boundary n T = K.zero n

/-- `IsClosedCurrent` is equivalent to membership in `LinearMap.ker` of the
boundary operator. This connects the geometric definition to the algebraic
kernel infrastructure. -/
theorem IsClosedCurrent_iff_mem_ker
    {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X)
    (n : ℕ)
    (T : K.current n) :
    IsClosedCurrent K n T ↔ T ∈ LinearMap.ker (K.boundaryLinear n) := by
  constructor
  · intro h; rw [LinearMap.mem_ker]; exact h
  · intro h; rw [LinearMap.mem_ker] at h; exact h

/-- Integral-current data. -/
structure IntegralCurrent
    {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X)
    (n : ℕ) where
  current : K.current n
  support : Type u
  multiplicity : support → ℤ
  rectifiableAtlas : Type u
  rectifiableChart : rectifiableAtlas

/-- Complex type `(p,p)` data for a current. -/
structure ComplexTypePP
    {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X)
    (p : ℕ)
    (T : K.current (dualCurrentDegree X p)) where
  annihilates_non_pp_test_forms :
    ∀ φ : K.testForm (dualCurrentDegree X p),
      K.isNonPPTestForm p φ → K.evaluate T φ = 0

/-- Recognition admissibility as genuine bounded data, not a `True`
predicate. -/
structure RecognitionAdmissibleChain
    {X : SmoothProjectiveComplexVariety.{u}}
    (C : ChainComplexData X)
    (M : MassNormData C)
    (n : ℕ)
    (c : Chain C n) where
  comassBound : ℝ
  variationBound : ℝ
  comassBound_nonneg : 0 ≤ comassBound
  variationBound_nonneg : 0 ≤ variationBound
  mass_le_comassBound : M.mass c ≤ comassBound
  variationBound_controls_mass :
    variationBound ≤ comassBound

/-- Flat-norm convergence of a sequence of currents. -/
structure FlatNormConverges
    {X : SmoothProjectiveComplexVariety.{u}}
    (K : CurrentSpaceData X)
    (n : ℕ)
    (seq : ℕ → K.current n)
    (limit : K.current n) where
  tendsToZero : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ,
    N ≤ k → K.flatDistance (seq k) limit < ε

/-- Flat-norm convergence implies metric-space convergence in the flat distance
pseudometric.  This connects the project's custom convergence predicate to
Mathlib's `Metric.tendsto_atTop`. -/
theorem FlatNormConverges.metric_tendsto
    {X : SmoothProjectiveComplexVariety.{u}}
    {K : CurrentSpaceData X}
    {n : ℕ}
    {seq : ℕ → K.current n}
    {limit : K.current n}
    (h : FlatNormConverges K n seq limit) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ,
      N ≤ k → @dist (K.current n) (K.instPseudoMetricSpace n).toDist (seq k) limit < ε :=
  h.tendsToZero

/-- Package of real chain/current semantics needed before the certificate
proof can be replaced by a referee-grade proof. -/
structure RefereeChainCurrentPackage
    (X : SmoothProjectiveComplexVariety.{u})
    (p : ℕ) where
  chains : ChainComplexData X
  massNorm : MassNormData chains
  flatNorm : FlatNormData chains
  currents : CurrentSpaceData X
  cellularApproximation : (n : ℕ) → Chain chains n → currents.current n
  cellularApproximation_add :
    ∀ {n : ℕ} (c₁ c₂ : Chain chains n),
      cellularApproximation n (chains.add c₁ c₂) =
        currents.add (cellularApproximation n c₁) (cellularApproximation n c₂)
  cellularApproximation_neg :
    ∀ {n : ℕ} (c : Chain chains n),
      cellularApproximation n (chains.neg c) =
        currents.neg (cellularApproximation n c)
  closed_chain_semantics :
    ∀ {n : ℕ} {c : Chain chains n},
      IsClosedChain chains n c →
      IsClosedCurrent currents n (cellularApproximation n c)
  flatNorm_le_mass : ∀ {n : ℕ} (c : Chain chains n),
    flatNorm.flatNorm c ≤ massNorm.mass c
  fixed_denominator_semantics :
    ∀ {n : ℕ} (q : FixedDenominatorChain chains n),
      RecognitionAdmissibleChain chains massNorm n q.chain

/-- The chain flat norm seminorm is dominated by the chain mass norm seminorm.
This is the Mathlib-native formulation of the package-level `flatNorm_le_mass`. -/
theorem RefereeChainCurrentPackage.flatNormSeminorm_le_massNormSeminorm
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (P : RefereeChainCurrentPackage X p) (n : ℕ) :
    P.flatNorm.toAddGroupSeminorm n ≤ P.massNorm.toAddGroupSeminorm n :=
  fun c => P.flatNorm_le_mass c

/-- Cellular approximation as a Mathlib `AddMonoidHom` from chains to currents.
The zero-preservation is derived from `add` and `neg` preservation using
the group axioms. -/
def RefereeChainCurrentPackage.cellularApproximationHom
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (P : RefereeChainCurrentPackage X p)
    (n : ℕ) : Chain P.chains n →+ P.currents.current n where
  toFun := P.cellularApproximation n
  map_zero' := by
    have h := P.cellularApproximation_add (P.chains.zero n) (P.chains.neg (P.chains.zero n))
    rw [P.chains.add_neg, P.cellularApproximation_neg, P.currents.add_neg] at h
    exact h
  map_add' := by exact P.cellularApproximation_add

/-- Cellular approximation maps closed chains (cycles) to closed currents:
the kernel of the chain boundary maps into the kernel of the current boundary
under the cellular approximation homomorphism. -/
theorem RefereeChainCurrentPackage.cellularApproximation_maps_cycles_to_cycles
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (P : RefereeChainCurrentPackage X p)
    {n : ℕ}
    {c : Chain P.chains n}
    (hc : c ∈ (P.chains.boundaryHom n).ker) :
    (P.cellularApproximationHom n) c ∈ LinearMap.ker (P.currents.boundaryLinear n) := by
  rw [AddMonoidHom.mem_ker] at hc
  rw [LinearMap.mem_ker]
  exact P.closed_chain_semantics hc

/-- Phase-2 target: construct real chain/current semantics for every
smooth projective complex variety and codimension. -/
def RefereeChainCurrentTarget : Prop :=
  ∀ (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ),
    Nonempty (RefereeChainCurrentPackage X p)

/-- Phase-2 completion marker: the target for replacing certificate
predicates by real chain/current semantics is isolated. -/
theorem phase2_chain_current_target_is_isolated :
    RefereeChainCurrentTarget.{u} = RefereeChainCurrentTarget.{u} :=
  rfl

end HodgeChainsAndCurrents
end Mathematics
end IndisputableMonolith

