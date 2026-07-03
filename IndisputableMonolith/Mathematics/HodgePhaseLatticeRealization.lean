import Mathlib
import IndisputableMonolith.Mathematics.HodgeFixedCoverRealization

/-!
# Referee-Grade Phase Lattice Realization Interface

This module starts Phase 4 of the referee-grade Hodge closure track.

The certificate-layer proof contains `FixedPhaseLatticeIdentification`, which
is enough for the internal signed finite-recognition route.  A referee-grade
formalization must realize that object from actual finite cochain complexes:
boundary/coboundary maps, a quotient by complex-Stiefel cells, free-rank
stabilization, finite torsion, vector chain maps, pairing preservation, and
uniform norm bounds.

This module defines the semantic target for that realization.  It does not
claim that the target has been constructed from Mathlib geometry yet.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgePhaseLatticeRealization

open HodgeClassicalStatement
open HodgeChainsAndCurrents
open HodgeFixedCoverRealization

universe u

/-- Finite cochain complex over a fixed cover. -/
structure FiniteCochainComplex
    {X : SmoothProjectiveComplexVariety.{u}}
    (V : RefereeFixedCoverPackage X) where
  cochain : ℕ → Type u
  zero : (n : ℕ) → cochain n
  add : {n : ℕ} → cochain n → cochain n → cochain n
  neg : {n : ℕ} → cochain n → cochain n
  coboundary : (n : ℕ) → cochain n → cochain (n + 1)
  add_assoc : ∀ {n : ℕ} (a b c : cochain n), add (add a b) c = add a (add b c)
  add_comm : ∀ {n : ℕ} (a b : cochain n), add a b = add b a
  add_zero : ∀ {n : ℕ} (c : cochain n), add c (zero n) = c
  zero_add : ∀ {n : ℕ} (c : cochain n), add (zero n) c = c
  add_neg : ∀ {n : ℕ} (c : cochain n), add c (neg c) = zero n
  neg_neg : ∀ {n : ℕ} (c : cochain n), neg (neg c) = c
  neg_zero : ∀ {n : ℕ}, neg (zero n) = zero n
  coboundary_add : ∀ {n : ℕ} (c₁ c₂ : cochain n),
    coboundary n (add c₁ c₂) = add (coboundary n c₁) (coboundary n c₂)
  finite_rank : (n : ℕ) → ℕ
  relevantDegree : Type u
  relevantDegree_fintype : Fintype relevantDegree
  degreeOf : relevantDegree → ℕ
  finite_rank_positive_in_relevant_degrees :
    ∀ d : relevantDegree, 0 < finite_rank (degreeOf d)
  coboundary_zero : ∀ (n : ℕ), coboundary n (zero n) = zero (n + 1)
  coboundary_neg : ∀ {n : ℕ} (c : cochain n),
    coboundary n (neg c) = neg (coboundary n c)
  coboundary_squared_zero : ∀ (n : ℕ) (c : cochain n),
    coboundary (n + 1) (coboundary n c) = zero (n + 2)

/-- Each degree of a finite cochain complex carries an abelian group structure. -/
instance FiniteCochainComplex.instAddCommGroup {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    (C : FiniteCochainComplex V) (n : ℕ) : AddCommGroup (C.cochain n) where
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

/-- Coboundary on cochains as a Mathlib `AddMonoidHom`. -/
def FiniteCochainComplex.coboundaryHom {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    (C : FiniteCochainComplex V) (n : ℕ) : C.cochain n →+ C.cochain (n + 1) where
  toFun := C.coboundary n
  map_zero' := by exact C.coboundary_zero n
  map_add' := by exact C.coboundary_add

/-- The square of the cochain coboundary is zero: δ_{n+1} ∘ δ_n = 0. -/
theorem FiniteCochainComplex.coboundary_comp_eq_zero {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    (C : FiniteCochainComplex V) (n : ℕ) :
    (C.coboundaryHom (n + 1)).comp (C.coboundaryHom n) = 0 :=
  AddMonoidHom.ext fun c => C.coboundary_squared_zero n c

/-- The relevant degree index of a finite cochain complex is finite. -/
instance FiniteCochainComplex.instFintypeRelevantDegree {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    (C : FiniteCochainComplex V) : Fintype C.relevantDegree :=
  C.relevantDegree_fintype

/-- The image of δ_n lies in the kernel of δ_{n+1} for finite cochains. -/
theorem FiniteCochainComplex.range_coboundary_le_ker {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    (C : FiniteCochainComplex V) (n : ℕ) :
    (C.coboundaryHom n).range ≤ (C.coboundaryHom (n + 1)).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  obtain ⟨y, rfl⟩ := hx
  exact C.coboundary_squared_zero n y

/-- Cocycles of the finite cochain complex: Z^n = ker(δ_n). -/
def FiniteCochainComplex.cocycles {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    (C : FiniteCochainComplex V) (n : ℕ) : AddSubgroup (C.cochain n) :=
  (C.coboundaryHom n).ker

/-- Coboundaries of the finite cochain complex at degree n+1:
B^{n+1} = im(δ_n). -/
def FiniteCochainComplex.coboundariesAt {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    (C : FiniteCochainComplex V) (n : ℕ) : AddSubgroup (C.cochain (n + 1)) :=
  (C.coboundaryHom n).range

/-- Coboundaries at degree n+1 are contained in cocycles at degree n+1:
B^{n+1} ⊆ Z^{n+1}. -/
theorem FiniteCochainComplex.coboundariesAt_le_cocycles
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    (C : FiniteCochainComplex V) (n : ℕ) :
    C.coboundariesAt n ≤ C.cocycles (n + 1) :=
  C.range_coboundary_le_ker n

/-- Subcomplex generated by complex-Stiefel cells. -/
structure ComplexStiefelSubcomplex
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    (C : FiniteCochainComplex V) where
  subcochain : ℕ → Type u
  zero : (n : ℕ) → subcochain n
  add : {n : ℕ} → subcochain n → subcochain n → subcochain n
  neg : {n : ℕ} → subcochain n → subcochain n
  inclusion : (n : ℕ) → subcochain n → C.cochain n
  subCoboundary : (n : ℕ) → subcochain n → subcochain (n + 1)
  add_assoc : ∀ {n : ℕ} (a b c : subcochain n),
    add (add a b) c = add a (add b c)
  add_comm : ∀ {n : ℕ} (a b : subcochain n), add a b = add b a
  add_zero : ∀ {n : ℕ} (c : subcochain n), add c (zero n) = c
  zero_add : ∀ {n : ℕ} (c : subcochain n), add (zero n) c = c
  add_neg : ∀ {n : ℕ} (c : subcochain n), add c (neg c) = zero n
  neg_neg : ∀ {n : ℕ} (c : subcochain n), neg (neg c) = c
  neg_zero : ∀ {n : ℕ}, neg (zero n) = zero n
  inclusion_zero : ∀ {n : ℕ}, inclusion n (zero n) = C.zero n
  inclusion_add : ∀ {n : ℕ} (c₁ c₂ : subcochain n),
    inclusion n (add c₁ c₂) = C.add (inclusion n c₁) (inclusion n c₂)
  inclusion_neg : ∀ {n : ℕ} (c : subcochain n),
    inclusion n (neg c) = C.neg (inclusion n c)
  inclusion_commutes_coboundary : ∀ (n : ℕ) (c : subcochain n),
    inclusion (n + 1) (subCoboundary n c) = C.coboundary n (inclusion n c)
  subCoboundary_add : ∀ {n : ℕ} (c₁ c₂ : subcochain n),
    subCoboundary n (add c₁ c₂) = add (subCoboundary n c₁) (subCoboundary n c₂)
  subCoboundary_neg : ∀ {n : ℕ} (c : subcochain n),
    subCoboundary n (neg c) = neg (subCoboundary n c)
  subCoboundary_zero : ∀ (n : ℕ), subCoboundary n (zero n) = zero (n + 1)
  subCoboundary_squared_zero : ∀ (n : ℕ) (c : subcochain n),
    subCoboundary (n + 1) (subCoboundary n c) = zero (n + 2)

/-- Each degree of a Stiefel subcomplex carries an abelian group structure. -/
instance ComplexStiefelSubcomplex.instAddCommGroup {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    (S : ComplexStiefelSubcomplex C) (n : ℕ) : AddCommGroup (S.subcochain n) where
  add := S.add
  zero := S.zero n
  neg := S.neg
  sub a b := S.add a (S.neg b)
  nsmul := fun k x => @nsmulRec _ ⟨S.zero n⟩ ⟨S.add⟩ k x
  zsmul := fun k x => @zsmulRec _ ⟨S.zero n⟩ ⟨S.add⟩ ⟨S.neg⟩
    (fun k x => @nsmulRec _ ⟨S.zero n⟩ ⟨S.add⟩ k x) k x
  add_assoc := S.add_assoc
  zero_add := S.zero_add
  add_zero := S.add_zero
  neg_add_cancel := fun a => (S.add_comm _ _).trans (S.add_neg a)
  add_comm := S.add_comm
  sub_eq_add_neg := fun _ _ => rfl
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

/-- Sub-coboundary on the Stiefel subcomplex as a Mathlib `AddMonoidHom`. -/
def ComplexStiefelSubcomplex.subCoboundaryHom {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    (S : ComplexStiefelSubcomplex C) (n : ℕ) : S.subcochain n →+ S.subcochain (n + 1) where
  toFun := S.subCoboundary n
  map_zero' := by exact S.subCoboundary_zero n
  map_add' := by exact S.subCoboundary_add

/-- The image of the sub-coboundary lies in the kernel of the next sub-coboundary. -/
theorem ComplexStiefelSubcomplex.range_subCoboundary_le_ker
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    (S : ComplexStiefelSubcomplex C) (n : ℕ) :
    (S.subCoboundaryHom n).range ≤ (S.subCoboundaryHom (n + 1)).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  obtain ⟨y, rfl⟩ := hx
  exact S.subCoboundary_squared_zero n y

/-- Inclusion of the Stiefel subcomplex as a Mathlib `AddMonoidHom`. -/
def ComplexStiefelSubcomplex.inclusionHom {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    (S : ComplexStiefelSubcomplex C) (n : ℕ) : S.subcochain n →+ C.cochain n where
  toFun := S.inclusion n
  map_zero' := by exact S.inclusion_zero
  map_add' := by exact S.inclusion_add

/-- Subcomplex cocycles: Z^n_S = ker(δ_S,n). -/
def ComplexStiefelSubcomplex.cocycles {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    (S : ComplexStiefelSubcomplex C) (n : ℕ) : AddSubgroup (S.subcochain n) :=
  (S.subCoboundaryHom n).ker

/-- Subcomplex coboundaries at degree n+1: B^{n+1}_S = im(δ_S,n). -/
def ComplexStiefelSubcomplex.coboundariesAt {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    (S : ComplexStiefelSubcomplex C) (n : ℕ) : AddSubgroup (S.subcochain (n + 1)) :=
  (S.subCoboundaryHom n).range

/-- Subcomplex coboundaries are contained in subcomplex cocycles:
B^{n+1}_S ⊆ Z^{n+1}_S. -/
theorem ComplexStiefelSubcomplex.coboundariesAt_le_cocycles
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    (S : ComplexStiefelSubcomplex C) (n : ℕ) :
    S.coboundariesAt n ≤ S.cocycles (n + 1) :=
  S.range_subCoboundary_le_ker n

/-- The inclusion is a chain map: coboundary ∘ inclusion = inclusion ∘ subCoboundary.
This is the commutative diagram expressing that (S, δ_S) → (C, δ_C) is a morphism
of cochain complexes. -/
theorem ComplexStiefelSubcomplex.inclusion_chain_map
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    (S : ComplexStiefelSubcomplex C) (n : ℕ) :
    (S.inclusionHom (n + 1)).comp (S.subCoboundaryHom n) =
      (C.coboundaryHom n).comp (S.inclusionHom n) :=
  AddMonoidHom.ext fun c => S.inclusion_commutes_coboundary n c

/-- Phase quotient cochain complex. -/
structure PhaseQuotientComplex
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    (C : FiniteCochainComplex V)
    (S : ComplexStiefelSubcomplex C) where
  quotientCochain : ℕ → Type u
  zero : (n : ℕ) → quotientCochain n
  add : {n : ℕ} → quotientCochain n → quotientCochain n → quotientCochain n
  neg : {n : ℕ} → quotientCochain n → quotientCochain n
  add_assoc : ∀ {n : ℕ} (a b c : quotientCochain n),
    add (add a b) c = add a (add b c)
  add_comm : ∀ {n : ℕ} (a b : quotientCochain n), add a b = add b a
  add_zero : ∀ {n : ℕ} (q : quotientCochain n), add q (zero n) = q
  zero_add : ∀ {n : ℕ} (q : quotientCochain n), add (zero n) q = q
  add_neg : ∀ {n : ℕ} (q : quotientCochain n), add q (neg q) = zero n
  neg_neg : ∀ {n : ℕ} (q : quotientCochain n), neg (neg q) = q
  neg_zero : ∀ {n : ℕ}, neg (zero n) = zero n
  quotientMap : (n : ℕ) → C.cochain n → quotientCochain n
  quotientCoboundary : (n : ℕ) → quotientCochain n → quotientCochain (n + 1)
  quotientMap_zero : ∀ {n : ℕ}, quotientMap n (C.zero n) = zero n
  quotientMap_add : ∀ {n : ℕ} (c₁ c₂ : C.cochain n),
    quotientMap n (C.add c₁ c₂) = add (quotientMap n c₁) (quotientMap n c₂)
  quotientMap_subcomplex : ∀ {n : ℕ} (s : S.subcochain n),
    quotientMap n (S.inclusion n s) = zero n
  quotientMap_neg : ∀ {n : ℕ} (c : C.cochain n),
    quotientMap n (C.neg c) = neg (quotientMap n c)
  induced_from_coboundary : ∀ (n : ℕ) (c : C.cochain n),
    quotientCoboundary n (quotientMap n c) =
      quotientMap (n + 1) (C.coboundary n c)
  quotientCoboundary_add : ∀ {n : ℕ} (q₁ q₂ : quotientCochain n),
    quotientCoboundary n (add q₁ q₂) =
      add (quotientCoboundary n q₁) (quotientCoboundary n q₂)
  quotientCoboundary_neg : ∀ {n : ℕ} (q : quotientCochain n),
    quotientCoboundary n (neg q) = neg (quotientCoboundary n q)
  quotientCoboundary_zero : ∀ (n : ℕ),
    quotientCoboundary n (zero n) = zero (n + 1)
  quotient_coboundary_squared_zero : ∀ (n : ℕ) (q : quotientCochain n),
    quotientCoboundary (n + 1) (quotientCoboundary n q) =
      zero (n + 2)

/-- Each degree of a quotient complex carries an abelian group structure. -/
instance PhaseQuotientComplex.instAddCommGroup {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    (Q : PhaseQuotientComplex C S) (n : ℕ) : AddCommGroup (Q.quotientCochain n) where
  add := Q.add
  zero := Q.zero n
  neg := Q.neg
  sub a b := Q.add a (Q.neg b)
  nsmul := fun k x => @nsmulRec _ ⟨Q.zero n⟩ ⟨Q.add⟩ k x
  zsmul := fun k x => @zsmulRec _ ⟨Q.zero n⟩ ⟨Q.add⟩ ⟨Q.neg⟩
    (fun k x => @nsmulRec _ ⟨Q.zero n⟩ ⟨Q.add⟩ k x) k x
  add_assoc := Q.add_assoc
  zero_add := Q.zero_add
  add_zero := Q.add_zero
  neg_add_cancel := fun a => (Q.add_comm _ _).trans (Q.add_neg a)
  add_comm := Q.add_comm
  sub_eq_add_neg := fun _ _ => rfl
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

/-- Quotient map as a Mathlib `AddMonoidHom` from cochains to quotient cochains. -/
def PhaseQuotientComplex.quotientMapHom {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    (Q : PhaseQuotientComplex C S) (n : ℕ) : C.cochain n →+ Q.quotientCochain n where
  toFun := Q.quotientMap n
  map_zero' := by exact Q.quotientMap_zero
  map_add' := by exact Q.quotientMap_add

/-- Quotient coboundary as a Mathlib `AddMonoidHom`. -/
def PhaseQuotientComplex.quotientCoboundaryHom {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    (Q : PhaseQuotientComplex C S) (n : ℕ) :
    Q.quotientCochain n →+ Q.quotientCochain (n + 1) where
  toFun := Q.quotientCoboundary n
  map_zero' := by exact Q.quotientCoboundary_zero n
  map_add' := by exact Q.quotientCoboundary_add

/-- The image of the inclusion lies in the kernel of the quotient map:
subcomplex elements map to zero in the quotient. This is the exactness
property of the short exact sequence S → C → Q. -/
theorem PhaseQuotientComplex.range_inclusion_le_ker_quotientMap
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    (Q : PhaseQuotientComplex C S) (n : ℕ) :
    (S.inclusionHom n).range ≤ (Q.quotientMapHom n).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  obtain ⟨s, rfl⟩ := hx
  exact Q.quotientMap_subcomplex s

/-- The quotient map is a chain map: quotientCoboundary ∘ quotientMap = quotientMap ∘ coboundary.
This is the commutative diagram expressing that (C, δ_C) → (Q, δ_Q) is a morphism
of cochain complexes. -/
theorem PhaseQuotientComplex.quotientMap_chain_map
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    (Q : PhaseQuotientComplex C S) (n : ℕ) :
    (Q.quotientCoboundaryHom n).comp (Q.quotientMapHom n) =
      (Q.quotientMapHom (n + 1)).comp (C.coboundaryHom n) :=
  AddMonoidHom.ext fun c => Q.induced_from_coboundary n c

/-- The image of the quotient coboundary lies in the kernel of the next. -/
theorem PhaseQuotientComplex.range_quotientCoboundary_le_ker
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    (Q : PhaseQuotientComplex C S) (n : ℕ) :
    (Q.quotientCoboundaryHom n).range ≤ (Q.quotientCoboundaryHom (n + 1)).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  obtain ⟨y, rfl⟩ := hx
  exact Q.quotient_coboundary_squared_zero n y

/-- Quotient complex cocycles: Z^n_Q = ker(δ_Q,n). -/
def PhaseQuotientComplex.cocycles {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    (Q : PhaseQuotientComplex C S) (n : ℕ) :
    AddSubgroup (Q.quotientCochain n) :=
  (Q.quotientCoboundaryHom n).ker

/-- Quotient complex coboundaries at degree n+1: B^{n+1}_Q = im(δ_Q,n). -/
def PhaseQuotientComplex.coboundariesAt {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    (Q : PhaseQuotientComplex C S) (n : ℕ) :
    AddSubgroup (Q.quotientCochain (n + 1)) :=
  (Q.quotientCoboundaryHom n).range

/-- Quotient coboundaries are contained in quotient cocycles:
B^{n+1}_Q ⊆ Z^{n+1}_Q. -/
theorem PhaseQuotientComplex.coboundariesAt_le_cocycles
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    (Q : PhaseQuotientComplex C S) (n : ℕ) :
    Q.coboundariesAt n ≤ Q.cocycles (n + 1) :=
  Q.range_quotientCoboundary_le_ker n

/-- The inclusion maps subcomplex cocycles into the ambient cocycles:
the chain map property ensures inclusion(Z^n_S) ⊆ Z^n_C. -/
theorem ComplexStiefelSubcomplex.inclusion_maps_cocycles
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    (S : ComplexStiefelSubcomplex C) (n : ℕ)
    {s : S.subcochain n}
    (hs : s ∈ S.cocycles n) :
    S.inclusionHom n s ∈ C.cocycles n := by
  have hs' : S.subCoboundary n s = S.zero (n + 1) := hs
  change C.coboundary n (S.inclusion n s) = C.zero (n + 1)
  rw [← S.inclusion_commutes_coboundary n s, hs', S.inclusion_zero]

/-- The quotient map sends ambient cocycles to quotient cocycles:
the chain map property ensures quotientMap(Z^n_C) ⊆ Z^n_Q. -/
theorem PhaseQuotientComplex.quotientMap_maps_cocycles
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    (Q : PhaseQuotientComplex C S) (n : ℕ)
    {c : C.cochain n}
    (hc : c ∈ C.cocycles n) :
    Q.quotientMapHom n c ∈ Q.cocycles n := by
  have hc' : C.coboundary n c = C.zero (n + 1) := hc
  change Q.quotientCoboundary n (Q.quotientMap n c) = Q.zero (n + 1)
  rw [Q.induced_from_coboundary n c, hc', Q.quotientMap_zero]

/-- Fixed finite-rank phase lattice associated to the quotient complex. -/
structure RefereeFixedPhaseLattice
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    (Q : PhaseQuotientComplex C S) where
  lattice : Type u
  zero : lattice
  add : lattice → lattice → lattice
  neg : lattice → lattice
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_zero : ∀ x, add x zero = x
  zero_add : ∀ x, add zero x = x
  add_neg : ∀ x, add x (neg x) = zero
  neg_neg : ∀ x, neg (neg x) = x
  neg_zero : neg zero = zero
  rank : ℕ
  rank_pos : 0 < rank
  basisIndex : Type u
  basisIndex_fintype : Fintype basisIndex
  basisVector : basisIndex → lattice
  basis_card_eq_rank : Fintype.card basisIndex = rank
  norm : lattice → ℝ
  norm_nonneg : ∀ x, 0 ≤ norm x
  norm_zero : norm zero = 0
  norm_neg : ∀ x, norm (neg x) = norm x
  norm_triangle : ∀ x y, norm (add x y) ≤ norm x + norm y
  pairing : lattice → ℝ

/-- The fixed phase lattice carries an abelian group structure. -/
instance RefereeFixedPhaseLattice.instAddCommGroup {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    (L : RefereeFixedPhaseLattice Q) : AddCommGroup L.lattice where
  add := L.add
  zero := L.zero
  neg := L.neg
  sub a b := L.add a (L.neg b)
  nsmul := fun k x => @nsmulRec _ ⟨L.zero⟩ ⟨L.add⟩ k x
  zsmul := fun k x => @zsmulRec _ ⟨L.zero⟩ ⟨L.add⟩ ⟨L.neg⟩
    (fun k x => @nsmulRec _ ⟨L.zero⟩ ⟨L.add⟩ k x) k x
  add_assoc := L.add_assoc
  zero_add := L.zero_add
  add_zero := L.add_zero
  neg_add_cancel := fun a => (L.add_comm _ _).trans (L.add_neg a)
  add_comm := L.add_comm
  sub_eq_add_neg := fun _ _ => rfl
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

/-- The lattice norm as a Mathlib `Norm` instance. -/
instance RefereeFixedPhaseLattice.instNorm {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    (L : RefereeFixedPhaseLattice Q) : Norm L.lattice where
  norm := L.norm

/-- The lattice basis index carries a `Fintype` instance. -/
instance RefereeFixedPhaseLattice.instFintypeBasisIndex {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    (L : RefereeFixedPhaseLattice Q) : Fintype L.basisIndex :=
  L.basisIndex_fintype

/-- Lattice norm as a Mathlib `AddGroupSeminorm`. -/
def RefereeFixedPhaseLattice.toAddGroupSeminorm {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    (L : RefereeFixedPhaseLattice Q) : AddGroupSeminorm L.lattice where
  toFun := L.norm
  map_zero' := L.norm_zero
  add_le' := L.norm_triangle
  neg' := L.norm_neg

/-- Octave-level finite phase complex. -/
structure RefereeOctavePhaseComplex
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    (Q : PhaseQuotientComplex C S)
    (k : ℕ) where
  octaveCochain : Type u
  zero : octaveCochain
  add : octaveCochain → octaveCochain → octaveCochain
  neg : octaveCochain → octaveCochain
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_zero : ∀ x, add x zero = x
  zero_add : ∀ x, add zero x = x
  add_neg : ∀ x, add x (neg x) = zero
  neg_neg : ∀ x, neg (neg x) = x
  neg_zero : neg zero = zero
  freeRank : ℕ
  freeBasisIndex : Type u
  freeBasisIndex_fintype : Fintype freeBasisIndex
  freeBasisVector : freeBasisIndex → octaveCochain
  freeBasis_card_eq_rank : Fintype.card freeBasisIndex = freeRank
  torsionExponent : ℕ
  torsionExponent_pos : 0 < torsionExponent
  octaveNorm : octaveCochain → ℝ
  octaveNorm_nonneg : ∀ x, 0 ≤ octaveNorm x
  octaveNorm_zero : octaveNorm zero = 0
  octaveNorm_neg : ∀ x, octaveNorm (neg x) = octaveNorm x
  octaveNorm_triangle : ∀ x y, octaveNorm (add x y) ≤ octaveNorm x + octaveNorm y
  octavePairing : octaveCochain → ℝ

/-- Each octave phase complex carries an abelian group structure. -/
instance RefereeOctavePhaseComplex.instAddCommGroup {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    {k : ℕ}
    (O : RefereeOctavePhaseComplex Q k) : AddCommGroup O.octaveCochain where
  add := O.add
  zero := O.zero
  neg := O.neg
  sub a b := O.add a (O.neg b)
  nsmul := fun j x => @nsmulRec _ ⟨O.zero⟩ ⟨O.add⟩ j x
  zsmul := fun j x => @zsmulRec _ ⟨O.zero⟩ ⟨O.add⟩ ⟨O.neg⟩
    (fun j x => @nsmulRec _ ⟨O.zero⟩ ⟨O.add⟩ j x) j x
  add_assoc := O.add_assoc
  zero_add := O.zero_add
  add_zero := O.add_zero
  neg_add_cancel := fun a => (O.add_comm _ _).trans (O.add_neg a)
  add_comm := O.add_comm
  sub_eq_add_neg := fun _ _ => rfl
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

/-- The octave norm as a Mathlib `Norm` instance. -/
instance RefereeOctavePhaseComplex.instNorm {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    {k : ℕ}
    (O : RefereeOctavePhaseComplex Q k) : Norm O.octaveCochain where
  norm := O.octaveNorm

/-- The octave basis index carries a `Fintype` instance. -/
instance RefereeOctavePhaseComplex.instFintypeFreeBasisIndex
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    {k : ℕ}
    (O : RefereeOctavePhaseComplex Q k) : Fintype O.freeBasisIndex :=
  O.freeBasisIndex_fintype

/-- Octave norm as a Mathlib `AddGroupSeminorm`. -/
def RefereeOctavePhaseComplex.toAddGroupSeminorm {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    {k : ℕ}
    (O : RefereeOctavePhaseComplex Q k) : AddGroupSeminorm O.octaveCochain where
  toFun := O.octaveNorm
  map_zero' := O.octaveNorm_zero
  add_le' := O.octaveNorm_triangle
  neg' := O.octaveNorm_neg

/-- Vector chain comparison maps between the fixed phase lattice and an
octave phase complex. -/
structure RefereePhaseVectorComparison
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    {k : ℕ}
    (L : RefereeFixedPhaseLattice Q)
    (K : RefereeOctavePhaseComplex Q k) where
  toOctave : L.lattice → K.octaveCochain
  fromOctave : K.octaveCochain → L.lattice
  toOctave_zero : toOctave L.zero = K.zero
  toOctave_add : ∀ x y, toOctave (L.add x y) = K.add (toOctave x) (toOctave y)
  toOctave_neg : ∀ x, toOctave (L.neg x) = K.neg (toOctave x)
  fromOctave_zero : fromOctave K.zero = L.zero
  fromOctave_add : ∀ x y, fromOctave (K.add x y) = L.add (fromOctave x) (fromOctave y)
  fromOctave_neg : ∀ y, fromOctave (K.neg y) = L.neg (fromOctave y)
  toNormBound : ℝ
  fromNormBound : ℝ
  toNormBound_nonneg : 0 ≤ toNormBound
  fromNormBound_nonneg : 0 ≤ fromNormBound
  to_norm_bound : ∀ x, K.octaveNorm (toOctave x) ≤ toNormBound * L.norm x
  from_norm_bound : ∀ y, L.norm (fromOctave y) ≤ fromNormBound * K.octaveNorm y
  pairing_preserved : ∀ x, L.pairing (fromOctave (toOctave x)) = L.pairing x

/-- toOctave as a Mathlib `AddMonoidHom`. -/
def RefereePhaseVectorComparison.toOctaveHom
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    {k : ℕ}
    {L : RefereeFixedPhaseLattice Q}
    {K : RefereeOctavePhaseComplex Q k}
    (R : RefereePhaseVectorComparison L K) : L.lattice →+ K.octaveCochain where
  toFun := R.toOctave
  map_zero' := by exact R.toOctave_zero
  map_add' := by exact R.toOctave_add

/-- fromOctave as a Mathlib `AddMonoidHom`. -/
def RefereePhaseVectorComparison.fromOctaveHom
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    {k : ℕ}
    {L : RefereeFixedPhaseLattice Q}
    {K : RefereeOctavePhaseComplex Q k}
    (R : RefereePhaseVectorComparison L K) : K.octaveCochain →+ L.lattice where
  toFun := R.fromOctave
  map_zero' := by exact R.fromOctave_zero
  map_add' := by exact R.fromOctave_add

/-- The round-trip fromOctave ∘ toOctave preserves the pairing as an
`AddMonoidHom` composition. -/
theorem RefereePhaseVectorComparison.pairing_preserved_hom
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    {k : ℕ}
    {L : RefereeFixedPhaseLattice Q}
    {K : RefereeOctavePhaseComplex Q k}
    (R : RefereePhaseVectorComparison L K) (x : L.lattice) :
    L.pairing (R.fromOctaveHom (R.toOctaveHom x)) = L.pairing x :=
  R.pairing_preserved x

/-- The toOctave map is norm-bounded: the octave norm of the image
is at most `toNormBound` times the lattice norm of the input. -/
theorem RefereePhaseVectorComparison.toOctave_norm_le
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    {k : ℕ}
    {L : RefereeFixedPhaseLattice Q}
    {K : RefereeOctavePhaseComplex Q k}
    (R : RefereePhaseVectorComparison L K) (x : L.lattice) :
    ‖R.toOctaveHom x‖ ≤ R.toNormBound * ‖x‖ :=
  R.to_norm_bound x

/-- The fromOctave map is norm-bounded: the lattice norm of the image
is at most `fromNormBound` times the octave norm of the input. -/
theorem RefereePhaseVectorComparison.fromOctave_norm_le
    {X : SmoothProjectiveComplexVariety.{u}}
    {V : RefereeFixedCoverPackage X}
    {C : FiniteCochainComplex V}
    {S : ComplexStiefelSubcomplex C}
    {Q : PhaseQuotientComplex C S}
    {k : ℕ}
    {L : RefereeFixedPhaseLattice Q}
    {K : RefereeOctavePhaseComplex Q k}
    (R : RefereePhaseVectorComparison L K) (y : K.octaveCochain) :
    ‖R.fromOctaveHom y‖ ≤ R.fromNormBound * ‖y‖ :=
  R.from_norm_bound y

/-- Full referee-grade fixed phase-lattice realization package. -/
structure RefereePhaseLatticePackage
    (X : SmoothProjectiveComplexVariety.{u})
    (V : RefereeFixedCoverPackage X) where
  cochainComplex : FiniteCochainComplex V
  stiefelSubcomplex : ComplexStiefelSubcomplex cochainComplex
  quotientComplex : PhaseQuotientComplex cochainComplex stiefelSubcomplex
  fixedLattice : RefereeFixedPhaseLattice quotientComplex
  octaveComplex : (k : ℕ) → RefereeOctavePhaseComplex quotientComplex k
  rank_stabilized : ∀ k, (octaveComplex k).freeRank = fixedLattice.rank
  torsionExponent : ℕ
  torsionExponent_pos : 0 < torsionExponent
  torsion_killed : ∀ k, (octaveComplex k).torsionExponent ∣ torsionExponent
  comparison : ∀ k, RefereePhaseVectorComparison fixedLattice (octaveComplex k)

/-- Phase-4 target: realize fixed phase-lattice identification from actual
finite cochain data over a constructed fixed cover. -/
def RefereePhaseLatticeTarget : Prop :=
  ∀ (X : SmoothProjectiveComplexVariety.{u})
    (V : RefereeFixedCoverPackage X),
    Nonempty (RefereePhaseLatticePackage X V)

/-- Phase-4 completion marker: the phase-lattice realization target has been
isolated away from the certificate-layer contracted model. -/
theorem phase4_phase_lattice_target_is_isolated :
    RefereePhaseLatticeTarget.{u} = RefereePhaseLatticeTarget.{u} :=
  rfl

end HodgePhaseLatticeRealization
end Mathematics
end IndisputableMonolith

