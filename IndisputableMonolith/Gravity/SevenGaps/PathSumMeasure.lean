import Mathlib
import IndisputableMonolith.Gravity.PathSumUVBound

/-!
# Seven Gaps, Lane 2: A Proved Path-Sum Measure for Z_RS

## Status tiers (honest tagging)

**THEOREM (proved below, 0 sorry, 0 new axioms):**
* The scoped configuration class `BoundedComplex B` is a `Fintype`
  (`instFintypeBoundedComplex`, via the explicit equivalence `codeEquiv`).
  Scope honesty: `BoundedComplex` carries arbitrary bounded incidence data
  (it does not enforce simplicial constraints, so it CONTAINS all bounded
  triangulations but also non-simplicial configurations); finiteness of the
  superclass gives finiteness of every subclass. This DISCHARGES the
  count-finiteness content of the assumed `growthBase` field of
  `PathSumUVBound.AdmissibleTriangulationFamily` (a proved finite cardinal
  where a bound was postulated); the sharper exponential-growth semantics
  of that field for exact simplicial classes remains OPEN.
* Relabeling isomorphism is a genuine equivalence relation
  (`relabelSetoid`; refl/symm/trans proved, not asserted), and the quotient
  `TriangulationClass B` is finite (`triangulationClass_finite`).
* The automorphism group `Aut K` of a labeled complex is finite and nonempty,
  so the symmetry-factor measure `mu K = 1 / |Aut K|` satisfies
  `0 < mu K ≤ 1` (`mu_pos`, `mu_le_one`) and is a relabeling invariant
  (`mu_congr`).
* The path sum `Z B w = Σ_K mu(K) · w(K)` over the labeled class is a finite
  sum with the modulus bounds `‖Z‖ ≤ Σ mu` (`Z_norm_le_muSum`) and
  `‖Z‖ ≤ card (BoundedComplex B)` (`Z_norm_le_card`), and it is invariant
  under any equivalence-preserving bijection of configurations
  (`Z_relabel_invariant`): the measure respects the equivalence.
* The unitary instance `w K = exp(i·S K)` for a real action `S` has
  `‖w K‖ = 1`, so all bounds apply (`zRS_scoped_wellDefined`).  This is the
  honest Z_RS statement for the scoped class.

**MODEL (definitional assumptions, stated, not derived):**
* Scoped class: bounded combinatorial triangulations at a fixed lattice
  scale.  The recognition substrate fixes the edge length at the minimum
  mesh ℓ_sub, so path-sum configurations are combinatorial and equilateral;
  all geometric data is carried by the incidence maps.  This is the standard
  CDT-style measure class.  `BoundedComplex` mirrors the incidence shape of
  `IndisputableMonolith.Geometry.ReggeTriangulation3D.Triangulation3D`
  (fields `nV nE nT`, `edgeVerts : Fin nE → Fin nV × Fin nV`,
  `tetVerts : Fin nT → Fin 4 → Fin nV`), with the metric field dropped
  (equilateral at fixed scale) and the size capped by `B`.
* Measure convention: the LABELED sum with the `1/|Aut|` symmetry factor
  (the standard discrete-gravity convention), not the bare quotient sum.
  `mu_congr` + `Z_relabel_invariant` give compatibility EVIDENCE (measure
  and summand are class functions); the orbit-counting identity equating
  the weighted labeled sum with a quotient sum is not proved here.
* The intended action `S` is the sinh recognition action of
  `PathSumUVBound.recognitionAction` evaluated on the deficit data of the
  complex; here `S` is an arbitrary real action parameter with an explicit
  relabeling-invariance hypothesis where needed.

**OPEN (recorded in `pathSumMeasureStatus`, not claimed):**
* The continuum limit of `Z B` as `B → ∞`.
* A substrate-DERIVED nonuniform measure (beyond the uniform `1/|Aut|`
  convention).

## Proof notes
* No `decide` / `native_decide` anywhere; cardinalities are never computed
  numerically, only bounded.
* All undischarged premises are explicit hypothesis parameters
  (`hw`, `hσ`, `hS`).
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace PathSumMeasure

/-! ## §1. The scoped configuration class -/

/-- A bounded combinatorial triangulation at fixed lattice scale: at most `B`
vertices, edges, and tetrahedra, with abstract incidence data.  MODEL: the
substrate fixes the edge length at the minimum mesh, so configurations are
combinatorial and equilateral (CDT-style); this mirrors the shape of
`Geometry.ReggeTriangulation3D.Triangulation3D` with the metric field
dropped and an explicit size cap. -/
structure BoundedComplex (B : ℕ) where
  nV : ℕ
  nE : ℕ
  nT : ℕ
  hV : nV ≤ B
  hE : nE ≤ B
  hT : nT ≤ B
  edgeVerts : Fin nE → Fin nV × Fin nV
  tetVerts : Fin nT → Fin 4 → Fin nV

/-- The empty complex: a concrete inhabitant of every `BoundedComplex B`. -/
def emptyComplex (B : ℕ) : BoundedComplex B where
  nV := 0
  nE := 0
  nT := 0
  hV := Nat.zero_le B
  hE := Nat.zero_le B
  hT := Nat.zero_le B
  edgeVerts := fun e => e.elim0
  tetVerts := fun t => t.elim0

instance (B : ℕ) : Nonempty (BoundedComplex B) := ⟨emptyComplex B⟩

/-! ## §2. THEOREM: count-finiteness of the scoped class

We exhibit an explicit equivalence with a finite code type (sizes packaged
as `Fin (B+1)`, incidence maps as functions between explicit finite types)
and transfer the `Fintype` instance.  This replaces the ASSUMED `growthBase`
count bound of `PathSumUVBound.AdmissibleTriangulationFamily` with a proved
finite cardinal. -/

/-- Finite code type for `BoundedComplex B`: sizes in `Fin (B+1)`, incidence
data as functions between explicit finite types.  `Fintype` is automatic
from the sigma/pi/prod instances. -/
abbrev CodeType (B : ℕ) : Type :=
  Σ (v : Fin (B + 1)) (e : Fin (B + 1)) (t : Fin (B + 1)),
    (Fin (e : ℕ) → Fin (v : ℕ) × Fin (v : ℕ)) × (Fin (t : ℕ) → Fin 4 → Fin (v : ℕ))

/-- Encode a bounded complex into the finite code type. -/
def toCode {B : ℕ} (K : BoundedComplex B) : CodeType B :=
  ⟨⟨K.nV, Nat.lt_succ_of_le K.hV⟩, ⟨K.nE, Nat.lt_succ_of_le K.hE⟩,
   ⟨K.nT, Nat.lt_succ_of_le K.hT⟩, (K.edgeVerts, K.tetVerts)⟩

/-- Decode: inverse of `toCode`. -/
def ofCode {B : ℕ} (c : CodeType B) : BoundedComplex B where
  nV := c.1
  nE := c.2.1
  nT := c.2.2.1
  hV := Nat.lt_succ_iff.mp c.1.isLt
  hE := Nat.lt_succ_iff.mp c.2.1.isLt
  hT := Nat.lt_succ_iff.mp c.2.2.1.isLt
  edgeVerts := c.2.2.2.1
  tetVerts := c.2.2.2.2

/-- The scoped class is EQUIVALENT to the finite code type (both inverses
are definitional, using structure eta and proof irrelevance). -/
def codeEquiv (B : ℕ) : BoundedComplex B ≃ CodeType B where
  toFun := toCode
  invFun := ofCode
  left_inv _ := rfl
  right_inv _ := rfl

/-- **THEOREM (count-finiteness).**  The scoped class of bounded
combinatorial triangulations is a finite type.  This is the proved
replacement for the assumed `growthBase` field. -/
instance instFintypeBoundedComplex (B : ℕ) : Fintype (BoundedComplex B) :=
  Fintype.ofEquiv (CodeType B) (codeEquiv B).symm

/-- The scoped class has at least one element (the empty complex). -/
theorem boundedComplex_card_pos (B : ℕ) : 0 < Fintype.card (BoundedComplex B) :=
  Fintype.card_pos

/-! ## §3. Relabeling isomorphism: a genuine Setoid -/

/-- A relabeling isomorphism between two bounded complexes: bijections of
the vertex/edge/tet index sets commuting with the incidence maps. -/
structure Relabel {B : ℕ} (K K' : BoundedComplex B) where
  vEquiv : Fin K.nV ≃ Fin K'.nV
  eEquiv : Fin K.nE ≃ Fin K'.nE
  tEquiv : Fin K.nT ≃ Fin K'.nT
  edge_comm : ∀ e : Fin K.nE,
    K'.edgeVerts (eEquiv e) = Prod.map vEquiv vEquiv (K.edgeVerts e)
  tet_comm : ∀ (t : Fin K.nT) (i : Fin 4),
    K'.tetVerts (tEquiv t) i = vEquiv (K.tetVerts t i)

namespace Relabel

variable {B : ℕ}

/-- Identity relabeling. -/
def refl (K : BoundedComplex B) : Relabel K K where
  vEquiv := Equiv.refl _
  eEquiv := Equiv.refl _
  tEquiv := Equiv.refl _
  edge_comm := fun _ => rfl
  tet_comm := fun _ _ => rfl

/-- Inverse relabeling. -/
def symm {K K' : BoundedComplex B} (r : Relabel K K') : Relabel K' K where
  vEquiv := r.vEquiv.symm
  eEquiv := r.eEquiv.symm
  tEquiv := r.tEquiv.symm
  edge_comm := fun e => by
    have h := r.edge_comm (r.eEquiv.symm e)
    rw [Equiv.apply_symm_apply] at h
    rw [h, Prod.map_map, Equiv.symm_comp_self, Prod.map_id, id_eq]
  tet_comm := fun t i => by
    have h := r.tet_comm (r.tEquiv.symm t) i
    rw [Equiv.apply_symm_apply] at h
    rw [h, Equiv.symm_apply_apply]

/-- Composite relabeling. -/
def trans {K₁ K₂ K₃ : BoundedComplex B} (r : Relabel K₁ K₂) (s : Relabel K₂ K₃) :
    Relabel K₁ K₃ where
  vEquiv := r.vEquiv.trans s.vEquiv
  eEquiv := r.eEquiv.trans s.eEquiv
  tEquiv := r.tEquiv.trans s.tEquiv
  edge_comm := fun e => by
    rw [Equiv.trans_apply, s.edge_comm, r.edge_comm, Prod.map_map, Equiv.coe_trans]
  tet_comm := fun t i => by
    rw [Equiv.trans_apply, s.tet_comm, r.tet_comm, Equiv.trans_apply]

@[simp] theorem refl_vEquiv (K : BoundedComplex B) : (refl K).vEquiv = Equiv.refl _ := rfl

@[simp] theorem symm_vEquiv {K K' : BoundedComplex B} (r : Relabel K K') :
    r.symm.vEquiv = r.vEquiv.symm := rfl
@[simp] theorem symm_eEquiv {K K' : BoundedComplex B} (r : Relabel K K') :
    r.symm.eEquiv = r.eEquiv.symm := rfl
@[simp] theorem symm_tEquiv {K K' : BoundedComplex B} (r : Relabel K K') :
    r.symm.tEquiv = r.tEquiv.symm := rfl

@[simp] theorem trans_vEquiv {K₁ K₂ K₃ : BoundedComplex B}
    (r : Relabel K₁ K₂) (s : Relabel K₂ K₃) :
    (r.trans s).vEquiv = r.vEquiv.trans s.vEquiv := rfl
@[simp] theorem trans_eEquiv {K₁ K₂ K₃ : BoundedComplex B}
    (r : Relabel K₁ K₂) (s : Relabel K₂ K₃) :
    (r.trans s).eEquiv = r.eEquiv.trans s.eEquiv := rfl
@[simp] theorem trans_tEquiv {K₁ K₂ K₃ : BoundedComplex B}
    (r : Relabel K₁ K₂) (s : Relabel K₂ K₃) :
    (r.trans s).tEquiv = r.tEquiv.trans s.tEquiv := rfl

/-- Forget the commutation proofs: the underlying triple of index bijections. -/
def toEquivTriple {K K' : BoundedComplex B} (r : Relabel K K') :
    (Fin K.nV ≃ Fin K'.nV) × (Fin K.nE ≃ Fin K'.nE) × (Fin K.nT ≃ Fin K'.nT) :=
  (r.vEquiv, r.eEquiv, r.tEquiv)

/-- A relabeling is determined by its index bijections (the commutation
fields are propositions). -/
theorem toEquivTriple_injective {K K' : BoundedComplex B} :
    Function.Injective (toEquivTriple (K := K) (K' := K')) := by
  rintro ⟨v₁, e₁, t₁, p₁, q₁⟩ ⟨v₂, e₂, t₂, p₂, q₂⟩ h
  simp only [toEquivTriple, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h1
  subst h2
  subst h3
  rfl

/-- Extensionality for relabelings. -/
theorem ext {K K' : BoundedComplex B} {r s : Relabel K K'}
    (hv : r.vEquiv = s.vEquiv) (he : r.eEquiv = s.eEquiv)
    (ht : r.tEquiv = s.tEquiv) : r = s := by
  apply toEquivTriple_injective
  unfold toEquivTriple
  rw [hv, he, ht]

end Relabel

/-- Two bounded complexes are EQUIVALENT iff a relabeling isomorphism
exists between them. -/
def Equivalent {B : ℕ} (K K' : BoundedComplex B) : Prop :=
  Nonempty (Relabel K K')

/-- **THEOREM (genuine equivalence relation).**  Relabeling isomorphism is a
Setoid on the scoped class: refl/symm/trans are proved via the explicit
identity/inverse/composite relabelings above. -/
def relabelSetoid (B : ℕ) : Setoid (BoundedComplex B) where
  r := Equivalent
  iseqv :=
    ⟨fun K => ⟨Relabel.refl K⟩,
     fun h => h.elim fun r => ⟨r.symm⟩,
     fun h₁ h₂ => h₁.elim fun r => h₂.elim fun s => ⟨r.trans s⟩⟩

/-- Combinatorially distinct triangulations: the quotient of the labeled
scoped class by relabeling isomorphism. -/
abbrev TriangulationClass (B : ℕ) := Quotient (relabelSetoid B)

/-- **THEOREM (quotient finiteness).**  The set of combinatorially distinct
bounded triangulations is finite. -/
theorem triangulationClass_finite (B : ℕ) : Finite (TriangulationClass B) :=
  Quotient.finite _

instance (B : ℕ) : Finite (TriangulationClass B) := triangulationClass_finite B

/-- The number of distinct classes is bounded by the labeled count. -/
theorem classCount_le_labeledCount (B : ℕ) :
    Nat.card (TriangulationClass B) ≤ Nat.card (BoundedComplex B) :=
  Nat.card_le_card_of_surjective (Quotient.mk (relabelSetoid B))
    (fun q => Quotient.exists_rep q)

/-- The labeled count agrees with the `Fintype` cardinal. -/
theorem labeledCount_eq_card (B : ℕ) :
    Nat.card (BoundedComplex B) = Fintype.card (BoundedComplex B) :=
  Nat.card_eq_fintype_card

/-! ## §4. The automorphism group and the measure μ -/

/-- The automorphism group of a labeled complex: relabelings of `K` onto
itself. -/
abbrev Aut {B : ℕ} (K : BoundedComplex B) := Relabel K K

instance {B : ℕ} (K : BoundedComplex B) : Nonempty (Aut K) :=
  ⟨Relabel.refl K⟩

/-- **THEOREM.**  The automorphism group is finite (inject into the finite
triple of index permutations). -/
instance instFiniteAut {B : ℕ} (K : BoundedComplex B) : Finite (Aut K) :=
  Finite.of_injective _ (Relabel.toEquivTriple_injective (K := K) (K' := K))

/-- The automorphism count is positive (the identity is an automorphism). -/
theorem autCard_pos {B : ℕ} (K : BoundedComplex B) : 0 < Nat.card (Aut K) :=
  Nat.card_pos

/-- The path-sum measure: the standard `1/|Aut|` symmetry factor of each
labeled configuration.  (MODEL: uniform convention; a substrate-derived
nonuniform measure is OPEN, see `pathSumMeasureStatus`.) -/
noncomputable def mu {B : ℕ} (K : BoundedComplex B) : ℝ :=
  1 / (Nat.card (Aut K) : ℝ)

/-- **THEOREM.**  0 < μ(K). -/
theorem mu_pos {B : ℕ} (K : BoundedComplex B) : 0 < mu K := by
  unfold mu
  have h : (0 : ℝ) < (Nat.card (Aut K) : ℝ) := by
    exact_mod_cast autCard_pos K
  exact div_pos one_pos h

/-- **THEOREM.**  μ(K) ≤ 1 (since |Aut K| ≥ 1). -/
theorem mu_le_one {B : ℕ} (K : BoundedComplex B) : mu K ≤ 1 := by
  unfold mu
  have h : (0 : ℝ) < (Nat.card (Aut K) : ℝ) := by
    exact_mod_cast autCard_pos K
  rw [div_le_one h]
  exact_mod_cast autCard_pos K

/-- Conjugation by a relabeling: automorphism groups of equivalent complexes
are in bijection. -/
def Relabel.autCongr {B : ℕ} {K K' : BoundedComplex B} (r : Relabel K K') :
    Aut K ≃ Aut K' where
  toFun a := (r.symm.trans a).trans r
  invFun b := (r.trans b).trans r.symm
  left_inv a := by
    apply Relabel.ext <;>
      · apply Equiv.ext
        intro x
        simp only [Relabel.trans_vEquiv, Relabel.trans_eEquiv, Relabel.trans_tEquiv,
          Relabel.symm_vEquiv, Relabel.symm_eEquiv, Relabel.symm_tEquiv,
          Equiv.trans_apply, Equiv.symm_apply_apply]
  right_inv b := by
    apply Relabel.ext <;>
      · apply Equiv.ext
        intro x
        simp only [Relabel.trans_vEquiv, Relabel.trans_eEquiv, Relabel.trans_tEquiv,
          Relabel.symm_vEquiv, Relabel.symm_eEquiv, Relabel.symm_tEquiv,
          Equiv.trans_apply, Equiv.apply_symm_apply]

/-- **THEOREM (measure respects the equivalence).**  μ is a relabeling
invariant: equivalent complexes have equal measure. -/
theorem mu_congr {B : ℕ} {K K' : BoundedComplex B} (h : Equivalent K K') :
    mu K = mu K' := by
  obtain ⟨r⟩ := h
  unfold mu
  rw [Nat.card_congr r.autCongr]

/-! ## §5. The path sum Z and its bounds

CONVENTION: `Z` is the sum over the LABELED scoped class with the `1/|Aut|`
symmetry factor (the standard discrete-gravity convention); `mu_congr` and
`Z_relabel_invariant` establish compatibility with the quotient view. -/

/-- The recognition path sum over the scoped class: a finite sum, hence
well-defined with no convergence hypothesis. -/
noncomputable def Z (B : ℕ) (w : BoundedComplex B → ℂ) : ℂ :=
  ∑ K : BoundedComplex B, (mu K : ℂ) * w K

/-- **THEOREM (μ-weighted modulus bound).**  For any weight of modulus at
most 1, `‖Z‖` is bounded by the total measure. -/
theorem Z_norm_le_muSum (B : ℕ) (w : BoundedComplex B → ℂ)
    (hw : ∀ K, ‖w K‖ ≤ 1) :
    ‖Z B w‖ ≤ ∑ K : BoundedComplex B, mu K := by
  unfold Z
  calc ‖∑ K : BoundedComplex B, (mu K : ℂ) * w K‖
      ≤ ∑ K : BoundedComplex B, ‖(mu K : ℂ) * w K‖ := norm_sum_le _ _
    _ ≤ ∑ K : BoundedComplex B, mu K := by
        refine Finset.sum_le_sum fun K _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mu_pos K)]
        exact mul_le_of_le_one_right (le_of_lt (mu_pos K)) (hw K)

/-- **THEOREM (UV-finiteness bound).**  For any weight of modulus at most 1,
`‖Z‖ ≤ card (BoundedComplex B)`: the path sum is finite with an explicit
proved bound, replacing the assumed `growthBase^N` count. -/
theorem Z_norm_le_card (B : ℕ) (w : BoundedComplex B → ℂ)
    (hw : ∀ K, ‖w K‖ ≤ 1) :
    ‖Z B w‖ ≤ (Fintype.card (BoundedComplex B) : ℝ) := by
  unfold Z
  calc ‖∑ K : BoundedComplex B, (mu K : ℂ) * w K‖
      ≤ ∑ K : BoundedComplex B, ‖(mu K : ℂ) * w K‖ := norm_sum_le _ _
    _ ≤ ∑ _K : BoundedComplex B, (1 : ℝ) := by
        refine Finset.sum_le_sum fun K _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mu_pos K)]
        calc mu K * ‖w K‖
            ≤ 1 * 1 := mul_le_mul (mu_le_one K) (hw K) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = (Fintype.card (BoundedComplex B) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **THEOREM (invariance).**  For ANY weight `w` and any bijection `σ` of
configurations that maps each complex to an equivalent one, replacing `w`
by `w ∘ σ` leaves `Z` unchanged: the `1/|Aut|` measure respects the
relabeling equivalence.  (Uses `mu_congr`; no invariance of `w` needed.) -/
theorem Z_relabel_invariant (B : ℕ) (w : BoundedComplex B → ℂ)
    (σ : BoundedComplex B ≃ BoundedComplex B)
    (hσ : ∀ K, Equivalent K (σ K)) :
    Z B (fun K => w (σ K)) = Z B w := by
  unfold Z
  calc ∑ K : BoundedComplex B, (mu K : ℂ) * w (σ K)
      = ∑ K : BoundedComplex B, (mu (σ K) : ℂ) * w (σ K) := by
        refine Finset.sum_congr rfl fun K _ => ?_
        rw [mu_congr (hσ K)]
    _ = ∑ K : BoundedComplex B, (mu K : ℂ) * w K :=
        Fintype.sum_equiv σ _ _ (fun _ => rfl)

/-- **THEOREM (class functions).**  If the weight is relabeling-invariant,
the summand μ·w is constant on equivalence classes, so `Z` descends to the
finite quotient `TriangulationClass B`. -/
theorem summand_class_constant (B : ℕ) (w : BoundedComplex B → ℂ)
    (hinv : ∀ K K', Equivalent K K' → w K = w K')
    {K K' : BoundedComplex B} (h : Equivalent K K') :
    (mu K : ℂ) * w K = (mu K' : ℂ) * w K' := by
  rw [mu_congr h, hinv K K' h]

/-! ## §6. The unitary instance: the honest Z_RS statement -/

/-- The unitary path-sum weight `exp(i·S)` for a real action `S`.  The
intended `S` for Z_RS is the sinh recognition action
(`PathSumUVBound.recognitionAction`) evaluated on the deficit data of the
complex. -/
noncomputable def unitaryWeight {B : ℕ} (S : BoundedComplex B → ℝ) :
    BoundedComplex B → ℂ :=
  fun K => Complex.exp (Complex.I * (S K : ℂ))

/-- **THEOREM.**  The unitary weight has modulus exactly 1. -/
theorem unitaryWeight_norm {B : ℕ} (S : BoundedComplex B → ℝ)
    (K : BoundedComplex B) : ‖unitaryWeight S K‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal (S K)

/-- **THEOREM (Z_RS on the scoped class).**  For an arbitrary real action
`S` with an explicit relabeling-invariance hypothesis `hS`, the unitary
path sum `Z_RS = Σ_K (1/|Aut K|)·exp(i·S K)`:
1. has unit-modulus weights,
2. is relabeling-invariant as a weight,
3. satisfies the proved UV-finiteness bound `‖Z_RS‖ ≤ card`,
4. is unchanged under any equivalence-preserving reindexing of the
   configuration class. -/
theorem zRS_scoped_wellDefined (B : ℕ) (S : BoundedComplex B → ℝ)
    (hS : ∀ K K', Equivalent K K' → S K = S K') :
    (∀ K, ‖unitaryWeight S K‖ = 1) ∧
    (∀ K K', Equivalent K K' → unitaryWeight S K = unitaryWeight S K') ∧
    ‖Z B (unitaryWeight S)‖ ≤ (Fintype.card (BoundedComplex B) : ℝ) ∧
    (∀ σ : BoundedComplex B ≃ BoundedComplex B, (∀ K, Equivalent K (σ K)) →
      Z B (fun K => unitaryWeight S (σ K)) = Z B (unitaryWeight S)) := by
  refine ⟨unitaryWeight_norm S, ?_, ?_, ?_⟩
  · intro K K' h
    unfold unitaryWeight
    rw [hS K K' h]
  · exact Z_norm_le_card B _ (fun K => le_of_eq (unitaryWeight_norm S K))
  · exact fun σ hσ => Z_relabel_invariant B (unitaryWeight S) σ hσ

/-! ## §7. Replacing the assumed growthBase field -/

/-- The admissible family whose count data is now PROVED: `growthBase` is
the actual `Fintype` cardinal of the scoped class (a derived quantity), not
an assumed exponential base.  `minMesh := 1` is the fixed lattice unit of
the scoped class. -/
noncomputable def provedFamily (B : ℕ) : PathSumUVBound.AdmissibleTriangulationFamily where
  maxSimplexCount := B + 1
  maxSimplexCount_pos := Nat.succ_pos B
  growthBase := (Fintype.card (BoundedComplex B) : ℝ)
  growthBase_pos := by exact_mod_cast boundedComplex_card_pos B
  minMesh := 1
  minMesh_pos := one_pos

/-- The growth base of the proved family is the derived cardinal. -/
theorem provedFamily_growthBase_derived (B : ℕ) :
    (provedFamily B).growthBase = (Fintype.card (BoundedComplex B) : ℝ) := rfl

/-- **THEOREM (bridge).**  The proved count is within the structural bound
of `PathSumUVBound.triangulationCountBound` for the proved family: the
assumed-count interface is satisfiable with derived data. -/
theorem proved_count_le_structural_bound (B : ℕ) :
    (Fintype.card (BoundedComplex B) : ℝ) ≤
      PathSumUVBound.triangulationCountBound (provedFamily B) := by
  unfold PathSumUVBound.triangulationCountBound
  show (Fintype.card (BoundedComplex B) : ℝ) ≤
    (Fintype.card (BoundedComplex B) : ℝ) ^ (B + 1)
  have h1 : (1 : ℝ) ≤ (Fintype.card (BoundedComplex B) : ℝ) := by
    exact_mod_cast boundedComplex_card_pos B
  exact le_self_pow₀ h1 (Nat.succ_ne_zero B)

/-! ## §8. Status ledger -/

/-- What is proved and what remains open in this gap.  All flags are
rfl-forced below; no `: True` fields. -/
structure GapStatus where
  count_finite_proved : Bool
  quotient_finite_proved : Bool
  measure_defined : Bool
  measure_positive_proved : Bool
  modulus_bound_proved : Bool
  relabel_invariance_proved : Bool
  continuum_limit_derived : Bool
  substrate_measure_derived : Bool

/-- Status of the path-sum-measure gap after this module. -/
def pathSumMeasureStatus : GapStatus where
  count_finite_proved := true
  quotient_finite_proved := true
  measure_defined := true
  measure_positive_proved := true
  modulus_bound_proved := true
  relabel_invariance_proved := true
  continuum_limit_derived := false
  substrate_measure_derived := false

theorem status_count_finite : pathSumMeasureStatus.count_finite_proved = true := rfl
theorem status_quotient_finite : pathSumMeasureStatus.quotient_finite_proved = true := rfl
theorem status_measure_defined : pathSumMeasureStatus.measure_defined = true := rfl
theorem status_measure_positive : pathSumMeasureStatus.measure_positive_proved = true := rfl
theorem status_modulus_bound : pathSumMeasureStatus.modulus_bound_proved = true := rfl
theorem status_relabel_invariance : pathSumMeasureStatus.relabel_invariance_proved = true := rfl
/-- OPEN: the continuum limit of `Z B` as `B → ∞` is not derived here. -/
theorem status_continuum_open : pathSumMeasureStatus.continuum_limit_derived = false := rfl
/-- OPEN: a substrate-derived nonuniform measure is not derived here. -/
theorem status_substrate_measure_open :
    pathSumMeasureStatus.substrate_measure_derived = false := rfl

end PathSumMeasure
end SevenGaps
end Gravity
end IndisputableMonolith
