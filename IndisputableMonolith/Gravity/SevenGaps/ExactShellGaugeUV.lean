import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.PathSumMeasure
import IndisputableMonolith.Gravity.SevenGaps.SimplicialClass

/-!
# Seven Gaps: exact complexity shells and the Gaussian-UV-regularized path sum

## What this module is (and is NOT)

This module organizes the quotient-class path-sum configuration space into
EXACT complexity shells (no size caps anywhere in the shell definition) and
proves that the shell-resummed path sum with an explicit Gaussian UV
regulator `exp(-ρ·n²)` converges for every regulator strength `ρ > 0`.

**HONESTY DISCLOSURES (binding, per the panel-locked protocol):**
* The regulator `exp(-ρ·n²)` is a MATHEMATICAL regulator inserted by hand;
  it is NOT derived physics.
* The action/phase entering the unitary weight is a PARAMETER (an arbitrary
  function on equivalence classes, equivalently a `GlobalEquivalent`-invariant
  function on labeled complexes, exactly as in
  `PathSumMeasure.zRS_scoped_wellDefined`); no physical action is derived.
* Regulator removal (the `ρ → 0⁺` limit) is a NAMED OPEN
  (`HasZRSRegulatorRemoval`, status flag `false`); it is NEVER claimed.
* NOTHING here is the physical continuum limit: the complexity cutoff is
  not mesh refinement.  `path_sum_continuum_limit` and
  `gap2_continuum_and_measure` stay RED; this module flips NO
  `FullTheoryLedger` flag.

## Status tiers (honest tagging)

**THEOREM (proved below, 0 sorry, 0 new axioms, no `native_decide`):**
* Stage 1 (shell structure): `complexity` is relabeling-invariant
  (`complexity_congr`); the cap-free exact class `ExactComplex v e t` with
  its independent relabeling equivalence `GlobalEquivalent` is a genuine
  setoid (`exactSetoid`); the exact complexity shell `ExactPathClass n` is
  a `Fintype` (`instFintypeExactPathClass`); the shell entropy bound
  `card (ExactPathClass n) ≤ (n+1)^(12·(n+1))` (`exactPathClass_card_le`);
  every shell is inhabited (`exactPathClass_unbounded_support`, witness:
  `n` isolated vertices — NO simpliciality claim).
* Stage 2 (regularized limit): the per-class measure `classMu = 1/|Aut|`
  is well-defined on classes (`exactMu_congr`), positive, and at most 1;
  the regulated shell term satisfies the modulus bound
  (`norm_zRSUVShell_le`); the shell series is summable for every `ρ > 0`
  (`summable_zRSUVShell`); the cutoff partial sums converge to `Z_RS_uv`
  (`zRSUVCutoff_tendsto`); at zero phase the regulated sum is real and
  strictly positive (`Z_RS_uv_zeroPhase_re_pos`) — non-vacuity.

**MODEL (definitional):** the `1/|Aut|` symmetry-factor measure convention
(standard discrete-gravity), the shell coordinate
`complexity = max(nV, max(nE, nT))`, and the Gaussian regulator shape.

**OPEN (named, recorded in `exactShellGaugeUVStatus`, not claimed):**
* `HasZRSRegulatorRemoval`: existence of `lim_{ρ→0⁺} Z_RS_uv ρ phase`.
* The physical continuum limit (complexity cutoff ≠ mesh refinement).

## The cross-cap identification problem (Stage 1 rationale)

The scoped class `PathSumMeasure.BoundedComplex B` carries a size cap `B`,
so the SAME abstract complex appears as an element of `BoundedComplex B`
for every `B` above its complexity — a cap-dependent double-counting
hazard for any sum over caps.  The exact class `ExactComplex v e t` has NO
cap fields: a complex determines its signature `(v, e, t)` and hence
EXACTLY ONE shell index `max v (max e t)` (`shell_index_unique`), and the
cap-relaxation map of the bounded class collapses (`toExact_relax` is a
definitional equality), so no configuration is counted in two shells.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace ExactShellGaugeUV

open PathSumMeasure

/-! ## §1 (S1a). Complexity of a bounded complex is relabeling-invariant -/

/-- The complexity of a bounded complex: the largest of its vertex, edge,
and tetrahedron counts.  This is the shell coordinate. -/
def complexity {B : ℕ} (K : BoundedComplex B) : ℕ :=
  max K.nV (max K.nE K.nT)

/-- A relabeling forces equal vertex counts (`Fin` cardinality through the
vertex bijection). -/
theorem relabel_nV_eq {B : ℕ} {K K' : BoundedComplex B} (r : Relabel K K') :
    K.nV = K'.nV := by
  have h := Fintype.card_congr r.vEquiv
  simp only [Fintype.card_fin] at h
  exact h

/-- A relabeling forces equal edge counts. -/
theorem relabel_nE_eq {B : ℕ} {K K' : BoundedComplex B} (r : Relabel K K') :
    K.nE = K'.nE := by
  have h := Fintype.card_congr r.eEquiv
  simp only [Fintype.card_fin] at h
  exact h

/-- A relabeling forces equal tetrahedron counts. -/
theorem relabel_nT_eq {B : ℕ} {K K' : BoundedComplex B} (r : Relabel K K') :
    K.nT = K'.nT := by
  have h := Fintype.card_congr r.tEquiv
  simp only [Fintype.card_fin] at h
  exact h

/-- **THEOREM (S1a).**  Complexity is a relabeling invariant: equivalent
bounded complexes have equal complexity. -/
theorem complexity_congr {B : ℕ} {K K' : BoundedComplex B}
    (h : Equivalent K K') : complexity K = complexity K' := by
  obtain ⟨r⟩ := h
  unfold complexity
  rw [relabel_nV_eq r, relabel_nE_eq r, relabel_nT_eq r]

/-! ## §2 (S1b). The cap-free exact class and its independent equivalence -/

/-- An EXACT-size combinatorial complex: exactly `v` vertices, `e` edges,
`t` tetrahedra, with abstract incidence data and NO cap inequalities.
This is the cap-free configuration type; the cross-cap identification
problem of `BoundedComplex` cannot arise here because there is no cap. -/
structure ExactComplex (v e t : ℕ) where
  edgeVerts : Fin e → Fin v × Fin v
  tetVerts : Fin t → Fin 4 → Fin v

/-- A relabeling isomorphism between two exact complexes of the same
signature: bijections of the vertex/edge/tet index sets commuting with the
incidence maps.  Defined INDEPENDENTLY of `PathSumMeasure.Relabel` (no
embedding into any capped class). -/
structure ExactRelabel {v e t : ℕ} (K K' : ExactComplex v e t) where
  vEquiv : Fin v ≃ Fin v
  eEquiv : Fin e ≃ Fin e
  tEquiv : Fin t ≃ Fin t
  edge_comm : ∀ i : Fin e,
    K'.edgeVerts (eEquiv i) = Prod.map vEquiv vEquiv (K.edgeVerts i)
  tet_comm : ∀ (i : Fin t) (j : Fin 4),
    K'.tetVerts (tEquiv i) j = vEquiv (K.tetVerts i j)

namespace ExactRelabel

variable {v e t : ℕ}

/-- Identity relabeling. -/
def refl (K : ExactComplex v e t) : ExactRelabel K K where
  vEquiv := Equiv.refl _
  eEquiv := Equiv.refl _
  tEquiv := Equiv.refl _
  edge_comm := fun _ => rfl
  tet_comm := fun _ _ => rfl

/-- Inverse relabeling. -/
def symm {K K' : ExactComplex v e t} (r : ExactRelabel K K') :
    ExactRelabel K' K where
  vEquiv := r.vEquiv.symm
  eEquiv := r.eEquiv.symm
  tEquiv := r.tEquiv.symm
  edge_comm := fun i => by
    have h := r.edge_comm (r.eEquiv.symm i)
    rw [Equiv.apply_symm_apply] at h
    rw [h, Prod.map_map, Equiv.symm_comp_self, Prod.map_id, id_eq]
  tet_comm := fun i j => by
    have h := r.tet_comm (r.tEquiv.symm i) j
    rw [Equiv.apply_symm_apply] at h
    rw [h, Equiv.symm_apply_apply]

/-- Composite relabeling. -/
def trans {K₁ K₂ K₃ : ExactComplex v e t} (r : ExactRelabel K₁ K₂)
    (s : ExactRelabel K₂ K₃) : ExactRelabel K₁ K₃ where
  vEquiv := r.vEquiv.trans s.vEquiv
  eEquiv := r.eEquiv.trans s.eEquiv
  tEquiv := r.tEquiv.trans s.tEquiv
  edge_comm := fun i => by
    rw [Equiv.trans_apply, s.edge_comm, r.edge_comm, Prod.map_map,
      Equiv.coe_trans]
  tet_comm := fun i j => by
    rw [Equiv.trans_apply, s.tet_comm, r.tet_comm, Equiv.trans_apply]

@[simp] theorem trans_vEquiv {K₁ K₂ K₃ : ExactComplex v e t}
    (r : ExactRelabel K₁ K₂) (s : ExactRelabel K₂ K₃) :
    (r.trans s).vEquiv = r.vEquiv.trans s.vEquiv := rfl
@[simp] theorem trans_eEquiv {K₁ K₂ K₃ : ExactComplex v e t}
    (r : ExactRelabel K₁ K₂) (s : ExactRelabel K₂ K₃) :
    (r.trans s).eEquiv = r.eEquiv.trans s.eEquiv := rfl
@[simp] theorem trans_tEquiv {K₁ K₂ K₃ : ExactComplex v e t}
    (r : ExactRelabel K₁ K₂) (s : ExactRelabel K₂ K₃) :
    (r.trans s).tEquiv = r.tEquiv.trans s.tEquiv := rfl
@[simp] theorem symm_vEquiv {K K' : ExactComplex v e t}
    (r : ExactRelabel K K') : r.symm.vEquiv = r.vEquiv.symm := rfl
@[simp] theorem symm_eEquiv {K K' : ExactComplex v e t}
    (r : ExactRelabel K K') : r.symm.eEquiv = r.eEquiv.symm := rfl
@[simp] theorem symm_tEquiv {K K' : ExactComplex v e t}
    (r : ExactRelabel K K') : r.symm.tEquiv = r.tEquiv.symm := rfl

/-- Forget the commutation proofs: the underlying triple of index
bijections. -/
def toEquivTriple {K K' : ExactComplex v e t} (r : ExactRelabel K K') :
    (Fin v ≃ Fin v) × (Fin e ≃ Fin e) × (Fin t ≃ Fin t) :=
  (r.vEquiv, r.eEquiv, r.tEquiv)

/-- A relabeling is determined by its index bijections (the commutation
fields are propositions). -/
theorem toEquivTriple_injective {K K' : ExactComplex v e t} :
    Function.Injective (toEquivTriple (K := K) (K' := K')) := by
  rintro ⟨v₁, e₁, t₁, p₁, q₁⟩ ⟨v₂, e₂, t₂, p₂, q₂⟩ h
  simp only [toEquivTriple, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h1
  subst h2
  subst h3
  rfl

/-- Extensionality for exact relabelings. -/
theorem ext {K K' : ExactComplex v e t} {r s : ExactRelabel K K'}
    (hv : r.vEquiv = s.vEquiv) (he : r.eEquiv = s.eEquiv)
    (ht : r.tEquiv = s.tEquiv) : r = s := by
  apply toEquivTriple_injective
  unfold toEquivTriple
  rw [hv, he, ht]

end ExactRelabel

/-- Two exact complexes of the same signature are GLOBALLY EQUIVALENT iff
an exact relabeling exists between them.  (A relabeling between different
signatures is impossible: `vEquiv : Fin v ≃ Fin v'` forces `v = v'` by
cardinality, so the equivalence lives on each `(v, e, t)` piece.) -/
def GlobalEquivalent {v e t : ℕ} (K K' : ExactComplex v e t) : Prop :=
  Nonempty (ExactRelabel K K')

/-- **THEOREM.**  Global equivalence is a genuine setoid on each exact
signature (refl/symm/trans via the explicit relabelings above). -/
def exactSetoid (v e t : ℕ) : Setoid (ExactComplex v e t) where
  r := GlobalEquivalent
  iseqv :=
    ⟨fun K => ⟨ExactRelabel.refl K⟩,
     fun h => h.elim fun r => ⟨r.symm⟩,
     fun h₁ h₂ => h₁.elim fun r => h₂.elim fun s => ⟨r.trans s⟩⟩

/-! ### Finiteness of the exact labeled class -/

/-- Finite code type for `ExactComplex v e t`: the raw incidence data. -/
def exactCodeEquiv (v e t : ℕ) :
    ExactComplex v e t ≃
      ((Fin e → Fin v × Fin v) × (Fin t → Fin 4 → Fin v)) where
  toFun K := (K.edgeVerts, K.tetVerts)
  invFun c := ⟨c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exact labeled class at any fixed signature is a finite type. -/
instance instFintypeExactComplex (v e t : ℕ) : Fintype (ExactComplex v e t) :=
  Fintype.ofEquiv _ (exactCodeEquiv v e t).symm

/-- The labeled count at signature `(v, e, t)`: `(v·v)^e · (v⁴)^t`
labelings (one vertex pair per edge, one 4-tuple of vertices per tet). -/
theorem exactComplex_card_eq (v e t : ℕ) :
    Fintype.card (ExactComplex v e t) = (v * v) ^ e * (v ^ 4) ^ t := by
  rw [Fintype.card_congr (exactCodeEquiv v e t)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]

/-- **Labeled entropy bound.**  If all three counts are at most `n + 1`,
the labeled count is at most `(n+1)^(6·(n+1))` (documented counting: at
most `((n+1)²)^e` edge labelings times `((n+1)⁴)^t` tet labelings, with
`e, t ≤ n + 1`). -/
theorem exactComplex_card_le (n v e t : ℕ) (hv : v ≤ n + 1)
    (he : e ≤ n + 1) (ht : t ≤ n + 1) :
    Fintype.card (ExactComplex v e t) ≤ (n + 1) ^ (6 * (n + 1)) := by
  rw [exactComplex_card_eq]
  have h1 : (v * v) ^ e ≤ (n + 1) ^ (2 * (n + 1)) := by
    calc (v * v) ^ e
        ≤ ((n + 1) * (n + 1)) ^ e :=
          Nat.pow_le_pow_left (Nat.mul_le_mul hv hv) e
      _ = (n + 1) ^ (2 * e) := by rw [← pow_two, ← pow_mul]
      _ ≤ (n + 1) ^ (2 * (n + 1)) :=
          Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  have h2 : (v ^ 4) ^ t ≤ (n + 1) ^ (4 * (n + 1)) := by
    calc (v ^ 4) ^ t
        ≤ ((n + 1) ^ 4) ^ t :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_left hv 4) t
      _ = (n + 1) ^ (4 * t) := by rw [← pow_mul]
      _ ≤ (n + 1) ^ (4 * (n + 1)) :=
          Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  calc (v * v) ^ e * (v ^ 4) ^ t
      ≤ (n + 1) ^ (2 * (n + 1)) * (n + 1) ^ (4 * (n + 1)) :=
        Nat.mul_le_mul h1 h2
    _ = (n + 1) ^ (6 * (n + 1)) := by
        rw [← pow_add]
        congr 1
        omega

/-! ### The exact complexity shell -/

/-- A shell signature at level `n`: a triple `(v, e, t)` with each count
at most `n` and `max v (max e t) = n`.  Packaged in `Fin (n+1)` so the
signature type is finite. -/
abbrev ShellSig (n : ℕ) : Type :=
  { s : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) //
      max (s.1 : ℕ) (max (s.2.1 : ℕ) (s.2.2 : ℕ)) = n }

/-- Vertex count of a shell signature. -/
abbrev sigV {n : ℕ} (s : ShellSig n) : ℕ := (s.1.1 : ℕ)
/-- Edge count of a shell signature. -/
abbrev sigE {n : ℕ} (s : ShellSig n) : ℕ := (s.1.2.1 : ℕ)
/-- Tetrahedron count of a shell signature. -/
abbrev sigT {n : ℕ} (s : ShellSig n) : ℕ := (s.1.2.2 : ℕ)

/-- The number of shell signatures at level `n` is at most `(n+1)³`. -/
theorem shellSig_card_le (n : ℕ) :
    Fintype.card (ShellSig n) ≤ (n + 1) ^ 3 := by
  have h := Fintype.card_subtype_le
    (fun s : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) =>
      max (s.1 : ℕ) (max (s.2.1 : ℕ) (s.2.2 : ℕ)) = n)
  calc Fintype.card (ShellSig n)
      ≤ Fintype.card (Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) := h
    _ = (n + 1) ^ 3 := by
        simp only [Fintype.card_prod, Fintype.card_fin]
        ring

/-- **THE EXACT COMPLEXITY SHELL (S1b).**  The set of combinatorially
distinct exact complexes of complexity exactly `n`: the disjoint union
over shell signatures of the quotient of the exact labeled class by
global equivalence.  NO cap type (`BoundedComplex B`) appears anywhere in
this definition. -/
abbrev ExactPathClass (n : ℕ) : Type :=
  Σ s : ShellSig n, Quotient (exactSetoid (sigV s) (sigE s) (sigT s))

instance instFiniteExactQuotient (v e t : ℕ) :
    Finite (Quotient (exactSetoid v e t)) :=
  Quotient.finite _

/-- **THEOREM (S1b).**  Each exact complexity shell is a finite type. -/
noncomputable instance instFintypeExactPathClass (n : ℕ) :
    Fintype (ExactPathClass n) :=
  Fintype.ofFinite _

/-! ### No cross-shell double counting -/

/-- The complexity of an exact complex: determined by its signature alone. -/
def exactComplexity {v e t : ℕ} (_ : ExactComplex v e t) : ℕ :=
  max v (max e t)

/-- **THEOREM (no double counting).**  An exact complex can sit in the
shell at level `n` (i.e. its signature can be a `ShellSig n`) ONLY for
`n = exactComplexity K`: each configuration has exactly one shell.
Combined with the fact that `GlobalEquivalent` lives on a fixed signature,
no abstract complex is counted in two shells. -/
theorem shell_index_unique {v e t : ℕ} (K : ExactComplex v e t) {n : ℕ}
    (s : ShellSig n) (hv : sigV s = v) (he : sigE s = e) (ht : sigT s = t) :
    n = exactComplexity K := by
  unfold exactComplexity
  rw [← hv, ← he, ← ht]
  exact s.2.symm

/-- Forget the cap: every bounded complex yields an exact complex with the
same incidence data.  The TARGET TYPE does not mention the cap `B`. -/
def toExact {B : ℕ} (K : BoundedComplex B) : ExactComplex K.nV K.nE K.nT where
  edgeVerts := K.edgeVerts
  tetVerts := K.tetVerts

/-- **THEOREM (cap-dependence collapses).**  Relaxing the cap of a bounded
complex does not change its exact image: the map to the cap-free class
identifies all capped copies of the same configuration (definitional
equality). -/
theorem toExact_relax {B B' : ℕ} (h : B ≤ B') (K : BoundedComplex B) :
    toExact (PathSumMeasure.relax h K) = toExact K := rfl

/-- The exact complexity of the image agrees with the capped complexity. -/
theorem toExact_complexity {B : ℕ} (K : BoundedComplex B) :
    exactComplexity (toExact K) = complexity K := rfl

/-! ## §3 (S1c). The shell entropy bound -/

/-- **THEOREM (shell entropy bound, S1c).**  The number of combinatorially
distinct exact complexes of complexity `n` is at most `(n+1)^(12·(n+1))`.
Counting audit: `≤ (n+1)³` signature choices (`shellSig_card_le`), times
`≤ (n+1)^(6·(n+1))` labeled configurations per signature
(`exactComplex_card_le`, quotient card ≤ labeled card via the surjection
`Quotient.mk`), and `3 + 6·(n+1) ≤ 12·(n+1)`. -/
theorem exactPathClass_card_le (n : ℕ) :
    Nat.card (ExactPathClass n) ≤ (n + 1) ^ (12 * (n + 1)) := by
  have hfiber : ∀ s : ShellSig n,
      Nat.card (Quotient (exactSetoid (sigV s) (sigE s) (sigT s))) ≤
        (n + 1) ^ (6 * (n + 1)) := by
    intro s
    have hsurj : Nat.card (Quotient (exactSetoid (sigV s) (sigE s) (sigT s))) ≤
        Nat.card (ExactComplex (sigV s) (sigE s) (sigT s)) :=
      Nat.card_le_card_of_surjective
        (Quotient.mk (exactSetoid (sigV s) (sigE s) (sigT s)))
        (fun q => Quotient.exists_rep q)
    have hlab : Nat.card (ExactComplex (sigV s) (sigE s) (sigT s)) ≤
        (n + 1) ^ (6 * (n + 1)) := by
      rw [Nat.card_eq_fintype_card]
      exact exactComplex_card_le n _ _ _ (le_of_lt s.1.1.isLt)
        (le_of_lt s.1.2.1.isLt) (le_of_lt s.1.2.2.isLt)
    exact le_trans hsurj hlab
  rw [Nat.card_sigma]
  calc ∑ s : ShellSig n,
        Nat.card (Quotient (exactSetoid (sigV s) (sigE s) (sigT s)))
      ≤ ∑ _s : ShellSig n, (n + 1) ^ (6 * (n + 1)) :=
        Finset.sum_le_sum fun s _ => hfiber s
    _ = Fintype.card (ShellSig n) * (n + 1) ^ (6 * (n + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ (n + 1) ^ 3 * (n + 1) ^ (6 * (n + 1)) :=
        Nat.mul_le_mul_right _ (shellSig_card_le n)
    _ = (n + 1) ^ (3 + 6 * (n + 1)) := by rw [← pow_add]
    _ ≤ (n + 1) ^ (12 * (n + 1)) :=
        Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)

/-! ## §4 (S1d). Every shell is inhabited -/

/-- The `n`-isolated-vertices complex: `n` vertices, no edges, no
tetrahedra.  Complexity exactly `n`.  NO simpliciality claim is made or
needed. -/
def isolatedVertices (n : ℕ) : ExactComplex n 0 0 where
  edgeVerts := fun i => i.elim0
  tetVerts := fun i => i.elim0

/-- The signature `(n, 0, 0)` is a shell signature at level `n`. -/
def isolatedSig (n : ℕ) : ShellSig n :=
  ⟨(⟨n, Nat.lt_succ_self n⟩, ⟨0, Nat.succ_pos n⟩, ⟨0, Nat.succ_pos n⟩), by
    show max n (max 0 0) = n
    rw [max_self, Nat.max_zero]⟩

/-- The class of the `n`-isolated-vertices complex in the shell at level
`n`. -/
def isolatedClass (n : ℕ) : ExactPathClass n :=
  ⟨isolatedSig n, Quotient.mk _ (isolatedVertices n)⟩

instance instNonemptyExactPathClass (n : ℕ) : Nonempty (ExactPathClass n) :=
  ⟨isolatedClass n⟩

/-- **THEOREM (S1d, unbounded support).**  EVERY shell is inhabited: the
`n`-isolated-vertices complex has complexity exactly `n`, so no shell is
eventually empty. -/
theorem exactPathClass_unbounded_support (n : ℕ) :
    0 < Nat.card (ExactPathClass n) :=
  Nat.card_pos

/-! ## §5 (S2a). The per-class measure `1/|Aut|` on exact classes -/

/-- The automorphism group of an exact labeled complex: exact relabelings
of `K` onto itself. -/
abbrev ExactAut {v e t : ℕ} (K : ExactComplex v e t) := ExactRelabel K K

instance {v e t : ℕ} (K : ExactComplex v e t) : Nonempty (ExactAut K) :=
  ⟨ExactRelabel.refl K⟩

/-- The automorphism group is finite (inject into the finite triple of
index permutations). -/
instance instFiniteExactAut {v e t : ℕ} (K : ExactComplex v e t) :
    Finite (ExactAut K) :=
  Finite.of_injective _
    (ExactRelabel.toEquivTriple_injective (K := K) (K' := K))

/-- The automorphism count is positive (the identity is an automorphism). -/
theorem exactAutCard_pos {v e t : ℕ} (K : ExactComplex v e t) :
    0 < Nat.card (ExactAut K) :=
  Nat.card_pos

/-- The symmetry-factor measure of an exact labeled complex:
`μ(K) = 1/|Aut K|` (MODEL: the standard discrete-gravity convention). -/
noncomputable def exactMu {v e t : ℕ} (K : ExactComplex v e t) : ℝ :=
  1 / (Nat.card (ExactAut K) : ℝ)

/-- **THEOREM.**  `0 < μ(K)`. -/
theorem exactMu_pos {v e t : ℕ} (K : ExactComplex v e t) : 0 < exactMu K := by
  unfold exactMu
  have h : (0 : ℝ) < (Nat.card (ExactAut K) : ℝ) := by
    exact_mod_cast exactAutCard_pos K
  exact div_pos one_pos h

/-- **THEOREM.**  `μ(K) ≤ 1` (since `|Aut K| ≥ 1`). -/
theorem exactMu_le_one {v e t : ℕ} (K : ExactComplex v e t) :
    exactMu K ≤ 1 := by
  unfold exactMu
  have h : (0 : ℝ) < (Nat.card (ExactAut K) : ℝ) := by
    exact_mod_cast exactAutCard_pos K
  rw [div_le_one h]
  exact_mod_cast exactAutCard_pos K

/-- Conjugation by an exact relabeling: automorphism groups of globally
equivalent complexes are in bijection (mirrors
`PathSumMeasure.Relabel.autCongr`). -/
def ExactRelabel.autCongr {v e t : ℕ} {K K' : ExactComplex v e t}
    (r : ExactRelabel K K') : ExactAut K ≃ ExactAut K' where
  toFun a := (r.symm.trans a).trans r
  invFun b := (r.trans b).trans r.symm
  left_inv a := by
    apply ExactRelabel.ext <;>
      · apply Equiv.ext
        intro x
        simp only [ExactRelabel.trans_vEquiv, ExactRelabel.trans_eEquiv,
          ExactRelabel.trans_tEquiv, ExactRelabel.symm_vEquiv,
          ExactRelabel.symm_eEquiv, ExactRelabel.symm_tEquiv,
          Equiv.trans_apply, Equiv.symm_apply_apply]
  right_inv b := by
    apply ExactRelabel.ext <;>
      · apply Equiv.ext
        intro x
        simp only [ExactRelabel.trans_vEquiv, ExactRelabel.trans_eEquiv,
          ExactRelabel.trans_tEquiv, ExactRelabel.symm_vEquiv,
          ExactRelabel.symm_eEquiv, ExactRelabel.symm_tEquiv,
          Equiv.trans_apply, Equiv.apply_symm_apply]

/-- **THEOREM (S2a, class invariance).**  `μ` is a global-equivalence
invariant (mirrors `PathSumMeasure.mu_congr`). -/
theorem exactMu_congr {v e t : ℕ} {K K' : ExactComplex v e t}
    (h : GlobalEquivalent K K') : exactMu K = exactMu K' := by
  obtain ⟨r⟩ := h
  unfold exactMu
  rw [Nat.card_congr r.autCongr]

/-- The measure descends to the quotient: the per-class measure. -/
noncomputable def classMuOn (v e t : ℕ) :
    Quotient (exactSetoid v e t) → ℝ :=
  Quotient.lift exactMu (fun _ _ h => exactMu_congr h)

/-- The per-class measure on a shell element. -/
noncomputable def classMu {n : ℕ} (c : ExactPathClass n) : ℝ :=
  classMuOn (sigV c.1) (sigE c.1) (sigT c.1) c.2

/-- **THEOREM.**  `0 < classMu c` for every class. -/
theorem classMu_pos {n : ℕ} (c : ExactPathClass n) : 0 < classMu c := by
  obtain ⟨s, q⟩ := c
  exact Quotient.inductionOn q (fun K => exactMu_pos K)

/-- **THEOREM.**  `classMu c ≤ 1` for every class. -/
theorem classMu_le_one {n : ℕ} (c : ExactPathClass n) : classMu c ≤ 1 := by
  obtain ⟨s, q⟩ := c
  exact Quotient.inductionOn q (fun K => exactMu_le_one K)

/-- A `GlobalEquivalent`-invariant labeled action descends to a class
function: the honest way a phase parameter enters (mirrors the `hS`
hypothesis of `PathSumMeasure.zRS_scoped_wellDefined`).  The phase used
below is an arbitrary function on classes, i.e. exactly such a lift. -/
noncomputable def liftedPhase
    (S : ∀ v e t : ℕ, ExactComplex v e t → ℝ)
    (hS : ∀ (v e t : ℕ) (K K' : ExactComplex v e t),
      GlobalEquivalent K K' → S v e t K = S v e t K') :
    ∀ n : ℕ, ExactPathClass n → ℝ :=
  fun _ c => Quotient.lift (S _ _ _) (fun _ _ h => hS _ _ _ _ _ h) c.2

/-! ## §6 (S2b). The regulated shell term and its modulus bound -/

/-- **The Gaussian-regulated shell term (S2b).**  At shell level `n`, the
per-class-weighted unitary sum with the explicit UV regulator
`exp(-ρ·n²)`.  DISCLOSURE: the regulator is mathematical, not derived
physics; `phase` is a parameter (an arbitrary invariant action on
classes), not derived physics. -/
noncomputable def zRSUVShell (ρ : ℝ) (phase : ∀ n : ℕ, ExactPathClass n → ℝ)
    (n : ℕ) : ℂ :=
  (Real.exp (-ρ * (n : ℝ) ^ 2) : ℝ) *
    ∑ c : ExactPathClass n,
      (classMu c : ℂ) * Complex.exp (Complex.I * (phase n c : ℂ))

/-- **THEOREM (S2b, modulus bound).**  The regulated shell term is bounded
by the regulator times the shell cardinality (`μ ≤ 1`, unit phases). -/
theorem norm_zRSUVShell_le (ρ : ℝ) (phase : ∀ n : ℕ, ExactPathClass n → ℝ)
    (n : ℕ) :
    ‖zRSUVShell ρ phase n‖ ≤
      Real.exp (-ρ * (n : ℝ) ^ 2) * (Nat.card (ExactPathClass n) : ℝ) := by
  unfold zRSUVShell
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  calc ‖∑ c : ExactPathClass n,
          (classMu c : ℂ) * Complex.exp (Complex.I * (phase n c : ℂ))‖
      ≤ ∑ c : ExactPathClass n,
          ‖(classMu c : ℂ) * Complex.exp (Complex.I * (phase n c : ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _c : ExactPathClass n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (classMu_pos c), Complex.norm_exp_I_mul_ofReal, mul_one]
        exact classMu_le_one c
    _ = (Fintype.card (ExactPathClass n) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    _ = (Nat.card (ExactPathClass n) : ℝ) := by
        rw [Nat.card_eq_fintype_card]

/-- **THEOREM (S2b + S1c composed).**  The regulated shell term is bounded
by the regulator times the proved entropy bound. -/
theorem norm_zRSUVShell_le_entropy (ρ : ℝ)
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) (n : ℕ) :
    ‖zRSUVShell ρ phase n‖ ≤
      Real.exp (-ρ * (n : ℝ) ^ 2) * ((n : ℝ) + 1) ^ (12 * (n + 1)) := by
  refine le_trans (norm_zRSUVShell_le ρ phase n) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have h := exactPathClass_card_le n
  have hcast : ((Nat.card (ExactPathClass n) : ℕ) : ℝ) ≤
      (((n + 1) ^ (12 * (n + 1)) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hcast
  exact hcast

/-! ## §7 (S2c). Summability of the regulated shell series -/

/-- Linear domination of the logarithm with arbitrary slope: for `δ > 0`
and `x ≥ 1`, `log x ≤ δ·x + (-1 - log δ)`.  (Apply `log y ≤ y - 1` at
`y = δ·x`.)  This is the sublinearity input that makes `n·log n = o(n²)`
quantitative. -/
theorem log_le_linear {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ δ * x + (-1 - Real.log δ) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have h1 : Real.log (δ * x) ≤ δ * x - 1 :=
    Real.log_le_sub_one_of_pos (mul_pos hδ hx0)
  have h2 : Real.log (δ * x) = Real.log δ + Real.log x :=
    Real.log_mul (ne_of_gt hδ) (ne_of_gt hx0)
  linarith

/-- **Eventual Gaussian domination.**  For every `ρ > 0` there is a
threshold `N` beyond which the entropy exponent `12·(n+1)·log(n+1)` is at
most half the Gaussian exponent `ρ·n²`. -/
theorem exists_gaussian_domination (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      12 * ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) ≤ ρ / 2 * (n : ℝ) ^ 2 := by
  set δ : ℝ := ρ / 192 with hδdef
  have hδ : 0 < δ := by positivity
  set C : ℝ := |(-1 : ℝ) - Real.log δ| with hCdef
  have hC0 : (0 : ℝ) ≤ C := abs_nonneg _
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (96 * C / ρ)
  refine ⟨max 1 N₀, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 N₀) hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnN₀ : 96 * C / ρ ≤ (n : ℝ) := by
    have h : (N₀ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (le_max_right 1 N₀) hn
    linarith
  set x : ℝ := (n : ℝ) + 1 with hxdef
  have hx1 : (1 : ℝ) ≤ x := by simp only [hxdef]; linarith
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hx2n : x ≤ 2 * (n : ℝ) := by simp only [hxdef]; linarith
  have hlx : Real.log x ≤ δ * x + C := by
    have h := log_le_linear hδ hx1
    have habs : (-1 : ℝ) - Real.log δ ≤ C := le_abs_self _
    linarith
  have hmul : 12 * x * Real.log x ≤ 12 * x * (δ * x + C) := by
    apply mul_le_mul_of_nonneg_left hlx
    positivity
  have hring : 12 * x * (δ * x + C) = 12 * δ * x ^ 2 + 12 * C * x := by ring
  have hxsq : x ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ hx0.le hx2n 2
    calc x ^ 2 ≤ (2 * (n : ℝ)) ^ 2 := h
      _ = 4 * (n : ℝ) ^ 2 := by ring
  have h1 : 12 * δ * x ^ 2 ≤ ρ / 4 * (n : ℝ) ^ 2 := by
    have hcoef : 12 * δ = ρ / 16 := by rw [hδdef]; ring
    rw [hcoef]
    calc ρ / 16 * x ^ 2 ≤ ρ / 16 * (4 * (n : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left hxsq
          positivity
      _ = ρ / 4 * (n : ℝ) ^ 2 := by ring
  have h2 : 12 * C * x ≤ ρ / 4 * (n : ℝ) ^ 2 := by
    have ha : 12 * C * x ≤ 24 * C * (n : ℝ) := by
      calc 12 * C * x ≤ 12 * C * (2 * (n : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hx2n
            positivity
        _ = 24 * C * (n : ℝ) := by ring
    have hρn : 96 * C ≤ ρ * (n : ℝ) := by
      have h := (div_le_iff₀ hρ).mp hnN₀
      linarith
    have hb : 24 * C * (n : ℝ) ≤ ρ / 4 * (n : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hρn)
        (le_trans zero_le_one hnR)]
    linarith
  linarith

/-- Convert a natural power of `(n+1)` into an exponential of its
logarithm. -/
theorem pow_eq_exp_log (n k : ℕ) :
    ((n : ℝ) + 1) ^ k = Real.exp ((k : ℝ) * Real.log ((n : ℝ) + 1)) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [← Real.log_pow, Real.exp_log (pow_pos hpos k)]

/-- **THEOREM (S2c, UV summability).**  For every regulator strength
`ρ > 0` and every phase parameter, the regulated shell series is
summable.  Proof: eventual comparison of
`exp(-ρn²)·(n+1)^(12(n+1))` with the geometric series `exp(-ρ/2)^n`,
using `exists_gaussian_domination` (entropy exponent grows like
`n·log n = o(n²)`). -/
theorem summable_zRSUVShell (ρ : ℝ) (hρ : 0 < ρ)
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) :
    Summable (fun n => zRSUVShell ρ phase n) := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-(ρ / 2)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(ρ / 2)) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : Summable (fun n : ℕ => Real.exp (-(ρ / 2)) ^ n) :=
    summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_norm_bounded_eventually_nat hgeo ?_
  obtain ⟨N, hN⟩ := exists_gaussian_domination ρ hρ
  rw [Filter.eventually_atTop]
  refine ⟨max 1 N, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 N) hn
  have hnN : N ≤ n := le_trans (le_max_right 1 N) hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have h3 : Real.exp (-ρ * (n : ℝ) ^ 2) * ((n : ℝ) + 1) ^ (12 * (n + 1)) ≤
      Real.exp (-(ρ / 2) * (n : ℝ) ^ 2) := by
    rw [pow_eq_exp_log n (12 * (n + 1)), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlog := hN n hnN
    have hcast : ((12 * (n + 1) : ℕ) : ℝ) = 12 * ((n : ℝ) + 1) := by
      push_cast
      ring
    rw [hcast]
    linarith
  have h4 : Real.exp (-(ρ / 2) * (n : ℝ) ^ 2) ≤ Real.exp (-(ρ / 2)) ^ n := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [hnR]
    have h := mul_le_mul_of_nonneg_left hsq
      (by positivity : (0 : ℝ) ≤ ρ / 2)
    linarith
  calc ‖zRSUVShell ρ phase n‖
      ≤ Real.exp (-ρ * (n : ℝ) ^ 2) * ((n : ℝ) + 1) ^ (12 * (n + 1)) :=
        norm_zRSUVShell_le_entropy ρ phase n
    _ ≤ Real.exp (-(ρ / 2) * (n : ℝ) ^ 2) := h3
    _ ≤ Real.exp (-(ρ / 2)) ^ n := h4

/-! ## §8 (S2d). The regulated path sum and the cutoff limit -/

/-- **The Gaussian-UV-regularized recognition path sum (S2d).**  The full
shell series at regulator strength `ρ`.  Well-defined as a `tsum`; for
`ρ > 0` the series is summable (`summable_zRSUVShell`), so this is the
genuine limit of the cutoff partial sums (`zRSUVCutoff_tendsto`). -/
noncomputable def Z_RS_uv (ρ : ℝ) (phase : ∀ n : ℕ, ExactPathClass n → ℝ) :
    ℂ :=
  ∑' n : ℕ, zRSUVShell ρ phase n

/-- **THEOREM (S2d, cutoff convergence).**  The complexity-cutoff partial
sums converge to the regulated path sum. -/
theorem zRSUVCutoff_tendsto (ρ : ℝ) (hρ : 0 < ρ)
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) :
    Filter.Tendsto
      (fun M : ℕ => ∑ n ∈ Finset.range M, zRSUVShell ρ phase n)
      Filter.atTop (nhds (Z_RS_uv ρ phase)) :=
  (summable_zRSUVShell ρ hρ phase).hasSum.tendsto_sum_nat

/-! ## §9 (S2e). Non-vacuity at zero phase -/

/-- The zero phase: `S ≡ 0` on every class. -/
def zeroPhase : ∀ n : ℕ, ExactPathClass n → ℝ := fun _ _ => 0

/-- The total measure of a shell: the sum of the per-class measures. -/
noncomputable def shellMass (n : ℕ) : ℝ :=
  ∑ c : ExactPathClass n, classMu c

/-- **THEOREM.**  Every shell carries strictly positive measure (the shell
is inhabited by `isolatedClass n` and each class has `μ > 0`). -/
theorem shellMass_pos (n : ℕ) : 0 < shellMass n :=
  Finset.sum_pos (fun c _ => classMu_pos c) Finset.univ_nonempty

/-- At zero phase the shell term is the real number
`exp(-ρn²) · shellMass n`. -/
theorem zRSUVShell_zeroPhase_eq (ρ : ℝ) (n : ℕ) :
    zRSUVShell ρ zeroPhase n =
      ((Real.exp (-ρ * (n : ℝ) ^ 2) * shellMass n : ℝ) : ℂ) := by
  unfold zRSUVShell zeroPhase shellMass
  rw [Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

/-- **THEOREM.**  At zero phase every shell term has strictly positive
real part (in particular the explicitly constructed inhabited shell
does). -/
theorem zRSUVShell_zeroPhase_re_pos (ρ : ℝ) (n : ℕ) :
    0 < (zRSUVShell ρ zeroPhase n).re := by
  rw [zRSUVShell_zeroPhase_eq, Complex.ofReal_re]
  exact mul_pos (Real.exp_pos _) (shellMass_pos n)

/-- **THEOREM (S2e, non-vacuity).**  At zero phase the regulated path sum
has strictly positive real part for every `ρ > 0`: the regulated theory
is not the zero functional.  (All terms are nonnegative real and the
`n = 0` term is positive; positivity passes to the `tsum`.) -/
theorem Z_RS_uv_zeroPhase_re_pos (ρ : ℝ) (hρ : 0 < ρ) :
    0 < (Z_RS_uv ρ zeroPhase).re := by
  have hsC : Summable
      (fun n : ℕ => ((Real.exp (-ρ * (n : ℝ) ^ 2) * shellMass n : ℝ) : ℂ)) :=
    (summable_zRSUVShell ρ hρ zeroPhase).congr
      (fun n => zRSUVShell_zeroPhase_eq ρ n)
  have hsR : Summable
      (fun n : ℕ => Real.exp (-ρ * (n : ℝ) ^ 2) * shellMass n) :=
    Complex.summable_ofReal.mp hsC
  have hZ : Z_RS_uv ρ zeroPhase =
      ((∑' n : ℕ, Real.exp (-ρ * (n : ℝ) ^ 2) * shellMass n : ℝ) : ℂ) := by
    unfold Z_RS_uv
    rw [tsum_congr (fun n => zRSUVShell_zeroPhase_eq ρ n),
      ← Complex.ofReal_tsum]
  rw [hZ, Complex.ofReal_re]
  exact hsR.tsum_pos
    (fun n => (mul_pos (Real.exp_pos _) (shellMass_pos n)).le) 0
    (mul_pos (Real.exp_pos _) (shellMass_pos 0))

/-! ## §10 (S2f). Regulator removal: the NAMED OPEN -/

/-- **NAMED OPEN (S2f, never claimed).**  Regulator removal for the
Gaussian-UV-regularized path sum: existence of the limit of
`Z_RS_uv ρ phase` as `ρ → 0⁺` (along `nhdsWithin 0 (Ioi 0)`).  This is a
DEFINITION ONLY; no theorem below asserts it, and
`exactShellGaugeUVStatus.regulator_removal_proved = false` records it as
OPEN.  Even if it were proved, it would NOT be the physical continuum
limit (complexity cutoff ≠ mesh refinement). -/
def HasZRSRegulatorRemoval (phase : ∀ n : ℕ, ExactPathClass n → ℝ) : Prop :=
  ∃ L : ℂ, Filter.Tendsto (fun ρ : ℝ => Z_RS_uv ρ phase)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

/-! ## §11 (S2g). Status ledger -/

/-- Status of the exact-shell Gaussian-UV module.  Every `true` flag is
grounded in its kernel theorem by `exactShellGaugeUVStatus_grounded`; the
two `false` flags are the honest OPEN boundary.

`continuum_limit_claimed` is `false` and MUST stay `false` in this
module: the complexity cutoff is NOT mesh refinement, so nothing here
touches the physical continuum limit; `path_sum_continuum_limit` and
`gap2_continuum_and_measure` stay RED and this module flips NO
`FullTheoryLedger` flag. -/
structure ExactShellGaugeUVStatus where
  /-- S1: `complexity_congr`, `exactSetoid`, `instFintypeExactPathClass`,
  `shell_index_unique`, `toExact_relax`. -/
  shell_structure_proved : Bool
  /-- S1c: `exactPathClass_card_le`. -/
  entropy_bound_proved : Bool
  /-- S2c: `summable_zRSUVShell`. -/
  uv_summability_proved : Bool
  /-- S2d: `zRSUVCutoff_tendsto`. -/
  cutoff_limit_proved : Bool
  /-- S2e: `Z_RS_uv_zeroPhase_re_pos`. -/
  nonvacuity_proved : Bool
  /-- S2f: `HasZRSRegulatorRemoval` is a NAMED OPEN definition; MUST stay
  `false` until a kernel proof of the `ρ → 0⁺` limit exists. -/
  regulator_removal_proved : Bool
  /-- The physical continuum limit is NOT claimed (complexity cutoff ≠
  mesh refinement); MUST stay `false` in this module. -/
  continuum_limit_claimed : Bool

/-- The canonical status record. -/
def exactShellGaugeUVStatus : ExactShellGaugeUVStatus where
  shell_structure_proved := true
  entropy_bound_proved := true
  uv_summability_proved := true
  cutoff_limit_proved := true
  nonvacuity_proved := true
  regulator_removal_proved := false
  continuum_limit_claimed := false

/-- **Grounding theorem.**  The status flags are not bare Booleans: each
`true` flag is tied to its kernel theorem, and the two OPEN flags are
recorded `false`. -/
theorem exactShellGaugeUVStatus_grounded :
    (exactShellGaugeUVStatus.shell_structure_proved = true ∧
      ∀ n : ℕ, 0 < Nat.card (ExactPathClass n)) ∧
    (exactShellGaugeUVStatus.entropy_bound_proved = true ∧
      ∀ n : ℕ, Nat.card (ExactPathClass n) ≤ (n + 1) ^ (12 * (n + 1))) ∧
    (exactShellGaugeUVStatus.uv_summability_proved = true ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ phase : ∀ n : ℕ, ExactPathClass n → ℝ,
        Summable (fun n => zRSUVShell ρ phase n)) ∧
    (exactShellGaugeUVStatus.cutoff_limit_proved = true ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ phase : ∀ n : ℕ, ExactPathClass n → ℝ,
        Filter.Tendsto
          (fun M : ℕ => ∑ n ∈ Finset.range M, zRSUVShell ρ phase n)
          Filter.atTop (nhds (Z_RS_uv ρ phase))) ∧
    (exactShellGaugeUVStatus.nonvacuity_proved = true ∧
      ∀ ρ : ℝ, 0 < ρ → 0 < (Z_RS_uv ρ zeroPhase).re) ∧
    exactShellGaugeUVStatus.regulator_removal_proved = false ∧
    exactShellGaugeUVStatus.continuum_limit_claimed = false :=
  ⟨⟨rfl, exactPathClass_unbounded_support⟩,
    ⟨rfl, exactPathClass_card_le⟩,
    ⟨rfl, fun ρ hρ phase => summable_zRSUVShell ρ hρ phase⟩,
    ⟨rfl, fun ρ hρ phase => zRSUVCutoff_tendsto ρ hρ phase⟩,
    ⟨rfl, fun ρ hρ => Z_RS_uv_zeroPhase_re_pos ρ hρ⟩,
    rfl, rfl⟩

end ExactShellGaugeUV
end SevenGaps
end Gravity
end IndisputableMonolith
