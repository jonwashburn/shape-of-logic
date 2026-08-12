import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import IndisputableMonolith.Geometry.CayleyMengerPolynomial
import IndisputableMonolith.Geometry.CayleyMengerMatrix
import IndisputableMonolith.Geometry.DihedralCayleyMenger
import IndisputableMonolith.Geometry.DihedralDerivatives

/-!
# Signed Regge Deficit Angles on a Four-Tetrahedron Hinge Star (THEOREM tier)

This module produces the first kernel-checked signed Regge-convention deficit
angles on an ABSTRACT four-tet star in the repository: an explicit one-parameter
family of hinge configurations whose star-local deficit is strictly positive for
one parameter sign and strictly negative for the other, in the weak-field regime,
with explicit mesh bounds.  "Abstract star" means the object is squared-edge data
for four congruent tetrahedra around a common hinge, certified nondegenerate by
the Cayley-Menger sign (cm3 > 0); it is not an encoded `Triangulation3D` instance
and no coordinate embedding of the closed 4-cycle link is formalized here.

## Configuration (panel-locked design)

Four congruent tetrahedra share an interior hinge edge AB in a closed 4-cycle link.
Each tetrahedron (A, B, P, Q) carries squared edges |AB|^2 = l, |AP|^2 = |BP|^2 =
|AQ|^2 = |BQ|^2 = m, |PQ|^2 = p.  In the repository edge convention (vertex 0 = A,
vertex 1 = B, vertices 2, 3 the equatorial pair) this is the squared-edge vector
(a0, a1, a2, a3, a4, a5) = (l, m, m, m, m, p), and the hinge AB is edge 0.

By congruence all four dihedral angles at AB are equal, with common cosine q given
by the repository's Cayley-Menger cofactor formula `dihedralCos3Sq`.  PROSE
COMMENTARY (offline sympy derivation, NOT kernel-checked in this generality): for
general (l, m, p) the cofactors are C34 = -l(l - 4m + 2p), C33 = C44 = l(l - 4m),
giving

  q(l, m, p) = (l - 4m + 2p) / (l - 4m).

The KERNEL-CHECKED case is the slice l = m = 1 proved in
`fourTet_centralDihedralCosine`: q(p) = (3 - 2p)/3, with sanity anchor
q(1) = 1/3, the regular tetrahedron (`fourTet_regular_sanity`).

At l = m = 1 the flat value is p0 = 3/2 (where q = 0 and theta = pi/2 exactly,
closing the 4-cycle flat).  The deformation family p(h) = (3/2)(1 - h) gives
q = h on the nose, hence

  deficit(h) = 2*pi - 4*arccos(h) = 4*arcsin(h),

so the SIGN of the deficit is certified by the sign of the rational quantity q = h:
no arccos evaluation, no interval arithmetic, no native_decide.

## Main results (all THEOREM tier, kernel checked, zero sorry, zero new axioms)

* `fourTet_centralDihedralCosine`: the hinge dihedral cosine equals (3 - 2p)/3.
* `fourTet_regular_sanity`: q = 1/3 at p = 1 (regular tetrahedron anchor).
* `fourTet_nondegenerate`: cm3 > 0 for |h| < 1 (the Cayley-Menger nondegeneracy
  certificate; a coordinate embedding is not formalized here).
* `fourTet_deficit_eq`: star deficit = 2*pi - 4*arccos(q).
* `fourTet_deficit_sign`: 0 < q implies 0 < deficit; q < 0 implies deficit < 0.
* `fourTet_weak_pair`: the weak-field certificate at q = +h^2 and q = -h^2 with
  mesh bound (all squared edges <= 3), cm3-nondegeneracy, opposite-signed
  deficits, and magnitude bound |deficit| <= 2*pi*h^2.
* `even_ledger_cannot_match_signed_regge`: a standalone algebraic parity fact
  (no even function of the deformation parameter can match the signed deficit
  family on a punctured interval); see its docstring for the disclosure of how
  it relates to the ledger no-go without importing it.

## Convention note (NOT a triangulation bridge)

`ReggeActionConcrete.deficitAngle` is defined as 2*pi minus the sum over incident
tetrahedra of `dihedralAngle3Sq` applied to squared-edge data.  This module's
star-local deficit follows the same 2*pi - sum convention with the same
`DihedralDerivatives.dihedralAngle3Sq` on the same kind of squared-edge data;
`starDeficit_convention_note` records the trivial constant-sum rewrite that makes
this explicit.  It does NOT instantiate `ReggeActionConcrete.deficitAngle` on an
encoded `Triangulation3D` object; that instantiation remains future work.

## Import firewall

Imports are Mathlib plus Geometry modules only.  No ledger, Cost, SevenGaps, or
Gravity module is imported, and no flatness assumption (in particular not
`FlatConfiguration.flat_deficit_zero`) is used anywhere.

## Scope

This is an existence certificate for signed weak-field deficits in Regge classes;
it is not a statement about the N=5 periodic Freudenthal torus.

Two further scoping disclosures.  First, realizability: the formalized
nondegeneracy statement is the Cayley-Menger sign certificate cm3 > 0 for each
tetrahedron; the existence of a coordinate embedding of the tetrahedra (and of
the closed 4-cycle link around the hinge) is standard given cm3 > 0 but is not
formalized in this file.  Second, quantifier domains: several theorems below are
stated over all real parameters because they are true as algebraic identities in
that generality; the geometric reading applies only on the nondegenerate range
(|h| < 1, equivalently 0 < p < 3), as flagged in the individual docstrings.
-/

namespace IndisputableMonolith
namespace Geometry
namespace FourTetSignedDeficit

open CayleyMengerPolynomial CayleyMengerMatrix DihedralCayleyMenger

noncomputable section

/-! ## The four-tet star squared-edge data -/

/-- Squared-edge data of one tetrahedron of the four-tet star with hinge
squared length 1, spoke squared lengths 1, and rim squared length `p`:
(a0, a1, a2, a3, a4, a5) = (1, 1, 1, 1, 1, p).  The hinge AB is edge 0. -/
def starSq (p : ℝ) : SqEdges :=
  fun e =>
    match e with
    | ⟨0, _⟩ => 1
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 1
    | ⟨3, _⟩ => 1
    | ⟨4, _⟩ => 1
    | ⟨5, _⟩ => p
    | ⟨n + 6, h⟩ => absurd h (by omega)

/-- The rim squared length along the deformation family: p(h) = (3/2)(1 - h).
The flat value is p(0) = 3/2, where the hinge dihedral cosine vanishes. -/
def starP (h : ℝ) : ℝ := 3 / 2 * (1 - h)

/-- THEOREM: the Cayley-Menger polynomial of the star tetrahedron is
2p(3 - p), strictly positive exactly on the open rim range 0 < p < 3.
Scoping note: this is a polynomial identity, stated (and true) for all real p;
the geometric reading applies only where cm3 > 0. -/
theorem star_cm3 (p : ℝ) : cm3 (starSq p) = 2 * p * (3 - p) := by
  have h0 : starSq p 0 = 1 := rfl
  have h1 : starSq p 1 = 1 := rfl
  have h2 : starSq p 2 = 1 := rfl
  have h3 : starSq p 3 = 1 := rfl
  have h4 : starSq p 4 = 1 := rfl
  have h5 : starSq p 5 = p := rfl
  unfold cm3
  rw [h0, h1, h2, h3, h4, h5]
  ring

/-- THEOREM (nondegeneracy certificate): for |h| < 1 the star tetrahedron has
strictly positive Cayley-Menger polynomial, cm3 > 0.  This is the standard
determinantal certificate for realizability as a Euclidean tetrahedron; the
coordinate embedding itself is not formalized in this file. -/
theorem fourTet_nondegenerate (h : ℝ) (hh : |h| < 1) :
    0 < cm3 (starSq (starP h)) := by
  have hb := abs_lt.mp hh
  rw [star_cm3]
  have hp : 0 < starP h := by unfold starP; nlinarith [hb.2]
  have hq : starP h < 3 := by unfold starP; nlinarith [hb.1]
  nlinarith

/-! ## Cayley-Menger cofactors of the star tetrahedron at the hinge

The hinge AB is edge 0; `oppositeCMVertices 0 = (3, 4)`.  The three cofactors
needed by `dihedralCos3Sq` are computed explicitly, mirroring the normal-form
minor technique of `CayleyMengerMatrix`. -/

/-- Normal form of the (3,4) Cayley-Menger minor of the star tetrahedron. -/
def starMinor34Matrix (p : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, 1, 1;
     1, 1, 0, 1;
     1, 1, 1, p]

theorem det_starMinor34 (p : ℝ) :
    Matrix.det (starMinor34Matrix p) = 2 * p - 3 := by
  unfold starMinor34Matrix
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

theorem star_minor_34_eq (p : ℝ) :
    Matrix.submatrix (cmMatrix3 (starSq p)) (Fin.succAbove (3 : Fin 5))
      (Fin.succAbove (4 : Fin 5)) = starMinor34Matrix p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [starMinor34Matrix, cmMatrix3, starSq, Fin.succAbove]

/-- THEOREM: the off-diagonal hinge cofactor C34 of the star tetrahedron. -/
theorem star_cofactor_34 (p : ℝ) :
    cmCofactor3 (starSq p) 3 4 = 3 - 2 * p := by
  unfold cmCofactor3 cmCofactorSign3 cmMinor3
  simp [show ¬ Even (7 : Nat) by norm_num]
  rw [star_minor_34_eq, det_starMinor34]
  ring

theorem star_minor_33_eq (p : ℝ) :
    Matrix.submatrix (cmMatrix3 (starSq p)) (Fin.succAbove (3 : Fin 5))
      (Fin.succAbove (3 : Fin 5)) = regularUnitDiagMinorMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [regularUnitDiagMinorMatrix, cmMatrix3, starSq, Fin.succAbove]

/-- THEOREM: the diagonal cofactor C33 of the star tetrahedron. -/
theorem star_cofactor_33 (p : ℝ) :
    cmCofactor3 (starSq p) 3 3 = -3 := by
  unfold cmCofactor3 cmCofactorSign3 cmMinor3
  simp [show Even (6 : Nat) by norm_num]
  rw [star_minor_33_eq, det_regularUnitDiagMinorMatrix]

theorem star_minor_44_eq (p : ℝ) :
    Matrix.submatrix (cmMatrix3 (starSq p)) (Fin.succAbove (4 : Fin 5))
      (Fin.succAbove (4 : Fin 5)) = regularUnitDiagMinorMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [regularUnitDiagMinorMatrix, cmMatrix3, starSq, Fin.succAbove]

/-- THEOREM: the diagonal cofactor C44 of the star tetrahedron. -/
theorem star_cofactor_44 (p : ℝ) :
    cmCofactor3 (starSq p) 4 4 = -3 := by
  unfold cmCofactor3 cmCofactorSign3 cmMinor3
  simp [show Even (8 : Nat) by norm_num]
  rw [star_minor_44_eq, det_regularUnitDiagMinorMatrix]

/-- THEOREM: the cofactor denominator at the hinge is the constant 3. -/
theorem star_denom (p : ℝ) : dihedralDenom3 (starSq p) 0 = 3 := by
  unfold dihedralDenom3
  simp only [oppositeCMVertices]
  rw [star_cofactor_33, star_cofactor_44]
  rw [show ((-3 : ℝ) * (-3 : ℝ)) = (3 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-! ## The rational hinge dihedral cosine -/

/-- THEOREM (the rational certificate): the dihedral cosine at the hinge AB,
computed by the repository's Cayley-Menger cofactor formula `dihedralCos3Sq`,
equals the explicit rational function (3 - 2p)/3 of the rim squared length.
This is the kernel-checked l = m = 1 slice of the prose-only general formula
q(l, m, p) in the module header.  Scoping note: stated for all real p as an
identity of the cofactor formula; the dihedral-angle reading applies on the
nondegenerate range 0 < p < 3. -/
theorem fourTet_centralDihedralCosine (p : ℝ) :
    dihedralCos3Sq (starSq p) 0 = (3 - 2 * p) / 3 := by
  unfold dihedralCos3Sq
  simp only [oppositeCMVertices]
  rw [star_cofactor_34, star_denom]

/-- THEOREM (sanity anchor): at p = 1 the star tetrahedron is regular and the
hinge dihedral cosine is 1/3, matching `dihedralCos3_regularUnit`. -/
theorem fourTet_regular_sanity : dihedralCos3Sq (starSq 1) 0 = 1 / 3 := by
  rw [fourTet_centralDihedralCosine]
  norm_num

/-- THEOREM: along the deformation family p(h) = (3/2)(1 - h) the hinge
dihedral cosine equals the deformation parameter h exactly.  Scoping note:
stated for all real h as an identity; a cosine reading requires |h| <= 1 and
the nondegenerate geometric range is |h| < 1. -/
theorem star_q (h : ℝ) : dihedralCos3Sq (starSq (starP h)) 0 = h := by
  rw [fourTet_centralDihedralCosine]
  unfold starP
  ring

/-! ## The star-local deficit -/

/-- Star-local Regge deficit at the hinge AB: 2*pi minus the sum of the four
equal dihedral angles of the congruent incident tetrahedra, each computed by
the repository's `DihedralDerivatives.dihedralAngle3Sq` on the star data. -/
def starDeficit (h : ℝ) : ℝ :=
  2 * Real.pi - 4 * DihedralDerivatives.dihedralAngle3Sq (starSq (starP h)) 0

/-- Convention note (a trivial constant-sum rewrite, NOT a triangulation
bridge): this records that the standalone `starDeficit` follows the same
2*pi - sum-over-incident-tetrahedra convention, with the same
`DihedralDerivatives.dihedralAngle3Sq`, as `ReggeActionConcrete.deficitAngle`.
It does NOT instantiate `ReggeActionConcrete.deficitAngle` on an encoded
`Triangulation3D` object; that instantiation remains future work. -/
theorem starDeficit_convention_note (h : ℝ) :
    starDeficit h =
      2 * Real.pi -
        ∑ _τ : Fin 4, DihedralDerivatives.dihedralAngle3Sq (starSq (starP h)) 0 := by
  unfold starDeficit
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- THEOREM: the star deficit equals 2*pi - 4*arccos(q) with q = h the
rational hinge cosine. -/
theorem fourTet_deficit_eq (h : ℝ) :
    starDeficit h = 2 * Real.pi - 4 * Real.arccos h := by
  unfold starDeficit DihedralDerivatives.dihedralAngle3Sq
  rw [star_q]

/-- THEOREM: closed arcsin form of the star deficit. -/
theorem starDeficit_eq_arcsin (h : ℝ) :
    starDeficit h = 4 * Real.arcsin h := by
  rw [fourTet_deficit_eq, Real.arccos_eq_pi_div_two_sub_arcsin]
  ring

/-- THEOREM: the deficit vanishes at the flat value h = 0 (p = 3/2). -/
theorem starDeficit_flat : starDeficit 0 = 0 := by
  rw [starDeficit_eq_arcsin, Real.arcsin_zero]
  ring

/-- THEOREM: the star deficit is an odd function of the deformation
parameter, deficit(-h) = -deficit(h). -/
theorem starDeficit_odd (h : ℝ) : starDeficit (-h) = -starDeficit h := by
  rw [starDeficit_eq_arcsin, starDeficit_eq_arcsin, Real.arcsin_neg]
  ring

/-- THEOREM (the signed-deficit contact certificate): the sign of the star
deficit is the sign of the rational hinge cosine q = h.  A strictly positive
q gives a strictly positive deficit, a strictly negative q gives a strictly
negative deficit.  Scoping note: stated for all real h (arcsin is constant
beyond [-1, 1], so the statement stays true); the geometric reading applies
on the nondegenerate range |h| < 1. -/
theorem fourTet_deficit_sign (h : ℝ) :
    (0 < h → 0 < starDeficit h) ∧ (h < 0 → starDeficit h < 0) := by
  constructor
  · intro hp
    rw [starDeficit_eq_arcsin]
    have := Real.arcsin_pos.mpr hp
    linarith
  · intro hn
    rw [starDeficit_eq_arcsin]
    have := Real.arcsin_lt_zero.mpr hn
    linarith

/-! ## Weak-field magnitude bounds -/

/-- Chord bound for arcsin on the nonnegative unit interval:
arcsin(x) <= (pi/2) * x. -/
private theorem arcsin_le_pi_div_two_mul (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.arcsin x ≤ Real.pi / 2 * x := by
  have hy0 : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.mpr h0
  have hy1 : Real.arcsin x ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two x
  have hsin : Real.sin (Real.arcsin x) = x := Real.sin_arcsin (by linarith) h1
  have hkey : 2 / Real.pi * Real.arcsin x ≤ Real.sin (Real.arcsin x) :=
    Real.mul_le_sin hy0 hy1
  rw [hsin] at hkey
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hexp : Real.pi / 2 * (2 / Real.pi * Real.arcsin x) = Real.arcsin x := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hkey
    (by positivity : (0 : ℝ) ≤ Real.pi / 2)
  rw [hexp] at hmul
  exact hmul

/-- Absolute chord bound for arcsin on the closed unit interval. -/
private theorem abs_arcsin_le_abs (x : ℝ) (hx : |x| ≤ 1) :
    |Real.arcsin x| ≤ Real.pi / 2 * |x| := by
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0, abs_of_nonneg (Real.arcsin_nonneg.mpr hx0)]
    exact arcsin_le_pi_div_two_mul x hx0 (by rwa [abs_of_nonneg hx0] at hx)
  · have hx1 : -x ≤ 1 := by
      rw [abs_of_neg hx0] at hx
      linarith
    rw [abs_of_neg hx0, abs_of_neg (Real.arcsin_lt_zero.mpr hx0)]
    rw [← Real.arcsin_neg]
    exact arcsin_le_pi_div_two_mul (-x) (by linarith) hx1

/-- THEOREM (weak-field magnitude): |deficit(h)| <= 2*pi*|h| for |h| <= 1. -/
theorem starDeficit_abs_le (h : ℝ) (hh : |h| ≤ 1) :
    |starDeficit h| ≤ 2 * Real.pi * |h| := by
  rw [starDeficit_eq_arcsin, abs_mul]
  have hbound := abs_arcsin_le_abs h hh
  rw [show |(4 : ℝ)| = 4 by norm_num]
  linarith

/-- THEOREM (mesh bound): every squared edge of the star tetrahedron is at
most 3 for |h| <= 1. -/
theorem star_mesh_bound (h : ℝ) (hh : |h| ≤ 1) (e : Fin 6) :
    starSq (starP h) e ≤ 3 := by
  have hb := abs_le.mp hh
  have hp : starP h ≤ 3 := by unfold starP; nlinarith [hb.1]
  fin_cases e
  · show (1 : ℝ) ≤ 3; norm_num
  · show (1 : ℝ) ≤ 3; norm_num
  · show (1 : ℝ) ≤ 3; norm_num
  · show (1 : ℝ) ≤ 3; norm_num
  · show (1 : ℝ) ≤ 3; norm_num
  · exact hp

/-! ## The weak-field pair certificate -/

/-- THEOREM (the weak-field signed pair, Test B certificate): for every
0 < h < 1 the pair of configurations at rim parameters p0 - (3/2)h^2 and
p0 + (3/2)h^2 (that is, deformation parameters +h^2 and -h^2, with
p0 = 3/2 the flat value) satisfies:

1. explicit rational hinge cosines q = +h^2 and q = -h^2;
2. strictly positive deficit on the first, strictly negative on the second;
3. exact antisymmetry, deficit(-h^2) = -deficit(+h^2);
4. mesh bound: all squared edges of both configurations are at most 3;
5. nondegeneracy certificate: cm3 > 0 for both configurations (the
   Cayley-Menger sign; a coordinate embedding is not formalized here);
6. weak-field magnitude bound |deficit| <= 2*pi*h^2 on both sides. -/
theorem fourTet_weak_pair (h : ℝ) (h0 : 0 < h) (h1 : h < 1) :
    dihedralCos3Sq (starSq (starP (h ^ 2))) 0 = h ^ 2 ∧
    dihedralCos3Sq (starSq (starP (-h ^ 2))) 0 = -h ^ 2 ∧
    0 < starDeficit (h ^ 2) ∧
    starDeficit (-h ^ 2) < 0 ∧
    starDeficit (-h ^ 2) = -starDeficit (h ^ 2) ∧
    (∀ e : Fin 6, starSq (starP (h ^ 2)) e ≤ 3 ∧ starSq (starP (-h ^ 2)) e ≤ 3) ∧
    0 < cm3 (starSq (starP (h ^ 2))) ∧
    0 < cm3 (starSq (starP (-h ^ 2))) ∧
    |starDeficit (h ^ 2)| ≤ 2 * Real.pi * h ^ 2 ∧
    |starDeficit (-h ^ 2)| ≤ 2 * Real.pi * h ^ 2 := by
  have hsq_pos : 0 < h ^ 2 := by positivity
  have hsq_lt : h ^ 2 < 1 := by nlinarith
  have habs_pos : |h ^ 2| ≤ 1 := by
    rw [abs_of_pos hsq_pos]; linarith
  have habs_neg : |-h ^ 2| ≤ 1 := by
    rw [abs_neg, abs_of_pos hsq_pos]; linarith
  have habs_pos' : |h ^ 2| < 1 := by
    rw [abs_of_pos hsq_pos]; exact hsq_lt
  have habs_neg' : |-h ^ 2| < 1 := by
    rw [abs_neg, abs_of_pos hsq_pos]; exact hsq_lt
  refine ⟨star_q (h ^ 2), star_q (-h ^ 2), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (fourTet_deficit_sign (h ^ 2)).1 hsq_pos
  · exact (fourTet_deficit_sign (-h ^ 2)).2 (neg_lt_zero.mpr hsq_pos)
  · exact starDeficit_odd (h ^ 2)
  · intro e
    exact ⟨star_mesh_bound (h ^ 2) habs_pos e, star_mesh_bound (-h ^ 2) habs_neg e⟩
  · exact fourTet_nondegenerate (h ^ 2) habs_pos'
  · exact fourTet_nondegenerate (-h ^ 2) habs_neg'
  · have := starDeficit_abs_le (h ^ 2) habs_pos
    rwa [abs_of_pos hsq_pos] at this
  · have := starDeficit_abs_le (-h ^ 2) habs_neg
    rwa [abs_neg, abs_of_pos hsq_pos] at this

/-! ## The even-ledger obstruction corollary -/

/-- THEOREM (standalone algebraic parity fact): no function that is EVEN in
the deformation parameter can equal a signed deficit family on a punctured
interval around the flat point.  Pure algebra; no geometric or ledger content
is used in the statement or proof.

Disclosure of the intended composition: the seven-gaps campaign's parity no-go
(`LedgerBridgeNoGo`) shows ledger J-deficits are even in the deformation
parameter.  Composing that result with this lemma would give "no ledger
J-deficit matches the signed star deficit family", but that composition is NOT
performed in Lean here: the import firewall of this lane forbids ledger
imports, deliberately, so the composition lives at the campaign level.  This
lemma is consistent with, but independent of, `LedgerBridgeNoGo`. -/
theorem even_ledger_cannot_match_signed_regge
    {δ g : ℝ → ℝ} {h₀ : ℝ} (hpos : 0 < h₀)
    (hsign : ∀ h : ℝ, 0 < h → h < h₀ → 0 < δ h ∧ δ (-h) < 0)
    (heven : ∀ h : ℝ, g (-h) = g h) :
    ¬ (∀ h : ℝ, 0 < |h| → |h| < h₀ → g h = δ h) := by
  intro hmatch
  have hh : 0 < h₀ / 2 := half_pos hpos
  have hlt : h₀ / 2 < h₀ := half_lt_self hpos
  obtain ⟨hδp, hδn⟩ := hsign (h₀ / 2) hh hlt
  have habs : |h₀ / 2| = h₀ / 2 := abs_of_pos hh
  have h1 : g (h₀ / 2) = δ (h₀ / 2) :=
    hmatch _ (by rw [habs]; exact hh) (by rw [habs]; exact hlt)
  have habs2 : |-(h₀ / 2)| = h₀ / 2 := by rw [abs_neg, habs]
  have h2 : g (-(h₀ / 2)) = δ (-(h₀ / 2)) :=
    hmatch _ (by rw [habs2]; exact hh) (by rw [habs2]; exact hlt)
  rw [heven] at h2
  linarith

/-- THEOREM: instantiation on the explicit star deficit family with h₀ = 1. -/
theorem even_cannot_match_starDeficit
    (g : ℝ → ℝ) (heven : ∀ h : ℝ, g (-h) = g h) :
    ¬ (∀ h : ℝ, 0 < |h| → |h| < 1 → g h = starDeficit h) :=
  even_ledger_cannot_match_signed_regge one_pos
    (fun h hp _ =>
      ⟨(fourTet_deficit_sign h).1 hp,
       (fourTet_deficit_sign (-h)).2 (neg_lt_zero.mpr hp)⟩)
    heven

/-! ## Status flags -/

/-- Status record for the signed-deficit contact certificate lane. -/
structure FourTetSignedDeficitStatus where
  signed_deficit_kernel_checked : Bool
  weak_field_pair_constructed : Bool
  firewall_no_ledger_imports : Bool
  n5_torus_extension_open : Bool

/-- The status of this module.  The N=5 periodic Freudenthal torus extension
is CLOSED by the Analysis lift
`FreudenthalN5TorusSignedDeficitLift.n5FaceDiagHingeDeficit_eq_faceDiagStarDeficit`
(field name retained; value flipped). -/
def status : FourTetSignedDeficitStatus where
  signed_deficit_kernel_checked := true
  weak_field_pair_constructed := true
  firewall_no_ledger_imports := true
  n5_torus_extension_open := false

theorem status_signed_deficit_kernel_checked :
    status.signed_deficit_kernel_checked = true := rfl

theorem status_weak_field_pair_constructed :
    status.weak_field_pair_constructed = true := rfl

theorem status_firewall_no_ledger_imports :
    status.firewall_no_ledger_imports = true := rfl

/-- Closed counterpart of the former openness rfl-anchor. -/
theorem status_n5_torus_extension_closed :
    status.n5_torus_extension_open = false := rfl

end

end FourTetSignedDeficit
end Geometry
end IndisputableMonolith
