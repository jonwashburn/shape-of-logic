import IndisputableMonolith.Gravity.Analysis.ReggeTTHingeAwareZeroMode
import IndisputableMonolith.Gravity.Analysis.BlochCellSum

/-!
# Regge TT finite Bloch assembly

This module is the C-DAG1 finite-cell assembly stage.  The cosine evaluator
is defined directly from a bucket's integer phase key, independently of any
quadratic moment evaluator.

For every side length and commensurate integer wave vector whose doubled
frequency is non-aliased in one coordinate, the normalized canonical finite
value equals the raw bucket-fiber Bloch fold exactly.  The proof uses
`BlochCellSum.cellSum_cos_mul_cos`; periodic wrapping in `localEdgeOf` is
handled by an explicit integer-turn phase decomposition and cosine
periodicity.

No spike or continuum-certificate module is imported.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTBlochAssembly

open Geometry.PeriodicFreudenthalTorus
open ReggeTTSymbolPreflight
open ReggeTTBlochInterfaceAudit
open ReggeTTHingeAwareZeroMode (slotDispClass slotDispClass_grounded)

noncomputable section

/-! ## Cell-relative phases and periodic wrapping -/

/-- A coordinate of a periodic vertex as a natural representative. -/
def vertexNatCoord {N : ℕ} (x : Vertex N N N) : Fin 3 → ℕ
  | 0 => x.1.val
  | 1 => x.2.1.val
  | 2 => x.2.2.val

/-- The selected Boolean coordinate of a cube vertex label. -/
def cubeVertexBit (a : Fin 8) : Fin 3 → Bool
  | 0 => (vertexBits a).1
  | 1 => (vertexBits a).2.1
  | 2 => (vertexBits a).2.2

/-- The base-vertex bit of local slot `f` in tetrahedron type `t`. -/
def slotBaseBit (t f : Fin 6) (i : Fin 3) : Bool :=
  cubeVertexBit
    (cubeEdgeBase (Geometry.FreudenthalCubeTriangulation.localEdgeOf t f)) i

/-- The selected Boolean coordinate of a positive cube displacement. -/
def cubeDispBit (d : Fin 7) : Fin 3 → Bool
  | 0 => (dispBits d).1
  | 1 => (dispBits d).2.1
  | 2 => (dispBits d).2.2

/-- The displacement bit of local slot `f` in tetrahedron type `t`. -/
def slotDispBit (t f : Fin 6) (i : Fin 3) : Bool :=
  cubeDispBit
    (cubeEdgeDisp (Geometry.FreudenthalCubeTriangulation.localEdgeOf t f)) i

/-- Geometry-derived doubled midpoint coordinate of a local edge slot:
twice its base offset plus its positive displacement bit. -/
def slotMidTwice (t f : Fin 6) (i : Fin 3) : ℤ :=
  2 * (bit (slotBaseBit t f i) : ℤ) + (bit (slotDispBit t f i) : ℤ)

/-- Number of periodic wraps made by the base-vertex translation in one
coordinate.  Since the translation bit is zero or one this is zero or one,
but the quotient form gives the exact modular identity without cases. -/
def slotWrapCount (N : ℕ) (cell : Vertex N N N) (t f : Fin 6)
    (i : Fin 3) : ℕ :=
  (vertexNatCoord cell i + bit (slotBaseBit t f i)) / N

/-- Total integer number of phase turns removed by periodic wrapping. -/
def slotWrapTurns (N : ℕ) (m : Fin 3 → ℤ) (cell : Vertex N N N)
    (t f : Fin 6) : ℤ :=
  ∑ i : Fin 3, m i * (slotWrapCount N cell t f i : ℤ)

/-- The cell-independent midpoint phase of one local edge slot. -/
def slotPhase (N : ℕ) [NeZero N] (m : Fin 3 → ℤ) (t f : Fin 6) : ℝ :=
  ∑ i : Fin 3,
    commensurateMomentum N m i * (((slotMidTwice t f i : ℤ) : ℝ) / 2)

/-- Cosine phase evaluator on a raw bucket.  This definition is direct from
the integer phase key and does not mention `rawPhaseQuadratic`. -/
def rawCosineEvaluator (N : ℕ) [NeZero N] (m : Fin 3 → ℤ)
    (b : Bucket) : ℝ :=
  Real.cos
    (∑ i : Fin 3,
      commensurateMomentum N m i * (((b.phase i : ℤ) : ℝ) / 2))

/-- Bucket key of one raw stencil triple.  Its phase is the doubled
midpoint displacement from the left slot to the right slot. -/
def bucketKeyOf (p : Fin 6 × Fin 6 × Fin 6) : Bucket :=
  ⟨p.2.1, p.2.2,
    fun i => slotMidTwice p.1 p.2.2 i - slotMidTwice p.1 p.2.1 i⟩

/-- Finite support of the raw cosine fold, obtained as the image of all
216 tetrahedron/slot triples under the geometry-derived bucket key. -/
def rawCosineSupport : Finset Bucket :=
  Finset.univ.image bucketKeyOf

/-- Signed cell-independent coefficient of one raw stencil triple. -/
def rawTripleWeight (E : Fin 3 → Fin 3 → ℝ)
    (p : Fin 6 × Fin 6 × Fin 6) : ℝ :=
  -(rawJacobianCoefficient p.2.1 p.2.2 *
    polEdgeCoeff E (slotDispClass p.1 p.2.1) *
    polEdgeCoeff E (slotDispClass p.1 p.2.2))

/-- Honest bucket-fiber aggregation of the signed raw stencil weights. -/
def rawBucketAmplitude (E : Fin 3 → Fin 3 → ℝ) (b : Bucket) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => bucketKeyOf p = b),
    rawTripleWeight E p

private theorem addBit_val_real (N : ℕ) [NeZero N] (x : Fin N) (b : Bool) :
    ((addBit x b).val : ℝ) =
      (x.val : ℝ) + (bit b : ℝ) -
        (N : ℝ) * (((x.val + bit b) / N : ℕ) : ℝ) := by
  have hnat :
      (x.val + bit b) % N + N * ((x.val + bit b) / N) =
        x.val + bit b :=
    Nat.mod_add_div (x.val + bit b) N
  have hreal :
      (((x.val + bit b) % N : ℕ) : ℝ) +
          (N : ℝ) * (((x.val + bit b) / N : ℕ) : ℝ) =
        (x.val : ℝ) + (bit b : ℝ) := by
    exact_mod_cast hnat
  change ((((x.val + bit b) % N : ℕ) : ℝ)) =
    (x.val : ℝ) + (bit b : ℝ) -
      (N : ℝ) * (((x.val + bit b) / N : ℕ) : ℝ)
  linarith

private theorem vertCoord_addVertexBits (N : ℕ) [NeZero N]
    (cell : Vertex N N N) (a : Fin 8) (i : Fin 3) :
    vertCoord N (addVertexBits cell a) i =
      (vertexNatCoord cell i : ℝ) + (bit (cubeVertexBit a i) : ℝ) -
        (N : ℝ) *
          (((vertexNatCoord cell i + bit (cubeVertexBit a i)) / N : ℕ) : ℝ) := by
  fin_cases i <;>
    simp only [vertCoord, addVertexBits, addBits, vertexNatCoord, cubeVertexBit] <;>
    apply addBit_val_real

/-- The literal doubled-midpoint table is exactly twice the base bit plus
the actual displacement vector, coordinate by coordinate. -/
theorem slotMidTwice_eq_geometry (N : ℕ) [NeZero N]
    (cell : Vertex N N N) (t f : Fin 6) (i : Fin 3) :
    (((slotMidTwice t f i : ℤ) : ℝ) / 2) =
      (bit (slotBaseBit t f i) : ℝ) +
        FreudenthalStencilPreflight.dispReal (localEdgeOf cell t f).disp i / 2 := by
  fin_cases t <;> fin_cases f <;> fin_cases i <;>
    norm_num [slotMidTwice, slotBaseBit, slotDispBit, cubeVertexBit,
      cubeDispBit, localEdgeOf,
      Geometry.FreudenthalCubeTriangulation.localEdgeOf, cubeEdgeBase,
      cubeEdgeDisp, vertexBits, dispBits, bit,
      FreudenthalStencilPreflight.dispReal]

/-- Exact phase decomposition for every cell, including periodic seams.
The wrapped representative differs from the unwrapped cell-relative phase
by an integral number of full turns. -/
theorem localEdge_phase_decomposition (N : ℕ) [NeZero N]
    (m : Fin 3 → ℤ) (cell : Vertex N N N) (t f : Fin 6) :
    edgeMidpointPhase N (commensurateMomentum N m) (localEdgeOf cell t f) =
      BlochCellSum.theta N m cell + slotPhase N m t f -
        2 * Real.pi * (slotWrapTurns N m cell t f : ℝ) := by
  have hwrap :
      (slotWrapTurns N m cell t f : ℝ) =
        ∑ i : Fin 3, (m i : ℝ) * (slotWrapCount N cell t f i : ℝ) := by
    unfold slotWrapTurns
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    norm_cast
  unfold edgeMidpointPhase slotPhase
  simp only [Fin.sum_univ_three]
  rw [show (localEdgeOf cell t f).base =
      addVertexBits cell
        (cubeEdgeBase
          (Geometry.FreudenthalCubeTriangulation.localEdgeOf t f)) from rfl]
  rw [vertCoord_addVertexBits N cell _ 0,
    vertCoord_addVertexBits N cell _ 1,
    vertCoord_addVertexBits N cell _ 2]
  rw [slotMidTwice_eq_geometry N cell t f 0,
    slotMidTwice_eq_geometry N cell t f 1,
    slotMidTwice_eq_geometry N cell t f 2]
  rw [hwrap]
  unfold BlochCellSum.theta commensurateMomentum slotWrapCount
  simp only [Fin.sum_univ_three]
  unfold slotBaseBit vertexNatCoord
  push_cast
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp [hN]
  ring

/-- Cosine form of the phase decomposition.  Integral seam corrections
disappear by `2*pi` periodicity. -/
theorem cos_localEdge_eq_cell_slot (N : ℕ) [NeZero N]
    (m : Fin 3 → ℤ) (cell : Vertex N N N) (t f : Fin 6) :
    Real.cos
        (edgeMidpointPhase N (commensurateMomentum N m)
          (localEdgeOf cell t f)) =
      Real.cos (BlochCellSum.theta N m cell + slotPhase N m t f) := by
  rw [localEdge_phase_decomposition N m cell t f]
  rw [show 2 * Real.pi * (slotWrapTurns N m cell t f : ℝ) =
      (slotWrapTurns N m cell t f : ℝ) * (2 * Real.pi) by ring]
  exact Real.cos_sub_int_mul_two_pi _ _

/-! ## Raw triple and bucket assembly -/

/-- The bucket cosine for a raw triple is the cosine of the difference of
its two cell-independent slot phases. -/
theorem rawCosineEvaluator_bucketKeyOf (N : ℕ) [NeZero N]
    (m : Fin 3 → ℤ) (p : Fin 6 × Fin 6 × Fin 6) :
    rawCosineEvaluator N m (bucketKeyOf p) =
      Real.cos (slotPhase N m p.1 p.2.1 - slotPhase N m p.1 p.2.2) := by
  unfold rawCosineEvaluator bucketKeyOf slotPhase
  have harg :
      (∑ i : Fin 3,
        commensurateMomentum N m i *
          (((slotMidTwice p.1 p.2.2 i - slotMidTwice p.1 p.2.1 i : ℤ) : ℝ) / 2)) =
        -(∑ i : Fin 3,
            commensurateMomentum N m i * (((slotMidTwice p.1 p.2.1 i : ℤ) : ℝ) / 2) -
          ∑ i : Fin 3,
            commensurateMomentum N m i *
              (((slotMidTwice p.1 p.2.2 i : ℤ) : ℝ) / 2)) := by
    simp only [Fin.sum_univ_three]
    push_cast
    ring
  rw [harg, Real.cos_neg]

/-- One signed raw stencil term is a cell-independent raw triple weight
times the two phase-shifted cell cosines. -/
theorem neg_rawCellStencilTerm_eq (N : ℕ) [NeZero N]
    (E : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℤ)
    (cell : Vertex N N N) (t f g : Fin 6) :
    -rawCellStencilTerm N E m (cell, t) f g =
      rawTripleWeight E (t, f, g) *
        Real.cos (BlochCellSum.theta N m cell + slotPhase N m t f) *
        Real.cos (BlochCellSum.theta N m cell + slotPhase N m t g) := by
  unfold rawCellStencilTerm rawTripleWeight
  unfold ReggeTTLocalSymbolExistence.planeWaveTetVelocity
  rw [slotDispClass_grounded N cell t f, slotDispClass_grounded N cell t g]
  rw [cos_localEdge_eq_cell_slot N m cell t f,
    cos_localEdge_eq_cell_slot N m cell t g]
  unfold ReggeTTBlochInterfaceAudit.rawJacobianCoefficient
  ring

/-- The raw cosine bucket fold expands to the plain sum over all 216 raw
triples, with bucket collisions retained through the fiber amplitude. -/
theorem rawCosineFold_eq_rawTripleSum (N : ℕ) [NeZero N]
    (E : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℤ) :
    reggeTTBlochFold rawCosineSupport (rawCosineEvaluator N m)
        (rawBucketAmplitude E) =
      ∑ p : Fin 6 × Fin 6 × Fin 6,
        rawCosineEvaluator N m (bucketKeyOf p) * rawTripleWeight E p := by
  unfold reggeTTBlochFold rawCosineSupport
  rw [Finset.sum_image' (fun p : Fin 6 × Fin 6 × Fin 6 =>
    rawCosineEvaluator N m (bucketKeyOf p) * rawTripleWeight E p)]
  intro p _
  unfold rawBucketAmplitude
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hkey : bucketKeyOf q = bucketKeyOf p := (Finset.mem_filter.mp hq).2
  rw [hkey]

/-- Exact cell sum for one raw triple under the one-coordinate doubled
frequency non-aliasing hypothesis. -/
theorem rawTriple_cellSum (N : ℕ) [NeZero N]
    (E : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℤ)
    (p : Fin 6 × Fin 6 × Fin 6)
    (halias : ∃ i : Fin 3, ¬ (N : ℤ) ∣ 2 * m i) :
    (∑ cell : Vertex N N N,
      rawTripleWeight E p *
        Real.cos (BlochCellSum.theta N m cell + slotPhase N m p.1 p.2.1) *
        Real.cos (BlochCellSum.theta N m cell + slotPhase N m p.1 p.2.2)) =
      rawTripleWeight E p * ((N : ℝ) ^ 3 / 2) *
        rawCosineEvaluator N m (bucketKeyOf p) := by
  have hcell := BlochCellSum.cellSum_cos_mul_cos N m
    (slotPhase N m p.1 p.2.1) (slotPhase N m p.1 p.2.2) halias
  calc
    (∑ cell : Vertex N N N,
        rawTripleWeight E p *
          Real.cos (BlochCellSum.theta N m cell + slotPhase N m p.1 p.2.1) *
          Real.cos (BlochCellSum.theta N m cell + slotPhase N m p.1 p.2.2))
        = rawTripleWeight E p *
            ∑ cell : Vertex N N N,
              Real.cos
                  (BlochCellSum.theta N m cell + slotPhase N m p.1 p.2.1) *
                Real.cos
                  (BlochCellSum.theta N m cell + slotPhase N m p.1 p.2.2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun cell _ => ?_
          ring
    _ = rawTripleWeight E p * ((N : ℝ) ^ 3 / 2) *
          rawCosineEvaluator N m (bucketKeyOf p) := by
          rw [hcell, rawCosineEvaluator_bucketKeyOf N m p]
          ring

/-- FINITE ASSEMBLY HEADLINE: under exact doubled-frequency non-aliasing,
the Schlaefli-reduced raw stencil equals the raw bucket cosine fold. -/
theorem rawCellStencil_eq_rawCosineBlochFold (N : ℕ) [NeZero N]
    (E : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℤ)
    (halias : ∃ i : Fin 3, ¬ (N : ℤ) ∣ 2 * m i) :
    rawCellStencil N E m =
      reggeTTBlochFold rawCosineSupport (rawCosineEvaluator N m)
        (rawBucketAmplitude E) := by
  unfold rawCellStencil
  have hregroup :
      -(∑ τ : PeriodicTet N N N, ∑ f : Fin 6, ∑ g : Fin 6,
          rawCellStencilTerm N E m τ f g) =
        ∑ p : Fin 6 × Fin 6 × Fin 6, ∑ cell : Vertex N N N,
          rawTripleWeight E p *
            Real.cos (BlochCellSum.theta N m cell + slotPhase N m p.1 p.2.1) *
            Real.cos (BlochCellSum.theta N m cell + slotPhase N m p.1 p.2.2) := by
    calc
      -(∑ τ : PeriodicTet N N N, ∑ f : Fin 6, ∑ g : Fin 6,
          rawCellStencilTerm N E m τ f g)
          = ∑ cell : Vertex N N N, ∑ t : Fin 6, ∑ f : Fin 6, ∑ g : Fin 6,
              -rawCellStencilTerm N E m (cell, t) f g := by
            rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun cell _ => ?_
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [← Finset.sum_neg_distrib]
      _ = ∑ t : Fin 6, ∑ f : Fin 6, ∑ g : Fin 6, ∑ cell : Vertex N N N,
              -rawCellStencilTerm N E m (cell, t) f g := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [Finset.sum_comm]
      _ = ∑ t : Fin 6, ∑ f : Fin 6, ∑ g : Fin 6, ∑ cell : Vertex N N N,
              rawTripleWeight E (t, f, g) *
                Real.cos (BlochCellSum.theta N m cell + slotPhase N m t f) *
                Real.cos
                  (BlochCellSum.theta N m cell + slotPhase N m t g) := by
            refine Finset.sum_congr rfl fun t _ => ?_
            refine Finset.sum_congr rfl fun f _ => ?_
            refine Finset.sum_congr rfl fun g _ => ?_
            exact Finset.sum_congr rfl fun cell _ =>
              neg_rawCellStencilTerm_eq N E m cell t f g
      _ = ∑ p : Fin 6 × Fin 6 × Fin 6, ∑ cell : Vertex N N N,
              rawTripleWeight E p *
                Real.cos
                  (BlochCellSum.theta N m cell + slotPhase N m p.1 p.2.1) *
                Real.cos
                  (BlochCellSum.theta N m cell + slotPhase N m p.1 p.2.2) := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Fintype.sum_prod_type]
  rw [hregroup]
  rw [Finset.sum_congr rfl fun p _ => rawTriple_cellSum N E m p halias]
  have hNcast : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hN : (N : ℝ) ^ (3 : ℕ) ≠ 0 := by
    positivity
  have hcancel :
      (2 / (N : ℝ) ^ (3 : ℕ)) * ((N : ℝ) ^ (3 : ℕ) / 2) = 1 := by
    field_simp [hNcast]
  calc
    (2 / (N : ℝ) ^ (3 : ℕ)) *
        ∑ p : Fin 6 × Fin 6 × Fin 6,
          rawTripleWeight E p * ((N : ℝ) ^ 3 / 2) *
            rawCosineEvaluator N m (bucketKeyOf p)
        = ∑ p : Fin 6 × Fin 6 × Fin 6,
            rawCosineEvaluator N m (bucketKeyOf p) * rawTripleWeight E p := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          calc
            (2 / (N : ℝ) ^ (3 : ℕ)) *
                (rawTripleWeight E p * ((N : ℝ) ^ 3 / 2) *
                  rawCosineEvaluator N m (bucketKeyOf p))
                = ((2 / (N : ℝ) ^ (3 : ℕ)) *
                    ((N : ℝ) ^ (3 : ℕ) / 2)) *
                    (rawTripleWeight E p *
                      rawCosineEvaluator N m (bucketKeyOf p)) := by ring
            _ = rawCosineEvaluator N m (bucketKeyOf p) *
                  rawTripleWeight E p := by
                  rw [hcancel, one_mul]
                  ring
    _ = reggeTTBlochFold rawCosineSupport (rawCosineEvaluator N m)
          (rawBucketAmplitude E) :=
      (rawCosineFold_eq_rawTripleSum N E m).symm

/-- CANONICAL FINITE ASSEMBLY: the actual reduced finite second variation
equals the raw bucket cosine fold under the same non-aliasing condition. -/
theorem canonicalFiniteH_eq_rawCosineBlochFold (N : ℕ) [NeZero N]
    (E : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℤ)
    (halias : ∃ i : Fin 3, ¬ (N : ℤ) ∣ 2 * m i) :
    canonicalFiniteH N E m =
      reggeTTBlochFold rawCosineSupport (rawCosineEvaluator N m)
        (rawBucketAmplitude E) := by
  rw [a2_reduced_eq_rawCellStencil,
    rawCellStencil_eq_rawCosineBlochFold N E m halias]

/-- For every fixed nonzero integer mode, the canonical finite assembly
identity holds at every sufficiently large side length.  The explicit
`NeZero N` argument only supplies the existing finite-torus definitions. -/
theorem eventually_canonicalFiniteH_eq_rawCosineBlochFold
    (E : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℤ)
    (hm : ∃ i : Fin 3, m i ≠ 0) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ hN : NeZero N,
      @canonicalFiniteH N hN E m =
        reggeTTBlochFold rawCosineSupport (@rawCosineEvaluator N hN m)
          (rawBucketAmplitude E) := by
  filter_upwards [BlochCellSum.eventually_nonaliased m hm] with N halias
  intro hN
  letI : NeZero N := hN
  exact canonicalFiniteH_eq_rawCosineBlochFold N E m halias

end

end ReggeTTBlochAssembly
end Analysis
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTBlochAssembly.localEdge_phase_decomposition
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTBlochAssembly.cos_localEdge_eq_cell_slot
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTBlochAssembly.rawCellStencil_eq_rawCosineBlochFold
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTBlochAssembly.canonicalFiniteH_eq_rawCosineBlochFold
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTBlochAssembly.eventually_canonicalFiniteH_eq_rawCosineBlochFold
