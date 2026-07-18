import IndisputableMonolith.Gravity.Analysis.ReggeTTHingeAwareZeroMode
import IndisputableMonolith.Gravity.Analysis.ReggeTTBlochConventionAudit
import IndisputableMonolith.Gravity.Analysis.ReggeTTGateBBridgeCore

/-!
# Regge TT Gate B: the spike convention bridge (Gate C-B)

QG full-theory campaign, Paper C / Pillar 1, Lane C of the finishing
charter.  This module closes the panel-locked Gate B target
`GateBConventionTarget` of `ReggeTTBlochConventionAudit`: the interface
moment fold `reggeTTMoment`, instantiated on support / phase quadratic /
amplitude built FROM THE ACTUAL RAW STENCIL, equals the committed spike
LHS `tetBlock0 + ... + tetBlock5` under the seven TT hypotheses.

## Instantiation (all from the raw stencil, none from the spike)

* `bucketKeyOf (t, f, g)` sends a raw stencil triple (tetrahedron type,
  ordered slot pair) to the bucket `(f, g, u)` whose integer phase key
  `u = 2*(mid_g - mid_f)` is the doubled midpoint displacement of the
  slot pair, from the literal `slotMidTwice` table of the core module.
  The table is GROUNDED against the actual periodic geometry:
  `edgeMidpointPhase_grounded` proves that the preregistered midpoint
  Bloch phase of `localEdgeOf` at the base cell is exactly
  `sum_i k_i * (slotMidTwice t f i) / 2`.
* `rawMomentSupport` is the image of all 216 raw triples under
  `bucketKeyOf`: the support IS the raw cell stencil's bucket set.
* `rawPhaseQuadratic x b = (sum_i x_i * u_i / 2)^2` is the squared
  midpoint-displacement phase of the bucket: the campaign's frozen
  cosine two-jet convention (`cos z ~ 1 - z^2/2`; `reggeTTMoment`
  supplies the `-z^2/2` evaluator itself).
* `rawBucketAmplitude E b` is the honest BUCKET-FIBER AGGREGATION: the
  sum over the raw triples in the fiber of `b` of
  `-(J_fg/(2 sqrt a*_f)) * c_{d(t,f)} * c_{d(t,g)}`, with
  `rawJacobianCoefficient` and `polEdgeCoeff` the actual interface-audit
  objects and `slotDispClass` the grounded displacement-class table.
  The minus sign is the raw cell stencil's own sign
  (`rawCellStencil = (2/N^3) * (-sum ...)`).

## Proof architecture (memory-guard split)

The 216-term polynomial normalization lives in the LEAF module
`ReggeTTGateBBridgeCore` (import-light so the local build memory guard
is respected); every literal table it uses is kernel-identified here
with the corresponding ACTUAL raw-stencil object
(`coreWeight_eq_raw`, `corePolEdgeCoeff_eq`, `slotDispCore_eq`,
`tripleTerm_ident`), so nothing rests on a transcription:

1. `reggeTTMoment_eq_rawTripleSum`: the bucket fold with the
   fiber-aggregated amplitude equals the plain 216-triple sum
   (`Finset.sum_image'`; nothing dropped or double counted).
2. `tripleTerm_ident`: each signed raw term equals the core term.
3. `coreTripleSum_eq_spikeSum` (core): the triple sum equals
   `tetBlock0 + .. + tetBlock5` with free `s2 s3 p`, identically.
4. `rawMoment_eq_committedSpikeLHS`: chained at
   `s2 = sqrt 2, s3 = sqrt 3, p = pi`.
5. `gateB_convention_bridge`, THE LOCKED HEADLINE:
   `GateBConventionTarget rawMomentSupport (rawPhaseQuadratic x)
   (rawBucketAmplitude E) E x` for every `E, x`.

`tt_continuum_certificate` and the spike's `-1/4` conclusion are NEVER
invoked; only the spike LHS blocks `tetBlock0..5` are used, as data.

## Disclosure: the seven TT hypotheses are not consumed

The bridge equality turned out to hold IDENTICALLY in `(E, x)`: the raw
J-weighted moment and the full-Hessian spike moment agree per
tetrahedron type BEFORE any TT reduction (the theta-second-derivative
part of the spike's Hessian weights drops out of the second-moment
layer per tet).  The locked target Prop takes the seven TT equations as
antecedents; they are introduced and the consequent is closed a
fortiori by the unconditional identity.  The stronger unconditional
statement is exported as `rawMoment_eq_committedSpikeLHS` so no
hypothesis strength is hidden.

## Inherited axiom footprint (disclosure)

Everything here is finite algebra over the Gate C-A2f table; the
expected footprint of every theorem is the standard trio
`[propext, Classical.choice, Quot.sound]`.  Receipts at end of file.

No `sorry`, no `admit`, no new axioms, no `native_decide`, no `: True`
or `Nonempty`-only headline in this file.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTGateBBridge

open Geometry.PeriodicFreudenthalTorus
open ReggeTTSymbolPreflight
open ReggeTTBlochInterfaceAudit
open ReggeTTBlochConventionAudit
open ReggeTTGateBBridgeCore (coreWeight slotDispCore slotMidTwice
  corePolEdgeCoeff coreTripleTerm coreTripleSum_eq_spikeSum)
open ReggeTTBucketAggregation (rawJacobianCoefficient_eval)
open ReggeTTHingeAwareZeroMode (slotDispClass slotDispClass_grounded)

noncomputable section

set_option maxHeartbeats 1600000

/-! ## §1. Grounding the literal tables against the actual objects -/

/-- GROUNDING (THEOREM): the literal doubled-midpoint table reproduces
the ACTUAL preregistered midpoint Bloch phase of the periodic geometry:
for every momentum `k` and slot, the midpoint phase of the local edge at
the base cell is `sum_i k_i * (slotMidTwice t f i) / 2` (stated at the
smallest campaign torus `N = 4` with the base cell; the offsets are
cell-relative by construction). -/
theorem edgeMidpointPhase_grounded (k : Fin 3 → ℝ) (t f : Fin 6) :
    edgeMidpointPhase 4 k
        (localEdgeOf (((0 : Fin 4), (0 : Fin 4), (0 : Fin 4)) :
          Vertex 4 4 4) t f) =
      ∑ i : Fin 3, k i * (((slotMidTwice t f i : ℤ) : ℝ) / 2) := by
  fin_cases t <;> fin_cases f <;>
    · simp only [edgeMidpointPhase, Fin.sum_univ_three, vertCoord,
        localEdgeOf, addVertexBits, addBits, addBit, bit, vertexBits,
        cubeEdgeBase, cubeEdgeDisp,
        Geometry.FreudenthalCubeTriangulation.localEdgeOf,
        FreudenthalStencilPreflight.dispReal, slotMidTwice]
      push_cast
      norm_num

/-- The core weight table IS the actual raw Jacobian coefficient (via
the Gate C-A2f kernel evaluation; nothing is transcribed on trust). -/
theorem coreWeight_eq_raw (f g : Fin 6) :
    coreWeight f g = rawJacobianCoefficient f g := by
  rw [rawJacobianCoefficient_eval f g]
  fin_cases f <;> fin_cases g <;>
    norm_num [coreWeight, ReggeTTBucketAggregation.rationalStencilWeight]

/-- The core edge-class linear forms ARE the actual `polEdgeCoeff`. -/
theorem corePolEdgeCoeff_eq (E : Fin 3 → Fin 3 → ℝ) (d : Fin 7) :
    corePolEdgeCoeff E d = polEdgeCoeff E d := by
  fin_cases d <;>
    · simp only [corePolEdgeCoeff, polEdgeCoeff, Fin.sum_univ_three,
        FreudenthalStencilPreflight.dispReal]
      ring

/-- The core slot displacement table IS the grounded `slotDispClass`. -/
theorem slotDispCore_eq (t f : Fin 6) :
    slotDispCore t f = slotDispClass t f := by
  fin_cases t <;> fin_cases f <;> rfl

/-! ## §2. The raw-stencil instantiation of the moment fold -/

/-- The bucket key of one raw stencil triple `(t, f, g)`: slot pair
`(f, g)` with integer phase key the doubled midpoint displacement
`2*(mid_g - mid_f)`. -/
def bucketKeyOf (p : Fin 6 × Fin 6 × Fin 6) : Bucket :=
  ⟨p.2.1, p.2.2,
    fun i => slotMidTwice p.1 p.2.2 i - slotMidTwice p.1 p.2.1 i⟩

/-- The support: the bucket set of the raw cell stencil (image of all
216 raw triples). -/
def rawMomentSupport : Finset Bucket :=
  Finset.univ.image bucketKeyOf

/-- The phase quadratic of a bucket: the squared midpoint-displacement
phase `(sum_i x_i * u_i/2)^2` in direction `x` (the halving undoes the
doubling of the integer key). -/
def rawPhaseQuadratic (x : Fin 3 → ℝ) (b : Bucket) : ℝ :=
  (∑ i : Fin 3, x i * (((b.phase i : ℤ) : ℝ) / 2)) ^ 2

/-- One signed raw stencil moment weight: `-(J_fg / (2 sqrt a*_f)) *
c_{d(t,f)} * c_{d(t,g)}` (the raw cell stencil's own minus sign). -/
def rawTripleWeight (E : Fin 3 → Fin 3 → ℝ)
    (p : Fin 6 × Fin 6 × Fin 6) : ℝ :=
  -(rawJacobianCoefficient p.2.1 p.2.2 *
    polEdgeCoeff E (slotDispClass p.1 p.2.1) *
    polEdgeCoeff E (slotDispClass p.1 p.2.2))

/-- The amplitude: the honest BUCKET-FIBER AGGREGATION of the signed raw
stencil weights over the triples landing in the bucket. -/
def rawBucketAmplitude (E : Fin 3 → Fin 3 → ℝ) (b : Bucket) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => bucketKeyOf p = b),
    rawTripleWeight E p

/-! ## §3. The fold equals the plain raw triple sum -/

/-- The bucket fold with fiber-aggregated amplitudes equals the plain
sum over all 216 raw triples: no collision of bucket keys is dropped or
double counted (`Finset.sum_image'` on the key map). -/
theorem reggeTTMoment_eq_rawTripleSum (E : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) :
    reggeTTMoment rawMomentSupport (rawPhaseQuadratic x)
        (rawBucketAmplitude E) =
      ∑ p : Fin 6 × Fin 6 × Fin 6,
        -(rawPhaseQuadratic x (bucketKeyOf p)) / 2 * rawTripleWeight E p := by
  unfold reggeTTMoment reggeTTBlochFold rawMomentSupport
  rw [Finset.sum_image' (fun p : Fin 6 × Fin 6 × Fin 6 =>
    -(rawPhaseQuadratic x (bucketKeyOf p)) / 2 * rawTripleWeight E p)]
  intro p _
  unfold rawBucketAmplitude
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hkey : bucketKeyOf q = bucketKeyOf p := (Finset.mem_filter.mp hq).2
  rw [hkey]

/-- Each signed raw moment term equals the core module's literal term
(pointwise identification of every table with its actual object; no
case split on the triple is needed). -/
theorem tripleTerm_ident (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (p : Fin 6 × Fin 6 × Fin 6) :
    -(rawPhaseQuadratic x (bucketKeyOf p)) / 2 * rawTripleWeight E p =
      coreTripleTerm E x p := by
  unfold rawPhaseQuadratic bucketKeyOf rawTripleWeight
  unfold ReggeTTGateBBridgeCore.coreTripleTerm
  rw [coreWeight_eq_raw, corePolEdgeCoeff_eq, corePolEdgeCoeff_eq,
    slotDispCore_eq, slotDispCore_eq]

/-! ## §4. The bridge and the locked headline -/

/-- **THE UNCONDITIONAL BRIDGE (THEOREM): the raw-stencil moment fold
equals the committed spike LHS IDENTICALLY in `(E, x)`.**  Chains the
fiber-aggregation fold, the pointwise identification, and the core
216-term identity at `s2 = sqrt 2`, `s3 = sqrt 3`, `p = pi` (the
sidecar's committed instantiation; the core identity holds for free
values).  The spike's `tt_continuum_certificate` and its `-1/4`
conclusion are never invoked: only the block data `tetBlock0..5`. -/
theorem rawMoment_eq_committedSpikeLHS (E : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) :
    reggeTTMoment rawMomentSupport (rawPhaseQuadratic x)
        (rawBucketAmplitude E) =
      committedSpikeLHS (spikeInput E x) := by
  rw [reggeTTMoment_eq_rawTripleSum]
  rw [Finset.sum_congr rfl fun p _ => tripleTerm_ident E x p]
  rw [coreTripleSum_eq_spikeSum E x (Real.sqrt 2) (Real.sqrt 3) Real.pi]
  rfl

/-- **GATE C-B HEADLINE (THEOREM): the panel-locked Gate B target is
closed on the raw-stencil instantiation.**  `GateBConventionTarget`
(exactly the sidecar's Prop) holds for the raw-stencil support, the
midpoint-displacement phase quadratic, and the bucket-fiber-aggregated
amplitude, for every `E` and `x`.  DISCLOSURE: the seven TT antecedents
of the locked Prop are introduced but not consumed, because the bridge
equality holds identically in `(E, x)`
(`rawMoment_eq_committedSpikeLHS`); the locked statement shape is closed
a fortiori and the stronger unconditional theorem is exported above. -/
theorem gateB_convention_bridge (E : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ) :
    GateBConventionTarget rawMomentSupport (rawPhaseQuadratic x)
      (rawBucketAmplitude E) E x := by
  intro _ _ _ _ _ _ _
  exact rawMoment_eq_committedSpikeLHS E x

end

end ReggeTTGateBBridge
end Analysis
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTGateBBridge.edgeMidpointPhase_grounded
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTGateBBridge.coreWeight_eq_raw
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTGateBBridge.corePolEdgeCoeff_eq
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTGateBBridge.slotDispCore_eq
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTGateBBridge.reggeTTMoment_eq_rawTripleSum
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTGateBBridge.tripleTerm_ident
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTGateBBridge.rawMoment_eq_committedSpikeLHS
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTGateBBridge.gateB_convention_bridge
