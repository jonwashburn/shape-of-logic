import IndisputableMonolith.Gravity.Analysis.ReggeTTSymbolPreflight
import IndisputableMonolith.Gravity.Analysis.ReggeTTDerivativeGate

/-!
# Regge TT local symbol existence at fixed `N` (Gate A1)

QG full-theory campaign, `ReggeTTContinuumSymbol` program, Crux-1(c) lane,
Gate A1 of the panel-locked protocol "Normalization-Gated Schläfli Two-Jet"
(Gate A0 is `ReggeTTSymbolSpecificationAudit`).

## What this module proves (all THEOREM)

* (a) `planeWaveTetSqEdges_apply` / `planeWaveTetSqEdges_contDiff`: along
  the plane-wave family, every tetrahedron's local squared-edge tuple is an
  AFFINE path `t ↦ flat + t · v` through the flat Freudenthal tuple
  (coefficients named in `planeWaveTetVelocity`), smooth of every order.
* (b) `planeWaveTetSqEdges_zero` + `tetDihedralAngle_planeWave_contDiffAt`:
  at `t = 0` the tuple is EXACTLY `freudenthalTetSqEdges` (where `cm3 = 8 >
  0`, all six squared edges positive, all six cosines strictly inside
  `(-1, 1)` — Gate-0 facts of `ReggeTTDerivativeGate`), and each local
  dihedral angle along the family is `ContDiffAt` at `0` of every finite
  order, by composing the angle's `ContDiffAt` at the nondegenerate flat
  tetrahedron with the affine path.
* (c) `planeWaveActionProfile_contDiffAt`: the plane-wave action profile
  `S(t)` of the TRUE nonlinear Regge action is `ContDiffAt ℝ n` at `t = 0`
  for every finite `n` — finite sums over edges and tetrahedra, `√`
  factors safe because every flat edge value is `≥ 1 > 0`, the
  `canonicalEdgeSlot?` match is a finite case split whose `none` branch is
  constant.
* (d) `tendsto_centeredSecondDifference_of_contDiffAt` (REUSABLE, general
  `f : ℝ → ℝ`): if `f` is `C²` at `0` (`ContDiffAt ℝ 2 f 0`), the centered
  second difference `(f(t) − 2f(0) + f(−t))/t²` converges on the punctured
  neighborhood filter to `iteratedDeriv 2 f 0`.  Proof: one L'Hôpital pass
  (`HasDerivAt.lhopital_zero_nhdsNE`) reduces to
  `(f'(t) − f'(−t))/(2t) → f''(0)`, which is the average of the two slope
  quotients of `deriv f` at `0` (`hasDerivAt_iff_tendsto_slope`).  The
  panel-forbidden global route (`ContinuumLimit.continuum_limit_second_order`,
  whose global `ContDiff ℝ 4` hypothesis is false for this family) is NOT
  used anywhere.
* (e) `planeWave_TTBlochSymbolIs_secondVariation`: THE FIXED-`N` TT BLOCH
  SYMBOL EXISTS — for every polarization matrix and every integer wave
  vector, `TTBlochSymbolIs N E m ((2/N³) · S''(0))` where `S''(0) =
  iteratedDeriv 2 (planeWaveActionProfile N E (commensurateMomentum N m)) 0`.
  Exact bookkeeping: `(S(t) − 2S(0) + S(−t))/t² → S''(0)` with no stray
  `1/2`; the `2/N³` is the preflight's per-unit-cell normalization carried
  verbatim.  First existence theorem of the program.

## What this module does NOT prove (binding scope disclosure)

* No VALUE of the symbol: `H = (2/N³)·S''(0)` is existence + identification
  of the limit, not an evaluation.  The continuum `-(1/4)` target stays
  OPEN, its status flag stays `false`, and the C10 numerics remain
  NUMERICAL EVIDENCE only.
* No continuum limit in `N`: everything here is at fixed `N`.

## Inherited axiom footprint (disclosure)

`planeWaveTetSqEdges_zero` and everything downstream of it (b, c, e) factor
through Stage-1's `tetSqEdgesOfField_flat`, which is pure algebra; but (e)
also uses `planeWaveActionProfile_zero`-adjacent structure only through the
general bridge (d), so the flat-value theorems of the certified angle-sum
chain are NOT on the dependency path of the headline (e) — expected
footprint is the standard `[propext, Classical.choice, Quot.sound]`.  The
`#print axioms` receipt is recorded by the conductor's audit; if the
`Lean.ofReduceBool`/`Lean.trustCompiler` pair appears through any imported
flat-point fact, it is inherited disclosure, not new axioms.

No `sorry`, no `admit`, no new axioms, no `native_decide` in this file.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTLocalSymbolExistence

open Geometry.PeriodicFreudenthalTorus
open Geometry.CayleyMengerPolynomial (SqEdges)
open Geometry.DihedralDerivatives (dihedralAngle3Sq)
open Geometry.FreudenthalCubeTriangulation (freudenthalTetSqEdges freudenthalTet)
open ReggeTTSymbolPreflight

noncomputable section

variable (N : ℕ) [NeZero N]

/-! ## §1. (a) The plane-wave local squared-edge path is affine and smooth -/

/-- Squared displacement class values are strictly positive (they are
`1, 1, 1, 2, 2, 2, 3`). -/
theorem periodicDispSqEdge_pos (d : Fin 7) : 0 < periodicDispSqEdge d := by
  fin_cases d <;> norm_num [periodicDispSqEdge]

/-- The affine velocity of the local squared-edge tuple of tetrahedron
`cellTet` along the plane-wave family:
`v_f = polEdgeCoeff E d_f · cos(k · x_mid(f))`. -/
def planeWaveTetVelocity (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (cellTet : PeriodicTet N N N) : Fin 6 → ℝ :=
  fun f =>
    polEdgeCoeff E (localEdgeOf cellTet.1 cellTet.2 f).disp *
      Real.cos (edgeMidpointPhase N k (localEdgeOf cellTet.1 cellTet.2 f))

/-- (a) THEOREM, affine coordinates: along the plane-wave family every
local squared-edge coordinate is `flat + t · velocity`, with the flat value
the canonical Freudenthal tuple. -/
theorem planeWaveTetSqEdges_apply (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (cellTet : PeriodicTet N N N) (t : ℝ) (f : Fin 6) :
    tetSqEdgesOfField N (planeWaveEdgeField N E k t) cellTet f =
      freudenthalTetSqEdges f + t * planeWaveTetVelocity N E k cellTet f := by
  simp only [tetSqEdgesOfField, planeWaveEdgeField, planeWaveTetVelocity]
  rw [show freudenthalTetSqEdges f =
      periodicDispSqEdge ((localEdgeOf cellTet.1 cellTet.2 f).disp) from
    freudenthalTet_sqEdge_eq_periodicDispSqEdge_localEdgeOf cellTet.1 cellTet.2 f]
  ring

/-- At `t = 0` the local tuple is exactly the flat Freudenthal tuple. -/
theorem planeWaveTetSqEdges_zero (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (cellTet : PeriodicTet N N N) :
    tetSqEdgesOfField N (planeWaveEdgeField N E k 0) cellTet =
      freudenthalTetSqEdges := by
  funext f
  rw [planeWaveTetSqEdges_apply, zero_mul, add_zero]

/-- (a) THEOREM, smoothness: the local squared-edge path is `C^n` in the
amplitude for every order (it is affine). -/
theorem planeWaveTetSqEdges_contDiff (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (cellTet : PeriodicTet N N N) (n : ℕ∞) :
    ContDiff ℝ n
      (fun t : ℝ => tetSqEdgesOfField N (planeWaveEdgeField N E k t) cellTet) := by
  have h : (fun t : ℝ => tetSqEdgesOfField N (planeWaveEdgeField N E k t) cellTet) =
      fun t : ℝ => fun f : Fin 6 =>
        freudenthalTetSqEdges f + t * planeWaveTetVelocity N E k cellTet f := by
    funext t f
    exact planeWaveTetSqEdges_apply N E k cellTet t f
  rw [h]
  refine contDiff_pi.mpr fun f => ?_
  exact contDiff_const.add (contDiff_id.mul contDiff_const)

/-- Each single plane-wave edge value is `C^n` in the amplitude (affine). -/
theorem planeWaveEdgeValue_contDiff (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (e : PeriodicEdge N N N) (n : ℕ∞) :
    ContDiff ℝ n (fun t : ℝ => planeWaveEdgeField N E k t e) := by
  have h : (fun t : ℝ => planeWaveEdgeField N E k t e) =
      fun t : ℝ => periodicDispSqEdge e.disp +
        t * (polEdgeCoeff E e.disp * Real.cos (edgeMidpointPhase N k e)) := by
    funext t
    simp only [planeWaveEdgeField]
    ring
  rw [h]
  exact contDiff_const.add (contDiff_id.mul contDiff_const)

/-! ## §2. (b) Endpoint/positivity safety at flat and angle smoothness -/

/-- (b) THEOREM: each local dihedral angle along the plane-wave family is
`ContDiffAt` at amplitude `0` of every finite order.  The flat point is the
nondegenerate Freudenthal tetrahedron (`cm3 = 8 > 0`, cosines
`√2/2, 0, 1/2` strictly inside `(-1,1)` — `ReggeTTDerivativeGate`
`flatCos_ne_endpoints`), so the angle map is `ContDiffAt` in the 6-tuple
there; composition with the affine path gives the amplitude smoothness. -/
theorem tetDihedralAngle_planeWave_contDiffAt (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) (cellTet : PeriodicTet N N N) (f : Fin 6) (n : ℕ∞) :
    ContDiffAt ℝ n
      (fun t : ℝ => tetDihedralAngleOfField N (planeWaveEdgeField N E k t) cellTet f)
      0 := by
  have hangle : ContDiffAt ℝ n (fun a : SqEdges => dihedralAngle3Sq a f)
      freudenthalTetSqEdges :=
    Geometry.ReggeActionFirstVariation.dihedralAngle3Sq_contDiffAt_nonDegenerate
      freudenthalTet f n (ReggeTTDerivativeGate.flatCos_ne_endpoints f)
  have hpath : ContDiffAt ℝ n
      (fun t : ℝ => tetSqEdgesOfField N (planeWaveEdgeField N E k t) cellTet) 0 :=
    (planeWaveTetSqEdges_contDiff N E k cellTet n).contDiffAt
  have hangle' : ContDiffAt ℝ n (fun a : SqEdges => dihedralAngle3Sq a f)
      (tetSqEdgesOfField N (planeWaveEdgeField N E k 0) cellTet) := by
    rw [planeWaveTetSqEdges_zero]
    exact hangle
  have hcomp := ContDiffAt.comp (x := (0 : ℝ)) hangle' hpath
  exact hcomp.congr_of_eventuallyEq (by
    filter_upwards with t
    rfl)

/-! ## §3. (c) The action profile is `ContDiffAt` at `0` of every order -/

/-- The per-tetrahedron angle contribution to one edge's angle sum is
`ContDiffAt` at `0` (finite case split on the slot lookup; `none` branch is
the constant `0`). -/
theorem edgeAngleContribution_planeWave_contDiffAt (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) (e : PeriodicEdge N N N) (cellTet : PeriodicTet N N N)
    (n : ℕ∞) :
    ContDiffAt ℝ n
      (fun t : ℝ =>
        edgeAngleContributionOfField N (planeWaveEdgeField N E k t) e cellTet)
      0 := by
  unfold edgeAngleContributionOfField
  cases h : canonicalEdgeSlot? e cellTet.1 cellTet.2 with
  | none => simpa [h] using contDiffAt_const (c := (0 : ℝ))
  | some f =>
      simpa [h] using
        tetDihedralAngle_planeWave_contDiffAt N E k cellTet f n

/-- Each edge deficit along the plane-wave family is `ContDiffAt` at `0`
(constant `2π` minus a finite sum of smooth contributions). -/
theorem deficit_planeWave_contDiffAt (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (e : PeriodicEdge N N N) (n : ℕ∞) :
    ContDiffAt ℝ n
      (fun t : ℝ => deficitOfField N (planeWaveEdgeField N E k t) e) 0 := by
  unfold deficitOfField
  refine ContDiffAt.sub contDiffAt_const ?_
  exact ContDiffAt.sum fun cellTet _ =>
    edgeAngleContribution_planeWave_contDiffAt N E k e cellTet n

/-- The square-root hinge factor of each edge is `ContDiffAt` at `0`: the
edge value at `t = 0` is `periodicDispSqEdge ∈ {1,2,3} > 0`, so `√` is
smooth there. -/
theorem sqrtEdge_planeWave_contDiffAt (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (e : PeriodicEdge N N N) (n : ℕ∞) :
    ContDiffAt ℝ n
      (fun t : ℝ => Real.sqrt (planeWaveEdgeField N E k t e)) 0 := by
  refine ContDiffAt.sqrt ((planeWaveEdgeValue_contDiff N E k e n).contDiffAt) ?_
  simp only [planeWaveEdgeField, zero_mul, add_zero]
  exact ne_of_gt (periodicDispSqEdge_pos e.disp)

/-- (c) THEOREM: the plane-wave action profile of the TRUE nonlinear Regge
action is `ContDiffAt ℝ n` at `t = 0` for every finite order `n`. -/
theorem planeWaveActionProfile_contDiffAt (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) (n : ℕ∞) :
    ContDiffAt ℝ n (planeWaveActionProfile N E k) 0 := by
  have h : planeWaveActionProfile N E k =
      fun t : ℝ => ∑ e : PeriodicEdge N N N,
        Real.sqrt (planeWaveEdgeField N E k t e) *
          deficitOfField N (planeWaveEdgeField N E k t) e := by
    funext t
    rfl
  rw [h]
  exact ContDiffAt.sum fun e _ =>
    (sqrtEdge_planeWave_contDiffAt N E k e n).mul
      (deficit_planeWave_contDiffAt N E k e n)

/-! ## §4. (d) The reusable centered second-difference bridge -/

/-- Slope average identity: for `t ≠ 0`,
`(g(t) − g(−t))/(2t) = (slope g 0 t + slope g 0 (−t))/2`. -/
theorem slope_average_eq (g : ℝ → ℝ) {t : ℝ} (_ht : t ≠ 0) :
    (g t - g (-t)) / (2 * t) =
      (slope g 0 t + slope g 0 (-t)) / 2 := by
  rw [slope_def_field, slope_def_field, sub_zero, sub_zero, div_neg,
    ← sub_eq_add_neg, div_sub_div_same, sub_sub_sub_cancel_right,
    div_div, mul_comm t 2]

/-- (d) THEOREM, THE REUSABLE LOCAL BRIDGE: if `f : ℝ → ℝ` is `C²` at `0`,
the centered second difference `(f(t) − 2f(0) + f(−t))/t²` converges along
the punctured neighborhood filter to `iteratedDeriv 2 f 0`.

Route (LOCAL Taylor / L'Hôpital, panel-approved): one pass of L'Hôpital's
rule for `0/0` forms on the punctured neighborhood
(`HasDerivAt.lhopital_zero_nhdsNE`) with numerator `g(t) = f(t) − 2f(0) +
f(−t)` and denominator `t²` reduces the limit to
`(f'(t) − f'(−t))/(2t) → f''(0)`, which is the average of the two slope
quotients of `deriv f` at `0` and converges by
`hasDerivAt_iff_tendsto_slope` applied to `deriv f` (differentiable at `0`
with derivative `deriv (deriv f) 0` since `f` is `C²` on a neighborhood).
The forbidden global lemma (`continuum_limit_second_order`, global
`ContDiff ℝ 4`) is not used. -/
theorem tendsto_centeredSecondDifference_of_contDiffAt (f : ℝ → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) :
    Filter.Tendsto
      (fun t : ℝ => (f t - 2 * f 0 + f (-t)) / t ^ (2 : ℕ))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (iteratedDeriv 2 f 0)) := by
  -- Extract a symmetric open ball on which f is C².
  obtain ⟨u, hu_mem, hu⟩ := hf.contDiffOn (le_refl 2) (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hu_mem
  have hfC2 : ContDiffOn ℝ 2 f (Metric.ball (0 : ℝ) ε) := hu.mono hball
  have hopen : IsOpen (Metric.ball (0 : ℝ) ε) := Metric.isOpen_ball
  have h0mem : (0 : ℝ) ∈ Metric.ball (0 : ℝ) ε := Metric.mem_ball_self hε
  -- deriv f is C¹ on the ball, hence differentiable at 0 with the second derivative.
  have hderivC1 : ContDiffOn ℝ 1 (deriv f) (Metric.ball (0 : ℝ) ε) :=
    hfC2.deriv_of_isOpen hopen (by norm_num)
  have hderiv_diffAt : DifferentiableAt ℝ (deriv f) 0 :=
    ((hderivC1.contDiffAt (hopen.mem_nhds h0mem)).differentiableAt (by norm_num))
  have hD : HasDerivAt (deriv f) (deriv (deriv f) 0) 0 := hderiv_diffAt.hasDerivAt
  set D : ℝ := deriv (deriv f) 0 with hD_def
  -- Membership of ±t in the ball, eventually on the punctured filter.
  have hmem_event : ∀ᶠ t in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ,
      t ∈ Metric.ball (0 : ℝ) ε ∧ -t ∈ Metric.ball (0 : ℝ) ε := by
    have hball_event : ∀ᶠ t in nhds (0 : ℝ),
        t ∈ Metric.ball (0 : ℝ) ε ∧ -t ∈ Metric.ball (0 : ℝ) ε := by
      have h1 : ∀ᶠ t in nhds (0 : ℝ), t ∈ Metric.ball (0 : ℝ) ε :=
        hopen.mem_nhds h0mem
      have hneg_cont : Filter.Tendsto (fun t : ℝ => -t) (nhds 0) (nhds 0) := by
        simpa using (continuous_neg (G := ℝ)).tendsto (0 : ℝ)
      have h2 : ∀ᶠ t in nhds (0 : ℝ), -t ∈ Metric.ball (0 : ℝ) ε :=
        hneg_cont.eventually h1
      exact h1.and h2
    exact hball_event.filter_mono nhdsWithin_le_nhds
  -- f is differentiable at every point of the ball, with derivative deriv f.
  have hfd : ∀ x ∈ Metric.ball (0 : ℝ) ε, HasDerivAt f (deriv f x) x := by
    intro x hx
    exact ((hfC2.contDiffAt (hopen.mem_nhds hx)).differentiableAt
      (by norm_num)).hasDerivAt
  -- The numerator g and its derivative on the punctured ball.
  have hgg' : ∀ᶠ t in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ,
      HasDerivAt (fun s : ℝ => f s - 2 * f 0 + f (-s))
        (deriv f t - deriv f (-t)) t := by
    filter_upwards [hmem_event] with t hmem
    have hft : HasDerivAt f (deriv f t) t := hfd t hmem.1
    have hfnt : HasDerivAt f (deriv f (-t)) (-t) := hfd (-t) hmem.2
    have hneg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := hasDerivAt_neg' t
    have hcomp : HasDerivAt (fun s : ℝ => f (-s)) (deriv f (-t) * (-1)) t :=
      HasDerivAt.comp t hfnt hneg
    have hsum := ((hft.sub_const (2 * f 0)).add hcomp)
    have hval : deriv f t + deriv f (-t) * (-1) = deriv f t - deriv f (-t) := by
      ring
    rw [hval] at hsum
    exact hsum
  -- The denominator t² and its derivative 2t.
  have hhh' : ∀ᶠ t in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ,
      HasDerivAt (fun s : ℝ => s ^ (2 : ℕ)) (2 * t) t := by
    filter_upwards with t
    simpa using hasDerivAt_pow 2 t
  have hden_ne : ∀ᶠ t in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ, 2 * t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero two_ne_zero ht
  -- Both numerator and denominator tend to 0.
  have hf_cont : ContinuousAt f 0 := hf.continuousAt
  have hnum_tendsto : Filter.Tendsto (fun s : ℝ => f s - 2 * f 0 + f (-s))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have hneg_cont : Filter.Tendsto (fun t : ℝ => -t) (nhds (0 : ℝ)) (nhds 0) := by
      simpa using (continuous_neg (G := ℝ)).tendsto (0 : ℝ)
    have hcompneg : Filter.Tendsto (fun s : ℝ => f (-s)) (nhds 0) (nhds (f 0)) := by
      simpa [Function.comp_def] using hf_cont.tendsto.comp hneg_cont
    have h1 : Filter.Tendsto (fun s : ℝ => f s - 2 * f 0 + f (-s))
        (nhds 0) (nhds (f 0 - 2 * f 0 + f 0)) :=
      (hf_cont.tendsto.sub tendsto_const_nhds).add hcompneg
    have hval : f 0 - 2 * f 0 + f 0 = 0 := by ring
    rw [hval] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hden_tendsto : Filter.Tendsto (fun s : ℝ => s ^ (2 : ℕ))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h1 : Filter.Tendsto (fun s : ℝ => s ^ (2 : ℕ)) (nhds 0)
        (nhds ((0 : ℝ) ^ (2 : ℕ))) :=
      (continuous_pow 2).tendsto (0 : ℝ)
    rw [show ((0 : ℝ) ^ (2 : ℕ)) = 0 by norm_num] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  -- The derivative quotient tends to D by slope averaging.
  have hslope : Filter.Tendsto (slope (deriv f) 0)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D) :=
    hasDerivAt_iff_tendsto_slope.mp hD
  have hnegmap : Filter.Tendsto (fun t : ℝ => -t)
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) := by
    have h1 : Filter.Tendsto (fun t : ℝ => -t) (nhds 0) (nhds 0) := by
      simpa using (continuous_neg (G := ℝ)).tendsto (0 : ℝ)
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h1.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact neg_ne_zero.mpr ht
  have hslope_neg : Filter.Tendsto (fun t : ℝ => slope (deriv f) 0 (-t))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D) :=
    hslope.comp hnegmap
  have havg : Filter.Tendsto
      (fun t : ℝ =>
        (slope (deriv f) 0 t + slope (deriv f) 0 (-t)) / 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((D + D) / 2)) :=
    (hslope.add hslope_neg).div_const 2
  rw [show (D + D) / 2 = D by ring] at havg
  have hdiv : Filter.Tendsto
      (fun t : ℝ => (deriv f t - deriv f (-t)) / (2 * t))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D) := by
    refine havg.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (slope_average_eq (deriv f) ht).symm
  -- One L'Hôpital pass assembles the limit.
  have hlim := HasDerivAt.lhopital_zero_nhdsNE hgg' hhh' hden_ne
    hnum_tendsto hden_tendsto hdiv
  have hiter : iteratedDeriv 2 f 0 = D := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hiter]
  exact hlim

/-! ## §5. (e) THE FIXED-`N` TT BLOCH SYMBOL EXISTS -/

/-- (e) HEADLINE THEOREM (first existence theorem of the program): for
every side `N`, every polarization matrix `E`, and every integer wave
vector `m`, the fixed-`N` TT Bloch symbol EXISTS and equals
`(2/N³) · S''(0)` where `S` is the plane-wave action profile of the TRUE
nonlinear Regge action.  Exact bookkeeping: the preflight's
`ttSecondDifference` is `(2/N³) · [(S(t) − 2S(0) + S(−t))/t²]` and the
bracket converges to `iteratedDeriv 2 S 0` by the local bridge (d) — no
stray `1/2` anywhere.  NOTE: this identifies the LIMIT, not its value; the
continuum `-(1/4)` target remains OPEN. -/
theorem planeWave_TTBlochSymbolIs_secondVariation (E : Fin 3 → Fin 3 → ℝ)
    (m : Fin 3 → ℤ) :
    TTBlochSymbolIs N E m
      ((2 / (N : ℝ) ^ (3 : ℕ)) *
        iteratedDeriv 2 (planeWaveActionProfile N E (commensurateMomentum N m)) 0) := by
  set k : Fin 3 → ℝ := commensurateMomentum N m with hk
  set S : ℝ → ℝ := planeWaveActionProfile N E k with hS
  have hC2 : ContDiffAt ℝ 2 S 0 := planeWaveActionProfile_contDiffAt N E k 2
  have hbridge := tendsto_centeredSecondDifference_of_contDiffAt S hC2
  unfold TTBlochSymbolIs
  have hconst := hbridge.const_mul (2 / (N : ℝ) ^ (3 : ℕ))
  refine hconst.congr' ?_
  filter_upwards with t
  unfold ttSecondDifference
  rw [← hk, ← hS, mul_div_assoc]

/-- Companion existence form: there IS a real number `H` with
`TTBlochSymbolIs N E m H` — the fixed-`N` symbol object is non-vacuous for
every polarization and wave vector. -/
theorem planeWave_TTBlochSymbol_exists (E : Fin 3 → Fin 3 → ℝ)
    (m : Fin 3 → ℤ) :
    ∃ H : ℝ, TTBlochSymbolIs N E m H :=
  ⟨_, planeWave_TTBlochSymbolIs_secondVariation N E m⟩

end

end ReggeTTLocalSymbolExistence
end Analysis
end Gravity
end IndisputableMonolith
