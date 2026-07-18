import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.HypersurfaceDeformation
import IndisputableMonolith.Gravity.Analysis.QuadratureLimit

/-!
# Background-weighted hypersurface bracket on the periodic lattice

QG Seven-Gaps campaign, Pillar 1 (constraint algebra), panel-locked live bet
C10: weighted structure function w on the lattice. This module generalizes the
frozen-1 hypersurface-deformation theorem `bracket_Ham_Ham` of
`HypersurfaceDeformation.lean` to a Hamiltonian generator carrying a fixed
background weight `w : ZMod n -> Real` in the stiffness (gradient-squared)
slot of the density, and proves the exact lattice bracket: the weight emerges
in the closure relation exactly where the Dirac structure function sits.

## Panel-lock honesty statement (binding)

This is a BACKGROUND-w structure function, not a phase-space-dependent inverse
metric; it moves toward but does NOT flip gap5_constraint_recovery; HKT
rigidity is untouched and OPEN. The weight `w` is a fixed function of the
lattice site, never of the phase-space point `(q, pi)`; the phase-space
dependent structure function `g^{ab}[q]` demanded by the full Dirac algebra
(and by any honest GR-recovery claim) remains OPEN and is not approximated,
inhabited, or claimed here. No `HojmanKucharTeitelboimTarget` instance is
provided; `HKTRigidityStatement` is not touched.

## What is proved (exact statements, no limits taken)

* `HamW w N` is the smeared Hamiltonian with density
  `(N_i / 2) * (pi_i^2 + w_i * (q_{i+1} - q_i)^2)`: the weight sits in the
  stiffness slot only, the kinetic slot is unweighted. Continuum reading: `w`
  is the sampled inverse spatial metric `h^{xx}(x)` (equivalently the local
  sound speed squared) of a STATIC background line element; that reading is
  interpretive commentary, not a theorem of this file.
* `HamW_one`: at `w = 1` the weighted generator IS the frozen-1 generator,
  as an equality of functions on phase space.
* `bracket_HamW_HamW` (headline): the exact lattice identity
  `{H_w[N], H_w[M]} = sum_j (N_j M_{j+1} - M_j N_{j+1}) * w_j *
  (pi_{j+1} (q_{j+1} - q_j))`. Two w-weighted Hamiltonian deformations close
  on a D-type (shift) generator whose smearing is the discrete lapse
  Wronskian multiplied by the background weight: the structure function of
  this bracket is `w`, appearing linearly (w-weighted, not w^2-weighted; the
  kinetic slot carries no weight, so exactly one factor of `w` survives the
  Kronecker collapse).
* `bracket_HamW_HamW_one`: substituting `w = 1` literally reproduces the
  proved frozen-1 statement `bracket_Ham_Ham`, via `HamW_one`.
* `weightedStructureSum_tendsto` (bonus): the h-scaled w-weighted structure
  smearing sums converge to the continuum integral, by direct consumption of
  `Analysis.weightedLatticeSum_tendsto` from the quadrature toolkit.

## Conventions (preregistered by the formulation panel)

* Point-split density: the closure density on the right of
  `bracket_HamW_HamW` is point-split, momentum at site `j + 1` and field
  gradient on the cell `(j, j + 1)`; the weight `w_j` sits at the LEFT point
  of the split pair. At `w = 1` the placement is invisible; here it is part
  of the exact statement and is disclosed rather than symmetrized.
* h-scaling: sites sample the unit interval at spacing `h = 1/N` with `q`,
  `pi`, `N`, `M`, `w` all sampled O(1). For C^1 lapse profiles the discrete
  lapse Wronskian `N_j M_{j+1} - M_j N_{j+1}` tends to
  `h * (N M' - M N')(x_j)`, and for a C^1 field profile the gradient factor
  `q_{j+1} - q_j` contributes the second `h`; the normalized closure-density
  profile is therefore `pi_{j+1} (q_{j+1} - q_j) / h`, and the bracket sum is
  a Riemann sum with one explicit h-factor from the Wronskian, finite and
  nonzero in the limit with NO further rescaling of `Dgen` or `Ham`. In
  `weightedStructureSum_tendsto` the continuum Wronskian profile is sampled
  directly, the `1/N` prefactor is exactly that Wronskian h-factor, and the
  density profile `S` is the normalized (per-h) shape, matching its own
  docstring.
* Positivity of `w` is the physical regime (nondegenerate background metric)
  but is NOT needed for any algebraic identity below, so no positivity
  hypothesis is imposed anywhere (no unused hypotheses).

## Status ledger

* MODEL: `HamW`, `HamWD` (definitional lattice discretizations, mirroring
  `Ham`, `HamD`).
* THEOREM (axiom-clean, no sorry, unconditional): `HamW_one`,
  `differentiable_HamW`, `pderivP_HamW`, `pderivQ_HamW`,
  `bracket_HamW_HamW`, `bracket_HamW_HamW_one`,
  `weightedStructureSum_tendsto` (the last with explicit `ContinuousOn`
  hypotheses, exactly as in the toolkit).
* OPEN (untouched here): phase-space-dependent structure function
  `g^{ab}[q]`; the full Dirac algebra continuum limit; HKT target
  inhabitation and `HKTRigidityStatement`; Jacobi for the fderiv bracket.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace WeightedHypersurfaceBracket

open HypersurfaceDeformation

noncomputable section

open Finset

variable {n : ℕ} [NeZero n]

/-- MODEL. The background-weighted smeared Hamiltonian
`H_w[N] = sum_i (N_i / 2) * (pi_i^2 + w_i * (q_{i+1} - q_i)^2)`.
The fixed background weight `w` sits in the stiffness (gradient) slot; the
kinetic slot is unweighted. `w` depends on the lattice site only, never on
the phase-space point: this is a BACKGROUND-w object. -/
def HamW (w N : ZMod n → ℝ) (x : PhaseSpace n) : ℝ :=
  ∑ i : ZMod n, (N i / 2) *
    (x.2 i * x.2 i + w i * ((x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i)))

/-- THEOREM (sanity anchor). At unit weight the weighted generator is the
frozen-1 generator of `HypersurfaceDeformation.lean`, as an equality of
functions on phase space. -/
theorem HamW_one (N : ZMod n → ℝ) : HamW (fun _ => 1) N = Ham N := by
  funext x
  unfold HamW Ham
  refine Finset.sum_congr rfl fun i _ => ?_
  show (N i / 2) *
      (x.2 i * x.2 i + 1 * ((x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i)))
      = (N i / 2) * (x.2 i * x.2 i + (x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i))
  ring

/-! ### Frechet derivative of the weighted generator

The fderiv chain of `HypersurfaceDeformation.lean` is fully generic in a
site-dependent scalar coefficient: the weight enters through one extra
`HasFDerivAt.const_mul`, and every Kronecker-collapse step goes through
unchanged. This answers the panel's w-genericity question affirmatively. -/

/-- The derivative of `HamW w N` at `x`, as an explicit continuous linear map. -/
def HamWD (w N : ZMod n → ℝ) (x : PhaseSpace n) : PhaseSpace n →L[ℝ] ℝ :=
  ∑ i : ZMod n,
    (N i / 2) • ((x.2 i • coordP i + x.2 i • coordP i)
      + w i • ((x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)
          + (x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)))

lemma hasFDerivAt_HamW (w N : ZMod n → ℝ) (x : PhaseSpace n) :
    HasFDerivAt (HamW w N) (HamWD w N x) x := by
  unfold HamW HamWD
  exact HasFDerivAt.fun_sum fun i _ =>
    ((((hasFDerivAt_coord_snd i x).mul (hasFDerivAt_coord_snd i x)).add
      ((((hasFDerivAt_coord_fst (i + 1) x).sub (hasFDerivAt_coord_fst i x)).mul
        ((hasFDerivAt_coord_fst (i + 1) x).sub (hasFDerivAt_coord_fst i x))).const_mul
          (w i))).const_mul (N i / 2))

/-- THEOREM. `HamW w N` is (unconditionally) differentiable. -/
theorem differentiable_HamW (w N : ZMod n → ℝ) :
    Differentiable ℝ (HamW (n := n) w N) :=
  fun x => (hasFDerivAt_HamW w N x).differentiableAt

/-! ### Partial derivatives (Kronecker collapse) -/

/-- THEOREM. The momentum partial of the weighted generator: the kinetic slot
is unweighted, so the weight does not appear. -/
theorem pderivP_HamW (w N : ZMod n → ℝ) (j : ZMod n) (x : PhaseSpace n) :
    pderivP (HamW w N) j x = N j * x.2 j := by
  rw [pderivP, (hasFDerivAt_HamW w N x).fderiv, HamWD, ContinuousLinearMap.sum_apply]
  have step : ∀ i : ZMod n,
      (((N i / 2) • ((x.2 i • coordP i + x.2 i • coordP i)
        + w i • ((x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)
            + (x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i))) :
          PhaseSpace n →L[ℝ] ℝ))
        ((0, Pi.single j 1) : PhaseSpace n)
      = (N i * x.2 i) * (if i = j then (1 : ℝ) else 0) := by
    intro i
    simp [Pi.single_apply]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => step i, sum_mul_ite]

/-- THEOREM. The configuration partial of the weighted generator: each
gradient term carries its own site weight. -/
theorem pderivQ_HamW (w N : ZMod n → ℝ) (j : ZMod n) (x : PhaseSpace n) :
    pderivQ (HamW w N) j x
      = N (j - 1) * (w (j - 1) * (x.1 j - x.1 (j - 1)))
        - N j * (w j * (x.1 (j + 1) - x.1 j)) := by
  rw [pderivQ, (hasFDerivAt_HamW w N x).fderiv, HamWD, ContinuousLinearMap.sum_apply]
  have step : ∀ i : ZMod n,
      (((N i / 2) • ((x.2 i • coordP i + x.2 i • coordP i)
        + w i • ((x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)
            + (x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i))) :
          PhaseSpace n →L[ℝ] ℝ))
        ((Pi.single j 1, 0) : PhaseSpace n)
      = (N i * (w i * (x.1 (i + 1) - x.1 i))) * (if i + 1 = j then (1 : ℝ) else 0)
        - (N i * (w i * (x.1 (i + 1) - x.1 i))) * (if i = j then (1 : ℝ) else 0) := by
    intro i
    simp [Pi.single_apply, mul_sub]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => step i, Finset.sum_sub_distrib,
    sum_mul_ite_add, sum_mul_ite]
  have e : j - 1 + 1 = j := by ring
  rw [e]

/-! ### The headline: exact weighted hypersurface-deformation relation -/

/-- THEOREM (headline; exact discrete weighted hypersurface deformation).
`{H_w[N], H_w[M]} = sum_j (N_j M_{j+1} - M_j N_{j+1}) * w_j *
(pi_{j+1} (q_{j+1} - q_j))`.

The bracket of two w-weighted Hamiltonian deformations is a D-type (shift)
generator: the point-split momentum density `pi_{j+1} (q_{j+1} - q_j)` smeared
by the discrete lapse Wronskian TIMES the background weight `w_j` at the left
split point. The weight appears exactly where the Dirac structure function
sits (in the continuum, `{H(N), H(M)} = D(g^{xx} (N M' - M N'))`), and it
appears LINEARLY: with the weight in the stiffness slot and the kinetic slot
unweighted, exactly one factor of `w` survives the Kronecker collapse, so the
answer is w-weighted, not w^2-weighted. Antisymmetric in `N, M` by
inspection; vanishes identically for `N = M`.

Honesty (panel lock): this is a BACKGROUND-w structure function, not a
phase-space-dependent inverse metric; it moves toward but does NOT flip
gap5_constraint_recovery; HKT rigidity is untouched and OPEN. -/
theorem bracket_HamW_HamW (w N M : ZMod n → ℝ) (x : PhaseSpace n) :
    bracket (HamW w N) (HamW w M) x
      = ∑ j : ZMod n, (N j * M (j + 1) - M j * N (j + 1))
          * (w j * (x.2 (j + 1) * (x.1 (j + 1) - x.1 j))) := by
  simp only [bracket, pderivQ_HamW, pderivP_HamW]
  have step1 : (∑ j : ZMod n,
      ((N (j - 1) * (w (j - 1) * (x.1 j - x.1 (j - 1)))
          - N j * (w j * (x.1 (j + 1) - x.1 j))) * (M j * x.2 j)
        - N j * x.2 j
          * (M (j - 1) * (w (j - 1) * (x.1 j - x.1 (j - 1)))
              - M j * (w j * (x.1 (j + 1) - x.1 j)))))
      = ∑ j : ZMod n,
          (N (j - 1) * M j - M (j - 1) * N j)
            * (w (j - 1) * (x.2 j * (x.1 j - x.1 (j - 1)))) :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [step1]
  refine sum_reindex 1
    (fun k => (N (k - 1) * M k - M (k - 1) * N k)
      * (w (k - 1) * (x.2 k * (x.1 k - x.1 (k - 1))))) _ fun j => ?_
  have e1 : j + 1 - 1 = j := by ring
  simp only [e1]

/-- THEOREM (frozen-1 recovery). Substituting the unit weight into the
weighted bracket literally reproduces the proved frozen-1 statement
`bracket_Ham_Ham`: the weighted theorem is an honest generalization, not a
parallel construction. Proof: rewrite by `HamW_one` and apply the existing
theorem. -/
theorem bracket_HamW_HamW_one (N M : ZMod n → ℝ) (x : PhaseSpace n) :
    bracket (HamW (fun _ => 1) N) (HamW (fun _ => 1) M) x
      = ∑ j : ZMod n, (N j * M (j + 1) - M j * N (j + 1))
          * (x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) := by
  rw [HamW_one, HamW_one, bracket_Ham_Ham]

end

/-! ### Bonus: continuum limit of the weighted structure smearing

Genuine consumption of the quadrature toolkit
(`IndisputableMonolith/Gravity/Analysis/QuadratureLimit.lean`), which was
built for exactly this consumer. -/

open Filter in
/-- THEOREM (weighted structure smearing, continuum limit). Sample a
background weight profile `W`, a continuum lapse-Wronskian profile `Wr`
(the limit shape of `(N_j M_{j+1} - M_j N_{j+1}) / h`), and a closure-density
profile `S` (the limit shape of the point-split density
`pi_{j+1} (q_{j+1} - q_j) / h`, one factor of `h` absorbed by the gradient),
all continuous on `[0, 1]`. Then the h-scaled w-weighted structure sums of
`bracket_HamW_HamW` converge:
`(1/N) * sum_{k<N} W(k/N) * (Wr(k/N) * S(k/N)) -> integral_0^1 W * (Wr * S)`.

h-scaling convention (stated per panel preregistration): the explicit `1/N`
prefactor is the single factor of lattice spacing carried by the discrete
lapse Wronskian; the sampled profiles are all O(1). This is a limit of the
SMEARING SHAPE with continuum profiles sampled directly; it is not a proof
that the discrete Wronskian of sampled lapses converges at rate h (that needs
C^1 data and is left OPEN with the full Dirac continuum limit). Direct
application of `Analysis.weightedLatticeSum_tendsto`. -/
theorem weightedStructureSum_tendsto (W Wr S : ℝ → ℝ)
    (hW : ContinuousOn W (Set.Icc 0 1)) (hWr : ContinuousOn Wr (Set.Icc 0 1))
    (hS : ContinuousOn S (Set.Icc 0 1)) :
    Filter.Tendsto
      (fun N : ℕ => (1 / (N : ℝ)) * ∑ k ∈ Finset.range N,
        W ((k : ℝ) / (N : ℝ)) * (Wr ((k : ℝ) / (N : ℝ)) * S ((k : ℝ) / (N : ℝ))))
      Filter.atTop (nhds (∫ x in (0:ℝ)..1, W x * (Wr x * S x))) := by
  have h := Analysis.weightedLatticeSum_tendsto (fun x => Wr x * S x) W
    (hWr.mul hS) hW
  have hint : (∫ x in (0:ℝ)..1, (Wr x * S x) * W x)
      = ∫ x in (0:ℝ)..1, W x * (Wr x * S x) :=
    intervalIntegral.integral_congr fun x _ => mul_comm _ _
  rw [hint] at h
  refine h.congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  show Wr ((k : ℝ) / (N : ℝ)) * S ((k : ℝ) / (N : ℝ)) * W ((k : ℝ) / (N : ℝ))
      = W ((k : ℝ) / (N : ℝ)) * (Wr ((k : ℝ) / (N : ℝ)) * S ((k : ℝ) / (N : ℝ)))
  ring

/-! ### Axiom receipts (expected: [propext, Classical.choice, Quot.sound]) -/

#print axioms HamW_one
#print axioms differentiable_HamW
#print axioms pderivP_HamW
#print axioms pderivQ_HamW
#print axioms bracket_HamW_HamW
#print axioms bracket_HamW_HamW_one
#print axioms weightedStructureSum_tendsto

end WeightedHypersurfaceBracket
end SevenGaps
end Gravity
end IndisputableMonolith
