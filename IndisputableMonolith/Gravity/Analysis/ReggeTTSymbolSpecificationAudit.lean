import IndisputableMonolith.Gravity.Analysis.ReggeTTSymbolPreflight

/-!
# Regge TT symbol specification audit: scaling well-posedness of the `-1/4` target

QG full-theory campaign, `ReggeTTContinuumSymbol` program, Crux-1(c) lane,
Gate A0 of the panel-locked protocol "Normalization-Gated Schläfli Two-Jet".

## What this gate decides

The OPEN target `ReggeTTContinuumIsotropyTarget` claims a FIXED value
`-(1/4)` for the continuum TT Bloch symbol on every TT polarization.  A
fixed numerical value is meaningful only if the statement cannot be
rescaled into a contradiction: the plane-wave family
`ℓ_e(t) = ℓ²_flat + t · c_d(E) · cos(k·x_mid)` is linear in the
polarization matrix `E` through the edge-class coefficient
`c_d(E) = Σ_ij E_ij D_d^i D_d^j`, so replacing `E ↦ c·E` reparametrizes
the SAME family (`t ↦ c·t`), and the second-difference quadratic form must
scale by `c²`.  This module kernel-checks exactly that scaling chain and
the normalization pin that makes the fixed-value statement well-posed.

## Convention-consistency audit (documentation record, checked by hand
against the kernel definitions in `ReggeTTSymbolPreflight`)

* `polEdgeCoeff E d = Σ_{i,j} E_ij · D_d^i · D_d^j` sums over ALL ordered
  index pairs, so for symmetric `E` each off-diagonal pair `(i,j) ≠ (j,i)`
  contributes twice.  This is the standard quadratic-form convention
  `D^T E D`.
* The Frobenius normalization in `IsTTPolarization` (fourth conjunct,
  `Σ_{i,j} E_ij · E_ij = 1`) likewise sums over ALL ordered pairs.
* The C10 numerics probe (`state/qg_full_theory/true_regge_tt_probe/`,
  commit f1d44266e5) used these same two conventions (background record;
  NUMERICAL EVIDENCE, never proof).
* Conclusion of the audit: the two double-counting conventions are
  CONSISTENT with each other; no mismatch was found, so the lane
  proceeds.  The kernel content below shows the target statement is
  scaling-coherent: the symbol value scales as `c²` under `E ↦ c·E`
  (`TTBlochSymbolIs_smul`), and `IsTTPolarization` pins the Frobenius
  norm so the only rescalings preserving the hypothesis class are
  `c² = 1` (`isTTPolarization_smul_iff`), under which `c²·H = H`.  Hence
  quantifying a FIXED value over `IsTTPolarization` is well-posed, while
  an unnormalized fixed-value claim would be contradictory.

## Tier tags

* THEOREM: every named result in this file (kernel-checked; no sorry, no
  admit, no new axioms, no `native_decide`, no `: True` shells).  All
  results here are pure algebra/topology over the preflight definitions
  and carry the standard axiom footprint
  `[propext, Classical.choice, Quot.sound]` (they do not touch the
  certified angle-sum chain, so no `Lean.ofReduceBool`/`Lean.trustCompiler`).
* No claim about the VALUE `-1/4` is made or implied anywhere here; the
  continuum target stays OPEN and its status flag stays `false`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTSymbolSpecificationAudit

open ReggeTTSymbolPreflight

noncomputable section

variable (N : ℕ) [NeZero N]

/-! ## §1. Scaling of the edge-class coefficient (Gate A0(a)) -/

/-- (a) THEOREM: the edge-class coefficient is linear in the polarization,
entrywise-scaling form. -/
theorem polEdgeCoeff_mul_left (c : ℝ) (E : Fin 3 → Fin 3 → ℝ) (d : Fin 7) :
    polEdgeCoeff (fun i j => c * E i j) d = c * polEdgeCoeff E d := by
  unfold polEdgeCoeff
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The scalar action on polarization matrices is entrywise. -/
theorem smul_polarization_apply (c : ℝ) (E : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    (c • E) i j = c * E i j := rfl

/-- (a) THEOREM, `•` form: `polEdgeCoeff (c • E) d = c * polEdgeCoeff E d`. -/
theorem polEdgeCoeff_smul (c : ℝ) (E : Fin 3 → Fin 3 → ℝ) (d : Fin 7) :
    polEdgeCoeff (c • E) d = c * polEdgeCoeff E d := by
  have h : (c • E) = fun i j => c * E i j := rfl
  rw [h]
  exact polEdgeCoeff_mul_left c E d

/-! ## §2. Scaling of the plane-wave family (Gate A0(b)) -/

/-- (b) THEOREM: rescaling the polarization by `c` reparametrizes the SAME
plane-wave edge-field family by `t ↦ c·t`.  This is the exact sense in
which the polarization normalization and the amplitude normalization are
one and the same gauge. -/
theorem planeWaveEdgeField_smul (c : ℝ) (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) (t : ℝ) :
    planeWaveEdgeField N (c • E) k t = planeWaveEdgeField N E k (c * t) := by
  funext e
  simp only [planeWaveEdgeField, polEdgeCoeff_smul]
  ring

/-- (b) corollary: the action profile of the rescaled polarization is the
original profile at the rescaled amplitude. -/
theorem planeWaveActionProfile_smul (c : ℝ) (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) (t : ℝ) :
    planeWaveActionProfile N (c • E) k t =
      planeWaveActionProfile N E k (c * t) := by
  unfold planeWaveActionProfile
  rw [planeWaveEdgeField_smul]

/-! ## §3. Quadratic scaling of the second-difference form (Gate A0(c)) -/

/-- (c) THEOREM: under `E ↦ c·E` the second-difference quadratic form
scales QUADRATICALLY, `D_{cE}(t) = c² · D_E(c·t)`.  This is the kernel
fact that makes any unnormalized "fixed `-1/4`" claim contradictory: the
same physical family would have to report both `H` and `c²·H`. -/
theorem ttSecondDifference_smul {c t : ℝ} (hc : c ≠ 0) (ht : t ≠ 0)
    (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ) :
    ttSecondDifference N (c • E) k t =
      c ^ 2 * ttSecondDifference N E k (c * t) := by
  have hN : ((N : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold ttSecondDifference
  simp only [planeWaveActionProfile_smul, mul_zero, mul_neg]
  field_simp

/-! ## §4. Scaling of the Bloch symbol value predicate (Gate A0(d)) -/

/-- Multiplication by a nonzero constant maps the punctured neighborhood
filter of `0` to itself. -/
theorem tendsto_const_mul_punctured {c : ℝ} (hc : c ≠ 0) :
    Filter.Tendsto (fun t : ℝ => c * t)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
  have h1 : Filter.Tendsto (fun t : ℝ => c * t) (nhds 0) (nhds 0) := by
    simpa using (continuous_const.mul continuous_id).tendsto (0 : ℝ)
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (h1.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  exact mul_ne_zero hc ht'

/-- One direction of (d): if the symbol value at `E` is `H`, the symbol
value at `c • E` is `c² · H`. -/
theorem TTBlochSymbolIs_smul_of {c : ℝ} (hc : c ≠ 0)
    (E : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℤ) (H : ℝ)
    (h : TTBlochSymbolIs N E m H) :
    TTBlochSymbolIs N (c • E) m (c ^ 2 * H) := by
  unfold TTBlochSymbolIs at h ⊢
  have hcomp := h.comp (tendsto_const_mul_punctured hc)
  have hmul := hcomp.const_mul (c ^ 2)
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  exact (ttSecondDifference_smul N hc ht' E (commensurateMomentum N m)).symm

/-- (d) THEOREM: the Bloch symbol value predicate transforms exactly
quadratically under polarization rescaling, as an equivalence.  Any
well-posed fixed-value target must therefore fix the polarization
normalization; `IsTTPolarization` does (§5). -/
theorem TTBlochSymbolIs_smul {c : ℝ} (hc : c ≠ 0)
    (E : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℤ) (H : ℝ) :
    TTBlochSymbolIs N E m H ↔ TTBlochSymbolIs N (c • E) m (c ^ 2 * H) := by
  constructor
  · exact TTBlochSymbolIs_smul_of N hc E m H
  · intro h
    have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
    have h' := TTBlochSymbolIs_smul_of N hc' (c • E) m (c ^ 2 * H) h
    have hE : c⁻¹ • c • E = E := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hH : (c⁻¹) ^ 2 * (c ^ 2 * H) = H := by
      field_simp
    rwa [hE, hH] at h'

/-! ## §5. The normalization pin and statement well-posedness (Gate A0(e)) -/

/-- Frobenius square-sum of a polarization matrix (ordered-pair
convention, matching both `polEdgeCoeff` and `IsTTPolarization`). -/
def frobeniusSq (E : Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, E i j * E i j

/-- (e), pin re-export: `IsTTPolarization` pins the Frobenius square-sum
to `1` (fourth conjunct of the definition). -/
theorem isTTPolarization_frobenius_pinned (m : Fin 3 → ℤ)
    (E : Fin 3 → Fin 3 → ℝ) (h : IsTTPolarization m E) :
    frobeniusSq E = 1 :=
  h.2.2.2

/-- The Frobenius square-sum scales quadratically under `E ↦ c·E`. -/
theorem frobeniusSq_smul (c : ℝ) (E : Fin 3 → Fin 3 → ℝ) :
    frobeniusSq (c • E) = c ^ 2 * frobeniusSq E := by
  unfold frobeniusSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (c * E i j) * (c * E i j) = c ^ 2 * (E i j * E i j)
  ring

/-- (e) THEOREM, the pin is real: starting from a TT polarization `E`, the
rescaled matrix `c • E` remains a TT polarization exactly when `c² = 1`.
Symmetry, tracelessness, and transversality survive every rescaling; the
Frobenius pin is the ONLY normalization-fixing clause, and it works. -/
theorem isTTPolarization_smul_iff (m : Fin 3 → ℤ)
    (E : Fin 3 → Fin 3 → ℝ) (c : ℝ) (h : IsTTPolarization m E) :
    IsTTPolarization m (c • E) ↔ c ^ 2 = 1 := by
  obtain ⟨hsym, htr, htrans, hfrob⟩ := h
  constructor
  · intro hcE
    have hpin := hcE.2.2.2
    have hfrob' : frobeniusSq (c • E) = 1 := hpin
    rw [frobeniusSq_smul] at hfrob'
    have hfrobE : frobeniusSq E = 1 := hfrob
    rw [hfrobE, mul_one] at hfrob'
    exact hfrob'
  · intro hc2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j
      show c * E i j = c * E j i
      rw [hsym i j]
    · show (∑ i : Fin 3, c * E i i) = 0
      rw [← Finset.mul_sum, htr, mul_zero]
    · intro j
      show (∑ i : Fin 3, (m i : ℝ) * (c * E i j)) = 0
      calc (∑ i : Fin 3, (m i : ℝ) * (c * E i j))
          = c * ∑ i : Fin 3, (m i : ℝ) * E i j := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [htrans j, mul_zero]
    · have h1 : frobeniusSq (c • E) = c ^ 2 * frobeniusSq E :=
        frobeniusSq_smul c E
      have h2 : frobeniusSq E = 1 := hfrob
      show frobeniusSq (c • E) = 1
      rw [h1, h2, hc2, mul_one]

/-- **GATE A0 VERDICT (THEOREM): the `-1/4` target statement is
well-posed under the `polEdgeCoeff` scaling convention.**

The three clauses, all kernel-checked, assemble the well-posedness
argument:

1. (pin) every `E` in the target's hypothesis class `IsTTPolarization`
   has Frobenius square-sum exactly `1`;
2. (quadratic scaling) the Bloch symbol value transforms as `H ↦ c²·H`
   under `E ↦ c·E`, so WITHOUT a normalization the fixed-value claim
   would be contradictory (the same family would report `H` and `c²·H`);
3. (pin bites) the only rescalings that stay inside the hypothesis class
   are `c² = 1`, and for those `c²·H = H` — the reported value is
   invariant on the quantified class.

Hence `ReggeTTContinuumIsotropyTarget`, which quantifies over
`IsTTPolarization` (pin included), assigns a scaling-coherent meaning to
the fixed constant `reggeTTContinuumCoefficient = -(1/4)`.  Nothing here
proves (or evidences) that the value IS `-1/4`; that target remains OPEN
with status flag `false`. -/
theorem reggeTT_target_scaling_wellPosed {c : ℝ} (hc : c ≠ 0)
    (m : Fin 3 → ℤ) (E : Fin 3 → Fin 3 → ℝ) (H : ℝ)
    (hE : IsTTPolarization m E) :
    frobeniusSq E = 1 ∧
      (TTBlochSymbolIs N E m H ↔ TTBlochSymbolIs N (c • E) m (c ^ 2 * H)) ∧
      (IsTTPolarization m (c • E) ↔ c ^ 2 = 1) :=
  ⟨isTTPolarization_frobenius_pinned m E hE,
    TTBlochSymbolIs_smul N hc E m H,
    isTTPolarization_smul_iff m E c hE⟩

end

end ReggeTTSymbolSpecificationAudit
end Analysis
end Gravity
end IndisputableMonolith
