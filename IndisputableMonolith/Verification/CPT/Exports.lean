import IndisputableMonolith.Verification.CPT.Core
import IndisputableMonolith.Verification.CPT.WindowIdentifiability
import IndisputableMonolith.Verification.CPT.Pipeline
import IndisputableMonolith.Verification.CPT.Optimality
import IndisputableMonolith.Verification.CPT.ForcedFactorization
import IndisputableMonolith.Verification.CPT.RankCertification
import IndisputableMonolith.Verification.CPT.EpsilonCertification

/-!
# CPT Export Surface

Citation-friendly theorem aliases for the CPT formalization layer.
All items are fully proved (no `sorry`, no new `axiom`).

Paper-to-Lean mapping:
- `WINDOW_*`        ← paper Thm. 4.5 / 6.5 (window identifiability family)
- `CPT_PIPELINE_*`  ← paper P→B→A pipeline (§5 / §6 composition)
- `CPT_OPT_*`       ← paper Thm. 6.11 (domination / optimality)
- `CPT_FACTOR_*`    ← paper Thm. 5.1 (forced factorisation)
- `CPT_EPS_*`       ← paper ε-noise layer (§5 ε-optimal certification)
-/

namespace IndisputableMonolith
namespace Verification
namespace CPT
namespace Exports

-- ───────────────────────────────────────────────────────────────
-- Window Identifiability (paper Thm. 4.5 / 6.5)
-- ───────────────────────────────────────────────────────────────

/-- Identifiability ↔ trivial kernel (paper Thm. 6.5). -/
theorem WINDOW_identifiable_iff_trivialKernel
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    WindowIdentifiability.Identifiable A ↔ WindowIdentifiability.TrivialKernel A :=
  WindowIdentifiability.identifiable_iff_trivialKernel A

/-- Identifiability ↔ full column rank (paper Thm. 4.5). -/
theorem WINDOW_identifiable_iff_fullColumnRank
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    WindowIdentifiability.Identifiable A ↔ WindowIdentifiability.FullColumnRank A :=
  WindowIdentifiability.identifiable_iff_fullColumnRank A

/-- Zero-detection under identifiability. -/
theorem WINDOW_zero_detection_of_identifiable
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hI : WindowIdentifiability.Identifiable A) (v : Fin n → ℝ)
    (hv : A.mulVec v = 0) : v = 0 :=
  WindowIdentifiability.zero_detection_of_identifiable A hI v hv

-- ───────────────────────────────────────────────────────────────
-- Unified P→B→A Pipeline (paper §5/§6)
-- ───────────────────────────────────────────────────────────────

/-- Pipeline is definitionally equal to A ∘ B ∘ P (paper §5). -/
theorem CPT_PIPELINE_factorization
    {X Y Z : Type}
    (P : Pipeline.ProjectionStage X Y)
    (B : Pipeline.CoercivityStage Y Z)
    (A : Pipeline.AggregationStage Z) :
    Pipeline.PhiStar P B A = A.run ∘ B.run ∘ P.run :=
  Pipeline.pipeline_factorization P B A

/-- Zero-decision soundness of the composed pipeline. -/
theorem CPT_PIPELINE_sound
    {X Y Z : Type}
    (P : Pipeline.ProjectionStage X Y)
    (B : Pipeline.CoercivityStage Y Z)
    (A : Pipeline.AggregationStage Z)
    (membership : X → Prop)
    (hzero : ∀ x, Pipeline.PhiStar P B A x = DecisionTag.zero → membership x) :
    ∀ x, Pipeline.PhiStar P B A x = DecisionTag.zero → membership x :=
  Pipeline.pipeline_sound P B A membership hzero

/-- Nonzero-decision soundness of the composed pipeline. -/
theorem CPT_PIPELINE_nonzero_sound
    {X Y Z : Type}
    (P : Pipeline.ProjectionStage X Y)
    (B : Pipeline.CoercivityStage Y Z)
    (A : Pipeline.AggregationStage Z)
    (excluded : X → Prop)
    (hnonzero : ∀ x, Pipeline.PhiStar P B A x = DecisionTag.nonzero → excluded x) :
    ∀ x, Pipeline.PhiStar P B A x = DecisionTag.nonzero → excluded x :=
  Pipeline.pipeline_nonzero_sound P B A excluded hnonzero

-- ───────────────────────────────────────────────────────────────
-- Domination / Optimality (paper Thm. 6.11)
-- ───────────────────────────────────────────────────────────────

/-- PhiStar dominates any agreeing procedure on the class (paper Thm. 6.11). -/
theorem CPT_OPT_phiStar_dominates
    {X Y Z : Type}
    (P : Pipeline.ProjectionStage X Y)
    (B : Pipeline.CoercivityStage Y Z)
    (A : Pipeline.AggregationStage Z)
    (C : Set X) (Ψ : Procedure X)
    (hPsiResolve : Optimality.ResolvesClass C Ψ)
    (hAgree : ∀ ⦃x : X⦄, x ∈ C → Pipeline.PhiStar P B A x = Ψ x) :
    dominatesOn C (Pipeline.PhiStar P B A) Ψ :=
  Optimality.phiStar_dominates P B A C Ψ hPsiResolve hAgree

/-- Global class (`Set.univ`) domination specialization. -/
theorem CPT_OPT_phiStar_dominates_global
    {X Y Z : Type}
    (P : Pipeline.ProjectionStage X Y)
    (B : Pipeline.CoercivityStage Y Z)
    (A : Pipeline.AggregationStage Z)
    (Ψ : Procedure X)
    (hPsiResolve : Optimality.ResolvesClass (Set.univ : Set X) Ψ)
    (hAgreeGlobal : ∀ x : X, Pipeline.PhiStar P B A x = Ψ x) :
    dominatesOn (Set.univ : Set X) (Pipeline.PhiStar P B A) Ψ :=
  Optimality.phiStar_dominates_global P B A Ψ hPsiResolve hAgreeGlobal

-- ───────────────────────────────────────────────────────────────
-- Forced Factorisation (paper Thm. 5.1)
-- ───────────────────────────────────────────────────────────────

/-- Monotone reparametrization exists under certificate hypotheses (paper Thm. 5.1 step 1). -/
theorem CPT_FACTOR_exists_monotone_reparam
    {S O : Type}
    (R : ForcedFactorization.RatioCostSpace S O)
    (C : S → O → ℝ)
    (h : ForcedFactorization.CertificateHypotheses R C) :
    ∃ φ : ForcedFactorization.RatioCostSpace.CostCode R → ℝ,
      (∀ s o, C s o = φ ⟨R.canonicalCost s o, ⟨(s, o), rfl⟩⟩)
      ∧
      (∀ s o1 o2,
          R.canonicalCost s o1 ≤ R.canonicalCost s o2 →
          φ ⟨R.canonicalCost s o1, ⟨(s, o1), rfl⟩⟩
            ≤
          φ ⟨R.canonicalCost s o2, ⟨(s, o2), rfl⟩⟩) :=
  ForcedFactorization.exists_monotone_reparam R C h

/-- State-independence under explicit rigidity hypothesis (paper Thm. 5.1 rigidity step). -/
theorem CPT_FACTOR_phi_independent_of_state
    {S O : Type} [Inhabited S]
    (R : ForcedFactorization.RatioCostSpace S O)
    (C : S → O → ℝ)
    (hRig : ForcedFactorization.RigidityHypotheses R C) :
    ∃ ψ : O → ℝ, ∀ s o, C s o = ψ o :=
  ForcedFactorization.phi_independent_of_state R C hRig

/-- Assembled forced-factorization theorem (paper Thm. 5.1). -/
theorem CPT_FACTOR_forced_factorization
    {S O : Type} [Inhabited S]
    (R : ForcedFactorization.RatioCostSpace S O)
    (C : S → O → ℝ)
    (h : ForcedFactorization.CertificateHypotheses R C)
    (hRig : ForcedFactorization.RigidityHypotheses R C) :
    (∃ φ : ForcedFactorization.RatioCostSpace.CostCode R → ℝ,
        (∀ s o, C s o = φ ⟨R.canonicalCost s o, ⟨(s, o), rfl⟩⟩))
    ∧
    (∃ ψ : O → ℝ, ∀ s o, C s o = ψ o) := by
  rcases ForcedFactorization.exists_monotone_reparam R C h with ⟨φ, hrepr, _⟩
  rcases ForcedFactorization.phi_independent_of_state R C hRig with ⟨ψ, hψ⟩
  exact ⟨⟨φ, hrepr⟩, ⟨ψ, hψ⟩⟩

/-- Strong forced-factorization form with uniqueness on both layers:
unique cost-image reparametrization + unique state-free profile. -/
theorem CPT_FACTOR_forced_factorization_unique
    {S O : Type} [Inhabited S]
    (R : ForcedFactorization.RatioCostSpace S O)
    (C : S → O → ℝ)
    (h : ForcedFactorization.CertificateHypotheses R C)
    (hRig : ForcedFactorization.RigidityHypotheses R C) :
    (∃! φ : ForcedFactorization.RatioCostSpace.CostCode R → ℝ,
        ∀ s o, C s o = φ ⟨R.canonicalCost s o, ⟨(s, o), rfl⟩⟩)
    ∧
    (∃! ψ : O → ℝ, ∀ s o, C s o = ψ o) :=
  ForcedFactorization.forced_factorization_unique R C h hRig

/-- Uniqueness theorem from primitive ratio-level assumptions
    (derives the H1/H2 bundle internally). -/
theorem CPT_FACTOR_forced_factorization_unique_of_primitives
    {S O : Type} [Inhabited S]
    (R : ForcedFactorization.RatioCostSpace S O)
    (C : S → O → ℝ)
    (hPrim : ForcedFactorization.PrimitiveCertificateHypotheses R C)
    (hRigPrim : ForcedFactorization.PrimitiveRigidityHypotheses R) :
    (∃! φ : ForcedFactorization.RatioCostSpace.CostCode R → ℝ,
        ∀ s o, C s o = φ ⟨R.canonicalCost s o, ⟨(s, o), rfl⟩⟩)
    ∧
    (∃! ψ : O → ℝ, ∀ s o, C s o = ψ o) :=
  ForcedFactorization.forced_factorization_unique_of_primitives R C hPrim hRigPrim

-- ───────────────────────────────────────────────────────────────
-- General (d,W) Rank Certification
-- ───────────────────────────────────────────────────────────────

/-- Vandermonde determinant is nonzero for distinct nodes. -/
theorem RANK_vandermonde_det_ne_zero
    {n : ℕ} (v : Fin n → ℝ)
    (hDistinct : RankCertification.DistinctNodes v) :
    (Matrix.vandermonde v).det ≠ 0 :=
  RankCertification.vandermonde_det_ne_zero v hDistinct

/-- Hankel matrix of an exponential sum with distinct nodes and nonzero amplitudes
    has nonzero determinant. -/
theorem RANK_hankel_det_ne_zero
    {d : ℕ} (E : RankCertification.ExponentialSumData d) :
    (RankCertification.hankelMatrix E).det ≠ 0 :=
  RankCertification.hankel_det_ne_zero E

/-- **General (d,W) rank certification**: For any d ≥ 1 and W ≥ 1 with an
    exponential-sum witness, the Hankel matrix is nonsingular, witnessing
    nonemptiness of the identifiability locus Ω_{d,W}. -/
theorem RANK_identifiability_locus_nonempty
    (d : ℕ) (W : ℕ) (_hd : 0 < d) (_hW : 0 < W)
    (E : RankCertification.ExponentialSumData d) :
    (RankCertification.hankelMatrix E).det ≠ 0 :=
  RankCertification.identifiability_locus_nonempty d W _hd _hW E

-- ───────────────────────────────────────────────────────────────
-- Epsilon / Noise Layer
-- ───────────────────────────────────────────────────────────────

/-- Perturbed argmin (`cHat`) is `2ε`-optimal for true cost (`c`)
under uniform absolute error `|cHat-c| ≤ ε`. -/
theorem CPT_EPS_approx_argmin_stability
    {O : Type}
    (c cHat : O → ℝ) (ε : ℝ)
    (hErr : ∀ o, |cHat o - c o| ≤ ε)
    (oHat : O)
    (hMin : ∀ o, cHat oHat ≤ cHat o) :
    ∀ o, c oHat ≤ c o + 2 * ε :=
  EpsilonCertification.approx_argmin_stability c cHat ε hErr oHat hMin

/-- Set-level form: perturbed minimizer lies in `MeanEps c (2ε)`. -/
theorem CPT_EPS_approx_argmin_mem_meanEps
    {O : Type}
    (c cHat : O → ℝ) (ε : ℝ)
    (hErr : ∀ o, |cHat o - c o| ≤ ε)
    (oHat : O)
    (hMin : ∀ o, cHat oHat ≤ cHat o) :
    oHat ∈ EpsilonCertification.MeanEps c (2 * ε) :=
  EpsilonCertification.approx_argmin_mem_meanEps c cHat ε hErr oHat hMin

end Exports
end CPT
end Verification
end IndisputableMonolith
