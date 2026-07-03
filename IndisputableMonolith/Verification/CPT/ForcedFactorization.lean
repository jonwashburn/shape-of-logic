import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Verification.CPT.Core

/-!
# CPT Forced Factorization (Hypothesis-Explicit Lean Layer)

This module captures the strongest currently defensible Lean shape for the paper's
forced-factorization claims:

- ratio-induced canonical cost scaffold,
- certificate hypotheses stated explicitly,
- existence of a reparametrization on the realized cost image,
- state-independence only under an explicit rigidity hypothesis.

No hidden assumptions are used.
-/

namespace IndisputableMonolith
namespace Verification
namespace CPT
namespace ForcedFactorization

open scoped Classical

variable {S O : Type}

/-- Ratio-cost scaffold used by CPT factorization statements. -/
structure RatioCostSpace (S O : Type) where
  iotaS : S → ℝ
  iotaO : O → ℝ
  iotaS_pos : ∀ s : S, 0 < iotaS s
  iotaO_pos : ∀ o : O, 0 < iotaO o

namespace RatioCostSpace

/-- Ratio coordinate entering the canonical reciprocal cost. -/
noncomputable def ratio (R : RatioCostSpace S O) (s : S) (o : O) : ℝ :=
  R.iotaS s / R.iotaO o

/-- Canonical ratio-induced cost used in CPT factorization arguments. -/
noncomputable def canonicalCost (R : RatioCostSpace S O) (s : S) (o : O) : ℝ :=
  IndisputableMonolith.Cost.Jcost (ratio R s o)

/-- Realized image of the canonical cost on `S × O`. -/
def CostImage (R : RatioCostSpace S O) : Set ℝ :=
  Set.range (fun p : S × O => canonicalCost R p.1 p.2)

/-- Encoded realized-cost coordinate used for reparametrization witnesses. -/
abbrev CostCode (R : RatioCostSpace S O) := {t : ℝ // t ∈ CostImage R}

end RatioCostSpace

open RatioCostSpace

/-- Explicit assumptions used for the factorization and monotone reparametrization layer. -/
structure CertificateHypotheses
    (R : RatioCostSpace S O) (C : S → O → ℝ) : Prop where
  /-- Ratio-level dependence: equal ratio coordinate implies equal certificate value. -/
  depends_on_ratio :
    ∀ {s1 s2 : S} {o1 o2 : O},
      ratio R s1 o1 = ratio R s2 o2 → C s1 o1 = C s2 o2
  /-- Cost-level dependence (stronger; used for image reparametrization existence). -/
  depends_on_cost :
    ∀ {s1 s2 : S} {o1 o2 : O},
      canonicalCost R s1 o1 = canonicalCost R s2 o2 → C s1 o1 = C s2 o2
  /-- Monotonicity in the canonical cost ordering for fixed `s`. -/
  monotone_in_cost :
    ∀ (s : S) (o1 o2 : O),
      canonicalCost R s o1 ≤ canonicalCost R s o2 → C s o1 ≤ C s o2

/-- Explicit rigidity bundle used to force independence from the state variable. -/
structure RigidityHypotheses
    (R : RatioCostSpace S O) (C : S → O → ℝ) : Prop where
  independent_of_state : ∀ (s1 s2 : S) (o : O), C s1 o = C s2 o

/-- More primitive hypothesis bundle for the cost-reparametrization layer.
`depends_on_cost` is derived from ratio-level dependence plus a cost-to-ratio bridge. -/
structure PrimitiveCertificateHypotheses
    (R : RatioCostSpace S O) (C : S → O → ℝ) : Prop where
  depends_on_ratio :
    ∀ {s1 s2 : S} {o1 o2 : O},
      ratio R s1 o1 = ratio R s2 o2 → C s1 o1 = C s2 o2
  ratio_of_cost_eq :
    ∀ {s1 s2 : S} {o1 o2 : O},
      canonicalCost R s1 o1 = canonicalCost R s2 o2 →
        ratio R s1 o1 = ratio R s2 o2
  monotone_in_cost :
    ∀ (s : S) (o1 o2 : O),
      canonicalCost R s o1 ≤ canonicalCost R s o2 → C s o1 ≤ C s o2

/-- Primitive rigidity hypothesis phrased at ratio level:
for fixed `o`, ratios collapse across states. -/
structure PrimitiveRigidityHypotheses
    (R : RatioCostSpace S O) : Prop where
  ratio_state_collapse : ∀ (s1 s2 : S) (o : O), ratio R s1 o = ratio R s2 o

theorem primitive_to_certificate
    (R : RatioCostSpace S O) (C : S → O → ℝ)
    (hPrim : PrimitiveCertificateHypotheses R C) :
    CertificateHypotheses R C := by
  refine
    { depends_on_ratio := hPrim.depends_on_ratio
      depends_on_cost := ?_
      monotone_in_cost := hPrim.monotone_in_cost }
  intro s1 s2 o1 o2 hCost
  exact hPrim.depends_on_ratio (hPrim.ratio_of_cost_eq hCost)

theorem primitive_to_rigidity
    (R : RatioCostSpace S O) (C : S → O → ℝ)
    (hPrim : PrimitiveCertificateHypotheses R C)
    (hRigPrim : PrimitiveRigidityHypotheses R) :
    RigidityHypotheses R C := by
  refine
    { independent_of_state := ?_ }
  intro s1 s2 o
  exact hPrim.depends_on_ratio (hRigPrim.ratio_state_collapse s1 s2 o)

theorem certificate_depends_on_ratio
    (R : RatioCostSpace S O) (C : S → O → ℝ)
    (h : CertificateHypotheses R C) :
    ∀ {s1 s2 : S} {o1 o2 : O},
      ratio R s1 o1 = ratio R s2 o2 → C s1 o1 = C s2 o2 :=
  h.depends_on_ratio

/-- Existence of a reparametrization on the realized cost image.
The codomain is `CostCode R` to avoid overclaiming global surjectivity onto `ℝ`. -/
theorem exists_monotone_reparam
    (R : RatioCostSpace S O) (C : S → O → ℝ)
    (h : CertificateHypotheses R C) :
    ∃ φ : CostCode R → ℝ,
      (∀ s o,
          C s o =
            φ ⟨canonicalCost R s o, ⟨(s, o), rfl⟩⟩)
      ∧
      (∀ s o1 o2,
          canonicalCost R s o1 ≤ canonicalCost R s o2 →
          φ ⟨canonicalCost R s o1, ⟨(s, o1), rfl⟩⟩
            ≤
          φ ⟨canonicalCost R s o2, ⟨(s, o2), rfl⟩⟩) := by
  classical
  let φ : CostCode R → ℝ := fun t =>
    let p : S × O := Classical.choose t.2
    C p.1 p.2
  refine ⟨φ, ?_, ?_⟩
  · intro s o
    let t : CostCode R := ⟨canonicalCost R s o, ⟨(s, o), rfl⟩⟩
    have ht :
        canonicalCost R (Classical.choose t.2).1 (Classical.choose t.2).2 = t.1 :=
      Classical.choose_spec t.2
    have hcost :
        canonicalCost R s o =
          canonicalCost R (Classical.choose t.2).1 (Classical.choose t.2).2 := by
      simpa [t] using ht.symm
    have hdep :
        C s o = C (Classical.choose t.2).1 (Classical.choose t.2).2 :=
      h.depends_on_cost hcost
    simpa [φ, t] using hdep
  · intro s o1 o2 hle
    have hrepr1 :
        C s o1 = φ ⟨canonicalCost R s o1, ⟨(s, o1), rfl⟩⟩ := by
      simpa using (show C s o1 = φ ⟨canonicalCost R s o1, ⟨(s, o1), rfl⟩⟩ from by
        let t : CostCode R := ⟨canonicalCost R s o1, ⟨(s, o1), rfl⟩⟩
        have ht :
            canonicalCost R (Classical.choose t.2).1 (Classical.choose t.2).2 = t.1 :=
          Classical.choose_spec t.2
        have hcost :
            canonicalCost R s o1 =
              canonicalCost R (Classical.choose t.2).1 (Classical.choose t.2).2 := by
          simpa [t] using ht.symm
        have hdep :
            C s o1 = C (Classical.choose t.2).1 (Classical.choose t.2).2 :=
          h.depends_on_cost hcost
        simpa [φ, t] using hdep)
    have hrepr2 :
        C s o2 = φ ⟨canonicalCost R s o2, ⟨(s, o2), rfl⟩⟩ := by
      simpa using (show C s o2 = φ ⟨canonicalCost R s o2, ⟨(s, o2), rfl⟩⟩ from by
        let t : CostCode R := ⟨canonicalCost R s o2, ⟨(s, o2), rfl⟩⟩
        have ht :
            canonicalCost R (Classical.choose t.2).1 (Classical.choose t.2).2 = t.1 :=
          Classical.choose_spec t.2
        have hcost :
            canonicalCost R s o2 =
              canonicalCost R (Classical.choose t.2).1 (Classical.choose t.2).2 := by
          simpa [t] using ht.symm
        have hdep :
            C s o2 = C (Classical.choose t.2).1 (Classical.choose t.2).2 :=
          h.depends_on_cost hcost
        simpa [φ, t] using hdep)
    calc
      φ ⟨canonicalCost R s o1, ⟨(s, o1), rfl⟩⟩ = C s o1 := by simpa using hrepr1.symm
      _ ≤ C s o2 := h.monotone_in_cost s o1 o2 hle
      _ = φ ⟨canonicalCost R s o2, ⟨(s, o2), rfl⟩⟩ := by simpa using hrepr2

/-- Uniqueness of the realized-cost reparametrization:
if a profile `φ` represents all certificate values on `CostCode R`, it is uniquely determined. -/
theorem existsUnique_cost_reparam
    (R : RatioCostSpace S O) (C : S → O → ℝ)
    (h : CertificateHypotheses R C) :
    ∃! φ : CostCode R → ℝ, ∀ s o,
      C s o = φ ⟨canonicalCost R s o, ⟨(s, o), rfl⟩⟩ := by
  rcases exists_monotone_reparam R C h with ⟨φ0, hrepr0, _hmono0⟩
  refine ⟨φ0, hrepr0, ?_⟩
  intro φ hrepr
  funext t
  rcases t with ⟨r, hr⟩
  rcases hr with ⟨p, hp⟩
  rcases p with ⟨s, o⟩
  have hcode :
      (⟨canonicalCost R s o, ⟨(s, o), rfl⟩⟩ : CostCode R) = ⟨r, ⟨(s, o), hp⟩⟩ := by
    apply Subtype.ext
    simp [hp]
  have hrepr0' : C s o = φ0 ⟨r, ⟨(s, o), hp⟩⟩ := by
    simpa [hcode] using hrepr0 s o
  have hrepr' : C s o = φ ⟨r, ⟨(s, o), hp⟩⟩ := by
    simpa [hcode] using hrepr s o
  calc
    φ ⟨r, ⟨(s, o), hp⟩⟩ = C s o := by simpa using hrepr'.symm
    _ = φ0 ⟨r, ⟨(s, o), hp⟩⟩ := by simpa using hrepr0'

/-- Rigidity consequence: if certificate values are state-independent by hypothesis,
there exists a single state-free profile `ψ` representing all `C s _`. -/
theorem phi_independent_of_state
    [Inhabited S]
    (R : RatioCostSpace S O) (C : S → O → ℝ)
    (hRig : RigidityHypotheses R C) :
    ∃ ψ : O → ℝ, ∀ s o, C s o = ψ o := by
  refine ⟨fun o => C (default : S) o, ?_⟩
  intro s o
  exact hRig.independent_of_state s default o

/-- Uniqueness of the state-free profile under explicit rigidity:
the profile `ψ : O → ℝ` is uniquely determined by certificate values. -/
theorem existsUnique_state_profile
    [Inhabited S]
    (R : RatioCostSpace S O) (C : S → O → ℝ)
    (hRig : RigidityHypotheses R C) :
    ∃! ψ : O → ℝ, ∀ s o, C s o = ψ o := by
  refine ⟨fun o => C (default : S) o, ?_, ?_⟩
  · intro s o
    exact hRig.independent_of_state s default o
  · intro ψ hψ
    funext o
    exact (hψ default o).symm

/-- Assembled forced-factorization statement at the current maximal claim-honest level:
cost-image reparametrization + (optional) state-independence under explicit rigidity. -/
theorem forced_factorization
    [Inhabited S]
    (R : RatioCostSpace S O) (C : S → O → ℝ)
    (h : CertificateHypotheses R C)
    (hRig : RigidityHypotheses R C) :
    ∃ φ : CostCode R → ℝ,
      (∀ s o,
        C s o = φ ⟨canonicalCost R s o, ⟨(s, o), rfl⟩⟩)
      ∧
      (∃ ψ : O → ℝ, ∀ s o, C s o = ψ o) := by
  rcases exists_monotone_reparam R C h with ⟨φ, hrepr, _hmono⟩
  rcases phi_independent_of_state R C hRig with ⟨ψ, hψ⟩
  exact ⟨φ, hrepr, ⟨ψ, hψ⟩⟩

/-- Strongest bundled statement currently proved:
both the cost-image reparametrization and the state-free profile are unique
under explicit hypothesis bundles. -/
theorem forced_factorization_unique
    [Inhabited S]
    (R : RatioCostSpace S O) (C : S → O → ℝ)
    (h : CertificateHypotheses R C)
    (hRig : RigidityHypotheses R C) :
    (∃! φ : CostCode R → ℝ,
      ∀ s o, C s o = φ ⟨canonicalCost R s o, ⟨(s, o), rfl⟩⟩)
    ∧
    (∃! ψ : O → ℝ, ∀ s o, C s o = ψ o) := by
  constructor
  · exact existsUnique_cost_reparam R C h
  · exact existsUnique_state_profile R C hRig

/-- Strong forced-factorization theorem from primitive ratio-level assumptions. -/
theorem forced_factorization_unique_of_primitives
    [Inhabited S]
    (R : RatioCostSpace S O) (C : S → O → ℝ)
    (hPrim : PrimitiveCertificateHypotheses R C)
    (hRigPrim : PrimitiveRigidityHypotheses R) :
    (∃! φ : CostCode R → ℝ,
      ∀ s o, C s o = φ ⟨canonicalCost R s o, ⟨(s, o), rfl⟩⟩)
    ∧
    (∃! ψ : O → ℝ, ∀ s o, C s o = ψ o) := by
  exact forced_factorization_unique R C
    (primitive_to_certificate R C hPrim)
    (primitive_to_rigidity R C hPrim hRigPrim)

end ForcedFactorization
end CPT
end Verification
end IndisputableMonolith
