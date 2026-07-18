import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.ZqContinuumBlocker

/-!
# Seven Gaps, P2.3: the capped-quotient to exact-shell carrier bridge

This module constructs the missing carrier equivalence behind
`ZqContinuumBlocker.CapShellCompatibility`.

At cap `B`, a bounded complex has a unique exact complexity
`max nV (max nE nT) ≤ B`.  Conversely, an exact complex in shell `n ≤ B`
becomes a bounded complex by reattaching the three cap proofs.  Both maps
carry the original incidence data and relabeling witnesses.  They therefore
descend to the two quotient carriers and are inverse there.

The bridge preserves automorphism cardinality and hence the `1 / |Aut|`
class measure.  An arbitrary exact-shell phase transports to a `PhaseModel`
at every cap.  Reindexing the finite quotient sum along the carrier
equivalence then proves the required equality with
`exactComplexityCutoff phase B`, whose shell range is `B + 1`.

No target sum equality, convergence statement, substrate phase, or physical
continuum interpretation is assumed.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace CapShellBridge

open PathSumMeasure
open QuotientFirstZ
open ExactShellGaugeUV
open ZqPhaseStructure
open ZqContinuumBlocker

noncomputable section

/-! ## 1. The labeled carrier maps -/

/-- The exact shells whose complexity is at most `B`.  The outer
`Fin (B + 1)` is the off-by-one-safe carrier for shell indices `0, ..., B`. -/
abbrev ShellsUpTo (B : ℕ) : Type :=
  Σ n : Fin (B + 1), ExactPathClass n

noncomputable local instance instFintypeTriangulationClass (B : ℕ) :
    Fintype (TriangulationClass B) :=
  Fintype.ofFinite _

/-- A bounded complex's exact complexity, packaged as an index in
`Fin (B + 1)`. -/
def boundedShellIndex {B : ℕ} (K : BoundedComplex B) : Fin (B + 1) :=
  ⟨complexity K, Nat.lt_succ_of_le (max_le K.hV (max_le K.hE K.hT))⟩

/-- The exact signature carried by a bounded complex. -/
def boundedShellSig {B : ℕ} (K : BoundedComplex B) : ShellSig (complexity K) :=
  ⟨(⟨K.nV, Nat.lt_succ_of_le (Nat.le_max_left _ _)⟩,
    ⟨K.nE, Nat.lt_succ_of_le
      (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))⟩,
    ⟨K.nT, Nat.lt_succ_of_le
      (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))⟩), rfl⟩

/-- Forward labeled map: forget the cap proofs, retain the exact signature
and incidence data, then enter the exact relabeling quotient. -/
def boundedToShell {B : ℕ} (K : BoundedComplex B) : ShellsUpTo B :=
  ⟨boundedShellIndex K, boundedShellSig K,
    Quotient.mk _ (toExact K)⟩

/-- Backward labeled map: attach a cap `B` to an exact complex whose shell
index is at most `B`. -/
def exactToBounded {B n : ℕ} (hn : n ≤ B) (s : ShellSig n)
    (K : ExactComplex (sigV s) (sigE s) (sigT s)) : BoundedComplex B where
  nV := sigV s
  nE := sigE s
  nT := sigT s
  hV := le_trans (Nat.le_of_lt_succ s.1.1.isLt) hn
  hE := le_trans (Nat.le_of_lt_succ s.1.2.1.isLt) hn
  hT := le_trans (Nat.le_of_lt_succ s.1.2.2.isLt) hn
  edgeVerts := K.edgeVerts
  tetVerts := K.tetVerts

/-- An exact relabeling remains a bounded relabeling after cap proofs are
attached. -/
def exactRelabelToBounded {B n : ℕ} (hn : n ≤ B) (s : ShellSig n)
    {K K' : ExactComplex (sigV s) (sigE s) (sigT s)}
    (r : ExactRelabel K K') :
    Relabel (exactToBounded hn s K) (exactToBounded hn s K') where
  vEquiv := r.vEquiv
  eEquiv := r.eEquiv
  tEquiv := r.tEquiv
  edge_comm := r.edge_comm
  tet_comm := r.tet_comm

/-- The backward map on one exact-signature quotient. -/
def exactClassToCap {B n : ℕ} (hn : n ≤ B) (s : ShellSig n) :
    Quotient (exactSetoid (sigV s) (sigE s) (sigT s)) →
      TriangulationClass B :=
  Quotient.lift
    (fun K => Quotient.mk _ (exactToBounded hn s K))
    (fun _K _K' h => Quotient.sound <|
      h.elim fun r => ⟨exactRelabelToBounded hn s r⟩)

/-- Backward map on the full disjoint union of exact shells through `B`. -/
def shellToCap {B : ℕ} (x : ShellsUpTo B) : TriangulationClass B :=
  exactClassToCap (Nat.le_of_lt_succ x.1.isLt) x.2.1 x.2.2

/-! ## 2. Descent to quotients and inverse laws -/

/-- The forward labeled map respects bounded relabeling. -/
theorem boundedToShell_congr {B : ℕ} {K K' : BoundedComplex B}
    (h : Equivalent K K') : boundedToShell K = boundedToShell K' := by
  rcases K with ⟨v, e, t, hV, hE, hT, edgeVerts, tetVerts⟩
  rcases K' with ⟨v', e', t', hV', hE', hT', edgeVerts', tetVerts'⟩
  obtain ⟨r⟩ := h
  have hv : v = v' := relabel_nV_eq r
  have he : e = e' := relabel_nE_eq r
  have ht : t = t' := relabel_nT_eq r
  cases hv
  cases he
  cases ht
  have hVproof : hV = hV' := Subsingleton.elim _ _
  have hEproof : hE = hE' := Subsingleton.elim _ _
  have hTproof : hT = hT' := Subsingleton.elim _ _
  cases hVproof
  cases hEproof
  cases hTproof
  apply Sigma.ext
  · rfl
  exact heq_of_eq <| by
    apply Sigma.ext
    · rfl
    exact heq_of_eq <| Quotient.sound ⟨{
      vEquiv := r.vEquiv
      eEquiv := r.eEquiv
      tEquiv := r.tEquiv
      edge_comm := r.edge_comm
      tet_comm := r.tet_comm }⟩

/-- Forward map on bounded quotient classes. -/
def capToShell {B : ℕ} : TriangulationClass B → ShellsUpTo B :=
  Quotient.lift boundedToShell (fun _K _K' h => boundedToShell_congr h)

/-- Attaching a cap after forgetting it returns the original bounded class. -/
theorem shellToCap_boundedToShell {B : ℕ} (K : BoundedComplex B) :
    shellToCap (boundedToShell K) =
      Quotient.mk (relabelSetoid B) K := by
  apply Quotient.sound
  exact ⟨{
    vEquiv := Equiv.refl _
    eEquiv := Equiv.refl _
    tEquiv := Equiv.refl _
    edge_comm := by
      intro e
      change K.edgeVerts e =
        Prod.map (Equiv.refl _) (Equiv.refl _) (K.edgeVerts e)
      cases K.edgeVerts e
      rfl
    tet_comm := by
      intro t i
      rfl }⟩

/-- Forgetting the cap after attaching it returns the original exact-shell
class.  Proof fields disappear by proof irrelevance; incidence data is
unchanged. -/
theorem boundedToShell_exactToBounded {B n : ℕ} (hn : n ≤ B)
    (s : ShellSig n) (K : ExactComplex (sigV s) (sigE s) (sigT s)) :
    boundedToShell (exactToBounded hn s K) =
      ⟨⟨n, Nat.lt_succ_of_le hn⟩, s, Quotient.mk _ K⟩ := by
  rcases s with ⟨⟨v, e, t⟩, hs⟩
  rcases v with ⟨v, hv⟩
  rcases e with ⟨e, he⟩
  rcases t with ⟨t, ht⟩
  dsimp only [sigV, sigE, sigT] at K ⊢
  dsimp only at hs
  subst n
  simp [boundedToShell, boundedShellIndex, boundedShellSig, exactToBounded,
    sigV, sigE, sigT, complexity]
  exact Quotient.sound ⟨ExactRelabel.refl K⟩

/-- Right inverse law on exact-shell quotient classes. -/
theorem capToShell_shellToCap {B : ℕ} (x : ShellsUpTo B) :
    capToShell (shellToCap x) = x := by
  rcases x with ⟨⟨n, hn⟩, s, q⟩
  refine Quotient.inductionOn q ?_
  intro K
  exact boundedToShell_exactToBounded (Nat.le_of_lt_succ hn) s K

/-- Left inverse law on bounded quotient classes. -/
theorem shellToCap_capToShell {B : ℕ} (q : TriangulationClass B) :
    shellToCap (capToShell q) = q := by
  refine Quotient.inductionOn q ?_
  intro K
  exact shellToCap_boundedToShell K

/-- **HEADLINE CARRIER EQUIVALENCE.**  Bounded quotient classes at cap `B`
are exactly the disjoint union of exact quotient shells `0, ..., B`. -/
def capShellEquiv (B : ℕ) : TriangulationClass B ≃ ShellsUpTo B where
  toFun := capToShell
  invFun := shellToCap
  left_inv := shellToCap_capToShell
  right_inv := capToShell_shellToCap

/-! ## 3. Automorphism cardinality and measure preservation -/

/-- Bounded automorphisms and exact automorphisms of the cap-forgotten
complex carry exactly the same relabeling data. -/
def autEquivToExact {B : ℕ} (K : BoundedComplex B) :
    Aut K ≃ ExactAut (toExact K) where
  toFun r :=
    { vEquiv := r.vEquiv
      eEquiv := r.eEquiv
      tEquiv := r.tEquiv
      edge_comm := r.edge_comm
      tet_comm := r.tet_comm }
  invFun r :=
    { vEquiv := r.vEquiv
      eEquiv := r.eEquiv
      tEquiv := r.tEquiv
      edge_comm := r.edge_comm
      tet_comm := r.tet_comm }
  left_inv r := Relabel.ext rfl rfl rfl
  right_inv r := ExactRelabel.ext rfl rfl rfl

/-- **AUTOMORPHISM-CARDINALITY PRESERVATION.** -/
theorem autCard_toExact {B : ℕ} (K : BoundedComplex B) :
    Nat.card (Aut K) = Nat.card (ExactAut (toExact K)) :=
  Nat.card_congr (autEquivToExact K)

/-- The labeled symmetry-factor measures agree under cap forgetting. -/
theorem mu_eq_exactMu_toExact {B : ℕ} (K : BoundedComplex B) :
    mu K = exactMu (toExact K) := by
  unfold mu exactMu
  rw [autCard_toExact K]

/-- Automorphism cardinality of a represented exact-shell class. -/
noncomputable def shellAutCard {n : ℕ} (c : ExactPathClass n) : ℕ :=
  Nat.card (ExactAut (Quotient.out c.2))

/-- **QUOTIENT-LEVEL AUTOMORPHISM PRESERVATION.** -/
theorem shellAutCard_capToShell {B : ℕ} (q : TriangulationClass B) :
    shellAutCard (capToShell q).2 = Nat.card (Aut (Quotient.out q)) := by
  refine Quotient.inductionOn q ?_
  intro K
  let qe := Quotient.mk (exactSetoid K.nV K.nE K.nT) (toExact K)
  have hrel : GlobalEquivalent (Quotient.out qe) (toExact K) :=
    Quotient.exact (Quotient.out_eq qe)
  obtain ⟨r⟩ := hrel
  have hcap : Equivalent
      (Quotient.out (Quotient.mk (relabelSetoid B) K)) K :=
    PathSum.equivalent_of_mk_eq
      (Quotient.out_eq (Quotient.mk (relabelSetoid B) K))
  obtain ⟨s⟩ := hcap
  dsimp [capToShell, boundedToShell, shellAutCard]
  calc
    Nat.card (ExactAut (Quotient.out qe))
        = Nat.card (ExactAut (toExact K)) := Nat.card_congr r.autCongr
    _ = Nat.card (Aut K) := (autCard_toExact K).symm
    _ = Nat.card (Aut (Quotient.out (Quotient.mk (relabelSetoid B) K))) :=
        (Nat.card_congr s.autCongr).symm

/-- **QUOTIENT-LEVEL MEASURE PRESERVATION.**  The class measure on the
exact-shell image is the capped representative measure. -/
theorem classMu_capToShell {B : ℕ} (q : TriangulationClass B) :
    classMu (capToShell q).2 = mu (Quotient.out q) := by
  refine Quotient.inductionOn q ?_
  intro K
  let qe := Quotient.mk (exactSetoid K.nV K.nE K.nT) (toExact K)
  have hrel : GlobalEquivalent (Quotient.out qe) (toExact K) :=
    Quotient.exact (Quotient.out_eq qe)
  have hcap : Equivalent
      (Quotient.out (Quotient.mk (relabelSetoid B) K)) K :=
    PathSum.equivalent_of_mk_eq
      (Quotient.out_eq (Quotient.mk (relabelSetoid B) K))
  dsimp [capToShell, boundedToShell, classMu]
  show classMuOn K.nV K.nE K.nT qe =
    mu (Quotient.out (Quotient.mk (relabelSetoid B) K))
  rw [RegulatorRemovalNoGo.classMuOn_out qe]
  calc
    exactMu (Quotient.out qe) = exactMu (toExact K) := exactMu_congr hrel
    _ = mu K := (mu_eq_exactMu_toExact K).symm
    _ = mu (Quotient.out (Quotient.mk (relabelSetoid B) K)) :=
        (mu_congr hcap).symm

/-! ## 4. Transport of arbitrary exact-shell phases -/

/-- Transport an arbitrary phase on exact shells to the labeled bounded
carrier at cap `B`. -/
def phaseModelAtCap
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) (B : ℕ) : PhaseModel B where
  phase K := phase (boundedToShell K).1 (boundedToShell K).2
  invariant K K' h := by rw [boundedToShell_congr h]

/-- The transported phase descends to exactly the original phase after the
carrier equivalence. -/
theorem classPhase_phaseModelAtCap
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) {B : ℕ}
    (q : TriangulationClass B) :
    classPhase (phaseModelAtCap phase B) q =
      phase (capToShell q).1 (capToShell q).2 := by
  refine Quotient.inductionOn q ?_
  intro K
  rfl

/-- The transported phase model at every cap. -/
def capPhaseFamily
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) : CapPhaseFamily :=
  fun B => phaseModelAtCap phase B

/-! ## 5. Finite-sum reindexing and compatibility -/

/-- A sum over `Fin N` is the corresponding natural-number range sum. -/
theorem sum_fin_eq_sum_range {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (N : ℕ) :
    (∑ i : Fin N, f i) = ∑ i ∈ Finset.range N, f i := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        (∑ i : Fin (N + 1), f i)
            = (∑ i : Fin N, f i) + f N := by
                simpa using Fin.sum_univ_castSucc
                  (f := fun i : Fin (N + 1) => f i)
        _ = (∑ i ∈ Finset.range N, f i) + f N := by rw [ih]
        _ = ∑ i ∈ Finset.range (N + 1), f i := by
              rw [Finset.sum_range_succ]

/-- Splitting the disjoint-union carrier gives exactly the shell cutoff
through `B`; the range is `B + 1`, so shell `B` is included. -/
theorem sum_shellsUpTo_eq_exactComplexityCutoff
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) (B : ℕ) :
    (∑ x : ShellsUpTo B,
      (classMu x.2 : ℂ) *
        Complex.exp (Complex.I * (phase x.1 x.2 : ℂ))) =
      exactComplexityCutoff phase B := by
  rw [Fintype.sum_sigma]
  change (∑ n : Fin (B + 1), exactShellAmplitude phase n) =
    ∑ n ∈ Finset.range (B + 1), exactShellAmplitude phase n
  exact sum_fin_eq_sum_range (exactShellAmplitude phase) (B + 1)

/-- **HEADLINE FINITE-SUM REINDEXING.**  The phased capped quotient sum
transported from any exact-shell phase equals its exact-shell cutoff through
shell `B`. -/
theorem phasedZq_eq_exactComplexityCutoff
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) (B : ℕ) :
    phasedZqSequence (capPhaseFamily phase) B =
      exactComplexityCutoff phase B := by
  unfold phasedZqSequence
  change Zq B (phasedWeight (phaseModelAtCap phase B)) =
    exactComplexityCutoff phase B
  rw [Zq]
  calc
    (∑ q : TriangulationClass B,
      (mu (Quotient.out q) : ℂ) *
        phasedWeight (phaseModelAtCap phase B) q)
        = ∑ x : ShellsUpTo B,
            (classMu x.2 : ℂ) *
              Complex.exp (Complex.I * (phase x.1 x.2 : ℂ)) := by
            apply Fintype.sum_equiv (capShellEquiv B)
            intro q
            change (mu (Quotient.out q) : ℂ) *
                phasedWeight (phaseModelAtCap phase B) q =
              (classMu (capToShell q).2 : ℂ) *
                Complex.exp (Complex.I * (phase (capToShell q).1 (capToShell q).2 : ℂ))
            rw [classMu_capToShell]
            simp only [phasedWeight, classPhase_phaseModelAtCap]
    _ = exactComplexityCutoff phase B :=
      sum_shellsUpTo_eq_exactComplexityCutoff phase B

/-- **P2.3 CLOSER.**  Every exact-shell phase has a canonically transported
capped phase family satisfying the previously missing
`ZqContinuumBlocker.CapShellCompatibility`. -/
theorem capShellCompatibility
    (phase : ∀ n : ℕ, ExactPathClass n → ℝ) :
    CapShellCompatibility (capPhaseFamily phase) phase :=
  ⟨phasedZq_eq_exactComplexityCutoff phase⟩

#print axioms capShellEquiv
#print axioms autCard_toExact
#print axioms shellAutCard_capToShell
#print axioms classMu_capToShell
#print axioms phasedZq_eq_exactComplexityCutoff
#print axioms capShellCompatibility

end

end CapShellBridge
end SevenGaps
end Gravity
end IndisputableMonolith
