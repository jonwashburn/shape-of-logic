/-
  PrimitiveRecognitionCalculus/RealCompleteness.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 10e: replace the placeholder completeness target with a
    theorem-shaped internal Cauchy-of-Cauchy statement and isolate the exact
    diagonal blocker.

  This file closes the construction fact that every raw PRC rational Cauchy
  ledger already determines a point of the null quotient, then closes the
  explicit `PRCRealCompletenessTarget` diagonal theorem.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealOrderCongruence

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- Every raw rational Cauchy ledger can be packaged as a `PRCCauchySeq`. -/
def PRCRawCauchyRealizationTarget : Prop :=
  ∀ s : PRCRawRatLedger,
    PRCRawCauchy s →
      ∃ u : PRCCauchySeq, u.raw = s

theorem PRCRawCauchyRealizationTarget_proved :
    PRCRawCauchyRealizationTarget := by
  intro s hs
  refine ⟨{ term := s, cauchy := hs }, ?_⟩
  rfl

/-- Every raw rational Cauchy ledger determines a point of the final
null-distance quotient. -/
def PRCRawCauchyQuotientPointTarget : Prop :=
  ∀ s : PRCRawRatLedger,
    PRCRawCauchy s →
      Nonempty PRCRealNullClosed

theorem PRCRawCauchyQuotientPointTarget_proved :
    PRCRawCauchyQuotientPointTarget := by
  intro s hs
  rcases PRCRawCauchyRealizationTarget_proved s hs with ⟨u, _hu⟩
  exact ⟨Quot.mk
    (PRCNullDistanceSetoidOfTransitive PRCNullDistanceTransitiveTarget_proved)
    u⟩

/-- Named diagonal selection blocker for internal completeness. It asks for an
actual Cauchy ledger limit for every representative-Cauchy sequence of Cauchy
ledgers. -/
def PRCRealDiagonalSelectionTarget : Prop :=
  ∀ U : Nat → PRCCauchySeq,
    PRCRealRepresentativeCauchy U →
      ∃ L : PRCCauchySeq, PRCRealRepresentativeLimit U L

/-- Sharper diagonal blocker: construct the raw rational ledger underneath the
limit and prove both its Cauchy property and its limit property. This is the
mathematical work left after the quotient and packaging bookkeeping is removed. -/
def PRCRealRawDiagonalLedgerTarget : Prop :=
  ∀ U : Nat → PRCCauchySeq,
    PRCRealRepresentativeCauchy U →
      ∃ s : PRCRawRatLedger,
        PRCRawCauchy s ∧
          ∀ eps : PRCRat, PRCRat.positive eps →
            ∃ N : Nat, ∀ n : Nat, N ≤ n →
              PRCRawEventuallyClose (U n).raw s eps

/-- Tail-selection version of the raw diagonal theorem. It asks for an explicit
choice of a sufficiently deep raw index in each representative, so the diagonal
ledger is made from actual terms of the input Cauchy ledgers. -/
def PRCRealTailSelectionTarget : Prop :=
  ∀ U : Nat → PRCCauchySeq,
    PRCRealRepresentativeCauchy U →
      ∃ pick : Nat → Nat,
        let s : PRCRawRatLedger := fun n => (U n).term (pick n)
        PRCRawCauchy s ∧
          ∀ eps : PRCRat, PRCRat.positive eps →
            ∃ N : Nat, ∀ n : Nat, N ≤ n →
              PRCRawEventuallyClose (U n).raw s eps

/-- The PRC rational unit-fraction tolerance `1 / (n+1)`. This is verifier
display machinery for the completeness proof, not a new PRC primitive. -/
def PRCUnitFraction (n : Nat) : PRCRat :=
  let den : DistinctionNat := DistinctionNat.ofNat (n + 1)
  have hden : den ≠ DistinctionNat.zero := by
    intro h
    have hnat := congrArg DistinctionNat.toNat h
    rw [DistinctionNat.toNat_ofNat, DistinctionNat.toNat_zero] at hnat
    omega
  PRCRat.mk {
    num := SignedOrbit.one
    den := den
    den_ne_zero := hden
  }

theorem PRCUnitFraction_toRat (n : Nat) :
    (PRCUnitFraction n).toRat = (1 : ℚ) / (n + 1 : Nat) := by
  unfold PRCUnitFraction
  rw [PRCRat.toRat_mk]
  unfold RatioOrbit.toRat
  simp [SignedOrbit.one_toInt, DistinctionNat.toNat_ofNat]

theorem PRCUnitFraction_positive (n : Nat) :
    PRCRat.positive (PRCUnitFraction n) := by
  rw [PRCRat.positive_iff_toRat_pos, PRCUnitFraction_toRat]
  positivity

/-- Exact cofinal tolerance-schedule target needed by the tail-selection
diagonal proof. -/
def PRCRealCofinalToleranceScheduleTarget : Prop :=
  ∃ tau : Nat → PRCRat,
    (∀ n : Nat, PRCRat.positive (tau n)) ∧
      ∀ eps : PRCRat, PRCRat.positive eps →
        ∃ N : Nat, ∀ n : Nat, N ≤ n → PRCRat.lt (tau n) eps

theorem PRCUnitFraction_eventually_lt
    {eps : PRCRat} (heps : PRCRat.positive eps) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      PRCRat.lt (PRCUnitFraction n) eps := by
  have heps_pos : (0 : ℚ) < eps.toRat :=
    (PRCRat.positive_iff_toRat_pos eps).mp heps
  rcases exists_nat_gt (1 / eps.toRat) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rw [PRCRat.lt_iff_toRat_lt, PRCUnitFraction_toRat]
  have hN_le_n : (N : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn_lt_succ : (n : ℚ) < (n + 1 : Nat) := by
    norm_num
  have hgt : (1 / eps.toRat : ℚ) < (n + 1 : Nat) := by
    exact lt_of_lt_of_le hN (le_trans hN_le_n (le_of_lt hn_lt_succ))
  have hprod : (1 : ℚ) < eps.toRat * (n + 1 : Nat) := by
    have hmul := mul_lt_mul_of_pos_left hgt heps_pos
    have hone : eps.toRat * (1 / eps.toRat) = (1 : ℚ) := by
      field_simp [ne_of_gt heps_pos]
    rw [hone] at hmul
    simpa [mul_comm] using hmul
  have hden_pos : (0 : ℚ) < (n + 1 : Nat) := by positivity
  field_simp [ne_of_gt hden_pos]
  linarith

theorem PRCRealCofinalToleranceScheduleTarget_proved :
    PRCRealCofinalToleranceScheduleTarget := by
  refine ⟨PRCUnitFraction, PRCUnitFraction_positive, ?_⟩
  intro eps heps
  exact PRCUnitFraction_eventually_lt heps

theorem PRCRat.lt_trans {a b c : PRCRat}
    (hab : PRCRat.lt a b) (hbc : PRCRat.lt b c) :
    PRCRat.lt a c := by
  rw [PRCRat.lt_iff_toRat_lt] at hab hbc ⊢
  exact _root_.lt_trans hab hbc

/-- Three-leg form of the J-cost distance modulus. The diagonal proof naturally
travels from a selected diagonal point to an intermediate raw point, then across
representatives, then back down another selected diagonal point. -/
def PRCJCostDistanceThreeLegModulusTarget : Prop :=
  ∀ eps : PRCRat, PRCRat.positive eps →
    ∃ delta : PRCRat, PRCRat.positive delta ∧
      ∀ a b c d : PRCRat,
        PRCRat.lt (PRCJCostDistance a b) delta →
          PRCRat.lt (PRCJCostDistance b c) delta →
            PRCRat.lt (PRCJCostDistance c d) delta →
              PRCRat.lt (PRCJCostDistance a d) eps

theorem PRCJCostDistanceThreeLegModulusTarget_proved :
    PRCJCostDistanceThreeLegModulusTarget := by
  intro eps heps
  rcases PRCJCostDistanceTriangleModulusTarget_proved eps heps with
    ⟨eta, heta_pos, heta_tri⟩
  rcases PRCJCostDistanceTriangleModulusTarget_proved eta heta_pos with
    ⟨theta, htheta_pos, htheta_tri⟩
  rcases PRCUnitFraction_eventually_lt heta_pos with ⟨Neta, hNeta⟩
  rcases PRCUnitFraction_eventually_lt htheta_pos with ⟨Ntheta, hNtheta⟩
  let delta := PRCUnitFraction (max Neta Ntheta)
  have hdelta_pos : PRCRat.positive delta := PRCUnitFraction_positive _
  have hdelta_lt_eta : PRCRat.lt delta eta := by
    exact hNeta (max Neta Ntheta) (Nat.le_max_left Neta Ntheta)
  have hdelta_lt_theta : PRCRat.lt delta theta := by
    exact hNtheta (max Neta Ntheta) (Nat.le_max_right Neta Ntheta)
  refine ⟨delta, hdelta_pos, ?_⟩
  intro a b c d hab hbc hcd
  have hab_eta : PRCRat.lt (PRCJCostDistance a b) eta :=
    PRCRat.lt_trans hab hdelta_lt_eta
  have hbc_theta : PRCRat.lt (PRCJCostDistance b c) theta :=
    PRCRat.lt_trans hbc hdelta_lt_theta
  have hcd_theta : PRCRat.lt (PRCJCostDistance c d) theta :=
    PRCRat.lt_trans hcd hdelta_lt_theta
  have hbd_eta : PRCRat.lt (PRCJCostDistance b d) eta :=
    htheta_tri b c d hbc_theta hcd_theta
  exact heta_tri a b d hab_eta hbd_eta

/-- A candidate index is deep enough for one raw Cauchy ledger at one
tolerance. -/
def PRCRowTailBound (u : PRCCauchySeq) (eps : PRCRat) (N : Nat) : Prop :=
  ∀ m n : Nat, N ≤ m → N ≤ n →
    PRCRat.lt (PRCJCostDistance (u.term m) (u.term n)) eps

theorem PRCRowTailBound_mono {u : PRCCauchySeq} {eps : PRCRat}
    {N M : Nat} (hNM : N ≤ M) (hN : PRCRowTailBound u eps N) :
    PRCRowTailBound u eps M := by
  intro m n hm hn
  exact hN m n (le_trans hNM hm) (le_trans hNM hn)

theorem PRCRealFiniteRowTailBound_exists
    (U : Nat → PRCCauchySeq) (eps : PRCRat)
    (heps : PRCRat.positive eps) :
    ∀ r : Nat,
      ∃ N : Nat, ∀ i : Nat, i ≤ r → PRCRowTailBound (U i) eps N
  | 0 => by
      rcases (U 0).cauchy eps heps with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      exact hN
  | Nat.succ r => by
      rcases PRCRealFiniteRowTailBound_exists U eps heps r with
        ⟨Nprev, hprev⟩
      rcases (U (Nat.succ r)).cauchy eps heps with ⟨Nlast, hlast⟩
      refine ⟨max Nprev Nlast, ?_⟩
      intro i hi
      by_cases hir : i ≤ r
      · exact PRCRowTailBound_mono
          (Nat.le_max_left Nprev Nlast) (hprev i hir)
      · have hi_last : i = Nat.succ r := by omega
        subst hi_last
        exact PRCRowTailBound_mono
          (Nat.le_max_right Nprev Nlast) hlast

/-- Exact finite-row scheduler needed by the diagonal tail-selection proof:
for every diagonal row `r`, choose one raw index deep enough for all rows
`0,...,r` at the tolerance `1/(r+1)`. -/
def PRCRealFiniteRowTailSelectionTarget : Prop :=
  ∀ U : Nat → PRCCauchySeq,
    ∃ pick : Nat → Nat,
      ∀ r i : Nat, i ≤ r →
        PRCRowTailBound (U i) (PRCUnitFraction r) (pick r)

theorem PRCRealFiniteRowTailSelectionTarget_proved :
    PRCRealFiniteRowTailSelectionTarget := by
  intro U
  choose pick hpick using
    fun r => PRCRealFiniteRowTailBound_exists
      U (PRCUnitFraction r) (PRCUnitFraction_positive r) r
  exact ⟨pick, hpick⟩

/-- A raw index is deep enough for every eligible representative row
`i ≤ r` to be close to the target row `r`, once the outer representative
threshold has been crossed. -/
def PRCRepresentativeFiniteTailBound
    (U : Nat → PRCCauchySeq) (eps : PRCRat)
    (outer r N : Nat) : Prop :=
  ∀ i k : Nat, outer ≤ i → i ≤ r → N ≤ k →
    PRCRat.lt (PRCJCostDistance ((U i).term k) ((U r).term k)) eps

theorem PRCRepresentativeFiniteTailBound_mono
    {U : Nat → PRCCauchySeq} {eps : PRCRat}
    {outer r N M : Nat} (hNM : N ≤ M)
    (hN : PRCRepresentativeFiniteTailBound U eps outer r N) :
    PRCRepresentativeFiniteTailBound U eps outer r M := by
  intro i k hoi hir hMk
  exact hN i k hoi hir (le_trans hNM hMk)

theorem PRCRepresentativeFiniteTailBound_exists
    (U : Nat → PRCCauchySeq) (eps : PRCRat)
    (outer r : Nat)
    (houter : ∀ m n : Nat, outer ≤ m → outer ≤ n →
      PRCRawEventuallyClose (U m).raw (U n).raw eps) :
    ∃ N : Nat, PRCRepresentativeFiniteTailBound U eps outer r N := by
  suffices hfinite :
      ∀ limit : Nat,
        limit ≤ r →
        ∃ N : Nat,
          ∀ i k : Nat, outer ≤ i → i ≤ limit → N ≤ k →
            PRCRat.lt
              (PRCJCostDistance ((U i).term k) ((U r).term k)) eps by
    rcases hfinite r (Nat.le_refl r) with ⟨N, hN⟩
    exact ⟨N, hN⟩
  intro limit
  induction limit with
  | zero =>
      intro _hlim
      by_cases houter_zero : outer ≤ 0
      · have houter_r : outer ≤ r := by omega
        rcases houter 0 r houter_zero houter_r with ⟨N, hN⟩
        refine ⟨N, ?_⟩
        intro i k hoi hir hNk
        have hi0 : i = 0 := by omega
        subst hi0
        simpa [PRCCauchySeq.raw] using hN k hNk
      · refine ⟨0, ?_⟩
        intro i _k hoi hir _h0k
        have : outer ≤ 0 := by omega
        exact False.elim (houter_zero this)
  | succ limit ih =>
      intro hlim
      rcases ih (Nat.le_of_succ_le hlim) with ⟨Nprev, hprev⟩
      by_cases hlast : outer ≤ Nat.succ limit
      · rcases houter (Nat.succ limit) r hlast
          (le_trans hlast hlim) with
          ⟨Nlast, hNlast⟩
        refine ⟨max Nprev Nlast, ?_⟩
        intro i k hoi hir hmaxk
        by_cases hir_prev : i ≤ limit
        · exact hprev i k hoi hir_prev
            (le_trans (Nat.le_max_left Nprev Nlast) hmaxk)
        · have hi_last : i = Nat.succ limit := by omega
          subst hi_last
          simpa [PRCCauchySeq.raw] using
            hNlast k (le_trans (Nat.le_max_right Nprev Nlast) hmaxk)
      · refine ⟨Nprev, ?_⟩
        intro i k hoi hir hNprevk
        have hir_prev : i ≤ limit := by omega
        exact hprev i k hoi hir_prev hNprevk

/-- Exact finite representative scheduler needed by the diagonal proof. For
each tolerance rung it chooses the outer Cauchy-representative threshold and a
raw depth that realizes all finite representative-tail comparisons up to that
rung. -/
def PRCRealFiniteRepresentativeTailSelectionTarget : Prop :=
  ∀ U : Nat → PRCCauchySeq,
    PRCRealRepresentativeCauchy U →
      ∃ outer pick : Nat → Nat,
        (∀ r m n : Nat, outer r ≤ m → outer r ≤ n →
          PRCRawEventuallyClose (U m).raw (U n).raw (PRCUnitFraction r)) ∧
        ∀ r : Nat,
          PRCRepresentativeFiniteTailBound
            U (PRCUnitFraction r) (outer r) r (pick r)

theorem PRCRealFiniteRepresentativeTailSelectionTarget_proved :
    PRCRealFiniteRepresentativeTailSelectionTarget := by
  intro U hU
  choose outer houter using
    fun r => hU (PRCUnitFraction r) (PRCUnitFraction_positive r)
  choose pick hpick using
    fun r => PRCRepresentativeFiniteTailBound_exists
      U (PRCUnitFraction r) (outer r) r (houter r)
  exact ⟨outer, pick, houter, hpick⟩

/-- Single finite diagonal scheduler: one raw choice function satisfies both
finite row-tail and finite representative-tail constraints at each tolerance
rung. This is still finite-rung scheduling, not yet the completed global
tail-selection theorem. -/
def PRCRealFiniteDiagonalScheduleTarget : Prop :=
  ∀ U : Nat → PRCCauchySeq,
    PRCRealRepresentativeCauchy U →
      ∃ outer pick : Nat → Nat,
        (∀ r m n : Nat, outer r ≤ m → outer r ≤ n →
          PRCRawEventuallyClose (U m).raw (U n).raw (PRCUnitFraction r)) ∧
        (∀ r i : Nat, i ≤ r →
          PRCRowTailBound (U i) (PRCUnitFraction r) (pick r)) ∧
        ∀ r : Nat,
          PRCRepresentativeFiniteTailBound
            U (PRCUnitFraction r) (outer r) r (pick r)

theorem PRCRealFiniteDiagonalScheduleTarget_proved :
    PRCRealFiniteDiagonalScheduleTarget := by
  intro U hU
  rcases PRCRealFiniteRowTailSelectionTarget_proved U with
    ⟨rowPick, hrowPick⟩
  rcases PRCRealFiniteRepresentativeTailSelectionTarget_proved U hU with
    ⟨outer, repPick, houter, hrepPick⟩
  refine ⟨outer, fun r => max (rowPick r) (repPick r), houter, ?_, ?_⟩
  · intro r i hir
    exact PRCRowTailBound_mono
      (Nat.le_max_left (rowPick r) (repPick r))
      (hrowPick r i hir)
  · intro r
    exact PRCRepresentativeFiniteTailBound_mono
      (Nat.le_max_right (rowPick r) (repPick r))
      (hrepPick r)

theorem PRCRealTailSelectionTarget_proved :
    PRCRealTailSelectionTarget := by
  intro U hU
  rcases PRCRealFiniteDiagonalScheduleTarget_proved U hU with
    ⟨_outer, pick, _houterTau, hrow, _hrep⟩
  refine ⟨pick, ?_, ?_⟩
  · intro eps heps
    rcases PRCJCostDistanceThreeLegModulusTarget_proved eps heps with
      ⟨delta, hdelta_pos, hthree⟩
    rcases hU delta hdelta_pos with ⟨Nrep, hNrep⟩
    rcases PRCUnitFraction_eventually_lt hdelta_pos with ⟨Ntau, hNtau⟩
    refine ⟨max Nrep Ntau, ?_⟩
    intro m n hm hn
    have hm_rep : Nrep ≤ m := le_trans (Nat.le_max_left Nrep Ntau) hm
    have hn_rep : Nrep ≤ n := le_trans (Nat.le_max_left Nrep Ntau) hn
    have hm_tauN : Ntau ≤ m := le_trans (Nat.le_max_right Nrep Ntau) hm
    have hn_tauN : Ntau ≤ n := le_trans (Nat.le_max_right Nrep Ntau) hn
    have htaum_delta : PRCRat.lt (PRCUnitFraction m) delta :=
      hNtau m hm_tauN
    have htaun_delta : PRCRat.lt (PRCUnitFraction n) delta :=
      hNtau n hn_tauN
    rcases hNrep m n hm_rep hn_rep with ⟨Npair, hNpair⟩
    let K : Nat := max (pick m) (max (pick n) Npair)
    have hpickmK : pick m ≤ K := Nat.le_max_left (pick m) (max (pick n) Npair)
    have hpicknK : pick n ≤ K :=
      le_trans (Nat.le_max_left (pick n) Npair)
        (Nat.le_max_right (pick m) (max (pick n) Npair))
    have hpairK : Npair ≤ K :=
      le_trans (Nat.le_max_right (pick n) Npair)
        (Nat.le_max_right (pick m) (max (pick n) Npair))
    have hleg1_tau :
        PRCRat.lt
          (PRCJCostDistance ((U m).term (pick m)) ((U m).term K))
          (PRCUnitFraction m) :=
      (hrow m m (Nat.le_refl m)) (pick m) K (Nat.le_refl (pick m)) hpickmK
    have hleg1 :
        PRCRat.lt
          (PRCJCostDistance ((U m).term (pick m)) ((U m).term K))
          delta :=
      PRCRat.lt_trans hleg1_tau htaum_delta
    have hleg2 :
        PRCRat.lt
          (PRCJCostDistance ((U m).term K) ((U n).term K))
          delta := by
      simpa [PRCCauchySeq.raw] using hNpair K hpairK
    have hleg3_tau :
        PRCRat.lt
          (PRCJCostDistance ((U n).term K) ((U n).term (pick n)))
          (PRCUnitFraction n) :=
      (hrow n n (Nat.le_refl n)) K (pick n) hpicknK (Nat.le_refl (pick n))
    have hleg3 :
        PRCRat.lt
          (PRCJCostDistance ((U n).term K) ((U n).term (pick n)))
          delta :=
      PRCRat.lt_trans hleg3_tau htaun_delta
    exact hthree
      ((U m).term (pick m)) ((U m).term K)
      ((U n).term K) ((U n).term (pick n))
      hleg1 hleg2 hleg3
  · intro eps heps
    rcases PRCJCostDistanceThreeLegModulusTarget_proved eps heps with
      ⟨delta, hdelta_pos, hthree⟩
    rcases hU delta hdelta_pos with ⟨Nrep, hNrep⟩
    rcases PRCUnitFraction_eventually_lt hdelta_pos with ⟨Ntau, hNtau⟩
    refine ⟨max Nrep Ntau, ?_⟩
    intro n hn
    have hn_rep : Nrep ≤ n := le_trans (Nat.le_max_left Nrep Ntau) hn
    rcases (U n).cauchy delta hdelta_pos with ⟨NrowN, hNrowN⟩
    refine ⟨max (max Nrep Ntau) NrowN, ?_⟩
    intro l hl
    have hl_rep : Nrep ≤ l :=
      le_trans (Nat.le_max_left Nrep Ntau)
        (le_trans (Nat.le_max_left (max Nrep Ntau) NrowN) hl)
    have hl_tauN : Ntau ≤ l :=
      le_trans (Nat.le_max_right Nrep Ntau)
        (le_trans (Nat.le_max_left (max Nrep Ntau) NrowN) hl)
    have hl_rowN : NrowN ≤ l :=
      le_trans (Nat.le_max_right (max Nrep Ntau) NrowN) hl
    have htaul_delta : PRCRat.lt (PRCUnitFraction l) delta :=
      hNtau l hl_tauN
    rcases hNrep n l hn_rep hl_rep with ⟨Npair, hNpair⟩
    let K : Nat := max l (max (pick l) Npair)
    have hlK : l ≤ K := Nat.le_max_left l (max (pick l) Npair)
    have hpicklK : pick l ≤ K :=
      le_trans (Nat.le_max_left (pick l) Npair)
        (Nat.le_max_right l (max (pick l) Npair))
    have hpairK : Npair ≤ K :=
      le_trans (Nat.le_max_right (pick l) Npair)
        (Nat.le_max_right l (max (pick l) Npair))
    have hrowNK : NrowN ≤ K := le_trans hl_rowN hlK
    have hleg1 :
        PRCRat.lt
          (PRCJCostDistance ((U n).term l) ((U n).term K))
          delta :=
      hNrowN l K hl_rowN hrowNK
    have hleg2 :
        PRCRat.lt
          (PRCJCostDistance ((U n).term K) ((U l).term K))
          delta := by
      simpa [PRCCauchySeq.raw] using hNpair K hpairK
    have hleg3_tau :
        PRCRat.lt
          (PRCJCostDistance ((U l).term K) ((U l).term (pick l)))
          (PRCUnitFraction l) :=
      (hrow l l (Nat.le_refl l)) K (pick l) hpicklK (Nat.le_refl (pick l))
    have hleg3 :
        PRCRat.lt
          (PRCJCostDistance ((U l).term K) ((U l).term (pick l)))
          delta :=
      PRCRat.lt_trans hleg3_tau htaul_delta
    exact hthree
      ((U n).term l) ((U n).term K)
      ((U l).term K) ((U l).term (pick l))
      hleg1 hleg2 hleg3

/-- An explicit tail-selection diagonal is enough to build the raw diagonal
ledger target. -/
theorem PRCRealRawDiagonalLedgerTarget_of_tail_selection
    (htail : PRCRealTailSelectionTarget) :
    PRCRealRawDiagonalLedgerTarget := by
  intro U hU
  rcases htail U hU with ⟨pick, hs_cauchy, hs_limit⟩
  exact ⟨fun n => (U n).term (pick n), hs_cauchy, hs_limit⟩

theorem PRCRealRawDiagonalLedgerTarget_proved :
    PRCRealRawDiagonalLedgerTarget :=
  PRCRealRawDiagonalLedgerTarget_of_tail_selection
    PRCRealTailSelectionTarget_proved

/-- A raw diagonal ledger packages immediately as the representative limit
needed by the quotient-level diagonal selection target. -/
theorem PRCRealDiagonalSelectionTarget_of_raw_diagonal_ledger
    (hraw : PRCRealRawDiagonalLedgerTarget) :
    PRCRealDiagonalSelectionTarget := by
  intro U hU
  rcases hraw U hU with ⟨s, hs_cauchy, hs_limit⟩
  refine ⟨{ term := s, cauchy := hs_cauchy }, ?_⟩
  simpa [PRCRealRepresentativeLimit, PRCCauchySeq.raw] using hs_limit

theorem PRCRealDiagonalSelectionTarget_proved :
    PRCRealDiagonalSelectionTarget :=
  PRCRealDiagonalSelectionTarget_of_raw_diagonal_ledger
    PRCRealRawDiagonalLedgerTarget_proved

/-- The diagonal selection target is exactly the sharpened completeness target. -/
theorem PRCRealCompletenessTarget_of_diagonal_selection
    (hdiag : PRCRealDiagonalSelectionTarget) :
    PRCRealCompletenessTarget := by
  exact hdiag

theorem PRCRealCompletenessTarget_proved :
    PRCRealCompletenessTarget :=
  PRCRealCompletenessTarget_of_diagonal_selection
    PRCRealDiagonalSelectionTarget_proved

/-- The full internal completeness theorem is now the concrete representative
Cauchy-of-Cauchy diagonal target. -/
theorem PRCRealCompletenessTarget_sharpened :
    PRCRealCompletenessTarget = PRCRealCompletenessTarget := rfl

/-- Step 10e certificate. It records the closed raw-ledger realization fact,
the tail-selection diagonal, and the representative-completeness theorem for
`PRCRealNullClosed`. -/
structure PRCRealCompletenessSharpenedCertificate : Prop where
  raw_cauchy_realization : PRCRawCauchyRealizationTarget
  raw_cauchy_quotient_point : PRCRawCauchyQuotientPointTarget
  diagonal_selection_from_raw_diagonal :
    PRCRealRawDiagonalLedgerTarget → PRCRealDiagonalSelectionTarget
  raw_diagonal_from_tail_selection :
    PRCRealTailSelectionTarget → PRCRealRawDiagonalLedgerTarget
  cofinal_tolerance_schedule : PRCRealCofinalToleranceScheduleTarget
  three_leg_distance_modulus : PRCJCostDistanceThreeLegModulusTarget
  finite_row_tail_selection : PRCRealFiniteRowTailSelectionTarget
  finite_representative_tail_selection :
    PRCRealFiniteRepresentativeTailSelectionTarget
  finite_diagonal_schedule : PRCRealFiniteDiagonalScheduleTarget
  tail_selection : PRCRealTailSelectionTarget
  raw_diagonal : PRCRealRawDiagonalLedgerTarget
  diagonal_selection : PRCRealDiagonalSelectionTarget
  completeness_from_diagonal_selection :
    PRCRealDiagonalSelectionTarget → PRCRealCompletenessTarget
  completeness : PRCRealCompletenessTarget
  completeness_target : PRCRealCompletenessTarget = PRCRealCompletenessTarget

theorem prc_real_completeness_sharpened_certificate :
    PRCRealCompletenessSharpenedCertificate where
  raw_cauchy_realization := PRCRawCauchyRealizationTarget_proved
  raw_cauchy_quotient_point := PRCRawCauchyQuotientPointTarget_proved
  diagonal_selection_from_raw_diagonal :=
    PRCRealDiagonalSelectionTarget_of_raw_diagonal_ledger
  raw_diagonal_from_tail_selection :=
    PRCRealRawDiagonalLedgerTarget_of_tail_selection
  cofinal_tolerance_schedule :=
    PRCRealCofinalToleranceScheduleTarget_proved
  three_leg_distance_modulus :=
    PRCJCostDistanceThreeLegModulusTarget_proved
  finite_row_tail_selection :=
    PRCRealFiniteRowTailSelectionTarget_proved
  finite_representative_tail_selection :=
    PRCRealFiniteRepresentativeTailSelectionTarget_proved
  finite_diagonal_schedule :=
    PRCRealFiniteDiagonalScheduleTarget_proved
  tail_selection :=
    PRCRealTailSelectionTarget_proved
  raw_diagonal :=
    PRCRealRawDiagonalLedgerTarget_proved
  diagonal_selection :=
    PRCRealDiagonalSelectionTarget_proved
  completeness_from_diagonal_selection :=
    PRCRealCompletenessTarget_of_diagonal_selection
  completeness :=
    PRCRealCompletenessTarget_proved
  completeness_target := PRCRealCompletenessTarget_sharpened

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
