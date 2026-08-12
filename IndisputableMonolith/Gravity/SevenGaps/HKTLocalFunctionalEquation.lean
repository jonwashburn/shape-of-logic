import IndisputableMonolith.Gravity.SevenGaps.HypersurfaceDeformation

/-!
# Wave C2 R5/R6 groundwork: local-profile functional equation (n = 2)

Landed at n = 2 (mirrors HamDyn). Reduces Dyn ham_ham for local profiles to
momDensity_j = h_b(j) * h_p(j+1). R6 attack surface; nothing proves rigidity.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace HKTLocalFunctionalEquation

open HypersurfaceDeformation

noncomputable section

open Finset

abbrev LocalHamProfile : Type := ℝ → ℝ → ℝ → ℝ

def LocalHamFromProfile (h : LocalHamProfile) (N : ZMod 2 → ℝ)
    (x : PhaseSpace 2) : ℝ :=
  ∑ j : ZMod 2, N j * h (x.1 j) (x.1 (j + 1)) (x.2 j)

structure LocalHamSmooth (h : LocalHamProfile) where
  ha : LocalHamProfile
  hb : LocalHamProfile
  hp : LocalHamProfile
  hasFDerivCell :
    ∀ (j : ZMod 2) (x : PhaseSpace 2),
      HasFDerivAt (fun y : PhaseSpace 2 => h (y.1 j) (y.1 (j + 1)) (y.2 j))
        ((ha (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ j +
          (hb (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ (j + 1) +
          (hp (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordP j)
        x

def localCellD (h : LocalHamProfile) (S : LocalHamSmooth h) (j : ZMod 2)
    (x : PhaseSpace 2) : PhaseSpace 2 →L[ℝ] ℝ :=
  (S.ha (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ j +
    (S.hb (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordQ (j + 1) +
    (S.hp (x.1 j) (x.1 (j + 1)) (x.2 j)) • coordP j

lemma hasFDerivAt_localCell (h : LocalHamProfile) (S : LocalHamSmooth h)
    (j : ZMod 2) (x : PhaseSpace 2) :
    HasFDerivAt (fun y : PhaseSpace 2 => h (y.1 j) (y.1 (j + 1)) (y.2 j))
      (localCellD h S j x) x :=
  S.hasFDerivCell j x

def LocalHamFromProfileD (h : LocalHamProfile) (S : LocalHamSmooth h)
    (N : ZMod 2 → ℝ) (x : PhaseSpace 2) : PhaseSpace 2 →L[ℝ] ℝ :=
  ∑ j : ZMod 2, (N j) • localCellD h S j x

lemma hasFDerivAt_LocalHamFromProfile (h : LocalHamProfile) (S : LocalHamSmooth h)
    (N : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    HasFDerivAt (LocalHamFromProfile h N) (LocalHamFromProfileD h S N x) x := by
  unfold LocalHamFromProfile LocalHamFromProfileD
  exact HasFDerivAt.fun_sum fun j _ =>
    (hasFDerivAt_localCell h S j x).const_mul (N j)

theorem differentiable_LocalHamFromProfile (h : LocalHamProfile)
    (S : LocalHamSmooth h) (N : ZMod 2 → ℝ) :
    Differentiable ℝ (LocalHamFromProfile h N) :=
  fun x => (hasFDerivAt_LocalHamFromProfile h S N x).differentiableAt

private lemma cellD_pdir (h : LocalHamProfile) (S : LocalHamSmooth h)
    (j k : ZMod 2) (x : PhaseSpace 2) :
    localCellD h S j x (0, Pi.single k 1)
      = S.hp (x.1 j) (x.1 (j + 1)) (x.2 j) * (if j = k then (1 : ℝ) else 0) := by
  simp only [localCellD, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    coordQ_apply, coordP_apply, Pi.single_apply]
  by_cases hjk : j = k <;> simp [hjk]

private lemma cellD_qdir (h : LocalHamProfile) (S : LocalHamSmooth h)
    (j k : ZMod 2) (x : PhaseSpace 2) :
    localCellD h S j x (Pi.single k 1, 0)
      = S.ha (x.1 j) (x.1 (j + 1)) (x.2 j) * (if j = k then (1 : ℝ) else 0)
        + S.hb (x.1 j) (x.1 (j + 1)) (x.2 j) * (if j + 1 = k then (1 : ℝ) else 0) := by
  simp only [localCellD, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    coordQ_apply, coordP_apply, Pi.single_apply]
  by_cases hjk : j = k
  · subst hjk
    have hjp : (j + 1 : ZMod 2) ≠ j := by
      intro h
      have : (1 : ZMod 2) = 0 := by
        calc (1 : ZMod 2) = j + 1 - j := by ring
          _ = j - j := by rw [h]
          _ = 0 := by ring
      exact absurd this (by decide)
    simp [hjp]
  · by_cases hjp : j + 1 = k
    · simp [hjk, hjp]
    · simp [hjk, hjp]

theorem pderivP_LocalHamFromProfile (h : LocalHamProfile) (S : LocalHamSmooth h)
    (N : ZMod 2 → ℝ) (k : ZMod 2) (x : PhaseSpace 2) :
    pderivP (LocalHamFromProfile h N) k x
      = N k * S.hp (x.1 k) (x.1 (k + 1)) (x.2 k) := by
  rw [pderivP, (hasFDerivAt_LocalHamFromProfile h S N x).fderiv,
    LocalHamFromProfileD, ContinuousLinearMap.sum_apply]
  have step : ∀ j : ZMod 2,
      (((N j) • localCellD h S j x : PhaseSpace 2 →L[ℝ] ℝ)
        ((0, Pi.single k 1) : PhaseSpace 2))
      = (N j * S.hp (x.1 j) (x.1 (j + 1)) (x.2 j)) *
          (if j = k then (1 : ℝ) else 0) := by
    intro j
    simp only [ContinuousLinearMap.smul_apply, cellD_pdir, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun j _ => step j, sum_mul_ite]

theorem pderivQ_LocalHamFromProfile (h : LocalHamProfile) (S : LocalHamSmooth h)
    (N : ZMod 2 → ℝ) (k : ZMod 2) (x : PhaseSpace 2) :
    pderivQ (LocalHamFromProfile h N) k x
      = N k * S.ha (x.1 k) (x.1 (k + 1)) (x.2 k)
        + N (k - 1) * S.hb (x.1 (k - 1)) (x.1 k) (x.2 (k - 1)) := by
  rw [pderivQ, (hasFDerivAt_LocalHamFromProfile h S N x).fderiv,
    LocalHamFromProfileD, ContinuousLinearMap.sum_apply]
  have step : ∀ j : ZMod 2,
      (((N j) • localCellD h S j x : PhaseSpace 2 →L[ℝ] ℝ)
        ((Pi.single k 1, 0) : PhaseSpace 2))
      = (N j * S.ha (x.1 j) (x.1 (j + 1)) (x.2 j)) *
            (if j = k then (1 : ℝ) else 0)
        + (N j * S.hb (x.1 j) (x.1 (j + 1)) (x.2 j)) *
            (if j + 1 = k then (1 : ℝ) else 0) := by
    intro j
    simp only [ContinuousLinearMap.smul_apply, cellD_qdir, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun j _ => step j, Finset.sum_add_distrib,
    sum_mul_ite, sum_mul_ite_add]
  have e : k - 1 + 1 = k := by ring
  simp only [e]

def localHamHamCoefficient (h : LocalHamProfile) (S : LocalHamSmooth h)
    (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  S.hb (x.1 j) (x.1 (j + 1)) (x.2 j) *
    S.hp (x.1 (j + 1)) (x.1 (j + 2)) (x.2 (j + 1))

theorem local_profile_ham_ham_form (h : LocalHamProfile) (S : LocalHamSmooth h)
    (N M : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (LocalHamFromProfile h N) (LocalHamFromProfile h M) x
      = ∑ j : ZMod 2,
          (N j * M (j + 1) - M j * N (j + 1)) *
            localHamHamCoefficient h S x j := by
  unfold bracket localHamHamCoefficient
  simp_rw [pderivQ_LocalHamFromProfile h S, pderivP_LocalHamFromProfile h S]
  have step1 :
      (∑ k : ZMod 2,
          ((N k * S.ha (x.1 k) (x.1 (k + 1)) (x.2 k)
              + N (k - 1) * S.hb (x.1 (k - 1)) (x.1 k) (x.2 (k - 1))) *
            (M k * S.hp (x.1 k) (x.1 (k + 1)) (x.2 k))
            - (N k * S.hp (x.1 k) (x.1 (k + 1)) (x.2 k)) *
              (M k * S.ha (x.1 k) (x.1 (k + 1)) (x.2 k)
                + M (k - 1) * S.hb (x.1 (k - 1)) (x.1 k) (x.2 (k - 1)))))
        = ∑ k : ZMod 2,
            (N (k - 1) * M k - M (k - 1) * N k) *
              (S.hb (x.1 (k - 1)) (x.1 k) (x.2 (k - 1)) *
                S.hp (x.1 k) (x.1 (k + 1)) (x.2 k)) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [step1]
  refine sum_reindex (n := 2) 1
    (fun k =>
      (N (k - 1) * M k - M (k - 1) * N k) *
        (S.hb (x.1 (k - 1)) (x.1 k) (x.2 (k - 1)) *
          S.hp (x.1 k) (x.1 (k + 1)) (x.2 k))) _
    fun j => ?_
  have e1 : j + 1 - 1 = j := by ring
  have e2 : j + 1 + 1 = j + 2 := by ring
  simp only [e1, e2]

def LocalProfileMomDensityIdentity (h : LocalHamProfile) (_S : LocalHamSmooth h)
    (momDensity : PhaseSpace 2 → ZMod 2 → ℝ) : Prop :=
  ∀ (N M : ZMod 2 → ℝ) (x : PhaseSpace 2),
    bracket (LocalHamFromProfile h N) (LocalHamFromProfile h M) x
      = ∑ j : ZMod 2,
          (N j * M (j + 1) - M j * N (j + 1)) * momDensity x j

theorem localHamHamCoefficient_witnesses_identity (h : LocalHamProfile)
    (S : LocalHamSmooth h) :
    LocalProfileMomDensityIdentity h S (localHamHamCoefficient h S) := by
  intro N M x
  exact local_profile_ham_ham_form h S N M x

/-- General-n packaging Prop (defined; proved form is the n=2 theorem above). -/
def LocalProfileHamHamFormGeneral (n : ℕ) [NeZero n]
    (h : LocalHamProfile) (hb hp : LocalHamProfile) : Prop :=
  ∀ (N M : ZMod n → ℝ) (x : PhaseSpace n),
    bracket (fun y => ∑ j : ZMod n, N j * h (y.1 j) (y.1 (j + 1)) (y.2 j))
      (fun y => ∑ j : ZMod n, M j * h (y.1 j) (y.1 (j + 1)) (y.2 j)) x
      = ∑ j : ZMod n,
          (N j * M (j + 1) - M j * N (j + 1)) *
            (hb (x.1 j) (x.1 (j + 1)) (x.2 j) *
              hp (x.1 (j + 1)) (x.1 (j + 2)) (x.2 (j + 1)))

end
end HKTLocalFunctionalEquation
end SevenGaps
end Gravity
end IndisputableMonolith
