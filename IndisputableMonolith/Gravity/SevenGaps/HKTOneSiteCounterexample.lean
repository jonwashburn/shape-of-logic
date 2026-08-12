import IndisputableMonolith.Gravity.SevenGaps.HypersurfaceDeformation

/-!
# Wave C2 R5/R6 groundwork: HKT rigidity falsified as stated (n = 1)

Codex adjudication (`D-gap5-hkt-design-20260722`) found that
`HKTRigidityStatement` is **false as stated**: on the degenerate one-site
lattice `ZMod 1`, every discrete difference and Wronskian vanishes, so a
quartic kinetic density with zero momentum density satisfies every field of
`HojmanKucharTeitelboimTarget 1` while escaping the quadratic pin.

This module lands that counterexample against the real fderiv bracket. It does
**not** flip `gap5_constraint_recovery` and does **not** prove any rigidity
statement.

The ledger terminal `hojman_pins_general_relativity` must bind to a repaired
statement (`HKTRigidityStatementDyn`, or an n-restricted + nondegenerate form),
with this counterexample disclosed.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace HKTOneSiteCounterexample

open HypersurfaceDeformation

noncomputable section

open Finset

/-! ## Quartic one-site densities -/

/-- MODEL. Quartic kinetic density on one site: `h_j = π_j^4`. -/
def quarticHamDensity (x : PhaseSpace 1) (j : ZMod 1) : ℝ :=
  (x.2 j) ^ 4

/-- MODEL. Vanishing momentum density. -/
def zeroMomDensity (_x : PhaseSpace 1) (_j : ZMod 1) : ℝ :=
  0

/-- Smeared quartic Hamiltonian. -/
def quarticHam (N : ZMod 1 → ℝ) (x : PhaseSpace 1) : ℝ :=
  ∑ j : ZMod 1, N j * quarticHamDensity x j

/-- Frechet derivative matching `HasFDerivAt.pow` then `const_mul`. -/
def quarticHamD (N : ZMod 1 → ℝ) (x : PhaseSpace 1) : PhaseSpace 1 →L[ℝ] ℝ :=
  ∑ i : ZMod 1, N i • ((4 • (x.2 i) ^ 3) • coordP i)

lemma hasFDerivAt_quarticHam (N : ZMod 1 → ℝ) (x : PhaseSpace 1) :
    HasFDerivAt (quarticHam N) (quarticHamD N x) x := by
  unfold quarticHam quarticHamD quarticHamDensity
  exact HasFDerivAt.fun_sum fun i _ =>
    ((hasFDerivAt_coord_snd i x).pow 4).const_mul (N i)

theorem differentiable_quarticHam (N : ZMod 1 → ℝ) :
    Differentiable ℝ (quarticHam N) :=
  fun x => (hasFDerivAt_quarticHam N x).differentiableAt

lemma pderivQ_quarticHam (N : ZMod 1 → ℝ) (j : ZMod 1) (x : PhaseSpace 1) :
    pderivQ (quarticHam N) j x = 0 := by
  rw [pderivQ, (hasFDerivAt_quarticHam N x).fderiv, quarticHamD,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [coordP]

/-- THEOREM. Quartic–quartic bracket vanishes: both generators depend only on
momentum, so all configuration partials are zero. -/
theorem bracket_quarticHam_quarticHam (N M : ZMod 1 → ℝ) (x : PhaseSpace 1) :
    bracket (quarticHam N) (quarticHam M) x = 0 := by
  simp only [bracket, pderivQ_quarticHam]
  exact Finset.sum_eq_zero fun _ _ => by ring

lemma zeroMom_eq_zero (w : ZMod 1 → ℝ) :
    (fun x : PhaseSpace 1 => ∑ j : ZMod 1, w j * zeroMomDensity x j)
      = fun _ => (0 : ℝ) := by
  funext y
  simp [zeroMomDensity]

lemma differentiable_zeroMom (w : ZMod 1 → ℝ) :
    Differentiable ℝ (fun x : PhaseSpace 1 => ∑ j : ZMod 1, w j * zeroMomDensity x j) := by
  rw [zeroMom_eq_zero]
  exact differentiable_const 0

lemma pderivQ_zeroMom (w : ZMod 1 → ℝ) (i : ZMod 1) (x : PhaseSpace 1) :
    pderivQ (fun y => ∑ j : ZMod 1, w j * zeroMomDensity y j) i x = 0 := by
  unfold pderivQ
  rw [zeroMom_eq_zero w]
  simp

lemma pderivP_zeroMom (w : ZMod 1 → ℝ) (i : ZMod 1) (x : PhaseSpace 1) :
    pderivP (fun y => ∑ j : ZMod 1, w j * zeroMomDensity y j) i x = 0 := by
  unfold pderivP
  rw [zeroMom_eq_zero w]
  simp

lemma bracket_zeroMom_any (w : ZMod 1 → ℝ) (G : PhaseSpace 1 → ℝ) (x : PhaseSpace 1) :
    bracket (fun y => ∑ j : ZMod 1, w j * zeroMomDensity y j) G x = 0 := by
  simp only [bracket, pderivQ_zeroMom, pderivP_zeroMom]
  exact Finset.sum_eq_zero fun _ _ => by ring

lemma zmod1_one_eq_zero : (1 : ZMod 1) = 0 := by decide

lemma zmod1_add_self (j : ZMod 1) : j + 1 = j := by
  simp [zmod1_one_eq_zero]

lemma zmod1_wronskian_zero (N M : ZMod 1 → ℝ) (j : ZMod 1) :
    N j * M (j + 1) - M j * N (j + 1) = 0 := by
  rw [zmod1_add_self]
  ring

lemma zmod1_lapse_diff_zero (N : ZMod 1 → ℝ) (j : ZMod 1) :
    N (j + 1) - N j = 0 := by
  rw [zmod1_add_self]
  ring

/-- DISCLOSURE. On `ZMod 1` every discrete Wronskian and every discrete lapse
difference vanishes identically (`j + 1 = j`). The Dirac `mom_ham` / `ham_ham`
right-hand sides are therefore vacuous for every density pair. -/
theorem one_site_wronskians_vacuous (N M : ZMod 1 → ℝ) (j : ZMod 1) :
    N j * M (j + 1) - M j * N (j + 1) = 0 ∧ N (j + 1) - N j = 0 :=
  ⟨zmod1_wronskian_zero N M j, zmod1_lapse_diff_zero N j⟩

/-! ## The counterexample inhabitant -/

/-- THEOREM (inhabitant). The quartic one-site densities satisfy every real
field of `HojmanKucharTeitelboimTarget 1`. On `ZMod 1`, `j + 1 = j`, so
Wronskians and discrete lapse derivatives vanish; the Hamiltonian depends only
on momentum, so its self-bracket vanishes by vanishing configuration
partials; the momentum density is identically zero. -/
def quarticOneSiteHKT : HojmanKucharTeitelboimTarget 1 where
  hamDensity := quarticHamDensity
  momDensity := zeroMomDensity
  ham_differentiable := differentiable_quarticHam
  mom_differentiable := differentiable_zeroMom
  ham_local := by
    intro x y j _ _ hp
    simp [quarticHamDensity, hp]
  ham_covariant := by
    intro x a j
    simp [quarticHamDensity]
  mom_mom := by
    intro v w x
    exact bracket_zeroMom_any v (fun y => ∑ j : ZMod 1, w j * zeroMomDensity y j) x
  mom_ham := by
    intro w N x
    rw [bracket_zeroMom_any]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [zmod1_lapse_diff_zero]
    ring
  ham_ham := by
    intro N M x
    change bracket (quarticHam N) (quarticHam M) x
        = ∑ j : ZMod 1, (N j * M (j + 1) - M j * N (j + 1)) * zeroMomDensity x j
    rw [bracket_quarticHam_quarticHam]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    simp [zeroMomDensity]

/-! ## Falsification of unrestricted rigidity -/

/-- Constant-configuration phase point with momentum `p` at the unique site. -/
def momPoint (p : ℝ) : PhaseSpace 1 :=
  (fun _ => 0, fun _ => p)

private lemma momPoint_q (p : ℝ) (j : ZMod 1) : (momPoint p).1 j = 0 := rfl
private lemma momPoint_p (p : ℝ) (j : ZMod 1) : (momPoint p).2 j = p := rfl

/-- THEOREM (headline falsification). `HKTRigidityStatement 1` is false:
`quarticOneSiteHKT` inhabits the target class, but `π^4` is not of the form
`cKin π² + cVac` on `ZMod 1` (the gradient slot vanishes by `j + 1 = j`). -/
theorem not_HKTRigidityStatement_one : ¬ HKTRigidityStatement 1 := by
  intro h
  obtain ⟨cKin, cGrad, cVac, hform⟩ := h quarticOneSiteHKT
  have form (p : ℝ) : p ^ 4 = cKin * (p * p) + cVac := by
    have hj := hform (momPoint p) (0 : ZMod 1)
    -- hj : quarticOneSiteHKT.hamDensity _ _ = cKin * .. + cGrad * .. + cVac
    change quarticHamDensity (momPoint p) (0 : ZMod 1)
        = cKin * ((momPoint p).2 0 * (momPoint p).2 0)
          + cGrad *
              (((momPoint p).1 ((0 : ZMod 1) + 1) - (momPoint p).1 0) *
                ((momPoint p).1 ((0 : ZMod 1) + 1) - (momPoint p).1 0))
          + cVac at hj
    simp only [quarticHamDensity, momPoint_p, momPoint_q, zmod1_add_self,
      sub_self, mul_zero, add_zero] at hj
    exact hj
  have hVac : cVac = 0 := by
    have := form 0
    norm_num at this
    exact this.symm
  have hKin : cKin = 1 := by
    have := form 1
    rw [hVac] at this
    norm_num at this
    linarith
  have boom := form 2
  rw [hVac, hKin] at boom
  norm_num at boom

end
end HKTOneSiteCounterexample
end SevenGaps
end Gravity
end IndisputableMonolith
