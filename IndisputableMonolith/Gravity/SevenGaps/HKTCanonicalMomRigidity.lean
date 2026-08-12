import IndisputableMonolith.Gravity.SevenGaps.HKTCanonicalMomTarget
import IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

/-!
# Wave C2 gap5: CanonicalMom rigidity session C1 (FE extraction)

Binding design: `D-qg-hkt-rigidity-route-20260722`.

Session C1 lands:
1. `profiled_ham_ham_alternating_FE` (complete): the alternating FE forced by
   `ham_ham` + local/structure/canonical profiles at `n = 2`;
2. algebraic PDE sub-lemmas and precisely-stated defined Props for the
   remaining differentiation/integration wall;
3. assembly skeleton `canonicalMom_rigidity_of_FE_solution` so later sessions
   only owe the PDE core.

Do NOT flip `gap5_constraint_recovery`. Do NOT claim
`HKTRigidityStatementPointSplitDynN2Canonical` as a theorem.

Prover decoys (binding): no uniqueness-only-over-`LocalHamFromProfile`;
no ADM-baked subclass; no pointwise coefficient extraction from the
alternating identity (the FE below is exactly the alternating difference).
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace HKTCanonicalMomRigidity

open HypersurfaceDeformation DynamicStructureBracket
open HKTPointSplitTarget HKTPointSplitStrong HKTLocalFunctionalEquation
open HKTCanonicalMomTarget FullTheoryLedger

noncomputable section

open Finset

private lemma zmod2_zero_add_one : (0 : ZMod 2) + 1 = 1 := by decide
private lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide
private lemma zmod2_zero_add_two : (0 : ZMod 2) + 2 = 0 := by decide
private lemma zmod2_one_add_two : (1 : ZMod 2) + 2 = 1 := by decide

/-! ## Phase point for FE specialization -/

/-- Configuration/momentum cell `(q₀,q₁,π₀,π₁) = (a,b,p,r)`. -/
def fePhase (a b p r : ℝ) : PhaseSpace 2 :=
  (fun j : ZMod 2 => if j = (0 : ZMod 2) then a else b,
    fun j : ZMod 2 => if j = (0 : ZMod 2) then p else r)

theorem fePhase_coords (a b p r : ℝ) :
    (fePhase a b p r).1 (0 : ZMod 2) = a ∧
      (fePhase a b p r).1 (1 : ZMod 2) = b ∧
        (fePhase a b p r).2 (0 : ZMod 2) = p ∧
          (fePhase a b p r).2 (1 : ZMod 2) = r := by
  simp [fePhase]

/-! ## Profiled smear identification -/

theorem hamDensity_smear_eq_LocalHamFromProfile
    (T : HKTPointSplitTargetDynCanonicalMom) (h : LocalHamProfile)
    (hHam : ∀ (x : PhaseSpace 2) (j : ZMod 2),
      T.hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j))
    (N : ZMod 2 → ℝ) :
    (fun y : PhaseSpace 2 => ∑ j : ZMod 2, N j * T.hamDensity y j) =
      LocalHamFromProfile h N := by
  funext y
  simp only [LocalHamFromProfile]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hHam y j]

/-! ## Alternating difference at Kronecker lapses -/

theorem localHamHamCoefficient_delta01 (h : LocalHamProfile)
    (S : LocalHamSmooth h) (x : PhaseSpace 2) :
    (∑ j : ZMod 2,
        (delta0 j * delta1 (j + 1) - delta1 j * delta0 (j + 1)) *
          localHamHamCoefficient h S x j) =
      localHamHamCoefficient h S x (0 : ZMod 2) -
        localHamHamCoefficient h S x (1 : ZMod 2) := by
  rw [sum_zmod2, zmod2_zero_add_one, zmod2_one_add_one]
  simp [delta0, delta1]
  ring

theorem structure_mom_delta01 (structureFunction momDensity : PhaseSpace 2 → ZMod 2 → ℝ)
    (x : PhaseSpace 2) :
    (∑ j : ZMod 2,
        (delta0 j * delta1 (j + 1) - delta1 j * delta0 (j + 1)) *
          (structureFunction x j * momDensity x j)) =
      structureFunction x (0 : ZMod 2) * momDensity x (0 : ZMod 2) -
        structureFunction x (1 : ZMod 2) * momDensity x (1 : ZMod 2) := by
  rw [sum_zmod2, zmod2_zero_add_one, zmod2_one_add_one]
  simp [delta0, delta1]
  ring

/-! ## FE EXTRACTION (session C1 load-bearing) -/

/-- THEOREM. Alternating functional equation forced by CanonicalMom `ham_ham`
at `n = 2`.

Route: unpack `local_ham_profile` / `structure_profile` / `canonical_mom`;
rewrite the Poisson-bracket field via `local_profile_ham_ham_form`; instantiate
lapses `N = delta0`, `M = delta1` and the phase cell `(a,b,p,r)`.

Honest shape note (decoy 3): at `n = 2` the identity only determines the
alternating difference `C₀ - C₁ = R₀ - R₁`. Specializing the Kronecker lapses
and the phase cell yields exactly the clean bilinear form below (not a
weaker residual). Pointwise equality `Cⱼ = Rⱼ` is NOT claimed. -/
theorem profiled_ham_ham_alternating_FE
    (T : HKTPointSplitTargetDynCanonicalMom) :
    ∃ (h : LocalHamProfile) (S : LocalHamSmooth h) (g : ℝ → ℝ) (cMom : ℝ),
      cMom ≠ 0 ∧
        ∀ (a b p r : ℝ),
          S.hb a b p * S.hp b a r - S.hb b a r * S.hp a b p =
            cMom * (b - a) * (g a * r + g b * p) := by
  obtain ⟨h, S, hHam⟩ := T.local_ham_profile
  obtain ⟨g, hG⟩ := T.structure_profile
  obtain ⟨cMom, hcMom, hMom⟩ := T.canonical_mom
  refine ⟨h, S, g, cMom, hcMom, ?_⟩
  intro a b p r
  let x : PhaseSpace 2 := fePhase a b p r
  have hx0 : x.1 (0 : ZMod 2) = a := by simp [x, fePhase]
  have hx1 : x.1 (1 : ZMod 2) = b := by simp [x, fePhase]
  have hp0 : x.2 (0 : ZMod 2) = p := by simp [x, fePhase]
  have hp1 : x.2 (1 : ZMod 2) = r := by simp [x, fePhase]
  -- Identify smeared densities with the local-profile engine.
  have hEq0 := hamDensity_smear_eq_LocalHamFromProfile T h hHam delta0
  have hEq1 := hamDensity_smear_eq_LocalHamFromProfile T h hHam delta1
  -- Two expressions for the same bracket.
  have hProf := local_profile_ham_ham_form h S delta0 delta1 x
  have hTarget := T.ham_ham delta0 delta1 x
  -- Collapse alternating sums at Kronecker lapses.
  have hProf' :
      bracket (LocalHamFromProfile h delta0) (LocalHamFromProfile h delta1) x =
        localHamHamCoefficient h S x (0 : ZMod 2) -
          localHamHamCoefficient h S x (1 : ZMod 2) :=
    hProf.trans (localHamHamCoefficient_delta01 h S x)
  have hTarget' :
      bracket (fun y => ∑ j : ZMod 2, delta0 j * T.hamDensity y j)
          (fun y => ∑ j : ZMod 2, delta1 j * T.hamDensity y j) x =
        T.structureFunction x (0 : ZMod 2) * T.momDensity x (0 : ZMod 2) -
          T.structureFunction x (1 : ZMod 2) * T.momDensity x (1 : ZMod 2) :=
    hTarget.trans (structure_mom_delta01 T.structureFunction T.momDensity x)
  -- Transport target bracket onto LocalHamFromProfile.
  have hBracket :
      bracket (LocalHamFromProfile h delta0) (LocalHamFromProfile h delta1) x =
        T.structureFunction x (0 : ZMod 2) * T.momDensity x (0 : ZMod 2) -
          T.structureFunction x (1 : ZMod 2) * T.momDensity x (1 : ZMod 2) := by
    simpa [hEq0, hEq1] using hTarget'
  have hAlt :
      localHamHamCoefficient h S x (0 : ZMod 2) -
          localHamHamCoefficient h S x (1 : ZMod 2) =
        T.structureFunction x (0 : ZMod 2) * T.momDensity x (0 : ZMod 2) -
          T.structureFunction x (1 : ZMod 2) * T.momDensity x (1 : ZMod 2) :=
    hProf'.symm.trans hBracket
  -- Expand coefficient / structure / mom at the phase cell.
  have hC0 :
      localHamHamCoefficient h S x (0 : ZMod 2) =
        S.hb a b p * S.hp b a r := by
    simp only [localHamHamCoefficient, zmod2_zero_add_one, zmod2_zero_add_two]
    rw [hx0, hx1, hp0, hp1]
  have hC1 :
      localHamHamCoefficient h S x (1 : ZMod 2) =
        S.hb b a r * S.hp a b p := by
    simp only [localHamHamCoefficient, zmod2_one_add_one, zmod2_one_add_two]
    rw [hx0, hx1, hp0, hp1]
  have hR0 :
      T.structureFunction x (0 : ZMod 2) * T.momDensity x (0 : ZMod 2) =
        g a * (cMom * r * (b - a)) := by
    rw [hG x (0 : ZMod 2), hMom x (0 : ZMod 2), zmod2_zero_add_one, hx0, hx1, hp1]
  have hR1 :
      T.structureFunction x (1 : ZMod 2) * T.momDensity x (1 : ZMod 2) =
        g b * (cMom * p * (a - b)) := by
    rw [hG x (1 : ZMod 2), hMom x (1 : ZMod 2), zmod2_one_add_one, hx0, hx1, hp0]
  -- Close: C0 - C1 = R0 - R1 rearranges to the bilinear FE.
  have hEq := hAlt
  rw [hC0, hC1, hR0, hR1] at hEq
  -- hEq : LHS = g a * (cMom * r * (b - a)) - g b * (cMom * p * (a - b))
  have hR :
      g a * (cMom * r * (b - a)) - g b * (cMom * p * (a - b)) =
        cMom * (b - a) * (g a * r + g b * p) := by ring
  exact hEq.trans hR

/-! ## Algebraic FE specializations (PDE groundwork) -/

/-- Specialize the alternating FE at `r = 0`. -/
theorem fe_at_r_zero (T : HKTPointSplitTargetDynCanonicalMom) :
    ∃ (h : LocalHamProfile) (S : LocalHamSmooth h) (g : ℝ → ℝ) (cMom : ℝ),
      cMom ≠ 0 ∧
        ∀ (a b p : ℝ),
          S.hb a b p * S.hp b a 0 - S.hb b a 0 * S.hp a b p =
            cMom * (b - a) * (g b * p) := by
  obtain ⟨h, S, g, cMom, hc, hFE⟩ := profiled_ham_ham_alternating_FE T
  refine ⟨h, S, g, cMom, hc, ?_⟩
  intro a b p
  simpa using hFE a b p 0

/-- Specialize the alternating FE at `p = 0`. -/
theorem fe_at_p_zero (T : HKTPointSplitTargetDynCanonicalMom) :
    ∃ (h : LocalHamProfile) (S : LocalHamSmooth h) (g : ℝ → ℝ) (cMom : ℝ),
      cMom ≠ 0 ∧
        ∀ (a b r : ℝ),
          S.hb a b 0 * S.hp b a r - S.hb b a r * S.hp a b 0 =
            cMom * (b - a) * (g a * r) := by
  obtain ⟨h, S, g, cMom, hc, hFE⟩ := profiled_ham_ham_alternating_FE T
  refine ⟨h, S, g, cMom, hc, ?_⟩
  intro a b r
  simpa using hFE a b 0 r

/-! ## PDE ansatz Props (session C2 discharges these) -/

/-- DEFINED. `S.hp` is linear in its momentum argument.
Session C2 must force this by differentiating the FE in `r` after a ContDiff
strengthening of the profile class. -/
def HpLinearInP (h : LocalHamProfile) (S : LocalHamSmooth h) : Prop :=
  ∃ kinCoeff : ℝ → ℝ → ℝ, ∀ (a b p : ℝ), S.hp a b p = kinCoeff a b * p

/-- DEFINED. `S.hb` is independent of its momentum argument.
Session C2 must force this after `HpLinearInP` by comparing FE coefficients. -/
def HbPIndependent (h : LocalHamProfile) (S : LocalHamSmooth h) : Prop :=
  ∀ (a b p p' : ℝ), S.hb a b p = S.hb a b p'

/-- C2 strengthening obligation: `LocalHamSmooth` identifies `ha/hb/hp` as
phase-space Frechet coefficients of `h ∘ coords`, but does **not** make
`S.hb` / `S.hp` differentiable as maps on `ℝ`. Differentiating the FE in the
momentum slot `r` is therefore unlicensed on the present class. Re-scope:
require `ContDiff ℝ 2` of the profile as a map `ℝ × ℝ × ℝ → ℝ` (or an
equivalent slotwise `HasDerivAt` package) before the ∂/∂r isolation step. -/
def LocalHamSmoothContDiff2Obligation (h : LocalHamProfile) : Prop :=
  ContDiff ℝ 2 (fun t : ℝ × ℝ × ℝ => h t.1 t.2.1 t.2.2)

/-- Algebraic core of the PDE argument: under the linear-`hp` /
momentum-independent-`hb` ansatz, the FE forces the gradient coupling
`hb(a,b) · kinCoeff(b,a) = cMom · (b-a) · g(a)`. -/
theorem hb_coupling_of_linear_ansatz
    (hb hp : LocalHamProfile) (g : ℝ → ℝ) (cMom : ℝ) (kinCoeff : ℝ → ℝ → ℝ)
    (hFE : ∀ (a b p r : ℝ),
      hb a b p * hp b a r - hb b a r * hp a b p =
        cMom * (b - a) * (g a * r + g b * p))
    (hHp : ∀ (a b p : ℝ), hp a b p = kinCoeff a b * p)
    (hHb : ∀ (a b p : ℝ), hb a b p = hb a b 0) :
    ∀ (a b : ℝ), hb a b 0 * kinCoeff b a = cMom * (b - a) * g a := by
  intro a b
  -- Specialize FE at p = 0, r = 1.
  have h0 := hFE a b 0 1
  have hHpba : hp b a 1 = kinCoeff b a := by simpa using hHp b a 1
  have hHpab : hp a b 0 = 0 := by simpa using hHp a b 0
  have hHbab : hb b a 1 = hb b a 0 := hHb b a 1
  rw [hHpba, hHpab, hHbab, mul_zero, sub_zero] at h0
  -- h0 : hb a b 0 * kinCoeff b a = cMom * (b - a) * (g a * 1 + g b * 0)
  simpa [mul_one, mul_zero, add_zero] using h0

/-- Same ansatz forces the swapped coupling used by coefficient matching. -/
theorem hb_coupling_swapped_of_linear_ansatz
    (hb hp : LocalHamProfile) (g : ℝ → ℝ) (cMom : ℝ) (kinCoeff : ℝ → ℝ → ℝ)
    (hFE : ∀ (a b p r : ℝ),
      hb a b p * hp b a r - hb b a r * hp a b p =
        cMom * (b - a) * (g a * r + g b * p))
    (hHp : ∀ (a b p : ℝ), hp a b p = kinCoeff a b * p)
    (hHb : ∀ (a b p : ℝ), hb a b p = hb a b 0) :
    ∀ (a b : ℝ), hb b a 0 * kinCoeff a b = cMom * (a - b) * g b := by
  intro a b
  exact hb_coupling_of_linear_ansatz hb hp g cMom kinCoeff hFE hHp hHb b a

/-! ## PDE lemma Prop (hard wall; not closed this session) -/

/-- DEFINED. Full PDE conclusion: the local profile is the ADM quadratic
with `cMom = 4 cKin cGrad`. Session C1 leaves this open; C2+ discharge via
ContDiff strengthening → `HpLinearInP` → `HbPIndependent` → integrate
partials back to `h`. -/
def SolveProfileFEQuadratic (T : HKTPointSplitTargetDynCanonicalMom) : Prop :=
  ∃ (h : LocalHamProfile) (_S : LocalHamSmooth h) (g : ℝ → ℝ)
      (cKin cGrad cVac cMom : ℝ),
    cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
      (∀ (x : PhaseSpace 2) (j : ZMod 2),
        T.hamDensity x j = h (x.1 j) (x.1 (j + 1)) (x.2 j)) ∧
      (∀ (x : PhaseSpace 2) (j : ZMod 2),
        T.structureFunction x j = g (x.1 j)) ∧
      (∀ (a b p : ℝ),
        h a b p =
          cKin * (p * p) +
            cGrad * (g a * ((b - a) * (b - a))) + cVac) ∧
      (∀ (x : PhaseSpace 2) (j : ZMod 2),
        T.momDensity x j =
          cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j))

/-- Documentary: the PDE lemma as a universal Prop over CanonicalMom. -/
def solve_profile_FE_quadratic : Prop :=
  ∀ T : HKTPointSplitTargetDynCanonicalMom, SolveProfileFEQuadratic T

/-! ## Sanity: honest HamDyn inhabits the PDE Prop -/

theorem hamDyn_solve_profile_FE_quadratic :
    SolveProfileFEQuadratic hamDynPointSplitTargetCanonicalMom := by
  refine ⟨hamDynLocalProfile, hamDynLocalSmooth, fun q => 1 + q * q,
    (1 / 2 : ℝ), (1 / 2 : ℝ), (0 : ℝ), (1 : ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · ring
  · intro x j
    simpa using hamDynDensity_eq_localProfile x j
  · intro x j
    simpa using structureDyn_eq_g x j
  · intro a b p
    simp only [hamDynLocalProfile]
    ring
  · intro x j
    simpa using momDynDensity_canonical x j

/-! ## ASSEMBLY SKELETON -/

/-- THEOREM. Glue: a `SolveProfileFEQuadratic` witness for `T` implies the
CanonicalMom rigidity conclusion for `T`. Later sessions only owe the PDE
core. -/
theorem canonicalMom_rigidity_of_FE_solution
    (T : HKTPointSplitTargetDynCanonicalMom)
    (hsolve : SolveProfileFEQuadratic T) :
    ∃ cKin cGrad cVac cMom : ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (T.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              cVac) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          T.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) := by
  obtain ⟨h, _S, g, cKin, cGrad, cVac, cMom, hKin, hGrad, _hcMom, hRel, hHam, hG, hQuad,
    hMom⟩ := hsolve
  refine ⟨cKin, cGrad, cVac, cMom, hKin, hGrad, hRel, ?_, hMom⟩
  intro x j
  have h1 := hHam x j
  have h2 := hG x j
  have h3 := hQuad (x.1 j) (x.1 (j + 1)) (x.2 j)
  -- h1 : ham = h(...); h3 : h = quadratic in (g a); h2 : structure = g.
  calc
    T.hamDensity x j
        = h (x.1 j) (x.1 (j + 1)) (x.2 j) := h1
    _ = cKin * (x.2 j * x.2 j) +
          cGrad * (g (x.1 j) * ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
          cVac := h3
    _ = cKin * (x.2 j * x.2 j) +
          cGrad *
            (T.structureFunction x j *
              ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
          cVac := by rw [h2]

/-- THEOREM. Universal glue: if every CanonicalMom target solves the PDE Prop,
CanonicalMom rigidity holds. -/
theorem HKTRigidityStatementPointSplitDynN2Canonical_of_solve
    (h : solve_profile_FE_quadratic) :
    HKTRigidityStatementPointSplitDynN2Canonical :=
  fun T => canonicalMom_rigidity_of_FE_solution T (h T)

/-- Instantiation: the honest HamDyn target satisfies the rigidity conclusion
via the assembly skeleton (does NOT close the universal rigidity theorem). -/
theorem hamDyn_canonicalMom_rigidity_conclusion :
    ∃ cKin cGrad cVac cMom : ℝ,
      cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynPointSplitTargetCanonicalMom.hamDensity x j =
            cKin * (x.2 j * x.2 j) +
              cGrad *
                (hamDynPointSplitTargetCanonicalMom.structureFunction x j *
                  ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) +
              cVac) ∧
        (∀ (x : PhaseSpace 2) (j : ZMod 2),
          hamDynPointSplitTargetCanonicalMom.momDensity x j =
            cMom * x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) :=
  canonicalMom_rigidity_of_FE_solution hamDynPointSplitTargetCanonicalMom
    hamDyn_solve_profile_FE_quadratic

/-! ## Status (gap5 unflipped; rigidity still open) -/

structure HKTCanonicalMomRigidityC1Status where
  /-- Session C1: alternating FE extraction closed. -/
  feExtractionClosed : Bool
  /-- PDE lemma `solve_profile_FE_quadratic` still open (universal). -/
  pdeLemmaClosed : Bool
  /-- Assembly skeleton closed (glue from PDE Prop to rigidity conclusion). -/
  assemblySkeletonClosed : Bool
  /-- Universal CanonicalMom rigidity still open. -/
  canonicalMomRigidityOpen : Bool
  /-- Ledger flag stays false. -/
  gap5ConstraintRecovery : Bool

def hktCanonicalMomRigidityC1Status : HKTCanonicalMomRigidityC1Status where
  feExtractionClosed := true
  pdeLemmaClosed := false
  assemblySkeletonClosed := true
  canonicalMomRigidityOpen := true
  gap5ConstraintRecovery := false

theorem hktCanonicalMomRigidityC1Status_flags :
    hktCanonicalMomRigidityC1Status.feExtractionClosed = true ∧
      hktCanonicalMomRigidityC1Status.pdeLemmaClosed = false ∧
        hktCanonicalMomRigidityC1Status.assemblySkeletonClosed = true ∧
          hktCanonicalMomRigidityC1Status.canonicalMomRigidityOpen = true ∧
            hktCanonicalMomRigidityC1Status.gap5ConstraintRecovery = false ∧
              fullTheoryBenchmarks.gap5_constraint_recovery = true := by
  decide

/-! ### Axiom receipts -/

#print axioms profiled_ham_ham_alternating_FE
#print axioms fe_at_r_zero
#print axioms fe_at_p_zero
#print axioms hb_coupling_of_linear_ansatz
#print axioms canonicalMom_rigidity_of_FE_solution
#print axioms HKTRigidityStatementPointSplitDynN2Canonical_of_solve
#print axioms hamDyn_solve_profile_FE_quadratic
#print axioms hamDyn_canonicalMom_rigidity_conclusion
#print axioms hktCanonicalMomRigidityC1Status_flags

end
end HKTCanonicalMomRigidity
end SevenGaps
end Gravity
end IndisputableMonolith
