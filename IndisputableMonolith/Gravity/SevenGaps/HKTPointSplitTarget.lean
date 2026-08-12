import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureBracket
import IndisputableMonolith.Gravity.SevenGaps.HKTDynamicTarget

/-!
# Wave C2 R5 repair: point-split HKT dynamic target

The widened Dyn target `HojmanKucharTeitelboimTargetDyn` in
`HKTDynamicTarget.lean` keeps an **unsplit** `mom_ham` field. That field is
uninhabitable for honest nearest-neighbor local momentum profiles against the
**frozen** quadratic Hamiltonian: at `n = 2` unsplit advection forces
`(p₀ + p₁) · ∂_d f = p₀² + d²`, which is singular on `p₀ + p₁ = 0`
(see `unsplit_mom_ham_no_smooth_nearestNeighbor_witness_frozenHam`). Scope is
honest and narrow (Codex `D-qg-hkt-pointsplit-adjudication-20260722`); the
analogous claim against campaign `HamDyn` is the open Prop
`UnsplitMomHamNoSmoothNearestNeighborWitnessHamDyn`. The unsplit Dyn target
remains as the falsification-adjacent record; this module is the repaired
sibling. The weak `HKTPointSplitTargetDyn` is schema-only after that
adjudication; the load-bearing class is `HKTPointSplitTargetDynStrong`.

**API adaptation (honest, n = 2).** On `ZMod 2` one has `-1 = 1`, so
`DgenSym a ≡ 0` as a functional and `{DgenSym a, ·} = 0` vacuously. The
adjudicated `mom_ham_split` sketch written with `DgenSym` is therefore
definitionally empty at the HamDyn size. The structure below uses the
**smeared point-split momentum density** that already appears in
`bracket_HamDyn_HamDyn` / `bracket_Ham_Ham`, with source/target advection
densities `hamAdvFrom` / `hamAdvTo`. Finding: that momentum sector is
**not** abelian (`mom_mom` carries a Wronskian density, not `0`).

No rigidity theorem is proved here. No ledger flag is flipped.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace HKTPointSplitTarget

open HypersurfaceDeformation DynamicStructureBracket DynamicStructureFunctionBlocker
open HKTDynamicTarget

noncomputable section

open Finset

private lemma zmod2_zero_add_one : (0 : ZMod 2) + 1 = 1 := by decide
private lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide
private lemma zmod2_zero_sub_one : (0 : ZMod 2) - 1 = 1 := by decide
private lemma zmod2_one_sub_one : (1 : ZMod 2) - 1 = 0 := by decide

lemma sum_zmod2 (g : ZMod 2 → ℝ) : (∑ j : ZMod 2, g j) = g 0 + g 1 := by
  have huniv : (univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]

/-! ## No-go: unsplit mom_ham has no smooth local witness at n = 2 -/

/-- Local momentum profile class: `m_j = f(d_j, π_j, π_{j+1})` with
`d_j = q_{j+1} - q_j`. Translation-covariant by construction. -/
abbrev LocalMomProfile : Type := ℝ → ℝ → ℝ → ℝ

def momFromProfile (f : LocalMomProfile) (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  f (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1))

def MomFromProfile (f : LocalMomProfile) (w : ZMod 2 → ℝ) (x : PhaseSpace 2) : ℝ :=
  ∑ j : ZMod 2, w j * momFromProfile f x j

/-- Canonical frozen quadratic Hamiltonian density. -/
def quadraticHamDensity (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  (x.2 j * x.2 j + (x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j)) / 2

theorem quadraticHamDensity_smear (N : ZMod 2 → ℝ) :
    (fun x : PhaseSpace 2 => ∑ j : ZMod 2, N j * quadraticHamDensity x j) = Ham N := by
  funext x
  unfold quadraticHamDensity Ham
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Smoothness package for a local momentum profile (Frechet cell data). -/
structure LocalMomSmooth (f : LocalMomProfile) where
  fd : LocalMomProfile
  fp : LocalMomProfile
  fr : LocalMomProfile
  hasFDerivCell :
    ∀ (j : ZMod 2) (x : PhaseSpace 2),
      HasFDerivAt (fun y : PhaseSpace 2 =>
          f (y.1 (j + 1) - y.1 j) (y.2 j) (y.2 (j + 1)))
        ((fd (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1))) •
            (coordQ (j + 1) - coordQ j) +
          (fp (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1))) • coordP j +
          (fr (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1))) • coordP (j + 1))
        x

def localMomCellD (f : LocalMomProfile) (S : LocalMomSmooth f) (j : ZMod 2)
    (x : PhaseSpace 2) : PhaseSpace 2 →L[ℝ] ℝ :=
  (S.fd (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1))) • (coordQ (j + 1) - coordQ j) +
    (S.fp (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1))) • coordP j +
    (S.fr (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1))) • coordP (j + 1)

lemma hasFDerivAt_localMomCell (f : LocalMomProfile) (S : LocalMomSmooth f)
    (j : ZMod 2) (x : PhaseSpace 2) :
    HasFDerivAt (fun y : PhaseSpace 2 =>
        f (y.1 (j + 1) - y.1 j) (y.2 j) (y.2 (j + 1)))
      (localMomCellD f S j x) x :=
  S.hasFDerivCell j x

def MomFromProfileD (f : LocalMomProfile) (S : LocalMomSmooth f)
    (w : ZMod 2 → ℝ) (x : PhaseSpace 2) : PhaseSpace 2 →L[ℝ] ℝ :=
  ∑ j : ZMod 2, (w j) • localMomCellD f S j x

lemma hasFDerivAt_MomFromProfile (f : LocalMomProfile) (S : LocalMomSmooth f)
    (w : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    HasFDerivAt (MomFromProfile f w) (MomFromProfileD f S w x) x := by
  unfold MomFromProfile MomFromProfileD momFromProfile
  exact HasFDerivAt.fun_sum fun j _ =>
    (hasFDerivAt_localMomCell f S j x).const_mul (w j)

private lemma localMomCellD_pdir (f : LocalMomProfile) (S : LocalMomSmooth f)
    (j k : ZMod 2) (x : PhaseSpace 2) :
    localMomCellD f S j x (0, Pi.single k 1)
      = S.fp (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1)) *
          (if j = k then (1 : ℝ) else 0)
        + S.fr (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1)) *
          (if j + 1 = k then (1 : ℝ) else 0) := by
  simp only [localMomCellD, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    coordQ_apply, coordP_apply, Pi.single_apply, smul_eq_mul]
  by_cases hjk : j = k <;> by_cases hjp : j + 1 = k <;> simp [hjk, hjp]

private lemma localMomCellD_qdir (f : LocalMomProfile) (S : LocalMomSmooth f)
    (j k : ZMod 2) (x : PhaseSpace 2) :
    localMomCellD f S j x (Pi.single k 1, 0)
      = S.fd (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1)) *
          ((if j + 1 = k then (1 : ℝ) else 0) - (if j = k then (1 : ℝ) else 0)) := by
  simp only [localMomCellD, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    coordQ_apply, coordP_apply, Pi.single_apply, smul_eq_mul]
  by_cases hjk : j = k <;> by_cases hjp : j + 1 = k <;> simp [hjk, hjp]

theorem pderivP_MomFromProfile (f : LocalMomProfile) (S : LocalMomSmooth f)
    (w : ZMod 2 → ℝ) (k : ZMod 2) (x : PhaseSpace 2) :
    pderivP (MomFromProfile f w) k x
      = w k * S.fp (x.1 (k + 1) - x.1 k) (x.2 k) (x.2 (k + 1))
        + w (k - 1) * S.fr (x.1 k - x.1 (k - 1)) (x.2 (k - 1)) (x.2 k) := by
  rw [pderivP, (hasFDerivAt_MomFromProfile f S w x).fderiv, MomFromProfileD,
    ContinuousLinearMap.sum_apply]
  have step : ∀ j : ZMod 2,
      (((w j) • localMomCellD f S j x : PhaseSpace 2 →L[ℝ] ℝ)
        ((0, Pi.single k 1) : PhaseSpace 2))
      = (w j * S.fp (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1))) *
            (if j = k then (1 : ℝ) else 0)
        + (w j * S.fr (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1))) *
            (if j + 1 = k then (1 : ℝ) else 0) := by
    intro j
    simp only [ContinuousLinearMap.smul_apply, localMomCellD_pdir, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun j _ => step j, Finset.sum_add_distrib,
    sum_mul_ite, sum_mul_ite_add]
  have e : k - 1 + 1 = k := by ring
  simp only [e]

theorem pderivQ_MomFromProfile (f : LocalMomProfile) (S : LocalMomSmooth f)
    (w : ZMod 2 → ℝ) (k : ZMod 2) (x : PhaseSpace 2) :
    pderivQ (MomFromProfile f w) k x
      = w (k - 1) * S.fd (x.1 k - x.1 (k - 1)) (x.2 (k - 1)) (x.2 k)
        - w k * S.fd (x.1 (k + 1) - x.1 k) (x.2 k) (x.2 (k + 1)) := by
  rw [pderivQ, (hasFDerivAt_MomFromProfile f S w x).fderiv, MomFromProfileD,
    ContinuousLinearMap.sum_apply]
  have step : ∀ j : ZMod 2,
      (((w j) • localMomCellD f S j x : PhaseSpace 2 →L[ℝ] ℝ)
        ((Pi.single k 1, 0) : PhaseSpace 2))
      = (w j * S.fd (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1))) *
          ((if j + 1 = k then (1 : ℝ) else 0) - (if j = k then (1 : ℝ) else 0)) := by
    intro j
    simp only [ContinuousLinearMap.smul_apply, localMomCellD_qdir, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun j _ => step j]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sum_mul_ite_add (fun j => w j * S.fd (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1))) 1 k,
    sum_mul_ite (fun j => w j * S.fd (x.1 (j + 1) - x.1 j) (x.2 j) (x.2 (j + 1))) k]
  have e : k - 1 + 1 = k := by ring
  simp only [e]

/-- Unsplit Dyn-style advection identity for a local momentum profile against
the frozen quadratic Hamiltonian. -/
def UnsplitMomHamForProfile (f : LocalMomProfile) : Prop :=
  ∀ (w N : ZMod 2 → ℝ) (x : PhaseSpace 2),
    bracket (MomFromProfile f w) (Ham N) x
      = ∑ j : ZMod 2, (w j * (N (j + 1) - N j)) * quadraticHamDensity x j

/-- Forced coefficient identity implied by unsplit advection on the class
`m_j = f(d_j, π_j, π_{j+1})`: `(p + r) · ∂_d f = p² + d²`. -/
def ForcedUnsplitPartialRelation (fd : LocalMomProfile) : Prop :=
  ∀ d p r : ℝ, (p + r) * fd d p r = p * p + d * d

/-- THEOREM. The forced unsplit partial relation is unsatisfiable: at
`(d, p, r) = (1, 1, -1)` the left side vanishes while the right side is `2`. -/
theorem forced_unsplit_partial_relation_impossible (fd : LocalMomProfile) :
    ¬ ForcedUnsplitPartialRelation fd := by
  intro h
  have := h (1 : ℝ) 1 (-1)
  norm_num at this

/-- Witness phase point for the no-go: `d = 1`, `π₀ = 1`, `π₁ = -1`. -/
def unsplitNoGoPhase : PhaseSpace 2 :=
  (fun j : ZMod 2 => if j = (0 : ZMod 2) then (0 : ℝ) else 1,
    fun j : ZMod 2 => if j = (0 : ZMod 2) then (1 : ℝ) else (-1 : ℝ))

def delta0 : ZMod 2 → ℝ := fun j => if j = (0 : ZMod 2) then (1 : ℝ) else 0
def delta1 : ZMod 2 → ℝ := fun j => if j = (1 : ZMod 2) then (1 : ℝ) else 0

private lemma unsplitNoGo_vals :
    unsplitNoGoPhase.1 (0 : ZMod 2) = 0 ∧
      unsplitNoGoPhase.1 (1 : ZMod 2) = 1 ∧
        unsplitNoGoPhase.2 (0 : ZMod 2) = 1 ∧
          unsplitNoGoPhase.2 (1 : ZMod 2) = -1 := by
  simp [unsplitNoGoPhase]

/-- At the no-go witness with `w = δ₀`,
`{Mom, Ham N} = (N₀ + N₁) (-∂_d f + ∂_p f - ∂_r f)`. -/
theorem bracket_MomFromProfile_delta0_unsplitNoGo (f : LocalMomProfile)
    (S : LocalMomSmooth f) (N : ZMod 2 → ℝ) :
    bracket (MomFromProfile f delta0) (Ham N) unsplitNoGoPhase
      = (N 0 + N 1) *
          (- S.fd (1 : ℝ) 1 (-1) + S.fp (1 : ℝ) 1 (-1) - S.fr (1 : ℝ) 1 (-1)) := by
  have hv := unsplitNoGo_vals
  have hq0 :
      pderivQ (MomFromProfile f delta0) (0 : ZMod 2) unsplitNoGoPhase
        = -S.fd (1 : ℝ) 1 (-1) := by
    rw [pderivQ_MomFromProfile f S]
    simp [delta0, zmod2_zero_add_one, zmod2_zero_sub_one, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  have hq1 :
      pderivQ (MomFromProfile f delta0) (1 : ZMod 2) unsplitNoGoPhase
        = S.fd (1 : ℝ) 1 (-1) := by
    rw [pderivQ_MomFromProfile f S]
    simp [delta0, zmod2_one_add_one, zmod2_one_sub_one, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  have hp0 :
      pderivP (MomFromProfile f delta0) (0 : ZMod 2) unsplitNoGoPhase
        = S.fp (1 : ℝ) 1 (-1) := by
    rw [pderivP_MomFromProfile f S]
    simp [delta0, zmod2_zero_add_one, zmod2_zero_sub_one, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  have hp1 :
      pderivP (MomFromProfile f delta0) (1 : ZMod 2) unsplitNoGoPhase
        = S.fr (1 : ℝ) 1 (-1) := by
    rw [pderivP_MomFromProfile f S]
    simp [delta0, zmod2_one_add_one, zmod2_one_sub_one, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  have hQP0 : pderivP (Ham N) (0 : ZMod 2) unsplitNoGoPhase = N 0 * (1 : ℝ) := by
    rw [pderivP_Ham, hv.2.2.1]
  have hQP1 : pderivP (Ham N) (1 : ZMod 2) unsplitNoGoPhase = N 1 * (-1 : ℝ) := by
    rw [pderivP_Ham, hv.2.2.2]
  have hQQ0 :
      pderivQ (Ham N) (0 : ZMod 2) unsplitNoGoPhase = -(N 0 + N 1) := by
    rw [pderivQ_Ham, zmod2_zero_add_one, zmod2_zero_sub_one, hv.1, hv.2.1]
    ring
  have hQQ1 :
      pderivQ (Ham N) (1 : ZMod 2) unsplitNoGoPhase = N 0 + N 1 := by
    rw [pderivQ_Ham, zmod2_one_add_one, zmod2_one_sub_one, hv.1, hv.2.1]
    ring
  unfold bracket
  rw [sum_zmod2, hq0, hq1, hp0, hp1, hQP0, hQP1, hQQ0, hQQ1]
  ring

theorem unsplit_RHS_delta0_unsplitNoGo (N : ZMod 2 → ℝ) :
    (∑ j : ZMod 2, (delta0 j * (N (j + 1) - N j)) *
        quadraticHamDensity unsplitNoGoPhase j)
      = N 1 - N 0 := by
  have hv := unsplitNoGo_vals
  have hδ : delta0 (0 : ZMod 2) = 1 ∧ delta0 (1 : ZMod 2) = 0 := by
    simp [delta0]
  have hq0 : quadraticHamDensity unsplitNoGoPhase (0 : ZMod 2) = 1 := by
    simp [quadraticHamDensity, zmod2_zero_add_one, hv.1, hv.2.1, hv.2.2.1]
  rw [sum_zmod2, hδ.1, hδ.2, zmod2_zero_add_one, zmod2_one_add_one, hq0]
  ring

/-- THEOREM (scoped no-go). No Frechet-smooth **nearest-neighbor** local
momentum profile `m_j = f(d_j, π_j, π_{j+1})` satisfies the unsplit Dyn
`mom_ham` identity against the **frozen** quadratic Hamiltonian density
`quadraticHamDensity` / `Ham` on `PhaseSpace 2`.

At the witness `(d, π₀, π₁) = (1, 1, -1)` with `w = δ₀`, unsplit forces
`(N₀ + N₁)(-f_d + f_p - f_r) = N₁ - N₀` for all lapses `N`. Taking
`N = δ₀` and `N = δ₁` yields `-f_d + f_p - f_r = -1` and
`-f_d + f_p - f_r = 1`, contradiction. Equivalent singular form:
`(π₀ + π₁) f_d = π₀² + d²` (see `ForcedUnsplitPartialRelation`).

**Does NOT establish:** (i) the same no-go against campaign `HamDyn` /
`hamDynDensity`; (ii) a no-go for non-nearest-neighbor momentum profiles;
(iii) uninhabitability of every unsplit identity in the widened Dyn target.
Those are separate claims; see `UnsplitMomHamNoSmoothNearestNeighborWitnessHamDyn`. -/
theorem unsplit_mom_ham_no_smooth_nearestNeighbor_witness_frozenHam
    (f : LocalMomProfile) (S : LocalMomSmooth f) :
    ¬ UnsplitMomHamForProfile f := by
  intro hUnsplit
  have h0 := hUnsplit delta0 delta0 unsplitNoGoPhase
  have h1 := hUnsplit delta0 delta1 unsplitNoGoPhase
  rw [bracket_MomFromProfile_delta0_unsplitNoGo f S,
    unsplit_RHS_delta0_unsplitNoGo] at h0 h1
  have hδ0 : (delta0 (0 : ZMod 2) : ℝ) = 1 ∧ delta0 (1 : ZMod 2) = 0 := by
    simp [delta0]
  have hδ1 : (delta1 (0 : ZMod 2) : ℝ) = 0 ∧ delta1 (1 : ZMod 2) = 1 := by
    simp [delta1]
  simp only [hδ0.1, hδ0.2, hδ1.1, hδ1.2] at h0 h1
  have h0' : -S.fd (1 : ℝ) 1 (-1) + S.fp (1 : ℝ) 1 (-1) - S.fr (1 : ℝ) 1 (-1) = -1 := by
    linarith
  have h1' : -S.fd (1 : ℝ) 1 (-1) + S.fp (1 : ℝ) 1 (-1) - S.fr (1 : ℝ) 1 (-1) = 1 := by
    linarith
  linarith

/-- Compatibility alias for ledger claim `C-qg-hkt-unsplit-nogo` and older
cross-refs. Prefer the scoped name
`unsplit_mom_ham_no_smooth_nearestNeighbor_witness_frozenHam`. -/
theorem unsplit_mom_ham_no_smooth_local_witness (f : LocalMomProfile)
    (S : LocalMomSmooth f) : ¬ UnsplitMomHamForProfile f :=
  unsplit_mom_ham_no_smooth_nearestNeighbor_witness_frozenHam f S

/-! ## Point-split dynamic target (SCHEMA-ONLY after critic) -/

/-- SCHEMA-ONLY (demoted). HKT hypotheses with dynamic structure function and
**point-split** momentum–Hamiltonian advection.

Adaptation from the DgenSym-shaped sketch: at `n = 2`, `DgenSym` vanishes, so
`mom_ham_split` is stated for the smeared `momDensity` that `ham_ham` already
uses, with source/target split densities. The `mom_mom` field records the
**true** (non-abelian) bracket of that sector.

**Critic demotion** (`D-qg-hkt-pointsplit-adjudication-20260722`):
`hamAdvFrom`/`hamAdvTo` are free record slots and `nondegenerate` only requires
some nonzero `hamDensity`. The quartic zero-momentum decoy
(`hamDensity = π_j^4`, `momDensity = 0`, decorative `structureFunction`, all
advection/bracket densities 0) inhabits this structure. Use
`HKTPointSplitTargetDynStrong` for any load-bearing claim or rigidity grind. -/
structure HKTPointSplitTargetDyn (n : ℕ) [NeZero n] where
  hamDensity : PhaseSpace n → ZMod n → ℝ
  momDensity : PhaseSpace n → ZMod n → ℝ
  structureFunction : PhaseSpace n → ZMod n → ℝ
  /-- Source advection density in
  `{D[w], H[N]} = Σ_j w_j (N_{j+1} · hamAdvTo_j - N_j · hamAdvFrom_j)`. -/
  hamAdvFrom : PhaseSpace n → ZMod n → ℝ
  /-- Target advection density (see `hamAdvFrom`). -/
  hamAdvTo : PhaseSpace n → ZMod n → ℝ
  /-- Structure density for `{D[v], D[w]}` of smeared `momDensity`
  (Wronskian form; not identically zero). -/
  momBracketDensity : PhaseSpace n → ZMod n → ℝ
  ham_differentiable : ∀ N : ZMod n → ℝ,
    Differentiable ℝ (fun x : PhaseSpace n => ∑ j : ZMod n, N j * hamDensity x j)
  mom_differentiable : ∀ w : ZMod n → ℝ,
    Differentiable ℝ (fun x : PhaseSpace n => ∑ j : ZMod n, w j * momDensity x j)
  structure_nonconstant : ¬ PhaseSpaceConstant structureFunction
  ham_local : ∀ (x y : PhaseSpace n) (j : ZMod n),
    x.1 j = y.1 j → x.1 (j + 1) = y.1 (j + 1) → x.2 j = y.2 j →
      hamDensity x j = hamDensity y j
  ham_covariant : ∀ (x : PhaseSpace n) (a j : ZMod n),
    hamDensity (fun i => x.1 (i + a), fun i => x.2 (i + a)) j = hamDensity x (j + a)
  structure_local : ∀ (x y : PhaseSpace n) (j : ZMod n),
    x.1 j = y.1 j → structureFunction x j = structureFunction y j
  /-- Finding: smeared point-split `momDensity` is not abelian. -/
  mom_mom : ∀ (v w : ZMod n → ℝ) (x : PhaseSpace n),
    bracket (fun y => ∑ j : ZMod n, v j * momDensity y j)
      (fun y => ∑ j : ZMod n, w j * momDensity y j) x
      = ∑ j : ZMod n,
          (v j * w (j + 1) - w j * v (j + 1)) * momBracketDensity x j
  /-- Point-split advection (repairs unsplit Dyn `mom_ham`). -/
  mom_ham_split : ∀ (w N : ZMod n → ℝ) (x : PhaseSpace n),
    bracket (fun y => ∑ j : ZMod n, w j * momDensity y j)
      (fun y => ∑ j : ZMod n, N j * hamDensity y j) x
      = ∑ j : ZMod n, w j * (N (j + 1) * hamAdvTo x j - N j * hamAdvFrom x j)
  ham_ham : ∀ (N M : ZMod n → ℝ) (x : PhaseSpace n),
    bracket (fun y => ∑ j : ZMod n, N j * hamDensity y j)
      (fun y => ∑ j : ZMod n, M j * hamDensity y j) x
      = ∑ j : ZMod n,
          (N j * M (j + 1) - M j * N (j + 1)) *
            (structureFunction x j * momDensity x j)
  /-- Excludes the zero-density junk inhabitant. -/
  nondegenerate : ∃ (x : PhaseSpace n) (j : ZMod n), hamDensity x j ≠ 0

/-- Convenience: pack source/target densities into a single slot keyed by a
shift `a` (DgenSym-shaped packaging). At `n = 2` this is documentary only:
`DgenSym` itself vanishes. -/
def hamAdvectionSplit {n : ℕ} [NeZero n] (T : HKTPointSplitTargetDyn n)
    (x : PhaseSpace n) (a j : ZMod n) : ℝ :=
  if a = 1 then (T.hamAdvTo x j + T.hamAdvFrom x j) / 2 else 0

/-! ## Honest HamDyn inhabitant at n = 2 -/

def hamDynDensity (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  (x.2 j * x.2 j +
      (1 + x.1 j * x.1 j) *
        ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))) / 2

/-! ### Open HamDyn-level unsplit no-go (stated, not proved) -/

/-- Unsplit Dyn-style advection identity for a local momentum profile against
the campaign `HamDyn` density (`hamDynDensity`), not the frozen quadratic. -/
def UnsplitMomHamForProfileDyn (f : LocalMomProfile) : Prop :=
  ∀ (w N : ZMod 2 → ℝ) (x : PhaseSpace 2),
    bracket (MomFromProfile f w) (HamDyn N) x
      = ∑ j : ZMod 2, (w j * (N (j + 1) - N j)) * hamDynDensity x j

/-- OPEN TARGET (DEFINED only; not proved). The HamDyn-level analogue of
`unsplit_mom_ham_no_smooth_nearestNeighbor_witness_frozenHam`: no Frechet-smooth
nearest-neighbor profile satisfies unsplit advection against `HamDyn`.

Honest effort note (Codex repair 2026-07-22): the frozen proof uses that at the
witness the LHS factorizes as `(N₀+N₁)·scalar` while the RHS is `N₁-N₀`. Against
`HamDyn` the configuration partials break that factorization, so the same
two-lapse contradiction does not transport. Do **not** cite this Prop as a
theorem until a proof lands. -/
def UnsplitMomHamNoSmoothNearestNeighborWitnessHamDyn : Prop :=
  ∀ (f : LocalMomProfile) (_S : LocalMomSmooth f), ¬ UnsplitMomHamForProfileDyn f

def momDynDensity (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  x.2 (j + 1) * (x.1 (j + 1) - x.1 j)

def structureDyn (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  1 + x.1 j * x.1 j

/-- TRUE source advection density for `{MomDyn w, HamDyn N}` at `n = 2`. -/
def hamDynAdvFrom (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  x.2 j * x.2 (j + 1) +
    (1 + x.1 j * x.1 j) * ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))

/-- TRUE target advection density for `{MomDyn w, HamDyn N}` at `n = 2`. -/
def hamDynAdvTo (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  x.2 (j + 1) * x.2 (j + 1) -
    (1 + x.1 (j + 1) * x.1 (j + 1)) *
      ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j)) -
    x.1 (j + 1) *
      ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))

/-- TRUE `{Mom, Mom}` Wronskian density at `n = 2`. -/
def momDynBracketDensity (x : PhaseSpace 2) (j : ZMod 2) : ℝ :=
  ((x.1 (j + 1) - x.1 j) * (x.2 j + x.2 (j + 1))) / 2

def MomDyn (w : ZMod 2 → ℝ) (x : PhaseSpace 2) : ℝ :=
  ∑ j : ZMod 2, w j * momDynDensity x j

theorem hamDynDensity_smear (N : ZMod 2 → ℝ) :
    (fun x : PhaseSpace 2 => ∑ j : ZMod 2, N j * hamDynDensity x j) = HamDyn N := by
  funext x
  unfold hamDynDensity HamDyn
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem structureDyn_eq_concrete (x : PhaseSpace 2) (j : ZMod 2) :
    structureDyn x j = concreteDynamicInverseMetric x j := by
  simp [structureDyn, concreteDynamicInverseMetric, pow_two]

theorem MomDyn_closed (w : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    MomDyn w x = (x.1 1 - x.1 0) * (w 0 * x.2 1 - w 1 * x.2 0) := by
  unfold MomDyn momDynDensity
  simp only [sum_zmod2, zmod2_zero_add_one, zmod2_one_add_one]
  ring

/-- Product-rule order matching `HasFDerivAt.mul`: `f x • g' + g x • f'`. -/
def MomDynD (w : ZMod 2 → ℝ) (x : PhaseSpace 2) : PhaseSpace 2 →L[ℝ] ℝ :=
  (x.1 1 - x.1 0) • (w 0 • coordP 1 - w 1 • coordP 0) +
    (w 0 * x.2 1 - w 1 * x.2 0) • (coordQ 1 - coordQ 0)

lemma hasFDerivAt_MomDyn (w : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    HasFDerivAt (MomDyn w) (MomDynD w x) x := by
  -- Match the Pi-sub form produced by `HasFDerivAt.sub` / `.mul`.
  have hform :
      MomDyn w =
        ((fun y : PhaseSpace 2 => y.1 1) - fun y => y.1 0) *
          ((fun y => w 0 * y.2 1) - fun y => w 1 * y.2 0) := by
    funext y
    dsimp [Pi.sub_apply]
    exact MomDyn_closed w y
  rw [hform]
  exact (((hasFDerivAt_coord_fst (1 : ZMod 2) x).sub (hasFDerivAt_coord_fst 0 x)).mul
    (((hasFDerivAt_coord_snd (1 : ZMod 2) x).const_mul (w 0)).sub
      ((hasFDerivAt_coord_snd (0 : ZMod 2) x).const_mul (w 1))))

theorem differentiable_MomDyn (w : ZMod 2 → ℝ) : Differentiable ℝ (MomDyn w) :=
  fun x => (hasFDerivAt_MomDyn w x).differentiableAt

theorem pderivQ_MomDyn_zero (w : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    pderivQ (MomDyn w) (0 : ZMod 2) x = -(w 0 * x.2 1 - w 1 * x.2 0) := by
  rw [pderivQ, (hasFDerivAt_MomDyn w x).fderiv, MomDynD]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, coordQ_apply,
    coordP_apply]

theorem pderivQ_MomDyn_one (w : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    pderivQ (MomDyn w) (1 : ZMod 2) x = w 0 * x.2 1 - w 1 * x.2 0 := by
  rw [pderivQ, (hasFDerivAt_MomDyn w x).fderiv, MomDynD]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, coordQ_apply,
    coordP_apply]

theorem pderivP_MomDyn_zero (w : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    pderivP (MomDyn w) (0 : ZMod 2) x = (x.1 1 - x.1 0) * (-w 1) := by
  rw [pderivP, (hasFDerivAt_MomDyn w x).fderiv, MomDynD]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, coordQ_apply,
    coordP_apply]

theorem pderivP_MomDyn_one (w : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    pderivP (MomDyn w) (1 : ZMod 2) x = (x.1 1 - x.1 0) * w 0 := by
  rw [pderivP, (hasFDerivAt_MomDyn w x).fderiv, MomDynD]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, coordQ_apply,
    coordP_apply]

theorem bracket_MomDyn_MomDyn (v w : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (MomDyn v) (MomDyn w) x
      = ∑ j : ZMod 2,
          (v j * w (j + 1) - w j * v (j + 1)) * momDynBracketDensity x j := by
  have hL :
      bracket (MomDyn v) (MomDyn w) x =
        (pderivQ (MomDyn v) (0 : ZMod 2) x * pderivP (MomDyn w) (0 : ZMod 2) x -
            pderivP (MomDyn v) (0 : ZMod 2) x * pderivQ (MomDyn w) (0 : ZMod 2) x) +
          (pderivQ (MomDyn v) (1 : ZMod 2) x * pderivP (MomDyn w) (1 : ZMod 2) x -
            pderivP (MomDyn v) (1 : ZMod 2) x * pderivQ (MomDyn w) (1 : ZMod 2) x) := by
    unfold bracket
    rw [sum_zmod2]
  have hR :
      (∑ j : ZMod 2,
          (v j * w (j + 1) - w j * v (j + 1)) * momDynBracketDensity x j) =
        (v 0 * w 1 - w 0 * v 1) * momDynBracketDensity x 0 +
          (v 1 * w 0 - w 1 * v 0) * momDynBracketDensity x 1 := by
    rw [sum_zmod2, zmod2_zero_add_one, zmod2_one_add_one]
  rw [hL, hR, pderivQ_MomDyn_zero v x, pderivQ_MomDyn_zero w x, pderivQ_MomDyn_one v x,
    pderivQ_MomDyn_one w x, pderivP_MomDyn_zero v x, pderivP_MomDyn_zero w x,
    pderivP_MomDyn_one v x, pderivP_MomDyn_one w x]
  simp only [momDynBracketDensity, zmod2_zero_add_one, zmod2_one_add_one]
  ring

set_option maxHeartbeats 800000 in
theorem bracket_MomDyn_HamDyn (w N : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (MomDyn w) (HamDyn N) x
      = ∑ j : ZMod 2, w j * (N (j + 1) * hamDynAdvTo x j - N j * hamDynAdvFrom x j) := by
  have hL :
      bracket (MomDyn w) (HamDyn N) x =
        (pderivQ (MomDyn w) (0 : ZMod 2) x * pderivP (HamDyn N) (0 : ZMod 2) x -
            pderivP (MomDyn w) (0 : ZMod 2) x * pderivQ (HamDyn N) (0 : ZMod 2) x) +
          (pderivQ (MomDyn w) (1 : ZMod 2) x * pderivP (HamDyn N) (1 : ZMod 2) x -
            pderivP (MomDyn w) (1 : ZMod 2) x * pderivQ (HamDyn N) (1 : ZMod 2) x) := by
    unfold bracket
    rw [sum_zmod2]
  have hR :
      (∑ j : ZMod 2, w j * (N (j + 1) * hamDynAdvTo x j - N j * hamDynAdvFrom x j)) =
        w 0 * (N 1 * hamDynAdvTo x 0 - N 0 * hamDynAdvFrom x 0) +
          w 1 * (N 0 * hamDynAdvTo x 1 - N 1 * hamDynAdvFrom x 1) := by
    rw [sum_zmod2, zmod2_zero_add_one, zmod2_one_add_one]
  -- Expand every partial, then every Adv density, with ZMod 2 arithmetic frozen.
  have hQ0 := pderivQ_HamDyn N (0 : ZMod 2) x
  have hQ1 := pderivQ_HamDyn N (1 : ZMod 2) x
  have hP0 := pderivP_HamDyn N (0 : ZMod 2) x
  have hP1 := pderivP_HamDyn N (1 : ZMod 2) x
  rw [hL, hR, pderivQ_MomDyn_zero w x, pderivQ_MomDyn_one w x, pderivP_MomDyn_zero w x,
    pderivP_MomDyn_one w x, hP0, hP1, hQ0, hQ1]
  -- Rewrite ZMod shifts before unfolding Adv (keeps ring's monomial count down).
  simp only [zmod2_zero_add_one, zmod2_one_add_one, zmod2_zero_sub_one, zmod2_one_sub_one]
  unfold hamDynAdvFrom hamDynAdvTo
  simp only [zmod2_zero_add_one, zmod2_one_add_one]
  -- Sympy-checked identity: LHS - RHS = 0 as a polynomial in the 8 scalars.
  ring

theorem structureDyn_not_constant : ¬ PhaseSpaceConstant structureDyn := by
  intro h
  have hEq := h zeroPhasePoint unitConfigurationPoint (0 : ZMod 2)
  simp only [structureDyn, zeroPhasePoint, unitConfigurationPoint] at hEq
  norm_num at hEq

def hamDynNondegPhase : PhaseSpace 2 :=
  (fun _ => (0 : ℝ), fun j => if j = (0 : ZMod 2) then (1 : ℝ) else 0)

theorem hamDynDensity_nondeg :
    hamDynDensity hamDynNondegPhase (0 : ZMod 2) ≠ 0 := by
  simp only [hamDynDensity, hamDynNondegPhase]
  norm_num

/-- THEOREM. Honest HamDyn inhabitant of the repaired point-split Dyn target. -/
def hamDynPointSplitTarget : HKTPointSplitTargetDyn 2 where
  hamDensity := hamDynDensity
  momDensity := momDynDensity
  structureFunction := structureDyn
  hamAdvFrom := hamDynAdvFrom
  hamAdvTo := hamDynAdvTo
  momBracketDensity := momDynBracketDensity
  ham_differentiable := by
    intro N
    simpa [hamDynDensity_smear] using differentiable_HamDyn N
  mom_differentiable := differentiable_MomDyn
  structure_nonconstant := structureDyn_not_constant
  ham_local := by
    intro x y j hx0 hx1 hp
    dsimp only [hamDynDensity]
    rw [hx0, hx1, hp]
  ham_covariant := by
    intro x a j
    unfold hamDynDensity
    have e1 : (j + a + 1 : ZMod 2) = j + 1 + a := by ring
    simp only [e1]
  structure_local := by
    intro x y j hx
    dsimp only [structureDyn]
    rw [hx]
  mom_mom := by
    intro v w x
    simpa [MomDyn] using bracket_MomDyn_MomDyn v w x
  mom_ham_split := by
    intro w N x
    simpa [MomDyn, hamDynDensity_smear] using bracket_MomDyn_HamDyn w N x
  ham_ham := by
    intro N M x
    have h := bracket_HamDyn_HamDyn N M x
    -- Rewrite densities by closed forms; avoid open-ended simp on ZMod.
    simp only [hamDynDensity_smear, structureDyn, momDynDensity, concreteDynamicInverseMetric,
      pow_two] at h ⊢
    exact h
  nondegenerate := ⟨hamDynNondegPhase, (0 : ZMod 2), hamDynDensity_nondeg⟩

theorem hktPointSplitTargetDyn_two_nonvacuous : Nonempty (HKTPointSplitTargetDyn 2) :=
  ⟨hamDynPointSplitTarget⟩

/-- Documentary: `DgenSym` vanishes on two sites, so a DgenSym-shaped
`mom_ham_split` would be vacuous. -/
theorem DgenSym_eq_zero_two (a : ZMod 2) (x : PhaseSpace 2) : DgenSym a x = 0 := by
  unfold DgenSym
  refine Finset.sum_eq_zero fun i _ => ?_
  have h : (i + a : ZMod 2) = i - a := by
    -- on ZMod 2, a = -a for all a
    have : a + a = (0 : ZMod 2) := by
      fin_cases a <;> decide
    calc i + a = i + a := rfl
      _ = i - a + (a + a) := by ring
      _ = i - a + 0 := by rw [this]
      _ = i - a := by ring
  simp [h]

/-- Zero-density junk fails `nondegenerate` by construction. -/
theorem zero_density_fails_nondegenerate :
    ¬ ∃ (_x : PhaseSpace 2) (_j : ZMod 2), (0 : ℝ) ≠ 0 := by
  rintro ⟨_, _, h⟩
  exact h rfl

/-! ## Binding rigidity Prop (DEMOTED: weak class) -/

/-- DEMOTED (likely false). Quantifies over the WEAK schema
`HKTPointSplitTargetDyn`, which the quartic zero-momentum decoy inhabits
(`quarticZeroMomTarget` in `HKTPointSplitStrong`). Critic finding
`D-qg-hkt-pointsplit-adjudication-20260722`: the n=1 quartic disease is
reproduced at n=2 over this class. Binding rigidity is
`HKTRigidityStatementPointSplitDynN2Strong`. -/
def HKTRigidityStatementPointSplitDynN2 : Prop :=
  ∀ T : HKTPointSplitTargetDyn 2,
    ∃ cKin cGrad cVac : ℝ, ∀ (x : PhaseSpace 2) (j : ZMod 2),
      T.hamDensity x j
        = cKin * (x.2 j * x.2 j)
          + cGrad *
              (T.structureFunction x j *
                ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j)))
          + cVac

/-! ### Axiom receipts -/

#print axioms forced_unsplit_partial_relation_impossible
#print axioms unsplit_mom_ham_no_smooth_nearestNeighbor_witness_frozenHam
#print axioms unsplit_mom_ham_no_smooth_local_witness
#print axioms bracket_MomDyn_MomDyn
#print axioms bracket_MomDyn_HamDyn
#print axioms hktPointSplitTargetDyn_two_nonvacuous
#print axioms DgenSym_eq_zero_two

end
end HKTPointSplitTarget
end SevenGaps
end Gravity
end IndisputableMonolith
