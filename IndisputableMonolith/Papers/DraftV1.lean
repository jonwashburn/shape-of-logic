import Mathlib
import IndisputableMonolith.RecogGeom.Quotient
import IndisputableMonolith.RecogGeom.Composition
import IndisputableMonolith.Foundation.AlexanderDuality

/-!
# Draft_v1.tex — theorem formalization surface (audit companion)

This module exists to **mirror the theorem statements** appearing in `Draft_v1.tex`
and to map them to what is currently available in this Lean repository.

Where the repo already contains a proved theorem with the same statement, we
re-export it here under a paper-oriented name.

Where the paper relies on heavy external mathematics (e.g. Alexander duality for complements
of embeddings, or full Binet/Bertrand machinery), we provide **explicit hypothesis interfaces**
instead of introducing new global axioms. This keeps the certified surface honest: theorems
depending on those hypotheses are only as strong as the hypotheses supplied.

See also: `Draft_v1_audit.tex` (the LaTeX-side inventory and mapping report).
-/

noncomputable section

namespace IndisputableMonolith
namespace Papers
namespace DraftV1

/-! ## Paper Theorem: Injectivity of Observable Map -/

namespace RecognitionGeometry

open RecogGeom

/-- Paper theorem: the induced map `R̄ : C_R → E` is injective. -/
theorem injectivity_of_observable_map {C E : Type*} (r : Recognizer C E) :
    Function.Injective (quotientEventMap r) :=
  quotientEventMap_injective (r := r)

/-! ## Paper Theorem: Refinement (Composition of Recognizers) -/

/-- Paper theorem: the composite quotient maps surjectively to each component quotient. -/
theorem refinement {C E₁ E₂ : Type*} (r₁ : Recognizer C E₁) (r₂ : Recognizer C E₂) :
    Function.Surjective (quotientMapLeft r₁ r₂) ∧
    Function.Surjective (quotientMapRight r₁ r₂) :=
  refinement_theorem (r₁ := r₁) (r₂ := r₂)

end RecognitionGeometry

/-! ## Constraint (S): Dyadic synchronization (N = 45) -/

open Nat

/-- The synchronization period used in `Draft_v1.tex`: `S(D) := lcm(2^D, 45)`. -/
def syncPeriod (D : ℕ) : ℕ := Nat.lcm (2 ^ D) 45

lemma syncPeriod_def (D : ℕ) : syncPeriod D = Nat.lcm (2 ^ D) 45 := rfl

/-! The key arithmetic lemma used in the paper's proof: since `45` is odd,
`gcd(2^D,45)=1`, hence `lcm(2^D,45)=2^D*45`. -/
theorem syncPeriod_eq_mul (D : ℕ) : syncPeriod D = (2 ^ D) * 45 := by
  unfold syncPeriod
  have h2 : Nat.Coprime 2 45 := by decide
  have h : Nat.Coprime (2 ^ D) 45 := h2.pow_left D
  simpa using h.lcm_eq_mul

/-! ### Synchronization Selection Principle (proved) -/

/-- A direct formalization of the paper's minimization statement:
among all `D ≥ 3`, the function `D ↦ lcm(2^D,45)` is minimized uniquely at `D = 3`. -/
theorem synchronization_selection_principle {D : ℕ} (hD : 3 ≤ D) :
    syncPeriod 3 ≤ syncPeriod D ∧ (syncPeriod D = syncPeriod 3 → D = 3) := by
  constructor
  · -- monotonicity from the closed form
    have h3 : syncPeriod 3 = (2 ^ 3) * 45 := syncPeriod_eq_mul 3
    have hD' : syncPeriod D = (2 ^ D) * 45 := syncPeriod_eq_mul D
    -- show 2^3 ≤ 2^D using D = 3 + k
    rcases Nat.exists_eq_add_of_le hD with ⟨k, rfl⟩
    have hk : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    have hpow : 2 ^ 3 ≤ 2 ^ (3 + k) := by
      calc
        2 ^ 3 = 2 ^ 3 * 1 := by ring
        _ ≤ 2 ^ 3 * 2 ^ k := by exact Nat.mul_le_mul_left (2 ^ 3) hk
        _ = 2 ^ (3 + k) := by
          -- 2^(3+k) = 2^3 * 2^k
          simp [Nat.pow_add]
    -- multiply by 45 on the right (commuting as needed)
    have hmul : (2 ^ 3) * 45 ≤ (2 ^ (3 + k)) * 45 := by
      -- use commutativity so we can multiply on the left
      have : 45 * (2 ^ 3) ≤ 45 * (2 ^ (3 + k)) := Nat.mul_le_mul_left 45 hpow
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    simpa [h3, hD', Nat.add_assoc] using hmul
  · intro heq
    -- use strictness: if D>3 then syncPeriod 3 < syncPeriod D, contradiction
    rcases Nat.exists_eq_add_of_le hD with ⟨k, rfl⟩
    cases k with
    | zero =>
        simp
    | succ k =>
        have hlt : 3 < 3 + Nat.succ k := Nat.lt_add_of_pos_right (by exact Nat.succ_pos _)
        have hpowlt : 2 ^ 3 < 2 ^ (3 + Nat.succ k) :=
          Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hlt
        have h3 : syncPeriod 3 = (2 ^ 3) * 45 := syncPeriod_eq_mul 3
        have hD' : syncPeriod (3 + Nat.succ k) = (2 ^ (3 + Nat.succ k)) * 45 :=
          syncPeriod_eq_mul (3 + Nat.succ k)
        have hmul : syncPeriod 3 < syncPeriod (3 + Nat.succ k) := by
          -- multiply strict inequality by 45 > 0 (again using commutativity)
          have : 45 * (2 ^ 3) < 45 * (2 ^ (3 + Nat.succ k)) :=
            (Nat.mul_lt_mul_left (by decide : 0 < 45)).2 hpowlt
          -- rewrite back to the paper order `(2^D)*45`
          have : (2 ^ 3) * 45 < (2 ^ (3 + Nat.succ k)) * 45 := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
          simpa [h3, hD'] using this
        -- contradiction: strict inequality implies not-equal
        exfalso
        exact (Nat.ne_of_lt hmul) (heq.symm)

/-! A convenience corollary matching the paper's explicit numeric claim `lcm(8,45)=360`. -/
theorem syncPeriod_3_eq_360 : syncPeriod 3 = 360 := by
  native_decide

/-! The paper also packages the minimization in terms of a resource functional
\(\mathcal{F}(D,45)=\alpha\,\mathrm{lcm}(2^D,45)+\beta D\) with \(\alpha>0,\beta\ge0\).
We record that consequence here. -/

/-- If `α>0` and `β≥0`, then the resource functional
`F(D)=α * lcm(2^D,45) + β * D` is minimized at `D=3` among `D≥3`. -/
theorem sync_resource_functional_minimized (α β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β)
    {D : ℕ} (hD : 3 ≤ D) :
    α * (syncPeriod 3 : ℝ) + β * (3 : ℝ) ≤ α * (syncPeriod D : ℝ) + β * (D : ℝ) := by
  have hsyncNat : syncPeriod 3 ≤ syncPeriod D := (synchronization_selection_principle (D := D) hD).1
  have hsync : (syncPeriod 3 : ℝ) ≤ (syncPeriod D : ℝ) := by
    exact_mod_cast hsyncNat
  have hdim : (3 : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hD
  have h1 : α * (syncPeriod 3 : ℝ) ≤ α * (syncPeriod D : ℝ) :=
    mul_le_mul_of_nonneg_left hsync (le_of_lt hα)
  have h2 : β * (3 : ℝ) ≤ β * (D : ℝ) :=
    mul_le_mul_of_nonneg_left hdim hβ
  linarith

/-! ## Constraint (K): Kepler non-precession (algebraic core) -/

open Real

/-- The apsidal-angle formula used in `Draft_v1.tex` after substituting the Green-kernel power
law: `Δθ(D) = 2π / √(4 - D)` (with `D` treated as a real parameter). -/
noncomputable def apsidalAngle (D : ℕ) : ℝ :=
  (2 * Real.pi) / Real.sqrt (4 - (D : ℝ))

/-- A direct formalization of the paper's last step:
`Δθ = 2π` holds iff `D=3` for the substituted closed-form apsidal angle. -/
theorem kepler_selection_principle (D : ℕ) :
    apsidalAngle D = 2 * Real.pi ↔ D = 3 := by
  constructor
  · intro h
    have hpi : (2 * Real.pi) ≠ 0 := by
      exact mul_ne_zero (by norm_num) Real.pi_ne_zero
    -- Let x be the denominator √(4 - D).
    set x : ℝ := Real.sqrt (4 - (D : ℝ))
    have hx : x ≠ 0 := by
      intro hx0
      have : apsidalAngle D = 0 := by
        simp [apsidalAngle, x, hx0]
      have h0 : 0 = 2 * Real.pi := by
        simpa [this] using h
      exact hpi h0.symm
    -- Rewrite h as (2π) * x⁻¹ = 2π, then cancel.
    have h' : (2 * Real.pi) * x⁻¹ = 2 * Real.pi := by
      simpa [apsidalAngle, x, div_eq_mul_inv] using h
    have hmul : (2 * Real.pi) * (x⁻¹ * x) = (2 * Real.pi) * x := by
      -- multiply both sides by x
      simpa [mul_assoc] using congrArg (fun t => t * x) h'
    have hmul' : (2 * Real.pi) = (2 * Real.pi) * x := by
      simpa [mul_assoc, inv_mul_cancel₀ hx, mul_one] using hmul
    -- cancel 2π to get x = 1
    have hx1 : x = 1 := by
      have hcancel : (2 * Real.pi) * x = (2 * Real.pi) * 1 := by
        calc
          (2 * Real.pi) * x = (2 * Real.pi) := by simpa [mul_assoc] using hmul'.symm
          _ = (2 * Real.pi) * 1 := by simp
      exact mul_left_cancel₀ hpi hcancel
    -- show 0 ≤ 4 - D so we can square the sqrt
    have hnonneg : 0 ≤ 4 - (D : ℝ) := by
      by_contra hneg
      have hle : 4 - (D : ℝ) ≤ 0 := le_of_not_ge hneg
      have : Real.sqrt (4 - (D : ℝ)) = 0 := Real.sqrt_eq_zero_of_nonpos hle
      -- but x = sqrt(...) = 1
      have : (1 : ℝ) = 0 := by simpa [x, hx1] using this
      exact one_ne_zero this
    have hsq : x ^ 2 = 4 - (D : ℝ) := by
      simpa [x, pow_two] using (Real.sq_sqrt hnonneg)
    -- x=1 => 4 - D = 1 => D = 3
    have hreal : (D : ℝ) = 3 := by
      have : (1 : ℝ) ^ 2 = 4 - (D : ℝ) := by simpa [hx1] using hsq
      nlinarith
    -- cast-injectivity to return to ℕ
    exact (Nat.cast_injective (R := ℝ) (by simpa using hreal))
  · intro hD
    subst hD
    have : (4 - (3 : ℝ)) = (1 : ℝ) := by norm_num
    simp [apsidalAngle, this]

/-! ## Paper Packaging: Dimensional Rigidity (T/K/S) -/

/-- Paper-style (S) constraint: `D` is admissible (`D ≥ 3`) and is a minimizer of `syncPeriod`. -/
def ConstraintS (D : ℕ) : Prop :=
  3 ≤ D ∧ ∀ D', 3 ≤ D' → syncPeriod D ≤ syncPeriod D'

/-- Paper-style (K) constraint, reduced to the closed-form apsidal-angle condition. -/
def ConstraintK (D : ℕ) : Prop :=
  apsidalAngle D = 2 * Real.pi

/-! The (S) constraint is fully formalized here (arithmetic only). -/

theorem constraintS_forces_D3 {D : ℕ} (hS : ConstraintS D) : D = 3 := by
  have hD : 3 ≤ D := hS.1
  have hle : syncPeriod D ≤ syncPeriod 3 := hS.2 3 (le_rfl)
  have hge : syncPeriod 3 ≤ syncPeriod D := (synchronization_selection_principle (D := D) hD).1
  have heq : syncPeriod D = syncPeriod 3 := le_antisymm hle hge
  exact (synchronization_selection_principle (D := D) hD).2 heq

theorem constraintS_iff_D3 (D : ℕ) : ConstraintS D ↔ D = 3 := by
  constructor
  · intro hS; exact constraintS_forces_D3 hS
  · intro hD
    subst hD
    refine ⟨le_rfl, ?_⟩
    intro D' hD'
    exact (synchronization_selection_principle (D := D') hD').1

/-!
Paper-style (T) constraint and Alexander duality are now formalized in
`IndisputableMonolith.Foundation.AlexanderDuality`. The Alexander duality
hypothesis interface below delegates to the cohomology-based predicate
`SphereAdmitsCircleLinking`, which is proved equivalent to D = 3 from
the reduced cohomology axiom for S¹.
-/

open IndisputableMonolith.Foundation.AlexanderDuality

/-- Hypothesis interface for the Alexander-duality computation used in `Draft_v1.tex`.
Now delegates to the cohomology-based `SphereAdmitsCircleLinking` from
`AlexanderDuality.lean` rather than being a vacuous `True`. -/
def AlexanderDualityForCircleHypothesis (D : ℕ) : Prop :=
  SphereAdmitsCircleLinking D

/-- Hypothesis interface for the paper's ``integer-valued loop-linking invariant exists'' premise.
Now delegates to the cohomology-based linking predicate. -/
def LinkingInvariantHypothesis (D : ℕ) : Prop :=
  SphereAdmitsCircleLinking D

/-! ## Remaining paper propositions (placeholders) -/

/-- Placeholder for the paper proposition ``RG Conditions for Duality''.

Status: not yet formalized (topology of quotients + local contractibility). -/
def RGConditionsForDualityHypothesis : Prop := True

theorem rg_conditions_for_duality (_h : RGConditionsForDualityHypothesis) : True := trivial

/-- Placeholder for the paper proposition ``RG Derivation of Central Potentials''.

Status: not yet formalized (Laplacian / Green's functions). -/
def CentralPotentialDerivationHypothesis : Prop := True

theorem rg_derivation_of_central_potentials (_h : CentralPotentialDerivationHypothesis) : True := trivial

/-- Placeholder for the paper proposition ``Robustness of D=3 Signature''.

Status: not yet formalized (perturbation theory / IFT / continuity). -/
def RobustnessHypothesis : Prop := True

theorem robustness_of_D3_signature (_h : RobustnessHypothesis) : True := trivial

/-- The (T) setup assumptions required for Alexander duality in the paper
are satisfied for this dimension. Now delegates to the cohomology-based
`SphereAdmitsCircleLinking` rather than being vacuous. -/
def AlexanderDualityApplies (D : ℕ) : Prop :=
  AlexanderDualityForCircleHypothesis D

/-- Paper proposition (T): Linking selection principle.

Previously an explicit hypothesis interface; now the bridge from
linking to D = 3 is provided by `alexander_duality_circle_linking`. -/
def LinkingSelectionPrincipleHypothesis (D : ℕ) : Prop :=
  LinkingInvariantHypothesis D → D = 3

theorem linking_selection_principle (D : ℕ)
    (h : LinkingSelectionPrincipleHypothesis D) (hLink : LinkingInvariantHypothesis D) :
    D = 3 :=
  h hLink

/-- Paper main theorem (forward direction): if (T), (K), (S) hold then `D=3`.

In the current repo, (S) and (K) are fully formalized at the arithmetic/algebraic level;
(T) is recorded but not used in the proof here. -/
theorem dimensional_rigidity_main (D : ℕ)
    (_hT : LinkingInvariantHypothesis D)
    (hK : ConstraintK D)
    (_hS : ConstraintS D) :
    D = 3 :=
  (kepler_selection_principle D).1 hK

/-- Paper combined theorem (full statement): forward direction plus a partial converse.

Status: the converse direction is recorded in the paper but depends on substantial
geometric infrastructure; we record only the forward direction as proved above. -/
theorem dimensional_rigidity_full_forward (D : ℕ)
    (hT : LinkingInvariantHypothesis D) (hK : ConstraintK D) (hS : ConstraintS D) :
    D = 3 :=
  dimensional_rigidity_main D hT hK hS

/-- Paper corollary: there is no `D > 3` satisfying all three constraints simultaneously.

We prove this using the (K)-based forcing `ConstraintK D → D=3`. -/
theorem no_higher_dimensional_alternative (D : ℕ) (hD : 3 < D)
    (hT : LinkingInvariantHypothesis D) (hK : ConstraintK D) (hS : ConstraintS D) :
    False := by
  have h3 : D = 3 := dimensional_rigidity_full_forward D hT hK hS
  have : D ≤ 3 := by simp [h3]
  exact (not_le_of_gt hD) this

end DraftV1
end Papers
end IndisputableMonolith
