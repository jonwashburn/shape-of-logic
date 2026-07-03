import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.DAlembert.Counterexamples
import IndisputableMonolith.Foundation.DAlembert.NecessityGates

/-!
# Entanglement Gate: Cross-Derivative Characterization

This module formalizes the **Entanglement Gate**: the requirement that the combiner P
has nonzero cross-derivative ∂²P/∂u∂v.

## Key Results

1. The additive combiner P(u,v) = 2u + 2v has ∂²P/∂u∂v = 0 (separable)
2. The RCL combiner P(u,v) = 2uv + 2u + 2v has ∂²P/∂u∂v = 2 (entangling)
3. Entanglement is equivalent to interaction under smoothness

## Physical Interpretation

Entanglement means: "Observing a composite system xy is NOT just the sum of
observing x and y separately. There is an interaction term that couples them."

This is precisely the 2uv term in the RCL.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DAlembert
namespace EntanglementGate

open Real Cost

/-! ## Definitions -/

/-- A combiner P is *separable* if P(u,v) = α(u) + β(v) for some α, β. -/
def IsSeparable (P : ℝ → ℝ → ℝ) : Prop :=
  ∃ α β : ℝ → ℝ, ∀ u v, P u v = α u + β v

/-- A combiner P is *entangling* (non-separable) if it's not of the form α(u) + β(v).
    Equivalently, the "mixed second difference" is nonzero at some point. -/
def IsEntangling (P : ℝ → ℝ → ℝ) : Prop :=
  ∃ u₀ v₀ u₁ v₁ : ℝ, P u₁ v₁ - P u₁ v₀ - P u₀ v₁ + P u₀ v₀ ≠ 0

/-- For smooth P, the cross-derivative at a point. -/
noncomputable def crossDeriv (P : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  deriv (fun u' => deriv (fun v' => P u' v') v) u

/-! ## The Additive Combiner is Separable -/

/-- The additive combiner from the counterexample. -/
def Padd (u v : ℝ) : ℝ := 2 * u + 2 * v

/-- Padd is separable: P(u,v) = 2u + 2v = α(u) + β(v). -/
theorem Padd_separable : IsSeparable Padd := by
  use fun u => 2 * u, fun v => 2 * v
  intro u v
  rfl

/-- The mixed second difference of Padd is zero. -/
theorem Padd_mixed_diff_zero : ∀ u₀ v₀ u₁ v₁ : ℝ,
    Padd u₁ v₁ - Padd u₁ v₀ - Padd u₀ v₁ + Padd u₀ v₀ = 0 := by
  intro u₀ v₀ u₁ v₁
  simp only [Padd]
  ring

/-- Padd is not entangling. -/
theorem Padd_not_entangling : ¬ IsEntangling Padd := by
  intro ⟨u₀, v₀, u₁, v₁, h⟩
  exact h (Padd_mixed_diff_zero u₀ v₀ u₁ v₁)

/-! ## The RCL Combiner is Entangling -/

/-- The RCL combiner. -/
def Prcl (u v : ℝ) : ℝ := 2 * u * v + 2 * u + 2 * v

/-- The mixed second difference of Prcl equals 2(u₁-u₀)(v₁-v₀).
    In particular, it's nonzero when u₁ ≠ u₀ and v₁ ≠ v₀. -/
theorem Prcl_mixed_diff : ∀ u₀ v₀ u₁ v₁ : ℝ,
    Prcl u₁ v₁ - Prcl u₁ v₀ - Prcl u₀ v₁ + Prcl u₀ v₀ = 2 * (u₁ - u₀) * (v₁ - v₀) := by
  intro u₀ v₀ u₁ v₁
  simp only [Prcl]
  ring

/-- Prcl is entangling. Witness: (0,0) and (1,1) give mixed diff = 2. -/
theorem Prcl_entangling : IsEntangling Prcl := by
  use 0, 0, 1, 1
  rw [Prcl_mixed_diff]
  norm_num

/-- Prcl is NOT separable. -/
theorem Prcl_not_separable : ¬ IsSeparable Prcl := by
  intro ⟨α, β, h⟩
  -- If Prcl(u,v) = α(u) + β(v), then the mixed second difference is 0
  have hsep : Prcl 1 1 - Prcl 1 0 - Prcl 0 1 + Prcl 0 0 = 0 := by
    calc Prcl 1 1 - Prcl 1 0 - Prcl 0 1 + Prcl 0 0
        = (α 1 + β 1) - (α 1 + β 0) - (α 0 + β 1) + (α 0 + β 0) := by
          simp only [h 1 1, h 1 0, h 0 1, h 0 0]
      _ = 0 := by ring
  rw [Prcl_mixed_diff] at hsep
  norm_num at hsep

/-! ## Separability is Equivalent to Zero Mixed Difference -/

/-- Separable implies zero mixed difference. -/
theorem separable_implies_zero_mixed_diff (P : ℝ → ℝ → ℝ) (hSep : IsSeparable P) :
    ∀ u₀ v₀ u₁ v₁, P u₁ v₁ - P u₁ v₀ - P u₀ v₁ + P u₀ v₀ = 0 := by
  obtain ⟨α, β, h⟩ := hSep
  intro u₀ v₀ u₁ v₁
  simp only [h]
  ring

/-- Separable implies not entangling (contrapositive of entangling implies not separable). -/
theorem separable_implies_not_entangling (P : ℝ → ℝ → ℝ) (hSep : IsSeparable P) :
    ¬ IsEntangling P := by
  intro ⟨u₀, v₀, u₁, v₁, h⟩
  exact h (separable_implies_zero_mixed_diff P hSep u₀ v₀ u₁ v₁)

/-! ## Connection to the F-level Interaction Gate -/

/-- If P is separable AND satisfies both boundary conditions,
    then P must be the additive combiner 2u + 2v. -/
theorem separable_with_boundary_is_additive (P : ℝ → ℝ → ℝ)
    (hSep : IsSeparable P)
    (hBdryU : ∀ u, P u 0 = 2 * u)
    (hBdryV : ∀ v, P 0 v = 2 * v) :
    ∀ u v, P u v = 2 * u + 2 * v := by
  obtain ⟨α, β, hαβ⟩ := hSep
  -- From hBdryU: α(u) + β(0) = 2u, so α(u) = 2u - β(0)
  have hα : ∀ u, α u = 2 * u - β 0 := by
    intro u
    have := hBdryU u
    rw [hαβ] at this
    linarith
  -- From hBdryV: α(0) + β(v) = 2v, so β(v) = 2v - α(0)
  have hβ : ∀ v, β v = 2 * v - α 0 := by
    intro v
    have := hBdryV v
    rw [hαβ] at this
    linarith
  -- From hα at u=0: α(0) = -β(0)
  have hα0 : α 0 = -β 0 := by
    have := hα 0
    simp at this
    exact this
  intro u v
  rw [hαβ]
  -- Goal: α u + β v = 2 * u + 2 * v
  have hαu := hα u
  have hβv := hβ v
  rw [hαu, hβv, hα0]
  ring

/-- If F has no interaction and P satisfies boundary conditions,
    then P is the additive combiner. -/
theorem no_interaction_implies_additive (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (hCons : ∀ x y : ℝ, 0 < x → 0 < y → F (x * y) + F (x / y) = P (F x) (F y))
    (hNorm : F 1 = 0)
    (hNoInt : ¬ NecessityGates.HasInteraction F) :
    ∀ u v : ℝ, (∃ x y, 0 < x ∧ 0 < y ∧ F x = u ∧ F y = v) →
      P u v = 2 * u + 2 * v := by
  intro u v ⟨x, y, hx, hy, hFx, hFy⟩
  -- hNoInt says: ∀ x y, 0 < x → 0 < y → F(xy) + F(x/y) = 2 F x + 2 F y
  simp only [NecessityGates.HasInteraction, not_exists, not_and, not_not] at hNoInt
  have hAdd := hNoInt x y hx hy
  rw [hCons x y hx hy] at hAdd
  -- hAdd : P (F x) (F y) = 2 * F x + 2 * F y
  rw [← hFx, ← hFy]
  exact hAdd

/-! ## Main Theorem: Entanglement is Necessary for RCL -/

/-- If F has interaction and symmetry, then ANY consistent combiner P must be entangling. -/
theorem interaction_implies_entangling (F : ℝ → ℝ) (P : ℝ → ℝ → ℝ)
    (hCons : ∀ x y : ℝ, 0 < x → 0 < y → F (x * y) + F (x / y) = P (F x) (F y))
    (hNorm : F 1 = 0)
    (hSymm : ∀ x : ℝ, 0 < x → F x = F x⁻¹)
    (hInt : NecessityGates.HasInteraction F) :
    IsEntangling P := by
  -- Proof by contradiction: suppose P is not entangling
  by_contra hNotEnt
  simp only [IsEntangling, not_exists, not_not] at hNotEnt
  -- Then P has zero mixed difference everywhere
  obtain ⟨x, y, hx, hy, hNeq⟩ := hInt
  have hcons := hCons x y hx hy
  -- Mixed difference = 0 implies P decomposes additively
  have hMixed : ∀ u₀ v₀ u₁ v₁, P u₁ v₁ - P u₁ v₀ - P u₀ v₁ + P u₀ v₀ = 0 :=
    fun u₀ v₀ u₁ v₁ => hNotEnt u₀ v₀ u₁ v₁
  have hDecomp : ∀ u v, P u v = P u 0 + P 0 v - P 0 0 := by
    intro u v
    have := hMixed 0 0 u v
    linarith
  -- P(u, 0) = 2u from normalization
  have hBdryU : ∀ u, (∃ x', 0 < x' ∧ F x' = u) → P u 0 = 2 * u := by
    intro u ⟨x', hxpos, hFx'⟩
    have hc := hCons x' 1 hxpos one_pos
    simp only [mul_one, div_one, hNorm] at hc
    rw [← hFx']
    linarith
  -- P(0, v) = 2v from symmetry: F(1·y) + F(1/y) = P(0, F y), and F(1/y) = F(y)
  have hBdryV : ∀ v, (∃ y', 0 < y' ∧ F y' = v) → P 0 v = 2 * v := by
    intro v ⟨y', hypos, hFy'⟩
    have hc := hCons 1 y' one_pos hypos
    simp only [one_mul, one_div, hNorm] at hc
    -- hc : F y' + F y'⁻¹ = P 0 (F y')
    have hsym := hSymm y' hypos
    -- hsym : F y' = F y'⁻¹, so F y' + F y'⁻¹ = F y' + F y' = 2 * F y'
    rw [← hsym] at hc
    -- hc : F y' + F y' = P 0 (F y')
    rw [← hFy']
    linarith
  -- P(0, 0) = 0
  have hP00 : P 0 0 = 0 := by
    have := hCons 1 1 one_pos one_pos
    simp only [mul_one, div_one, hNorm] at this
    linarith
  -- On the range of F, P(u, v) = 2u + 2v
  have hPadd : P (F x) (F y) = 2 * F x + 2 * F y := by
    rw [hDecomp]
    rw [hBdryU (F x) ⟨x, hx, rfl⟩]
    rw [hBdryV (F y) ⟨y, hy, rfl⟩]
    rw [hP00]
    ring
  -- But F has interaction: F(xy) + F(x/y) ≠ 2 F x + 2 F y
  -- And consistency: F(xy) + F(x/y) = P(F x, F y) = 2 F x + 2 F y
  rw [hcons] at hNeq
  exact hNeq hPadd

/-! ## The Gate Theorem -/

/-- **Entanglement Gate Theorem**: J has interaction, hence any consistent combiner
    for J must be entangling (not separable). The RCL combiner satisfies this. -/
theorem entanglement_gate_theorem :
    NecessityGates.HasInteraction Cost.Jcost ∧
    IsEntangling Prcl ∧
    ¬ IsEntangling Padd := by
  refine ⟨NecessityGates.Jcost_hasInteraction, Prcl_entangling, Padd_not_entangling⟩

end EntanglementGate
end DAlembert
end Foundation
end IndisputableMonolith
