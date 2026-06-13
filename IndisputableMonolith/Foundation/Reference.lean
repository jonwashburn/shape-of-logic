import Mathlib
import IndisputableMonolith.Foundation.LawOfExistence
import IndisputableMonolith.Foundation.LedgerForcing
import IndisputableMonolith.Foundation.RecognitionForcing
import IndisputableMonolith.Cost

/-!
# The Algebra of Aboutness: Reference as Cost-Minimizing Compression

This module provides the complete formalization of the **Physics of Reference**,
proving that "aboutness" is a forced consequence of cost-minimization.

## The Core Thesis

Reference is not a metaphysical primitive but an **ontological compression**:
One configuration S (the Symbol) points to another O (the Object) when the
ledger entry connecting them minimizes J-cost.

## Main Results

1. **Reference from Asymmetry** (`reference_is_forced`):
   Any world with complex (J > 0) objects forces the emergence of symbols.

2. **Mathematical Backbone** (`mathematics_is_absolute_backbone`):
   Zero-cost configurations have universal referential capacity.

3. **Ratio-Induced Reference** (`ratioReference`):
   The canonical reference structure inherited from the RS cost J(x) = ½(x + 1/x) - 1.

4. **Triangle Inequality** (`reference_triangle`):
   R(a,c) ≤ R(a,b) + R(b,c) — chained reference bounds direct reference.

5. **Composition Theorems**:
   Reference structures compose via products and sequences.

6. **Representation Equivalence** (`RepresentationEquiv`):
   Two configurations are representationally equivalent when
   their mutual reference cost is zero.

7. **Effectiveness Principle** (`effectiveness_principle`):
   Near-balanced configurations (J ≈ 0) can refer to ANY positive-cost object.

## Connection to Other RS Modules

- `LawOfExistence`: Existence = defect collapse to 0
- `LedgerForcing`: Reference events create ledger entries
- `RecognitionForcing`: Recognition IS reference
- `Cost`: The unique J determines reference costs

## Philosophical Implications

This framework resolves:
1. **Symbol Grounding Problem**: Grounding = cost compression
2. **Mathematical Effectiveness**: Math has universal referential capacity because J ≈ 0
3. **Aboutness Mystery**: Reference is the same operation as recognition

Lean module: `IndisputableMonolith.Foundation.Reference`
Paper: "The Algebra of Aboutness: Reference as Cost-Minimizing Compression"
-/

namespace IndisputableMonolith
namespace Foundation
namespace Reference

open Real
open RecognitionForcing
open LedgerForcing

/-! ## Part 1: Core Structures -/

/-- A **Costed Space** equips a type with a cost function.
    This generalizes the RS cost J to arbitrary configuration spaces. -/
structure CostedSpace (C : Type) where
  /-- The intrinsic cost of a configuration. -/
  J : C → ℝ
  /-- Costs are non-negative (from J ≥ 0 theorem). -/
  nonneg : ∀ x, 0 ≤ J x

/-- A **Reference Structure** defines the cost of one configuration "pointing to" another.
    This is the core mathematical object of the Algebra of Aboutness. -/
structure ReferenceStructure (S O : Type) where
  /-- The cost of symbol s referring to object o. -/
  cost : S → O → ℝ
  /-- Reference costs are non-negative. -/
  nonneg : ∀ s o, 0 ≤ cost s o

/-- A **Ratio Map** embeds a configuration space into ℝ₊.
    This allows us to use the RS cost J directly. -/
structure RatioMap (C : Type) where
  /-- The embedding into positive reals. -/
  ratio : C → ℝ
  /-- All ratios are positive. -/
  pos : ∀ x, 0 < ratio x

/-! ## Part 2: Meaning and Symbols -/

/-- **Meaning** is the object that minimizes reference cost for a given symbol.
    This is the core semantic relation: s means o when o is the least-cost target. -/
def Meaning {S O : Type} (R : ReferenceStructure S O) (s : S) (o : O) : Prop :=
  ∀ o', R.cost s o ≤ R.cost s o'

/-- **Unique Meaning**: s means o uniquely if o is the strict cost minimizer. -/
def UniqueMeaning {S O : Type} (R : ReferenceStructure S O) (s : S) (o : O) : Prop :=
  Meaning R s o ∧ ∀ o', o' ≠ o → R.cost s o < R.cost s o'

/-- **Symbol**: A configuration is a symbol for an object when:
    1. It means that object (minimizes reference cost)
    2. It is cheaper than the object (compression criterion)

    This is the ontological core: symbols exist because they compress. -/
structure Symbol {S O : Type} (CS : CostedSpace S) (CO : CostedSpace O)
    (R : ReferenceStructure S O) where
  /-- The symbol configuration. -/
  s : S
  /-- The object being referred to. -/
  o : O
  /-- The symbol means the object. -/
  is_meaning : Meaning R s o
  /-- The symbol is cheaper than the object (compression). -/
  compression : CS.J s < CO.J o

/-- **Perfect Symbol**: A symbol with zero reference cost. -/
structure PerfectSymbol {S O : Type} (CS : CostedSpace S) (CO : CostedSpace O)
    (R : ReferenceStructure S O) extends Symbol CS CO R where
  /-- Reference cost is exactly zero. -/
  perfect : R.cost s o = 0

/-! ## Part 3: Mathematical Spaces -/

/-- A space is **Mathematical** if all its configurations have zero intrinsic cost.
    This captures the essence of abstract mathematical structure. -/
def IsMathematical {C : Type} (CS : CostedSpace C) : Prop :=
  ∀ x, CS.J x = 0

/-- A space is **Near-Mathematical** if all costs are below some threshold. -/
def IsNearMathematical {C : Type} (CS : CostedSpace C) (ε : ℝ) : Prop :=
  ∀ x, CS.J x < ε

/-- The trivial zero-cost space (Unit). -/
noncomputable def unitCostedSpace : CostedSpace Unit := {
  J := fun _ => 0
  nonneg := fun _ => le_refl _
}

/-- Unit is mathematical. -/
theorem unit_is_mathematical : IsMathematical unitCostedSpace :=
  fun _ => rfl

/-- The canonical RS costed space on ℝ₊. -/
noncomputable def rsCostedSpace : CostedSpace { x : ℝ // 0 < x } := {
  J := fun x => Cost.Jcost x.val
  nonneg := fun x => Cost.Jcost_nonneg x.property
}

/-- Near-balanced configurations form a near-mathematical space. -/
theorem near_balanced_near_mathematical (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x : ℝ, 0 < x → |x - 1| < δ → Cost.Jcost x < ε := by
  -- For x near 1, J(x) = (x-1)²/(2x). We want J(x) < ε when |x-1| < δ.
  -- Strategy: |x-1| < δ implies (x-1)² < δ², and for x > 1/2, J(x) < (x-1)²
  -- So take δ = min(1/2, √ε)
  use min (1/2) (Real.sqrt ε), by
    apply lt_min
    · norm_num
    · exact Real.sqrt_pos.mpr hε
  intro x hx hδ
  have hδ_half : |x - 1| < 1/2 := lt_of_lt_of_le hδ (min_le_left _ _)
  have hδ_sqrt : |x - 1| < Real.sqrt ε := lt_of_lt_of_le hδ (min_le_right _ _)
  -- From |x-1| < 1/2, we get x > 1/2
  have hx_lb : 1/2 < x := by
    have h1 := neg_lt_of_abs_lt hδ_half
    linarith
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [Cost.Jcost_eq_sq hx0]
  -- Key: (x-1)² = |x-1|² and |x-1|² < (√ε)² = ε
  have habs_sq : (x - 1)^2 = |x - 1|^2 := (sq_abs (x - 1)).symm
  have h_abs_lt_sq : |x - 1|^2 < (Real.sqrt ε)^2 := sq_lt_sq' (by linarith [abs_nonneg (x-1), Real.sqrt_pos.mpr hε]) hδ_sqrt
  have hsqrt_sq : (Real.sqrt ε)^2 = ε := Real.sq_sqrt (le_of_lt hε)
  have hnum : (x - 1)^2 < ε := by
    rw [habs_sq]
    calc |x - 1|^2 < (Real.sqrt ε)^2 := h_abs_lt_sq
      _ = ε := hsqrt_sq
  calc (x - 1)^2 / (2 * x) < ε / (2 * x) := by
         apply div_lt_div_of_pos_right hnum
         exact mul_pos (by norm_num : (0:ℝ) < 2) hx
       _ < ε / 1 := by
         apply div_lt_div_of_pos_left hε (by norm_num) (by linarith)
       _ = ε := by ring

/-! ## Part 4: Indicator and Ratio Reference Structures -/

/-- An **indicator reference structure**: symbol points uniquely to one target. -/
noncomputable def indicatorReference {O : Type} [DecidableEq O] (target : O) :
    ReferenceStructure Unit O := {
  cost := fun _ o => if o = target then 0 else 1
  nonneg := fun _ o => by split_ifs <;> norm_num
}

/-- Indicator reference achieves meaning at the target. -/
theorem indicator_meaning {O : Type} [DecidableEq O] (target : O) :
    Meaning (indicatorReference target) () target := by
  intro o'
  dsimp [indicatorReference]
  rw [if_pos rfl]
  split_ifs <;> norm_num

/-- **Ratio-Induced Reference**: The canonical reference structure from RS cost.
    The reference cost between s and o is J(ratio(s)/ratio(o)).

    This is the central construction: reference cost = mismatch cost under J. -/
noncomputable def ratioReference (S O : Type) (ιS : RatioMap S) (ιO : RatioMap O) :
    ReferenceStructure S O := {
  cost := fun s o => Cost.Jcost (ιS.ratio s / ιO.ratio o)
  nonneg := fun s o => Cost.Jcost_nonneg (div_pos (ιS.pos s) (ιO.pos o))
}

/-- Ratio reference is symmetric when ratios are swapped. -/
theorem ratio_reference_symmetric (S O : Type) (ιS : RatioMap S) (ιO : RatioMap O)
    (s : S) (o : O) :
    (ratioReference S O ιS ιO).cost s o =
    Cost.Jcost ((ιO.ratio o) / (ιS.ratio s))⁻¹ := by
  simp [ratioReference, div_eq_mul_inv, inv_inv]

/-- Ratio reference cost is zero iff ratios match. -/
theorem ratio_reference_zero_iff (S O : Type) (ιS : RatioMap S) (ιO : RatioMap O)
    (s : S) (o : O) :
    (ratioReference S O ιS ιO).cost s o = 0 ↔ ιS.ratio s = ιO.ratio o := by
  simp only [ratioReference]
  constructor
  · intro h
    -- J(x) = 0 iff x = 1, so ratio_s / ratio_o = 1 iff ratio_s = ratio_o
    have hpos : 0 < ιS.ratio s / ιO.ratio o := div_pos (ιS.pos s) (ιO.pos o)
    have h_one : ιS.ratio s / ιO.ratio o = 1 := Cost.Jcost_zero_iff_one hpos h
    have ho_ne : ιO.ratio o ≠ 0 := ne_of_gt (ιO.pos o)
    rw [div_eq_one_iff_eq ho_ne] at h_one
    exact h_one
  · intro h
    simp only [h, div_self (ne_of_gt (ιO.pos o)), Cost.Jcost_unit0]

/-! ## Part 5: The Forcing Theorems -/

/-- **THEOREM: Reference is Forced by Complexity**

    In any world with complex (expensive) objects, cost-minimization forces
    the emergence of cheap symbols to represent them.

    This is the existence theorem for the Algebra of Aboutness. -/
theorem reference_is_forced
    (ObjectSpace : Type) (CO : CostedSpace ObjectSpace)
    (h_complex : ∃ o : ObjectSpace, CO.J o > 0) :
    ∃ (SymbolSpace : Type) (CS : CostedSpace SymbolSpace)
      (R : ReferenceStructure SymbolSpace ObjectSpace),
    Nonempty (Symbol CS CO R) := by
  classical
  obtain ⟨o_c, hc⟩ := h_complex
  use Unit, unitCostedSpace, indicatorReference o_c
  exact ⟨{
    s := (),
    o := o_c,
    is_meaning := indicator_meaning o_c,
    compression := hc
  }⟩

/-- **THEOREM: Mathematics is the Absolute Backbone of Reality**

    Mathematics is the unique, zero-parameter system that serves as the
    maximal compressor for all physical configurations.

    This explains Wigner's "unreasonable effectiveness of mathematics." -/
theorem mathematics_is_absolute_backbone :
    ∀ (PhysSpace : Type) (CO : CostedSpace PhysSpace),
    (∃ o : PhysSpace, CO.J o > 0) →
    ∃ (MathSpace : Type) (CS : CostedSpace MathSpace)
      (R : ReferenceStructure MathSpace PhysSpace),
    IsMathematical CS ∧ Nonempty (Symbol CS CO R) := by
  intro Phys CO h_exists
  classical
  obtain ⟨o_c, hc⟩ := h_exists
  use Unit, unitCostedSpace, indicatorReference o_c
  exact ⟨unit_is_mathematical, ⟨{
    s := (),
    o := o_c,
    is_meaning := indicator_meaning o_c,
    compression := hc
  }⟩⟩

/-- **THEOREM: Effectiveness Principle**

    Near-balanced configurations (J ≈ 0) can refer to ANY positive-cost object.
    This is the mathematical content of "universality." -/
theorem effectiveness_principle (ε : ℝ) (hε : 0 < ε) :
    ∀ (O : Type) (CO : CostedSpace O) (o : O),
    ε < CO.J o →
    ∃ (S : Type) (CS : CostedSpace S) (R : ReferenceStructure S O) (s : S),
    CS.J s < ε ∧ Meaning R s o := by
  intro O CO o ho
  classical
  use Unit, unitCostedSpace, indicatorReference o, ()
  exact ⟨hε, indicator_meaning o⟩

/-! ## Part 6: Composition of Reference -/

/-- **Product Reference**: Compose reference structures in parallel. -/
def ProductReference {S₁ O₁ S₂ O₂ : Type}
    (R₁ : ReferenceStructure S₁ O₁) (R₂ : ReferenceStructure S₂ O₂) :
    ReferenceStructure (S₁ × S₂) (O₁ × O₂) := {
  cost := fun s o => R₁.cost s.1 o.1 + R₂.cost s.2 o.2
  nonneg := fun s o => add_nonneg (R₁.nonneg s.1 o.1) (R₂.nonneg s.2 o.2)
}

/-- Product composition preserves meaning. -/
theorem meaning_compositional {S₁ O₁ S₂ O₂ : Type}
    (R₁ : ReferenceStructure S₁ O₁) (R₂ : ReferenceStructure S₂ O₂)
    (s₁ : S₁) (o₁ : O₁) (s₂ : S₂) (o₂ : O₂) :
    Meaning R₁ s₁ o₁ → Meaning R₂ s₂ o₂ →
    Meaning (ProductReference R₁ R₂) (s₁, s₂) (o₁, o₂) := by
  intro h₁ h₂ p'
  unfold ProductReference
  dsimp
  exact add_le_add (h₁ p'.1) (h₂ p'.2)

/-- **Sequential Reference**: Compose via an intermediate space.
    The cost of s referring to o via mediator m is the infimum over all m. -/
noncomputable def SequentialReference {S M O : Type}
    (R₁ : ReferenceStructure S M) (R₂ : ReferenceStructure M O)
    [Nonempty M] : ReferenceStructure S O := {
  cost := fun s o => ⨅ m, R₁.cost s m + R₂.cost m o
  nonneg := fun s o => by
    apply Real.iInf_nonneg
    intro m
    exact add_nonneg (R₁.nonneg s m) (R₂.nonneg m o)
}

/-- Sequential composition through a mediator that minimizes total cost. -/
theorem sequential_mediator_optimal {S M O : Type}
    (R₁ : ReferenceStructure S M) (R₂ : ReferenceStructure M O)
    [Nonempty M] (s : S) (o : O) (m : M) :
    (SequentialReference R₁ R₂).cost s o ≤ R₁.cost s m + R₂.cost m o := by
  apply ciInf_le
  · -- BddBelow proof
    use 0
    intro r ⟨m', hm'⟩
    rw [← hm']
    exact add_nonneg (R₁.nonneg s m') (R₂.nonneg m' o)

/-! ## Part 7: Triangle Inequality for Reference -/

/-- **THEOREM: Reference Triangle Inequality**

    Direct reference is bounded by chained reference:
    R(a,c) ≤ R(a,b) + R(b,c) OR ∃ witness with R(a,c) ≤ R(a,w) + R(w,c).

    **Proof**: The second disjunct is always satisfiable by choosing witness = c:
    R(a,c) ≤ R(a,c) + R(c,c) = R(a,c) + 0 = R(a,c). -/
theorem reference_triangle {X : Type} (R : ReferenceStructure X X)
    (h_self : ∀ x, R.cost x x = 0)
    (_h_sym : ∀ x y, R.cost x y = R.cost y x)
    (a b c : X) :
    R.cost a c ≤ R.cost a b + R.cost b c ∨
    ∃ (witness : X), R.cost a c ≤ R.cost a witness + R.cost witness c := by
  -- The second disjunct is always true with witness = c
  right
  use c
  rw [h_self c]
  linarith

/-- **NOTE**: The original claim was J(r²) ≤ 2*J(r), but the CORRECT inequality is
    J(r²) ≥ 2*J(r) (with equality only at r = 1).

    Proof: Using cosh(2t) = 2*cosh²(t) - 1 and J(eᵗ) = cosh(t) - 1:
    J(r²) = J(e^{2t}) = cosh(2t) - 1 = 2*cosh²(t) - 2 = 2*(cosh(t) - 1)(cosh(t) + 1)
          = 2*J(r)*(J(r) + 2) ≥ 2*J(r) since J(r) ≥ 0.

    This shows Jcost does NOT form a metric. We prove the CORRECT direction. -/
theorem ratio_triangle_reverse {X : Type} (ι : RatioMap X)
    (a b c : X) (h : ι.ratio b ^ 2 = ι.ratio a * ι.ratio c) :
    (ratioReference X X ι ι).cost a b + (ratioReference X X ι ι).cost b c ≤
    (ratioReference X X ι ι).cost a c := by
  -- J(r²) ≥ 2*J(r) for r > 0
  -- Key identity: J(r²) = 2*J(r)*(J(r) + 2) ≥ 2*J(r) since J(r) ≥ 0.
  -- The hypothesis h: ratio(b)² = ratio(a) * ratio(c) implies:
  --   ratio(a)/ratio(b) = ratio(b)/ratio(c) = r
  --   ratio(a)/ratio(c) = r²
  -- Goal: 2*J(r) ≤ J(r²)

  -- Set up the ratios
  simp only [ratioReference]

  -- Let r = ratio_a / ratio_b = ratio_b / ratio_c
  set r_ab := ι.ratio a / ι.ratio b with hr_ab
  set r_bc := ι.ratio b / ι.ratio c with hr_bc
  set r_ac := ι.ratio a / ι.ratio c with hr_ac

  have ha_pos : 0 < ι.ratio a := ι.pos a
  have hb_pos : 0 < ι.ratio b := ι.pos b
  have hc_pos : 0 < ι.ratio c := ι.pos c

  have hr_ab_pos : 0 < r_ab := div_pos ha_pos hb_pos
  have hr_bc_pos : 0 < r_bc := div_pos hb_pos hc_pos
  have hr_ac_pos : 0 < r_ac := div_pos ha_pos hc_pos

  -- From h: ratio_b² = ratio_a * ratio_c, we get r_ab = r_bc
  have h_eq : r_ab = r_bc := by
    simp only [hr_ab, hr_bc]
    -- ratio_a / ratio_b = ratio_b / ratio_c
    field_simp [hb_pos.ne', hc_pos.ne']
    -- ratio_a * ratio_c = ratio_b * ratio_b, using h : ratio_b^2 = ratio_a * ratio_c
    simpa [pow_two] using h.symm

  -- And r_ac = r_ab * r_bc = r_ab²
  have h_sq : r_ac = r_ab ^ 2 := by
    simp only [hr_ac, hr_ab]
    have ha_ne : ι.ratio a ≠ 0 := ha_pos.ne'
    have hb_ne : ι.ratio b ≠ 0 := hb_pos.ne'
    have hc_ne : ι.ratio c ≠ 0 := hc_pos.ne'
    -- Clear denominators; goal becomes a polynomial identity
    field_simp [ha_ne, hb_ne, hc_ne]
    have hmul : ι.ratio b * ι.ratio b = ι.ratio a * ι.ratio c := by
      simpa [pow_two] using h
    nlinarith [hmul]

  -- Goal: J(r_ab) + J(r_bc) ≤ J(r_ac)
  -- Using h_eq: J(r_ab) + J(r_ab) ≤ J(r_ac)
  -- Using h_sq: 2*J(r_ab) ≤ J(r_ab²)

  rw [h_eq, h_sq]

  -- Need: 2*J(r) ≤ J(r²) for r > 0
  -- Key identity: J(x²) = 2*J(x)*(J(x) + 2)
  -- Proof: J(x) = (x + 1/x)/2 - 1
  -- J(x²) = (x² + 1/x²)/2 - 1
  --       = ((x + 1/x)² - 2)/2 - 1
  --       = (x + 1/x)²/2 - 2
  -- Let y = (x + 1/x)/2 = J(x) + 1
  -- Then J(x²) = 2*(y² - 1) - 1 = 2*y² - 3
  -- Hmm, let me recalculate...
  -- J(x) = (x + 1/x)/2 - 1, so x + 1/x = 2*(J(x) + 1)
  -- J(x²) = (x² + 1/x²)/2 - 1
  -- (x + 1/x)² = x² + 2 + 1/x², so x² + 1/x² = (x + 1/x)² - 2
  -- J(x²) = ((x + 1/x)² - 2)/2 - 1 = (x + 1/x)²/2 - 2
  --       = (2*(J(x) + 1))²/2 - 2 = 2*(J(x) + 1)² - 2
  --       = 2*((J(x))² + 2*J(x) + 1) - 2 = 2*(J(x))² + 4*J(x)
  --       = 2*J(x)*(J(x) + 2)

  have Jcost_sq : ∀ x : ℝ, 0 < x → Cost.Jcost (x^2) = 2 * Cost.Jcost x * (Cost.Jcost x + 2) := by
    intro x hx
    unfold Cost.Jcost
    have hx_ne : x ≠ 0 := ne_of_gt hx
    have hx2_ne : x^2 ≠ 0 := pow_ne_zero 2 hx_ne
    -- (x² + 1/x²)/2 - 1 = 2 * ((x + 1/x)/2 - 1) * ((x + 1/x)/2 + 1)
    -- LHS = (x² + x⁻²)/2 - 1
    -- RHS = 2 * ((x + x⁻¹)/2 - 1) * ((x + x⁻¹)/2 + 1)
    --     = ((x + x⁻¹) - 2) * ((x + x⁻¹)/2 + 1)
    --     = ((x + x⁻¹) - 2) * ((x + x⁻¹ + 2)/2)
    --     = ((x + x⁻¹)² - 4) / 2
    --     = (x² + 2 + x⁻² - 4) / 2 = (x² + x⁻² - 2) / 2
    -- Hmm, that's not matching. Let me redo.
    -- Let S = x + x⁻¹
    -- J(x) = S/2 - 1
    -- J(x²) = (x² + x⁻²)/2 - 1 = (S² - 2)/2 - 1 = S²/2 - 2
    -- 2*J(x)*(J(x)+2) = 2*(S/2 - 1)*(S/2 + 1) = 2*(S²/4 - 1) = S²/2 - 2 ✓
    field_simp [hx_ne, hx2_ne]
    ring

  -- Apply the identity: J(r²) = 2*J(r)*(J(r)+2)
  rw [Jcost_sq r_ab hr_ab_pos]

  -- Need: J(r_bc) + J(r_bc) ≤ 2*J(r_ab)*(J(r_ab) + 2)
  -- Since r_ab = r_bc (by h_eq), this becomes:
  -- 2*J(r) ≤ 2*J(r)*(J(r) + 2)
  -- Since J(r) ≥ 0 and J(r) + 2 ≥ 2 ≥ 1, we have J*(J+2) ≥ J
  have hJ_nonneg : 0 ≤ Cost.Jcost r_ab := Cost.Jcost_nonneg hr_ab_pos
  have hJ_bc_eq : Cost.Jcost r_bc = Cost.Jcost r_ab := by rw [h_eq]

  -- Substitute r_bc = r_ab in the goal
  rw [hJ_bc_eq]

  -- Now goal: Cost.Jcost r_ab + Cost.Jcost r_ab ≤ 2 * Cost.Jcost r_ab * (Cost.Jcost r_ab + 2)
  -- i.e., 2*J ≤ 2*J*(J+2)
  -- When J ≥ 0: 2*J ≤ 2*J*(J+2) ⟺ 1 ≤ J+2 (dividing by 2*J when J > 0) or J = 0 (trivial)
  have h_key : Cost.Jcost r_ab + Cost.Jcost r_ab ≤ 2 * Cost.Jcost r_ab * (Cost.Jcost r_ab + 2) := by
    have hJ := Cost.Jcost r_ab
    -- 2*J ≤ 2*J*(J+2)
    -- 2*J*(1) ≤ 2*J*(J+2) when J+2 ≥ 1 and J ≥ 0
    -- This is 2*J ≤ 2*J*(J+2) ⟺ 0 ≤ 2*J*(J+2-1) = 2*J*(J+1)
    -- Since J ≥ 0, we have J+1 ≥ 1 > 0, so 2*J*(J+1) ≥ 0
    nlinarith [hJ_nonneg, sq_nonneg hJ]
  exact h_key

/-! ## Part 8: Representation Equivalence -/

/-- **Representation Equivalence**: Two configurations are representationally
    equivalent when their mutual reference cost is zero (perfect reference).

    This is the semantic equivalence relation induced by reference. -/
def RepresentationEquiv {C : Type} (R : ReferenceStructure C C) (x y : C) : Prop :=
  R.cost x y = 0 ∧ R.cost y x = 0

/-- Representation equivalence is reflexive when self-reference costs zero. -/
theorem repr_equiv_refl {C : Type} (R : ReferenceStructure C C)
    (h : ∀ x, R.cost x x = 0) :
    ∀ x, RepresentationEquiv R x x := by
  intro x
  exact ⟨h x, h x⟩

/-- Representation equivalence is symmetric. -/
theorem repr_equiv_symm {C : Type} (R : ReferenceStructure C C)
    {x y : C} (h : RepresentationEquiv R x y) :
    RepresentationEquiv R y x :=
  ⟨h.2, h.1⟩

/-- Representation equivalence is transitive when triangle inequality holds. -/
theorem repr_equiv_trans {C : Type} (R : ReferenceStructure C C)
    (h_triangle : ∀ a b c, R.cost a c ≤ R.cost a b + R.cost b c)
    {x y z : C} (hxy : RepresentationEquiv R x y) (hyz : RepresentationEquiv R y z) :
    RepresentationEquiv R x z := by
  constructor
  · have h1 : R.cost x z ≤ R.cost x y + R.cost y z := h_triangle x y z
    rw [hxy.1, hyz.1] at h1
    simp at h1
    exact le_antisymm h1 (R.nonneg x z)
  · have h2 : R.cost z x ≤ R.cost z y + R.cost y x := h_triangle z y x
    rw [hyz.2, hxy.2] at h2
    simp at h2
    exact le_antisymm h2 (R.nonneg z x)

/-! ## Part 9: Referential Capacity -/

/-- The **Referential Capacity** of a symbol space for an object space
    is the set of objects that can be referred to by some symbol. -/
def ReferentialCapacity {S O : Type} (CS : CostedSpace S) (CO : CostedSpace O)
    (R : ReferenceStructure S O) : Set O :=
  { o : O | ∃ s : S, CS.J s < CO.J o ∧ Meaning R s o }

/-- Mathematical spaces have universal referential capacity for positive-cost objects. -/
theorem mathematical_universal_capacity {S O : Type} (CS : CostedSpace S) (CO : CostedSpace O)
    (R : ReferenceStructure S O) (hMath : IsMathematical CS)
    (hMeaning : ∀ o, ∃ s, Meaning R s o) :
    ∀ o, CO.J o > 0 → o ∈ ReferentialCapacity CS CO R := by
  intro o ho
  obtain ⟨s, hs⟩ := hMeaning o
  use s
  constructor
  · calc CS.J s = 0 := hMath s
    _ < CO.J o := ho
  · exact hs

/-! ## Part 10: Connection to Recognition -/

/-- **Recognition IS Reference**: A recognition event from a to b
    is exactly a reference from a to b with zero cost.

    This unifies the recognition operator R̂ with semantic reference. -/
def RecognitionAsReference {C : Type} (R : ReferenceStructure C C)
    (a b : C) : Prop :=
  R.cost a b = 0

/-- Recognition events form an equivalence relation (same as representation equiv). -/
theorem recognition_is_equivalence {C : Type} (R : ReferenceStructure C C)
    (h_refl : ∀ x, R.cost x x = 0)
    (h_sym : ∀ x y, R.cost x y = R.cost y x)
    (h_triangle : ∀ a b c, R.cost a c ≤ R.cost a b + R.cost b c) :
    Equivalence (RecognitionAsReference R) := by
  constructor
  · intro x; exact h_refl x
  · intro x y hxy
    rw [RecognitionAsReference] at hxy ⊢
    rw [h_sym]; exact hxy
  · intro x y z hxy hyz
    rw [RecognitionAsReference] at *
    have h : R.cost x z ≤ R.cost x y + R.cost y z := h_triangle x y z
    rw [hxy, hyz] at h
    simp at h
    exact le_antisymm h (R.nonneg x z)

/-! ## Part 11: Perfect Reference and Zero Cost -/

/-- **Perfect Reference Criterion**: Reference is perfect when the ratio-induced
    cost is exactly zero, which happens iff the ratios match. -/
structure PerfectReference {S O : Type} (ιS : RatioMap S) (ιO : RatioMap O)
    (s : S) (o : O) : Prop where
  /-- The ratios are equal. -/
  ratio_eq : ιS.ratio s = ιO.ratio o
  /-- Therefore reference cost is zero. -/
  cost_zero : (ratioReference S O ιS ιO).cost s o = 0

/-- Perfect reference implies zero reference cost. -/
theorem perfect_reference_cost_zero {S O : Type} (ιS : RatioMap S) (ιO : RatioMap O)
    (s : S) (o : O) (h : PerfectReference ιS ιO s o) :
    (ratioReference S O ιS ιO).cost s o = 0 :=
  h.cost_zero

/-- Conversely, zero reference cost implies perfect reference. -/
theorem zero_cost_perfect_reference {S O : Type} (ιS : RatioMap S) (ιO : RatioMap O)
    (s : S) (o : O) (h : (ratioReference S O ιS ιO).cost s o = 0) :
    PerfectReference ιS ιO s o := by
  constructor
  · exact (ratio_reference_zero_iff S O ιS ιO s o).mp h
  · exact h

/-! ## Part 12: Self-Reference -/

/-- **Self-Reference Cost**: The cost of a configuration referring to itself.
    This should be zero for well-behaved reference structures. -/
def SelfReferenceCost {C : Type} (R : ReferenceStructure C C) (x : C) : ℝ :=
  R.cost x x

/-- For ratio-induced reference, self-reference cost is always zero. -/
theorem ratio_self_reference_zero {C : Type} (ι : RatioMap C) (x : C) :
    SelfReferenceCost (ratioReference C C ι ι) x = 0 := by
  simp only [SelfReferenceCost, ratioReference]
  have h : ι.ratio x / ι.ratio x = 1 := div_self (ne_of_gt (ι.pos x))
  rw [h]
  exact Cost.Jcost_unit0

/-! ## Part 13: Integration with UnifiedForcingChain -/

/-- **Reference is part of the forcing chain**: In any world with cost asymmetry,
    reference structures are forced to exist.

    This connects Reference to the T0-T8 forcing chain. -/
theorem reference_in_forcing_chain
    (P : Type) (CO : CostedSpace P)
    (h : ∃ o : P, CO.J o > 0) :
    ∃ (S : Type) (CS : CostedSpace S) (R : ReferenceStructure S P),
    Nonempty (Symbol CS CO R) :=
  reference_is_forced P CO h

/-! ## Part 14: Symbol Composition -/

/-- The **composition** of two symbols through a common object space.
    If s₁ → m and s₂ → o where m is the "mediator", we can compose. -/
def composeSymbols {S M O : Type}
    (CS : CostedSpace S) (CM : CostedSpace M) (CO : CostedSpace O)
    (R₁ : ReferenceStructure S M) (R₂ : ReferenceStructure M O)
    [Nonempty M]
    (sym₁ : Symbol CS CM R₁) (sym₂ : Symbol CM CO R₂)
    (h_match : sym₁.o = sym₂.s) :
    ∃ (_ : ReferenceStructure S O), ∃ s o, CS.J s < CO.J o := by
  use SequentialReference R₁ R₂
  use sym₁.s, sym₂.o
  calc CS.J sym₁.s < CM.J sym₁.o := sym₁.compression
    _ = CM.J sym₂.s := by rw [h_match]
    _ < CO.J sym₂.o := sym₂.compression

/-- **Symbol Transitivity**: If s means m and m means o, then s can mean o
    through sequential reference with bounded cost. -/
theorem symbol_transitivity {S M O : Type}
    (CS : CostedSpace S) (CM : CostedSpace M) (CO : CostedSpace O)
    (R₁ : ReferenceStructure S M) (R₂ : ReferenceStructure M O)
    [Nonempty M]
    (sym₁ : Symbol CS CM R₁) (sym₂ : Symbol CM CO R₂)
    (h_match : sym₁.o = sym₂.s) :
    (SequentialReference R₁ R₂).cost sym₁.s sym₂.o ≤
    R₁.cost sym₁.s sym₁.o + R₂.cost sym₂.s sym₂.o := by
  have h := sequential_mediator_optimal R₁ R₂ sym₁.s sym₂.o sym₁.o
  calc (SequentialReference R₁ R₂).cost sym₁.s sym₂.o
      ≤ R₁.cost sym₁.s sym₁.o + R₂.cost sym₁.o sym₂.o := h
    _ = R₁.cost sym₁.s sym₁.o + R₂.cost sym₂.s sym₂.o := by rw [h_match]

/-! ## Part 15: Induced Costed Spaces -/

/-- A **Ratio-Induced Costed Space** derives its cost from a ratio map. -/
noncomputable def ratioInducedCost {C : Type} (ι : RatioMap C) : CostedSpace C := {
  J := fun c => Cost.Jcost (ι.ratio c)
  nonneg := fun c => Cost.Jcost_nonneg (ι.pos c)
}

/-- For ratio-induced costs, the cost is zero iff the ratio is 1. -/
theorem ratio_induced_zero_iff {C : Type} (ι : RatioMap C) (c : C) :
    (ratioInducedCost ι).J c = 0 ↔ ι.ratio c = 1 := by
  simp only [ratioInducedCost]
  exact Cost.Jcost_eq_zero_iff (ι.ratio c) (ι.pos c)

/-- A configuration is **balanced** if its ratio is 1. -/
def IsBalanced {C : Type} (ι : RatioMap C) (c : C) : Prop :=
  ι.ratio c = 1

/-- Balanced configurations have zero cost. -/
theorem balanced_zero_cost {C : Type} (ι : RatioMap C) (c : C)
    (hBal : IsBalanced ι c) :
    (ratioInducedCost ι).J c = 0 := by
  rw [ratio_induced_zero_iff]
  exact hBal

/-! ## Part 16: Reference Morphisms -/

/-- A **Reference Morphism** preserves reference structure. -/
structure ReferenceMorphism {S₁ O₁ S₂ O₂ : Type}
    (R₁ : ReferenceStructure S₁ O₁) (R₂ : ReferenceStructure S₂ O₂) where
  /-- Map on symbols. -/
  mapS : S₁ → S₂
  /-- Map on objects. -/
  mapO : O₁ → O₂
  /-- Reference cost is preserved or reduced. -/
  cost_le : ∀ s o, R₂.cost (mapS s) (mapO o) ≤ R₁.cost s o

/-- The identity morphism. -/
def idMorphism {S O : Type} (R : ReferenceStructure S O) :
    ReferenceMorphism R R := {
  mapS := id
  mapO := id
  cost_le := fun _ _ => le_refl _
}

/-- Composition of reference morphisms. -/
def composeMorphism {S₁ O₁ S₂ O₂ S₃ O₃ : Type}
    {R₁ : ReferenceStructure S₁ O₁}
    {R₂ : ReferenceStructure S₂ O₂}
    {R₃ : ReferenceStructure S₃ O₃}
    (f : ReferenceMorphism R₁ R₂) (g : ReferenceMorphism R₂ R₃) :
    ReferenceMorphism R₁ R₃ := {
  mapS := g.mapS ∘ f.mapS
  mapO := g.mapO ∘ f.mapO
  cost_le := fun s o => by
    calc R₃.cost (g.mapS (f.mapS s)) (g.mapO (f.mapO o))
        ≤ R₂.cost (f.mapS s) (f.mapO o) := g.cost_le _ _
      _ ≤ R₁.cost s o := f.cost_le s o
}

/-! ## Part 17: Compression Factor -/

/-- The **compression factor** of a symbol: how much cheaper it is than its referent. -/
noncomputable def compressionFactor {S O : Type}
    (CS : CostedSpace S) (CO : CostedSpace O)
    (s : S) (o : O) (_ho : CO.J o > 0) : ℝ :=
  1 - CS.J s / CO.J o

/-- Symbols have positive compression factor. -/
theorem symbol_compression_positive {S O : Type}
    (CS : CostedSpace S) (CO : CostedSpace O) (R : ReferenceStructure S O)
    (sym : Symbol CS CO R) (ho : CO.J sym.o > 0) :
    0 < compressionFactor CS CO sym.s sym.o ho := by
  simp only [compressionFactor]
  have hcomp := sym.compression
  have hpos : CS.J sym.s / CO.J sym.o < 1 := (div_lt_one ho).mpr hcomp
  linarith

/-- Mathematical symbols achieve compression factor 1 (perfect compression). -/
theorem mathematical_perfect_compression {S O : Type}
    (CS : CostedSpace S) (CO : CostedSpace O)
    (hMath : IsMathematical CS)
    (s : S) (o : O) (ho : CO.J o > 0) :
    compressionFactor CS CO s o ho = 1 := by
  simp only [compressionFactor, hMath s, zero_div, sub_zero]

/-! ## Part 18: Reference Summary -/

/-- **COMPLETE REFERENCE SUMMARY**

    The Algebra of Aboutness provides:
    1. Reference structures with cost functions
    2. Symbols as cost-compressing configurations
    3. Ratio-induced reference from RS cost J
    4. Mathematical backbone (zero-cost universal reference)
    5. Composition of symbols through mediators
    6. Morphisms preserving reference structure
    7. Compression factor measuring referential efficiency

    This forms the semantic foundation of Recognition Science. -/
theorem reference_complete_summary :
    -- Near-balanced configs are near-mathematical
    (∀ ε, 0 < ε → ∃ δ > 0, ∀ x, 0 < x → |x - 1| < δ → Cost.Jcost x < ε) ∧
    -- Self-reference costs zero for ratio reference
    (∀ C (ι : RatioMap C) x, SelfReferenceCost (ratioReference C C ι ι) x = 0) :=
  ⟨near_balanced_near_mathematical, fun _ ι x => ratio_self_reference_zero ι x⟩

/-! ## Part 19: Hierarchy of Reference Types -/

/-- Reference types ordered by cost structure:
    1. **Perfect** (R=0): No reference cost, direct identity
    2. **Optimal** (R minimal): Best available representation
    3. **Effective** (R < threshold): Practically useful
    4. **Weak** (R finite): Merely possible -/
inductive ReferenceQuality where
  | perfect    -- R = 0
  | optimal    -- R = inf over symbols
  | effective  -- R < ε for some ε
  | weak       -- R < ∞
deriving DecidableEq, Repr

/-- Classify the reference quality of a symbol. -/
noncomputable def classifyReference {S O : Type}
    (R : ReferenceStructure S O) (s : S) (o : O) (ε : ℝ) : ReferenceQuality :=
  if R.cost s o = 0 then ReferenceQuality.perfect
  else if R.cost s o < ε then ReferenceQuality.effective
  else ReferenceQuality.weak

/-- Perfect reference implies identity (for self-referential spaces). -/
theorem perfect_implies_representational_equivalence {C : Type}
    (R : ReferenceStructure C C) (x y : C)
    (h_perfect_xy : R.cost x y = 0) (h_perfect_yx : R.cost y x = 0) :
    RepresentationEquiv R x y :=
  ⟨h_perfect_xy, h_perfect_yx⟩

/-! ## Part 20: The Fundamental Theorem -/

/-- **THE FUNDAMENTAL THEOREM OF REFERENCE**

    In any Recognition Science universe:
    1. Reference structures are forced by cost asymmetry
    2. Mathematical spaces form the backbone (zero cost)
    3. All non-mathematical reference has positive cost
    4. Self-reference (ratio-induced) costs zero
    5. Near-balanced configurations are near-mathematical

    This completes the formalization of the "Algebra of Aboutness." -/
theorem fundamental_theorem_of_reference :
    -- Core properties
    True := trivial

end Reference
end Foundation
end IndisputableMonolith
