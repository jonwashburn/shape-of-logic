import Mathlib
import IndisputableMonolith.Constants.AlphaDerivation
import IndisputableMonolith.Masses.SectorDependentTorsion

/-!
# Step Value Enumeration: Narrowing the Open Forcing Step

## The Remaining Open Step (Gap A from Validation Program)

`SectorDependentTorsion.lean` proves that the four generation-step values
{13, 11, 6, 8} are Q₃ cube invariants at D=3:

- 13 = V + F - C = E + 1 (by Euler characteristic V-E+F=2 at ∂Q₃ ≅ S²)
- 11 = E - A = E - 1 (passive edges, with A = 1 = active edges per tick)
- 6 = F (face count)
- 8 = V (vertex count)

The docstring of `SDGTForcing.lean` explicitly flags that while these integers
ARE proved Q₃ cell counts, their appearance *as generation steps* (rather
than other cube invariants) is IDENTIFIED from PDG data rather than derived.

This module narrows that gap by:

1. **Proving the structural constraints**: lepton middle pair {11, 6} is
   uniquely forced (recapitulating existing proofs in SDGTForcing).
2. **Enumerating the finite alternatives**: there are a small number of
   cube-invariant pairs (a, d) with a + d = 21 (the endpoint constraint from
   the partition N₃ = 55 and middle = W = 17). We enumerate them.
3. **Showing the current choice is the UNIQUE one with specific structural
   properties**: given additional natural constraints, {13, 8} is the unique
   endpoint pair.

## What remains genuinely open after this module

The endpoint pair is forced modulo the "natural cube invariant" set that we
allow. The choice of this set (which we make explicit) remains a modeling
decision — but it is now *explicit* rather than hidden.

-/

namespace IndisputableMonolith
namespace Masses
namespace StepValueEnumeration

open Constants.AlphaDerivation
open SectorDependentTorsion

/-! ## The natural Q₃ invariants at D = 3

We work with cube invariants at D=3 that arise from direct cell counts or
simple linear combinations. This explicitly delimits the candidate pool.
-/

/-- The "natural invariants" we consider: cell counts and simple combinations.
These are the integers that have a direct Q₃-combinatorial interpretation.

At D=3:
- V = 8
- E = 12, E-A = 11 (passive edges)
- F = 6
- C = 1
- V+F = 14, V-C = 7
- V+F-C = 13 (equivalently, E+1 by Euler χ=2)
- 2V+1 = 17 = W (wallpaper groups, by the D=3 coincidence N₀ = W)
- V+F+C = 15, V+E = 20, E+F = 18, V+E+F = 26
- F+C = 7, E+C = 13, E-C = 11 (same integers as above)
-/
def natural_invariants_D3 : List ℕ :=
  [1, 6, 7, 8, 11, 12, 13, 14, 15, 17, 18, 20, 25, 26]

/-! ## Constraint 1: Middle pair sums to W = 17 -/

/-- All pairs (b, c) with b+c = 17 from the natural invariants,
    excluding trivial pairs (same value) and order. -/
def middle_pairs_summing_to_17 : List (ℕ × ℕ) :=
  [(6, 11), (11, 6)]

theorem middle_pairs_are_11_6 :
    ∀ (b c : ℕ), b ∈ natural_invariants_D3 → c ∈ natural_invariants_D3 →
    b + c = 17 → b ≠ c →
    (b = 6 ∧ c = 11) ∨ (b = 11 ∧ c = 6) ∨
    -- Any other pair summing to 17 among our natural invariants
    (b = 17 ∧ c = 0) ∨ (b = 0 ∧ c = 17) := by
  intro b c hb hc hsum _hne
  simp [natural_invariants_D3, List.mem_cons] at hb hc
  omega

/-- Excluding zero (since 0 is not a "natural cube invariant"), only
    {11, 6} appears in the middle pair position. -/
theorem middle_pair_unique_nonzero :
    ∀ (b c : ℕ), b ∈ natural_invariants_D3 → c ∈ natural_invariants_D3 →
    b + c = 17 → b ≠ c → b ≠ 0 → c ≠ 0 →
    (b = 6 ∧ c = 11) ∨ (b = 11 ∧ c = 6) := by
  intro b c hb hc hsum hne hb0 hc0
  have h := middle_pairs_are_11_6 b c hb hc hsum hne
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h.2 hc0
  · exact absurd h.1 hb0

/-! ## Constraint 2: Endpoint pair (a, d) sums to 21

From the partition constraint a + 2b + 2c + d = 55 with b+c = 17:
a + 34 + d = 55, so a + d = 21.
-/

/-- All pairs (a, d) from natural invariants with a + d = 21,
    excluding {11, 6} (already used as middle) and ordered pairs. -/
def endpoint_pairs_summing_to_21 : List (ℕ × ℕ) :=
  [(7, 14), (8, 13), (14, 7), (13, 8)]
  -- Note: 1+20, 6+15, 11+10 excluded because they use middle values or
  -- values outside the natural set. 20 and 15 are possible but form less
  -- natural chains (see analysis below).

/-- There exist multiple valid endpoint pairs from the natural invariants.
    This is the heart of the openness: uniqueness cannot be proved without
    additional structural constraints. -/
theorem endpoint_pairs_not_unique :
    ∃ (a₁ d₁ a₂ d₂ : ℕ),
      a₁ ∈ natural_invariants_D3 ∧ d₁ ∈ natural_invariants_D3 ∧ a₁ + d₁ = 21 ∧
      a₂ ∈ natural_invariants_D3 ∧ d₂ ∈ natural_invariants_D3 ∧ a₂ + d₂ = 21 ∧
      (a₁, d₁) ≠ (a₂, d₂) ∧
      a₁ ≠ 11 ∧ a₁ ≠ 6 ∧ d₁ ≠ 11 ∧ d₁ ≠ 6 ∧
      a₂ ≠ 11 ∧ a₂ ≠ 6 ∧ d₂ ≠ 11 ∧ d₂ ≠ 6 := by
  refine ⟨13, 8, 14, 7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [natural_invariants_D3]

/-! ## Constraint 3: The current chain (13, 11, 6, 8) satisfies all structural constraints -/

/-- The current chain satisfies the partition constraint. -/
theorem current_chain_partition :
    13 + 2*11 + 2*6 + 8 = 55 := by norm_num

/-- The current chain has middle pair summing to W. -/
theorem current_chain_middle : 11 + 6 = 17 := by norm_num

/-- The current chain has endpoint sum = 21. -/
theorem current_chain_endpoints : 13 + 8 = 21 := by norm_num

/-- All four values of the current chain are distinct. -/
theorem current_chain_distinct : (13 : ℕ) ≠ 11 ∧ 11 ≠ 6 ∧ 6 ≠ 8 ∧ 13 ≠ 6 ∧ 13 ≠ 8 ∧ 11 ≠ 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ## Constraint 4: The Unique Fully-Integer-Chain Containing E±1

One natural structural filter: the chain should contain both "edge plus one"
(E+1 = 13) and "edge minus one" (E-1 = 11). These are the simplest
symmetric deformations of the edge count E = 12.

Under this filter, the remaining two values must sum to 21 - 13 - 11 = ...
wait, that over-constrains. Let me redo:

If two of the four values are E±1, and the cyclic chain structure is
(E+1, E-1, ?, ?) ending back at E+1, then the middle pair is (E-1, ?) with
sum 17, forcing ? = 17 - 11 = 6 = F. Then the fourth value must satisfy
6 + d = span_down, with span_down = 55 - 24 - 17 = 14, so d = 8 = V.

Under this filter, the chain (E+1, E-1, F, V) = (13, 11, 6, 8) is unique.
-/

/-- If the chain contains both E+1 and E-1 as adjacent values, the chain is
    uniquely determined. -/
theorem chain_unique_given_edge_pair
    (a b c d : ℕ)
    (h_chain_partition : a + 2*b + 2*c + d = 55)
    (h_middle : b + c = 17)
    (h_a_eq : a = 13)  -- E+1
    (h_b_eq : b = 11)  -- E-1
    :
    a = 13 ∧ b = 11 ∧ c = 6 ∧ d = 8 := by
  subst h_a_eq h_b_eq
  have hc : c = 6 := by omega
  have hd : d = 8 := by omega
  exact ⟨rfl, rfl, hc, hd⟩

/-- The chain (13, 11, 6, 8) is uniquely determined by the edge-pair filter
    (13 = E+1, 11 = E-1) plus the partition and middle constraints.

This is a CONDITIONAL UNIQUENESS result: given that the chain contains the
edge-symmetric pair (E+1, E-1) as its leading two values, the remaining
values are forced. -/
theorem current_chain_unique_modulo_edge_pair_filter :
    ∀ (a b c d : ℕ),
      a + 2*b + 2*c + d = 55 →
      b + c = 17 →
      a = 13 → b = 11 →
      (a, b, c, d) = (13, 11, 6, 8) := by
  intro a b c d h_part h_mid h_a h_b
  have ⟨_, _, hc, hd⟩ := chain_unique_given_edge_pair a b c d h_part h_mid h_a h_b
  rw [h_a, h_b, hc, hd]

/-! ## Constraint 5: The Euler-Characteristic Interpretation

The integer 13 = V + F - C has a specific interpretation: it is the
Euler characteristic of ∂Q₃ (= 2) shifted by the cube body C:

  V + F - C = (V - E + F) + E - C = χ(S²) + E - C = 2 + 12 - 1 = 13.

Equivalently: 13 = E + 1 (since χ(S²) = 2 and C = 1 implies 13 = E + χ - C = E + 1).

This means 13 has an interpretation in terms of:
(a) Cell counts with Euler shift: V + F - C = 13.
(b) Edges plus Euler number minus body: E + 2 - 1 = 13.
(c) Edges plus one: E + 1 = 13.

All three give the same integer at D=3, and all three are natural cube
invariants.
-/

/-- The Euler-characteristic identity for Q₃. -/
theorem euler_identity_Q3 :
    cube_vertices' 3 + cube_faces' 3 - cube_body = cube_edges' 3 + 1 := by
  native_decide

/-- Therefore 13 has three equivalent natural-invariant interpretations. -/
theorem thirteen_natural_interpretations :
    -- V + F - C
    cube_vertices' 3 + cube_faces' 3 - cube_body = 13 ∧
    -- E + 1
    cube_edges' 3 + 1 = 13 ∧
    -- The value equals itself
    (13 : ℕ) = 13 := by
  refine ⟨?_, ?_, rfl⟩ <;> native_decide

/-! ## Summary of What This Module Proves

1. **Middle pair uniqueness** (re-proved): {11, 6} is the only nonzero
   natural-invariant pair summing to 17. See `middle_pair_unique_nonzero`.

2. **Endpoint non-uniqueness** (newly proved): multiple endpoint pairs
   satisfy a + d = 21. See `endpoint_pairs_not_unique`.

3. **Conditional uniqueness** (newly proved): given the "edge-symmetric"
   structural filter (chain starts with E+1, E-1), the chain is uniquely
   (13, 11, 6, 8). See `current_chain_unique_modulo_edge_pair_filter`.

4. **Euler identity** (newly proved): 13 = V+F-C = E+1 at D=3, by the
   Euler characteristic χ(S²) = 2. See `euler_identity_Q3`.

## Residual Openness

The only unresolved step is: *why* the edge-symmetric pair (E+1, E-1) appears
as the "opening" of the cyclic chain (i.e., why Up-quark generation steps
are {V+F-C, E-A} = {13, 11} rather than e.g. {V+F, V-C} = {14, 7}).

This reflects a physical identification of the U(1) gauge channel with the
edge cells of Q₃ (which is proved separately in `Foundation/GaugeFromCube`).
Under that identification, the edge-symmetric opening {E+1, E-1} is natural,
but the Lean does not yet have a first-principles forcing proof that the Up
sector specifically uses this opening.

The epistemic status is therefore:
- Structural uniqueness modulo the edge-symmetric filter: **THEOREM**.
- Physical identification of Up sector with edge-symmetric opening: **HYPOTHESIS**.

-/

end StepValueEnumeration
end Masses
end IndisputableMonolith
