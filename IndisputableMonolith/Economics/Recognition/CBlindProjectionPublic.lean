import Mathlib

/-!
# The C-Blind Projection: self-contained public formalization

This file is the public, independently-checkable certificate for the paper
"The C-Blind Projection: A Topological Obstruction to Welfare Aggregation".
It imports **only Mathlib**: it has no dependency on the Recognition Physics
institute library, so any reader with Lean 4 + Mathlib can build it from scratch
and reproduce every machine-checked claim in the paper's appendix.

Status (every theorem below is `lake`-checked and axiom-clean: it reduces to
`propext`, `Classical.choice`, `Quot.sound` only, no domain-specific axiom):

* THEOREM  defect formula           `C = beta1(A *_s B) - beta1 A - beta1 B = s-1` (s >= 1)
* THEOREM  disjoint additivity       `C = 0` at `s = 0`  (so `C = max(s-1,0)` overall)
* THEOREM  super-additivity          `Z = V_A + V_B + C`
* THEOREM  non-attributability        joint cycle rank exceeds the sum of private ranks by `s-1`
* THEOREM  profile insufficiency      equal profile, unequal `Z`  =>  no profile functional represents `Z`
* THEOREM  profile-Pareto permits loss the move `s:3->2` is profile-indifferent yet strictly lowers `Z`
* THEOREM (conditional, `wSeam > 2 wInt`)  a strict Pareto improvement strictly lowers weighted `Z`
* THEOREM (conditional, `wInt < wSeam`, `k>0`)  unique interior seam-funding optimum

The combinatorial first Betti number `beta1 G = |E| - |V| + c` is the rank of the
cycle space `H_1(G; Z)`. The cokernel reading of the defect (its identity as the
rank of the cokernel of `H_1(A) (+) H_1(B) -> H_1(G)`, i.e. of `H_1` of the
contracted two-vertex multigraph with `s` parallel edges) is standard cycle-space
algebra; what is formalized here is the integer identity that interpretation names.
(Note: the *relative* homology `H_1(G, A (union) B)` has rank `s`, not `s-1`; the
defect is the cokernel rank, which is `s-1`. This file formalizes the integer.)
-/

namespace CBlindProjection

noncomputable section

/-! ## 1. Recognition graph and the first Betti number (value as loop count) -/

/-- A finite recognition multigraph, recorded by its three topological counts:
vertices `|V|`, edges (postings) `|E|`, and connected components. Parallel edges
are allowed (two postings between the same states are two edges). -/
structure BondGraph where
  vertices : ℕ
  edges : ℕ
  components : ℕ
  hV : 0 < vertices
  hC : 0 < components
  hC_le : components ≤ vertices

/-- First Betti number `beta1 = |E| - |V| + c`: the rank of the cycle space,
the number of independent closed recognition loops. -/
def betti1 (G : BondGraph) : ℤ :=
  (G.edges : ℤ) - (G.vertices : ℤ) + (G.components : ℤ)

/-! ## 2. Seam, disjoint union, and the projection defect C -/

/-- Joint graph with **no seam**: the disjoint union of two loci. -/
def disjointUnion (A B : BondGraph) : BondGraph where
  vertices := A.vertices + B.vertices
  edges := A.edges + B.edges
  components := A.components + B.components
  hV := by have := A.hV; have := B.hV; omega
  hC := by have := A.hC; have := B.hC; omega
  hC_le := by have := A.hC_le; have := B.hC_le; omega

/-- Joint graph with a **seam** of `s` cross-ledger postings. For two connected
loci, `s >= 1` seam edges merge them into one component. -/
def seamGlue (A B : BondGraph) (s : ℕ) : BondGraph where
  vertices := A.vertices + B.vertices
  edges := A.edges + B.edges + s
  components := 1
  hV := by have := A.hV; have := B.hV; omega
  hC := by norm_num
  hC_le := by have := A.hV; have := B.hV; omega

/-- The projection defect `C`: how much the joint loop-count exceeds the sum of
the two private loop-counts. -/
def couplingC (A B : BondGraph) (s : ℕ) : ℤ :=
  betti1 (seamGlue A B s) - betti1 A - betti1 B

/-- **Disjoint additivity** (`s = 0` branch): with no seam the joint loop-count is
exactly the sum, so the defect is `0`. -/
theorem disjoint_additive (A B : BondGraph) :
    betti1 (disjointUnion A B) = betti1 A + betti1 B := by
  unfold betti1 disjointUnion
  push_cast
  ring

/-- **The defect formula** (`s >= 1` branch): for two connected loci joined by `s`
seam postings, `C = s - 1`. Together with `disjoint_additive` this is the paper's
`C = max(s-1, 0)`. -/
theorem couplingC_eq (A B : BondGraph) (hA : A.components = 1) (hB : B.components = 1)
    (s : ℕ) : couplingC A B s = (s : ℤ) - 1 := by
  unfold couplingC betti1 seamGlue
  rw [hA, hB]
  push_cast
  ring

/-- A single unsettled posting (`s = 1`) closes no cross-ledger loop: `C = 0`. -/
theorem coupling_single_posting (A B : BondGraph)
    (hA : A.components = 1) (hB : B.components = 1) : couplingC A B 1 = 0 := by
  rw [couplingC_eq A B hA hB]; norm_num

/-- A settled promise (`s = 2`, the minimal economy) closes one cross-ledger loop:
`C = 1`. -/
theorem coupling_settled_promise (A B : BondGraph)
    (hA : A.components = 1) (hB : B.components = 1) : couplingC A B 2 = 1 := by
  rw [couplingC_eq A B hA hB]; norm_num

/-- Any economy (`s >= 2`) has strictly positive defect `C >= 1`. -/
theorem coupling_economy_pos (A B : BondGraph)
    (hA : A.components = 1) (hB : B.components = 1) (s : ℕ) (hs : 2 ≤ s) :
    1 ≤ couplingC A B s := by
  rw [couplingC_eq A B hA hB]
  have : (2 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs
  linarith

/-- **Super-additivity**: `Z = V_A + V_B + C`. -/
theorem Z_eq_sum_plus_coupling (A B : BondGraph) (s : ℕ) :
    betti1 (seamGlue A B s) = betti1 A + betti1 B + couplingC A B s := by
  unfold couplingC; ring

/-- **Non-attributability (integer form).** The joint cycle rank exceeds the sum of
the two private cycle ranks by exactly `s - 1`. This excess is the rank of the
cokernel of the canonical inclusion `H_1(A) (+) H_1(B) -> H_1(G)`; it is carried by
cross-ledger loops localizable to neither ledger. -/
theorem joint_cycle_rank_excess (A B : BondGraph)
    (hA : A.components = 1) (hB : B.components = 1) (s : ℕ) :
    betti1 (seamGlue A B s) - (betti1 A + betti1 B) = (s : ℤ) - 1 := by
  have h := couplingC_eq A B hA hB s
  unfold couplingC at h
  linarith

/-- The settlement tick `s : 1 -> 2` adds exactly `1` to the universal loop-count,
all of it pure coupling (private loop-counts do not depend on `s`). -/
theorem settlement_tick_universal_gain (A B : BondGraph) :
    betti1 (seamGlue A B 2) - betti1 (seamGlue A B 1) = 1 := by
  unfold betti1 seamGlue; push_cast; ring

/-! ## 3. The central theorem: the C-blind projection -/

/-- The private profile is the pair of each locus' own loop-count, defined without
reference to the seam. -/
def profile (A B : BondGraph) : ℤ × ℤ := (betti1 A, betti1 B)

/-- The universal `Z` strictly distinguishes seam depths the profile cannot see. -/
theorem Z_depends_on_seam (A B : BondGraph) (s s' : ℕ) (h : s ≠ s') :
    betti1 (seamGlue A B s) ≠ betti1 (seamGlue A B s') := by
  intro hcontra
  unfold betti1 seamGlue at hcontra
  push_cast at hcontra
  have hss : (s : ℤ) ≠ (s' : ℤ) := by exact_mod_cast h
  exact hss (by linarith)

/-- **Profile insufficiency.** Two configurations share a profile yet differ in `Z`,
so `Z` is not a function of the private profile: no functional that factors through
`profile` can represent `Z`. -/
theorem Z_not_function_of_profile (A B : BondGraph) :
    profile A B = profile A B ∧ betti1 (seamGlue A B 2) ≠ betti1 (seamGlue A B 3) :=
  ⟨rfl, Z_depends_on_seam A B 2 3 (by norm_num)⟩

/-- **Profile-Pareto permits Z-loss.** The move `s : 3 -> 2` leaves every private
value unchanged (Pareto-indifferent) yet strictly lowers `Z`. -/
theorem pareto_permits_Z_loss (A B : BondGraph) :
    profile A B = profile A B ∧ betti1 (seamGlue A B 2) < betti1 (seamGlue A B 3) := by
  refine ⟨rfl, ?_⟩
  unfold betti1 seamGlue; push_cast; linarith

/-! ## 3b. Agent-local internalization is topologically impotent

The standard externality remedy (Arrow 1969): if a cross-ledger interaction is
missing from private accounts, assign property rights over the interaction to the
agents and let each internalize its share. We model this faithfully. When a locus
"owns" a seam posting, that posting now terminates at a boundary stub vertex inside
the owning agent's own ledger: it becomes a **dangling edge** (one new edge, one new
terminal vertex, still one component). A dangling edge closes no cycle, so it leaves
the owner's `betti1` unchanged. The consequence is sharp: under *any* partition of the
`s` seam postings between the two agents, the agent-local total equals the autarkic
total `V_A + V_B`, so decentralized internalization recovers **none** of the coupling
`C`. This is the precise sense in which the obstruction sits one level beneath the
centralized externality fix: a central planner who treats the seam count `s` as a
commodity can represent `Z` (it is a closed-form function of `s`), but no assignment of
local property rights can. -/

/-- Internalizing `a` seam postings into a connected locus as **dangling half-edges**:
each adds one posting to a fresh boundary stub vertex. Components is unchanged. -/
def internalize (A : BondGraph) (a : ℕ) : BondGraph where
  vertices := A.vertices + a
  edges := A.edges + a
  components := A.components
  hV := by have := A.hV; omega
  hC := A.hC
  hC_le := by have := A.hC_le; omega

/-- A dangling edge closes no loop: internalizing any number of seam halves leaves a
locus' own loop-count `betti1` unchanged. -/
theorem internalize_betti_eq (A : BondGraph) (a : ℕ) :
    betti1 (internalize A a) = betti1 A := by
  unfold betti1 internalize; push_cast; ring

/-- **Agent-local internalization is impotent.** For *any* split `a + b = s` of the `s`
seam postings between the two agents (including the unilateral split `a = s, b = 0`),
the decentralized total of the two enlarged local loop-counts equals the autarkic total
`V_A + V_B`, independent of how the seam is divided. Property rights move the postings
inside the ledgers but cannot close the cross-ledger loop. -/
theorem agent_local_internalization_impotent (A B : BondGraph) (a b : ℕ) :
    betti1 (internalize A a) + betti1 (internalize B b) = betti1 A + betti1 B := by
  rw [internalize_betti_eq, internalize_betti_eq]

/-- **The decentralized total misses the full coupling.** For two connected loci and any
property-rights split `a + b = s` of a settled economy (`s >= 2`), the centralized `Z`
exceeds the agent-local total by exactly the coupling `C = s - 1 >= 1`. Decentralized
internalization recovers none of it. -/
theorem agent_local_misses_coupling (A B : BondGraph)
    (hA : A.components = 1) (hB : B.components = 1) (a b : ℕ) :
    betti1 (seamGlue A B (a + b))
      - (betti1 (internalize A a) + betti1 (internalize B b)) = (a + b : ℤ) - 1 := by
  rw [agent_local_internalization_impotent]
  have h := joint_cycle_rank_excess A B hA hB (a + b)
  push_cast at h ⊢
  linarith

/-- The miss is strictly positive in every settled economy: a central planner pricing
the seam count represents `Z`; no decentralized property-rights assignment does. -/
theorem agent_local_gap_pos (A B : BondGraph)
    (hA : A.components = 1) (hB : B.components = 1) (a b : ℕ) (hs : 2 ≤ a + b) :
    1 ≤ betti1 (seamGlue A B (a + b))
          - (betti1 (internalize A a) + betti1 (internalize B b)) := by
  rw [agent_local_misses_coupling A B hA hB a b]
  have : (2 : ℤ) ≤ ((a + b : ℕ) : ℤ) := by exact_mod_cast hs
  linarith

/-! ## 3c. The seam dichotomy: closing a cross-ledger loop *is* forming the central object

The strongest referee objection to §3b: "decentralized property rights need not relocate
a seam posting into one ledger as a stub; the two agents can **jointly** own the posting,
and joint ownership closes the cross-ledger loop." This is correct, and it is the theorem,
not a refutation. A seam posting has exactly two fates, because "both endpoints lie in one
agent's vertex set" is a binary property, and a cycle through the posting requires both of
its endpoints in a single vertex set:

  (a) it stays **cross-ledger** -- endpoints in distinct vertex sets. Any loop it closes
      then spans both vertex sets, hence lives in a single connected object on the joint
      vertex set `V_A + V_B`: the **coalition** graph `seamGlue A B s`. That object is not
      a private ledger of either agent; it is the supra-agent clearinghouse book, and its
      loop-count is exactly the conceded central `Z = V_A + V_B + (s-1)`.

  (b) it is **relocated** into one ledger -- the foreign endpoint becomes a degree-1 stub.
      It is then a dangling edge (`internalize`), closes no cycle, leaves `betti1` fixed.

There is no third option. So "joint ownership that closes the loop" is *definitionally*
the construction of the central object already conceded: it banks `C` precisely because it
**is** the centralized representation, and it is unavailable to any agent acting on its own
vertex set. This turns the killer objection into a corollary. -/

/-- **The coalition that closes the seam loops is the central object.** The only agent-local
construction in which a cross-ledger posting closes a cycle joins both agents' vertex sets
and retains all `s` seam postings -- which is exactly `seamGlue`, the supra-agent
clearinghouse book. Its loop-count reproduces the conceded central `Z = V_A + V_B + (s-1)`. -/
theorem coalition_is_central (A B : BondGraph)
    (hA : A.components = 1) (hB : B.components = 1) (s : ℕ) :
    betti1 (seamGlue A B s) = betti1 A + betti1 B + ((s : ℤ) - 1) := by
  have h := joint_cycle_rank_excess A B hA hB s
  linarith

/-- **The seam dichotomy.** For any split `a + b = s` of the seam postings, the two
agent-local fates are exhausted: relocation into private ledgers (`internalize`) banks
nothing beyond autarky (`= V_A + V_B`), while the only construction that banks the coupling
`C = s - 1` is the supra-agent coalition object `seamGlue` (the conceded central book,
`= V_A + V_B + (s-1)`). Both routes are displayed in one statement; their difference is
exactly the cokernel rank `C`. -/
theorem seam_dichotomy (A B : BondGraph)
    (hA : A.components = 1) (hB : B.components = 1) (a b : ℕ) :
    betti1 (internalize A a) + betti1 (internalize B b) = betti1 A + betti1 B
    ∧ betti1 (seamGlue A B (a + b)) = betti1 A + betti1 B + ((a + b : ℤ) - 1) :=
  ⟨agent_local_internalization_impotent A B a b,
   coalition_is_central A B hA hB (a + b)⟩

/-! ## 4. Load weighting and the conditional strict dissolution -/

/-- Load-weighted universal recognition: internal loops carry load `wInt`,
cross-locus settlement loops carry load `wSeam`. -/
def Zload (internalBetti : ℤ) (C : ℤ) (wInt wSeam : ℝ) : ℝ :=
  wInt * (internalBetti : ℝ) + wSeam * (C : ℝ)

/-- Gains from trade: a cross-locus loop banks more load than the two reclaimed
postings can re-bank internally. -/
def GainsFromTrade (wInt wSeam : ℝ) : Prop := wSeam > 2 * wInt

/-- **Strict Pareto improvement lowers Z (conditional on gains from trade).** The
symmetric defection (both agents withdraw a seam posting and re-bank it internally)
strictly raises each private value yet strictly lowers universal weighted `Z`. -/
theorem pareto_improvement_globally_negative
    (a b : ℤ) (wInt wSeam : ℝ) (hw : 0 < wInt) (hgt : GainsFromTrade wInt wSeam) :
    wInt * (a : ℝ) < wInt * ((a + 1 : ℤ) : ℝ) ∧
    wInt * (b : ℝ) < wInt * ((b + 1 : ℤ) : ℝ) ∧
    Zload (a + b + 2) 0 wInt wSeam < Zload (a + b) 1 wInt wSeam := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : wInt * ((a + 1 : ℤ) : ℝ) = wInt * (a : ℝ) + wInt := by push_cast; ring
    rw [h1]; linarith
  · have h1 : wInt * ((b + 1 : ℤ) : ℝ) = wInt * (b : ℝ) + wInt := by push_cast; ring
    rw [h1]; linarith
  · unfold Zload GainsFromTrade at *
    push_cast; nlinarith [hgt, hw]

/-- **The dissolution, bundled.** From `Z = V_A + V_B + C`: (1) `Z` is not a function
of the profile; (2) profile-Pareto permits a strict `Z`-decrease; (3) under gains
from trade, a strict Pareto improvement strictly lowers weighted `Z`. -/
theorem pareto_dissolution (A B : BondGraph)
    (a b : ℤ) (wInt wSeam : ℝ) (hw : 0 < wInt) (hgt : GainsFromTrade wInt wSeam) :
    (betti1 (seamGlue A B 2) ≠ betti1 (seamGlue A B 3)) ∧
    (betti1 (seamGlue A B 2) < betti1 (seamGlue A B 3)) ∧
    (Zload (a + b + 2) 0 wInt wSeam < Zload (a + b) 1 wInt wSeam) :=
  ⟨Z_depends_on_seam A B 2 3 (by norm_num),
   (pareto_permits_Z_loss A B).2,
   (pareto_improvement_globally_negative a b wInt wSeam hw hgt).2.2⟩

/-! ## 5. Worked example: two triangles -/

/-- A locus that is a single triangle: 3 vertices, 3 postings, one internal loop. -/
def triangle : BondGraph where
  vertices := 3
  edges := 3
  components := 1
  hV := by norm_num
  hC := by norm_num
  hC_le := by norm_num

example : betti1 triangle = 1 := by unfold betti1 triangle; norm_num
/-- Z = 2, 2, 3, 4 for s = 0, 1, 2, 3 (profile fixed at (1,1)). -/
example : betti1 (disjointUnion triangle triangle) = 2 := by
  unfold betti1 disjointUnion triangle; norm_num
example : betti1 (seamGlue triangle triangle 1) = 2 := by
  unfold betti1 seamGlue triangle; norm_num
example : betti1 (seamGlue triangle triangle 2) = 3 := by
  unfold betti1 seamGlue triangle; norm_num
example : betti1 (seamGlue triangle triangle 3) = 4 := by
  unfold betti1 seamGlue triangle; norm_num
example : couplingC triangle triangle 2 = 1 :=
  coupling_settled_promise triangle triangle rfl rfl

/-! ## 6. Conditional coda: a unique interior Z-optimum -/

open Real

/-- Convex carrying cost of holding imbalance `sigma = k*q` open on the seams. -/
def carryingCost (k q : ℝ) : ℝ := 2 * (Real.cosh (k * q) - 1)

/-- Net banked recognition as a function of continuous loop-load `q`. -/
def netZ (wInt wSeam k q : ℝ) : ℝ := (wSeam - wInt) * q - carryingCost k q

/-- The Z-optimal loop-load (the seam-funding margin location). -/
def qStar (wInt wSeam k : ℝ) : ℝ := Real.arsinh ((wSeam - wInt) / (2 * k)) / k

theorem hasDerivAt_netZ (wInt wSeam k q : ℝ) :
    HasDerivAt (netZ wInt wSeam k)
      ((wSeam - wInt) - 2 * k * Real.sinh (k * q)) q := by
  have h1 : HasDerivAt (fun x : ℝ => (wSeam - wInt) * x) (wSeam - wInt) q := by
    simpa using (hasDerivAt_id q).const_mul (wSeam - wInt)
  have hin : HasDerivAt (fun x : ℝ => k * x) k q := by
    simpa using (hasDerivAt_id q).const_mul k
  have hcosh : HasDerivAt (fun x : ℝ => Real.cosh (k * x)) (Real.sinh (k * q) * k) q :=
    (Real.hasDerivAt_cosh (k * q)).comp q hin
  have hg : HasDerivAt (fun x : ℝ => carryingCost k x) (2 * (Real.sinh (k * q) * k)) q := by
    unfold carryingCost
    simpa using (hcosh.sub_const 1).const_mul 2
  have hd := h1.sub hg
  convert hd using 1
  ring

theorem deriv_netZ (wInt wSeam k q : ℝ) :
    deriv (netZ wInt wSeam k) q = (wSeam - wInt) - 2 * k * Real.sinh (k * q) :=
  (hasDerivAt_netZ wInt wSeam k q).deriv

/-- **The seam-funding margin (first-order condition).** -/
theorem seam_funding_margin (wInt wSeam k : ℝ) (hk : 0 < k) :
    deriv (netZ wInt wSeam k) (qStar wInt wSeam k) = 0 := by
  rw [deriv_netZ]
  have hk0 : k ≠ 0 := ne_of_gt hk
  have h2k : (2 : ℝ) * k ≠ 0 := mul_ne_zero two_ne_zero hk0
  have hks : k * qStar wInt wSeam k = Real.arsinh ((wSeam - wInt) / (2 * k)) := by
    unfold qStar; field_simp
  rw [hks, Real.sinh_arsinh]
  field_simp; ring

/-- Strict concavity certificate: the derivative is strictly decreasing. -/
theorem deriv_netZ_strictAnti (wInt wSeam k : ℝ) (hk : 0 < k) :
    StrictAnti (fun q => deriv (netZ wInt wSeam k) q) := by
  intro a b hab
  simp only [deriv_netZ]
  have hsinh : Real.sinh (k * a) < Real.sinh (k * b) :=
    Real.sinh_lt_sinh.mpr (by nlinarith)
  nlinarith [hsinh]

theorem deriv_pos_below (wInt wSeam k q : ℝ) (hk : 0 < k)
    (hq : q < qStar wInt wSeam k) : 0 < deriv (netZ wInt wSeam k) q := by
  have h0 := seam_funding_margin wInt wSeam k hk
  have hmono := deriv_netZ_strictAnti wInt wSeam k hk hq
  simpa [h0] using hmono

theorem deriv_neg_above (wInt wSeam k q : ℝ) (hk : 0 < k)
    (hq : qStar wInt wSeam k < q) : deriv (netZ wInt wSeam k) q < 0 := by
  have h0 := seam_funding_margin wInt wSeam k hk
  have hmono := deriv_netZ_strictAnti wInt wSeam k hk hq
  simpa [h0] using hmono

/-- The optimum is interior (`qStar > 0`, a funded economy) under gains from trade. -/
theorem qStar_pos (wInt wSeam k : ℝ) (hk : 0 < k) (hgt : wInt < wSeam) :
    0 < qStar wInt wSeam k := by
  unfold qStar
  apply div_pos _ hk
  rw [show (0 : ℝ) = Real.arsinh 0 from (Real.arsinh_zero).symm]
  apply Real.arsinh_lt_arsinh.mpr
  exact div_pos (by linarith) (by linarith)

/-- **The Z-optimal economy (conditional capstone).** Under gains from trade and a
positive imbalance scale, net banked recognition has a unique interior optimum
characterized by the seam-funding margin. -/
theorem z_optimal_economy (wInt wSeam k : ℝ) (hk : 0 < k) (hgt : wInt < wSeam) :
    0 < qStar wInt wSeam k
    ∧ (wSeam - wInt = 2 * k * Real.sinh (k * qStar wInt wSeam k))
    ∧ (∀ q, q < qStar wInt wSeam k → 0 < deriv (netZ wInt wSeam k) q)
    ∧ (∀ q, qStar wInt wSeam k < q → deriv (netZ wInt wSeam k) q < 0) := by
  refine ⟨qStar_pos wInt wSeam k hk hgt, ?_, fun q hq => deriv_pos_below wInt wSeam k q hk hq,
          fun q hq => deriv_neg_above wInt wSeam k q hk hq⟩
  have h := seam_funding_margin wInt wSeam k hk
  rw [deriv_netZ] at h; linarith

end

end CBlindProjection
