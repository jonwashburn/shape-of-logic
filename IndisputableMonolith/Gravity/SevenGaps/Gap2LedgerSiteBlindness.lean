import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.MeasureSubstrateBlocker
import IndisputableMonolith.Gravity.RecognitionLedger

/-!
# Gap 2, R2: the recognition ledger's site symmetry cannot supply gauge counting

A scoped no-go for the open measure obligation. The obligation is a proof of
`GaugeCountingPrinciple` in which some recognition-substrate premise is
load-bearing. This module shows that one whole shape of candidate premise is
dead, and names what any derivation must import instead.

The shape: read the measure off the SITE SYMMETRY of a recognition ledger, that
is, off how many relabelings of the site type leave the ledger's cost unchanged.
This is the natural first move, because orbit-stabilizer already converts a
symmetry count into `1/|Aut|` and the ledger is the substrate's only carrier of
cost.

The obstruction is that two of the ledger's own axioms make it blind at the
smallest size where the target has anything to say. On a two-element site type a
recognition ledger is a symmetric matrix with zero diagonal, so it is determined
by the single number `cost 0 1`, and the transposition therefore fixes EVERY such
ledger. Meanwhile two two-vertex complexes have different automorphism counts:
the edgeless pair has `|Aut| = 2` and the single directed edge has `|Aut| = 1`,
because `Relabel.edge_comm` compares ORDERED endpoint pairs and a symmetric cost
cannot see an orientation.

So the site-symmetry count is 2 for both, while gauge counting demands masses
`1/2` and `1`. No measure that factors through the site-symmetry count can be
right.

## What this licenses, exactly

Under the premise that the candidate measure factors through the ledger's
site-symmetry count on the vertex site type, gauge counting fails. That is one
conditional and this module claims no more. It does NOT say the ledger cannot
supply the measure by some other route, and it does not touch any status flag.

What it does supply is the named import: any derivation must bring structure
that separates the edgeless pair from the single directed edge. Ledger cost on
vertex sites provably does not, so the import is either an orientation-carrying
refinement of the ledger, or sites for simplices rather than for vertices alone.

Status: THEOREM. Expected axiom footprint `[propext, Classical.choice,
Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2LedgerSiteBlindness

open PathSumMeasure
open ExactShellGaugePreflight
open MeasureSubstrateBlocker
open MeasureInvarianceNoGo
open IndisputableMonolith.Gravity.RecognitionLedger

/-! ## §1. The second witness: two vertices joined by one directed edge -/

/-- Two vertices and a single edge from vertex 0 to vertex 1. -/
abbrev twoPointOneEdge (B : ℕ) (hB : 2 ≤ B) (hB1 : 1 ≤ B) : BoundedComplex B where
  nV := 2
  nE := 1
  nT := 0
  hV := hB
  hE := hB1
  hT := Nat.zero_le B
  edgeVerts := fun _ => (0, 1)
  tetVerts := fun t => t.elim0

/-- The automorphism group of the directed edge is trivial. `edge_comm`
compares ordered endpoint pairs, so an automorphism must fix vertex 0 and
vertex 1 separately; the edge and tetrahedron index bijections are forced
because their index types have at most one element. -/
instance instSubsingletonAutOneEdge (B : ℕ) (hB : 2 ≤ B) (hB1 : 1 ≤ B) :
    Subsingleton (Aut (twoPointOneEdge B hB hB1)) := by
  constructor
  intro a b
  -- every automorphism fixes both vertices
  have key : ∀ c : Aut (twoPointOneEdge B hB hB1),
      c.vEquiv = Equiv.refl (Fin 2) := by
    intro c
    have h := c.edge_comm 0
    simp only [Prod.map] at h
    have h0 : c.vEquiv 0 = 0 := (Prod.mk.injEq _ _ _ _).mp h.symm |>.1
    have h1 : c.vEquiv 1 = 1 := (Prod.mk.injEq _ _ _ _).mp h.symm |>.2
    refine Equiv.ext fun x => ?_
    fin_cases x
    · simpa using h0
    · simpa using h1
  refine Relabel.ext (by rw [key a, key b]) ?_ ?_
  · exact Equiv.ext fun x => Subsingleton.elim _ _
  · exact Equiv.ext fun x => x.elim0

/-- **THEOREM.** `|Aut(directed edge on two vertices)| = 1`. -/
theorem autCard_twoPointOneEdge (B : ℕ) (hB : 2 ≤ B) (hB1 : 1 ≤ B) :
    Nat.card (Aut (twoPointOneEdge B hB hB1)) = 1 :=
  Nat.card_unique

/-- **THEOREM.** The symmetry-factor measure of the directed edge is 1. -/
theorem mu_twoPointOneEdge (B : ℕ) (hB : 2 ≤ B) (hB1 : 1 ≤ B) :
    mu (twoPointOneEdge B hB hB1) = 1 := by
  unfold mu
  rw [autCard_twoPointOneEdge]
  norm_num

/-! ## §2. Ledger site symmetry, and its blindness at two sites -/

/-- The site-symmetry count of a recognition ledger: how many relabelings of
the site type leave the cost function unchanged. This is the ledger-side
quantity a derivation would feed to orbit-stabilizer. Its definition mentions
no automorphism, no orbit count and no gauge volume. -/
noncomputable def siteSymCard {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (L : RecognitionLedger Λ) : ℕ :=
  Nat.card {σ : Equiv.Perm Λ // ∀ i j, L.cost (σ i) (σ j) = L.cost i j}

/-- On two sites there is only one off-diagonal cost. Zero diagonal and
symmetry of cost together leave a recognition ledger on `Fin 2` with exactly
one degree of freedom, and this lemma is that fact in usable form. -/
theorem cost_offDiag_fin2 (L : RecognitionLedger (Fin 2)) :
    ∀ a b : Fin 2, a ≠ b → L.cost a b = L.cost 0 1 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [L.symmetric]

/-- **THEOREM (blindness at two sites).** EVERY permutation of a two-element
site type is a site symmetry of EVERY recognition ledger on it. A permutation
either fixes a pair of sites, where zero diagonal settles it, or exchanges
them, where symmetry of cost settles it. So no ledger on two sites can
distinguish its two sites. -/
theorem every_perm_is_siteSym (L : RecognitionLedger (Fin 2))
    (σ : Equiv.Perm (Fin 2)) (i j : Fin 2) :
    L.cost (σ i) (σ j) = L.cost i j := by
  by_cases hij : i = j
  · subst hij
    rw [L.diagonal_zero, L.diagonal_zero]
  · rw [cost_offDiag_fin2 L _ _ (fun h => hij (σ.injective h)),
      cost_offDiag_fin2 L _ _ hij]

/-- **THEOREM.** The site-symmetry group at two sites is the whole permutation
group, so the site-symmetry count is 2 for every recognition ledger. -/
theorem siteSymCard_fin2 (L : RecognitionLedger (Fin 2)) : siteSymCard L = 2 := by
  have huniv : {σ : Equiv.Perm (Fin 2) //
      ∀ i j, L.cost (σ i) (σ j) = L.cost i j} ≃ Equiv.Perm (Fin 2) :=
    { toFun := fun s => s.val
      invFun := fun σ => ⟨σ, every_perm_is_siteSym L σ⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  rw [siteSymCard, Nat.card_congr huniv, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  norm_num [Nat.factorial]

/-! ## §3. The no-go -/

/-- **HEADLINE (KILL + WITNESS).** No candidate measure that factors through
the ledger's site-symmetry count on the vertex site type satisfies gauge
counting.

The premise `hfactor` says only that on two-vertex complexes the measure is
some function of the site-symmetry count of the encoded ledger. The encoding
`enc` and the readout `g` are arbitrary: this kills the whole shape at once,
not one construction. -/
theorem no_siteSymmetry_measure {B : ℕ} (hB : 2 ≤ B) (hB1 : 1 ≤ B)
    (enc : BoundedComplex B → RecognitionLedger (Fin 2)) (g : ℕ → ℝ)
    (ν : TriangulationClass B → ℝ)
    (hfactor : ∀ K : BoundedComplex B, K.nV = 2 →
      ν (Quotient.mk (relabelSetoid B) K) = g (siteSymCard (enc K))) :
    ¬ GaugeCountingPrinciple ν := by
  intro hgc
  have hmu := (gaugeCountingPrinciple_iff_mu_on_representatives ν).mp hgc
  -- the edgeless pair: gauge counting demands 1/2
  have e1 : g 2 = 1 / 2 := by
    have h := hfactor (twoPointComplex B hB) rfl
    rw [siteSymCard_fin2] at h
    rw [← h, hmu, mu_twoPointComplex B hB]
  -- the directed edge: gauge counting demands 1
  have e2 : g 2 = 1 := by
    have h := hfactor (twoPointOneEdge B hB hB1) rfl
    rw [siteSymCard_fin2] at h
    rw [← h, hmu, mu_twoPointOneEdge B hB hB1]
  rw [e1] at e2
  norm_num at e2

/-- **The separation, stated without reference to any candidate measure.** The
two witnesses agree on every ledger site-symmetry count and disagree on the
symmetry-factor measure. This is what any derivation must import structure to
separate. -/
theorem witnesses_agree_on_ledger_disagree_on_measure {B : ℕ}
    (hB : 2 ≤ B) (hB1 : 1 ≤ B)
    (enc : BoundedComplex B → RecognitionLedger (Fin 2)) :
    siteSymCard (enc (twoPointComplex B hB))
        = siteSymCard (enc (twoPointOneEdge B hB hB1)) ∧
      mu (twoPointComplex B hB) ≠ mu (twoPointOneEdge B hB hB1) := by
  refine ⟨by rw [siteSymCard_fin2, siteSymCard_fin2], ?_⟩
  rw [mu_twoPointComplex B hB, mu_twoPointOneEdge B hB hB1]
  norm_num

/-! ## §4. The other route, and why it is not a derivation either

Section 3 kills measures that factor through the ledger's site-symmetry count,
which is the route by which an automorphism count naturally arises. The
remaining route is to read the measure off the ledger's cost VALUES. That route
is not blind, and it is not a derivation, for the opposite reason: the ledger
axioms place no constraint on which ledger a complex is encoded as, so the
encoding is a free parameter and whatever it is fed determines the answer.

The two theorems below make that exact. First, every non-negative number is the
off-diagonal cost of some recognition ledger on two sites, so the axioms
constrain the value not at all. Second, one fixed readout gives the correct
measure under one encoding and a wrong measure under another, so what determined
the measure was the choice of encoding and not the substrate. -/

/-- The uniform ledger on two sites with off-diagonal cost `t`. Every axiom
holds for every `t ≥ 0`: the gate `rclGate u v = 2uv + 2u + 2v` gives
`rclGate 0 t = 2t ≥ t`, so subadditivity is slack rather than binding. -/
noncomputable def uniformLedger {t : ℝ} (ht : 0 ≤ t) : RecognitionLedger (Fin 2) where
  cost := fun i j => if i = j then 0 else t
  symmetric := fun i j => by
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  diagonal_zero := fun i => by simp
  nonneg := fun i j => by by_cases h : i = j <;> simp [h, ht]
  rcl_subadditive := fun i j k => by
    unfold rclGate
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp <;> nlinarith

@[simp] theorem uniformLedger_offDiag {t : ℝ} (ht : 0 ≤ t) :
    (uniformLedger ht).cost 0 1 = t := by
  simp [uniformLedger]

/-- **THEOREM (the encoding is unconstrained).** For any assignment of
non-negative numbers to bounded complexes there is an encoding into recognition
ledgers on two sites realizing it exactly. The ledger axioms therefore say
nothing about which ledger a complex should become. -/
theorem encoding_unconstrained {B : ℕ} (f : BoundedComplex B → ℝ)
    (hf : ∀ K, 0 ≤ f K) :
    ∃ enc : BoundedComplex B → RecognitionLedger (Fin 2),
      ∀ K, (enc K).cost 0 1 = f K :=
  ⟨fun K => uniformLedger (hf K), fun K => uniformLedger_offDiag (hf K)⟩

/-- **HEADLINE (the value route is fitting, not deriving).** There is a single
readout, the identity on the off-diagonal cost, which returns exactly the
symmetry-factor measure under one encoding and returns the wrong answer under
another. So a construction of the form "encode the complex as a ledger, read the
measure off its cost" has its answer supplied by the encoding, not by the
substrate.

Combined with §3 this is the named import the open obligation needs: any
derivation must bring a canonical encoding from complexes to recognition
ledgers, forced rather than chosen, and neither the ledger axioms nor the
carrier supplies one. -/
theorem value_route_is_encoding_choice {B : ℕ} (hB : 2 ≤ B) :
    ∃ enc enc' : BoundedComplex B → RecognitionLedger (Fin 2),
      (∀ K : BoundedComplex B, (enc K).cost 0 1 = mu K) ∧
      (∀ K : BoundedComplex B, (enc' K).cost 0 1 = 0) ∧
      mu (twoPointComplex B hB) ≠ 0 := by
  refine ⟨fun K => uniformLedger (mu_pos K).le, fun _ => flatLedger (Fin 2),
    fun K => uniformLedger_offDiag (mu_pos K).le, fun _ => rfl, ?_⟩
  rw [mu_twoPointComplex B hB]
  norm_num

/-! ## §5. The general statement: on any site type the symmetry is chosen

Sections 3 and 4 are about the vertex site type, where a two-vertex complex
encodes into a ledger on two sites. The obvious escape is a richer site type,
one site per simplex rather than per vertex, which can carry an orientation that
a symmetric cost on vertex sites cannot. This section shows the escape does not
change the verdict, and it upgrades the answer from "vertex sites" to "any site
type".

The reason is that a recognition ledger's site-symmetry group is itself chosen by
the encoding. On three or more sites the axioms admit both a ledger whose site
symmetries are everything and a ledger for which a given transposition is not a
site symmetry. So the symmetry data a derivation would read is a function of the
encoding, and the ledger axioms never pick one. Whatever the site type, the
premise to import is the same: a canonical encoding, forced rather than chosen. -/

/-- The uniform ledger on three sites: cost `t` off the diagonal, valid for
every `t ≥ 0`. -/
noncomputable def uniformLedger3 {t : ℝ} (ht : 0 ≤ t) : RecognitionLedger (Fin 3) where
  cost := fun i j => if i = j then 0 else t
  symmetric := fun i j => by
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  diagonal_zero := fun i => by simp
  nonneg := fun i j => by by_cases h : i = j <;> simp [h, ht]
  rcl_subadditive := fun i j k => by
    unfold rclGate
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp <;> nlinarith

/-- Every permutation is a site symmetry of the uniform ledger: its cost
depends only on whether two sites are equal, and a permutation preserves that. -/
theorem uniform3_siteSym {t : ℝ} (ht : 0 ≤ t) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (uniformLedger3 ht).cost (σ i) (σ j) = (uniformLedger3 ht).cost i j := by
  show (if σ i = σ j then (0:ℝ) else t) = if i = j then 0 else t
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (fun he : σ i = σ j => h (σ.injective he))]

/-- Pair costs on three sites, pairwise different off the diagonal: `1`, `3/2`
and `2`. Matching on `Fin.mk` so the values reduce on literals. -/
noncomputable def dcost : Fin 3 → Fin 3 → ℝ
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨2, _⟩ => 3 / 2
  | ⟨2, _⟩, ⟨0, _⟩ => 3 / 2
  | ⟨1, _⟩, ⟨2, _⟩ => 2
  | ⟨2, _⟩, ⟨1, _⟩ => 2
  | _, _ => 0

/-- A ledger on three sites whose three pair costs are pairwise different. All
four axioms hold; RCL subadditivity is slack because the gate at two
off-diagonal arguments is at least `2 * 1 * 1 + 2 + 2 = 6`. -/
noncomputable def distinctLedger : RecognitionLedger (Fin 3) where
  cost := dcost
  symmetric := fun i j => by fin_cases i <;> fin_cases j <;> norm_num [dcost]
  diagonal_zero := fun i => by fin_cases i <;> norm_num [dcost]
  nonneg := fun i j => by fin_cases i <;> fin_cases j <;> norm_num [dcost]
  rcl_subadditive := fun i j k => by
    unfold rclGate
    fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [dcost]

/-- **THEOREM.** The transposition of sites 0 and 1 is NOT a site symmetry of
`distinctLedger`: it carries the pair cost `3/2` to the pair cost `2`. -/
theorem swap01_not_siteSym_distinct :
    ¬ (∀ i j : Fin 3, distinctLedger.cost (Equiv.swap 0 1 i) (Equiv.swap 0 1 j)
        = distinctLedger.cost i j) := by
  intro h
  have h02 := h 0 2
  rw [Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)] at h02
  norm_num [distinctLedger, dcost] at h02

/-- **HEADLINE (general form).** On a site type with three or more sites the
recognition ledger axioms admit both a ledger for which every permutation is a
site symmetry and a ledger for which a given transposition is not. The
site-symmetry group a derivation would read off the substrate is therefore
determined by the encoding and not by the axioms, on every site type, however
rich.

Together with §3 and §4 this is the answer to the open obligation's second
disjunct in its general form. The additional premise any encoding-based
derivation of the path-sum measure must import is a CANONICAL encoding from
bounded complexes to recognition ledgers, forced rather than chosen. Moving to
simplex-level sites buys the expressiveness that vertex sites provably lack, and
buys nothing at all against this. -/
theorem siteSymmetry_is_chosen_by_the_encoding :
    (∀ σ : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
      (uniformLedger3 (le_refl (0:ℝ))).cost (σ i) (σ j)
        = (uniformLedger3 (le_refl (0:ℝ))).cost i j) ∧
    ¬ (∀ i j : Fin 3, distinctLedger.cost (Equiv.swap 0 1 i) (Equiv.swap 0 1 j)
        = distinctLedger.cost i j) :=
  ⟨fun σ => uniform3_siteSym (le_refl (0:ℝ)) σ, swap01_not_siteSym_distinct⟩

#print axioms autCard_twoPointOneEdge
#print axioms siteSymCard_fin2
#print axioms no_siteSymmetry_measure
#print axioms witnesses_agree_on_ledger_disagree_on_measure
#print axioms encoding_unconstrained
#print axioms value_route_is_encoding_choice
#print axioms siteSymmetry_is_chosen_by_the_encoding

end Gap2LedgerSiteBlindness
end SevenGaps
end Gravity
end IndisputableMonolith
