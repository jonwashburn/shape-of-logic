import Mathlib

namespace IndisputableMonolith
namespace Complexity

/-- Complexity pair (functions of input size). -/
structure ComplexityPair where
  Tc : ℕ → ℕ
  Tr : ℕ → ℕ

namespace VertexCover

/-- Vertex Cover instance over `Nat` vertices. -/
structure Instance where
  vertices : List Nat
  edges    : List (Nat × Nat)
  k        : Nat
  deriving Repr

/-- A set `S` covers an edge `(u,v)` if it contains `u` or `v`. -/
def InCover (S : List Nat) (v : Nat) : Prop := v ∈ S

def EdgeCovered (S : List Nat) (e : Nat × Nat) : Prop :=
  InCover S e.fst ∨ InCover S e.snd

/-- `S` covers all edges of instance `I`. -/
def Covers (S : List Nat) (I : Instance) : Prop :=
  ∀ e, e ∈ I.edges → EdgeCovered S e

/-- There exists a vertex cover of size ≤ k. -/
def HasCover (I : Instance) : Prop :=
  ∃ S : List Nat, S.length ≤ I.k ∧ Covers S I

/-- A trivial example with no edges is always covered by the empty set. -/
@[simp] def trivialInstance : Instance := { vertices := [1], edges := [], k := 0 }

lemma trivial_hasCover : HasCover trivialInstance := by
  refine ⟨[], by decide, ?_⟩
  intro e he
  simpa using he

@[simp] lemma InCover_cons {x : Nat} {xs : List Nat} : InCover (x :: xs) x := by
  simp [InCover]

@[simp] lemma InCover_of_mem {S : List Nat} {v : Nat} (h : v ∈ S) : InCover S v := by
  simpa [InCover] using h

lemma EdgeCovered_comm (S : List Nat) (u v : Nat) :
  EdgeCovered S (u, v) ↔ EdgeCovered S (v, u) := by
  simp [EdgeCovered, Or.comm]

lemma Covers_nil_edges (S : List Nat) (I : Instance) (h_edges : I.edges = []) : Covers S I := by
  intro e he
  simpa [Covers, h_edges] using he

lemma hasCover_of_nil_edges (I : Instance) (h_edges : I.edges = []) : HasCover I := by
  refine ⟨[], by simp, ?_⟩
  intro e he
  simpa [Covers, h_edges] using he

end VertexCover

end Complexity

end IndisputableMonolith
