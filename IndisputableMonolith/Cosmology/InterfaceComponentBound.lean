import Mathlib

/-!
# Locked domains are at most the interface plus one (any dimension)

## Status: THEOREM (0 sorry, 0 axiom beyond Mathlib's standard three).

This module closes the connected-graph fact left OPEN in
`scripts/cosmogenesis/domain_coarsen_2d.py`, `domain_coarsen_3d.py`, and their Lean bridges
`IndisputableMonolith.Cosmology.DomainCoarsening2D` / `DomainCoarsening3D`: the locked-domain
("super-region") count the engine carries is at most the number of forced distinctions
(the recognition-active interface) plus one,

  `components(monochromatic graph) <= (bichromatic edges) + 1`,

on any connected world in any dimension. In 1D this is the exact identity
`DomainCoarsening.runs_eq` (`runs = boundaries + 1`); in 2D and 3D a domain interface can be
multiply connected, so the equality becomes this inequality. It was previously only
numeric-discharged ("verified on the live field every cycle") because it needs
component-counting-under-edge-deletion, which is not in Mathlib. Here it is a Lean theorem.

The proof is dimension-free. A finite world is a finite vertex type `V`. A charge field
`c : V -> β` colours the vertices; an edge list `E : List (V × V)` is the adjacency the world
actually has (the 6-neighbour graph in 3D, 4-neighbour in 2D, the line in 1D). The monochromatic
edges (`c` equal on both ends) generate the locked domains; the bichromatic edges (`c` unequal)
are the interface. Component count is `Nat.card` of the quotient by the equivalence closure of the
edge relation, which needs only `Finite V` (no decidability of the closure, the usual obstruction).

The mechanism is the classical "deleting an edge raises the component count by at most one": adding
the bichromatic edges back to the monochromatic graph reconstructs the (connected) ambient world,
and each added edge merges at most two locked domains. Formally, `comp_le_comp_cons` is the atomic
merge bound (proved by an `Option`-valued injection that is injective away from the single class the
new edge can collapse into), `comp_le_comp_append` iterates it over the interface, and
`comp_eq_one_of_connected` supplies the connected ambient endpoint. The headline is
`mono_components_le_bichromatic_succ`.

The headline takes connectivity as a hypothesis. For the lattices the engine actually runs on, that
hypothesis is discharged here too, by a reusable criterion: `connected_of_descent` says a finite world
with a height `h : V → ℕ` that has a unique zero and a descent edge from every other cell is one
component. That is the recognition law's own pull toward the coarsest description, read as graph
connectivity. The 2D diamond (`Diamond`, the L1 ball `|x| + |y| ≤ t`, 4-neighbour) and the 3D
octahedron (`Octahedron`, `|x| + |y| + |z| ≤ t`, 6-neighbour) instantiate it with the L1 norm as
height and the origin as the unique zero, so `Diamond.mono_le_interface_succ` and
`Octahedron.mono_le_interface_succ` give `locked domains ≤ interface + 1` on the exact lattices the
engine evolves, for every radius (no fixed size, no `decide`). This closes the "wire the specific
lattice graph" step left routine in the Phase 13/14/15 docstrings.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace InterfaceComponentBound

variable {V : Type*}

/-- Base adjacency from an edge list, as ordered pairs. The equivalence closure symmetrizes, so the
orientation of each pair is irrelevant. -/
def gen (E : List (V × V)) (a b : V) : Prop := (a, b) ∈ E

/-- Connectivity closure of the edge relation: the least equivalence relation containing `gen E`.
Two vertices are related iff a path of edges joins them. -/
def clos (E : List (V × V)) : V → V → Prop := Relation.EqvGen (gen E)

theorem clos_equiv (E : List (V × V)) : Equivalence (clos E) := Relation.EqvGen.is_equivalence _

/-- The connectivity closure as a `Setoid`; its quotient is the set of locked domains. -/
def cs (E : List (V × V)) : Setoid V := ⟨clos E, clos_equiv E⟩

/-- The number of connected components (locked domains) of the graph with edge list `E`. Uses
`Nat.card`, so it is well-defined for any `Finite V` with no decidability hypothesis on the closure. -/
noncomputable def comp (E : List (V × V)) : ℕ := Nat.card (Quotient (cs E))

/-- Universal property of the equivalence closure: it is below any equivalence relation containing
the generating relation. -/
theorem eqvGen_le {r s : V → V → Prop} (hs : Equivalence s) (h : ∀ a b, r a b → s a b) :
    ∀ a b, Relation.EqvGen r a b → s a b := by
  intro a b hab
  induction hab with
  | rel x y hxy => exact h x y hxy
  | refl x => exact hs.refl x
  | symm x y _ ih => exact hs.symm ih
  | trans x y z _ _ ih1 ih2 => exact hs.trans ih1 ih2

/-- Monotonicity in the edge list: more edges can only merge domains, so the closure grows. Here,
prepending an edge keeps every prior connection. -/
theorem clos_mono_cons (a b : V) (X : List (V × V)) {u v : V} (h : clos X u v) :
    clos ((a, b) :: X) u v := by
  refine eqvGen_le (clos_equiv ((a, b) :: X)) ?_ u v h
  intro x y hxy
  exact Relation.EqvGen.rel x y (List.mem_cons_of_mem _ hxy)

/-- The merged relation: the closure of `X` with the classes of `a` and `b` lumped together. This is
exactly the closure after adding the single edge `(a, b)`. -/
def merged (a b : V) (X : List (V × V)) (u v : V) : Prop :=
  clos X u v ∨ (clos X u a ∧ clos X v b) ∨ (clos X u b ∧ clos X v a)

theorem merged_equiv (a b : V) (X : List (V × V)) : Equivalence (merged a b X) := by
  have e := clos_equiv X
  refine ⟨?_, ?_, ?_⟩
  · intro u; exact Or.inl (e.refl u)
  · intro u v h
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (e.symm h)
    · exact Or.inr (Or.inr ⟨h2, h1⟩)
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
  · intro u v w huv hvw
    rcases huv with huv | ⟨ua, vb⟩ | ⟨ub, va⟩
    · rcases hvw with hvw | ⟨va', wb'⟩ | ⟨vb', wa'⟩
      · exact Or.inl (e.trans huv hvw)
      · exact Or.inr (Or.inl ⟨e.trans huv va', wb'⟩)
      · exact Or.inr (Or.inr ⟨e.trans huv vb', wa'⟩)
    · rcases hvw with hvw | ⟨va', wb'⟩ | ⟨vb', wa'⟩
      · exact Or.inr (Or.inl ⟨ua, e.trans (e.symm hvw) vb⟩)
      · exact Or.inr (Or.inl ⟨ua, wb'⟩)
      · exact Or.inl (e.trans ua (e.symm wa'))
    · rcases hvw with hvw | ⟨va', wb'⟩ | ⟨vb', wa'⟩
      · exact Or.inr (Or.inr ⟨ub, e.trans (e.symm hvw) va⟩)
      · exact Or.inl (e.trans ub (e.symm wb'))
      · exact Or.inr (Or.inr ⟨ub, wa'⟩)

theorem gen_cons_le_merged (a b : V) (X : List (V × V)) :
    ∀ u v, gen ((a, b) :: X) u v → merged a b X u v := by
  intro u v h
  have e := clos_equiv X
  rcases List.mem_cons.1 h with hpair | hmem
  · rw [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact Or.inr (Or.inl ⟨e.refl _, e.refl _⟩)
  · exact Or.inl (Relation.EqvGen.rel u v hmem)

/-- The closure after adding edge `(a, b)` is exactly the merge of the `a`-class and the `b`-class. -/
theorem clos_cons_iff (a b : V) (X : List (V × V)) (u v : V) :
    clos ((a, b) :: X) u v ↔ merged a b X u v := by
  constructor
  · exact eqvGen_le (merged_equiv a b X) (gen_cons_le_merged a b X) u v
  · intro h
    have hab : clos ((a, b) :: X) a b := Relation.EqvGen.rel a b List.mem_cons_self
    rcases h with h | ⟨ua, vb⟩ | ⟨ub, va⟩
    · exact clos_mono_cons a b X h
    · exact (clos_equiv ((a, b) :: X)).trans (clos_mono_cons a b X ua)
        ((clos_equiv ((a, b) :: X)).trans hab
          ((clos_equiv ((a, b) :: X)).symm (clos_mono_cons a b X vb)))
    · exact (clos_equiv ((a, b) :: X)).trans (clos_mono_cons a b X ub)
        ((clos_equiv ((a, b) :: X)).trans ((clos_equiv ((a, b) :: X)).symm hab)
          ((clos_equiv ((a, b) :: X)).symm (clos_mono_cons a b X va)))

/-- The surjection from the finer (fewer edges) to the coarser (one more edge) quotient. -/
def proj (a b : V) (X : List (V × V)) : Quotient (cs X) → Quotient (cs ((a, b) :: X)) :=
  Quotient.lift (fun v => Quotient.mk (cs ((a, b) :: X)) v)
    (fun _ _ h => Quotient.sound (clos_mono_cons a b X h))

/-- A surjection that collapses at most one pair (everything maps injectively except possibly into a
single class) loses at most one element of cardinality. -/
theorem card_le_succ_of_merge {A B : Type*} [Finite B]
    (f : A → B) (β : A) (hmerge : ∀ x y, f x = f y → x = y ∨ x = β ∨ y = β) :
    Nat.card A ≤ Nat.card B + 1 := by
  classical
  have hinj : Function.Injective
      (fun x : A => if x = β then (none : Option B) else some (f x)) := by
    intro x y hxy
    dsimp only at hxy
    by_cases hx : x = β <;> by_cases hy : y = β
    · exact hx.trans hy.symm
    · rw [if_pos hx, if_neg hy] at hxy; exact absurd hxy (by simp)
    · rw [if_neg hx, if_pos hy] at hxy; exact absurd hxy (by simp)
    · rw [if_neg hx, if_neg hy] at hxy
      have hf : f x = f y := Option.some.inj hxy
      rcases hmerge x y hf with h | h | h
      · exact h
      · exact absurd h hx
      · exact absurd h hy
  have hcard := Nat.card_le_card_of_injective _ hinj
  haveI := Fintype.ofFinite B
  have hoption : Nat.card (Option B) = Nat.card B + 1 := by
    rw [← Fintype.card_eq_nat_card, ← Fintype.card_eq_nat_card, Fintype.card_option]
  omega

/-- **Atomic merge bound.** Adding one edge lowers the component count by at most one: equivalently,
the component count without the edge is at most the count with it, plus one. -/
theorem comp_le_comp_cons [Finite V] (a b : V) (X : List (V × V)) :
    comp X ≤ comp ((a, b) :: X) + 1 := by
  have hmerge : ∀ x y : Quotient (cs X),
      proj a b X x = proj a b X y → x = y ∨ x = Quotient.mk (cs X) b ∨ y = Quotient.mk (cs X) b := by
    refine Quotient.ind₂ ?_
    intro u v huv
    have hcl : clos ((a, b) :: X) u v := Quotient.exact huv
    rcases (clos_cons_iff a b X u v).1 hcl with h | ⟨ua, vb⟩ | ⟨ub, va⟩
    · exact Or.inl (Quotient.sound h)
    · exact Or.inr (Or.inr (Quotient.sound vb))
    · exact Or.inr (Or.inl (Quotient.sound ub))
  exact card_le_succ_of_merge (proj a b X) (Quotient.mk (cs X) b) hmerge

/-- The component count depends only on the edge set, not the order or multiplicity of the list. -/
theorem comp_congr {X Y : List (V × V)} (h : ∀ p, p ∈ X ↔ p ∈ Y) : comp X = comp Y := by
  have hgen : gen X = gen Y := by
    funext a b
    exact propext (h (a, b))
  have hclos : clos X = clos Y := by unfold clos; rw [hgen]
  have hcs : cs X = cs Y := by
    apply Setoid.ext
    intro a b
    change clos X a b ↔ clos Y a b
    rw [hclos]
  unfold comp; rw [hcs]

/-- **Iterated merge bound.** Adding a list `F` of edges lowers the component count by at most
`F.length`. -/
theorem comp_le_comp_append [Finite V] (X F : List (V × V)) :
    comp X ≤ comp (X ++ F) + F.length := by
  induction F with
  | nil => simp
  | cons f F' ih =>
    obtain ⟨a, b⟩ := f
    have hset : ∀ p, p ∈ (a, b) :: (X ++ F') ↔ p ∈ X ++ (a, b) :: F' := by
      intro p
      simp only [List.mem_cons, List.mem_append]
      tauto
    have hstep : comp (X ++ F') ≤ comp (X ++ (a, b) :: F') + 1 := by
      have := comp_le_comp_cons a b (X ++ F')
      rwa [comp_congr hset] at this
    calc comp X ≤ comp (X ++ F') + F'.length := ih
      _ ≤ (comp (X ++ (a, b) :: F') + 1) + F'.length := by omega
      _ = comp (X ++ (a, b) :: F') + (F'.length + 1) := by ring
      _ = comp (X ++ (a, b) :: F') + ((a, b) :: F').length := by simp [List.length_cons]

/-- On the empty edge list every vertex is its own component, so the count is the number of cells. -/
theorem clos_nil (u v : V) : clos ([] : List (V × V)) u v ↔ u = v := by
  constructor
  · intro h
    induction h with
    | rel x y hxy => exact absurd hxy (by simp [gen])
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h; subst h; exact Relation.EqvGen.refl u

theorem comp_nil [Finite V] : comp ([] : List (V × V)) = Nat.card V := by
  have hbij : Function.Bijective (Quotient.mk (cs ([] : List (V × V)))) := by
    refine ⟨?_, Quotient.mk_surjective⟩
    intro u v h
    exact (clos_nil u v).1 (Quotient.exact h)
  unfold comp
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

/-- A connected ambient world is a single component. -/
theorem comp_eq_one_of_connected [Finite V] [Nonempty V] (E : List (V × V))
    (hconn : ∀ u v : V, clos E u v) : comp E = 1 := by
  haveI : Subsingleton (Quotient (cs E)) :=
    ⟨Quotient.ind₂ fun u v => Quotient.sound (hconn u v)⟩
  haveI : Nonempty (Quotient (cs E)) := ⟨Quotient.mk (cs E) (Classical.arbitrary V)⟩
  unfold comp
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, inferInstance⟩

/-- **Locked domains are at most the interface plus one.** For a connected finite world with edge
list `E` and charge `c`, the number of monochromatic connected components (the locked domains the
engine carries) is at most the number of bichromatic edges (the recognition-active interface) plus
one. This is the dimension-free form of the 1D identity `runs = boundaries + 1`. -/
theorem mono_components_le_bichromatic_succ {β : Type*} [Finite V] [Nonempty V] [DecidableEq β]
    (E : List (V × V)) (c : V → β)
    (hconn : ∀ u v : V, clos E u v) :
    comp (E.filter (fun p => decide (c p.1 = c p.2)))
      ≤ (E.filter (fun p => decide (c p.1 ≠ c p.2))).length + 1 := by
  set mono := E.filter (fun p => decide (c p.1 = c p.2)) with hmono
  set bi := E.filter (fun p => decide (c p.1 ≠ c p.2)) with hbi
  have hsplit : ∀ p, p ∈ mono ++ bi ↔ p ∈ E := by
    intro p
    simp only [hmono, hbi, List.mem_append, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      by_cases hc : c p.1 = c p.2
      · exact Or.inl ⟨hp, hc⟩
      · exact Or.inr ⟨hp, hc⟩
  have h1 : comp mono ≤ comp (mono ++ bi) + bi.length := comp_le_comp_append mono bi
  have h2 : comp (mono ++ bi) = comp E := comp_congr hsplit
  have h3 : comp E = 1 := comp_eq_one_of_connected E hconn
  rw [h2, h3] at h1
  omega

/-! ### A reusable connectivity criterion: descent toward a root

The headline needs a connected ambient world (`hconn`). For the lattices the engine actually runs on
(the growing 2D diamond and the 3D octahedron, both L1 balls) connectivity has one cause: from any
cell off the centre, a single step toward the centre is a lattice edge to a strictly-lower cell, so
every cell reaches the centre. This is the recognition law's own pull toward the coarsest description,
read as a graph statement. We package it once, dimension-free, as a potential-descent criterion, then
instantiate it on the concrete lattices below. -/

/-- If a height `h : V → ℕ` has a unique zero `root`, and every cell of positive height has a lattice
edge to a strictly-lower cell, then every cell is connected to `root`. The proof is strong induction
on `h v`: a zero-height cell is the root; a positive-height cell steps down an edge to a cell the
induction hypothesis already connects to the root. -/
theorem clos_root_of_descent [Finite V] (E : List (V × V)) (h : V → ℕ) (root : V)
    (hzero : ∀ v, h v = 0 → v = root)
    (hdesc : ∀ v, h v ≠ 0 → ∃ u, ((v, u) ∈ E ∨ (u, v) ∈ E) ∧ h u < h v) :
    ∀ v, clos E v root := by
  have e := clos_equiv E
  have H : ∀ n, ∀ v, h v = n → clos E v root := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv
      rcases Nat.eq_zero_or_pos (h v) with h0 | hpos
      · rw [hzero v h0]; exact e.refl root
      · have hvne : h v ≠ 0 := by omega
        obtain ⟨u, hedge, hlt⟩ := hdesc v hvne
        have hvu : clos E v u := by
          rcases hedge with he | he
          · exact Relation.EqvGen.rel v u he
          · exact e.symm (Relation.EqvGen.rel u v he)
        have hur : clos E u root := ih (h u) (by omega) u rfl
        exact e.trans hvu hur
  intro v
  exact H (h v) v rfl

/-- **Descent connectivity.** Under the same hypotheses the whole world is one component: any two
cells are connected through the root. -/
theorem connected_of_descent [Finite V] (E : List (V × V)) (h : V → ℕ) (root : V)
    (hzero : ∀ v, h v = 0 → v = root)
    (hdesc : ∀ v, h v ≠ 0 → ∃ u, ((v, u) ∈ E ∨ (u, v) ∈ E) ∧ h u < h v) :
    ∀ u v, clos E u v := by
  have e := clos_equiv E
  intro u v
  exact e.trans (clos_root_of_descent E h root hzero hdesc u)
    (e.symm (clos_root_of_descent E h root hzero hdesc v))

/-- **Interface bound from a descent function.** Combining the descent criterion with the headline:
any finite world that admits a height with a unique zero and an edge of descent from every other cell
satisfies `locked domains ≤ interface + 1`. This is the form instantiated on the diamond and the
octahedron below: the lattice supplies `E`, the L1 norm supplies `h`, the centre supplies `root`. -/
theorem mono_le_interface_of_descent {β : Type*} [Finite V] [Nonempty V] [DecidableEq β]
    (E : List (V × V)) (c : V → β) (h : V → ℕ) (root : V)
    (hzero : ∀ v, h v = 0 → v = root)
    (hdesc : ∀ v, h v ≠ 0 → ∃ u, ((v, u) ∈ E ∨ (u, v) ∈ E) ∧ h u < h v) :
    comp (E.filter (fun p => decide (c p.1 = c p.2)))
      ≤ (E.filter (fun p => decide (c p.1 ≠ c p.2))).length + 1 :=
  mono_components_le_bichromatic_succ E c (connected_of_descent E h root hzero hdesc)

/-! ### Concrete certificate

Two cells of opposite charge joined by one edge: two locked domains, exactly one interface edge plus
one. This pins the bound tight and confirms the theorem is not vacuous. -/

theorem twoCell_connected : ∀ u v : Fin 2, clos [((0 : Fin 2), (1 : Fin 2))] u v := by
  have e := clos_equiv [((0 : Fin 2), (1 : Fin 2))]
  have h01 : clos [((0 : Fin 2), (1 : Fin 2))] 0 1 := Relation.EqvGen.rel 0 1 (by simp [gen])
  have h : ∀ u : Fin 2, clos [((0 : Fin 2), (1 : Fin 2))] u 0 := by
    intro u
    fin_cases u
    · exact e.refl 0
    · exact e.symm h01
  intro u v
  fin_cases v
  · exact h u
  · exact e.trans (h u) h01

/-- The two-cell world has exactly two locked domains (its empty monochromatic graph), pinned by
`comp_nil`. -/
theorem twoCell_comp_nil : comp ([] : List (Fin 2 × Fin 2)) = 2 := by
  rw [comp_nil]; simp [Nat.card_eq_fintype_card]

/-- The interface bound applied to the two opposite-charge cells: two locked domains, one interface
edge. The bound is tight (`2 ≤ 1 + 1`). -/
theorem twoCell_interface_bound :
    comp (([((0 : Fin 2), (1 : Fin 2))]).filter (fun p => decide ((id p.1) = (id p.2))))
      ≤ (([((0 : Fin 2), (1 : Fin 2))]).filter (fun p => decide ((id p.1) ≠ (id p.2)))).length + 1 :=
  mono_components_le_bichromatic_succ [((0 : Fin 2), (1 : Fin 2))] id twoCell_connected

/-! ### The engine's actual lattices: the 2D diamond and the 3D octahedron

The coarsening engine runs on a growing 2D diamond (`scripts/cosmogenesis/domain_coarsen_2d.py`: the
L1 ball `|x| + |y| ≤ t`, 4-neighbour adjacency) and a growing 3D octahedron
(`domain_coarsen_3d.py`: `|x| + |y| + |z| ≤ t`, 6-neighbour adjacency). Both are connected at every
radius for the same reason, supplied once by the descent criterion: the L1 norm is a height with a
unique zero at the origin, and from any other cell a single step toward the origin is a lattice edge
to a strictly-lower cell. So the interface bound holds on the actual structures the simulation
evolves, for every radius, as a THEOREM (no fixed size, no `decide`). This closes the "wire the
specific lattice graph" step left routine-but-open in Phases 13/14/15. -/

namespace Diamond

/-- The 2D diamond of radius `t`: the L1 ball `|x| + |y| ≤ t` as a finite set of lattice points.
The bounding box makes it a `Finset`; the L1 filter carves out the diamond. -/
def ball (t : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(t : ℤ), -(t : ℤ)) ((t : ℤ), (t : ℤ))).filter
    (fun p => p.1.natAbs + p.2.natAbs ≤ t)

theorem mem_ball_iff (t : ℕ) (x y : ℤ) : (x, y) ∈ ball t ↔ x.natAbs + y.natAbs ≤ t := by
  unfold ball
  simp only [Finset.mem_filter, Finset.mem_Icc, Prod.mk_le_mk]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, h⟩

/-- Vertices of the diamond: lattice points in the ball. The `Finset` coercion provides `Fintype`
and `DecidableEq` automatically. -/
abbrev Vtx (t : ℕ) := {p : ℤ × ℤ // p ∈ ball t}

/-- L1 height of a diamond vertex (its graph-distance potential toward the centre). -/
def height (t : ℕ) (v : Vtx t) : ℕ := v.val.1.natAbs + v.val.2.natAbs

/-- The centre of the diamond is a vertex (the origin lies in every ball). -/
def center (t : ℕ) : Vtx t := ⟨(0, 0), by rw [mem_ball_iff]; omega⟩

instance (t : ℕ) : Nonempty (Vtx t) := ⟨center t⟩

/-- 4-neighbour adjacency: L1 distance exactly one. -/
def adj (p q : ℤ × ℤ) : Prop := (p.1 - q.1).natAbs + (p.2 - q.2).natAbs = 1

instance : DecidableRel adj := fun p q => by unfold adj; infer_instance

/-- The 4-neighbour edge list of the diamond: every adjacent ordered pair of vertices. -/
noncomputable def edges (t : ℕ) : List (Vtx t × Vtx t) :=
  (Finset.univ.filter (fun pr : Vtx t × Vtx t => adj pr.1.val pr.2.val)).toList

theorem mem_edges (t : ℕ) (a b : Vtx t) : (a, b) ∈ edges t ↔ adj a.val b.val := by
  unfold edges
  rw [Finset.mem_toList, Finset.mem_filter]
  simp [Finset.mem_univ]

/-- A zero-height diamond vertex is the centre. -/
theorem hzero (t : ℕ) : ∀ v : Vtx t, height t v = 0 → v = center t := by
  rintro ⟨⟨x, y⟩, hmem⟩ h0
  simp only [height] at h0
  apply Subtype.ext
  have hx : x = 0 := by omega
  have hy : y = 0 := by omega
  subst hx; subst hy; rfl

/-- From any off-centre diamond vertex there is a 4-neighbour edge to a strictly-lower cell: step the
larger-magnitude coordinate one unit toward the origin. -/
theorem descent (t : ℕ) :
    ∀ v : Vtx t, height t v ≠ 0 →
      ∃ u, ((v, u) ∈ edges t ∨ (u, v) ∈ edges t) ∧ height t u < height t v := by
  rintro ⟨⟨x, y⟩, hmem⟩ hv
  simp only [height] at hv
  rw [mem_ball_iff] at hmem
  rcases lt_trichotomy x 0 with hx | hx | hx
  · refine ⟨⟨(x + 1, y), ?_⟩, Or.inl ?_, ?_⟩
    · rw [mem_ball_iff]; omega
    · rw [mem_edges]; unfold adj; dsimp only; omega
    · simp only [height]; omega
  · subst hx
    rcases lt_trichotomy y 0 with hy | hy | hy
    · refine ⟨⟨(0, y + 1), ?_⟩, Or.inl ?_, ?_⟩
      · rw [mem_ball_iff]; omega
      · rw [mem_edges]; unfold adj; dsimp only; omega
      · simp only [height]; omega
    · exfalso; omega
    · refine ⟨⟨(0, y - 1), ?_⟩, Or.inl ?_, ?_⟩
      · rw [mem_ball_iff]; omega
      · rw [mem_edges]; unfold adj; dsimp only; omega
      · simp only [height]; omega
  · refine ⟨⟨(x - 1, y), ?_⟩, Or.inl ?_, ?_⟩
    · rw [mem_ball_iff]; omega
    · rw [mem_edges]; unfold adj; dsimp only; omega
    · simp only [height]; omega

/-- **The interface bound on the 2D diamond, every radius.** For any charge field `c` on the diamond
of radius `t`, the number of locked (monochromatic) 4-connected domains is at most the number of
bichromatic interface edges plus one. THEOREM for all radii, on the exact lattice the 2D engine runs
on. -/
theorem mono_le_interface_succ {β : Type*} [DecidableEq β] (t : ℕ) (c : Vtx t → β) :
    comp ((edges t).filter (fun p => decide (c p.1 = c p.2)))
      ≤ ((edges t).filter (fun p => decide (c p.1 ≠ c p.2))).length + 1 :=
  mono_le_interface_of_descent (edges t) c (height t) (center t) (hzero t) (descent t)

end Diamond

namespace Octahedron

/-- The 3D octahedron of radius `t`: the L1 ball `|x| + |y| + |z| ≤ t` as a finite set of points. -/
def ball (t : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(t : ℤ), -(t : ℤ), -(t : ℤ)) ((t : ℤ), (t : ℤ), (t : ℤ))).filter
    (fun p => p.1.natAbs + p.2.1.natAbs + p.2.2.natAbs ≤ t)

theorem mem_ball_iff (t : ℕ) (x y z : ℤ) :
    (x, y, z) ∈ ball t ↔ x.natAbs + y.natAbs + z.natAbs ≤ t := by
  unfold ball
  simp only [Finset.mem_filter, Finset.mem_Icc, Prod.mk_le_mk]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨⟨⟨by omega, by omega, by omega⟩, by omega, by omega, by omega⟩, h⟩

/-- Vertices of the octahedron: lattice points in the ball. -/
abbrev Vtx (t : ℕ) := {p : ℤ × ℤ × ℤ // p ∈ ball t}

/-- L1 height of an octahedron vertex. -/
def height (t : ℕ) (v : Vtx t) : ℕ := v.val.1.natAbs + v.val.2.1.natAbs + v.val.2.2.natAbs

/-- The centre of the octahedron is a vertex. -/
def center (t : ℕ) : Vtx t := ⟨(0, 0, 0), by rw [mem_ball_iff]; omega⟩

instance (t : ℕ) : Nonempty (Vtx t) := ⟨center t⟩

/-- 6-neighbour adjacency: L1 distance exactly one. -/
def adj (p q : ℤ × ℤ × ℤ) : Prop :=
  (p.1 - q.1).natAbs + (p.2.1 - q.2.1).natAbs + (p.2.2 - q.2.2).natAbs = 1

instance : DecidableRel adj := fun p q => by unfold adj; infer_instance

/-- The 6-neighbour edge list of the octahedron. -/
noncomputable def edges (t : ℕ) : List (Vtx t × Vtx t) :=
  (Finset.univ.filter (fun pr : Vtx t × Vtx t => adj pr.1.val pr.2.val)).toList

theorem mem_edges (t : ℕ) (a b : Vtx t) : (a, b) ∈ edges t ↔ adj a.val b.val := by
  unfold edges
  rw [Finset.mem_toList, Finset.mem_filter]
  simp [Finset.mem_univ]

/-- A zero-height octahedron vertex is the centre. -/
theorem hzero (t : ℕ) : ∀ v : Vtx t, height t v = 0 → v = center t := by
  rintro ⟨⟨x, y, z⟩, hmem⟩ h0
  simp only [height] at h0
  apply Subtype.ext
  have hx : x = 0 := by omega
  have hy : y = 0 := by omega
  have hz : z = 0 := by omega
  subst hx; subst hy; subst hz; rfl

/-- From any off-centre octahedron vertex there is a 6-neighbour edge to a strictly-lower cell. -/
theorem descent (t : ℕ) :
    ∀ v : Vtx t, height t v ≠ 0 →
      ∃ u, ((v, u) ∈ edges t ∨ (u, v) ∈ edges t) ∧ height t u < height t v := by
  rintro ⟨⟨x, y, z⟩, hmem⟩ hv
  simp only [height] at hv
  rw [mem_ball_iff] at hmem
  rcases lt_trichotomy x 0 with hx | hx | hx
  · refine ⟨⟨(x + 1, y, z), ?_⟩, Or.inl ?_, ?_⟩
    · rw [mem_ball_iff]; omega
    · rw [mem_edges]; unfold adj; dsimp only; omega
    · simp only [height]; omega
  · subst hx
    rcases lt_trichotomy y 0 with hy | hy | hy
    · refine ⟨⟨(0, y + 1, z), ?_⟩, Or.inl ?_, ?_⟩
      · rw [mem_ball_iff]; omega
      · rw [mem_edges]; unfold adj; dsimp only; omega
      · simp only [height]; omega
    · subst hy
      rcases lt_trichotomy z 0 with hz | hz | hz
      · refine ⟨⟨(0, 0, z + 1), ?_⟩, Or.inl ?_, ?_⟩
        · rw [mem_ball_iff]; omega
        · rw [mem_edges]; unfold adj; dsimp only; omega
        · simp only [height]; omega
      · exfalso; omega
      · refine ⟨⟨(0, 0, z - 1), ?_⟩, Or.inl ?_, ?_⟩
        · rw [mem_ball_iff]; omega
        · rw [mem_edges]; unfold adj; dsimp only; omega
        · simp only [height]; omega
    · refine ⟨⟨(0, y - 1, z), ?_⟩, Or.inl ?_, ?_⟩
      · rw [mem_ball_iff]; omega
      · rw [mem_edges]; unfold adj; dsimp only; omega
      · simp only [height]; omega
  · refine ⟨⟨(x - 1, y, z), ?_⟩, Or.inl ?_, ?_⟩
    · rw [mem_ball_iff]; omega
    · rw [mem_edges]; unfold adj; dsimp only; omega
    · simp only [height]; omega

/-- **The interface bound on the 3D octahedron, every radius.** For any charge field `c` on the
octahedron of radius `t`, the number of locked (monochromatic) 6-connected domains is at most the
number of bichromatic interface edges plus one. THEOREM for all radii, on the exact lattice the 3D
engine runs on (D = 3 is the dimension the forcing chain selects). -/
theorem mono_le_interface_succ {β : Type*} [DecidableEq β] (t : ℕ) (c : Vtx t → β) :
    comp ((edges t).filter (fun p => decide (c p.1 = c p.2)))
      ≤ ((edges t).filter (fun p => decide (c p.1 ≠ c p.2))).length + 1 :=
  mono_le_interface_of_descent (edges t) c (height t) (center t) (hzero t) (descent t)

end Octahedron

end InterfaceComponentBound
end Cosmology
end IndisputableMonolith
