import Mathlib

/-!
# Periodic Freudenthal 4-Torus: the typed 4D carrier

This module builds the typed periodic Freudenthal triangulation of the
4-torus that the 4D `MetricRefinementFamily` recon
(`QG/attack_full_theory_20260729/A23_4D_recon_20260729.html`) named as the
missing object: four-coordinate periodic vertices, the fifteen
positive-displacement edge classes of the 4-cube, the Kuhn (permutation)
triangulation of the 4-cube into `4! = 24` four-simplices, a finite encoder,
a self-contained simplicial carrier with simpliciality evidence, and the
mesh scale machinery.

It is the 4D mirror of `Geometry/PeriodicFreudenthalTorus.lean` (3D). Per the
recon, it is deliberately self-contained: `PathSumMeasure.BoundedComplex` is
tetrahedron-only and cannot hold Kuhn 4-simplices (`Fin 5` corners), so this
module defines its own carrier shape `Carrier4D` and its own simplicial
predicate `IsSimplicial4D` mirroring the 3D interface. Extending
`BoundedComplex` to admit 4-simplices is a separate authorized decision and
is not taken here. No existing module is modified.

Honesty boundary:
* THEOREM: every named result below (kernel-checked, no `sorry`, no new
  axioms, no `native_decide`). Finite combinatorial checks on explicit tables
  use `decide` only.
* The Kuhn tables are explicit: corners are the partial sums of the 24
  permutations of the four axes (lexicographic order), and every edge slot is
  a comparable corner pair. The kernel re-verifies the tables through the
  endpoint-incidence theorem `localEdgeOf4_endpoints_match_kuhnVerts`.
* What is NOT here: the side schedule, Config, coarsen, decoration pullback,
  action step control, and the `MetricRefinementFamily` instance itself.
  Those are the next worker's assembly job (the 4D analog of
  `Gap2MetricRefinementFamilyInstance`); the period-doubling projection and
  its section live in `Gravity/SevenGaps/Gap2FreudenthalPeriodDoubling4D`.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Geometry
namespace PeriodicFreudenthalTorus4D

noncomputable section

/-! ## §1. One-coordinate bit arithmetic (self-contained mirror of the 3D helpers) -/

def bit : Bool → ℕ
  | false => 0
  | true => 1

def addBit {N : ℕ} [NeZero N] (i : Fin N) (b : Bool) : Fin N :=
  ⟨(i.val + bit b) % N, Nat.mod_lt _ (Nat.pos_of_neZero N)⟩

@[simp] theorem addBit_false {N : ℕ} [NeZero N] (i : Fin N) :
    addBit i false = i := by
  ext
  simp [addBit, bit, Nat.mod_eq_of_lt i.isLt]

@[simp] theorem addBit_true_eq_mk {N : ℕ} [NeZero N] (i : Fin N) :
    addBit i true =
      ⟨(i.val + 1) % N, Nat.mod_lt _ (Nat.pos_of_neZero N)⟩ := by
  rfl

@[simp] theorem addBit_false_after_true {N : ℕ} [NeZero N] (i : Fin N) :
    addBit (addBit i true) false = addBit i true := by
  simp

@[simp] theorem addBit_true_after_false {N : ℕ} [NeZero N] (i : Fin N) :
    addBit (addBit i false) true = addBit i true := by
  simp

theorem addBit_true_ne_self {N : ℕ} [NeZero N] (hN : 2 < N) (i : Fin N) :
    addBit i true ≠ i := by
  intro h
  have hval : (i.val + 1) % N = i.val := by
    simpa [addBit, bit] using congrArg Fin.val h
  have hcases : i.val + 1 < N ∨ i.val + 1 = N := by
    omega
  cases hcases with
  | inl hlt =>
      have hmod : (i.val + 1) % N = i.val + 1 := Nat.mod_eq_of_lt hlt
      omega
  | inr heq =>
      have hmod : (i.val + 1) % N = 0 := by
        rw [heq, Nat.mod_self]
      omega

theorem addBit_true_injective {N : ℕ} [NeZero N] :
    Function.Injective (fun i : Fin N => addBit i true) := by
  intro i j h
  ext
  have hval : (i.val + 1) % N = (j.val + 1) % N := by
    simpa [addBit, bit] using congrArg Fin.val h
  have hi : i.val + 1 < N ∨ i.val + 1 = N := by
    omega
  have hj : j.val + 1 < N ∨ j.val + 1 = N := by
    omega
  cases hi with
  | inl hi_lt =>
      have himod : (i.val + 1) % N = i.val + 1 := Nat.mod_eq_of_lt hi_lt
      cases hj with
      | inl hj_lt =>
          have hjmod : (j.val + 1) % N = j.val + 1 := Nat.mod_eq_of_lt hj_lt
          omega
      | inr hj_eq =>
          have hjmod : (j.val + 1) % N = 0 := by
            rw [hj_eq, Nat.mod_self]
          omega
  | inr hi_eq =>
      have himod : (i.val + 1) % N = 0 := by
        rw [hi_eq, Nat.mod_self]
      cases hj with
      | inl hj_lt =>
          have hjmod : (j.val + 1) % N = j.val + 1 := Nat.mod_eq_of_lt hj_lt
          omega
      | inr hj_eq =>
          omega

theorem addBit_injective {N : ℕ} [NeZero N] (b : Bool) :
    Function.Injective (fun i : Fin N => addBit i b) := by
  cases b
  · intro i j h
    simpa using h
  · exact addBit_true_injective

/-- If two one-step bit translations of the same coordinate agree, the bits
agree when `1 < N`. (4D copy of the 3D cancellation lemma.) -/
theorem addBit4_cancel (N : ℕ) [NeZero N] (hN : 1 < N)
    (c : Fin N) (b₁ b₂ : Bool) (h : addBit c b₁ = addBit c b₂) : b₁ = b₂ := by
  have hval : (c.val + bit b₁) % N = (c.val + bit b₂) % N := by
    simpa [addBit] using congrArg Fin.val h
  have h' : (c.val % N + bit b₁) % N = (c.val % N + bit b₂) % N := by
    simpa [Nat.add_mod] using hval
  have hc : c.val % N = c.val := Nat.mod_eq_of_lt c.isLt
  rw [hc] at h'
  cases b₁ <;> cases b₂ <;> simp [bit] at h' ⊢
  · have hcases : c.val + 1 < N ∨ c.val + 1 = N := by omega
    cases hcases with
    | inl hlt =>
        have : (c.val + 1) % N = c.val + 1 := Nat.mod_eq_of_lt hlt
        omega
    | inr heq =>
        have : (c.val + 1) % N = 0 := by rw [heq, Nat.mod_self]
        omega
  · have hcases : c.val + 1 < N ∨ c.val + 1 = N := by omega
    cases hcases with
    | inl hlt =>
        have : (c.val + 1) % N = c.val + 1 := Nat.mod_eq_of_lt hlt
        omega
    | inr heq =>
        have : (c.val + 1) % N = 0 := by rw [heq, Nat.mod_self]
        omega

private theorem two_bit_steps_ne_id (N : ℕ) [NeZero N] (hN : 2 < N)
    (x : Fin N) (b₁ b₂ : Bool) :
    addBit (addBit x b₁) b₂ = x → b₁ = false ∧ b₂ = false := by
  intro h
  cases b₁ <;> cases b₂
  · simp [addBit_false] at h ⊢
  · exact (addBit_true_ne_self hN x (by simpa [addBit_false] using h)).elim
  · exact (addBit_true_ne_self hN x (by simpa [addBit_false] using h)).elim
  · have hv : ((x.val + 1) % N + 1) % N = x.val := by
      simpa [addBit, bit] using congrArg Fin.val h
    have : x.val + 1 < N ∨ x.val + 1 = N := by omega
    cases this with
    | inl hlt =>
      rw [Nat.mod_eq_of_lt hlt] at hv
      have hv' : (x.val + 2) % N = x.val := by simpa [Nat.add_assoc] using hv
      have : x.val + 2 < N ∨ x.val + 2 = N := by omega
      cases this with
      | inl hlt2 =>
        have : x.val + 2 = x.val := by rwa [Nat.mod_eq_of_lt hlt2] at hv'
        omega
      | inr heq2 =>
        have : (x.val + 2) % N = 0 := by rw [heq2, Nat.mod_self]
        omega
    | inr heq =>
      rw [heq, Nat.mod_self] at hv
      have h1 : 1 % N = 1 := Nat.mod_eq_of_lt (lt_trans (by decide : 1 < 2) hN)
      rw [h1] at hv
      omega

/-! ## §2. Periodic 4-grid vertices -/

/-- Periodic 4-torus vertices on the side-`N` grid. -/
abbrev Vertex4 (N : ℕ) := Fin N × Fin N × Fin N × Fin N

/-- Four-axis bit translation of a periodic vertex. -/
def addBits4 {N : ℕ} [NeZero N] (v : Vertex4 N) (dx dy dz dw : Bool) : Vertex4 N :=
  (addBit v.1 dx, addBit v.2.1 dy, addBit v.2.2.1 dz, addBit v.2.2.2 dw)

theorem addBits4_injective {N : ℕ} [NeZero N] (dx dy dz dw : Bool) :
    Function.Injective (fun v : Vertex4 N => addBits4 v dx dy dz dw) := by
  intro v w h
  rcases v with ⟨vx, vy, vz, vw⟩
  rcases w with ⟨wx, wy, wz, ww⟩
  simp [addBits4] at h ⊢
  exact ⟨addBit_injective dx h.1, addBit_injective dy h.2.1,
    addBit_injective dz h.2.2.1, addBit_injective dw h.2.2.2⟩

/-- Equality of two four-axis bit translations cancels to equality of the
bits, when `1 < N`. -/
theorem addBits4_cancel_offsets (N : ℕ) [NeZero N] (hN : 1 < N)
    (cell : Vertex4 N) (dx₁ dy₁ dz₁ dw₁ dx₂ dy₂ dz₂ dw₂ : Bool)
    (h : addBits4 cell dx₁ dy₁ dz₁ dw₁ = addBits4 cell dx₂ dy₂ dz₂ dw₂) :
    dx₁ = dx₂ ∧ dy₁ = dy₂ ∧ dz₁ = dz₂ ∧ dw₁ = dw₂ :=
  ⟨addBit4_cancel N hN cell.1 dx₁ dx₂ (congrArg Prod.fst h),
    addBit4_cancel N hN cell.2.1 dy₁ dy₂
      (congrArg (fun v : Vertex4 N => v.2.1) h),
    addBit4_cancel N hN cell.2.2.1 dz₁ dz₂
      (congrArg (fun v : Vertex4 N => v.2.2.1) h),
    addBit4_cancel N hN cell.2.2.2 dw₁ dw₂
      (congrArg (fun v : Vertex4 N => v.2.2.2) h)⟩

/-! ## §3. The fifteen positive-displacement classes of the 4-cube -/

/-- Nonzero positive 4-cube displacements, ordered by the bit mask
`d.val + 1` (bit `i` of the mask is coordinate `i`). The weight spectrum is
four axis edges (classes 0, 1, 3, 7), six face diagonals (2, 4, 5, 8, 9, 11),
four space diagonals of 3-faces (6, 10, 12, 13), and one hyperbody diagonal
(14). Matches the `ReggeEdgeStencil4D` mask convention; the bit-for-bit
bridge is proved in `Gap2FreudenthalPeriodDoubling4D`. -/
def dispBits4 : Fin 15 → Bool × Bool × Bool × Bool
  | 0 => (true, false, false, false)
  | 1 => (false, true, false, false)
  | 2 => (true, true, false, false)
  | 3 => (false, false, true, false)
  | 4 => (true, false, true, false)
  | 5 => (false, true, true, false)
  | 6 => (true, true, true, false)
  | 7 => (false, false, false, true)
  | 8 => (true, false, false, true)
  | 9 => (false, true, false, true)
  | 10 => (true, true, false, true)
  | 11 => (false, false, true, true)
  | 12 => (true, false, true, true)
  | 13 => (false, true, true, true)
  | 14 => (true, true, true, true)

theorem dispBits4_ne_zero (d : Fin 15) :
    dispBits4 d ≠ (false, false, false, false) := by
  revert d
  decide

theorem dispBits4_injective : Function.Injective dispBits4 := by
  decide

/-- **Sanity (displacement classes).** The edge displacement classes are
exactly fifteen: `dispBits4` is a bijection between `Fin 15` and the nonzero
0/1 displacement vectors of the 4-cube. -/
theorem displacement_classes_are_fifteen :
    Function.Injective dispBits4 ∧
      (∀ d : Fin 15, dispBits4 d ≠ (false, false, false, false)) ∧
        (∀ b : Bool × Bool × Bool × Bool, b ≠ (false, false, false, false) →
          ∃ d : Fin 15, dispBits4 d = b) := by
  decide

/-! ## §4. Local 4-cube vertex offsets -/

/-- Local 4-cube vertex offsets, using binary cube labels (`Fin 16`, bit `i`
of the label is coordinate `i`). -/
def vertexBits4 : Fin 16 → Bool × Bool × Bool × Bool
  | 0 => (false, false, false, false)
  | 1 => (true, false, false, false)
  | 2 => (false, true, false, false)
  | 3 => (true, true, false, false)
  | 4 => (false, false, true, false)
  | 5 => (true, false, true, false)
  | 6 => (false, true, true, false)
  | 7 => (true, true, true, false)
  | 8 => (false, false, false, true)
  | 9 => (true, false, false, true)
  | 10 => (false, true, false, true)
  | 11 => (true, true, false, true)
  | 12 => (false, false, true, true)
  | 13 => (true, false, true, true)
  | 14 => (false, true, true, true)
  | ⟨_+15, _⟩ => (true, true, true, true)

theorem vertexBits4_injective : Function.Injective vertexBits4 := by
  decide

/-- Translate a periodic vertex by a local 4-cube corner offset. -/
def addVertexBits4 {N : ℕ} [NeZero N] (v : Vertex4 N) (a : Fin 16) : Vertex4 N :=
  let b := vertexBits4 a
  addBits4 v b.1 b.2.1 b.2.2.1 b.2.2.2

theorem addVertexBits4_injective {N : ℕ} [NeZero N] (a : Fin 16) :
    Function.Injective (fun v : Vertex4 N => addVertexBits4 v a) := by
  intro v w h
  unfold addVertexBits4 at h
  exact addBits4_injective _ _ _ _ h

/-! ## §5. Positive-displacement periodic 4-edges -/

/-- A positive-displacement periodic 4-edge, represented by its base vertex
and one of the fifteen positive 4-cube displacement classes. -/
structure PeriodicEdge4 (N : ℕ) [NeZero N] where
  base : Vertex4 N
  disp : Fin 15
deriving DecidableEq, Fintype

/-- Endpoints of a positive-displacement periodic 4-edge. -/
def PeriodicEdge4.endpoints {N : ℕ} [NeZero N] (e : PeriodicEdge4 N) :
    Vertex4 N × Vertex4 N :=
  let d := dispBits4 e.disp
  (e.base, addBits4 e.base d.1 d.2.1 d.2.2.1 d.2.2.2)

theorem PeriodicEdge4.endpoints_ne {N : ℕ} [NeZero N] (hN : 2 < N)
    (e : PeriodicEdge4 N) :
    e.endpoints.1 ≠ e.endpoints.2 := by
  cases e with
  | mk base disp =>
      fin_cases disp <;>
        · intro h
          simp [PeriodicEdge4.endpoints, dispBits4, addBits4] at h
          first
          | exact addBit_true_ne_self hN base.1 ((congrArg Prod.fst h).symm)
          | exact addBit_true_ne_self hN base.2.1
              ((congrArg (fun v : Vertex4 N => v.2.1) h).symm)
          | exact addBit_true_ne_self hN base.2.2.1
              ((congrArg (fun v : Vertex4 N => v.2.2.1) h).symm)
          | exact addBit_true_ne_self hN base.2.2.2
              ((congrArg (fun v : Vertex4 N => v.2.2.2) h).symm)

/-! ## §6. Cardinalities of the typed skeleton -/

/-- The periodic 4-vertex set at side `N` has `N ^ 4` elements. -/
theorem card_vertex4 (N : ℕ) : Fintype.card (Vertex4 N) = N ^ 4 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
  ring

/-- A positive-displacement periodic 4-edge is exactly a (base vertex,
displacement class) pair. -/
def periodicEdge4EquivProd (N : ℕ) [NeZero N] :
    PeriodicEdge4 N ≃ Vertex4 N × Fin 15 where
  toFun e := (e.base, e.disp)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Edge count formula.** The periodic 4-edge set at side `N` has
`15 * N ^ 4` elements. -/
theorem card_periodicEdge4 (N : ℕ) [NeZero N] :
    Fintype.card (PeriodicEdge4 N) = 15 * N ^ 4 := by
  rw [Fintype.card_congr (periodicEdge4EquivProd N), Fintype.card_prod,
    card_vertex4, Fintype.card_fin]
  ring

/- Finite types of the carrier: vertices and edges (and below, Kuhn
simplices) are finite at every side, by the derived `Fintype` instances on
`Vertex4` (a product of `Fin`) and `PeriodicEdge4` (`deriving Fintype`). -/

/-! ## §7. The Kuhn triangulation of the 4-cube (24 permutation simplices) -/

/-- The 24 Kuhn 4-simplices of the unit 4-cube as corner lists: the monotone
paths from cube vertex `0` to cube vertex `15`, one per permutation of the
four axes, in lexicographic permutation order. Corner `k` of simplex `σ` is
the partial sum of the first `k` axis steps, as a binary cube label. -/
def kuhnVerts : Fin 24 → Fin 5 → Fin 16
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 3
  | 0, 3 => 7
  | 0, 4 => 15
  | 1, 0 => 0
  | 1, 1 => 1
  | 1, 2 => 3
  | 1, 3 => 11
  | 1, 4 => 15
  | 2, 0 => 0
  | 2, 1 => 1
  | 2, 2 => 5
  | 2, 3 => 7
  | 2, 4 => 15
  | 3, 0 => 0
  | 3, 1 => 1
  | 3, 2 => 5
  | 3, 3 => 13
  | 3, 4 => 15
  | 4, 0 => 0
  | 4, 1 => 1
  | 4, 2 => 9
  | 4, 3 => 11
  | 4, 4 => 15
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 9
  | 5, 3 => 13
  | 5, 4 => 15
  | 6, 0 => 0
  | 6, 1 => 2
  | 6, 2 => 3
  | 6, 3 => 7
  | 6, 4 => 15
  | 7, 0 => 0
  | 7, 1 => 2
  | 7, 2 => 3
  | 7, 3 => 11
  | 7, 4 => 15
  | 8, 0 => 0
  | 8, 1 => 2
  | 8, 2 => 6
  | 8, 3 => 7
  | 8, 4 => 15
  | 9, 0 => 0
  | 9, 1 => 2
  | 9, 2 => 6
  | 9, 3 => 14
  | 9, 4 => 15
  | 10, 0 => 0
  | 10, 1 => 2
  | 10, 2 => 10
  | 10, 3 => 11
  | 10, 4 => 15
  | 11, 0 => 0
  | 11, 1 => 2
  | 11, 2 => 10
  | 11, 3 => 14
  | 11, 4 => 15
  | 12, 0 => 0
  | 12, 1 => 4
  | 12, 2 => 5
  | 12, 3 => 7
  | 12, 4 => 15
  | 13, 0 => 0
  | 13, 1 => 4
  | 13, 2 => 5
  | 13, 3 => 13
  | 13, 4 => 15
  | 14, 0 => 0
  | 14, 1 => 4
  | 14, 2 => 6
  | 14, 3 => 7
  | 14, 4 => 15
  | 15, 0 => 0
  | 15, 1 => 4
  | 15, 2 => 6
  | 15, 3 => 14
  | 15, 4 => 15
  | 16, 0 => 0
  | 16, 1 => 4
  | 16, 2 => 12
  | 16, 3 => 13
  | 16, 4 => 15
  | 17, 0 => 0
  | 17, 1 => 4
  | 17, 2 => 12
  | 17, 3 => 14
  | 17, 4 => 15
  | 18, 0 => 0
  | 18, 1 => 8
  | 18, 2 => 9
  | 18, 3 => 11
  | 18, 4 => 15
  | 19, 0 => 0
  | 19, 1 => 8
  | 19, 2 => 9
  | 19, 3 => 13
  | 19, 4 => 15
  | 20, 0 => 0
  | 20, 1 => 8
  | 20, 2 => 10
  | 20, 3 => 11
  | 20, 4 => 15
  | 21, 0 => 0
  | 21, 1 => 8
  | 21, 2 => 10
  | 21, 3 => 14
  | 21, 4 => 15
  | 22, 0 => 0
  | 22, 1 => 8
  | 22, 2 => 12
  | 22, 3 => 13
  | 22, 4 => 15
  | 23, 0 => 0
  | 23, 1 => 8
  | 23, 2 => 12
  | 23, 3 => 14
  | 23, 4 => 15
  | ⟨n+24, h⟩, _ => absurd h (by omega)

/-- The ten edge slots of a 4-simplex: corner pairs `(i, j)` with `i < j`,
in lexicographic order. -/
def edgeSlotPair : Fin 10 → Fin 5 × Fin 5
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (0, 4)
  | 4 => (1, 2)
  | 5 => (1, 3)
  | 6 => (1, 4)
  | 7 => (2, 3)
  | 8 => (2, 4)
  | 9 => (3, 4)
  | ⟨n+10, h⟩ => absurd h (by omega)

/-- Base cube-corner label of each Kuhn edge slot: slot `f` of simplex `σ`
starts at corner `(edgeSlotPair f).1`. -/
def kuhnEdgeBase : Fin 24 → Fin 10 → Fin 16
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 1
  | 0, 5 => 1
  | 0, 6 => 1
  | 0, 7 => 3
  | 0, 8 => 3
  | 0, 9 => 7
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 1
  | 1, 5 => 1
  | 1, 6 => 1
  | 1, 7 => 3
  | 1, 8 => 3
  | 1, 9 => 11
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 1
  | 2, 5 => 1
  | 2, 6 => 1
  | 2, 7 => 5
  | 2, 8 => 5
  | 2, 9 => 7
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 1
  | 3, 5 => 1
  | 3, 6 => 1
  | 3, 7 => 5
  | 3, 8 => 5
  | 3, 9 => 13
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 1
  | 4, 5 => 1
  | 4, 6 => 1
  | 4, 7 => 9
  | 4, 8 => 9
  | 4, 9 => 11
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 0
  | 5, 3 => 0
  | 5, 4 => 1
  | 5, 5 => 1
  | 5, 6 => 1
  | 5, 7 => 9
  | 5, 8 => 9
  | 5, 9 => 13
  | 6, 0 => 0
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 0
  | 6, 4 => 2
  | 6, 5 => 2
  | 6, 6 => 2
  | 6, 7 => 3
  | 6, 8 => 3
  | 6, 9 => 7
  | 7, 0 => 0
  | 7, 1 => 0
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 2
  | 7, 5 => 2
  | 7, 6 => 2
  | 7, 7 => 3
  | 7, 8 => 3
  | 7, 9 => 11
  | 8, 0 => 0
  | 8, 1 => 0
  | 8, 2 => 0
  | 8, 3 => 0
  | 8, 4 => 2
  | 8, 5 => 2
  | 8, 6 => 2
  | 8, 7 => 6
  | 8, 8 => 6
  | 8, 9 => 7
  | 9, 0 => 0
  | 9, 1 => 0
  | 9, 2 => 0
  | 9, 3 => 0
  | 9, 4 => 2
  | 9, 5 => 2
  | 9, 6 => 2
  | 9, 7 => 6
  | 9, 8 => 6
  | 9, 9 => 14
  | 10, 0 => 0
  | 10, 1 => 0
  | 10, 2 => 0
  | 10, 3 => 0
  | 10, 4 => 2
  | 10, 5 => 2
  | 10, 6 => 2
  | 10, 7 => 10
  | 10, 8 => 10
  | 10, 9 => 11
  | 11, 0 => 0
  | 11, 1 => 0
  | 11, 2 => 0
  | 11, 3 => 0
  | 11, 4 => 2
  | 11, 5 => 2
  | 11, 6 => 2
  | 11, 7 => 10
  | 11, 8 => 10
  | 11, 9 => 14
  | 12, 0 => 0
  | 12, 1 => 0
  | 12, 2 => 0
  | 12, 3 => 0
  | 12, 4 => 4
  | 12, 5 => 4
  | 12, 6 => 4
  | 12, 7 => 5
  | 12, 8 => 5
  | 12, 9 => 7
  | 13, 0 => 0
  | 13, 1 => 0
  | 13, 2 => 0
  | 13, 3 => 0
  | 13, 4 => 4
  | 13, 5 => 4
  | 13, 6 => 4
  | 13, 7 => 5
  | 13, 8 => 5
  | 13, 9 => 13
  | 14, 0 => 0
  | 14, 1 => 0
  | 14, 2 => 0
  | 14, 3 => 0
  | 14, 4 => 4
  | 14, 5 => 4
  | 14, 6 => 4
  | 14, 7 => 6
  | 14, 8 => 6
  | 14, 9 => 7
  | 15, 0 => 0
  | 15, 1 => 0
  | 15, 2 => 0
  | 15, 3 => 0
  | 15, 4 => 4
  | 15, 5 => 4
  | 15, 6 => 4
  | 15, 7 => 6
  | 15, 8 => 6
  | 15, 9 => 14
  | 16, 0 => 0
  | 16, 1 => 0
  | 16, 2 => 0
  | 16, 3 => 0
  | 16, 4 => 4
  | 16, 5 => 4
  | 16, 6 => 4
  | 16, 7 => 12
  | 16, 8 => 12
  | 16, 9 => 13
  | 17, 0 => 0
  | 17, 1 => 0
  | 17, 2 => 0
  | 17, 3 => 0
  | 17, 4 => 4
  | 17, 5 => 4
  | 17, 6 => 4
  | 17, 7 => 12
  | 17, 8 => 12
  | 17, 9 => 14
  | 18, 0 => 0
  | 18, 1 => 0
  | 18, 2 => 0
  | 18, 3 => 0
  | 18, 4 => 8
  | 18, 5 => 8
  | 18, 6 => 8
  | 18, 7 => 9
  | 18, 8 => 9
  | 18, 9 => 11
  | 19, 0 => 0
  | 19, 1 => 0
  | 19, 2 => 0
  | 19, 3 => 0
  | 19, 4 => 8
  | 19, 5 => 8
  | 19, 6 => 8
  | 19, 7 => 9
  | 19, 8 => 9
  | 19, 9 => 13
  | 20, 0 => 0
  | 20, 1 => 0
  | 20, 2 => 0
  | 20, 3 => 0
  | 20, 4 => 8
  | 20, 5 => 8
  | 20, 6 => 8
  | 20, 7 => 10
  | 20, 8 => 10
  | 20, 9 => 11
  | 21, 0 => 0
  | 21, 1 => 0
  | 21, 2 => 0
  | 21, 3 => 0
  | 21, 4 => 8
  | 21, 5 => 8
  | 21, 6 => 8
  | 21, 7 => 10
  | 21, 8 => 10
  | 21, 9 => 14
  | 22, 0 => 0
  | 22, 1 => 0
  | 22, 2 => 0
  | 22, 3 => 0
  | 22, 4 => 8
  | 22, 5 => 8
  | 22, 6 => 8
  | 22, 7 => 12
  | 22, 8 => 12
  | 22, 9 => 13
  | 23, 0 => 0
  | 23, 1 => 0
  | 23, 2 => 0
  | 23, 3 => 0
  | 23, 4 => 8
  | 23, 5 => 8
  | 23, 6 => 8
  | 23, 7 => 12
  | 23, 8 => 12
  | 23, 9 => 14
  | ⟨n+24, h⟩, _ => absurd h (by omega)

/-- Displacement class of each Kuhn edge slot: slot `f` of simplex `σ` runs
from corner `(edgeSlotPair f).1` to corner `(edgeSlotPair f).2`, whose
componentwise difference is one of the fifteen positive classes. Every one
of the fifteen classes occurs across the table. -/
def kuhnEdgeDisp : Fin 24 → Fin 10 → Fin 15
  | 0, 0 => 0
  | 0, 1 => 2
  | 0, 2 => 6
  | 0, 3 => 14
  | 0, 4 => 1
  | 0, 5 => 5
  | 0, 6 => 13
  | 0, 7 => 3
  | 0, 8 => 11
  | 0, 9 => 7
  | 1, 0 => 0
  | 1, 1 => 2
  | 1, 2 => 10
  | 1, 3 => 14
  | 1, 4 => 1
  | 1, 5 => 9
  | 1, 6 => 13
  | 1, 7 => 7
  | 1, 8 => 11
  | 1, 9 => 3
  | 2, 0 => 0
  | 2, 1 => 4
  | 2, 2 => 6
  | 2, 3 => 14
  | 2, 4 => 3
  | 2, 5 => 5
  | 2, 6 => 13
  | 2, 7 => 1
  | 2, 8 => 9
  | 2, 9 => 7
  | 3, 0 => 0
  | 3, 1 => 4
  | 3, 2 => 12
  | 3, 3 => 14
  | 3, 4 => 3
  | 3, 5 => 11
  | 3, 6 => 13
  | 3, 7 => 7
  | 3, 8 => 9
  | 3, 9 => 1
  | 4, 0 => 0
  | 4, 1 => 8
  | 4, 2 => 10
  | 4, 3 => 14
  | 4, 4 => 7
  | 4, 5 => 9
  | 4, 6 => 13
  | 4, 7 => 1
  | 4, 8 => 5
  | 4, 9 => 3
  | 5, 0 => 0
  | 5, 1 => 8
  | 5, 2 => 12
  | 5, 3 => 14
  | 5, 4 => 7
  | 5, 5 => 11
  | 5, 6 => 13
  | 5, 7 => 3
  | 5, 8 => 5
  | 5, 9 => 1
  | 6, 0 => 1
  | 6, 1 => 2
  | 6, 2 => 6
  | 6, 3 => 14
  | 6, 4 => 0
  | 6, 5 => 4
  | 6, 6 => 12
  | 6, 7 => 3
  | 6, 8 => 11
  | 6, 9 => 7
  | 7, 0 => 1
  | 7, 1 => 2
  | 7, 2 => 10
  | 7, 3 => 14
  | 7, 4 => 0
  | 7, 5 => 8
  | 7, 6 => 12
  | 7, 7 => 7
  | 7, 8 => 11
  | 7, 9 => 3
  | 8, 0 => 1
  | 8, 1 => 5
  | 8, 2 => 6
  | 8, 3 => 14
  | 8, 4 => 3
  | 8, 5 => 4
  | 8, 6 => 12
  | 8, 7 => 0
  | 8, 8 => 8
  | 8, 9 => 7
  | 9, 0 => 1
  | 9, 1 => 5
  | 9, 2 => 13
  | 9, 3 => 14
  | 9, 4 => 3
  | 9, 5 => 11
  | 9, 6 => 12
  | 9, 7 => 7
  | 9, 8 => 8
  | 9, 9 => 0
  | 10, 0 => 1
  | 10, 1 => 9
  | 10, 2 => 10
  | 10, 3 => 14
  | 10, 4 => 7
  | 10, 5 => 8
  | 10, 6 => 12
  | 10, 7 => 0
  | 10, 8 => 4
  | 10, 9 => 3
  | 11, 0 => 1
  | 11, 1 => 9
  | 11, 2 => 13
  | 11, 3 => 14
  | 11, 4 => 7
  | 11, 5 => 11
  | 11, 6 => 12
  | 11, 7 => 3
  | 11, 8 => 4
  | 11, 9 => 0
  | 12, 0 => 3
  | 12, 1 => 4
  | 12, 2 => 6
  | 12, 3 => 14
  | 12, 4 => 0
  | 12, 5 => 2
  | 12, 6 => 10
  | 12, 7 => 1
  | 12, 8 => 9
  | 12, 9 => 7
  | 13, 0 => 3
  | 13, 1 => 4
  | 13, 2 => 12
  | 13, 3 => 14
  | 13, 4 => 0
  | 13, 5 => 8
  | 13, 6 => 10
  | 13, 7 => 7
  | 13, 8 => 9
  | 13, 9 => 1
  | 14, 0 => 3
  | 14, 1 => 5
  | 14, 2 => 6
  | 14, 3 => 14
  | 14, 4 => 1
  | 14, 5 => 2
  | 14, 6 => 10
  | 14, 7 => 0
  | 14, 8 => 8
  | 14, 9 => 7
  | 15, 0 => 3
  | 15, 1 => 5
  | 15, 2 => 13
  | 15, 3 => 14
  | 15, 4 => 1
  | 15, 5 => 9
  | 15, 6 => 10
  | 15, 7 => 7
  | 15, 8 => 8
  | 15, 9 => 0
  | 16, 0 => 3
  | 16, 1 => 11
  | 16, 2 => 12
  | 16, 3 => 14
  | 16, 4 => 7
  | 16, 5 => 8
  | 16, 6 => 10
  | 16, 7 => 0
  | 16, 8 => 2
  | 16, 9 => 1
  | 17, 0 => 3
  | 17, 1 => 11
  | 17, 2 => 13
  | 17, 3 => 14
  | 17, 4 => 7
  | 17, 5 => 9
  | 17, 6 => 10
  | 17, 7 => 1
  | 17, 8 => 2
  | 17, 9 => 0
  | 18, 0 => 7
  | 18, 1 => 8
  | 18, 2 => 10
  | 18, 3 => 14
  | 18, 4 => 0
  | 18, 5 => 2
  | 18, 6 => 6
  | 18, 7 => 1
  | 18, 8 => 5
  | 18, 9 => 3
  | 19, 0 => 7
  | 19, 1 => 8
  | 19, 2 => 12
  | 19, 3 => 14
  | 19, 4 => 0
  | 19, 5 => 4
  | 19, 6 => 6
  | 19, 7 => 3
  | 19, 8 => 5
  | 19, 9 => 1
  | 20, 0 => 7
  | 20, 1 => 9
  | 20, 2 => 10
  | 20, 3 => 14
  | 20, 4 => 1
  | 20, 5 => 2
  | 20, 6 => 6
  | 20, 7 => 0
  | 20, 8 => 4
  | 20, 9 => 3
  | 21, 0 => 7
  | 21, 1 => 9
  | 21, 2 => 13
  | 21, 3 => 14
  | 21, 4 => 1
  | 21, 5 => 5
  | 21, 6 => 6
  | 21, 7 => 3
  | 21, 8 => 4
  | 21, 9 => 0
  | 22, 0 => 7
  | 22, 1 => 11
  | 22, 2 => 12
  | 22, 3 => 14
  | 22, 4 => 3
  | 22, 5 => 4
  | 22, 6 => 6
  | 22, 7 => 0
  | 22, 8 => 2
  | 22, 9 => 1
  | 23, 0 => 7
  | 23, 1 => 11
  | 23, 2 => 13
  | 23, 3 => 14
  | 23, 4 => 3
  | 23, 5 => 5
  | 23, 6 => 6
  | 23, 7 => 1
  | 23, 8 => 2
  | 23, 9 => 0
  | ⟨n+24, h⟩, _ => absurd h (by omega)

/-- Periodic Kuhn 4-simplices: one of the 24 Kuhn simplices inside each
periodic cubic cell. Finite at every side as a product of finite types. -/
abbrev PeriodicSimplex4 (N : ℕ) := Vertex4 N × Fin 24

/-- **Simplex count formula.** The periodic Kuhn 4-simplex set at side `N`
has `24 * N ^ 4` elements. -/
theorem card_periodicSimplex4 (N : ℕ) :
    Fintype.card (PeriodicSimplex4 N) = 24 * N ^ 4 := by
  rw [Fintype.card_prod, card_vertex4, Fintype.card_fin]
  ring

/-- **Sanity (Kuhn count).** The triangulation of one 4-cube has exactly
`4! = 24` four-simplices. -/
theorem kuhn_simplex_count_per_cube :
    Fintype.card (Fin 24) = 24 ∧ Nat.factorial 4 = 24 :=
  ⟨rfl, by decide⟩

/-- Every Kuhn simplex starts at the cube origin. -/
theorem kuhnVerts_zero (σ : Fin 24) : kuhnVerts σ 0 = 0 := by
  fin_cases σ <;> rfl

/-- Every Kuhn simplex ends at the opposite cube corner `15`. -/
theorem kuhnVerts_four (σ : Fin 24) : kuhnVerts σ 4 = 15 := by
  fin_cases σ <;> rfl

/-- The five corner labels of each Kuhn simplex are pairwise distinct. -/
theorem kuhnVerts_label_injective (σ : Fin 24) :
    Function.Injective (kuhnVerts σ) := by
  fin_cases σ <;> decide

/-- The translated global 4-edge of a local Kuhn edge slot. -/
def localEdgeOf4 {N : ℕ} [NeZero N] (cell : Vertex4 N) (σ : Fin 24)
    (f : Fin 10) : PeriodicEdge4 N :=
  { base := addVertexBits4 cell (kuhnEdgeBase σ f), disp := kuhnEdgeDisp σ f }

/-- Corner `k` of Kuhn simplex `σ`, translated to the periodic cell. -/
def kuhnCornerAt {N : ℕ} [NeZero N] (cell : Vertex4 N) (σ : Fin 24)
    (k : Fin 5) : Vertex4 N :=
  addVertexBits4 cell (kuhnVerts σ k)

set_option maxHeartbeats 1600000 in
/-- **Endpoint incidence (edge-in-class sanity).** Every edge slot of every
Kuhn 4-simplex is realized by a positive-displacement periodic 4-edge in one
of the fifteen classes: slot `f` runs from corner `(edgeSlotPair f).1` to
corner `(edgeSlotPair f).2`, and the endpoints of `localEdgeOf4` agree with
those translated corners (in direct order, by construction of the tables). -/
theorem localEdgeOf4_endpoints_match_kuhnVerts {N : ℕ} [NeZero N]
    (cell : Vertex4 N) (σ : Fin 24) (f : Fin 10) :
    (kuhnCornerAt cell σ (edgeSlotPair f).1 = (localEdgeOf4 cell σ f).endpoints.1 ∧
      kuhnCornerAt cell σ (edgeSlotPair f).2 = (localEdgeOf4 cell σ f).endpoints.2) ∨
      (kuhnCornerAt cell σ (edgeSlotPair f).1 = (localEdgeOf4 cell σ f).endpoints.2 ∧
        kuhnCornerAt cell σ (edgeSlotPair f).2 = (localEdgeOf4 cell σ f).endpoints.1) := by
  fin_cases σ <;> fin_cases f <;>
    simp [localEdgeOf4, PeriodicEdge4.endpoints, kuhnCornerAt, edgeSlotPair,
      kuhnVerts, kuhnEdgeBase, kuhnEdgeDisp, addVertexBits4, addBits4,
      vertexBits4, dispBits4]

/-- On a side-`N` torus with `1 < N`, the five corners of any Kuhn
4-simplex are pairwise distinct. -/
theorem kuhn_corners_injective (N : ℕ) [NeZero N] (hN : 1 < N)
    (cell : Vertex4 N) (σ : Fin 24) :
    Function.Injective (fun k : Fin 5 => kuhnCornerAt cell σ k) := by
  intro a b h
  have hcancel :
      vertexBits4 (kuhnVerts σ a) = vertexBits4 (kuhnVerts σ b) := by
    rcases addBits4_cancel_offsets N hN cell
        (vertexBits4 (kuhnVerts σ a)).1
        (vertexBits4 (kuhnVerts σ a)).2.1
        (vertexBits4 (kuhnVerts σ a)).2.2.1
        (vertexBits4 (kuhnVerts σ a)).2.2.2
        (vertexBits4 (kuhnVerts σ b)).1
        (vertexBits4 (kuhnVerts σ b)).2.1
        (vertexBits4 (kuhnVerts σ b)).2.2.1
        (vertexBits4 (kuhnVerts σ b)).2.2.2
        (by simpa [kuhnCornerAt, addVertexBits4] using h) with ⟨hx, hy, hz, hw⟩
    exact Prod.ext hx (Prod.ext hy (Prod.ext hz hw))
  exact kuhnVerts_label_injective σ (vertexBits4_injective hcancel)

/-- The slot of an unordered corner pair (the inverse of `edgeSlotPair` up
to orientation). -/
def pairSlot4 (i j : Fin 5) : Fin 10 :=
  let a := min i j
  let b := max i j
  if a = 0 ∧ b = 1 then 0
  else if a = 0 ∧ b = 2 then 1
  else if a = 0 ∧ b = 3 then 2
  else if a = 0 ∧ b = 4 then 3
  else if a = 1 ∧ b = 2 then 4
  else if a = 1 ∧ b = 3 then 5
  else if a = 1 ∧ b = 4 then 6
  else if a = 2 ∧ b = 3 then 7
  else if a = 2 ∧ b = 4 then 8
  else 9

theorem pairSlot4_spec (i j : Fin 5) (hij : i ≠ j) :
    edgeSlotPair (pairSlot4 i j) = (i, j) ∨
      edgeSlotPair (pairSlot4 i j) = (j, i) := by
  fin_cases i <;> fin_cases j
  all_goals (try exact (hij rfl).elim)
  all_goals (first | (left; rfl) | (right; rfl))

/-! ## §8. Finite encoder -/

/-- Canonical finite index set for periodic 4-vertices. -/
noncomputable def vertexFinEquiv4 (N : ℕ) [NeZero N] :
    Fin (Fintype.card (Vertex4 N)) ≃ Vertex4 N :=
  (Fintype.equivFin (Vertex4 N)).symm

/-- Canonical finite index set for positive-displacement periodic 4-edges. -/
noncomputable def edgeFinEquiv4 (N : ℕ) [NeZero N] :
    Fin (Fintype.card (PeriodicEdge4 N)) ≃ PeriodicEdge4 N :=
  (Fintype.equivFin (PeriodicEdge4 N)).symm

/-- Canonical finite index set for periodic Kuhn 4-simplices. -/
noncomputable def simplexFinEquiv4 (N : ℕ) [NeZero N] :
    Fin (Fintype.card (PeriodicSimplex4 N)) ≃ PeriodicSimplex4 N :=
  (Fintype.equivFin (PeriodicSimplex4 N)).symm

/-- Canonical endpoint map for positive-displacement periodic 4-edges,
expressed in the finite vertex index set. -/
def canonicalEdgeVerts4 (N : ℕ) [NeZero N]
    (e : Fin (Fintype.card (PeriodicEdge4 N))) :
    Fin (Fintype.card (Vertex4 N)) × Fin (Fintype.card (Vertex4 N)) :=
  let edge := edgeFinEquiv4 N e
  let endpoints := edge.endpoints
  ((vertexFinEquiv4 N).symm endpoints.1,
    (vertexFinEquiv4 N).symm endpoints.2)

/-- Canonical 4-simplex corner map for the 24-simplex Kuhn decomposition in
every periodic cell. -/
def canonicalSimplexVerts4 (N : ℕ) [NeZero N]
    (τ : Fin (Fintype.card (PeriodicSimplex4 N))) (k : Fin 5) :
    Fin (Fintype.card (Vertex4 N)) :=
  let cellS := simplexFinEquiv4 N τ
  (vertexFinEquiv4 N).symm (addVertexBits4 cellS.1 (kuhnVerts cellS.2 k))

/-! ## §9. The simplicial 4D carrier -/

/-- Unordered-pair equality of ordered vertex pairs (local mirror of the 3D
`sameUnorderedPair`, which lives in the SevenGaps path-sum layer). -/
def sameUnorderedPair4 {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  p = q ∨ p = q.swap

/-- The self-contained 4D analog of the path-sum `BoundedComplex` incidence
shape: vertex count, edge count, 4-simplex count, endpoint incidence, and
corner incidence with `Fin 5` corners. `BoundedComplex` is tet-only and
cannot hold Kuhn 4-simplices; extending it is a separate decision. -/
structure Carrier4D where
  nV : ℕ
  nE : ℕ
  nS : ℕ
  edgeVerts : Fin nE → Fin nV × Fin nV
  simplexVerts : Fin nS → Fin 5 → Fin nV

/-- The simplicial predicate on a 4D carrier (mirror of the 3D
`IsSimplicial`): no degenerate edges, no multi-edges, injective 4-simplex
corners, and skeleton closure (every corner pair of every 4-simplex is an
edge of the carrier). -/
def IsSimplicial4D (K : Carrier4D) : Prop :=
  (∀ e : Fin K.nE, (K.edgeVerts e).1 ≠ (K.edgeVerts e).2) ∧
  (∀ e e' : Fin K.nE,
    sameUnorderedPair4 (K.edgeVerts e) (K.edgeVerts e') → e = e') ∧
  (∀ s : Fin K.nS, Function.Injective (K.simplexVerts s)) ∧
  (∀ (s : Fin K.nS) (i j : Fin 5), i ≠ j →
    ∃ e : Fin K.nE,
      sameUnorderedPair4 (K.edgeVerts e) (K.simplexVerts s i, K.simplexVerts s j))

/-- The canonical periodic Freudenthal 4-torus carrier at side `N`. -/
def canonicalCarrier4D (N : ℕ) [NeZero N] : Carrier4D where
  nV := Fintype.card (Vertex4 N)
  nE := Fintype.card (PeriodicEdge4 N)
  nS := Fintype.card (PeriodicSimplex4 N)
  edgeVerts := canonicalEdgeVerts4 N
  simplexVerts := canonicalSimplexVerts4 N

/-- Vertex count of the canonical carrier: `N ^ 4`. -/
theorem canonicalCarrier4D_nV (N : ℕ) [NeZero N] :
    (canonicalCarrier4D N).nV = N ^ 4 :=
  card_vertex4 N

/-- Edge count of the canonical carrier: `15 * N ^ 4`. -/
theorem canonicalCarrier4D_nE (N : ℕ) [NeZero N] :
    (canonicalCarrier4D N).nE = 15 * N ^ 4 :=
  card_periodicEdge4 N

/-- 4-simplex count of the canonical carrier: `24 * N ^ 4`. -/
theorem canonicalCarrier4D_nS (N : ℕ) [NeZero N] :
    (canonicalCarrier4D N).nS = 24 * N ^ 4 :=
  card_periodicSimplex4 N

theorem canonicalCarrier4D_no_loops (N : ℕ) [NeZero N] (hN : 2 < N) :
    ∀ e : Fin (canonicalCarrier4D N).nE,
      ((canonicalCarrier4D N).edgeVerts e).1 ≠
        ((canonicalCarrier4D N).edgeVerts e).2 := by
  intro e heq
  have hne := PeriodicEdge4.endpoints_ne hN (edgeFinEquiv4 N e)
  apply hne
  change (canonicalEdgeVerts4 N e).1 = (canonicalEdgeVerts4 N e).2 at heq
  dsimp [canonicalEdgeVerts4] at heq
  exact (vertexFinEquiv4 N).symm.injective heq

theorem endpoints_injective4 (N : ℕ) [NeZero N] (hN : 1 < N)
    {e₁ e₂ : PeriodicEdge4 N} (h : e₁.endpoints = e₂.endpoints) :
    e₁ = e₂ := by
  rcases e₁ with ⟨b₁, d₁⟩
  rcases e₂ with ⟨b₂, d₂⟩
  have hb : b₁ = b₂ := congrArg Prod.fst h
  subst hb
  have htip :
      addBits4 b₁ (dispBits4 d₁).1 (dispBits4 d₁).2.1 (dispBits4 d₁).2.2.1
        (dispBits4 d₁).2.2.2 =
        addBits4 b₁ (dispBits4 d₂).1 (dispBits4 d₂).2.1 (dispBits4 d₂).2.2.1
          (dispBits4 d₂).2.2.2 := by
    simpa [PeriodicEdge4.endpoints] using congrArg Prod.snd h
  have hbits := addBits4_cancel_offsets N hN b₁
    (dispBits4 d₁).1 (dispBits4 d₁).2.1 (dispBits4 d₁).2.2.1 (dispBits4 d₁).2.2.2
    (dispBits4 d₂).1 (dispBits4 d₂).2.1 (dispBits4 d₂).2.2.1 (dispBits4 d₂).2.2.2
    htip
  have hd : d₁ = d₂ :=
    dispBits4_injective
      (Prod.ext hbits.1 (Prod.ext hbits.2.1 (Prod.ext hbits.2.2.1 hbits.2.2.2)))
  cases hd
  rfl

theorem reverse_impossible4 (N : ℕ) [NeZero N] (hN : 2 < N)
    (e₁ e₂ : PeriodicEdge4 N) (h : e₁.endpoints = e₂.endpoints.swap) :
    False := by
  rcases e₁ with ⟨b, d⟩
  rcases e₂ with ⟨b', d'⟩
  simp only [PeriodicEdge4.endpoints, Prod.swap_prod_mk] at h
  obtain ⟨hb, ht⟩ := Prod.mk.inj h
  have hloop :
      addBits4 (addBits4 b' (dispBits4 d').1 (dispBits4 d').2.1
        (dispBits4 d').2.2.1 (dispBits4 d').2.2.2)
        (dispBits4 d).1 (dispBits4 d).2.1 (dispBits4 d).2.2.1
        (dispBits4 d).2.2.2 = b' := by
    rw [← hb]
    exact ht
  have hx := two_bit_steps_ne_id N hN b'.1 (dispBits4 d').1 (dispBits4 d).1
    (congrArg Prod.fst hloop)
  have hy := two_bit_steps_ne_id N hN b'.2.1 (dispBits4 d').2.1 (dispBits4 d).2.1
    (congrArg (fun v : Vertex4 N => v.2.1) hloop)
  have hz := two_bit_steps_ne_id N hN b'.2.2.1 (dispBits4 d').2.2.1
    (dispBits4 d).2.2.1 (congrArg (fun v : Vertex4 N => v.2.2.1) hloop)
  have hw := two_bit_steps_ne_id N hN b'.2.2.2 (dispBits4 d').2.2.2
    (dispBits4 d).2.2.2 (congrArg (fun v : Vertex4 N => v.2.2.2) hloop)
  exact dispBits4_ne_zero d'
    (Prod.ext hx.1 (Prod.ext hy.1 (Prod.ext hz.1 hw.1)))

theorem canonicalCarrier4D_no_multiedges (N : ℕ) [NeZero N] (hN : 2 < N) :
    ∀ e e' : Fin (canonicalCarrier4D N).nE,
      sameUnorderedPair4 ((canonicalCarrier4D N).edgeVerts e)
        ((canonicalCarrier4D N).edgeVerts e') → e = e' := by
  intro e e' hpair
  set Eeq := edgeFinEquiv4 N
  set Veq := vertexFinEquiv4 N
  change sameUnorderedPair4 (canonicalEdgeVerts4 N e) (canonicalEdgeVerts4 N e')
    at hpair
  cases hpair with
  | inl hsame =>
    have hends : (Eeq e).endpoints = (Eeq e').endpoints := by
      refine Prod.ext ?_ ?_
      · have := congrArg (fun p => Veq p.1) hsame
        simpa [canonicalEdgeVerts4, Equiv.apply_symm_apply] using this
      · have := congrArg (fun p => Veq p.2) hsame
        simpa [canonicalEdgeVerts4, Equiv.apply_symm_apply] using this
    exact Eeq.injective
      (endpoints_injective4 N (lt_trans (by decide : 1 < 2) hN) hends)
  | inr hswap =>
    have hends : (Eeq e).endpoints = (Eeq e').endpoints.swap := by
      refine Prod.ext ?_ ?_
      · have := congrArg (fun p => Veq p.1) hswap
        simpa [canonicalEdgeVerts4, Equiv.apply_symm_apply, Prod.swap_prod_mk]
          using this
      · have := congrArg (fun p => Veq p.2) hswap
        simpa [canonicalEdgeVerts4, Equiv.apply_symm_apply, Prod.swap_prod_mk]
          using this
    exact (reverse_impossible4 N hN _ _ hends).elim

theorem canonicalCarrier4D_simplex_injective (N : ℕ) [NeZero N] (hN : 2 < N) :
    ∀ s : Fin (canonicalCarrier4D N).nS,
      Function.Injective ((canonicalCarrier4D N).simplexVerts s) := by
  intro s a b hab
  set cellS := simplexFinEquiv4 N s
  change canonicalSimplexVerts4 N s a = canonicalSimplexVerts4 N s b at hab
  have hadd :
      addVertexBits4 cellS.1 (kuhnVerts cellS.2 a) =
        addVertexBits4 cellS.1 (kuhnVerts cellS.2 b) := by
    have := congrArg (vertexFinEquiv4 N) hab
    simpa [canonicalSimplexVerts4, Equiv.apply_symm_apply] using this
  exact kuhn_corners_injective N (lt_trans (by decide : 1 < 2) hN) cellS.1
    cellS.2 hadd

theorem canonicalCarrier4D_skeleton (N : ℕ) [NeZero N]
    (s : Fin (canonicalCarrier4D N).nS) (i j : Fin 5) (hij : i ≠ j) :
    ∃ e : Fin (canonicalCarrier4D N).nE,
      sameUnorderedPair4 ((canonicalCarrier4D N).edgeVerts e)
        ((canonicalCarrier4D N).simplexVerts s i,
          (canonicalCarrier4D N).simplexVerts s j) := by
  set cellS := simplexFinEquiv4 N s
  let slot := pairSlot4 i j
  refine ⟨(edgeFinEquiv4 N).symm (localEdgeOf4 cellS.1 cellS.2 slot), ?_⟩
  have hInc := localEdgeOf4_endpoints_match_kuhnVerts cellS.1 cellS.2 slot
  change sameUnorderedPair4
    (canonicalEdgeVerts4 N ((edgeFinEquiv4 N).symm (localEdgeOf4 cellS.1 cellS.2 slot)))
    (canonicalSimplexVerts4 N s i, canonicalSimplexVerts4 N s j)
  simp only [canonicalEdgeVerts4, canonicalSimplexVerts4, Equiv.apply_symm_apply,
    sameUnorderedPair4]
  rcases pairSlot4_spec i j hij with hp | hp
  · rw [show slot = pairSlot4 i j from rfl, hp] at hInc
    rcases hInc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact Prod.ext (congrArg (vertexFinEquiv4 N).symm h1.symm)
        (congrArg (vertexFinEquiv4 N).symm h2.symm)
    · right
      exact Prod.ext (congrArg (vertexFinEquiv4 N).symm h2.symm)
        (congrArg (vertexFinEquiv4 N).symm h1.symm)
  · rw [show slot = pairSlot4 i j from rfl, hp] at hInc
    rcases hInc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      exact Prod.ext (congrArg (vertexFinEquiv4 N).symm h1.symm)
        (congrArg (vertexFinEquiv4 N).symm h2.symm)
    · left
      exact Prod.ext (congrArg (vertexFinEquiv4 N).symm h2.symm)
        (congrArg (vertexFinEquiv4 N).symm h1.symm)

/-- **Headline (carrier simpliciality).** The canonical periodic Freudenthal
4-torus carrier at side `2 < N` is simplicial: distinct edge endpoints, no
multi-edges, five distinct corners per Kuhn 4-simplex, and skeleton
closure. -/
theorem canonicalCarrier4D_isSimplicial (N : ℕ) [NeZero N] (hN : 2 < N) :
    IsSimplicial4D (canonicalCarrier4D N) :=
  ⟨canonicalCarrier4D_no_loops N hN, canonicalCarrier4D_no_multiedges N hN,
    canonicalCarrier4D_simplex_injective N hN,
    fun s i j hij => canonicalCarrier4D_skeleton N s i j hij⟩

/-! ## §10. Class squared lengths and the mesh scale -/

/-- Hamming weight of a displacement class (the squared lattice length of
its 0/1 displacement). -/
def dispWeight4 : Fin 15 → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 3
  | 11 => 2
  | 12 => 3
  | 13 => 3
  | 14 => 4

/-- Squared lattice displacement determined only by the class (the 4D mirror
of the 3D `periodicDispSqEdge`). -/
def periodicDispSqEdge4 (d : Fin 15) : ℝ :=
  dispWeight4 d

theorem dispWeight4_le_four (d : Fin 15) : dispWeight4 d ≤ 4 := by
  fin_cases d <;> decide

theorem periodicDispSqEdge4_le_four (d : Fin 15) :
    periodicDispSqEdge4 d ≤ (4 : ℝ) := by
  unfold periodicDispSqEdge4
  exact_mod_cast dispWeight4_le_four d

/-- Mesh scale at side `N`: the length of the largest class edge at lattice
spacing `1 / N`, which is the weight-4 hyperbody diagonal (class 14).
Mirrors the 3D `meshVal = sqrt 3 * spacing` (max weight 3 there). -/
def meshVal4D (N : ℕ) : ℝ :=
  Real.sqrt 4 * (N : ℝ)⁻¹

theorem meshVal4D_pos (N : ℕ) (hN : 0 < N) : 0 < meshVal4D N :=
  mul_pos (Real.sqrt_pos.mpr (by norm_num)) (inv_pos.mpr (Nat.cast_pos.mpr hN))

/-- **Mesh attainment.** The constant weight-4 class assignment (class 14,
the hyperbody diagonal) realizes the mesh scale on any edge, at lattice
spacing `1 / N`. -/
theorem meshVal4D_attained (N : ℕ) [NeZero N] :
    ∃ c : PeriodicEdge4 N → Fin 15, ∃ e : PeriodicEdge4 N,
      Real.sqrt ((N : ℝ)⁻¹ ^ 2 * periodicDispSqEdge4 (c e)) = meshVal4D N := by
  refine ⟨fun _ => 14, ⟨(0, 0, 0, 0), 0⟩, ?_⟩
  change Real.sqrt ((N : ℝ)⁻¹ ^ 2 * periodicDispSqEdge4 (14 : Fin 15)) = meshVal4D N
  have hN : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
  have hNN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hN)
  have h14 : periodicDispSqEdge4 (14 : Fin 15) = 4 := by
    unfold periodicDispSqEdge4
    norm_num [dispWeight4]
  unfold meshVal4D
  rw [h14, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hNN, mul_comm]

#print axioms canonicalCarrier4D_isSimplicial
#print axioms card_periodicEdge4
#print axioms card_periodicSimplex4
#print axioms displacement_classes_are_fifteen
#print axioms localEdgeOf4_endpoints_match_kuhnVerts
#print axioms kuhn_corners_injective
#print axioms kuhn_simplex_count_per_cube
#print axioms meshVal4D_attained
#print axioms vertexFinEquiv4
#print axioms edgeFinEquiv4
#print axioms simplexFinEquiv4

end

end PeriodicFreudenthalTorus4D
end Geometry
end IndisputableMonolith
