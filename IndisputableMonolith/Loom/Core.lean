import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Loom: a certificate language for configurations of closed recognition walks

A recognition history is a walk across states, and a finished history closes. On the
eight state, three axis window the forcing chain gives us, the closed walks up to
homotopy form a free group of rank `E - V + 1 = 5`, so a closed walk is a word in five
signed generators and a finished utterance is a finite LIST of such words sharing one
basepoint.

Two premises fix what counts as content, and both say something is NOT content.
Spelling is not content, so words are read up to free reduction. Where the utterance
started is not content, because a received meaning arrives whole rather than word by
word, so one SIMULTANEOUS conjugation of every loop by the same word is not content
either. That second premise was carried as phenomenological rather than proved, and this
header said everything below was conditional on it. `Loom.BasepointForced` has since
removed it from the load path, and the honest statement now has two parts. Closure gives
conjugation by prefixes of the walk as a theorem (`rotate_is_conjugation`), since a closed
history is a map from a circle and names no vertex of itself as first. The step from
prefixes to arbitrary words is vertex homogeneity, which is not proved there either; it is
the same refusal to let an observable depend on a label the description supplies that
already motivates quotienting by the 48 automorphisms of the window. So a reader who
accepts that quotient is committed to this one, and a reader who rejects it is not. The
phenomenological observation now agrees with the argument instead of carrying it.

This module supplies three things and nothing else: a total checker for
well-formedness, a computable invariant of a configuration, and the theorems that the
invariant is blind to exactly the two non-content operations. It carries no model and
no search, so it can be trusted with a finished object it did not build.

The invariant reads traces in `SL(2, ZMod 3)`. Trace is a class function, which is the
whole reason it is usable here: blindness to conjugation is a ring identity rather than
a canonicalisation. Loop traces alone do not separate the intended witness (measured:
they collide on two of the forty eight automorphism images), so the invariant also
reads the traces of the pairwise COMMUTATORS of the loop images, which is the depth two
data of the lower central series and is exactly what an abelianised reading destroys.
-/

namespace IndisputableMonolith
namespace Loom

/-- A closed walk up to homotopy: a word in the five signed cotree generators. -/
abbrev Word := List Int

/-- An utterance: a finite list of closed walks sharing one basepoint. -/
abbrev Config := List Word

-- ---------------------------------------------------------------------------
-- free reduction, and the checker
-- ---------------------------------------------------------------------------

/-- Prepend one act to an already reduced word, cancelling if it cancels. -/
def consRed (x : Int) : Word → Word
  | [] => [x]
  | y :: r => if x + y = 0 then r else x :: y :: r

/-- Free reduction. Total and linear, which is why every question this language can
ask is cheap and always answerable. -/
def reduceWord : Word → Word
  | [] => []
  | x :: t => consRed x (reduceWord t)

/-- No adjacent cancelling pair. This is what the checker checks. -/
def isReduced : Word → Bool
  | [] => true
  | [_] => true
  | x :: y :: t => (x + y != 0) && isReduced (y :: t)

/-- Reversing a walk and negating every act. Per loop this is a content operation
(it is how denial is encoded); applied to every loop at once it is gauge. -/
def invWord : Word → Word
  | [] => []
  | x :: t => invWord t ++ [-x]

/-- Moving the basepoint of the whole utterance by one word. -/
def conjWord (g w : Word) : Word := reduceWord (g ++ w ++ invWord g)

theorem reduceWord_cons (x : Int) (t : Word) :
    reduceWord (x :: t) = consRed x (reduceWord t) := rfl

theorem invWord_cons (x : Int) (t : Word) : invWord (x :: t) = invWord t ++ [-x] := rfl

theorem isReduced_cons_cons (x y : Int) (t : Word) :
    isReduced (x :: y :: t) = ((x + y != 0) && isReduced (y :: t)) := rfl

theorem isReduced_tail (y : Int) (r : Word) (h : isReduced (y :: r) = true) :
    isReduced r = true := by
  cases r with
  | nil => rfl
  | cons z t =>
    rw [isReduced_cons_cons] at h
    exact (Bool.and_eq_true _ _ ▸ h).2

theorem isReduced_consRed (x : Int) (u : Word) (h : isReduced u = true) :
    isReduced (consRed x u) = true := by
  cases u with
  | nil => rfl
  | cons y r =>
    by_cases hxy : x + y = 0
    · rw [consRed, if_pos hxy]
      exact isReduced_tail y r h
    · rw [consRed, if_neg hxy, isReduced_cons_cons]
      refine Bool.and_eq_true _ _ ▸ ⟨?_, h⟩
      simpa only [bne_iff_ne, ne_eq] using hxy

/-- The checker's specification: reduction really reduces. Without this the checker's
verdict would be a wish rather than a fact. -/
theorem isReduced_reduceWord (w : Word) : isReduced (reduceWord w) = true := by
  induction w with
  | nil => rfl
  | cons x t ih => exact isReduced_consRed x (reduceWord t) ih

/-- The frame generator: the cotree edge that closes the Gray cycle, so the loop that
is the complete recognition window. The census measured all ninety six Hamiltonian
walks as a single class under gauge, which is what lets this loop supply an orientation
reference without contributing content of its own. -/
def frameGen : Int := 2

/-- The total checker. An utterance is well formed when every loop is a reduced word
and the frame loop is present. Both conditions are decidable in linear time. -/
def wellFormed (c : Config) : Bool :=
  c.all isReduced && c.contains [frameGen]

-- ---------------------------------------------------------------------------
-- two by two matrices over ZMod 3, by components
-- ---------------------------------------------------------------------------

/-- Components rather than `Matrix`, because a later module evaluates several thousand
products inside the kernel and `Finset.sum` does not reduce cheaply. -/
structure Mat where
  a : ZMod 3
  b : ZMod 3
  c : ZMod 3
  d : ZMod 3
deriving DecidableEq, Repr

namespace Mat

theorem eq_of (X Y : Mat) (ha : X.a = Y.a) (hb : X.b = Y.b) (hc : X.c = Y.c)
    (hd : X.d = Y.d) : X = Y := by
  cases X
  cases Y
  subst ha
  subst hb
  subst hc
  subst hd
  rfl

def one : Mat := ⟨1, 0, 0, 1⟩

def mul (X Y : Mat) : Mat :=
  ⟨X.a * Y.a + X.b * Y.c, X.a * Y.b + X.b * Y.d,
   X.c * Y.a + X.d * Y.c, X.c * Y.b + X.d * Y.d⟩

def det (X : Mat) : ZMod 3 := X.a * X.d - X.b * X.c

/-- The adjugate. It is a total function, and it is the inverse exactly when the
determinant is one, which is the case for every matrix this module evaluates. -/
def adj (X : Mat) : Mat := ⟨X.d, -X.b, -X.c, X.a⟩

def tr (X : Mat) : ZMod 3 := X.a + X.d

/-- The trace as a natural number, so invariants are lists of `Nat` and can be sorted
by a hand rolled comparison that no library change can move. -/
def trN (X : Mat) : Nat := (tr X).val

theorem mul_assoc' (X Y Z : Mat) : mul (mul X Y) Z = mul X (mul Y Z) := by
  cases X; cases Y; cases Z
  refine eq_of _ _ ?_ ?_ ?_ ?_ <;> simp only [mul] <;> ring

theorem one_mul' (X : Mat) : mul one X = X := by
  cases X
  refine eq_of _ _ ?_ ?_ ?_ ?_ <;> simp only [mul, one] <;> ring

theorem mul_one' (X : Mat) : mul X one = X := by
  cases X
  refine eq_of _ _ ?_ ?_ ?_ ?_ <;> simp only [mul, one] <;> ring

instance : Mul Mat := ⟨mul⟩
instance : One Mat := ⟨one⟩

instance : Monoid Mat where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'

theorem mul_def (X Y : Mat) : X * Y = mul X Y := rfl
theorem one_def : (1 : Mat) = one := rfl

theorem det_mul (X Y : Mat) : det (X * Y) = det X * det Y := by
  cases X; cases Y
  simp only [mul_def, mul, det]
  ring

theorem det_one : det (1 : Mat) = 1 := by
  simp only [one_def, one, det]
  ring

/-- An identity for two by two matrices over any commutative ring, with no
determinant hypothesis. This is the lemma that makes the conjugation argument short:
without it the components blow up and nothing closes. -/
theorem adj_mul (X Y : Mat) : adj (X * Y) = adj Y * adj X := by
  cases X; cases Y
  refine eq_of _ _ ?_ ?_ ?_ ?_ <;> simp only [mul_def, mul, adj] <;> ring

theorem adj_adj (X : Mat) : adj (adj X) = X := by
  cases X
  refine eq_of _ _ ?_ ?_ ?_ ?_ <;> simp only [adj] <;> ring

theorem tr_adj (X : Mat) : tr (adj X) = tr X := by
  cases X
  simp only [adj, tr]
  ring

theorem tr_mul_comm (X Y : Mat) : tr (X * Y) = tr (Y * X) := by
  cases X; cases Y
  simp only [mul_def, mul, tr]
  ring

theorem mul_adj_of_det_one (X : Mat) (h : det X = 1) : X * adj X = 1 := by
  cases X
  simp only [det] at h
  refine eq_of _ _ ?_ ?_ ?_ ?_ <;> simp only [mul_def, mul, adj, one_def, one]
  · linear_combination h
  · ring
  · ring
  · linear_combination h

theorem adj_mul_of_det_one (X : Mat) (h : det X = 1) : adj X * X = 1 := by
  cases X
  simp only [det] at h
  refine eq_of _ _ ?_ ?_ ?_ ?_ <;> simp only [mul_def, mul, adj, one_def, one]
  · linear_combination h
  · ring
  · ring
  · linear_combination h

/-- Moving the basepoint: conjugation by a matrix of determinant one. -/
def cj (G X : Mat) : Mat := G * X * adj G

/-- Conjugation commutes with the adjugate, with no hypothesis at all, because
`adj_mul` and `adj_adj` are identities. -/
theorem adj_cj (G X : Mat) : adj (cj G X) = cj G (adj X) := by
  simp only [cj, adj_mul, adj_adj, mul_assoc]

theorem adj_one : adj (1 : Mat) = 1 := by decide

theorem cj_mul (G X Y : Mat) (h : det G = 1) : cj G X * cj G Y = cj G (X * Y) := by
  have hGG : adj G * G = 1 := adj_mul_of_det_one G h
  simp only [cj, mul_assoc]
  rw [← mul_assoc (adj G) G, hGG, one_mul]


theorem tr_cj (G X : Mat) (h : det G = 1) : tr (cj G X) = tr X := by
  have hGG : adj G * G = 1 := adj_mul_of_det_one G h
  calc tr (cj G X) = tr (G * (X * adj G)) := by simp only [cj, mul_assoc]
    _ = tr (X * adj G * G) := tr_mul_comm _ _
    _ = tr (X * (adj G * G)) := by simp only [mul_assoc]
    _ = tr X := by rw [hGG, mul_one]

/-- The commutator of two loop images: the depth two coordinate. An abelianised
reading is blind to this by construction, which is why it is here. -/
def comm (X Y : Mat) : Mat := X * Y * (adj X * adj Y)

theorem comm_cj (G X Y : Mat) (h : det G = 1) :
    comm (cj G X) (cj G Y) = cj G (comm X Y) := by
  simp only [comm, adj_cj]
  rw [cj_mul G X Y h, cj_mul G (adj X) (adj Y) h, cj_mul G (X * Y) (adj X * adj Y) h]

theorem det_adj (X : Mat) : det (adj X) = det X := by
  cases X
  simp only [adj, det]
  ring

/-- The commutator trace is symmetric in its two loops, with no hypothesis. For two by
two matrices `tr (X * adj Y) = det (X + Y) - det X - det Y`, which is symmetric, and
that is what makes the invariant blind to the ORDER of the loops. Without this the
invariant would be reading the order in which loops happened to be listed, which is
not content. -/
theorem tr_comm_symm (X Y : Mat) : tr (comm X Y) = tr (comm Y X) := by
  cases X
  cases Y
  simp only [comm, mul_def, mul, adj, tr]
  ring

theorem trN_comm_symm (X Y : Mat) : trN (comm X Y) = trN (comm Y X) := by
  simp only [trN, tr_comm_symm]

/-- Reversing every loop at once cannot be seen by any trace, because in this group
the inverse is the adjugate. The gate takes the hostile position that reversal IS
gauge, and this theorem is why that position costs nothing. -/
theorem trN_comm_adj (X Y : Mat) : trN (comm (adj X) (adj Y)) = trN (comm X Y) := by
  have h1 : comm (adj X) (adj Y) = adj (Y * X) * (X * Y) := by
    simp only [comm, adj_adj, adj_mul, mul_assoc]
  have h2 : comm X Y = X * Y * adj (Y * X) := by
    simp only [comm, adj_mul, mul_assoc]
  simp only [trN, h1, h2, tr_mul_comm (adj (Y * X)) (X * Y)]

end Mat

-- ---------------------------------------------------------------------------
-- the homomorphism, given as a table
-- ---------------------------------------------------------------------------

/-- For each generator, the matrix it goes to and the matrix its inverse goes to. -/
abbrev Table := List (Mat × Mat)

def entryOk (e : Mat × Mat) : Bool :=
  (Mat.mul e.1 e.2 == Mat.one) && (Mat.mul e.2 e.1 == Mat.one) &&
  (Mat.det e.1 == 1) && (Mat.det e.2 == 1)

/-- A table defines a homomorphism from the free group exactly when each pair really
is an inverse pair inside the determinant one subgroup. Decidable, so the data can be
checked rather than trusted. -/
def Table.ok (T : Table) : Bool := T.all entryOk

def matAt : Table → Nat → Mat × Mat
  | [], _ => (Mat.one, Mat.one)
  | e :: _, 0 => e
  | _ :: t, (n + 1) => matAt t n

theorem entryOk_one : entryOk (Mat.one, Mat.one) = true := by decide

theorem entryOk_matAt (T : Table) (hT : Table.ok T = true) (n : Nat) :
    entryOk (matAt T n) = true := by
  induction T generalizing n with
  | nil => simpa only [matAt] using entryOk_one
  | cons e t ih =>
    simp only [Table.ok, List.all_cons, Bool.and_eq_true] at hT
    cases n with
    | zero => simpa only [matAt] using hT.1
    | succ m => exact ih (by simpa only [Table.ok] using hT.2) m

def letterMat (T : Table) (x : Int) : Mat :=
  if 0 < x then (matAt T (x.natAbs - 1)).1
  else if x < 0 then (matAt T (x.natAbs - 1)).2
  else Mat.one

theorem det_letterMat (T : Table) (hT : Table.ok T = true) (x : Int) :
    Mat.det (letterMat T x) = 1 := by
  have h := entryOk_matAt T hT (x.natAbs - 1)
  simp only [entryOk, Bool.and_eq_true, beq_iff_eq] at h
  simp only [letterMat]
  by_cases hx : 0 < x
  · simp only [hx, if_pos]
    exact h.1.2
  · simp only [hx, if_neg]
    by_cases hx' : x < 0
    · simp only [hx', if_pos]
      exact h.2
    · simp only [hx', if_neg]
      exact Mat.det_one

theorem letterMat_mul_neg (T : Table) (hT : Table.ok T = true) (x : Int) :
    letterMat T x * letterMat T (-x) = 1 := by
  have h := entryOk_matAt T hT (x.natAbs - 1)
  simp only [entryOk, Bool.and_eq_true, beq_iff_eq] at h
  have habs : (-x).natAbs = x.natAbs := Int.natAbs_neg x
  simp only [letterMat, habs]
  by_cases hx : 0 < x
  · have hneg : ¬ (0 < -x) := by omega
    have hneg' : -x < 0 := by omega
    simp only [hx, if_pos, hneg, if_neg, hneg', if_pos, Mat.mul_def]
    exact h.1.1.1
  · by_cases hx' : x < 0
    · have hneg : (0 : Int) < -x := by omega
      simp only [hx, if_neg, hx', if_pos, hneg, if_pos, Mat.mul_def]
      exact h.1.1.2
    · have hx0 : x = 0 := by omega
      subst hx0
      simp only [Mat.mul_def]
      norm_num
      exact Mat.mul_one' Mat.one

/-- The image of a word. Structural on the head, so appending is an easy induction. -/
def evalWord (T : Table) : Word → Mat
  | [] => 1
  | x :: t => letterMat T x * evalWord T t

def evalConfig (T : Table) (c : Config) : List Mat := c.map (evalWord T)

theorem evalWord_cons (T : Table) (x : Int) (t : Word) :
    evalWord T (x :: t) = letterMat T x * evalWord T t := rfl

theorem evalWord_singleton (T : Table) (x : Int) : evalWord T [x] = letterMat T x := by
  simp only [evalWord, mul_one]

theorem evalWord_append (T : Table) (u v : Word) :
    evalWord T (u ++ v) = evalWord T u * evalWord T v := by
  induction u with
  | nil => simp only [List.nil_append, evalWord, one_mul]
  | cons x t ih => simp only [List.cons_append, evalWord, ih, mul_assoc]

theorem det_evalWord (T : Table) (hT : Table.ok T = true) (w : Word) :
    Mat.det (evalWord T w) = 1 := by
  induction w with
  | nil => simpa only [evalWord] using Mat.det_one
  | cons x t ih =>
    simp only [evalWord, Mat.det_mul, ih, det_letterMat T hT x, one_mul]

/-- One letter's inverse image is its adjugate. This is the only place the determinant
one hypothesis is really used. -/
theorem letterMat_neg (T : Table) (hT : Table.ok T = true) (x : Int) :
    letterMat T (-x) = Mat.adj (letterMat T x) := by
  have hx : Mat.det (letterMat T x) = 1 := det_letterMat T hT x
  have h := letterMat_mul_neg T hT x
  calc letterMat T (-x) = 1 * letterMat T (-x) := (one_mul _).symm
    _ = Mat.adj (letterMat T x) * letterMat T x * letterMat T (-x) := by
        rw [Mat.adj_mul_of_det_one _ hx]
    _ = Mat.adj (letterMat T x) * (letterMat T x * letterMat T (-x)) := by
        rw [mul_assoc]
    _ = Mat.adj (letterMat T x) := by rw [h, mul_one]

theorem evalWord_invWord (T : Table) (hT : Table.ok T = true) (w : Word) :
    evalWord T (invWord w) = Mat.adj (evalWord T w) := by
  induction w with
  | nil => simp only [invWord, evalWord, Mat.adj_one]
  | cons x t ih =>
    rw [invWord_cons, evalWord_append, ih, evalWord_singleton,
      letterMat_neg T hT x, evalWord_cons, Mat.adj_mul]

theorem evalWord_consRed (T : Table) (hT : Table.ok T = true) (x : Int) (u : Word) :
    evalWord T (consRed x u) = letterMat T x * evalWord T u := by
  cases u with
  | nil => rw [consRed, evalWord_singleton, evalWord, mul_one]
  | cons y r =>
    by_cases hxy : x + y = 0
    · have hy : y = -x := by omega
      subst hy
      rw [consRed, if_pos hxy, evalWord_cons, ← mul_assoc,
        letterMat_mul_neg T hT x, one_mul]
    · rw [consRed, if_neg hxy]
      exact evalWord_cons T x (y :: r)

theorem evalWord_reduceWord (T : Table) (hT : Table.ok T = true) (w : Word) :
    evalWord T (reduceWord w) = evalWord T w := by
  induction w with
  | nil => rfl
  | cons x t ih =>
    rw [reduceWord_cons, evalWord_consRed T hT, ih, evalWord_cons]

-- ---------------------------------------------------------------------------
-- relabelling the generators: the automorphism half of the gauge group
-- ---------------------------------------------------------------------------

/-- An automorphism of the recognition window acts on the five generators by sending
each to a word. A relabelling is that data. -/
abbrev Subst := List Word

def getWord : Subst → Nat → Word
  | [], _ => []
  | g :: _, 0 => g
  | _ :: t, (n + 1) => getWord t n

def substLetter (σ : Subst) (x : Int) : Word :=
  if 0 < x then getWord σ (x.natAbs - 1)
  else if x < 0 then invWord (getWord σ (x.natAbs - 1))
  else []

def substWord (σ : Subst) : Word → Word
  | [] => []
  | x :: t => substLetter σ x ++ substWord σ t

theorem substWord_cons (σ : Subst) (x : Int) (t : Word) :
    substWord σ (x :: t) = substLetter σ x ++ substWord σ t := rfl

def substConfig (σ : Subst) (c : Config) : Config := c.map (substWord σ)

/-- Pushing a relabelling through a homomorphism gives another homomorphism, and this
computes it. Because Lean builds this itself from the relabelling, the composite
tables are not trusted data. -/
def tableOfSubst (T : Table) (σ : Subst) : Table :=
  σ.map (fun g => (evalWord T g, evalWord T (invWord g)))

theorem ok_tableOfSubst (T : Table) (hT : Table.ok T = true) (σ : Subst) :
    Table.ok (tableOfSubst T σ) = true := by
  simp only [Table.ok, List.all_eq_true, tableOfSubst, List.mem_map]
  rintro e ⟨g, -, rfl⟩
  have hM : Mat.det (evalWord T g) = 1 := det_evalWord T hT g
  have hinv : evalWord T (invWord g) = Mat.adj (evalWord T g) := evalWord_invWord T hT g
  have h1 : Mat.mul (evalWord T g) (evalWord T (invWord g)) = Mat.one := by
    rw [hinv, ← Mat.mul_def, Mat.mul_adj_of_det_one _ hM, Mat.one_def]
  have h2 : Mat.mul (evalWord T (invWord g)) (evalWord T g) = Mat.one := by
    rw [hinv, ← Mat.mul_def, Mat.adj_mul_of_det_one _ hM, Mat.one_def]
  have h3 : Mat.det (evalWord T (invWord g)) = 1 := by
    rw [hinv, Mat.det_adj]; exact hM
  simp only [entryOk, h1, h2, h3, hM, beq_self_eq_true, Bool.and_self]

theorem matAt_tableOfSubst (T : Table) (σ : Subst) (n : Nat) :
    matAt (tableOfSubst T σ) n
      = (evalWord T (getWord σ n), evalWord T (invWord (getWord σ n))) := by
  induction σ generalizing n with
  | nil => cases n with
    | zero => rfl
    | succ m => rfl
  | cons g t ih => cases n with
    | zero => rfl
    | succ m => exact ih m

theorem evalWord_substLetter (T : Table) (σ : Subst) (x : Int) :
    evalWord T (substLetter σ x) = letterMat (tableOfSubst T σ) x := by
  rw [substLetter, letterMat, matAt_tableOfSubst]
  by_cases hx : 0 < x
  · rw [if_pos hx, if_pos hx]
  · rw [if_neg hx, if_neg hx]
    by_cases hx' : x < 0
    · rw [if_pos hx', if_pos hx']
    · rw [if_neg hx', if_neg hx']
      rfl

/-- Reading a relabelled utterance under a homomorphism is reading the original
utterance under the relabelled homomorphism. This is what lets the forty eight
automorphisms of the window be checked by changing the table rather than by rewriting
every word, and it is a theorem rather than an assumption. -/
theorem evalWord_substWord (T : Table) (σ : Subst) (w : Word) :
    evalWord T (substWord σ w) = evalWord (tableOfSubst T σ) w := by
  induction w with
  | nil => rfl
  | cons x t ih =>
    rw [substWord_cons, evalWord_append, ih, evalWord_substLetter, evalWord_cons]

-- ---------------------------------------------------------------------------
-- the invariant
-- ---------------------------------------------------------------------------

def insertNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: t => if x ≤ y then x :: y :: t else y :: insertNat x t

/-- Hand rolled, so no library rename can silently change what the invariant is. -/
def sortNat : List Nat → List Nat
  | [] => []
  | x :: t => insertNat x (sortNat t)

/-- Traces of the pairwise commutators, over index pairs in order. Because both sides
of every theorem below build this list in the same order, no permutation reasoning is
needed anywhere. -/
def pairTraces : List Mat → List Nat
  | [] => []
  | M :: rest => rest.map (fun N => Mat.trN (Mat.comm M N)) ++ pairTraces rest

/-- Depth one and depth two, together. The first component is what an amplitude style
reading can see and the second is what it cannot. -/
def invariantOf (Ms : List Mat) : List Nat × List Nat :=
  (sortNat (Ms.map Mat.trN), sortNat (pairTraces Ms))

def invariant (T : Table) (c : Config) : List Nat × List Nat :=
  invariantOf (evalConfig T c)

-- ---------------------------------------------------------------------------
-- the sort is honest: the invariant reads a multiset, not a list
-- ---------------------------------------------------------------------------

theorem insertNat_perm (x : Nat) (l : List Nat) :
    List.Perm (insertNat x l) (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y t ih =>
    by_cases h : x ≤ y
    · rw [insertNat, if_pos h]
    · rw [insertNat, if_neg h]
      exact (List.Perm.cons y ih).trans (List.Perm.swap x y t)

theorem sortNat_perm (l : List Nat) : List.Perm (sortNat l) l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x t ih => exact (insertNat_perm x (sortNat t)).trans (List.Perm.cons x ih)

theorem pairwise_insertNat (x : Nat) (l : List Nat) (h : l.Pairwise (· ≤ ·)) :
    (insertNat x l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp only [insertNat, List.pairwise_cons, List.not_mem_nil, false_implies,
      implies_true, List.Pairwise.nil, and_self]
  | cons y t ih =>
    rw [List.pairwise_cons] at h
    by_cases hxy : x ≤ y
    · rw [insertNat, if_pos hxy, List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr h⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hxy
      · exact le_trans hxy (h.1 b hb)
    · rw [insertNat, if_neg hxy, List.pairwise_cons]
      refine ⟨?_, ih h.2⟩
      intro b hb
      rcases List.mem_cons.mp ((insertNat_perm x t).mem_iff.mp hb) with rfl | hb
      · exact le_of_not_le hxy
      · exact h.1 b hb

theorem pairwise_sortNat (l : List Nat) : (sortNat l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x t ih => exact pairwise_insertNat x (sortNat t) ih

theorem sortNat_eq_of_perm {l₁ l₂ : List Nat} (h : List.Perm l₁ l₂) :
    sortNat l₁ = sortNat l₂ :=
  List.Perm.eq_of_pairwise'
    (pairwise_sortNat l₁) (pairwise_sortNat l₂)
    ((sortNat_perm l₁).trans (h.trans (sortNat_perm l₂).symm))

theorem perm_append_left_comm (A B P : List Nat) :
    List.Perm (A ++ (B ++ P)) (B ++ (A ++ P)) := by
  rw [← List.append_assoc A B P, ← List.append_assoc B A P]
  exact List.Perm.append_right P List.perm_append_comm

/-- The pairwise commutator traces of a reordered utterance are the same multiset. The
swap case is where the symmetry of the commutator trace is spent. -/
theorem pairTraces_perm {Ms Ns : List Mat} (h : List.Perm Ms Ns) :
    List.Perm (pairTraces Ms) (pairTraces Ns) := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons M h ih =>
    simp only [pairTraces]
    exact List.Perm.append (h.map _) ih
  | swap M N l =>
    simp only [pairTraces, List.map_cons, List.cons_append]
    rw [Mat.trN_comm_symm N M]
    exact List.Perm.cons _ (perm_append_left_comm _ _ _)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- SOUNDNESS, the multiset half. An utterance is a multiset of loops, and the
invariant reads it as one: no ordering of the loops is content. -/
theorem invariantOf_perm {Ms Ns : List Mat} (h : List.Perm Ms Ns) :
    invariantOf Ms = invariantOf Ns := by
  simp only [invariantOf, sortNat_eq_of_perm (h.map Mat.trN),
    sortNat_eq_of_perm (pairTraces_perm h)]

theorem invariant_perm (T : Table) {c d : Config} (h : List.Perm c d) :
    invariant T c = invariant T d :=
  invariantOf_perm (h.map (evalWord T))

/-- THE SOUNDNESS THEOREM. There is no first word: moving the basepoint of the whole
utterance leaves the invariant alone. -/
theorem invariantOf_cj (G : Mat) (h : Mat.det G = 1) (Ms : List Mat) :
    invariantOf (Ms.map (Mat.cj G)) = invariantOf Ms := by
  have hloops : (Ms.map (Mat.cj G)).map Mat.trN = Ms.map Mat.trN := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro M _
    simp only [Function.comp_apply, Mat.trN, Mat.tr_cj G M h]
  have hpairs : ∀ Ns : List Mat, pairTraces (Ns.map (Mat.cj G)) = pairTraces Ns := by
    intro Ns
    induction Ns with
    | nil => simp only [List.map_nil, pairTraces]
    | cons M rest ih =>
      simp only [List.map_cons, pairTraces, ih]
      congr 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro N _
      simp only [Function.comp_apply, Mat.comm_cj G M N h, Mat.trN, Mat.tr_cj _ _ h]
  simp only [invariantOf, hloops, hpairs]

/-- Reversing every loop at once is invisible too, and this one needs no hypothesis:
in the determinant one subgroup the inverse is the adjugate, and no trace can see an
adjugate. So the gate's hostile choice, putting time reversal into the gauge group,
costs the carrier nothing. -/
theorem invariantOf_adj (Ms : List Mat) :
    invariantOf (Ms.map Mat.adj) = invariantOf Ms := by
  have hloops : (Ms.map Mat.adj).map Mat.trN = Ms.map Mat.trN := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro M _
    simp only [Function.comp_apply, Mat.trN, Mat.tr_adj]
  have hpairs : ∀ Ns : List Mat, pairTraces (Ns.map Mat.adj) = pairTraces Ns := by
    intro Ns
    induction Ns with
    | nil => simp only [List.map_nil, pairTraces]
    | cons M rest ih =>
      simp only [List.map_cons, pairTraces, ih]
      congr 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro N _
      simp only [Function.comp_apply, Mat.trN_comm_adj]
  simp only [invariantOf, hloops, hpairs]

/-- Moving one loop's basepoint is conjugating its image. -/
theorem evalWord_conjWord (T : Table) (hT : Table.ok T = true) (g w : Word) :
    evalWord T (conjWord g w) = Mat.cj (evalWord T g) (evalWord T w) := by
  simp only [conjWord, evalWord_reduceWord T hT, evalWord_append,
    evalWord_invWord T hT, Mat.cj, mul_assoc]

/-- Nesting is invisible at depth one. A loop that sits inside a binder is a CONJUGATE
of the same loop outside it, and a trace cannot see a conjugation, which is exactly why
the invariant has to read the commutators as well. -/
theorem trN_conjWord (T : Table) (hT : Table.ok T = true) (g w : Word) :
    Mat.trN (evalWord T (conjWord g w)) = Mat.trN (evalWord T w) := by
  rw [evalWord_conjWord T hT]
  simp only [Mat.trN, Mat.tr_cj _ _ (det_evalWord T hT g)]

/-- The two soundness statements as one fact about utterances: respelling every loop
and moving the shared basepoint leave the invariant alone. -/
theorem invariant_conjWord (T : Table) (hT : Table.ok T = true) (g : Word)
    (c : Config) : invariant T (c.map (conjWord g)) = invariant T c := by
  have hev : ∀ w : Word, evalWord T (conjWord g w)
      = Mat.cj (evalWord T g) (evalWord T w) := evalWord_conjWord T hT g
  have hmap : evalConfig T (c.map (conjWord g))
      = (evalConfig T c).map (Mat.cj (evalWord T g)) := by
    simp only [evalConfig, List.map_map]
    apply List.map_congr_left
    intro w _
    simp only [Function.comp_apply, hev w]
  simp only [invariant, hmap,
    invariantOf_cj (evalWord T g) (det_evalWord T hT g) (evalConfig T c)]

/-- Reversing every loop of an utterance at once leaves the invariant alone. -/
theorem invariant_map_invWord (T : Table) (hT : Table.ok T = true) (c : Config) :
    invariant T (c.map invWord) = invariant T c := by
  have hmap : evalConfig T (c.map invWord) = (evalConfig T c).map Mat.adj := by
    simp only [evalConfig, List.map_map]
    apply List.map_congr_left
    intro w _
    simp only [Function.comp_apply, evalWord_invWord T hT w]
  simp only [invariant, hmap, invariantOf_adj]

/-- SOUNDNESS, the relabelling half. Reading a relabelled utterance is reading the
original one under the relabelled homomorphism, so the forty eight automorphisms of the
window are checked by forty eight tables and no word is rewritten. -/
theorem invariant_substConfig (T : Table) (σ : Subst) (c : Config) :
    invariant T (substConfig σ c) = invariant (tableOfSubst T σ) c := by
  have h : evalConfig T (substConfig σ c) = evalConfig (tableOfSubst T σ) c := by
    simp only [evalConfig, substConfig, List.map_map]
    apply List.map_congr_left
    intro w _
    simp only [Function.comp_apply, evalWord_substWord]
  simp only [invariant, h]

-- ---------------------------------------------------------------------------
-- the checker, at the level of an utterance
-- ---------------------------------------------------------------------------

/-- Freely reduce every loop. Total, linear in the size of the utterance. -/
def reduceConfig (c : Config) : Config := c.map reduceWord

theorem all_isReduced_reduceConfig (c : Config) :
    (reduceConfig c).all isReduced = true := by
  simp only [reduceConfig, List.all_eq_true, List.mem_map]
  rintro w ⟨v, -, rfl⟩
  exact isReduced_reduceWord v

/-- The checker accepts every framed, normalised utterance. This is the checker's
specification: it never rejects an honest utterance, and by `isReduced_reduceWord` its
verdict is a fact about the words rather than a wish. -/
theorem wellFormed_reduceConfig_frame (c : Config) :
    wellFormed (reduceConfig ([frameGen] :: c)) = true := by
  have h : reduceConfig ([frameGen] :: c) = [frameGen] :: reduceConfig c := rfl
  rw [wellFormed, h]
  refine Bool.and_eq_true _ _ ▸ ⟨?_, ?_⟩
  · rw [List.all_cons, all_isReduced_reduceConfig]
    rfl
  · simp

/-- Spelling is not content: normalising the loops leaves the invariant alone. -/
theorem invariant_reduceConfig (T : Table) (hT : Table.ok T = true) (c : Config) :
    invariant T (reduceConfig c) = invariant T c := by
  have h : evalConfig T (reduceConfig c) = evalConfig T c := by
    simp only [evalConfig, reduceConfig, List.map_map]
    apply List.map_congr_left
    intro w _
    simp only [Function.comp_apply, evalWord_reduceWord T hT]
  simp only [invariant, h]

-- ---------------------------------------------------------------------------
-- the depth one reading, for comparison
-- ---------------------------------------------------------------------------

/-- Exponent sums: the abelianisation, which is the unique canonical quotient and the
reading that a bag of faces performs. -/
def abel (w : Word) : List Int :=
  (List.range 5).map (fun i =>
    (w.filter (fun x => x = (i + 1 : Int))).length -
      (w.filter (fun x => x = -(i + 1 : Int))).length)

def leLexInt : List Int → List Int → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else leLexInt xs ys

def insertLex (v : List Int) : List (List Int) → List (List Int)
  | [] => [v]
  | u :: t => if leLexInt v u then v :: u :: t else u :: insertLex v t

def sortLex : List (List Int) → List (List Int)
  | [] => []
  | v :: t => insertLex v (sortLex t)

/-- The depth one reading of an utterance: the multiset of abelianised loops. -/
def abelBag (c : Config) : List (List Int) := sortLex (c.map abel)

#print axioms isReduced_reduceWord
#print axioms wellFormed_reduceConfig_frame
#print axioms invariantOf_perm
#print axioms invariant_conjWord
#print axioms invariant_map_invWord
#print axioms invariant_substConfig
#print axioms invariant_reduceConfig

end Loom
end IndisputableMonolith
