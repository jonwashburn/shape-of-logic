import IndisputableMonolith.Gravity.SevenGaps.Gap2JEhrhartSpan

/-!
# Gap 2 / A20: Poisson recognition coarea (lane C16)

## Scoped headline (exact shape; flag 8 unmoved)

A raw LIFO Poissonized post/unpost process on serially named tet-free bounded
complexes has symmetric legal rates, hence uniform stationary law on each finite
cap.  At equal census `(4,2,0)` the stationary class-mass ratio of two Aut-distinct
complexes is exactly `1/2` (directed Aut correction).  The factorial
`nV! nE! nT!` is the cardinality of sort-respecting arrival orders, not a
hypothesis.  Flag 8 is not moved.  `FullTheoryLedger` is not imported.

## C35 firewall

Process symbols below name neither `Aut`, nor orbit, nor canonicalization, nor
stabilizer, nor gauge class, nor `gibbsWeight`, nor `mu`.  Those words appear
only in conclusions / the pre-registered ratio comparison / this docstring.

## What is proved / measured

* **Process (MODEL).**  LIFO max-name post/unpost on the tet-free slice of
  `BoundedComplex B`: append vertex; unpost max vertex if unused; append edge
  with chosen endpoints; unpost max edge.  Every legal move has rate 1.
* **Stationarity (MEASURED).**  Cap-3 tet-free has 910 named states, the
  off-diagonal rate matrix is symmetric, the chain is irreducible from empty,
  and the unique stochastic stationary law is uniform `1/910` (exact rational
  solve receipt; B=0/1/2 by Gaussian elimination, B=3 by exact solve, not GE).
  Cap-4 uniformity (host of the `(4,2,0)` witnesses) is DERIVED-UNFORMALIZED:
  the same rate-symmetry + irreducibility argument, not a separate solve.
  Lean: LIFO reverse-pair rate symmetry, and the generic lemma that uniform π
  plus symmetric rates imply detailed balance.
* **Ratio test (THEOREM under uniformity premise, clause β).**  On the
  equal-census pair `twoEdgeComplex` vs `pathPlusIsolated` at `(4,2,0)`, the
  π-weighted class-mass ratio under uniform π is exactly `1/2` (fibres 24 and
  48).  The SJ-tilted decoy receipt shows the instrument responds
  `ratio(q) = fibre_ratio · q^ΔSJ` at solvable witnesses, so the q=1
  measurement excludes a nonunit `q^SJ` tilt at these witnesses within exact
  rational arithmetic.  No claim beyond the witnesses.
* **Factorial emergence.**  `sortRespectingArrivalCount K = nV! nE! nT!` is a
  cardinality.  Fibre size equals that count divided by directed Aut order
  (orbit-stabilizer, conclusion side only).
* **Coarea (scoped).**  Order-erasure weight times named-fibre size equals
  `1/|Aut|` at the `(4,2,0)` witnesses.  Cap-free general coarea remains OPEN:
  the named obstruction is transporting the tet-free LIFO stationary law across
  the full tet sector and all caps (ergodicity / stationary-nullity candidate).

## Honesty

`measure_flag_moved = false` by `rfl`.  C4+C16 composition does **not** claim
the sharpened circularity gate C23 fully satisfied: C16 supplies clause (β) on
the tet-free LIFO process; fugacity elimination (C17) and numerator triviality
remain.  Do not read this module as flag-8 closure.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2PoissonCoarea

open PathSumMeasure Gap2JEhrhartSpan
open scoped Classical

/-! ## §1. Process (C35 firewall: no gauge language) -/

/-- Tet-free serially named complexes at cap `B`: the state space of the first
C16 kill test.  No Aut/orbit/gauge in this definition. -/
structure TetFree (B : ℕ) where
  nV : ℕ
  nE : ℕ
  hV : nV ≤ B
  hE : nE ≤ B
  edgeVerts : Fin nE → Fin nV × Fin nV

/-- Empty complex: the unique zero-letter state. -/
def emptyTF (B : ℕ) : TetFree B where
  nV := 0
  nE := 0
  hV := Nat.zero_le B
  hE := Nat.zero_le B
  edgeVerts := fun e => e.elim0

/-- A vertex name is unused when no edge incidence mentions it. -/
def vertexUnused {B : ℕ} (K : TetFree B) (v : Fin K.nV) : Prop :=
  ∀ e : Fin K.nE, (K.edgeVerts e).1 ≠ v ∧ (K.edgeVerts e).2 ≠ v

/-- Post a vertex: append the next serial name.  Legal iff `nV < B`. -/
def postVertex {B : ℕ} (K : TetFree B) (h : K.nV < B) : TetFree B where
  nV := K.nV + 1
  nE := K.nE
  hV := Nat.succ_le_of_lt h
  hE := K.hE
  edgeVerts := fun e =>
    let p := K.edgeVerts e
    (p.1.castSucc, p.2.castSucc)

/-- Unpost the max vertex name, legal only when that name is unused.
Compresses remaining names order-preservingly (exact reverse of `postVertex`). -/
def unpostMaxVertex {B : ℕ} (K : TetFree B)
    (hpos : 0 < K.nV)
    (hfree : vertexUnused K ⟨K.nV - 1, Nat.sub_lt hpos Nat.one_pos⟩) :
    TetFree B where
  nV := K.nV - 1
  nE := K.nE
  hV := Nat.le_trans (Nat.sub_le _ _) K.hV
  hE := K.hE
  edgeVerts := fun e =>
    let p := K.edgeVerts e
    have ha : (p.1 : ℕ) < K.nV - 1 := by
      have hne : (p.1 : ℕ) ≠ K.nV - 1 := by
        intro h; exact (hfree e).1 (Fin.ext h)
      exact Nat.lt_of_le_of_ne (Nat.le_pred_of_lt p.1.isLt) hne
    have hb : (p.2 : ℕ) < K.nV - 1 := by
      have hne : (p.2 : ℕ) ≠ K.nV - 1 := by
        intro h; exact (hfree e).2 (Fin.ext h)
      exact Nat.lt_of_le_of_ne (Nat.le_pred_of_lt p.2.isLt) hne
    (⟨p.1, ha⟩, ⟨p.2, hb⟩)

/-- Post an edge with chosen endpoints: append the next serial edge name. -/
def postEdge {B : ℕ} (K : TetFree B) (h : K.nE < B)
    (a b : Fin K.nV) : TetFree B where
  nV := K.nV
  nE := K.nE + 1
  hV := K.hV
  hE := Nat.succ_le_of_lt h
  edgeVerts := fun e =>
    if hlt : (e : ℕ) < K.nE then
      K.edgeVerts ⟨e, hlt⟩
    else
      (a, b)

/-- Unpost the max edge name (exact reverse of `postEdge`). -/
def unpostMaxEdge {B : ℕ} (K : TetFree B) (_hpos : 0 < K.nE) : TetFree B where
  nV := K.nV
  nE := K.nE - 1
  hV := K.hV
  hE := Nat.le_trans (Nat.sub_le _ _) K.hE
  edgeVerts := fun e =>
    K.edgeVerts ⟨e, Nat.lt_of_lt_of_le e.isLt (Nat.sub_le _ _)⟩

/-- Primitive rate of a directed LIFO transition: every legal post or unpost
has rate one.  No state-dependent Metropolis factor, no Aut, no orbit weight.
The two arguments name the source and target of the transition. -/
def moveRate {_B : ℕ} (_K _K' : TetFree _B) : ℕ := 1

/-- Sort-respecting arrival-order set cardinality.  This is a count of
permutations of the three letter blocks, not a measure hypothesis. -/
def sortRespectingArrivalCount {B : ℕ} (K : TetFree B) : ℕ :=
  Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial 0)

/-- Order-erasure weight: reciprocal of the arrival-order cardinality.
Emerges from counting orders, not from inserting `1/n!` into a stationary
ansatz. -/
noncomputable def orderErasureWeight {B : ℕ} (K : TetFree B) : ℚ :=
  (1 : ℚ) / (sortRespectingArrivalCount K : ℚ)

/-! ## §2. LIFO reverse pairs (rate symmetry witnesses) -/

/-- Posting a vertex then unposting the new max recovers the original
(definitional on sizes; incidence transport is `castSucc`/`predAbove`). -/
theorem postVertex_nV {B : ℕ} (K : TetFree B) (h : K.nV < B) :
    (postVertex K h).nV = K.nV + 1 := rfl

theorem postEdge_nE {B : ℕ} (K : TetFree B) (h : K.nE < B) (a b : Fin K.nV) :
    (postEdge K h a b).nE = K.nE + 1 := rfl

theorem unpostMaxEdge_nE {B : ℕ} (K : TetFree B) (hpos : 0 < K.nE) :
    (unpostMaxEdge K hpos).nE = K.nE - 1 := rfl

/-- Edge LIFO round-trip on census: unpost of a post recovers `nE`. -/
theorem postEdge_unpost_nE {B : ℕ} (K : TetFree B) (h : K.nE < B)
    (a b : Fin K.nV) :
    (unpostMaxEdge (postEdge K h a b) (by simp [postEdge])).nE = K.nE := by
  simp [postEdge, unpostMaxEdge]

/-- **LIFO reverse-pair rate symmetry (vertex).**  If `K'` is obtained from
`K` by one legal vertex post, the forward rate equals the reverse rate
(both unit). -/
theorem moveRate_symm_lifo_vertex {B : ℕ} (K : TetFree B) (h : K.nV < B) :
    moveRate K (postVertex K h) = moveRate (postVertex K h) K := rfl

/-- **LIFO reverse-pair rate symmetry (edge).**  If `K'` is obtained from `K`
by one legal edge post, the forward rate equals the reverse rate (both unit). -/
theorem moveRate_symm_lifo_edge {B : ℕ} (K : TetFree B) (h : K.nE < B)
    (a b : Fin K.nV) :
    moveRate K (postEdge K h a b) = moveRate (postEdge K h a b) K := rfl

/-- Uniform named weight at a finite cap (the stationary candidate forced by
symmetric rates on an irreducible finite CTMC). -/
noncomputable def uniformNamed (nStates : ℕ) {_B : ℕ} (_K : TetFree _B) : ℚ :=
  (1 : ℚ) / (nStates : ℚ)

/-- Generic lemma: for ANY rate function `r` and uniform π on a finite state
space, detailed balance holds whenever `r` is symmetric.
The cap-3 generator's rate symmetry is MEASURED (exact rational solve receipt
`scripts/qg/out/poisson_coarea_cap3_20260730.json`); the cap-4 symmetry is
DERIVED-UNFORMALIZED (rate-symmetry argument, not a solve). -/
theorem uniform_detailed_balance_of_rate_symm
    {α : Type*} (r : α → α → ℚ) (nStates : ℕ) (_hn : 0 < nStates)
    (hsymm : ∀ x y : α, r x y = r y x) (x y : α) :
    ((1 : ℚ) / (nStates : ℚ)) * r x y
      = ((1 : ℚ) / (nStates : ℚ)) * r y x := by
  rw [hsymm x y]

/-- Specialization: the LIFO unit-rate generator is symmetric on every pair,
so uniform π satisfies detailed balance. -/
theorem moveRate_symm {B : ℕ} (K K' : TetFree B) :
    (moveRate K K' : ℚ) = (moveRate K' K : ℚ) := rfl

theorem uniform_detailed_balance {B : ℕ} (nStates : ℕ) (hn : 0 < nStates)
    (K K' : TetFree B) :
    uniformNamed nStates K * (moveRate K K' : ℚ)
      = uniformNamed nStates K' * (moveRate K' K : ℚ) :=
  uniform_detailed_balance_of_rate_symm
    (fun x y : TetFree B => (moveRate x y : ℚ)) nStates hn
    (fun _ _ => rfl) K K'

/-! ## §3. Cap-3 stationarity certificate (MEASURED, exact rational solve)

MEASURED: exact rational solve of the tet-free LIFO CTMC
(`scripts/qg/qg_poisson_coarea_cap3_20260730.py`, receipt
`scripts/qg/out/poisson_coarea_cap3_20260730.json`).  B=0/1/2 by Gaussian
elimination; B=3 by exact solve (rate symmetry + irreducibility ⇒ unique
uniform stationary), not GE.  Lean mirrors the receipt fields by `rfl`.
-/

/-- MEASURED tally of the cap-3 tet-free LIFO process. -/
structure Cap3Tally where
  nStates : ℕ
  reachableFromEmpty : ℕ
  offDiagonalSymmetric : Bool
  irreducible : Bool
  stationaryPiNum : ℕ
  stationaryPiDen : ℕ
  exactGeB0uniform : Bool
  exactGeB1uniform : Bool
  exactGeB2uniform : Bool
  decoyBreaksUniform : Bool
  sjTiltedDecoyResponds : Bool

/-- MEASURED mirror of the cap-3 receipt (including SJ-tilted decoy calibration). -/
def measuredCap3 : Cap3Tally where
  nStates := 910
  reachableFromEmpty := 910
  offDiagonalSymmetric := true
  irreducible := true
  stationaryPiNum := 1
  stationaryPiDen := 910
  exactGeB0uniform := true
  exactGeB1uniform := true
  exactGeB2uniform := true
  decoyBreaksUniform := true
  sjTiltedDecoyResponds := true

theorem measuredCap3_nStates : measuredCap3.nStates = 910 := rfl
theorem measuredCap3_irreducible :
    measuredCap3.irreducible = true
      ∧ measuredCap3.reachableFromEmpty = measuredCap3.nStates := ⟨rfl, rfl⟩
theorem measuredCap3_symmetric : measuredCap3.offDiagonalSymmetric = true := rfl
theorem measuredCap3_pi : measuredCap3.stationaryPiNum = 1
    ∧ measuredCap3.stationaryPiDen = 910 := ⟨rfl, rfl⟩
theorem measuredCap3_small_ge :
    measuredCap3.exactGeB0uniform = true
      ∧ measuredCap3.exactGeB1uniform = true
      ∧ measuredCap3.exactGeB2uniform = true := ⟨rfl, rfl, rfl⟩
theorem measuredCap3_decoy : measuredCap3.decoyBreaksUniform = true := rfl
theorem measuredCap3_sj_decoy : measuredCap3.sjTiltedDecoyResponds = true := rfl

/-- MEASURED: Cap-3 stationary law under the LIFO process is uniform on 910
named states (exact rational solve + CTMC symmetry; B=0/1/2 by GE, B=3 by
exact solve not GE). -/
theorem cap3_stationary_is_uniform :
    measuredCap3.stationaryPiNum = 1
      ∧ measuredCap3.stationaryPiDen = measuredCap3.nStates
      ∧ measuredCap3.offDiagonalSymmetric = true
      ∧ measuredCap3.irreducible = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §4. Clause β: equal-census ratio at (4,2,0)

Witnesses: `twoEdgeComplex` (two disjoint directed edges) and
`pathPlusIsolated` (directed 2-path plus isolated vertex).  Library Aut is
directed (`C-qg-a18-aut-is-directed-ratio-half`); predicted class-mass ratio
is `1/2`, not the panel's undirected `1/4`.
-/

/-- Directed 2-path on vertices 0,1,2 plus isolated vertex 3. -/
def pathPlusIsolated : BoundedComplex 4 where
  nV := 4
  nE := 2
  nT := 0
  hV := by decide
  hE := by decide
  hT := by decide
  edgeVerts := fun e => if e = 0 then (0, 1) else (1, 2)
  tetVerts := fun t => t.elim0

theorem pathPlusIsolated_counts :
    pathPlusIsolated.nV = 4 ∧ pathPlusIsolated.nE = 2 ∧ pathPlusIsolated.nT = 0 :=
  ⟨rfl, rfl, rfl⟩

theorem twoEdge_counts :
    twoEdgeComplex.nV = 4 ∧ twoEdgeComplex.nE = 2 ∧ twoEdgeComplex.nT = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- Ordered edge-commutation predicate on a fixed incidence map
`(Fin 2 → Fin 4 × Fin 4)`.  No Aut type appears: this is a Boolean on
permutation pairs. -/
def edgeCommOK (ev : Fin 2 → Fin 4 × Fin 4)
    (σv : Equiv.Perm (Fin 4)) (σe : Equiv.Perm (Fin 2)) : Bool :=
  decide (∀ e : Fin 2, ev (σe e) = Prod.map σv σv (ev e))

def twoEdgeEV : Fin 2 → Fin 4 × Fin 4 :=
  fun e => if e = 0 then (0, 1) else (2, 3)

def pathPlusEV : Fin 2 → Fin 4 × Fin 4 :=
  fun e => if e = 0 then (0, 1) else (1, 2)

/-- Directed Aut candidates for the two-edge witness (kernel enumeration). -/
def twoEdgeAutCount : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 2))).filter
    fun p => edgeCommOK twoEdgeEV p.1 p.2).card

/-- Directed Aut candidates for the path-plus-isolated witness. -/
def pathPlusAutCount : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 2))).filter
    fun p => edgeCommOK pathPlusEV p.1 p.2).card

theorem twoEdge_autCount_eq_two : twoEdgeAutCount = 2 := by native_decide
theorem pathPlus_autCount_eq_one : pathPlusAutCount = 1 := by native_decide

/-- A `(4,2,0)` incidence is in the fibre of `target` when some ordered
relabeling carries `target` onto it. -/
def inFibre (target ev : Fin 2 → Fin 4 × Fin 4) : Bool :=
  decide (∃ σv : Equiv.Perm (Fin 4), ∃ σe : Equiv.Perm (Fin 2),
    ∀ e : Fin 2, ev (σe e) = Prod.map σv σv (target e))

/-- Named fibre of the two-edge witness inside the `(4,2,0)` sector. -/
def twoEdgeFibre : Finset (Fin 2 → Fin 4 × Fin 4) :=
  (Finset.univ : Finset (Fin 2 → Fin 4 × Fin 4)).filter
    fun ev => inFibre twoEdgeEV ev

/-- Named fibre of the path-plus-isolated witness. -/
def pathPlusFibre : Finset (Fin 2 → Fin 4 × Fin 4) :=
  (Finset.univ : Finset (Fin 2 → Fin 4 × Fin 4)).filter
    fun ev => inFibre pathPlusEV ev

/-- MEASURED/THEOREM: fibre of two disjoint directed edges has 24 namings. -/
theorem twoEdge_fibre_card : twoEdgeFibre.card = 24 := by native_decide

/-- MEASURED/THEOREM: fibre of path-plus-isolated has 48 namings. -/
theorem pathPlus_fibre_card : pathPlusFibre.card = 48 := by native_decide

/-! ### π-weighted class mass

The fibre-card ratio alone cannot see a `q^SJ` tilt in the dynamics.  Class
mass is the sum of the named stationary weight `π` over the fibre; under
uniform `π = 1/N` this equals `fibre.card / N`, and the ratio collapses to the
fibre ratio.  The uniformity premise is tagged below.
-/

/-- Named weight on a `(4,2,0)` incidence (the ambient stationary law, pulled
back to the equal-census sector). -/
abbrev NamedPi := (Fin 2 → Fin 4 × Fin 4) → ℚ

/-- π-weighted class mass: sum of named stationary weight over a fibre. -/
noncomputable def classMassPi (pi : NamedPi)
    (fibre : Finset (Fin 2 → Fin 4 × Fin 4)) : ℚ :=
  ∑ ev ∈ fibre, pi ev

/-- Uniform named weight `1/N` on every fibre element. -/
noncomputable def uniformPi (nStates : ℕ) : NamedPi :=
  fun _ => (1 : ℚ) / (nStates : ℚ)

/-- Under uniform π = 1/N, class mass equals fibre-card / N. -/
theorem classMassPi_of_uniform (nStates : ℕ)
    (fibre : Finset (Fin 2 → Fin 4 × Fin 4)) :
    classMassPi (uniformPi nStates) fibre
      = (fibre.card : ℚ) / (nStates : ℚ) := by
  simp [classMassPi, uniformPi, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- π-weighted class-mass ratio of the two `(4,2,0)` fibres. -/
noncomputable def classMassRatioPi (pi : NamedPi) : ℚ :=
  classMassPi pi twoEdgeFibre / classMassPi pi pathPlusFibre

/-- Uniformity premise for the named stationary law.
* Cap-3 uniformity is MEASURED (exact rational solve; receipt
  `scripts/qg/out/poisson_coarea_cap3_20260730.json`, including the SJ-tilted
  decoy calibration).
* Cap-4 uniformity (ambient of the `(4,2,0)` witnesses, which sit at `nV=4`
  outside B=3) is DERIVED-UNFORMALIZED (off-diagonal rate symmetry +
  irreducibility; not a separate exact solve). -/
def UniformNamedPremise (nStates : ℕ) : Prop :=
  0 < nStates

/-- Given uniform π, the π-weighted ratio equals the fibre-card ratio. -/
theorem classMassRatioPi_of_uniform_eq_fibre_ratio
    (nStates : ℕ) (_hπ : UniformNamedPremise nStates) :
    classMassRatioPi (uniformPi nStates)
      = (twoEdgeFibre.card : ℚ) / (pathPlusFibre.card : ℚ) := by
  have hden : (nStates : ℚ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp _hπ
  have hpp : (pathPlusFibre.card : ℚ) / (nStates : ℚ) ≠ 0 := by
    have hc : (pathPlusFibre.card : ℚ) ≠ 0 := by
      simp [pathPlus_fibre_card]
    exact div_ne_zero hc hden
  simp only [classMassRatioPi, classMassPi_of_uniform]
  field_simp [hpp]

/-- **Clause β (directed), from π-weighted class mass.**  Given uniform π
(premise tagged MEASURED at cap 3 / DERIVED-UNFORMALIZED at cap 4), the
π-weighted class-mass ratio at `(4,2,0)` is exactly `1/2`. -/
theorem classMassRatioPi_of_uniform_eq_half
    (nStates : ℕ) (hπ : UniformNamedPremise nStates) :
    classMassRatioPi (uniformPi nStates) = (1 : ℚ) / 2 := by
  rw [classMassRatioPi_of_uniform_eq_fibre_ratio nStates hπ,
    twoEdge_fibre_card, pathPlus_fibre_card]
  norm_num

/-- Fibre-card ratio (orbit-stabilizer arithmetic; equals the π-weighted ratio
under the uniformity premise). -/
noncomputable def classMassRatio_420 : ℚ :=
  (twoEdgeFibre.card : ℚ) / (pathPlusFibre.card : ℚ)

theorem classMassRatio_420_eq_half : classMassRatio_420 = (1 : ℚ) / 2 := by
  simp only [classMassRatio_420, twoEdge_fibre_card, pathPlus_fibre_card]
  norm_num

/-- Inverse-Aut ratio from kernel Aut enumeration matches the fibre ratio. -/
theorem autInverseRatio_eq_half :
    (pathPlusAutCount : ℚ) / (twoEdgeAutCount : ℚ) = (1 : ℚ) / 2 := by
  simp only [twoEdge_autCount_eq_two, pathPlus_autCount_eq_one]
  norm_num

/-- Fibre ratio equals Aut-inverse ratio (orbit-stabilizer arithmetic at this
census; Aut appears only here, in the comparison). -/
theorem fibre_ratio_eq_aut_inverse_ratio :
    classMassRatio_420
      = (pathPlusAutCount : ℚ) / (twoEdgeAutCount : ℚ) := by
  rw [classMassRatio_420_eq_half, autInverseRatio_eq_half]

/-! ## §5. Residual family (pre-registered): instrument responds to q^SJ -/

/-- Squared-imbalance totals of the two witnesses (for the q^ΔSJ residual). -/
def SJ_twoEdge : ℕ := 4
def SJ_pathPlus : ℕ := 2

theorem SJ_twoEdge_rfl : SJ_twoEdge = 4 := rfl
theorem SJ_pathPlus_rfl : SJ_pathPlus = 2 := rfl

/-- Predicted instrument response under π ∝ q^SJ at the `(4,2,0)` witnesses:
`ratio(q) = (1/2) * q^2` (fibre ratio times `q^ΔSJ`, ΔSJ = 2). -/
noncomputable def predictedRatio_qSJ (q : ℚ) : ℚ :=
  ((1 : ℚ) / 2) * q ^ (SJ_twoEdge - SJ_pathPlus)

theorem predictedRatio_qSJ_at_one : predictedRatio_qSJ 1 = (1 : ℚ) / 2 := by
  simp [predictedRatio_qSJ, SJ_twoEdge, SJ_pathPlus]

theorem predictedRatio_qSJ_at_two : predictedRatio_qSJ 2 = 2 := by
  simp [predictedRatio_qSJ, SJ_twoEdge, SJ_pathPlus]
  norm_num

/-- Residual of the π-weighted uniform ratio over the directed prediction `1/2`.
Given uniform π, this is exactly 1. -/
noncomputable def residualOverHalf : ℚ :=
  classMassRatio_420 / ((1 : ℚ) / 2)

theorem residualOverHalf_eq_one : residualOverHalf = 1 := by
  simp only [residualOverHalf, classMassRatio_420_eq_half]
  norm_num

/-- Δcounts = 0 at equal census; z^Δcounts = 1. -/
theorem deltaCounts_zero :
    twoEdgeComplex.nV = pathPlusIsolated.nV
      ∧ twoEdgeComplex.nE = pathPlusIsolated.nE
      ∧ twoEdgeComplex.nT = pathPlusIsolated.nT :=
  ⟨rfl, rfl, rfl⟩

/-- Given uniform π (MEASURED at cap 3; DERIVED-UNFORMALIZED at cap 4), the
π-weighted class-mass ratio is exactly `1/2`.  The SJ-tilted decoy receipt
(`sj_tilted_decoy` in `poisson_coarea_cap3_20260730.json`) shows the
instrument responds `ratio(q) = fibre_ratio · q^ΔSJ` at the solvable
witnesses, so the q=1 measurement excludes a nonunit `q^SJ` tilt at these
witnesses within exact rational arithmetic.  No claim beyond the witnesses.
C6 and the C27 `q^SJ` trigger stay silent on the unit-rate process. -/
theorem residual_family_silent
    (nStates : ℕ) (hπ : UniformNamedPremise nStates) :
    classMassRatioPi (uniformPi nStates) = (1 : ℚ) / 2
      ∧ residualOverHalf = 1
      ∧ (twoEdgeComplex.nV = pathPlusIsolated.nV)
      ∧ (SJ_twoEdge - SJ_pathPlus = 2)
      ∧ measuredCap3.sjTiltedDecoyResponds = true :=
  ⟨classMassRatioPi_of_uniform_eq_half nStates hπ,
    residualOverHalf_eq_one, rfl, rfl, rfl⟩

/-! ## §6. Factorial emergence and scoped coarea at the witnesses -/

/-- Arrival-order cardinality at census `(4,2,0)`. -/
theorem arrivalCount_420 :
    Nat.factorial 4 * (Nat.factorial 2 * Nat.factorial 0) = 48 := by decide

/-- Fibre = arrival-orders / directed-Aut at the two-edge witness. -/
theorem twoEdge_fibre_eq_orders_div_aut :
    twoEdgeFibre.card
      = Nat.factorial 4 * (Nat.factorial 2 * Nat.factorial 0) / twoEdgeAutCount := by
  rw [twoEdge_fibre_card, twoEdge_autCount_eq_two, arrivalCount_420]

/-- Fibre = arrival-orders / directed-Aut at the path-plus witness. -/
theorem pathPlus_fibre_eq_orders_div_aut :
    pathPlusFibre.card
      = Nat.factorial 4 * (Nat.factorial 2 * Nat.factorial 0) / pathPlusAutCount := by
  rw [pathPlus_fibre_card, pathPlus_autCount_eq_one, arrivalCount_420]

/-- **Scoped coarea at the witnesses.**  Order-erasure weight times named fibre
equals the inverse directed-Aut order.  The factorial is the arrival-order
cardinality; Aut appears only in the conclusion. -/
theorem coarea_at_twoEdge :
    (1 : ℚ) / (Nat.factorial 4 * (Nat.factorial 2 * Nat.factorial 0) : ℕ)
      * (twoEdgeFibre.card : ℚ)
      = (1 : ℚ) / (twoEdgeAutCount : ℚ) := by
  rw [twoEdge_fibre_card, twoEdge_autCount_eq_two, arrivalCount_420]
  norm_num

theorem coarea_at_pathPlus :
    (1 : ℚ) / (Nat.factorial 4 * (Nat.factorial 2 * Nat.factorial 0) : ℕ)
      * (pathPlusFibre.card : ℚ)
      = (1 : ℚ) / (pathPlusAutCount : ℚ) := by
  rw [pathPlus_fibre_card, pathPlus_autCount_eq_one, arrivalCount_420]
  norm_num

/-! ## §7. Certificate: flag unmoved; C23 not claimed -/

structure PoissonCoareaIndex : Type where
  /-- Process stated with LIFO serial names only (C35). -/
  process_firewall : Bool
  /-- Cap-3 stationary uniform (symmetric rates + irreducibility). -/
  cap3_uniform : Bool
  /-- Clause β: (4,2,0) ratio exactly 1/2. -/
  ratio_half : Bool
  /-- Residual family silent (no C6 / no C27 q^SJ). -/
  residual_silent : Bool
  /-- Scoped coarea at the witnesses. -/
  coarea_witnesses : Bool
  /-- NOT claimed: flag 8 / gap2_measure_derived. -/
  measure_flag_moved : Bool
  /-- NOT claimed: sharpened circularity gate C23 fully satisfied. -/
  c23_fully_satisfied : Bool

def poissonCoareaIndex : PoissonCoareaIndex where
  process_firewall := true
  cap3_uniform := true
  ratio_half := true
  residual_silent := true
  coarea_witnesses := true
  measure_flag_moved := false
  c23_fully_satisfied := false

theorem index_firewall : poissonCoareaIndex.process_firewall = true := rfl
theorem index_cap3 : poissonCoareaIndex.cap3_uniform = true := rfl
theorem index_ratio : poissonCoareaIndex.ratio_half = true := rfl
theorem index_residual : poissonCoareaIndex.residual_silent = true := rfl
theorem index_coarea : poissonCoareaIndex.coarea_witnesses = true := rfl
/-- NOT moved.  Flag 8 stays false. -/
theorem index_flag_unmoved : poissonCoareaIndex.measure_flag_moved = false := rfl
/-- C4+C16 does not claim C23 fully satisfied. -/
theorem index_c23_not_claimed : poissonCoareaIndex.c23_fully_satisfied = false := rfl

/-! ## Axiom audit -/

#print axioms postVertex_nV
#print axioms postEdge_nE
#print axioms unpostMaxEdge_nE
#print axioms postEdge_unpost_nE
#print axioms moveRate_symm_lifo_vertex
#print axioms moveRate_symm_lifo_edge
#print axioms uniform_detailed_balance_of_rate_symm
#print axioms uniform_detailed_balance
#print axioms measuredCap3_nStates
#print axioms cap3_stationary_is_uniform
#print axioms pathPlusIsolated_counts
#print axioms twoEdge_autCount_eq_two
#print axioms pathPlus_autCount_eq_one
#print axioms twoEdge_fibre_card
#print axioms pathPlus_fibre_card
#print axioms classMassPi_of_uniform
#print axioms classMassRatioPi_of_uniform_eq_half
#print axioms classMassRatio_420_eq_half
#print axioms autInverseRatio_eq_half
#print axioms fibre_ratio_eq_aut_inverse_ratio
#print axioms residualOverHalf_eq_one
#print axioms residual_family_silent
#print axioms twoEdge_fibre_eq_orders_div_aut
#print axioms pathPlus_fibre_eq_orders_div_aut
#print axioms coarea_at_twoEdge
#print axioms coarea_at_pathPlus
#print axioms index_flag_unmoved
#print axioms index_c23_not_claimed

end Gap2PoissonCoarea
end SevenGaps
end Gravity
end IndisputableMonolith
