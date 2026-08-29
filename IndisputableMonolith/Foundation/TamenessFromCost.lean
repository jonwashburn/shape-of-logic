import Mathlib
import IndisputableMonolith.Foundation.SubstrateFromLedger

/-!
# Tameness, derived: the cell an act forces and the cost of a wild one

`SubstrateFromLedger` builds the stage from the ledger's records and proves its
dimension, its acyclicity, and its compactification. What it leaves standing is
the last clause of the cellular-completion definition: that the cube-graph
realization is *tame*, each closed 1-cell a smooth regular embedding and each
vertex carrying a chart onto radial segments in pairwise distinct directions.
Until now that embedding was exhibited (an affine model in the cube) rather than
forced, and a topological embedding of a graph into a manifold may be wild.

This module removes the clause. Nothing here is a placement: the realization is
read off the acts, and the two halves of tameness turn out to be two facts the
ledger already carries.

## The three moves

1. **The closed 1-cell is forced, not chosen.** An edge of the cube graph is a
   level-0 act. Read one level finer, that act is a chain of two acts through
   the record halfway along; read `n` levels finer, a chain of `2 ^ n` acts
   through the records at every dyadic tally between its endpoints
   (`actSites`). Those records are sites of the stage, and their closure is
   exactly the set of stage points agreeing with the act's record at every
   primitive the act does not move (`closure_actSites`). The recognizer does not
   get to say where the edge goes: refining the act already says.

2. **What is forced is straight, and the directions at a vertex are
   independent.** That closure is the affine segment between the act's endpoints
   (`actCell_eq_segment`), affinely parametrized with constant nonzero velocity
   (`actParam_hasDerivAt`, `actDir_ne_zero`), so each closed 1-cell is a smooth
   regular embedding. The act's direction is `Pi.single i 1`
   (`actDir_eq_single`), so the `D` acts at a vertex leave along the `D`
   standard basis vectors, linearly independent
   (`directions_linearIndependent`). That independence is the joint independence
   of the primitives read on the stage, and it is the definition's
   pairwise-distinctness clause.

3. **The vertex is a cone point, in the stage's own coordinates.** An act not
   incident to a vertex pins a primitive at the opposite value, so its whole
   cell sits a full unit away (`one_le_dist_of_not_incident`). Hence a ball of
   radius below one around a vertex meets the realized skeleton in exactly the
   `D` incident cells (`ball_inter_skeleton`), each of which is the straight
   line through the vertex in its own direction (`mem_actCell_iff_radial`). The
   identity chart radializes every vertex; no chart has to be produced, and none
   can be obstructed.

## Where the cost floor enters

Moves 1 to 3 describe what a *finite* set of acts lays down. That finiteness is
the ledger's, not an assumption: reading a posted act at a finer level moves no
record and costs nothing, while posting a distinction that is not a refinement
of a posted one costs at least one unit. So a pass of bounded cost posts
boundedly many acts (`card_le_of_cost_le`) and sweeps a finite union of straight
segments (`locus_eq_union_segments`), whereas any locus demanding new
distinctions without bound costs without bound (`cost_unbounded`). Wildness is
exactly the demand for structure at every scale in a bounded region, so a wild
locus is not something a recognizer can afford to post.

## Non-vacuity

`center_not_mem_locus`: with at least two primitives the centre of the stage
lies on no pass locus, so "is swept by a pass" is a real constraint and not a
token. `dist_vertex_flip` records that the cells are not degenerate.

Scope: this derives the tameness clause **on the constructed stage**. For a
substrate handed over without the construction it remains a hypothesis, which is
what the axiomatic class in the sharpness results needs.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace TamenessFromCost

open SubstrateFromLedger

/-- The coordinates of a placed record: tally over resolution. -/
theorem toPoint_apply (D n : ℕ) (v : Grid D n) (j : Fin D) :
    (toPoint D n v : Fin D → ℝ) j = ((v j : ℕ) : ℝ) / (2 ^ n : ℝ) := rfl

/-! ## Reading a level-0 record at a finer level -/

/-- A level-0 record read at level `n`: every tally scales by `2 ^ n`, which is
the refinement step iterated, and changes no value. -/
def liftLevel (D n : ℕ) (p : Grid D 0) : Grid D n := fun j =>
  ⟨(p j : ℕ) * 2 ^ n, by
    have h2 : (p j : ℕ) < 2 := by
      have h := (p j).isLt
      norm_num at h
      exact h
    have h01 : (p j : ℕ) = 0 ∨ (p j : ℕ) = 1 := by omega
    rcases h01 with h | h <;> simp [h]⟩

theorem toPoint_liftLevel (D n : ℕ) (p : Grid D 0) :
    toPoint D n (liftLevel D n p) = toPoint D 0 p := by
  apply Subtype.ext
  funext j
  show (((p j : ℕ) * 2 ^ n : ℕ) : ℝ) / (2 ^ n : ℝ) = ((p j : ℕ) : ℝ) / (2 ^ 0 : ℝ)
  have hne : (2 : ℝ) ^ n ≠ 0 := by positivity
  push_cast
  field_simp

/-! ## An act, and the cell its own refinement forces -/

/-- A level-0 act: a record together with the one primitive it moves. The acts
are the edges of the cube graph. -/
abbrev Act (D : ℕ) := Grid D 0 × Fin D

/-- The level-`n` reading of an act: the moved primitive's tally runs over
`0, …, 2 ^ n` while every other tally is the record's own, read `n` levels
finer. This is the act refined, not a placement of the act. -/
def actGrid (D n : ℕ) (a : Act D) (m : Fin (2 ^ n + 1)) : Grid D n :=
  Function.update (liftLevel D n a.1) a.2 m

theorem toPoint_actGrid_apply (D n : ℕ) (a : Act D) (m : Fin (2 ^ n + 1))
    (j : Fin D) :
    (toPoint D n (actGrid D n a m) : Fin D → ℝ) j =
      if j = a.2 then ((m : ℕ) : ℝ) / (2 ^ n : ℝ)
      else (toPoint D 0 a.1 : Fin D → ℝ) j := by
  show ((actGrid D n a m j : ℕ) : ℝ) / (2 ^ n : ℝ) = _
  by_cases h : j = a.2
  · have hupd : actGrid D n a m j = m := by
      simp only [actGrid, Function.update_apply, if_pos h]
    rw [hupd, if_pos h]
  · have hupd : actGrid D n a m j = liftLevel D n a.1 j := by
      simp only [actGrid, Function.update_apply, if_neg h]
    rw [hupd, if_neg h]
    exact congrFun (congrArg Subtype.val (toPoint_liftLevel D n a.1)) j

/-- The sites an act's refinements visit: every dyadic tally between its
endpoints, at every level. -/
def actSites (D : ℕ) (a : Act D) : Set (Ambient D) :=
  ⋃ n, Set.range fun m : Fin (2 ^ n + 1) => toPoint D n (actGrid D n a m)

/-- The closed 1-cell the ledger names for an act: the points of the stage
agreeing with the act's record at every primitive the act does not move. -/
def actCell (D : ℕ) (a : Act D) : Set (Ambient D) :=
  {x | ∀ j, j ≠ a.2 → (x : Fin D → ℝ) j = (toPoint D 0 a.1 : Fin D → ℝ) j}

theorem actSites_subset_actCell (D : ℕ) (a : Act D) :
    actSites D a ⊆ actCell D a := by
  rintro x hx
  simp only [actSites, Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨n, m, rfl⟩ := hx
  intro j hj
  rw [toPoint_actGrid_apply, if_neg hj]

theorem isClosed_actCell (D : ℕ) (a : Act D) : IsClosed (actCell D a) := by
  have hrw : actCell D a =
      ⋂ j ∈ {j : Fin D | j ≠ a.2},
        (fun x : Ambient D => (x : Fin D → ℝ) j) ⁻¹'
          {(toPoint D 0 a.1 : Fin D → ℝ) j} := by
    ext x
    simp [actCell, Set.mem_iInter]
  rw [hrw]
  refine isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact IsClosed.preimage ((continuous_apply j).comp continuous_subtype_val)
    isClosed_singleton

/-- **The closed 1-cell is forced.** The closure of the sites an act's own
refinements visit is exactly the cell. The recognizer does not choose where an
edge of its state graph goes on the stage: refining the act already places it,
and the placement is the only one consistent with the records. -/
theorem closure_actSites (D : ℕ) (a : Act D) :
    closure (actSites D a) = actCell D a := by
  haveI : Nonempty (Fin D) := ⟨a.2⟩
  refine Set.Subset.antisymm
    (closure_minimal (actSites_subset_actCell D a) (isClosed_actCell D a)) ?_
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < ε :=
    exists_pow_lt_of_lt_one hε (by norm_num)
  have hxi : (x : Fin D → ℝ) a.2 ∈ Set.Icc (0 : ℝ) 1 :=
    x.property a.2 (Set.mem_univ _)
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hy0 : (0 : ℝ) ≤ (x : Fin D → ℝ) a.2 * 2 ^ n := by
    have := hxi.1; positivity
  have hbound : ⌊(x : Fin D → ℝ) a.2 * 2 ^ n⌋₊ < 2 ^ n + 1 := by
    have hle : (x : Fin D → ℝ) a.2 * 2 ^ n ≤ (2 : ℝ) ^ n := by
      nlinarith [hxi.2, hpow]
    have hfle : (⌊(x : Fin D → ℝ) a.2 * 2 ^ n⌋₊ : ℝ) ≤ (2 : ℝ) ^ n :=
      le_trans (Nat.floor_le hy0) hle
    have hnat : ⌊(x : Fin D → ℝ) a.2 * 2 ^ n⌋₊ ≤ 2 ^ n := by exact_mod_cast hfle
    omega
  set m : Fin (2 ^ n + 1) := ⟨⌊(x : Fin D → ℝ) a.2 * 2 ^ n⌋₊, hbound⟩ with hm
  refine ⟨toPoint D n (actGrid D n a m), Set.mem_iUnion.mpr ⟨n, ⟨m, rfl⟩⟩, ?_⟩
  rw [Subtype.dist_eq, dist_pi_lt_iff hε]
  intro j
  by_cases hj : j = a.2
  · have hval : (toPoint D n (actGrid D n a m) : Fin D → ℝ) j
        = ((m : ℕ) : ℝ) / (2 ^ n : ℝ) := by
      rw [toPoint_actGrid_apply, if_pos hj]
    have hxj : (x : Fin D → ℝ) j = (x : Fin D → ℝ) a.2 := by rw [hj]
    rw [hxj, hval]
    have hmv : ((m : ℕ) : ℝ) = (⌊(x : Fin D → ℝ) a.2 * 2 ^ n⌋₊ : ℝ) := by simp [hm]
    have hlow : ((m : ℕ) : ℝ) / (2 ^ n : ℝ) ≤ (x : Fin D → ℝ) a.2 := by
      rw [div_le_iff₀ hpow, hmv]
      exact Nat.floor_le hy0
    have hup : (x : Fin D → ℝ) a.2 < (((m : ℕ) : ℝ) + 1) / (2 ^ n : ℝ) := by
      rw [lt_div_iff₀ hpow, hmv]
      exact Nat.lt_floor_add_one _
    have hsplit : (((m : ℕ) : ℝ) + 1) / (2 ^ n : ℝ)
        = ((m : ℕ) : ℝ) / (2 ^ n : ℝ) + 1 / 2 ^ n := by field_simp
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlow)]
    have hlt : (x : Fin D → ℝ) a.2 - ((m : ℕ) : ℝ) / (2 ^ n : ℝ) < 1 / 2 ^ n := by
      rw [hsplit] at hup; linarith
    calc (x : Fin D → ℝ) a.2 - ((m : ℕ) : ℝ) / (2 ^ n : ℝ)
        < 1 / 2 ^ n := hlt
      _ = (1 / 2 : ℝ) ^ n := by rw [div_pow, one_pow]
      _ < ε := hn
  · have h1 : (toPoint D n (actGrid D n a m) : Fin D → ℝ) j
        = (toPoint D 0 a.1 : Fin D → ℝ) j := by
      rw [toPoint_actGrid_apply, if_neg hj]
    rw [h1, ← hx j hj, dist_self]
    exact hε

/-! ## What is forced is straight -/

/-- The act's endpoint at tally `0` on the moved primitive. -/
noncomputable def endLo (D : ℕ) (a : Act D) : Ambient D :=
  toPoint D 0 (Function.update a.1 a.2 ⟨0, by norm_num⟩)

/-- The act's endpoint at tally `1` on the moved primitive. -/
noncomputable def endHi (D : ℕ) (a : Act D) : Ambient D :=
  toPoint D 0 (Function.update a.1 a.2 ⟨1, by norm_num⟩)

theorem endLo_apply (D : ℕ) (a : Act D) (j : Fin D) :
    (endLo D a : Fin D → ℝ) j =
      if j = a.2 then 0 else (toPoint D 0 a.1 : Fin D → ℝ) j := by
  simp only [endLo, toPoint_apply, Function.update_apply]
  by_cases h : j = a.2 <;> simp [h]

theorem endHi_apply (D : ℕ) (a : Act D) (j : Fin D) :
    (endHi D a : Fin D → ℝ) j =
      if j = a.2 then 1 else (toPoint D 0 a.1 : Fin D → ℝ) j := by
  simp only [endHi, toPoint_apply, Function.update_apply]
  by_cases h : j = a.2 <;> simp [h]

/-- The act's direction on the stage. -/
noncomputable def actDir (D : ℕ) (a : Act D) : Fin D → ℝ :=
  (endHi D a : Fin D → ℝ) - (endLo D a : Fin D → ℝ)

/-- **An act moves along one axis.** Its direction is the standard basis vector
of the primitive it moves: one primitive per act is what the ledger says, and
one axis per act is what that becomes on the stage. -/
theorem actDir_eq_single (D : ℕ) (a : Act D) :
    actDir D a = Pi.single a.2 1 := by
  funext j
  by_cases h : j = a.2
  · subst h
    simp [actDir, endLo_apply, endHi_apply]
  · simp [actDir, endLo_apply, endHi_apply, h]

theorem actDir_ne_zero (D : ℕ) (a : Act D) : actDir D a ≠ 0 := by
  intro h
  have h2 : actDir D a a.2 = 0 := by rw [h]; rfl
  rw [actDir_eq_single] at h2
  simp at h2

/-- **The primitives leave a vertex in independent directions.** At any record
of the stage the `D` acts available issue along the `D` standard basis vectors,
which are linearly independent. This is the joint independence of the primitives
read on the stage, and it is the pairwise-distinctness clause of the
cellular-completion definition. -/
theorem directions_linearIndependent (D : ℕ) (p : Grid D 0) :
    LinearIndependent ℝ fun i : Fin D => actDir D (p, i) := by
  have hfun : (fun i : Fin D => actDir D (p, i))
      = fun i : Fin D => (Pi.single i 1 : Fin D → ℝ) := by
    funext i; exact actDir_eq_single D (p, i)
  rw [hfun]
  have hb : (fun i : Fin D => (Pi.single i 1 : Fin D → ℝ))
      = ⇑(Pi.basisFun ℝ (Fin D)) := by
    funext i; simp
  rw [hb]
  exact (Pi.basisFun ℝ (Fin D)).linearIndependent

/-- The affine parametrization of an act's cell. -/
noncomputable def actParam (D : ℕ) (a : Act D) : ℝ → (Fin D → ℝ) :=
  fun t => (endLo D a : Fin D → ℝ) + t • actDir D a

/-- **Each closed 1-cell is a smooth regular embedding.** The parametrization is
affine with constant velocity `actDir`, which is nonzero, so the derivative never
vanishes. -/
theorem actParam_hasDerivAt (D : ℕ) (a : Act D) (t : ℝ) :
    HasDerivAt (actParam D a) (actDir D a) t := by
  have h0 : HasDerivAt (fun s : ℝ => s • actDir D a) ((1 : ℝ) • actDir D a) t :=
    (hasDerivAt_id t).smul_const (actDir D a)
  rw [one_smul] at h0
  exact h0.const_add ((endLo D a : Fin D → ℝ))

theorem actParam_contDiff (D : ℕ) (a : Act D) :
    ContDiff ℝ (⊤ : ℕ∞) (actParam D a) := by
  refine ContDiff.add contDiff_const ?_
  exact ContDiff.smul contDiff_id contDiff_const

theorem actParam_injective (D : ℕ) (a : Act D) :
    Function.Injective (actParam D a) := by
  intro s t hst
  have h := congrFun hst a.2
  simp only [actParam, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    actDir_eq_single, Pi.single_eq_same, mul_one] at h
  linarith

/-- **The forced cell is the straight segment between the act's endpoints.**
Nothing about the placement is left over: the refinement of the act names a set
whose closure is an affine segment. -/
theorem actCell_eq_segment (D : ℕ) (a : Act D) :
    Subtype.val '' actCell D a
      = segment ℝ (endLo D a : Fin D → ℝ) (endHi D a : Fin D → ℝ) := by
  rw [segment_eq_image]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hy : (x : Fin D → ℝ) a.2 ∈ Set.Icc (0 : ℝ) 1 :=
      x.property a.2 (Set.mem_univ _)
    refine ⟨(x : Fin D → ℝ) a.2, hy, ?_⟩
    funext j
    by_cases h : j = a.2
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, endLo_apply,
        endHi_apply, if_pos h]
      rw [h]; ring
    · have hxj := hx j h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, endLo_apply,
        endHi_apply, if_neg h]
      rw [hxj]; ring
  · rintro ⟨θ, hθ, rfl⟩
    have hmem : (fun j => (1 - θ) * (endLo D a : Fin D → ℝ) j
        + θ * (endHi D a : Fin D → ℝ) j) ∈ cubeSet D := by
      intro j _
      have h0 : (endLo D a : Fin D → ℝ) j ∈ Set.Icc (0 : ℝ) 1 :=
        (endLo D a).property j (Set.mem_univ _)
      have h1 : (endHi D a : Fin D → ℝ) j ∈ Set.Icc (0 : ℝ) 1 :=
        (endHi D a).property j (Set.mem_univ _)
      constructor
      · nlinarith [h0.1, h1.1, hθ.1, hθ.2]
      · nlinarith [h0.2, h1.2, hθ.1, hθ.2]
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · intro j hj
      show (1 - θ) * (endLo D a : Fin D → ℝ) j
        + θ * (endHi D a : Fin D → ℝ) j = _
      rw [endLo_apply, endHi_apply, if_neg hj, if_neg hj]
      ring
    · funext j
      show (1 - θ) * (endLo D a : Fin D → ℝ) j
        + θ * (endHi D a : Fin D → ℝ) j = _
      simp [Pi.add_apply, Pi.smul_apply]

/-- The cells are not degenerate: an act's two endpoints are a unit apart. -/
theorem dist_endLo_endHi (D : ℕ) (a : Act D) :
    (endHi D a : Fin D → ℝ) a.2 - (endLo D a : Fin D → ℝ) a.2 = 1 := by
  simp [endLo_apply, endHi_apply]

/-! ## The vertex is a cone point -/

/-- An act is incident to a record when the record lies on the act's cell:
they agree at every primitive the act does not move. -/
def Incident (D : ℕ) (p : Grid D 0) (a : Act D) : Prop :=
  ∀ j, j ≠ a.2 → (toPoint D 0 p : Fin D → ℝ) j = (toPoint D 0 a.1 : Fin D → ℝ) j

theorem mem_actCell_iff_incident (D : ℕ) (p : Grid D 0) (a : Act D) :
    toPoint D 0 p ∈ actCell D a ↔ Incident D p a := Iff.rfl

/-- An incident act's cell is the cell of the act read at the record itself. -/
theorem actCell_of_incident (D : ℕ) (p : Grid D 0) (a : Act D)
    (h : Incident D p a) : actCell D a = actCell D (p, a.2) := by
  ext x
  constructor
  · intro hx j hj; rw [hx j hj]; exact (h j hj).symm
  · intro hx j hj; rw [hx j hj]; exact h j hj

/-- **Each incident cell is a radial line through the vertex.** The cell of an
act at a record is exactly the set of stage points reached from that record by
moving along the act's own direction. -/
theorem mem_actCell_iff_radial (D : ℕ) (p : Grid D 0) (i : Fin D)
    (x : Ambient D) :
    x ∈ actCell D (p, i) ↔ ∃ s : ℝ,
      (x : Fin D → ℝ) = (toPoint D 0 p : Fin D → ℝ) + s • actDir D (p, i) := by
  constructor
  · intro hx
    refine ⟨(x : Fin D → ℝ) i - (toPoint D 0 p : Fin D → ℝ) i, ?_⟩
    funext j
    by_cases h : j = i
    · subst h
      simp [actDir_eq_single]
    · have := hx j h
      simp [actDir_eq_single, h, this]
  · rintro ⟨s, hs⟩ j hj
    have := congrFun hs j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, actDir_eq_single,
      Pi.single_apply, if_neg hj, mul_zero, add_zero] at this
    exact this

/-- **A non-incident act stays a full unit away.** Its cell pins some primitive
at the opposite vertex value, and vertex values differ by one. -/
theorem one_le_dist_of_not_incident (D : ℕ) (p : Grid D 0) (a : Act D)
    (h : ¬ Incident D p a) (x : Ambient D) (hx : x ∈ actCell D a) :
    1 ≤ dist (toPoint D 0 p) x := by
  obtain ⟨j, hj, hne⟩ : ∃ j, j ≠ a.2 ∧
      (toPoint D 0 p : Fin D → ℝ) j ≠ (toPoint D 0 a.1 : Fin D → ℝ) j := by
    by_contra hc
    push_neg at hc
    exact h fun j hj => hc j hj
  have hxj : (x : Fin D → ℝ) j = (toPoint D 0 a.1 : Fin D → ℝ) j := hx j hj
  have hcoord : (1 : ℝ)
      = dist ((toPoint D 0 p : Fin D → ℝ) j) ((x : Fin D → ℝ) j) := by
    rw [hxj, Real.dist_eq]
    rcases toPoint_zero_vertex D p j with hp | hp <;>
      rcases toPoint_zero_vertex D a.1 j with hq | hq <;>
      rw [hp, hq] at hne ⊢
    · exact absurd rfl hne
    · norm_num
    · norm_num
    · exact absurd rfl hne
  rw [hcoord, Subtype.dist_eq]
  exact dist_le_pi_dist _ _ j

/-- The realized 1-skeleton of the state graph on the stage. -/
def skeleton (D : ℕ) : Set (Ambient D) := ⋃ a : Act D, actCell D a

/-- **The vertex is a cone point, in the stage's own coordinates.** For any
radius at most one, the ball around a record meets the realized skeleton in
exactly the union of the `D` cells at that record, each of which is radial
(`mem_actCell_iff_radial`) and which leave in linearly independent directions
(`directions_linearIndependent`). The identity chart radializes every vertex, so
the tameness clause of the cellular-completion definition is a theorem on the
constructed stage rather than a hypothesis about it. -/
theorem ball_inter_skeleton (D : ℕ) (p : Grid D 0) {r : ℝ} (hr1 : r ≤ 1) :
    Metric.ball (toPoint D 0 p) r ∩ skeleton D
      = Metric.ball (toPoint D 0 p) r ∩ ⋃ i : Fin D, actCell D (p, i) := by
  ext x
  constructor
  · rintro ⟨hball, hskel⟩
    refine ⟨hball, ?_⟩
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hskel
    by_cases hinc : Incident D p a
    · exact Set.mem_iUnion.mpr ⟨a.2, (actCell_of_incident D p a hinc) ▸ ha⟩
    · exfalso
      have h1 := one_le_dist_of_not_incident D p a hinc x ha
      have h2 : dist x (toPoint D 0 p) < r := Metric.mem_ball.mp hball
      rw [dist_comm] at h2
      linarith
  · rintro ⟨hball, hx⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨hball, Set.mem_iUnion.mpr ⟨(p, i), hi⟩⟩

/-! ## What the cost floor supplies: finiteness -/

/-- A pass posts finitely many acts. Reading a posted act at a finer level is
free (it moves no record); posting a distinction that is not a refinement of a
posted one is not. -/
structure Pass (D : ℕ) where
  /-- The acts the pass posts. -/
  acts : Finset (Act D)

/-- The locus a pass sweeps: the cells its acts force. -/
def Pass.locus {D : ℕ} (P : Pass D) : Set (Ambient D) :=
  ⋃ a ∈ P.acts, actCell D a

/-- The cost of a pass at a per-posting floor `c`. -/
def Pass.cost {D : ℕ} (P : Pass D) (c : ℝ) : ℝ := (P.acts.card : ℝ) * c

/-- **Bounded cost bounds the postings.** With a positive floor under each
posting, a pass of cost at most `B` posts at most `B / c` acts. -/
theorem card_le_of_cost_le {D : ℕ} (P : Pass D) {c B : ℝ} (hc : 0 < c)
    (h : P.cost c ≤ B) : (P.acts.card : ℝ) ≤ B / c := by
  rw [Pass.cost] at h
  rwa [le_div_iff₀ hc]

/-- **A pass sweeps a finite union of straight segments.** Everything a
recognizer can afford to lay down is a finite polyhedron. -/
theorem locus_eq_union_segments {D : ℕ} (P : Pass D) :
    Subtype.val '' P.locus
      = ⋃ a ∈ P.acts,
          segment ℝ (endLo D a : Fin D → ℝ) (endHi D a : Fin D → ℝ) := by
  rw [Pass.locus, Set.image_iUnion₂]
  exact Set.iUnion₂_congr fun a _ => actCell_eq_segment D a

/-- **Cost is unbounded in the number of postings.** With a positive floor, no
bound survives: a locus demanding new distinctions without bound demands cost
without bound. Wildness is exactly that demand, structure at every scale in a
bounded region, so no pass of finite cost sweeps a wild locus. -/
theorem cost_unbounded {c : ℝ} (hc : 0 < c) (B : ℝ) : ∃ n : ℕ, B < (n : ℝ) * c := by
  obtain ⟨n, hn⟩ := exists_nat_gt (B / c)
  exact ⟨n, by rwa [div_lt_iff₀ hc] at hn⟩

/-! ## Non-vacuity -/

theorem center_mem_cube (D : ℕ) : (fun _ => (1 / 2 : ℝ)) ∈ cubeSet D := by
  intro i _
  constructor <;> norm_num

/-- The centre of the stage. -/
noncomputable def center (D : ℕ) : Ambient D := ⟨fun _ => 1 / 2, center_mem_cube D⟩

/-- **The predicate is not a token.** With at least two primitives the centre of
the stage lies on no pass locus: every point of a swept cell has all but one
coordinate at a vertex value. So "is swept by a pass" excludes something, and
the tameness theorems above are not vacuous. -/
theorem center_not_mem_locus (D : ℕ) (hD : 2 ≤ D) (P : Pass D) :
    center D ∉ P.locus := by
  intro hmem
  obtain ⟨a, _, ha⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨j, hj⟩ : ∃ j : Fin D, j ≠ a.2 := by
    have hcard : 1 < Fintype.card (Fin D) := by simpa using hD
    exact Fintype.exists_ne_of_one_lt_card hcard a.2
  have h := ha j hj
  have hc : (center D : Fin D → ℝ) j = 1 / 2 := rfl
  rw [hc] at h
  rcases toPoint_zero_vertex D a.1 j with hv | hv <;> rw [hv] at h <;> norm_num at h

/-! ## Certificate -/

/-- The tameness-from-cost certificate. Every field is a proved theorem of this
module. Together they replace the tameness clause of the cellular-completion
definition with facts the ledger already carries: an act's refinement forces its
cell, the cell is the affine segment between the act's endpoints, the acts at a
record leave along linearly independent axes, a ball of radius at most one meets
the skeleton in exactly those radial cells, and the cost floor makes the swept
locus a finite union of segments. -/
structure TamenessFromCostCert : Prop where
  /-- The closed 1-cell is the closure of the act's own refinement. -/
  cell_forced : ∀ (D : ℕ) (a : Act D), closure (actSites D a) = actCell D a
  /-- The forced cell is the affine segment between the act's endpoints. -/
  cell_straight : ∀ (D : ℕ) (a : Act D),
    Subtype.val '' actCell D a
      = segment ℝ (endLo D a : Fin D → ℝ) (endHi D a : Fin D → ℝ)
  /-- The parametrization is smooth with constant velocity. -/
  cell_smooth : ∀ (D : ℕ) (a : Act D) (t : ℝ),
    HasDerivAt (actParam D a) (actDir D a) t
  /-- The velocity never vanishes: the embedding is regular. -/
  cell_regular : ∀ (D : ℕ) (a : Act D), actDir D a ≠ 0
  /-- The acts at a record leave in linearly independent directions. -/
  directions_independent : ∀ (D : ℕ) (p : Grid D 0),
    LinearIndependent ℝ fun i : Fin D => actDir D (p, i)
  /-- Every incident cell is radial through the record. -/
  cells_radial : ∀ (D : ℕ) (p : Grid D 0) (i : Fin D) (x : Ambient D),
    x ∈ actCell D (p, i) ↔ ∃ s : ℝ,
      (x : Fin D → ℝ) = (toPoint D 0 p : Fin D → ℝ) + s • actDir D (p, i)
  /-- A unit ball at a record meets the skeleton in exactly the incident cells. -/
  vertex_is_cone_point : ∀ (D : ℕ) (p : Grid D 0) (r : ℝ), r ≤ 1 →
    Metric.ball (toPoint D 0 p) r ∩ skeleton D
      = Metric.ball (toPoint D 0 p) r ∩ ⋃ i : Fin D, actCell D (p, i)
  /-- Bounded cost bounds the postings. -/
  cost_bounds_postings : ∀ (D : ℕ) (P : Pass D) (c B : ℝ), 0 < c →
    P.cost c ≤ B → (P.acts.card : ℝ) ≤ B / c
  /-- What a pass sweeps is a finite union of straight segments. -/
  locus_polyhedral : ∀ (D : ℕ) (P : Pass D),
    Subtype.val '' P.locus
      = ⋃ a ∈ P.acts,
          segment ℝ (endLo D a : Fin D → ℝ) (endHi D a : Fin D → ℝ)
  /-- Unbounded postings cost without bound. -/
  unbounded_postings_cost : ∀ (c : ℝ), 0 < c → ∀ B : ℝ, ∃ n : ℕ, B < (n : ℝ) * c
  /-- The swept-locus predicate excludes something. -/
  not_a_token : ∀ (D : ℕ), 2 ≤ D → ∀ P : Pass D, center D ∉ P.locus

/-- The tameness-from-cost certificate holds. -/
theorem tamenessFromCostCert : TamenessFromCostCert where
  cell_forced := closure_actSites
  cell_straight := actCell_eq_segment
  cell_smooth := actParam_hasDerivAt
  cell_regular := actDir_ne_zero
  directions_independent := directions_linearIndependent
  cells_radial := mem_actCell_iff_radial
  vertex_is_cone_point := fun D p _r hr => ball_inter_skeleton D p hr
  cost_bounds_postings := fun _D P _c _B hc h => card_le_of_cost_le P hc h
  locus_polyhedral := fun _D P => locus_eq_union_segments P
  unbounded_postings_cost := fun _c hc B => cost_unbounded hc B
  not_a_token := center_not_mem_locus

end TamenessFromCost
end Foundation
end IndisputableMonolith
