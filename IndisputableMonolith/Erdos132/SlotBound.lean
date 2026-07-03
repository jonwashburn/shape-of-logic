/-
Copyright (c) 2026 Recognition Physics Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Erdos-132 `d=1` slot bound: a planar 3-distance set with a unique diameter has ≤ 5 points.

This module is the Lean scaffold for the `n ≤ 5` theorem on planar 3-distance sets
whose maximum distance (the diameter) is attained by a unique unordered pair. The
result is the `d=1` branch of the Erdos-132 program: one diameter class plus two
shorter non-empty distance classes.

## Provenance (the math is verified outside Lean, three independent ways)

Normalize by an isometry so the unique diameter pair is `A = (0,0)`, `B = (1,0)`
(diameter `= 1`). Every other point `P` is a *non-diameter* point: both `|PA|` and
`|PB|` lie in `{u, v}` with `0 < u, v < 1`, `u ≠ v` (they cannot equal the diameter
`1`, which is attained only by `A,B`). Each such `P` is then pinned to a **slot**:
`x = (1 + |PA|² − |PB|²)/2`, `y² = |PA|² − x²`. There are 4 type-choices
(`|PA|,|PB| ∈ {u,v}`) × 2 sides (`sign y`), so 8 off-line slots plus the collinear
locus `y = 0`.

The core fact — `offline_no_four_slots` — is that no 4 distinct *off-line*
non-diameter points can have all six pairwise distances in `{u,v}`. Verified
exactly three ways (resultant elimination + real-root isolation `_slot_bound.py`,
Groebner `_slot_bound_groebner.py`, independent re-derivation `_slot_bound_verify.py`):
all `C(8,4)=70` slot-subsets × `2⁶=64` colorings = 4480 systems are real-infeasible.
The collinear locus (`y=0`) is closed separately (`_slot_bound_collinear.py`): at most
two collinear non-diameter points exist, and they cannot coexist with two off-line
ones. The obstruction census (`_slot_obstruction_classify.py`) found only 2 coarse
certificate shapes (4478 `ROOT_FORCES_OUT`, 2 `POSDIM`, 0 `NO_ROOT_IN_BOX`), so the
`nlinarith` dispatch is small. A pure-chord test (`_slot_chord_test.py`) showed 96.9%
of systems need the A↔B metric tie (only the all-equal colorings die chordally), so
the proof must carry the slot x-positions: the obstruction is genuinely metric, not a
2-distance-set impossibility.

Tightness: `n = 5` is realized at `u = √2/2`, `v = (√3−1)/2` (Burnside enumeration,
kept as a regression test only).

## Status of this file

Every theorem below carries a faithful STATEMENT and a `sorry`. The sorries are the
targets for the gated autonomous prover loop (maker = GLM, judge = `lake` +
`#print axioms`). The proof of `offline_no_four_slots` is the workhorse: a finite
case split (`rcases` on each point's two distance choices and on each pair's color)
followed by `nlinarith` using `y² > 0` (off-line) and the box `0 < u,v < 1`. The
collinear and mixed lemmas are smaller per-case dispatches; `no_four_nondiameter`
assembles them by counting how many of the four points are collinear; `n_le_5` is
the isometry-normalization wrapper.
-/
import Mathlib.Tactic

noncomputable section

namespace Erdos132.SlotBound

/-- Squared Euclidean distance on the plane `ℝ × ℝ`. -/
def d2 (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- A point `p` is a **non-diameter point** for the normalized diameter
`A = (0,0)`, `B = (1,0)` and short distances `u, v`: both squared distances to the
endpoints lie in `{u², v²}`. -/
def IsNonDiameter (u v : ℝ) (p : ℝ × ℝ) : Prop :=
  (d2 p ((0 : ℝ), (0 : ℝ)) = u ^ 2 ∨ d2 p ((0 : ℝ), (0 : ℝ)) = v ^ 2) ∧
  (d2 p ((1 : ℝ), (0 : ℝ)) = u ^ 2 ∨ d2 p ((1 : ℝ), (0 : ℝ)) = v ^ 2)

/-- The forced x-coordinate of a non-diameter point whose squared distances to
`A = (0,0)` and `B = (1,0)` are `s2` and `t2`. Derived from `x² + y² = s2` and
`(x−1)² + y² = t2`, whose difference is `2x − 1 = s2 − t2`. -/
def slotX (s2 t2 : ℝ) : ℝ := (1 + s2 - t2) / 2

/-- The forced `y²` of such a point: `y² = s2 − x²`. The slot is *off-line*
(`y ≠ 0`) iff `slotYsq s2 t2 > 0`, and *collinear* (`y = 0`) iff it is `0`. -/
def slotYsq (s2 t2 : ℝ) : ℝ := s2 - (slotX s2 t2) ^ 2

/-- **Slot classification.** Every non-diameter point is pinned to a slot: its
x-coordinate and its `y²` are determined by the two type-choices `s2, t2 ∈ {u², v²}`.
This is pure algebra from the two distance equations. -/
theorem slot_classification (u v : ℝ) (p : ℝ × ℝ) (h : IsNonDiameter u v p) :
    ∃ s2 t2 : ℝ, (s2 = u ^ 2 ∨ s2 = v ^ 2) ∧ (t2 = u ^ 2 ∨ t2 = v ^ 2) ∧
      p.1 = slotX s2 t2 ∧ p.2 ^ 2 = slotYsq s2 t2 := by
  obtain ⟨hA, hB⟩ := h
  refine ⟨d2 p ((0 : ℝ), (0 : ℝ)), d2 p ((1 : ℝ), (0 : ℝ)), hA, hB, ?_, ?_⟩
  · simp only [slotX, d2]; ring
  · simp only [slotYsq, slotX, d2]; ring

/-- **Collinear point structure.** A collinear (`y = 0`) non-diameter point `p` has its
x-coordinate in `{u, v}` and its reflected coordinate `1 − p.1` in `{u, v}`. (From
`p.1² ∈ {u²,v²}`, `(p.1−1)² ∈ {u²,v²}`, and the box `0 < u,v < 1`, the negative square
roots are excluded.) -/
theorem collinear_props (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (p : ℝ × ℝ) (hnd : IsNonDiameter u v p) (hcol : p.2 = 0) :
    (p.1 = u ∨ p.1 = v) ∧ (p.1 = 1 - u ∨ p.1 = 1 - v) := by
  obtain ⟨hA, hB⟩ := hnd
  have hAsq : p.1 ^ 2 = u ^ 2 ∨ p.1 ^ 2 = v ^ 2 := by
    rcases hA with h | h
    · left; rw [← h, d2, hcol]; ring
    · right; rw [← h, d2, hcol]; ring
  have hBsq : (p.1 - 1) ^ 2 = u ^ 2 ∨ (p.1 - 1) ^ 2 = v ^ 2 := by
    rcases hB with h | h
    · left; rw [← h, d2, hcol]; ring
    · right; rw [← h, d2, hcol]; ring
  constructor
  · rcases hAsq with h | h
    · have hfac : (p.1 - u) * (p.1 + u) = 0 := by linear_combination h
      rcases mul_eq_zero.mp hfac with h' | h'
      · left; linarith
      · exfalso
        have hx : p.1 = -u := by linarith
        rcases hBsq with hB' | hB' <;> rw [hx] at hB' <;> nlinarith [hu0, hv0, hu1, hv1]
    · have hfac : (p.1 - v) * (p.1 + v) = 0 := by linear_combination h
      rcases mul_eq_zero.mp hfac with h' | h'
      · right; linarith
      · exfalso
        have hx : p.1 = -v := by linarith
        rcases hBsq with hB' | hB' <;> rw [hx] at hB' <;> nlinarith [hu0, hv0, hu1, hv1]
  · rcases hBsq with h | h
    · have hfac : (p.1 - 1 + u) * (p.1 - 1 - u) = 0 := by linear_combination h
      rcases mul_eq_zero.mp hfac with h' | h'
      · left; linarith
      · -- p.1 - 1 = u  ⇒  p.1 = 1 + u > 1, but p.1² ≤ max(u²,v²) < 1
        exfalso
        have hx : p.1 = 1 + u := by linarith
        rcases hAsq with hA' | hA' <;> rw [hx] at hA' <;> nlinarith [hu0, hv0, hu1, hv1]
    · have hfac : (p.1 - 1 + v) * (p.1 - 1 - v) = 0 := by linear_combination h
      rcases mul_eq_zero.mp hfac with h' | h'
      · right; linarith
      · exfalso
        have hx : p.1 = 1 + v := by linarith
        rcases hAsq with hA' | hA' <;> rw [hx] at hA' <;> nlinarith [hu0, hv0, hu1, hv1]

/-- **Single-collinear locus.** The existence of one collinear non-diameter point forces
`u = 1/2`, `v = 1/2`, or `u + v = 1`. -/
theorem collinear_locus (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (p : ℝ × ℝ) (hnd : IsNonDiameter u v p) (hcol : p.2 = 0) :
    u = 1 / 2 ∨ v = 1 / 2 ∨ u + v = 1 := by
  obtain ⟨h1, h2⟩ := collinear_props u v hu0 hu1 hv0 hv1 p hnd hcol
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left; linarith
  · right; right; linarith
  · right; right; linarith
  · right; left; linarith

/-- **Off-line point on the `u+v=1` locus.** When `u + v = 1`, an off-line non-diameter
point sits on the vertical bisector `x = 1/2`, with `y² = u² − 1/4` or `y² = v² − 1/4`.
(The two "mixed-type" assignments force `y² = 0`, i.e. collinear, contradicting
`q.2 ≠ 0`.) -/
theorem offline_on_locus (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (huv1 : u + v = 1)
    (q : ℝ × ℝ) (hnd : IsNonDiameter u v q) (hoff : q.2 ≠ 0) :
    q.1 = 1 / 2 ∧ (q.2 ^ 2 = u ^ 2 - 1 / 4 ∨ q.2 ^ 2 = v ^ 2 - 1 / 4) := by
  obtain ⟨hA, hB⟩ := hnd
  -- distance squared to A and B, written out
  have hAe : q.1 ^ 2 + q.2 ^ 2 = u ^ 2 ∨ q.1 ^ 2 + q.2 ^ 2 = v ^ 2 := by
    rcases hA with h | h
    · left; rw [← h, d2]; ring
    · right; rw [← h, d2]; ring
  have hBe : (q.1 - 1) ^ 2 + q.2 ^ 2 = u ^ 2 ∨ (q.1 - 1) ^ 2 + q.2 ^ 2 = v ^ 2 := by
    rcases hB with h | h
    · left; rw [← h, d2]; ring
    · right; rw [← h, d2]; ring
  rcases hAe with hAe | hAe <;> rcases hBe with hBe | hBe
  · -- (u², u²): subtract ⇒ 1 - 2x = 0 ⇒ x = 1/2, y² = u² - 1/4
    refine ⟨by nlinarith [hAe, hBe], ?_⟩
    left; nlinarith [hAe, hBe]
  · -- (u², v²): forces x = u and y² = 0, contradiction
    exfalso
    have hx : q.1 = u := by nlinarith [hAe, hBe]
    apply hoff
    have : q.2 ^ 2 = 0 := by rw [hx] at hAe; nlinarith [hAe]
    nlinarith [this, sq_nonneg q.2]
  · -- (v², u²): forces x = v and y² = 0, contradiction
    exfalso
    have hx : q.1 = v := by nlinarith [hAe, hBe]
    apply hoff
    have : q.2 ^ 2 = 0 := by rw [hx] at hAe; nlinarith [hAe]
    nlinarith [this, sq_nonneg q.2]
  · -- (v², v²): x = 1/2, y² = v² - 1/4
    refine ⟨by nlinarith [hAe, hBe], ?_⟩
    right; nlinarith [hAe, hBe]

/-- **Two distinct collinear points force `u + v = 1`.** The single-point loci `u = 1/2`
and `v = 1/2` each admit only one collinear position, so two distinct collinear
non-diameter points can only live on `u + v = 1`. -/
theorem two_collinear_forces_sum (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
    (c0 c1 : ℝ × ℝ)
    (hndc0 : IsNonDiameter u v c0) (hndc1 : IsNonDiameter u v c1)
    (hcol0 : c0.2 = 0) (hcol1 : c1.2 = 0) (hne : c0 ≠ c1) :
    u + v = 1 := by
  obtain ⟨ha0, hb0⟩ := collinear_props u v hu0 hu1 hv0 hv1 c0 hndc0 hcol0
  obtain ⟨ha1, hb1⟩ := collinear_props u v hu0 hu1 hv0 hv1 c1 hndc1 hcol1
  have hxne : c0.1 ≠ c1.1 := by
    intro h; exact hne (Prod.ext h (by rw [hcol0, hcol1]))
  rcases ha0 with h0 | h0 <;> rcases ha1 with h1 | h1
  · exact absurd (h0.trans h1.symm) hxne
  · rcases hb0 with hb | hb
    · rcases hb1 with hb1 | hb1
      · linarith
      · exfalso; exact huv (by linarith)
    · linarith
  · rcases hb0 with hb | hb
    · linarith
    · rcases hb1 with hb1 | hb1
      · exfalso; exact huv (by linarith)
      · linarith
  · exact absurd (h0.trans h1.symm) hxne

/- **Core off-line dispatch** — `offline_no_four_slots` — is now PROVEN (axiom-clean,
no `sorry`) in `IndisputableMonolith.Erdos132.SlotDispatch`. It cannot live here: its
proof imports the 204 per-type helper shards (`SlotDispatch.H00..H15`), each of which
imports this file (`SlotBound`), so the proof must sit downstream. The fully-qualified
name is unchanged (`Erdos132.SlotBound.offline_no_four_slots`); `import
IndisputableMonolith.Erdos132.SlotDispatch` to use it. Statement, for reference:

    theorem offline_no_four_slots (u v : ℝ)
        (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
        (P : Fin 4 → ℝ × ℝ) (hinj : Function.Injective P)
        (hnd : ∀ i, IsNonDiameter u v (P i)) (hoff : ∀ i, (P i).2 ≠ 0)
        (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2) :
        False
-/

/-- **Collinear locus.** No three distinct *collinear* (`y = 0`) non-diameter points
exist. A collinear non-diameter point has `x ∈ {u, v}` with `1 − x ∈ {u, v}`, which
admits at most two distinct positions (`x = u` and `x = 1 − u` when `u + v = 1`, or
`x = 1/2`). -/
theorem no_three_collinear
    (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
    (P : Fin 3 → ℝ × ℝ)
    (hinj : Function.Injective P)
    (hnd : ∀ i, IsNonDiameter u v (P i))
    (hcol : ∀ i, (P i).2 = 0) :
    False := by
  -- Every collinear non-diameter point has first coordinate `u` or `v`.
  have key : ∀ i, (P i).1 = u ∨ (P i).1 = v := by
    intro i
    obtain ⟨hA, hB⟩ := hnd i
    have hy : (P i).2 = 0 := hcol i
    -- squared distances to A=(0,0) and B=(1,0) with y=0
    have hA' : (P i).1 ^ 2 = u ^ 2 ∨ (P i).1 ^ 2 = v ^ 2 := by
      rcases hA with h | h
      · left; rw [← h, d2, hy]; ring
      · right; rw [← h, d2, hy]; ring
    have hB' : ((P i).1 - 1) ^ 2 = u ^ 2 ∨ ((P i).1 - 1) ^ 2 = v ^ 2 := by
      rcases hB with h | h
      · left; rw [← h, d2, hy]; ring
      · right; rw [← h, d2, hy]; ring
    -- From x^2 ∈ {u^2,v^2}, factor x = ±u or ±v; the box rules out the negative roots.
    rcases hA' with hA' | hA'
    · -- x^2 = u^2  ⇒  x = u ∨ x = -u
      have hfac : ((P i).1 - u) * ((P i).1 + u) = 0 := by linear_combination hA'
      rcases mul_eq_zero.mp hfac with h | h
      · left; linarith
      · -- x = -u : then (x-1)^2 = (u+1)^2 > 1 ≥ u^2, v^2, contradiction
        exfalso
        have hx : (P i).1 = -u := by linarith
        rcases hB' with hB' | hB' <;> rw [hx] at hB' <;> nlinarith [hu0, hv0, hu1, hv1]
    · -- x^2 = v^2  ⇒  x = v ∨ x = -v
      have hfac : ((P i).1 - v) * ((P i).1 + v) = 0 := by linear_combination hA'
      rcases mul_eq_zero.mp hfac with h | h
      · right; linarith
      · exfalso
        have hx : (P i).1 = -v := by linarith
        rcases hB' with hB' | hB' <;> rw [hx] at hB' <;> nlinarith [hu0, hv0, hu1, hv1]
  -- Pigeonhole: three points, two possible first coordinates ⇒ two coincide ⇒ ¬injective.
  have hpt : ∀ i j : Fin 3, (P i).1 = (P j).1 → i = j := by
    intro i j hxij
    apply hinj
    exact Prod.ext_iff.mpr ⟨hxij, by rw [hcol i, hcol j]⟩
  rcases key 0 with h0 | h0 <;> rcases key 1 with h1 | h1 <;> rcases key 2 with h2 | h2
  -- among 0,1,2 with values in {u,v}, two share a value; deduce equal index (absurd).
  · exact absurd (hpt 0 1 (by rw [h0, h1])) (by decide)  -- uuu
  · exact absurd (hpt 0 1 (by rw [h0, h1])) (by decide)  -- uuv
  · exact absurd (hpt 0 2 (by rw [h0, h2])) (by decide)  -- uvu
  · exact absurd (hpt 1 2 (by rw [h1, h2])) (by decide)  -- uvv
  · exact absurd (hpt 1 2 (by rw [h1, h2])) (by decide)  -- vuu
  · exact absurd (hpt 0 2 (by rw [h0, h2])) (by decide)  -- vuv
  · exact absurd (hpt 0 1 (by rw [h0, h1])) (by decide)  -- vvu
  · exact absurd (hpt 0 1 (by rw [h0, h1])) (by decide)  -- vvv

set_option maxHeartbeats 1600000 in
/-- **Mixed locus (2 + 2).** Two distinct collinear non-diameter points and two
distinct off-line non-diameter points cannot coexist with all cross- and
internal-pairwise distances in `{u², v²}`. -/
theorem two_collinear_two_offline
    (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
    (c0 c1 q0 q1 : ℝ × ℝ)
    (hndc0 : IsNonDiameter u v c0) (hndc1 : IsNonDiameter u v c1)
    (hndq0 : IsNonDiameter u v q0) (hndq1 : IsNonDiameter u v q1)
    (hcol0 : c0.2 = 0) (hcol1 : c1.2 = 0)
    (hoff0 : q0.2 ≠ 0) (hoff1 : q1.2 ≠ 0)
    (hdistinct : c0 ≠ c1 ∧ q0 ≠ q1)
    (hpair : ∀ p ∈ ({c0, c1, q0, q1} : Finset (ℝ × ℝ)),
             ∀ q ∈ ({c0, c1, q0, q1} : Finset (ℝ × ℝ)),
             p ≠ q → d2 p q = u ^ 2 ∨ d2 p q = v ^ 2) :
    False := by
  -- Two distinct collinear points force u + v = 1.
  have hsum : u + v = 1 :=
    two_collinear_forces_sum u v hu0 hu1 hv0 hv1 huv c0 c1 hndc0 hndc1 hcol0 hcol1 hdistinct.1
  have hve : v = 1 - u := by linarith
  -- The off-line point q0 lives at x = 1/2 with y² ∈ {u²−1/4, v²−1/4}.
  obtain ⟨hq0x, hq0y⟩ := offline_on_locus u v hu0 hu1 hv0 hv1 hsum q0 hndq0 hoff0
  -- The collinear points have x-coordinate in {u, v}.
  obtain ⟨hc0x, _⟩ := collinear_props u v hu0 hu1 hv0 hv1 c0 hndc0 hcol0
  obtain ⟨hc1x, _⟩ := collinear_props u v hu0 hu1 hv0 hv1 c1 hndc1 hcol1
  -- c0 ≠ q0 since c0.2 = 0 ≠ q0.2.
  have hc0q0 : c0 ≠ q0 := fun h => hoff0 (h ▸ hcol0)
  -- Two cross/internal distances, expanded to polynomial form.
  have hcc : d2 c0 c1 = u ^ 2 ∨ d2 c0 c1 = v ^ 2 :=
    hpair c0 (by simp) c1 (by simp) hdistinct.1
  have hcq : d2 c0 q0 = u ^ 2 ∨ d2 c0 q0 = v ^ 2 :=
    hpair c0 (by simp) q0 (by simp) hc0q0
  have ed_cc : d2 c0 c1 = (c0.1 - c1.1) ^ 2 := by rw [d2, hcol0, hcol1]; ring
  have ed_cq : d2 c0 q0 = (c0.1 - 1 / 2) ^ 2 + q0.2 ^ 2 := by rw [d2, hcol0, hq0x]; ring
  rw [ed_cc] at hcc
  rw [ed_cq] at hcq
  -- Eliminate the projection atoms by substituting the discrete coordinate choices,
  -- so each leaf is a low-degree (in)equation in u, v, q0.2 only.
  rcases hc0x with hc0 | hc0 <;> rcases hc1x with hc1 | hc1 <;>
    rw [hc0, hc1] at hcc <;> rw [hc0] at hcq <;>
    rcases hq0y with hy | hy <;> rcases hcc with hcc | hcc <;> rcases hcq with hcq | hcq <;>
    nlinarith [hy, hcc, hcq, hsum, hve, hu0, hu1, hv0, hv1, sq_nonneg q0.2]

set_option maxHeartbeats 800000 in
private lemma oc3_sq_eq_sign {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have hprod : (x - y) * (x + y) = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with h1 | h2
  · left; linarith
  · right; linarith

set_option maxHeartbeats 800000 in
private lemma oc3_sq_sub_quarter_neg {x : ℝ} (hx0 : 0 < x) (hxh : x < 1 / 2) :
    x ^ 2 - 1 / 4 < 0 := by
  have hdiff : 0 < (1 / 2 : ℝ) - x := by linarith
  have hmul : 0 < x * ((1 / 2 : ℝ) - x) := mul_pos hx0 hdiff
  nlinarith

set_option maxHeartbeats 800000 in
private lemma oc3_same_x_same_sq
    (Q : Fin 3 → ℝ × ℝ) (hinjQ : Function.Injective Q)
    (X Y : ℝ)
    (hx0 : (Q 0).1 = X) (hx1 : (Q 1).1 = X) (hx2 : (Q 2).1 = X)
    (hy0 : (Q 0).2 ^ 2 = Y) (hy1 : (Q 1).2 ^ 2 = Y) (hy2 : (Q 2).2 ^ 2 = Y) :
    False := by
  have s01 : (Q 1).2 = (Q 0).2 ∨ (Q 1).2 = -(Q 0).2 :=
    oc3_sq_eq_sign (by rw [hy1, hy0])
  have s02 : (Q 2).2 = (Q 0).2 ∨ (Q 2).2 = -(Q 0).2 :=
    oc3_sq_eq_sign (by rw [hy2, hy0])
  rcases s01 with s01 | s01 <;> rcases s02 with s02 | s02
  · have hQ : Q 1 = Q 0 := by
      apply Prod.ext <;> linarith
    exact (show (1 : Fin 3) ≠ 0 by decide) (hinjQ hQ)
  · have hQ : Q 1 = Q 0 := by
      apply Prod.ext <;> linarith
    exact (show (1 : Fin 3) ≠ 0 by decide) (hinjQ hQ)
  · have hQ : Q 2 = Q 0 := by
      apply Prod.ext <;> linarith
    exact (show (2 : Fin 3) ≠ 0 by decide) (hinjQ hQ)
  · have hQ : Q 1 = Q 2 := by
      apply Prod.ext <;> linarith
    exact (show (1 : Fin 3) ≠ 2 by decide) (hinjQ hQ)

set_option maxHeartbeats 800000 in
private lemma oc3_half_classify
    (a b : ℝ) (c q : ℝ × ℝ)
    (hahalf : a = 1 / 2) (hcx : c.1 = 1 / 2) (hcol : c.2 = 0)
    (hb0 : 0 < b)
    (hndq : IsNonDiameter a b q)
    (hcq : d2 c q = a ^ 2 ∨ d2 c q = b ^ 2) :
    (b ^ 2 = 1 / 2 ∧ q.1 = 1 / 2 ∧ q.2 ^ 2 = 1 / 4) ∨
      (b ^ 2 = 3 / 4 ∧ (q.1 = 1 / 4 ∨ q.1 = 3 / 4) ∧ q.2 ^ 2 = 3 / 16) := by
  have hb2pos : 0 < b ^ 2 := by nlinarith [mul_pos hb0 hb0]
  obtain ⟨s2, t2, hs, ht, hx, hy⟩ := slot_classification a b q hndq
  simp only [d2] at hcq
  dsimp only [slotX, slotYsq] at hx hy
  subst hahalf
  rw [hcx, hcol] at hcq
  -- Substitute the slot signs so each leaf is concrete in `b^2, q.1, q.2`,
  -- and fold the slot coordinates into `hcq`, eliminating the cross-terms.
  rcases hs with hs | hs <;> rcases ht with ht | ht <;> subst hs <;> subst ht <;>
    rw [hx] at hcq <;>
    rcases hcq with hcq | hcq
  · exfalso
    nlinarith [hcq, hx, hy, hb2pos]
  · exfalso
    nlinarith [hcq, hx, hy, hb2pos]
  · right
    have hb23 : b ^ 2 = 3 / 4 := by nlinarith [hcq, hx, hy, hb2pos]
    refine ⟨hb23, ?_, ?_⟩
    · left; nlinarith [hx, hb23]
    · nlinarith [hy, hb23]
  · exfalso
    nlinarith [hcq, hx, hy, hb2pos]
  · right
    have hb23 : b ^ 2 = 3 / 4 := by nlinarith [hcq, hx, hy, hb2pos]
    refine ⟨hb23, ?_, ?_⟩
    · right; nlinarith [hx, hb23]
    · nlinarith [hy, hb23]
  · exfalso
    nlinarith [hcq, hx, hy, hb2pos]
  · left
    have hb21 : b ^ 2 = 1 / 2 := by nlinarith [hcq, hx, hy, hb2pos]
    refine ⟨hb21, ?_, ?_⟩
    · nlinarith [hx, hb21]
    · nlinarith [hy, hb21]
  · exfalso
    nlinarith [hcq, hx, hy, hb2pos]

set_option maxHeartbeats 4000000 in
private lemma oc3_mixed_three
    (a b : ℝ) (Q : Fin 3 → ℝ × ℝ)
    (hinjQ : Function.Injective Q)
    (hpair : ∀ i j : Fin 3, i ≠ j → d2 (Q i) (Q j) = a ^ 2 ∨ d2 (Q i) (Q j) = b ^ 2)
    (hahalf : a = 1 / 2) (hb23 : b ^ 2 = 3 / 4) (hb2pos : 0 < b ^ 2)
    (hx0 : (Q 0).1 = 1 / 4 ∨ (Q 0).1 = 3 / 4)
    (hx1 : (Q 1).1 = 1 / 4 ∨ (Q 1).1 = 3 / 4)
    (hx2 : (Q 2).1 = 1 / 4 ∨ (Q 2).1 = 3 / 4)
    (hy0 : (Q 0).2 ^ 2 = 3 / 16)
    (hy1 : (Q 1).2 ^ 2 = 3 / 16)
    (hy2 : (Q 2).2 ^ 2 = 3 / 16) :
    False := by
  subst hahalf
  have s01 : (Q 1).2 = (Q 0).2 ∨ (Q 1).2 = -(Q 0).2 :=
    oc3_sq_eq_sign (by rw [hy1, hy0])
  have s02 : (Q 2).2 = (Q 0).2 ∨ (Q 2).2 = -(Q 0).2 :=
    oc3_sq_eq_sign (by rw [hy2, hy0])
  rcases hx0 with hx0 | hx0 <;>
    rcases hx1 with hx1 | hx1 <;>
    rcases hx2 with hx2 | hx2 <;>
    rcases s01 with s01 | s01 <;>
    rcases s02 with s02 | s02
  all_goals
    first
    | (have hQ : Q 1 = Q 0 := by apply Prod.ext <;> linarith
       exact (show (1 : Fin 3) ≠ 0 by decide) (hinjQ hQ))
    | (have hQ : Q 2 = Q 0 := by apply Prod.ext <;> linarith
       exact (show (2 : Fin 3) ≠ 0 by decide) (hinjQ hQ))
    | (have hQ : Q 1 = Q 2 := by apply Prod.ext <;> linarith
       exact (show (1 : Fin 3) ≠ 2 by decide) (hinjQ hQ))
    | (have hp := hpair 0 1 (by decide)
       simp only [d2] at hp
       rcases hp with hp | hp <;>
         nlinarith [hp, hx0, hx1, hy0, hy1, s01, hb23, hb2pos])
    | (have hp := hpair 0 2 (by decide)
       simp only [d2] at hp
       rcases hp with hp | hp <;>
         nlinarith [hp, hx0, hx2, hy0, hy2, s02, hb23, hb2pos])
    | (have hp := hpair 1 2 (by decide)
       simp only [d2] at hp
       rcases hp with hp | hp <;>
         nlinarith [hp, hx1, hx2, hy0, hy1, hy2, s01, s02, hb23, hb2pos])

set_option maxHeartbeats 800000 in
private lemma oc3_half_case
    (a b : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) (hab : a ≠ b)
    (c : ℝ × ℝ) (Q : Fin 3 → ℝ × ℝ)
    (hinjQ : Function.Injective Q)
    (hcol : c.2 = 0)
    (hahalf : a = 1 / 2)
    (hndc_ab : IsNonDiameter a b c) (hndQ_ab : ∀ i : Fin 3, IsNonDiameter a b (Q i))
    (hpair_ab : ∀ i j : Fin 3, i ≠ j → d2 (Q i) (Q j) = a ^ 2 ∨ d2 (Q i) (Q j) = b ^ 2)
    (hcross_ab : ∀ i : Fin 3, d2 c (Q i) = a ^ 2 ∨ d2 c (Q i) = b ^ 2) :
    False := by
  classical
  have hcprops := collinear_props a b ha0 ha1 hb0 hb1 c hndc_ab hcol
  have hcx : c.1 = 1 / 2 := by
    rcases hcprops.1 with hca | hcb <;> rcases hcprops.2 with hc1a | hc1b
    · nlinarith [hca, hahalf]
    · nlinarith [hca, hahalf]
    · nlinarith [hc1a, hahalf]
    · have hbhalf : b = 1 / 2 := by nlinarith [hcb, hc1b]
      exfalso
      exact hab (by linarith)
  have hb2pos : 0 < b ^ 2 := by nlinarith [mul_pos hb0 hb0]
  have h0 := oc3_half_classify a b c (Q 0) hahalf hcx hcol hb0 (hndQ_ab 0) (hcross_ab 0)
  have h1 := oc3_half_classify a b c (Q 1) hahalf hcx hcol hb0 (hndQ_ab 1) (hcross_ab 1)
  have h2 := oc3_half_classify a b c (Q 2) hahalf hcx hcol hb0 (hndQ_ab 2) (hcross_ab 2)
  rcases h0 with h0C | h0M
  · rcases h0C with ⟨hb21, hx0, hy0⟩
    have h1C : b ^ 2 = 1 / 2 ∧ (Q 1).1 = 1 / 2 ∧ (Q 1).2 ^ 2 = 1 / 4 := by
      rcases h1 with h1C | h1M
      · exact h1C
      · exfalso
        nlinarith [hb21, h1M.1]
    have h2C : b ^ 2 = 1 / 2 ∧ (Q 2).1 = 1 / 2 ∧ (Q 2).2 ^ 2 = 1 / 4 := by
      rcases h2 with h2C | h2M
      · exact h2C
      · exfalso
        nlinarith [hb21, h2M.1]
    rcases h1C with ⟨_, hx1, hy1⟩
    rcases h2C with ⟨_, hx2, hy2⟩
    exact oc3_same_x_same_sq Q hinjQ (1 / 2) (1 / 4) hx0 hx1 hx2 hy0 hy1 hy2
  · rcases h0M with ⟨hb23, hx0, hy0⟩
    have h1M :
        b ^ 2 = 3 / 4 ∧
          ((Q 1).1 = 1 / 4 ∨ (Q 1).1 = 3 / 4) ∧ (Q 1).2 ^ 2 = 3 / 16 := by
      rcases h1 with h1C | h1M
      · exfalso
        nlinarith [hb23, h1C.1]
      · exact h1M
    have h2M :
        b ^ 2 = 3 / 4 ∧
          ((Q 2).1 = 1 / 4 ∨ (Q 2).1 = 3 / 4) ∧ (Q 2).2 ^ 2 = 3 / 16 := by
      rcases h2 with h2C | h2M
      · exfalso
        nlinarith [hb23, h2C.1]
      · exact h2M
    rcases h1M with ⟨_, hx1, hy1⟩
    rcases h2M with ⟨_, hx2, hy2⟩
    exact oc3_mixed_three a b Q hinjQ hpair_ab hahalf hb23 hb2pos hx0 hx1 hx2 hy0 hy1 hy2

set_option maxHeartbeats 800000 in
/-- **Mixed locus (1 + 3).** One collinear non-diameter point and three distinct
off-line non-diameter points cannot coexist with all pairwise distances in
`{u², v²}`. -/
theorem one_collinear_three_offline
    (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
    (c : ℝ × ℝ) (Q : Fin 3 → ℝ × ℝ)
    (hndc : IsNonDiameter u v c) (hndQ : ∀ i, IsNonDiameter u v (Q i))
    (hcol : c.2 = 0) (hoff : ∀ i, (Q i).2 ≠ 0)
    (hinjQ : Function.Injective Q)
    (hpairQ : ∀ i j, i ≠ j → d2 (Q i) (Q j) = u ^ 2 ∨ d2 (Q i) (Q j) = v ^ 2)
    (hcross : ∀ i, d2 c (Q i) = u ^ 2 ∨ d2 c (Q i) = v ^ 2) :
    False := by
  classical
  rcases collinear_locus u v hu0 hu1 hv0 hv1 c hndc hcol with huhalf | hvhalf | hsum
  · exact oc3_half_case u v hu0 hu1 hv0 hv1 huv c Q hinjQ hcol huhalf hndc hndQ hpairQ hcross
  · have hndc' : IsNonDiameter v u c := by
      constructor
      · rcases hndc.1 with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rcases hndc.2 with h | h
        · exact Or.inr h
        · exact Or.inl h
    have hndQ' : ∀ i : Fin 3, IsNonDiameter v u (Q i) := by
      intro i
      constructor
      · rcases (hndQ i).1 with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rcases (hndQ i).2 with h | h
        · exact Or.inr h
        · exact Or.inl h
    have hpairQ' : ∀ i j : Fin 3, i ≠ j →
        d2 (Q i) (Q j) = v ^ 2 ∨ d2 (Q i) (Q j) = u ^ 2 := by
      intro i j hij
      rcases hpairQ i j hij with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hcross' : ∀ i : Fin 3, d2 c (Q i) = v ^ 2 ∨ d2 c (Q i) = u ^ 2 := by
      intro i
      rcases hcross i with h | h
      · exact Or.inr h
      · exact Or.inl h
    exact oc3_half_case v u hv0 hv1 hu0 hu1 (fun h => huv h.symm)
      c Q hinjQ hcol hvhalf hndc' hndQ' hpairQ' hcross'
  · rcases lt_or_gt_of_ne huv with huvlt | hvult
    · have hu_lt_half : u < 1 / 2 := by nlinarith [hsum, huvlt]
      have hu2neg : u ^ 2 - 1 / 4 < 0 := oc3_sq_sub_quarter_neg hu0 hu_lt_half
      have getQ : ∀ i : Fin 3,
          (Q i).1 = 1 / 2 ∧ (Q i).2 ^ 2 = v ^ 2 - 1 / 4 := by
        intro i
        have h := offline_on_locus u v hu0 hu1 hv0 hv1 hsum (Q i) (hndQ i) (hoff i)
        refine ⟨h.1, ?_⟩
        rcases h.2 with hy | hy
        · exfalso
          nlinarith [sq_nonneg (Q i).2, hy, hu2neg]
        · exact hy
      have h0 := getQ 0
      have h1 := getQ 1
      have h2 := getQ 2
      exact oc3_same_x_same_sq Q hinjQ (1 / 2) (v ^ 2 - 1 / 4)
        h0.1 h1.1 h2.1 h0.2 h1.2 h2.2
    · have hv_lt_half : v < 1 / 2 := by nlinarith [hsum, hvult]
      have hv2neg : v ^ 2 - 1 / 4 < 0 := oc3_sq_sub_quarter_neg hv0 hv_lt_half
      have getQ : ∀ i : Fin 3,
          (Q i).1 = 1 / 2 ∧ (Q i).2 ^ 2 = u ^ 2 - 1 / 4 := by
        intro i
        have h := offline_on_locus u v hu0 hu1 hv0 hv1 hsum (Q i) (hndQ i) (hoff i)
        refine ⟨h.1, ?_⟩
        rcases h.2 with hy | hy
        · exact hy
        · exfalso
          nlinarith [sq_nonneg (Q i).2, hy, hv2neg]
      have h0 := getQ 0
      have h1 := getQ 1
      have h2 := getQ 2
      exact oc3_same_x_same_sq Q hinjQ (1 / 2) (u ^ 2 - 1 / 4)
        h0.1 h1.1 h2.1 h0.2 h1.2 h2.2

end Erdos132.SlotBound
