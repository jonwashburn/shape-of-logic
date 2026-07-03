import IndisputableMonolith.Erdos132.SlotBound

/-!
# Erdős-132: conjugate-pair (pmpair) bridge and kill lemmas

This module is the Lean side of the `pmpair` certificate class from the keystone
decider (`scripts/erdos132/keystone_decider.py::pm_pair_kill`). A **pmpair** core is a
sub-configuration `{p, q, t}` of a candidate 6-point general-slot set in which `p` and
`q` occupy the SAME slot class `(s2, t2)` (hence the same `x` and the same `y²`) with
opposite `y`-signs, and `t` is any third point. The geometry then forces two
square-root-free identities against the alphabet values `c_p = d2 t p`,
`c_q = d2 t q ∈ {1, u², v²}`:

* SUM  : `c_p + c_q = 2·M` where `M = (x_t − x_c)² + Y_t + Y_c`,
* DIFF²: `(c_p − c_q)² = 16·W` where `W = Y_t·Y_c`,

with `x_c, Y_c` (resp. `x_t, Y_t`) the pinned `slotX`/`slotYsq` values of the pair
class (resp. neighbor class). The core-manifest survey
(`scripts/erdos132/_core_manifest.json`) shows all 118 pmpair cores fall into 4
(pair-class, neighbor-class) shapes, and since `M` and `W` are symmetric in the two
classes these collapse to exactly TWO algebraic systems:

* **System A** (pair `(1,w²)` with neighbor `(1,1)`, either orientation):
  `2M = w² + 2`, killed by SUM alone in all 9 alphabet combinations (`linarith`).
* **System B** (pair `(1,1)` with neighbor `(u²,v²)`, either orientation):
  `2M = u² + v² + 1`, `16W = −3u⁴ + 6u²v² + 6u² − 3v⁴ + 6v² − 3`. Eight alphabet
  combinations die on SUM (`linarith`); the `(1,1)` combination forces
  `u² + v² = 1` and then `16W = 12·u²v² = 0`, impossible on the open box.

All verified symbolically (sympy) before formalization; `ring`/`linarith` recheck
everything here, so the Lean file is self-contained ground truth.
-/

set_option maxHeartbeats 1000000

noncomputable section

namespace Erdos132.SlotBound

/-! ## Generic conjugate-pair identities (geometry → algebra) -/

/-- Two distinct points with the same `x` and the same `y²` are conjugate:
the second has the opposite `y`. -/
theorem conj_opp (p q : ℝ × ℝ) (hx : p.1 = q.1) (hy2 : p.2 ^ 2 = q.2 ^ 2)
    (hne : p ≠ q) : q.2 = -p.2 := by
  have hyne : p.2 ≠ q.2 := fun h => hne (Prod.ext hx h)
  have h0 : (q.2 - p.2) * (q.2 + p.2) = 0 := by
    have h : (q.2 - p.2) * (q.2 + p.2) = q.2 ^ 2 - p.2 ^ 2 := by ring
    rw [h, ← hy2]
    ring
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (show p.2 = q.2 by linarith) hyne
  · linarith

/-- **SUM identity.** For a conjugate pair `p, q` and any third point `t`,
`d2 t p + d2 t q = 2·((t.1 − p.1)² + t.2² + p.2²)` — square-root free. -/
theorem conj_sum (p q t : ℝ × ℝ) (hx : p.1 = q.1) (hy2 : p.2 ^ 2 = q.2 ^ 2)
    (hne : p ≠ q) :
    d2 t p + d2 t q = 2 * ((t.1 - p.1) ^ 2 + t.2 ^ 2 + p.2 ^ 2) := by
  have hopp := conj_opp p q hx hy2 hne
  simp only [d2]
  rw [← hx, hopp]
  ring

/-- **DIFF² identity.** `(d2 t p − d2 t q)² = 16·t.2²·p.2²` — the cross term
`y_t·y_p` is squared away. -/
theorem conj_diff_sq (p q t : ℝ × ℝ) (hx : p.1 = q.1) (hy2 : p.2 ^ 2 = q.2 ^ 2)
    (hne : p ≠ q) :
    (d2 t p - d2 t q) ^ 2 = 16 * t.2 ^ 2 * p.2 ^ 2 := by
  have hopp := conj_opp p q hx hy2 hne
  simp only [d2]
  rw [← hx, hopp]
  ring

/-! ## Algebraic kill lemmas (alphabet + box constraints → False) -/

/-- **System-A kill.** If `c_p + c_q = w² + 2` with `c_p, c_q` in the alphabet
`{1, u², v²}` and `0 < u, v < 1`, then `False`. Covers the pmpair shapes
pair `(1,w²)` / neighbor `(1,1)` in either orientation (`w ∈ {u, v}` via
argument order). All 9 alphabet cases are linear kills. -/
theorem pmpair_kill_sysA (u v cp cq : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (hcp : cp = 1 ∨ cp = u ^ 2 ∨ cp = v ^ 2)
    (hcq : cq = 1 ∨ cq = u ^ 2 ∨ cq = v ^ 2)
    (hsum : cp + cq = u ^ 2 + 2) : False := by
  have hu2 : 0 < u ^ 2 := by positivity
  have hu2' : u ^ 2 < 1 := by nlinarith
  have hv2 : 0 < v ^ 2 := by positivity
  have hv2' : v ^ 2 < 1 := by nlinarith
  rcases hcp with rfl | rfl | rfl <;> rcases hcq with rfl | rfl | rfl <;> linarith

/-- **System-B kill.** If `c_p + c_q = u² + v² + 1` and
`(c_p − c_q)² = −3u⁴ + 6u²v² + 6u² − 3v⁴ + 6v² − 3` with `c_p, c_q` in the
alphabet and `0 < u, v < 1`, then `False`. Covers the pmpair shapes
pair `(1,1)` / neighbor `(u²,v²)` in either orientation. Eight alphabet cases
are linear kills from SUM; the `(1,1)` case forces `u² + v² = 1`, whence
`16W = 12·u²v² = 0`, impossible on the open box. -/
theorem pmpair_kill_sysB (u v cp cq : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (hcp : cp = 1 ∨ cp = u ^ 2 ∨ cp = v ^ 2)
    (hcq : cq = 1 ∨ cq = u ^ 2 ∨ cq = v ^ 2)
    (hsum : cp + cq = u ^ 2 + v ^ 2 + 1)
    (hdiff : (cp - cq) ^ 2
      = -3 * u ^ 4 + 6 * u ^ 2 * v ^ 2 + 6 * u ^ 2 - 3 * v ^ 4 + 6 * v ^ 2 - 3) :
    False := by
  have hu2 : 0 < u ^ 2 := by positivity
  have hu2' : u ^ 2 < 1 := by nlinarith
  have hv2 : 0 < v ^ 2 := by positivity
  have hv2' : v ^ 2 < 1 := by nlinarith
  rcases hcp with rfl | rfl | rfl <;> rcases hcq with rfl | rfl | rfl
  -- (1,1): SUM gives u² + v² = 1; DIFF² then reads 0 = 12·u²v², impossible.
  · have hkey : -3 * u ^ 4 + 6 * u ^ 2 * v ^ 2 + 6 * u ^ 2 - 3 * v ^ 4 + 6 * v ^ 2 - 3
        = -3 * (u ^ 2 + v ^ 2 - 1) ^ 2 + 12 * (u ^ 2 * v ^ 2) := by ring
    rw [hkey] at hdiff
    have h1 : u ^ 2 + v ^ 2 - 1 = 0 := by linarith
    rw [h1] at hdiff
    have h2 : 0 < u ^ 2 * v ^ 2 := mul_pos hu2 hv2
    nlinarith [hdiff]
  all_goals linarith

/-! ## End-to-end vertical slices (one per manifest shape)

Each slice takes the raw geometric classification of `p, q, t` (from
`slot_classification_general`), the pairwise-distance alphabet membership of the
two conjugate edges, and the box constraints, and derives `False`. These are the
exact lemma shapes the pmpair oracle dispatches to. The mirrored shapes with
`u ↔ v` swapped are the same lemmas applied at `(v, u)`. -/

/-- Shape S1: pair class `(1, u²)`, neighbor class `(1, 1)` → System A. -/
theorem pmpair_slice_pair1w_nb11 (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (p q t : ℝ × ℝ) (hne : p ≠ q)
    (hpx : p.1 = slotX 1 (u ^ 2)) (hpy : p.2 ^ 2 = slotYsq 1 (u ^ 2))
    (hqx : q.1 = slotX 1 (u ^ 2)) (hqy : q.2 ^ 2 = slotYsq 1 (u ^ 2))
    (htx : t.1 = slotX 1 1) (hty : t.2 ^ 2 = slotYsq 1 1)
    (hcp : d2 t p = 1 ∨ d2 t p = u ^ 2 ∨ d2 t p = v ^ 2)
    (hcq : d2 t q = 1 ∨ d2 t q = u ^ 2 ∨ d2 t q = v ^ 2) :
    False := by
  have hx : p.1 = q.1 := by rw [hpx, hqx]
  have hy2 : p.2 ^ 2 = q.2 ^ 2 := by rw [hpy, hqy]
  have hsum := conj_sum p q t hx hy2 hne
  have hM : 2 * ((t.1 - p.1) ^ 2 + t.2 ^ 2 + p.2 ^ 2) = u ^ 2 + 2 := by
    rw [htx, hpx, hty, hpy]
    simp only [slotX, slotYsq]
    ring
  exact pmpair_kill_sysA u v (d2 t p) (d2 t q) hu0 hu1 hv0 hv1 hcp hcq
    (by rw [hsum, hM])

/-- Shape S2: pair class `(1, 1)`, neighbor class `(1, u²)` → System A
(same algebra as S1; `M`, `W` are symmetric in the two classes). -/
theorem pmpair_slice_pair11_nb1w (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (p q t : ℝ × ℝ) (hne : p ≠ q)
    (hpx : p.1 = slotX 1 1) (hpy : p.2 ^ 2 = slotYsq 1 1)
    (hqx : q.1 = slotX 1 1) (hqy : q.2 ^ 2 = slotYsq 1 1)
    (htx : t.1 = slotX 1 (u ^ 2)) (hty : t.2 ^ 2 = slotYsq 1 (u ^ 2))
    (hcp : d2 t p = 1 ∨ d2 t p = u ^ 2 ∨ d2 t p = v ^ 2)
    (hcq : d2 t q = 1 ∨ d2 t q = u ^ 2 ∨ d2 t q = v ^ 2) :
    False := by
  have hx : p.1 = q.1 := by rw [hpx, hqx]
  have hy2 : p.2 ^ 2 = q.2 ^ 2 := by rw [hpy, hqy]
  have hsum := conj_sum p q t hx hy2 hne
  have hM : 2 * ((t.1 - p.1) ^ 2 + t.2 ^ 2 + p.2 ^ 2) = u ^ 2 + 2 := by
    rw [htx, hpx, hty, hpy]
    simp only [slotX, slotYsq]
    ring
  exact pmpair_kill_sysA u v (d2 t p) (d2 t q) hu0 hu1 hv0 hv1 hcp hcq
    (by rw [hsum, hM])

/-- Shape S3: pair class `(1, 1)`, neighbor class `(u², v²)` → System B. -/
theorem pmpair_slice_pair11_nbuv (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (p q t : ℝ × ℝ) (hne : p ≠ q)
    (hpx : p.1 = slotX 1 1) (hpy : p.2 ^ 2 = slotYsq 1 1)
    (hqx : q.1 = slotX 1 1) (hqy : q.2 ^ 2 = slotYsq 1 1)
    (htx : t.1 = slotX (u ^ 2) (v ^ 2)) (hty : t.2 ^ 2 = slotYsq (u ^ 2) (v ^ 2))
    (hcp : d2 t p = 1 ∨ d2 t p = u ^ 2 ∨ d2 t p = v ^ 2)
    (hcq : d2 t q = 1 ∨ d2 t q = u ^ 2 ∨ d2 t q = v ^ 2) :
    False := by
  have hx : p.1 = q.1 := by rw [hpx, hqx]
  have hy2 : p.2 ^ 2 = q.2 ^ 2 := by rw [hpy, hqy]
  have hsum := conj_sum p q t hx hy2 hne
  have hdiff := conj_diff_sq p q t hx hy2 hne
  have hM : 2 * ((t.1 - p.1) ^ 2 + t.2 ^ 2 + p.2 ^ 2) = u ^ 2 + v ^ 2 + 1 := by
    rw [htx, hpx, hty, hpy]
    simp only [slotX, slotYsq]
    ring
  have hW : 16 * t.2 ^ 2 * p.2 ^ 2
      = -3 * u ^ 4 + 6 * u ^ 2 * v ^ 2 + 6 * u ^ 2 - 3 * v ^ 4 + 6 * v ^ 2 - 3 := by
    rw [hty, hpy]
    simp only [slotX, slotYsq]
    ring
  exact pmpair_kill_sysB u v (d2 t p) (d2 t q) hu0 hu1 hv0 hv1 hcp hcq
    (by rw [hsum, hM]) (by rw [hdiff, hW])

/-- Shape S4: pair class `(u², v²)`, neighbor class `(1, 1)` → System B
(same algebra as S3 by symmetry of `M`, `W`). -/
theorem pmpair_slice_pairuv_nb11 (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (p q t : ℝ × ℝ) (hne : p ≠ q)
    (hpx : p.1 = slotX (u ^ 2) (v ^ 2)) (hpy : p.2 ^ 2 = slotYsq (u ^ 2) (v ^ 2))
    (hqx : q.1 = slotX (u ^ 2) (v ^ 2)) (hqy : q.2 ^ 2 = slotYsq (u ^ 2) (v ^ 2))
    (htx : t.1 = slotX 1 1) (hty : t.2 ^ 2 = slotYsq 1 1)
    (hcp : d2 t p = 1 ∨ d2 t p = u ^ 2 ∨ d2 t p = v ^ 2)
    (hcq : d2 t q = 1 ∨ d2 t q = u ^ 2 ∨ d2 t q = v ^ 2) :
    False := by
  have hx : p.1 = q.1 := by rw [hpx, hqx]
  have hy2 : p.2 ^ 2 = q.2 ^ 2 := by rw [hpy, hqy]
  have hsum := conj_sum p q t hx hy2 hne
  have hdiff := conj_diff_sq p q t hx hy2 hne
  have hM : 2 * ((t.1 - p.1) ^ 2 + t.2 ^ 2 + p.2 ^ 2) = u ^ 2 + v ^ 2 + 1 := by
    rw [htx, hpx, hty, hpy]
    simp only [slotX, slotYsq]
    ring
  have hW : 16 * t.2 ^ 2 * p.2 ^ 2
      = -3 * u ^ 4 + 6 * u ^ 2 * v ^ 2 + 6 * u ^ 2 - 3 * v ^ 4 + 6 * v ^ 2 - 3 := by
    rw [hty, hpy]
    simp only [slotX, slotYsq]
    ring
  exact pmpair_kill_sysB u v (d2 t p) (d2 t q) hu0 hu1 hv0 hv1 hcp hcq
    (by rw [hsum, hM]) (by rw [hdiff, hW])

end Erdos132.SlotBound
