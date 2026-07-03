import Mathlib
import IndisputableMonolith.Cosmology.InterfaceComponentBound

/-!
# Lattice-ball cardinalities: the area and volume laws of the coarsening engine

The scale-adaptive coarsening engine accumulates its world on an L1 ball that grows by one rung per
recognition cycle: the 2D diamond `|x| + |y| ≤ t` and the 3D octahedron `|x| + |y| + |z| ≤ t`. The
numeric runs report the *total* cell count after `t` cycles ("the diamond grew to 1201 cells" at
`t = 24`; "the octahedron grew to 2625 cells" at `t = 12`). This module lifts those counts to closed
forms, as THEOREMs over `ℕ`, with no `sorry` and no new axioms.

* `Diamond.card_ball t = 2 t² + 2 t + 1` (the centered square number). At `t = 24` this is `1201`.
* `Octahedron.three_mul_card_ball t : 3 * card (ball t) = 4 t³ + 6 t² + 8 t + 3` (the centered
  octahedral number `(2t+1)(2t²+2t+3)/3`, division-free). At `t = 12` the count is `2625`.

Why this matters for the simulation: the accumulated world is `Θ(t^d)` while the recognition-active
frontier born each cycle is the shell `card (ball t) - card (ball (t-1))`, which these laws make
`4 t` (diamond) and `4 t² + 2` (octahedron), i.e. `Θ(t^{d-1})`. The active fraction
`shell / ball → 0`: the cost localizes to a perimeter. The interface-component bound
(`InterfaceComponentBound`) and these volume laws together are the geometric backbone of the
sub-extensivity claim of Phases 13/14/15.

Both proofs reduce a `d`-dimensional ball to a fibered sum over the first coordinate of `(d-1)`-balls,
so the octahedron law is built on the diamond law. The diamond slice over a fixed `x` is the integer
interval `[-(t - |x|), t - |x|]`, of width `2(t - |x|) + 1`; summing that over `x ∈ [-t, t]` gives the
closed form by induction (peeling the two new endpoints each step).
-/

namespace IndisputableMonolith
namespace Cosmology
namespace LatticeBallVolume

open Finset
open scoped BigOperators

/-! ### The 1-D slice: lattice points in `[-t, t]` with `|x| + |y| ≤ t` for fixed `x`. -/

/-- For `|x| ≤ t`, the `y`-slice `{ y ∈ [-t, t] : |x| + |y| ≤ t }` is exactly the interval
`[-(t - |x|), t - |x|]`, hence has `2 (t - |x|) + 1` points. -/
theorem slice_card (t : ℕ) (x : ℤ) (hx : x.natAbs ≤ t) :
    ((Finset.Icc (-(t : ℤ)) t).filter (fun y => x.natAbs + y.natAbs ≤ t)).card
      = 2 * (t - x.natAbs) + 1 := by
  have hset : (Finset.Icc (-(t : ℤ)) t).filter (fun y => x.natAbs + y.natAbs ≤ t)
      = Finset.Icc (-(((t - x.natAbs : ℕ)) : ℤ)) (((t - x.natAbs : ℕ)) : ℤ) := by
    apply Finset.ext
    intro y
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hset, Int.card_Icc]
  omega

/-! ### The 2-D diamond area law. -/

/-- Fibered form of the diamond cardinality: sum the slice widths over the first coordinate. -/
theorem diamond_card_eq_sum (t : ℕ) :
    (InterfaceComponentBound.Diamond.ball t).card
      = ∑ x ∈ Finset.Icc (-(t : ℤ)) t, (2 * (t - x.natAbs) + 1) := by
  have hb : InterfaceComponentBound.Diamond.ball t
      = (Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t).filter
          (fun p => p.1.natAbs + p.2.natAbs ≤ t) := rfl
  rw [hb, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.mem_Icc] at hx
  have hxnat : x.natAbs ≤ t := by omega
  dsimp only
  rw [← slice_card t x hxnat, Finset.card_filter]

/-- The symmetric-interval sum `∑_{x ∈ [-t,t]} (2 (t - |x|) + 1) = 2 t² + 2 t + 1`, by induction
peeling the two new endpoints `±(t+1)` each step. -/
theorem outer_sum_2d (t : ℕ) :
    ∑ x ∈ Finset.Icc (-(t : ℤ)) t, (2 * (t - x.natAbs) + 1) = 2 * t ^ 2 + 2 * t + 1 := by
  induction t with
  | zero => simp
  | succ n ih =>
    have hsplit : Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1)
        = insert (-((n : ℤ) + 1)) (insert ((n : ℤ) + 1) (Finset.Icc (-(n : ℤ)) (n : ℤ))) := by
      apply Finset.ext
      intro z
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hmem2 : ((n : ℤ) + 1) ∉ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    have hmem1 : (-((n : ℤ) + 1))
        ∉ insert ((n : ℤ) + 1) (Finset.Icc (-(n : ℤ)) (n : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hcast : (((n : ℕ) + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [show (((n : ℕ) + 1 : ℕ) : ℤ) = (n : ℤ) + 1 from hcast]
    rw [hsplit, Finset.sum_insert hmem1, Finset.sum_insert hmem2]
    -- endpoint contributions: |±(n+1)| = n+1, so each summand is 2*((n+1) - (n+1)) + 1 = 1
    have hendL : 2 * ((n + 1) - (-((n : ℤ) + 1)).natAbs) + 1 = 1 := by
      have : (-((n : ℤ) + 1)).natAbs = n + 1 := by
        rw [Int.natAbs_neg]; omega
      rw [this]; omega
    have hendR : 2 * ((n + 1) - (((n : ℤ) + 1)).natAbs) + 1 = 1 := by
      have : (((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [this]; omega
    rw [hendL, hendR]
    -- rewrite the inner sum's summand: for x ∈ [-n,n], (n+1) - |x| = (n - |x|) + 1
    have hcongr : ∑ x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), (2 * ((n + 1) - x.natAbs) + 1)
        = ∑ x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ((2 * (n - x.natAbs) + 1) + 2) := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [Finset.mem_Icc] at hx
      have hxnat : x.natAbs ≤ n := by omega
      omega
    rw [hcongr, Finset.sum_add_distrib, ih, Finset.sum_const]
    have hcard : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
      rw [Int.card_Icc]; omega
    rw [hcard]
    ring

/-- **The 2-D diamond area law, every radius.** The L1 ball `|x| + |y| ≤ t` has exactly
`2 t² + 2 t + 1` lattice points (the centered square number). At `t = 24` this is `1201`, the cell
count the 2D coarsening run reports. THEOREM over `ℕ`. -/
theorem Diamond.card_ball (t : ℕ) :
    (InterfaceComponentBound.Diamond.ball t).card = 2 * t ^ 2 + 2 * t + 1 := by
  rw [diamond_card_eq_sum, outer_sum_2d]

/-! ### The 3-D octahedron volume law (reduces to the diamond law fiber by fiber). -/

/-- Fibered form of the octahedron cardinality: each `x`-fiber is a diamond of radius `t - |x|`. -/
theorem octa_card_eq_sum (t : ℕ) :
    (InterfaceComponentBound.Octahedron.ball t).card
      = ∑ x ∈ Finset.Icc (-(t : ℤ)) t,
          (InterfaceComponentBound.Diamond.ball (t - x.natAbs)).card := by
  have hb : InterfaceComponentBound.Octahedron.ball t
      = (Finset.Icc (-(t : ℤ)) t ×ˢ (Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t)).filter
          (fun p => p.1.natAbs + p.2.1.natAbs + p.2.2.natAbs ≤ t) := rfl
  rw [hb, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.mem_Icc] at hx
  have hxnat : x.natAbs ≤ t := by omega
  dsimp only
  -- the (y,z)-fiber over x equals the diamond of radius (t - |x|)
  have hfib : (Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t).filter
        (fun q : ℤ × ℤ => x.natAbs + q.1.natAbs + q.2.natAbs ≤ t)
      = InterfaceComponentBound.Diamond.ball (t - x.natAbs) := by
    apply Finset.ext
    rintro ⟨y, z⟩
    rw [InterfaceComponentBound.Diamond.mem_ball_iff]
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_product]
    omega
  -- the inner (y,z)-sum is exactly the diamond-fiber card
  rw [← hfib, Finset.card_filter]

/-- The octahedron outer sum reduces to the centered-octahedral recurrence. We prove the
division-free form `3 · ∑ = 4 t³ + 6 t² + 8 t + 3` by induction, reusing the diamond area law for
each fiber and the 2-D outer sum for the `∑ (t - |x|) = t²` identity that the step needs. -/
theorem three_mul_outer_sum_3d (t : ℕ) :
    3 * (∑ x ∈ Finset.Icc (-(t : ℤ)) t,
            (InterfaceComponentBound.Diamond.ball (t - x.natAbs)).card)
      = 4 * t ^ 3 + 6 * t ^ 2 + 8 * t + 3 := by
  -- rewrite each fiber card via the diamond area law
  have hrw : ∀ s : ℕ, ∑ x ∈ Finset.Icc (-(s : ℤ)) s,
        (InterfaceComponentBound.Diamond.ball (s - x.natAbs)).card
      = ∑ x ∈ Finset.Icc (-(s : ℤ)) s,
          (2 * (s - x.natAbs) ^ 2 + 2 * (s - x.natAbs) + 1) := by
    intro s
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Diamond.card_ball]
  rw [hrw]
  -- now an ℕ identity about a symmetric-interval sum of a quadratic in (t - |x|)
  induction t with
  | zero => simp
  | succ n ih =>
    have hsplit : Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1)
        = insert (-((n : ℤ) + 1)) (insert ((n : ℤ) + 1) (Finset.Icc (-(n : ℤ)) (n : ℤ))) := by
      apply Finset.ext
      intro z
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hmem2 : ((n : ℤ) + 1) ∉ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    have hmem1 : (-((n : ℤ) + 1))
        ∉ insert ((n : ℤ) + 1) (Finset.Icc (-(n : ℤ)) (n : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hcast : (((n : ℕ) + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [show (((n : ℕ) + 1 : ℕ) : ℤ) = (n : ℤ) + 1 from hcast]
    rw [hsplit, Finset.sum_insert hmem1, Finset.sum_insert hmem2]
    have hendL : 2 * ((n + 1) - (-((n : ℤ) + 1)).natAbs) ^ 2
          + 2 * ((n + 1) - (-((n : ℤ) + 1)).natAbs) + 1 = 1 := by
      have : (-((n : ℤ) + 1)).natAbs = n + 1 := by rw [Int.natAbs_neg]; omega
      rw [this]; simp
    have hendR : 2 * ((n + 1) - (((n : ℤ) + 1)).natAbs) ^ 2
          + 2 * ((n + 1) - (((n : ℤ) + 1)).natAbs) + 1 = 1 := by
      have : (((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [this]; simp
    rw [hendL, hendR]
    -- inner-sum congruence: g((n+1) - |x|) = g((n - |x|)) + 4*(n+1 - |x|) for |x| ≤ n
    have hcongr : ∑ x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
            (2 * ((n + 1) - x.natAbs) ^ 2 + 2 * ((n + 1) - x.natAbs) + 1)
        = ∑ x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
            ((2 * (n - x.natAbs) ^ 2 + 2 * (n - x.natAbs) + 1)
              + (4 * (n - x.natAbs) + 4)) := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [Finset.mem_Icc] at hx
      have hxnat : x.natAbs ≤ n := by omega
      have hsub : (n + 1) - x.natAbs = (n - x.natAbs) + 1 := by omega
      rw [hsub]; ring
    rw [hcongr, Finset.sum_add_distrib]
    have hcard : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
      rw [Int.card_Icc]; omega
    set S := ∑ x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ),
        (2 * (n - x.natAbs) ^ 2 + 2 * (n - x.natAbs) + 1) with hSdef
    set T := ∑ x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), (4 * (n - x.natAbs) + 4) with hTdef
    -- closed form for the residual increment sum T via the 2-D outer sum
    have hT : T = 4 * n ^ 2 + 8 * n + 4 := by
      rw [hTdef]
      have hcongr2 : ∑ x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), (4 * (n - x.natAbs) + 4)
          = ∑ x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), (2 * (2 * (n - x.natAbs) + 1) + 2) := by
        refine Finset.sum_congr rfl (fun x _ => ?_); ring
      rw [hcongr2, Finset.sum_add_distrib, ← Finset.mul_sum, outer_sum_2d, Finset.sum_const, hcard]
      simp only [smul_eq_mul]; ring
    -- regroup so that `3 * S` (the inductive hypothesis) appears as a subterm, then close by ring
    have hcomb : 3 * (1 + (1 + (S + T))) = 3 * S + (3 * T + 6) := by ring
    rw [hcomb, ih, hT]
    ring

/-- **The 3-D octahedron volume law, every radius.** The L1 ball `|x| + |y| + |z| ≤ t` has exactly
the centered octahedral number `(2t+1)(2t²+2t+3)/3` of lattice points, stated division-free as
`3 · card = 4 t³ + 6 t² + 8 t + 3`. At `t = 12` the count is `2625`, the cell count the 3D coarsening
run reports. THEOREM over `ℕ`, reducing fiber by fiber to the diamond area law. -/
theorem Octahedron.three_mul_card_ball (t : ℕ) :
    3 * (InterfaceComponentBound.Octahedron.ball t).card = 4 * t ^ 3 + 6 * t ^ 2 + 8 * t + 3 := by
  rw [octa_card_eq_sum, three_mul_outer_sum_3d]

/-- The octahedron count at the radius the 3D run uses: `card (ball 12) = 2625`. -/
theorem Octahedron.card_ball_twelve :
    (InterfaceComponentBound.Octahedron.ball 12).card = 2625 := by
  have h := Octahedron.three_mul_card_ball 12
  norm_num at h
  omega

/-- The diamond count at the radius the 2D run uses: `card (ball 24) = 1201`. -/
theorem Diamond.card_ball_twentyfour :
    (InterfaceComponentBound.Diamond.ball 24).card = 1201 := by
  rw [Diamond.card_ball]; norm_num

/-! ### Boundary-shell laws: the per-cycle growth lives on a codimension-1 shell.

The coarsening engine grows the world one radius per cycle, so the cells *added* at cycle `t+1`
are the shell `ball (t+1) \ ball t`, whose count is `card_ball (t+1) - card_ball t`. These
recurrences are the discrete derivative of the Phase-49 area/volume laws, and they are the exact
geometric content of "the cost localizes to a perimeter / a surface": in 2D the per-cycle growth is
linear (`4(t+1)`, a 1-D perimeter), in 3D it is quadratic (`4(t+1)² + 2`, a 2-D surface). This is the
geometric boundary shell of newly recognized cells; it is distinct from the charge-dependent
bichromatic interface bounded in `InterfaceComponentBound`. -/

/-- **The 2-D perimeter (per-cycle growth) law.** Going from radius `t` to `t+1` adds exactly
`4(t+1)` cells: the new cells form a 1-D perimeter shell. Equivalently, the shell at radius `s ≥ 1`
has `4s` cells. Immediate from the area law `Diamond.card_ball`. -/
theorem Diamond.shell_card (t : ℕ) :
    (InterfaceComponentBound.Diamond.ball (t + 1)).card
      = (InterfaceComponentBound.Diamond.ball t).card + 4 * (t + 1) := by
  simp only [Diamond.card_ball]; ring

/-- **The 3-D surface (per-cycle growth) law, division-free.** Going from radius `t` to `t+1` adds
exactly `4(t+1)² + 2` cells (so `3 ·` the increment is `12(t+1)² + 6`): the new cells form a 2-D
surface shell, the sharpest sub-extensive growth `~ V^(2/3)`. Immediate from the volume law
`Octahedron.three_mul_card_ball`. -/
theorem Octahedron.three_mul_shell_card (t : ℕ) :
    3 * (InterfaceComponentBound.Octahedron.ball (t + 1)).card
      = 3 * (InterfaceComponentBound.Octahedron.ball t).card + (12 * (t + 1) ^ 2 + 6) := by
  simp only [Octahedron.three_mul_card_ball]; ring

/-- The last 2-D shell the run adds (radius 24) has `4 · 24 = 96` cells. -/
theorem Diamond.shell_card_twentyfour :
    (InterfaceComponentBound.Diamond.ball 24).card
      = (InterfaceComponentBound.Diamond.ball 23).card + 96 := by
  have h := Diamond.shell_card 23; norm_num at h ⊢; exact h

/-- The last 3-D shell the run adds (radius 12) has `4 · 12² + 2 = 578` cells (so `3 · 578 = 1734`). -/
theorem Octahedron.three_mul_shell_card_twelve :
    3 * (InterfaceComponentBound.Octahedron.ball 12).card
      = 3 * (InterfaceComponentBound.Octahedron.ball 11).card + 1734 := by
  have h := Octahedron.three_mul_shell_card 11; norm_num at h ⊢; exact h

end LatticeBallVolume
end Cosmology
end IndisputableMonolith
