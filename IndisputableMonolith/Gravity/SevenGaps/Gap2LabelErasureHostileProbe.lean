import IndisputableMonolith.Gravity.SevenGaps.Gap2LabelErasure
import IndisputableMonolith.Gravity.SevenGaps.Gap2JEhrhartSpan

/-!
# Hostile probe: Gap2LabelErasure G1 / directed-Aut / fibre-count (2026-07-30)

Uncommitted adversarial module.  Attacks A (G1 dependency graph), C (definitional
collapse), D (directed Aut recomputation via kernel enumeration), E (G2), G (vacuity).
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2LabelErasureHostileProbe

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume
open Gap2GluingDerivation Gap2PostingCostDerivation Gap2JEhrhartSpan Gap2LabelErasure
open scoped Classical

/-! ## A. G1 dependency-graph probe -/

#print labeledWeight
#print RelabelInvariant
#print rename
#print Gap2GaugeVolume.push
#print BoundedComplex
#check pushforward_labeledWeight_eq_gauge_divisor
#print classMass

theorem g1_hyp_defs_avoid_aut :
    (labeledWeight 0 = (BoundedComplex 0 → ℝ))
      ∧ (∀ (w : labeledWeight 1),
          RelabelInvariant w ↔
            ∀ (K : BoundedComplex 1) (σv : Equiv.Perm (Fin K.nV))
              (σe : Equiv.Perm (Fin K.nE)) (σt : Equiv.Perm (Fin K.nT)),
              w (rename K σv σe σt) = w K)
      ∧ (∀ (K : BoundedComplex 1) (σv : Equiv.Perm (Fin K.nV))
            (σe : Equiv.Perm (Fin K.nE)) (σt : Equiv.Perm (Fin K.nT)),
          rename K σv σe σt = Gap2GaugeVolume.push K (σv, σe, σt)) :=
  ⟨rfl, fun _ => Iff.rfl, fun _ _ _ _ => rfl⟩

theorem push_preserves_ordered_incidence (K : BoundedComplex 4)
    (g : Gap2GaugeVolume.SectorGroup K) (e : Fin (push K g).nE) :
    (push K g).edgeVerts e
      = Prod.map g.1 g.1 (K.edgeVerts (g.2.1.symm e)) :=
  rfl

theorem relabel_edge_comm_is_ordered {K K' : BoundedComplex 4} (r : Relabel K K')
    (e : Fin K.nE) :
    K'.edgeVerts (r.eEquiv e) = Prod.map r.vEquiv r.vEquiv (K.edgeVerts e) :=
  r.edge_comm e

/-! ## C. Fibre-count / definitional-collapse probe -/

/-- `classMass` is definitionally a fibre sum (see `#print classMass`); no Aut factor. -/
theorem classMass_def_is_fibre_sum :
    (∀ (w : BoundedComplex 1 → ℝ) (c : TriangulationClass 1),
      classMass w c
        = ∑ K : BoundedComplex 1,
            if Quotient.mk (relabelSetoid 1) K = c then w K else 0) := by
  intro w c
  rfl

theorem orbit_stabilizer_is_proved (K : BoundedComplex 1) :
    gaugeOrbitCard K * Nat.card (Aut K)
      = Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) :=
  orbitCard_mul_autCard K

theorem corollary_factor_explicit {c : LetterCost} (hc : Equivariant c) (K : BoundedComplex 1) :
    erasePush (fun K' : BoundedComplex 1 => Real.exp (-(historyCost c 1 K'))) (erase 1 K)
      = Real.exp (-(historyCost c 1 K))
          * ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)
          / (Nat.card (Aut K) : ℝ) :=
  (gibbsWeight_is_the_erasure_jacobian hc K).1

/-! ## D. Directed Aut recomputation at (4,2,0)

`Aut K = Relabel K K` injects into `Perm nV × Perm nE × Perm nT`
(`Relabel.toEquivTriple_injective`).  For `nT = 0`, Aut membership is exactly
ordered edge-commutation on `(σv, σe)`.  Kernel enumeration of that predicate
is the C16 receipt. -/

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

theorem twoEdgeComplex_counts :
    twoEdgeComplex.nV = 4 ∧ twoEdgeComplex.nE = 2 ∧ twoEdgeComplex.nT = 0 :=
  ⟨rfl, rfl, rfl⟩

def edgeCommOK (ev : Fin 2 → Fin 4 × Fin 4)
    (σv : Equiv.Perm (Fin 4)) (σe : Equiv.Perm (Fin 2)) : Bool :=
  decide (∀ e : Fin 2, ev (σe e) = Prod.map σv σv (ev e))

def twoEdgeEV : Fin 2 → Fin 4 × Fin 4 :=
  fun e => if e = 0 then (0, 1) else (2, 3)

def pathPlusEV : Fin 2 → Fin 4 × Fin 4 :=
  fun e => if e = 0 then (0, 1) else (1, 2)

def twoEdgeAutCount : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 2))).filter
    fun p => edgeCommOK twoEdgeEV p.1 p.2).card

def pathPlusAutCount : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 2))).filter
    fun p => edgeCommOK pathPlusEV p.1 p.2).card

/-- Kernel: two disjoint directed edges have exactly 2 ordered Aut candidates. -/
theorem twoEdge_autCount_eq_two : twoEdgeAutCount = 2 := by native_decide

/-- Kernel: directed 2-path + isolated vertex has exactly 1 ordered Aut candidate. -/
theorem pathPlus_autCount_eq_one : pathPlusAutCount = 1 := by native_decide

/-- Component swap of the two directed edges satisfies ordered edge_comm. -/
def twoEdgeSwapV : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap (1 : Fin 4) 3)

theorem twoEdge_component_swap_ok :
    edgeCommOK twoEdgeEV twoEdgeSwapV (Equiv.swap (0 : Fin 2) 1) = true := by
  native_decide

/-- Identity also satisfies edge_comm (so the two candidates are inhabited). -/
theorem twoEdge_id_ok :
    edgeCommOK twoEdgeEV (1 : Equiv.Perm (Fin 4)) (1 : Equiv.Perm (Fin 2)) = true := by
  native_decide

/-- Edge reversal fails ordered edge_comm (directed carrier; undirected flip absent). -/
theorem twoEdge_edge_flip_fails_comm :
    edgeCommOK twoEdgeEV (Equiv.swap (0 : Fin 4) 1) (1 : Equiv.Perm (Fin 2)) = false := by
  native_decide

/-- Class-mass / mu ratio from enumerated Aut counts: 1/2, not the undirected 1/4. -/
theorem enumerated_mu_ratio_is_half :
    (1 : ℚ) / twoEdgeAutCount / ((1 : ℚ) / pathPlusAutCount) = 1 / 2 := by
  rw [twoEdge_autCount_eq_two, pathPlus_autCount_eq_one]
  norm_num

theorem dust_aut_arithmetic :
    Nat.card (Aut (dust 1)) = 1
      ∧ Nat.card (Aut (dunion (dust 1) (dust 1))) = 2 := by
  constructor
  · rw [autCard_dust]; decide
  · rw [autCard_congr (dunion_dust_equivalent 1 1), autCard_dust]; decide

theorem pathPlus_aut_inhabited : Nonempty (Aut pathPlusIsolated) :=
  ⟨Relabel.refl _⟩

/-! ## E. G2 locality -/

theorem locallyAdditive_is_explicit :
    LocallyAdditive (fun _ _ => (0 : ℝ)) := by
  intro B B' A C; simp

theorem uniform_quantifies_all_Q :
    ¬ ∃ (Q : ∀ B : ℕ, BoundedComplex B → ℝ) (zV zE zT : ℝ),
        (∀ (B B' : ℕ) (A : BoundedComplex B) (C : BoundedComplex B'),
          Q (B + B') (dunion A C) = Q B A * Q B' C)
          ∧ (∀ (B : ℕ) (K : BoundedComplex B),
              Q B K * zV ^ K.nV * zE ^ K.nE * zT ^ K.nT
                = (Nat.card (Aut K) : ℝ)) :=
  uniform_is_not_a_local_pushforward

/-! ## G. Vacuity -/

theorem relabelInvariant_inhabited_constant :
    RelabelInvariant (fun _ : BoundedComplex 2 => (1 : ℝ)) :=
  relabelInvariant_one

theorem relabelInvariant_inhabited_equivariant_numerator :
    RelabelInvariant
      (fun K : BoundedComplex 2 => Real.exp (-(historyCost (incidenceCost 1) 2 K))) :=
  relabelInvariant_exp_neg_history (incidenceCost_equivariant 1)

theorem dust_twin_admissible_real :
    (dust 1 : BoundedComplex 1).nV = 1 ∧ (dust 1).nE = 0 ∧ (dust 1).nT = 0
      ∧ Equivalent (dunion (dust 1) (dust 1)) (dust 2) :=
  dust_twin_admissible

theorem wreath_proved_not_assumed :
    Nat.card (Aut (dunion (dust 1) (dust 1)))
      = 2 * (Nat.card (Aut (dust 1))) ^ 2 :=
  autCard_dust_twin

theorem flag_still_false : labelErasureIndex.measure_flag_moved = false :=
  index_flag_unmoved

#print axioms g1_hyp_defs_avoid_aut
#print axioms push_preserves_ordered_incidence
#print axioms classMass_def_is_fibre_sum
#print axioms orbit_stabilizer_is_proved
#print axioms corollary_factor_explicit
#print axioms twoEdge_autCount_eq_two
#print axioms pathPlus_autCount_eq_one
#print axioms twoEdge_component_swap_ok
#print axioms twoEdge_edge_flip_fails_comm
#print axioms enumerated_mu_ratio_is_half
#print axioms dust_aut_arithmetic
#print axioms relabelInvariant_inhabited_equivariant_numerator
#print axioms dust_twin_admissible_real
#print axioms wreath_proved_not_assumed
#print axioms uniform_quantifies_all_Q
#print axioms flag_still_false

end Gap2LabelErasureHostileProbe
end SevenGaps
end Gravity
end IndisputableMonolith
