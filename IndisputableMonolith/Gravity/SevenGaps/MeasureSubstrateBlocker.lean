import IndisputableMonolith.Gravity.SevenGaps.ExactShellGaugePreflight
import IndisputableMonolith.Gravity.SevenGaps.MeasureInvarianceNoGo

/-!
# Path-sum measure: exact substrate blocker

## Status: THEOREM

`MeasureInvarianceNoGo` proves that relabeling invariance, positivity, and
normalization do not select a path-sum measure. `ExactShellGaugePreflight`
proves that the gauge-counting mass equals `1 / |Aut|`, while recording the
uniform gauge-density principle as a MODEL premise.

This file identifies that premise exactly. A class mass satisfies normalized
gauge counting if its mass times the number of `(labeled copy, relabeling
witness)` pairs equals the number of labeled copies. The main equivalence says
that this principle holds exactly when every class has the `1 / |Aut|` mass.

The explicit two-point class proves the principle has real content: the
quotient-uniform class mass fails it. Thus the remaining substrate task cannot
be discharged by the invariance axioms or by renaming uniform quotient
counting. It requires a derivation of normalized gauge counting from richer
ledger structure. This module supplies the certified blocker and flips no
`FullTheoryLedger` flag.

No `sorry`, `admit`, new axiom, or `native_decide`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace MeasureSubstrateBlocker

open PathSumMeasure
open ExactShellGaugePreflight

noncomputable section

/-- The exact extra principle used by the gauge-counting derivation: class
mass times gauge-witness volume equals labeled orbit size. -/
def GaugeCountingPrinciple {B : ℕ}
    (ν : TriangulationClass B → ℝ) : Prop :=
  ∀ c, ν c * (pairCountClass c : ℝ) = (orbitCardClass c : ℝ)

/-- The counting-defined mass satisfies normalized gauge counting. -/
theorem gaugeOrbitMass_satisfies {B : ℕ} :
    GaugeCountingPrinciple (gaugeOrbitMass :
      TriangulationClass B → ℝ) :=
  gaugeOrbitMass_mul_pairCount

/-- Normalized gauge counting selects exactly the counting-defined mass.
This packages existence and uniqueness in one equivalence. -/
theorem gaugeCountingPrinciple_iff_eq_gaugeOrbitMass {B : ℕ}
    (ν : TriangulationClass B → ℝ) :
    GaugeCountingPrinciple ν ↔ ν = gaugeOrbitMass := by
  constructor
  · intro hν
    funext c
    exact gaugeCountingMass_unique ν hν c
  · intro hν
    subst hν
    exact gaugeOrbitMass_satisfies

/-- **Exact blocker theorem.** Normalized gauge counting is equivalent to
assigning `1 / |Aut K|` to every represented bounded complex. The forward
direction is the orbit-stabilizer derivation. The reverse direction shows
that no weaker unnamed condition is hidden in the counting statement. -/
theorem gaugeCountingPrinciple_iff_mu_on_representatives {B : ℕ}
    (ν : TriangulationClass B → ℝ) :
    GaugeCountingPrinciple ν ↔
      ∀ K : BoundedComplex B,
        ν (Quotient.mk (relabelSetoid B) K) = mu K := by
  rw [gaugeCountingPrinciple_iff_eq_gaugeOrbitMass]
  constructor
  · intro hν K
    rw [hν]
    exact gaugeOrbitMass_eq_mu K
  · intro hν
    funext c
    refine Quotient.inductionOn c ?_
    intro K
    exact (hν K).trans (gaugeOrbitMass_eq_mu K).symm

/-- Uniform mass on quotient classes. This is the live decoy admitted by
the weaker invariance requirements. -/
def uniformClassMass {B : ℕ} : TriangulationClass B → ℝ :=
  fun _ => 1

/-- The quotient-uniform decoy fails normalized gauge counting on the
two-point class, where the required mass is `1/2`. This proves that the
extra principle is discriminating and does not restate class invariance. -/
theorem uniformClassMass_not_gaugeCounting (B : ℕ) (hB : 2 ≤ B) :
    ¬ GaugeCountingPrinciple
      (uniformClassMass : TriangulationClass B → ℝ) := by
  intro h
  have hmu :=
    (gaugeCountingPrinciple_iff_mu_on_representatives
      (uniformClassMass : TriangulationClass B → ℝ)).mp h
      (MeasureInvarianceNoGo.twoPointComplex B hB)
  unfold uniformClassMass at hmu
  rw [MeasureInvarianceNoGo.mu_twoPointComplex B hB] at hmu
  norm_num at hmu

/-- **Certified blocker package.** Gauge counting exists and selects
`1/|Aut|`; the quotient-uniform decoy fails it. What remains is precisely a
ledger theorem supplying `GaugeCountingPrinciple`, not more invariance. -/
theorem substrate_measure_blocker_certificate (B : ℕ) (hB : 2 ≤ B) :
    GaugeCountingPrinciple
        (gaugeOrbitMass : TriangulationClass B → ℝ) ∧
      (∀ ν : TriangulationClass B → ℝ,
        GaugeCountingPrinciple ν ↔
          ∀ K : BoundedComplex B,
            ν (Quotient.mk (relabelSetoid B) K) = mu K) ∧
      ¬ GaugeCountingPrinciple
        (uniformClassMass : TriangulationClass B → ℝ) :=
  ⟨gaugeOrbitMass_satisfies,
    gaugeCountingPrinciple_iff_mu_on_representatives,
    uniformClassMass_not_gaugeCounting B hB⟩

end

end MeasureSubstrateBlocker
end SevenGaps
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.SevenGaps.MeasureSubstrateBlocker.gaugeCountingPrinciple_iff_mu_on_representatives
#print axioms IndisputableMonolith.Gravity.SevenGaps.MeasureSubstrateBlocker.uniformClassMass_not_gaugeCounting
#print axioms IndisputableMonolith.Gravity.SevenGaps.MeasureSubstrateBlocker.substrate_measure_blocker_certificate
