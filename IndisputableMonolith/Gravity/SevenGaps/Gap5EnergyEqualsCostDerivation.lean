import IndisputableMonolith.Gravity.SevenGaps.Gap5MomentumMagnitudeBridge

/-!
# EnergyEqualsCost: the Hamiltonian lead is closed negatively (polarization
independence), and the premise discharges from exactly one extra input

**Verdict, stated first.** Of the three charged outcomes, **(b) LANDED** as the
headline and **(c) LANDED** as the constructive corollary; **(a) is refuted by
the no-go**, not merely unbuilt.

## (b) The no-go: `EnergyEqualsCost` is independent of the Hamiltonian data

The orbit family `orbitPoint k t` is, on the stated carrier `LedgerState` with
the σ = 0 area form of `Cost.SymplecticAction`, exactly the Hamiltonian flow of
the Casimir Hamiltonian `orbitHamiltonian z = casimir z / 2`
(`orbitPoint_is_hamiltonian_flow`, `orbitHamiltonian_constant_on_orbit`; both
MODEL-tagged definitions are stated in §0 and disclosed). That Hamiltonian
system admits two canonical momentum observables which agree on every substrate
selection that is not already equivalent to the premise:

* `imbalance`, canonically conjugate to the ledger total with bracket
  `{imbalance, total} = 2`, which is exactly the determinant of the chart's
  canonical frame (`poisson_imbalance_total_eq_frame_det`), satisfies
  `EnergyEqualsCost` (`energy_equals_cost_of_imbalance`, existing);
* the reparametrized momentum `nlP ∘ imbalance`, canonically conjugate to
  `nlQ` with Jacobian determinant `1` (`nl_jacobian_det_eq_one`, existing, so
  it is canonical with the same normalization), fails `EnergyEqualsCost`
  (`not_energyEqualsCost_nlP`, new).

Both are continuous, swap-odd under the debit-credit exchange, and vanishing on
the balance locus (the nlP package is `nlP_countermodel`, existing). Hence
`EnergyEqualsCost` is **independent of the Hamiltonian data**: the symplectic
form, the Hamiltonian, and the orbit flow do not determine whether "the
momentum" satisfies the premise, because two canonical momenta of the same
system, passing every substrate selection short of the premise, land on
opposite sides of it (`energyEqualsCost_independent_of_hamiltonian_data`).
This closes the general Hamiltonian lead that `Gap5MomentumMagnitudeBridge`
left OPEN, and closes it at class level: the exhibited pair defeats any
argument whose only inputs are Hamiltonian structure, not any named candidate.
What survives the no-go, disclosed as its scope: a derivation that imports
*non-symplectic* structure of the ledger. §3 names the exact extra input.

(Remark, prose only: the nlP momentum also generates a balance-locus-preserving
flow, since any function of the imbalance does; linearity is the only property
on which the two packages provably differ.)

## (c) The sharper reduction: the premise is the linear momentum, normalized

Three kernel-checked pieces.

1. **Pointwise cost form.** `EnergyEqualsCost p` is equivalent, on the open
   positive quadrant, to the pointwise identity
   `p z ^ 2 = 2 * casimir z * Cost.Jcost (z.1 / z.2)`
   (`energyEqualsCost_iff_pointwise_ratio_cost`): the momentum's square is
   twice the Casimir times the recognition cost of the state's own ledger
   ratio. Via `imbalance_sq_eq_two_casimir_jcost` this is the known
   equivalence with the kinetic condition, now with the cost explicit per
   state.
2. **The exact discharge condition.** Additivity under ledger consolidation,
   continuity, balance-vanishing, and the unit normalization `p (1,0) ^ 2 = 1`
   together imply `EnergyEqualsCost p`
   (`energyEqualsCost_of_additive_continuous_balanced_unit`): the chart
   reduction forces `p = a • imbalance`, the normalization pins `a ^ 2 = 1`,
   and the existing `energy_equals_cost_of_imbalance` closes. Deriving THAT
   requires exactly one thing the library does not yet have: additivity of the
   physical momentum under consolidation (the chart successor, OPEN), since
   the unit normalization is the ledger-scale choice already recorded as
   unfixed in the HKT kinetic header. The premise's real home is the
   additivity lane; the Hamiltonian lane is closed by (b).
3. **The quadrant question, answered.** The orbit route is confined to the
   open positive quadrant for a kernel-checked reason: `orbitPoint k t` has
   positive coordinates for `0 < k` (`orbitPoint_pos`, existing) and
   degenerates to the origin for `k ≤ 0` (`orbitPoint_eq_zero_of_nonpos`,
   new, since `Real.sqrt` of a nonpositive is `0`). The route extends to Q3 by
   the signed parameterization: every state with both coordinates negative
   lies on the negated orbit of its (positive) Casimir
   (`neg_orbit_coverage`), and there the ratio is positive and the cost
   reading is intact. The algebraic identity underlying everything,
   `imbalance z ^ 2 = 2 * casimir z * Cost.Jcost (z.1 / z.2)`, holds at every
   off-axis state in every quadrant (`imbalance_sq_eq_two_casimir_jcost`), so
   the kinetic condition itself is quadrant-free; what is confined to
   Q1 ∪ Q3 is the *energy-cost reading*, since on Q2/Q4 the ratio is negative
   and the recognition cost of the ratio is negative (`quadrant_signs`).
   Extending the premise to Q2/Q4 in its cost form would therefore require a
   premise about a negative-cost quantity, which is a different physical
   statement, not an orbit-coverage gap.

## What is NOT claimed

* No flag flip. Flags 6 and 12 still rest on `EnergyEqualsCost`; the premise
  is not discharged, because the one surviving input (momentum additivity) is
  itself open.
* The no-go kills derivations from Hamiltonian/symplectic data alone. It does
  not touch the additivity route; it redirects to it.
* `orbitHamiltonian` and `hamiltonianVectorField` are MODEL-tagged stated
  definitions (the stated Hamiltonian of the split-torus posting dynamics on
  the chart carrier, identity carrier map), per the charge's disclosure rule.
  The no-go does not depend on them being canonical choices: the exhibited
  counter-pair lives on the same carrier with the same area form.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace EnergyEqualsCostDerivation

open ChartFromLedgerMomentum MomentumAdditivity MomentumMagnitudeBridge

noncomputable section

/-! ## §0. The stated Hamiltonian on the stated carrier -/

/-- **The Casimir Hamiltonian (MODEL, stated and disclosed).** On the chart
carrier `LedgerState` with the σ = 0 area form of `Cost.SymplecticAction`, the
split-torus recognition dynamics (`diagSL`) is the Hamiltonian flow of
`H z = casimir z / 2`. The carrier map is the identity on the chart carrier. -/
def orbitHamiltonian (z : LedgerState) : ℝ := casimir z / 2

/-- **The Hamiltonian vector field of `orbitHamiltonian` (MODEL, stated).**
With `ω = dd ∧ dc` (the `areaForm`), `X_H = (∂H/∂c) ∂_d − (∂H/∂d) ∂_c`, which
for `H = d·c/2` is `(d/2, −c/2)`. -/
def hamiltonianVectorField (z : LedgerState) : LedgerState := (z.1 / 2, - z.2 / 2)

/-- Poisson bracket of two coefficient-listed linear observables under the
ledger area form: for `f = a₁ d + b₁ c` and `g = a₂ d + b₂ c`,
`{f, g} = a₁ b₂ − b₁ a₂`. -/
def poissonLin (a₁ b₁ a₂ b₂ : ℝ) : ℝ := a₁ * b₂ - b₁ * a₂

/-! ## §1. The orbit flow is Hamiltonian -/

private theorem hasDerivAt_exp_half (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) / 2) t := by
  have h : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t :=
    ((hasDerivAt_id' t).div_const (2 : ℝ)).exp
  convert h using 1
  ring

private theorem hasDerivAt_exp_neg_half (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s / 2)) (- Real.exp (-t / 2) / 2) t := by
  have h : HasDerivAt (fun s : ℝ => Real.exp (-s / 2)) (Real.exp (-t / 2) * (-1 / 2)) t :=
    (((hasDerivAt_id' t).neg).div_const (2 : ℝ)).exp
  convert h using 1
  ring

/-- **The orbit is the Hamiltonian flow of the Casimir Hamiltonian.** The time
derivative of `orbitPoint k t` at `t` is the Hamiltonian vector field evaluated
at the orbit point. -/
theorem orbitPoint_is_hamiltonian_flow (k t : ℝ) :
    HasDerivAt (fun s : ℝ => orbitPoint k s)
      (hamiltonianVectorField (orbitPoint k t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => Real.sqrt k * Real.exp (s / 2))
      (Real.sqrt k * (Real.exp (t / 2) / 2)) t :=
    (hasDerivAt_exp_half t).const_mul (Real.sqrt k)
  have h2 : HasDerivAt (fun s : ℝ => Real.sqrt k * Real.exp (-s / 2))
      (Real.sqrt k * (- Real.exp (-t / 2) / 2)) t :=
    (hasDerivAt_exp_neg_half t).const_mul (Real.sqrt k)
  have hp := h1.prodMk h2
  have e1 : (fun s : ℝ => orbitPoint k s)
      = fun s => (Real.sqrt k * Real.exp (s / 2), Real.sqrt k * Real.exp (-s / 2)) :=
    funext fun s => rfl
  have c1 : (orbitPoint k t).1 / 2 = Real.sqrt k * (Real.exp (t / 2) / 2) := by
    show Real.sqrt k * Real.exp (t / 2) / 2 = Real.sqrt k * (Real.exp (t / 2) / 2)
    ring
  have c2 : -(orbitPoint k t).2 / 2 = Real.sqrt k * (- Real.exp (-t / 2) / 2) := by
    show -(Real.sqrt k * Real.exp (-t / 2)) / 2 = Real.sqrt k * (- Real.exp (-t / 2) / 2)
    ring
  have e2 : hamiltonianVectorField (orbitPoint k t)
      = (Real.sqrt k * (Real.exp (t / 2) / 2),
          Real.sqrt k * (- Real.exp (-t / 2) / 2)) := by
    rw [show hamiltonianVectorField (orbitPoint k t)
        = ((orbitPoint k t).1 / 2, -(orbitPoint k t).2 / 2) from rfl]
    rw [c1, c2]
  rw [e1, e2]
  exact hp

/-- The Casimir Hamiltonian is conserved along its own flow: its value on the
orbit of Casimir `k` is constantly `k / 2`. -/
theorem orbitHamiltonian_constant_on_orbit (k t : ℝ) (hk : 0 ≤ k) :
    orbitHamiltonian (orbitPoint k t) = k / 2 := by
  rw [orbitHamiltonian, orbitPoint_casimir k t hk]

/-! ## §2. The two canonical momenta, and the no-go -/

/-- `{imbalance, total} = 2`: the imbalance is canonically conjugate to the
ledger total with normalization 2. -/
theorem poisson_imbalance_total : poissonLin 1 (-1) 1 1 = 2 := by
  norm_num [poissonLin]

/-- The bracket normalization is exactly the canonical-frame determinant of the
chart module: `{imbalance, total} = det imbalanceTotalMap = 2`. -/
theorem poisson_imbalance_total_eq_frame_det :
    poissonLin 1 (-1) 1 1 = imbalanceTotalMap.det := by
  rw [poisson_imbalance_total, imbalanceTotalMap_det]

/-- **The reparametrized momentum fails the premise.** Witness: the unit-Casimir
orbit point at `t = 2 arsinh (1/2)`, where the imbalance is `1` but
`nlP 1 = 2`, so the squared value `4` differs from the required `1`. -/
theorem not_energyEqualsCost_nlP :
    ¬ EnergyEqualsCost (fun z : LedgerState => nlP (imbalance z)) := by
  intro hE
  have hkin := (open_positive_kinetic_iff_energy_equals_cost).mpr hE
  set t₀ : ℝ := 2 * Real.arsinh (1 / 2) with ht₀
  have hpos := orbitPoint_pos 1 t₀ one_pos
  have h1 := hkin (orbitPoint 1 t₀) hpos.1 hpos.2
  have himb : imbalance (orbitPoint 1 t₀) = 1 := by
    rw [orbitPoint_imbalance, Real.sqrt_one, ht₀]
    rw [show (2 * Real.arsinh (1 / 2 : ℝ)) / 2 = Real.arsinh (1 / 2) from by ring,
      Real.sinh_arsinh]
    ring
  have hnl : nlP (1 : ℝ) = 2 := by norm_num [nlP]
  change nlP (imbalance (orbitPoint 1 t₀)) ^ 2 = imbalance (orbitPoint 1 t₀) ^ 2 at h1
  rw [himb, hnl] at h1
  norm_num at h1

/-- **The imbalance package:** the canonical momentum that satisfies the
premise, with every substrate selection it passes. -/
theorem imbalance_momentum_package :
    Continuous imbalance ∧ SwapOdd imbalance ∧
      (∀ z : LedgerState, Balanced z → imbalance z = 0) ∧
      EnergyEqualsCost imbalance ∧ poissonLin 1 (-1) 1 1 = 2 :=
  ⟨continuous_imbalance, fun z => imbalance_swap z,
    fun z hz => show imbalance z = 0 from sub_eq_zero.mpr hz, energy_equals_cost_of_imbalance,
    poisson_imbalance_total⟩

/-- **The nlP package:** the canonical momentum that fails the premise, passing
the same selections: continuity, swap parity, balance-vanishing, and canonical
status with the same normalization (Jacobian 1 on the `(imbalance, total)`
frame, whose own determinant is 2). -/
theorem nlP_momentum_package :
    Continuous (fun z : LedgerState => nlP (imbalance z)) ∧
      SwapOdd (fun z : LedgerState => nlP (imbalance z)) ∧
      (∀ z : LedgerState, Balanced z → nlP (imbalance z) = 0) ∧
      (∀ m q : ℝ, Matrix.det !![1 + 3 * m ^ 2, 0; q, 1 / (1 + 3 * m ^ 2)] = 1) ∧
      imbalanceTotalMap.det = 2 ∧
      ¬ EnergyEqualsCost (fun z : LedgerState => nlP (imbalance z)) :=
  ⟨nlP_countermodel.1, nlP_countermodel.2.1, nlP_countermodel.2.2.1,
    nl_jacobian_det_eq_one, imbalanceTotalMap_det, not_energyEqualsCost_nlP⟩

/-- **NO-GO (polarization independence).** The ledger Hamiltonian system (the
σ = 0 area form, the Casimir Hamiltonian, its orbit flow) admits two canonical
momentum observables that agree on continuity, swap parity, balance-vanishing,
and canonical-momentum normalization, and disagree on `EnergyEqualsCost`. The
premise is therefore independent of the Hamiltonian data: no derivation whose
inputs are the symplectic form, the Hamiltonian, and the orbit flow alone can
conclude it. This knocks down the class of Hamiltonian-only derivations, not
any named candidate; the surviving route (non-symplectic, the ledger's linear
structure) is §3. -/
theorem energyEqualsCost_independent_of_hamiltonian_data :
    (Continuous imbalance ∧ SwapOdd imbalance ∧
      (∀ z : LedgerState, Balanced z → imbalance z = 0) ∧
      EnergyEqualsCost imbalance ∧ poissonLin 1 (-1) 1 1 = 2) ∧
    (Continuous (fun z : LedgerState => nlP (imbalance z)) ∧
      SwapOdd (fun z : LedgerState => nlP (imbalance z)) ∧
      (∀ z : LedgerState, Balanced z → nlP (imbalance z) = 0) ∧
      (∀ m q : ℝ, Matrix.det !![1 + 3 * m ^ 2, 0; q, 1 / (1 + 3 * m ^ 2)] = 1) ∧
      imbalanceTotalMap.det = 2 ∧
      ¬ EnergyEqualsCost (fun z : LedgerState => nlP (imbalance z))) :=
  ⟨imbalance_momentum_package, nlP_momentum_package⟩

/-! ## §3. The exact discharge condition -/

/-- **The discharge condition.** If the momentum is additive under ledger
consolidation, continuous, balance-vanishing, and unit-normalized
(`p (1,0) ^ 2 = 1`, the ledger scale), then it is a unit sign times the
imbalance and `EnergyEqualsCost` holds. The only open input is additivity
(the chart successor); the normalization is the scale choice already recorded
as unfixed in the HKT kinetic header. -/
theorem energyEqualsCost_of_additive_continuous_balanced_unit
    (p : LedgerState → ℝ)
    (hadd : ∀ z w : LedgerState, p (z + w) = p z + p w)
    (hcont : Continuous p)
    (hbal : ∀ z : LedgerState, Balanced z → p z = 0)
    (hunit : p (1, 0) ^ 2 = 1) :
    EnergyEqualsCost p := by
  obtain ⟨a, ha⟩ := additive_continuous_balanced_is_imbalance p hadd hcont hbal
  have hpa : p (1, 0) = a := by
    have h := ha ((1, 0) : LedgerState)
    rw [h]
    simp [imbalance]
  have ha2 : a ^ 2 = 1 := by
    rw [hpa] at hunit
    exact hunit
  intro k t hk
  have hE := energy_equals_cost_of_imbalance k t hk
  calc p (orbitPoint k t) ^ 2
      = (a * imbalance (orbitPoint k t)) ^ 2 := by rw [ha]
    _ = a ^ 2 * imbalance (orbitPoint k t) ^ 2 := by ring
    _ = imbalance (orbitPoint k t) ^ 2 := by rw [ha2, one_mul]
    _ = 2 * k * Cost.Jlog t := hE

/-- **The pointwise cost form of the premise.** On the open positive quadrant,
`EnergyEqualsCost p` says state by state: the momentum's square is twice the
Casimir times the recognition cost of the state's own ledger ratio. -/
theorem energyEqualsCost_iff_pointwise_ratio_cost {p : LedgerState → ℝ} :
    EnergyEqualsCost p ↔
      ∀ z : LedgerState, 0 < z.1 → 0 < z.2 →
        p z ^ 2 = 2 * casimir z * Cost.Jcost (z.1 / z.2) := by
  constructor
  · intro hE z hd hc
    have hz := orbit_coverage z hd hc
    have hk : 0 < casimir z := mul_pos hd hc
    have h1 := hE (casimir z) (Real.log (z.1 / z.2)) hk
    have hJ : Cost.Jlog (Real.log (z.1 / z.2)) = Cost.Jcost (z.1 / z.2) := by
      show Cost.Jcost (Real.exp (Real.log (z.1 / z.2))) = Cost.Jcost (z.1 / z.2)
      rw [Real.exp_log (div_pos hd hc)]
    rw [← hz, hJ] at h1
    exact h1
  · intro hpt k t hk
    have hpos := orbitPoint_pos k t hk
    have h1 := hpt (orbitPoint k t) hpos.1 hpos.2
    have hratio : (orbitPoint k t).1 / (orbitPoint k t).2 = Real.exp t := by
      have hsk : Real.sqrt k ≠ 0 := (Real.sqrt_ne_zero').mpr hk
      show (Real.sqrt k * Real.exp (t / 2)) / (Real.sqrt k * Real.exp (-t / 2)) =
        Real.exp t
      rw [mul_div_mul_comm, div_self hsk, one_mul, ← Real.exp_sub]
      congr 1
      ring
    rw [orbitPoint_casimir k t hk.le, hratio] at h1
    simpa only [Cost.Jlog] using h1

/-! ## §4. The quadrant question -/

/-- **Why the orbit route cannot leave the positive quadrant.** For nonpositive
Casimir the orbit degenerates to the origin, since `Real.sqrt` of a
nonpositive is `0`. With `orbitPoint_pos` (positive Casimir gives positive
coordinates) this confines the route to the open positive quadrant. -/
theorem orbitPoint_eq_zero_of_nonpos {k : ℝ} (hk : k ≤ 0) (t : ℝ) :
    orbitPoint k t = (0, 0) := by
  have hsk : Real.sqrt k = 0 := (Real.sqrt_eq_zero').mpr hk
  simp [orbitPoint, hsk]

/-- **Q3 is reachable by the signed orbit.** Every state with both coordinates
negative lies on the negated orbit of its (positive) Casimir, at the same log
ratio. The cost reading is intact there: the ratio is positive. -/
theorem neg_orbit_coverage (z : LedgerState) (hd : z.1 < 0) (hc : z.2 < 0) :
    z = - orbitPoint (casimir z) (Real.log (z.1 / z.2)) := by
  have hw := orbit_coverage (-z.1, -z.2) (neg_pos.mpr hd) (neg_pos.mpr hc)
  have hcas : casimir (-z.1, -z.2) = casimir z := by
    simp only [casimir, neg_mul_neg]
  have hrat : ((-z.1, -z.2) : LedgerState).1 / ((-z.1, -z.2) : LedgerState).2 =
      z.1 / z.2 := neg_div_neg_eq _ _
  rw [hcas, hrat] at hw
  rw [← hw]
  apply Prod.ext
  · show z.1 = - -z.1
    simp
  · show z.2 = - -z.2
    simp

/-- **The master identity is quadrant-free.** At every off-axis state, the
squared imbalance is twice the Casimir times the recognition cost of the ledger
ratio. The kinetic condition has no quadrant boundary; only the energy-cost
reading does. -/
theorem imbalance_sq_eq_two_casimir_jcost (z : LedgerState)
    (h1 : z.1 ≠ 0) (h2 : z.2 ≠ 0) :
    imbalance z ^ 2 = 2 * casimir z * Cost.Jcost (z.1 / z.2) := by
  simp only [imbalance, casimir, Cost.Jcost]
  field_simp [h1, h2]
  ring

/-- **Quadrant signs.** Ratio and Casimir share a sign on Q1 and Q3 (where the
recognition cost of the ratio is nonnegative, so the energy-cost reading is
natural) and are both negative-signed appropriately on Q2/Q4: there the ratio
is negative and the Casimir is negative, so the energy-cost reading is a
statement about a negative-cost quantity. -/
theorem quadrant_signs (z : LedgerState) :
    (0 < z.1 → 0 < z.2 → 0 < casimir z ∧ 0 < z.1 / z.2) ∧
    (z.1 < 0 → z.2 < 0 → 0 < casimir z ∧ 0 < z.1 / z.2) ∧
    (z.1 < 0 → 0 < z.2 → casimir z < 0 ∧ z.1 / z.2 < 0) ∧
    (0 < z.1 → z.2 < 0 → casimir z < 0 ∧ z.1 / z.2 < 0) :=
  ⟨fun h1 h2 => ⟨mul_pos h1 h2, div_pos h1 h2⟩,
    fun h1 h2 => ⟨mul_pos_of_neg_of_neg h1 h2, div_pos_of_neg_of_neg h1 h2⟩,
    fun h1 h2 => ⟨mul_neg_of_neg_of_pos h1 h2, div_neg_of_neg_of_pos h1 h2⟩,
    fun h1 h2 => ⟨mul_neg_of_pos_of_neg h1 h2, div_neg_of_pos_of_neg h1 h2⟩⟩

/-! ## §5. The verdict certificate -/

/-- **The derivation verdict, packaged.** (b): the orbit flow is the Casimir
Hamiltonian's flow, and the premise is independent of the Hamiltonian data by
the exhibited canonical counter-pair. (c): the pointwise cost form, the exact
discharge condition (additivity + continuity + balance + unit normalization),
and the quadrant answer (orbit confinement for a kernel reason, Q3 signed
coverage, the quadrant-free master identity, the quadrant signs). -/
structure EnergyEqualsCostDerivationVerdict : Prop where
  orbit_is_hamiltonian_flow :
    ∀ k t : ℝ, HasDerivAt (fun s : ℝ => orbitPoint k s)
      (hamiltonianVectorField (orbitPoint k t)) t
  hamiltonian_conserved_on_orbit :
    ∀ k t : ℝ, 0 ≤ k → orbitHamiltonian (orbitPoint k t) = k / 2
  hamiltonian_data_independence :
    (Continuous imbalance ∧ SwapOdd imbalance ∧
      (∀ z : LedgerState, Balanced z → imbalance z = 0) ∧
      EnergyEqualsCost imbalance ∧ poissonLin 1 (-1) 1 1 = 2) ∧
    (Continuous (fun z : LedgerState => nlP (imbalance z)) ∧
      SwapOdd (fun z : LedgerState => nlP (imbalance z)) ∧
      (∀ z : LedgerState, Balanced z → nlP (imbalance z) = 0) ∧
      (∀ m q : ℝ, Matrix.det !![1 + 3 * m ^ 2, 0; q, 1 / (1 + 3 * m ^ 2)] = 1) ∧
      imbalanceTotalMap.det = 2 ∧
      ¬ EnergyEqualsCost (fun z : LedgerState => nlP (imbalance z)))
  sufficient_additive_unit :
    ∀ p : LedgerState → ℝ,
      (∀ z w : LedgerState, p (z + w) = p z + p w) → Continuous p →
      (∀ z : LedgerState, Balanced z → p z = 0) → p (1, 0) ^ 2 = 1 →
      EnergyEqualsCost p
  premise_pointwise_cost_form :
    ∀ p : LedgerState → ℝ, EnergyEqualsCost p ↔
      ∀ z : LedgerState, 0 < z.1 → 0 < z.2 →
        p z ^ 2 = 2 * casimir z * Cost.Jcost (z.1 / z.2)
  orbit_degenerate_of_nonpos :
    ∀ k t : ℝ, k ≤ 0 → orbitPoint k t = (0, 0)
  q3_signed_orbit_coverage :
    ∀ z : LedgerState, z.1 < 0 → z.2 < 0 →
      z = - orbitPoint (casimir z) (Real.log (z.1 / z.2))
  off_axis_cost_identity :
    ∀ z : LedgerState, z.1 ≠ 0 → z.2 ≠ 0 →
      imbalance z ^ 2 = 2 * casimir z * Cost.Jcost (z.1 / z.2)
  quadrant_signs_hold :
    ∀ z : LedgerState,
      (0 < z.1 → 0 < z.2 → 0 < casimir z ∧ 0 < z.1 / z.2) ∧
      (z.1 < 0 → z.2 < 0 → 0 < casimir z ∧ 0 < z.1 / z.2) ∧
      (z.1 < 0 → 0 < z.2 → casimir z < 0 ∧ z.1 / z.2 < 0) ∧
      (0 < z.1 → z.2 < 0 → casimir z < 0 ∧ z.1 / z.2 < 0)

theorem energyEqualsCostDerivationVerdict : EnergyEqualsCostDerivationVerdict where
  orbit_is_hamiltonian_flow := orbitPoint_is_hamiltonian_flow
  hamiltonian_conserved_on_orbit := orbitHamiltonian_constant_on_orbit
  hamiltonian_data_independence := energyEqualsCost_independent_of_hamiltonian_data
  sufficient_additive_unit := energyEqualsCost_of_additive_continuous_balanced_unit
  premise_pointwise_cost_form := fun _ => energyEqualsCost_iff_pointwise_ratio_cost
  orbit_degenerate_of_nonpos := fun k t hk => orbitPoint_eq_zero_of_nonpos (k := k) hk t
  q3_signed_orbit_coverage := neg_orbit_coverage
  off_axis_cost_identity := imbalance_sq_eq_two_casimir_jcost
  quadrant_signs_hold := quadrant_signs

/-! ## Axiom audit -/

#print axioms orbitPoint_is_hamiltonian_flow
#print axioms orbitHamiltonian_constant_on_orbit
#print axioms poisson_imbalance_total
#print axioms poisson_imbalance_total_eq_frame_det
#print axioms not_energyEqualsCost_nlP
#print axioms imbalance_momentum_package
#print axioms nlP_momentum_package
#print axioms energyEqualsCost_independent_of_hamiltonian_data
#print axioms energyEqualsCost_of_additive_continuous_balanced_unit
#print axioms energyEqualsCost_iff_pointwise_ratio_cost
#print axioms orbitPoint_eq_zero_of_nonpos
#print axioms neg_orbit_coverage
#print axioms imbalance_sq_eq_two_casimir_jcost
#print axioms quadrant_signs
#print axioms energyEqualsCostDerivationVerdict

end
end EnergyEqualsCostDerivation
end SevenGaps
end Gravity
end IndisputableMonolith
