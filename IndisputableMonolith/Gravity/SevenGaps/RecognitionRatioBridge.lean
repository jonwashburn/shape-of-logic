import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Gravity.RecognitionLedger
import IndisputableMonolith.Gravity.SevenGaps.LedgerBridgeNoGo
import IndisputableMonolith.Gravity.SevenGaps.LedgerEnergyBridge

/-!
# Seven Gaps, Phase 0a: the recognition-ratio bridge (the paper's odd form)

## Status: the structure `RecognitionRatioBridge` is MODEL tier (an explicit
admissibility HYPOTHESIS, the paper's Def 6.2 clause, not yet derived); the
named theorems below are THEOREM tier (0 sorry, 0 admit, 0 new axiom;
`decide` is used only for `Fin 2` literal disequalities; no `native_decide`).
The status record at the end is documentation, not mathematics.

`SevenGaps.LedgerBridgeNoGo` refuted the OLD bridge form
(`LedgerToHingeBridge.bridge_assumed`: ledger deficit = signed geometric
hinge deficit): ledger deficits are nonnegative
(`bridge_forces_nonneg_geometricDeficit`, the sign no-go) and J-ratio
deficits are EVEN in the deformation parameter
(`ledger_family_deficit_even_of_ratio_parity` and its corollaries), while
the signed Regge deficit response is odd.

The physics paper does NOT assert that refuted form. Its substrate-to-
geometry bridge is the ODD relation on a positive comparison ratio x_sigma
at each hinge sigma:

  log x_sigma = kappa_sigma * delta_sigma + remainder,
  |remainder| <= remBound * meshScale ^ 3,

an admissibility clause on log x, not an equality of nonnegative deficits.
This module encodes that relation (`RecognitionRatioBridge`) and reconciles
it with the no-gos by KERNEL-CHECKED statements, not prose:

* `ratioBridge_admits_negative_deficit`: for EVERY d there is an exact
  (remBound = 0), unit-coupled (kappa = 1) bridge on two hinges with
  geometric deficits d and -d. No free field absorbs the content: exactness
  and unit coupling are exported in the statement.
* `ratioBridgeLedger` and `ratioBridge_separates_deficit_observables`: every
  bridge induces a genuine `RecognitionLedger` (cost = J-cost of the ratio
  quotient, realized through the proved `coboundaryStrainLedger`), and on
  the witness family the induced LEDGER deficit is nonnegative
  (`RecognitionLedger.deficit_nonneg`, the engine of the sign no-go) and
  even under d -> -d (via `ledger_family_deficit_even_of_ratio_parity`),
  WHILE the GEOMETRIC deficit stays signed. The no-gos constrain the ledger
  deficit; the odd bridge keeps the signed information in log x: two
  different observables, no contradiction.
* `jcost_of_ratioBridge_cosh`, `jcost_of_ratioBridge_even_in_deficit`:
  J(x) = cosh(log x) - 1, so the J-cost sees only the even part of the
  relation and is invariant under a deficit sign flip.
* `ratioBridge_jcost_quadratic` (exact) and
  `ratioBridge_jcost_quadratic_inexact` (any remBound): the J-cost of the
  ratio matches (kappa * delta)^2 / 2 up to the quartic term, plus, in the
  inexact case, an explicit perturbation term in remBound * meshScale ^ 3.
  Both use the same numeric lemma `Jcost_exp_sub_half_sq_abs_le` (and the
  cosh bounds) proved in `LedgerEnergyBridge`.

OPEN (wave 1b): deriving the ratio relation from stationarity of the ledger
action, rather than positing it as an admissibility hypothesis. OPEN
(lane 2): the h -> 0 asymptotic family; this module records the remainder
clause at one fixed mesh only.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps

/-! ## §1. The recognition-ratio bridge structure (MODEL tier) -/

/-- **MODEL (explicit hypothesis, the paper's Def 6.2 recognition-ratio
admissibility clause; NOT yet derived, derivation target is wave 1b).**

A recognition-ratio bridge on a hinge type `H` assigns to each hinge
`sigma` a positive comparison ratio `xRatio sigma`, a coupling
`kappa sigma`, and a SIGNED geometric deficit `geometricDeficit sigma`,
together with a mesh scale `meshScale` and a remainder constant `remBound`,
subject to the odd admissibility relation

  |log (xRatio sigma) - kappa sigma * geometricDeficit sigma|
    <= remBound * meshScale ^ 3.

Scope note: this records the paper's remainder clause AT A FIXED MESH; the
h -> 0 asymptotic family behind the O(h^3) notation is not yet formalized
(open, lane 2). Contrast with the REFUTED
`LedgerToHingeBridge.bridge_assumed` (ledger deficit = geometric deficit):
here the relation is carried by log x, which can take either sign, and the
reconciliation with the sign and parity no-gos is proved below
(`ratioBridge_admits_negative_deficit`,
`ratioBridge_separates_deficit_observables`). -/
structure RecognitionRatioBridge (H : Type*) where
  /-- The positive comparison ratio x_sigma at each hinge. -/
  xRatio : H → ℝ
  /-- Positivity of the comparison ratio. -/
  xRatio_pos : ∀ σ, 0 < xRatio σ
  /-- The hinge coupling kappa_sigma. -/
  kappa : H → ℝ
  /-- The SIGNED geometric deficit delta_sigma at each hinge. -/
  geometricDeficit : H → ℝ
  /-- The mesh scale h. -/
  meshScale : ℝ
  /-- The mesh scale is positive. -/
  meshScale_pos : 0 < meshScale
  /-- The remainder constant of the cubic-mesh clause. -/
  remBound : ℝ
  /-- The remainder constant is nonnegative. -/
  remBound_nonneg : 0 ≤ remBound
  /-- The odd admissibility relation: log x_sigma matches
  kappa_sigma * delta_sigma up to the cubic mesh remainder. -/
  ratio_relation : ∀ σ,
    |Real.log (xRatio σ) - kappa σ * geometricDeficit σ|
      ≤ remBound * meshScale ^ 3

/-! ## §2. Exactness specializations (THEOREM tier, one-step)

These are one-step specializations of `ratio_relation` at remBound = 0,
recorded once so later proofs can cite them; they carry no independent
content. -/

/-- **THEOREM (one-step specialization).** For an exact bridge (remainder
constant 0) the relation is an equality: log (xRatio sigma) = kappa sigma *
geometricDeficit sigma. -/
theorem log_xRatio_eq_of_exact {H : Type*}
    (B : RecognitionRatioBridge H) (hB : B.remBound = 0) (σ : H) :
    Real.log (B.xRatio σ) = B.kappa σ * B.geometricDeficit σ := by
  have h := B.ratio_relation σ
  rw [hB, zero_mul] at h
  have habs : |Real.log (B.xRatio σ) - B.kappa σ * B.geometricDeficit σ|
      = 0 :=
    le_antisymm h (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

/-- **THEOREM (one-step specialization).** For an exact bridge the
comparison ratio is the exponential of the linear deficit response. -/
theorem xRatio_eq_exp_of_exact {H : Type*}
    (B : RecognitionRatioBridge H) (hB : B.remBound = 0) (σ : H) :
    B.xRatio σ = Real.exp (B.kappa σ * B.geometricDeficit σ) := by
  rw [← log_xRatio_eq_of_exact B hB σ, Real.exp_log (B.xRatio_pos σ)]

/-! ## §3. Escape from the sign no-go: the strong witness (THEOREM tier)

`bridge_forces_nonneg_geometricDeficit` (in `LedgerBridgeNoGo`) shows the
OLD form forces every reached geometric deficit to be nonnegative. The odd
form does not, and the witness exports its full strength: exact relation,
unit coupling, prescribed signed deficits. -/

/-- The explicit two-hinge witness: deficits d at hinge 0 and -d at hinge 1,
kappa = 1, xRatio sigma = exp(deficit sigma), mesh scale 1, remainder 0.
The ratio relation holds exactly. -/
noncomputable def twoHingeWitnessBridge (d : ℝ) :
    RecognitionRatioBridge (Fin 2) where
  xRatio := fun σ => Real.exp (if σ = 0 then d else -d)
  xRatio_pos := fun _ => Real.exp_pos _
  kappa := fun _ => 1
  geometricDeficit := fun σ => if σ = 0 then d else -d
  meshScale := 1
  meshScale_pos := one_pos
  remBound := 0
  remBound_nonneg := le_refl 0
  ratio_relation := by
    intro σ
    simp only [Real.log_exp, one_mul, sub_self, abs_zero, zero_mul, le_refl]

/-- **THEOREM.** Evaluation of the witness deficits: d at hinge 0 and -d at
hinge 1. (Uses `decide` only for the `Fin 2` literal disequality 1 ≠ 0.) -/
theorem twoHingeWitnessBridge_deficit (d : ℝ) :
    (twoHingeWitnessBridge d).geometricDeficit 0 = d ∧
      (twoHingeWitnessBridge d).geometricDeficit 1 = -d := by
  constructor
  · show (if (0 : Fin 2) = 0 then d else -d) = d
    rw [if_pos rfl]
  · show (if (1 : Fin 2) = 0 then d else -d) = -d
    have h10 : ¬((1 : Fin 2) = 0) := by decide
    rw [if_neg h10]

/-- **THEOREM (escape from the sign no-go, strong universal form).** For
EVERY d there is an EXACT (remBound = 0), UNIT-COUPLED (kappa = 1)
recognition-ratio bridge on two hinges whose geometric deficit takes the
prescribed values d at hinge 0 and -d at hinge 1. For d > 0 the deficit at
hinge 1 is strictly negative, which
`bridge_forces_nonneg_geometricDeficit` proves impossible for the old
deficit-equality form: the odd log-ratio form escapes the sign obstruction
with no free field absorbing the content. -/
theorem ratioBridge_admits_negative_deficit (d : ℝ) :
    ∃ B : RecognitionRatioBridge (Fin 2),
      B.remBound = 0 ∧ (∀ σ, B.kappa σ = 1) ∧
      B.geometricDeficit 0 = d ∧ B.geometricDeficit 1 = -d :=
  ⟨twoHingeWitnessBridge d, rfl, fun _ => rfl,
    (twoHingeWitnessBridge_deficit d).1, (twoHingeWitnessBridge_deficit d).2⟩

/-! ## §4. The induced recognition ledger and the reconciliation theorem

Engagement with the no-go on its own ground: every bridge induces a genuine
`RecognitionLedger`, and the no-go's constraints (nonnegative, parity-even
deficit) hold for THAT object while the bridge's geometric deficit stays
signed. -/

/-- The recognition ledger induced by a recognition-ratio bridge: the cost
of the pair (sigma, tau) is the J-cost of the comparison-ratio quotient
xRatio sigma / xRatio tau. Realized as `coboundaryStrainLedger` with cell
potential log (xRatio sigma), so symmetry, diagonal zero, nonnegativity,
and RCL subadditivity are all inherited from the proved construction in
`LedgerEnergyBridge`. -/
noncomputable def ratioBridgeLedger {H : Type*} [Fintype H] [DecidableEq H]
    (B : RecognitionRatioBridge H) :
    RecognitionLedger.RecognitionLedger H :=
  coboundaryStrainLedger (fun σ => Real.log (B.xRatio σ))

/-- **THEOREM.** The induced ledger cost is the J-cost of the ratio
quotient: cost sigma tau = J(xRatio sigma / xRatio tau). -/
theorem ratioBridgeLedger_cost {H : Type*} [Fintype H] [DecidableEq H]
    (B : RecognitionRatioBridge H) (σ τ : H) :
    (ratioBridgeLedger B).cost σ τ
      = Cost.Jcost (B.xRatio σ / B.xRatio τ) := by
  show Cost.Jcost
      (Real.exp (Real.log (B.xRatio σ) - Real.log (B.xRatio τ))) = _
  rw [Real.exp_sub, Real.exp_log (B.xRatio_pos σ),
    Real.exp_log (B.xRatio_pos τ)]

/-- **THEOREM.** Ratio parity of the witness family: flipping the sign of d
inverts every comparison ratio. -/
theorem twoHingeWitnessBridge_xRatio_neg (d : ℝ) (σ : Fin 2) :
    (twoHingeWitnessBridge (-d)).xRatio σ
      = ((twoHingeWitnessBridge d).xRatio σ)⁻¹ := by
  show Real.exp (if σ = 0 then -d else -(-d))
      = (Real.exp (if σ = 0 then d else -d))⁻¹
  rw [← Real.exp_neg]
  congr 1
  by_cases h : σ = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- **THEOREM.** The ledger deficit induced by the witness family is EVEN
under d -> -d, by direct application of the no-go's own family theorem
`ledger_family_deficit_even_of_ratio_parity` (with ratios r d sigma tau =
xRatio sigma / xRatio tau, parity-covariant by
`twoHingeWitnessBridge_xRatio_neg`). -/
theorem twoHingeWitness_ledger_deficit_even (d : ℝ) (σ : Fin 2) :
    RecognitionLedger.deficit
        (ratioBridgeLedger (twoHingeWitnessBridge (-d))) σ
      = RecognitionLedger.deficit
        (ratioBridgeLedger (twoHingeWitnessBridge d)) σ := by
  exact ledger_family_deficit_even_of_ratio_parity
    (fun ε => ratioBridgeLedger (twoHingeWitnessBridge ε))
    (fun ε i j =>
      (twoHingeWitnessBridge ε).xRatio i / (twoHingeWitnessBridge ε).xRatio j)
    (fun ε i j => div_pos ((twoHingeWitnessBridge ε).xRatio_pos i)
      ((twoHingeWitnessBridge ε).xRatio_pos j))
    (fun ε i j => ratioBridgeLedger_cost (twoHingeWitnessBridge ε) i j)
    (fun ε i j => by
      show (twoHingeWitnessBridge (-ε)).xRatio i
            / (twoHingeWitnessBridge (-ε)).xRatio j
          = ((twoHingeWitnessBridge ε).xRatio i
            / (twoHingeWitnessBridge ε).xRatio j)⁻¹
      rw [twoHingeWitnessBridge_xRatio_neg ε i,
        twoHingeWitnessBridge_xRatio_neg ε j, inv_div_inv, inv_div])
    d σ

/-- **THEOREM (deficit-observable separation: the reconciliation).** For
every d > 0 the exact, unit-coupled two-hinge witness simultaneously has:

* a SIGNED geometric deficit (value d at hinge 0, strictly negative value
  -d at hinge 1), which the sign no-go forbids for the LEDGER deficit; and
* an induced genuine `RecognitionLedger` whose deficit is NONNEGATIVE at
  every cell (`RecognitionLedger.deficit_nonneg`, the engine behind
  `bridge_forces_nonneg_geometricDeficit`) and EVEN under the sign flip
  d -> -d (`ledger_family_deficit_even_of_ratio_parity`, via
  `twoHingeWitness_ledger_deficit_even`).

The no-gos constrain the ledger deficit; the paper's odd bridge stores the
signed information in log x, hence in the geometric deficit. The two
observables are separated by this witness, so the no-gos and the paper's
bridge are jointly consistent. -/
theorem ratioBridge_separates_deficit_observables (d : ℝ) (hd : 0 < d) :
    (twoHingeWitnessBridge d).remBound = 0 ∧
    (∀ σ, (twoHingeWitnessBridge d).kappa σ = 1) ∧
    (twoHingeWitnessBridge d).geometricDeficit 0 = d ∧
    (twoHingeWitnessBridge d).geometricDeficit 1 < 0 ∧
    (∀ σ, 0 ≤ RecognitionLedger.deficit
        (ratioBridgeLedger (twoHingeWitnessBridge d)) σ) ∧
    (∀ σ, RecognitionLedger.deficit
          (ratioBridgeLedger (twoHingeWitnessBridge (-d))) σ
        = RecognitionLedger.deficit
          (ratioBridgeLedger (twoHingeWitnessBridge d)) σ) := by
  refine ⟨rfl, fun _ => rfl, (twoHingeWitnessBridge_deficit d).1, ?_,
    fun σ => RecognitionLedger.deficit_nonneg _ σ,
    fun σ => twoHingeWitness_ledger_deficit_even d σ⟩
  rw [(twoHingeWitnessBridge_deficit d).2]
  linarith

/-! ## §5. Parity of the J-cost (THEOREM tier)

The ledger cost of the comparison ratio sees only the EVEN part of the
relation: J(x) = cosh(log x) - 1. The signed information lives in log x. -/

/-- **THEOREM.** For any bridge and hinge, the J-cost of the comparison
ratio is cosh of its logarithm minus one. Since cosh is even, the ledger
cost is blind to the sign of log x_sigma. -/
theorem jcost_of_ratioBridge_cosh {H : Type*}
    (B : RecognitionRatioBridge H) (σ : H) :
    Cost.Jcost (B.xRatio σ)
      = Real.cosh (Real.log (B.xRatio σ)) - 1 := by
  conv_lhs => rw [← Real.exp_log (B.xRatio_pos σ)]
  exact Cost.Jcost_exp_cosh _

/-- **THEOREM.** For an exact bridge the J-cost of the comparison ratio is
cosh(kappa sigma * delta sigma) - 1, an EVEN function of the deficit. -/
theorem jcost_of_exact_ratioBridge {H : Type*}
    (B : RecognitionRatioBridge H) (hB : B.remBound = 0) (σ : H) :
    Cost.Jcost (B.xRatio σ)
      = Real.cosh (B.kappa σ * B.geometricDeficit σ) - 1 := by
  rw [jcost_of_ratioBridge_cosh B σ, log_xRatio_eq_of_exact B hB σ]

/-- **THEOREM (J-cost parity).** For two exact bridges whose deficits at a
hinge differ by a sign flip while the couplings agree, the J-costs of the
comparison ratios are EQUAL: the per-hinge ledger cost is parity-blind,
exactly as the parity no-gos require, while the signed deficit information
survives in log x_sigma. -/
theorem jcost_of_ratioBridge_even_in_deficit {H : Type*}
    (B₁ B₂ : RecognitionRatioBridge H)
    (h₁ : B₁.remBound = 0) (h₂ : B₂.remBound = 0) (σ : H)
    (hκ : B₂.kappa σ = B₁.kappa σ)
    (hδ : B₂.geometricDeficit σ = - B₁.geometricDeficit σ) :
    Cost.Jcost (B₂.xRatio σ) = Cost.Jcost (B₁.xRatio σ) := by
  rw [jcost_of_exact_ratioBridge B₁ h₁ σ, jcost_of_exact_ratioBridge B₂ h₂ σ,
    hκ, hδ, mul_neg, Real.cosh_neg]

/-! ## §6. Quadratic expansion: exact and inexact (THEOREM tier)

Both statements use the numeric expansion lemmas of `LedgerEnergyBridge`
(`Jcost_exp_sub_half_sq_abs_le`, `cosh_sub_one_le_half_sq_mul_cosh`,
`abs_sinh_le_abs_mul_cosh`, `cosh_one_lt_two`). The inexact form is the one
that actually consumes the remainder clause of the structure. -/

/-- **THEOREM (exact quadratic expansion).** For an exact bridge with small
response |kappa sigma * delta sigma| <= 1:

  |J(x_sigma) - (kappa sigma * delta sigma)^2 / 2|
    <= (kappa sigma * delta sigma)^4 / 2.

Same numeric lemma `Jcost_exp_sub_half_sq_abs_le` as the quadratic-energy
matching of `LedgerEnergyBridge`. -/
theorem ratioBridge_jcost_quadratic {H : Type*}
    (B : RecognitionRatioBridge H) (hB : B.remBound = 0) (σ : H)
    (hsmall : |B.kappa σ * B.geometricDeficit σ| ≤ 1) :
    |Cost.Jcost (B.xRatio σ)
        - (B.kappa σ * B.geometricDeficit σ) ^ 2 / 2|
      ≤ (B.kappa σ * B.geometricDeficit σ) ^ 4 / 2 := by
  rw [xRatio_eq_exp_of_exact B hB σ]
  exact Jcost_exp_sub_half_sq_abs_le _ hsmall

/-- **THEOREM.** |sinh a| <= cosh a for all a (from the exponential forms:
cosh a - sinh a = exp(-a) > 0 and cosh a + sinh a = exp a > 0). -/
theorem abs_sinh_le_cosh (a : ℝ) : |Real.sinh a| ≤ Real.cosh a := by
  rw [abs_le]
  constructor
  · rw [Real.sinh_eq, Real.cosh_eq]
    nlinarith [Real.exp_pos a, Real.exp_pos (-a)]
  · rw [Real.sinh_eq, Real.cosh_eq]
    nlinarith [Real.exp_pos a, Real.exp_pos (-a)]

/-- **THEOREM (cosh perturbation bound).** For all a, r:

  |cosh (a + r) - cosh a| <= cosh a * cosh r * (|r| + r^2 / 2),

from cosh(a + r) = cosh a * cosh r + sinh a * sinh r together with
cosh r - 1 <= (r^2/2) * cosh r and |sinh| bounds. -/
theorem abs_cosh_add_sub_cosh_le (a r : ℝ) :
    |Real.cosh (a + r) - Real.cosh a|
      ≤ Real.cosh a * Real.cosh r * (|r| + r ^ 2 / 2) := by
  have hsplit : Real.cosh (a + r) - Real.cosh a
      = Real.cosh a * (Real.cosh r - 1) + Real.sinh a * Real.sinh r := by
    rw [Real.cosh_add]
    ring
  rw [hsplit]
  have hcosh_r1 : 0 ≤ Real.cosh r - 1 := by linarith [Real.one_le_cosh r]
  have hca : 0 ≤ Real.cosh a := le_of_lt (Real.cosh_pos a)
  have h2 : |Real.cosh a * (Real.cosh r - 1)|
      = Real.cosh a * (Real.cosh r - 1) :=
    abs_of_nonneg (mul_nonneg hca hcosh_r1)
  have h4 : Real.cosh a * (Real.cosh r - 1)
      ≤ Real.cosh a * (r ^ 2 / 2 * Real.cosh r) :=
    mul_le_mul_of_nonneg_left (cosh_sub_one_le_half_sq_mul_cosh r) hca
  have h5 : |Real.sinh a| * |Real.sinh r|
      ≤ Real.cosh a * (|r| * Real.cosh r) :=
    mul_le_mul (abs_sinh_le_cosh a) (abs_sinh_le_abs_mul_cosh r)
      (abs_nonneg _) hca
  calc |Real.cosh a * (Real.cosh r - 1) + Real.sinh a * Real.sinh r|
      ≤ |Real.cosh a * (Real.cosh r - 1)| + |Real.sinh a * Real.sinh r| :=
        abs_add_le _ _
    _ = Real.cosh a * (Real.cosh r - 1) + |Real.sinh a| * |Real.sinh r| := by
        rw [h2, abs_mul]
    _ ≤ Real.cosh a * (r ^ 2 / 2 * Real.cosh r)
          + Real.cosh a * (|r| * Real.cosh r) := add_le_add h4 h5
    _ = Real.cosh a * Real.cosh r * (|r| + r ^ 2 / 2) := by ring

/-- **THEOREM (inexact quadratic expansion, generic form).** If
|t - a| <= R with 0 <= R and |a| <= 1, then

  |cosh t - 1 - a^2/2| <= a^4/2 + 2 * cosh R * (R + R^2/2).

The first term is the exact quartic remainder; the second is the explicit
perturbation cost of the inexactness. -/
theorem cosh_sub_one_sub_half_sq_abs_le_of_near (a t R : ℝ)
    (hsmall : |a| ≤ 1) (hR0 : 0 ≤ R) (hnear : |t - a| ≤ R) :
    |Real.cosh t - 1 - a ^ 2 / 2|
      ≤ a ^ 4 / 2 + 2 * Real.cosh R * (R + R ^ 2 / 2) := by
  have hexact : |Real.cosh a - 1 - a ^ 2 / 2| ≤ a ^ 4 / 2 := by
    have h := Jcost_exp_sub_half_sq_abs_le a hsmall
    rwa [Cost.Jcost_exp_cosh] at h
  have hpert := abs_cosh_add_sub_cosh_le a (t - a)
  rw [show a + (t - a) = t from by ring] at hpert
  have hcosha : Real.cosh a ≤ 2 := by
    have hmono : Real.cosh a ≤ Real.cosh 1 := by
      rw [Real.cosh_le_cosh]
      simpa using hsmall
    linarith [cosh_one_lt_two]
  have hcoshr : Real.cosh (t - a) ≤ Real.cosh R := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hR0]
    exact hnear
  have hr2 : (t - a) ^ 2 ≤ R ^ 2 := by
    nlinarith [hnear, abs_nonneg (t - a), sq_abs (t - a)]
  have hnn : (0 : ℝ) ≤ |t - a| + (t - a) ^ 2 / 2 :=
    add_nonneg (abs_nonneg _) (by positivity)
  have hchain : Real.cosh a * Real.cosh (t - a) * (|t - a| + (t - a) ^ 2 / 2)
      ≤ 2 * Real.cosh R * (R + R ^ 2 / 2) := by
    have h1 : Real.cosh a * Real.cosh (t - a) ≤ 2 * Real.cosh R :=
      mul_le_mul hcosha hcoshr (le_of_lt (Real.cosh_pos _)) (by norm_num)
    have h2 : |t - a| + (t - a) ^ 2 / 2 ≤ R + R ^ 2 / 2 := by
      linarith [hnear, hr2]
    have h3 : (0 : ℝ) ≤ 2 * Real.cosh R :=
      mul_nonneg (by norm_num) (le_of_lt (Real.cosh_pos R))
    calc Real.cosh a * Real.cosh (t - a) * (|t - a| + (t - a) ^ 2 / 2)
        ≤ 2 * Real.cosh R * (|t - a| + (t - a) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right h1 hnn
      _ ≤ 2 * Real.cosh R * (R + R ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left h2 h3
  have htri : |Real.cosh t - 1 - a ^ 2 / 2|
      ≤ |Real.cosh t - Real.cosh a| + |Real.cosh a - 1 - a ^ 2 / 2| := by
    have hsplit : Real.cosh t - 1 - a ^ 2 / 2
        = (Real.cosh t - Real.cosh a) + (Real.cosh a - 1 - a ^ 2 / 2) := by
      ring
    rw [hsplit]
    exact abs_add_le _ _
  linarith [htri, hpert, hexact, hchain]

/-- **THEOREM (inexact quadratic expansion of the bridge).** For ANY
recognition-ratio bridge (no exactness assumed) with small response
|kappa sigma * delta sigma| <= 1, writing R = remBound * meshScale^3 for
the remainder budget of `ratio_relation`:

  |J(x_sigma) - (kappa sigma * delta sigma)^2 / 2|
    <= (kappa sigma * delta sigma)^4 / 2 + 2 * cosh R * (R + R^2 / 2).

At remBound = 0 the perturbation term vanishes (cosh 0 * 0 = 0) and the
bound reduces to the exact statement `ratioBridge_jcost_quadratic`. This is
the theorem that actually consumes the remainder clause of the structure. -/
theorem ratioBridge_jcost_quadratic_inexact {H : Type*}
    (B : RecognitionRatioBridge H) (σ : H)
    (hsmall : |B.kappa σ * B.geometricDeficit σ| ≤ 1) :
    |Cost.Jcost (B.xRatio σ)
        - (B.kappa σ * B.geometricDeficit σ) ^ 2 / 2|
      ≤ (B.kappa σ * B.geometricDeficit σ) ^ 4 / 2
        + 2 * Real.cosh (B.remBound * B.meshScale ^ 3)
            * (B.remBound * B.meshScale ^ 3
                + (B.remBound * B.meshScale ^ 3) ^ 2 / 2) := by
  have hR0 : 0 ≤ B.remBound * B.meshScale ^ 3 :=
    mul_nonneg B.remBound_nonneg (pow_nonneg (le_of_lt B.meshScale_pos) 3)
  rw [jcost_of_ratioBridge_cosh B σ]
  exact cosh_sub_one_sub_half_sq_abs_le_of_near
    (B.kappa σ * B.geometricDeficit σ) (Real.log (B.xRatio σ))
    (B.remBound * B.meshScale ^ 3) hsmall hR0 (B.ratio_relation σ)

/-! ## §7. Status record (documentation, not mathematics) -/

/-- Status flags for the recognition-ratio bridge (documentation record;
the mathematics lives in the theorems above, not in these booleans).

**MODEL** (explicit hypothesis, this module): the structure
`RecognitionRatioBridge` itself, encoding the paper's Def 6.2
recognition-ratio admissibility clause at a fixed mesh.

**THEOREM** (kernel-checked, this module): the strong sign-no-go escape
witness (`ratioBridge_admits_negative_deficit`); the induced-ledger
reconciliation (`ratioBridgeLedger`,
`ratioBridge_separates_deficit_observables`); the J-cost parity statements
(`jcost_of_ratioBridge_cosh`, `jcost_of_ratioBridge_even_in_deficit`); the
exact and inexact quadratic expansions (`ratioBridge_jcost_quadratic`,
`ratioBridge_jcost_quadratic_inexact`).

**OPEN**: derivation of the ratio relation from stationarity (wave 1b);
the h -> 0 asymptotic family behind the O(h^3) notation (lane 2).

UPDATE (2026-07-15, `StationarityBridgeClosure`): the CONSTITUTIVE form of
wave 1b is now closed — `recognitionRatioBridge_ofStationarity` inhabits
this structure with `ratio_relation` PROVED from sourced J-stationarity
(`sourced_ratio_cubic_error`). The flag below stays `true` because its
honest reading is the residual: the deficit-source coupling inside
`sourcedAction` is itself a MODEL premise, so derivation from the BARE
`RecognitionLedger` (no constitutive action) remains open. See
`stationarityBridgeClosureStatus` for the split record. -/
structure RecognitionRatioBridgeStatus where
  /-- MODEL tier: the paper's odd ratio relation is encoded as an explicit
  hypothesis structure. -/
  paper_relation_encoded : Bool
  /-- THEOREM tier: strong witness with exactness and unit coupling
  exported and a strictly negative geometric deficit for d > 0. -/
  negative_deficit_witness : Bool
  /-- OPEN residual: derivation from the BARE ledger. The constitutive
  form is closed by `StationarityBridgeClosure.recognitionRatioBridge_ofStationarity`
  (2026-07-15); the deficit-source coupling remains a MODEL premise. -/
  derivation_from_stationarity_open : Bool
  /-- THEOREM tier (in `LedgerBridgeNoGo`): the old even/nonneg
  deficit-equality form is refuted. -/
  old_even_form_refuted : Bool

/-- The canonical status record (documentation, not new mathematics). -/
def recognitionRatioBridgeStatus : RecognitionRatioBridgeStatus where
  paper_relation_encoded := true
  negative_deficit_witness := true
  derivation_from_stationarity_open := true
  old_even_form_refuted := true

/-- Status flags record (rfl-forced; documentation, not new mathematics). -/
theorem recognitionRatioBridgeStatus_flags :
    recognitionRatioBridgeStatus.paper_relation_encoded = true ∧
    recognitionRatioBridgeStatus.negative_deficit_witness = true ∧
    recognitionRatioBridgeStatus.derivation_from_stationarity_open = true ∧
    recognitionRatioBridgeStatus.old_even_form_refuted = true :=
  ⟨rfl, rfl, rfl, rfl⟩

end SevenGaps
end Gravity
end IndisputableMonolith
