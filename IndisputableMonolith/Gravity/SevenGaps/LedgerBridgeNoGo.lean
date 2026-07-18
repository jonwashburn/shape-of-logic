import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Gravity.RecognitionLedger
import IndisputableMonolith.Gravity.LedgerToGeometryBridge

/-!
# Seven Gaps, Lane 1a: the ledger-to-hinge bridge no-go

## Status: THEOREM (0 sorry, 0 RS-internal axiom, no decide/native_decide).

This module proves two obstruction theorems against the assumed form of the
substrate-to-triangulation bridge (`Gravity.LedgerToHingeBridge.bridge_assumed`,
which equates the recognition-ledger deficit at each cell with a raw geometric
hinge deficit). PRECISE SCOPE OF WHAT IS FORMALIZED: (1) no bridge exists for
any specification that puts a strictly negative deficit in the image of the
comparison map; (2) no parity-covariant J-ratio ledger family has a deficit
with a signed linear response. The composite reading "hence the assumed form
is unsatisfiable on two-sided weak-field deformation classes" additionally
uses the GEOMETRIC PREMISE (not formalized here, prose tier) that such
classes contain hinges of strictly negative deficit in the image of any
faithful comparison map, and that the weak-field Regge response is odd at
leading order.

**1. Sign no-go.** The ledger deficit is a sum of J-costs, hence provably
nonnegative (`RecognitionLedger.deficit_nonneg`). Weak-field Regge deficit
angles are signed: a two-sided deformation class contains hinges with
strictly negative deficit. Consequently every `LedgerToHingeBridge` forces
its geometric deficit to be nonnegative on the image of the comparison map
(`bridge_forces_nonneg_geometricDeficit`), and no bridge exists whose
specified deficit assignment is negative anywhere on that image
(`no_bridge_matches_negative_deficit_spec`).

**2. Parity no-go.** Any ledger built from J-costs of comparison ratios
inherits the ratio symmetry J(x) = J(1/x) (`Cost.Jcost_symm`). If the
one-parameter ratio family satisfies the natural ratio parity
r(-ε) = r(ε)⁻¹ (e.g. exponential strain ratios r = exp(ε·s)), the induced
deficit is an EVEN function of the deformation parameter ε
(`jRatioDeficit_even`, `ledger_family_deficit_even_of_ratio_parity`),
with O(ε²) leading term. The signed Regge deficit response is odd, O(ε).
An even function can match an odd function only if both vanish identically
(`even_and_odd_forces_zero`); in particular a signed linear-response
deficit δ(ε) = c·ε with c ≠ 0 admits no J-ratio realization on any
symmetric interval (`no_jRatio_deficit_linear_response`,
`no_ledger_family_linear_response`).

**Reading revision.** The status structure `LedgerBridgeNoGoStatus` records
what these theorems change about the reading of
`LedgerToHingeBridge.bridge_assumed`: the field is not a neutral assumption
awaiting derivation; it carries the two proved obstructions above, and under
the stated geometric premise (prose tier) it is unsatisfiable on two-sided
weak-field classes. The corrected bridge target is the nonnegative
curvature-QUADRATIC geometric energy (discrete Isaacson-type form
Σ_h A_h · δ_h²), built in
`IndisputableMonolith.Gravity.SevenGaps.LedgerEnergyBridge`.

Honest tier split: the sign and parity theorems are THEOREM; the negative
deficits and odd leading response of two-sided weak-field Regge classes are
the geometric input motivating the hypotheses (MODEL/prose, not formalized
in this file).
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps

/-! ## §1. Sign no-go -/

/-- **THEOREM (sign obstruction, positive form).** Any bridge satisfying the
assumed deficit-matching condition forces the geometric deficit to be
nonnegative at every hinge in the image of the comparison map `x_sigma`.
Direct consequence of `RecognitionLedger.deficit_nonneg`: ledger deficits
are sums of nonnegative J-costs. -/
theorem bridge_forces_nonneg_geometricDeficit
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {H : Type*}
    (L : RecognitionLedger.RecognitionLedger Λ)
    (B : LedgerToHingeBridge H L) (i : Λ) :
    0 ≤ B.geometricDeficit (B.x_sigma i) := by
  rw [← B.bridge_assumed i]
  exact RecognitionLedger.deficit_nonneg L i

/-- **THEOREM (sign obstruction, nonexistence form).** Given any hinge
specification (comparison map `x` and deficit assignment `δ`) for which some
cell `i` sees a strictly negative geometric deficit `δ (x i) < 0`, there is
NO `LedgerToHingeBridge` realizing that specification, for any recognition
ledger `L` whatsoever. Combined with the geometric premise that two-sided
(signed) weak-field deformation classes place negative deficits in the image
of any faithful comparison map (prose tier, not formalized here), this
excludes the assumed bridge form on such classes. -/
theorem no_bridge_matches_negative_deficit_spec
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {H : Type*}
    (L : RecognitionLedger.RecognitionLedger Λ)
    (x : Λ → H) (δ : H → ℝ) (i : Λ) (hneg : δ (x i) < 0) :
    ¬ ∃ B : LedgerToHingeBridge H L, B.x_sigma = x ∧ B.geometricDeficit = δ := by
  rintro ⟨B, hx, hd⟩
  have h := bridge_forces_nonneg_geometricDeficit L B i
  rw [hx, hd] at h
  exact absurd h (not_le.mpr hneg)

/-! ## §2. Parity no-go

A J-ratio ledger family assigns to each cell pair the J-cost of a
one-parameter comparison ratio. The natural ratio parity r(-ε) = r(ε)⁻¹
(satisfied by exponential strain ratios r = exp(ε·s)) makes every induced
cost, hence every induced deficit, EVEN in the deformation parameter ε. -/

/-- **THEOREM (abstract ratio parity).** For any positive one-parameter ratio
family with the natural parity r(-ε) = r(ε)⁻¹, the J-cost of the ratio is an
even function of ε. This is exactly J(x) = J(1/x) (`Cost.Jcost_symm`). -/
theorem Jcost_ratio_parity (r : ℝ → ℝ) (hpos : ∀ ε, 0 < r ε)
    (hpar : ∀ ε, r (-ε) = (r ε)⁻¹) (ε : ℝ) :
    Cost.Jcost (r (-ε)) = Cost.Jcost (r ε) := by
  rw [hpar ε]
  exact (Cost.Jcost_symm (hpos ε)).symm

/-- The J-cost of the exponential strain ratio exp(ε·s i j) on cell pair
(i, j). This is the generic J-ratio ledger cell cost; no antisymmetry of `s`
is required for the parity argument. -/
noncomputable def jRatioCellCost {Λ : Type*} (s : Λ → Λ → ℝ) (ε : ℝ)
    (i j : Λ) : ℝ :=
  Cost.Jcost (Real.exp (ε * s i j))

/-- The deficit at cell `i` induced by the J-ratio family: the sum over all
cells of the cell-pair J-costs (the raw analogue of
`RecognitionLedger.deficit`, needing no ledger axioms). -/
noncomputable def jRatioDeficit {Λ : Type*} [Fintype Λ] (s : Λ → Λ → ℝ)
    (ε : ℝ) (i : Λ) : ℝ :=
  ∑ j, jRatioCellCost s ε i j

/-- **THEOREM.** Each J-ratio cell cost is even in ε: the exponential strain
ratio satisfies exp(-ε·s) = (exp(ε·s))⁻¹ and J(x) = J(1/x). -/
theorem jRatioCellCost_even {Λ : Type*} (s : Λ → Λ → ℝ) (ε : ℝ) (i j : Λ) :
    jRatioCellCost s (-ε) i j = jRatioCellCost s ε i j := by
  unfold jRatioCellCost
  have hexp : Real.exp (-ε * s i j) = (Real.exp (ε * s i j))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hexp]
  exact (Cost.Jcost_symm (Real.exp_pos _)).symm

/-- **THEOREM (parity no-go, deficit form).** The J-ratio deficit at every
cell is an EVEN function of the deformation parameter ε. Its response to a
deformation therefore has no odd part: the leading term is O(ε²), never the
signed O(ε) linear response of a weak-field Regge deficit. -/
theorem jRatioDeficit_even {Λ : Type*} [Fintype Λ] (s : Λ → Λ → ℝ) (ε : ℝ)
    (i : Λ) :
    jRatioDeficit s (-ε) i = jRatioDeficit s ε i := by
  unfold jRatioDeficit
  exact Finset.sum_congr rfl fun j _ => jRatioCellCost_even s ε i j

/-- **THEOREM (even vs. odd exclusion).** An even function of ε can equal an
odd function of ε only if both vanish identically. -/
theorem even_and_odd_forces_zero (g d : ℝ → ℝ)
    (hg : ∀ ε, g (-ε) = g ε) (hd : ∀ ε, d (-ε) = - d ε)
    (hmatch : ∀ ε, g ε = d ε) (ε : ℝ) :
    g ε = 0 ∧ d ε = 0 := by
  have h1 : d ε = - d ε := by
    calc d ε = g ε := (hmatch ε).symm
      _ = g (-ε) := (hg ε).symm
      _ = d (-ε) := hmatch (-ε)
      _ = - d ε := hd ε
  have h2 : d ε = 0 := by linarith
  exact ⟨(hmatch ε).trans h2, h2⟩

/-- **THEOREM (parity no-go, linear-response form).** A signed
linear-response deficit assignment δ(ε) = c·ε with c ≠ 0 admits no J-ratio
realization on any symmetric interval [-a, a] with a > 0: evenness of the
J-ratio deficit forces c·a = c·(-a). -/
theorem no_jRatio_deficit_linear_response {Λ : Type*} [Fintype Λ]
    (s : Λ → Λ → ℝ) (i : Λ) (c a : ℝ) (hc : c ≠ 0) (ha : 0 < a) :
    ¬ (∀ ε : ℝ, |ε| ≤ a → jRatioDeficit s ε i = c * ε) := by
  intro hmatch
  have hpa : jRatioDeficit s a i = c * a :=
    hmatch a (le_of_eq (abs_of_pos ha))
  have habs : |(-a)| = a := by
    rw [abs_neg]
    exact abs_of_pos ha
  have hna : jRatioDeficit s (-a) i = c * (-a) :=
    hmatch (-a) (le_of_eq habs)
  rw [jRatioDeficit_even] at hna
  have hca : c * a = 0 := by linarith
  rcases mul_eq_zero.mp hca with h | h
  · exact hc h
  · exact absurd h (ne_of_gt ha)

/-- **THEOREM (parity no-go, ledger-family form).** For any one-parameter
family of recognition ledgers whose costs are J-costs of PARITY-COVARIANT
positive ratios (r(-ε) = r(ε)⁻¹), the `RecognitionLedger.deficit` at every
cell is even in ε. Scope note: the parity hypothesis is genuine scope, not
decoration; ratio families violating it (e.g. r = exp(ε·s + ε²·t) with
t ≠ 0) escape this theorem. Exponential strain ratios r = exp(ε·s), the
natural first-order substrate deformations, satisfy it. -/
theorem ledger_family_deficit_even_of_ratio_parity
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : ℝ → RecognitionLedger.RecognitionLedger Λ)
    (r : ℝ → Λ → Λ → ℝ)
    (hpos : ∀ ε i j, 0 < r ε i j)
    (hcost : ∀ ε i j, (L ε).cost i j = Cost.Jcost (r ε i j))
    (hpar : ∀ ε i j, r (-ε) i j = (r ε i j)⁻¹)
    (ε : ℝ) (i : Λ) :
    RecognitionLedger.deficit (L (-ε)) i
      = RecognitionLedger.deficit (L ε) i := by
  unfold RecognitionLedger.deficit
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcost (-ε) i j, hcost ε i j, hpar ε i j]
  exact (Cost.Jcost_symm (hpos ε i j)).symm

/-- **THEOREM (parity no-go, ledger-family linear-response form).** No
one-parameter family of recognition ledgers with parity-covariant J-ratio
costs can have a deficit matching a signed linear response c·ε (c ≠ 0) on
any symmetric interval. -/
theorem no_ledger_family_linear_response
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (L : ℝ → RecognitionLedger.RecognitionLedger Λ)
    (r : ℝ → Λ → Λ → ℝ)
    (hpos : ∀ ε i j, 0 < r ε i j)
    (hcost : ∀ ε i j, (L ε).cost i j = Cost.Jcost (r ε i j))
    (hpar : ∀ ε i j, r (-ε) i j = (r ε i j)⁻¹)
    (i : Λ) (c a : ℝ) (hc : c ≠ 0) (ha : 0 < a) :
    ¬ (∀ ε : ℝ, |ε| ≤ a → RecognitionLedger.deficit (L ε) i = c * ε) := by
  intro hmatch
  have hpa : RecognitionLedger.deficit (L a) i = c * a :=
    hmatch a (le_of_eq (abs_of_pos ha))
  have habs : |(-a)| = a := by
    rw [abs_neg]
    exact abs_of_pos ha
  have hna : RecognitionLedger.deficit (L (-a)) i = c * (-a) :=
    hmatch (-a) (le_of_eq habs)
  rw [ledger_family_deficit_even_of_ratio_parity L r hpos hcost hpar a i]
    at hna
  have hca : c * a = 0 := by linarith
  rcases mul_eq_zero.mp hca with h | h
  · exact hc h
  · exact absurd h (ne_of_gt ha)

/-! ### Concrete two-cell instance

The minimal substrate exhibiting the parity mechanism: two cells with a
single strain σ between them. The induced deficit is cosh(ε·σ) - 1, an
explicitly even function of ε with leading term (σ²/2)·ε². -/

/-- The two-cell antisymmetric strain: s 0 1 = σ, s 1 0 = -σ, diagonal 0. -/
noncomputable def twoCellStrain (σ : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then 0 else if i = 0 then σ else -σ

/-- **THEOREM (two-cell parity witness).** On the two-cell substrate the
J-ratio deficit at cell 0 is exactly cosh(ε·σ) - 1: even in ε, O(ε²) at
small ε, and containing no odd (signed linear-response) part. -/
theorem twoCell_jRatioDeficit (σ ε : ℝ) :
    jRatioDeficit (twoCellStrain σ) ε 0 = Real.cosh (ε * σ) - 1 := by
  have h00 : twoCellStrain σ 0 0 = 0 := by norm_num [twoCellStrain]
  have h01 : twoCellStrain σ 0 1 = σ := by norm_num [twoCellStrain]
  unfold jRatioDeficit jRatioCellCost
  rw [Fin.sum_univ_two, h00, h01, mul_zero, Real.exp_zero, Cost.Jcost_unit0,
    zero_add, Cost.Jcost_exp_cosh]

/-! ## §3. Status: the corrected reading of `bridge_assumed` -/

/-- Status flags for the ledger-bridge no-go (documentation record; the
mathematics lives in the theorems above, not in these booleans).

What is PROVED: (1) sign obstruction, `bridge_forces_nonneg_geometricDeficit`
and `no_bridge_matches_negative_deficit_spec` (no bridge for any
negative-deficit-in-image specification); (2) parity obstruction,
`jRatioDeficit_even` and `no_ledger_family_linear_response` (no signed linear
response for parity-covariant J-ratio families). What is GEOMETRIC PREMISE
(prose tier): two-sided weak-field Regge classes carry negative image
deficits and odd leading response. Under that premise the assumed raw-deficit
bridge form is excluded on such classes, and the honest bridge target is the
nonnegative curvature-quadratic energy Σ_h A_h · δ_h² built in
`SevenGaps.LedgerEnergyBridge` (deliverable B of this lane). -/
structure LedgerBridgeNoGoStatus where
  /-- PROVED: no bridge exists for any specification with a strictly negative
  deficit in the image of the comparison map (sign obstruction). -/
  sign_nogo_proved_for_negative_image_specs : Bool
  /-- PROVED: parity-covariant J-ratio ledger families admit no signed
  linear-response deficit (parity obstruction). -/
  parity_nogo_proved_for_parity_covariant_families : Bool
  /-- The corrected bridge target is the curvature-quadratic energy
  Σ_h A_h · δ_h², not the raw signed deficit Σ_h A_h · δ_h. -/
  corrected_target_is_quadratic_energy : Bool

/-- The canonical no-go status: all flags true, forced by `rfl`. -/
def ledgerBridgeNoGoStatus : LedgerBridgeNoGoStatus where
  sign_nogo_proved_for_negative_image_specs := true
  parity_nogo_proved_for_parity_covariant_families := true
  corrected_target_is_quadratic_energy := true

/-- Status flags record (rfl-forced; documentation, not new mathematics). -/
theorem ledgerBridgeNoGoStatus_flags :
    ledgerBridgeNoGoStatus.sign_nogo_proved_for_negative_image_specs = true ∧
    ledgerBridgeNoGoStatus.parity_nogo_proved_for_parity_covariant_families
        = true ∧
    ledgerBridgeNoGoStatus.corrected_target_is_quadratic_energy = true :=
  ⟨rfl, rfl, rfl⟩

end SevenGaps
end Gravity
end IndisputableMonolith
