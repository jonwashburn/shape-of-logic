import IndisputableMonolith.Gravity.SevenGaps.HKTKineticFromRecognitionCost

/-!
# Campaign 2 Track A: the reparametrization attack on the constraint sector

`HKTKineticFromRecognitionCost` §8 derives field-independence of the kinetic
weight from the Recognition Composition Law (RCL). The paper built on it,
`papers/QG_Constraint_Sector_Recognition_Premise_20260725.tex`, printed a
falsifier it had not run:

> Exhibit a weight functional that is NOT `SatisfiesCompositionLaw`, satisfies
> the remaining clauses of the model class, and still forces unit weight.

The same attack killed the framing of O5 (`Gap1ClassLengthsFromRecognitionCost`
§5b), where a strictly increasing reparametrization of the recognition cost
reproduced every rung of the ladder while violating the composition law, so the
ladder could not identify `J`. The paper's stated reason to expect the attack to
fail here was that §8's conclusion is a functional form rather than a level set.
This module settles it. The reason was wrong, and the attack lands, though at
lower severity than in O5.

## What is established

**§1. The forcing never looks at the recognition cost.** The proof of
`compositionLaw_forces_unit_weight` in §8 evaluates at the single point
`x = y = 2` and uses three numerical values of `J`. That is an artifact of the
proof, not of the theorem: `compositionLaw_forces_unit_weight_generic` shows the
same conclusion for an arbitrary `F` satisfying the law, with the only input
being that `F` is nonzero somewhere. The mechanism is that the law is quadratic
in the function, so scaling by `w` produces `w ^ 2 = w` on the quadratic term
and `w = w` on the linear ones. `Cost.Jcost` is not used.

**§2. The law does not pin the recognition cost.** Substituting `x ↦ x ^ n`
carries solutions to solutions (`satisfiesCompositionLaw_comp_pow`), so
`fun x => J (x ^ n)` satisfies the law for every `n`, and differs from `J` for
`n ≥ 2` (`powCost_two_ne_Jcost`). Each member is a strictly increasing
reparametrization of `J` on `[1, ∞)`, since `J (x ^ n)` is `T n` applied to
`J x + 1`, minus one, with `T n` the Chebyshev polynomial. So the orbit under
reparametrization is nontrivial and lands inside the law's solution set rather
than outside it.

This is the invariance test that Campaign 1's third acceptance rule demands, and
§8 fails it: the tested property is invariant under a group action that moves
`J`, so the test cannot pin `J`.

**§3. Calibration, not recognition, is the discriminator.** Within the power
family the second log-derivative at the origin is `n ^ 2`
(`deriv2_G_powCost`), so exactly one member is calibrated
(`isCalibrated_powCost_iff`). This is the Lean form of what
`Cost.FunctionalEquation.law_of_logic_forces_jcost_with_regularization` already
required and §8 dropped: the uniqueness theorem for `J` takes RCL *and*
calibration, and §8 imposes only the first half.

**§4. The falsifier as printed is met, and was ill-posed.** A one-point
normalization `w * J 2 = J 2` is not the composition law, leaves the other
clauses untouched, and forces `w = 1` on the nose, which is strictly sharper
than RCL's `w ∈ {0, 1}` (`calibratedWeightAtTwo_forces_one`). The two clauses
are genuinely different predicates: `w = 0` satisfies RCL's and not this one
(`rclWeight_zero`, `not_calibratedWeightAtTwo_zero`). So the falsifier is
satisfied by a cheaper clause, which means the falsifier as written could never
have discriminated: any predicate implying `w = 1` meets it, including `w = 1`.
Recorded as a defect in the paper's gate, not as a defect in its theorem.

## §4b. Neither clause carries recognition content

This module's first conclusion was a division of labour: the composition law buys
unit weight by generic algebra, and the recognition cost buys quadraticity of the
momentum sector, where it is not replaceable. A cross-family hostile panel
attacked that conclusion and the second half did not survive.

The profile clause reads the cost in the chart `t = 2 arsinh (λ p)`, and that chart
is `J`'s own inverse: `chart_alone_forces_the_cost` proves that *any* function
exactly quadratic in it is a multiple of the cost, using no functional equation, no
regularity and no positivity. So the clause is a uniqueness theorem for the cost
wearing the clothes of a physical premise, its solution set is the one-parameter
scale family (`profile_clause_solution_set_is_a_scale_family`), and no substitution
into it could ever have succeeded. `oscCost_not_quadratic_in_log_chart` is
therefore true and nearly empty: it is one instance of a general fact that leaves
recognition out of it.

Worse for the attribution, the chart is *typed in*. `exactCostKineticProfile`
writes `2 * Real.arsinh (lam * p)` as a literal and nothing derives it from the
substrate, so the clause does not derive a quadratic momentum sector from
recognition; it writes down a quadratic in a coordinate chosen to make the cost
look quadratic. The coefficient `2 λ ^ 2` is the double-angle identity.

So the corrected reading of §8: the law clause contributes one bit (`w ^ 2 = w`) by
algebra generic to any equation quadratic in the unknown function, the profile
clause contributes a change of variables, and field-independence needs the model
class's separate nonvanishing clause `∀ a b, W a b ≠ 0` on top of the law, since
the law alone permits a field-dependent weight valued in `{0, 1}`. Nothing in
either clause is recognition-specific.

## Scope

The theorems are untouched. `RCLKineticCanonicalMom` is still inhabited, its
conclusion still holds, and the clause still excludes the kill inhabitant
(`no_rcl_presentation_of_vacuumKinetic`). What changes is what may be claimed about
why, and the claim shrinks to nothing on the recognition side.

The power family here is indexed by natural exponents; the real-exponent family
`J (x ^ c)` would need `rpow` and is not formalized. The one thing that would
restore recognition content to the profile clause is a derivation of the
half-imbalance chart from the substrate rather than a stipulation of it. That is
the open successor, and it is now the only route by which this sector can carry
recognition content at all.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace ConstraintSectorReparamAttack

open IndisputableMonolith.Cost.FunctionalEquation

/-- `Cost.Jcost` satisfies the composition law, routed through the repo's own
cosh-addition identity so this module stays on `FunctionalEquation`'s import
path rather than pulling in `CostUniqueness`. -/
theorem jcost_rcl : SatisfiesCompositionLaw Cost.Jcost :=
  (composition_law_equiv_coshAdd Cost.Jcost).2 Jcost_cosh_add_identity

/-! ## §1. The forcing never looks at the recognition cost -/

/-- **The composition law forces unit weight for any of its solutions.**

If `F` satisfies the law and `w * F` satisfies it too, then `w` is `0` or `1`,
provided `F` is nonzero at some pair of points. No property of `Cost.Jcost`
beyond membership in the solution set is used.

The mechanism: the law is quadratic in the function, so the scaling passes
through the linear terms as `w` and through the product term as `w ^ 2`,
leaving `w ^ 2 = w` once a nonvanishing product is available. -/
theorem compositionLaw_forces_unit_weight_generic (F : ℝ → ℝ) (w : ℝ)
    (hF : SatisfiesCompositionLaw F)
    (hwF : SatisfiesCompositionLaw (fun x => w * F x))
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : F x * F y ≠ 0) :
    w = 0 ∨ w = 1 := by
  have h1 := hF x y hx hy
  have h2 := hwF x y hx hy
  simp only at h2
  have hkey : (w * (w - 1)) * (2 * (F x * F y)) = 0 := by
    linear_combination w * h1 - h2
  have hfac : w * (w - 1) = 0 := by
    rcases mul_eq_zero.mp hkey with h | h
    · exact h
    · exact absurd (by linarith : F x * F y = 0) hne
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- The repo's §8 lemma is the `F = Cost.Jcost` instance of the generic one, so
the recognition cost was never load-bearing for that step. -/
theorem compositionLaw_forces_unit_weight_is_an_instance (w : ℝ)
    (hComp : SatisfiesCompositionLaw (fun x => w * Cost.Jcost x)) :
    w = 0 ∨ w = 1 :=
  compositionLaw_forces_unit_weight_generic Cost.Jcost w
    jcost_rcl hComp
    (x := 2) (y := 2) (by norm_num) (by norm_num)
    (by norm_num [Cost.Jcost])

/-! ## §2. The law does not pin the recognition cost -/

/-- **Argument rescaling carries solutions to solutions.** The law only sees the
multiplicative structure of the argument, and `x ↦ x ^ n` is a monoid
endomorphism of the positive reals, so it acts on the solution set. -/
theorem satisfiesCompositionLaw_comp_pow (F : ℝ → ℝ) (n : ℕ)
    (hF : SatisfiesCompositionLaw F) :
    SatisfiesCompositionLaw (fun x => F (x ^ n)) := by
  intro x y hx hy
  simp only
  rw [mul_pow, div_pow]
  exact hF (x ^ n) (y ^ n) (pow_pos hx n) (pow_pos hy n)

/-- The `n`-th member of the power family: the recognition cost read at a
rescaled argument. `powCost 1` is `Cost.Jcost` and `powCost 0` is the zero
solution. -/
noncomputable def powCost (n : ℕ) : ℝ → ℝ := fun x => Cost.Jcost (x ^ n)

theorem powCost_one : powCost 1 = Cost.Jcost := by
  funext x; simp [powCost]

/-- Every member of the family satisfies the composition law. -/
theorem powCost_satisfiesCompositionLaw (n : ℕ) :
    SatisfiesCompositionLaw (powCost n) :=
  satisfiesCompositionLaw_comp_pow Cost.Jcost n
    jcost_rcl

/-- The family is not constant: the square member already differs from `J`. -/
theorem powCost_two_ne_Jcost : powCost 2 ≠ Cost.Jcost := by
  intro h
  have := congrArg (fun f => f 2) h
  norm_num [powCost, Cost.Jcost] at this

/-- `J` is strictly positive above one, which is the nonvanishing input §1
needs. -/
theorem Jcost_pos_of_one_lt {x : ℝ} (hx : 1 < x) : 0 < Cost.Jcost x := by
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hsq : 0 < (x - 1) ^ 2 := pow_pos (by linarith) 2
  have hinv : x⁻¹ * x = 1 := inv_mul_cancel₀ (ne_of_gt hx0)
  simp only [Cost.Jcost]
  nlinarith [hsq, hinv, hx0]

/-- **The whole family forces unit weight.** So the conclusion §8 draws is
constant along the orbit, which is why the attack does not damage the theorem
even though it damages the attribution. -/
theorem powCost_forces_unit_weight (n : ℕ) (hn : n ≠ 0) (w : ℝ)
    (hw : SatisfiesCompositionLaw (fun x => w * powCost n x)) :
    w = 0 ∨ w = 1 := by
  have hpow : ∀ m : ℕ, (1 : ℝ) ≤ (2 : ℝ) ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; nlinarith
  have h2 : (1 : ℝ) < (2 : ℝ) ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [pow_succ]
    nlinarith [hpow m]
  have hpos : 0 < powCost n 2 := Jcost_pos_of_one_lt h2
  exact compositionLaw_forces_unit_weight_generic (powCost n) w
    (powCost_satisfiesCompositionLaw n) hw
    (x := 2) (y := 2) (by norm_num) (by norm_num)
    (by positivity)

/-! ## §2b. The law admits solutions that are not costs at all

The power family stays inside the recognition family, which would make the
attack mild. The oscillatory branch of d'Alembert does not, and it is the reason
the verdict below is not mild. `cos (c log x) - 1` satisfies the composition
law, takes negative values, and so is not a cost under any reading, yet it
forces unit weight exactly as `J` does.

What it cannot do is the other half of §8's job. `J` was chosen for the chart
identity `J (exp (2 arsinh u)) = 2 u ^ 2`, which is what makes the momentum
sector quadratic and hence the response linear. The oscillatory solution is
bounded, so no such identity exists for it
(`oscCost_not_quadratic_in_log_chart`). That is the division of labour, and
stating it is the substantive result of this track: the composition law buys
unit weight and knows nothing about recognition, while the recognition cost's
own functional form buys quadraticity and is not replaceable. -/

/-- The oscillatory branch of the d'Alembert solution set. -/
noncomputable def oscCost (c : ℝ) : ℝ → ℝ :=
  fun x => Real.cos (c * Real.log x) - 1

/-- **The oscillatory branch satisfies the composition law.** The law is the
cosine addition identity in disguise as much as it is the hyperbolic one. -/
theorem oscCost_satisfiesCompositionLaw (c : ℝ) :
    SatisfiesCompositionLaw (oscCost c) := by
  intro x y hx hy
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  simp only [oscCost, Real.log_mul hx0 hy0, Real.log_div hx0 hy0, mul_add,
    mul_sub, Real.cos_add, Real.cos_sub]
  ring

/-- It takes the value `-2`, so it is not a cost: `Cost.Jcost` and every
recognition cost is nonnegative on the positive reals. -/
theorem oscCost_neg_at_exp_pi : oscCost 1 (Real.exp Real.pi) = -2 := by
  simp [oscCost, Real.log_exp]
  norm_num

/-- **A non-cost forces unit weight just as well.** So the forcing step cannot
be reading any recognition content out of the clause. -/
theorem oscCost_forces_unit_weight (w : ℝ)
    (hw : SatisfiesCompositionLaw (fun x => w * oscCost 1 x)) :
    w = 0 ∨ w = 1 := by
  have hx : (0 : ℝ) < Real.exp Real.pi := Real.exp_pos _
  refine compositionLaw_forces_unit_weight_generic (oscCost 1) w
    (oscCost_satisfiesCompositionLaw 1) hw hx hx ?_
  rw [oscCost_neg_at_exp_pi]
  norm_num

/-- **But it cannot make the momentum sector quadratic.** `J` earns its place in
the model class through the chart identity `Jlog_two_arsinh`; the oscillatory
solution is bounded and admits no such identity, in the log chart or any
rescaling of it. This is what the composition law alone does not supply. -/
theorem oscCost_not_quadratic_in_log_chart :
    ¬ ∃ c : ℝ, ∀ t : ℝ, oscCost 1 (Real.exp t) = c * t ^ 2 := by
  rintro ⟨c, hc⟩
  have h2pi := hc (2 * Real.pi)
  have hpi := hc Real.pi
  simp only [oscCost, Real.log_exp, one_mul, Real.cos_two_pi, Real.cos_pi] at h2pi hpi
  have hc0 : c = 0 := by
    have hne : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
    have : c * (2 * Real.pi) ^ 2 = 0 := by linarith
    exact by
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hne
  rw [hc0] at hpi
  norm_num at hpi

/-! ## §3. Calibration, not recognition, is the discriminator -/

/-- In the logarithmic chart the family is `cosh (n t) - 1`. -/
theorem G_powCost (n : ℕ) (t : ℝ) :
    G (powCost n) t = Real.cosh ((n : ℝ) * t) - 1 := by
  simp only [G, powCost, Cost.Jcost]
  rw [← Real.exp_nat_mul, Real.cosh_eq, ← Real.exp_neg]

/-- The log-curvature of the `n`-th member is `n ^ 2`. -/
theorem deriv2_G_powCost (n : ℕ) :
    deriv (deriv (G (powCost n))) 0 = (n : ℝ) ^ 2 := by
  have hG : G (powCost n) = fun t => Real.cosh ((n : ℝ) * t) - 1 :=
    funext (G_powCost n)
  have hfirst : deriv (fun t : ℝ => Real.cosh ((n : ℝ) * t) - 1)
      = fun t : ℝ => Real.sinh ((n : ℝ) * t) * (n : ℝ) := by
    funext t
    have hin : HasDerivAt (fun s : ℝ => (n : ℝ) * s) (n : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul ((n : ℝ))
    exact (hin.cosh.sub_const 1).deriv
  have hin0 : HasDerivAt (fun s : ℝ => (n : ℝ) * s) (n : ℝ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul ((n : ℝ))
  have hsecond : HasDerivAt (fun t : ℝ => Real.sinh ((n : ℝ) * t) * (n : ℝ))
      (Real.cosh ((n : ℝ) * 0) * (n : ℝ) * (n : ℝ)) 0 :=
    hin0.sinh.mul_const ((n : ℝ))
  rw [hG, hfirst, hsecond.deriv]
  simp
  ring

/-- **Exactly one member of the family is calibrated.** The composition law
leaves a one-parameter family; calibration is what collapses it to `J`. This is
the clause §8 does not impose. -/
theorem isCalibrated_powCost_iff (n : ℕ) :
    IsCalibrated (powCost n) ↔ n = 1 := by
  rw [IsCalibrated, deriv2_G_powCost]
  constructor
  · intro h
    have hn : (n : ℝ) ^ 2 = (1 : ℝ) ^ 2 := by simpa using h
    have : (n : ℝ) = 1 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1), sq_nonneg ((n : ℝ) + 1),
        Nat.cast_nonneg (α := ℝ) n]
    exact_mod_cast this
  · rintro rfl; norm_num

/-! ## §4. The falsifier as printed is met, and was ill-posed -/

/-- A one-point normalization of the cost weight. This is not the composition
law and has no recognition content: it says the weighted cost agrees with the
cost at a single argument. -/
def CalibratedWeightAtTwo (w : ℝ) : Prop := w * Cost.Jcost 2 = Cost.Jcost 2

/-- It forces unit weight, and does so more sharply than the law, which leaves
the `w = 0` branch open. -/
theorem calibratedWeightAtTwo_forces_one (w : ℝ) (h : CalibratedWeightAtTwo w) :
    w = 1 := by
  have hJ : Cost.Jcost 2 = 1 / 4 := by norm_num [Cost.Jcost]
  rw [CalibratedWeightAtTwo, hJ] at h
  linarith

/-- The zero weight satisfies the composition-law clause. -/
theorem rclWeight_zero :
    SatisfiesCompositionLaw (fun x => (0 : ℝ) * Cost.Jcost x) := by
  intro x y _ _
  simp

/-- The zero weight does not satisfy the normalization clause. -/
theorem not_calibratedWeightAtTwo_zero : ¬ CalibratedWeightAtTwo 0 := by
  intro h
  have := calibratedWeightAtTwo_forces_one 0 h
  norm_num at this

/-- **The two clauses are different predicates.** So the normalization is a
genuine witness for the falsifier rather than the composition law in disguise. -/
theorem calibratedWeightAtTwo_ne_rclWeight :
    CalibratedWeightAtTwo
      ≠ fun w => SatisfiesCompositionLaw (fun x => w * Cost.Jcost x) := by
  intro h
  have := congrArg (fun P => P 0) h
  simp only [eq_iff_iff] at this
  exact not_calibratedWeightAtTwo_zero (this.mpr rclWeight_zero)

/-- **The falsifier printed in the paper is met.**

There is a clause that is not the composition law, that forces unit weight, and
that leaves every other clause of the model class alone. The falsifier is
therefore satisfied as written.

The finding this records is about the gate, not the theorem. A falsifier of the
form "exhibit any non-`P` clause with the same consequence" is met by the
consequence itself, so it cannot discriminate and should never have been
printed. §5 states the repaired version. -/
theorem falsifier_as_printed_is_met :
    (CalibratedWeightAtTwo
      ≠ fun w => SatisfiesCompositionLaw (fun x => w * Cost.Jcost x))
    ∧ (∀ w : ℝ, CalibratedWeightAtTwo w → w = 1) :=
  ⟨calibratedWeightAtTwo_ne_rclWeight, calibratedWeightAtTwo_forces_one⟩

/-! ## §4b. The profile clause needs no composition law at all

A cross-family hostile panel attacked the §5 verdict below on 2026-07-25 and
found something sharper than either side of it. The verdict says the recognition
cost is load-bearing for quadraticity because the oscillatory branch cannot be
substituted into the profile clause. That is true, and it is nearly empty, because
the profile clause has exactly *one* solution and says so without help.

The clause reads `h a b p = W a b * Jlog (2 * arsinh (lam * p)) + U a b`, and the
chart `2 * arsinh` is J's own inverse chart: `u ↦ 2 arsinh u` is the substitution
that turns `Jlog` into `2 u ^ 2`. So asking for a function that is quadratic in
that chart is asking for `Jlog` up to scale, and `chart_alone_forces_the_cost`
proves it: no functional equation, no regularity, no measurability, no positivity.

Two consequences, and the second is why this section exists.

First, "the recognition cost is not replaceable in the profile clause" is true but
carries no information about recognition. It holds for the same reason that
`f (f⁻¹ y) = y` holds.

Second, the chart is *typed in*. `exactCostKineticProfile` in
`HKTKineticFromRecognitionCost` writes `2 * Real.arsinh (lam * p)` as a literal,
and no theorem in the repo derives that chart from the substrate. So the clause
does not derive a quadratic momentum sector from recognition; it writes a
quadratic in a coordinate chosen to make the recognition cost look quadratic, and
the coefficient `2 λ ^ 2` is the double-angle identity
`cosh 2θ = 1 + 2 sinh ^ 2 θ`. Until a substrate derivation of the chart exists,
the honest reading of §8 is that neither of its two clauses carries recognition
content: the law clause contributes one bit by generic algebra, and the profile
clause contributes a change of variables. -/

/-- **The chart alone forces the cost.** If any `G` is exactly quadratic in the
half-imbalance chart, then `G` is a multiple of the recognition cost in the log
chart. The hypothesis mentions no functional equation and no regularity; the proof
is the substitution `u = sinh (t / 2)`, which is available because
`u ↦ 2 arsinh u` inverts it.

This is the formal content of the panel's attack on §8: the profile clause is a
uniqueness theorem for `Jlog` disguised as a physical premise. -/
theorem chart_alone_forces_the_cost (G : ℝ → ℝ) (C : ℝ)
    (h : ∀ u : ℝ, G (2 * Real.arsinh u) = C * u ^ 2) :
    ∀ t : ℝ, G t = (C / 2) * Cost.Jlog t := by
  intro t
  have hinv : 2 * Real.arsinh (Real.sinh (t / 2)) = t := by
    rw [Real.arsinh_sinh]; ring
  have hG : G t = C * Real.sinh (t / 2) ^ 2 := by
    have hu := h (Real.sinh (t / 2))
    rwa [hinv] at hu
  have hJ : Cost.Jlog t = 2 * Real.sinh (t / 2) ^ 2 := by
    have hu := HKTKineticFromRecognitionCost.Jlog_two_arsinh (Real.sinh (t / 2))
    rwa [hinv] at hu
  rw [hG, hJ]
  ring

/-- The recognition cost is the `C = 2` member, which is the identity the profile
clause is built on. This is `HKTKineticFromRecognitionCost.Jlog_two_arsinh`, named
here so that `profile_clause_solution_set_is_a_scale_family` reads as an
equivalence rather than a one-way bound. -/
theorem Jlog_is_the_C_two_solution :
    ∀ u : ℝ, Cost.Jlog (2 * Real.arsinh u) = 2 * u ^ 2 :=
  HKTKineticFromRecognitionCost.Jlog_two_arsinh

/-- **The uniqueness in the profile clause is worth zero bits about recognition.**
The solution set of the clause is a one-parameter family of multiples of the cost,
so "only the recognition cost satisfies it" is a restatement of the clause and not
evidence for the cost. Compare `oscCost_not_quadratic_in_log_chart`, which is the
special case of this at one substituted function; the general statement makes it
clear that the special case was never going to fail. -/
theorem profile_clause_solution_set_is_a_scale_family (C : ℝ) :
    ∀ G : ℝ → ℝ, (∀ u : ℝ, G (2 * Real.arsinh u) = C * u ^ 2)
      ↔ (∀ t : ℝ, G t = (C / 2) * Cost.Jlog t) := by
  intro G
  constructor
  · exact chart_alone_forces_the_cost G C
  · intro hG u
    rw [hG, Jlog_is_the_C_two_solution u]
    ring

/-! ## §5. The scoped verdict -/

/-- **Track A verdict, as a single named proposition.**

Six facts. The conjunction is the honest statement of what §8's recognition
clause buys and what it does not.

1. The forcing is generic in the law's solution set, so `Cost.Jcost` is not used
   for it.
2. The solution set is strictly larger than `{Cost.Jcost}`: argument rescaling
   acts on it and moves `J`.
3. It also contains functions that are not costs, since the oscillatory branch
   takes the value `-2`.
4. Those non-costs force unit weight too, which is the O5 failure mode on this
   step.
5. Calibration is what collapses the power family to `J`, and §8 does not
   impose calibration.
6. But the oscillatory branch cannot be substituted into the profile clause,
   because it is bounded and so is not quadratic in any log chart.

Read together, and **corrected by §4b**: the composition law is load-bearing for
field-independence and buys it by algebra that no recognition primitive enters.
Fact 6 is true and nearly empty, because `chart_alone_forces_the_cost` shows the
profile clause has a one-parameter solution set consisting of multiples of the
cost, so *no* substitution into it could have succeeded. The first draft of this
verdict read fact 6 as recognition doing real work in the profile clause. It is not
work; the clause is a change of variables into the chart that inverts `J`, and the
chart is typed in rather than derived. Field-independence also needs the
model class's separate nonvanishing clause `∀ a b, W a b ≠ 0`, since the law alone
permits a field-dependent weight valued in `{0, 1}`.

So the corrected verdict is that neither clause of §8 carries recognition content,
and this proposition is retained with fact 6 relabelled rather than deleted, so
that the record shows what was claimed and what replaced it. -/
def constraint_sector_recognition_load_is_quadraticity_not_unit_weight : Prop :=
  (∀ (F : ℝ → ℝ) (w : ℝ), SatisfiesCompositionLaw F →
      SatisfiesCompositionLaw (fun x => w * F x) →
      ∀ {x y : ℝ}, 0 < x → 0 < y → F x * F y ≠ 0 → w = 0 ∨ w = 1)
  ∧ (∀ n : ℕ, SatisfiesCompositionLaw (powCost n)) ∧ powCost 2 ≠ Cost.Jcost
  ∧ (SatisfiesCompositionLaw (oscCost 1) ∧ oscCost 1 (Real.exp Real.pi) = -2)
  ∧ (∀ w : ℝ, SatisfiesCompositionLaw (fun x => w * oscCost 1 x) →
      w = 0 ∨ w = 1)
  ∧ (∀ n : ℕ, IsCalibrated (powCost n) ↔ n = 1)
  ∧ (¬ ∃ c : ℝ, ∀ t : ℝ, oscCost 1 (Real.exp t) = c * t ^ 2)

theorem constraint_sector_recognition_load_is_quadraticity_not_unit_weight_holds :
    constraint_sector_recognition_load_is_quadraticity_not_unit_weight :=
  ⟨fun F w hF hwF _ _ hx hy hne =>
      compositionLaw_forces_unit_weight_generic F w hF hwF hx hy hne,
   powCost_satisfiesCompositionLaw,
   powCost_two_ne_Jcost,
   ⟨oscCost_satisfiesCompositionLaw 1, oscCost_neg_at_exp_pi⟩,
   oscCost_forces_unit_weight,
   isCalibrated_powCost_iff,
   oscCost_not_quadratic_in_log_chart⟩

/-! ## §6. Axiom audit -/

section Audit

#print axioms compositionLaw_forces_unit_weight_generic
#print axioms compositionLaw_forces_unit_weight_is_an_instance
#print axioms satisfiesCompositionLaw_comp_pow
#print axioms powCost_satisfiesCompositionLaw
#print axioms powCost_two_ne_Jcost
#print axioms Jcost_pos_of_one_lt
#print axioms powCost_forces_unit_weight
#print axioms G_powCost
#print axioms deriv2_G_powCost
#print axioms isCalibrated_powCost_iff
#print axioms calibratedWeightAtTwo_forces_one
#print axioms rclWeight_zero
#print axioms not_calibratedWeightAtTwo_zero
#print axioms calibratedWeightAtTwo_ne_rclWeight
#print axioms falsifier_as_printed_is_met
#print axioms oscCost_satisfiesCompositionLaw
#print axioms oscCost_neg_at_exp_pi
#print axioms oscCost_forces_unit_weight
#print axioms oscCost_not_quadratic_in_log_chart
#print axioms chart_alone_forces_the_cost
#print axioms Jlog_is_the_C_two_solution
#print axioms profile_clause_solution_set_is_a_scale_family
#print axioms constraint_sector_recognition_load_is_quadraticity_not_unit_weight_holds

end Audit

end ConstraintSectorReparamAttack
end SevenGaps
end Gravity
end IndisputableMonolith
