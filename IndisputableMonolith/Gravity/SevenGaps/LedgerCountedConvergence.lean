import Mathlib

/-!
# The ledger-counted convergence organ (U15 attainment)

The unit-fugacity census reduced the Gap-2 measure question to one premise:
the physical weight is a stationary state of the ledger-counted recognition
dynamics (U15). UNIQUENESS of that state is banked in the census
(`equilibrium_forces_inverse_factorial`); what was missing is ATTAINMENT,
the theorem that the dynamics actually carries lawful initial data to the
stationary state rather than nature being assumed at equilibrium. This
module builds that organ.

## The object

The ledger-counted dynamics is the birth-death chain with size-blind birth
(one fresh posting available per tick) and per-label death (each of the
`x` posted labels can retire): birth rate `1`, death rate `x`. We take the
uniformized discrete-time chain truncated at level `n` (births from `n`
are clipped), with uniformization constant `c = n + 2`, so every row is a
genuine probability vector with positive holding mass. Transition entries
are defined as differences of a jump-tail function, so row sums telescope.

## The theorems

* `M_pow_hit_zero`: from every state the chain reaches state `0` within
  `n` steps with probability at least `(1/c)^n` (the descend-or-hold path).
  This is a Doeblin minorization with the empty ledger as the small set.
* `doeblin`: one `n`-step block contracts every zero-sum signed vector in
  total variation by the factor `1 - eps`, `eps = (1/c)^n`.
* `detailed_balance` / `piDist_stationary`: the inverse-factorial weight
  `1/x!` is reversible for the counted rates, hence stationary. The
  SELECTION is carried by the counted rates through this reversibility;
  the contraction machinery is rate-agnostic.
* `attainment`: from EVERY initial distribution, total-variation distance
  to the inverse-factorial distribution decays geometrically:
  `TV(mu * P^(n*k), pi) <= (1-eps)^k * TV(mu, pi)`, with `eps > 0` proved
  (`eps_pos`), so the gate actually fires.
* `attainment_tendsto`: the bound tends to zero.
* `stationary_unique`: any stationary distribution IS the
  inverse-factorial distribution (attainment applied at one block).
* Decoy scored (`uniform_not_stationary`): the uniform distribution is
  not stationary for the counted chain at any level `n >= 2`, so the
  organ discriminates: it is the counted death rate `x`, not the balance
  or contraction formalism, that selects the inverse factorial. The
  equal-per-slot decoy at the rate level is already scored in the census
  (`constantWeight_globalBalance_equalPerSlot`).

## Honest scope

The organ proves attainment at every truncation level `n`, with the SAME
selected weight (the inverse factorial, restricted and normalized) at
every level; the contraction constant degrades with `n`, and no claim is
made about the untruncated chain's convergence rate. What remains of U15
after this organ is the late-time identification (the physical weight is
the late-time state of the recognition dynamics) and the truncation
scoping; both are MODEL-tier statements named in the census, not here.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace LedgerCountedConvergence

open Finset

noncomputable section

variable (n : ℕ)

/-- Uniformization constant for truncation level `n`. -/
def c : ℝ := (n : ℝ) + 2

theorem c_pos : 0 < c n := by
  unfold c
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem c_ge_two : 2 ≤ c n := by
  unfold c
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem c_ne_zero : c n ≠ 0 := ne_of_gt (c_pos n)

/-- Birth probability from size `x`: one fresh posting per tick, clipped
at the truncation level. -/
def birth (x : ℕ) : ℝ := if x < n then 1 / c n else 0

theorem birth_nonneg (x : ℕ) : 0 ≤ birth n x := by
  unfold birth
  split
  · exact le_of_lt (div_pos one_pos (c_pos n))
  · exact le_refl 0

theorem birth_le (x : ℕ) : birth n x ≤ 1 / c n := by
  unfold birth
  split
  · exact le_refl _
  · exact le_of_lt (div_pos one_pos (c_pos n))

/-- The jump tail: probability of stepping to a state at least `y` from
state `x`. Entries of the chain are differences of this function, so row
sums telescope. -/
def tail (x y : ℕ) : ℝ :=
  if y + 1 ≤ x then 1
  else if y = x then 1 - (x : ℝ) / c n
  else if y = x + 1 then birth n x
  else 0

theorem tail_low (x y : ℕ) (h : y + 1 ≤ x) : tail n x y = 1 := by
  unfold tail
  rw [if_pos h]

theorem tail_self (x : ℕ) : tail n x x = 1 - (x : ℝ) / c n := by
  unfold tail
  have h1 : ¬ (x + 1 ≤ x) := by omega
  rw [if_neg h1, if_pos rfl]

theorem tail_succ_self (x : ℕ) : tail n x (x + 1) = birth n x := by
  unfold tail
  have h1 : ¬ (x + 1 + 1 ≤ x) := by omega
  have h2 : ¬ (x + 1 = x) := by omega
  rw [if_neg h1, if_neg h2, if_pos rfl]

theorem tail_high (x y : ℕ) (h : x + 2 ≤ y) : tail n x y = 0 := by
  unfold tail
  have h1 : ¬ (y + 1 ≤ x) := by omega
  have h2 : ¬ (y = x) := by omega
  have h3 : ¬ (y = x + 1) := by omega
  rw [if_neg h1, if_neg h2, if_neg h3]

theorem tail_zero (x : ℕ) : tail n x 0 = 1 := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    rw [tail_self]
    norm_num
  · exact tail_low n x 0 (by omega)

theorem tail_top (x : ℕ) (hx : x ≤ n) : tail n x (n + 1) = 0 := by
  rcases eq_or_lt_of_le hx with hxe | hxl
  · subst hxe
    rw [tail_succ_self]
    unfold birth
    rw [if_neg (lt_irrefl x)]
  · exact tail_high n x (n + 1) (by omega)

/-- One transition entry, as a tail difference. -/
def step (x y : ℕ) : ℝ := tail n x y - tail n x (y + 1)

theorem step_death (x : ℕ) (hx : 1 ≤ x) : step n x (x - 1) = (x : ℝ) / c n := by
  unfold step
  have h2 : x - 1 + 1 = x := by omega
  rw [tail_low n x (x - 1) (by omega), h2, tail_self]
  ring

theorem step_self (x : ℕ) : step n x x = 1 - (x : ℝ) / c n - birth n x := by
  unfold step
  rw [tail_self, tail_succ_self]

theorem step_birth (x : ℕ) : step n x (x + 1) = birth n x := by
  unfold step
  rw [tail_succ_self, tail_high n x (x + 1 + 1) (by omega)]
  ring

theorem step_far (x y : ℕ) (h : x + 2 ≤ y ∨ y + 2 ≤ x) : step n x y = 0 := by
  unfold step
  rcases h with h | h
  · rw [tail_high n x y h, tail_high n x (y + 1) (by omega)]
    ring
  · rw [tail_low n x y (by omega), tail_low n x (y + 1) (by omega)]
    ring

/-- The holding mass is at least `1/c` at every admissible state: this is
the descend-or-hold bound at the boundary. -/
theorem step_self_ge (x : ℕ) (hx : x ≤ n) : 1 / c n ≤ step n x x := by
  rw [step_self]
  have hb := birth_le n x
  have hc := c_pos n
  have hxn : (x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx
  have hxc : (x : ℝ) / c n ≤ (n : ℝ) / c n := by
    have h1 : (n : ℝ) / c n - (x : ℝ) / c n = ((n : ℝ) - (x : ℝ)) / c n :=
      (sub_div _ _ _).symm
    have h2 : 0 ≤ ((n : ℝ) - (x : ℝ)) / c n :=
      div_nonneg (by linarith) (le_of_lt hc)
    linarith
  have hone : (1 : ℝ) = ((n : ℝ) + 2) / c n := by
    rw [eq_div_iff (c_ne_zero n)]
    unfold c
    ring
  have hkey : 1 - (n : ℝ) / c n - 1 / c n = 1 / c n := by
    have hnum : ((n : ℝ) + 2) - (n : ℝ) - 1 = 1 := by ring
    calc 1 - (n : ℝ) / c n - 1 / c n
        = ((n : ℝ) + 2) / c n - (n : ℝ) / c n - 1 / c n := by rw [← hone]
      _ = (((n : ℝ) + 2) - (n : ℝ) - 1) / c n := by rw [← sub_div, ← sub_div]
      _ = 1 / c n := by rw [hnum]
  linarith

theorem step_nonneg (x y : ℕ) (hx : x ≤ n) : 0 ≤ step n x y := by
  have hc := c_pos n
  rcases lt_trichotomy y x with h | h | h
  · by_cases h1 : y + 1 = x
    · have hy : y = x - 1 := by omega
      rw [hy, step_death n x (by omega)]
      positivity
    · rw [step_far n x y (Or.inr (by omega))]
  · subst h
    have h1 := step_self_ge n y hx
    have h2 : 0 < 1 / c n := div_pos one_pos hc
    linarith
  · by_cases h1 : y = x + 1
    · rw [h1, step_birth]
      exact birth_nonneg n x
    · rw [step_far n x y (Or.inl (by omega))]

/-- The chain, as a matrix on the truncated state space. -/
def M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun x y => step n x.val y.val

theorem M_apply (x y : Fin (n + 1)) : M n x y = step n x.val y.val := rfl

theorem M_nonneg (x y : Fin (n + 1)) : 0 ≤ M n x y :=
  step_nonneg n x.val y.val (Nat.lt_succ_iff.mp x.isLt)

theorem M_row_sum (x : Fin (n + 1)) : ∑ y, M n x y = 1 := by
  have hx : x.val ≤ n := Nat.lt_succ_iff.mp x.isLt
  have h : ∑ y ∈ Finset.range (n + 1), step n x.val y = 1 := by
    unfold step
    rw [Finset.sum_range_sub' (fun y => tail n x.val y) (n + 1)]
    rw [tail_zero, tail_top n x.val hx]
    ring
  calc ∑ y, M n x y = ∑ y ∈ Finset.range (n + 1), step n x.val y := by
        rw [← Fin.sum_univ_eq_sum_range (fun y => step n x.val y) (n + 1)]
        rfl
    _ = 1 := h

/-! ## Generic facts about powers of a stochastic matrix -/

theorem pow_entry_nonneg (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : ∀ x y, 0 ≤ A x y) (k : ℕ) :
    ∀ x y, 0 ≤ (A ^ k) x y := by
  induction k with
  | zero =>
      intro x y
      rw [pow_zero]
      by_cases h : x = y <;> simp [Matrix.one_apply, h]
  | succ k ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hA z y)

theorem pow_row_sum (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : ∀ x, ∑ y, A x y = 1) (k : ℕ) :
    ∀ x, ∑ y, (A ^ k) x y = 1 := by
  induction k with
  | zero =>
      intro x
      rw [pow_zero]
      simp [Matrix.one_apply]
  | succ k ih =>
      intro x
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      have hz : ∀ z : Fin (n + 1), ∑ y, (A ^ k) x z * A z y = (A ^ k) x z := by
        intro z
        rw [← Finset.mul_sum, hA, mul_one]
      calc ∑ z, ∑ y, (A ^ k) x z * A z y = ∑ z, (A ^ k) x z :=
            Finset.sum_congr rfl fun z _ => hz z
        _ = 1 := ih x

/-! ## The Doeblin minorization: descend to the empty ledger -/

/-- One step down (clamped at zero). -/
def down (x : Fin (n + 1)) : Fin (n + 1) :=
  ⟨x.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩

/-- Every state moves one step down (or holds at zero) with probability at
least `1/c`. -/
theorem M_descend (x : Fin (n + 1)) : 1 / c n ≤ M n x (down n x) := by
  have hx : x.val ≤ n := Nat.lt_succ_iff.mp x.isLt
  rcases Nat.eq_zero_or_pos x.val with h0 | h1
  · have hd : (down n x).val = x.val := by
      unfold down
      simp [h0]
    rw [M_apply, hd, h0]
    exact step_self_ge n 0 (Nat.zero_le n)
  · have hd : (down n x).val = x.val - 1 := rfl
    rw [M_apply, hd, step_death n x.val h1]
    have hc := c_pos n
    gcongr
    exact_mod_cast h1

/-- **The minorization.** Within `k` steps the chain reaches the empty
ledger from any state of size at most `k`, with probability at least
`(1/c)^k`: the descend-or-hold path is always available. -/
theorem M_pow_hit_zero (k : ℕ) (x : Fin (n + 1)) (hx : x.val ≤ k) :
    (1 / c n) ^ k ≤ (M n ^ k) x 0 := by
  induction k generalizing x with
  | zero =>
      have hx0 : x = 0 := by
        apply Fin.ext
        simpa using hx
      subst hx0
      rw [pow_zero, pow_zero]
      simp
  | succ k ih =>
      have hterm : (1 / c n) * (1 / c n) ^ k ≤
          M n x (down n x) * (M n ^ k) (down n x) 0 := by
        apply mul_le_mul (M_descend n x)
        · exact ih (down n x) (by
            have : (down n x).val = x.val - 1 := rfl
            omega)
        · exact pow_nonneg (le_of_lt (div_pos one_pos (c_pos n))) k
        · exact le_trans (le_of_lt (div_pos one_pos (c_pos n))) (M_descend n x)
      calc (1 / c n) ^ (k + 1) = (1 / c n) * (1 / c n) ^ k := by
            rw [pow_succ']
        _ ≤ M n x (down n x) * (M n ^ k) (down n x) 0 := hterm
        _ ≤ ∑ z, M n x z * (M n ^ k) z 0 := by
            apply Finset.single_le_sum
              (f := fun z => M n x z * (M n ^ k) z 0)
            · intro z _
              exact mul_nonneg (M_nonneg n x z)
                (pow_entry_nonneg n (M n) (M_nonneg n) k z 0)
            · exact Finset.mem_univ (down n x)
        _ = (M n ^ (k + 1)) x 0 := by
            rw [pow_succ']
            rw [Matrix.mul_apply]

/-- The contraction constant. -/
def eps : ℝ := (1 / c n) ^ n

/-- **Gate: the contraction actually fires.** -/
theorem eps_pos : 0 < eps n := pow_pos (div_pos one_pos (c_pos n)) n

theorem eps_le_one : eps n ≤ 1 := by
  apply pow_le_one₀ (le_of_lt (div_pos one_pos (c_pos n)))
  rw [div_le_one (c_pos n)]
  linarith [c_ge_two n]

/-! ## The action of the chain on signed vectors -/

/-- Push a signed vector through a matrix (distribution evolution). -/
def act (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun y => ∑ x, v x * A x y

theorem act_one (v : Fin (n + 1) → ℝ) : act n 1 v = v := by
  funext y
  unfold act
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ y v]
  simp

theorem act_mul (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (v : Fin (n + 1) → ℝ) : act n (A * B) v = act n B (act n A v) := by
  funext y
  unfold act
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun x _ => ?_
  ring

theorem act_sum (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : ∀ x, ∑ y, A x y = 1) (v : Fin (n + 1) → ℝ) :
    ∑ y, act n A v y = ∑ x, v x := by
  unfold act
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, hA, mul_one]

/-! ## The Doeblin contraction -/

/-- **One block contracts.** An `n`-step block of the chain contracts
every zero-sum signed vector in total variation by `1 - eps`: split each
row of the block as `eps` times the point mass at the empty ledger plus a
nonnegative remainder with row sum `1 - eps`; the point-mass part
annihilates zero-sum vectors. -/
theorem doeblin (v : Fin (n + 1) → ℝ) (hv : ∑ x, v x = 0) :
    ∑ y, |act n (M n ^ n) v y| ≤ (1 - eps n) * ∑ x, |v x| := by
  classical
  have hApos : ∀ x y, 0 ≤ (M n ^ n) x y :=
    pow_entry_nonneg n (M n) (M_nonneg n) n
  have hArow : ∀ x, ∑ y, (M n ^ n) x y = 1 :=
    pow_row_sum n (M n) (M_row_sum n) n
  have hhit : ∀ x : Fin (n + 1), eps n ≤ (M n ^ n) x 0 := fun x =>
    M_pow_hit_zero n n x (Nat.lt_succ_iff.mp x.isLt)
  -- the remainder kernel
  have Qnn : ∀ x y : Fin (n + 1),
      0 ≤ (M n ^ n) x y - (if y = 0 then eps n else 0) := by
    intro x y
    by_cases h : y = 0
    · subst h
      rw [if_pos rfl]
      linarith [hhit x]
    · rw [if_neg h, sub_zero]
      exact hApos x y
  have Qrow : ∀ x : Fin (n + 1),
      ∑ y, ((M n ^ n) x y - (if y = 0 then eps n else 0)) = 1 - eps n := by
    intro x
    rw [Finset.sum_sub_distrib, hArow]
    congr 1
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (n + 1)) (fun _ => eps n)]
    simp
  have expand : ∀ y : Fin (n + 1),
      act n (M n ^ n) v y =
        ∑ x, v x * ((M n ^ n) x y - (if y = 0 then eps n else 0)) := by
    intro y
    have hsplit : ∑ x, v x * ((M n ^ n) x y - (if y = 0 then eps n else 0)) =
        (∑ x, v x * (M n ^ n) x y) -
          (∑ x, v x) * (if y = 0 then eps n else 0) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    rw [hsplit, hv, zero_mul, sub_zero]
    rfl
  calc ∑ y, |act n (M n ^ n) v y|
      = ∑ y, |∑ x, v x * ((M n ^ n) x y - (if y = 0 then eps n else 0))| := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [expand y]
    _ ≤ ∑ y, ∑ x, |v x| * ((M n ^ n) x y - (if y = 0 then eps n else 0)) := by
        refine Finset.sum_le_sum fun y _ => ?_
        calc |∑ x, v x * ((M n ^ n) x y - (if y = 0 then eps n else 0))|
            ≤ ∑ x, |v x * ((M n ^ n) x y - (if y = 0 then eps n else 0))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ x, |v x| * ((M n ^ n) x y - (if y = 0 then eps n else 0)) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [abs_mul, abs_of_nonneg (Qnn x y)]
    _ = ∑ x, |v x| * (1 - eps n) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.mul_sum, Qrow]
    _ = (1 - eps n) * ∑ x, |v x| := by
        rw [← Finset.sum_mul]
        ring

/-- Iterated blocks contract geometrically. -/
theorem contract_iter (v : Fin (n + 1) → ℝ) (hv : ∑ x, v x = 0) (k : ℕ) :
    ∑ y, |act n ((M n ^ n) ^ k) v y| ≤ (1 - eps n) ^ k * ∑ x, |v x| := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero, one_mul, act_one]
  | succ k ih =>
      rw [pow_succ, act_mul]
      have hurow : ∀ x, ∑ y, ((M n ^ n) ^ k) x y = 1 :=
        pow_row_sum n (M n ^ n) (pow_row_sum n (M n) (M_row_sum n) n) k
      have husum : ∑ x, act n ((M n ^ n) ^ k) v x = 0 := by
        rw [act_sum n ((M n ^ n) ^ k) hurow v, hv]
      have hd := doeblin n (act n ((M n ^ n) ^ k) v) husum
      have h1 : 0 ≤ 1 - eps n := by linarith [eps_le_one n]
      calc ∑ y, |act n (M n ^ n) (act n ((M n ^ n) ^ k) v) y|
          ≤ (1 - eps n) * ∑ x, |act n ((M n ^ n) ^ k) v x| := hd
        _ ≤ (1 - eps n) * ((1 - eps n) ^ k * ∑ x, |v x|) :=
            mul_le_mul_of_nonneg_left ih h1
        _ = (1 - eps n) ^ (k + 1) * ∑ x, |v x| := by ring

/-! ## The inverse-factorial stationary state -/

/-- The unnormalized weight: the census's inverse factorial. -/
def w (x : ℕ) : ℝ := 1 / (Nat.factorial x : ℝ)

theorem w_pos (x : ℕ) : 0 < w x := by
  unfold w
  have : (0 : ℝ) < (Nat.factorial x : ℝ) := by
    exact_mod_cast Nat.factorial_pos x
  positivity

/-- Detailed balance across an up edge: the counted rates carry the
selection. -/
theorem db_lt (a b : ℕ) (hab : a < b) (hb : b ≤ n) :
    w a * step n a b = w b * step n b a := by
  by_cases h1 : b = a + 1
  · subst h1
    have han : a < n := by omega
    have hbirth : step n a (a + 1) = 1 / c n := by
      rw [step_birth]
      unfold birth
      rw [if_pos han]
    have hdeath : step n (a + 1) a = ((a + 1 : ℕ) : ℝ) / c n := by
      have h2 : a = a + 1 - 1 := by omega
      calc step n (a + 1) a = step n (a + 1) (a + 1 - 1) := by rw [← h2]
        _ = ((a + 1 : ℕ) : ℝ) / c n := step_death n (a + 1) (by omega)
    rw [hbirth, hdeath]
    unfold w
    have hfa : ((Nat.factorial a : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos a).ne'
    have hfb : ((Nat.factorial (a + 1) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos (a + 1)).ne'
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  · have h2 : a + 2 ≤ b := by omega
    rw [step_far n a b (Or.inl h2), step_far n b a (Or.inr h2)]
    ring

/-- **Detailed balance (the counted selection).** The inverse-factorial
weight is reversible for the ledger-counted rates. -/
theorem detailed_balance (x y : Fin (n + 1)) :
    w x.val * M n x y = w y.val * M n y x := by
  have hx : x.val ≤ n := Nat.lt_succ_iff.mp x.isLt
  have hy : y.val ≤ n := Nat.lt_succ_iff.mp y.isLt
  rcases lt_trichotomy x.val y.val with h | h | h
  · exact db_lt n x.val y.val h hy
  · rw [M_apply, M_apply, h]
  · exact (db_lt n y.val x.val h hx).symm

/-- Reversibility gives stationarity of the unnormalized weight. -/
theorem w_stationary (y : Fin (n + 1)) :
    ∑ x, w x.val * M n x y = w y.val := by
  calc ∑ x, w x.val * M n x y = ∑ x, w y.val * M n y x :=
        Finset.sum_congr rfl fun x _ => detailed_balance n x y
    _ = w y.val * ∑ x, M n y x := by rw [Finset.mul_sum]
    _ = w y.val := by rw [M_row_sum, mul_one]

/-- The normalizer. -/
def Z : ℝ := ∑ x : Fin (n + 1), w x.val

theorem Z_pos : 0 < Z n :=
  Finset.sum_pos (fun x _ => w_pos x.val) Finset.univ_nonempty

theorem Z_ne_zero : Z n ≠ 0 := ne_of_gt (Z_pos n)

/-- The stationary distribution: the inverse factorial, normalized. -/
def piDist : Fin (n + 1) → ℝ := fun x => w x.val / Z n

theorem piDist_sum : ∑ x, piDist n x = 1 := by
  unfold piDist
  rw [← Finset.sum_div]
  exact div_self (Z_ne_zero n)

theorem piDist_stationary : act n (M n) (piDist n) = piDist n := by
  funext y
  unfold act piDist
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, w_stationary]

theorem piDist_act_pow (k : ℕ) : act n (M n ^ k) (piDist n) = piDist n := by
  induction k with
  | zero =>
      rw [pow_zero, act_one]
  | succ k ih =>
      rw [pow_succ, act_mul, ih, piDist_stationary]

/-! ## The attainment theorem -/

/-- **The attainment organ.** From EVERY initial distribution on the
truncated ledger-counted chain, the total-variation distance to the
inverse-factorial stationary distribution contracts geometrically in
`n`-step blocks, with the contraction constant `eps > 0` proved. The
equilibrium premise's attainment half is therefore a theorem: the
dynamics carries arbitrary lawful initial data to the census's selected
weight. -/
theorem attainment (μ : Fin (n + 1) → ℝ) (hsum : ∑ x, μ x = 1) (k : ℕ) :
    ∑ y, |act n ((M n ^ n) ^ k) μ y - piDist n y| ≤
      (1 - eps n) ^ k * ∑ x, |μ x - piDist n x| := by
  have hv : ∑ x, (μ x - piDist n x) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, piDist_sum]
    ring
  have hlin : ∀ y, act n ((M n ^ n) ^ k) μ y - piDist n y =
      act n ((M n ^ n) ^ k) (fun x => μ x - piDist n x) y := by
    intro y
    have hpi : act n ((M n ^ n) ^ k) (piDist n) y = piDist n y := by
      have h1 : (M n ^ n) ^ k = M n ^ (n * k) := by
        rw [pow_mul]
      rw [h1, piDist_act_pow n (n * k)]
    unfold act at *
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    rw [hpi]
  calc ∑ y, |act n ((M n ^ n) ^ k) μ y - piDist n y|
      = ∑ y, |act n ((M n ^ n) ^ k) (fun x => μ x - piDist n x) y| := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hlin y]
    _ ≤ (1 - eps n) ^ k * ∑ x, |μ x - piDist n x| :=
        contract_iter n (fun x => μ x - piDist n x) hv k

/-- The geometric bound tends to zero: attainment in the limit. -/
theorem attainment_tendsto (C : ℝ) :
    Filter.Tendsto (fun k => (1 - eps n) ^ k * C)
      Filter.atTop (nhds 0) := by
  have h1 : 0 ≤ 1 - eps n := by linarith [eps_le_one n]
  have h2 : 1 - eps n < 1 := by linarith [eps_pos n]
  have h3 := tendsto_pow_atTop_nhds_zero_of_lt_one h1 h2
  simpa using h3.mul_const C

/-- **Uniqueness from attainment.** Any stationary distribution of the
chain IS the inverse-factorial distribution: one contracted block forces
the total-variation distance to zero. -/
theorem stationary_unique (ν : Fin (n + 1) → ℝ) (hsum : ∑ x, ν x = 1)
    (hstat : act n (M n) ν = ν) : ν = piDist n := by
  have hpow : ∀ k, act n (M n ^ k) ν = ν := by
    intro k
    induction k with
    | zero => rw [pow_zero, act_one]
    | succ k ih => rw [pow_succ, act_mul, ih, hstat]
  have hv : ∑ x, (ν x - piDist n x) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, piDist_sum]
    ring
  have hlin : ∀ y, act n (M n ^ n) (fun x => ν x - piDist n x) y =
      ν y - piDist n y := by
    intro y
    have hν : act n (M n ^ n) ν y = ν y := by rw [hpow n]
    have hπ : act n (M n ^ n) (piDist n) y = piDist n y := by
      rw [piDist_act_pow n n]
    unfold act at *
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, hν, hπ]
  have hb := doeblin n (fun x => ν x - piDist n x) hv
  have hb' : ∑ y, |ν y - piDist n y| ≤
      (1 - eps n) * ∑ x, |ν x - piDist n x| := by
    calc ∑ y, |ν y - piDist n y|
        = ∑ y, |act n (M n ^ n) (fun x => ν x - piDist n x) y| := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hlin y]
      _ ≤ (1 - eps n) * ∑ x, |ν x - piDist n x| := hb
  have hDnn : 0 ≤ ∑ x, |ν x - piDist n x| :=
    Finset.sum_nonneg fun x _ => abs_nonneg _
  have hD0 : ∑ x, |ν x - piDist n x| = 0 := by
    nlinarith [eps_pos n]
  funext x
  have hle : |ν x - piDist n x| ≤ ∑ z, |ν z - piDist n z| :=
    Finset.single_le_sum (f := fun z => |ν z - piDist n z|)
      (fun z _ => abs_nonneg _) (Finset.mem_univ x)
  have : |ν x - piDist n x| = 0 := le_antisymm (by linarith) (abs_nonneg _)
  have := abs_eq_zero.mp this
  linarith

/-! ## Decoy scored: the organ discriminates -/

/-- **Decoy: the uniform distribution is not stationary** for the counted
chain at any level `n >= 2`. The contraction and balance formalism is
rate-agnostic; it is the counted death rate (each posted label can
retire) that selects the inverse factorial and rejects the uniform
weight. -/
theorem uniform_not_stationary (hn : 2 ≤ n) :
    ¬ act n (M n) (fun _ => 1 / ((n : ℝ) + 1)) =
      (fun _ => 1 / ((n : ℝ) + 1)) := by
  intro hstat
  have hsum : ∑ _x : Fin (n + 1), (1 / ((n : ℝ) + 1)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  have huni := stationary_unique n _ hsum hstat
  have h0 := congrFun huni ⟨0, by omega⟩
  have h2 := congrFun huni ⟨2, by omega⟩
  have hw0 : w 0 = 1 := by
    unfold w
    simp [Nat.factorial]
  have hw2 : w 2 = 1 / 2 := by
    unfold w
    norm_num [Nat.factorial]
  unfold piDist at h0 h2
  simp only at h0 h2
  rw [hw0] at h0
  rw [hw2] at h2
  have hZ := Z_ne_zero n
  have : (1 : ℝ) / Z n = (1 / 2) / Z n := by
    rw [← h0, ← h2]
  have h12 : (1 : ℝ) = 1 / 2 := by
    field_simp at this
    linarith
  norm_num at h12

end

#print axioms M_row_sum
#print axioms M_pow_hit_zero
#print axioms eps_pos
#print axioms doeblin
#print axioms contract_iter
#print axioms detailed_balance
#print axioms piDist_stationary
#print axioms attainment
#print axioms attainment_tendsto
#print axioms stationary_unique
#print axioms uniform_not_stationary

end LedgerCountedConvergence
end SevenGaps
end Gravity
end IndisputableMonolith
