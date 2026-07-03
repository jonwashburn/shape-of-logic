/-
  PrimitiveRecognitionCalculus/OrbitEuclidean.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchors:
    Build Order step 3: Euclidean quotient/remainder, GCD, coprime, and
    rational normalization targets.

  Strength: δ-only for definitions. Nat division, modulo, and gcd appear only
  in verifier transport theorems.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.OrbitDivisibility

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace DistinctionNat

/-! ## Object-level quotient and remainder by repeated subtraction -/

/-- Fuelled quotient/remainder by repeated subtraction. The first argument is
an orbit fuel, not verifier `Nat`. -/
def divModFuel : DistinctionNat → DistinctionNat → DistinctionNat → DistinctionNat × DistinctionNat
  | zero, n, _ => (zero, n)
  | succ fuel, n, d =>
      if DistinctionNat.leq d n then
        let qr := divModFuel fuel (DistinctionNat.truncatedSub n d) d
        (succ qr.1, qr.2)
      else
        (zero, n)

/-- Euclidean quotient/remainder. The fuel `n` is enough when `d` is nonzero,
because each successful subtraction lowers the dividend by at least one. -/
def divMod (n d : DistinctionNat) (_hd : d ≠ zero) : DistinctionNat × DistinctionNat :=
  divModFuel n n d

/-- Object-level quotient. -/
def quotient (n d : DistinctionNat) (hd : d ≠ zero) : DistinctionNat :=
  (divMod n d hd).1

/-- Object-level remainder. -/
def remainder (n d : DistinctionNat) (hd : d ≠ zero) : DistinctionNat :=
  (divMod n d hd).2

private theorem divModFuel_toNat_aux (fuel n d : DistinctionNat)
    (hd : d.toNat ≠ 0)
    (hbound : n.toNat ≤ fuel.toNat) :
    let qr := divModFuel fuel n d
    qr.1.toNat = n.toNat / d.toNat ∧
      qr.2.toNat = n.toNat % d.toNat := by
  induction fuel generalizing n with
  | zero =>
      rw [toNat_zero] at hbound
      have hn0 : n.toNat = 0 := by omega
      simp [divModFuel, hn0]
  | succ fuel ih =>
      rw [toNat_succ] at hbound
      unfold divModFuel
      by_cases hleq : DistinctionNat.leq d n = true
      · have hle : d.toNat ≤ n.toNat :=
          (DistinctionNat.leq_eq_true_iff d n).mp hleq
        have hpos : 0 < d.toNat := by omega
        simp [hleq]
        have hbound' : (DistinctionNat.truncatedSub n d).toNat ≤ fuel.toNat := by
          rw [DistinctionNat.toNat_truncatedSub]
          omega
        have ih' := ih (DistinctionNat.truncatedSub n d) hbound'
        rcases ih' with ⟨hq, hr⟩
        rw [hq, hr]
        constructor
        · rw [DistinctionNat.toNat_truncatedSub, Nat.div_eq_sub_div hpos hle]
        · rw [DistinctionNat.toNat_truncatedSub]
          exact (Nat.mod_eq_sub_mod hle).symm
      · have hlt : n.toNat < d.toNat := by
          have hf := (DistinctionNat.leq_eq_false_iff d n).mp (by
            cases h : DistinctionNat.leq d n with
            | false => rfl
            | true =>
                exfalso
                exact hleq h)
          exact hf
        simp [hleq]
        constructor
        · exact (Nat.div_eq_of_lt hlt).symm
        · exact (Nat.mod_eq_of_lt hlt).symm

/-- Euclidean quotient/remainder transports to verifier Nat division and
modulus. -/
theorem divMod_toNat (n d : DistinctionNat) (hd : d ≠ zero) :
    let qr := divMod n d hd
    qr.1.toNat = n.toNat / d.toNat ∧
      qr.2.toNat = n.toNat % d.toNat := by
  unfold divMod
  apply divModFuel_toNat_aux
  · intro hzero
    have : d = zero := by
      apply toNat_inj
      rw [hzero, toNat_zero]
    exact hd this
  · omega

theorem quotient_toNat (n d : DistinctionNat) (hd : d ≠ zero) :
    (quotient n d hd).toNat = n.toNat / d.toNat := by
  have h := divMod_toNat n d hd
  exact h.1

theorem remainder_toNat (n d : DistinctionNat) (hd : d ≠ zero) :
    (remainder n d hd).toNat = n.toNat % d.toNat := by
  have h := divMod_toNat n d hd
  exact h.2

theorem remainder_lt_divisor (n d : DistinctionNat) (hd : d ≠ zero) :
    (remainder n d hd).toNat < d.toNat := by
  rw [remainder_toNat]
  apply Nat.mod_lt
  exact Nat.pos_of_ne_zero (by
    intro hzero
    have : d = zero := by
      apply toNat_inj
      rw [hzero, toNat_zero]
    exact hd this)

/-- The quotient and remainder reconstruct the dividend in orbit arithmetic. -/
theorem quotient_mul_divisor_add_remainder_eq
    (n d : DistinctionNat) (hd : d ≠ zero) :
    quotient n d hd * d + remainder n d hd = n := by
  apply toNat_inj
  rw [toNat_add, toNat_mul, quotient_toNat, remainder_toNat]
  rw [Nat.mul_comm (n.toNat / d.toNat) d.toNat]
  exact Nat.div_add_mod n.toNat d.toNat

/-! ## Object-level GCD by subtractive Euclidean descent -/

/-- Fuelled subtractive Euclidean GCD. -/
def gcdFuel : DistinctionNat → DistinctionNat → DistinctionNat → DistinctionNat
  | zero, a, b => a + b
  | succ fuel, a, b =>
      if a = zero then
        b
      else if b = zero then
        a
      else if DistinctionNat.leq b a then
        gcdFuel fuel (DistinctionNat.truncatedSub a b) b
      else
        gcdFuel fuel a (DistinctionNat.truncatedSub b a)

/-- Object-level GCD by subtractive Euclidean descent. -/
def gcd (a b : DistinctionNat) : DistinctionNat :=
  gcdFuel (a + b) a b

/-- Object-level coprimality. -/
def coprime (a b : DistinctionNat) : Prop :=
  unit (gcd a b)

private theorem gcdFuel_toNat_aux (fuel a b : DistinctionNat)
    (hbound : a.toNat + b.toNat ≤ fuel.toNat) :
    (gcdFuel fuel a b).toNat = Nat.gcd a.toNat b.toNat := by
  induction fuel generalizing a b with
  | zero =>
      rw [toNat_zero] at hbound
      have ha0 : a.toNat = 0 := by omega
      have hb0 : b.toNat = 0 := by omega
      simp [gcdFuel, ha0, hb0, toNat_add]
  | succ fuel ih =>
      rw [toNat_succ] at hbound
      unfold gcdFuel
      by_cases ha : a = zero
      · simp [ha, Nat.gcd_zero_left]
      · by_cases hb : b = zero
        · simp [ha, hb, Nat.gcd_zero_right]
        · by_cases hleq : DistinctionNat.leq b a = true
          · have hle : b.toNat ≤ a.toNat :=
              (DistinctionNat.leq_eq_true_iff b a).mp hleq
            have hbpos : 0 < b.toNat := by
              have hbne : b.toNat ≠ 0 := by
                intro hzero
                have : b = zero := by
                  apply toNat_inj
                  rw [hzero, toNat_zero]
                exact hb this
              omega
            have hbound' :
                (DistinctionNat.truncatedSub a b).toNat + b.toNat ≤ fuel.toNat := by
              rw [DistinctionNat.toNat_truncatedSub]
              omega
            simp [ha, hb, hleq]
            rw [ih (DistinctionNat.truncatedSub a b) b hbound']
            rw [DistinctionNat.toNat_truncatedSub]
            exact Nat.gcd_sub_self_left hle
          · have hlt : a.toNat < b.toNat := by
              exact (DistinctionNat.leq_eq_false_iff b a).mp (by
                cases h : DistinctionNat.leq b a with
                | false => rfl
                | true =>
                    exfalso
                    exact hleq h)
            have hle : a.toNat ≤ b.toNat := by omega
            have hapos : 0 < a.toNat := by
              have hane : a.toNat ≠ 0 := by
                intro hzero
                have : a = zero := by
                  apply toNat_inj
                  rw [hzero, toNat_zero]
                exact ha this
              omega
            have hbound' :
                a.toNat + (DistinctionNat.truncatedSub b a).toNat ≤ fuel.toNat := by
              rw [DistinctionNat.toNat_truncatedSub]
              omega
            simp [ha, hb, hleq]
            rw [ih a (DistinctionNat.truncatedSub b a) hbound']
            rw [DistinctionNat.toNat_truncatedSub]
            exact Nat.gcd_sub_self_right hle

theorem gcd_toNat (a b : DistinctionNat) :
    (gcd a b).toNat = Nat.gcd a.toNat b.toNat := by
  unfold gcd
  apply gcdFuel_toNat_aux
  rw [toNat_add]

theorem coprime_iff_nat_coprime (a b : DistinctionNat) :
    coprime a b ↔ Nat.Coprime a.toNat b.toNat := by
  simp [coprime, gcd_toNat, unit_iff_toNat_eq_one]

/-- The native GCD divides the left input. -/
theorem gcd_divides_left (a b : DistinctionNat) :
    divides (gcd a b) a := by
  rw [divides_iff_toNat_dvd, gcd_toNat]
  exact Nat.gcd_dvd_left a.toNat b.toNat

/-- The native GCD divides the right input. -/
theorem gcd_divides_right (a b : DistinctionNat) :
    divides (gcd a b) b := by
  rw [divides_iff_toNat_dvd, gcd_toNat]
  exact Nat.gcd_dvd_right a.toNat b.toNat

/-- Any common native divisor divides the native GCD. -/
theorem divides_gcd_of_divides_left_right {c a b : DistinctionNat}
    (hca : divides c a) (hcb : divides c b) :
    divides c (gcd a b) := by
  rw [divides_iff_toNat_dvd, gcd_toNat]
  exact Nat.dvd_gcd
    ((divides_iff_toNat_dvd c a).mp hca)
    ((divides_iff_toNat_dvd c b).mp hcb)

/-! ## Coprime divisor cancellation -/

/-- If `a` is coprime to `b` and divides `b*c`, then `a` divides `c`.
The argument is native at the statement level; Nat appears only in transport. -/
theorem coprime_divides_of_divides_mul_left {a b c : DistinctionNat}
    (hcop : coprime b a) (hdiv : divides a (b * c)) :
    divides a c := by
  rw [divides_iff_toNat_dvd] at hdiv ⊢
  rw [toNat_mul] at hdiv
  have hcopNat : Nat.Coprime b.toNat a.toNat :=
    (coprime_iff_nat_coprime b a).mp hcop
  exact hcopNat.symm.dvd_of_dvd_mul_left hdiv

theorem gcd_ne_zero_of_right_ne_zero (a b : DistinctionNat) (hb : b ≠ zero) :
    gcd a b ≠ zero := by
  intro h
  have hnat : (gcd a b).toNat = 0 := by
    rw [h, toNat_zero]
  rw [gcd_toNat] at hnat
  have hb0 : b.toNat = 0 := (Nat.gcd_eq_zero_iff.mp hnat).2
  apply hb
  apply toNat_inj
  rw [hb0, toNat_zero]

theorem quotient_mul_divisor_toNat_of_divides {n d : DistinctionNat}
    (hd : d ≠ zero) (hdiv : divides d n) :
    (quotient n d hd).toNat * d.toNat = n.toNat := by
  rw [quotient_toNat]
  exact Nat.div_mul_cancel ((divides_iff_toNat_dvd d n).mp hdiv)

theorem quotient_ne_zero_of_divides {n d : DistinctionNat}
    (hd : d ≠ zero) (hdiv : divides d n) (hn : n ≠ zero) :
    quotient n d hd ≠ zero := by
  intro hq
  have hqnat : (quotient n d hd).toNat = 0 := by
    rw [hq, toNat_zero]
  have hmul := quotient_mul_divisor_toNat_of_divides (n := n) (d := d) hd hdiv
  rw [hqnat, Nat.zero_mul] at hmul
  apply hn
  apply toNat_inj
  rw [hmul.symm, toNat_zero]

/-! ## Signed rational normalization by native orbit GCD -/

/-- Quotient a signed orbit by a nonzero orbit position, restoring the sign by
the structural signed-orbit comparison. -/
def signedQuotient (z : SignedOrbit) (d : DistinctionNat) (hd : d ≠ zero) :
    SignedOrbit :=
  let q := quotient z.abs d hd
  if z.nonnegFlag then
    SignedOrbit.ofOrbit q
  else
    SignedOrbit.negate (SignedOrbit.ofOrbit q)

theorem signedQuotient_abs_toNat (z : SignedOrbit)
    (d : DistinctionNat) (hd : d ≠ zero) :
    (signedQuotient z d hd).abs.toNat = z.abs.toNat / d.toNat := by
  unfold signedQuotient
  by_cases hflag : z.nonnegFlag = true
  · have hAbsQ :
        (SignedOrbit.ofOrbit (quotient z.abs d hd)).abs.toNat =
          (quotient z.abs d hd).toNat := by
      simp [SignedOrbit.abs_toNat, SignedOrbit.ofOrbit_toInt]
    simpa [hflag, hAbsQ] using quotient_toNat z.abs d hd
  · have hflagFalse : z.nonnegFlag = false := by
      cases h : z.nonnegFlag with
      | false => rfl
      | true =>
          exfalso
          exact hflag h
    have hAbsQ :
        (SignedOrbit.negate (SignedOrbit.ofOrbit (quotient z.abs d hd))).abs.toNat =
          (quotient z.abs d hd).toNat := by
      simp [SignedOrbit.abs_toNat, SignedOrbit.ofOrbit_toInt,
        SignedOrbit.negate_toInt]
    simpa [hflagFalse, hAbsQ] using quotient_toNat z.abs d hd

theorem signedQuotient_mul_divisor_toInt_of_divides
    (z : SignedOrbit) (d : DistinctionNat) (hd : d ≠ zero)
    (hdiv : divides d z.abs) :
    (signedQuotient z d hd).toInt * (d.toNat : ℤ) = z.toInt := by
  have hquotNat :
      (quotient z.abs d hd).toNat * d.toNat = z.abs.toNat :=
    quotient_mul_divisor_toNat_of_divides (n := z.abs) (d := d) hd hdiv
  have hquotInt :
      ((quotient z.abs d hd).toNat : ℤ) * (d.toNat : ℤ) =
        (z.abs.toNat : ℤ) := by
    exact_mod_cast hquotNat
  unfold signedQuotient
  by_cases hflag : z.nonnegFlag = true
  · have hnonneg : 0 ≤ z.toInt :=
      (SignedOrbit.nonnegFlag_eq_true_iff z).mp hflag
    have habs : (z.abs.toNat : ℤ) = z.toInt := by
      rw [SignedOrbit.abs_toNat]
      exact Int.ofNat_natAbs_of_nonneg hnonneg
    simp [hflag, SignedOrbit.ofOrbit_toInt]
    rw [hquotInt, habs]
  · have hflagFalse : z.nonnegFlag = false := by
      cases h : z.nonnegFlag with
      | false => rfl
      | true =>
          exfalso
          exact hflag h
    have hneg : z.toInt < 0 :=
      (SignedOrbit.nonnegFlag_eq_false_iff z).mp hflagFalse
    have habs : (z.abs.toNat : ℤ) = -z.toInt := by
      rw [SignedOrbit.abs_toNat]
      exact Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)
    simp [hflagFalse, SignedOrbit.ofOrbit_toInt, SignedOrbit.negate_toInt]
    rw [hquotInt, habs]
    ring

/-- Normalize a ratio orbit by dividing numerator magnitude and denominator by
their native orbit GCD. The signed numerator orientation is restored by
`SignedOrbit.nonnegFlag`. -/
def normalizeRatio (q : RatioOrbit) : RatioOrbit :=
  let g := gcd q.num.abs q.den
  have hg : g ≠ zero := gcd_ne_zero_of_right_ne_zero q.num.abs q.den q.den_ne_zero
  {
    num := signedQuotient q.num g hg
    den := quotient q.den g hg
    den_ne_zero :=
      quotient_ne_zero_of_divides
        (n := q.den) (d := g) hg
        (gcd_divides_right q.num.abs q.den)
        q.den_ne_zero
  }

theorem normalizeRatio_num_mul_gcd_toInt (q : RatioOrbit) :
    (normalizeRatio q).num.toInt *
      ((gcd q.num.abs q.den).toNat : ℤ) = q.num.toInt := by
  unfold normalizeRatio
  exact signedQuotient_mul_divisor_toInt_of_divides
    q.num (gcd q.num.abs q.den)
    (gcd_ne_zero_of_right_ne_zero q.num.abs q.den q.den_ne_zero)
    (gcd_divides_left q.num.abs q.den)

theorem normalizeRatio_den_mul_gcd_toNat (q : RatioOrbit) :
    (normalizeRatio q).den.toNat *
      (gcd q.num.abs q.den).toNat = q.den.toNat := by
  unfold normalizeRatio
  exact quotient_mul_divisor_toNat_of_divides
    (n := q.den) (d := gcd q.num.abs q.den)
    (gcd_ne_zero_of_right_ne_zero q.num.abs q.den q.den_ne_zero)
    (gcd_divides_right q.num.abs q.den)

theorem normalizeRatio_toRat (q : RatioOrbit) :
    (normalizeRatio q).toRat = q.toRat := by
  unfold RatioOrbit.toRat
  have hnumZ := normalizeRatio_num_mul_gcd_toInt q
  have hdenN := normalizeRatio_den_mul_gcd_toNat q
  have hnumQ :
      ((normalizeRatio q).num.toInt : ℚ) *
        ((gcd q.num.abs q.den).toNat : ℚ) =
          (q.num.toInt : ℚ) := by
    exact_mod_cast hnumZ
  have hdenQ :
      ((normalizeRatio q).den.toNat : ℚ) *
        ((gcd q.num.abs q.den).toNat : ℚ) =
          (q.den.toNat : ℚ) := by
    exact_mod_cast hdenN
  have hNormDen : ((normalizeRatio q).den.toNat : ℚ) ≠ 0 :=
    (normalizeRatio q).den_cast_ne_zero
  have hDen : (q.den.toNat : ℚ) ≠ 0 := q.den_cast_ne_zero
  field_simp [hNormDen, hDen]
  calc
    ((normalizeRatio q).num.toInt : ℚ) * (q.den.toNat : ℚ)
        = ((normalizeRatio q).num.toInt : ℚ) *
            (((normalizeRatio q).den.toNat : ℚ) *
              ((gcd q.num.abs q.den).toNat : ℚ)) := by
          rw [hdenQ]
    _ = (((normalizeRatio q).num.toInt : ℚ) *
            ((gcd q.num.abs q.den).toNat : ℚ)) *
            ((normalizeRatio q).den.toNat : ℚ) := by ring
    _ = (q.num.toInt : ℚ) * ((normalizeRatio q).den.toNat : ℚ) := by
          rw [hnumQ]
    _ = ((normalizeRatio q).den.toNat : ℚ) * (q.num.toInt : ℚ) := by ring

theorem normalizeRatio_crossEq (q : RatioOrbit) :
    RatioOrbit.crossEq q (normalizeRatio q) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq]
  exact (normalizeRatio_toRat q).symm

theorem normalizeRatio_coprime (q : RatioOrbit) :
    coprime (normalizeRatio q).num.abs (normalizeRatio q).den := by
  rw [coprime_iff_nat_coprime]
  unfold normalizeRatio
  rw [signedQuotient_abs_toNat, quotient_toNat]
  have hgpos : 0 < (gcd q.num.abs q.den).toNat := by
    rw [gcd_toNat]
    apply Nat.gcd_pos_of_pos_right
    exact Nat.pos_of_ne_zero (by
      intro hzero
      apply q.den_ne_zero
      apply toNat_inj
      rw [hzero, toNat_zero])
  have hgposNat : 0 < Nat.gcd q.num.abs.toNat q.den.toNat := by
    rw [← gcd_toNat]
    exact hgpos
  rw [gcd_toNat]
  exact Nat.coprime_div_gcd_div_gcd
    (m := q.num.abs.toNat) (n := q.den.toNat) hgposNat

/-- After signed division by orbit GCD, every `RatioOrbit` admits a balanced
equivalent representative whose numerator absolute value is coprime to the
denominator. -/
def RatioNormalizationTarget : Prop :=
  ∀ q : RatioOrbit,
    ∃ q' : RatioOrbit,
      RatioOrbit.crossEq q q' ∧
      coprime q'.num.abs q'.den

theorem ratio_normalization_target : RatioNormalizationTarget := by
  intro q
  exact ⟨normalizeRatio q, normalizeRatio_crossEq q, normalizeRatio_coprime q⟩

/-- Bundling certificate for the Euclidean orbit surface closed in this pass. -/
structure OrbitEuclideanCertificate : Prop where
  divmod_display :
    ∀ (n d : DistinctionNat) (hd : d ≠ zero),
      let qr := divMod n d hd
      qr.1.toNat = n.toNat / d.toNat ∧
        qr.2.toNat = n.toNat % d.toNat
  quotient_display :
    ∀ (n d : DistinctionNat) (hd : d ≠ zero),
      (quotient n d hd).toNat = n.toNat / d.toNat
  remainder_display :
    ∀ (n d : DistinctionNat) (hd : d ≠ zero),
      (remainder n d hd).toNat = n.toNat % d.toNat
  remainder_bound :
    ∀ (n d : DistinctionNat) (hd : d ≠ zero),
      (remainder n d hd).toNat < d.toNat
  quotient_remainder_decomposition :
    ∀ (n d : DistinctionNat) (hd : d ≠ zero),
      quotient n d hd * d + remainder n d hd = n
  gcd_display :
    ∀ a b : DistinctionNat, (gcd a b).toNat = Nat.gcd a.toNat b.toNat
  coprime_display :
    ∀ a b : DistinctionNat, coprime a b ↔ Nat.Coprime a.toNat b.toNat
  gcd_greatest_divisor :
    ∀ {c a b : DistinctionNat}, divides c a → divides c b → divides c (gcd a b)
  coprime_divisor_cancellation :
    ∀ {a b c : DistinctionNat}, coprime b a → divides a (b * c) → divides a c
  ratio_normalization :
    RatioNormalizationTarget

/-- The closed δ-only Euclidean orbit surface, including signed-rational
normalization by native orbit GCD. -/
theorem orbit_euclidean_certificate : OrbitEuclideanCertificate where
  divmod_display := divMod_toNat
  quotient_display := quotient_toNat
  remainder_display := remainder_toNat
  remainder_bound := remainder_lt_divisor
  quotient_remainder_decomposition := quotient_mul_divisor_add_remainder_eq
  gcd_display := gcd_toNat
  coprime_display := coprime_iff_nat_coprime
  gcd_greatest_divisor := by
    intro c a b hca hcb
    exact divides_gcd_of_divides_left_right hca hcb
  coprime_divisor_cancellation := by
    intro a b c hcop hdiv
    exact coprime_divides_of_divides_mul_left hcop hdiv
  ratio_normalization := ratio_normalization_target

end DistinctionNat
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
