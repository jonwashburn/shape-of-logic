import Mathlib

namespace IndisputableMonolith
namespace URCGenerators
namespace Numeric

/-! Minimal numeric helpers for rational formatting (pure, computable). -/
namespace NumFmt

def pow10 (d : Nat) : Nat := Nat.pow 10 d

def padLeftZeros (s : String) (len : Nat) : String :=
  let deficit := if s.length ≥ len then 0 else len - s.length
  let rec mkZeros (n : Nat) (acc : String) : String :=
    match n with
    | 0 => acc
    | n+1 => mkZeros n ("0" ++ acc)
  mkZeros deficit s

/-- Render a rational q = n / m to a fixed d-decimal string. -/
def ratToDecimal (n : Int) (m : Nat) (d : Nat) : String :=
  let sign := if n < 0 then "-" else ""
  let nAbs : Nat := Int.natAbs n
  if m = 0 then sign ++ "NaN" else
  let scale := pow10 d
  let scaled : Nat := (nAbs * scale) / m
  let ip : Nat := scaled / scale
  let fp : Nat := scaled % scale
  let fpStr := padLeftZeros (toString fp) d
  sign ++ toString ip ++ (if d = 0 then "" else "." ++ fpStr)

end NumFmt

/-- Compute φ^k as a fixed-decimal string using a high-precision rational φ.
    Supports negative exponents by inversion. Deterministic and computable. -/
def phiPowValueStr (k : Int) (digits : Nat := 12) : String :=
  -- φ as a rational
  -- Use Source.txt canonical value φ ≈ 1.6180339887498948 with 16 fractional digits
  -- to reduce rounding error in comparator checks on φ^Δr ratios.
  let φ_num : Int := 16180339887498948
  let φ_den : Nat := 10000000000000000
  -- integer power helper for Int and Nat
  let rec powInt (a : Int) (n : Nat) : Int :=
    match n with
    | 0 => 1
    | n+1 => (powInt a n) * a
  let rec powNat (a : Nat) (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | n+1 => (powNat a n) * a
  -- assemble numerator/denominator for φ^k
  let (num, den) : (Int × Nat) :=
    if k ≥ 0 then
      let kk : Nat := Int.toNat k
      (powInt φ_num kk, powNat φ_den kk)
    else
      let kk : Nat := Int.toNat (-k)
      -- invert: (φ_den^kk) / (φ_num^kk)
      ((powNat φ_den kk : Nat) |> fun n => (n : Int), (powInt φ_num kk).natAbs)
  NumFmt.ratToDecimal num den digits

/-- φ-only curvature pipeline evaluator (deterministic, computable):
    α^{-1} ≈ 4π·11 − (w8·ln φ + δ_κ),
    with π ≈ 104348/33215, φ ≈ 161803399/100000000,
    w8 = 2.488254397846 ≈ 2488254397846 / 10^12,
    δ_κ = −103/(102·π^5). Emits 12-decimal string. -/
def alphaInvValueStr : String :=
  -- π and φ rationals
  let π_num : Int := 104348
  let π_den : Nat := 33215
  let φ_num : Int := 161803399
  let φ_den : Nat := 100000000
  -- y = 1/φ = φ_den / φ_num
  let y_num : Int := φ_den
  let y_den : Nat := φ_num.natAbs
  -- ln(1 + y) via alternating series up to N terms
  let N : Nat := 80
  -- Rational helpers
  let addR (aN : Int) (aD : Nat) (bN : Int) (bD : Nat) : (Int × Nat) :=
    (aN * bD + bN * (aD : Int), aD * bD)
  let negR (aN : Int) (aD : Nat) : (Int × Nat) := (-aN, aD)
  let mulR (aN : Int) (aD : Nat) (bN : Int) (bD : Nat) : (Int × Nat) :=
    (aN * bN, aD * bD)
  -- y^k / k
  let rec pow (baseN : Int) (baseD : Nat) (k : Nat) : (Int × Nat) :=
    match k with
    | 0 => (1, 1)
    | k+1 =>
      let (pn, pd) := pow baseN baseD k
      mulR pn pd baseN baseD
  let rec ln1p (k : Nat) (accN : Int) (accD : Nat) : (Int × Nat) :=
    if k = 0 then (accN, accD) else
      let (ykN, ykD) := pow y_num y_den k
      let termN : Int := ykN
      let termD : Nat := ykD * k
      let (termN, termD) := if k % 2 = 1 then (termN, termD) else negR termN termD
      let (n2, d2) := addR accN accD termN termD
      ln1p (k - 1) n2 d2
  let (lnφN, lnφD) := ln1p N 0 1
  -- f_gap = w8 * ln φ with w8 ≈ 2.488254397846 ≈ 2488254397846 / 10^12
  let w8N : Int := 2488254397846
  let w8D : Nat := 1000000000000
  let (gapN, gapD) := mulR lnφN lnφD w8N w8D
  -- δκ = -103 / (102 * π^5)
  let π5N : Int := π_num ^ 5
  let π5D : Nat := π_den ^ 5
  let δκN : Int := -103 * (π5D : Int)
  let δκD : Nat := 102 * π5N.natAbs
  -- f_gap + δκ
  let (sumN, sumD) := addR gapN gapD δκN δκD
  -- 4 * π * 11 = 44 * π
  let aN : Int := 44 * π_num
  let aD : Nat := π_den
  -- α^{-1} = 44π - (f_gap + δκ)
  let (negSumN, negSumD) := negR sumN sumD
  let (resN, resD) := addR aN aD negSumN negSumD
  NumFmt.ratToDecimal resN resD 12

end Numeric
end URCGenerators
end IndisputableMonolith
