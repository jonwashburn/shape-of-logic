import Mathlib
import IndisputableMonolith.Masses.L1b2SignKernelExclusion

/-!
# L1b3 Q3 Flag Carrier

Finite B3 signed-permutation carrier for the charged-lepton L1b bridge.

This file intentionally closes only the carrier/action/projector algebra:
* `Q3Flag = Equiv.Perm (Fin 3) × (Fin 3 → Bool)`;
* cardinality `48`;
* genuine signed-permutation composition/action;
* principal transitivity / unique transporter;
* Reynolds average equals the uniform Reynolds projector;
* flip-parity tau-odd sign kernel is excluded by entrywise CPM nonnegativity.

It does not close L1b or L1.
-/

namespace IndisputableMonolith
namespace Masses
namespace L1b3Q3FlagCarrier

open L1b1UniformReynoldsEngine
open L1b2SignKernelExclusion

noncomputable section

/-- The 48 signed coordinate flags of the Q3/B3 carrier. -/
abbrev Q3Flag : Type :=
  Equiv.Perm (Fin 3) × (Fin 3 → Bool)

/-- The signed-permutation B3 carrier, used as a principal left-action carrier. -/
abbrev B3 : Type :=
  Q3Flag

private theorem q3Flag_nonempty : Nonempty Q3Flag :=
  ⟨(Equiv.refl (Fin 3), fun _ => false)⟩

local instance : Nonempty Q3Flag := q3Flag_nonempty

/-- Local Bool xor, avoiding dependence on library naming. -/
def qxor : Bool → Bool → Bool
  | false, b => b
  | true, false => true
  | true, true => false

/-- Local Bool negation. -/
def qnot : Bool → Bool
  | false => true
  | true => false

@[simp] theorem qxor_self (b : Bool) : qxor b b = false := by
  cases b <;> rfl

@[simp] theorem qxor_comm (a b : Bool) : qxor a b = qxor b a := by
  cases a <;> cases b <;> rfl

@[simp] theorem qxor_assoc (a b c : Bool) :
    qxor (qxor a b) c = qxor a (qxor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem qnot_qnot (b : Bool) : qnot (qnot b) = b := by
  cases b <;> rfl

/-- The Q3 flag carrier has cardinality `3! * 2^3 = 48`. -/
theorem q3Flag_card : Fintype.card Q3Flag = 48 := by
  native_decide

theorem b3_card : Fintype.card B3 = 48 := by
  native_decide

/-- Identity signed permutation. -/
def b3Id : B3 :=
  (Equiv.refl (Fin 3), fun _ => false)

/--
Genuine signed-permutation composition.

If `x` sends slot `i` to axis `x.1 i` with sign bit `x.2 i`,
then `g ∘ x` sends `i` to `g.1 (x.1 i)` and accumulates the sign bit
`x.2 i xor g.2 (x.1 i)`.
-/
def b3Mul (g x : B3) : B3 :=
  (x.1.trans g.1, fun i => qxor (x.2 i) (g.2 (x.1 i)))

/-- Signed-permutation inverse. -/
def b3Inv (x : B3) : B3 :=
  (x.1.symm, fun i => x.2 (x.1.symm i))

/-- The principal left action is signed-permutation composition. -/
def b3Act (g : B3) (x : Q3Flag) : Q3Flag :=
  b3Mul g x

/-- Closed finite sanity check: associativity of genuine B3 composition. -/
theorem b3Mul_assoc_all :
    ∀ a b c : B3, b3Mul a (b3Mul b c) = b3Mul (b3Mul a b) c := by
  native_decide

theorem b3Id_left_all :
    ∀ x : B3, b3Mul b3Id x = x := by
  native_decide

theorem b3Id_right_all :
    ∀ x : B3, b3Mul x b3Id = x := by
  native_decide

theorem b3Inv_left_all :
    ∀ x : B3, b3Mul (b3Inv x) x = b3Id := by
  native_decide

theorem b3Inv_right_all :
    ∀ x : B3, b3Mul x (b3Inv x) = b3Id := by
  native_decide

/-- The unique signed permutation carrying `x` to `y`. -/
def b3Transporter (x y : Q3Flag) : B3 :=
  b3Mul y (b3Inv x)

/-- Finite certificate: the named transporter sends `x` to `y`. -/
theorem b3Act_transporter_all :
    ∀ x y : Q3Flag, b3Act (b3Transporter x y) x = y := by
  native_decide

theorem b3Act_transporter (x y : Q3Flag) :
    b3Act (b3Transporter x y) x = y :=
  b3Act_transporter_all x y

/-- Finite certificate: no other B3 element transports `x` to `y`. -/
theorem b3Act_unique_transporter_iff_all :
    ∀ g x y : Q3Flag,
      (b3Act g x = y ↔ g = b3Transporter x y) := by
  native_decide

/-- The genuine B3 action is transitive. -/
theorem b3Act_transitive :
    ∀ x y : Q3Flag, ∃ g : B3, b3Act g x = y := by
  intro x y
  exact ⟨b3Transporter x y, b3Act_transporter x y⟩

/-- The genuine B3 action is principal: there is a unique transporter. -/
theorem b3Act_unique_transporter (x y : Q3Flag) :
    ∃! g : B3, b3Act g x = y := by
  refine ⟨b3Transporter x y, b3Act_transporter x y, ?_⟩
  intro g hg
  exact (b3Act_unique_transporter_iff_all g x y).mp hg

/-- Permutation matrix of one B3 action element. -/
def b3ActMatrix (g : B3) : Matrix Q3Flag Q3Flag ℝ :=
  fun x y => if b3Act g x = y then 1 else 0

/-- Reynolds average over the genuine B3 principal action. -/
def b3ReynoldsAverage : Matrix Q3Flag Q3Flag ℝ :=
  fun x y =>
    (Fintype.card B3 : ℝ)⁻¹ *
      (∑ g : B3, (if b3Act g x = y then (1 : ℝ) else 0))

private theorem b3_indicator_sum_eq_one (x y : Q3Flag) :
    (∑ g : B3, (if b3Act g x = y then (1 : ℝ) else 0)) = 1 := by
  classical
  let t : B3 := b3Transporter x y
  have hiff : ∀ g : B3, (b3Act g x = y) ↔ g = t := by
    intro g
    dsimp [t]
    exact b3Act_unique_transporter_iff_all g x y
  calc
    (∑ g : B3, (if b3Act g x = y then (1 : ℝ) else 0))
        = ∑ g : B3, (if g = t then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro g _
          simp [hiff g]
    _ = 1 := by
          simp

/-- Reynolds averaging over the principal B3 carrier is the uniform Reynolds projector. -/
theorem b3ReynoldsAverage_eq_uniformReynolds :
    b3ReynoldsAverage = uniformReynolds Q3Flag := by
  ext x y
  rw [uniformReynolds_apply (α := Q3Flag) x y]
  have hsum := b3_indicator_sum_eq_one x y
  simp [b3ReynoldsAverage, hsum, B3]

/-! ## Tau-odd flip-parity character and CPM-cone exclusion -/

/-- Flip-sign parity over the three Bool sign bits. -/
def signParity (s : Fin 3 → Bool) : Bool :=
  qxor (s 0) (qxor (s 1) (s 2))

/-- Toggle the first sign bit. This is the concrete tau involution on the carrier. -/
def flipSignZero (s : Fin 3 → Bool) : Fin 3 → Bool :=
  fun i => if i = (0 : Fin 3) then qnot (s i) else s i

theorem flipSignZero_involutive (s : Fin 3 → Bool) :
    flipSignZero (flipSignZero s) = s := by
  funext i
  by_cases h : i = (0 : Fin 3) <;> simp [flipSignZero, h]

/-- The tau involution toggles one signed-coordinate bit. -/
def q3Tau : Equiv.Perm Q3Flag where
  toFun f := (f.1, flipSignZero f.2)
  invFun f := (f.1, flipSignZero f.2)
  left_inv := by
    intro f
    rcases f with ⟨p, s⟩
    simp [flipSignZero_involutive]
  right_inv := by
    intro f
    rcases f with ⟨p, s⟩
    simp [flipSignZero_involutive]

theorem signParity_flipSignZero (s : Fin 3 → Bool) :
    signParity (flipSignZero s) = qnot (signParity s) := by
  unfold signParity flipSignZero
  simp
  cases s (0 : Fin 3) <;>
  cases s (1 : Fin 3) <;>
  cases s (2 : Fin 3) <;> rfl

/-- Flip-parity is multiplicative under genuine signed-permutation composition. -/
theorem signParity_b3Mul_all :
    ∀ g x : B3,
      signParity (b3Mul g x).2 = qxor (signParity x.2) (signParity g.2) := by
  native_decide

/-- The real plus-or-minus-one flip-parity character. -/
def flipParityChar (f : Q3Flag) : ℝ :=
  if signParity f.2 then (-1 : ℝ) else 1

/-- The flip-parity character is a one-dimensional B3 sign character. -/
theorem flipParityChar_mul (g x : B3) :
    flipParityChar (b3Mul g x) = flipParityChar g * flipParityChar x := by
  unfold flipParityChar
  rw [signParity_b3Mul_all g x]
  cases hx : signParity x.2 <;>
  cases hg : signParity g.2 <;>
  simp [qxor]

theorem flipParityChar_signValues :
    signValues flipParityChar := by
  intro f
  unfold flipParityChar
  by_cases h : signParity f.2
  · right
    simp [h]
  · left
    simp [h]

/-- Toggling one sign bit makes the flip-parity character tau-odd. -/
theorem flipParityChar_tauOdd :
    tauOdd q3Tau flipParityChar := by
  intro f
  rcases f with ⟨p, s⟩
  unfold flipParityChar
  simp [q3Tau, signParity_flipSignZero]
  cases h : signParity s <;> simp [qnot]

theorem flipParityChar_mixedSigns :
    mixedSigns flipParityChar :=
  mixedSigns_of_tauOdd flipParityChar_signValues flipParityChar_tauOdd

/-- The tau-odd flip-parity sign kernel fails entrywise CPM-cone nonnegativity. -/
theorem flipParitySignKernel_not_entrywiseNonneg :
    ¬ entrywiseNonneg (signKernel flipParityChar) := by
  exact signKernel_not_entrywiseNonneg_of_tauOdd
    (α := Q3Flag) (eps := flipParityChar) (tau := q3Tau)
    flipParityChar_signValues flipParityChar_tauOdd

/-- The weak PSD/positive-diagonal gates still hold, but entrywise CPM nonnegativity fails. -/
theorem flipParitySignKernel_weakGates_not_entrywiseNonneg :
    positiveDiagonal (signKernel flipParityChar) ∧
      quadraticNonneg (signKernel flipParityChar) ∧
        ¬ entrywiseNonneg (signKernel flipParityChar) := by
  exact mixedSignKernel_weakGates_hold_not_entrywiseNonneg
    flipParityChar_signValues flipParityChar_mixedSigns

/-- L1b3 finite-carrier certificate. This is not an L1b or L1 closure. -/
structure L1b3Q3FlagCarrierCert where
  q3_card :
    Fintype.card Q3Flag = 48
  b3_card :
    Fintype.card B3 = 48
  b3_assoc :
    ∀ a b c : B3, b3Mul a (b3Mul b c) = b3Mul (b3Mul a b) c
  b3_id_left :
    ∀ x : B3, b3Mul b3Id x = x
  b3_id_right :
    ∀ x : B3, b3Mul x b3Id = x
  b3_inv_left :
    ∀ x : B3, b3Mul (b3Inv x) x = b3Id
  b3_inv_right :
    ∀ x : B3, b3Mul x (b3Inv x) = b3Id
  transitive :
    ∀ x y : Q3Flag, ∃ g : B3, b3Act g x = y
  unique_transporter :
    ∀ x y : Q3Flag, ∃! g : B3, b3Act g x = y
  reynolds_uniform :
    b3ReynoldsAverage = uniformReynolds Q3Flag
  flip_parity_character :
    ∀ g x : B3, flipParityChar (b3Mul g x) = flipParityChar g * flipParityChar x
  tau_odd :
    tauOdd q3Tau flipParityChar
  tau_odd_kernel_not_entrywise_nonneg :
    ¬ entrywiseNonneg (signKernel flipParityChar)
  weak_gates_insufficient :
    positiveDiagonal (signKernel flipParityChar) ∧
      quadraticNonneg (signKernel flipParityChar) ∧
        ¬ entrywiseNonneg (signKernel flipParityChar)

theorem l1b3Q3FlagCarrierCert_holds :
    Nonempty L1b3Q3FlagCarrierCert :=
  ⟨{ q3_card := q3Flag_card
     b3_card := b3_card
     b3_assoc := b3Mul_assoc_all
     b3_id_left := b3Id_left_all
     b3_id_right := b3Id_right_all
     b3_inv_left := b3Inv_left_all
     b3_inv_right := b3Inv_right_all
     transitive := b3Act_transitive
     unique_transporter := b3Act_unique_transporter
     reynolds_uniform := b3ReynoldsAverage_eq_uniformReynolds
     flip_parity_character := flipParityChar_mul
     tau_odd := flipParityChar_tauOdd
     tau_odd_kernel_not_entrywise_nonneg := flipParitySignKernel_not_entrywiseNonneg
     weak_gates_insufficient := flipParitySignKernel_weakGates_not_entrywiseNonneg }⟩

end

end L1b3Q3FlagCarrier
end Masses
end IndisputableMonolith
