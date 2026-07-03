import IndisputableMonolith.Foundation.ArithmeticFromLogic
import IndisputableMonolith.Foundation.ArithmeticOf
import IndisputableMonolith.Foundation.UniversalForcing
import IndisputableMonolith.Foundation.UniversalForcing.CanonicalForcing
import IndisputableMonolith.Foundation.UniversalInstantiationFromDistinction
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealLineNonNativity

/-!
# Distinction to Arithmetic: the named bridge (Universal Forcing, distinction side)

This module welds the two halves of the Universal-Forcing program that were
already proved separately, into the single named object the program register
(`δ native analysis / unification from distinction`, L5) asks for: a Lean object
that maps a *distinction* to its forced `ArithmeticOf` and proves that object is
canonical.

Until now the route from a distinction to `ArithmeticOf` existed only
compositionally:

```
(∃ x y : K, x ≠ y)
  → logicRealizationOfDistinction K x y hxy : LogicRealization      -- instantiation
  → UniversalForcing.arithmeticOf …          : ArithmeticOf _        -- extraction
  → distinction_arithmetic_equiv_logicNat    : carrier ≃ LogicNat    -- identification
```

There was no single named `ArithmeticOf`-valued constructor from distinction
data, and no statement that the resulting forcing map is the *unique*
structure-preserving map (canonicity, not bare iso). This module supplies both,
and then states the δ-native scope honestly: a distinction forces the *countable*
initial Peano arithmetic (`LogicNat`), and the continuum is **not** forced from
countable distinction certificates (`real_not_forced_from_distinction`). So the
forced arithmetic of a distinction lands at `LogicNat`, never at `ℝ`; the real
line enters only through a completion/display interface, not from distinction
alone.

What is THEOREM-grade here (0 sorry, no project-local axioms):

* `arithmeticOfDistinction` — the named `ArithmeticOf` object of one distinction.
* `arithmeticOfDistinction_peanoSurface` — it carries the Peano surface
  (zero ≠ step, step injective, induction).
* `arithmeticOfDistinction_carrier_equiv_logicNat` — its carrier is `LogicNat`.
* `arithmeticOfDistinction_carrier_countable` — hence countable.
* `distinction_forcing_map` / `distinction_forcing_map_unique` /
  `distinction_arithmetic_universal_objective` — between any two distinctions
  (carriers in one universe) the forcing map exists and is the *unique*
  zero/step-preserving map. This is canonicity, the content of
  `universal-forcing-program.mdc`'s "canonical equivalence of `ArithmeticOf R`
  and `ArithmeticOf S`", instantiated on the distinction primitive.
* `real_not_forced_from_distinction` — the δ-native upper scope: ℝ is not
  faithfully certifiable from any countable certificate system.
* `DistinctionArithmeticCert` / `distinctionArithmeticCert` — the bundle.

This does not re-prove Universal Forcing Part II; it **anchors** it to the
distinction primitive that the `δ` papers and `RealityFromDistinction` use.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DistinctionToArithmetic

open ArithmeticFromLogic
open UniversalForcing
open UniversalInstantiationFromDistinction

universe u

/-! ## The named forced-arithmetic object of one distinction -/

/-- **The forced arithmetic object of a single distinction.** Given a carrier `K`
with two distinguishable points `x ≠ y`, this is the `ArithmeticOf` extracted from
the `K`-native Law-of-Logic realization. It is the named object the program
register asks for: a Lean map from distinction data to `ArithmeticOf`. -/
noncomputable def arithmeticOfDistinction
    {K : Type u} [DecidableEq K] (x y : K) (hxy : x ≠ y) :
    ArithmeticOf.{u, 0, u, u, u} (logicRealizationOfDistinction K x y hxy) :=
  UniversalForcing.arithmeticOf (logicRealizationOfDistinction K x y hxy)

/-- The distinction-forced arithmetic carries the Peano surface: its zero is never
a step, its step is injective, and it satisfies induction. -/
theorem arithmeticOfDistinction_peanoSurface
    {K : Type u} [DecidableEq K] (x y : K) (hxy : x ≠ y) :
    ArithmeticOf.PeanoSurface (arithmeticOfDistinction x y hxy) :=
  UniversalForcing.peano_surface (logicRealizationOfDistinction K x y hxy)

/-- The carrier of the distinction-forced arithmetic is canonically `LogicNat`. -/
noncomputable def arithmeticOfDistinction_carrier_equiv_logicNat
    {K : Type u} [DecidableEq K] (x y : K) (hxy : x ≠ y) :
    (arithmeticOfDistinction x y hxy).peano.carrier ≃ LogicNat :=
  distinction_arithmetic_equiv_logicNat.{u, u, u} x y hxy

/-- The distinction-forced arithmetic carrier is **countable**: it is `LogicNat`,
which is equivalent to `ℕ`. This is the δ-native lower fact: a distinction forces
exactly the countable initial Peano object, no more. -/
theorem arithmeticOfDistinction_carrier_countable
    {K : Type u} [DecidableEq K] (x y : K) (hxy : x ≠ y) :
    Countable (arithmeticOfDistinction x y hxy).peano.carrier := by
  haveI : Countable LogicNat := Countable.of_equiv Nat LogicNat.equivNat.symm
  exact Countable.of_equiv LogicNat
    (arithmeticOfDistinction_carrier_equiv_logicNat x y hxy).symm

/-- **Distinction forces an initial Peano arithmetic.** From the bare proposition
that `K` has two distinct points, there is a named distinction whose forced
arithmetic carrier is canonically `LogicNat`. -/
theorem distinction_forces_arithmeticOf
    {K : Type u} [DecidableEq K] (h : ∃ x y : K, x ≠ y) :
    ∃ (x y : K) (hxy : x ≠ y),
      Nonempty ((arithmeticOfDistinction x y hxy).peano.carrier ≃ LogicNat) := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, hxy, ⟨arithmeticOfDistinction_carrier_equiv_logicNat x y hxy⟩⟩

/-! ## Canonicity: the forcing map between two distinctions is unique

These statements fix both carriers in one universe `u`. That is the standard
"shared carrier universe" setting documented in `CanonicalForcing.lean`; it is not
a restriction on the mathematics, only the setting in which "the unique structure
morphism" is a well-formed comparison. -/

/-- The canonical forcing equivalence between the forced arithmetics of two
distinctions. -/
noncomputable def distinction_forcing_map
    {K L : Type u} [DecidableEq K] [DecidableEq L]
    {x y : K} {a b : L} (hxy : x ≠ y) (hab : a ≠ b) :
    (arithmeticOfDistinction x y hxy).peano.carrier ≃
      (arithmeticOfDistinction a b hab).peano.carrier :=
  ArithmeticOf.equivOfInitial (arithmeticOfDistinction x y hxy) (arithmeticOfDistinction a b hab)

/-- **Canonicity for distinctions.** Any zero/step-preserving function between the
forced arithmetics of two distinctions *is* the forcing map. The map is determined
by the distinction data alone, with no representational freedom. -/
theorem distinction_forcing_map_unique
    {K L : Type u} [DecidableEq K] [DecidableEq L]
    {x y : K} {a b : L} (hxy : x ≠ y) (hab : a ≠ b)
    (f : (arithmeticOfDistinction x y hxy).peano.carrier →
          (arithmeticOfDistinction a b hab).peano.carrier)
    (hz : f (arithmeticOfDistinction x y hxy).peano.zero =
            (arithmeticOfDistinction a b hab).peano.zero)
    (hs : ∀ p, f ((arithmeticOfDistinction x y hxy).peano.step p) =
            (arithmeticOfDistinction a b hab).peano.step (f p)) :
    f = (distinction_forcing_map hxy hab).toFun :=
  ArithmeticOf.forcing_map_unique
    (arithmeticOfDistinction x y hxy) (arithmeticOfDistinction a b hab) f hz hs

/-- **The Universal-Forcing objective on the distinction primitive.** For any two
distinctions, there is a structure-preserving equivalence between their forced
arithmetics that is *the unique* zero/step-preserving map: existence plus
canonicity in one statement. -/
theorem distinction_arithmetic_universal_objective
    {K L : Type u} [DecidableEq K] [DecidableEq L]
    {x y : K} {a b : L} (hxy : x ≠ y) (hab : a ≠ b) :
    ∃ e : (arithmeticOfDistinction x y hxy).peano.carrier ≃
            (arithmeticOfDistinction a b hab).peano.carrier,
      e (arithmeticOfDistinction x y hxy).peano.zero =
          (arithmeticOfDistinction a b hab).peano.zero
      ∧ (∀ p, e ((arithmeticOfDistinction x y hxy).peano.step p) =
            (arithmeticOfDistinction a b hab).peano.step (e p))
      ∧ (∀ f : (arithmeticOfDistinction x y hxy).peano.carrier →
              (arithmeticOfDistinction a b hab).peano.carrier,
            f (arithmeticOfDistinction x y hxy).peano.zero =
                (arithmeticOfDistinction a b hab).peano.zero →
            (∀ p, f ((arithmeticOfDistinction x y hxy).peano.step p) =
                  (arithmeticOfDistinction a b hab).peano.step (f p)) →
            f = e.toFun) :=
  ArithmeticOf.universal_objective
    (arithmeticOfDistinction x y hxy) (arithmeticOfDistinction a b hab)

/-! ## δ-native scope: the continuum is not forced from a distinction

The forced arithmetic of any distinction is countable (`LogicNat`). The continuum
is a strictly larger object, and the cardinality obstruction shows it cannot be
faithfully covered by any countable certificate system. So the real line is not
native to distinction; it is reached only by completion/display. -/

/-- **ℝ is not forced from a distinction.** No countable certificate system
faithfully covers ℝ. Restated from `RealLineNonNativity.real_not_faithfully_certifiable`
to sit beside the distinction-forced (countable) arithmetic and make the
unification explicit: distinction forces `LogicNat`, never `ℝ`. -/
theorem real_not_forced_from_distinction
    {Cert : Type} [Countable Cert] (assign : ℝ → Cert) :
    ¬ PrimitiveRecognitionCalculus.RealLineNonNativity.Faithful assign :=
  PrimitiveRecognitionCalculus.RealLineNonNativity.real_not_faithfully_certifiable assign

/-! ## Certificate -/

/-- **Distinction-to-arithmetic certificate.** For any carrier `K`, every
distinction on `K` forces an initial Peano arithmetic object whose carrier is
`LogicNat` (hence countable) and which carries the full Peano surface. -/
structure DistinctionArithmeticCert (K : Type u) [DecidableEq K] : Prop where
  /-- Every distinction forces an arithmetic carrier equivalent to `LogicNat`. -/
  forces_initial_arithmetic :
    ∀ (x y : K) (hxy : x ≠ y),
      Nonempty ((arithmeticOfDistinction x y hxy).peano.carrier ≃ LogicNat)
  /-- The forced arithmetic carrier is countable. -/
  forced_arithmetic_countable :
    ∀ (x y : K) (hxy : x ≠ y),
      Countable (arithmeticOfDistinction x y hxy).peano.carrier
  /-- The forced arithmetic carries the Peano surface. -/
  peano_surface :
    ∀ (x y : K) (hxy : x ≠ y),
      ArithmeticOf.PeanoSurface (arithmeticOfDistinction x y hxy)

/-- The distinction-to-arithmetic certificate holds for every carrier. -/
theorem distinctionArithmeticCert (K : Type u) [DecidableEq K] :
    DistinctionArithmeticCert K where
  forces_initial_arithmetic := fun x y hxy =>
    ⟨arithmeticOfDistinction_carrier_equiv_logicNat x y hxy⟩
  forced_arithmetic_countable := fun x y hxy =>
    arithmeticOfDistinction_carrier_countable x y hxy
  peano_surface := fun x y hxy =>
    arithmeticOfDistinction_peanoSurface x y hxy

end DistinctionToArithmetic
end Foundation
end IndisputableMonolith
