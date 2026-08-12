import IndisputableMonolith.Gravity.SevenGaps.ZqShellBalanceBlocker

/-!
# Wave C1 R2: exact-shell tick-phase enrichment schema

Banks the schema residual named in
`plans/QG_WaveC1_Gap2_Residual_DAG_Draft_20260722.txt` R2 (and the CORE 2
PHASE design in `plans/QG_WaveC1_Gap2_HardCore_Design_20260722.txt`):

* `ExactPathClass n` is already the GlobalEquivalent quotient (sigma over
  `ShellSig n` of `Quotient (exactSetoid …)`), so a tick assignment
  `ExactPathClass n → Fin 8` is well-posed on classes by construction.
* Dead classes `ShellConstant` / `EventuallyZeroPhase` are banked in
  `ZqShellBalanceBlocker`; escape requires intra-shell tick variance.
* Eight-tick API (`RRF.Hypotheses.EightTick`) is a Fin-8 *trace*
  hypothesis only; it supplies no equidistribution theorem. The
  equidistribution content lives here as an independent Prop.

## What this module proves (THEOREM)

* Schema structure `ExactShellTickPhaseSubstrate` with derived phase
  `2π · tick / 8`, plus escape fields `not_shellConstant` /
  `not_eventuallyZero`.
* Non-circular guard `TickEquidistributedInShell` (equal fiber
  cardinalities inside each shell; no mention of amplitudes / tails).
* Bridge: mass-balanced Fin-8 fibers cancel by 8th-root orthogonality,
  yielding `ShellAmplitudeVanishes` (`tickEquidistribution_implies_shellAmplitudeVanishes`).
* Concrete witness: signature vertex-count mod 8 escapes both dead
  classes (THEOREM). Its `OscillatoryTail` stays OPEN (R4).
* Decoy: raw complexity tick `2π·(n%8)/8` is `ShellConstant`, hence dead.

## What stays OPEN

* `TypedResidual_strengthened_tick_balance`: contiguous late-block
  `ExactShellTailCancellation` for a tick phase. Per-shell
  equidistribution / `ShellAmplitudeVanishes` is necessary but not
  sufficient for uniform block cancellation.
* Analytic `OscillatoryTail` for the signature-vertex witness (R4).

Does NOT flip `gap2_continuum_and_measure`. No `sorry`, `admit`, new
axiom, or `native_decide`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2TickPhaseSubstrate

open ExactShellGaugeUV
open ZqContinuumBlocker
open ZqShellBalanceBlocker

noncomputable section

/-! ## §1. Derived phase from a Fin-8 tick assignment -/

/-- Phase (radians) attached to a Fin-8 tick: `2π · tick / 8`. -/
def tickDerivedPhase (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) :
    ∀ n : ℕ, ExactPathClass n → ℝ :=
  fun n c => 2 * Real.pi * ((tau n c : ℕ) : ℝ) / 8

/-- Unit 8th-root character of a tick. -/
def tickRoot (p : Fin 8) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((p : ℕ) : ℂ) / 8)

theorem tickDerivedPhase_exp (tau : ∀ n : ℕ, ExactPathClass n → Fin 8)
    (n : ℕ) (c : ExactPathClass n) :
    Complex.exp (Complex.I * (tickDerivedPhase tau n c : ℂ)) =
      tickRoot (tau n c) := by
  unfold tickDerivedPhase tickRoot
  congr 1
  push_cast
  ring

/-! ## §2. Schema structure (escape dead classes; no analytic tail field) -/

/-- Tick-phase enrichment substrate on exact complexity shells.

`tickPhase` is well-posed on the GlobalEquivalent quotient because
`ExactPathClass` is already that quotient type (no separate descent
proof). The analytic cancellation field is *not* packed here: it is the
separate OPEN residual `TypedResidual_strengthened_tick_balance`. -/
structure ExactShellTickPhaseSubstrate where
  tickPhase : ∀ n : ℕ, ExactPathClass n → Fin 8
  not_shellConstant :
    ¬ ShellConstant (tickDerivedPhase tickPhase)
  not_eventuallyZero :
    ¬ EventuallyZeroPhase (tickDerivedPhase tickPhase)

/-- Extracted real phase of a substrate. -/
def ExactShellTickPhaseSubstrate.phase (S : ExactShellTickPhaseSubstrate) :
    ∀ n : ℕ, ExactPathClass n → ℝ :=
  tickDerivedPhase S.tickPhase

/-! ## §3. Non-circular equidistribution guard (cardinal) -/

/-- Fiber of tick value `p` inside shell `n`. -/
def tickFiber (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) (n : ℕ) (p : Fin 8) :
    Finset (ExactPathClass n) :=
  Finset.univ.filter (fun c => tau n c = p)

/-- **Non-circular guard.** Equal cardinalities of tick fibers inside each
exact shell. Mentions only `tau` and Finset cardinality; never
`exactShellAmplitude`, `OscillatoryTail`, or limits. -/
def TickEquidistributedInShell (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) :
    Prop :=
  ∀ n : ℕ, ∀ p q : Fin 8, (tickFiber tau n p).card = (tickFiber tau n q).card

/-- Mass of a tick fiber (uses `classMu` only; still free of amplitude /
tail / limit language). -/
def tickFiberMass (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) (n : ℕ)
    (p : Fin 8) : ℝ :=
  ∑ c ∈ tickFiber tau n p, classMu c

/-- Equal `classMu`-mass across the eight tick fibers of each shell.
This is the load-bearing hypothesis of the root-of-unity bridge: cardinal
equidistribution alone cannot cancel unequal class masses. -/
def TickFiberMassBalanced (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) : Prop :=
  ∀ n : ℕ, ∀ p q : Fin 8, tickFiberMass tau n p = tickFiberMass tau n q

/-- Cardinal equidistribution + shellwise-constant `classMu` yields mass
balance (transport between the combinatorial guard and the bridge hyp). -/
theorem tickCardEquidistribution_constantMu_implies_massBalanced
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8)
    (hcard : TickEquidistributedInShell tau)
    (hmu : ∀ n : ℕ, ∀ c d : ExactPathClass n, classMu c = classMu d) :
    TickFiberMassBalanced tau := by
  intro n p q
  unfold tickFiberMass
  obtain ⟨c0⟩ := (inferInstance : Nonempty (ExactPathClass n))
  have hcard_eq := hcard n p q
  have hmu_p : ∀ c ∈ tickFiber tau n p, classMu c = classMu c0 :=
    fun c _ => hmu n c c0
  have hmu_q : ∀ c ∈ tickFiber tau n q, classMu c = classMu c0 :=
    fun c _ => hmu n c c0
  simp only [Finset.sum_congr rfl hmu_p, Finset.sum_congr rfl hmu_q,
    Finset.sum_const, nsmul_eq_mul]
  rw [hcard_eq]

/-! ## §4. Eighth-root orthogonality and the amplitude bridge -/

private lemma eighth_root_ne_one :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) ≠ 1 := by
  intro h
  have hpow :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) ^ 4 =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8 * 4) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hπ :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8 * 4) =
        Complex.exp ((Real.pi : ℂ) * Complex.I) := by
    congr 1
    ring
  have hneg : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 :=
    Complex.exp_pi_mul_I
  have : (1 : ℂ) = -1 := by
    calc (1 : ℂ)
        = (1 : ℂ) ^ 4 := by norm_num
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) ^ 4 := by rw [h]
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8 * 4) := hpow
      _ = Complex.exp ((Real.pi : ℂ) * Complex.I) := hπ
      _ = -1 := hneg
  exact absurd this (by norm_num)

private lemma eighth_root_pow_eight :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) ^ 8 = 1 := by
  rw [← Complex.exp_nat_mul]
  have harg : (8 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 8) =
      2 * (Real.pi : ℂ) * Complex.I := by
    ring
  rw [harg, Complex.exp_two_pi_mul_I]

/-- Sum of the eight 8th roots of unity vanishes. -/
theorem sum_tickRoots_eq_zero : ∑ p : Fin 8, tickRoot p = 0 := by
  unfold tickRoot
  have hterm : ∀ p : Fin 8,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((p : ℕ) : ℂ) / 8) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) ^ (p : ℕ) := by
    intro p
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  calc ∑ p : Fin 8,
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((p : ℕ) : ℂ) / 8)
      = ∑ p : Fin 8,
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) ^ (p : ℕ) :=
        Finset.sum_congr rfl fun p _ => hterm p
    _ = ∑ k ∈ Finset.range 8,
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) ^ k :=
        Fin.sum_univ_eq_sum_range
          (fun k => Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) ^ k) 8
    _ = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) ^ 8 - 1) /
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 8) - 1) :=
        geom_sum_eq eighth_root_ne_one 8
    _ = 0 := by
        rw [eighth_root_pow_eight, sub_self, zero_div]

/-- Group the weighted shell amplitude by tick fiber. -/
theorem exactShellAmplitude_tick_fiberwise
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) (n : ℕ) :
    exactShellAmplitude (tickDerivedPhase tau) n =
      ∑ p : Fin 8, (tickFiberMass tau n p : ℂ) * tickRoot p := by
  unfold exactShellAmplitude tickFiberMass tickFiber
  have hsplit :
      (∑ c : ExactPathClass n,
          (classMu c : ℂ) *
            Complex.exp (Complex.I * (tickDerivedPhase tau n c : ℂ))) =
        ∑ p : Fin 8,
          ∑ c ∈ Finset.univ.filter (fun c => tau n c = p),
            (classMu c : ℂ) *
              Complex.exp (Complex.I * (tickDerivedPhase tau n c : ℂ)) := by
    exact (Finset.sum_fiberwise_of_maps_to
      (t := Finset.univ) (g := fun c : ExactPathClass n => tau n c)
      (fun _ _ => Finset.mem_univ _) _).symm
  rw [hsplit]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hmul :
      ∑ c ∈ Finset.univ.filter (fun c => tau n c = p),
          (classMu c : ℂ) *
            Complex.exp (Complex.I * (tickDerivedPhase tau n c : ℂ)) =
        ∑ c ∈ Finset.univ.filter (fun c => tau n c = p),
          (classMu c : ℂ) * tickRoot p := by
    refine Finset.sum_congr rfl fun c hc => ?_
    have htau : tau n c = p := (Finset.mem_filter.mp hc).2
    rw [tickDerivedPhase_exp, htau]
  rw [hmul, ← Finset.sum_mul, Complex.ofReal_sum]

/-- Under equal fiber masses, every shell amplitude is identically zero
(8th-root cancellation). -/
theorem exactShellAmplitude_eq_zero_of_massBalanced
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8)
    (hbal : TickFiberMassBalanced tau) (n : ℕ) :
    exactShellAmplitude (tickDerivedPhase tau) n = 0 := by
  rw [exactShellAmplitude_tick_fiberwise]
  have hconst : ∀ p : Fin 8, tickFiberMass tau n p = tickFiberMass tau n 0 :=
    fun p => hbal n p 0
  calc ∑ p : Fin 8, (tickFiberMass tau n p : ℂ) * tickRoot p
      = ∑ p : Fin 8, (tickFiberMass tau n 0 : ℂ) * tickRoot p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hconst p]
    _ = (tickFiberMass tau n 0 : ℂ) * ∑ p : Fin 8, tickRoot p := by
        rw [Finset.mul_sum]
    _ = (tickFiberMass tau n 0 : ℂ) * 0 := by rw [sum_tickRoots_eq_zero]
    _ = 0 := by ring

/-- **BRIDGE THEOREM.** Mass-balanced Fin-8 tick equidistribution forces
the shell-local necessary condition `ShellAmplitudeVanishes`.

Honesty: the named design bridge is realized by equal fiber *mass*
(`TickFiberMassBalanced`). The cardinal guard
`TickEquidistributedInShell` is non-circular and independent; with
shellwise-constant `classMu` it implies mass balance via
`tickCardEquidistribution_constantMu_implies_massBalanced`. -/
theorem tickEquidistribution_implies_shellAmplitudeVanishes
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8)
    (hbal : TickFiberMassBalanced tau) :
    ShellAmplitudeVanishes (tickDerivedPhase tau) := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  rw [exactShellAmplitude_eq_zero_of_massBalanced tau hbal n, norm_zero]
  exact hε

/-! ## §5. Strengthened contiguous-block residual (OPEN) -/

/-- **OPEN typed residual** (R3→R4 analytic half). Contiguous late-block
cancellation for a tick-derived phase:
`ExactShellTailCancellation (tickDerivedPhase tau)`.

Why per-shell equidistribution is insufficient: `TickFiberMassBalanced`
(and even the consequence `ShellAmplitudeVanishes`) only forces each
individual late shell amplitude to vanish. `ExactShellTailCancellation`
(equivalently `OscillatoryTail`) demands uniform smallness of every
contiguous late block `∑_{k ∈ Ico (m+1) (n+1)} amp_k`. Vanishing of
summands does not automatically control coherent accumulation across many
shells; the banked implication
`oscillatoryTail_implies_shellAmplitudeVanishes` is one-directional.

This Prop is uninhabited in this module on purpose. -/
def TypedResidual_strengthened_tick_balance
    (tau : ∀ n : ℕ, ExactPathClass n → Fin 8) : Prop :=
  ExactShellTailCancellation (tickDerivedPhase tau)

/-- Schema package Prop matching DAG R2 (existence of an escaping
tick-phase enrichment; analytic tail NOT required). -/
def TypedResidual_shell_phase_enrichment_schema : Prop :=
  Nonempty ExactShellTickPhaseSubstrate

/-! ## §6. Concrete escaping witness: signature vertex-count mod 8 -/

/-- Intra-shell tick from the shell-signature vertex count mod 8.

`ExactPathClass n = Σ s : ShellSig n, Quotient …` exposes the signature
`(v,e,t)` outside the GlobalEquivalent quotient. Vertex count `sigV`
therefore descends automatically and varies inside a shell (e.g. isolated
`(n,0,0)` vs edge-heavy `(1,n,0)`). Quotient-internal incidence data is
*not* used here; R4 feasibility for true oscillatory cancellation may
still need richer class invariants than signature counts alone. -/
def signatureVertexTick (n : ℕ) (c : ExactPathClass n) : Fin 8 :=
  ⟨sigV c.1 % 8, Nat.mod_lt _ (by norm_num : (0 : ℕ) < 8)⟩

/-- Edge-heavy labeled complex at signature `(1, n, 0)`. -/
def edgeHeavyComplex (n : ℕ) : ExactComplex 1 n 0 where
  edgeVerts := fun _ => (0, 0)
  tetVerts := fun i => i.elim0

/-- Shell signature `(1, n, 0)` at level `n ≥ 1`. -/
def edgeHeavySig (n : ℕ) (hn : 1 ≤ n) : ShellSig n :=
  ⟨(⟨1, by omega⟩, ⟨n, Nat.lt_succ_self n⟩, ⟨0, Nat.succ_pos n⟩), by
    change max (1 : ℕ) (max n 0) = n
    rw [Nat.max_zero]
    exact Nat.max_eq_right hn⟩

/-- Class of the edge-heavy complex inside shell `n`. -/
def edgeHeavyClass (n : ℕ) (hn : 1 ≤ n) : ExactPathClass n :=
  ⟨edgeHeavySig n hn, Quotient.mk _ (edgeHeavyComplex n)⟩

theorem signatureVertexTick_edgeHeavy (n : ℕ) (hn : 1 ≤ n) :
    signatureVertexTick n (edgeHeavyClass n hn) =
      ⟨1 % 8, Nat.mod_lt _ (by norm_num : (0 : ℕ) < 8)⟩ := by
  rfl

theorem signatureVertexTick_isolated (n : ℕ) :
    signatureVertexTick n (isolatedClass n) =
      ⟨n % 8, Nat.mod_lt _ (by norm_num : (0 : ℕ) < 8)⟩ := by
  rfl

theorem signatureVertexTickPhase_not_shellConstant :
    ¬ ShellConstant (tickDerivedPhase signatureVertexTick) := by
  intro hconst
  have h := hconst 2 (edgeHeavyClass 2 (by norm_num))
  -- LHS tick = 1, RHS tick = 2
  have hL : tickDerivedPhase signatureVertexTick 2 (edgeHeavyClass 2 (by norm_num)) =
      2 * Real.pi * (1 : ℝ) / 8 := by
    simp only [tickDerivedPhase, signatureVertexTick_edgeHeavy]
    norm_num
  have hR : tickDerivedPhase signatureVertexTick 2 (isolatedClass 2) =
      2 * Real.pi * (2 : ℝ) / 8 := by
    simp only [tickDerivedPhase, signatureVertexTick_isolated]
    norm_num
  have hEq : (2 * Real.pi * (1 : ℝ) / 8) = 2 * Real.pi * (2 : ℝ) / 8 := by
    calc 2 * Real.pi * (1 : ℝ) / 8
        = tickDerivedPhase signatureVertexTick 2 (edgeHeavyClass 2 (by norm_num)) :=
          hL.symm
      _ = tickDerivedPhase signatureVertexTick 2 (isolatedClass 2) := h
      _ = 2 * Real.pi * (2 : ℝ) / 8 := hR
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have : (1 : ℝ) = 2 := by
    have := congrArg (fun x : ℝ => x * 8 / (2 * Real.pi)) hEq
    field_simp [hπ.ne'] at this
    linarith
  norm_num at this

theorem signatureVertexTickPhase_not_eventuallyZero :
    ¬ EventuallyZeroPhase (tickDerivedPhase signatureVertexTick) := by
  intro hzero
  obtain ⟨N, hN⟩ := hzero
  let n : ℕ := 8 * N + 1
  have hn : N ≤ n := by
    change N ≤ 8 * N + 1
    omega
  have hph := hN n hn (isolatedClass n)
  have hval : tickDerivedPhase signatureVertexTick n (isolatedClass n) =
      2 * Real.pi * (1 : ℝ) / 8 := by
    simp only [tickDerivedPhase, signatureVertexTick_isolated]
    have hmod : n % 8 = 1 := by
      change (8 * N + 1) % 8 = 1
      rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt (by norm_num)]
    simp only [hmod]
    norm_num
  have hEq : (2 * Real.pi * (1 : ℝ) / 8) = 0 := by
    calc 2 * Real.pi * (1 : ℝ) / 8
        = tickDerivedPhase signatureVertexTick n (isolatedClass n) := hval.symm
      _ = 0 := by
          simpa [zeroPhase] using hph
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [hπ]

/-- **THEOREM.** Signature vertex-count mod 8 is an escaping tick-phase
substrate (clears both certified dead classes). Analytic
`OscillatoryTail` / strengthened block cancellation remain OPEN. -/
def signatureVertexTickSubstrate : ExactShellTickPhaseSubstrate where
  tickPhase := signatureVertexTick
  not_shellConstant := signatureVertexTickPhase_not_shellConstant
  not_eventuallyZero := signatureVertexTickPhase_not_eventuallyZero

theorem typedResidual_shell_phase_enrichment_schema_closed :
    TypedResidual_shell_phase_enrichment_schema :=
  ⟨signatureVertexTickSubstrate⟩

/-! ## §7. Decoy: complexity-only eight-tick phase is ShellConstant -/

/-- Raw complexity tick: phase depends only on shell index `n % 8`. -/
def complexityTick (n : ℕ) (_c : ExactPathClass n) : Fin 8 :=
  ⟨n % 8, Nat.mod_lt n (by norm_num : (0 : ℕ) < 8)⟩

def complexityTickPhase : ∀ n : ℕ, ExactPathClass n → ℝ :=
  tickDerivedPhase complexityTick

/-- **DECOY THEOREM.** The raw complexity eight-tick phase is
shell-constant (banked dead class). -/
theorem complexityTickPhase_shellConstant :
    ShellConstant complexityTickPhase := by
  intro n c
  rfl

/-- Decoy is killed by the banked `shellConstant_not_oscillatoryTail`. -/
theorem complexityTickPhase_not_oscillatoryTail :
    ¬ OscillatoryTail complexityTickPhase :=
  shellConstant_not_oscillatoryTail complexityTickPhase
    complexityTickPhase_shellConstant

theorem complexityTickPhase_decoy_dead :
    ShellConstant complexityTickPhase ∧
      ¬ OscillatoryTail complexityTickPhase :=
  ⟨complexityTickPhase_shellConstant, complexityTickPhase_not_oscillatoryTail⟩

/-! ## §8. Status flags (no continuum flip) -/

structure Gap2TickPhaseSubstrateStatus where
  r2SchemaClosed : Bool
  escapingWitnessLanded : Bool
  strengthenedBalanceOpen : Bool
  gap2ContinuumAndMeasure : Bool

def gap2TickPhaseSubstrateStatus : Gap2TickPhaseSubstrateStatus where
  r2SchemaClosed := true
  escapingWitnessLanded := true
  strengthenedBalanceOpen := true
  gap2ContinuumAndMeasure := false

theorem gap2TickPhaseSubstrateStatus_flags :
    gap2TickPhaseSubstrateStatus.r2SchemaClosed = true ∧
      gap2TickPhaseSubstrateStatus.escapingWitnessLanded = true ∧
      gap2TickPhaseSubstrateStatus.strengthenedBalanceOpen = true ∧
      gap2TickPhaseSubstrateStatus.gap2ContinuumAndMeasure = false := by
  decide

end

end Gap2TickPhaseSubstrate
end SevenGaps
end Gravity
end IndisputableMonolith
