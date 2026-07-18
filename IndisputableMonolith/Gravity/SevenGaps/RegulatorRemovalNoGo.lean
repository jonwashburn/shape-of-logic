import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.ExactShellGaugeUV

/-!
# Seven Gaps: regulator removal FAILS at zero phase (kernel no-go)

## What this module proves (and what it does NOT)

**Status: THEOREM (kernel no-go at zero phase).**  This module proves that
the Gaussian-regulated quotient path sum `Z_RS_uv` of
`ExactShellGaugeUV` has NO `ρ → 0⁺` limit at zero phase
(`not_hasZRSRegulatorRemoval_zeroPhase`): the named OPEN
`HasZRSRegulatorRemoval zeroPhase` is refuted, not merely left open.
The mechanism is quantitative and fully kernel-checked:

* **Shell-mass identity (Burnside / orbit-stabilizer route).**  For every
  exact signature `(v, e, t)`, the sum of the per-class measures
  `1/|Aut|` over the quotient equals the labeled count divided by the
  full relabeling gauge volume `v!·e!·t!`
  (`sum_classMuOn_eq_card_div_factorials`).  The proof realizes the
  relabeling-triple group as a torsor over the sigma of all relabelings
  out of a fixed base complex (`relabelSigmaEquiv`), splits it fiberwise
  by orbit-stabilizer (`orbitCard_mul_autCard`), and sums fibers over the
  quotient (`sum_orbitCard`).
* **Shell-mass divergence.**  `shellMass n = ∑_classes 1/|Aut|` grows
  without bound (`shellMass_unbounded`): restricting to the single
  signature `(n, n, n)` gives `shellMass n ≥ n^(6n)/(n!)³ ≥ n^(3n)`
  (`shellMass_lower`) since `n! ≤ n^n`.  Labeled entropy beats the
  factorial gauge volume, so the absolute/positive-term route to
  regulator removal is dead.
* **The headline no-go.**  At zero phase every regulated term is real and
  nonnegative, so a single shell bounds the regulated sum from below
  (`single_shell_re_lower_bound`); as `ρ → 0⁺` the regulator on any fixed
  shell tends to 1, so any putative limit `L` is exceeded by a shell of
  mass `> L.re + 2`.  Contradiction: `¬ HasZRSRegulatorRemoval zeroPhase`.

**What is NOT proved (binding honesty disclosures):**
* NOTHING about oscillatory phases: regulator removal for a genuine
  action phase would require proved cancellation between unit phases and
  remains OPEN (`OscillatoryRemovalOpen` is a definition-level Prop
  below, never claimed, and `regulatorRemovalNoGoStatus` records it
  `open`).  The zero-phase refutation does NOT transport to nonzero
  phases: the lower-bound argument uses positivity, which oscillation
  destroys.
* NOTHING about the physical continuum limit: the complexity cutoff is
  NOT mesh refinement (standing constraint); no `FullTheoryLedger` or
  `CampaignLedger` flag is flipped by this module.
* `Z_RS_uv` is the QUOTIENT-sum convention (per-class measure `1/|Aut|`);
  it must never be silently equated with the labeled-sum convention of
  `PathSumMeasure.Z` (standing constraint, respected here: only
  `ExactShellGaugeUV` definitions are used).

## Status tiers (honest tagging)

**THEOREM (proved below, 0 sorry, 0 new axioms, no `native_decide`):**
`sum_classMuOn_eq_card_div_factorials`, `orbitCard_mul_autCard`,
`shellMass_lower`, `shellMass_unbounded`,
`single_shell_re_lower_bound`, `not_hasZRSRegulatorRemoval_zeroPhase`.

**MODEL (definitional, inherited):** the `1/|Aut|` symmetry-factor
measure and the Gaussian regulator shape, both from `ExactShellGaugeUV`.

**OPEN (named, never claimed):** `OscillatoryRemovalOpen` (regulator
removal for some nonzero phase); the physical continuum limit.

Expected axiom footprint: standard trio
`[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace RegulatorRemovalNoGo

open ExactShellGaugeUV

/-! ## §1. The relabeling triple group and its pushforward action -/

variable {v e t : ℕ}

/-- The full relabeling gauge group at signature `(v, e, t)`: independent
permutations of the vertex, edge, and tetrahedron index sets. -/
abbrev RelabelTriple (v e t : ℕ) : Type :=
  (Fin v ≃ Fin v) × (Fin e ≃ Fin e) × (Fin t ≃ Fin t)

/-- **Gauge volume.**  The relabeling triple group has cardinality
`v!·e!·t!`. -/
theorem relabelTriple_card (v e t : ℕ) :
    Fintype.card (RelabelTriple v e t)
      = v.factorial * e.factorial * t.factorial := by
  have hv : Fintype.card (Fin v ≃ Fin v) = v.factorial := by
    rw [Fintype.card_equiv (Equiv.refl (Fin v)), Fintype.card_fin]
  have he : Fintype.card (Fin e ≃ Fin e) = e.factorial := by
    rw [Fintype.card_equiv (Equiv.refl (Fin e)), Fintype.card_fin]
  have ht : Fintype.card (Fin t ≃ Fin t) = t.factorial := by
    rw [Fintype.card_equiv (Equiv.refl (Fin t)), Fintype.card_fin]
  rw [Fintype.card_prod, Fintype.card_prod, hv, he, ht]
  ring

/-- Pushforward action of a relabeling triple on a labeled complex:
transport the incidence data along the three index bijections. -/
def act (σ : RelabelTriple v e t) (K : ExactComplex v e t) :
    ExactComplex v e t where
  edgeVerts i := Prod.map σ.1 σ.1 (K.edgeVerts (σ.2.1.symm i))
  tetVerts i j := σ.1 (K.tetVerts (σ.2.2.symm i) j)

/-- The tautological relabeling witness from `K` to `act σ K`. -/
def actRelabel (σ : RelabelTriple v e t) (K : ExactComplex v e t) :
    ExactRelabel K (act σ K) where
  vEquiv := σ.1
  eEquiv := σ.2.1
  tEquiv := σ.2.2
  edge_comm := fun i => by
    show Prod.map σ.1 σ.1 (K.edgeVerts (σ.2.1.symm (σ.2.1 i)))
        = Prod.map σ.1 σ.1 (K.edgeVerts i)
    rw [Equiv.symm_apply_apply]
  tet_comm := fun i j => by
    show σ.1 (K.tetVerts (σ.2.2.symm (σ.2.2 i)) j) = σ.1 (K.tetVerts i j)
    rw [Equiv.symm_apply_apply]

/-- Extensionality for exact complexes (incidence data determines the
complex). -/
theorem exactComplex_ext {K K' : ExactComplex v e t}
    (he : K.edgeVerts = K'.edgeVerts) (ht : K.tetVerts = K'.tetVerts) :
    K = K' := by
  cases K with
  | mk ev tv =>
    cases K' with
    | mk ev' tv' =>
      simp only [ExactComplex.mk.injEq]
      exact ⟨he, ht⟩

/-- A pair `(target, witness)` in the total relabeling sigma is determined
by the witness's index bijections (the target is forced by the
commutation equations). -/
theorem sigma_relabel_ext {K : ExactComplex v e t}
    (p q : Σ K' : ExactComplex v e t, ExactRelabel K K')
    (hv : p.2.vEquiv = q.2.vEquiv) (he : p.2.eEquiv = q.2.eEquiv)
    (ht : p.2.tEquiv = q.2.tEquiv) : p = q := by
  obtain ⟨K₁, r₁⟩ := p
  obtain ⟨K₂, r₂⟩ := q
  replace hv : r₁.vEquiv = r₂.vEquiv := hv
  replace he : r₁.eEquiv = r₂.eEquiv := he
  replace ht : r₁.tEquiv = r₂.tEquiv := ht
  have hK : K₁ = K₂ := by
    refine exactComplex_ext ?_ ?_
    · funext i
      have h₁ := r₁.edge_comm (r₁.eEquiv.symm i)
      rw [Equiv.apply_symm_apply] at h₁
      have h₂ := r₂.edge_comm (r₂.eEquiv.symm i)
      rw [Equiv.apply_symm_apply] at h₂
      rw [h₁, h₂, hv, he]
    · funext i j
      have h₁ := r₁.tet_comm (r₁.tEquiv.symm i) j
      rw [Equiv.apply_symm_apply] at h₁
      have h₂ := r₂.tet_comm (r₂.tEquiv.symm i) j
      rw [Equiv.apply_symm_apply] at h₂
      rw [h₁, h₂, hv, ht]
  subst hK
  exact congrArg (Sigma.mk K₁) (ExactRelabel.ext hv he ht)

/-- **THEOREM (the total torsor).**  The sigma of ALL relabelings out of a
fixed base complex `K` is in bijection with the full relabeling triple
group: every triple acts (pushforward), and every pair `(target, witness)`
comes from exactly one triple. -/
def relabelSigmaEquiv (K : ExactComplex v e t) :
    RelabelTriple v e t ≃ Σ K' : ExactComplex v e t, ExactRelabel K K' where
  toFun σ := ⟨act σ K, actRelabel σ K⟩
  invFun p := p.2.toEquivTriple
  left_inv _ := rfl
  right_inv p := sigma_relabel_ext _ _ rfl rfl rfl

/-! ## §2. Orbit-stabilizer on exact complexes -/

/-- Relabeling witnesses between any two exact complexes form a finite
type (inject into the finite triple of index bijections; generalizes
`instFiniteExactAut` beyond the diagonal). -/
instance instFiniteExactRelabel (K K' : ExactComplex v e t) :
    Finite (ExactRelabel K K') :=
  Finite.of_injective _
    (ExactRelabel.toEquivTriple_injective (K := K) (K' := K'))

/-- **THEOREM (torsor over the automorphism group).**  Fixing one witness
`r0 : ExactRelabel K K'`, composition `a ↦ a.trans r0` is a bijection
`ExactAut K ≃ ExactRelabel K K'` (mirrors
`ExactShellGaugePreflight.torsorEquiv` on the cap-free class). -/
def torsorEquiv {K K' : ExactComplex v e t} (r0 : ExactRelabel K K') :
    ExactAut K ≃ ExactRelabel K K' where
  toFun a := a.trans r0
  invFun r := r.trans r0.symm
  left_inv a := by
    apply ExactRelabel.ext <;>
      · apply Equiv.ext
        intro x
        simp only [ExactRelabel.trans_vEquiv, ExactRelabel.trans_eEquiv,
          ExactRelabel.trans_tEquiv, ExactRelabel.symm_vEquiv,
          ExactRelabel.symm_eEquiv, ExactRelabel.symm_tEquiv,
          Equiv.trans_apply, Equiv.symm_apply_apply]
  right_inv r := by
    apply ExactRelabel.ext <;>
      · apply Equiv.ext
        intro x
        simp only [ExactRelabel.trans_vEquiv, ExactRelabel.trans_eEquiv,
          ExactRelabel.trans_tEquiv, ExactRelabel.symm_vEquiv,
          ExactRelabel.symm_eEquiv, ExactRelabel.symm_tEquiv,
          Equiv.trans_apply, Equiv.apply_symm_apply]

/-- The relabeling orbit size of `K` inside the exact labeled class. -/
noncomputable def orbitCard (K : ExactComplex v e t) : ℕ :=
  Nat.card {K' : ExactComplex v e t // GlobalEquivalent K K'}

/-- Summing witness counts over all targets exhausts the triple group. -/
theorem sum_card_relabel (K : ExactComplex v e t) :
    ∑ K' : ExactComplex v e t, Nat.card (ExactRelabel K K')
      = v.factorial * e.factorial * t.factorial := by
  calc ∑ K' : ExactComplex v e t, Nat.card (ExactRelabel K K')
      = Nat.card (Σ K' : ExactComplex v e t, ExactRelabel K K') :=
        Nat.card_sigma.symm
    _ = Nat.card (RelabelTriple v e t) :=
        Nat.card_congr (relabelSigmaEquiv K).symm
    _ = Fintype.card (RelabelTriple v e t) := Nat.card_eq_fintype_card
    _ = v.factorial * e.factorial * t.factorial := relabelTriple_card v e t

/-- Summing witness counts over all targets factorizes through the orbit:
each on-orbit fiber is an `Aut`-torsor, each off-orbit fiber is empty. -/
theorem sum_card_relabel_eq_orbit (K : ExactComplex v e t) :
    ∑ K' : ExactComplex v e t, Nat.card (ExactRelabel K K')
      = orbitCard K * Nat.card (ExactAut K) := by
  classical
  calc ∑ K' : ExactComplex v e t, Nat.card (ExactRelabel K K')
      = ∑ K' : ExactComplex v e t,
          (if GlobalEquivalent K K' then Nat.card (ExactAut K) else 0) := by
        refine Finset.sum_congr rfl fun K' _ => ?_
        by_cases h : GlobalEquivalent K K'
        · rw [if_pos h]
          obtain ⟨r0⟩ := h
          exact (Nat.card_congr (torsorEquiv r0)).symm
        · rw [if_neg h]
          haveI : IsEmpty (ExactRelabel K K') := ⟨fun r => h ⟨r⟩⟩
          exact Nat.card_of_isEmpty
    _ = ∑ K' ∈ Finset.univ.filter (fun K' => GlobalEquivalent K K'),
          Nat.card (ExactAut K) := (Finset.sum_filter _ _).symm
    _ = (Finset.univ.filter (fun K' => GlobalEquivalent K K')).card
          * Nat.card (ExactAut K) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = orbitCard K * Nat.card (ExactAut K) := by
        congr 1
        show (Finset.univ.filter (fun K' => GlobalEquivalent K K')).card
            = Nat.card {K' : ExactComplex v e t // GlobalEquivalent K K'}
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **THEOREM (orbit-stabilizer, exact form).**  Orbit size times
automorphism count equals the full gauge volume `v!·e!·t!` for EVERY
labeled complex. -/
theorem orbitCard_mul_autCard (K : ExactComplex v e t) :
    orbitCard K * Nat.card (ExactAut K)
      = v.factorial * e.factorial * t.factorial := by
  rw [← sum_card_relabel_eq_orbit K]
  exact sum_card_relabel K

/-! ## §3. The shell-mass identity (Burnside route) -/

/-- The quotient at a fixed signature is a finite type (noncomputable
enumeration; `instFiniteExactQuotient` supplies finiteness). -/
noncomputable instance instFintypeExactQuotient (v e t : ℕ) :
    Fintype (Quotient (exactSetoid v e t)) :=
  Fintype.ofFinite _

/-- The per-class measure at a representative: `classMuOn` evaluated on a
class is `exactMu` of its chosen representative. -/
theorem classMuOn_out (c : Quotient (exactSetoid v e t)) :
    classMuOn v e t c = exactMu (Quotient.out c) := by
  refine Quotient.inductionOn c ?_
  intro K
  change exactMu K =
    exactMu (Quotient.out (Quotient.mk (exactSetoid v e t) K))
  exact (exactMu_congr
    (Quotient.exact
      (Quotient.out_eq (Quotient.mk (exactSetoid v e t) K)))).symm

/-- The fiber of the quotient map over a class has the orbit cardinality
of the class representative. -/
theorem fiber_card (c : Quotient (exactSetoid v e t)) :
    Nat.card {K : ExactComplex v e t //
        Quotient.mk (exactSetoid v e t) K = c}
      = orbitCard (Quotient.out c) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun K => ?_)
  constructor
  · intro hK
    exact Quotient.exact ((Quotient.out_eq c).trans hK.symm)
  · intro hE
    exact (Quotient.sound hE).symm.trans (Quotient.out_eq c)

/-- Orbit sizes over the quotient sum to the labeled count (the orbits
partition the labeled class). -/
theorem sum_orbitCard (v e t : ℕ) :
    ∑ c : Quotient (exactSetoid v e t), orbitCard (Quotient.out c)
      = Fintype.card (ExactComplex v e t) := by
  classical
  have h1 : Nat.card (Σ c : Quotient (exactSetoid v e t),
      {K : ExactComplex v e t // Quotient.mk (exactSetoid v e t) K = c})
      = Fintype.card (ExactComplex v e t) := by
    rw [Nat.card_congr
      (Equiv.sigmaFiberEquiv (Quotient.mk (exactSetoid v e t))),
      Nat.card_eq_fintype_card]
  rw [Nat.card_sigma] at h1
  rw [← h1]
  exact Finset.sum_congr rfl fun c _ => (fiber_card c).symm

/-- **HEADLINE IDENTITY (Burnside / orbit-stabilizer route).**  At every
exact signature, the total per-class measure equals the labeled count
divided by the full gauge volume:
`∑_classes 1/|Aut| = |labeled| / (v!·e!·t!)`. -/
theorem sum_classMuOn_eq_card_div_factorials (v e t : ℕ) :
    ∑ c : Quotient (exactSetoid v e t), classMuOn v e t c
      = (Fintype.card (ExactComplex v e t) : ℝ)
        / ((v.factorial * e.factorial * t.factorial : ℕ) : ℝ) := by
  classical
  have hfactpos : 0 < v.factorial * e.factorial * t.factorial :=
    Nat.mul_pos (Nat.mul_pos v.factorial_pos e.factorial_pos) t.factorial_pos
  have hfactR : (0 : ℝ) < ((v.factorial * e.factorial * t.factorial : ℕ) : ℝ) := by
    exact_mod_cast hfactpos
  rw [eq_div_iff hfactR.ne', Finset.sum_mul]
  have hterm : ∀ c : Quotient (exactSetoid v e t),
      classMuOn v e t c * ((v.factorial * e.factorial * t.factorial : ℕ) : ℝ)
        = (orbitCard (Quotient.out c) : ℝ) := by
    intro c
    have hOS := orbitCard_mul_autCard (Quotient.out c)
    have hautpos : (0 : ℝ) < (Nat.card (ExactAut (Quotient.out c)) : ℝ) := by
      exact_mod_cast exactAutCard_pos (Quotient.out c)
    have hcast : (orbitCard (Quotient.out c) : ℝ)
        * (Nat.card (ExactAut (Quotient.out c)) : ℝ)
        = ((v.factorial * e.factorial * t.factorial : ℕ) : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hOS
    rw [classMuOn_out c]
    unfold exactMu
    rw [div_mul_eq_mul_div, one_mul, ← hcast, mul_div_assoc,
      div_self hautpos.ne', mul_one]
  rw [Finset.sum_congr rfl fun c _ => hterm c, ← Nat.cast_sum]
  exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (sum_orbitCard v e t)

/-! ## §4. Shell-mass divergence -/

/-- The cube signature `(n, n, n)` is a shell signature at level `n`. -/
def cubeSig (n : ℕ) : ShellSig n :=
  ⟨(⟨n, Nat.lt_succ_self n⟩, ⟨n, Nat.lt_succ_self n⟩,
      ⟨n, Nat.lt_succ_self n⟩), by
    show max n (max n n) = n
    rw [max_self, max_self]⟩

/-- Restricting the shell mass to the single cube signature `(n, n, n)`
bounds it from below (all classes carry positive measure). -/
theorem cube_sum_le_shellMass (n : ℕ) :
    ∑ q : Quotient (exactSetoid n n n), classMuOn n n n q ≤ shellMass n := by
  classical
  have himg : ∑ c ∈ Finset.univ.image
        (fun q : Quotient (exactSetoid n n n) =>
          (⟨cubeSig n, q⟩ : ExactPathClass n)),
      classMu c
      = ∑ q : Quotient (exactSetoid n n n),
          classMu (⟨cubeSig n, q⟩ : ExactPathClass n) :=
    Finset.sum_image
      (f := fun c : ExactPathClass n => classMu c)
      (s := (Finset.univ : Finset (Quotient (exactSetoid n n n))))
      (g := fun q : Quotient (exactSetoid n n n) =>
        (⟨cubeSig n, q⟩ : ExactPathClass n))
      (by
        intro q _ q' _ h
        cases h
        rfl)
  calc ∑ q : Quotient (exactSetoid n n n), classMuOn n n n q
      = ∑ q : Quotient (exactSetoid n n n),
          classMu (⟨cubeSig n, q⟩ : ExactPathClass n) :=
        Finset.sum_congr rfl fun q _ => rfl
    _ = ∑ c ∈ Finset.univ.image
          (fun q : Quotient (exactSetoid n n n) =>
            (⟨cubeSig n, q⟩ : ExactPathClass n)),
          classMu c := himg.symm
    _ ≤ ∑ c : ExactPathClass n, classMu c :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun c _ _ => (classMu_pos c).le)
    _ = shellMass n := rfl

/-- **Quantitative shell-mass lower bound.**
`shellMass n ≥ n^(6n)/(n!)³ ≥ n^(3n)`: the labeled entropy of the cube
signature beats its factorial gauge volume. -/
theorem shellMass_lower (n : ℕ) :
    ((n : ℝ)) ^ (3 * n) ≤ shellMass n := by
  have hfact3 : n.factorial * n.factorial * n.factorial ≤ n ^ (3 * n) := by
    have h := Nat.factorial_le_pow n
    calc n.factorial * n.factorial * n.factorial
        ≤ n ^ n * n ^ n * n ^ n := Nat.mul_le_mul (Nat.mul_le_mul h h) h
      _ = n ^ (3 * n) := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
  have hcard : Fintype.card (ExactComplex n n n) = n ^ (6 * n) := by
    rw [exactComplex_card_eq, ← pow_two, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hfactR : (0 : ℝ) < ((n.factorial * n.factorial * n.factorial : ℕ) : ℝ) := by
    exact_mod_cast
      Nat.mul_pos (Nat.mul_pos n.factorial_pos n.factorial_pos) n.factorial_pos
  have hkey : ((n : ℝ)) ^ (3 * n)
      ≤ (Fintype.card (ExactComplex n n n) : ℝ)
        / ((n.factorial * n.factorial * n.factorial : ℕ) : ℝ) := by
    rw [le_div_iff₀ hfactR]
    calc ((n : ℝ)) ^ (3 * n)
          * ((n.factorial * n.factorial * n.factorial : ℕ) : ℝ)
        ≤ ((n : ℝ)) ^ (3 * n) * ((n : ℝ)) ^ (3 * n) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ((n.factorial * n.factorial * n.factorial : ℕ) : ℝ)
              ≤ ((n ^ (3 * n) : ℕ) : ℝ) := by exact_mod_cast hfact3
            _ = ((n : ℝ)) ^ (3 * n) := Nat.cast_pow n (3 * n)
      _ = ((n : ℝ)) ^ (6 * n) := by
          rw [← pow_add]
          congr 1
          omega
      _ = ((n ^ (6 * n) : ℕ) : ℝ) := (Nat.cast_pow n (6 * n)).symm
      _ = (Fintype.card (ExactComplex n n n) : ℝ) := by rw [hcard]
  calc ((n : ℝ)) ^ (3 * n)
      ≤ (Fintype.card (ExactComplex n n n) : ℝ)
          / ((n.factorial * n.factorial * n.factorial : ℕ) : ℝ) := hkey
    _ = ∑ q : Quotient (exactSetoid n n n), classMuOn n n n q :=
        (sum_classMuOn_eq_card_div_factorials n n n).symm
    _ ≤ shellMass n := cube_sum_le_shellMass n

/-- **HEADLINE DIVERGENCE.**  The shell masses are unbounded: for every
real threshold there is a shell whose total `1/|Aut|` mass exceeds it. -/
theorem shellMass_unbounded (C : ℝ) : ∃ n : ℕ, C < shellMass n := by
  obtain ⟨m, hm⟩ := exists_nat_gt C
  refine ⟨max 1 m, ?_⟩
  have hle : ((max 1 m : ℕ) : ℝ) ^ (3 * max 1 m) ≤ shellMass (max 1 m) :=
    shellMass_lower (max 1 m)
  have hselfN : (max 1 m : ℕ) ≤ (max 1 m) ^ (3 * max 1 m) :=
    Nat.le_self_pow (by omega) _
  have hself : ((max 1 m : ℕ) : ℝ) ≤ ((max 1 m : ℕ) : ℝ) ^ (3 * max 1 m) := by
    calc ((max 1 m : ℕ) : ℝ)
        ≤ (((max 1 m) ^ (3 * max 1 m) : ℕ) : ℝ) := by exact_mod_cast hselfN
      _ = ((max 1 m : ℕ) : ℝ) ^ (3 * max 1 m) := Nat.cast_pow _ _
  have hmR : (m : ℝ) ≤ ((max 1 m : ℕ) : ℝ) := by
    exact_mod_cast le_max_right 1 m
  linarith

/-! ## §5. The headline no-go: regulator removal fails at zero phase -/

/-- **Single-shell lower bound.**  At zero phase every regulated term is
real and nonnegative, so any single shell bounds the real part of the
regulated path sum from below. -/
theorem single_shell_re_lower_bound (ρ : ℝ) (hρ : 0 < ρ) (n₀ : ℕ) :
    Real.exp (-ρ * (n₀ : ℝ) ^ 2) * shellMass n₀
      ≤ (Z_RS_uv ρ zeroPhase).re := by
  have hsC : Summable
      (fun n : ℕ => ((Real.exp (-ρ * (n : ℝ) ^ 2) * shellMass n : ℝ) : ℂ)) :=
    (summable_zRSUVShell ρ hρ zeroPhase).congr
      (fun n => zRSUVShell_zeroPhase_eq ρ n)
  have hsR : Summable
      (fun n : ℕ => Real.exp (-ρ * (n : ℝ) ^ 2) * shellMass n) :=
    Complex.summable_ofReal.mp hsC
  have hZ : Z_RS_uv ρ zeroPhase =
      ((∑' n : ℕ, Real.exp (-ρ * (n : ℝ) ^ 2) * shellMass n : ℝ) : ℂ) := by
    unfold Z_RS_uv
    rw [tsum_congr (fun n => zRSUVShell_zeroPhase_eq ρ n),
      ← Complex.ofReal_tsum]
  rw [hZ, Complex.ofReal_re]
  exact hsR.le_tsum n₀
    (fun j _ => (mul_pos (Real.exp_pos _) (shellMass_pos j)).le)

/-- **HEADLINE (kernel no-go).**  Regulator removal FAILS at zero phase:
the Gaussian-regulated quotient path sum `Z_RS_uv ρ zeroPhase` has NO
limit as `ρ → 0⁺`.  Mechanism: any putative limit `L` is beaten by a
single shell of mass `> L.re + 2` (shell masses diverge), whose regulated
contribution tends to its full mass as the regulator is removed. -/
theorem not_hasZRSRegulatorRemoval_zeroPhase :
    ¬ HasZRSRegulatorRemoval zeroPhase := by
  rintro ⟨L, hL⟩
  have hre : Filter.Tendsto (fun ρ : ℝ => (Z_RS_uv ρ zeroPhase).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L.re) :=
    (Complex.continuous_re.tendsto L).comp hL
  obtain ⟨n₀, hn₀⟩ := shellMass_unbounded (L.re + 2)
  have hexp : Filter.Tendsto
      (fun ρ : ℝ => Real.exp (-ρ * (n₀ : ℝ) ^ 2) * shellMass n₀)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (shellMass n₀)) := by
    refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
    refine Continuous.tendsto' ?_ 0 (shellMass n₀) ?_
    · exact (Real.continuous_exp.comp
        (continuous_neg.mul continuous_const)).mul continuous_const
    · simp only [neg_zero, zero_mul, Real.exp_zero, one_mul]
  have hev1 : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      L.re + 1 < Real.exp (-ρ * (n₀ : ℝ) ^ 2) * shellMass n₀ :=
    hexp.eventually_const_lt (by linarith)
  have hev2 : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (Z_RS_uv ρ zeroPhase).re < L.re + 1 :=
    hre.eventually_lt_const (by linarith)
  have hev3 : ∀ᶠ ρ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ρ ∈ Set.Ioi (0 : ℝ) :=
    eventually_mem_nhdsWithin
  obtain ⟨ρ, ⟨h1, h2⟩, h3⟩ := ((hev1.and hev2).and hev3).exists
  have h4 := single_shell_re_lower_bound ρ (Set.mem_Ioi.mp h3) n₀
  linarith

/-! ## §6. Status record (honest boundary) -/

/-- **NAMED OPEN (definition only, NEVER claimed).**  Whether regulator
removal holds for SOME phase (in particular, for a genuine oscillatory
action phase whose cancellations could tame the diverging shell masses).
The zero-phase refutation above does NOT decide this: its lower-bound
argument uses positivity, which oscillation destroys.  No theorem in this
module asserts or refutes this Prop. -/
def OscillatoryRemovalOpen : Prop :=
  ∃ phase : ∀ n : ℕ, ExactPathClass n → ℝ, HasZRSRegulatorRemoval phase

/-- Status of the regulator-removal no-go module.  Every `true` flag is
grounded in its kernel theorem by `regulatorRemovalNoGoStatus_grounded`;
`oscillatory_removal_open` records the honest OPEN boundary (the nonzero-
phase question, `OscillatoryRemovalOpen`, is a definition-level Prop with
no claim).  This module flips NO `FullTheoryLedger` or `CampaignLedger`
flag. -/
structure RegulatorRemovalNoGoStatus where
  /-- §3: `sum_classMuOn_eq_card_div_factorials` (Burnside identity). -/
  shell_mass_identity_proved : Bool
  /-- §4: `shellMass_unbounded` (via `shellMass_lower`). -/
  shell_mass_divergence_proved : Bool
  /-- §5: `not_hasZRSRegulatorRemoval_zeroPhase`. -/
  zero_phase_removal_refuted : Bool
  /-- §6: `OscillatoryRemovalOpen` is a NAMED OPEN definition; MUST stay
  `true` (open) until a kernel proof or refutation for nonzero phases
  exists. -/
  oscillatory_removal_open : Bool

/-- The canonical status record. -/
def regulatorRemovalNoGoStatus : RegulatorRemovalNoGoStatus where
  shell_mass_identity_proved := true
  shell_mass_divergence_proved := true
  zero_phase_removal_refuted := true
  oscillatory_removal_open := true

/-- **Grounding theorem.**  The status flags are not bare Booleans: each
`true` proof flag is tied to its kernel theorem, and the OPEN flag is
recorded without any claim on `OscillatoryRemovalOpen`. -/
theorem regulatorRemovalNoGoStatus_grounded :
    (regulatorRemovalNoGoStatus.shell_mass_identity_proved = true ∧
      ∀ v e t : ℕ, ∑ c : Quotient (exactSetoid v e t), classMuOn v e t c
        = (Fintype.card (ExactComplex v e t) : ℝ)
          / ((v.factorial * e.factorial * t.factorial : ℕ) : ℝ)) ∧
    (regulatorRemovalNoGoStatus.shell_mass_divergence_proved = true ∧
      ∀ C : ℝ, ∃ n : ℕ, C < shellMass n) ∧
    (regulatorRemovalNoGoStatus.zero_phase_removal_refuted = true ∧
      ¬ HasZRSRegulatorRemoval zeroPhase) ∧
    regulatorRemovalNoGoStatus.oscillatory_removal_open = true :=
  ⟨⟨rfl, sum_classMuOn_eq_card_div_factorials⟩,
    ⟨rfl, shellMass_unbounded⟩,
    ⟨rfl, not_hasZRSRegulatorRemoval_zeroPhase⟩, rfl⟩

end RegulatorRemovalNoGo
end SevenGaps
end Gravity
end IndisputableMonolith
