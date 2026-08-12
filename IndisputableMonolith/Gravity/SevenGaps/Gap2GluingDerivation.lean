import IndisputableMonolith.Gravity.SevenGaps.Gap2GaugeVolume

/-!
# Gap 2: deriving the gluing law instead of assuming it

`Gap2GaugeVolume` §6d proves that a gluing law forces the inverse factorial and
hence implies the gauge-counting principle.  The gluing law was assumed there.
This module attempts to derive it, following the route the 2026-07-28 adversarial
panel's judge selected as the only candidate that closes rather than relocates.

The route needs a disjoint union on the carrier, which `MeasureInvarianceNoGo`
explicitly records as missing ("the existing `BoundedComplex` machinery carries no
disjoint-union operation to state it against").  §1 supplies it.

## The shape of the derivation

Two premises, neither mentioning `mu`, `Aut`, factorials, or the counting
principle:

* **(i) size-blindness**: the labeled weight depends only on the three index
  sizes.  This, and not independence, is what excludes the known decoy
  `1/orbitCard`, whose class mass is identically one and is therefore trivially
  multiplicative.
* **(ii) gluing multiplicativity**: class mass multiplies over disjoint unions.

Given those, the *orbit counts* supply a binomial interleaving factor on their
own, and cancelling them turns (ii) into the three-variable shuffle identity,
whose solutions are `f(a,b,c) = x^a y^b z^c / (a! b! c!)`.  So the premise is
reduced from a normalization to a locality statement plus three couplings.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2GluingDerivation

open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume

/-! ## §1. Disjoint union on the carrier

The union of a `BoundedComplex B` and a `BoundedComplex B'` lives at cap `B + B'`.
Index sets add, and the incidence maps are the two originals pushed into the two
halves of the summed index sets by `finSumFinEquiv`. -/

/-- Push a vertex of the left summand into the union's vertex set. -/
abbrev inlV {m n : ℕ} (i : Fin m) : Fin (m + n) := finSumFinEquiv (Sum.inl i)

/-- Push a vertex of the right summand into the union's vertex set. -/
abbrev inrV {m n : ℕ} (i : Fin n) : Fin (m + n) := finSumFinEquiv (Sum.inr i)

/-- The **disjoint union** of two bounded complexes, at the summed cap. -/
def dunion {B B' : ℕ} (K : BoundedComplex B) (L : BoundedComplex B') :
    BoundedComplex (B + B') where
  nV := K.nV + L.nV
  nE := K.nE + L.nE
  nT := K.nT + L.nT
  hV := Nat.add_le_add K.hV L.hV
  hE := Nat.add_le_add K.hE L.hE
  hT := Nat.add_le_add K.hT L.hT
  edgeVerts := fun e =>
    Sum.elim
      (fun e' : Fin K.nE => (inlV (K.edgeVerts e').1, inlV (K.edgeVerts e').2))
      (fun e' : Fin L.nE => (inrV (L.edgeVerts e').1, inrV (L.edgeVerts e').2))
      (finSumFinEquiv.symm e)
  tetVerts := fun t i =>
    Sum.elim
      (fun t' : Fin K.nT => inlV (K.tetVerts t' i))
      (fun t' : Fin L.nT => inrV (L.tetVerts t' i))
      (finSumFinEquiv.symm t)

@[simp] theorem dunion_nV {B B' : ℕ} (K : BoundedComplex B) (L : BoundedComplex B') :
    (dunion K L).nV = K.nV + L.nV := rfl

@[simp] theorem dunion_nE {B B' : ℕ} (K : BoundedComplex B) (L : BoundedComplex B') :
    (dunion K L).nE = K.nE + L.nE := rfl

@[simp] theorem dunion_nT {B B' : ℕ} (K : BoundedComplex B) (L : BoundedComplex B') :
    (dunion K L).nT = K.nT + L.nT := rfl

/-! ## §2. The gauge volume of a union, and where the binomial comes from

This is pure factorial arithmetic and it is the reason the interleaving count is
binomial: the gauge volume of the union exceeds the product of the parts' gauge
volumes by exactly the three binomial coefficients counting how the label blocks
can be interleaved. -/

/-- The three-way interleaving count for a pair of size triples. -/
def interleave (a b c a' b' c' : ℕ) : ℕ :=
  Nat.choose (a + a') a * (Nat.choose (b + b') b * Nat.choose (c + c') c)

/-- The gauge volume of a size triple. -/
def gaugeVol (a b c : ℕ) : ℕ :=
  Nat.factorial a * (Nat.factorial b * Nat.factorial c)

/-- **THEOREM (the interleaving count is binomial).**  The gauge volume of a sum
of size triples is the interleaving count times the product of the parts' gauge
volumes.  Pure arithmetic, no complexes involved. -/
theorem gaugeVol_add (a b c a' b' c' : ℕ) :
    gaugeVol (a + a') (b + b') (c + c')
      = interleave a b c a' b' c' * (gaugeVol a b c * gaugeVol a' b' c') := by
  have key : ∀ m n : ℕ,
      Nat.factorial (m + n)
        = Nat.choose (m + n) m * (Nat.factorial m * Nat.factorial n) := by
    intro m n
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n)
    have hsub : m + n - m = n := Nat.add_sub_cancel_left m n
    rw [hsub] at h
    rw [← h, mul_assoc]
  unfold gaugeVol interleave
  rw [key a a', key b b', key c c']
  ring

/-- The gauge volume of a union, in the module's own terms. -/
theorem gaugeVol_dunion {B B' : ℕ} (K : BoundedComplex B) (L : BoundedComplex B') :
    gaugeVol (dunion K L).nV (dunion K L).nE (dunion K L).nT
      = interleave K.nV K.nE K.nT L.nV L.nE L.nT
        * (gaugeVol K.nV K.nE K.nT * gaugeVol L.nV L.nE L.nT) := by
  simp only [dunion_nV, dunion_nE, dunion_nT]
  exact gaugeVol_add _ _ _ _ _ _

/-- `pairCount` is the gauge volume of the index sizes, in the notation of this
module. -/
theorem pairCount_eq_gaugeVol {B : ℕ} (K : BoundedComplex B) :
    pairCount K = gaugeVol K.nV K.nE K.nT :=
  pairCount_eq_factorials K

/-- The interleaving count is positive. -/
theorem interleave_pos (a b c a' b' c' : ℕ) : 0 < interleave a b c a' b' c' := by
  unfold interleave
  have h1 : 0 < Nat.choose (a + a') a := Nat.choose_pos (Nat.le_add_right a a')
  have h2 : 0 < Nat.choose (b + b') b := Nat.choose_pos (Nat.le_add_right b b')
  have h3 : 0 < Nat.choose (c + c') c := Nat.choose_pos (Nat.le_add_right c c')
  positivity

/-- The gauge volume is positive. -/
theorem gaugeVol_pos (a b c : ℕ) : 0 < gaugeVol a b c := by
  unfold gaugeVol
  have := Nat.factorial_pos a
  have := Nat.factorial_pos b
  have := Nat.factorial_pos c
  positivity

/-! ## §3. Dust, and the refutation of unrestricted gluing multiplicativity

Before using premise (ii) it must be checked against the intended answer.  It
fails.  `dust n` is `n` isolated vertices; its automorphism group is the full
symmetric group, so `mu (dust n) = 1/n!`, while dust glues to dust.  Unrestricted
multiplicativity would demand `1/(a+b)! = 1/a! · 1/b!`, which is false as soon as
both parts are nonempty.  So premise (ii) is not a free lunch: it must carry a
side condition excluding repeated isomorphic pieces, and that side condition is
mandatory rather than a convenience. -/

/-- `n` isolated vertices: no edges, no tetrahedra. -/
def dust (n : ℕ) : BoundedComplex n where
  nV := n
  nE := 0
  nT := 0
  hV := le_refl n
  hE := Nat.zero_le n
  hT := Nat.zero_le n
  edgeVerts := Fin.elim0
  tetVerts := Fin.elim0

@[simp] theorem dust_nV (n : ℕ) : (dust n).nV = n := rfl
@[simp] theorem dust_nE (n : ℕ) : (dust n).nE = 0 := rfl
@[simp] theorem dust_nT (n : ℕ) : (dust n).nT = 0 := rfl

/-- **The automorphism group of dust is the full symmetric group.**  With no
incidence data, both commutation conditions are vacuous, so every vertex
permutation is an automorphism. -/
def autDustEquiv (n : ℕ) : Aut (dust n) ≃ Equiv.Perm (Fin n) where
  toFun := fun r => r.vEquiv
  invFun := fun v =>
    { vEquiv := v
      eEquiv := Equiv.refl _
      tEquiv := Equiv.refl _
      edge_comm := fun e => Fin.elim0 e
      tet_comm := fun t _ => Fin.elim0 t }
  left_inv := by
    intro r
    have he : r.eEquiv = Equiv.refl (Fin (dust n).nE) := Equiv.ext fun e => Fin.elim0 e
    have ht : r.tEquiv = Equiv.refl (Fin (dust n).nT) := Equiv.ext fun t => Fin.elim0 t
    cases r
    simp_all
  right_inv := by intro v; rfl

/-- `|Aut (dust n)| = n!`. -/
theorem autCard_dust (n : ℕ) : Nat.card (Aut (dust n)) = Nat.factorial n := by
  rw [Nat.card_congr (autDustEquiv n), Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]

/-- The RS measure on dust is the reciprocal factorial. -/
theorem mu_dust (n : ℕ) : mu (dust n) = 1 / (Nat.factorial n : ℝ) := by
  unfold mu
  rw [autCard_dust]

/-- Dust glues to dust: the union of `a` and `b` isolated vertices is `a + b`
isolated vertices. -/
def dunionDustRelabel (a b : ℕ) : Relabel (dunion (dust a) (dust b)) (dust (a + b)) where
  vEquiv := Equiv.refl _
  eEquiv := Equiv.refl _
  tEquiv := Equiv.refl _
  edge_comm := fun e => Fin.elim0 e
  tet_comm := fun t _ => Fin.elim0 t

theorem dunion_dust_equivalent (a b : ℕ) :
    Equivalent (dunion (dust a) (dust b)) (dust (a + b)) :=
  ⟨dunionDustRelabel a b⟩

/-- **THEOREM (unrestricted gluing multiplicativity is FALSE).**  There is no
version of premise (ii) that applies to every disjoint union, because the
intended answer `mu` itself violates it.  Witness: one vertex glued to one
vertex.  `mu` of the union is `1/2`; the product of the parts' `mu` is `1`. -/
theorem unrestricted_gluing_multiplicativity_false :
    ¬ (∀ (B B' : ℕ) (K : BoundedComplex B) (L : BoundedComplex B'),
        mu (dunion K L) = mu K * mu L) := by
  intro h
  have hd := h 1 1 (dust 1) (dust 1)
  rw [mu_congr (dunion_dust_equivalent 1 1)] at hd
  rw [mu_dust, mu_dust] at hd
  norm_num at hd

/-- The same failure, quantified: `mu` of a dust union undershoots the product of
the parts by exactly the interleaving count, which is the binomial coefficient.
This is the extra symmetry that repeated isomorphic pieces create. -/
theorem mu_dust_union_off_by_binomial (a b : ℕ) :
    mu (dunion (dust a) (dust b)) * (Nat.choose (a + b) a : ℝ)
      = mu (dust a) * mu (dust b) := by
  rw [mu_congr (dunion_dust_equivalent a b), mu_dust, mu_dust, mu_dust]
  have hfac : (Nat.factorial (a + b) : ℝ)
      = (Nat.choose (a + b) a : ℝ) * ((Nat.factorial a : ℝ) * (Nat.factorial b : ℝ)) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
    have hsub : a + b - a = b := Nat.add_sub_cancel_left a b
    rw [hsub] at h
    have : ((Nat.choose (a + b) a * Nat.factorial a * Nat.factorial b : ℕ) : ℝ)
        = ((Nat.factorial (a + b) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith [this]
  rw [hfac]
  have hca : (0 : ℝ) < (Nat.choose (a + b) a : ℝ) := by
    have := Nat.choose_pos (Nat.le_add_right a b)
    exact_mod_cast this
  have ha : (0 : ℝ) < (Nat.factorial a : ℝ) := by
    have := Nat.factorial_pos a; exact_mod_cast this
  have hb : (0 : ℝ) < (Nat.factorial b : ℝ) := by
    have := Nat.factorial_pos b; exact_mod_cast this
  field_simp

/-! ## §4. What the interleaving count is, at the level of orbit counts

Kill condition 1 of the pre-registered gate asks whether the interleaving count is
binomial.  §2 settles that for the gauge volume unconditionally.  Transporting it
to orbit counts costs exactly one thing: multiplicativity of the automorphism
count.  This section proves the transport, so the residue is isolated to a single
identity about `Aut`. -/

/-- **THEOREM (the interleaving count is binomial, given `Aut` multiplicativity).**
If the automorphism count multiplies over a union, the orbit counts satisfy the
binomial interleaving identity.  No other hypothesis. -/
theorem orbitCard_dunion_of_autMul {B B' : ℕ}
    (K : BoundedComplex B) (L : BoundedComplex B')
    (haut : Nat.card (Aut (dunion K L)) = Nat.card (Aut K) * Nat.card (Aut L)) :
    gaugeOrbitCard (dunion K L)
      = interleave K.nV K.nE K.nT L.nV L.nE L.nT
        * (gaugeOrbitCard K * gaugeOrbitCard L) := by
  have hU : pairCount (dunion K L)
      = gaugeOrbitCard (dunion K L) * Nat.card (Aut (dunion K L)) :=
    pairCount_eq_orbitCard_mul_autCard _
  have hK : pairCount K = gaugeOrbitCard K * Nat.card (Aut K) :=
    pairCount_eq_orbitCard_mul_autCard _
  have hL : pairCount L = gaugeOrbitCard L * Nat.card (Aut L) :=
    pairCount_eq_orbitCard_mul_autCard _
  have hvol : pairCount (dunion K L)
      = interleave K.nV K.nE K.nT L.nV L.nE L.nT * (pairCount K * pairCount L) := by
    rw [pairCount_eq_gaugeVol, pairCount_eq_gaugeVol, pairCount_eq_gaugeVol]
    exact gaugeVol_dunion K L
  rw [hU, haut, hK, hL] at hvol
  have hpos : 0 < Nat.card (Aut K) * Nat.card (Aut L) :=
    Nat.mul_pos (autCard_pos K) (autCard_pos L)
  have hcancel : gaugeOrbitCard (dunion K L) * (Nat.card (Aut K) * Nat.card (Aut L))
      = (interleave K.nV K.nE K.nT L.nV L.nE L.nT
          * (gaugeOrbitCard K * gaugeOrbitCard L))
        * (Nat.card (Aut K) * Nat.card (Aut L)) := by
    rw [hvol]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos hcancel

/-! ## §5. Premise (i): size-blindness, and the transport to a shuffle identity -/

/-- **Premise (i), size-blindness.**  A single function of the three index sizes,
used as the labeled weight at every cap.  Nothing here mentions `mu`, `Aut`,
factorials, or the counting principle. -/
def sizeWeight (f : ℕ → ℕ → ℕ → ℝ) {B : ℕ} (K : BoundedComplex B) : ℝ :=
  f K.nV K.nE K.nT

/-- A size-blind weight is relabeling-invariant, since a relabeling preserves the
three index sizes. -/
theorem sizeWeight_invariant (f : ℕ → ℕ → ℕ → ℝ) {B : ℕ} {K K' : BoundedComplex B}
    (h : Equivalent K K') : sizeWeight f K = sizeWeight f K' := by
  obtain ⟨r⟩ := h
  unfold sizeWeight
  rw [size_v r, size_e r, size_t r]

/-- The class mass of a size-blind weight is the orbit count times the size value.
This is where the orbit counts enter, and they are the only thing that does. -/
theorem classMass_sizeWeight (f : ℕ → ℕ → ℕ → ℝ) {B : ℕ} (K : BoundedComplex B) :
    classMass (sizeWeight f) (Quotient.mk (relabelSetoid B) K)
      = (gaugeOrbitCard K : ℝ) * f K.nV K.nE K.nT := by
  rw [classMass_of_invariant _ (fun _ _ h => sizeWeight_invariant f h)]
  have hout : sizeWeight f (Quotient.out (Quotient.mk (relabelSetoid B) K))
      = sizeWeight f K :=
    sizeWeight_invariant f (equivalent_out K)
  rw [hout, orbitCardClass_mk]
  rfl

/-- **Premise (ii), gluing multiplicativity, at one pair.**  The class mass of a
union is the product of the parts' class masses.  Stated with no reference to
`mu`, `Aut`, factorials, the gauge volume, or the counting principle: only the
class mass of the size-blind weight and the disjoint union. -/
def GluesAt (f : ℕ → ℕ → ℕ → ℝ) {B B' : ℕ}
    (K : BoundedComplex B) (L : BoundedComplex B') : Prop :=
  classMass (sizeWeight f) (Quotient.mk (relabelSetoid (B + B')) (dunion K L))
    = classMass (sizeWeight f) (Quotient.mk (relabelSetoid B) K)
      * classMass (sizeWeight f) (Quotient.mk (relabelSetoid B') L)

/-- **THEOREM (the transport).**  At any pair where the automorphism count
multiplies, premise (ii) for a size-blind weight is *exactly* the shuffle identity
on the size function.  The orbit counts cancel; their entire contribution is the
binomial interleaving factor.  This is the step that converts a locality premise
into a normalization identity, and it is where the compiled arithmetic of §2 and
§4 is spent. -/
theorem shuffle_of_gluesAt (f : ℕ → ℕ → ℕ → ℝ) {B B' : ℕ}
    (K : BoundedComplex B) (L : BoundedComplex B')
    (haut : Nat.card (Aut (dunion K L)) = Nat.card (Aut K) * Nat.card (Aut L))
    (hglue : GluesAt f K L) :
    f (K.nV + L.nV) (K.nE + L.nE) (K.nT + L.nT)
        * (interleave K.nV K.nE K.nT L.nV L.nE L.nT : ℝ)
      = f K.nV K.nE K.nT * f L.nV L.nE L.nT := by
  have hob := orbitCard_dunion_of_autMul K L haut
  unfold GluesAt at hglue
  rw [classMass_sizeWeight, classMass_sizeWeight, classMass_sizeWeight] at hglue
  simp only [dunion_nV, dunion_nE, dunion_nT] at hglue
  rw [hob] at hglue
  push_cast at hglue
  have hK : (0 : ℝ) < (gaugeOrbitCard K : ℝ) := by
    exact_mod_cast gaugeOrbitCard_pos K
  have hL : (0 : ℝ) < (gaugeOrbitCard L : ℝ) := by
    exact_mod_cast gaugeOrbitCard_pos L
  have hprod : (gaugeOrbitCard K : ℝ) * (gaugeOrbitCard L : ℝ) ≠ 0 :=
    (mul_pos hK hL).ne'
  refine mul_right_cancel₀ hprod ?_
  calc f (K.nV + L.nV) (K.nE + L.nE) (K.nT + L.nT)
        * (interleave K.nV K.nE K.nT L.nV L.nE L.nT : ℝ)
        * ((gaugeOrbitCard K : ℝ) * (gaugeOrbitCard L : ℝ))
      = (interleave K.nV K.nE K.nT L.nV L.nE L.nT : ℝ)
          * ((gaugeOrbitCard K : ℝ) * (gaugeOrbitCard L : ℝ))
          * f (K.nV + L.nV) (K.nE + L.nE) (K.nT + L.nT) := by ring
    _ = (gaugeOrbitCard K : ℝ) * f K.nV K.nE K.nT
          * ((gaugeOrbitCard L : ℝ) * f L.nV L.nE L.nT) := hglue
    _ = f K.nV K.nE K.nT * f L.nV L.nE L.nT
          * ((gaugeOrbitCard K : ℝ) * (gaugeOrbitCard L : ℝ)) := by ring

/-! ## §6. What the two premises force

The premise supplies the shuffle identity only at pairs the carrier can realize
with non-mixing automorphisms.  §3 proves this restriction is mandatory.  Four
families suffice, and each is a union of two complexes sharing no isomorphic
component:

* `dust a` glued to a **bouquet**: one vertex carrying `b` loops and `c`
  degenerate tetrahedra, with at least one incidence.  The bouquet vertex has an
  incidence and the dust vertices do not, so no automorphism exchanges them.
* `dust a` glued to a single **edge**.
* a bouquet glued to a single **edge** (one vertex versus two).
* a bouquet glued to a single **tetrahedron** (one vertex versus four).

Nothing below mentions `mu`, `Aut`, factorials, or the counting principle: the
input is four instances of premise (ii) transported through
`shuffle_of_gluesAt`. -/

/-- Two times a middle binomial, in closed form.  Needed because the dust-edge
instance carries `C(a+2, a)` rather than a linear factor. -/
theorem two_mul_choose (a : ℕ) : 2 * Nat.choose (a + 2) a = (a + 2) * (a + 1) := by
  have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + 2 by omega)
  have h2 : a + 2 - a = 2 := by omega
  rw [h2] at h
  have hf : Nat.factorial (a + 2) = (a + 2) * ((a + 1) * Nat.factorial a) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
  rw [hf] at h
  have hfac : Nat.factorial 2 = 2 := rfl
  rw [hfac] at h
  have hcancel : (2 * Nat.choose (a + 2) a) * Nat.factorial a
      = ((a + 2) * (a + 1)) * Nat.factorial a := by
    calc (2 * Nat.choose (a + 2) a) * Nat.factorial a
        = Nat.choose (a + 2) a * Nat.factorial a * 2 := by ring
      _ = (a + 2) * ((a + 1) * Nat.factorial a) := h
      _ = ((a + 2) * (a + 1)) * Nat.factorial a := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos a) hcancel

@[simp] theorem interleave_pt (a b c : ℕ) : interleave a 0 0 1 b c = a + 1 := by
  unfold interleave
  simp

@[simp] theorem interleave_edge (a : ℕ) : interleave a 0 0 2 1 0 = Nat.choose (a + 2) a := by
  unfold interleave
  simp

@[simp] theorem interleave_bqEdge (b c : ℕ) : interleave 1 b c 2 1 0 = 3 * (b + 1) := by
  unfold interleave
  simp [Nat.choose_one_right]

@[simp] theorem interleave_bqTet (b c : ℕ) : interleave 1 b c 4 0 1 = 5 * (c + 1) := by
  unfold interleave
  simp [Nat.choose_one_right]

/-- **The four gluing instances the carrier supplies**, written purely as
identities on the size function.  Each is premise (ii) at one family of pairs,
already transported through `shuffle_of_gluesAt`. -/
structure CarrierShuffle (f : ℕ → ℕ → ℕ → ℝ) : Prop where
  /-- A weight is a positive number. -/
  pos : ∀ a b c, 0 < f a b c
  /-- The empty complex has unit weight (the normalization of the sum). -/
  unit : f 0 0 0 = 1
  /-- `dust a ⊔ bouquet(b,c)`, the bouquet carrying at least one incidence. -/
  dust_bouquet : ∀ a b c, 1 ≤ b + c →
    f (a + 1) b c * (interleave a 0 0 1 b c : ℝ) = f a 0 0 * f 1 b c
  /-- `dust a ⊔ edge`. -/
  dust_edge : ∀ a,
    f (a + 2) 1 0 * (interleave a 0 0 2 1 0 : ℝ) = f a 0 0 * f 2 1 0
  /-- `bouquet(b,c) ⊔ edge`. -/
  bouquet_edge : ∀ b c,
    f 3 (b + 1) c * (interleave 1 b c 2 1 0 : ℝ) = f 1 b c * f 2 1 0
  /-- `bouquet(b,c) ⊔ tetrahedron`. -/
  bouquet_tet : ∀ b c,
    f 5 b (c + 1) * (interleave 1 b c 4 0 1 : ℝ) = f 1 b c * f 4 0 1

namespace CarrierShuffle

variable {f : ℕ → ℕ → ℕ → ℝ}

/-- The single-edge weight, from the loop-plus-point realization of the same size
triple.  This is the step where size-blindness does real work: the size triple
`(2,1,0)` is realized both by the indecomposable edge and by the decomposable
`loop ⊔ point`, and premise (i) identifies them. -/
theorem edgeWeight (h : CarrierShuffle f) : f 2 1 0 * 2 = f 1 0 0 * f 1 1 0 := by
  have hd := h.dust_bouquet 1 1 0 (by omega)
  rw [interleave_pt] at hd
  push_cast at hd
  linarith [hd]

/-- **The vertex recursion.**  Adding one isolated vertex divides the weight by the
new vertex count.  Derived from the dust-bouquet and dust-edge instances; the
binomial `C(a+2,a)` cancels against the linear factors. -/
theorem vertexRec (h : CarrierShuffle f) (a : ℕ) :
    f (a + 1) 0 0 * ((a : ℝ) + 1) = f a 0 0 * f 1 0 0 := by
  have hP1 := h.dust_bouquet (a + 1) 1 0 (by omega)
  rw [interleave_pt] at hP1
  have hQ := h.dust_edge a
  rw [interleave_edge] at hQ
  have hR := edgeWeight h
  have hC : (2 : ℝ) * (Nat.choose (a + 2) a : ℝ) = ((a : ℝ) + 2) * ((a : ℝ) + 1) := by
    have := two_mul_choose a
    have hcast : ((2 * Nat.choose (a + 2) a : ℕ) : ℝ) = (((a + 2) * (a + 1) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
    push_cast at hcast
    linarith [hcast]
  push_cast at hP1
  have hq : f 1 1 0 ≠ 0 := (h.pos 1 1 0).ne'
  refine mul_right_cancel₀ hq ?_
  linear_combination (-((a : ℝ) + 1)) * hP1 + (-(f (a + 2) 1 0)) * hC + 2 * hQ
    + (f a 0 0) * hR

/-- **The dust row.**  Iterating the vertex recursion: `f(a,0,0) · a! = x^a`. -/
theorem dustRow (h : CarrierShuffle f) (a : ℕ) :
    f a 0 0 * (Nat.factorial a : ℝ) = (f 1 0 0) ^ a := by
  induction a with
  | zero => simpa using h.unit
  | succ n ih =>
      have hv := vertexRec h n
      have hfac : (Nat.factorial (n + 1) : ℝ)
          = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      calc f (n + 1) 0 0 * (Nat.factorial (n + 1) : ℝ)
          = (f (n + 1) 0 0 * ((n : ℝ) + 1)) * (Nat.factorial n : ℝ) := by
            rw [hfac]; ring
        _ = (f n 0 0 * f 1 0 0) * (Nat.factorial n : ℝ) := by rw [hv]
        _ = (f n 0 0 * (Nat.factorial n : ℝ)) * f 1 0 0 := by ring
        _ = (f 1 0 0) ^ n * f 1 0 0 := by rw [ih]
        _ = (f 1 0 0) ^ (n + 1) := by ring

/-- **The edge recursion.**  Adding one loop to a bouquet divides by the new edge
count, with the edge fugacity `f(1,1,0)/f(1,0,0)` as the ratio. -/
theorem bRec (h : CarrierShuffle f) (b c : ℕ) :
    f 1 (b + 1) c * ((b : ℝ) + 1) * f 1 0 0 = f 1 b c * f 1 1 0 := by
  have hi := h.bouquet_edge b c
  rw [interleave_bqEdge] at hi
  have hii := h.dust_bouquet 2 (b + 1) c (by omega)
  rw [interleave_pt] at hii
  have hiii : f 2 0 0 * 2 = (f 1 0 0) ^ 2 := by
    have := dustRow h 2
    have hf2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [hf2] at this
    linarith [this]
  have hiv := edgeWeight h
  push_cast at hi hii
  have hx : f 1 0 0 ≠ 0 := (h.pos 1 0 0).ne'
  refine mul_right_cancel₀ hx ?_
  linear_combination (-(f 1 (b + 1) c * ((b : ℝ) + 1))) * hiii
    + (-2 * ((b : ℝ) + 1)) * hii + 2 * hi + (f 1 b c) * hiv

/-- The four-vertex tetrahedron weight, from the point-plus-tetrahedron
realization. -/
theorem tetWeight (h : CarrierShuffle f) : f 4 0 1 * 4 = f 3 0 0 * f 1 0 1 := by
  have hd := h.dust_bouquet 3 0 1 (by omega)
  rw [interleave_pt] at hd
  push_cast at hd
  linarith [hd]

/-- **The tetrahedron recursion.**  Adding one degenerate tetrahedron to a bouquet
divides by the new tetrahedron count, with fugacity `f(1,0,1)/f(1,0,0)`. -/
theorem cRec (h : CarrierShuffle f) (b c : ℕ) :
    f 1 b (c + 1) * ((c : ℝ) + 1) * f 1 0 0 = f 1 b c * f 1 0 1 := by
  have hi := h.bouquet_tet b c
  rw [interleave_bqTet] at hi
  have hii := h.dust_bouquet 4 b (c + 1) (by omega)
  rw [interleave_pt] at hii
  have hiii := tetWeight h
  have hF3 : f 3 0 0 * 6 = (f 1 0 0) ^ 3 := by
    have := dustRow h 3
    have hf3 : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [hf3] at this
    linarith [this]
  have hF4 : f 4 0 0 * 24 = (f 1 0 0) ^ 4 := by
    have := dustRow h 4
    have hf4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf4] at this
    linarith [this]
  push_cast at hi hii
  have hx3 : (f 1 0 0) ^ 3 ≠ 0 := pow_ne_zero _ (h.pos 1 0 0).ne'
  refine mul_right_cancel₀ hx3 ?_
  linear_combination (-(f 1 b (c + 1) * ((c : ℝ) + 1))) * hF4
    + (-24 * ((c : ℝ) + 1)) * hii + 24 * hi + (6 * f 1 b c) * hiii
    + (f 1 b c * f 1 0 1) * hF3

/-- The bouquet column: iterating the tetrahedron recursion at `b = 0`. -/
theorem bouquetTetCol (h : CarrierShuffle f) (c : ℕ) :
    f 1 0 c * (Nat.factorial c : ℝ) * (f 1 0 0) ^ c
      = f 1 0 0 * (f 1 0 1) ^ c := by
  induction c with
  | zero => simp
  | succ n ih =>
      have hc := cRec h 0 n
      have hfac : (Nat.factorial (n + 1) : ℝ)
          = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      calc f 1 0 (n + 1) * (Nat.factorial (n + 1) : ℝ) * (f 1 0 0) ^ (n + 1)
          = (f 1 0 (n + 1) * ((n : ℝ) + 1) * f 1 0 0)
              * ((Nat.factorial n : ℝ) * (f 1 0 0) ^ n) := by
            rw [hfac]; ring
        _ = (f 1 0 n * f 1 0 1) * ((Nat.factorial n : ℝ) * (f 1 0 0) ^ n) := by rw [hc]
        _ = (f 1 0 n * (Nat.factorial n : ℝ) * (f 1 0 0) ^ n) * f 1 0 1 := by ring
        _ = (f 1 0 0 * (f 1 0 1) ^ n) * f 1 0 1 := by rw [ih]
        _ = f 1 0 0 * (f 1 0 1) ^ (n + 1) := by ring

/-- **The bouquet weight in closed form.**  A one-vertex bouquet with `b` loops and
`c` degenerate tetrahedra: the two fugacities appear as powers over factorials. -/
theorem bouquetRow (h : CarrierShuffle f) (b c : ℕ) :
    f 1 b c * ((Nat.factorial b : ℝ) * (Nat.factorial c : ℝ))
        * (f 1 0 0) ^ (b + c)
      = f 1 0 0 * (f 1 1 0) ^ b * (f 1 0 1) ^ c := by
  induction b with
  | zero =>
      have hcol := bouquetTetCol h c
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, pow_zero, mul_one]
      exact hcol
  | succ n ih =>
      have hb := bRec h n c
      have hfac : (Nat.factorial (n + 1) : ℝ)
          = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      calc f 1 (n + 1) c * ((Nat.factorial (n + 1) : ℝ) * (Nat.factorial c : ℝ))
              * (f 1 0 0) ^ (n + 1 + c)
          = (f 1 (n + 1) c * ((n : ℝ) + 1) * f 1 0 0)
              * ((Nat.factorial n : ℝ) * (Nat.factorial c : ℝ) * (f 1 0 0) ^ (n + c)) := by
            rw [hfac]
            have : (f 1 0 0) ^ (n + 1 + c) = (f 1 0 0) ^ (n + c) * f 1 0 0 := by
              rw [show n + 1 + c = (n + c) + 1 by omega, pow_succ]
            rw [this]; ring
        _ = (f 1 n c * f 1 1 0)
              * ((Nat.factorial n : ℝ) * (Nat.factorial c : ℝ) * (f 1 0 0) ^ (n + c)) := by
            rw [hb]
        _ = (f 1 n c * ((Nat.factorial n : ℝ) * (Nat.factorial c : ℝ))
              * (f 1 0 0) ^ (n + c)) * f 1 1 0 := by ring
        _ = (f 1 0 0 * (f 1 1 0) ^ n * (f 1 0 1) ^ c) * f 1 1 0 := by rw [ih]
        _ = f 1 0 0 * (f 1 1 0) ^ (n + 1) * (f 1 0 1) ^ c := by ring

/-- **THEOREM (the two premises determine the weight up to three constants).**
On every size triple the carrier can realize, the size-blind weight is the inverse
gauge volume times three fugacities: one per index type.  The infinite-dimensional
residue of `Gap2GaugeVolume` §6c (an arbitrary `a : ℕ³ → ℝ`) collapses to three
real numbers. -/
theorem closedForm (h : CarrierShuffle f) (a b c : ℕ) (ha : 1 ≤ a) :
    f a b c * ((Nat.factorial a : ℝ) * (Nat.factorial b : ℝ) * (Nat.factorial c : ℝ))
        * (f 1 0 0) ^ (b + c)
      = (f 1 0 0) ^ a * (f 1 1 0) ^ b * (f 1 0 1) ^ c := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rcases Nat.eq_zero_or_pos (b + c) with hbc | hbc
  · -- No edges and no tetrahedra: the dust row already settles it.
    have hb : b = 0 := by omega
    have hc : c = 0 := by omega
    subst hb; subst hc
    have := dustRow h (a' + 1)
    simpa using this
  · -- At least one incidence: the dust-bouquet instance plus the bouquet row.
    have hd := h.dust_bouquet a' b c hbc
    rw [interleave_pt] at hd
    push_cast at hd
    have hrow := dustRow h a'
    have hbq := bouquetRow h b c
    have hfac : (Nat.factorial (a' + 1) : ℝ)
        = ((a' : ℝ) + 1) * (Nat.factorial a' : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hx : f 1 0 0 ≠ 0 := (h.pos 1 0 0).ne'
    calc f (a' + 1) b c
            * ((Nat.factorial (a' + 1) : ℝ) * (Nat.factorial b : ℝ) * (Nat.factorial c : ℝ))
            * (f 1 0 0) ^ (b + c)
        = (f (a' + 1) b c * ((a' : ℝ) + 1)) * (Nat.factorial a' : ℝ)
            * (f 1 b c * ((Nat.factorial b : ℝ) * (Nat.factorial c : ℝ))
                * (f 1 0 0) ^ (b + c)) / f 1 b c := by
          rw [hfac]
          field_simp [(h.pos 1 b c).ne']
      _ = (f a' 0 0 * f 1 b c) * (Nat.factorial a' : ℝ)
            * (f 1 0 0 * (f 1 1 0) ^ b * (f 1 0 1) ^ c) / f 1 b c := by
          rw [hd, hbq]
      _ = (f a' 0 0 * (Nat.factorial a' : ℝ))
            * (f 1 0 0 * (f 1 1 0) ^ b * (f 1 0 1) ^ c) := by
          field_simp [(h.pos 1 b c).ne']
      _ = (f 1 0 0) ^ a' * (f 1 0 0 * (f 1 1 0) ^ b * (f 1 0 1) ^ c) := by rw [hrow]
      _ = (f 1 0 0) ^ (a' + 1) * (f 1 1 0) ^ b * (f 1 0 1) ^ c := by ring

/-- **THEOREM (the Gibbs weight, from the two premises plus three unit
normalizations).**  If a single labeled vertex, a single labeled loop, and a
single labeled degenerate tetrahedron each carry unit weight, the size-blind
weight is forced to be the inverse gauge volume: exactly `gibbsWeight`.  By
`Gap2GaugeVolume.gibbsWeight_gives_gaugeCounting` the counting principle then
follows, so the measure is derived. -/
theorem gibbs_of_unit_fugacities (h : CarrierShuffle f) (hx : f 1 0 0 = 1) (hy : f 1 1 0 = 1)
    (hz : f 1 0 1 = 1) (a b c : ℕ) (ha : 1 ≤ a) :
    f a b c
      = 1 / ((Nat.factorial a : ℝ) * (Nat.factorial b : ℝ) * (Nat.factorial c : ℝ)) := by
  have hcf := closedForm h a b c ha
  rw [hx, hy, hz] at hcf
  simp only [one_pow, mul_one] at hcf
  have hpos : (0 : ℝ) < (Nat.factorial a : ℝ) * (Nat.factorial b : ℝ)
      * (Nat.factorial c : ℝ) := by
    have h1 : (0 : ℝ) < (Nat.factorial a : ℝ) := by
      have := Nat.factorial_pos a; exact_mod_cast this
    have h2 : (0 : ℝ) < (Nat.factorial b : ℝ) := by
      have := Nat.factorial_pos b; exact_mod_cast this
    have h3 : (0 : ℝ) < (Nat.factorial c : ℝ) := by
      have := Nat.factorial_pos c; exact_mod_cast this
    positivity
  field_simp at hcf ⊢
  linarith [hcf]

end CarrierShuffle

/-! ## §7. Availability: the gluing instances are not vacuous

§6 assumes the four gluing instances.  They are legitimate only if the pairs
really do have multiplicative automorphism counts, since §4 shows that is what the
binomial interleaving needs and §3 shows it genuinely fails for repeated
isomorphic pieces.  This section compiles the check on a nontrivial slice of
family (a): `dust 1` glued to a bouquet with `b` loops and `c` degenerate
tetrahedra.  The automorphism groups involved have order `b! · c!`, so this is not
a rigid or trivial-group witness; it is unbounded in both index directions.

The general theorem (parts sharing no isomorphic component have multiplicative
`Aut`) is not formalized here.  That is the remaining formalization debt and it is
recorded in the certificate rather than assumed away. -/

/-- A **bouquet**: one vertex carrying `b` loops and `c` degenerate tetrahedra
(every corner of every tetrahedron at the same vertex). -/
def bouquet (b c : ℕ) : BoundedComplex (1 + b + c) where
  nV := 1
  nE := b
  nT := c
  hV := by omega
  hE := by omega
  hT := by omega
  edgeVerts := fun _ => (0, 0)
  tetVerts := fun _ _ => 0

@[simp] theorem bouquet_nV (b c : ℕ) : (bouquet b c).nV = 1 := rfl
@[simp] theorem bouquet_nE (b c : ℕ) : (bouquet b c).nE = b := rfl
@[simp] theorem bouquet_nT (b c : ℕ) : (bouquet b c).nT = c := rfl

/-- A **cone**: `a` isolated vertices plus one apex carrying `b` loops and `c`
degenerate tetrahedra.  The cap matches `dunion (dust a) (bouquet b c)` so the two
are comparable. -/
def cone (a b c : ℕ) : BoundedComplex (a + (1 + b + c)) where
  nV := a + 1
  nE := b
  nT := c
  hV := by omega
  hE := by omega
  hT := by omega
  edgeVerts := fun _ => (Fin.last a, Fin.last a)
  tetVerts := fun _ _ => Fin.last a

@[simp] theorem cone_nV (a b c : ℕ) : (cone a b c).nV = a + 1 := rfl
@[simp] theorem cone_nE (a b c : ℕ) : (cone a b c).nE = b := rfl
@[simp] theorem cone_nT (a b c : ℕ) : (cone a b c).nT = c := rfl

/-- The right-hand injection of the single bouquet vertex lands on the apex. -/
theorem inrV_zero (a : ℕ) : (inrV (0 : Fin 1) : Fin (a + 1)) = Fin.last a := by
  apply Fin.ext
  simp [inrV]

/-- In a union whose left part has no edges, every edge comes from the right part.
Stated for a right part whose edges all sit on one vertex. -/
theorem dunion_dust_edgeVerts {B' : ℕ} (a : ℕ) (L : BoundedComplex B') (v : Fin L.nV)
    (hL : ∀ e, L.edgeVerts e = (v, v)) (e : Fin (dunion (dust a) L).nE) :
    (dunion (dust a) L).edgeVerts e
      = ((inrV v : Fin (a + L.nV)), (inrV v : Fin (a + L.nV))) := by
  simp only [dunion]
  cases hsum : finSumFinEquiv.symm e with
  | inl i => exact Fin.elim0 i
  | inr e' => simp [hL e']

/-- The same for tetrahedra. -/
theorem dunion_dust_tetVerts {B' : ℕ} (a : ℕ) (L : BoundedComplex B') (v : Fin L.nV)
    (hL : ∀ t i, L.tetVerts t i = v) (t : Fin (dunion (dust a) L).nT) (i : Fin 4) :
    (dunion (dust a) L).tetVerts t i = (inrV v : Fin (a + L.nV)) := by
  simp only [dunion]
  cases hsum : finSumFinEquiv.symm t with
  | inl j => exact Fin.elim0 j
  | inr t' => simp [hL t']

/-- **The union of dust and a bouquet is the cone.**  Every edge and tetrahedron of
the union comes from the bouquet, since dust carries none, and the bouquet's single
vertex sits at the apex. -/
def dunionConeRelabel (a b c : ℕ) :
    Relabel (dunion (dust a) (bouquet b c)) (cone a b c) where
  vEquiv := Equiv.refl _
  eEquiv := finCongr (Nat.zero_add b)
  tEquiv := finCongr (Nat.zero_add c)
  edge_comm := by
    intro e
    rw [dunion_dust_edgeVerts a (bouquet b c)
      (show Fin (bouquet b c).nV from (0 : Fin 1)) (fun _ => rfl) e]
    simp [cone]
    apply Fin.ext
    simp
  tet_comm := by
    intro t i
    rw [dunion_dust_tetVerts a (bouquet b c)
      (show Fin (bouquet b c).nV from (0 : Fin 1)) (fun _ _ => rfl) t i]
    simp [cone]
    apply Fin.ext
    simp

theorem dunion_cone_equivalent (a b c : ℕ) :
    Equivalent (dunion (dust a) (bouquet b c)) (cone a b c) :=
  ⟨dunionConeRelabel a b c⟩

/-- **The automorphism group of a bouquet.**  The single vertex has no choice, and
both incidence maps are constant, so every permutation of loops and of
tetrahedra is an automorphism and nothing else is required. -/
def autBouquetEquiv (b c : ℕ) :
    Aut (bouquet b c) ≃ Equiv.Perm (Fin b) × Equiv.Perm (Fin c) where
  toFun := fun r => (r.eEquiv, r.tEquiv)
  invFun := fun p =>
    { vEquiv := Equiv.refl _
      eEquiv := p.1
      tEquiv := p.2
      edge_comm := fun e => by simp [bouquet]
      tet_comm := fun t i => by simp [bouquet] }
  left_inv := by
    intro r
    have hv : r.vEquiv = Equiv.refl (Fin (bouquet b c).nV) := by
      refine Equiv.ext fun i => ?_
      simp only [Equiv.refl_apply]
      apply Fin.ext
      have h1 := (r.vEquiv i).isLt
      have h2 := i.isLt
      simp only [bouquet_nV] at h1 h2
      omega
    cases r
    simp_all
  right_inv := by intro p; rfl

theorem autCard_bouquet (b c : ℕ) :
    Nat.card (Aut (bouquet b c)) = Nat.factorial b * Nat.factorial c := by
  rw [Nat.card_congr (autBouquetEquiv b c), Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_fin,
    Fintype.card_fin]

/-- A permutation of a two-element index set that fixes one point is the identity. -/
theorem perm_fin_two_fixes (σ : Equiv.Perm (Fin 2)) (h : σ (Fin.last 1) = Fin.last 1) :
    σ = Equiv.refl (Fin 2) := by
  revert h
  revert σ
  decide

/-- **The automorphism group of a one-dust cone.**  The apex is the only vertex
carrying an incidence, so it is fixed; with only two vertices the remaining vertex
is fixed too, and the loops and tetrahedra permute freely.  Hence
`|Aut| = b! · c!`, which equals `|Aut (dust 1)| · |Aut (bouquet b c)|`. -/
def autConeOneEquiv (b c : ℕ) (hbc : 1 ≤ b + c) :
    Aut (cone 1 b c) ≃ Equiv.Perm (Fin b) × Equiv.Perm (Fin c) where
  toFun := fun r => (r.eEquiv, r.tEquiv)
  invFun := fun p =>
    { vEquiv := Equiv.refl _
      eEquiv := p.1
      tEquiv := p.2
      edge_comm := fun e => by simp [cone]
      tet_comm := fun t i => by simp [cone] }
  left_inv := by
    intro r
    have hfix : r.vEquiv (Fin.last 1) = Fin.last 1 := by
      rcases Nat.eq_zero_or_pos b with hb | hb
      · -- no loops, so there is at least one tetrahedron
        have hc : 0 < c := by omega
        have ht := r.tet_comm ⟨0, hc⟩ 0
        simpa [cone] using ht.symm
      · have he := r.edge_comm ⟨0, hb⟩
        have := congrArg Prod.fst he
        simpa [cone] using this.symm
    have hv : r.vEquiv = Equiv.refl (Fin (cone 1 b c).nV) := by
      have : r.vEquiv = Equiv.refl (Fin 2) := perm_fin_two_fixes r.vEquiv hfix
      exact this
    cases r
    simp_all
  right_inv := by intro p; rfl

theorem autCard_cone_one (b c : ℕ) (hbc : 1 ≤ b + c) :
    Nat.card (Aut (cone 1 b c)) = Nat.factorial b * Nat.factorial c := by
  rw [Nat.card_congr (autConeOneEquiv b c hbc), Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_fin,
    Fintype.card_fin]

/-- The permutations of a vertex set fixing one distinguished vertex number the
permutations of the rest. -/
theorem stab_card (a : ℕ) :
    Nat.card {σ : Equiv.Perm (Fin (a + 1)) // σ (Fin.last a) = Fin.last a}
      = Nat.factorial a := by
  classical
  have hiff : ∀ f : Equiv.Perm (Fin (a + 1)),
      f (Fin.last a) = Fin.last a ↔ ∀ x, ¬(x ≠ Fin.last a) → f x = x := by
    intro f
    constructor
    · intro h x hx
      have hxe : x = Fin.last a := by by_contra hc; exact hx hc
      rw [hxe]; exact h
    · intro h; exact h _ (by simp)
  have e2 : {σ : Equiv.Perm (Fin (a + 1)) // σ (Fin.last a) = Fin.last a}
      ≃ {f : Equiv.Perm (Fin (a + 1)) // ∀ x, ¬(x ≠ Fin.last a) → f x = x} :=
    Equiv.subtypeEquivRight (fun f => hiff f)
  have e1 : {f : Equiv.Perm (Fin (a + 1)) // ∀ x, ¬(x ≠ Fin.last a) → f x = x}
      ≃ Equiv.Perm {y : Fin (a + 1) // y ≠ Fin.last a} :=
    (Equiv.Perm.subtypeEquivSubtypePerm (fun y : Fin (a + 1) => y ≠ Fin.last a)).symm
  have hc : Fintype.card {y : Fin (a + 1) // y ≠ Fin.last a} = a := by
    have h := Fintype.card_subtype_compl (p := fun y : Fin (a + 1) => y = Fin.last a)
    rw [Fintype.card_subtype_eq, Fintype.card_fin] at h
    simpa using h
  rw [Nat.card_congr (e2.trans e1), Nat.card_eq_fintype_card, Fintype.card_perm, hc]

/-- **The automorphism group of a cone, for every amount of dust.**  The apex is the
only vertex carrying an incidence, so it is fixed; the remaining vertices permute
freely, and so do the loops and the tetrahedra. -/
def autConeEquiv (a b c : ℕ) (hbc : 1 ≤ b + c) :
    Aut (cone a b c)
      ≃ {σ : Equiv.Perm (Fin (a + 1)) // σ (Fin.last a) = Fin.last a}
          × (Equiv.Perm (Fin b) × Equiv.Perm (Fin c)) where
  toFun := fun r =>
    (⟨r.vEquiv, by
        rcases Nat.eq_zero_or_pos b with hb | hb
        · have hc : 0 < c := by omega
          have ht := r.tet_comm ⟨0, hc⟩ 0
          simpa [cone] using ht.symm
        · have he := r.edge_comm ⟨0, hb⟩
          have h1 := congrArg Prod.fst he
          simpa [cone] using h1.symm⟩,
      (r.eEquiv, r.tEquiv))
  invFun := fun p =>
    { vEquiv := p.1.val
      eEquiv := p.2.1
      tEquiv := p.2.2
      edge_comm := fun e => by simp [cone, p.1.property]
      tet_comm := fun t i => by simp [cone, p.1.property] }
  left_inv := by intro r; rfl
  right_inv := by intro p; rfl

theorem autCard_cone (a b c : ℕ) (hbc : 1 ≤ b + c) :
    Nat.card (Aut (cone a b c))
      = Nat.factorial a * (Nat.factorial b * Nat.factorial c) := by
  classical
  rw [Nat.card_congr (autConeEquiv a b c hbc), Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
    Fintype.card_fin, Fintype.card_fin]
  have hs : Fintype.card {σ : Equiv.Perm (Fin (a + 1)) // σ (Fin.last a) = Fin.last a}
      = Nat.factorial a := by
    have := stab_card a
    rwa [Nat.card_eq_fintype_card] at this
  rw [hs]

/-- **THEOREM (family (a) is available in full).**  For every amount of dust and every
bouquet carrying at least one incidence, the automorphism count multiplies over the
union.  This is the family that carries the vertex, edge and tetrahedron recursions
of §6, so the most-used gluing instance is verified rather than assumed. -/
theorem autMul_dust_bouquet (a b c : ℕ) (hbc : 1 ≤ b + c) :
    Nat.card (Aut (dunion (dust a) (bouquet b c)))
      = Nat.card (Aut (dust a)) * Nat.card (Aut (bouquet b c)) := by
  rw [autCard_congr (dunion_cone_equivalent a b c), autCard_cone a b c hbc,
    autCard_dust, autCard_bouquet]

/-- The orbit-count form: the interleaving factor is `a + 1`, and each part has a
single labeled presentation. -/
theorem orbitCard_dust_bouquet (a b c : ℕ) (hbc : 1 ≤ b + c) :
    gaugeOrbitCard (dunion (dust a) (bouquet b c))
      = interleave a 0 0 1 b c
        * (gaugeOrbitCard (dust a) * gaugeOrbitCard (bouquet b c)) :=
  orbitCard_dunion_of_autMul _ _ (autMul_dust_bouquet a b c hbc)

/-- **THEOREM (family (a) is available at `a = 1`, for every `b` and `c`).**  The
automorphism count multiplies over `dust 1 ⊔ bouquet(b,c)`.  Together with §4 this
means the orbit counts there satisfy the binomial interleaving identity, so the
gluing instance used in §6 is a real instance and not an assumption with no
models.  The groups have order `b! · c!`, unbounded in both directions. -/
theorem autMul_dust_one_bouquet (b c : ℕ) (hbc : 1 ≤ b + c) :
    Nat.card (Aut (dunion (dust 1) (bouquet b c)))
      = Nat.card (Aut (dust 1)) * Nat.card (Aut (bouquet b c)) := by
  rw [autCard_congr (dunion_cone_equivalent 1 b c), autCard_cone_one b c hbc,
    autCard_dust, autCard_bouquet]
  simp [Nat.factorial]

/-- The corresponding orbit-count identity, spelled out: the interleaving factor is
exactly `2`, which is `C(1+1, 1)`, and both parts have a single labeled
presentation. -/
theorem orbitCard_dust_one_bouquet (b c : ℕ) (hbc : 1 ≤ b + c) :
    gaugeOrbitCard (dunion (dust 1) (bouquet b c))
      = interleave 1 0 0 1 b c
        * (gaugeOrbitCard (dust 1) * gaugeOrbitCard (bouquet b c)) :=
  orbitCard_dunion_of_autMul _ _ (autMul_dust_one_bouquet b c hbc)

/-! ### §7b. Families (b), (c) and (d): the rigid parts

Family (a) is dust glued to a bouquet, and its availability is above.  The other three
instances glue something to a *rigid* part, meaning a part with no automorphisms: a
single edge with distinct endpoints, or a single nondegenerate tetrahedron.  Rigidity is
what makes those parts contribute a factor of one, and it is a consequence of the
incidence data being *ordered*: a relabeling must match the endpoint pair in order, so it
cannot reverse an edge or rotate a tetrahedron.

The no-mixing argument is the same in all three cases and rests on invariants of the
incidence pattern rather than on any count.  Whether an edge's two endpoints coincide is
preserved by relabeling, so a loop can never map to a proper edge; whether a
tetrahedron's four corners coincide is preserved likewise.  So the parts cannot exchange
cells, every vertex carrying an incidence is pinned, and the remaining vertices permute
freely. -/

/-- A permutation fixing every point but one fixes that one too, by injectivity. -/
theorem perm_fix_of_fixes_others {α : Type*} (σ : Equiv.Perm α) (x : α)
    (h : ∀ y, y ≠ x → σ y = y) : σ x = x := by
  by_contra hx
  exact hx (σ.injective (h (σ x) hx))

/-- The permutations of an index set fixing one distinguished point number the
permutations of the rest.  The `Fin.last` case is `stab_card`; this is the general one,
needed because the distinguished point of a union is an injection image. -/
theorem stab1_card {m : ℕ} (p : Fin (m + 1)) :
    Nat.card {σ : Equiv.Perm (Fin (m + 1)) // σ p = p} = Nat.factorial m := by
  classical
  have hiff : ∀ f : Equiv.Perm (Fin (m + 1)),
      f p = p ↔ ∀ x, ¬(x ≠ p) → f x = x := by
    intro f
    constructor
    · intro h x hx
      rw [not_not.mp hx]; exact h
    · intro h; exact h _ (by simp)
  have e2 : {σ : Equiv.Perm (Fin (m + 1)) // σ p = p}
      ≃ {f : Equiv.Perm (Fin (m + 1)) // ∀ x, ¬(x ≠ p) → f x = x} :=
    Equiv.subtypeEquivRight (fun f => hiff f)
  have e1 : {f : Equiv.Perm (Fin (m + 1)) // ∀ x, ¬(x ≠ p) → f x = x}
      ≃ Equiv.Perm {y : Fin (m + 1) // y ≠ p} :=
    (Equiv.Perm.subtypeEquivSubtypePerm (fun y : Fin (m + 1) => y ≠ p)).symm
  have hc : Fintype.card {y : Fin (m + 1) // y ≠ p} = m := by
    have h := Fintype.card_subtype_compl (p := fun y : Fin (m + 1) => y = p)
    rw [Fintype.card_subtype_eq, Fintype.card_fin] at h
    simpa using h
  rw [Nat.card_congr (e2.trans e1), Nat.card_eq_fintype_card, Fintype.card_perm, hc]

/-! The four accessors for a union's incidence maps.  Every cell of the union is the
image of a cell of one part, and these say what its vertices are. -/

theorem dunion_edgeVerts_inl {B B' : ℕ} (K : BoundedComplex B) (L : BoundedComplex B')
    (e : Fin K.nE) :
    (dunion K L).edgeVerts (finSumFinEquiv (Sum.inl e))
      = ((inlV (K.edgeVerts e).1 : Fin (K.nV + L.nV)), inlV (K.edgeVerts e).2) := by
  simp only [dunion, Equiv.symm_apply_apply, Sum.elim_inl]

theorem dunion_edgeVerts_inr {B B' : ℕ} (K : BoundedComplex B) (L : BoundedComplex B')
    (e : Fin L.nE) :
    (dunion K L).edgeVerts (finSumFinEquiv (Sum.inr e))
      = ((inrV (L.edgeVerts e).1 : Fin (K.nV + L.nV)), inrV (L.edgeVerts e).2) := by
  simp only [dunion, Equiv.symm_apply_apply, Sum.elim_inr]

theorem dunion_tetVerts_inl {B B' : ℕ} (K : BoundedComplex B) (L : BoundedComplex B')
    (t : Fin K.nT) (i : Fin 4) :
    (dunion K L).tetVerts (finSumFinEquiv (Sum.inl t)) i
      = (inlV (K.tetVerts t i) : Fin (K.nV + L.nV)) := by
  simp only [dunion, Equiv.symm_apply_apply, Sum.elim_inl]

theorem dunion_tetVerts_inr {B B' : ℕ} (K : BoundedComplex B) (L : BoundedComplex B')
    (t : Fin L.nT) (i : Fin 4) :
    (dunion K L).tetVerts (finSumFinEquiv (Sum.inr t)) i
      = (inrV (L.tetVerts t i) : Fin (K.nV + L.nV)) := by
  simp only [dunion, Equiv.symm_apply_apply, Sum.elim_inr]

/-- A **single edge** with distinct endpoints: two vertices, one edge joining them. -/
def edge : BoundedComplex 2 where
  nV := 2
  nE := 1
  nT := 0
  hV := le_refl 2
  hE := by omega
  hT := by omega
  edgeVerts := fun _ => (0, Fin.last 1)
  tetVerts := fun t _ => Fin.elim0 t

@[simp] theorem edge_nV : edge.nV = 2 := rfl
@[simp] theorem edge_nE : edge.nE = 1 := rfl
@[simp] theorem edge_nT : edge.nT = 0 := rfl

/-- A permutation of a one-element index set is the identity. -/
theorem perm_fin_one (σ : Equiv.Perm (Fin 1)) : σ = Equiv.refl (Fin 1) := by
  refine Equiv.ext fun i => ?_
  apply Fin.ext
  have h1 := (σ i).isLt
  have h2 := i.isLt
  omega

/-- A permutation of an empty index set is the identity. -/
theorem perm_fin_zero (σ : Equiv.Perm (Fin 0)) : σ = Equiv.refl (Fin 0) :=
  Equiv.ext fun t => Fin.elim0 t

/-- The permutations of a vertex set fixing two distinguished vertices number the
permutations of the rest.  Used by all three rigid families. -/
theorem stab2_card {m : ℕ} (p q : Fin (m + 2)) (hpq : p ≠ q) :
    Nat.card {σ : Equiv.Perm (Fin (m + 2)) // σ p = p ∧ σ q = q} = Nat.factorial m := by
  classical
  have hiff : ∀ f : Equiv.Perm (Fin (m + 2)),
      (f p = p ∧ f q = q) ↔ ∀ x, ¬(x ≠ p ∧ x ≠ q) → f x = x := by
    intro f
    constructor
    · intro h x hx
      rcases not_and_or.mp hx with hxp | hxq
      · rw [not_not.mp hxp]; exact h.1
      · rw [not_not.mp hxq]; exact h.2
    · intro h
      exact ⟨h p (by simp), h q (by simp)⟩
  have e2 : {σ : Equiv.Perm (Fin (m + 2)) // σ p = p ∧ σ q = q}
      ≃ {f : Equiv.Perm (Fin (m + 2)) // ∀ x, ¬(x ≠ p ∧ x ≠ q) → f x = x} :=
    Equiv.subtypeEquivRight (fun f => hiff f)
  have e1 : {f : Equiv.Perm (Fin (m + 2)) // ∀ x, ¬(x ≠ p ∧ x ≠ q) → f x = x}
      ≃ Equiv.Perm {y : Fin (m + 2) // y ≠ p ∧ y ≠ q} :=
    (Equiv.Perm.subtypeEquivSubtypePerm (fun y : Fin (m + 2) => y ≠ p ∧ y ≠ q)).symm
  have hc : Fintype.card {y : Fin (m + 2) // y ≠ p ∧ y ≠ q} = m := by
    rw [Fintype.card_subtype]
    have hfil : (Finset.univ.filter (fun y : Fin (m + 2) => y ≠ p ∧ y ≠ q))
        = Finset.univ \ {p, q} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hfil, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem (by simpa using hpq), Finset.card_singleton]
    omega
  rw [Nat.card_congr (e2.trans e1), Nat.card_eq_fintype_card, Fintype.card_perm, hc]

/-- The single edge is **rigid**: ordered endpoints leave no automorphism. -/
def autEdgeEquiv : Aut edge ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ =>
    { vEquiv := Equiv.refl _
      eEquiv := Equiv.refl _
      tEquiv := Equiv.refl _
      edge_comm := fun e => by simp [edge]
      tet_comm := fun t _ => Fin.elim0 t }
  left_inv := by
    intro r
    have hsnd : r.vEquiv (Fin.last 1) = Fin.last 1 := by
      have he := r.edge_comm (show Fin edge.nE from (0 : Fin 1))
      have h2 := congrArg Prod.snd he
      simpa [edge] using h2.symm
    have hv : r.vEquiv = Equiv.refl (Fin edge.nV) := perm_fin_two_fixes r.vEquiv hsnd
    have he : r.eEquiv = Equiv.refl (Fin edge.nE) := perm_fin_one r.eEquiv
    have ht : r.tEquiv = Equiv.refl (Fin edge.nT) := perm_fin_zero r.tEquiv
    cases r
    simp_all
  right_inv := by intro _; rfl

theorem autCard_edge : Nat.card (Aut edge) = 1 := by
  rw [Nat.card_congr autEdgeEquiv, Nat.card_eq_fintype_card, Fintype.card_unit]

/-- In a union of dust with the single edge, the one edge is the pushed-in edge of the
right part, so its endpoints are the two pushed-in vertices. -/
theorem dunion_dust_edge_edgeVerts (a : ℕ) (e : Fin (dunion (dust a) edge).nE) :
    (dunion (dust a) edge).edgeVerts e
      = ((inrV (0 : Fin 2) : Fin (a + 2)), (inrV (Fin.last 1) : Fin (a + 2))) := by
  simp only [dunion]
  cases hsum : finSumFinEquiv.symm e with
  | inl i => exact Fin.elim0 i
  | inr e' => simp [edge]

/-- The two pushed-in endpoints are distinct, since the injection is injective. -/
theorem inrV_edge_ne (a : ℕ) :
    (inrV (0 : Fin 2) : Fin (a + 2)) ≠ (inrV (Fin.last 1) : Fin (a + 2)) := by
  intro h
  have hv := congrArg Fin.val h
  simp [inrV] at hv

/-- **The automorphism group of dust glued to an edge.**  The two endpoints are the only
vertices carrying an incidence and the edge is ordered, so both are pinned; the dust
permutes freely. -/
def autDustEdgeEquiv (a : ℕ) :
    Aut (dunion (dust a) edge)
      ≃ {σ : Equiv.Perm (Fin (a + 2)) //
          σ (inrV (0 : Fin 2)) = inrV (0 : Fin 2)
            ∧ σ (inrV (Fin.last 1)) = inrV (Fin.last 1)} where
  toFun := fun r =>
    ⟨r.vEquiv, by
      have he := r.edge_comm (show Fin (dunion (dust a) edge).nE from (0 : Fin 1))
      rw [dunion_dust_edge_edgeVerts, dunion_dust_edge_edgeVerts] at he
      simp only [Prod.map, Prod.mk.injEq] at he
      exact ⟨he.1.symm, he.2.symm⟩⟩
  invFun := fun σ =>
    { vEquiv := σ.val
      eEquiv := Equiv.refl _
      tEquiv := Equiv.refl _
      edge_comm := fun e => by
        rw [dunion_dust_edge_edgeVerts, dunion_dust_edge_edgeVerts]
        simp only [Prod.map, Prod.mk.injEq]
        exact ⟨σ.property.1.symm, σ.property.2.symm⟩
      tet_comm := fun t _ => Fin.elim0 t }
  left_inv := by
    intro r
    have he : r.eEquiv = Equiv.refl (Fin (dunion (dust a) edge).nE) :=
      perm_fin_one r.eEquiv
    have ht : r.tEquiv = Equiv.refl (Fin (dunion (dust a) edge).nT) :=
      perm_fin_zero r.tEquiv
    cases r
    simp_all
  right_inv := by intro _; rfl

theorem autCard_dust_edge (a : ℕ) :
    Nat.card (Aut (dunion (dust a) edge)) = Nat.factorial a := by
  rw [Nat.card_congr (autDustEdgeEquiv a)]
  exact stab2_card _ _ (inrV_edge_ne a)

/-- **THEOREM (family (b) is available).**  The automorphism count multiplies over dust
glued to a single edge, for every amount of dust. -/
theorem autMul_dust_edge (a : ℕ) :
    Nat.card (Aut (dunion (dust a) edge))
      = Nat.card (Aut (dust a)) * Nat.card (Aut edge) := by
  rw [autCard_dust_edge, autCard_dust, autCard_edge, mul_one]

/-- The orbit-count form of family (b). -/
theorem orbitCard_dust_edge (a : ℕ) :
    gaugeOrbitCard (dunion (dust a) edge)
      = interleave a 0 0 2 1 0
        * (gaugeOrbitCard (dust a) * gaugeOrbitCard edge) :=
  orbitCard_dunion_of_autMul _ _ (autMul_dust_edge a)

/-! ### Family (c): a bouquet glued to an edge

Three vertices: the bouquet vertex, and the edge's two ends.  The proper edge cannot map
to a loop, because a relabeling carries the two endpoints of an edge to the two endpoints
of its image *in order*, so it preserves whether those endpoints coincide.  That pins both
ends of the proper edge, and then the bouquet vertex is pinned because a permutation
fixing all but one point fixes that one.  Loops and tetrahedra then permute freely. -/

/-- The bouquet vertex of the union. -/
def bqeV (b c : ℕ) : Fin (dunion (bouquet b c) edge).nV := inlV (0 : Fin 1)
/-- The first endpoint of the proper edge. -/
def bqeV0 (b c : ℕ) : Fin (dunion (bouquet b c) edge).nV := inrV (0 : Fin 2)
/-- The second endpoint of the proper edge. -/
def bqeV1 (b c : ℕ) : Fin (dunion (bouquet b c) edge).nV := inrV (Fin.last 1)
/-- The index of the proper edge. -/
def bqePE (b c : ℕ) : Fin (dunion (bouquet b c) edge).nE := finSumFinEquiv (Sum.inr (0 : Fin 1))

theorem bqeV_val (b c : ℕ) : (bqeV b c).val = 0 := rfl
theorem bqeV0_val (b c : ℕ) : (bqeV0 b c).val = 1 := rfl
theorem bqeV1_val (b c : ℕ) : (bqeV1 b c).val = 2 := rfl

/-- The proper edge joins the two pushed-in endpoints. -/
theorem bqe_edgeVerts_pE (b c : ℕ) :
    (dunion (bouquet b c) edge).edgeVerts (bqePE b c) = (bqeV0 b c, bqeV1 b c) := by
  rw [bqePE, dunion_edgeVerts_inr]
  rfl

/-- Every other edge of the union is a loop at the bouquet vertex. -/
theorem bqe_edgeVerts_loop (b c : ℕ) (e : Fin (dunion (bouquet b c) edge).nE)
    (h : e ≠ bqePE b c) :
    (dunion (bouquet b c) edge).edgeVerts e = (bqeV b c, bqeV b c) := by
  cases hsum : finSumFinEquiv.symm e with
  | inl i =>
      have he : e = finSumFinEquiv (Sum.inl i) := by rw [← hsum, Equiv.apply_symm_apply]
      rw [he, dunion_edgeVerts_inl]
      rfl
  | inr j =>
      exfalso
      apply h
      apply finSumFinEquiv.symm.injective
      rw [hsum, bqePE, Equiv.symm_apply_apply]
      congr 1
      apply Fin.ext
      have h1 : edge.nE = 1 := rfl
      have h2 := j.isLt
      have h3 : ((0 : Fin 1) : ℕ) = 0 := rfl
      omega

/-- Every tetrahedron of the union sits at the bouquet vertex, the edge having none. -/
theorem bqe_tetVerts (b c : ℕ) (t : Fin (dunion (bouquet b c) edge).nT) (i : Fin 4) :
    (dunion (bouquet b c) edge).tetVerts t i = bqeV b c := by
  cases hsum : finSumFinEquiv.symm t with
  | inl t' =>
      have ht : t = finSumFinEquiv (Sum.inl t') := by rw [← hsum, Equiv.apply_symm_apply]
      rw [ht, dunion_tetVerts_inl]
      rfl
  | inr t' => exact Fin.elim0 t'

/-- **The proper edge is fixed.**  If it mapped to a loop its two distinct endpoints
would have the same image. -/
theorem bqe_eEquiv_fixes (b c : ℕ) (r : Aut (dunion (bouquet b c) edge)) :
    r.eEquiv (bqePE b c) = bqePE b c := by
  by_contra hne
  have he := r.edge_comm (bqePE b c)
  rw [bqe_edgeVerts_loop b c _ hne, bqe_edgeVerts_pE] at he
  simp only [Prod.map, Prod.mk.injEq] at he
  have hcoll : bqeV0 b c = bqeV1 b c := r.vEquiv.injective (he.1.symm.trans he.2)
  have h0 := bqeV0_val b c
  rw [hcoll] at h0
  rw [bqeV1_val] at h0
  omega

/-- **Every vertex is pinned.** -/
theorem bqe_vEquiv_refl (b c : ℕ) (r : Aut (dunion (bouquet b c) edge)) :
    r.vEquiv = Equiv.refl _ := by
  have he := r.edge_comm (bqePE b c)
  rw [bqe_eEquiv_fixes, bqe_edgeVerts_pE] at he
  simp only [Prod.map, Prod.mk.injEq] at he
  have h0 : r.vEquiv (bqeV0 b c) = bqeV0 b c := he.1.symm
  have h1 : r.vEquiv (bqeV1 b c) = bqeV1 b c := he.2.symm
  have hother : ∀ y, y ≠ bqeV b c → r.vEquiv y = y := by
    intro y hy
    have hlt : y.val < 3 := by
      have := y.isLt
      simpa using this
    have hne0 : y.val ≠ 0 := fun hc => hy (Fin.ext (by rw [hc, bqeV_val]))
    rcases (show y.val = 1 ∨ y.val = 2 by omega) with h | h
    · have hy0 : y = bqeV0 b c := Fin.ext (by rw [h, bqeV0_val])
      rw [hy0]; exact h0
    · have hy1 : y = bqeV1 b c := Fin.ext (by rw [h, bqeV1_val])
      rw [hy1]; exact h1
  have hb := perm_fix_of_fixes_others r.vEquiv (bqeV b c) hother
  refine Equiv.ext fun y => ?_
  by_cases hy : y = bqeV b c
  · rw [hy]; exact hb
  · exact hother y hy

/-- **The automorphism group of a bouquet glued to an edge.**  The edge contributes
nothing; the loops and the tetrahedra permute freely. -/
def autBqEdgeEquiv (b c : ℕ) :
    Aut (dunion (bouquet b c) edge)
      ≃ {σ : Equiv.Perm (Fin (dunion (bouquet b c) edge).nE) // σ (bqePE b c) = bqePE b c}
          × Equiv.Perm (Fin (dunion (bouquet b c) edge).nT) where
  toFun := fun r => (⟨r.eEquiv, bqe_eEquiv_fixes b c r⟩, r.tEquiv)
  invFun := fun p =>
    { vEquiv := Equiv.refl _
      eEquiv := p.1.val
      tEquiv := p.2
      edge_comm := fun e => by
        by_cases he : e = bqePE b c
        · rw [he, p.1.property, bqe_edgeVerts_pE]; rfl
        · have hne : p.1.val e ≠ bqePE b c := fun hc =>
            he (p.1.val.injective (hc.trans p.1.property.symm))
          rw [bqe_edgeVerts_loop b c _ hne, bqe_edgeVerts_loop b c e he]; rfl
      tet_comm := fun t i => by rw [bqe_tetVerts, bqe_tetVerts]; rfl }
  left_inv := by
    intro r
    have hv := bqe_vEquiv_refl b c r
    cases r
    simp_all
  right_inv := by intro _; rfl

theorem autCard_bouquet_edge (b c : ℕ) :
    Nat.card (Aut (dunion (bouquet b c) edge))
      = Nat.factorial b * Nat.factorial c := by
  classical
  rw [Nat.card_congr (autBqEdgeEquiv b c), Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_perm, Fintype.card_fin]
  have hs : Fintype.card {σ : Equiv.Perm (Fin (dunion (bouquet b c) edge).nE) //
      σ (bqePE b c) = bqePE b c} = Nat.factorial b := by
    have := stab1_card (bqePE b c)
    rwa [Nat.card_eq_fintype_card] at this
  rw [hs]
  simp

/-- **THEOREM (family (c) is available).**  The automorphism count multiplies over a
bouquet glued to a single edge, for every number of loops and tetrahedra. -/
theorem autMul_bouquet_edge (b c : ℕ) :
    Nat.card (Aut (dunion (bouquet b c) edge))
      = Nat.card (Aut (bouquet b c)) * Nat.card (Aut edge) := by
  rw [autCard_bouquet_edge, autCard_bouquet, autCard_edge, mul_one]

/-- The orbit-count form of family (c). -/
theorem orbitCard_bouquet_edge (b c : ℕ) :
    gaugeOrbitCard (dunion (bouquet b c) edge)
      = interleave 1 b c 2 1 0
        * (gaugeOrbitCard (bouquet b c) * gaugeOrbitCard edge) :=
  orbitCard_dunion_of_autMul _ _ (autMul_bouquet_edge b c)

/-! ### Family (d): a bouquet glued to a tetrahedron

Five vertices.  A nondegenerate tetrahedron cannot map to a degenerate one, because a
relabeling carries the four corners of a tetrahedron to the four corners of its image in
order, so it preserves whether they coincide.  That pins all four corners, and the
bouquet vertex follows. -/

/-- A **single nondegenerate tetrahedron**: four vertices, one tetrahedron on them. -/
def tetra : BoundedComplex 4 where
  nV := 4
  nE := 0
  nT := 1
  hV := le_refl 4
  hE := by omega
  hT := by omega
  edgeVerts := Fin.elim0
  tetVerts := fun _ i => i

@[simp] theorem tetra_nV : tetra.nV = 4 := rfl
@[simp] theorem tetra_nE : tetra.nE = 0 := rfl
@[simp] theorem tetra_nT : tetra.nT = 1 := rfl

/-- The tetrahedron is **rigid**: ordered corners leave no automorphism. -/
def autTetraEquiv : Aut tetra ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ =>
    { vEquiv := Equiv.refl _
      eEquiv := Equiv.refl _
      tEquiv := Equiv.refl _
      edge_comm := fun e => Fin.elim0 e
      tet_comm := fun t i => by simp [tetra] }
  left_inv := by
    intro r
    have hv : r.vEquiv = Equiv.refl (Fin tetra.nV) := by
      refine Equiv.ext fun i => ?_
      have ht := r.tet_comm (show Fin tetra.nT from (0 : Fin 1)) i
      simpa [tetra] using ht.symm
    have he : r.eEquiv = Equiv.refl (Fin tetra.nE) := perm_fin_zero r.eEquiv
    have ht : r.tEquiv = Equiv.refl (Fin tetra.nT) := perm_fin_one r.tEquiv
    cases r
    simp_all
  right_inv := by intro _; rfl

theorem autCard_tetra : Nat.card (Aut tetra) = 1 := by
  rw [Nat.card_congr autTetraEquiv, Nat.card_eq_fintype_card, Fintype.card_unit]

/-- The bouquet vertex of the union. -/
def bqtV (b c : ℕ) : Fin (dunion (bouquet b c) tetra).nV := inlV (0 : Fin 1)
/-- The `i`-th corner of the tetrahedron, in the union. -/
def bqtVR (b c : ℕ) (i : Fin 4) : Fin (dunion (bouquet b c) tetra).nV := inrV i
/-- The index of the nondegenerate tetrahedron. -/
def bqtPT (b c : ℕ) : Fin (dunion (bouquet b c) tetra).nT := finSumFinEquiv (Sum.inr (0 : Fin 1))

theorem bqtV_val (b c : ℕ) : (bqtV b c).val = 0 := rfl
theorem bqtVR_val (b c : ℕ) (i : Fin 4) : (bqtVR b c i).val = 1 + i.val := rfl

/-- The nondegenerate tetrahedron has the four pushed-in corners. -/
theorem bqt_tetVerts_pT (b c : ℕ) (i : Fin 4) :
    (dunion (bouquet b c) tetra).tetVerts (bqtPT b c) i = bqtVR b c i := by
  rw [bqtPT, dunion_tetVerts_inr]
  rfl

/-- Every other tetrahedron sits at the bouquet vertex. -/
theorem bqt_tetVerts_deg (b c : ℕ) (t : Fin (dunion (bouquet b c) tetra).nT)
    (h : t ≠ bqtPT b c) (i : Fin 4) :
    (dunion (bouquet b c) tetra).tetVerts t i = bqtV b c := by
  cases hsum : finSumFinEquiv.symm t with
  | inl t' =>
      have ht : t = finSumFinEquiv (Sum.inl t') := by rw [← hsum, Equiv.apply_symm_apply]
      rw [ht, dunion_tetVerts_inl]
      rfl
  | inr t' =>
      exfalso
      apply h
      apply finSumFinEquiv.symm.injective
      rw [hsum, bqtPT, Equiv.symm_apply_apply]
      congr 1
      apply Fin.ext
      have h1 : tetra.nT = 1 := rfl
      have h2 := t'.isLt
      have h3 : ((0 : Fin 1) : ℕ) = 0 := rfl
      omega

/-- Every edge of the union is a loop at the bouquet vertex, the tetrahedron having none. -/
theorem bqt_edgeVerts (b c : ℕ) (e : Fin (dunion (bouquet b c) tetra).nE) :
    (dunion (bouquet b c) tetra).edgeVerts e = (bqtV b c, bqtV b c) := by
  cases hsum : finSumFinEquiv.symm e with
  | inl i =>
      have he : e = finSumFinEquiv (Sum.inl i) := by rw [← hsum, Equiv.apply_symm_apply]
      rw [he, dunion_edgeVerts_inl]
      rfl
  | inr j => exact Fin.elim0 j

/-- **The nondegenerate tetrahedron is fixed.**  If it mapped to a degenerate one, its
four distinct corners would all have the same image. -/
theorem bqt_tEquiv_fixes (b c : ℕ) (r : Aut (dunion (bouquet b c) tetra)) :
    r.tEquiv (bqtPT b c) = bqtPT b c := by
  by_contra hne
  have h0 := r.tet_comm (bqtPT b c) 0
  have h1 := r.tet_comm (bqtPT b c) 1
  rw [bqt_tetVerts_deg b c _ hne, bqt_tetVerts_pT] at h0
  rw [bqt_tetVerts_deg b c _ hne, bqt_tetVerts_pT] at h1
  have hcoll : bqtVR b c 0 = bqtVR b c 1 := r.vEquiv.injective (h0.symm.trans h1)
  have hv := bqtVR_val b c 0
  rw [hcoll, bqtVR_val] at hv
  simp at hv

/-- **Every vertex is pinned.** -/
theorem bqt_vEquiv_refl (b c : ℕ) (r : Aut (dunion (bouquet b c) tetra)) :
    r.vEquiv = Equiv.refl _ := by
  have hcorner : ∀ i : Fin 4, r.vEquiv (bqtVR b c i) = bqtVR b c i := by
    intro i
    have ht := r.tet_comm (bqtPT b c) i
    rw [bqt_tEquiv_fixes, bqt_tetVerts_pT] at ht
    exact ht.symm
  have hother : ∀ y, y ≠ bqtV b c → r.vEquiv y = y := by
    intro y hy
    have hlt : y.val < 5 := by
      have := y.isLt
      simpa using this
    have hne0 : y.val ≠ 0 := fun hc => hy (Fin.ext (by rw [hc, bqtV_val]))
    have hyi : y = bqtVR b c ⟨y.val - 1, by omega⟩ := by
      apply Fin.ext
      rw [bqtVR_val]
      show y.val = 1 + (y.val - 1)
      omega
    rw [hyi]
    exact hcorner _
  have hb := perm_fix_of_fixes_others r.vEquiv (bqtV b c) hother
  refine Equiv.ext fun y => ?_
  by_cases hy : y = bqtV b c
  · rw [hy]; exact hb
  · exact hother y hy

/-- **The automorphism group of a bouquet glued to a tetrahedron.** -/
def autBqTetEquiv (b c : ℕ) :
    Aut (dunion (bouquet b c) tetra)
      ≃ Equiv.Perm (Fin (dunion (bouquet b c) tetra).nE)
          × {τ : Equiv.Perm (Fin (dunion (bouquet b c) tetra).nT) //
              τ (bqtPT b c) = bqtPT b c} where
  toFun := fun r => (r.eEquiv, ⟨r.tEquiv, bqt_tEquiv_fixes b c r⟩)
  invFun := fun p =>
    { vEquiv := Equiv.refl _
      eEquiv := p.1
      tEquiv := p.2.val
      edge_comm := fun e => by rw [bqt_edgeVerts, bqt_edgeVerts]; rfl
      tet_comm := fun t i => by
        by_cases ht : t = bqtPT b c
        · rw [ht, p.2.property, bqt_tetVerts_pT]; rfl
        · have hne : p.2.val t ≠ bqtPT b c := fun hc =>
            ht (p.2.val.injective (hc.trans p.2.property.symm))
          rw [bqt_tetVerts_deg b c _ hne, bqt_tetVerts_deg b c t ht]; rfl }
  left_inv := by
    intro r
    have hv := bqt_vEquiv_refl b c r
    cases r
    simp_all
  right_inv := by intro _; rfl

theorem autCard_bouquet_tetra (b c : ℕ) :
    Nat.card (Aut (dunion (bouquet b c) tetra))
      = Nat.factorial b * Nat.factorial c := by
  classical
  rw [Nat.card_congr (autBqTetEquiv b c), Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_perm, Fintype.card_fin]
  have hs : Fintype.card {τ : Equiv.Perm (Fin (dunion (bouquet b c) tetra).nT) //
      τ (bqtPT b c) = bqtPT b c} = Nat.factorial c := by
    have := stab1_card (bqtPT b c)
    rwa [Nat.card_eq_fintype_card] at this
  rw [hs]
  simp

/-- **THEOREM (family (d) is available).**  The automorphism count multiplies over a
bouquet glued to a single nondegenerate tetrahedron. -/
theorem autMul_bouquet_tetra (b c : ℕ) :
    Nat.card (Aut (dunion (bouquet b c) tetra))
      = Nat.card (Aut (bouquet b c)) * Nat.card (Aut tetra) := by
  rw [autCard_bouquet_tetra, autCard_bouquet, autCard_tetra, mul_one]

/-- The orbit-count form of family (d). -/
theorem orbitCard_bouquet_tetra (b c : ℕ) :
    gaugeOrbitCard (dunion (bouquet b c) tetra)
      = interleave 1 b c 4 0 1
        * (gaugeOrbitCard (bouquet b c) * gaugeOrbitCard tetra) :=
  orbitCard_dunion_of_autMul _ _ (autMul_bouquet_tetra b c)

/-- **THEOREM (all four gluing instances of the premise set are available).**  Each of
the four unions used by `CarrierShuffle` has automorphism counts that multiply, so the
premise set is not an assumption about instances that might fail to exist: it is a
statement about four verified families, each unbounded in the sizes it ranges over. -/
theorem all_four_families_available :
    (∀ a b c : ℕ, 1 ≤ b + c →
        Nat.card (Aut (dunion (dust a) (bouquet b c)))
          = Nat.card (Aut (dust a)) * Nat.card (Aut (bouquet b c)))
      ∧ (∀ a : ℕ, Nat.card (Aut (dunion (dust a) edge))
          = Nat.card (Aut (dust a)) * Nat.card (Aut edge))
      ∧ (∀ b c : ℕ, Nat.card (Aut (dunion (bouquet b c) edge))
          = Nat.card (Aut (bouquet b c)) * Nat.card (Aut edge))
      ∧ (∀ b c : ℕ, Nat.card (Aut (dunion (bouquet b c) tetra))
          = Nat.card (Aut (bouquet b c)) * Nat.card (Aut tetra)) :=
  ⟨fun a b c h => autMul_dust_bouquet a b c h, autMul_dust_edge,
    autMul_bouquet_edge, autMul_bouquet_tetra⟩

/-! ## §8. How much each premise does: the strength measurement

A hostile panel run on §1-§7 converged on one correction: the headline "two premises
force the measure" hides the fact that the two premises are not equal partners.  This
section measures them, because a premise set is only worth what its weakest member
excludes.

The first theorem is a decoy: a relabeling-invariant weight that satisfies premise (ii)
at **every** pair, with no side condition whatsoever, and is not the RS measure.  So
premise (ii) alone excludes nothing at all, and every bit of the derivation's force
comes from premise (i).

The second is the converse receipt.  Premise (ii) is *silent* on `dust a ⊔ dust b`,
because the parts share a component; C3 shows why it must be.  The weight the two
premises force nonetheless satisfies the binomial-corrected identity there, as a
theorem rather than a premise.  A premise fitted to produce a wanted answer would
have its bodies buried exactly in the region it declines to speak about; this one
predicts that region correctly.  That is the non-circularity receipt. -/

/-- The **uniform weight**: unit mass per class, spread evenly over the labeled
complexes presenting it.  This is the honest "labels are physical, every class counts
once" alternative to the RS measure. -/
noncomputable def uniformWeight {B : ℕ} (K : BoundedComplex B) : ℝ :=
  1 / (gaugeOrbitCard K : ℝ)

/-- The gauge orbit count is relabeling-invariant: it is determined by the index sizes
and the automorphism count, and a relabeling preserves both. -/
theorem gaugeOrbitCard_congr {B : ℕ} {K K' : BoundedComplex B} (h : Equivalent K K') :
    gaugeOrbitCard K = gaugeOrbitCard K' := by
  have hK := orbitCard_mul_autCard K
  have hK' := orbitCard_mul_autCard K'
  obtain ⟨r⟩ := h
  rw [size_v r, size_e r, size_t r] at hK
  rw [autCard_congr ⟨r⟩] at hK
  exact Nat.eq_of_mul_eq_mul_right (autCard_pos K') (hK.trans hK'.symm)

theorem uniformWeight_invariant {B : ℕ} {K K' : BoundedComplex B} (h : Equivalent K K') :
    uniformWeight K = uniformWeight K' := by
  unfold uniformWeight
  rw [gaugeOrbitCard_congr h]

/-- **Every class carries unit mass under the uniform weight.** -/
theorem classMass_uniform {B : ℕ} (K : BoundedComplex B) :
    classMass uniformWeight (Quotient.mk (relabelSetoid B) K) = 1 := by
  rw [classMass_of_invariant _ (fun _ _ h => uniformWeight_invariant h) _,
    uniformWeight_invariant (equivalent_out K), orbitCardClass_mk]
  unfold uniformWeight
  have hpos : (0 : ℝ) < (gaugeOrbitCard K : ℝ) := by
    exact_mod_cast gaugeOrbitCard_pos K
  field_simp

/-- **Premise (ii), stated for a family of labeled weights**, one at each size cap:
the class mass of a union is the product of the class masses of the parts.  This is
the unrestricted form, with no side condition on the parts. -/
def GluesGenerally (W : ∀ B : ℕ, BoundedComplex B → ℝ) : Prop :=
  ∀ {B B' : ℕ} (K : BoundedComplex B) (L : BoundedComplex B'),
    classMass (W (B + B')) (Quotient.mk (relabelSetoid (B + B')) (dunion K L))
      = classMass (W B) (Quotient.mk (relabelSetoid B) K)
        * classMass (W B') (Quotient.mk (relabelSetoid B') L)

/-- The uniform weight satisfies unrestricted gluing, at every pair, trivially. -/
theorem uniform_gluesGenerally :
    GluesGenerally (fun B => (uniformWeight : BoundedComplex B → ℝ)) := by
  intro B B' K L
  rw [classMass_uniform, classMass_uniform, classMass_uniform]
  norm_num

/-- The uniform weight's class mass is not the RS measure: a bouquet with two loops
has automorphism count two, so `mu` there is one half, while uniform mass is one. -/
theorem uniform_classMass_ne_mu :
    classMass uniformWeight (Quotient.mk (relabelSetoid (1 + 2 + 0)) (bouquet 2 0))
      ≠ mu (bouquet 2 0) := by
  rw [classMass_uniform]
  unfold mu
  rw [autCard_bouquet]
  norm_num [Nat.factorial]

/-- **THEOREM (premise (ii) alone excludes nothing).**  There is a relabeling-invariant
labeled weight whose class mass multiplies over *every* disjoint union, with no side
condition, and which is not the RS measure.  So the gluing premise carries no
discriminating power by itself: all of it is contributed by size-blindness, premise (i).

This is the strength measurement the honest-tag discipline requires, and it corrects
the framing of §5-§6: the two premises are not equal partners. -/
theorem gluing_alone_does_not_force_mu :
    GluesGenerally (fun B => (uniformWeight : BoundedComplex B → ℝ))
      ∧ classMass uniformWeight (Quotient.mk (relabelSetoid (1 + 2 + 0)) (bouquet 2 0))
          ≠ mu (bouquet 2 0) :=
  ⟨uniform_gluesGenerally, uniform_classMass_ne_mu⟩

/-- Dust has a single labeled presentation per class: with no incidence data to move,
every relabeling returns the same complex. -/
theorem orbitCard_dust (n : ℕ) : gaugeOrbitCard (dust n) = 1 := by
  have h := orbitCard_mul_autCard (dust n)
  rw [autCard_dust] at h
  have hd : (dust n).nV = n ∧ (dust n).nE = 0 ∧ (dust n).nT = 0 := ⟨rfl, rfl, rfl⟩
  rw [hd.1, hd.2.1, hd.2.2] at h
  simp only [Nat.factorial_zero, mul_one, one_mul] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos n) (by simpa using h)

/-- The class mass of a size-blind weight on dust is just its value at that size. -/
theorem classMass_sizeWeight_dust (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    classMass (sizeWeight f) (Quotient.mk (relabelSetoid n) (dust n)) = f n 0 0 := by
  rw [classMass_of_invariant _ (fun _ _ h => sizeWeight_invariant f h) _,
    sizeWeight_invariant f (equivalent_out (dust n)), orbitCardClass_mk, orbitCard_dust]
  unfold sizeWeight
  norm_num

namespace CarrierShuffle

variable {f : ℕ → ℕ → ℕ → ℝ}

/-- **THEOREM (the derived weight predicts the region the premise excludes).**  Premise
(ii) says nothing about `dust a ⊔ dust b`, since the two parts share a component.  The
weight forced by the two premises satisfies the binomial-corrected gluing identity
there anyway, matching `mu`'s own behaviour from C3 exactly.

This is the non-circularity receipt.  Had the side condition been reverse-engineered to
carve out the cases where the wanted answer fails, the excluded region would be where
the derivation breaks.  Instead it is where the derivation is confirmed. -/
theorem excludedRegion_predicted (h : CarrierShuffle f) (a b : ℕ) :
    classMass (sizeWeight f) (Quotient.mk (relabelSetoid (a + b)) (dust (a + b)))
        * (Nat.choose (a + b) a : ℝ)
      = classMass (sizeWeight f) (Quotient.mk (relabelSetoid a) (dust a))
        * classMass (sizeWeight f) (Quotient.mk (relabelSetoid b) (dust b)) := by
  rw [classMass_sizeWeight_dust, classMass_sizeWeight_dust, classMass_sizeWeight_dust]
  have hA := dustRow h a
  have hB := dustRow h b
  have hAB := dustRow h (a + b)
  have hchoose : (Nat.choose (a + b) a : ℝ) * (Nat.factorial a : ℝ) * (Nat.factorial b : ℝ)
      = (Nat.factorial (a + b) : ℝ) := by
    have hn : a ≤ a + b := Nat.le_add_right a b
    have hsub : a + b - a = b := by omega
    have := Nat.choose_mul_factorial_mul_factorial hn
    rw [hsub] at this
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
  have hfa : (Nat.factorial a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos a).ne'
  have hfb : (Nat.factorial b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos b).ne'
  refine mul_right_cancel₀ (mul_ne_zero hfa hfb) ?_
  calc f (a + b) 0 0 * (Nat.choose (a + b) a : ℝ)
        * ((Nat.factorial a : ℝ) * (Nat.factorial b : ℝ))
      = f (a + b) 0 0 * ((Nat.choose (a + b) a : ℝ) * (Nat.factorial a : ℝ)
          * (Nat.factorial b : ℝ)) := by ring
    _ = f (a + b) 0 0 * (Nat.factorial (a + b) : ℝ) := by rw [hchoose]
    _ = (f 1 0 0) ^ (a + b) := hAB
    _ = (f 1 0 0) ^ a * (f 1 0 0) ^ b := by rw [pow_add]
    _ = (f a 0 0 * (Nat.factorial a : ℝ)) * (f b 0 0 * (Nat.factorial b : ℝ)) := by
        rw [hA, hB]
    _ = f a 0 0 * f b 0 0 * ((Nat.factorial a : ℝ) * (Nat.factorial b : ℝ)) := by ring

end CarrierShuffle

/-! ## §9. The side condition is forced, not chosen

The sharpest charge against §5 is that the side condition on premise (ii) was
reverse-engineered: keep the pairs where the wanted answer survives, drop the rest.
Two compiled facts answer it, in place of an argument.

First, the premise set is **satisfiable**, and satisfied at the intended point: the
inverse gauge volume, which is the size function of `gibbsWeight`, meets all four
gluing instances with all three constants equal to one.  So §6 is not vacuously true.

Second, the **unrestricted** premise is *inconsistent* with size-blindness and
positivity.  Not "inconsistent with `mu`", which is §3 and invites the reply that the
cases where the answer fails were deleted.  Inconsistent full stop, on a statement
mentioning no measure, no automorphism count, and no factorial.  The four instances
the carrier supplies force the vertex recursion, which divides by the new vertex
count; unrestricted gluing applied to two piles of dust does not divide.

Together: the restriction is the boundary of consistency of the two premises, fixed
before any measure enters.  It could not have been chosen otherwise, so it cannot have
been fitted to an answer. -/

/-- The size function of the Gibbs weight: the inverse gauge volume. -/
noncomputable def gibbsSize (a b c : ℕ) : ℝ :=
  1 / ((Nat.factorial a : ℝ) * (Nat.factorial b : ℝ) * (Nat.factorial c : ℝ))

theorem factorial_cast_pos (n : ℕ) : (0 : ℝ) < (Nat.factorial n : ℝ) := by
  exact_mod_cast Nat.factorial_pos n

theorem gibbsSize_pos (a b c : ℕ) : 0 < gibbsSize a b c := by
  unfold gibbsSize
  have := factorial_cast_pos a
  have := factorial_cast_pos b
  have := factorial_cast_pos c
  positivity

theorem gibbsSize_eq_inv_gaugeVol (a b c : ℕ) :
    gibbsSize a b c = 1 / (gaugeVol a b c : ℝ) := by
  unfold gibbsSize gaugeVol
  push_cast
  ring

theorem gaugeVol_cast_pos (a b c : ℕ) : (0 : ℝ) < (gaugeVol a b c : ℝ) := by
  exact_mod_cast gaugeVol_pos a b c

/-- **THEOREM (the inverse gauge volume satisfies the shuffle identity at every
pair).**  This is `gaugeVol_add` read as a statement about weights: the gauge volume
of a sum of size triples exceeds the product by exactly the interleaving count, so its
reciprocal shuffles.  No side condition and no hypothesis. -/
theorem gibbsSize_shuffle (a b c a' b' c' : ℕ) :
    gibbsSize (a + a') (b + b') (c + c') * (interleave a b c a' b' c' : ℝ)
      = gibbsSize a b c * gibbsSize a' b' c' := by
  rw [gibbsSize_eq_inv_gaugeVol, gibbsSize_eq_inv_gaugeVol, gibbsSize_eq_inv_gaugeVol,
    gaugeVol_add a b c a' b' c']
  have h1 := gaugeVol_cast_pos a b c
  have h2 := gaugeVol_cast_pos a' b' c'
  have h3 : (0 : ℝ) < (interleave a b c a' b' c' : ℝ) := by
    exact_mod_cast interleave_pos a b c a' b' c'
  push_cast
  field_simp

/-- **THEOREM (the premise set is satisfiable, at the intended point).**  The inverse
gauge volume satisfies all four gluing instances.  Since `gibbsSize 1 0 0`,
`gibbsSize 1 1 0` and `gibbsSize 1 0 1` are all one, §6's three constants are attained
at unity, so `gibbs_of_unit_fugacities` has a witness and the derivation is not
vacuously true. -/
theorem gibbsSize_carrierShuffle : CarrierShuffle gibbsSize where
  pos := gibbsSize_pos
  unit := by norm_num [gibbsSize]
  dust_bouquet := by
    intro a b c _
    simpa [Nat.zero_add] using gibbsSize_shuffle a 0 0 1 b c
  dust_edge := by
    intro a
    simpa [Nat.zero_add] using gibbsSize_shuffle a 0 0 2 1 0
  bouquet_edge := by
    intro b c
    simpa [Nat.add_zero] using gibbsSize_shuffle 1 b c 2 1 0
  bouquet_tet := by
    intro b c
    simpa [Nat.add_zero] using gibbsSize_shuffle 1 b c 4 0 1

/-- **Premise (ii) with no side condition**: class mass multiplies over every disjoint
union, whatever the parts. -/
def GluesEverywhere (f : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ {B B' : ℕ} (K : BoundedComplex B) (L : BoundedComplex B'), GluesAt f K L

/-- Under the unrestricted premise, dust glues with no binomial correction at all. -/
theorem dust_glues_plainly (f : ℕ → ℕ → ℕ → ℝ) (hplain : GluesEverywhere f) (a b : ℕ) :
    f (a + b) 0 0 = f a 0 0 * f b 0 0 := by
  have h := hplain (dust a) (dust b)
  unfold GluesAt at h
  rw [show Quotient.mk (relabelSetoid (a + b)) (dunion (dust a) (dust b))
        = Quotient.mk (relabelSetoid (a + b)) (dust (a + b)) from
      Quotient.sound (dunion_dust_equivalent a b)] at h
  rw [classMass_sizeWeight_dust, classMass_sizeWeight_dust,
    classMass_sizeWeight_dust] at h
  exact h

/-- **THEOREM (the unrestricted premise is inconsistent, and the statement never
mentions the measure).**  No positive size-blind weight satisfies the four gluing
instances the carrier supplies *and* gluing at every pair.  The first forces
`f(a+1,0,0)·(a+1) = f(a,0,0)·f(1,0,0)`; the second forces
`f(a+b,0,0) = f(a,0,0)·f(b,0,0)`; at `a = b = 1` these give `2x² = x²`, so `x = 0`,
against positivity.

This is the receipt that the side condition is forced rather than fitted.  §3 showed
that `mu` fails unrestricted gluing, which leaves open the reply that the failing cases
were simply excluded.  This shows the *premises* fail unrestricted gluing, with no
measure named, so the exclusion is prior to any answer. -/
theorem unrestricted_gluing_inconsistent (f : ℕ → ℕ → ℕ → ℝ)
    (h : CarrierShuffle f) (hplain : GluesEverywhere f) : False := by
  have h1 := CarrierShuffle.vertexRec h 1
  have h2 := dust_glues_plainly f hplain 1 1
  have hpos := h.pos 1 0 0
  norm_num at h1 h2
  nlinarith [h1, h2, hpos]

/-- **THEOREM (some restriction is mandatory).**  The restricted premise is
satisfiable, by the inverse gauge volume; the unrestricted premise is satisfied by
nothing.  So a restriction on premise (ii) is not a convenience: dropping it entirely
makes the premise set empty.

Read the scope exactly.  This says a restriction is *necessary*.  It does not say the
particular restriction used here is the *only* one that would restore consistency, and
several others plainly would.  What removes the remaining worry is not this theorem but
`all_four_families_available`: the derivation consumes four named instances, each of
them proved, so it never depends on where the general boundary is drawn. -/
theorem restriction_is_mandatory :
    CarrierShuffle gibbsSize ∧ (∀ f : ℕ → ℕ → ℕ → ℝ, CarrierShuffle f → ¬ GluesEverywhere f) :=
  ⟨gibbsSize_carrierShuffle, fun f h hp => unrestricted_gluing_inconsistent f h hp⟩

/-! ## §9a. The transport runs both ways, and which size triples exist

Two gaps a second hostile read found in the write-up, both closed here rather than
hedged in prose.  The first: `shuffle_of_gluesAt` proves the premise implies the
shuffle identity, so `CarrierShuffle` was only known to be *implied by* premise (ii),
and a reader was entitled to say the structure is four algebraic equations rather than
the premise.  At an eligible pair the transport is an equivalence, so the converse is
the same algebra run backwards.  The second: `closedForm` says nothing at triples with
no vertex, which is harmless only because the carrier cannot realize them, and that
fact was assumed rather than proved. -/

/-- **THEOREM (the transport is an equivalence at an eligible pair).**  Converse of
`shuffle_of_gluesAt`.  Together they say that at a pair where automorphism counts
multiply, the shuffle identity on the size function and premise (ii) on the class mass
are the same statement, so `CarrierShuffle` is the premise at those four families and
not merely a consequence of it. -/
theorem gluesAt_of_shuffle (f : ℕ → ℕ → ℕ → ℝ) {B B' : ℕ}
    (K : BoundedComplex B) (L : BoundedComplex B')
    (haut : Nat.card (Aut (dunion K L)) = Nat.card (Aut K) * Nat.card (Aut L))
    (hsh : f (K.nV + L.nV) (K.nE + L.nE) (K.nT + L.nT)
            * (interleave K.nV K.nE K.nT L.nV L.nE L.nT : ℝ)
          = f K.nV K.nE K.nT * f L.nV L.nE L.nT) :
    GluesAt f K L := by
  have hob := orbitCard_dunion_of_autMul K L haut
  unfold GluesAt
  rw [classMass_sizeWeight, classMass_sizeWeight, classMass_sizeWeight]
  simp only [dunion_nV, dunion_nE, dunion_nT]
  rw [hob]
  push_cast
  calc (interleave K.nV K.nE K.nT L.nV L.nE L.nT : ℝ)
        * ((gaugeOrbitCard K : ℝ) * (gaugeOrbitCard L : ℝ))
        * f (K.nV + L.nV) (K.nE + L.nE) (K.nT + L.nT)
      = (f (K.nV + L.nV) (K.nE + L.nE) (K.nT + L.nT)
          * (interleave K.nV K.nE K.nT L.nV L.nE L.nT : ℝ))
        * ((gaugeOrbitCard K : ℝ) * (gaugeOrbitCard L : ℝ)) := by ring
    _ = (f K.nV K.nE K.nT * f L.nV L.nE L.nT)
        * ((gaugeOrbitCard K : ℝ) * (gaugeOrbitCard L : ℝ)) := by rw [hsh]
    _ = (gaugeOrbitCard K : ℝ) * f K.nV K.nE K.nT
        * ((gaugeOrbitCard L : ℝ) * f L.nV L.nE L.nT) := by ring

/-- **THEOREM (any incidence needs a vertex to carry it).**  A complex with an edge or
a tetrahedron has at least one vertex, since both incidence maps land in `Fin nV` and
that type is empty when `nV = 0`.  So the size triples the carrier realizes all have
`1 ≤ nV`, which is exactly the hypothesis `closedForm` carries: the closed form pins
the size function at every triple that any complex actually has, and its silence at
`(0, b, c)` with `b + c ≥ 1` is silence about sizes nothing can have. -/
theorem vertex_of_incidence {B : ℕ} (K : BoundedComplex B) (h : 1 ≤ K.nE + K.nT) :
    1 ≤ K.nV := by
  by_contra hv
  push_neg at hv
  have hv0 : K.nV = 0 := by omega
  rcases Nat.lt_or_ge 0 K.nE with he | he
  · have hx := (K.edgeVerts ⟨0, he⟩).1.isLt
    omega
  · have ht : 0 < K.nT := by omega
    have hx := (K.tetVerts ⟨0, ht⟩ 0).isLt
    omega

/-- The closed form applies to every complex the carrier contains: either it has a
vertex, or it is the empty complex, where `unit` already gives the value. -/
theorem closedForm_or_empty {f : ℕ → ℕ → ℕ → ℝ} (h : CarrierShuffle f) {B : ℕ}
    (K : BoundedComplex B) :
    (1 ≤ K.nV) ∨ (K.nV = 0 ∧ K.nE = 0 ∧ K.nT = 0) := by
  rcases Nat.lt_or_ge 0 (K.nE + K.nT) with hi | hi
  · exact Or.inl (vertex_of_incidence K hi)
  · rcases Nat.lt_or_ge 0 K.nV with hv | hv
    · exact Or.inl hv
    · exact Or.inr ⟨by omega, by omega, by omega⟩

/-! ## §9b. Where the symmetry factor actually comes from

Added 2026-07-28 after a hostile read of the write-up located a misattribution in
the headline, not in any proof.  The natural summary of this module, "two premises
force the class measure to `1/|Aut|` up to three constants", credits the wrong
premise with the `1/|Aut|`.  The two theorems below measure it instead of asserting
it, and the first of them deflates the headline.  Keep them next to the derivation
so the next reader cannot restate it the old way. -/

/-- The **sector fugacity** of a size-blind weight: the gauge volume of a size triple
times the weight there.  It is everything about a size-blind weight that
orbit-stabilizer has not already fixed. -/
noncomputable def fugacityOf (f : ℕ → ℕ → ℕ → ℝ) (a b c : ℕ) : ℝ :=
  (gaugeVol a b c : ℝ) * f a b c

/-- **THEOREM (premise (i) alone already produces the symmetry factor).**  For *any*
size-blind weight whatever, positive or not, normalized or not, the class mass of a
class is its sector fugacity divided by the automorphism count.  The only inputs are
premise (i) and `orbitCard_mul_autCard`, which the carrier had before this module
existed.  No gluing premise is used, and none is even available at this point.

The consequence for the derivation is worth stating flatly, because it is easy to
claim the opposite.  The `1/|Aut K|` dependence is a consequence of size-blindness.
Premise (ii) does not produce it and could not, since it is already here before
premise (ii) is stated.  What premise (ii) does is force `fugacityOf f` to be a
character rather than an arbitrary function of the three sizes, which is the content
of `closedForm`; and the unit character is what makes the constant one. -/
theorem classMass_sizeWeight_eq_fugacity_div_autCard
    (f : ℕ → ℕ → ℕ → ℝ) {B : ℕ} (K : BoundedComplex B) :
    classMass (sizeWeight f) (Quotient.mk (relabelSetoid B) K)
      = fugacityOf f K.nV K.nE K.nT / (Nat.card (Aut K) : ℝ) := by
  have hmul : (gaugeOrbitCard K : ℝ) * (Nat.card (Aut K) : ℝ)
      = (gaugeVol K.nV K.nE K.nT : ℝ) := by
    have h := orbitCard_mul_autCard K
    unfold gaugeVol
    exact_mod_cast h
  have hA : (0 : ℝ) < (Nat.card (Aut K) : ℝ) := by
    exact_mod_cast autCard_pos K
  rw [classMass_sizeWeight, eq_div_iff hA.ne', fugacityOf]
  calc (gaugeOrbitCard K : ℝ) * f K.nV K.nE K.nT * (Nat.card (Aut K) : ℝ)
      = ((gaugeOrbitCard K : ℝ) * (Nat.card (Aut K) : ℝ)) * f K.nV K.nE K.nT := by ring
    _ = (gaugeVol K.nV K.nE K.nT : ℝ) * f K.nV K.nE K.nT := by rw [hmul]

/-- The **character weights**: one positive number per index type, spread over the
gauge volume.  `gibbsSize` is the member with all three equal to one. -/
noncomputable def characterSize (u v w : ℝ) (a b c : ℕ) : ℝ :=
  (u ^ a * v ^ b * w ^ c) / (gaugeVol a b c : ℝ)

theorem characterSize_shuffle (u v w : ℝ) (a b c a' b' c' : ℕ) :
    characterSize u v w (a + a') (b + b') (c + c') * (interleave a b c a' b' c' : ℝ)
      = characterSize u v w a b c * characterSize u v w a' b' c' := by
  unfold characterSize
  rw [gaugeVol_add a b c a' b' c']
  have h1 := gaugeVol_cast_pos a b c
  have h2 := gaugeVol_cast_pos a' b' c'
  have h3 : (0 : ℝ) < (interleave a b c a' b' c' : ℝ) := by
    exact_mod_cast interleave_pos a b c a' b' c'
  push_cast
  field_simp
  ring

theorem characterSize_carrierShuffle {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    CarrierShuffle (characterSize u v w) where
  pos := by
    intro a b c
    unfold characterSize
    have := gaugeVol_cast_pos a b c
    positivity
  unit := by norm_num [characterSize, gaugeVol]
  dust_bouquet := by
    intro a b c _
    simpa [Nat.zero_add] using characterSize_shuffle u v w a 0 0 1 b c
  dust_edge := by
    intro a
    simpa [Nat.zero_add] using characterSize_shuffle u v w a 0 0 2 1 0
  bouquet_edge := by
    intro b c
    simpa [Nat.add_zero] using characterSize_shuffle u v w 1 b c 2 1 0
  bouquet_tet := by
    intro b c
    simpa [Nat.add_zero] using characterSize_shuffle u v w 1 b c 4 0 1

theorem gibbsSize_eq_characterSize_one : gibbsSize = characterSize 1 1 1 := by
  funext a b c
  rw [gibbsSize_eq_inv_gaugeVol]
  unfold characterSize
  norm_num

/-- **THEOREM (the residue is exactly three positive constants, not at most three).**
Forward, `closedForm`: every solution of the premise set has the three-constant form.
Backward: every positive triple is realized by an actual solution.  Both directions
are needed before the residue can be called a three-parameter family, and the
backward one also settles a question about strategy: no further gluing family can
ever shrink the residue, because the whole three-parameter family satisfies the
shuffle identity at every pair unconditionally, by `characterSize_shuffle`. -/
theorem residue_is_exactly_three_positive_constants :
    (∀ f : ℕ → ℕ → ℕ → ℝ, CarrierShuffle f → ∀ a b c : ℕ, 1 ≤ a →
        f a b c * ((Nat.factorial a : ℝ) * (Nat.factorial b : ℝ) * (Nat.factorial c : ℝ))
            * (f 1 0 0) ^ (b + c)
          = (f 1 0 0) ^ a * (f 1 1 0) ^ b * (f 1 0 1) ^ c)
      ∧ (∀ u v w : ℝ, 0 < u → 0 < v → 0 < w → CarrierShuffle (characterSize u v w)) :=
  ⟨fun _ h a b c ha => h.closedForm a b c ha,
    fun _ _ _ hu hv hw => characterSize_carrierShuffle hu hv hw⟩

/-! ## §10. Certificate: what is derived, what is assumed, what remains -/

/-- The state of the gluing route after this module. -/
structure GluingStatus where
  /-- The carrier now carries a disjoint union (previously recorded as missing). -/
  dunion_exists : Bool
  /-- The interleaving count is binomial, as pure arithmetic on gauge volumes. -/
  interleaving_binomial : Bool
  /-- Unrestricted gluing multiplicativity is refuted against `mu` itself. -/
  unrestricted_gluing_refuted : Bool
  /-- Automorphism multiplicativity is the exact residue for transporting the
  binomial identity to orbit counts. -/
  autmul_is_the_residue : Bool
  /-- Size-blindness plus gluing is exactly the shuffle identity where `Aut`
  multiplies. -/
  premises_give_shuffle : Bool
  /-- The two premises force the weight up to three constants. -/
  three_constants : Bool
  /-- Unit values for those three constants give exactly `gibbsWeight`. -/
  units_give_gibbs : Bool
  /-- One nontrivial family of gluing instances is verified available. -/
  availability_witnessed : Bool
  /-- All four gluing instances the premise set uses are verified available, each over
  an unbounded family. -/
  all_four_families_available : Bool
  /-- Measured: premise (ii) alone excludes nothing, so premise (i) carries the force. -/
  gluing_alone_is_empty : Bool
  /-- Measured: the derived weight predicts the region premise (ii) declines to
  speak about, which is the non-circularity receipt. -/
  excluded_region_predicted : Bool
  /-- The premise set is satisfiable, and satisfied at the intended unit point. -/
  premises_satisfiable : Bool
  /-- The unrestricted premise is satisfied by nothing, so some restriction on
  premise (ii) is mandatory rather than a carve-out. -/
  restriction_is_mandatory : Bool
  /-- NOT proved: the general no-mixing theorem for parts sharing no isomorphic
  component. -/
  general_autmul_formalized : Bool
  /-- NOT proved: that the three constants must equal one. -/
  three_constants_forced : Bool

/-- Status after this module. -/
def gluingStatus : GluingStatus where
  dunion_exists := true
  interleaving_binomial := true
  unrestricted_gluing_refuted := true
  autmul_is_the_residue := true
  premises_give_shuffle := true
  three_constants := true
  units_give_gibbs := true
  availability_witnessed := true
  all_four_families_available := true
  gluing_alone_is_empty := true
  excluded_region_predicted := true
  premises_satisfiable := true
  restriction_is_mandatory := true
  general_autmul_formalized := false
  three_constants_forced := false

theorem status_dunion : gluingStatus.dunion_exists = true := rfl
theorem status_binomial : gluingStatus.interleaving_binomial = true := rfl
theorem status_refuted : gluingStatus.unrestricted_gluing_refuted = true := rfl
theorem status_residue : gluingStatus.autmul_is_the_residue = true := rfl
theorem status_shuffle : gluingStatus.premises_give_shuffle = true := rfl
theorem status_three : gluingStatus.three_constants = true := rfl
theorem status_units : gluingStatus.units_give_gibbs = true := rfl
theorem status_witness : gluingStatus.availability_witnessed = true := rfl
theorem status_all_four : gluingStatus.all_four_families_available = true := rfl
theorem status_gluing_empty : gluingStatus.gluing_alone_is_empty = true := rfl
theorem status_excluded : gluingStatus.excluded_region_predicted = true := rfl
theorem status_satisfiable : gluingStatus.premises_satisfiable = true := rfl
theorem status_forced : gluingStatus.restriction_is_mandatory = true := rfl

/-- **The two honest negatives.**  The general no-mixing theorem is not formalized,
and nothing here forces the three constants to equal one.  Both flags are `false`
by construction, so the certificate cannot drift into claiming them. -/
theorem status_open :
    gluingStatus.general_autmul_formalized = false ∧
    gluingStatus.three_constants_forced = false :=
  ⟨rfl, rfl⟩

end Gap2GluingDerivation
end SevenGaps
end Gravity
end IndisputableMonolith
