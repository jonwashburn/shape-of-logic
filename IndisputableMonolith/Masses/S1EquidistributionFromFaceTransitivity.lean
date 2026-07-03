import Mathlib
import IndisputableMonolith.Masses.L1bHyperoctahedralGroup
import IndisputableMonolith.Masses.TrailingSpanDistribution

/-!
# S1 relocation: Span Equidistribution from Hyperoctahedral Face Transitivity

This module RELOCATES the MODEL premise **S1**
(`TrailingSpanDistribution.SpanEquidistributionPremise f := ∀ i j, f i = f j`, the
uniform distribution of the φ/2 trailing debit over the 6 rung-increments) from an
ad hoc uniformity assumption to **O_h-invariance of the rung-share profile**, exactly
parallel to the banked L1_Test2 octahedral pattern (vertex uniformity from a
transitive hyperoctahedral action).

## The geometry

The trailing span is the cube face count: `Δr_32 = 6 = cube_faces' 3`
(`SectorDependentTorsion.lepton_step_23_eq`, proved upstream). The hyperoctahedral
group `B3` (the 48 signed permutations, `L1bHyperoctahedralGroup.SignedPerm`) acts on
the 6 faces of the cube, and — the load-bearing fact proved here — that action is
**transitive** (`MulAction.IsPretransitive SignedPerm Face`). Hence any B3-invariant
share profile on the faces is constant, and pulling back along an explicit
rung-increments↔faces identification `e : Fin 6 ≃ Face` yields the ACTUAL premise
`SpanEquidistributionPremise` as a theorem.

## Refutation of the recorded KILL condition

`TrailingSpanDistribution` recorded a kill condition for this route: "KILL if the
recognition group acts with 3 antipodal orbits on the faces." The full B3 does NOT:
a pure sign flip on axis `0` maps the face `+e₀` to `−e₀` **within one orbit**
(witness `axisFlip_smul` below), so the transitivity instance constructively refutes
the 3-antipodal-orbit scenario as the default. That scenario would require the
recognition-relevant symmetry to be a *proper subgroup* preserving each antipodal
pair sign-wise, which is exactly what the residual below names.

## What is proved (THEOREM layer, no `sorry`, axiom-clean)

* `Face` (= `Bool × Fin 3`, sign × axis) has exactly 6 elements (`card_face`).
* `faceAct` is a genuine left `MulAction SignedPerm Face` (semidirect law verified,
  `faceAct_mul` closing by `Bool.xor_assoc`), induced by the linear action on
  `Fin 3 → ℝ`: the face `{v : v i = ±1}` maps to axis `g.perm⁻¹ i` with sign twisted
  by `g.sign (g.perm⁻¹ i)`.
* **Transitivity** (`instIsPretransitive`): explicit witness via `Equiv.swap` plus a
  targeted sign pattern — no finite search over the 48·6·6 table, fully axiom-clean.
* **Collapse** (`invariant_const`): any B3-invariant `F : Face → ℝ` is constant,
  routed through `MulAction.exists_smul_eq` (the transporting group element), not a
  case bash.
* **Bridge** (`equidistribution_from_face_invariance`): a B3-invariant share profile
  satisfies the ACTUAL `TrailingSpanDistribution.SpanEquidistributionPremise` after
  the identification `e` — the relocation itself.
* **End-to-end** (`perRungTorsion_from_face_invariance`): O_h-invariance + T1 total
  `φ/2` + S2 sign ⇒ every rung carries `−(φ/2)/6`, chaining into the banked
  conditional forcing theorem `TrailingSpanDistribution.perRungTorsion_forced`.
* **Non-vacuity**: (a) the action genuinely moves points (`axisFlip_moves`); (b) the
  invariance hypothesis excludes real profiles: the spike profile concentrated on one
  face is NOT invariant (`spike_not_invariant`) — the face-side analog of the
  library's `endpointProfile_not_uniform`.

## Honest residual MODEL floor (NOT closed here)

The relocation replaces "shares are uniform" (ad hoc) with two sharper commitments:

1. **O_h-invariance of the physical rung-share profile** under THIS face action. If
   the recognition-relevant symmetry were a proper subgroup fixing each antipodal
   face pair sign-wise (3 orbits), the relocation would not bind; full-B3
   transitivity rules that out only as the *default* symmetry of the recognition
   geometry, not as a theorem about the physical profile.
2. **The rung-increments↔faces identification** `e : Fin 6 ≃ Face`. The span *count*
   6 = faces is proved upstream; that the six rung-increments ARE the six faces (not
   merely equinumerous) is a modeling identification.

Uniformity is now a THEOREM conditional on (1)+(2). Tier: THEOREM (bridge) on top of
a sharpened MODEL floor.

Lean status: no `sorry`; no new axioms beyond Mathlib base; no `native_decide`.
-/

namespace IndisputableMonolith
namespace Masses
namespace S1EquidistributionFromFaceTransitivity

open L1bHyperoctahedralGroup
open Constants

noncomputable section

/-! ## The face type: 6 faces of the cube as sign × axis -/

/-- A face of the cube `[-1,1]³`: the pair (sign-of-face, axis). `(false, i)` is the
`+e_i` face `{v : v i = +1}`; `(true, i)` is the `−e_i` face `{v : v i = −1}`. -/
abbrev Face : Type := Bool × Fin 3

/-- The cube has exactly `6` faces — the trailing span
(`SectorDependentTorsion.lepton_step_23 = 6`). -/
theorem card_face : Fintype.card Face = 6 := by
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]

/-! ## The face action induced by the linear action -/

/-- The action of a signed permutation on faces, induced by the linear action
`(g • v) j = ±v (g.perm j)` on `Fin 3 → ℝ`: the face `{v : v i = s}` maps to the face
on axis `g.perm⁻¹ i` with sign twisted by `g.sign (g.perm⁻¹ i)`. -/
def faceAct (g : SignedPerm) (f : Face) : Face :=
  (xor (g.sign (g.perm⁻¹ f.2)) f.1, g.perm⁻¹ f.2)

theorem faceAct_one (f : Face) : faceAct 1 f = f := by
  obtain ⟨s, i⟩ := f
  unfold faceAct
  simp

theorem faceAct_mul (g h : SignedPerm) (f : Face) :
    faceAct (g * h) f = faceAct g (faceAct h f) := by
  obtain ⟨s, i⟩ := f
  unfold faceAct
  simp only [SignedPerm.mul_sign, SignedPerm.mul_perm, Equiv.Perm.inv_def,
    Equiv.symm_trans_apply, Equiv.apply_symm_apply, Prod.mk.injEq]
  exact ⟨Bool.xor_assoc _ _ _, trivial⟩

/-- The 6 faces carry a genuine left action of the hyperoctahedral group. -/
instance : MulAction SignedPerm Face where
  smul := faceAct
  one_smul := faceAct_one
  mul_smul := faceAct_mul

@[simp] theorem face_smul_def (g : SignedPerm) (f : Face) : g • f = faceAct g f := rfl

/-! ## Transitivity (the load-bearing fact) -/

/-- **B3 acts transitively on the 6 faces.** Explicit witness: to send face `(s, i)`
to face `(t, j)`, use the transposition `swap i j` with the sign pattern that places
`xor s t` at slot `j`. Axiom-clean (no finite search, no `decide` over the group). -/
instance instIsPretransitive : MulAction.IsPretransitive SignedPerm Face where
  exists_smul_eq := by
    rintro ⟨s, i⟩ ⟨t, j⟩
    refine ⟨⟨Equiv.swap i j, fun k => if k = j then xor s t else false⟩, ?_⟩
    show (xor (if (Equiv.swap i j)⁻¹ i = j then xor s t else false) s,
        (Equiv.swap i j)⁻¹ i) = (t, j)
    rw [Equiv.Perm.inv_def, Equiv.symm_swap, Equiv.swap_apply_left, if_pos rfl]
    cases s <;> cases t <;> rfl

/-! ## Collapse: invariant profiles are constant -/

/-- **Collapse.** Any B3-invariant real profile on the faces is constant. The proof
routes through transitivity: obtain the transporting `g` with `g • f = f'` and
rewrite — not a case bash that never uses the group. -/
theorem invariant_const (F : Face → ℝ)
    (hinv : ∀ (g : SignedPerm) (f : Face), F (g • f) = F f) (f f' : Face) :
    F f = F f' := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SignedPerm f f'
  rw [← hg, hinv g f]

/-! ## The rung-increments↔faces identification -/

/-- Explicit table `Fin 6 → Face`: increments `0,1,2 ↦ +e₀,+e₁,+e₂` and
`3,4,5 ↦ −e₀,−e₁,−e₂`. -/
def toFace (k : Fin 6) : Face :=
  if h : (k : ℕ) < 3 then (false, ⟨(k : ℕ), h⟩)
  else (true, ⟨(k : ℕ) - 3, by have := k.isLt; omega⟩)

/-- Explicit inverse table `Face → Fin 6`. -/
def ofFace (f : Face) : Fin 6 :=
  ⟨(if f.1 then 3 else 0) + (f.2 : ℕ), by
    have h2 := f.2.isLt
    by_cases hb : f.1 <;> simp [hb] <;> omega⟩

theorem ofFace_toFace : ∀ k : Fin 6, ofFace (toFace k) = k := by decide

theorem toFace_ofFace : ∀ f : Face, toFace (ofFace f) = f := by decide

/-- The explicit identification of the 6 trailing rung-increments with the 6 faces.
This identification is part of the honest residual MODEL floor (see module
docstring). -/
def e : Fin 6 ≃ Face where
  toFun := toFace
  invFun := ofFace
  left_inv := ofFace_toFace
  right_inv := toFace_ofFace

/-! ## The bridge: the relocation itself -/

/-- **The relocation (capstone).** A B3-invariant share profile on the faces
satisfies the ACTUAL S1 premise
`TrailingSpanDistribution.SpanEquidistributionPremise` on the rung-increments, via
the identification `e`. The ad hoc "shares are uniform" is now a THEOREM conditional
on "shares are O_h-invariant" — a symmetry of the recognition geometry. -/
theorem equidistribution_from_face_invariance (share : Face → ℝ)
    (hinv : ∀ (g : SignedPerm) (f : Face), share (g • f) = share f) :
    TrailingSpanDistribution.SpanEquidistributionPremise
      (fun k : Fin 6 => share (e k)) := by
  unfold TrailingSpanDistribution.SpanEquidistributionPremise
  intro i j
  exact invariant_const share hinv (e i) (e j)

/-- **End-to-end forcing.** O_h-invariance of the share profile, the T1 total `φ/2`,
and the S2 closure sign force every rung's torsion to `−(φ/2)/6`, by chaining the
relocation into the banked conditional forcing theorem
`TrailingSpanDistribution.perRungTorsion_forced`. -/
theorem perRungTorsion_from_face_invariance
    {sign : ℝ} (share : Face → ℝ)
    (hinv : ∀ (g : SignedPerm) (f : Face), share (g • f) = share f)
    (htot : (∑ k : Fin 6, share (e k)) = phi / 2)
    (hS2 : TrailingSpanDistribution.ClosureSignPremise sign)
    (i : Fin 6) :
    TrailingSpanDistribution.perRungTorsion sign (fun k : Fin 6 => share (e k)) i
      = -(phi / 2) / 6 :=
  TrailingSpanDistribution.perRungTorsion_forced (by norm_num)
    (fun k : Fin 6 => share (e k))
    (equidistribution_from_face_invariance share hinv) htot rfl hS2 i

/-! ## Non-vacuity witnesses -/

/-- The pure sign flip on axis 0 (identity permutation, flip coordinate 0). -/
def axisFlip : SignedPerm := ⟨1, fun k => decide (k = 0)⟩

/-- The sign flip maps the `+e₀` face to the `−e₀` face: antipodal faces lie in ONE
orbit. This is the constructive refutation of the recorded 3-antipodal-orbit KILL
condition for the full B3. -/
theorem axisFlip_smul : axisFlip • ((false, 0) : Face) = ((true, 0) : Face) := by
  show faceAct axisFlip (false, 0) = (true, 0)
  rfl

/-- **Non-vacuity (a): the action moves points.** `g • f ≠ f` for the sign flip on
the `+e₀` face — the invariance hypothesis quantifies over a genuinely nontrivial
action. -/
theorem axisFlip_moves : axisFlip • ((false, 0) : Face) ≠ ((false, 0) : Face) := by
  rw [axisFlip_smul]
  decide

/-- A spike profile concentrated on the single face `+e₀`. -/
def spike : Face → ℝ := fun f => if f = (false, 0) then 1 else 0

/-- **Non-vacuity (b): the invariance hypothesis excludes real profiles.** The spike
profile is NOT B3-invariant (the sign flip moves its support), so
`equidistribution_from_face_invariance` is not satisfied vacuously — it genuinely
constrains which share profiles qualify. Face-side analog of
`TrailingSpanDistribution.endpointProfile_not_uniform`. -/
theorem spike_not_invariant :
    ¬ (∀ (g : SignedPerm) (f : Face), spike (g • f) = spike f) := by
  intro h
  have h0 := h axisFlip (false, 0)
  rw [axisFlip_smul] at h0
  unfold spike at h0
  rw [if_neg (by decide : ¬ (((true, 0) : Face) = ((false, 0) : Face))),
    if_pos rfl] at h0
  norm_num at h0

/-! ## Certificate bundling the relocation -/

/-- Certificate for the S1 relocation: face count, transitivity-driven collapse, the
bridge to the ACTUAL premise, and both non-vacuity witnesses. -/
structure S1RelocationCert where
  faces_are_span :
    Fintype.card Face = 6
  collapse :
    ∀ (F : Face → ℝ), (∀ (g : SignedPerm) (f : Face), F (g • f) = F f) →
      ∀ f f', F f = F f'
  bridge :
    ∀ (share : Face → ℝ), (∀ (g : SignedPerm) (f : Face), share (g • f) = share f) →
      TrailingSpanDistribution.SpanEquidistributionPremise
        (fun k : Fin 6 => share (e k))
  action_moves :
    axisFlip • ((false, 0) : Face) ≠ ((false, 0) : Face)
  invariance_excludes :
    ¬ (∀ (g : SignedPerm) (f : Face), spike (g • f) = spike f)

theorem s1RelocationCert_holds : Nonempty S1RelocationCert :=
  ⟨{ faces_are_span := card_face
     collapse := invariant_const
     bridge := equidistribution_from_face_invariance
     action_moves := axisFlip_moves
     invariance_excludes := spike_not_invariant }⟩

end

end S1EquidistributionFromFaceTransitivity
end Masses
end IndisputableMonolith
