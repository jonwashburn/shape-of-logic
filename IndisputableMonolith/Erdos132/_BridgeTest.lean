import IndisputableMonolith.Erdos132.SlotBound

/-!
Scratch validation of the **keystone bridge lemma**: the sound polynomial reduction
that turns each realized pairwise-distance constraint of six general slots into a
square-root-free polynomial equation in `(u², v²)`.

For the INFEASIBILITY (keystone) direction we only need soundness: every real
configuration satisfies the squared-membership identity, and a certificate that a
chosen small subsystem of those identities has no common root in the open unit
square refutes the configuration. The sign-consistency condition (needed only to
FIND a witness) is dropped, so no `sqrt` algebra is required.
-/

noncomputable section

namespace Erdos132.BridgeTest

open Erdos132.SlotBound

/-- **Bridge lemma.** Two general slots with slot data `(s2i,t2i)`, `(s2j,t2j)` whose
pairwise squared distance is `c` satisfy the square-root-free polynomial identity
`(Mᵢⱼ − c)² = 4·Yᵢ·Yⱼ`, where `Mᵢⱼ = (xᵢ−xⱼ)² + Yᵢ + Yⱼ`. Squaring the genuine
signed-distance equation `2·yᵢ·yⱼ = Mᵢⱼ − c` eliminates the cross term; the identity
is an UNCONDITIONAL consequence of the geometry (sound for refutation). -/
theorem pair_membership_poly (pi pj : ℝ × ℝ)
    (s2i t2i s2j t2j c : ℝ)
    (hxi : pi.1 = slotX s2i t2i) (hyi : pi.2 ^ 2 = slotYsq s2i t2i)
    (hxj : pj.1 = slotX s2j t2j) (hyj : pj.2 ^ 2 = slotYsq s2j t2j)
    (hc : d2 pi pj = c) :
    ((slotX s2i t2i - slotX s2j t2j) ^ 2 + slotYsq s2i t2i + slotYsq s2j t2j - c) ^ 2
      = 4 * slotYsq s2i t2i * slotYsq s2j t2j := by
  -- Write out d2 in terms of the pinned x-coordinates.
  have hd : (slotX s2i t2i - slotX s2j t2j) ^ 2 + (pi.2 - pj.2) ^ 2 = c := by
    have h := hc
    simp only [d2] at h
    rw [hxi, hxj] at h
    exact h
  have hexp : (pi.2 - pj.2) ^ 2 = pi.2 ^ 2 - 2 * pi.2 * pj.2 + pj.2 ^ 2 := by ring
  -- The cross-term equation (still contains yᵢyⱼ, but that is about to be squared away).
  have hcross : 2 * pi.2 * pj.2
      = (slotX s2i t2i - slotX s2j t2j) ^ 2 + slotYsq s2i t2i + slotYsq s2j t2j - c := by
    linarith [hd, hexp, hyi, hyj]
  -- Square the cross-term equation; yᵢ²·yⱼ² is a polynomial via hyi, hyj.
  have hsub : (slotX s2i t2i - slotX s2j t2j) ^ 2 + slotYsq s2i t2i + slotYsq s2j t2j - c
      = 2 * pi.2 * pj.2 := hcross.symm
  rw [hsub]
  have : (2 * pi.2 * pj.2) ^ 2 = 4 * pi.2 ^ 2 * pj.2 ^ 2 := by ring
  rw [this, hyi, hyj]

end Erdos132.BridgeTest
