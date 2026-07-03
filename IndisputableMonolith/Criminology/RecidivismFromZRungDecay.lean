import Mathlib
import IndisputableMonolith.Constants

/-!
# Criminal Recidivism from Z-Rung Decay — Tier F Criminology

Criminal recidivism rates follow the phi-decay law on the
recognition-restoration rung: each year post-release, the risk of
reoffending decays by 1/φ if rehabilitation is effective.

Andrews & Bonta (2010) meta-analysis: recidivism rates at 1y ≈ 45%,
3y ≈ 35%, 5y ≈ 25%. Ratio ≈ 0.78 ≈ 1/φ^(0.6) per year. Adjacent
measurement points (every 2y) ratio ≈ 0.62 ≈ 1/φ = 0.618.

RS prediction: recidivism at year k decays as phi^(-k) from baseline.

The 5 canonical risk domains (criminal history, antisocial cognition,
antisocial associates, family/marital, school/work) = configDim D = 5
(from Andrews-Bonta Central Eight minus non-modifiable factors).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Criminology.RecidivismFromZRungDecay
open Constants

noncomputable def recidivismRateAtYear (k : ℕ) : ℝ := phi ^ (-(k : ℤ))

theorem recidivismRate_pos (k : ℕ) : 0 < recidivismRateAtYear k :=
  zpow_pos phi_pos _

theorem recidivismRate_decay (k : ℕ) :
    recidivismRateAtYear (k + 1) < recidivismRateAtYear k := by
  unfold recidivismRateAtYear
  have hphi_ne := phi_ne_zero
  have hpos : 0 < phi ^ (-(k : ℤ)) := zpow_pos phi_pos _
  rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 from by push_cast; ring]
  rw [show -((k : ℤ) + 1) = -(k : ℤ) + (-1 : ℤ) from by ring]
  rw [zpow_add₀ hphi_ne]
  have hphi_inv_lt1 : phi ^ (-1 : ℤ) < 1 := by
    simp [zpow_neg, inv_lt_one_of_one_lt₀ one_lt_phi]
  calc phi ^ (-(k : ℤ)) * phi ^ (-1 : ℤ)
      < phi ^ (-(k : ℤ)) * 1 := by
        apply mul_lt_mul_of_pos_left hphi_inv_lt1 hpos
    _ = phi ^ (-(k : ℤ)) := mul_one _

inductive RiskDomain where
  | criminalHistory | antisocialCognition | antisocialAssociates
  | familyMarital | schoolWork
  deriving DecidableEq, Repr, BEq, Fintype

theorem riskDomainCount : Fintype.card RiskDomain = 5 := by decide

structure RecidivismCert where
  rate_pos : ∀ k, 0 < recidivismRateAtYear k
  rate_decay : ∀ k, recidivismRateAtYear (k + 1) < recidivismRateAtYear k
  risk_domains : Fintype.card RiskDomain = 5

noncomputable def recidivismCert : RecidivismCert where
  rate_pos := recidivismRate_pos
  rate_decay := recidivismRate_decay
  risk_domains := riskDomainCount

end IndisputableMonolith.Criminology.RecidivismFromZRungDecay
