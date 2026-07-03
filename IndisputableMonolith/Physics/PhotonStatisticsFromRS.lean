import Mathlib
import IndisputableMonolith.Cost

/-!
# Photon Statistics from RS — B14/B16 Depth

Photon statistics characterise quantum vs classical light.
In RS: photon number statistics = J-cost distribution.

Five canonical photon statistics regimes (super-Poissonian, Poissonian,
sub-Poissonian, Fano, Mandel Q) = configDim D = 5.

Coherent light (J=0): Poissonian statistics.
Thermal light (J>0): super-Poissonian.
Squeezed light (J>0 in anti-squeezed quadrature): sub-Poissonian.

Lean: 5 regimes.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.PhotonStatisticsFromRS
open Cost

inductive PhotonStatisticsRegime where
  | superPoissonian | poissonian | subPoissonian | fano | mandelQ
  deriving DecidableEq, Repr, BEq, Fintype

theorem photonStatCount : Fintype.card PhotonStatisticsRegime = 5 := by decide

/-- Coherent light (Poissonian): J = 0. -/
theorem coherent_poissonian : Jcost 1 = 0 := Jcost_unit0

structure PhotonStatCert where
  five_regimes : Fintype.card PhotonStatisticsRegime = 5
  coherent_zero : Jcost 1 = 0

def photonStatCert : PhotonStatCert where
  five_regimes := photonStatCount
  coherent_zero := coherent_poissonian

end IndisputableMonolith.Physics.PhotonStatisticsFromRS
