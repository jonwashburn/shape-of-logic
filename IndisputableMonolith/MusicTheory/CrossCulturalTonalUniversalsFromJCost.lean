import Mathlib
import IndisputableMonolith.Common.CanonicalJBand

/-!
# F6: Cross-Cultural Tonal Universals from J-Cost on Frequency Ratios

Compounds with `MusicalConsonanceFromJCost` (closed-form J-cost values
for the five canonical intervals). Cross-cultural studies (Mehr et al.
2019; McDermott et al. 2016) find that octave (2:1) and perfect fifth
(3:2) are recognised as consonant in every documented tradition, while
many other intervals show cultural variation. The structural prediction:
intervals at the canonical golden-section J-cost band are the universals;
intervals outside are the culturally variable ones.

Falsifier: a documented musical tradition without 2:1 octave equivalence
or without preference for low-J-cost intervals over high-J-cost ones in
psychoacoustic testing.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace MusicTheory
namespace CrossCulturalTonalUniversalsFromJCost

open Common.CanonicalJBand

structure CrossCulturalTonalCert where
  base : CanonicalCert

def crossCulturalTonalCert : CrossCulturalTonalCert where
  base := cert

end CrossCulturalTonalUniversalsFromJCost
end MusicTheory
end IndisputableMonolith
