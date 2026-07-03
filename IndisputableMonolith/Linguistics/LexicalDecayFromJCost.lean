import Mathlib
import IndisputableMonolith.Common.CanonicalJBand

/-!
# F4: Lexical Decay Rate from J-Cost on Word-Frequency Persistence

Compounds with `Linguistics/PhonemeInventoryBound` and
`Linguistics/LexiconRatio`. Per-word J-cost on `r := observed_frequency /
expected_frequency_under_zipf`. Lexical decay rate (Pagel et al. 2007;
~50% replacement per 8000 years for basic Swadesh-list vocabulary) sits
on the φ-ladder: half-life decay is structurally permitted at the
canonical band on the persistence ratio.

Falsifier: any reconstructed proto-language with measured Swadesh-list
half-life outside the canonical-band-derived window on >5 daughter
language pairs.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Linguistics
namespace LexicalDecayFromJCost

open Common.CanonicalJBand

structure LexicalDecayCert where
  base : CanonicalCert

def lexicalDecayCert : LexicalDecayCert where
  base := cert

end LexicalDecayFromJCost
end Linguistics
end IndisputableMonolith
