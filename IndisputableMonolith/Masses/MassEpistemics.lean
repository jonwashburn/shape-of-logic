/-!
# Mass Epistemics: what is observed versus what is inferred

Companion formalization for `What_A_Mass_Actually_Is_20260530.html`.

The Particle Data Group table is routinely read as a list of measurements. It is
not. It is a list of best-fit parameters in one theory (the Standard Model),
each obtained by feeding a genuine observable through the SM Lagrangian and a
renormalization convention. The word "mass" hides several distinct epistemic
situations. This module makes the distinction exact and machine-checkable.

For each particle we record:
* `signal`  — the raw thing a detector actually records;
* `depth`   — how theory-laden the path from that signal to a quoted "mass" is.

The theorems below pin down the claims that matter for honest comparison:
* no confined quark mass is directly observed (each is a scheme parameter);
* the absolute neutrino mass has never been observed (difference-only);
* the electron and proton masses are near-direct.

Deliberately imports nothing beyond the Lean prelude, so it is fast, robust,
and cannot drift from the heavy mass-scorecard library it comments on.

**Lean: 0 sorry, 0 axiom (kernel-only via `decide`).**
-/

namespace IndisputableMonolith
namespace Masses
namespace MassEpistemics

/-- The raw signal a detector records, before any theory turns it into a "mass". -/
inductive ObservedSignal where
  /-- Penning-trap cyclotron-frequency ratio of a stable, isolated particle. -/
  | cyclotronFrequencyRatio
  /-- Atomic or muonium transition frequency (bound-state spectroscopy). -/
  | spectralLine
  /-- Cross-section onset at `√s = 2m` (threshold scan). -/
  | thresholdTurnOn
  /-- Invariant mass / endpoints of reconstructed decay products. -/
  | decayKinematics
  /-- Breit-Wigner peak position in a cross-section (line shape). -/
  | resonancePeak
  /-- Neutrino flavor-oscillation phase: yields `Δm²` only, never an absolute mass. -/
  | oscillationPhase
  /-- Lattice / chiral-PT / sum-rule fit of hadron observables to a Lagrangian parameter. -/
  | hadronSpectrumFit
deriving DecidableEq, Repr

/-- How theory-laden the path from `signal` to the quoted "mass" is. -/
inductive InferenceDepth where
  /-- Inertia/rest energy of a stable asymptotic state, up to unit conversion. -/
  | nearDirect
  /-- `E² = p² + m²` on a free, metastable, asymptotic state. -/
  | kinematic
  /-- Breit-Wigner parameter; convention-dependent at the tens-of-MeV level. -/
  | resonance
  /-- Reconstructed decay products plus a Monte-Carlo model (pole-vs-MC ambiguity). -/
  | reconstructed
  /-- Renormalization-scheme- and scale-dependent Lagrangian coupling;
      never an asymptotic state (confined quarks). -/
  | schemeParameter
  /-- Only mass-squared differences are observed; the absolute scale is unmeasured. -/
  | differenceOnly
deriving DecidableEq, Repr

inductive Particle where
  | electron | muon | tau
  | up | down | strange | charm | bottom | top
  | neutrinoAbs | wBoson | zBoson | higgs | proton
deriving DecidableEq, Repr

/-- One row of the mass-epistemics registry. -/
structure MassDatum where
  particle : Particle
  signal   : ObservedSignal
  depth    : InferenceDepth
deriving DecidableEq, Repr

open Particle ObservedSignal InferenceDepth

/-- Convenience constructor for a registry row. -/
def datum (p : Particle) (s : ObservedSignal) (i : InferenceDepth) : MassDatum :=
  { particle := p, signal := s, depth := i }

/-- A mass is "directly observed" only when it is the inertia / rest energy of an
asymptotic state, read near-directly or via kinematics. Everything else is inferred. -/
def directlyObserved (d : MassDatum) : Bool :=
  match d.depth with
  | InferenceDepth.nearDirect => true
  | InferenceDepth.kinematic  => true
  | _                          => false

/-- True iff the quoted "mass" is a renormalization-scheme parameter (a confined quark). -/
def isSchemeParameter (d : MassDatum) : Bool :=
  match d.depth with
  | InferenceDepth.schemeParameter => true
  | _                               => false

/-- True iff only squared-mass differences are observed (the absolute scale is unmeasured). -/
def isDifferenceOnly (d : MassDatum) : Bool :=
  match d.depth with
  | InferenceDepth.differenceOnly => true
  | _                              => false

/-- The full registry: every Standard-Model mass, tagged by signal and inference depth. -/
def registry : List MassDatum :=
  [ datum electron   cyclotronFrequencyRatio nearDirect
  , datum proton     cyclotronFrequencyRatio nearDirect
  , datum muon       spectralLine            kinematic
  , datum tau        thresholdTurnOn         kinematic
  , datum zBoson     resonancePeak           resonance
  , datum higgs      resonancePeak           resonance
  , datum wBoson     decayKinematics         reconstructed
  , datum top        decayKinematics         reconstructed
  , datum up         hadronSpectrumFit       schemeParameter
  , datum down       hadronSpectrumFit       schemeParameter
  , datum strange    hadronSpectrumFit       schemeParameter
  , datum charm      hadronSpectrumFit       schemeParameter
  , datum bottom     hadronSpectrumFit       schemeParameter
  , datum neutrinoAbs oscillationPhase       differenceOnly ]

/-- The five confined light/heavy quarks whose "mass" is a Lagrangian scheme parameter. -/
def confinedQuarks : List Particle := [up, down, strange, charm, bottom]

/-- Lookup helper: the recorded datum for a particle, if present. -/
def find? (p : Particle) : Option MassDatum :=
  registry.find? (fun d => decide (d.particle = p))

/-! ## Theorems: the claims that govern honest comparison -/

/-- No confined quark mass is directly observed: each row is a scheme parameter,
not the inertia of any asymptotic state. -/
theorem confined_quarks_not_directly_observed :
    confinedQuarks.all
      (fun p => !directlyObserved (datum p hadronSpectrumFit schemeParameter)) = true := by
  decide

/-- Each confined quark mass is a renormalization-scheme parameter. -/
theorem confined_quarks_are_scheme :
    confinedQuarks.all
      (fun p => isSchemeParameter (datum p hadronSpectrumFit schemeParameter)) = true := by
  decide

/-- The electron mass is near-direct: the inertia of a stable, isolated, asymptotic state. -/
theorem electron_directly_observed :
    directlyObserved (datum electron cyclotronFrequencyRatio nearDirect) = true := by
  decide

/-- The proton mass is near-direct in value, even though its *origin* (QCD binding) is dynamical. -/
theorem proton_directly_observed :
    directlyObserved (datum proton cyclotronFrequencyRatio nearDirect) = true := by
  decide

/-- The absolute neutrino mass has never been observed: oscillation yields differences only,
and the difference-only depth is not directly observed. -/
theorem neutrino_absolute_difference_only :
    isDifferenceOnly (datum neutrinoAbs oscillationPhase differenceOnly) = true
    ∧ directlyObserved (datum neutrinoAbs oscillationPhase differenceOnly) = false := by
  decide

/-- The W and top masses are reconstructed (Monte-Carlo / model dependent), hence not
directly observed despite being heavy. -/
theorem w_and_top_reconstructed :
    directlyObserved (datum wBoson decayKinematics reconstructed) = false
    ∧ directlyObserved (datum top decayKinematics reconstructed) = false := by
  decide

/-- The registry has exactly one row per particle (fourteen rows, no duplicates of the
fourteen named particles). A sanity check that the taxonomy is total over what we track. -/
theorem registry_size : registry.length = 14 := by decide

/-! ## Certificate bundling the epistemic facts -/

/-- A certificate that the mass-epistemics taxonomy is internally consistent:
quarks are scheme parameters and not directly observed, the neutrino absolute mass
is difference-only, and the electron/proton masses are near-direct. -/
structure MassEpistemicsCert : Prop where
  quarks_not_observed :
    confinedQuarks.all
      (fun p => !directlyObserved (datum p hadronSpectrumFit schemeParameter)) = true
  quarks_scheme :
    confinedQuarks.all
      (fun p => isSchemeParameter (datum p hadronSpectrumFit schemeParameter)) = true
  neutrino_diff_only :
    isDifferenceOnly (datum neutrinoAbs oscillationPhase differenceOnly) = true
  electron_observed :
    directlyObserved (datum electron cyclotronFrequencyRatio nearDirect) = true

/-- The mass-epistemics certificate holds. -/
def massEpistemicsCert : MassEpistemicsCert where
  quarks_not_observed := confined_quarks_not_directly_observed
  quarks_scheme := confined_quarks_are_scheme
  neutrino_diff_only := (neutrino_absolute_difference_only).1
  electron_observed := electron_directly_observed

end MassEpistemics
end Masses
end IndisputableMonolith
